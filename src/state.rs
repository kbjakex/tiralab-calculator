use std::ops::{Deref, Range};

use anyhow::bail;
use bevy_utils::HashMap;

use crate::{
    builtins::{self, BuiltinFnPtr},
    operators::{BinaryOperator, UnaryOperator},
    parser::{self, parse_error, ParseResult},
};

pub struct CalculatorState {
    pub variables: HashMap<String, Variable>,
    pub functions: HashMap<String, Function>,
}

impl CalculatorState {
    pub fn new_with_builtins() -> Self {
        let mut state = Self {
            variables: Default::default(),
            functions: Default::default(),
        };
        builtins::add_builtin_constants(&mut state.variables);
        state
    }

    /// Inserts a (user-defined) variable with the given name and value.
    /// If there was already a value with the name, the value is replaced
    /// and the old value is returned.
    #[rustfmt::skip]
    pub fn set_variable(&mut self, name: &str, value: Value, dry_run: bool) -> anyhow::Result<Option<Value>> {
        if let Some(old) = self.variables.get(name) {
            if old.builtin {
                bail!("'{name}' is a built-in constant that can't be replaced! Please choose another name.");
            }
        }

        if dry_run {
            return Ok(None);
        }

        let old = self.variables.insert(name.to_owned(), Variable {
            value,
            builtin: false
        })
        .map(|var| var.value);

        Ok(old)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Decimal(rug::Float),
    Rational(rug::Rational),
    Complex(rug::Complex),
    Boolean(bool),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Decimal(value) => value.fmt(f),
            Value::Rational(value) => value.fmt(f),
            Value::Complex(value) => value.fmt(f),
            Value::Boolean(value) => value.fmt(f),
        }
    }
}

impl Value {
    // Convenience function for construction
    pub fn rational(numerator: i32, denominator: u32) -> Value {
        Value::Rational(rug::Rational::from((numerator, denominator)))
    }

    pub fn type_name(&self) -> &'static str {
        match self {
            // To not confuse end users with information that is unlikely
            // to be useful, display both rationals and decimals as "real number"
            Value::Decimal(_) => "real number",
            Value::Rational(_) => "real number",
            Value::Complex(_) => "complex",
            Value::Boolean(_) => "boolean",
        }
    }
}

enum Token {
    Constant(Value),
    BinaryOperator(BinaryOperator),
    UnaryOperator(UnaryOperator),
    FunctionCall {
        name: Box<str>,
        parameter_count: u32,
    },
    BuiltInFunctionCall {
        fn_pointer: BuiltinFnPtr,
        // Note: number of *provided* parameters,
        // not how many are required. (Same for FunctionCall.)
        parameter_count: u32,
    },
    Parameter {
        index: usize,
    },
}

pub struct Variable {
    pub value: Value,
    pub builtin: bool,
}

pub struct Function {
    name: Box<str>,
    expression: Vec<Token>,
    pub parameter_count: u32,
}

impl Function {
    pub fn from_name_and_expression(
        name: Box<str>,
        name_span: Range<usize>,
        expression: &str,
        parameter_names: &[&str],
        state: &CalculatorState,
    ) -> ParseResult<Self> {
        let tokens = parser::infix_to_postfix(expression)?;
        Self::from_name_and_tokens(name, name_span, &tokens, parameter_names, state)
    }

    pub fn from_name_and_tokens(
        name: Box<str>,
        name_span: Range<usize>,
        tokens: &[parser::Token],
        parameter_names: &[&str],
        state: &CalculatorState,
    ) -> ParseResult<Self> {
        if builtins::resolve_builtin_fn_call(&name).is_some() {
            parse_error!(
                name_span,
                "{name} is a built-in function! Choose another name."
            );
        }

        let mut resolved = Vec::new();
        for token in tokens {
            match &token.kind {
                parser::TokenKind::Number(value) => resolved.push(Token::Constant(value.clone())),
                &parser::TokenKind::Variable { name } => {
                    if let Some(index) = parameter_names
                        .iter()
                        .position(|param_name| *param_name == name)
                    {
                        // reverse the index, because with shunting yard, the parameters end up being in the wrong order
                        resolved.push(Token::Parameter { index });
                    } else if let Some(var) = state.variables.get(name) {
                        resolved.push(Token::Constant(var.value.clone()));
                    } else {
                        parse_error!(token.span.clone(), "Unknown variable '{name}'");
                    }
                }
                &parser::TokenKind::Function {
                    name: called_fn_name,
                    parameter_count,
                } => {
                    if called_fn_name == name.as_ref() {
                        parse_error!(token.span.clone(), "Recursion is not allowed!");
                    }

                    if let Some((fn_pointer, expected_param_count)) =
                        builtins::resolve_builtin_fn_call(called_fn_name)
                    {
                        if parameter_count as usize != expected_param_count
                            && expected_param_count != usize::MAX
                        {
                            parse_error!(token.span.clone(), "Function '{called_fn_name}' takes {expected_param_count} parameters, {parameter_count} were given");
                        }

                        resolved.push(Token::BuiltInFunctionCall {
                            fn_pointer,
                            parameter_count,
                        });
                        continue;
                    }

                    resolved.push(Token::FunctionCall {
                        name: called_fn_name.into(),
                        parameter_count,
                    });
                }
                &parser::TokenKind::UnaryOperator(operator) => {
                    resolved.push(Token::UnaryOperator(operator));
                }
                &parser::TokenKind::BinaryOperator(operator) => {
                    resolved.push(Token::BinaryOperator(operator));
                }
            };
        }

        Ok(Function {
            name,
            expression: resolved,
            parameter_count: parameter_names.len() as _,
        })
    }

    pub fn evaluate(
        &self,
        state: &CalculatorState,
        parameters: &[Value],
        precision_bits: u32,
    ) -> anyhow::Result<Value> {
        if self.parameter_count != parameters.len() as u32 {
            bail!(
                "Function '{}' takes {} parameters, {} were given",
                self.name,
                self.parameter_count,
                parameters.len()
            );
        }

        let mut stack = Vec::with_capacity(self.expression.len()); // Upper bound

        for i in 0..self.expression.len() {
            match &self.expression[i] {
                Token::Constant(value) => stack.push(value.clone()),
                &Token::Parameter { index } => stack.push(parameters[index].clone()),
                Token::FunctionCall {
                    name,
                    parameter_count,
                } => {
                    let parameter_count = *parameter_count as usize;
                    if let Some(function) = state.functions.get(name.deref()) {
                        let parameters = &stack[stack.len() - parameter_count..];
                        let result = function.evaluate(state, parameters, precision_bits)?;

                        stack.drain(stack.len() - parameter_count..);
                        stack.push(result);
                    } else {
                        bail!("Function '{name}' does not exist.");
                    }
                }
                Token::BuiltInFunctionCall {
                    fn_pointer,
                    parameter_count: num_provided_parameters,
                } => {
                    let parameter_count = *num_provided_parameters as usize;
                    let parameters = &stack[stack.len() - parameter_count..];
                    let result = fn_pointer(parameters, precision_bits)?;

                    stack.drain(stack.len() - parameter_count..);
                    stack.push(result);
                }
                Token::UnaryOperator(operator) => {
                    if let Some(x) = stack.last_mut() {
                        *x = operator.apply(x.clone())?;
                    } else {
                        unreachable!()
                    }
                }
                Token::BinaryOperator(operator) => {
                    if let (Some(rhs), Some(lhs)) = (stack.pop(), stack.pop()) {
                        stack.push(operator.apply(lhs, rhs, precision_bits)?);
                    } else {
                        unreachable!();
                    }
                }
            }
        }

        Ok(stack.pop().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use crate::{state::Variable, DEFAULT_PRECISION};

    use super::{CalculatorState, Function, Value};

    fn eval(
        state: &CalculatorState,
        expression: &str,
        params: &[&str],
        param_values: &[Value],
    ) -> Value {
        Function::from_name_and_expression("foo".into(), 0..0, expression, params, state)
            .unwrap()
            .evaluate(state, param_values, DEFAULT_PRECISION)
            .unwrap()
    }

    fn val(numerator: i32, denominator: u32) -> Value {
        Value::rational(numerator, denominator)
    }

    #[test]
    fn test_simple_evaluates_correctly() {
        let state = CalculatorState::new_with_builtins();
        assert_eq!(val(1, 6), eval(&state, "1.0 / 6.0", &[], &[]));
        assert_eq!(val(5, 2), eval(&state, "(x + 3) / 2", &["x"], &[val(2, 1)]));
        assert_eq!(
            val(-1, 1),
            eval(&state, "x - y", &["x", "y"], &[val(1, 1), val(2, 1)])
        );
        assert_eq!(
            val(-3, 1),
            eval(
                &state,
                "(x - y) / (x + y)",
                &["x", "y"],
                &[val(1, 1), val(-2, 1)]
            )
        );
    }

    #[test]
    fn test_variable_references_work() {
        let mut state = CalculatorState::new_with_builtins();
        state.variables.insert(
            "mypi".into(),
            Variable {
                value: val(31415926, 10000000),
                builtin: false,
            },
        );
        state.variables.insert(
            "foo".into(),
            Variable {
                value: val(-100, 1),
                builtin: false,
            },
        );

        assert_eq!(
            val(-31415926, 1000000000),
            eval(&state, "mypi / foo", &[], &[])
        );
        assert_eq!(val(0, 1), eval(&state, "foo + x", &["x"], &[val(100, 1)]));
    }

    #[test]
    fn test_unknown_variables_error() {
        let state = CalculatorState::new_with_builtins();

        let result = Function::from_name_and_expression("foo".into(), 0..0, "x", &[], &state);
        assert!(result.is_err());
    }

    #[test]
    fn test_function_calls_work() {
        let mut state = CalculatorState::new_with_builtins();
        let test_fn = Function::from_name_and_expression(
            "f".into(),
            0..0,
            "x * y / z",
            &["x", "y", "z"],
            &state,
        )
        .unwrap();
        state.functions.insert("f".into(), test_fn);

        assert_eq!(val(3 * 5, 7), eval(&state, "f(3, 5, 7)", &[], &[]));
        assert_eq!(
            val(3 * 5, 7),
            eval(
                &state,
                "f(x, y, z)",
                &["x", "y", "z"],
                &[val(3, 1), val(5, 1), val(7, 1)]
            )
        );
    }

    #[test]
    fn test_unknown_functions_error() {
        let state = CalculatorState::new_with_builtins();

        let result = Function::from_name_and_expression("foo".into(), 0..0, "f(x)", &[], &state);
        assert!(result.is_err());

        let result =
            Function::from_name_and_expression("foo".into(), 0..0, "g(x) + f(x, y)", &[], &state);
        assert!(result.is_err());
    }

    #[test]
    fn test_parameter_count_mismatch_errors() {
        let state = CalculatorState::new_with_builtins();
        let test_fn = Function::from_name_and_expression(
            "f".into(),
            0..0,
            "x * y / z",
            &["x", "y", "z"],
            &state,
        )
        .unwrap();

        assert!(test_fn.evaluate(&state, &[], DEFAULT_PRECISION).is_err());
        assert!(test_fn
            .evaluate(&state, &[val(1, 1)], DEFAULT_PRECISION)
            .is_err());
        assert!(test_fn
            .evaluate(&state, &[val(1, 1), val(2, 1)], DEFAULT_PRECISION)
            .is_err());
        assert!(test_fn
            .evaluate(
                &state,
                &[val(1, 1), val(2, 1), val(3, 1)],
                DEFAULT_PRECISION
            )
            .is_ok());
    }
}
