use std::ops::Deref;

use anyhow::bail;
use bevy_utils::HashMap;

use crate::{
    operators::{BinaryOperator, UnaryOperator},
    parser,
};

#[derive(Default)]
pub struct CalculatorState {
    pub variables: HashMap<String, f64>,
    pub functions: HashMap<String, Function>,
}

#[derive(Debug)]
enum Token {
    Constant(f64),
    BinaryOperator(BinaryOperator),
    UnaryOperator(UnaryOperator),
    FunctionCall {
        name: Box<str>,
        parameter_count: u32,
    },
    Parameter {
        index: usize,
    },
}

pub struct Function {
    name: Box<str>,
    expression: Vec<Token>,
    pub parameter_count: u32,
}

impl Function {
    pub fn from_name_and_expression(
        name: Box<str>,
        expression: &str,
        parameter_names: &[&str],
        state: &CalculatorState,
    ) -> anyhow::Result<Self> {
        let tokens = parser::infix_to_postfix(expression)?;
        Self::from_name_and_tokens(name, &tokens, parameter_names, state)
    }

    pub fn from_name_and_tokens(
        name: Box<str>,
        tokens: &[parser::Token],
        parameter_names: &[&str],
        state: &CalculatorState,
    ) -> anyhow::Result<Self> {
        let mut resolved = Vec::new();
        for token in tokens {
            match *token {
                parser::Token::Number(value) => resolved.push(Token::Constant(value)),
                parser::Token::Variable { name } => {
                    if let Some(&value) = state.variables.get(name) {
                        resolved.push(Token::Constant(value));
                    } else if let Some(index) = parameter_names
                        .iter()
                        .position(|param_name| *param_name == name)
                    {
                        // reverse the index, because with shunting yard, the parameters end up being in the wrong order
                        resolved.push(Token::Parameter { index });
                    } else {
                        bail!("Unknown variable '{name}'");
                    }
                }
                parser::Token::Function {
                    name: called_fn_name,
                    parameter_count,
                } => {
                    if called_fn_name == name.as_ref() {
                        bail!("Recursion is not allowed!");
                    }

                    resolved.push(Token::FunctionCall {
                        name: called_fn_name.into(),
                        parameter_count,
                    });
                }
                parser::Token::UnaryOperator(operator) => {
                    resolved.push(Token::UnaryOperator(operator));
                }
                parser::Token::BinaryOperator(operator) => {
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

    pub fn evaluate(&self, state: &CalculatorState, parameters: &[f64]) -> anyhow::Result<f64> {
        if self.parameter_count != parameters.len() as _ {
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
                &Token::Constant(value) => stack.push(value),
                &Token::Parameter { index } => stack.push(parameters[index]),
                Token::FunctionCall {
                    name,
                    parameter_count,
                } => {
                    let parameter_count = *parameter_count as usize;
                    if let Some(function) = state.functions.get(name.deref()) {
                        let parameters = &stack[stack.len() - parameter_count..];
                        let result = function.evaluate(state, parameters)?;

                        stack.drain(stack.len() - parameter_count..);
                        stack.push(result);
                    } else {
                        bail!("Function '{name}' does not exist.");
                    }
                }
                Token::UnaryOperator(operator) => {
                    if let Some(x) = stack.last_mut() {
                        *x = operator.apply(*x);
                    } else {
                        unreachable!()
                    }
                }
                Token::BinaryOperator(operator) => {
                    if let (Some(rhs), Some(lhs)) = (stack.pop(), stack.pop()) {
                        stack.push(operator.apply(lhs, rhs));
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
    use super::{CalculatorState, Function};

    fn eval(
        state: &CalculatorState,
        expression: &str,
        params: &[&str],
        param_values: &[f64],
    ) -> f64 {
        Function::from_name_and_expression("foo".into(), expression, params, state)
            .unwrap()
            .evaluate(state, param_values)
            .unwrap()
    }

    #[test]
    fn test_simple_evaluates_correctly() {
        let state = CalculatorState::default();
        assert_eq!(1.0 / 6.0, eval(&state, "1.0 / 6.0", &[], &[]));
        assert_eq!(2.5, eval(&state, "(x + 3) / 2", &["x"], &[2.0]));
        assert_eq!(-1.0, eval(&state, "x - y", &["x", "y"], &[1.0, 2.0]));
        assert_eq!(
            -3.0,
            eval(&state, "(x - y) / (x + y)", &["x", "y"], &[1.0, -2.0])
        );
    }

    #[test]
    fn test_variable_references_work() {
        let mut state = CalculatorState::default();
        state.variables.insert("mypi".into(), std::f64::consts::PI);
        state.variables.insert("foo".into(), -100.0);

        assert_eq!(
            std::f64::consts::PI / -100.0,
            eval(&state, "mypi / foo", &[], &[])
        );
        assert_eq!(0.0, eval(&state, "foo + x", &["x"], &[100.0]));
    }

    #[test]
    fn test_unknown_variables_error() {
        let state = CalculatorState::default();

        let result = Function::from_name_and_expression("foo".into(), "x", &[], &state);
        assert!(result.is_err());
    }

    #[test]
    fn test_function_calls_work() {
        let mut state = CalculatorState::default();
        let test_fn =
            Function::from_name_and_expression("f".into(), "x * y / z", &["x", "y", "z"], &state)
                .unwrap();
        state.functions.insert("f".into(), test_fn);

        assert_eq!(3.0 * 5.0 / 7.0, eval(&state, "f(3, 5, 7)", &[], &[]));
        assert_eq!(
            3.0 * 5.0 / 7.0,
            eval(&state, "f(x, y, z)", &["x", "y", "z"], &[3.0, 5.0, 7.0])
        );
    }

    #[test]
    fn test_unknown_functions_error() {
        let state = CalculatorState::default();

        let result = Function::from_name_and_expression("foo".into(), "f(x)", &[], &state);
        assert!(result.is_err());

        let result = Function::from_name_and_expression("foo".into(), "g(x) + f(x, y)", &[], &state);
        assert!(result.is_err());
    }

    #[test]
    fn test_parameter_count_mismatch_errors() {
        let state = CalculatorState::default();
        let test_fn =
            Function::from_name_and_expression("f".into(), "x * y / z", &["x", "y", "z"], &state)
                .unwrap();

        assert!(test_fn.evaluate(&state, &[]).is_err());
        assert!(test_fn.evaluate(&state, &[1.0]).is_err());
        assert!(test_fn.evaluate(&state, &[1.0, 2.0]).is_err());
        assert!(test_fn.evaluate(&state, &[1.0, 2.0, 3.0]).is_ok());
    }
}
