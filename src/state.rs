use std::ops::Deref;

use anyhow::bail;
use bevy_utils::HashMap;

use crate::{ast::BinaryOperator, parser};

#[derive(Default)]
pub struct CalculatorState {
    pub variables: HashMap<String, f64>,
    pub functions: HashMap<String, Function>,
}

#[derive(Debug)]
enum Token {
    Constant(f64),
    BinaryOperator(BinaryOperator),
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
        state: &CalculatorState
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
                    name,
                    parameter_count,
                } => {
                    resolved.push(Token::FunctionCall {
                        name: name.into(),
                        parameter_count,
                    });
                }
                parser::Token::BinaryOperator(operator) => {
                    resolved.push(Token::BinaryOperator(operator));
                }
            };
        }

        Ok(Function { name, expression: resolved, parameter_count: parameter_names.len() as _ })
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
                        println!("{name}{parameters:?} = {result}");

                        stack.drain(stack.len() - parameter_count..);
                        stack.push(result);

                    }
                }
                Token::BinaryOperator(operator) => {
                    if let (Some(rhs), Some(lhs)) = (stack.pop(), stack.pop()) {
                        stack.push(operator.apply(lhs, rhs));
                        println!("{operator:?}({lhs}, {rhs}) = {}", stack.last().unwrap());
                    } else {
                        unreachable!();
                    }
                }
            }
        }

        Ok(stack.pop().unwrap())
    }
}
