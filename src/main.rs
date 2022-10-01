#![warn(clippy::all, clippy::cargo)]

pub mod ast;
pub mod parser;
pub mod state;

use std::io::{self, BufRead, Write};

use parser::{infix_to_postfix, ParserToken, TokenIterator};

use anyhow::{bail, Result};
use state::CalculatorState;

use crate::{parser::Token, state::Function};

fn print_input_expected_marker() {
    print!("> ");
    // A flush is needed because output is buffered, and the '>' would
    // otherwise be printed when the next println!() occurs.
    io::stdout().flush().unwrap();
}

fn main() {
    let mut state = CalculatorState::default();

    // A simple REPL (read-eval-print-loop) interface
    print_input_expected_marker();
    for line in std::io::stdin().lock().lines() {
        if line.is_err() {
            return; // No more input
        }

        let line = line.unwrap().trim().to_lowercase();

        if line == "exit" {
            break;
        }

        if let Err(e) = process_input(&mut state, line) {
            println!("Syntax error: {e}");
        }

        print_input_expected_marker();
    }
}

/// Process a line of input from the user, resulting either a direct evaluation
/// of an expression printed in the console, or a variable or a function added
/// to the calculator state.
/// # Errors
/// If the input string was not syntactically valid, an error describing the
/// problem is returned.
fn process_input(state: &mut CalculatorState, input: String) -> Result<()> {
    if input.is_empty() {
        return Ok(());
    }

    if let Some((start, rest)) = input.split_once('=') {
        return process_variable_or_function(state, start, rest);
    }

    // Neither a variable nor a function, so simply evaluate
    let mut postfix = parser::infix_to_postfix(input.as_str())?;

    println!("{}", eval_postfix(&mut postfix, state)?);

    Ok(())
}

/// Declare a function or a variable based on the input.
/// Assumes the input is trimmed and non-empty.
fn process_variable_or_function(
    state: &mut CalculatorState,
    start: &str, // parts before the = sign, i.e variable or function name
    rest: &str,
) -> Result<()> {
    let mut tokens = TokenIterator::of(start);

    // 1. Variable and function should both begin with what is a valid variable name
    let identifier_token = tokens.next().unwrap()?;

    match identifier_token {
        ParserToken::Variable { name } => {
            if tokens.next().is_some() {
                bail!("Invalid syntax (interpreted as variable declaration, which should be `name = value`)");
            }
            let mut value_tokens = infix_to_postfix(rest)?;
            let value = eval_postfix(&mut value_tokens, state)?;
            state
                .variables
                .entry(name.to_owned())
                .and_modify(|old_value| {
                    *old_value = value;
                    println!("{name} changed from {} to {value}", *old_value);
                })
                .or_insert_with(|| {
                    println!("{name} = {value}");
                    value
                });
        }
        ParserToken::Function { name } => {
            assert!(matches!(tokens.next().unwrap()?, ParserToken::LeftParen));
            let mut param_names = Vec::new();
            let mut expecting_identifier = true;
            loop {
                if let Some(next) = tokens.next() {
                    let next = next?;

                    match next {
                        ParserToken::Variable { name } => param_names.push(name),
                        ParserToken::Delimiter => {}
                        ParserToken::RightParen => break,
                        other => bail!("'{other:?}' not allowed in function declaration!"),
                    }

                    let is_identifier = matches!(next, ParserToken::Variable { .. });
                    if expecting_identifier && !is_identifier {
                        bail!("Expected parameter name, got '{next:?}");
                    }
                    if !expecting_identifier && is_identifier {
                        bail!("Expected `,` or `)`, got identifier '{next:?}'");
                    }
                    expecting_identifier = !is_identifier;
                } else {
                    bail!("Missing closing ) for function declaration");
                }
            }

            if tokens.next().is_some() {
                bail!("Found extra symbols after function name");
            }

            let function =
                Function::from_name_and_expression(name.into(), rest, &param_names, state)?;

            if state.functions.insert(name.to_owned(), function).is_some() {
                println!("Updated function '{name}'");
            } else {
                println!("Defined function '{name}'!");
            }
        }
        _ => {
            bail!("Invalid syntax");
        }
    }

    Ok(())
}

/// Attempts to evaluate the postfix expression. Evaluation happens in-place, treating the
/// input array as a stack, and this is therefore a destructive operation.
///
/// The function assumes `tokens` as a whole represents a valid postfix expression.
/// # Errors
/// Should an error occur, a human-readable message describing the issue is returned.
fn eval_postfix(tokens: &mut [Token], state: &CalculatorState) -> Result<f64> {
    let mut head = 0;
    for i in 0..tokens.len() {
        match tokens[i] {
            Token::Number(value) => {
                tokens[head] = Token::Number(value);
                head += 1;
            }
            Token::Variable { name } => {
                if let Some(&resolved) = state.variables.get(name) {
                    tokens[head] = Token::Number(resolved);
                    head += 1;
                } else {
                    bail!("Variable '{name}' not found");
                };
            }
            Token::Function {
                name,
                parameter_count,
            } => {
                if let Some(function) = state.functions.get(name) {
                    let mut parameters = [0f64; 8];
                    for i in 0..parameter_count as usize {
                        parameters[parameter_count as usize - 1 - i] = match tokens[head - i - 1] {
                            Token::Number(value) => value,
                            _ => unreachable!(),
                        }
                    }

                    head -= parameter_count as usize;
                    tokens[head] = Token::Number(
                        function.evaluate(state, &parameters[..parameter_count as usize])?,
                    );
                    head += 1;
                } else {
                    bail!("Function '{name}' not found");
                }
            }
            Token::BinaryOperator(operator) => match (&tokens[head - 2], &tokens[head - 1]) {
                (&Token::Number(lhs), &Token::Number(rhs)) => {
                    tokens[head - 2] = Token::Number(operator.apply(lhs, rhs));
                    head -= 1;
                }
                _ => unreachable!(),
            },
        }
    }

    assert_eq!(1, head);

    match tokens[0] {
        Token::Number(value) => Ok(value),
        _ => unreachable!(),
    }
}
