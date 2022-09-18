#![feature(let_else)]
#![warn(clippy::all, clippy::pedantic, clippy::cargo)]

pub mod ast;
pub mod parser;
pub mod state;

use std::io::{self, BufRead, Write};

use state::CalculatorState;

use anyhow::{bail, Result};

use crate::parser::Token;

fn print_input_marker() {
    print!("> ");
    // A flush is needed because output is buffered, and the '>' would
    // otherwise be printed when the next println!() occurs.
    io::stdout().flush().unwrap();
}

fn main() {
    let mut state = CalculatorState::default();

    // A simple REPL (read-eval-print-loop) interface
    print_input_marker();
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

        print_input_marker();
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
    let mut postfix = parser::infix_to_postfix_shunting_yard(&input)?;

    println!("{}", eval_postfix(&mut postfix, state)?);

    Ok(())
}

fn process_variable_or_function(
    _state: &mut CalculatorState,
    _start: &str,
    _rest: &str,
) -> Result<()> {
    bail!("TBD")
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
                let Some(&resolved) = state.variables.get(name) else {
                    bail!("Variable '{name}' not found");
                };

                tokens[head] = Token::Number(resolved);
                head += 1;
            }
            Token::BinaryOperator(operator) => {
                let Some(&Token::Number(lhs)) = tokens.get(head-2) else {
                    unreachable!();
                };
                let Some(&Token::Number(rhs)) = tokens.get(head-1) else {
                    unreachable!();
                };

                tokens[head - 2] = Token::Number(operator.apply(lhs, rhs));
                head -= 1;
            }
        }
    }

    assert_eq!(1, head);

    match tokens[0] {
        Token::Number(value) => Ok(value),
        _ => unreachable!()
    }
}
