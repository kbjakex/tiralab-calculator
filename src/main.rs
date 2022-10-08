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

        match process_input(&mut state, &line) {
            Ok(Some(output)) => println!("{output}"),
            Ok(None) => {},
            Err(e) => println!("{e}"),
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
fn process_input(state: &mut CalculatorState, input: &str) -> Result<Option<f64>> {
    if input.is_empty() {
        return Ok(None);
    }

    if let Some((start, rest)) = input.split_once('=') {
        process_variable_or_function(state, start.trim(), rest.trim())?;
        return Ok(None);
    }

    // Neither a variable nor a function, so simply evaluate
    let mut postfix = parser::infix_to_postfix(input)?;
    let result = eval_postfix(&mut postfix, state)?;

    Ok(Some(result))
}

/// Declare a function or a variable based on the input.
/// Assumes the input is trimmed and non-empty.
fn process_variable_or_function(
    state: &mut CalculatorState,
    start: &str, // parts before the = sign, i.e variable or function name
    rest: &str,
) -> Result<()> {
    if start.is_empty() {
        bail!("Syntax error: can't start with a `=`");
    }
    let mut tokens = TokenIterator::of(start);

    // 1. Variable and function should both begin with what is a valid variable name
    let identifier_token = tokens.next().unwrap()?;

    match identifier_token {
        ParserToken::Variable { name } => {
            if tokens.next().is_some() {
                bail!("Syntax error: extra tokens after variable name (interpreted as variable declaration, which should be `name = value`)");
            }
            process_variable(name, rest, state)?;
        }
        ParserToken::Function { name } => {
            debug_assert!(matches!(tokens.next().unwrap()?, ParserToken::LeftParen));
            process_function(name, tokens, rest, state)?;
        }
        other => bail!("Syntax error: found `=`, but input did not start with a function/variable name, but `{other}`")
    }

    Ok(())
}

fn process_variable(variable_name: &str, rest: &str, state: &mut CalculatorState) -> anyhow::Result<()> {
    if rest.is_empty() {
        bail!("Value (after `=`) can't be empty");
    }

    let mut value_tokens = infix_to_postfix(rest)?;
    let value = eval_postfix(&mut value_tokens, state)?;
    state
        .variables
        .entry(variable_name.to_owned())
        .and_modify(|old_value| {
            *old_value = value;
            println!("{variable_name} changed from {} to {value}", *old_value);
        })
        .or_insert_with(|| {
            println!("{variable_name} = {value}");
            value
        });

    Ok(())
}

fn process_function(function_name: &str, tokens: TokenIterator<'_>, rest: &str, state: &mut CalculatorState) -> anyhow::Result<()> {
    if rest.is_empty() {
        bail!("Value (after `=`) can't be empty");
    }

    let parameters = parse_function_parameters(tokens)?;    

    let function =
        Function::from_name_and_expression(function_name.into(), rest, &parameters, state)?;

    if state.functions.insert(function_name.into(), function).is_some() {
        println!("Updated function '{function_name}'");
    } else {
        println!("Defined function '{function_name}'!");
    }
    Ok(())
}

fn parse_function_parameters<'a>(mut tokens: TokenIterator<'a>) -> anyhow::Result<Vec<&'a str>> {
    let mut param_names = Vec::new();
    let mut expecting_identifier = true;
    let mut prev_token = None;
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
            prev_token = Some(next);
        } else {
            bail!("Missing closing ) for function declaration");
        }
    }

    if matches!(prev_token, Some(ParserToken::Delimiter)) {
        bail!("Last parameter name is empty");
    }

    if tokens.next().is_some() {
        bail!("Found extra symbols after function name");
    }

    Ok(param_names)
}

/// Attempts to evaluate the postfix expression. Evaluation happens in-place, treating the
/// input array as a stack, and this is therefore a destructive operation.
///
/// The function assumes `tokens` as a whole represents a valid postfix expression.
/// # Errors
/// Should an error occur, a human-readable message describing the issue is returned.
fn eval_postfix(tokens: &mut [Token], state: &CalculatorState) -> Result<f64> {
    // Re-use evaluation implemented for functions
    let function = Function::from_name_and_tokens("".into(), tokens, &[], state)?;
    function.evaluate(state, &[])
}

#[cfg(test)]
mod tests {
    use crate::{state::CalculatorState, process_input};

    #[test]
    fn test_empty_input_is_ok() {
        assert_eq!(None, process_input(&mut CalculatorState::default(), "").unwrap());
    }

    #[test]
    fn test_direct_eval_works() {
        let mut state = CalculatorState::default();
        assert_eq!(Some(5.0), process_input(&mut state, "5").unwrap());
        assert_eq!(Some(3.75), process_input(&mut state, "5 * -(2 + -3) / -4 + 5").unwrap());
    }

    #[test]
    fn test_invalid_input_reports_syntax_error() {
        let mut state = CalculatorState::default();
        assert!(process_input(&mut state, "()").is_err());
    }

    #[test]
    fn test_variables_work() {
        let mut state = CalculatorState::default();

        assert!(process_input(&mut state, "variable").is_err());
        assert_eq!(None, process_input(&mut state, "variable = 3.1415926535").unwrap());
        assert_eq!(Some(3.1415926535), process_input(&mut state, "variable").unwrap());
        assert!(process_input(&mut state, "variabl").is_err());
        assert!(process_input(&mut state, "variables").is_err());

        assert_eq!(None, process_input(&mut state, "variable=2").unwrap());
        assert_eq!(Some(2.0), process_input(&mut state, "variable").unwrap());
    }

    #[test]
    fn test_invalid_variable_declaration_syntax_errors() {
        let mut state = CalculatorState::default();
        assert!(process_input(&mut state, "= 5").is_err());
        assert!(process_input(&mut state, "x =").is_err());
        assert!(process_input(&mut state, "= 5").is_err());
        assert!(process_input(&mut state, "x + = 5").is_err());
        assert!(process_input(&mut state, "x = 5 +").is_err());
        assert!(process_input(&mut state, "7est = 5").is_err()); // names can't start with numbers
    }

    #[test]
    fn test_functions_work() {
        let mut state = CalculatorState::default();

        assert_eq!(None, process_input(&mut state, "f() = 5").unwrap());
        assert_eq!(Some(5.0), process_input(&mut state, "f()").unwrap());

        assert_eq!(None, process_input(&mut state, "f(x) = 5x").unwrap());
        assert!(process_input(&mut state, "f()").is_err());
        assert_eq!(Some(-25.0), process_input(&mut state, "f(-5)").unwrap());

        assert_eq!(None, process_input(&mut state, "g(x, y) = f(x) / f(y)").unwrap());
        assert_eq!(Some(-0.5), process_input(&mut state, "g(-2, 4)").unwrap());
    }

    #[test]
    fn test_invalid_function_declaration_syntax_errors() {
        let mut state = CalculatorState::default();
        assert!(process_input(&mut state, "f(,) = 5").is_err());
        assert!(process_input(&mut state, "f( = 5").is_err());
        assert!(process_input(&mut state, "f() =").is_err());
        assert!(process_input(&mut state, "f() + 5 = 5").is_err());
        assert!(process_input(&mut state, "f(2x) = 5").is_err());
        assert!(process_input(&mut state, "f(x) = 2x +").is_err());
        assert!(process_input(&mut state, "f(a,,b) = a + b").is_err());
        assert!(process_input(&mut state, "f(a,b,) = a + b").is_err());
        assert!(process_input(&mut state, "f(a,) = a").is_err());
        assert!(process_input(&mut state, "f(a b) = a + b").is_err());
    }

}