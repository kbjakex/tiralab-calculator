#![warn(clippy::all)]

mod builtins;
pub mod operators;
pub mod parser;
pub mod state;
pub mod tui;
pub mod util;

use std::{cell::RefCell, rc::Rc};

use parser::{
    infix_to_postfix, make_parse_error, ParseResult, ParserToken, ParserTokenKind, Token,
    TokenIterator, offset,
};

use rustyline::{Cmd, KeyCode, KeyEvent, Modifiers, Movement};
use state::{CalculatorState, Value};
use tui::TuiHelper;
use util::stringify_output;

use crate::{parser::parse_error, state::Function, util::subslice_range};

pub const DEFAULT_PRECISION: u32 = 256; // in bits

fn main() {
    let args = std::env::args()
        .skip(1)
        .fold(String::new(), |result, string| result + &string);
    let args = args.trim();

    let state = Rc::new(RefCell::new(CalculatorState::new_with_builtins()));
    let mut editor = rustyline::Editor::<TuiHelper>::new().unwrap();
    editor.bind_sequence(
        KeyEvent(KeyCode::Right, Modifiers::empty()),
        Cmd::Move(Movement::ForwardChar(1)),
    );
    editor.set_helper(Some(TuiHelper {
        state: state.clone(),
    }));

    // Use same evaluation logic when being invoked directly
    if !args.is_empty() {
        editor.readline_with_initial("", ("", args)).unwrap();
    }

    // A simple REPL (read-eval-print-loop) interface
    loop {
        let line = editor.readline("\x1b[38;5;8m>\x1b[0m ");
        match line {
            Ok(line) => {
                let line = line.trim();
                if line.eq_ignore_ascii_case("exit") {
                    break;
                }

                editor.add_history_entry(line);

                let mut state = state.borrow_mut();
                print_result(process_input(&mut state, &line, false), false);
                if !args.is_empty() {
                    return;
                }

                println!();
            }
            _ => return,
        }
    }
}

fn print_result(result: ParseResult<Option<Value>>, compact: bool) {
    match result {
        Ok(Some(output)) => println!("{}", stringify_output(output, compact).unwrap()),
        Ok(None) => {}
        Err(e) => println!("{e:#}"),
    }
}

/// Process a line of input from the user, resulting either a direct evaluation
/// of an expression printed in the console, or a variable or a function added
/// to the calculator state.
/// If "dry run" is true, the calculator state won't be modified, but all error
/// checking will be performed. Used for syntax checking.
/// # Errors
/// If the input string was not syntactically valid, an error describing the
/// problem is returned.
pub fn process_input(
    state: &mut CalculatorState,
    input: &str,
    dry_run: bool,
) -> ParseResult<Option<Value>> {
    if input.trim().is_empty() {
        return Ok(None);
    }

    if let Some((start, rest)) = input.split_once('=') {
        let last = start
            .as_bytes()
            .get(start.len().saturating_sub(1))
            .copied()
            .unwrap_or(b' ');
        if !rest.starts_with("=") && ![b'!', b'<', b'>'].contains(&last) {
            process_variable_or_function(state, start.trim(), rest.trim(), input, dry_run)?;
            return Ok(None);
        }
    }

    // Neither a variable nor a function, so simply evaluate
    let mut postfix = parser::infix_to_postfix(input)?;
    let result = eval_postfix(&mut postfix, state)?;

    state.set_variable("ans", result.clone(), dry_run).unwrap();

    Ok(Some(result))
}

/// Declare a function or a variable based on the input.
/// Assumes the input is trimmed and non-empty.
fn process_variable_or_function(
    state: &mut CalculatorState,
    start: &str, // parts before the = sign, i.e variable or function name
    rest: &str,
    full: &str,
    dry_run: bool,
) -> ParseResult<()> {
    if start.is_empty() {
        parse_error!(0..1, "Syntax error: can't start with a `=`");
    }
    let mut tokens = TokenIterator::of(start, DEFAULT_PRECISION);

    // 1. Variable and function should both begin with what is a valid variable name
    let identifier_token = tokens.next().unwrap()?;

    match identifier_token.kind {
        ParserTokenKind::Variable { name } => {
            if let Some(token) = tokens.next() {
                let span = token.map_or(0..start.len(), |tok| tok.span);
                parse_error!(span, "Syntax error: extra tokens after variable name (interpreted as variable declaration, which should be `name = value`)");
            }
            process_variable(name, rest, full, state, dry_run)?;
        }
        ParserTokenKind::Function { name } => {
            assert!(matches!(tokens.next().unwrap()?.kind, ParserTokenKind::LeftParen));
            process_function(name, tokens, rest, full, state, dry_run)?;
        }
        other => parse_error!(identifier_token.span, "Syntax error: found `=`, but input did not start with a function/variable name, but `{other}`")
    }

    Ok(())
}

fn process_variable(
    variable_name: &str,
    rest: &str,
    full: &str,
    state: &mut CalculatorState,
    dry_run: bool,
) -> ParseResult<()> {
    if rest.is_empty() {
        let span = subslice_range(full, rest);
        parse_error!(span, "Value (after `=`) can't be empty");
    }

    let span = subslice_range(full, variable_name);
    if variable_name == "ans" {
        parse_error!(
            span,
            "'ans' is a reserved variable name, please choose another"
        );
    }

    let off = subslice_range(full, rest).start;

    let mut value_tokens = infix_to_postfix(rest).map_err(|e| offset(e, off))?;
    let value = eval_postfix(&mut value_tokens, state).map_err(|e| offset(e, off))?;

    let old = state
        .set_variable(variable_name, value, dry_run)
        .map_err(|e| make_parse_error!(span, "{e}"))?;
    if dry_run {
        return Ok(());
    }

    if let Some(old_value) = old {
        println!(
            "{variable_name} changed from {old_value} to {}",
            state.variables[variable_name].value
        );
    } else {
        println!("{variable_name} = {}", state.variables[variable_name].value);
    }

    Ok(())
}

fn process_function(
    function_name: &str,
    tokens: TokenIterator<'_>,
    rest: &str,
    full: &str,
    state: &mut CalculatorState,
    dry_run: bool,
) -> ParseResult<()> {
    if rest.is_empty() {
        let span = subslice_range(full, rest);
        parse_error!(span, "Value (after `=`) can't be empty");
    }

    let parameters = parse_function_parameters(tokens)?;

    let name_span = subslice_range(full, function_name);

    let off = subslice_range(full, rest).start;
    let function = Function::from_name_and_expression(
        function_name.into(),
        name_span,
        rest,
        &parameters,
        state,
    ).map_err(|e| offset(e, off))?;

    if dry_run {
        return Ok(());
    }

    if state
        .functions
        .insert(function_name.into(), function)
        .is_some()
    {
        println!("Updated function '{function_name}'");
    } else {
        println!("Defined function '{function_name}'!");
    }
    Ok(())
}

fn parse_function_parameters(mut tokens: TokenIterator<'_>) -> ParseResult<Vec<&str>> {
    let mut param_names = Vec::new();
    let mut expecting_identifier = true;
    let mut prev_token = None;
    loop {
        if let Some(next) = tokens.next() {
            let next = next?;

            match next.kind {
                ParserTokenKind::Variable { name } => param_names.push(name),
                ParserTokenKind::Delimiter => {}
                ParserTokenKind::RightParen => break,
                other => parse_error!(next.span, "'{other}' not allowed in function declaration!"),
            }

            let is_identifier = matches!(next.kind, ParserTokenKind::Variable { .. });
            if expecting_identifier && !is_identifier {
                parse_error!(next.span, "Expected parameter name, got '{next}");
            }
            if !expecting_identifier && is_identifier {
                parse_error!(next.span, "Expected `,` or `)`, got identifier '{next}'");
            }
            expecting_identifier = !is_identifier;
            prev_token = Some(next);
        } else {
            // `value` is asserted to be non-empty before calling this function, which means
            // there has to be at least one token before this can happen.
            let span = prev_token.unwrap().span;
            parse_error!(span, "Missing closing ) for function declaration");
        }
    }

    if matches!(
        prev_token,
        Some(ParserToken {
            kind: ParserTokenKind::Delimiter,
            ..
        })
    ) {
        parse_error!(prev_token.unwrap().span, "Last parameter name is empty");
    }

    if let Some(next) = tokens.next() {
        let span = match next {
            Ok(token) => token.span,
            Err(error) => error.span,
        };
        parse_error!(span, "Found extra symbols after function name");
    }

    Ok(param_names)
}

/// Attempts to evaluate the postfix expression. Evaluation happens in-place, treating the
/// input array as a stack, and this is therefore a destructive operation.
///
/// The function assumes `tokens` as a whole represents a valid postfix expression.
/// # Errors
/// Should an error occur, a human-readable message describing the issue is returned.
fn eval_postfix(tokens: &mut [Token], state: &CalculatorState) -> ParseResult<Value> {
    // Re-use evaluation implemented for functions
    let function = Function::from_name_and_tokens("".into(), 0..0, tokens, &[], state)?;
    match function.evaluate(state, &[], DEFAULT_PRECISION) {
        // TODO: don't hard-code precision
        Ok(val) => Ok(val),
        Err(e) => parse_error!(0..0, "{e}"),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        process_input,
        state::{CalculatorState, Value},
    };

    #[test]
    fn test_empty_input_is_ok() {
        assert_eq!(
            None,
            process_input(&mut CalculatorState::new_with_builtins(), "", false).unwrap()
        );
    }

    #[test]
    fn test_direct_eval_works() {
        let mut state = CalculatorState::new_with_builtins();
        assert_eq!(
            Some(val(5.0)),
            process_input(&mut state, "5", false).unwrap()
        );
        assert_eq!(
            Some(val(3.75)),
            process_input(&mut state, "5 * -(2 + -3) / -4 + 5", false).unwrap()
        );
    }

    #[test]
    fn test_invalid_input_reports_syntax_error() {
        let mut state = CalculatorState::new_with_builtins();
        assert!(process_input(&mut state, "()", false).is_err());
    }

    #[test]
    fn test_variables_work() {
        let mut state = CalculatorState::new_with_builtins();

        assert!(process_input(&mut state, "variable", false).is_err());
        assert_eq!(
            None,
            process_input(&mut state, "variable = 1.234567", false).unwrap()
        );
        assert_eq!(
            Some(Value::rational(1234567, 1000000)),
            process_input(&mut state, "variable", false).unwrap()
        );
        assert!(process_input(&mut state, "variabl", false).is_err());
        assert!(process_input(&mut state, "variables", false).is_err());

        assert_eq!(
            None,
            process_input(&mut state, "variable=2", false).unwrap()
        );
        assert_eq!(
            Some(val(2.0)),
            process_input(&mut state, "variable", false).unwrap()
        );
    }

    #[test]
    fn test_invalid_variable_declaration_syntax_errors() {
        let mut state = CalculatorState::new_with_builtins();
        assert!(process_input(&mut state, "= 5", false).is_err());
        assert!(process_input(&mut state, "x =", false).is_err());
        assert!(process_input(&mut state, "= 5", false).is_err());
        assert!(process_input(&mut state, "x + = 5", false).is_err());
        assert!(process_input(&mut state, "x = 5 +", false).is_err());
        assert!(process_input(&mut state, "7est = 5", false).is_err()); // names can't start with numbers
    }

    #[test]
    fn test_functions_work() {
        let mut state = CalculatorState::new_with_builtins();

        assert_eq!(None, process_input(&mut state, "f() = 5", false).unwrap());
        assert_eq!(
            Some(val(5.0)),
            process_input(&mut state, "f()", false).unwrap()
        );

        assert_eq!(None, process_input(&mut state, "f(x) = 5x", false).unwrap());
        assert!(process_input(&mut state, "f()", false).is_err());
        assert_eq!(
            Some(val(-25.0)),
            process_input(&mut state, "f(-5)", false).unwrap()
        );

        assert_eq!(
            None,
            process_input(&mut state, "g(x, y) = f(x) / f(y)", false).unwrap()
        );
        assert_eq!(
            Some(val(-0.5)),
            process_input(&mut state, "g(-2, 4)", false).unwrap()
        );
    }

    #[test]
    fn test_invalid_function_declaration_syntax_errors() {
        let mut state = CalculatorState::new_with_builtins();
        assert!(process_input(&mut state, "f(,) = 5", false).is_err());
        assert!(process_input(&mut state, "f( = 5", false).is_err());
        assert!(process_input(&mut state, "f() =", false).is_err());
        assert!(process_input(&mut state, "f() + 5 = 5", false).is_err());
        assert!(process_input(&mut state, "f(2x) = 5", false).is_err());
        assert!(process_input(&mut state, "f(x) = 2x +", false).is_err());
        assert!(process_input(&mut state, "f(a,,b) = a + b", false).is_err());
        assert!(process_input(&mut state, "f(a,b,) = a + b", false).is_err());
        assert!(process_input(&mut state, "f(a,) = a", false).is_err());
        assert!(process_input(&mut state, "f(a b) = a + b", false).is_err());
    }

    // Convenience method to construct rationals for the tests
    fn val(x: f64) -> Value {
        let mut value = rug::Rational::new();
        value.assign_f64(x).unwrap();
        Value::Rational(value)
    }
}
