pub mod parser;
pub mod state;
pub mod ast;

use std::io::BufRead;

use state::CalculatorState;

use anyhow::Result;

fn main() {
    let mut state = CalculatorState::default();

    // A simple REPL (read-eval-print-loop) interface
    for line in std::io::stdin().lock().lines() {
        if line.is_err() {
            return; // No more input
        }
        
        let line = line.unwrap().trim().to_lowercase();
        if let Err(e) = process_input(&mut state, line) {
            println!("{e}");
        }
    }
}

/// Process a line of input from the user, resulting either a direct evaluation
/// of an expression printed in the console, or a variable or a function added
/// to the calculator state.
/// ## Errors
/// If the input string was not syntactically valid, an error describing the
/// problem is returned.
fn process_input(state: &mut CalculatorState, input: String) -> Result<()> {
    let postfix = parser::infix_to_postfix_shunting_yard(&input)?;
    let syntax_tree = parser::postfix_to_ast(postfix)?;

    // TBD

    Ok(())
}