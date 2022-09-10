pub mod parser;
pub mod state;
pub mod ast;

use std::io::BufRead;

use state::CalculatorState;

use anyhow::Result;

fn main() {
    let mut state = CalculatorState::new();

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

fn process_input(state: &mut CalculatorState, input: String) -> Result<()> {
    let postfix = parser::infix_to_postfix_shunting_yard(&input)?;

    Ok(())
}