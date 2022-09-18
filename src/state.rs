use bevy_utils::HashMap; // Uses the excellent AHash instead of the default cryptographically secure hash

use crate::ast::Ast; 

pub struct Function {
    pub definition: Ast
}

/// Contains all the state in the calculator; most importantly,
/// all functions and variables, and a mapping to them from their names.
#[derive(Default)]
pub struct CalculatorState {
    pub functions: HashMap<String, Function>,
    pub variables: HashMap<String, f64>
}
