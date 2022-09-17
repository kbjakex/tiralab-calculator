use bevy_utils::HashMap;

use crate::ast::Ast; // Uses the excellent AHash instead of the default cryptographically secure hash


struct Function {
    pub definition: Ast
}

struct Variable {
    pub value: Ast
}

/// Contains all the state in the calculator; most importantly,
/// all functions and variables, and a mapping to them from their names.
#[derive(Default)]
pub struct CalculatorState {
    functions: HashMap<String, Function>,
    variables: HashMap<String, f64>
}
