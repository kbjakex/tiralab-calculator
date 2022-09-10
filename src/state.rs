use bevy_utils::HashMap;

use crate::ast::Ast; // Uses the excellent AHash instead of the default cryptographically secure hash


struct Function {
    pub definition: Ast
}

struct Variable {
    pub value: Ast
}

struct SymbolTable {
    functions: HashMap<String, Function>,
    variables: HashMap<String, f64>
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            functions: HashMap::default(),
            variables: HashMap::default(),
        }
    }
}

pub struct CalculatorState {
    sym_table: SymbolTable
}

impl CalculatorState {
    pub fn new() -> Self {
        Self {
            sym_table: SymbolTable::new()
        }
    }
}

