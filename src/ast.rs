use flexstr::LocalStr;


#[repr(u8)]
#[derive(Clone, Copy)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Divide,
    Multiply
}

impl BinaryOperator {
    pub const fn precedence(self) -> i32 {
        match self {
            BinaryOperator::Add => 0,
            BinaryOperator::Subtract => 0,
            BinaryOperator::Divide => 1,
            BinaryOperator::Multiply => 1,
        }
    }

    pub fn left_associative(self) -> bool {
        match self {
            _ => true
        }
    }
}

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum UnaryOperator {
    Negate
}

pub enum AstNode {
    Constant {
        value: f64
    },
    FunctionCall {
        name: LocalStr,
    },
    VariableReference {
        name: LocalStr,
    },
    UnaryOperation { // Represents `OP(node)`, for example `-f(x)`
        node_index: u32,
        operation: UnaryOperator
    },
    BinaryOperation { // Represents `(lhs) OP (rhs)`, for example `1 + f(x)`
        lhs_node_index: u32,
        rhs_node_index: u32,
        operation: BinaryOperator
    }
}

/// Represents an abstract syntax tree
/// See: https://en.wikipedia.org/wiki/Abstract_syntax_tree
pub struct Ast {
    // Root node is at index 0.
    pub nodes: Vec<AstNode>
}

impl Ast {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new()
        }
    }
}