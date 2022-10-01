use flexstr::LocalStr;


#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
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

    pub const fn left_associative(self) -> bool {
        match self {
            _ => true
        }
    }

    /// Compute `lhs OP rhs`, where OP is a binary operator (self),
    /// and will always return a f64.
    pub fn apply(self, lhs: f64, rhs: f64) -> f64  {
        match self {
            BinaryOperator::Add => lhs + rhs,
            BinaryOperator::Subtract => lhs - rhs,
            BinaryOperator::Multiply => lhs * rhs,
            BinaryOperator::Divide => lhs / rhs,
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperator {
    Negate
}

#[derive(Debug)]
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
    /// Represents `OP(node)`, for example `-f(x)`.
    UnaryOperation {
        node_index: u32,
        operation: UnaryOperator
    },
    /// Represents `(lhs) OP (rhs)`, for example `1 + f(x)`.
    BinaryOperation {
        lhs_node_index: u32,
        rhs_node_index: u32,
        operation: BinaryOperator
    }
}

/// Represents an abstract syntax tree
/// See: https://en.wikipedia.org/wiki/Abstract_syntax_tree
#[derive(Debug, Default)]
pub struct Ast {
    // Root node is at index 0.
    pub nodes: Vec<AstNode>
}