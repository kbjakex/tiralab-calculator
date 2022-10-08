#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    Power,
}

impl BinaryOperator {
    pub const fn precedence(self) -> i32 {
        match self {
            BinaryOperator::Add => 4,
            BinaryOperator::Subtract => 4,
            BinaryOperator::Divide => 5,
            BinaryOperator::Multiply => 5,
            BinaryOperator::Remainder => 5,
            BinaryOperator::Power => 6,
        }
    }

    pub const fn left_associative(self) -> bool {
        !matches!(self, BinaryOperator::Power)
    }

    /// Compute `lhs OP rhs`, where OP is a binary operator (self),
    /// and will always return a f64.
    pub fn apply(self, lhs: f64, rhs: f64) -> f64 {
        match self {
            BinaryOperator::Add => lhs + rhs,
            BinaryOperator::Subtract => lhs - rhs,
            BinaryOperator::Multiply => lhs * rhs,
            BinaryOperator::Divide => lhs / rhs,
            BinaryOperator::Power => lhs.powf(rhs),
            BinaryOperator::Remainder => lhs % rhs,
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperator {
    Negate,
}

impl UnaryOperator {
    pub fn apply(self, x: f64) -> f64 {
        match self {
            UnaryOperator::Negate => -x,
        }
    }
}
