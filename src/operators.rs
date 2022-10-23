use anyhow::{bail, Context};
use rug::ops::Pow;

use crate::{
    state::Value,
    util::{complex_pow, decimal_to_complex, promote_to_common_type, rational_pow},
};

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    Power,

    LessThan,
    LequalTo,
    GreaterThan,
    GequalTo,
    EqualTo,
    NequalTo,

    LogicalAnd,
    LogicalOr,

    BitAnd,
    BitOr,
    BitXor,
    BitLeftShift,
    BitRightShift,
}

impl BinaryOperator {
    /// If the array starts with the characters representing a binary
    /// operator, that operator is returned along with its byte length
    pub fn from_chars(chars: &[u8]) -> Option<(BinaryOperator, usize)> {
        use BinaryOperator::*;

        let result = match chars {
            &[b'+', ..] => (Add, 1),
            &[b'-', ..] => (Subtract, 1),
            &[b'*', ..] => (Multiply, 1),
            &[b'/', ..] => (Divide, 1),
            &[b'%', ..] => (Remainder, 1),
            &[b'^', ..] => (Power, 1),

            &[b'<', b'<', ..] => (BitLeftShift, 2),
            &[b'>', b'>', ..] => (BitRightShift, 2),

            &[b'<', b'=', ..] => (LequalTo, 2),
            &[b'>', b'=', ..] => (GequalTo, 2),
            &[b'=', b'=', ..] => (EqualTo, 2),
            &[b'!', b'=', ..] => (NequalTo, 2),
            &[b'<', ..] => (LessThan, 1),
            &[b'>', ..] => (GreaterThan, 1),

            &[b'&', b'&', ..] => (LogicalAnd, 2),
            &[b'|', b'|', ..] => (LogicalOr, 2),

            &[b'&', ..] => (BitAnd, 1),
            &[b'|', ..] => (BitOr, 1),
            &[b'x', b'o', b'r', ..] => (BitXor, 3),

            _ => return None,
        };

        Some(result)
    }

    pub const fn precedence(self) -> i32 {
        use BinaryOperator::*;
        // See https://en.cppreference.com/w/c/language/operator_precedence
        match self {
            LogicalOr => 0,
            LogicalAnd => 1,
            BitOr => 2,
            BitXor => 3,
            BitAnd => 4,
            EqualTo => 5,
            NequalTo => 5,
            LessThan => 6,
            LequalTo => 6,
            GreaterThan => 6,
            GequalTo => 6,
            BitLeftShift => 7,
            BitRightShift => 7,
            Add => 4,
            Subtract => 4,
            Divide => 5,
            Multiply => 5,
            Remainder => 5,
            Power => 6,
        }
    }

    pub const fn left_associative(self) -> bool {
        !matches!(self, BinaryOperator::Power)
    }

    /// Compute `lhs OP rhs`, where OP is a binary operator (self),
    /// and will always return a f64.
    pub fn apply(self, lhs: Value, rhs: Value, precision_bits: u32) -> anyhow::Result<Value> {
        use BinaryOperator::*;
        use Value::*;

        if matches!(self, Divide) {
            // Check for div by zero
            let dividing_by_zero = match &rhs {
                Decimal(x) => x == &0,
                Rational(x) => x == &0,
                Complex(x) => x == &0,
                Boolean(_) => false, // can't divide by boolean; checked later
            };
            if dividing_by_zero {
                bail!("Division by zero");
            }
        }

        let (lhs, rhs) = promote_to_common_type(&lhs, &rhs, precision_bits)
            .with_context(|| format!("Needed for '{lhs} {} {rhs}'", self.display_name()))?;

        match (lhs, rhs) {
            (Rational(lhs), Rational(rhs)) => {
                let result = match self {
                    Add => rug::Rational::from(lhs + rhs),
                    Subtract => rug::Rational::from(lhs - rhs),
                    Multiply => rug::Rational::from(lhs * rhs),
                    Divide => rug::Rational::from(lhs / rhs),
                    Remainder => rug::Rational::from(lhs / rhs),
                    Power => return rational_pow(lhs, &rhs, precision_bits),

                    LessThan => return Ok(Boolean(lhs < rhs)),
                    GreaterThan => return Ok(Boolean(lhs > rhs)),
                    LequalTo => return Ok(Boolean(lhs <= rhs)),
                    GequalTo => return Ok(Boolean(lhs >= rhs)),
                    EqualTo => return Ok(Boolean(lhs == rhs)),
                    NequalTo => return Ok(Boolean(lhs != rhs)),

                    other if lhs.is_integer() && rhs.is_integer() => match other {
                        BitAnd => rug::Rational::from(lhs.numer() & rhs.numer()),
                        BitOr => rug::Rational::from(lhs.numer() | rhs.numer()),
                        BitXor => rug::Rational::from(lhs.numer() ^ rhs.numer()),
                        BitLeftShift if rhs < i32::MAX => rug::Rational::from(lhs.numer() << rhs.numer().to_i32().unwrap()),
                        BitLeftShift => bail!("Left shift amount '{}' is too large", rhs.numer()),
                        BitRightShift if rhs < i32::MAX => rug::Rational::from(lhs.numer() >> rhs.numer().to_i32().unwrap()),
                        BitRightShift => bail!("Right shift amount '{}' is too large", rhs.numer()),
                        _ => unreachable!()
                    }

                    other => bail!("'{}' is not defined for real numbers", other.display_name()),
                };
                Ok(Rational(result))
            }
            (Decimal(lhs), Decimal(rhs)) => {
                let result = match self {
                    Add => rug::Float::from(lhs + rhs),
                    Subtract => rug::Float::from(lhs - rhs),
                    Multiply => rug::Float::from(lhs * rhs),
                    Divide => rug::Float::from(lhs / rhs),
                    Remainder => rug::Float::from(lhs % rhs),
                    Power => return complex_pow(decimal_to_complex(&lhs, precision_bits), &rhs),

                    LessThan => return Ok(Boolean(lhs < rhs)),
                    GreaterThan => return Ok(Boolean(lhs > rhs)),
                    LequalTo => return Ok(Boolean(lhs <= rhs)),
                    GequalTo => return Ok(Boolean(lhs >= rhs)),
                    EqualTo => return Ok(Boolean(lhs == rhs)),
                    NequalTo => return Ok(Boolean(lhs != rhs)),

                    other => bail!("'{}' is not defined for real numbers", other.display_name()),
                };
                if let Some(result) = result.to_rational() {
                    return Ok(Rational(result));
                }
                Ok(Decimal(result))
            }
            (Complex(lhs), Complex(rhs)) => {
                let result = match self {
                    Add => rug::Complex::from(lhs + rhs),
                    Subtract => rug::Complex::from(lhs - rhs),
                    Multiply => rug::Complex::from(lhs * rhs),
                    Divide => rug::Complex::from(lhs / rhs),
                    Remainder => bail!("Can't compute remainder (%) of a complex number"),
                    Power => rug::Complex::from(lhs.pow(rhs)),

                    EqualTo => return Ok(Boolean(lhs == rhs)),
                    NequalTo => return Ok(Boolean(lhs != rhs)),

                    other => bail!(
                        "'{}' is not defined for complex numbers",
                        other.display_name()
                    ),
                };
                if result.imag() == &0 {
                    // No imaginary part anymore: back to decimal or rational so f.e comparisons are available again.
                    let (result, _) = result.into_real_imag();
                    if let Some(rational) = result.to_rational() {
                        return Ok(Rational(rational));
                    }
                    return Ok(Decimal(result));
                }
                Ok(Complex(result))
            }
            (Boolean(lhs), Boolean(rhs)) => {
                let result = match self {
                    LogicalOr | BitOr => lhs || rhs,
                    LogicalAnd | BitAnd => lhs && rhs,
                    EqualTo => lhs == rhs,
                    NequalTo | BitXor => lhs != rhs,

                    other => bail!("'{}' is not defined for booleans", other.display_name()),
                };
                Ok(Boolean(result))
            }
            _ => unreachable!(),
        }
    }

    pub fn display_name(self) -> &'static str {
        use BinaryOperator::*;
        match self {
            Add => "+",
            Subtract => "-",
            Multiply => "*",
            Divide => "/",
            Remainder => "%",
            Power => "^",

            LessThan => "<",
            LequalTo => "<=",
            GreaterThan => ">",
            GequalTo => ">=",
            EqualTo => "==",
            NequalTo => "!=",

            LogicalAnd => "&&",
            LogicalOr => "||",

            BitAnd => "&",
            BitOr => "|",
            BitXor => "xor",
            BitLeftShift => "<<",
            BitRightShift => ">>",
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperator {
    Negate,
    Not,
}

impl UnaryOperator {
    pub fn apply(self, x: Value) -> anyhow::Result<Value> {
        use UnaryOperator::*;
        use Value::*;
        match (self, x) {
            (Negate, Decimal(x)) => Ok(Decimal(-x)),
            (Negate, Rational(x)) => Ok(Rational(-x)),
            (Negate, Complex(x)) => Ok(Complex(-x)),
            (Negate, Boolean(_)) => {
                bail!("Can't negate a boolean with `-`! Prefix with `!` to invert instead.")
            }

            (Not, Boolean(x)) => Ok(Boolean(!x)),
            (Not, other) => bail!("`!` is not defined for {}", other.type_name()),
        }
    }
}
