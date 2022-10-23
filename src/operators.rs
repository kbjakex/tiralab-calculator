use anyhow::{bail, Context};
use rug::ops::Pow;

use crate::{state::Value, util::{promote_to_common_type, rational_pow, decimal_to_complex, complex_pow}};

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
}

impl BinaryOperator {
    pub const fn precedence(self) -> i32 {
        use BinaryOperator::*;
        // See https://en.cppreference.com/w/c/language/operator_precedence
        match self {
            LogicalOr => 0,
            LogicalAnd => 1,
            EqualTo => 2,
            NequalTo => 2,
            LessThan => 3,
            LequalTo => 3,
            GreaterThan => 3,
            GequalTo => 3,
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
                    LogicalOr => lhs || rhs,
                    LogicalAnd => lhs && rhs,
                    EqualTo => lhs == rhs,
                    NequalTo => lhs != rhs,
                    other => bail!("'{}' is not defined for booleans", other.display_name()),
                };
                Ok(Boolean(result))
            }
            _ => unreachable!(),
        }
    }

    fn display_name(self) -> &'static str {
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
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperator {
    Negate,
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
        }
    }
}
