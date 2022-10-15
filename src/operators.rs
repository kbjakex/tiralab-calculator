use anyhow::bail;
use rug::ops::{Pow, PowAssign};

use crate::state::Value;

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

        match promote_to_common_type(lhs, rhs, precision_bits)? {
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
                    
                    other => bail!("'{}' is not defined for real numbers", other.display_name())
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
                    Power => rug::Float::from(lhs.pow(rhs)),

                    LessThan => return Ok(Boolean(lhs < rhs)),
                    GreaterThan => return Ok(Boolean(lhs > rhs)),
                    LequalTo => return Ok(Boolean(lhs <= rhs)),
                    GequalTo => return Ok(Boolean(lhs >= rhs)),
                    EqualTo => return Ok(Boolean(lhs == rhs)),
                    NequalTo => return Ok(Boolean(lhs != rhs)),

                    other => bail!("'{}' is not defined for real numbers", other.display_name())
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

                    other => bail!("'{}' is not defined for complex numbers", other.display_name())
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
                    other => bail!("'{}' is not defined for booleans", other.display_name())
                };
                Ok(Boolean(result))
            }
            _ => unreachable!(),
        }
    }

    fn display_name(self) -> &'static str {
        use BinaryOperator::*;
        match self {
            Add => "add (+)",
            Subtract => "subtract (-)",
            Multiply => "multiply (*)",
            Divide => "divide (/)",
            Remainder => "remainder (%)",
            Power => "power (^)",
            
            LessThan => "less than (<)",
            LequalTo => "less or equal to (<=)",
            GreaterThan => "greater than (>)",
            GequalTo => "greater or equal to (>=)",
            EqualTo => "equal to (==)",
            NequalTo => "not equal to (!=)",

            LogicalAnd => "logical and (&&)",
            LogicalOr => "logical or (||)",
            
        }
    }
}

/// Convert values such that they have the same type (type being rational or decimal or ...).
/// Fails if there doesn't exist a non-opinionated conversion.
fn promote_to_common_type(
    lhs: Value,
    rhs: Value,
    precision_bits: u32,
) -> anyhow::Result<(Value, Value)> {
    use Value::*;
    // Entering combinatorial explosion territory...
    let result = match (lhs, rhs) {
        (Decimal(lhs), Rational(rhs)) => (
            Decimal(lhs),
            Decimal(rational_to_decimal(&rhs, precision_bits)),
        ),
        (Rational(lhs), Decimal(rhs)) => (
            Decimal(rational_to_decimal(&lhs, precision_bits)),
            Decimal(rhs),
        ),
        (Decimal(lhs), Complex(rhs)) => (
            Complex(decimal_to_complex(&lhs, precision_bits)),
            Complex(rhs),
        ),
        (Rational(lhs), Complex(rhs)) => (
            Complex(rational_to_complex(&lhs, precision_bits)),
            Complex(rhs),
        ),
        (Complex(lhs), Decimal(rhs)) => (
            Complex(lhs),
            Complex(decimal_to_complex(&rhs, precision_bits)),
        ),
        (Complex(lhs), Rational(rhs)) => (
            Complex(lhs),
            Complex(rational_to_complex(&rhs, precision_bits)),
        ),

        (Boolean(lhs), Boolean(rhs)) => (Boolean(lhs), Boolean(rhs)),
        (Boolean(_), other) | (other, Boolean(_)) => bail!(
            "Can't implicitly convert between {} and boolean",
            other.type_name()
        ),

        // If both are of the same type already.
        (lhs, rhs) => (lhs, rhs),
    };

    Ok(result)
}

/// There is no built-in `pow(rational, rational)` in rug, very understandably: it is a tricky problem.
/// a<sup>b/c</sup> is not the same as (a<sup>b</sup>)<sup>1/c</sup> or (a<sup>1/c</sup>)<sup>b</sup>;
/// consider (-1)<sup>2/3</sup> for example, which results in a complex number equal to cos(2pi/3) + i sin(2pi/3).
///
/// Because of this: attempt to stay in rational domain by first checking if rhs is an integer,
/// but otherwise, resort to an approximate solution with either a real or a complex number.
///
/// Better solutions welcome!
fn rational_pow(
    mut lhs: rug::Rational,
    rhs: &rug::Rational,
    precision_bits: u32,
) -> anyhow::Result<Value> {
    let denom = rhs.denom();
    if denom == &1 {
        // Integer!
        let numer_ref = rhs.numer();
        if let Some(int_exp) = numer_ref.to_i32() {
            lhs.pow_assign(int_exp);
            return Ok(Value::Rational(lhs));
        } else if let Some(uint_exp) = numer_ref.to_u32() {
            lhs.pow_assign(uint_exp);
            return Ok(Value::Rational(lhs));
        }

        // Should this fail, or should it just silently convert to a decimal instead?...
        bail!("Exponent {numer_ref} too big!")
    }

    // This is a lot of allocations! Probably could be done with less?
    let mut as_complex = rational_to_complex(&lhs, precision_bits);
    as_complex.pow_assign(rational_to_decimal(rhs, precision_bits));

    if as_complex.imag() == &0 {
        let (decimal, _) = as_complex.into_real_imag();
        if let Some(rational) = decimal.to_rational() {
            return Ok(Value::Rational(rational));
        }
        return Ok(Value::Decimal(decimal))
    }

    Ok(Value::Complex(as_complex))
}

/// Converts from rational to decimal at the desired precision.
pub fn rational_to_decimal(rational: &rug::Rational, precision_bits: u32) -> rug::Float {
    // TODO? I couldn't find a direct way to convert rational to float, but
    // adding a rational to a zero float accomplishes the same
    rug::Float::new(precision_bits) + rational
}

pub fn rational_to_complex(rational: &rug::Rational, precision_bits: u32) -> rug::Complex {
    // See the comment in rational_to_decimal about this.
    rug::Complex::new(precision_bits) + rational
}

/// Converts from decimal to complex at the desired precision.
pub fn decimal_to_complex(decimal: &rug::Float, precision_bits: u32) -> rug::Complex {
    // See the comment in rational_to_decimal about this.
    rug::Complex::new(precision_bits) + decimal
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
