use std::ops::Range;

use anyhow::bail;
use rug::ops::{PowAssign, AddFrom};

use crate::{
    state::{OutputFmt, Value},
    PRECISION,
};

/// ANSI color codes for some foreground/background colors.
pub mod ansi {
    pub const RESET : &str = "\x1b[0m";

    pub mod fg {
        pub const GRAY : &str = "\x1b[38;5;8m";
        pub const RED : &str = "\x1b[38;5;1m";
        pub const CYAN : &str = "\x1b[38;5;6m";
        pub const LIGHT_CYAN_BOLD : &str = "\x1b[38;5;14;1m";
        pub const PURPLE : &str = "\x1b[38;5;13m";
        pub const PURPLE_BOLD : &str = "\x1b[38;5;13;1m";
        pub const GOLD_BOLD : &str = "\x1b[38;5;3;1m";
        pub const BLUE : &str = "\x1b[38;5;12m";
        pub const BLUE_BOLD : &str = "\x1b[38;5;12;1m";
        pub const LIGHT_GRAY_248 : &str = "\x1b[38;5;248m";
    }

    pub mod bg {
        pub const DARK_RED : &str = "\x1b[48;5;52m";
    }
}

/// Given the slice `full` and its subslice `part`, this computes the range `r`
/// for which `full[r] == part`. `part` must be an actual subslice, otherwise this
/// makes no sense and will probably error.
pub fn subslice_range(full: &str, part: &str) -> Range<usize> {
    let start = part.as_ptr() as usize - full.as_ptr() as usize;
    let end = (start + part.len()).min(full.len());
    start..end
}

/// Converts a Value to a user-friendly string format, ready to be displayed to the user.
/// If compact mode is used, only single-line outputs (no newlines) will be returned,
/// meaning some information will be lost (cut off).
#[cfg_attr(coverage, no_coverage)]
pub fn stringify_output(value: Value, format: OutputFmt, compact: bool) -> anyhow::Result<String> {
    let (radix, prefix, unit) = match format {
        OutputFmt::Base10 => (10, "", "digits"),
        OutputFmt::Binary => (2, "0b", "bits"),
        OutputFmt::Hex => (16, "0x", "digits"),
    };
    let digits = if compact { 18 } else { 50 };

    let result = match value {
        Value::Decimal(value) => {
            format!("≈ {prefix}{}", float_to_string(&value, digits, radix))
        }
        
        Value::Rational(value) => {
            if value.is_integer() {
                let mut formatted = String::new();

                use std::fmt::Write;
                write!(&mut formatted, "= {prefix}{}", value.to_string_radix(radix)).unwrap();

                if !compact && formatted.len() >= 10 {
                    format!("{formatted} ({} {unit})", formatted.len() - 2)
                } else {
                    formatted
                }
            } else {
                stringify_rational(value, digits, radix, prefix, compact)?
            }
        }

        Value::Complex(value) => {
            stringify_complex(value, digits, radix, prefix)?
        }

        Value::Boolean(value) => {
            format!("= {value}")
        }
    };
    Ok(result)
}

#[cfg_attr(coverage, no_coverage)]
fn stringify_complex(value: rug::Complex, digits: usize, radix: i32, prefix: &str) -> anyhow::Result<String> {
    use std::fmt::Write;
    let mut result = String::new();
    write!(&mut result, "≈ {prefix}")?;
    let (real, imag) = value.into_real_imag();
    let (real_s, imag_s) = (
        float_to_string(&real, digits, radix),
        float_to_string(&imag, digits, radix),
    );
    match (&real_s == "0" || &real_s == "-0", &imag_s == "0" || &imag_s == "-0") {
        (true, true) => write!(&mut result, "0")?,
        (true, false) => write!(&mut result, "{imag_s}i")?,
        (false, true) => write!(&mut result, "{real_s}")?,
        (false, false) if imag < 0 => write!(&mut result, "{real_s} - {}i", &imag_s[1..])?,
        (false, false) => write!(&mut result, "{real_s} + {imag_s}i")?,
    };
    Ok(result)
}

#[cfg_attr(coverage, no_coverage)]
fn stringify_rational(value: rug::Rational, digits: usize, radix: i32, prefix: &str, compact: bool) -> anyhow::Result<String> {
    use std::fmt::Write;
    
    let approx = float_to_string(&rational_to_decimal(&value, PRECISION), digits, radix);
    
    // Heuristic: if denominator is this big, it's probably not actually an exact result.
    // For compact results an even less optimistic heuristic is used because compact mode
    // would only print the rational, which is not useful if it's wrong.
    if (compact && value.denom() > &u32::MAX) || value.denom() > &u64::MAX {
        return Ok(format!("≈ {prefix}{approx}"));
    }
    if compact {
        return Ok(format!("= {prefix}{} ≈ {prefix}{approx}", value.to_string_radix(radix)));
    }

    let mut result = String::new();
    write!(&mut result, "= {prefix}{}", value.to_string_radix(radix))?;
    
    let (fract, floor) = value.clone().fract_floor(rug::Integer::new());
    if floor != 0 {
        write!(
            &mut result,
            "\n= {prefix}{} + {prefix}{}",
            floor.to_string_radix(radix),
            fract.to_string_radix(radix)
        )?;
    }

    write!(&mut result, "\n≈ {prefix}{approx}")?;

    Ok(result)
}

/// Converts a decimal value into a user-friendly string representation.
/// The default formatting implemented for rug types can be very rough,
/// preferring no leading zeros but adding numerous trailing zeros.
#[cfg_attr(coverage, no_coverage)]
pub fn float_to_string(float: &rug::Float, digits: usize, radix: i32) -> String {
    // 1. Because floats are inherently lossy and cannot represent all values exactly,
    // sometimes values are printed wrong; for example 5.2 as 5.199999999999... .
    // Add a tiny amount to combat this; well outside the range of displayed numbers
    // so that actual output precision is not impacted.
    let mut float = float.clone();
    if float > 0 {
        float.add_from(1e-50);
    } else {
        float.add_from(-1e-60)
    }

    let mut string = float.to_string_radix(radix, None);

    let negative = float < 0.0;

    // 2. Very likely that rug outputs a result with a negative exponent.
    // Unshift the digits to do away with it.
    // Code note: unfortunately Rust currently forces you to nest ifs like this with if-lets.
    if let Some((num, exponent)) = string.split_once('e') {
        if let Ok(exponent) = exponent.parse::<i32>() {
            if exponent < 0 {
                // Get rid of old decimal point
                let (mut before, after) = num.split_once('.').unwrap();
                if negative {
                    before = &before[1..];
                }

                string = "0.".to_owned() + &"0".repeat((-exponent - 1) as usize) + before + after;

                if negative {
                    string.insert(0, '-');
                }
            }
        }
    }

    // 3. Rug seems to output values at more resolution than it is accurate to. Technically 256 bits
    // provide 77 digits, but limiting is useful for two reasons:
    // - floating-point errors accumulate, but in practice not enough to show up in the first 50 digits.
    // - by trimming here before the removal of trailing zeroes, values very close to a round number
    //   are reduced to the desired round number.
    if string.len() > digits {
        string.drain(digits..);
    }

    if string.contains('.') {
        // 4. Remove trailing zeroes.
        string = string.trim_end_matches('0').to_owned();

        // 5. Remove trailing `,` to make outputs such as `1.` a bit nicer.
        string = string.trim_end_matches('.').to_owned();
    }

    string
}

/// Convert values such that they have the same type (type being rational or decimal or ...).
/// Fails if there doesn't exist a non-opinionated conversion.
pub fn promote_to_common_type(
    lhs: &Value,
    rhs: &Value,
    precision_bits: u32,
) -> anyhow::Result<(Value, Value)> {
    use Value::*;
    // Entering combinatorial explosion territory...
    let result = match (lhs, rhs) {
        (Decimal(lhs), Rational(rhs)) => (
            Decimal(lhs.clone()),
            Decimal(rational_to_decimal(rhs, precision_bits)),
        ),
        (Rational(lhs), Decimal(rhs)) => (
            Decimal(rational_to_decimal(lhs, precision_bits)),
            Decimal(rhs.clone()),
        ),
        (Decimal(lhs), Complex(rhs)) => (
            Complex(decimal_to_complex(lhs, precision_bits)),
            Complex(rhs.clone()),
        ),
        (Rational(lhs), Complex(rhs)) => (
            Complex(rational_to_complex(lhs, precision_bits)),
            Complex(rhs.clone()),
        ),
        (Complex(lhs), Decimal(rhs)) => (
            Complex(lhs.clone()),
            Complex(decimal_to_complex(rhs, precision_bits)),
        ),
        (Complex(lhs), Rational(rhs)) => (
            Complex(lhs.clone()),
            Complex(rational_to_complex(rhs, precision_bits)),
        ),

        (Boolean(lhs), Boolean(rhs)) => (Boolean(lhs.clone()), Boolean(rhs.clone())),
        (Boolean(_), rhs) => bail!(
            "Can't implicitly convert between {} and boolean",
            rhs.type_name()
        ),
        (lhs, Boolean(_)) => bail!(
            "Can't implicitly convert between {} and boolean",
            lhs.type_name()
        ),

        // If both are of the same type already.
        (lhs, rhs) => (lhs.clone(), rhs.clone()),
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
pub fn rational_pow(
    mut lhs: rug::Rational,
    rhs: &rug::Rational,
    precision_bits: u32,
) -> anyhow::Result<Value> {
    if lhs == 0.0 && rhs <= &0 {
        // `0^(-x)` <=> `1/(0^x)`, which will cause a division by zero.
        bail!("Division by zero");
    }

    let denom = rhs.denom();
    if denom == &1 {
        // Integer!
        let numer_ref = rhs.numer();
        if let Some(int_exp) = numer_ref.to_i32() {
            lhs.pow_assign(int_exp);
            return Ok(Value::Rational(lhs));
        }

        // If this really fails, the exponent is over two billion
        // which definitely wouldn't work well with floats so just give up
        bail!("Exponent {numer_ref} too big!")
    }

    // This is a lot of allocations! Probably could be done with less?
    let base = rational_to_complex(&lhs, precision_bits);
    let exponent = rational_to_decimal(rhs, precision_bits);

    complex_pow(base, &exponent)
}

/// Computes c<sup>d</sup> where `c` is a complex number and `d` a decimal value.
/// Result will be converted back to decimal / rational where possible.
pub fn complex_pow(mut base: rug::Complex, exponent: &rug::Float) -> anyhow::Result<Value> {
    base.pow_assign(exponent);

    if base.imag() == &0 {
        let (decimal, _) = base.into_real_imag();
        if let Some(rational) = decimal.to_rational() {
            return Ok(Value::Rational(rational));
        }
        return Ok(Value::Decimal(decimal));
    }

    Ok(Value::Complex(base))
}

/// Converts from rational to decimal at the desired precision.
pub fn rational_to_decimal(rational: &rug::Rational, precision_bits: u32) -> rug::Float {
    // TODO? I couldn't find a direct way to convert rational to float, but
    // adding a rational to a zero float accomplishes the same
    rug::Float::new(precision_bits) + rational
}

pub fn rational_to_complex(rational: &rug::Rational, precision_bits: u32) -> rug::Complex {
    rug::Complex::new(precision_bits) + rational
}

pub fn decimal_to_complex(decimal: &rug::Float, precision_bits: u32) -> rug::Complex {
    rug::Complex::new(precision_bits) + decimal
}

/// Functions to help with writing tests
#[cfg(test)]
pub mod testing {
    use crate::{state::Value, PRECISION};

    use super::promote_to_common_type;

    // Convenience functions to create values of specific types, to reduce verbosity.

    pub fn float(value: f64) -> Value {
        Value::Decimal(rug::Float::with_val(PRECISION, value))
    }

    pub fn rational(numer: i32, denom: u32) -> Value {
        Value::Rational(rug::Rational::from((numer, denom)))
    }

    pub fn complex(real: f64, imag: f64) -> Value {
        Value::Complex(rug::Complex::with_val(PRECISION, (real, imag)))
    }

    pub fn bool(value: bool) -> Value {
        Value::Boolean(value)
    }

    #[cfg_attr(coverage, no_coverage)]
    pub fn approx_eq(value: Value, target: Value, epsilon: f64) -> bool {
        let (value, target) = promote_to_common_type(&value, &target, PRECISION).unwrap();

        match (value, target) {
            (Value::Decimal(lhs), Value::Decimal(rhs)) => lhs.positive_diff(&rhs) <= epsilon,
            (Value::Rational(lhs), Value::Rational(rhs)) => lhs == rhs, // rationals are exact
            (Value::Complex(lhs), Value::Complex(rhs)) => lhs.real().clone().positive_diff(rhs.real()) <= epsilon 
                                                                         && lhs.imag().clone().positive_diff(rhs.imag()) <= epsilon,
            (Value::Boolean(lhs), Value::Boolean(rhs)) => lhs == rhs,
            _ => unreachable!()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{PRECISION, util::testing::{float, rational, complex, bool, approx_eq}, state::Value};

    use super::{promote_to_common_type, rational_pow};

    // Type promotion can be tested exhaustively, so the tests just test every single possible pair of inputs
    // and verify that they produce the intended results. Precision bits do not affect the outcome.

    #[test]
    fn test_valid_type_promotions_work() {
        fn promote(lhs: &Value, rhs: &Value) -> (Value, Value) {
            promote_to_common_type(&lhs, &rhs, PRECISION).unwrap()
        }
        let float = float(0.0);
        let complex = complex(0.0, 0.0);
        let rational = rational(0, 1);
        let bool = bool(false);

        assert!(matches!(promote(&float, &float),       (Value::Decimal(..), Value::Decimal(..))));
        assert!(matches!(promote(&rational, &rational), (Value::Rational(..), Value::Rational(..))));
        assert!(matches!(promote(&complex, &complex),   (Value::Complex(..), Value::Complex(..))));
        assert!(matches!(promote(&bool, &bool),         (Value::Boolean(..), Value::Boolean(..))));

        assert!(matches!(promote(&float, &rational),    (Value::Decimal(..), Value::Decimal(..))));
        assert!(matches!(promote(&rational, &float),    (Value::Decimal(..), Value::Decimal(..))));

        assert!(matches!(promote(&float, &complex),     (Value::Complex(..), Value::Complex(..))));
        assert!(matches!(promote(&complex, &float),     (Value::Complex(..), Value::Complex(..))));

        assert!(matches!(promote(&rational, &complex),     (Value::Complex(..), Value::Complex(..))));
        assert!(matches!(promote(&complex, &rational),     (Value::Complex(..), Value::Complex(..))));

        assert!(matches!(promote(&bool, &bool),         (Value::Boolean(..), Value::Boolean(..))));
    }

    #[test]
    fn test_invalid_type_promotions_fail() {
        let float = float(0.0);
        let complex = complex(0.0, 0.0);
        let rational = rational(0, 1);
        let bool = bool(false);

        assert!(promote_to_common_type(&float, &bool, PRECISION).is_err());
        assert!(promote_to_common_type(&bool, &float, PRECISION).is_err());
        assert!(promote_to_common_type(&complex, &bool, PRECISION).is_err());
        assert!(promote_to_common_type(&bool, &complex, PRECISION).is_err());
        assert!(promote_to_common_type(&rational, &bool, PRECISION).is_err());
        assert!(promote_to_common_type(&bool, &rational, PRECISION).is_err());
    }

    #[test]
    fn test_rational_pow() {
        fn val(x: f64) -> rug::Rational {
            let mut rational = rug::Rational::new();
            rational.assign_f64(x).unwrap();
            rational
        }
        
        // Tricky to test: practically infinite possible inputs, so focus on edge cases instead

        assert!(rational_pow(val(0.0), &val(0.0), PRECISION).is_err()); // 0^0 is undefined
        assert!(rational_pow(val(0.0), &val(-1.0), PRECISION).is_err()); // div by zero, because 0^(-x) <=> 1/(0^x) <=> 1/0
        
        
        assert!(approx_eq(rational_pow(val(1000.0), &val(0.0), PRECISION).unwrap(), rational(1,1), 0.0)); // x^0 = 1
        assert!(approx_eq(rational_pow(val(0.0), &val(1000.0), PRECISION).unwrap(), rational(0,1), 0.0)); // 0^x = 0

        assert!(approx_eq(rational_pow(val(-1.0), &val(2.5), PRECISION).unwrap(), complex(0.0, 1.0), 0.00001)); // (-1)^2.5 = i
        assert!(approx_eq(rational_pow(val(-1.0), &val(-2.5), PRECISION).unwrap(), complex(0.0, -1.0), 0.00001)); // (-1)^-2.5 = -i

        assert!(approx_eq(rational_pow(val(1.0), &val(10000.0), PRECISION).unwrap(), rational(1, 1), 0.00001)); // 1^x = 1
        assert!(approx_eq(rational_pow(val(-1.0), &val(10001.0), PRECISION).unwrap(), rational(-1, 1), 0.00001)); // (-1)^(2n+1) = -1
    }
}