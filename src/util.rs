use std::ops::Range;

use anyhow::bail;
use rug::ops::PowAssign;

use crate::{
    state::{OutputFmt, Value},
    DEFAULT_PRECISION,
};

/// Given the slice `full` and its subslice `part`, this computes the range `r`
/// for which `full[r] == part`. `part` must be an actual subslice, otherwise this
/// makes no sense.
pub fn subslice_range(full: &str, part: &str) -> Range<usize> {
    let start = part.as_ptr() as usize - full.as_ptr() as usize;
    let end = (start + part.len()).min(full.len());
    start..end
}

/// Converts a Value to a user-friendly string format, ready to be displayed to the user.
/// If compact mode is used, only single-line outputs (no newlines) will be returned,
/// meaning some information will be lost (cut off).
pub fn stringify_output(value: Value, format: OutputFmt, compact: bool) -> anyhow::Result<String> {
    use std::fmt::Write;

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
                write!(&mut formatted, "= {prefix}{}", value.to_string_radix(radix)).unwrap();

                if !compact && formatted.len() >= 10 {
                    format!("{formatted} ({} {unit}))", formatted.len())
                } else {
                    formatted
                }
            } else {
                // Heuristic: if denominator is this big, it's probably not actually an exact result.
                // For compact results an even less optimistic heuristic is used because compact mode
                // would only print the rational, which is not useful if it's wrong.
                if (compact && value.denom() > &u32::MAX) || value.denom() > &u64::MAX {
                    format!(
                        "≈ {prefix}{}",
                        float_to_string(
                            &rational_to_decimal(&value, DEFAULT_PRECISION),
                            digits,
                            radix
                        )
                    )
                } else {
                    let (fract, floor) = value.clone().fract_floor(rug::Integer::new());

                    let mut result = String::new();

                    if compact {
                        write!(
                            &mut result,
                            "= {prefix}{} ≈ {prefix}{}",
                            value.to_string_radix(radix),
                            float_to_string(
                                &rational_to_decimal(&value, DEFAULT_PRECISION),
                                digits,
                                radix
                            )
                        )?;
                    } else {
                        write!(&mut result, "= {prefix}{}", value.to_string_radix(radix))?;
                        if floor != 0 {
                            write!(
                                &mut result,
                                "\n= {prefix}{} + {prefix}{}",
                                floor.to_string_radix(radix),
                                fract.to_string_radix(radix)
                            )?;
                        }
                        write!(
                            &mut result,
                            "\n≈ {prefix}{}",
                            float_to_string(
                                &rational_to_decimal(&value, DEFAULT_PRECISION),
                                digits,
                                radix
                            )
                        )?;
                    }
                    result
                }
            }
        }
        Value::Complex(value) => {
            let mut result = String::new();
            write!(&mut result, "≈ {prefix}")?;
            let (real, imag) = value.into_real_imag();
            let (real_s, imag_s) = (
                float_to_string(&real, digits, radix),
                float_to_string(&imag, digits, radix),
            );
            match (&real_s == "0", &imag_s == "0" || &imag_s == "-0") {
                (true, true) => write!(&mut result, "0")?,
                (true, false) => write!(&mut result, "{imag_s}i")?,
                (false, true) => write!(&mut result, "{real_s}")?,
                (false, false) if imag < 0 => write!(&mut result, "{real_s} - {}i", &imag_s[1..])?,
                (false, false) => write!(&mut result, "{real_s} + {imag_s}i")?,
            };
            result
        }

        Value::Boolean(value) => {
            format!("= {value}")
        }
    };
    Ok(result)
}

/// Converts a decimal value into a user-friendly string representation.
/// The default formatting implemented for rug types can be very rough,
/// preferring no leading zeros but adding numerous trailing zeros.
pub fn float_to_string(float: &rug::Float, digits: usize, radix: i32) -> String {
    let mut string = float.to_string_radix(radix, None);

    let negative = float < &0.0;

    // 1. Very likely that rug outputs a result with a negative exponent.
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

    // 2. Rug seems to output values at more resolution than it is accurate to. Technically 256 bits
    // provide 77 digits, but limiting is useful for two reasons:
    // - floating-point errors accumulate, but in practice not enough to show up in the first 50 digits.
    // - by trimming here before the removal of trailing zeroes, values very close to a round number
    //   are reduced to the desired round number.
    if string.len() > digits {
        string.drain(digits..);
    }

    if string.contains('.') {
        // 3. Remove trailing zeroes.
        string = string.trim_end_matches('0').to_owned();

        // 4. Remove trailing `,` to make outputs such as `1.` a bit nicer.
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
