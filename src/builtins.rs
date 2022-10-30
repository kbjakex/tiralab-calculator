// All the built-in functions.

use anyhow::{bail, Context};
use bevy_utils::HashMap;
use rug::Assign;

use crate::{
    operators::BinaryOperator,
    state::{Value, Variable},
    util::promote_to_common_type,
    PRECISION,
};

pub type BuiltinFnPtr = fn(&[Value], u32) -> anyhow::Result<Value>;

/// If a builtin function exists with the given name, a function pointer to
/// that function is returned along with its expected parameter count.
/// The parameter count will be usize::MAX if it takes a variable number of
/// parameters.
#[rustfmt::skip]
#[cfg_attr(coverage, no_coverage)]
pub fn resolve_builtin_fn_call(name: &str) -> Option<(BuiltinFnPtr, usize)> {
    let (fn_ptr, param_count) = match name {
        "sqrt"  => (sqrt as BuiltinFnPtr, 1),
        "cbrt"  => (cbrt as BuiltinFnPtr, 1),
        "sin"   => (sin as BuiltinFnPtr, 1),
        "cos"   => (cos as BuiltinFnPtr, 1),
        "tan"   => (tan as BuiltinFnPtr, 1),
        "asin" | "arcsin"  => (asin as BuiltinFnPtr, 1),
        "acos" | "arccos"  => (acos as BuiltinFnPtr, 1),
        "atan" | "arctan"  => (atan as BuiltinFnPtr, 1),
        "exp"   => (exp as BuiltinFnPtr, 1),
        "ln"    => (ln as BuiltinFnPtr, 1),
        "log10" => (log10 as BuiltinFnPtr, 1),
        "log2"  => (log2 as BuiltinFnPtr, 1),

        "gcd"   => (gcd as BuiltinFnPtr, 2),
        "lcm"   => (lcm as BuiltinFnPtr, 2),

        "abs"   => (abs as BuiltinFnPtr, 1),
        "floor" => (floor as BuiltinFnPtr, 1),
        "round" => (round as BuiltinFnPtr, 1),
        "ceil"  => (ceil as BuiltinFnPtr, 1),
        "frac"  => (frac as BuiltinFnPtr, 1),
        "int"   => (int as BuiltinFnPtr, 1), 
        "min"   => (min as BuiltinFnPtr, usize::MAX),
        "max"   => (max as BuiltinFnPtr, usize::MAX),
        "avg"   => (avg as BuiltinFnPtr, usize::MAX),

        // Output format specifiers
        "dec"   => (noop as BuiltinFnPtr, 1),
        "bin"   => (noop as BuiltinFnPtr, 1),
        "hex"   => (noop as BuiltinFnPtr, 1),

        _ => return None,
    };
    Some((fn_ptr, param_count))
}

fn noop(parameters: &[Value], _precision_bits: u32) -> anyhow::Result<Value> {
    Ok(parameters[0].clone())
}

fn sqrt(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() != 1 {
        // Typo for consistency :)
        bail!("sqrt() takes 1 parameters, {} provided", parameters.len());
    }

    let parameter = parameters[0].clone();
    if matches!(parameter, Value::Boolean(..)) {
        bail!("sqrt() not defined for {}", parameter.type_name());
    }

    let exponent = rug::Rational::from((1, 2));

    BinaryOperator::Power.apply(parameter, Value::Rational(exponent), precision_bits)
}

fn cbrt(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() != 1 {
        bail!("cbrt() takes 1 parameters, {} provided", parameters.len());
    }

    let parameter = parameters[0].clone();
    if matches!(parameter, Value::Boolean(..)) {
        bail!("cbrt() not defined for {}", parameter.type_name());
    }

    let exponent = rug::Rational::from((1, 3));

    BinaryOperator::Power.apply(parameter, Value::Rational(exponent), precision_bits)
}

fn gcd(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() != 2 {
        bail!("gcd() takes 2 parameters, {} provided", parameters.len());
    }
    let (lhs, rhs) = promote_to_common_type(&parameters[0], &parameters[1], precision_bits)?;
    let result = match (lhs, rhs) {
        (Value::Rational(lhs), Value::Rational(rhs)) if lhs.is_integer() && rhs.is_integer() => {
            let lhs = lhs.into_numer_denom().0; // numerator
            Value::Rational(rug::Rational::from(lhs.gcd(rhs.numer())))
        },
        
        (other, _) => bail!("gcd() not defined for {}", other.type_name()),
    };
    Ok(result)
}

fn lcm(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() != 2 {
        bail!("lcm() takes 2 parameters, {} provided", parameters.len());
    }
    let (lhs, rhs) = promote_to_common_type(&parameters[0], &parameters[1], precision_bits)?;
    let result = match (lhs, rhs) {
        (Value::Rational(lhs), Value::Rational(rhs)) if lhs.is_integer() && rhs.is_integer() => {
            let lhs = lhs.into_numer_denom().0; // numerator
            Value::Rational(rug::Rational::from(lhs.lcm(rhs.numer())))
        },
        
        (other, _) => bail!("lcm() not defined for {}", other.type_name()),
    };
    Ok(result)
}

/// 'avg()' takes a variable number of parameters (> 0) unlike most other functions.
fn avg(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() == 0 {
        bail!("avg() takes at least 1 parameter, 0 provided");
    }

    let mut sum = parameters[0].clone();
    for (i, next) in (&parameters[1..]).iter().enumerate() {
        let (lhs, rhs) = promote_to_common_type(&sum, next, precision_bits).with_context(|| {
            format!("In avg() with parameters '{}' and '{next}'", parameters[i])
        })?;

        sum = BinaryOperator::Add.apply(lhs, rhs, precision_bits)?;
    }

    let count = rug::Rational::from((parameters.len() as u32, 1));
    let result = BinaryOperator::Divide.apply(sum, Value::Rational(count), precision_bits)?;

    Ok(result)
}

fn min(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() == 0 {
        bail!("min() takes at least 1 parameter, 0 provided");
    }

    let mut result = parameters[0].clone();
    for (i, next) in (&parameters[1..]).iter().enumerate() {
        let (lhs, rhs) = promote_to_common_type(&result, next, precision_bits).with_context(|| {
            format!("In min() with parameters '{}' and '{next}'", parameters[i])
        })?;

        result = match (lhs, rhs) {
            (Value::Decimal(lhs), Value::Decimal(rhs)) => Value::Decimal(lhs.min(&rhs)),
            (Value::Rational(lhs), Value::Rational(rhs)) => Value::Rational(lhs.min(rhs)),

            (other, _) => bail!("min() not defined for {}", other.type_name()),
        }
    }

    Ok(result)
}

fn max(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() == 0 {
        bail!("max() takes at least 1 parameter, 0 provided");
    }

    let mut result = parameters[0].clone();
    for (i, next) in (&parameters[1..]).iter().enumerate() {
        let (lhs, rhs) = promote_to_common_type(&result, next, precision_bits).with_context(|| {
            format!("In max() with parameters '{}' and '{next}'", parameters[i])
        })?;

        result = match (lhs, rhs) {
            (Value::Decimal(lhs), Value::Decimal(rhs)) => Value::Decimal(lhs.max(&rhs)),
            (Value::Rational(lhs), Value::Rational(rhs)) => Value::Rational(lhs.max(rhs)),

            (other, _) => bail!("max() not defined for {}", other.type_name()),
        }
    }

    Ok(result)
}

fn frac(parameters: &[Value], _precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() == 0 {
        bail!("frac() takes 1 parameters, 0 provided");
    }
    let result = match parameters[0].clone() {
        Value::Decimal(x) => Value::Decimal(x.fract()),
        Value::Rational(x) if x < 0 => Value::Rational(-(-x).fract_floor(rug::Integer::new()).0),
        Value::Rational(x) => Value::Rational(x.fract_floor(rug::Integer::new()).0),
        other => bail!("frac() not defined for {}", other.type_name()),
    };
    Ok(result)
}

fn int(parameters: &[Value], _precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() == 0 {
        bail!("int() takes 1 parameters, 0 provided");
    }
    let result = match parameters[0].clone() {
        Value::Decimal(x) => Value::Decimal(x.trunc()),
        Value::Rational(x) => Value::Rational(x.trunc()),
        Value::Boolean(bool) => Value::Rational(rug::Rational::from((bool as i32, 1))),
        other => bail!("int() not defined for {}", other.type_name()),
    };
    Ok(result)
}

fn floor(parameters: &[Value], _precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() != 1 {
        bail!("floor() takes 1 parameters, {} provided", parameters.len());
    }

    let rational = match parameters[0].clone() {
        Value::Decimal(x) => x.floor().to_rational().unwrap(),
        Value::Rational(x) => x.floor(),
        other => bail!("floor() not defined for {}", other.type_name()),
    };
    Ok(Value::Rational(rational))
}

fn ceil(parameters: &[Value], _precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() != 1 {
        bail!("ceil() takes 1 parameters, {} provided", parameters.len());
    }

    let rational = match parameters[0].clone() {
        Value::Decimal(x) => x.ceil().to_rational().unwrap(),
        Value::Rational(x) => x.ceil(),
        other => bail!("ceil() not defined for {}", other.type_name()),
    };
    Ok(Value::Rational(rational))
}

fn round(parameters: &[Value], _precision_bits: u32) -> anyhow::Result<Value> {
    if parameters.len() != 1 {
        bail!("round() takes 1 parameters, {} provided", parameters.len());
    }

    let rational = match parameters[0].clone() {
        Value::Decimal(x) => x.round().to_rational().unwrap(),
        Value::Rational(x) => x.round(),
        other => bail!("round() not defined for {}", other.type_name()),
    };
    Ok(Value::Rational(rational))
}

/// A helper to cut down on the boilerplate of declaring functions with minimal differences.
/// Parameters are: function name, the types the function exists for, and whether to convert
/// rational to decimal in case rationals don't have an implementation (such as sin, cos)
macro_rules! single_param_fn {
    ($fn:ident, $($type:ident),+) => {
        fn $fn(parameters: &[Value], _precision_bits: u32) -> anyhow::Result<Value> {
            let result = match parameters {
                $([Value::$type(value)] => Value::$type(value.clone().$fn()),)*
                [other] => bail!(concat!(stringify!($fn), "() not defined for {}"), other.type_name()),
                others => bail!(concat!(stringify!($fn), "() tkaes 1 parameter, {} provided"), others.len())
            };
            Ok(result)
        }
    };

    ($fn:ident, $($type:ident),+; rational_to_decimal) => {
        fn $fn(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
            let result = match parameters {
                $([Value::$type(value)] => Value::$type(value.clone().$fn()),)*
                [Value::Rational(value)] => Value::Decimal({
                    let decimal = crate::util::rational_to_decimal(value, precision_bits);
                    decimal.$fn()
                }),
                [other] => bail!(concat!(stringify!($fn), "() not defined for {}"), other.type_name()),
                others => bail!(concat!(stringify!($fn), "() tkaes 1 parameter, {} provided"), others.len())
            };
            Ok(result)
        }
    };
}

// The ones marked with "rational_to_decimal" implement the function for rationals
// by converting to a decimal. This is lossy, but this done because the function
// simply doesn't exist for rationals.

single_param_fn!(abs, Rational, Decimal, Complex);
single_param_fn!(sin, Decimal, Complex; rational_to_decimal);
single_param_fn!(cos, Decimal, Complex; rational_to_decimal);
single_param_fn!(tan, Decimal, Complex; rational_to_decimal);
single_param_fn!(asin, Decimal, Complex; rational_to_decimal);
single_param_fn!(acos, Decimal, Complex; rational_to_decimal);
single_param_fn!(atan, Decimal, Complex; rational_to_decimal);
single_param_fn!(exp, Decimal, Complex; rational_to_decimal);
single_param_fn!(ln, Decimal, Complex; rational_to_decimal);
single_param_fn!(log10, Decimal, Complex; rational_to_decimal);
single_param_fn!(log2, Decimal; rational_to_decimal);

#[rustfmt::skip]
pub fn add_builtin_constants(variables: &mut HashMap<String, Variable>) {
    fn add_constant(variables: &mut HashMap<String, Variable>, names: &[&str], value_as_string: &str) {
        let mut decimal = rug::Float::new(PRECISION);
        decimal.assign(rug::Float::parse(value_as_string).unwrap());

        for &name in names {
            variables.insert(
                name.to_owned(),
                Variable {
                    value: Value::Decimal(decimal.clone()),
                    builtin: true,
                },
            );
        }
    }

    // 256 bits is just shy of 78 decimal places
    add_constant(variables, &["pi", "π"], "3.14159265358979323846264338327950288419716939937510582097494459230781640628621");
    add_constant(variables, &["phi", "ϕ"], "1.61803398874989484820458683436563811772030917980576286213544862270526046281890");
    add_constant(variables, &["tau"], "6.28318530717958647692528676655900576839433879875021164194988918461563281257242");
    add_constant(variables, &["e"], "2.71828182845904523536028747135266249775724709369995957496696762772407663035355");

    // Add 'i' as the imaginary unit, for when there is not a quantity before it (such as `1i`).
    let imag_unit = rug::Complex::from((rug::Float::new(PRECISION), rug::Float::with_val(PRECISION, 1.0)));
    variables.insert(
        "i".to_owned(),
        Variable {
            value: Value::Complex(imag_unit),
            builtin: true,
        },
    );
}

#[cfg(test)]
#[rustfmt::skip]
mod tests {
    use crate::{PRECISION, builtins::resolve_builtin_fn_call, util::testing::{float, rational, complex, bool, approx_eq}};

    #[test]
    fn test_min() {
        let min = resolve_builtin_fn_call("min").unwrap().0;

        assert!(min(&[float(-1.0), float(1.0)], PRECISION).unwrap() == float(-1.0));
        assert!(min(&[float(1.0), float(-1.0)], PRECISION).unwrap() == float(-1.0));
        assert!(min(&[rational(-1, 1), float(1.0)], PRECISION).unwrap() == float(-1.0));
        assert!(min(&[rational(-1, 1), rational(1, 1)], PRECISION).unwrap() == rational(-1, 1));
        assert!(min(&[float(1.0), complex(1.0, -1.0)], PRECISION).is_err());
        assert!(min(&[float(1.0), bool(true)], PRECISION).is_err());

        assert!(min(&[float(-1.0), float(0.0), float(1.0)], PRECISION).unwrap() == float(-1.0));
        assert!(min(&[float(1.0)], PRECISION).unwrap() == float(1.0));
        assert!(min(&[], PRECISION).is_err());
    }

    #[test]
    fn test_max() {
        let max = resolve_builtin_fn_call("max").unwrap().0;

        assert!(max(&[float(-1.0), float(1.0)], PRECISION).unwrap() == float(1.0));
        assert!(max(&[float(1.0), float(-1.0)], PRECISION).unwrap() == float(1.0));
        assert!(max(&[rational(-1, 1), float(1.0)], PRECISION).unwrap() == float(1.0));
        assert!(max(&[rational(-1, 1), rational(1, 1)], PRECISION).unwrap() == rational(1, 1));
        assert!(max(&[float(1.0), complex(1.0, -1.0)], PRECISION).is_err());
        assert!(max(&[float(1.0), bool(true)], PRECISION).is_err());

        assert!(max(&[float(-1.0), float(0.0), float(1.0)], PRECISION).unwrap() == float(1.0));
        assert!(max(&[float(1.0)], PRECISION).unwrap() == float(1.0));
        assert!(max(&[], PRECISION).is_err());
    }

    #[test]
    fn test_avg() {
        let avg = resolve_builtin_fn_call("avg").unwrap().0;

        assert!(approx_eq(avg(&[float(-1.0), float(1.0)], PRECISION).unwrap(), float(0.0), 0.000001));
        assert!(approx_eq(avg(&[float(1.0), float(-1.0)], PRECISION).unwrap(), float(0.0), 0.000001));
        assert!(approx_eq(avg(&[rational(-1, 1), float(1.0)], PRECISION).unwrap(), float(0.0), 0.000001));
        assert!(avg(&[rational(-1, 1), rational(1, 1)], PRECISION).unwrap() == rational(0, 1));
        assert!(approx_eq(avg(&[float(1.0), complex(1.0, -1.0)], PRECISION).unwrap(), complex(1.0, -0.5), 0.000001));
        assert!(avg(&[float(1.0), bool(true)], PRECISION).is_err());

        assert!(approx_eq(avg(&[float(-1.0), float(0.0), float(1.0)], PRECISION).unwrap(), float(1.0), 0.000001));
        assert!(approx_eq(avg(&[float(1.0)], PRECISION).unwrap(), float(1.0), 0.000001));
        assert!(avg(&[], PRECISION).is_err());
    }

    #[test]
    fn test_sqrt() {
        let sqrt = resolve_builtin_fn_call("sqrt").unwrap().0;

        assert!(approx_eq(sqrt(&[float(0.0)], PRECISION).unwrap(), float(0.0), 0.0000001));
        assert!(approx_eq(sqrt(&[float(1.0)], PRECISION).unwrap(), float(1.0), 0.0000001));
        assert!(approx_eq(sqrt(&[float(256.0 * 256.0)], PRECISION).unwrap(), float(256.0), 0.0000001));
        assert!(approx_eq(sqrt(&[float(-9.0)], PRECISION).unwrap(), complex(0.0, 3.0), 0.0000001));

        // https://en.wikipedia.org/wiki/Square_root#Algebraic_formula
        assert!(approx_eq(sqrt(&[complex(3.0, 4.0)], PRECISION).unwrap(), complex(2.0, 1.0), 0.0000001));

        assert!(sqrt(&[float(0.0), float(1.0)], PRECISION).is_err());
        assert!(sqrt(&[bool(false)], PRECISION).is_err());
        assert!(sqrt(&[], PRECISION).is_err());
    }
}