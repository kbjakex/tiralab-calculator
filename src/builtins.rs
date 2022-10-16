// All the built-in functions.

use anyhow::bail;
use bevy_utils::HashMap;
use rug::Assign;

use crate::{
    operators::{rational_to_complex, rational_to_decimal},
    state::{Value, Variable},
};

#[derive(Debug, Clone, Copy)]
pub enum BuiltInFunction {
    Sqrt,
    Cbrt,
    Abs,
    Floor,
    Ceil,
    Round,
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    Exp,
    Ln,
    Log10,
    Log2,
}

impl BuiltInFunction {
    pub fn from_name(name: &str) -> Option<Self> {
        let result = match name {
            "sqrt" => Self::Sqrt,
            "cbrt" => Self::Cbrt,
            "abs" => Self::Abs,
            "floor" => Self::Floor,
            "round" => Self::Round,
            "ceil" => Self::Ceil,
            "sin" => Self::Sin,
            "cos" => Self::Cos,
            "tan" => Self::Tan,
            "asin" => Self::Asin,
            "acos" => Self::Acos,
            "atan" => Self::Atan,
            "exp" => Self::Exp,
            "ln" => Self::Ln,
            "log10" => Self::Log10,
            "log2" => Self::Log2,
            _ => return None,
        };

        Some(result)
    }

    pub const fn parameter_count(self) -> usize {
        match self {
            _ => 1,
        }
    }

    pub fn evaluate(self, parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
        use BuiltInFunction::*;
        match self {
            Sqrt => sqrt(parameters, precision_bits),
            Cbrt => bail!("Unimplemented"),
            Abs => abs(parameters),
            Sin => sin(parameters, precision_bits),
            Cos => cos(parameters, precision_bits),
            Tan => tan(parameters, precision_bits),
            Floor => floor(parameters),
            Ceil => ceil(parameters),
            Round => round(parameters),
            Asin => asin(parameters, precision_bits),
            Acos => acos(parameters, precision_bits),
            Atan => atan(parameters, precision_bits),
            Exp => exp(parameters, precision_bits),
            Ln => ln(parameters, precision_bits),
            Log10 => log10(parameters, precision_bits),
            Log2 => log2(parameters, precision_bits),
        }
    }
}

fn sqrt(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
    let result = match parameters {
        [Value::Rational(value)] => {
            let (numer, denom) = (value.numer(), value.denom());
            if numer.is_perfect_square() && denom.is_perfect_square() {
                Value::Rational(rug::Rational::from((
                    numer.clone().sqrt(),
                    denom.clone().sqrt(),
                )))
            } else if numer < &0 {
                let mut complex = rational_to_complex(&value, precision_bits);
                complex.sqrt_mut();
                Value::Complex(complex)
            } else {
                let mut decimal = rational_to_decimal(&value, precision_bits);
                decimal.sqrt_mut();
                Value::Decimal(decimal)
            }
        }
        [Value::Decimal(value)] => Value::Decimal(value.clone().sqrt()),
        [Value::Complex(value)] => Value::Complex(value.clone().sqrt()),
        [other] => bail!("sqrt() not defined for {}", other.type_name()),
        others => bail!("sqrt() takes 1 parameter, {} provided", others.len()),
    };

    Ok(result)
}

/// A helper to cut down on the boilerplate of declaring functions with minimal differences.
/// Parameters are: function name, the types the function exists for, and whether to convert
/// rational to decimal in case rationals don't have an implementation (such as sin, cos)
macro_rules! single_param_fn {
    ($fn:ident, $($type:ident),+) => {
        fn $fn(parameters: &[Value]) -> anyhow::Result<Value> {
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
                    let decimal = crate::operators::rational_to_decimal(value, precision_bits);
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

single_param_fn!(floor, Rational, Decimal);
single_param_fn!(round, Rational, Decimal);
single_param_fn!(ceil, Rational, Decimal);
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
    fn add_constant(variables: &mut HashMap<String, Variable>, name: &str, value_as_string: &str) {
        let mut decimal = rug::Float::new(128);
        decimal.assign(rug::Float::parse(value_as_string).unwrap());

        variables.insert(
            name.to_owned(),
            Variable {
                value: Value::Decimal(decimal),
                builtin: true,
            },
        );
    }

    // 128 bits is roughly 40 decimal places
    add_constant(variables, "pi", "3.141592653589793238462643383279502884197");
    add_constant(variables, "tau", "6.283185307179586476925286766559005768394");
    add_constant(variables, "e", "2.718281828459045235360287471352662497757");

    // Add 'i' as the imaginary unit, for when there is not a quantity before it (such as `1i`).
    let imag_unit = rug::Complex::from((rug::Float::new(128), rug::Float::with_val(128, 1.0)));
    variables.insert(
        "i".to_owned(),
        Variable {
            value: Value::Complex(imag_unit),
            builtin: true,
        },
    );
}
