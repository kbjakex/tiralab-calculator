// All the built-in functions.

use anyhow::bail;
use bevy_utils::HashMap;
use rug::Assign;

use crate::{
    operators::{rational_to_complex, rational_to_decimal},
    state::{Value, Variable},
};

pub fn sqrt(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
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
