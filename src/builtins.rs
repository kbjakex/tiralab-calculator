// All the built-in functions.

use anyhow::bail;

use crate::{state::Value, operators::{rational_to_complex, rational_to_decimal}};

pub fn sqrt(parameters: &[Value], precision_bits: u32) -> anyhow::Result<Value> {
    let result = match parameters {
        [Value::Rational(value)] => {
            let (numer, denom) = (value.numer(), value.denom());
            if numer.is_perfect_square() && denom.is_perfect_square() {
                Value::Rational(rug::Rational::from((numer.clone().sqrt(), denom.clone().sqrt())))
            } else if numer < &0 {
                let mut complex = rational_to_complex(&value, precision_bits);
                complex.sqrt_mut();
                Value::Complex(complex)
            } else {
                let mut decimal = rational_to_decimal(&value, precision_bits);
                decimal.sqrt_mut();
                Value::Decimal(decimal)
            }
        },
        [Value::Decimal(value)] => {
            Value::Decimal(value.clone().sqrt())
        },
        [Value::Complex(value)] => {
            Value::Complex(value.clone().sqrt())
        },
        [other] => bail!("sqrt() not defined for {}", other.type_name()),
        others => bail!("sqrt() takes 1 parameter, {} provided", others.len())
    };
    Ok(result)
}