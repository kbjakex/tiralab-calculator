use anyhow::{bail, Result};
use bstr::BStr;
use rug::{ops::PowAssign, Assign};

use crate::{
    operators::{BinaryOperator, UnaryOperator},
    state::Value,
};

#[derive(Debug, PartialEq)]
pub enum Token<'a> {
    Number(Value),
    Variable { name: &'a str },
    Function { name: &'a str, parameter_count: u32 },
    BinaryOperator(BinaryOperator),
    UnaryOperator(UnaryOperator),
}

/// Converts an expression from infix form (`1 + 2`) to postfix form (`1 2 +`).
/// The result is checked for correctness and any missing correctness checks
/// should be considered a bug.
///
/// References:
/// * <http://mathcenter.oxford.emory.edu/site/cs171/shuntingYardAlgorithm/>
/// * <https://aquarchitect.github.io/swift-algorithm-club/Shunting%20Yard/>
///
/// # Errors
/// In the case of a syntax error in the input, an error describing the syntax error
/// is returned.
pub fn infix_to_postfix<'a>(tokens: impl Into<TokenIterator<'a>>) -> Result<Vec<Token<'a>>> {
    let mut iterator = tokens.into();
    match shunting_yard(&mut iterator) {
        Ok(result) => Ok(result),
        Err(e) => bail!("Syntax error: {e}"),
    }
}

/// The actual implementation. Separated for a nicer interface.
fn shunting_yard<'a>(tokens: &mut TokenIterator<'a>) -> Result<Vec<Token<'a>>> {
    use crate::operators::BinaryOperator as BinOp;
    use crate::operators::UnaryOperator as UnOp;
    use ParserToken::*;

    fn assert_value_is_valid_here(
        token: &ParserToken,
        prev_token: &Option<ParserToken>,
    ) -> anyhow::Result<()> {
        if !matches!(
            prev_token,
            None | Some(Delimiter | LeftParen | UnaryOperator(..) | BinaryOperator(..))
        ) {
            bail!(
                "A value (`{token}`) is not valid after `{}`",
                prev_token.as_ref().unwrap()
            );
        }
        Ok(())
    }

    // Runtime invariant: `operators` does *not* contain numbers, variables or right parens.
    let mut output = Vec::new();
    let mut operators = Vec::new();
    let mut parameter_counts = Vec::new();

    let mut last_token = None;
    for token in tokens.by_ref() {
        let token = token?; // Check for parsing errors

        match token {
            Number(ref value) => {
                assert_value_is_valid_here(&token, &last_token)?;
                output.push(Token::Number(value.clone()));
            }

            Variable { name } => {
                assert_value_is_valid_here(&token, &last_token)?;
                output.push(Token::Variable { name });
            }
            
            Function { name } => {
                assert_value_is_valid_here(&token, &last_token)?;
                operators.push(Function { name });
                parameter_counts.push(0);
            }
            
            LeftParen => {
                if matches!(last_token, Some(Number(..))) {
                    bail!("`(` is not valid after `{}`", last_token.unwrap());
                }
                operators.push(LeftParen);
            }
            
            RightParen => {
                if matches!(last_token, Some(Delimiter)) {
                    bail!("Empty function parameter after `,`");
                }

                if matches!(last_token, Some(LeftParen))
                    && !matches!(&operators[..], &[.., ParserToken::Function { .. }, _])
                {
                    bail!("Empty parentheses is invalid");
                }

                pop_until_lparen(&mut operators, &mut output);
                // If there are tokens left, it is an opening paren, so pop that. Otherwise,
                // there were more closing parens than opening parens, so report that.
                if operators.pop().is_none() {
                    bail!("Too many closing parentheses!");
                }
                // If on top of operators is a function, that means this ) marks the end of the
                // function's parameters.
                if let Some(Function { name }) = operators.last() {
                    let mut parameter_count = parameter_counts.pop().unwrap();
                    if !matches!(last_token, Some(LeftParen)) {
                        parameter_count += 1;
                    }

                    output.push(Token::Function {
                        name,
                        parameter_count,
                    });
                    operators.pop();
                }
            }

            UnaryOperator(operator) => {
                if matches!(last_token, Some(UnaryOperator(..))) {
                    bail!(
                        "Two (unary) operators in a row (`{token}` and `{}`)",
                        last_token.unwrap()
                    );
                }
                operators.push(UnaryOperator(operator));
            }
            
            BinaryOperator(operator) => {
                // Detect unary -
                if matches!(
                    last_token,
                    None | Some(LeftParen | UnaryOperator(..) | BinaryOperator(..))
                ) && matches!(operator, BinOp::Subtract)
                {
                    if matches!(last_token, Some(UnaryOperator(..))) {
                        bail!(
                            "Two (unary) operators in a row (`{token}` and `{}`)",
                            last_token.unwrap()
                        );
                    }
                    operators.push(UnaryOperator(UnOp::Negate));
                    last_token = Some(UnaryOperator(UnOp::Negate));
                    continue;
                }

                if matches!(last_token, Some(UnaryOperator(..) | BinaryOperator(..))) {
                    bail!(
                        "Two operators in a row (`{token}` and `{}`)",
                        last_token.unwrap()
                    );
                }
                if matches!(last_token, None) {
                    bail!("Can't start with a binary (two-operand) operator");
                }

                let precedence = operator.precedence();
                let left_associative = operator.left_associative();

                loop {
                    match operators.last() {
                        Some(&BinaryOperator(top_of_stack)) => {
                            let top_precedence = top_of_stack.precedence();

                            if (left_associative && precedence <= top_precedence)
                                || (!left_associative && precedence < top_precedence)
                            {
                                output.push(Token::BinaryOperator(top_of_stack));
                                operators.pop();
                            } else {
                                break;
                            }
                        }
                        Some(&UnaryOperator(top_of_stack)) => {
                            if !left_associative {
                                break;
                            }
                            output.push(Token::UnaryOperator(top_of_stack));
                            operators.pop();
                        }
                        _ => break,
                    }
                }

                operators.push(BinaryOperator(operator));
            }

            Delimiter => {
                if matches!(last_token, Some(LeftParen | Delimiter)) {
                    bail!("Empty function parameter before a `,`");
                }

                if let Some(count) = parameter_counts.last_mut() {
                    *count += 1;
                } else {
                    bail!("`,` outside of a function call");
                }

                loop {
                    match operators.last() {
                        Some(&BinaryOperator(top_of_stack)) => {
                            output.push(Token::BinaryOperator(top_of_stack));
                        }
                        Some(&UnaryOperator(top_of_stack)) => {
                            output.push(Token::UnaryOperator(top_of_stack));
                        }
                        _ => break,
                    }
                    operators.pop();
                }
            }
        }

        last_token = Some(token);
    }

    if matches!(last_token, Some(BinaryOperator(..) | UnaryOperator(..))) {
        bail!("Trailing operator (`{}`)", last_token.unwrap());
    }

    pop_until_lparen(&mut operators, &mut output);

    // No tokens should remain
    if !operators.is_empty() {
        bail!("Too many opening parentheses!");
    }

    Ok(output)
}

/// Last step in the shunting-yard algorithm: pop nodes from operator stack into the output
/// until a left paren ('(') is found. The function does not pop the left paren.
fn pop_until_lparen<'a>(operators: &mut Vec<ParserToken<'a>>, output: &mut Vec<Token<'a>>) {
    loop {
        let top = match operators.last() {
            None | Some(ParserToken::LeftParen) => return,
            _ => operators.pop().unwrap(),
        };

        match top {
            ParserToken::Number(value) => output.push(Token::Number(value)),
            ParserToken::Variable { name } => output.push(Token::Variable { name }),
            ParserToken::Function { name } => output.push(Token::Function {
                name,
                parameter_count: 0,
            }),
            ParserToken::BinaryOperator(operator) => output.push(Token::BinaryOperator(operator)),
            ParserToken::UnaryOperator(operator) => output.push(Token::UnaryOperator(operator)),
            ParserToken::RightParen => unreachable!("operators never contains right parens"),
            ParserToken::Delimiter => unreachable!("operators never contains delimiters"),
            ParserToken::LeftParen => return,
        }
    }
}

/// Represents a token internal to the parser.
#[derive(Debug)]
pub enum ParserToken<'a> {
    Number(Value),
    Variable { name: &'a str },
    Function { name: &'a str },
    Delimiter,
    BinaryOperator(BinaryOperator),
    UnaryOperator(UnaryOperator),
    LeftParen,
    RightParen,
}

impl std::fmt::Display for ParserToken<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ParserToken::Number(ref x) => write!(f, "{x}"),
            ParserToken::Variable { name } => f.write_str(name),
            ParserToken::Function { name } => f.write_str(name),
            ParserToken::Delimiter => f.write_str(","),
            ParserToken::BinaryOperator(op) => match op {
                BinaryOperator::Add => f.write_str("+"),
                BinaryOperator::Subtract => f.write_str("-"),
                BinaryOperator::Multiply => f.write_str("*"),
                BinaryOperator::Divide => f.write_str("/"),
                BinaryOperator::Remainder => f.write_str("%"),
                BinaryOperator::Power => f.write_str("^"),
                BinaryOperator::LessThan => f.write_str("<"),
                BinaryOperator::LequalTo => f.write_str("<="),
                BinaryOperator::GreaterThan => f.write_str(">"),
                BinaryOperator::GequalTo => f.write_str(">="),
                BinaryOperator::EqualTo => f.write_str("=="),
                BinaryOperator::NequalTo => f.write_str("!="),
                BinaryOperator::LogicalAnd => f.write_str("&&"),
                BinaryOperator::LogicalOr => f.write_str("||"),
            },
            ParserToken::UnaryOperator(op) => match op {
                UnaryOperator::Negate => f.write_str("-"),
            },
            ParserToken::LeftParen => f.write_str("("),
            ParserToken::RightParen => f.write_str(")"),
        }
    }
}

pub struct TokenIterator<'a> {
    source: &'a BStr,
    index: usize, // Current position in `source`
    last_was_number: bool,
    precision_bits: u32,
}

impl<'a> TokenIterator<'a> {
    /// Creates a new iterator over the tokens in the source string.
    pub fn of(source: &'a str, precision_bits: u32) -> Self {
        Self {
            source: source.into(), // Guaranteed to be free and infallible
            index: 0,
            last_was_number: false,
            precision_bits,
        }
    }

    /// Advance cursor until a non-space character is found.
    fn skip_spaces(&mut self) {
        while self.index < self.source.len() && self.source[self.index].is_ascii_whitespace() {
            self.index += 1;
        }
    }

    /// Greedily reads (consumes) all consecutive digits and periods, attempts
    /// to parse them as a number, and leaves `self.index` pointing to the first
    /// excluded character.
    fn read_number(&mut self) -> Result<Value> {
        let end_index = self
            .source
            .iter()
            .skip(self.index)
            .position(|&c| !c.is_ascii_digit() && c != b'.')
            .map_or(self.source.len(), |i| i + self.index);

        // SAFETY: this is safe, because byte_str can necessarily only contain ascii digits or an ascii dot,
        // and ascii is valid UTF-8. Both types have the same representation. Empty source is also fine.
        let string: &str = unsafe { std::mem::transmute(&self.source[self.index..end_index]) };
        let mut string = string.to_owned();
        if string.starts_with(".") {
            // Reviewer suggestion: allow leading `.`. Rug doesn't allow
            // a leading decimal point, so fix by appending a zero when it's missing.
            string.insert(0, '0');
        }
        println!("'{string}' (len {})", string.len());

        let period_index = string.find('.');

        self.index = end_index;
        self.last_was_number = true;

        if let Some(b'i') = self.source.get(self.index) {
            self.last_was_number = false; // don't allow a variable directly after the 'i'
            self.index += 1;

            // Imaginary unit
            let mut value = rug::Complex::new(self.precision_bits);
            value.assign((
                rug::Float::new(self.precision_bits),
                rug::Float::parse(string)?,
            ));
            return Ok(Value::Complex(value));
        }

        if let Some(index) = period_index {
            // All inputs entered in the form `<whole part>.<fract part>` are necessary not irrational, so
            // might as well parse them as exact rationals by parsing `123.456` as `123456/1000` and letting
            // the library canonicalize it.

            let whole_part_str = &string[..index];
            let fract_part_str = &string[index + 1..];

            let mut whole_part = rug::Integer::new();
            whole_part.assign(rug::Integer::parse(whole_part_str)?);

            let mut fract_part = rug::Integer::new();
            fract_part.assign(rug::Integer::parse(fract_part_str)?);

            let mut denominator = rug::Integer::new();
            denominator.assign(10);
            denominator.pow_assign(u32::try_from(fract_part_str.len())?);

            whole_part *= &denominator;
            whole_part += fract_part;

            let rational = rug::Rational::from((whole_part, denominator));

            return Ok(Value::Rational(rational));
        }

        let res = rug::Rational::parse(string)?;
        let mut value = rug::Rational::new();
        value.assign(res);

        Ok(Value::Rational(value))
    }

    /// Similar to `read_number`. Identifiers are of the form
    /// `[a-zA-Z][a-zA-Z0-9]*`.
    fn read_identifier(&mut self) -> &'a str {
        let end_index = self
            .source
            .iter()
            .skip(self.index)
            .position(|c| !matches!(c, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_'))
            .map_or(self.source.len(), |i| i + self.index);

        let byte_str = &self.source[self.index..end_index];
        // SAFETY: this is safe, because byte_str can necessarily only contain ascii codepoints,
        // and this is therefore valid UTF-8. Both types have the same representation. Empty source is also fine.
        let str_slice: &str = unsafe { std::mem::transmute(byte_str) };

        self.index = end_index;

        str_slice
    }

    /// Determines the type of, and reads, the next token, incrementing `self.index`
    /// to point to the start of the next token.
    /// This method assumes that there are no spaces at the cursor position and that
    /// there are still tokens to be read.
    fn read_token(&mut self) -> Result<ParserToken<'a>> {
        // Inject implicit * for `2x`
        if std::mem::replace(&mut self.last_was_number, false)
            && self.source[self.index].is_ascii_alphabetic()
        {
            return Ok(ParserToken::BinaryOperator(BinaryOperator::Multiply));
        }

        let (result, advance) = match (self.source[self.index], self.source.get(self.index + 1)) {
            (b'(', _) => (ParserToken::LeftParen, 1),
            (b')', _) => (ParserToken::RightParen, 1),
            (b'+', _) => (ParserToken::BinaryOperator(BinaryOperator::Add), 1),
            (b'-', _) => (ParserToken::BinaryOperator(BinaryOperator::Subtract), 1),
            (b'*', _) => (ParserToken::BinaryOperator(BinaryOperator::Multiply), 1),
            (b'/', _) => (ParserToken::BinaryOperator(BinaryOperator::Divide), 1),
            (b'%', _) => (ParserToken::BinaryOperator(BinaryOperator::Remainder), 1),
            (b'^', _) => (ParserToken::BinaryOperator(BinaryOperator::Power), 1),
            (b',', _) => (ParserToken::Delimiter, 1),
            (b'|', Some(b'|')) => (ParserToken::BinaryOperator(BinaryOperator::LogicalOr), 2),
            (b'&', Some(b'&')) => (ParserToken::BinaryOperator(BinaryOperator::LogicalAnd), 2),
            (b'<', Some(b'=')) => (ParserToken::BinaryOperator(BinaryOperator::LequalTo), 2),
            (b'>', Some(b'=')) => (ParserToken::BinaryOperator(BinaryOperator::GequalTo), 2),
            (b'=', Some(b'=')) => (ParserToken::BinaryOperator(BinaryOperator::EqualTo), 2),
            (b'!', Some(b'=')) => (ParserToken::BinaryOperator(BinaryOperator::NequalTo), 2),
            (b'<', _) => (ParserToken::BinaryOperator(BinaryOperator::LessThan), 1),
            (b'>', _) => (ParserToken::BinaryOperator(BinaryOperator::GreaterThan), 1),

            (c, _) => {
                if c == b'.' || c.is_ascii_digit() {
                    return Ok(ParserToken::Number(self.read_number()?));
                }
                if c.is_ascii_alphabetic() {
                    let name = self.read_identifier();
                    self.skip_spaces();
                    if self.source.get(self.index) == Some(&b'(') {
                        return Ok(ParserToken::Function { name });
                    }
                    return Ok(ParserToken::Variable { name });
                }

                bail!("Invalid token `{}` (at `{}`)", c as char, unsafe {
                    std::mem::transmute::<&BStr, &str>(&self.source[self.index..])
                });
            }
        };

        self.index += advance;
        Ok(result)
    }
}

impl<'a> Iterator for TokenIterator<'a> {
    type Item = Result<ParserToken<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_spaces();

        if self.index == self.source.len() {
            return None;
        }

        Some(self.read_token())
    }
}

impl<'a> From<&'a str> for TokenIterator<'a> {
    fn from(source: &'a str) -> Self {
        Self::of(source, 128)
    }
}

#[rustfmt::skip] // rustfmt keeps splitting the asserts which ends up actually hurting readability
#[cfg(test)]
mod tests {
    use crate::{operators::BinaryOperator, operators::UnaryOperator, parser::Token, state::Value};

    use super::infix_to_postfix;

    // A macro to make building expected solutions not enormously verbose. Macros are unfortunately
    // fairly unreadable, but you can probably mostly infer what it does from the usage in below tests.
    macro_rules! tokens {
        (+) => {Token::BinaryOperator(BinaryOperator::Add)};
        (-) => {Token::BinaryOperator(BinaryOperator::Subtract)};
        (*) => {Token::BinaryOperator(BinaryOperator::Multiply)};
        (/) => {Token::BinaryOperator(BinaryOperator::Divide)};
        (^) => {Token::BinaryOperator(BinaryOperator::Power)};
        (%) => {Token::BinaryOperator(BinaryOperator::Remainder)};
        (~) => {Token::UnaryOperator(UnaryOperator::Negate)};
        ($lit:literal) => {Token::Number(Value::Rational(rug::Rational::from($lit))) };
        ($name:ident) => (Token::Variable{ name: stringify!($name) });
        // Loop over space-separated input tokens, parse them with the token! macro, and build
        // a vector out of them.
        ($($tok:tt)+) => {
            vec![$(tokens!($tok),)*]
        }
    }

    #[test]
    fn test_reports_mismatched_parentheses() {
        assert!(infix_to_postfix("(()").is_err());
        assert!(infix_to_postfix("())").is_err());
        assert!(infix_to_postfix("(").is_err());
        assert!(infix_to_postfix(")").is_err());
    }

    #[test]
    fn test_valid_numbers_are_accepted() {
        // This is implemented using standard library routines so actual parsing need not to
        // be tested, fortunately, but test anyways that valid inputs aren't rejected.
        assert!(infix_to_postfix("0").is_ok());
        assert!(infix_to_postfix("0.0").is_ok());
        assert!(infix_to_postfix("0.").is_ok());
        assert!(infix_to_postfix("3.1415936535").is_ok());
    }

    #[test]
    fn test_invalid_numbers_are_rejected() {
        assert!(infix_to_postfix(".0").is_err());
        assert!(infix_to_postfix("0..").is_err());
        assert!(infix_to_postfix("..0").is_err());
        assert!(infix_to_postfix(".0.").is_err());
    }

    #[test]
    fn test_valid_expressions() {
        assert_eq!(tokens![5 5 +], infix_to_postfix("5. + 5.").unwrap());
        assert_eq!(tokens![5 5 + 3 3 + *], infix_to_postfix("(5 + 5) * (3 + 3)").unwrap());
        assert_eq!(tokens![5 5 + 3 * 3 +], infix_to_postfix("(5 + 5) * 3 + 3").unwrap());
        assert_eq!(tokens![5 5 3 * + 3 +], infix_to_postfix("5 + 5 * 3 + 3").unwrap());
        assert_eq!(tokens![5 5 3 3 + * +], infix_to_postfix("5 + 5 * (3 + 3)").unwrap());
    }

    #[test]
    fn test_unary_works() {
        // ~ represents unary minus 
        assert_eq!(tokens![5 ~], infix_to_postfix("-5").unwrap());
        assert_eq!(tokens![5 ~ 5 ~ -], infix_to_postfix("-5 - -5").unwrap());
        assert_eq!(tokens![2 3 + ~], infix_to_postfix("-(2+3)").unwrap());
        assert_eq!(tokens![5 3 ~ /], infix_to_postfix("5 / -3").unwrap());
    }

    #[test]
    fn test_power_operator_works() {
        assert_eq!(infix_to_postfix("2^(3^4)").unwrap(), infix_to_postfix("2^3^4").unwrap());
        assert_eq!(tokens![2 3 4 ^ ^], infix_to_postfix("2^3^4").unwrap());
        assert_eq!(infix_to_postfix("-5^2").unwrap(), infix_to_postfix("-(5^2)").unwrap());
        assert_eq!(tokens![5 2 ^ ~], infix_to_postfix("-5^2").unwrap());
    }

    #[test]
    fn test_variables_work() {
        assert_eq!(tokens![a 3 +], infix_to_postfix("a + 3").unwrap());
        assert_eq!(tokens![variable 3 +], infix_to_postfix("variable + 3").unwrap());
        assert_eq!(tokens![x x * y y * -], infix_to_postfix("x*x - y*y").unwrap());
    }

    #[test]
    fn test_function_calls_work() {
        assert!(infix_to_postfix("foo(a)").is_ok());
        assert!(infix_to_postfix("bar ( a , b )").is_ok());
        assert!(infix_to_postfix("f(a,b,c)").is_ok());
    }

    #[test]
    fn test_implicit_multiply() {
        assert_eq!(tokens![2 x *], infix_to_postfix("2x").unwrap());
        // I don't want implicit multiplication to work with parentheses I think?
        assert!(infix_to_postfix("2(a+b)").is_err());
    }

    #[test]
    fn test_postfix_is_rejected() {
        // Shunting yard accepts postfix by default. Test that it is rejected after my modifications.
        assert!(infix_to_postfix("1 2 + 3 *").is_err());
        assert!(infix_to_postfix("1 2 +").is_err());
        assert!(infix_to_postfix("a + +").is_err());
        assert!(infix_to_postfix("a +").is_err());
        assert!(infix_to_postfix("+ a").is_err());
    }
}
