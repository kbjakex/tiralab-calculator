use anyhow::{anyhow, bail, Result};
use bstr::BStr;

use crate::ast::BinaryOperator;

#[derive(Debug, PartialEq)]
pub enum Token<'a> {
    Number(f64),
    Variable { name: &'a str },
    BinaryOperator(BinaryOperator),
}

/// Converts an expression from infix form (`1 + 2`) to postfix form (`1 2 +`) using the
/// shunting yard algorithm. The result is checked for correctness and any missing
/// correctness checks should be considered a bug.
/// 
/// References:
/// * <http://mathcenter.oxford.emory.edu/site/cs171/shuntingYardAlgorithm/>
/// * <https://aquarchitect.github.io/swift-algorithm-club/Shunting%20Yard/>
/// 
/// # Errors
/// In the case of a syntax error in the input, an error describing the syntax error
/// is returned.
pub fn infix_to_postfix_shunting_yard(infix_str: &str) -> Result<Vec<Token>> {
    // Runtime invariant: `operators` does *not* contain numbers, variables or right parens.
    let mut output = Vec::new();
    let mut operators = Vec::new();

    // Shunting yard in itself accepts both postfix and infix, but in this case,
    // I want only infix to be accepted. In infix, after each value or right paren,
    // there must necessarily be an operator, after which is again a value of left paren,
    // and so on. This bit of state is enough to verify this.
    let mut expecting_operator = false;

    use ParserToken::*;
    for token in TokenIterator::of(infix_str) {
        match token? {
            Number(..) | Variable { .. } if expecting_operator => {
                bail!("Found two values in a row (missing an operator?)");
            }

            Number(value) => {
                output.push(Token::Number(value));
                expecting_operator = true;
            }
            Variable { name } => {
                output.push(Token::Variable { name });
                expecting_operator = true;
            }
            LeftParen => operators.push(LeftParen),
            RightParen => {
                pop_until_lparen(&mut operators, &mut output);
                // If there are tokens left, it is an openin paren, so pop that. Otherwise,
                // there were more closing parens than opening parens, so report that.
                if operators.pop().is_none() {
                    bail!("Too many closing parentheses!");
                }
            }
            BinaryOperator(operator) => {
                if !expecting_operator {
                    bail!("An operator is missing an operand (two operators in a row?)");
                }
                expecting_operator = false;

                let precedence = operator.precedence();

                while let Some(&BinaryOperator(top_of_stack)) = operators.last() {
                    let top_precedence = top_of_stack.precedence();

                    if (operator.left_associative() && precedence <= top_precedence)
                        || (!operator.left_associative() && precedence < top_precedence)
                    {
                        output.push(Token::BinaryOperator(top_of_stack));
                        operators.pop();
                    } else {
                        break;
                    }
                }

                operators.push(BinaryOperator(operator));
            }
        }
    }

    if !expecting_operator {
        bail!("Expression can't end with an operator");
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
    while let Some(top) = operators.last() {
        match *top {
            ParserToken::Number(value) => output.push(Token::Number(value)),
            ParserToken::Variable { name } => output.push(Token::Variable { name }),
            ParserToken::BinaryOperator(operator) => output.push(Token::BinaryOperator(operator)),
            ParserToken::RightParen => unreachable!("operators never contains right parens"),
            ParserToken::LeftParen => return,
        }
        operators.pop();
    }
}

/// Represents a token internal to the parser.
#[derive(Debug)]
enum ParserToken<'a> {
    Number(f64),
    Variable { name: &'a str },
    BinaryOperator(BinaryOperator),
    LeftParen,
    RightParen,
}

struct TokenIterator<'a> {
    source: &'a BStr,
    index: usize, // Current position in `source`
    last_was_number: bool,
}

impl<'a> TokenIterator<'a> {
    /// Creates a new iterator over the tokens in the source string.
    pub fn of(source: &'a str) -> Self {
        Self {
            source: source.into(), // Guaranteed to be free and infallible
            index: 0,
            last_was_number: false,
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
    fn read_number(&mut self) -> Result<f64> {
        let end_index = self
            .source
            .iter()
            .skip(self.index)
            .position(|&c| !c.is_ascii_digit() && c != b'.')
            .map_or(self.source.len(), |i| i + self.index);

        let byte_str = &self.source[self.index..end_index];
        // SAFETY: this is safe, because byte_str can necessarily only contain ascii digits or an ascii dot,
        // and ascii is valid UTF-8. Both types have the same representation. Empty source is also fine.
        let str_slice: &str = unsafe { std::mem::transmute(byte_str) };

        self.index = end_index - 1;

        str_slice
            .parse()
            .map_err(|_| anyhow!("Invalid number: '{str_slice}'"))
    }

    /// Similar to `read_number`. Identifiers are of the form
    /// `[a-zA-Z][a-zA-Z0-9]*`.
    fn read_identifier(&mut self) -> &'a str {
        let end_index = self
            .source
            .iter()
            .skip(self.index)
            .position(|c| !matches!(c, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9'))
            .map_or(self.source.len(), |i| i + self.index);

        let byte_str = &self.source[self.index..end_index];
        // SAFETY: this is safe, because byte_str can necessarily only contain ascii codepoints,
        // and this is therefore valid UTF-8. Both types have the same representation. Empty source is also fine.
        let str_slice: &str = unsafe { std::mem::transmute(byte_str) };

        self.index = end_index - 1;

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

        let result = match self.source[self.index] {
            b'(' => ParserToken::LeftParen,
            b')' => ParserToken::RightParen,
            b'+' => ParserToken::BinaryOperator(BinaryOperator::Add),
            b'-' => ParserToken::BinaryOperator(BinaryOperator::Subtract),
            b'*' => ParserToken::BinaryOperator(BinaryOperator::Multiply),
            b'/' => ParserToken::BinaryOperator(BinaryOperator::Divide),

            c if c.is_ascii_digit() => {
                self.last_was_number = true;
                ParserToken::Number(self.read_number()?)
            }
            c if c.is_ascii_alphabetic() => ParserToken::Variable {
                name: self.read_identifier(),
            },

            // Looks a bit ugly, because the Result is wrapped in an Option (necessitated by Iterator)
            // and the usual error reporting facilities ('?' operator) don't work with that.
            other => bail!("Invalid symbol (starts with '{}')", other as char),
        };

        self.index += 1;
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

#[cfg(test)]
mod tests {
    use crate::{ast::BinaryOperator, parser::Token};

    use super::infix_to_postfix_shunting_yard;

    // A macro to make building expected solutions not enormously verbose. Macros are unfortunately
    // fairly unreadable, but you can probably mostly infer what it does from the usage in below tests.
    macro_rules! tokens {
        (+) => {Token::BinaryOperator(BinaryOperator::Add)};
        (-) => {Token::BinaryOperator(BinaryOperator::Subtract)};
        (*) => {Token::BinaryOperator(BinaryOperator::Multiply)};
        (/) => {Token::BinaryOperator(BinaryOperator::Divide)};
        ($lit:literal) => {Token::Number($lit as f64) };
        ($name:ident) => (Token::Variable{ name: stringify!($name) });
        // Loop over space-separated input tokens, parse them with the token! macro, and build
        // a vector out of them.
        ($($tok:tt)+) => {
            vec![$(tokens!($tok),)*]
        }
    }

    #[test]
    fn test_reports_mismatched_parentheses() {
        assert!(infix_to_postfix_shunting_yard("(()").is_err());
        assert!(infix_to_postfix_shunting_yard("())").is_err());
        assert!(infix_to_postfix_shunting_yard("(").is_err());
        assert!(infix_to_postfix_shunting_yard(")").is_err());
    }

    #[test]
    fn test_valid_numbers_are_accepted() {
        // This is implemented using standard library routines so actual parsing need not to
        // be tested, fortunately, but test anyways that valid inputs aren't rejected.
        assert!(infix_to_postfix_shunting_yard("0").is_ok());
        assert!(infix_to_postfix_shunting_yard("0.0").is_ok());
        assert!(infix_to_postfix_shunting_yard("0.").is_ok());
        assert!(infix_to_postfix_shunting_yard("3.1415936535").is_ok());
    }

    #[test]
    fn test_invalid_numbers_are_rejected() {
        assert!(infix_to_postfix_shunting_yard(".0").is_err());
        assert!(infix_to_postfix_shunting_yard("0..").is_err());
        assert!(infix_to_postfix_shunting_yard("..0").is_err());
        assert!(infix_to_postfix_shunting_yard(".0.").is_err());
    }

    #[test]
    fn test_valid_expressions() {
        assert_eq!(
            tokens![5 5 +],
            infix_to_postfix_shunting_yard("5. + 5.").unwrap()
        );
        assert_eq!(
            tokens![5 5 + 3 3 + *],
            infix_to_postfix_shunting_yard("(5 + 5) * (3 + 3)").unwrap()
        );
        assert_eq!(
            tokens![5 5 + 3 * 3 +],
            infix_to_postfix_shunting_yard("(5 + 5) * 3 + 3").unwrap()
        );
        assert_eq!(
            tokens![5 5 3 * + 3 +],
            infix_to_postfix_shunting_yard("5 + 5 * 3 + 3").unwrap()
        );
        assert_eq!(
            tokens![5 5 3 3 + * +],
            infix_to_postfix_shunting_yard("5 + 5 * (3 + 3)").unwrap()
        );
    }

    #[test]
    fn test_variables_work() {
        assert_eq!(
            tokens![a 3 +],
            infix_to_postfix_shunting_yard("a + 3").unwrap()
        );
        assert_eq!(
            tokens![variable 3 +],
            infix_to_postfix_shunting_yard("variable + 3").unwrap()
        );
        assert_eq!(
            tokens![x x * y y * -],
            infix_to_postfix_shunting_yard("x*x - y*y").unwrap()
        );
    }

    #[test]
    fn test_implicit_multiply() {
        assert_eq!(
            tokens![2 x *],
            infix_to_postfix_shunting_yard("2x").unwrap()
        );
        // I don't want implicit multiplication to work with parentheses I think?
        assert!(infix_to_postfix_shunting_yard("2(a+b)").is_err());
    }

    #[test]
    fn test_postfix_is_rejected() {
        // Shunting yard accepts postfix by default. Test that it is rejected after my modifications.
        assert!(infix_to_postfix_shunting_yard("1 2 + 3 *").is_err());
        assert!(infix_to_postfix_shunting_yard("1 2 +").is_err());
        assert!(infix_to_postfix_shunting_yard("a + +").is_err());
        assert!(infix_to_postfix_shunting_yard("a +").is_err());
        assert!(infix_to_postfix_shunting_yard("+ a").is_err());
    }
}
