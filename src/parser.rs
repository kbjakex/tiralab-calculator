use std::ops::Range;

use bstr::BStr;
use rug::{ops::PowAssign, Assign};
use thiserror::Error;
use Result;

use crate::{
    operators::{self, BinaryOperator, UnaryOperator},
    state::Value,
    DEFAULT_PRECISION,
};

#[derive(Error, Debug)]
pub struct ParseError {
    pub message: String,
    /// Specifies the start & end byte indices of the part of the
    /// source string that caused the error
    pub span: Range<usize>,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

/// Represents the result of parsing an input.
pub type ParseResult<T> = Result<T, Box<ParseError>>;

macro_rules! make_parse_error {
    ($span:expr, $($arg:tt)*) => {
        crate::parser::ParseError {
            message: format!($($arg)*),
            span: $span
        }
    };
}

pub(crate) use make_parse_error;

macro_rules! parse_error {
    ($span:expr, $($arg:tt)*) => {
        return Err(Box::new(crate::parser::make_parse_error!($span, $($arg)*)))
    };
}

pub(crate) use parse_error;

impl ParseError {
    pub fn offset(&mut self, offset: usize) -> &mut Self {
        self.span.start += offset;
        self.span.end += offset;
        self
    }
}

pub fn offset(mut e: Box<ParseError>, offset: usize) -> Box<ParseError> {
    e.offset(offset);
    e
}

#[derive(Debug)]
pub struct Token<'a> {
    pub kind: TokenKind<'a>,
    pub span: Range<usize>,
}

impl<'a> Token<'a> {
    pub fn new(span: Range<usize>, kind: TokenKind<'a>) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, PartialEq)]
pub enum TokenKind<'a> {
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
pub fn infix_to_postfix<'a>(tokens: impl Into<TokenIterator<'a>>) -> ParseResult<Vec<Token<'a>>> {
    let mut iterator = tokens.into();
    match shunting_yard(&mut iterator) {
        Ok(result) => Ok(result),
        Err(e) => parse_error!(e.span, "Syntax error: {e}"),
    }
}

/// The actual implementation. Separated for a nicer interface.
fn shunting_yard<'a>(tokens: &mut TokenIterator<'a>) -> ParseResult<Vec<Token<'a>>> {
    use crate::operators::BinaryOperator as BinOp;
    use crate::operators::UnaryOperator as UnOp;
    use ParserTokenKind::*;

    fn assert_value_is_valid_here(
        token: &ParserToken,
        prev_token: &Option<ParserTokenKind>,
    ) -> ParseResult<()> {
        if !matches!(
            prev_token,
            None | Some(Delimiter | LeftParen | UnaryOperator(..) | BinaryOperator(..))
        ) {
            parse_error!(
                token.span.clone(),
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
    let mut last_span = 0..0;
    while let Some(token) = tokens.next() {
        let token = token?; // Check for parsing errors
        let span = token.span.clone();
        last_span = span.clone();

        match token.kind {
            Number(ref value) => {
                assert_value_is_valid_here(&token, &last_token)?;
                output.push(Token::new(span, TokenKind::Number(value.clone())));
            }

            Variable { name } => {
                assert_value_is_valid_here(&token, &last_token)?;
                output.push(Token::new(span, TokenKind::Variable { name }));
            }

            Function { .. } => {
                assert_value_is_valid_here(&token, &last_token)?;
                operators.push(token.clone());
                parameter_counts.push(0);
            }

            LeftParen => {
                if matches!(last_token, Some(Number(..))) {
                    parse_error!(span, "`(` is not valid after `{}`", last_token.unwrap());
                }
                operators.push(token.clone());
            }

            RightParen => {
                if matches!(last_token, Some(Delimiter)) {
                    parse_error!(span, "Empty function parameter after `,`");
                }

                if matches!(last_token, Some(LeftParen))
                    && !matches!(
                        &operators[..],
                        &[
                            ..,
                            ParserToken {
                                kind: ParserTokenKind::Function { .. },
                                ..
                            },
                            _
                        ]
                    )
                {
                    let span = span.start.saturating_sub(1)..span.end;
                    parse_error!(span, "Empty parentheses is invalid");
                }

                if matches!(last_token, Some(BinaryOperator(..) | UnaryOperator(..))) {
                    parse_error!(
                        last_span,
                        "`)` is not valid after an operator (`{}`)",
                        last_token.unwrap()
                    );
                }

                pop_until_lparen(&mut operators, &mut output);
                // If there are tokens left, it is an opening paren, so pop that. Otherwise,
                // there were more closing parens than opening parens, so report that.
                if operators.pop().is_none() {
                    parse_error!(span, "Too many closing parentheses");
                }
                // If on top of operators is a function, that means this ) marks the end of the
                // function's parameters.
                if let Some(ParserToken {
                    kind: Function { name },
                    ..
                }) = operators.last()
                {
                    let mut parameter_count = parameter_counts.pop().unwrap();
                    if !matches!(last_token, Some(LeftParen)) {
                        parameter_count += 1;
                    }

                    output.push(Token::new(
                        span,
                        TokenKind::Function {
                            name,
                            parameter_count,
                        },
                    ));
                    operators.pop();
                }
            }

            UnaryOperator(..) => {
                if matches!(last_token, Some(UnaryOperator(UnOp::Negate))) {
                    parse_error!(
                        span,
                        "Two (unary) operators in a row (`{token}` and `{}`)",
                        last_token.unwrap()
                    );
                }
                operators.push(token.clone());
            }

            BinaryOperator(operator) => {
                // Detect unary -
                if matches!(
                    last_token,
                    None | Some(Delimiter | LeftParen | UnaryOperator(..) | BinaryOperator(..))
                ) && matches!(operator, BinOp::Subtract)
                {
                    if matches!(last_token, Some(UnaryOperator(..))) {
                        parse_error!(
                            span,
                            "Two (unary) operators in a row (`{token}` and `{}`)",
                            last_token.unwrap()
                        );
                    }
                    operators.push(ParserToken::new(span.clone(), UnaryOperator(UnOp::Negate)));
                    last_token = Some(UnaryOperator(UnOp::Negate));
                    continue;
                }

                if matches!(last_token, Some(UnaryOperator(..) | BinaryOperator(..))) {
                    parse_error!(
                        span,
                        "Two operators in a row (`{token}` and `{}`)",
                        last_token.unwrap()
                    );
                }
                if matches!(last_token, None) {
                    parse_error!(span, "Can't start with a binary (two-operand) operator");
                }
                if matches!(last_token, Some(LeftParen)) {
                    parse_error!(span, "Operator (`{}`) is not valid after a `(`", token);
                }

                let precedence = operator.precedence();
                let left_associative = operator.left_associative();

                loop {
                    match operators.last().map(|tok| (tok.span.clone(), &tok.kind)) {
                        Some((span, BinaryOperator(top_of_stack))) => {
                            let top_precedence = top_of_stack.precedence();

                            if (left_associative && precedence <= top_precedence)
                                || (!left_associative && precedence < top_precedence)
                            {
                                output.push(Token::new(
                                    span,
                                    TokenKind::BinaryOperator(*top_of_stack),
                                ));
                                operators.pop();
                            } else {
                                break;
                            }
                        }
                        Some((span, UnaryOperator(top_of_stack))) => {
                            if !left_associative {
                                break;
                            }
                            output.push(Token::new(span, TokenKind::UnaryOperator(*top_of_stack)));
                            operators.pop();
                        }
                        _ => break,
                    }
                }

                operators.push(token.clone());
            }

            Delimiter => {
                if matches!(last_token, Some(LeftParen | Delimiter)) {
                    parse_error!(span, "Empty function parameter before a `,`");
                }

                if matches!(last_token, Some(BinaryOperator(..) | UnaryOperator(..))) {
                    parse_error!(
                        last_span,
                        "Parameter ends with an operator (`{}`)",
                        last_token.unwrap()
                    );
                }

                if let Some(count) = parameter_counts.last_mut() {
                    *count += 1;
                } else {
                    parse_error!(span, "`,` outside of a function call");
                }

                loop {
                    match operators.last().map(|tok| (tok.span.clone(), &tok.kind)) {
                        Some((span, BinaryOperator(top_of_stack))) => {
                            output.push(Token::new(span, TokenKind::BinaryOperator(*top_of_stack)));
                        }
                        Some((span, UnaryOperator(top_of_stack))) => {
                            output.push(Token::new(span, TokenKind::UnaryOperator(*top_of_stack)));
                        }
                        _ => break,
                    }
                    operators.pop();
                }
            }
        }

        last_token = Some(token.kind);
    }

    if matches!(last_token, Some(BinaryOperator(..) | UnaryOperator(..))) {
        parse_error!(last_span, "Trailing operator (`{}`)", last_token.unwrap());
    }

    pop_until_lparen(&mut operators, &mut output);

    // No tokens should remain
    if !operators.is_empty() {
        let span = last_span.end.saturating_sub(1)..last_span.end;
        parse_error!(span, "Missing a closing `)`");
    }

    Ok(output)
}

/// Last step in the shunting-yard algorithm: pop nodes from operator stack into the output
/// until a left paren ('(') is found. The function does not pop the left paren.
fn pop_until_lparen<'a>(operators: &mut Vec<ParserToken<'a>>, output: &mut Vec<Token<'a>>) {
    loop {
        let top = match operators.last() {
            None
            | Some(ParserToken {
                kind: ParserTokenKind::LeftParen,
                ..
            }) => return,
            _ => operators.pop().unwrap(),
        };

        let span = top.span;
        match top.kind {
            ParserTokenKind::Number(value) => {
                output.push(Token::new(span, TokenKind::Number(value)))
            }
            ParserTokenKind::Variable { name } => {
                output.push(Token::new(span, TokenKind::Variable { name }))
            }
            ParserTokenKind::Function { name } => output.push(Token::new(
                span,
                TokenKind::Function {
                    name,
                    parameter_count: 0,
                },
            )),
            ParserTokenKind::BinaryOperator(operator) => {
                output.push(Token::new(span, TokenKind::BinaryOperator(operator)))
            }
            ParserTokenKind::UnaryOperator(operator) => {
                output.push(Token::new(span, TokenKind::UnaryOperator(operator)))
            }
            ParserTokenKind::RightParen => unreachable!("operators never contains right parens"),
            ParserTokenKind::Delimiter => unreachable!("operators never contains delimiters"),
            ParserTokenKind::LeftParen => return,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ParserToken<'a> {
    pub kind: ParserTokenKind<'a>,
    pub span: Range<usize>,
}

impl<'a> ParserToken<'a> {
    pub fn new(span: Range<usize>, kind: ParserTokenKind<'a>) -> Self {
        Self { kind, span }
    }
}

/// Represents a token internal to the parser.
#[derive(Debug, Clone)]
pub enum ParserTokenKind<'a> {
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
        self.kind.fmt(f)
    }
}

impl std::fmt::Display for ParserTokenKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ParserTokenKind::Number(ref x) => write!(f, "{x}"),
            ParserTokenKind::Variable { name } => f.write_str(name),
            ParserTokenKind::Function { name } => f.write_str(name),
            ParserTokenKind::Delimiter => f.write_str(","),
            ParserTokenKind::BinaryOperator(op) => f.write_str(op.display_name()),
            ParserTokenKind::UnaryOperator(op) => match op {
                UnaryOperator::Negate => f.write_str("-"),
                UnaryOperator::Not => f.write_str("!"),
            },
            ParserTokenKind::LeftParen => f.write_str("("),
            ParserTokenKind::RightParen => f.write_str(")"),
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

    pub fn position(&self) -> usize {
        self.index
    }

    /// Advance cursor until a non-space character is found.
    fn skip_spaces(&mut self) {
        while self.index < self.source.len() && self.source[self.index].is_ascii_whitespace() {
            self.index += 1;
        }
    }

    /// Greedily reads (consumes) all consecutive digits/periods/underscores, attempts
    /// to parse them as a number, and leaves `self.index` pointing to the first
    /// excluded character.
    fn read_number(&mut self) -> ParseResult<Value> {
        // Read radix from prefixes '0b', '0x' and '0X', but only if
        // they are followed by another digit, so that '0x' definitely
        // doesn't mean just "0*x".
        fn read_radix(src: &BStr) -> Option<(i32, &'static str)> {
            if src.len() < 3 || src[0] != b'0' {
                return None;
            }
            match src[1] {
                b'x' | b'X' if src[2].is_ascii_hexdigit() => {
                    return Some((16, "0123456789abcdefABCDEF._"))
                }
                b'b' if src[2] == b'0' || src[2] == b'1' => return Some((2, "01._")),
                _ => return None,
            }
        }

        let mut radix = 10;
        let mut valid_chars = "0123456789._";
        if let Some((new_radix, new_valid_chars)) = read_radix(&self.source[self.index..]) {
            radix = new_radix;
            valid_chars = new_valid_chars;
            self.index += 2;
        }

        let mut end_index = self
            .source
            .iter()
            .skip(self.index)
            .position(|c| !valid_chars.as_bytes().contains(c))
            .map_or(self.source.len(), |i| i + self.index);

        // Explicitly disallow trailing `_` (so `1000_` is not valid).
        while let Some(b'_') = self.source.get((end_index as isize - 1) as usize) {
            end_index -= 1;
        }

        let span = self.index..end_index;

        // Improve error message when a non-binary digit is after a binary input by erroring here
        // with all needed information available. Nothing breaks without this.
        if radix == 2 && matches!(self.source.get(end_index), Some(b'0'..=b'9')) {
            parse_error!(
                span,
                "Digit '{}' not valid in a binary string!",
                self.source[end_index] as char
            );
        }

        // SAFETY: this is safe, because byte_str can necessarily only contain ascii digits or an ascii dot,
        // and ascii is valid UTF-8. Both types have the same representation. Empty source is also fine.
        let string: &str = unsafe { std::mem::transmute(&self.source[self.index..end_index]) };
        let mut string = string.to_owned();

        if string.starts_with(".") {
            // Reviewer suggestion: allow leading `.`. Rug doesn't allow
            // a leading decimal point, so fix by appending a zero when it's missing.
            string.insert(0, '0');
        }
        if string.ends_with(".") {
            string.push('0');
        }
        // Allow underscores in numbers
        //string = string.replace('_', "");

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
                rug::Float::parse_radix(string, radix)
                    .map_err(|e| make_parse_error!(span, "{e}"))?,
            ));
            return Ok(Value::Complex(value));
        }

        if let Some(index) = period_index {
            if radix != 10 {
                let mut float = rug::Float::new(self.precision_bits);
                float.assign(
                    rug::Float::parse_radix(&string, radix)
                        .map_err(|e| make_parse_error!(span, "{e}"))?,
                );

                if let Some(rational) = float.to_rational() {
                    return Ok(Value::Rational(rational));
                }
                println!("Warning: non-exact parsing");
                return Ok(Value::Decimal(float));
            }

            // All inputs entered in the form `<whole part>.<fract part>` are necessary not irrational, so
            // might as well parse them as exact rationals by parsing `123.456` as `123456/1000` and letting
            // the library canonicalize it. Note: this gives better accuracy than Float::parse, because
            // floats are inherently limited in precision (they take the number of bits as input), whereas rationals
            // are truly arbitrary-precision.

            let whole_part_str = &string[..index];
            let fract_part_str = &string[index + 1..];

            let mut whole_part = rug::Integer::new();
            whole_part.assign(
                rug::Integer::parse(whole_part_str)
                    .map_err(|e| make_parse_error!(span.clone(), "{e}"))?,
            );

            let mut fract_part = rug::Integer::new();
            fract_part.assign(
                rug::Integer::parse(fract_part_str)
                    .map_err(|e| make_parse_error!(span.clone(), "{e}"))?,
            );

            let mut denominator = rug::Integer::new();
            denominator.assign(10);
            denominator.pow_assign(
                u32::try_from(fract_part_str.len()).map_err(|e| make_parse_error!(span, "{e}"))?,
            );

            whole_part *= &denominator;
            whole_part += fract_part;

            let rational = rug::Rational::from((whole_part, denominator));

            return Ok(Value::Rational(rational));
        }

        let res = rug::Rational::parse_radix(string, radix)
            .map_err(|e| make_parse_error!(span, "{e}"))?;
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
    fn read_token(&mut self) -> ParseResult<ParserTokenKind<'a>> {
        if let Some((operator, advance)) =
            operators::BinaryOperator::from_chars(&self.source[self.index..])
        {
            self.index += advance;
            return Ok(ParserTokenKind::BinaryOperator(operator));
        }

        // Inject implicit * for `2x`
        if std::mem::replace(&mut self.last_was_number, false)
            && self.source[self.index].is_ascii_alphabetic()
        {
            return Ok(ParserTokenKind::BinaryOperator(BinaryOperator::Multiply));
        }

        let c = self.source[self.index];
        if c == b'!' {
            self.index += 1;
            return Ok(ParserTokenKind::UnaryOperator(UnaryOperator::Not));
        }
        if c == b'(' {
            self.index += 1;
            return Ok(ParserTokenKind::LeftParen);
        }
        if c == b')' {
            self.index += 1;
            return Ok(ParserTokenKind::RightParen);
        }
        if c == b',' {
            self.index += 1;
            return Ok(ParserTokenKind::Delimiter);
        }

        if c == b'.' || c.is_ascii_digit() {
            return Ok(ParserTokenKind::Number(self.read_number()?));
        }
        if c.is_ascii_alphabetic() {
            let name = self.read_identifier();

            let mut next_index = self.index;
            while self
                .source
                .get(next_index)
                .filter(|&&c| c.is_ascii_whitespace())
                .is_some()
            {
                next_index += 1;
            }

            if self.source.get(next_index) == Some(&b'(') {
                self.index = next_index;
                return Ok(ParserTokenKind::Function { name });
            }

            if name == "true" {
                return Ok(ParserTokenKind::Number(Value::Boolean(true)));
            }
            if name == "false" {
                return Ok(ParserTokenKind::Number(Value::Boolean(false)));
            }

            return Ok(ParserTokenKind::Variable { name });
        }

        self.index += 1;
        let pos = self.index;
        parse_error!(
            pos - 1..pos,
            "Unexpected token `{}` (at `{}`)",
            c as char,
            unsafe { std::mem::transmute::<&BStr, &str>(&self.source[self.index - 1..]) }
        );
    }
}

impl<'a> Iterator for TokenIterator<'a> {
    type Item = ParseResult<ParserToken<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_spaces();

        if self.index == self.source.len() {
            return None;
        }

        let span_start = self.index;
        let token = self.read_token();
        let span = span_start..self.index;

        Some(token.map(|tok| ParserToken::new(span, tok)))
    }
}

impl<'a> From<&'a str> for TokenIterator<'a> {
    fn from(source: &'a str) -> Self {
        Self::of(source, DEFAULT_PRECISION)
    }
}

#[rustfmt::skip] // rustfmt keeps splitting the asserts which ends up actually hurting readability
#[cfg(test)]
mod tests {
    use crate::{operators::BinaryOperator, operators::UnaryOperator, parser::TokenKind, state::Value};

    use super::{infix_to_postfix, Token};

    // A macro to make building expected solutions not enormously verbose. Macros are unfortunately
    // fairly unreadable, but you can probably mostly infer what it does from the usage in below tests.
    macro_rules! tokens {
        (+) => {TokenKind::BinaryOperator(BinaryOperator::Add)};
        (-) => {TokenKind::BinaryOperator(BinaryOperator::Subtract)};
        (*) => {TokenKind::BinaryOperator(BinaryOperator::Multiply)};
        (/) => {TokenKind::BinaryOperator(BinaryOperator::Divide)};
        (^) => {TokenKind::BinaryOperator(BinaryOperator::Power)};
        (%) => {TokenKind::BinaryOperator(BinaryOperator::Remainder)};
        (~) => {TokenKind::UnaryOperator(UnaryOperator::Negate)};
        ($lit:literal) => {TokenKind::Number(Value::Rational(rug::Rational::from($lit))) };
        ($name:ident) => (TokenKind::Variable{ name: stringify!($name) });
        // Loop over space-separated input tokens, parse them with the token! macro, and build
        // a vector out of them.
        ($($tok:tt)+) => {
            vec![$(tokens!($tok),)*]
        }
    }

    // The spans are irrelevant for tests, so this exists to
    // map them to the actually relevant TokenKinds.
    fn unwrap_tokens(tokens: Vec<Token>) -> Vec<TokenKind> {
        tokens.into_iter().map(|tok| tok.kind).collect()
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
        assert!(infix_to_postfix(".0.0").is_err());
        assert!(infix_to_postfix("0.0.").is_err());
        assert!(infix_to_postfix("0.0.0").is_err());
        assert!(infix_to_postfix("0..").is_err());
        assert!(infix_to_postfix("..0").is_err());
        assert!(infix_to_postfix(".0.").is_err());
    }

    #[test]
    fn test_valid_expressions() {
        assert_eq!(tokens![5 5 +], unwrap_tokens(infix_to_postfix("5. + 5.").unwrap()));
        assert_eq!(tokens![5 5 + 3 3 + *], unwrap_tokens(infix_to_postfix("(5 + 5) * (3 + 3)").unwrap()));
        assert_eq!(tokens![5 5 + 3 * 3 +], unwrap_tokens(infix_to_postfix("(5 + 5) * 3 + 3").unwrap()));
        assert_eq!(tokens![5 5 3 * + 3 +], unwrap_tokens(infix_to_postfix("5 + 5 * 3 + 3").unwrap()));
        assert_eq!(tokens![5 5 3 3 + * +], unwrap_tokens(infix_to_postfix("5 + 5 * (3 + 3)").unwrap()));
    }

    #[test]
    fn test_unary_works() {
        // ~ represents unary minus 
        assert_eq!(tokens![5 ~], unwrap_tokens(infix_to_postfix("-5").unwrap()));
        assert_eq!(tokens![5 ~ 5 ~ -], unwrap_tokens(infix_to_postfix("-5 - -5").unwrap()));
        assert_eq!(tokens![2 3 + ~], unwrap_tokens(infix_to_postfix("-(2+3)").unwrap()));
        assert_eq!(tokens![5 3 ~ /], unwrap_tokens(infix_to_postfix("5 / -3").unwrap()));
    }

    #[test]
    fn test_power_operator_works() {
        assert_eq!(unwrap_tokens(infix_to_postfix("2^(3^4)").unwrap()), unwrap_tokens(infix_to_postfix("2^3^4").unwrap()));
        assert_eq!(tokens![2 3 4 ^ ^], unwrap_tokens(infix_to_postfix("2^3^4").unwrap()));
        assert_eq!(unwrap_tokens(infix_to_postfix("-5^2").unwrap()), unwrap_tokens(infix_to_postfix("-(5^2)").unwrap()));
        assert_eq!(tokens![5 2 ^ ~], unwrap_tokens(infix_to_postfix("-5^2").unwrap()));
    }

    #[test]
    fn test_variables_work() {
        assert_eq!(tokens![a 3 +], unwrap_tokens(infix_to_postfix("a + 3").unwrap()));
        assert_eq!(tokens![variable 3 +], unwrap_tokens(infix_to_postfix("variable + 3").unwrap()));
        assert_eq!(tokens![x x * y y * -], unwrap_tokens(infix_to_postfix("x*x - y*y").unwrap()));
    }

    #[test]
    fn test_function_calls_work() {
        assert!(infix_to_postfix("foo(a)").is_ok());
        assert!(infix_to_postfix("bar ( a , b )").is_ok());
        assert!(infix_to_postfix("f(a,b,c)").is_ok());
    }

    #[test]
    fn test_implicit_multiply() {
        assert_eq!(tokens![2 x *], unwrap_tokens(infix_to_postfix("2x").unwrap()));
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
