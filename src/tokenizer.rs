use std::ops::Range;

use bstr::BStr;
use rug::{ops::PowAssign, Assign};

use crate::{
    operators::{self, BinaryOperator, UnaryOperator},
    infix_to_postfix::{make_parse_error, parse_error, ParseResult},
    state::Value,
    PRECISION,
};

#[derive(Clone)]
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
#[derive(Clone)]
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
    #[cfg_attr(coverage, no_coverage)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::fmt::Display for ParserTokenKind<'_> {
    #[cfg_attr(coverage, no_coverage)]
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
    // For returning multiple values for one symbol
    queued: Option<ParserTokenKind<'a>>,
    last_was_number: bool,
    precision_bits: u32,
}

impl<'a> TokenIterator<'a> {
    /// Creates a new iterator over the tokens in the source string.
    pub fn of(source: &'a str, precision_bits: u32) -> Self {
        Self {
            source: source.into(), // Guaranteed to be free and infallible
            index: 0,
            queued: None,
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

    /// Greedily reads (consumes) all consecutive digits/periods/underscores
    /// and leaves `self.index` pointing to the first excluded character.
    /// Returns the number string, its radix, and its start/end byte indices as a Range.
    ///
    /// Note that the returned string may be longer than the span, since it might have
    /// been altered after reading.
    fn read_number_as_string(&mut self) -> ParseResult<(String, i32, Range<usize>)> {
        // Read radix from prefixes '0b', '0x' and '0X', but only if
        // they are followed by another digit, so that '0x' definitely
        // doesn't mean just "0*x".
        fn read_radix(src: &BStr) -> Option<(i32, &'static str)> {
            if src.len() < 3 || src[0] != b'0' {
                return None;
            }
            match src[1] {
                b'x' | b'X' if src[2].is_ascii_hexdigit() => {
                    return Some((16, "0123456789abcdefABCDEF._ "))
                }
                b'b' if src[2] == b'0' || src[2] == b'1' => return Some((2, "01._ ")),
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

        // Explicitly exclude trailing `_`s (so `1000_` is not valid).
        while let Some(b'_') = self.source.get((end_index as isize - 1) as usize) {
            end_index -= 1;
        }

        let span = self.index..end_index;

        // Improve error message when a non-binary digit is after a binary input by erroring here
        // with all needed information available. Nothing breaks without this.
        if radix == 2 && matches!(self.source.get(end_index), Some(b'0'..=b'9')) {
            self.index = end_index;
            parse_error!(span, "Digit '{}' not valid in a binary string!", self.source[end_index] as char);
        }

        // SAFETY: this is safe, because byte_str can necessarily only contain ascii digits or an ascii dot,
        // and ascii is valid UTF-8. Both types have the same representation. Empty source is also fine.
        let string: &str = unsafe { std::mem::transmute(&self.source[self.index..end_index]) };
        let mut string = string.to_owned();

        if string == "." {
            self.index = end_index;
            parse_error!(span, "`.` is not a valid number");
        }

        if string.starts_with(".") {
            // Reviewer suggestion: allow leading `.`. Rug doesn't allow
            // a leading decimal point, so fix by appending a zero when it's missing.
            string.insert(0, '0');
        }
        if string.ends_with(".") {
            string.push('0');
        }

        self.index = end_index;
        self.last_was_number = true;

        Ok((string, radix, span))
    }

    /// Calls `read_number_as_string()` and attempts to parse it to a Value.
    fn read_number(&mut self) -> ParseResult<Value> {
        let (string, radix, span) = self.read_number_as_string()?;
        let period_index = string.find('.');

        if let Some(b'i') = self.source.get(self.index) {
            self.last_was_number = false; // don't allow implicit symbols (mostly *) here
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
        let mut end_index = self.index;

        while end_index < self.source.len() {
            let c = self.source[end_index];
            if matches!(c, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_') {
                end_index += 1;
                continue;
            }

            // Superscript digits are of course valid utf8, but serve a special purpose,
            // so don't accept one.
            if self.read_superscript_at(end_index).is_some() {
                break;
            }

            // UTF8 support. See this table for what's going on: https://en.wikipedia.org/wiki/UTF-8#Encoding
            if c & 0b11100000 == 0b11000000 {
                end_index += 2;
            } else if c & 0b11110000 == 0b11100000 {
                end_index += 3;
            } else if c & 0b11111000 == 0b11110000 {
                end_index += 4;
            } else {
                break;
            }
        }

        let byte_str = &self.source[self.index..end_index];
        // SAFETY: this is safe, because ascii is always valid utf8, and non-ascii symbols are checked for above.
        // Additionally, both types have the same representation. Empty source is also fine.
        let str_slice: &str = unsafe { std::mem::transmute(byte_str) };

        self.index = end_index;

        str_slice
    }

    /// Determines the type of, and reads, the next token, incrementing `self.index`
    /// to point to the start of the next token.
    /// This method assumes that there are no spaces at the cursor position and that
    /// there are still tokens to be read.
    fn read_token(&mut self) -> ParseResult<ParserTokenKind<'a>> {
        let last_was_number = std::mem::replace(&mut self.last_was_number, false);

        if let Some((operator, advance)) =
            operators::BinaryOperator::from_chars(&self.source[self.index..])
        {
            self.index += advance;
            return Ok(ParserTokenKind::BinaryOperator(operator));
        }

        if let Some((kind, advance)) = self.read_simple_symbol() {
            self.index += advance;
            return Ok(kind);
        }

        let c = self.source[self.index];
        if c == b'.' || c.is_ascii_digit() {
            return Ok(ParserTokenKind::Number(self.read_number()?));
        }

        let ident = self.read_identifier();
        if !ident.is_empty() {
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
                return Ok(ParserTokenKind::Function { name: ident });
            }

            if last_was_number {
                self.queued = Some(ParserTokenKind::Variable { name: ident });
                return Ok(ParserTokenKind::BinaryOperator(BinaryOperator::Multiply));
            }

            return Ok(ParserTokenKind::Variable { name: ident });
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

    /// Reads an individual UTF8 superscript digit (², ³, ...) and returns its
    /// numeric value and byte length.
    fn read_superscript_at(&mut self, start_index: usize) -> Option<(i32, usize)> {
        let bytes = &self.source[start_index..] as &[u8];

        for (i, &needle) in ["⁰", "¹", "²", "³", "⁴", "⁵", "⁶", "⁷", "⁸", "⁹"]
            .iter()
            .enumerate()
        {
            if bytes.starts_with(needle.as_bytes()) {
                return Some((i as i32, needle.len()));
            }
        }
        None
    }

    fn read_simple_symbol(&mut self) -> Option<(ParserTokenKind<'a>, usize)> {
        let bytes = &self.source[self.index..] as &[u8];

        if let Some((digit, byte_len)) = self.read_superscript_at(self.index) {
            self.queued = Some(ParserTokenKind::Number(Value::Rational(
                rug::Rational::from((digit, 1)),
            )));
            return Some((
                ParserTokenKind::BinaryOperator(BinaryOperator::Power),
                byte_len,
            ));
        }

        let (kind, advance) = match bytes {
            &[b'(', ..] => (ParserTokenKind::LeftParen, 1),
            &[b')', ..] => (ParserTokenKind::RightParen, 1),
            &[b'!', ..] => (ParserTokenKind::UnaryOperator(UnaryOperator::Not), 1),
            &[b',', ..] => (ParserTokenKind::Delimiter, 1),

            // Check the next byte to make sure `true` and `false` can also be used as a part
            // of an identifier, e.g. "trueWhenZero".
            &[b't', b'r', b'u', b'e', next, ..] if !next.is_ascii() => {
                (ParserTokenKind::Number(Value::Boolean(true)), 4)
            }
            &[b't', b'r', b'u', b'e'] => (ParserTokenKind::Number(Value::Boolean(true)), 4),

            &[b'f', b'a', b'l', b's', b'e', next, ..] if !next.is_ascii() => {
                (ParserTokenKind::Number(Value::Boolean(false)), 5)
            }
            &[b'f', b'a', b'l', b's', b'e'] => (ParserTokenKind::Number(Value::Boolean(false)), 5),

            _ => return None,
        };
        Some((kind, advance))
    }
}

impl<'a> Iterator for TokenIterator<'a> {
    type Item = ParseResult<ParserToken<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(queued) = self.queued.take() {
            return Some(Ok(ParserToken::new(self.index..self.index, queued)));
        }

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
        Self::of(source, PRECISION)
    }
}

// Tested along with shunting yard in parser.rs.