use std::ops::Range;

use thiserror::Error;
use Result;

use crate::{
    operators::{BinaryOperator as BinOp, UnaryOperator as UnOp},
    state::Value,
    tokenizer::{ParserToken, ParserTokenKind::{self, *}, TokenIterator},
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
        crate::infix_to_postfix::ParseError {
            message: format!($($arg)*),
            span: $span
        }
    };
}

pub(crate) use make_parse_error;

macro_rules! parse_error {
    ($span:expr, $($arg:tt)*) => {
        return Err(Box::new(crate::infix_to_postfix::make_parse_error!($span, $($arg)*)))
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
    BinaryOperator(BinOp),
    UnaryOperator(UnOp),
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
    match ShuntingYard::run(&mut iterator) {
        Ok(result) => Ok(result),
        Err(e) => parse_error!(e.span, "Syntax error: {e}"),
    }
}

/// State needed for the execution of the algorithm.
struct ShuntingYard<'a> {
    output: Vec<Token<'a>>,
    // Runtime invariant: `operators` *only* contains unary/binary operators.
    operators: Vec<ParserToken<'a>>,
    parameter_counts: Vec<u32>,

    last_token: Option<ParserTokenKind<'a>>,
    last_span: Range<usize>,
}

#[rustfmt::skip]
impl<'a> ShuntingYard<'a> {
    fn run(tokens: &mut TokenIterator<'a>) -> ParseResult<Vec<Token<'a>>> {
        let mut instance = Self {
            output: Vec::new(),
            operators: Vec::new(),
            parameter_counts: Vec::new(),
            last_token: None,
            last_span: 0..0,
        };

        instance.run_inner(tokens)
    }

    /// Actual implementation. Currently, this assumes that the struct has just been initialized
    /// with default values, so re-using the instance will not work.
    fn run_inner(&mut self, tokens: &mut TokenIterator<'a>) -> ParseResult<Vec<Token<'a>>> {
        while let Some(token) = tokens.next() {
            let token = token?; // Check for parsing errors
            let span = token.span.clone();
            self.last_span = span.clone();

            match token.kind {
                Number(ref value) => {
                    self.assert_value_is_valid_here(&token)?;
                    self.output.push(Token::new(span, TokenKind::Number(value.clone())));
                }

                Variable { name } => {
                    self.assert_value_is_valid_here(&token)?;
                    self.output.push(Token::new(span, TokenKind::Variable { name }));
                }

                Function { .. } => {
                    self.assert_value_is_valid_here(&token)?;
                    self.operators.push(token.clone());
                    self.parameter_counts.push(0);
                }

                LeftParen => {
                    if matches!(self.last_token, Some(Number(..) | RightParen)) {
                        parse_error!(span, "`(` is not valid after `{}`", self.last_token.as_ref().unwrap());
                    }
                    self.operators.push(token.clone());
                }

                RightParen => {
                    self.process_right_paren(span)?;
                }

                UnaryOperator(..) => {
                    if matches!(self.last_token, Some(UnaryOperator(UnOp::Negate))) {
                        parse_error!(
                            span,
                            "Two (unary) operators in a row (`{token}` and `{}`)",
                            self.last_token.as_ref().unwrap()
                        );
                    }
                    self.operators.push(token.clone());
                }

                BinaryOperator(operator) => {
                    if self.process_binary_operator(operator, span)? {
                        continue; // see comment on process_binary_operator
                    }
                }

                Delimiter => {
                    self.process_delimiter(span)?;
                }
            }

            self.last_token = Some(token.kind);
        }

        if matches!(self.last_token, Some(BinaryOperator(..) | UnaryOperator(..))) {
            parse_error!(self.last_span.clone(), "Trailing operator (`{}`)", self.last_token.as_ref().unwrap());
        }

        self.pop_until_lparen();

        // No tokens should remain
        if !self.operators.is_empty() {
            parse_error!(self.last_span.clone(), "Missing a closing `)`");
        }

        Ok(std::mem::take(&mut self.output))
    }

    fn process_right_paren(&mut self, span: Range<usize>) -> ParseResult<()> {
        if matches!(self.last_token, Some(Delimiter)) {
            parse_error!(span, "Empty function parameter after `,`");
        }

        if matches!(self.last_token, Some(LeftParen))
            && !matches!(&self.operators[..], &[.., ParserToken { kind: ParserTokenKind::Function { .. }, .. }, _ ])
        {
            let span = span.start.saturating_sub(1)..span.end;
            parse_error!(span, "Empty parentheses is invalid");
        }

        if matches!(self.last_token, Some(BinaryOperator(..) | UnaryOperator(..))) {
            parse_error!(
                self.last_span.clone(),
                "`)` is not valid after an operator (`{}`)",
                self.last_token.as_ref().unwrap()
            );
        }

        self.pop_until_lparen();
        // If there are tokens left, it is an opening paren, so pop that. Otherwise,
        // there were more closing parens than opening parens, so report that.
        if self.operators.pop().is_none() {
            parse_error!(span, "Too many closing parentheses");
        }
        // If on top of operators is a function, that means this ) marks the end of the
        // function's parameters.
        if let Some(ParserToken {
            kind: Function { name },
            ..
        }) = self.operators.last()
        {
            let mut parameter_count = self.parameter_counts.pop().unwrap();
            if !matches!(self.last_token, Some(LeftParen)) {
                parameter_count += 1;
            }

            self.output.push(Token::new(span, TokenKind::Function { name, parameter_count }));
            self.operators.pop();
        }
        Ok(())
    }

    /// As a special case since unary minus is hard to distinguish from regular subtraction;
    /// this function returns `true` if it has modified `self.last_token`, meaning it should not be overridden
    /// by the calling function.
    fn process_binary_operator(&mut self, operator: BinOp, span: Range<usize>) -> ParseResult<bool> {
        // Detect unary -
        if matches!(self.last_token, None | Some(Delimiter | LeftParen | UnaryOperator(..) | BinaryOperator(..))) 
            && matches!(operator, BinOp::Subtract)
        {
            if matches!(self.last_token, Some(UnaryOperator(..))) {
                parse_error!(span, "Two (unary) operators in a row (`{}` and `{}`)",
                    operator.display_name(), self.last_token.as_ref().unwrap()
                );
            }
            self.operators.push(ParserToken::new(span.clone(), UnaryOperator(UnOp::Negate)));
            self.last_token = Some(UnaryOperator(UnOp::Negate));
            return Ok(true);
        }

        if matches!(self.last_token, Some(Delimiter)) {
            parse_error!(span, "Can't start parameter with a binary (two-operand) operator")
        }

        if matches!(self.last_token, Some(UnaryOperator(..) | BinaryOperator(..))) {
            parse_error!(span, "Two operators in a row (`{}` and `{}`)",
                operator.display_name(), self.last_token.as_ref().unwrap()
            );
        }
        if matches!(self.last_token, None) {
            parse_error!(span, "Can't start with a binary (two-operand) operator");
        }
        if matches!(self.last_token, Some(LeftParen)) {
            parse_error!(span, "Operator (`{}`) is not valid after a `(`", operator.display_name());
        }

        let precedence = operator.precedence();
        let left_associative = operator.left_associative();

        loop {
            match self.operators.last().map(|tok| (tok.span.clone(), &tok.kind)) {
                Some((span, BinaryOperator(top_of_stack))) => {
                    let top_precedence = top_of_stack.precedence();

                    if (left_associative && precedence <= top_precedence)
                        || (!left_associative && precedence < top_precedence)
                    {
                        self.output.push(Token::new(
                            span,
                            TokenKind::BinaryOperator(*top_of_stack),
                        ));
                        self.operators.pop();
                    } else {
                        break;
                    }
                }
                Some((span, UnaryOperator(top_of_stack))) => {
                    if !left_associative {
                        break;
                    }
                    self.output.push(Token::new(span, TokenKind::UnaryOperator(*top_of_stack)));
                    self.operators.pop();
                }
                _ => break,
            }
        }

        self.operators.push(ParserToken::new(span, ParserTokenKind::BinaryOperator(operator)));
        Ok(false)
    }

    fn process_delimiter(&mut self, span: Range<usize>) -> ParseResult<()> {
        use ParserTokenKind::*;

        if matches!(self.last_token, Some(LeftParen | Delimiter)) {
            parse_error!(span, "Empty function parameter before a `,`");
        }

        if matches!(self.last_token, Some(BinaryOperator(..) | UnaryOperator(..))) {
            parse_error!(
                self.last_span.clone(),
                "Parameter ends with an operator (`{}`)",
                self.last_token.as_ref().unwrap()
            );
        }

        if let Some(count) = self.parameter_counts.last_mut() {
            *count += 1;
        } else {
            parse_error!(span, "`,` outside of a function call");
        }

        loop {
            match self.operators.last().map(|tok| (tok.span.clone(), &tok.kind)) {
                Some((span, BinaryOperator(top_of_stack))) => {
                    self.output.push(Token::new(span, TokenKind::BinaryOperator(*top_of_stack)));
                }
                Some((span, UnaryOperator(top_of_stack))) => {
                    self.output.push(Token::new(span, TokenKind::UnaryOperator(*top_of_stack)));
                }
                _ => break,
            }
            self.operators.pop();
        }
        Ok(())
    }

    fn assert_value_is_valid_here(
        &self,
        token: &ParserToken,
    ) -> ParseResult<()> {
        use ParserTokenKind::*;
        if !matches!(
            self.last_token,
            None | Some(Delimiter | LeftParen | UnaryOperator(..) | BinaryOperator(..))
        ) {
            parse_error!(
                token.span.clone(),
                "A value (`{token}`) is not valid after `{}`",
                self.last_token.as_ref().unwrap()
            );
        }
        Ok(())
    }

    /// Last step in the shunting-yard algorithm: pop nodes from operator stack into the output
    /// until a left paren ('(') is found. The function does not pop the left paren.
    fn pop_until_lparen(&mut self) {
        loop {
            let top = match self.operators.last() {
                None | Some(ParserToken {kind: ParserTokenKind::LeftParen, ..}) => return,
                _ => self.operators.pop().unwrap(),
            };

            let span = top.span;
            match top.kind {
                ParserTokenKind::BinaryOperator(operator) => {
                    self.output.push(Token::new(span, TokenKind::BinaryOperator(operator)))
                }
                ParserTokenKind::UnaryOperator(operator) => {
                    self.output.push(Token::new(span, TokenKind::UnaryOperator(operator)))
                }
                _ => unreachable!()
            }
        }
    }
}

#[rustfmt::skip] // rustfmt keeps splitting the asserts which ends up actually hurting readability
#[cfg(test)]
mod tests {
    use super::*;

    // A macro to make building expected solutions not enormously verbose. Macros are unfortunately
    // fairly unreadable, but you can probably mostly infer what it does from the usage in below tests.
    macro_rules! tokens {
        (+) =>  {TokenKind::BinaryOperator(BinOp::Add)};
        (-) =>  {TokenKind::BinaryOperator(BinOp::Subtract)};
        (*) =>  {TokenKind::BinaryOperator(BinOp::Multiply)};
        (/) =>  {TokenKind::BinaryOperator(BinOp::Divide)};
        (^) =>  {TokenKind::BinaryOperator(BinOp::Power)};
        (%) =>  {TokenKind::BinaryOperator(BinOp::Remainder)};
        (&&) => {TokenKind::BinaryOperator(BinOp::LogicalAnd)};
        (||) => {TokenKind::BinaryOperator(BinOp::LogicalOr)};
        (&) =>  {TokenKind::BinaryOperator(BinOp::BitAnd)};
        (|) =>  {TokenKind::BinaryOperator(BinOp::BitOr)};
        (xor) => {TokenKind::BinaryOperator(BinOp::BitXor)};
        (<=) => {TokenKind::BinaryOperator(BinOp::LequalTo)};
        (>=) => {TokenKind::BinaryOperator(BinOp::GequalTo)};
        (<<) => {TokenKind::BinaryOperator(BinOp::BitLeftShift)};
        (>>) => {TokenKind::BinaryOperator(BinOp::BitRightShift)};
        (<) =>  {TokenKind::BinaryOperator(BinOp::LessThan)};
        (>) =>  {TokenKind::BinaryOperator(BinOp::GreaterThan)};
        (!=) => {TokenKind::BinaryOperator(BinOp::NequalTo)};
        (==) => {TokenKind::BinaryOperator(BinOp::EqualTo)};
        (!) =>  {TokenKind::UnaryOperator(UnOp::Not)};
        (~) =>  {TokenKind::UnaryOperator(UnOp::Negate)};
        (true) => {TokenKind::Number(Value::Boolean(true))};
        (false) => {TokenKind::Number(Value::Boolean(false))};
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
        assert!(infix_to_postfix(")(").is_err());
        assert!(infix_to_postfix("()(").is_err());
        assert!(infix_to_postfix(")()").is_err());
    }

    #[test]
    fn test_valid_numbers_are_accepted() {
        assert!(infix_to_postfix("0").is_ok());
        assert!(infix_to_postfix("0.0").is_ok());
        assert!(infix_to_postfix("0.").is_ok());
        assert!(infix_to_postfix(".0").is_ok());
        assert!(infix_to_postfix("3.1415936535").is_ok());
        assert!(infix_to_postfix("2i").is_ok());
    }

    #[test]
    fn test_valid_binary_and_hex_inputs_are_accepted() {
        assert!(infix_to_postfix("0b001001011").is_ok());
        assert!(infix_to_postfix("0xabCD1234").is_ok());
        assert!(infix_to_postfix("0xab.CD1234").is_ok());
        assert!(infix_to_postfix("0b11100.00111").is_ok());
    }

    #[test]
    fn test_invalid_numbers_are_rejected() {
        assert!(infix_to_postfix(".0.0").is_err());
        assert!(infix_to_postfix("0.0.").is_err());
        assert!(infix_to_postfix("0.0.0").is_err());
        assert!(infix_to_postfix("0..").is_err());
        assert!(infix_to_postfix("..0").is_err());
        assert!(infix_to_postfix(".0.").is_err());
        assert!(infix_to_postfix(".").is_err());
        assert!(infix_to_postfix("_.").is_err());
    }

    #[test]
    fn test_some_valid_expressions() {
        assert_eq!(tokens![5 5 +], unwrap_tokens(infix_to_postfix("5. + 5.").unwrap()));
        assert_eq!(tokens![5 5 + 3 3 + *], unwrap_tokens(infix_to_postfix("(5 + 5) * (3 + 3)").unwrap()));
        assert_eq!(tokens![5 5 + 3 * 3 +], unwrap_tokens(infix_to_postfix("(5 + 5) * 3 + 3").unwrap()));
        assert_eq!(tokens![5 5 3 * + 3 +], unwrap_tokens(infix_to_postfix("5 + 5 * 3 + 3").unwrap()));
        assert_eq!(tokens![5 5 3 3 + * +], unwrap_tokens(infix_to_postfix("5 + 5 * (3 + 3)").unwrap()));
    }

    #[test]
    fn test_unary_negate_works() {
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
        // I don't want implicit multiplication to work with parentheses
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

    #[test]
    fn test_all_valid_operators_are_recognized() {
        fn test_with_and_without_spaces(tokens: Vec<TokenKind>, expression: &str) {
            assert_eq!(tokens, unwrap_tokens(infix_to_postfix(expression).unwrap()));
            assert_eq!(tokens, unwrap_tokens(infix_to_postfix(expression.replace(' ', "").as_str()).unwrap()));    
        }

        test_with_and_without_spaces(tokens![1 1 +], "1 + 1");
        test_with_and_without_spaces(tokens![1 1 -], "1 - 1");
        test_with_and_without_spaces(tokens![1 1 *], "1 * 1");
        test_with_and_without_spaces(tokens![1 1 /], "1 / 1");
        test_with_and_without_spaces(tokens![1 1 %], "1 % 1");
        test_with_and_without_spaces(tokens![1 1 ^], "1 ^ 1");
        test_with_and_without_spaces(tokens![1 1 <], "1 < 1");
        test_with_and_without_spaces(tokens![1 1 >], "1 > 1");
        test_with_and_without_spaces(tokens![1 1 <=], "1 <= 1");
        test_with_and_without_spaces(tokens![1 1 >=], "1 >= 1");
        test_with_and_without_spaces(tokens![1 1 ==], "1 == 1");
        test_with_and_without_spaces(tokens![1 1 !=], "1 != 1");
        test_with_and_without_spaces(tokens![1 1 &&], "1 && 1");
        test_with_and_without_spaces(tokens![1 1 ||], "1 || 1");
        test_with_and_without_spaces(tokens![1 1 &], "1 & 1");
        test_with_and_without_spaces(tokens![1 1 |], "1 | 1");
        test_with_and_without_spaces(tokens![1 1 xor], "1 xor 1");
        test_with_and_without_spaces(tokens![1 1 <<], "1 << 1");
        test_with_and_without_spaces(tokens![1 1 >>], "1 >> 1");
    }

    #[test]
    fn test_invalid_token_sequences_error() {
        fn test_with_and_without_spaces(expression: &str) {
            assert!(infix_to_postfix(expression).is_err());
            assert!(infix_to_postfix(expression.replace(' ', "").as_str()).is_err());
        }

        // These tests might look a bit silly, but I have had a lot of fighting with
        // which tokens are allowed after which.. Most of these have actually passed
        // without error at some point
        test_with_and_without_spaces("-");
        test_with_and_without_spaces("xor");
        test_with_and_without_spaces("( 2 ) ( 3 )");
        test_with_and_without_spaces("- - 1"); // two unary operators
        test_with_and_without_spaces("- - x");
        test_with_and_without_spaces("( 1 + )");
        test_with_and_without_spaces("( + 1 )");
        test_with_and_without_spaces("( 1 ) 1");
        test_with_and_without_spaces("1 ( 1 )");
        test_with_and_without_spaces("f( x + )");
        test_with_and_without_spaces("f( + x )");
        test_with_and_without_spaces("f( 2 + , 3 )");
        test_with_and_without_spaces("f( + 1 , 3 )");
        test_with_and_without_spaces("f( 1 , + 2 )");
        assert!(infix_to_postfix("2 3").is_err()); // spaces are meaningful here
    }

    #[test]
    fn test_booleans_are_parsed_correctly() {
        assert_eq!(vec![tokens![true]], unwrap_tokens(infix_to_postfix("true").unwrap()));
        assert_eq!(vec![tokens![false]], unwrap_tokens(infix_to_postfix("false").unwrap()));
        assert_eq!(vec![tokens![truefalse]], unwrap_tokens(infix_to_postfix("truefalse").unwrap())); // identifier, so single token
        assert_eq!(vec![tokens![falsetrue]], unwrap_tokens(infix_to_postfix("falsetrue").unwrap()));
    }

    #[test]
    fn test_multiple_nots_works() {
        assert!(infix_to_postfix("!true").is_ok());
        assert!(infix_to_postfix("!!true").is_ok());
        assert!(infix_to_postfix("!!!true").is_ok());
    }

    #[test]
    fn test_empty_function_parameters_error() {
        assert!(infix_to_postfix("f(1,2,)").is_err());
        assert!(infix_to_postfix("f(,2,3)").is_err());
        assert!(infix_to_postfix("f(,2,)").is_err());
        assert!(infix_to_postfix("f(,)").is_err());
        assert!(infix_to_postfix("f(,,)").is_err());
    }
}
