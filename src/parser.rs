use anyhow::{Result, bail};
use bstr::BStr;

use crate::ast::{Ast, BinaryOperator, AstNode};

#[derive(Debug, PartialEq)]
pub enum Value<'a> {
    Constant { value: f64 },
    Variable { name: &'a str },
}

#[derive(Debug, PartialEq)]
pub enum Token<'a> {
    Value { value: Value<'a> },
    BinaryOperator { operator: BinaryOperator },
}

/// Takes a sequence of nodes in postfix order (produced by `infix_to_postfix_shunting_yard`)
/// and builds an abstract syntax tree in. This runs in O(n) time and space.
pub fn postfix_to_ast<'a>(tokens: Vec<Token<'a>>) -> Ast {
    let mut ast = Ast::new();
    for token in tokens.iter() {
        match token {
            &Token::Value { value: Value::Constant { value } } => ast.nodes.push(AstNode::Constant { value }),
            &Token::Value { value: Value::Variable { name }} => ast.nodes.push(AstNode::VariableReference { name: name.into() }),
            &Token::BinaryOperator { operator } => ast.nodes.push(AstNode::BinaryOperation {
                lhs_node_index: ast.nodes.len() as u32 - 2,
                rhs_node_index: ast.nodes.len() as u32 - 1,
                operation: operator,
            }),
        }
    }
    
    ast
}

/// Converts an expression from infix form (`1 + 2`) to postfix form (`1 2 +`) using the
/// shunting yard algorithm. The postfix result is represented as an array of `AstNode`s.
/// References: 
/// http://mathcenter.oxford.emory.edu/site/cs171/shuntingYardAlgorithm/
/// https://aquarchitect.github.io/swift-algorithm-club/Shunting%20Yard/
pub fn infix_to_postfix_shunting_yard<'a>(infix_str: &'a str) -> Result<Vec<Token>> {
    // Runtime invariant: `operators` does not contain Token::Number entries.
    let mut output: Vec<Token<'a>> = Vec::new();
    let mut operators: Vec<ParserToken<'a>> = Vec::new();

    for token in TokenIterator::of(infix_str) {
        match token? {
            ParserToken::Number { value } => output.push(Token::Value { value: Value::Constant { value }}),
            ParserToken::Variable { name } => output.push(Token::Value { value: Value::Variable { name }}),
            ParserToken::LeftParen => operators.push(ParserToken::LeftParen),
            ParserToken::RightParen => {
                pop_until_lparen(&mut operators, &mut output);
                // If there are tokens left, it is an openin paren, so pop that. Otherwise,
                // there were more closing parens than opening parens, so report that.
                if operators.pop().is_none() {
                    bail!("Too many closing parentheses!");
                }
            },
            ParserToken::BinaryOperator { operator } => {
                let precedence = operator.precedence();
                
                while let Some(ParserToken::BinaryOperator{ operator: top_of_stack}) = operators.last() {
                    let top_precedence = top_of_stack.precedence();
                
                    if (operator.left_associative() && precedence <= top_precedence)
                        || (!operator.left_associative() && precedence < top_precedence) {
                        output.push(Token::BinaryOperator{ operator: *top_of_stack });
                        operators.pop();
                    } else {
                        break;
                    }
                }

                operators.push(ParserToken::BinaryOperator { operator });
            },
        }
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
        match top {
            &ParserToken::Number { value } => output.push(Token::Value { value: Value::Constant { value } }),
            &ParserToken::Variable { name } => output.push(Token::Value{ value: Value::Variable { name }}),
            &ParserToken::BinaryOperator { operator } => output.push(Token::BinaryOperator { operator }),
            ParserToken::RightParen => unreachable!("operators never contains right parens"),
            ParserToken::LeftParen => return,
        }
        operators.pop();
    }
}

/// Represents a token internal to the parser.
#[derive(Debug)]
enum ParserToken<'a> {
    Number { value: f64 },
    Variable { name: &'a str },
    BinaryOperator { operator: BinaryOperator },
    LeftParen,
    RightParen,
}

struct TokenIterator<'a> {
    source: &'a BStr,
    index: usize, // Current position in `source`
}

impl<'a> TokenIterator<'a> {
    /// Creates a new iterator over the tokens in the source string.
    pub fn of(source: &'a str) -> Self {
        Self {
            source: source.into(), // Guaranteed to be free and infallible
            index: 0,
        }
    }

    fn skip_spaces(&mut self) {
        while self.index < self.source.len() && self.source[self.index].is_ascii_whitespace() {
            self.index += 1;
        }
    }

    fn read_number(&mut self) -> Result<f64> {
        let end_index = self.source
            .iter()
            .skip(self.index)
            .position(|&c| !c.is_ascii_digit() && c != b'.')
            .map_or(self.source.len(), |i| i + self.index);
    
        let byte_str = &self.source[self.index..end_index];
        // SAFETY: this is safe, because byte_str can necessarily only contain ascii digits or an ascii dot,
        // and ascii is valid UTF-8. Both types have the same representation. Empty source is also fine.
        let str_slice : &str = unsafe { std::mem::transmute(byte_str) };

        self.index = end_index-1;

        str_slice
            .parse()
            .map_err(|_| anyhow::anyhow!("Invalid number: '{str_slice}'"))
    }

    fn read_identifier(&mut self) -> &'a str {
        let end_index = self.source
            .iter()
            .skip(self.index)
            .position(|&c| !c.is_ascii_alphabetic())
            .unwrap_or(self.source.len());

        let byte_str = &self.source[self.index..end_index];
        // SAFETY: this is safe, because byte_str can necessarily only contain ascii codepoints,
        // and this is therefore valid UTF-8. Both types have the same representation. Empty source is also fine.
        let str_slice : &str = unsafe { std::mem::transmute(byte_str) };

        self.index = end_index;

        str_slice
    }

    fn read_token(&mut self) -> Result<ParserToken<'a>> {
        let result = match self.source[self.index] {
            b'(' => ParserToken::LeftParen,
            b')' => ParserToken::RightParen,
            b'+' => ParserToken::BinaryOperator { operator: BinaryOperator::Add },
            b'-' => ParserToken::BinaryOperator { operator: BinaryOperator::Subtract },
            b'*' => ParserToken::BinaryOperator { operator: BinaryOperator::Multiply },
            b'/' => ParserToken::BinaryOperator { operator: BinaryOperator::Divide },

            c if c.is_ascii_digit() => ParserToken::Number { value: self.read_number()? },
            c if c.is_ascii_alphabetic() => ParserToken::Variable { name: self.read_identifier() },

            // Looks a bit ugly, because the Result is wrapped in an Option (necessitated by Iterator)
            // and the usual error reporting facilities ('?' operator) don't work with that.
            other => bail!("Invalid symbol (starts with '{}')", other as char)
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
    use crate::{parser::{Token, Value}, ast::BinaryOperator};

    use super::infix_to_postfix_shunting_yard;
    
    // A macro to make building expected solutions not enormously verbose. Macros are unfortunately
    // fairly unreadable, but you can probably mostly infer what it does from the usage in below tests.
    macro_rules! tokens {
        (+) => {Token::BinaryOperator { operator: BinaryOperator::Add }};
        (-) => {Token::BinaryOperator { operator: BinaryOperator::Subtract }};
        (*) => {Token::BinaryOperator { operator: BinaryOperator::Multiply }};
        (/) => {Token::BinaryOperator { operator: BinaryOperator::Divide }};
        ($lit:literal) => {Token::Value { value: Value::Constant{ value: $lit as f64 } }};
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
        assert_eq!(tokens![5 5 +], infix_to_postfix_shunting_yard("5. + 5.").unwrap());
        assert_eq!(tokens![5 5 + 3 3 + *], infix_to_postfix_shunting_yard("(5 + 5) * (3 + 3)").unwrap());
        assert_eq!(tokens![5 5 + 3 * 3 +], infix_to_postfix_shunting_yard("(5 + 5) * 3 + 3").unwrap());
        assert_eq!(tokens![5 5 3 * + 3 +], infix_to_postfix_shunting_yard("5 + 5 * 3 + 3").unwrap());
        assert_eq!(tokens![5 5 3 3 + * +], infix_to_postfix_shunting_yard("5 + 5 * (3 + 3)").unwrap());
    }
}
