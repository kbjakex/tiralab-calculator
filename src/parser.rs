
use anyhow::{Result, bail};
use bstr::BStr;
use thiserror::Error;

use crate::ast::AstNode;

/// Converts an expression from infix form (`1 + 2`) to postfix form (`1 2 +`) using the
/// Shunting-Yard algorithm. The postfix result is represented as an array of `AstNode`s.
/// 
/// Does not allocate memory unless an error (invalid input) occurs, in which case formatting
/// the error message requires an allocation.
pub fn infix_to_postfix_shunting_yard<'a>(infix_str: &'a str) -> Result<Vec<AstNode>> {
    // Runtime invariant: `operators` does not contain Token::Number entries.
    let mut output : Vec<Token<'a>> = Vec::new();
    let mut operators: Vec<Token<'a>> = Vec::new();

    for token in TokenIterator::of(infix_str) {
        match token? {
            Token::Number { value } => output.push(Token::Number { value }),
            Token::FunctionCall { name } => operators.push(Token::FunctionCall { name }),
            Token::BinaryOperator { kind } => {
                let precedence = kind.precedence();
                while let Some(top_operator) = operators.last() {
                    if matches!(top_operator, Token::LeftParen) {
                        break;
                    }

                    todo!()
                }
            },
            Token::LeftParen => operators.push(Token::LeftParen),
            Token::RightParen => {
                while let Some(top_operator) = operators.pop() {
                    if matches!(top_operator, Token::LeftParen) {
                        bail!("Mismatched parentheses");
                    }
                    output.push(top_operator);
                }

                todo!()
            },
        }
    }

    while let Some(top_operator) = operators.pop() {
        if matches!(top_operator, Token::LeftParen) {
            bail!("Mismatched parentheses");
        }

        output.push(top_operator);
    }

    todo!()
}

enum Token<'a> {
    Number {
        value: f64
    },
    FunctionCall {
        name: &'a str,
    },
    BinaryOperator {
        kind: crate::ast::BinaryOperator,
    },
    LeftParen,
    RightParen,
}

#[derive(Error, Debug)]
pub enum TokenError {
    #[error("Unexpected symbol '{0}' at position '{1}'")]
    UnexpectedToken(String, usize)
}

struct TokenIterator<'a> {
    source: &'a BStr,
    index: usize, // Current position in `source`
}

impl<'a> TokenIterator<'a> {
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
}

impl<'a> Iterator for TokenIterator<'a> {
    type Item = Result<Token<'a>, TokenError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_spaces();
        if self.index == self.source.len() {
            return None;
        }

        None
    }
}
