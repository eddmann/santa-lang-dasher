pub mod ast;
#[cfg(test)]
mod tests;

use crate::lexer::{Token, TokenKind};
use ast::*;

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub line: usize,
    pub column: usize,
}

pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, current: 0 }
    }

    pub fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.parse_pratt_expr(0)
    }

    fn parse_pratt_expr(&mut self, min_precedence: u8) -> Result<Expr, ParseError> {
        let mut left = self.parse_primary()?;

        while !self.is_at_end() {
            let precedence = self.get_infix_precedence();
            // Stop if precedence is 0 (not an infix op) or less than minimum
            if precedence == 0 || precedence < min_precedence {
                break;
            }

            left = self.parse_infix(left, precedence)?;
        }

        Ok(left)
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        let token = self.current_token()?.clone();

        match &token.kind {
            TokenKind::Integer(n) => {
                let value = *n;
                self.advance();
                Ok(Expr::Integer(value))
            }
            TokenKind::Decimal(f) => {
                let value = *f;
                self.advance();
                Ok(Expr::Decimal(value))
            }
            TokenKind::String(s) => {
                let value = s.clone();
                self.advance();
                Ok(Expr::String(value))
            }
            TokenKind::True => {
                self.advance();
                Ok(Expr::Boolean(true))
            }
            TokenKind::False => {
                self.advance();
                Ok(Expr::Boolean(false))
            }
            TokenKind::Nil => {
                self.advance();
                Ok(Expr::Nil)
            }
            TokenKind::Identifier(name) => {
                let value = name.clone();
                self.advance();
                Ok(Expr::Identifier(value))
            }
            TokenKind::LeftBracket => {
                self.parse_list()
            }
            TokenKind::Bang => {
                self.advance();
                let right = self.parse_pratt_expr(7)?; // Prefix has high precedence (7)
                Ok(Expr::Prefix {
                    op: PrefixOp::Not,
                    right: Box::new(right),
                })
            }
            TokenKind::Minus => {
                self.advance();
                let right = self.parse_pratt_expr(7)?; // Prefix has high precedence (7)
                Ok(Expr::Prefix {
                    op: PrefixOp::Negate,
                    right: Box::new(right),
                })
            }
            _ => Err(ParseError {
                message: format!("Unexpected token: {:?}", token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            }),
        }
    }

    fn parse_list(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume '['

        let mut elements = Vec::new();

        // Check for empty list
        if let Ok(token) = self.current_token() {
            if matches!(token.kind, TokenKind::RightBracket) {
                self.advance();
                return Ok(Expr::List(elements));
            }
        }

        // Parse elements - use low precedence to stop at commas
        loop {
            // Parse with precedence > comma (which would have precedence 0)
            let elem = self.parse_pratt_expr(0)?;
            elements.push(elem);

            let token = self.current_token()?;
            match &token.kind {
                TokenKind::Comma => {
                    self.advance();
                    // Check for trailing comma
                    if let Ok(next) = self.current_token() {
                        if matches!(next.kind, TokenKind::RightBracket) {
                            self.advance();
                            break;
                        }
                    }
                }
                TokenKind::RightBracket => {
                    self.advance();
                    break;
                }
                _ => {
                    return Err(ParseError {
                        message: format!("Expected ',' or ']', got {:?}", token.kind),
                        line: token.span.start.line as usize,
                        column: token.span.start.column as usize,
                    })
                }
            }
        }

        Ok(Expr::List(elements))
    }

    fn parse_infix(&mut self, left: Expr, precedence: u8) -> Result<Expr, ParseError> {
        let token = self.current_token()?.clone();
        let op = self.token_to_infix_op(&token.kind)?;

        self.advance();
        let right = self.parse_pratt_expr(precedence + 1)?;

        Ok(Expr::Infix {
            left: Box::new(left),
            op,
            right: Box::new(right),
        })
    }

    fn token_to_infix_op(&self, kind: &TokenKind) -> Result<InfixOp, ParseError> {
        match kind {
            TokenKind::Plus => Ok(InfixOp::Add),
            TokenKind::Minus => Ok(InfixOp::Subtract),
            TokenKind::Star => Ok(InfixOp::Multiply),
            TokenKind::Slash => Ok(InfixOp::Divide),
            TokenKind::Percent => Ok(InfixOp::Modulo),
            TokenKind::EqualEqual => Ok(InfixOp::Equal),
            TokenKind::NotEqual => Ok(InfixOp::NotEqual),
            TokenKind::Less => Ok(InfixOp::LessThan),
            TokenKind::LessEqual => Ok(InfixOp::LessThanOrEqual),
            TokenKind::Greater => Ok(InfixOp::GreaterThan),
            TokenKind::GreaterEqual => Ok(InfixOp::GreaterThanOrEqual),
            TokenKind::AndAnd => Ok(InfixOp::And),
            TokenKind::OrOr => Ok(InfixOp::Or),
            TokenKind::Pipe => Ok(InfixOp::Pipeline),
            TokenKind::RightRight => Ok(InfixOp::Composition),
            TokenKind::DotDot => Ok(InfixOp::Range),
            TokenKind::DotDotEqual => Ok(InfixOp::RangeInclusive),
            TokenKind::Backtick => Ok(InfixOp::InfixCall),
            _ => Err(ParseError {
                message: format!("Expected infix operator, got {:?}", kind),
                line: 0,
                column: 0,
            }),
        }
    }

    fn get_infix_precedence(&self) -> u8 {
        if self.is_at_end() {
            return 0;
        }

        let token = &self.tokens[self.current];

        // Precedence from PLAN.md Phase 2.2
        // Lower number = lower precedence
        match &token.kind {
            // 9. Logical AND/OR (lowest precedence, same level)
            TokenKind::AndAnd | TokenKind::OrOr => 1,

            // 8. Equality/Assignment (same level)
            TokenKind::EqualEqual | TokenKind::NotEqual | TokenKind::Equal => 2,

            // 7. Comparison
            TokenKind::Less | TokenKind::LessEqual | TokenKind::Greater | TokenKind::GreaterEqual => 3,

            // 6. Composition/Pipeline/Range
            TokenKind::RightRight | TokenKind::Pipe | TokenKind::DotDot | TokenKind::DotDotEqual => 4,

            // 5. Additive
            TokenKind::Plus | TokenKind::Minus => 5,

            // 4. Multiplicative/Infix
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent | TokenKind::Backtick => 6,

            // Not an infix operator
            _ => 0,
        }
    }

    fn current_token(&self) -> Result<&Token, ParseError> {
        self.tokens.get(self.current).ok_or_else(|| ParseError {
            message: "Unexpected end of input".to_string(),
            line: 0,
            column: 0,
        })
    }

    fn advance(&mut self) {
        if !self.is_at_end() {
            self.current += 1;
        }
    }

    fn is_at_end(&self) -> bool {
        if self.current >= self.tokens.len() {
            return true;
        }
        matches!(self.tokens[self.current].kind, TokenKind::Eof)
    }
}

pub fn parse(tokens: Vec<Token>) -> Result<Expr, ParseError> {
    let mut parser = Parser::new(tokens);
    parser.parse_expression()
}
