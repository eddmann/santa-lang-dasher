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

        // Handle postfix operators (call, index) and infix operators
        while !self.is_at_end() {
            let token = self.current_token()?;

            // Check for postfix operators first (highest precedence)
            match &token.kind {
                TokenKind::LeftParen => {
                    // Function call - highest precedence (8)
                    if 8 < min_precedence {
                        break;
                    }
                    left = self.parse_call(left)?;
                    continue;
                }
                TokenKind::LeftBracket => {
                    // Index - highest precedence (8)
                    if 8 < min_precedence {
                        break;
                    }
                    left = self.parse_index(left)?;
                    continue;
                }
                _ => {}
            }

            // Check for infix operators
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
            TokenKind::Underscore => {
                self.advance();
                Ok(Expr::Placeholder)
            }
            TokenKind::LeftBracket => {
                self.parse_list()
            }
            TokenKind::HashBrace => {
                self.parse_set_or_dict()
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
            TokenKind::VerticalBar => {
                self.parse_function()
            }
            TokenKind::OrOr => {
                // || is lexed as a single token, but it could be an empty function parameter list
                // We need to check if this is a function (|| ...) or a logical OR
                // For now, treat it as a function with empty params
                self.parse_function_empty_params()
            }
            _ => Err(ParseError {
                message: format!("Unexpected token: {:?}", token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            }),
        }
    }

    fn parse_function(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume first '|'

        let mut params = Vec::new();

        // Parse parameters
        loop {
            let token = self.current_token()?;
            match &token.kind {
                TokenKind::Identifier(name) => {
                    params.push(Param { name: name.clone() });
                    self.advance();

                    // Check for comma (more params) or closing |
                    let next = self.current_token()?;
                    match &next.kind {
                        TokenKind::Comma => {
                            self.advance();
                            continue;
                        }
                        TokenKind::VerticalBar => {
                            self.advance(); // consume closing '|'
                            break;
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!("Expected ',' or '|' in function parameters, got {:?}", next.kind),
                                line: next.span.start.line as usize,
                                column: next.span.start.column as usize,
                            });
                        }
                    }
                }
                TokenKind::VerticalBar => {
                    // Empty parameter list: ||
                    self.advance();
                    break;
                }
                _ => {
                    return Err(ParseError {
                        message: format!("Expected identifier or '|' in function parameters, got {:?}", token.kind),
                        line: token.span.start.line as usize,
                        column: token.span.start.column as usize,
                    });
                }
            }
        }

        // Parse function body
        let body = self.parse_pratt_expr(0)?;

        Ok(Expr::Function {
            params,
            body: Box::new(body),
        })
    }

    fn parse_function_empty_params(&mut self) -> Result<Expr, ParseError> {
        // Handle || as an empty parameter list for a function
        self.advance(); // consume '||'

        // Parse function body
        let body = self.parse_pratt_expr(0)?;

        Ok(Expr::Function {
            params: Vec::new(),
            body: Box::new(body),
        })
    }

    fn parse_call(&mut self, function: Expr) -> Result<Expr, ParseError> {
        self.advance(); // consume '('

        let mut args = Vec::new();

        // Check for empty argument list
        if let Ok(token) = self.current_token() {
            if matches!(token.kind, TokenKind::RightParen) {
                self.advance();
                return Ok(Expr::Call {
                    function: Box::new(function),
                    args,
                });
            }
        }

        // Parse arguments
        loop {
            let arg = self.parse_pratt_expr(0)?;
            args.push(arg);

            let token = self.current_token()?;
            match &token.kind {
                TokenKind::Comma => {
                    self.advance();
                    // Check for trailing comma
                    if let Ok(next) = self.current_token() {
                        if matches!(next.kind, TokenKind::RightParen) {
                            self.advance();
                            break;
                        }
                    }
                }
                TokenKind::RightParen => {
                    self.advance();
                    break;
                }
                _ => {
                    return Err(ParseError {
                        message: format!("Expected ',' or ')' in call arguments, got {:?}", token.kind),
                        line: token.span.start.line as usize,
                        column: token.span.start.column as usize,
                    })
                }
            }
        }

        Ok(Expr::Call {
            function: Box::new(function),
            args,
        })
    }

    fn parse_index(&mut self, collection: Expr) -> Result<Expr, ParseError> {
        self.advance(); // consume '['

        let index = self.parse_pratt_expr(0)?;

        let token = self.current_token()?;
        if !matches!(token.kind, TokenKind::RightBracket) {
            return Err(ParseError {
                message: format!("Expected ']' after index, got {:?}", token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            });
        }
        self.advance(); // consume ']'

        Ok(Expr::Index {
            collection: Box::new(collection),
            index: Box::new(index),
        })
    }

    fn parse_set_or_dict(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume '#{'

        // Check for empty set/dict
        if let Ok(token) = self.current_token() {
            if matches!(token.kind, TokenKind::RightBrace) {
                self.advance();
                // Empty #{} is a set per LANG.txt
                return Ok(Expr::Set(Vec::new()));
            }
        }

        // Parse first element to determine if it's a set or dict
        let first_elem = self.parse_pratt_expr(0)?;

        // Check if this is a dict entry (has a colon)
        if let Ok(token) = self.current_token() {
            if matches!(token.kind, TokenKind::Colon) {
                // It's a dict
                self.advance(); // consume ':'
                let first_value = self.parse_pratt_expr(0)?;
                let mut entries = vec![(first_elem, first_value)];

                // Parse remaining entries
                loop {
                    let token = self.current_token()?;
                    match &token.kind {
                        TokenKind::Comma => {
                            self.advance();
                            // Check for trailing comma
                            if let Ok(next) = self.current_token() {
                                if matches!(next.kind, TokenKind::RightBrace) {
                                    self.advance();
                                    break;
                                }
                            }
                            // Parse next key:value pair
                            let key = self.parse_pratt_expr(0)?;
                            let colon = self.current_token()?;
                            if !matches!(colon.kind, TokenKind::Colon) {
                                return Err(ParseError {
                                    message: format!("Expected ':' in dict literal, got {:?}", colon.kind),
                                    line: colon.span.start.line as usize,
                                    column: colon.span.start.column as usize,
                                });
                            }
                            self.advance(); // consume ':'
                            let value = self.parse_pratt_expr(0)?;
                            entries.push((key, value));
                        }
                        TokenKind::RightBrace => {
                            self.advance();
                            break;
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!("Expected ',' or '}}' in dict literal, got {:?}", token.kind),
                                line: token.span.start.line as usize,
                                column: token.span.start.column as usize,
                            })
                        }
                    }
                }

                return Ok(Expr::Dict(entries));
            }
        }

        // It's a set
        let mut elements = vec![first_elem];

        loop {
            let token = self.current_token()?;
            match &token.kind {
                TokenKind::Comma => {
                    self.advance();
                    // Check for trailing comma
                    if let Ok(next) = self.current_token() {
                        if matches!(next.kind, TokenKind::RightBrace) {
                            self.advance();
                            break;
                        }
                    }
                    let elem = self.parse_pratt_expr(0)?;
                    elements.push(elem);
                }
                TokenKind::RightBrace => {
                    self.advance();
                    break;
                }
                _ => {
                    return Err(ParseError {
                        message: format!("Expected ',' or '}}' in set literal, got {:?}", token.kind),
                        line: token.span.start.line as usize,
                        column: token.span.start.column as usize,
                    })
                }
            }
        }

        Ok(Expr::Set(elements))
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
