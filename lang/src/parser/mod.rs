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

            // Check for trailing lambda syntax: expr identifier lambda
            // e.g., [1, 2, 3] map |x| x * 2
            if let TokenKind::Identifier(func_name) = &token.kind {
                // Look ahead to see if there's a lambda following
                if let Some(next) = self.tokens.get(self.current + 1) {
                    if matches!(next.kind, TokenKind::VerticalBar | TokenKind::OrOr) {
                        // This is a trailing lambda
                        let func_name = func_name.clone();
                        self.advance(); // consume identifier

                        // Parse the lambda
                        let lambda = self.parse_expression()?;

                        // Transform to: func_name(left, lambda)
                        left = Expr::Call {
                            function: Box::new(Expr::Identifier(func_name)),
                            args: vec![left, lambda],
                        };
                        continue;
                    }
                }
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
            TokenKind::Match => {
                self.parse_match()
            }
            TokenKind::LeftBrace => {
                // Disambiguate {} based on whether it's empty
                // Empty {} → Set (in expression context)
                // Non-empty { ... } → Block
                if let Some(next) = self.tokens.get(self.current + 1) {
                    if matches!(next.kind, TokenKind::RightBrace) {
                        // Empty braces: {} → Set
                        self.advance(); // consume '{'
                        self.advance(); // consume '}'
                        return Ok(Expr::Set(Vec::new()));
                    }
                }
                // Non-empty or function body → Block
                self.parse_block()
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

        // Parse function body (use parse_body_expr for correct {} handling)
        let body = self.parse_body_expr()?;

        Ok(Expr::Function {
            params,
            body: Box::new(body),
        })
    }

    fn parse_function_empty_params(&mut self) -> Result<Expr, ParseError> {
        // Handle || as an empty parameter list for a function
        self.advance(); // consume '||'

        // Parse function body (use parse_body_expr for correct {} handling)
        let body = self.parse_body_expr()?;

        Ok(Expr::Function {
            params: Vec::new(),
            body: Box::new(body),
        })
    }

    /// Parse an expression in "body" context where {} is always a Block
    fn parse_body_expr(&mut self) -> Result<Expr, ParseError> {
        let token = self.current_token()?;

        // Special handling for empty braces in body context
        if matches!(token.kind, TokenKind::LeftBrace) {
            if let Some(next) = self.tokens.get(self.current + 1) {
                if matches!(next.kind, TokenKind::RightBrace) {
                    // Empty braces in body context → Block
                    self.advance(); // consume '{'
                    self.advance(); // consume '}'
                    return Ok(Expr::Block(Vec::new()));
                }
            }
        }

        // Otherwise parse normally
        self.parse_pratt_expr(0)
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

        // Check if this is a dict entry (has a colon) or dict shorthand
        if let Ok(token) = self.current_token() {
            if matches!(token.kind, TokenKind::Colon) {
                // It's a dict with explicit key:value syntax
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
                            // Parse next entry (could be key:value or shorthand)
                            let next_entry = self.parse_dict_entry()?;
                            entries.push(next_entry);
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
            } else if matches!(token.kind, TokenKind::Comma | TokenKind::RightBrace) {
                // Check if first_elem is an identifier - if so, this is dict shorthand
                if let Expr::Identifier(name) = first_elem {
                    // Dict shorthand: #{name} → #{"name": name}
                    let key = Expr::String(name.clone());
                    let value = Expr::Identifier(name);
                    let mut entries = vec![(key, value)];

                    // Parse remaining shorthand entries if comma
                    if matches!(token.kind, TokenKind::Comma) {
                        loop {
                            self.advance(); // consume ','

                            // Check for trailing comma
                            if let Ok(next) = self.current_token() {
                                if matches!(next.kind, TokenKind::RightBrace) {
                                    self.advance();
                                    break;
                                }
                            }

                            // Parse next entry (could be key:value or shorthand)
                            let next_entry = self.parse_dict_entry()?;
                            entries.push(next_entry);

                            // Check what comes next
                            let token = self.current_token()?;
                            if matches!(token.kind, TokenKind::RightBrace) {
                                self.advance();
                                break;
                            } else if !matches!(token.kind, TokenKind::Comma) {
                                return Err(ParseError {
                                    message: format!("Expected ',' or '}}' in dict literal, got {:?}", token.kind),
                                    line: token.span.start.line as usize,
                                    column: token.span.start.column as usize,
                                });
                            }
                        }
                    } else {
                        // Just closing brace
                        self.advance();
                    }

                    return Ok(Expr::Dict(entries));
                }
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

    /// Parse a dict entry - either key:value or shorthand identifier
    fn parse_dict_entry(&mut self) -> Result<(Expr, Expr), ParseError> {
        // Check if this is a shorthand identifier
        let token = self.current_token()?;

        if let TokenKind::Identifier(name) = &token.kind {
            // Look ahead to see if there's a colon or comma/brace
            if let Some(next) = self.tokens.get(self.current + 1) {
                if matches!(next.kind, TokenKind::Comma | TokenKind::RightBrace) {
                    // Shorthand: name → "name": name
                    let name = name.clone();
                    self.advance(); // consume identifier
                    let key = Expr::String(name.clone());
                    let value = Expr::Identifier(name);
                    return Ok((key, value));
                }
            }
        }

        // Otherwise, parse as key:value
        let key = self.parse_pratt_expr(0)?;
        let colon = self.current_token()?;
        if !matches!(colon.kind, TokenKind::Colon) {
            return Err(ParseError {
                message: format!("Expected ':' in dict entry, got {:?}", colon.kind),
                line: colon.span.start.line as usize,
                column: colon.span.start.column as usize,
            });
        }
        self.advance(); // consume ':'
        let value = self.parse_pratt_expr(0)?;
        Ok((key, value))
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

    /// Expect a specific token kind and consume it
    fn expect(&mut self, expected: TokenKind) -> Result<(), ParseError> {
        let token = self.current_token()?;
        if std::mem::discriminant(&token.kind) == std::mem::discriminant(&expected) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError {
                message: format!("Expected {:?}, got {:?}", expected, token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            })
        }
    }

    /// Parse a statement (let, return, break, or expression)
    pub fn parse_statement(&mut self) -> Result<Stmt, ParseError> {
        let token = self.current_token()?;

        match &token.kind {
            TokenKind::Let => self.parse_let_statement(),
            TokenKind::Return => self.parse_return_statement(),
            TokenKind::Break => self.parse_break_statement(),
            _ => {
                // Expression statement
                let expr = self.parse_expression()?;
                Ok(Stmt::Expr(expr))
            }
        }
    }

    fn parse_let_statement(&mut self) -> Result<Stmt, ParseError> {
        self.advance(); // consume 'let'

        // Check for 'mut' keyword
        let mutable = if matches!(self.current_token()?.kind, TokenKind::Mut) {
            self.advance();
            true
        } else {
            false
        };

        // Parse pattern (for now, just identifier)
        let pattern = self.parse_pattern()?;

        // Expect '=' token
        let token = self.current_token()?;
        if !matches!(token.kind, TokenKind::Equal) {
            return Err(ParseError {
                message: format!("Expected '=' after pattern, got {:?}", token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            });
        }
        self.advance(); // consume '='

        // Parse value expression
        let value = self.parse_expression()?;

        Ok(Stmt::Let {
            mutable,
            pattern,
            value,
        })
    }

    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        let token = self.current_token()?;

        match &token.kind {
            TokenKind::Identifier(name) => {
                let pattern = Pattern::Identifier(name.clone());
                self.advance();
                Ok(pattern)
            }
            TokenKind::Underscore => {
                self.advance();
                Ok(Pattern::Wildcard)
            }
            TokenKind::LeftBracket => {
                self.parse_list_pattern()
            }
            // Literal patterns
            TokenKind::Integer(n) => {
                let pattern = Pattern::Literal(Literal::Integer(*n));
                self.advance();
                Ok(pattern)
            }
            TokenKind::Decimal(f) => {
                let pattern = Pattern::Literal(Literal::Decimal(*f));
                self.advance();
                Ok(pattern)
            }
            TokenKind::String(s) => {
                let pattern = Pattern::Literal(Literal::String(s.clone()));
                self.advance();
                Ok(pattern)
            }
            TokenKind::True => {
                self.advance();
                Ok(Pattern::Literal(Literal::Boolean(true)))
            }
            TokenKind::False => {
                self.advance();
                Ok(Pattern::Literal(Literal::Boolean(false)))
            }
            TokenKind::Nil => {
                self.advance();
                Ok(Pattern::Literal(Literal::Nil))
            }
            _ => Err(ParseError {
                message: format!("Expected pattern, got {:?}", token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            }),
        }
    }

    fn parse_list_pattern(&mut self) -> Result<Pattern, ParseError> {
        self.advance(); // consume '['

        let mut patterns = Vec::new();

        loop {
            let token = self.current_token()?;

            match &token.kind {
                TokenKind::RightBracket => {
                    self.advance(); // consume ']'
                    break;
                }
                TokenKind::DotDotIdent(name) => {
                    // Rest pattern: ..rest (lexed as a single token)
                    let rest_pattern = Pattern::RestIdentifier(name.clone());
                    self.advance();
                    patterns.push(rest_pattern);

                    // After rest pattern, expect ] or ,
                    let next = self.current_token()?;
                    match &next.kind {
                        TokenKind::RightBracket => {
                            self.advance();
                            break;
                        }
                        TokenKind::Comma => {
                            self.advance();
                            // Continue to next pattern
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!("Expected ',' or ']' after rest pattern, got {:?}", next.kind),
                                line: next.span.start.line as usize,
                                column: next.span.start.column as usize,
                            });
                        }
                    }
                }
                _ => {
                    // Regular pattern
                    let pattern = self.parse_pattern()?;
                    patterns.push(pattern);

                    // Check for comma or closing bracket
                    let next = self.current_token()?;
                    match &next.kind {
                        TokenKind::Comma => {
                            self.advance();
                            // Continue to next pattern
                        }
                        TokenKind::RightBracket => {
                            self.advance();
                            break;
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!("Expected ',' or ']' in list pattern, got {:?}", next.kind),
                                line: next.span.start.line as usize,
                                column: next.span.start.column as usize,
                            });
                        }
                    }
                }
            }
        }

        Ok(Pattern::List(patterns))
    }

    fn parse_return_statement(&mut self) -> Result<Stmt, ParseError> {
        self.advance(); // consume 'return'
        let expr = self.parse_expression()?;
        Ok(Stmt::Return(expr))
    }

    fn parse_break_statement(&mut self) -> Result<Stmt, ParseError> {
        self.advance(); // consume 'break'
        let expr = self.parse_expression()?;
        Ok(Stmt::Break(expr))
    }

    fn parse_match(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'match'

        // Parse subject expression
        let subject = self.parse_expression()?;

        // Expect '{'
        let token = self.current_token()?;
        if !matches!(token.kind, TokenKind::LeftBrace) {
            return Err(ParseError {
                message: format!("Expected '{{' after match subject, got {:?}", token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            });
        }
        self.advance(); // consume '{'

        // Parse match arms
        let mut arms = Vec::new();

        loop {
            let token = self.current_token()?;

            // Check for closing brace
            if matches!(token.kind, TokenKind::RightBrace) {
                self.advance();
                break;
            }

            // Parse pattern
            let pattern = self.parse_pattern()?;

            // Check for guard (if keyword)
            let guard = if matches!(self.current_token()?.kind, TokenKind::If) {
                self.advance(); // consume 'if'
                Some(self.parse_expression()?)
            } else {
                None
            };

            // Parse body (expect '{')
            let token = self.current_token()?;
            if !matches!(token.kind, TokenKind::LeftBrace) {
                return Err(ParseError {
                    message: format!("Expected '{{' after match pattern, got {:?}", token.kind),
                    line: token.span.start.line as usize,
                    column: token.span.start.column as usize,
                });
            }

            let body = self.parse_block()?;

            arms.push(MatchArm {
                pattern,
                guard,
                body,
            });
        }

        Ok(Expr::Match {
            subject: Box::new(subject),
            arms,
        })
    }

    fn parse_block(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume '{'

        let mut statements = Vec::new();

        loop {
            let token = self.current_token()?;

            // Check for closing brace
            if matches!(token.kind, TokenKind::RightBrace) {
                self.advance();
                break;
            }

            // Parse statement
            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }

        Ok(Expr::Block(statements))
    }

    /// Parse a complete program with statements and AOC sections
    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut statements = Vec::new();
        let mut sections = Vec::new();

        while !self.is_at_end() {
            // Skip any leading semicolons/newlines
            self.skip_statement_terminators();

            if self.is_at_end() {
                break;
            }

            // Check if this is a section (identifier followed by colon)
            if self.is_section_start() {
                let section = self.parse_section()?;
                sections.push(section);
                self.skip_statement_terminators();
            } else {
                // Parse as a regular statement
                let stmt = self.parse_statement()?;
                statements.push(stmt);
                self.skip_statement_terminators();
            }
        }

        Ok(Program {
            statements,
            sections,
        })
    }

    /// Skip semicolons and newlines (statement terminators)
    fn skip_statement_terminators(&mut self) {
        while !self.is_at_end() {
            if let Ok(token) = self.current_token() {
                if matches!(token.kind, TokenKind::Semicolon) {
                    self.advance();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }

    /// Check if current position is the start of a section
    fn is_section_start(&self) -> bool {
        if let Ok(token) = self.current_token() {
            if let TokenKind::Identifier(name) = &token.kind {
                // Check if it's a section keyword and followed by colon
                if matches!(name.as_str(), "input" | "part_one" | "part_two" | "test") {
                    // Look ahead to see if there's a colon
                    if let Some(next) = self.tokens.get(self.current + 1) {
                        return matches!(next.kind, TokenKind::Colon);
                    }
                }
            }
        }
        false
    }

    /// Parse a section (input, part_one, part_two, or test)
    fn parse_section(&mut self) -> Result<Section, ParseError> {
        let token = self.current_token()?.clone();

        if let TokenKind::Identifier(name) = &token.kind {
            match name.as_str() {
                "input" => {
                    self.advance(); // consume 'input'
                    self.expect(TokenKind::Colon)?;
                    let expr = self.parse_expression()?;
                    Ok(Section::Input(expr))
                }
                "part_one" => {
                    self.advance(); // consume 'part_one'
                    self.expect(TokenKind::Colon)?;
                    let expr = self.parse_expression()?;
                    Ok(Section::PartOne(expr))
                }
                "part_two" => {
                    self.advance(); // consume 'part_two'
                    self.expect(TokenKind::Colon)?;
                    let expr = self.parse_expression()?;
                    Ok(Section::PartTwo(expr))
                }
                "test" => {
                    self.advance(); // consume 'test'
                    self.expect(TokenKind::Colon)?;
                    self.expect(TokenKind::LeftBrace)?;

                    // Parse test section fields
                    let mut input_expr = None;
                    let mut part_one_expr = None;
                    let mut part_two_expr = None;

                    while !self.is_at_end() {
                        let token = self.current_token()?;

                        // Check for closing brace
                        if matches!(token.kind, TokenKind::RightBrace) {
                            self.advance();
                            break;
                        }

                        // Parse field
                        if let TokenKind::Identifier(field_name) = &token.kind {
                            match field_name.as_str() {
                                "input" => {
                                    self.advance();
                                    self.expect(TokenKind::Colon)?;
                                    input_expr = Some(self.parse_expression()?);
                                }
                                "part_one" => {
                                    self.advance();
                                    self.expect(TokenKind::Colon)?;
                                    part_one_expr = Some(self.parse_expression()?);
                                }
                                "part_two" => {
                                    self.advance();
                                    self.expect(TokenKind::Colon)?;
                                    part_two_expr = Some(self.parse_expression()?);
                                }
                                _ => {
                                    return Err(ParseError {
                                        message: format!("Unexpected field in test section: {}", field_name),
                                        line: token.span.start.line as usize,
                                        column: token.span.start.column as usize,
                                    });
                                }
                            }
                        } else {
                            return Err(ParseError {
                                message: format!("Expected field name in test section, got {:?}", token.kind),
                                line: token.span.start.line as usize,
                                column: token.span.start.column as usize,
                            });
                        }
                    }

                    let input = input_expr.ok_or_else(|| ParseError {
                        message: "test section requires 'input' field".to_string(),
                        line: token.span.start.line as usize,
                        column: token.span.start.column as usize,
                    })?;

                    Ok(Section::Test {
                        input,
                        part_one: part_one_expr,
                        part_two: part_two_expr,
                    })
                }
                _ => Err(ParseError {
                    message: format!("Unexpected section name: {}", name),
                    line: token.span.start.line as usize,
                    column: token.span.start.column as usize,
                }),
            }
        } else {
            Err(ParseError {
                message: format!("Expected section identifier, got {:?}", token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            })
        }
    }
}

pub fn parse(tokens: Vec<Token>) -> Result<Expr, ParseError> {
    let mut parser = Parser::new(tokens);
    parser.parse_expression()
}
