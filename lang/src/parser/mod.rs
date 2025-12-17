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
        // Filter out comment tokens - they're lexed but not needed for parsing
        let filtered_tokens: Vec<Token> = tokens
            .into_iter()
            .filter(|t| !matches!(t.kind, TokenKind::Comment(_)))
            .collect();
        Self { tokens: filtered_tokens, current: 0 }
    }

    /// Create a binary operator lambda: |__op_0, __op_1| __op_0 OP __op_1
    /// Used when operators like + are passed as function references: fold(0, +, list)
    fn make_operator_lambda(op: InfixOp) -> Expr {
        Expr::Function {
            params: vec![
                Param { name: "__op_0".to_string() },
                Param { name: "__op_1".to_string() },
            ],
            body: Box::new(Expr::Infix {
                left: Box::new(Expr::Identifier("__op_0".to_string())),
                op,
                right: Box::new(Expr::Identifier("__op_1".to_string())),
            }),
        }
    }

    /// Check if current token could start an expression (for operator reference detection)
    fn is_expression_start(&self) -> bool {
        if let Some(token) = self.tokens.get(self.current) {
            matches!(
                token.kind,
                TokenKind::Integer(_)
                    | TokenKind::Decimal(_)
                    | TokenKind::String(_)
                    | TokenKind::True
                    | TokenKind::False
                    | TokenKind::Nil
                    | TokenKind::Identifier(_)
                    | TokenKind::Underscore
                    | TokenKind::LeftParen
                    | TokenKind::LeftBracket
                    | TokenKind::LeftBrace
                    | TokenKind::HashBrace
                    | TokenKind::VerticalBar
                    | TokenKind::OrOr
                    | TokenKind::If
                    | TokenKind::Match
                    | TokenKind::Bang
            )
        } else {
            false
        }
    }

    pub fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        let expr = self.parse_pratt_expr(0)?;
        // Transform expressions containing placeholders into functions
        Ok(self.transform_partial_application(expr))
    }

    /// Transform an expression containing placeholders into a function.
    /// For example: `_ + 1` becomes `|__arg_0| __arg_0 + 1`
    /// Multiple placeholders: `_ / _` becomes `|__arg_0, __arg_1| __arg_0 / __arg_1`
    fn transform_partial_application(&self, expr: Expr) -> Expr {
        // Count placeholders to see if we need to transform
        let placeholder_count = self.count_placeholders(&expr);
        if placeholder_count == 0 {
            return expr;
        }

        // Generate parameter names
        let params: Vec<Param> = (0..placeholder_count)
            .map(|i| Param { name: format!("__arg_{}", i) })
            .collect();

        // Replace placeholders with identifiers
        let mut counter = 0;
        let body = self.replace_placeholders(expr, &mut counter);

        Expr::Function {
            params,
            body: Box::new(body),
        }
    }

    /// Count the number of placeholders in an expression
    fn count_placeholders(&self, expr: &Expr) -> usize {
        match expr {
            Expr::Placeholder => 1,
            Expr::Prefix { right, .. } => self.count_placeholders(right),
            Expr::Infix { left, right, .. } => {
                self.count_placeholders(left) + self.count_placeholders(right)
            }
            Expr::Call { function, args } => {
                self.count_placeholders(function) +
                args.iter().map(|a| self.count_placeholders(a)).sum::<usize>()
            }
            Expr::Index { collection, index } => {
                self.count_placeholders(collection) + self.count_placeholders(index)
            }
            Expr::List(elements) => {
                elements.iter().map(|e| self.count_placeholders(e)).sum()
            }
            Expr::Set(elements) => {
                elements.iter().map(|e| self.count_placeholders(e)).sum()
            }
            Expr::Dict(entries) => {
                entries.iter()
                    .map(|(k, v)| self.count_placeholders(k) + self.count_placeholders(v))
                    .sum()
            }
            // Don't count placeholders inside nested functions (they belong to that scope)
            Expr::Function { .. } => 0,
            // Other expressions don't contain placeholders
            _ => 0,
        }
    }

    /// Replace placeholders with identifiers
    fn replace_placeholders(&self, expr: Expr, counter: &mut usize) -> Expr {
        match expr {
            Expr::Placeholder => {
                let name = format!("__arg_{}", *counter);
                *counter += 1;
                Expr::Identifier(name)
            }
            Expr::Prefix { op, right } => {
                Expr::Prefix {
                    op,
                    right: Box::new(self.replace_placeholders(*right, counter)),
                }
            }
            Expr::Infix { left, op, right } => {
                Expr::Infix {
                    left: Box::new(self.replace_placeholders(*left, counter)),
                    op,
                    right: Box::new(self.replace_placeholders(*right, counter)),
                }
            }
            Expr::Call { function, args } => {
                Expr::Call {
                    function: Box::new(self.replace_placeholders(*function, counter)),
                    args: args.into_iter()
                        .map(|a| self.replace_placeholders(a, counter))
                        .collect(),
                }
            }
            Expr::Index { collection, index } => {
                Expr::Index {
                    collection: Box::new(self.replace_placeholders(*collection, counter)),
                    index: Box::new(self.replace_placeholders(*index, counter)),
                }
            }
            Expr::List(elements) => {
                Expr::List(
                    elements.into_iter()
                        .map(|e| self.replace_placeholders(e, counter))
                        .collect()
                )
            }
            Expr::Set(elements) => {
                Expr::Set(
                    elements.into_iter()
                        .map(|e| self.replace_placeholders(e, counter))
                        .collect()
                )
            }
            Expr::Dict(entries) => {
                Expr::Dict(
                    entries.into_iter()
                        .map(|(k, v)| (
                            self.replace_placeholders(k, counter),
                            self.replace_placeholders(v, counter)
                        ))
                        .collect()
                )
            }
            // Don't transform inside nested functions
            Expr::Function { params, body } => Expr::Function { params, body },
            // Other expressions pass through unchanged
            other => other,
        }
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

                // Check for direct trailing lambda syntax: identifier |params| body
                // e.g., memoize |x| x becomes memoize(|x| x)
                // This is the LANG.txt §8.8 "Direct trailing lambda" feature
                if let Some(next) = self.tokens.get(self.current) {
                    if matches!(next.kind, TokenKind::VerticalBar | TokenKind::OrOr) {
                        // This is a direct trailing lambda call
                        let lambda = self.parse_expression()?;
                        return Ok(Expr::Call {
                            function: Box::new(Expr::Identifier(value)),
                            args: vec![lambda],
                        });
                    }
                }

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
                // Check if this is an operator reference (no following operand)
                // or a prefix negation (followed by an expression)
                if self.is_expression_start() {
                    let right = self.parse_pratt_expr(7)?; // Prefix has high precedence (7)
                    Ok(Expr::Prefix {
                        op: PrefixOp::Negate,
                        right: Box::new(right),
                    })
                } else {
                    // Bare - is an operator reference: |a, b| a - b
                    Ok(Self::make_operator_lambda(InfixOp::Subtract))
                }
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
            TokenKind::If => {
                self.parse_if()
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

            // Operator function references: +, *, /, %, ==, !=, <, >, <=, >=, &&
            // These transform to lambdas: + becomes |__op_0, __op_1| __op_0 + __op_1
            // Per LANG.txt: fold(0, +, [1, 2, 3]) is valid
            TokenKind::Plus => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::Add))
            }
            TokenKind::Star => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::Multiply))
            }
            TokenKind::Slash => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::Divide))
            }
            TokenKind::Percent => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::Modulo))
            }
            TokenKind::EqualEqual => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::Equal))
            }
            TokenKind::NotEqual => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::NotEqual))
            }
            TokenKind::Less => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::LessThan))
            }
            TokenKind::LessEqual => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::LessThanOrEqual))
            }
            TokenKind::Greater => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::GreaterThan))
            }
            TokenKind::GreaterEqual => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::GreaterThanOrEqual))
            }
            TokenKind::AndAnd => {
                self.advance();
                Ok(Self::make_operator_lambda(InfixOp::And))
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
    ///
    /// For function bodies that start with `{`, we parse ONLY the block - not any
    /// trailing postfix operations like `()`. This ensures `|| { ... }()` is parsed
    /// as `(|| { ... })()` rather than `|| ({ ... }())`.
    fn parse_body_expr(&mut self) -> Result<Expr, ParseError> {
        let token = self.current_token()?;

        // If body starts with `{`, parse just the block (no postfix operations)
        if matches!(token.kind, TokenKind::LeftBrace) {
            return self.parse_block();
        }

        // Otherwise parse normally (e.g., for `|x| x + 1`)
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

        // Handle assignment specially - left must be an identifier
        if matches!(token.kind, TokenKind::Equal) {
            self.advance();
            // Assignment is right-associative, so use same precedence instead of +1
            let value = self.parse_pratt_expr(precedence)?;

            // Left side must be an identifier for assignment
            match left {
                Expr::Identifier(name) => {
                    return Ok(Expr::Assignment {
                        name,
                        value: Box::new(value),
                    });
                }
                _ => {
                    return Err(ParseError {
                        message: "Invalid assignment target - must be an identifier".to_string(),
                        line: token.span.start.line as usize,
                        column: token.span.start.column as usize,
                    });
                }
            }
        }

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

    fn parse_if(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'if'

        // Parse condition expression
        let condition = self.parse_expression()?;

        // Parse then branch (expect '{')
        let token = self.current_token()?;
        if !matches!(token.kind, TokenKind::LeftBrace) {
            return Err(ParseError {
                message: format!("Expected '{{' after if condition, got {:?}", token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            });
        }
        let then_branch = self.parse_block()?;

        // Check for else branch
        let else_branch = if matches!(self.current_token().map(|t| &t.kind), Ok(TokenKind::Else)) {
            self.advance(); // consume 'else'

            // Check if else-if or else
            let token = self.current_token()?;
            if matches!(token.kind, TokenKind::If) {
                // else if - parse as another if expression
                Some(self.parse_if()?)
            } else if matches!(token.kind, TokenKind::LeftBrace) {
                // else { ... }
                Some(self.parse_block()?)
            } else {
                return Err(ParseError {
                    message: format!("Expected '{{' or 'if' after else, got {:?}", token.kind),
                    line: token.span.start.line as usize,
                    column: token.span.start.column as usize,
                });
            }
        } else {
            None
        };

        Ok(Expr::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: else_branch.map(Box::new),
        })
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
            // Skip any semicolons between statements
            self.skip_statement_terminators();

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

            // Check for @slow attribute before test section
            let slow = if matches!(self.current_token()?.kind, TokenKind::At) {
                self.advance(); // consume '@'
                // Expect 'slow' identifier
                let token = self.current_token()?;
                if let TokenKind::Identifier(name) = &token.kind {
                    if name == "slow" {
                        self.advance(); // consume 'slow'
                        true
                    } else {
                        return Err(ParseError {
                            message: format!("Unknown attribute: @{}", name),
                            line: token.span.start.line as usize,
                            column: token.span.start.column as usize,
                        });
                    }
                } else {
                    return Err(ParseError {
                        message: format!("Expected attribute name after @, got {:?}", token.kind),
                        line: token.span.start.line as usize,
                        column: token.span.start.column as usize,
                    });
                }
            } else {
                false
            };

            // Check if this is a section (identifier followed by colon)
            if self.is_section_start() {
                let section = self.parse_section_with_slow(slow)?;
                sections.push(section);
                self.skip_statement_terminators();
            } else if slow {
                // @slow can only be applied to test sections
                let token = self.current_token()?;
                return Err(ParseError {
                    message: "@slow attribute can only be applied to test sections".to_string(),
                    line: token.span.start.line as usize,
                    column: token.span.start.column as usize,
                });
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

    /// Parse a section (input, part_one, part_two, or test) with optional slow attribute
    fn parse_section_with_slow(&mut self, slow: bool) -> Result<Section, ParseError> {
        let token = self.current_token()?.clone();

        if let TokenKind::Identifier(name) = &token.kind {
            match name.as_str() {
                "input" => {
                    if slow {
                        return Err(ParseError {
                            message: "@slow attribute can only be applied to test sections".to_string(),
                            line: token.span.start.line as usize,
                            column: token.span.start.column as usize,
                        });
                    }
                    self.advance(); // consume 'input'
                    self.expect(TokenKind::Colon)?;
                    let expr = self.parse_expression()?;
                    Ok(Section::Input(expr))
                }
                "part_one" => {
                    if slow {
                        return Err(ParseError {
                            message: "@slow attribute can only be applied to test sections".to_string(),
                            line: token.span.start.line as usize,
                            column: token.span.start.column as usize,
                        });
                    }
                    self.advance(); // consume 'part_one'
                    self.expect(TokenKind::Colon)?;
                    let expr = self.parse_expression()?;
                    Ok(Section::PartOne(expr))
                }
                "part_two" => {
                    if slow {
                        return Err(ParseError {
                            message: "@slow attribute can only be applied to test sections".to_string(),
                            line: token.span.start.line as usize,
                            column: token.span.start.column as usize,
                        });
                    }
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
                        slow,
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
