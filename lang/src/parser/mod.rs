pub mod ast;
#[cfg(test)]
mod tests;

use crate::lexer::{Token, TokenKind};
use ast::*;

// Precedence levels (higher number = higher precedence)
const PREC_ASSIGN: u8 = 1;
const PREC_OR: u8 = 2;
const PREC_AND: u8 = 3;
const PREC_EQUALITY: u8 = 4;
const PREC_COMPARISON: u8 = 5;
const PREC_PIPELINE: u8 = 6;
const PREC_ADDITIVE: u8 = 7;
const PREC_MULTIPLICATIVE: u8 = 8;
const PREC_PREFIX: u8 = 9;
const PREC_POSTFIX: u8 = 10;

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
        Self {
            tokens: filtered_tokens,
            current: 0,
        }
    }

    /// Create a binary operator lambda: |__op_0, __op_1| __op_0 OP __op_1
    /// Used when operators like + are passed as function references: fold(0, +, list)
    fn make_operator_lambda(op: InfixOp) -> Expr {
        Expr::Function {
            params: vec![
                Param::simple("__op_0".to_string()),
                Param::simple("__op_1".to_string()),
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
                    | TokenKind::Let
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
        // Special handling for Pipeline: transform both sides before looking at whole expression
        // This makes `10 |> _ - 1` correctly become `10 |> (|x| x - 1)`, not `|x| 10 |> x - 1`
        // And handles chained pipelines like `x |> f |> _ * 2`
        if let Expr::Infix {
            left,
            op: InfixOp::Pipeline,
            right,
        } = &expr
        {
            let transformed_left = self.transform_partial_application((**left).clone());
            let transformed_right = self.transform_partial_application((**right).clone());
            return Expr::Infix {
                left: Box::new(transformed_left),
                op: InfixOp::Pipeline,
                right: Box::new(transformed_right),
            };
        }

        // Special handling for Composition: transform both sides independently
        // This makes `f >> 6 - _` correctly become `f >> (|x| 6 - x)`, not `|x| f >> (6 - x)`
        if let Expr::Infix {
            left,
            op: InfixOp::Composition,
            right,
        } = &expr
        {
            let transformed_left = self.transform_partial_application((**left).clone());
            let transformed_right = self.transform_partial_application((**right).clone());
            return Expr::Infix {
                left: Box::new(transformed_left),
                op: InfixOp::Composition,
                right: Box::new(transformed_right),
            };
        }

        // Count placeholders to see if we need to transform
        let placeholder_count = self.count_placeholders(&expr);
        if placeholder_count == 0 {
            return expr;
        }

        // Generate parameter names
        let params: Vec<Param> = (0..placeholder_count)
            .map(|i| Param::simple(format!("__arg_{}", i)))
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
    #[allow(clippy::only_used_in_recursion)]
    fn count_placeholders(&self, expr: &Expr) -> usize {
        match expr {
            Expr::Placeholder => 1,
            Expr::Prefix { right, .. } => self.count_placeholders(right),
            Expr::Infix { left, right, .. } => {
                self.count_placeholders(left) + self.count_placeholders(right)
            }
            Expr::InfixCall { left, right, .. } => {
                self.count_placeholders(left) + self.count_placeholders(right)
            }
            Expr::Call { function, args } => {
                self.count_placeholders(function)
                    + args
                        .iter()
                        .map(|a| self.count_placeholders(a))
                        .sum::<usize>()
            }
            Expr::Index { collection, index } => {
                self.count_placeholders(collection) + self.count_placeholders(index)
            }
            Expr::List(elements) => elements.iter().map(|e| self.count_placeholders(e)).sum(),
            Expr::Set(elements) => elements.iter().map(|e| self.count_placeholders(e)).sum(),
            Expr::Dict(entries) => entries
                .iter()
                .map(|(k, v)| self.count_placeholders(k) + self.count_placeholders(v))
                .sum(),
            // Don't count placeholders inside nested functions (they belong to that scope)
            Expr::Function { .. } => 0,
            // Other expressions don't contain placeholders
            _ => 0,
        }
    }

    /// Replace placeholders with identifiers
    #[allow(clippy::only_used_in_recursion)]
    fn replace_placeholders(&self, expr: Expr, counter: &mut usize) -> Expr {
        match expr {
            Expr::Placeholder => {
                let name = format!("__arg_{}", *counter);
                *counter += 1;
                Expr::Identifier(name)
            }
            Expr::Prefix { op, right } => Expr::Prefix {
                op,
                right: Box::new(self.replace_placeholders(*right, counter)),
            },
            Expr::Infix { left, op, right } => Expr::Infix {
                left: Box::new(self.replace_placeholders(*left, counter)),
                op,
                right: Box::new(self.replace_placeholders(*right, counter)),
            },
            Expr::InfixCall {
                function,
                left,
                right,
            } => Expr::InfixCall {
                function,
                left: Box::new(self.replace_placeholders(*left, counter)),
                right: Box::new(self.replace_placeholders(*right, counter)),
            },
            Expr::Call { function, args } => Expr::Call {
                function: Box::new(self.replace_placeholders(*function, counter)),
                args: args
                    .into_iter()
                    .map(|a| self.replace_placeholders(a, counter))
                    .collect(),
            },
            Expr::Index { collection, index } => Expr::Index {
                collection: Box::new(self.replace_placeholders(*collection, counter)),
                index: Box::new(self.replace_placeholders(*index, counter)),
            },
            Expr::List(elements) => Expr::List(
                elements
                    .into_iter()
                    .map(|e| self.replace_placeholders(e, counter))
                    .collect(),
            ),
            Expr::Set(elements) => Expr::Set(
                elements
                    .into_iter()
                    .map(|e| self.replace_placeholders(e, counter))
                    .collect(),
            ),
            Expr::Dict(entries) => Expr::Dict(
                entries
                    .into_iter()
                    .map(|(k, v)| {
                        (
                            self.replace_placeholders(k, counter),
                            self.replace_placeholders(v, counter),
                        )
                    })
                    .collect(),
            ),
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
                    // Function call - highest precedence
                    if PREC_POSTFIX < min_precedence {
                        break;
                    }
                    left = self.parse_call(left)?;
                    continue;
                }
                TokenKind::LeftBracket => {
                    // Index - highest precedence
                    if PREC_POSTFIX < min_precedence {
                        break;
                    }
                    left = self.parse_index(left)?;
                    continue;
                }
                _ => {}
            }

            // Check for trailing lambda syntax: expr identifier lambda
            // e.g., [1, 2, 3] map |x| x * 2
            // For OrOr (||), only treat as trailing lambda if it can't be the OR operator
            if let TokenKind::Identifier(func_name) = &token.kind {
                // Look ahead to see if there's a lambda following
                if let Some(next) = self.tokens.get(self.current + 1) {
                    let is_lambda_start = match &next.kind {
                        TokenKind::VerticalBar => true,
                        TokenKind::OrOr => min_precedence > PREC_OR, // Only if || can't be OR operator
                        _ => false,
                    };
                    if is_lambda_start {
                        // This is a trailing lambda
                        let func_name = func_name.clone();
                        self.advance(); // consume identifier

                        // Parse the lambda with limited body precedence
                        // This ensures `list |> map |x| x |> dict` is parsed as
                        // `(list |> map(|x| x)) |> dict` rather than
                        // `list |> map(|x| x |> dict)`
                        let lambda = self.parse_trailing_lambda()?;

                        // Transform to: func_name(left, lambda)
                        left = Expr::Call {
                            function: Box::new(Expr::Identifier(func_name)),
                            args: vec![left, lambda],
                        };
                        continue;
                    }
                }
            }

            // Check for trailing lambda after a call: call(...) |params| body
            // e.g., fold(init) |acc, x| acc + x  ->  fold(init, |acc, x| acc + x)
            // For OrOr (||), only treat as trailing lambda if it can't be the OR operator
            // at this precedence level (i.e., OrOr precedence 1 < min_precedence)
            let is_trailing_lambda = match &token.kind {
                TokenKind::VerticalBar => true,
                TokenKind::OrOr => {
                    // Only treat || as trailing lambda if OR operator doesn't apply here
                    // OR has lower precedence than this context
                    min_precedence > PREC_OR
                }
                _ => false,
            };
            if is_trailing_lambda {
                if let Expr::Call { function, mut args } = left {
                    // Parse the lambda with limited body precedence
                    let lambda = self.parse_trailing_lambda()?;
                    args.push(lambda);
                    left = Expr::Call { function, args };
                    continue;
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
                // NOTE: Only match VerticalBar (|) here, not OrOr (||).
                // OrOr should primarily be the OR operator. If we match OrOr here,
                // expressions like `a `func` b || c` get misparsed because
                // the high-precedence parsing of `b` sees `|| c` as a trailing lambda.
                if let Some(next) = self.tokens.get(self.current) {
                    if matches!(next.kind, TokenKind::VerticalBar) {
                        // This is a direct trailing lambda call
                        // Use parse_trailing_lambda to limit body precedence, so that
                        // `[1, 2] |> map |x| x |> size` parses correctly
                        let lambda = self.parse_trailing_lambda()?;
                        return Ok(Expr::Call {
                            function: Box::new(Expr::Identifier(value)),
                            args: vec![lambda],
                        });
                    }
                }

                Ok(Expr::Identifier(value))
            }
            TokenKind::Let => self.parse_let_expression(),
            TokenKind::Underscore => {
                self.advance();
                Ok(Expr::Placeholder)
            }
            TokenKind::LeftBracket => self.parse_list(),
            TokenKind::HashBrace => self.parse_set_or_dict(),
            TokenKind::Bang => {
                self.advance();
                let right = self.parse_pratt_expr(PREC_PREFIX)?; // Prefix has high precedence
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
                    let right = self.parse_pratt_expr(PREC_PREFIX)?; // Prefix has high precedence
                    Ok(Expr::Prefix {
                        op: PrefixOp::Negate,
                        right: Box::new(right),
                    })
                } else {
                    // Bare - is an operator reference: |a, b| a - b
                    Ok(Self::make_operator_lambda(InfixOp::Subtract))
                }
            }
            TokenKind::DotDot => {
                // Spread operator: ..expr
                // Used in list literals: [..a, ..b]
                // Also used for infinite ranges when at start: ..n (same as 0..n)
                self.advance(); // consume '..'
                let expr = self.parse_pratt_expr(PREC_PREFIX)?; // High precedence
                Ok(Expr::Spread(Box::new(expr)))
            }
            TokenKind::VerticalBar => self.parse_function(),
            TokenKind::OrOr => {
                // || is lexed as a single token, but it could be an empty function parameter list
                // We need to check if this is a function (|| ...) or a logical OR
                // For now, treat it as a function with empty params
                self.parse_function_empty_params()
            }
            TokenKind::If => self.parse_if(),
            TokenKind::Match => self.parse_match(),
            TokenKind::LeftParen => {
                // Grouped expression: (expr)
                self.advance(); // consume '('
                let expr = self.parse_expression()?;
                let close = self.current_token()?;
                if !matches!(close.kind, TokenKind::RightParen) {
                    return Err(ParseError {
                        message: format!(
                            "Expected ')' after grouped expression, got {:?}",
                            close.kind
                        ),
                        line: close.span.start.line as usize,
                        column: close.span.start.column as usize,
                    });
                }
                self.advance(); // consume ')'
                Ok(expr)
            }
            TokenKind::LeftBrace => {
                // Disambiguate {} based on context (expression position)
                // Per LANG.txt: In expression position, {} should be parsed as a Set
                // We need to distinguish between:
                //   {1, 2, 3} - set literal
                //   {x} - set with one element
                //   {let y = 1; y} - block with statements
                self.parse_set_or_block_in_expr_position()
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

        // Parse parameters (can be identifiers or patterns like [a, b])
        loop {
            let token = self.current_token()?;
            match &token.kind {
                TokenKind::Identifier(name) => {
                    params.push(Param::simple(name.clone()));
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
                                message: format!(
                                    "Expected ',' or '|' in function parameters, got {:?}",
                                    next.kind
                                ),
                                line: next.span.start.line as usize,
                                column: next.span.start.column as usize,
                            });
                        }
                    }
                }
                TokenKind::LeftBracket => {
                    // Pattern parameter like [a, b]
                    let pattern = self.parse_pattern()?;
                    params.push(Param { pattern });

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
                                message: format!(
                                    "Expected ',' or '|' after pattern parameter, got {:?}",
                                    next.kind
                                ),
                                line: next.span.start.line as usize,
                                column: next.span.start.column as usize,
                            });
                        }
                    }
                }
                TokenKind::Underscore => {
                    // Wildcard parameter: |_| or |x, _|
                    params.push(Param {
                        pattern: Pattern::Wildcard,
                    });
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
                                message: format!(
                                    "Expected ',' or '|' after wildcard parameter, got {:?}",
                                    next.kind
                                ),
                                line: next.span.start.line as usize,
                                column: next.span.start.column as usize,
                            });
                        }
                    }
                }
                TokenKind::DotDot => {
                    // Rest parameter: |..rest| or |a, ..rest|
                    self.advance(); // consume '..'
                    let name_token = self.current_token()?;
                    let name = match &name_token.kind {
                        TokenKind::Identifier(name) => name.clone(),
                        _ => {
                            return Err(ParseError {
                                message: format!(
                                    "Expected identifier after '..' in rest parameter, got {:?}",
                                    name_token.kind
                                ),
                                line: name_token.span.start.line as usize,
                                column: name_token.span.start.column as usize,
                            });
                        }
                    };
                    self.advance(); // consume identifier
                    params.push(Param {
                        pattern: Pattern::RestIdentifier(name),
                    });

                    // Rest parameter must be last, so expect closing |
                    let next = self.current_token()?;
                    if !matches!(next.kind, TokenKind::VerticalBar) {
                        return Err(ParseError {
                            message: format!(
                                "Rest parameter must be last, expected '|' but got {:?}",
                                next.kind
                            ),
                            line: next.span.start.line as usize,
                            column: next.span.start.column as usize,
                        });
                    }
                    self.advance(); // consume closing '|'
                    break;
                }
                TokenKind::VerticalBar => {
                    // Empty parameter list: ||
                    self.advance();
                    break;
                }
                _ => {
                    return Err(ParseError {
                        message: format!(
                            "Expected identifier, '[', '..', or '|' in function parameters, got {:?}",
                            token.kind
                        ),
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
        self.parse_body_expr_with_min_prec(0)
    }

    /// Parse function body with a minimum precedence for non-block bodies.
    /// Used by trailing lambdas to limit body parsing.
    fn parse_body_expr_with_min_prec(&mut self, min_prec: u8) -> Result<Expr, ParseError> {
        let token = self.current_token()?;

        // If body starts with `{`, parse just the block (no postfix operations)
        if matches!(token.kind, TokenKind::LeftBrace) {
            return self.parse_block();
        }

        // Otherwise parse with the given minimum precedence
        self.parse_pratt_expr(min_prec)
    }

    /// Parse a lambda expression in trailing position (e.g., `map |x| x + 1`)
    ///
    /// For trailing lambdas, the body should NOT consume pipeline operators.
    /// This ensures `list |> map |x| x |> dict` is parsed as
    /// `(list |> map(|x| x)) |> dict` rather than `list |> map(|x| x |> dict)`.
    fn parse_trailing_lambda(&mut self) -> Result<Expr, ParseError> {
        let token = self.current_token()?;

        match &token.kind {
            TokenKind::VerticalBar => {
                self.advance(); // consume first '|'

                let mut params = Vec::new();

                // Parse parameters (can be identifiers or patterns like [a, b])
                loop {
                    let token = self.current_token()?;
                    match &token.kind {
                        TokenKind::Identifier(name) => {
                            params.push(Param::simple(name.clone()));
                            self.advance();

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
                                        message: format!(
                                            "Expected ',' or '|' in function parameters, got {:?}",
                                            next.kind
                                        ),
                                        line: next.span.start.line as usize,
                                        column: next.span.start.column as usize,
                                    });
                                }
                            }
                        }
                        TokenKind::LeftBracket => {
                            let pattern = self.parse_pattern()?;
                            params.push(Param { pattern });

                            let next = self.current_token()?;
                            match &next.kind {
                                TokenKind::Comma => {
                                    self.advance();
                                    continue;
                                }
                                TokenKind::VerticalBar => {
                                    self.advance();
                                    break;
                                }
                                _ => {
                                    return Err(ParseError {
                                        message: format!(
                                            "Expected ',' or '|' after pattern parameter, got {:?}",
                                            next.kind
                                        ),
                                        line: next.span.start.line as usize,
                                        column: next.span.start.column as usize,
                                    });
                                }
                            }
                        }
                        TokenKind::DotDot => {
                            // Rest parameter: |..rest|
                            self.advance();
                            let name_token = self.current_token()?;
                            let name = match &name_token.kind {
                                TokenKind::Identifier(name) => name.clone(),
                                _ => {
                                    return Err(ParseError {
                                        message: format!(
                                            "Expected identifier after '..' in rest parameter, got {:?}",
                                            name_token.kind
                                        ),
                                        line: name_token.span.start.line as usize,
                                        column: name_token.span.start.column as usize,
                                    });
                                }
                            };
                            self.advance();
                            params.push(Param {
                                pattern: Pattern::RestIdentifier(name),
                            });

                            let next = self.current_token()?;
                            if !matches!(next.kind, TokenKind::VerticalBar) {
                                return Err(ParseError {
                                    message: format!(
                                        "Expected '|' after rest parameter, got {:?}",
                                        next.kind
                                    ),
                                    line: next.span.start.line as usize,
                                    column: next.span.start.column as usize,
                                });
                            }
                            self.advance();
                            break;
                        }
                        TokenKind::VerticalBar => {
                            self.advance();
                            break;
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!(
                                    "Expected parameter or '|', got {:?}",
                                    token.kind
                                ),
                                line: token.span.start.line as usize,
                                column: token.span.start.column as usize,
                            });
                        }
                    }
                }

                // Parse body with precedence just above pipeline
                // This stops the body before consuming |> operators
                let body = self.parse_body_expr_with_min_prec(PREC_PIPELINE + 1)?;

                Ok(Expr::Function {
                    params,
                    body: Box::new(body),
                })
            }
            TokenKind::OrOr => {
                // Empty parameter list: || body
                self.advance();
                let body = self.parse_body_expr_with_min_prec(PREC_PIPELINE + 1)?;
                Ok(Expr::Function {
                    params: Vec::new(),
                    body: Box::new(body),
                })
            }
            _ => Err(ParseError {
                message: format!("Expected '|' or '||' for trailing lambda, got {:?}", token.kind),
                line: token.span.start.line as usize,
                column: token.span.start.column as usize,
            }),
        }
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
            // Transform placeholders in compound expressions to create nested functions.
            // This makes `filter(_ != 1)` parse as `filter(|x| x != 1)` first,
            // then the whole call can be transformed for partial application.
            // BUT: don't transform bare placeholders - `get(_, dict)` needs `_` to stay
            // as a placeholder for the outer Call's partial application transform.
            let arg = if matches!(arg, Expr::Placeholder) {
                arg // Keep bare placeholder for Call-level partial application
            } else {
                self.transform_partial_application(arg)
            };
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
                        message: format!(
                            "Expected ',' or ')' in call arguments, got {:?}",
                            token.kind
                        ),
                        line: token.span.start.line as usize,
                        column: token.span.start.column as usize,
                    })
                }
            }
        }

        let call = Expr::Call {
            function: Box::new(function),
            args,
        };

        // Transform placeholders at the call level.
        // This makes `get(_, x)` become `|a| get(a, x)` and
        // `map(get(_, x))` become `map(|a| get(a, x))` (since the nested
        // call is already transformed when used as an argument).
        Ok(self.transform_partial_application(call))
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

        // Check for empty dict
        if let Ok(token) = self.current_token() {
            if matches!(token.kind, TokenKind::RightBrace) {
                self.advance();
                // Empty #{} is an empty dictionary per LANG.txt
                return Ok(Expr::Dict(Vec::new()));
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
                                message: format!(
                                    "Expected ',' or '}}' in dict literal, got {:?}",
                                    token.kind
                                ),
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
                                    message: format!(
                                        "Expected ',' or '}}' in dict literal, got {:?}",
                                        token.kind
                                    ),
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
                        message: format!(
                            "Expected ',' or '}}' in set literal, got {:?}",
                            token.kind
                        ),
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

        // Handle range operators specially - produce Expr::Range instead of Expr::Infix
        if matches!(token.kind, TokenKind::DotDot | TokenKind::DotDotEqual) {
            let inclusive = matches!(token.kind, TokenKind::DotDotEqual);
            self.advance();

            // Check if there's a valid RHS expression (for infinite ranges like 1..)
            // A valid RHS starts with something that can begin an expression
            let has_rhs = !self.is_at_end() && self.can_start_expression();

            let end = if has_rhs {
                Some(Box::new(self.parse_pratt_expr(precedence + 1)?))
            } else {
                None
            };

            return Ok(Expr::Range {
                start: Box::new(left),
                end,
                inclusive,
            });
        }

        // Handle backtick infix call: a `f` b -> f(a, b)
        if matches!(token.kind, TokenKind::Backtick) {
            self.advance(); // consume first backtick

            // Expect an identifier (function name)
            let fn_token = self.current_token()?.clone();
            let function = match &fn_token.kind {
                TokenKind::Identifier(name) => name.clone(),
                _ => {
                    return Err(ParseError {
                        message: format!(
                            "Expected function name in backtick expression, got {:?}",
                            fn_token.kind
                        ),
                        line: fn_token.span.start.line as usize,
                        column: fn_token.span.start.column as usize,
                    });
                }
            };
            self.advance(); // consume function name

            // Expect closing backtick
            let close_token = self.current_token()?.clone();
            if !matches!(close_token.kind, TokenKind::Backtick) {
                return Err(ParseError {
                    message: format!("Expected closing backtick, got {:?}", close_token.kind),
                    line: close_token.span.start.line as usize,
                    column: close_token.span.start.column as usize,
                });
            }
            self.advance(); // consume closing backtick

            // Parse right operand
            let right = self.parse_pratt_expr(precedence + 1)?;

            return Ok(Expr::InfixCall {
                function,
                left: Box::new(left),
                right: Box::new(right),
            });
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

    /// Check if current token can start an expression (used for infinite range detection)
    fn can_start_expression(&self) -> bool {
        if self.is_at_end() {
            return false;
        }
        let token = &self.tokens[self.current];
        matches!(
            token.kind,
            TokenKind::Integer(_)
                | TokenKind::Decimal(_)
                | TokenKind::String(_)
                | TokenKind::Identifier(_)
                | TokenKind::True
                | TokenKind::False
                | TokenKind::Nil
                | TokenKind::LeftParen
                | TokenKind::LeftBracket
                | TokenKind::LeftBrace
                | TokenKind::HashBrace
                | TokenKind::VerticalBar
                | TokenKind::Minus
                | TokenKind::Bang
                | TokenKind::Underscore
        )
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

        // Precedence from LANG.txt §14.5
        // Lower number = lower precedence
        match &token.kind {
            // Assignment (lowest, right associative)
            TokenKind::Equal => PREC_ASSIGN,

            // Logical OR (||)
            TokenKind::OrOr => PREC_OR,

            // Logical AND (&&)
            TokenKind::AndAnd => PREC_AND,

            // Equality
            TokenKind::EqualEqual | TokenKind::NotEqual => PREC_EQUALITY,

            // Comparison
            TokenKind::Less
            | TokenKind::LessEqual
            | TokenKind::Greater
            | TokenKind::GreaterEqual => PREC_COMPARISON,

            // Composition/Pipeline/Range
            TokenKind::RightRight
            | TokenKind::Pipe
            | TokenKind::DotDot
            | TokenKind::DotDotEqual => PREC_PIPELINE,

            // Additive
            TokenKind::Plus | TokenKind::Minus => PREC_ADDITIVE,

            // Multiplicative/Infix
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent | TokenKind::Backtick => {
                PREC_MULTIPLICATIVE
            }

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
            TokenKind::LeftBracket => self.parse_list_pattern(),
            // Literal patterns
            TokenKind::Integer(n) => {
                let start = *n;
                self.advance();

                // Check for range pattern: 8..12, 8..=12, or 8..
                if let Ok(next) = self.current_token() {
                    match next.kind {
                        TokenKind::DotDot => {
                            self.advance(); // consume '..'
                            // Check for end value (optional for unbounded range)
                            let end = self.parse_range_end_integer(false)?;
                            return Ok(Pattern::Range {
                                start,
                                end,
                                inclusive: false,
                            });
                        }
                        TokenKind::DotDotEqual => {
                            self.advance(); // consume '..='
                            // Inclusive range requires end value
                            let end = self.parse_range_end_integer(true)?.unwrap();
                            return Ok(Pattern::Range {
                                start,
                                end: Some(end),
                                inclusive: true,
                            });
                        }
                        _ => {}
                    }
                }

                Ok(Pattern::Literal(Literal::Integer(start)))
            }
            TokenKind::Minus => {
                self.advance(); // consume '-'
                let next = self.current_token()?;
                match &next.kind {
                    TokenKind::Integer(n) => {
                        let start = -*n;
                        self.advance(); // consume integer

                        // Check for range pattern: -8..12, -8..=12, or -8..
                        if let Ok(next) = self.current_token() {
                            match next.kind {
                                TokenKind::DotDot => {
                                    self.advance(); // consume '..'
                                    let end = self.parse_range_end_integer(false)?;
                                    return Ok(Pattern::Range {
                                        start,
                                        end,
                                        inclusive: false,
                                    });
                                }
                                TokenKind::DotDotEqual => {
                                    self.advance(); // consume '..='
                                    let end = self.parse_range_end_integer(true)?.unwrap();
                                    return Ok(Pattern::Range {
                                        start,
                                        end: Some(end),
                                        inclusive: true,
                                    });
                                }
                                _ => {}
                            }
                        }

                        Ok(Pattern::Literal(Literal::Integer(start)))
                    }
                    TokenKind::Decimal(f) => {
                        let value = -*f;
                        self.advance(); // consume decimal
                        Ok(Pattern::Literal(Literal::Decimal(value)))
                    }
                    _ => Err(ParseError {
                        message: format!(
                            "Expected numeric literal after '-' in pattern, got {:?}",
                            next.kind
                        ),
                        line: next.span.start.line as usize,
                        column: next.span.start.column as usize,
                    }),
                }
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
        let mut seen_rest = false;

        loop {
            let token = self.current_token()?;

            match &token.kind {
                TokenKind::RightBracket => {
                    self.advance(); // consume ']'
                    break;
                }
                TokenKind::DotDot => {
                    // Rest pattern: ..rest (DotDot followed by identifier)
                    if seen_rest {
                        return Err(ParseError {
                            message: "Multiple rest patterns are not allowed".to_string(),
                            line: token.span.start.line as usize,
                            column: token.span.start.column as usize,
                        });
                    }
                    self.advance(); // consume '..'
                    let token = self.current_token()?;
                    let name = match &token.kind {
                        TokenKind::Identifier(name) => {
                            let name = name.clone();
                            self.advance(); // consume identifier
                            name
                        }
                        TokenKind::RightBracket | TokenKind::Comma => {
                            // Bare rest pattern: `..` (ignore rest)
                            String::new()
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!(
                                    "Expected identifier or ']' after '..' in rest pattern, got {:?}",
                                    token.kind
                                ),
                                line: token.span.start.line as usize,
                                column: token.span.start.column as usize,
                            });
                        }
                    };
                    let rest_pattern = Pattern::RestIdentifier(name);
                    patterns.push(rest_pattern);
                    seen_rest = true;

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
                                message: format!(
                                    "Expected ',' or ']' after rest pattern, got {:?}",
                                    next.kind
                                ),
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
                                message: format!(
                                    "Expected ',' or ']' in list pattern, got {:?}",
                                    next.kind
                                ),
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

    /// Parse the end value of a range pattern (integer only, optional minus).
    /// If `required` is true and no valid integer is found, returns an error.
    fn parse_range_end_integer(&mut self, required: bool) -> Result<Option<i64>, ParseError> {
        if self.is_at_end() {
            if required {
                return Err(ParseError {
                    message: "Expected integer in range pattern".to_string(),
                    line: 0,
                    column: 0,
                });
            }
            return Ok(None);
        }

        let token = self.current_token()?;
        match &token.kind {
            TokenKind::Integer(n) => {
                let end = *n;
                self.advance();
                Ok(Some(end))
            }
            TokenKind::Minus => {
                self.advance(); // consume '-'
                let next = self.current_token()?;
                if let TokenKind::Integer(n) = next.kind {
                    self.advance();
                    Ok(Some(-n))
                } else {
                    Err(ParseError {
                        message: format!(
                            "Expected integer after '-' in range pattern, got {:?}",
                            next.kind
                        ),
                        line: next.span.start.line as usize,
                        column: next.span.start.column as usize,
                    })
                }
            }
            _ => {
                if required {
                    Err(ParseError {
                        message: format!(
                            "Expected integer in range pattern, got {:?}",
                            token.kind
                        ),
                        line: token.span.start.line as usize,
                        column: token.span.start.column as usize,
                    })
                } else {
                    Ok(None)
                }
            }
        }
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

    fn parse_let_expression(&mut self) -> Result<Expr, ParseError> {
        let stmt = self.parse_let_statement()?;
        Ok(Expr::Block(vec![stmt]))
    }

    fn parse_if(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'if'

        // Check for if-let pattern
        if matches!(self.current_token().map(|t| &t.kind), Ok(TokenKind::Let)) {
            self.advance(); // consume 'let'

            // Parse pattern
            let pattern = self.parse_pattern()?;

            // Expect '='
            let token = self.current_token()?;
            if !matches!(token.kind, TokenKind::Equal) {
                return Err(ParseError {
                    message: format!("Expected '=' after if-let pattern, got {:?}", token.kind),
                    line: token.span.start.line as usize,
                    column: token.span.start.column as usize,
                });
            }
            self.advance(); // consume '='

            // Parse value expression
            let value = self.parse_expression()?;

            // Parse then branch
            let then_branch = self.parse_block()?;

            // Check for else branch
            let else_branch =
                if matches!(self.current_token().map(|t| &t.kind), Ok(TokenKind::Else)) {
                    self.advance(); // consume 'else'
                    let token = self.current_token()?;
                    if matches!(token.kind, TokenKind::LeftBrace) {
                        Some(self.parse_block()?)
                    } else if matches!(token.kind, TokenKind::If) {
                        Some(self.parse_if()?)
                    } else {
                        return Err(ParseError {
                            message: format!(
                                "Expected '{{' or 'if' after else, got {:?}",
                                token.kind
                            ),
                            line: token.span.start.line as usize,
                            column: token.span.start.column as usize,
                        });
                    }
                } else {
                    None
                };

            return Ok(Expr::IfLet {
                pattern,
                value: Box::new(value),
                then_branch: Box::new(then_branch),
                else_branch: else_branch.map(Box::new),
            });
        }

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

    /// Disambiguate between set literal and block in expression position
    /// Per LANG.txt: In expression position, {} should be parsed as Set
    /// - {1, 2, 3} → set literal
    /// - {x} → set with one element
    /// - {let y = 1; y} → block with statements
    fn parse_set_or_block_in_expr_position(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume '{'

        // Empty braces: {} → empty Set in expression position
        if let Ok(token) = self.current_token() {
            if matches!(token.kind, TokenKind::RightBrace) {
                self.advance();
                return Ok(Expr::Set(Vec::new()));
            }
        }

        // Check if the first token indicates this must be a block
        // (statement-starting keywords that can't be expression starts)
        if let Ok(token) = self.current_token() {
            if matches!(
                token.kind,
                TokenKind::Let | TokenKind::Return | TokenKind::Break
            ) {
                // Definitely a block - use parse_block logic
                return self.parse_block_body();
            }
        }

        // Try to parse as expression, then look at what follows
        let first_expr = self.parse_pratt_expr(0)?;

        // Check what follows the first expression
        if let Ok(token) = self.current_token() {
            match &token.kind {
                // Comma means it's definitely a set
                TokenKind::Comma => {
                    // It's a set, parse remaining elements
                    let mut elements = vec![first_expr];
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
                                    message: format!(
                                        "Expected ',' or '}}' in set literal, got {:?}",
                                        token.kind
                                    ),
                                    line: token.span.start.line as usize,
                                    column: token.span.start.column as usize,
                                })
                            }
                        }
                    }
                    return Ok(Expr::Set(elements));
                }
                // Closing brace with single expression and no semicolon
                // Per decision: in expression position, {expr} is always a Set literal.
                TokenKind::RightBrace => {
                    self.advance();
                    return Ok(Expr::Set(vec![first_expr]));
                }
                // Semicolon means it's a block
                TokenKind::Semicolon => {
                    // It's a block - first_expr becomes a statement, continue parsing
                    let first_stmt = Stmt::Expr(first_expr);
                    let mut statements = vec![first_stmt];

                    loop {
                        self.skip_statement_terminators();

                        let token = self.current_token()?;
                        if matches!(token.kind, TokenKind::RightBrace) {
                            self.advance();
                            break;
                        }

                        let stmt = self.parse_statement()?;
                        statements.push(stmt);
                    }
                    return Ok(Expr::Block(statements));
                }
                // Something else - could be continuation of expression or block
                _ => {
                    // Could be a more complex expression that wasn't fully parsed,
                    // or could be a block statement. Treat as block.
                    let first_stmt = Stmt::Expr(first_expr);
                    let mut statements = vec![first_stmt];

                    loop {
                        self.skip_statement_terminators();

                        let token = self.current_token()?;
                        if matches!(token.kind, TokenKind::RightBrace) {
                            self.advance();
                            break;
                        }

                        let stmt = self.parse_statement()?;
                        statements.push(stmt);
                    }
                    return Ok(Expr::Block(statements));
                }
            }
        }

        Err(ParseError {
            message: "Unexpected end of input in braces".to_string(),
            line: 0,
            column: 0,
        })
    }

    /// Parse block body (after '{' has been consumed)
    fn parse_block_body(&mut self) -> Result<Expr, ParseError> {
        let mut statements = Vec::new();

        loop {
            self.skip_statement_terminators();

            let token = self.current_token()?;
            if matches!(token.kind, TokenKind::RightBrace) {
                self.advance();
                break;
            }

            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }

        Ok(Expr::Block(statements))
    }

    fn parse_block(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume '{'
        self.parse_block_body()
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
                            message: "@slow attribute can only be applied to test sections"
                                .to_string(),
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
                            message: "@slow attribute can only be applied to test sections"
                                .to_string(),
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
                            message: "@slow attribute can only be applied to test sections"
                                .to_string(),
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
                                        message: format!(
                                            "Unexpected field in test section: {}",
                                            field_name
                                        ),
                                        line: token.span.start.line as usize,
                                        column: token.span.start.column as usize,
                                    });
                                }
                            }
                        } else {
                            return Err(ParseError {
                                message: format!(
                                    "Expected field name in test section, got {:?}",
                                    token.kind
                                ),
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

    /// Determines if an expression is suitable as a single set element.
    /// Returns true for "value-like" expressions (identifiers, literals, collections).
    /// Returns false for computed expressions (infix, calls) which suggest a block.
    fn is_set_element_expr(expr: &Expr) -> bool {
        match expr {
            // These are clearly set elements (literals and collections)
            Expr::Identifier(_) => true,
            Expr::List(_) => true,
            Expr::Dict(_) => true,
            Expr::Set(_) => true,
            Expr::Integer(_) => true,
            Expr::Decimal(_) => true,
            Expr::String(_) => true,
            Expr::Boolean(_) => true,
            Expr::Nil => true,
            Expr::Placeholder => true,
            Expr::RestIdentifier(_) => true,
            // Range is a value (could be a set element)
            Expr::Range { .. } => true,
            // Index access is value-like (getting an element)
            Expr::Index { .. } => true,
            // These suggest computation, so treat as block
            Expr::Infix { .. } => false,
            Expr::Prefix { .. } => false,
            Expr::Call { .. } => false,
            Expr::InfixCall { .. } => false,
            Expr::Function { .. } => false,
            Expr::Block(_) => false,
            Expr::If { .. } => false,
            Expr::IfLet { .. } => false,
            Expr::Match { .. } => false,
            Expr::Spread(_) => false,
            Expr::Assignment { .. } => false,
        }
    }
}

pub fn parse(tokens: Vec<Token>) -> Result<Expr, ParseError> {
    let mut parser = Parser::new(tokens);
    parser.parse_expression()
}
