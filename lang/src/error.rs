//! Unified error handling for santa-lang.
//!
//! This module provides a unified error type that captures errors from all
//! phases of compilation and execution, with accurate source locations.

#[cfg(test)]
mod tests;

use crate::lexer::token::{Position, Span};
use std::fmt;

/// A unified error type for all phases of santa-lang compilation and execution.
///
/// All errors carry source location information (where available) and produce
/// clear, user-friendly error messages.
#[derive(Debug, Clone, PartialEq)]
pub enum SantaError {
    /// Lexer error (tokenization failed)
    LexError {
        message: String,
        position: Position,
    },

    /// Parser error (syntax error)
    ParseError {
        message: String,
        span: Span,
    },

    /// Compile error (code generation failed)
    CompileError {
        message: String,
        span: Option<Span>,
    },

    /// Runtime error (execution failed)
    RuntimeError {
        message: String,
        /// Stack trace of function calls (if available)
        stack_trace: Vec<StackFrame>,
    },
}

/// A frame in the call stack for error reporting.
#[derive(Debug, Clone, PartialEq)]
pub struct StackFrame {
    /// The function name (or "<anonymous>" for lambdas)
    pub function: String,
    /// Source location of the call site
    pub span: Option<Span>,
}

impl SantaError {
    /// Create a new lex error.
    pub fn lex(message: impl Into<String>, position: Position) -> Self {
        SantaError::LexError {
            message: message.into(),
            position,
        }
    }

    /// Create a new parse error.
    pub fn parse(message: impl Into<String>, span: Span) -> Self {
        SantaError::ParseError {
            message: message.into(),
            span,
        }
    }

    /// Create a new compile error with source location.
    pub fn compile(message: impl Into<String>, span: Span) -> Self {
        SantaError::CompileError {
            message: message.into(),
            span: Some(span),
        }
    }

    /// Create a new compile error without source location.
    pub fn compile_no_span(message: impl Into<String>) -> Self {
        SantaError::CompileError {
            message: message.into(),
            span: None,
        }
    }

    /// Create a new runtime error.
    pub fn runtime(message: impl Into<String>) -> Self {
        SantaError::RuntimeError {
            message: message.into(),
            stack_trace: Vec::new(),
        }
    }

    /// Create a new runtime error with stack trace.
    pub fn runtime_with_trace(message: impl Into<String>, stack_trace: Vec<StackFrame>) -> Self {
        SantaError::RuntimeError {
            message: message.into(),
            stack_trace,
        }
    }

    /// Get a short error kind description (e.g., "LexError", "ParseError").
    pub fn kind(&self) -> &'static str {
        match self {
            SantaError::LexError { .. } => "LexError",
            SantaError::ParseError { .. } => "ParseError",
            SantaError::CompileError { .. } => "CompileError",
            SantaError::RuntimeError { .. } => "RuntimeError",
        }
    }

    /// Get the error message.
    pub fn message(&self) -> &str {
        match self {
            SantaError::LexError { message, .. } => message,
            SantaError::ParseError { message, .. } => message,
            SantaError::CompileError { message, .. } => message,
            SantaError::RuntimeError { message, .. } => message,
        }
    }

    /// Get the source position/span if available.
    pub fn position(&self) -> Option<Position> {
        match self {
            SantaError::LexError { position, .. } => Some(*position),
            SantaError::ParseError { span, .. } => Some(span.start),
            SantaError::CompileError { span, .. } => span.map(|s| s.start),
            SantaError::RuntimeError { .. } => None,
        }
    }
}

impl fmt::Display for SantaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SantaError::LexError { message, position } => {
                write!(f, "LexError at {}:{}: {}", position.line, position.column, message)
            }
            SantaError::ParseError { message, span } => {
                write!(
                    f,
                    "ParseError at {}:{}: {}",
                    span.start.line, span.start.column, message
                )
            }
            SantaError::CompileError { message, span } => {
                if let Some(span) = span {
                    write!(
                        f,
                        "CompileError at {}:{}: {}",
                        span.start.line, span.start.column, message
                    )
                } else {
                    write!(f, "CompileError: {}", message)
                }
            }
            SantaError::RuntimeError { message, stack_trace } => {
                write!(f, "RuntimeError: {}", message)?;
                if !stack_trace.is_empty() {
                    writeln!(f)?;
                    writeln!(f, "Stack trace:")?;
                    for (i, frame) in stack_trace.iter().enumerate() {
                        if let Some(span) = &frame.span {
                            writeln!(
                                f,
                                "  {}: {} at {}:{}",
                                i, frame.function, span.start.line, span.start.column
                            )?;
                        } else {
                            writeln!(f, "  {}: {}", i, frame.function)?;
                        }
                    }
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for SantaError {}

// Conversions from existing error types

impl From<crate::lexer::LexError> for SantaError {
    fn from(err: crate::lexer::LexError) -> Self {
        use crate::lexer::LexError;
        match err {
            LexError::UnexpectedCharacter { ch, position } => {
                SantaError::lex(format!("Unexpected character '{}'", ch), position)
            }
            LexError::UnterminatedString { position } => {
                SantaError::lex("Unterminated string literal", position)
            }
            LexError::InvalidNumber { text, position } => {
                SantaError::lex(format!("Invalid number: '{}'", text), position)
            }
        }
    }
}

impl From<crate::parser::ParseError> for SantaError {
    fn from(err: crate::parser::ParseError) -> Self {
        let position = Position::new(err.line as u32, err.column as u32);
        let span = Span::new(position, position);
        SantaError::parse(err.message, span)
    }
}

impl From<crate::codegen::compiler::CompileError> for SantaError {
    fn from(err: crate::codegen::compiler::CompileError) -> Self {
        use crate::codegen::compiler::CompileError;
        let message = match err {
            CompileError::UnsupportedExpression(msg) => format!("Unsupported expression: {}", msg),
            CompileError::UnsupportedStatement(msg) => format!("Unsupported statement: {}", msg),
            CompileError::UnsupportedPattern(msg) => format!("Unsupported pattern: {}", msg),
            CompileError::ProtectedName(name) => {
                format!("'{}' is a protected built-in function and cannot be shadowed", name)
            }
        };
        SantaError::compile_no_span(message)
    }
}

impl From<crate::codegen::pipeline::CompileError> for SantaError {
    fn from(err: crate::codegen::pipeline::CompileError) -> Self {
        use crate::codegen::pipeline::CompileError;
        let message = match err {
            CompileError::LexError(msg) => format!("Lex error: {}", msg),
            CompileError::ParseError(msg) => format!("Parse error: {}", msg),
            CompileError::CodegenError(msg) => format!("Codegen error: {}", msg),
            CompileError::LinkError(msg) => format!("Link error: {}", msg),
            CompileError::IoError(e) => format!("I/O error: {}", e),
        };
        SantaError::compile_no_span(message)
    }
}

impl From<crate::runner::RunnerError> for SantaError {
    fn from(err: crate::runner::RunnerError) -> Self {
        use crate::runner::RunnerError;
        let message = match err {
            RunnerError::DuplicateInput => "Expected a single 'input' section".to_string(),
            RunnerError::DuplicatePartOne => "Expected single 'part_one' solution".to_string(),
            RunnerError::DuplicatePartTwo => "Expected single 'part_two' solution".to_string(),
            RunnerError::RuntimeError(msg) => msg,
        };
        SantaError::runtime(message)
    }
}
