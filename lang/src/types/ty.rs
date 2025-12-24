use crate::lexer::token::Span;
use crate::parser::ast::{Expr, Section, Stmt};

/// Compile-time type information for specialization
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    // Primitive types
    Int,
    Decimal,
    String,
    Bool,
    Nil,

    // Collection types (with element/key-value types)
    List(Box<Type>),
    Set(Box<Type>),
    Dict(Box<Type>, Box<Type>), // key type, value type
    LazySequence(Box<Type>),    // element type

    // Function type
    Function { params: Vec<Type>, ret: Box<Type> },

    // Inference helpers
    Unknown,      // Cannot determine - fall back to runtime dispatch
    TypeVar(u32), // Unification variable (for polymorphic functions)
    Never,        // Bottom type (return, break - doesn't produce value)
}

impl Type {
    /// Check if this type is fully known (no Unknown or TypeVar)
    pub fn is_concrete(&self) -> bool {
        match self {
            Type::Unknown | Type::TypeVar(_) => false,
            Type::List(elem) | Type::Set(elem) | Type::LazySequence(elem) => elem.is_concrete(),
            Type::Dict(k, v) => k.is_concrete() && v.is_concrete(),
            Type::Function { params, ret } => {
                params.iter().all(|p| p.is_concrete()) && ret.is_concrete()
            }
            _ => true,
        }
    }

    /// Check if specialization is worthwhile for this type
    pub fn is_specializable(&self) -> bool {
        matches!(self, Type::Int | Type::Decimal | Type::Bool)
    }
}

/// Expression with inferred type
#[derive(Debug, Clone)]
pub struct TypedExpr {
    pub expr: Expr,
    pub ty: Type,
    pub span: Span,
}

/// Statement with type information
#[derive(Debug, Clone)]
pub struct TypedStmt {
    pub stmt: Stmt,
    pub ty: Type, // Type of expression statements, or Nil for let/return
    pub span: Span,
}

/// Typed section
#[derive(Debug, Clone)]
pub struct TypedSection {
    pub section: Section,
    pub ty: Type,
}

/// Typed program ready for codegen
#[derive(Debug, Clone)]
pub struct TypedProgram {
    pub statements: Vec<TypedStmt>,
    pub sections: Vec<TypedSection>,
}
