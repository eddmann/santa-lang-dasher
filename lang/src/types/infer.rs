use std::collections::HashMap;
use crate::parser::ast::{Expr, Program, InfixOp};
use crate::types::ty::{Type, TypedExpr, TypedProgram};
use crate::types::unify::Unifier;
use crate::lexer::token::{Span, Position};

#[derive(Debug)]
pub struct TypeError {
    pub message: String,
    pub span: Span,
}

pub struct TypeInference {
    /// Type environment: variable name -> type
    _env: HashMap<String, Type>,

    /// Current type variable counter
    _next_type_var: u32,

    /// Unifier for type variables
    _unifier: Unifier,
}

impl Default for TypeInference {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeInference {
    pub fn new() -> Self {
        Self {
            _env: HashMap::new(),
            _next_type_var: 0,
            _unifier: Unifier::new(),
        }
    }

    pub fn infer_program(&mut self, _program: &Program) -> Result<TypedProgram, TypeError> {
        // TODO: Implement
        unimplemented!()
    }

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<TypedExpr, TypeError> {
        // Create a dummy span for now (we'll add real span tracking later)
        let span = Span::new(Position::new(1, 1), Position::new(1, 1));

        let ty = match expr {
            // Literals have known types
            Expr::Integer(_) => Type::Int,
            Expr::Decimal(_) => Type::Decimal,
            Expr::String(_) => Type::String,
            Expr::Boolean(_) => Type::Bool,
            Expr::Nil => Type::Nil,

            // Binary operations
            Expr::Infix { left, op, right } => {
                let left_typed = self.infer_expr(left)?;
                let right_typed = self.infer_expr(right)?;
                self.infer_binary_op(op, &left_typed.ty, &right_typed.ty)
            }

            // Collections
            Expr::List(elements) => self.infer_list(elements)?,
            Expr::Set(elements) => self.infer_set(elements)?,
            Expr::Dict(entries) => self.infer_dict(entries)?,

            // Everything else is Unknown for now
            _ => Type::Unknown,
        };

        Ok(TypedExpr {
            expr: expr.clone(),
            ty,
            span,
        })
    }

    /// Infer the type of a list literal
    fn infer_list(&mut self, elements: &[Expr]) -> Result<Type, TypeError> {
        if elements.is_empty() {
            // Empty list: can't infer element type
            return Ok(Type::List(Box::new(Type::Unknown)));
        }

        // Infer type of first element
        let first_ty = self.infer_expr(&elements[0])?.ty;

        // Unify with all other elements
        let elem_ty = elements[1..]
            .iter()
            .try_fold(first_ty, |acc, elem| {
                let elem_ty = self.infer_expr(elem)?.ty;
                self._unifier
                    .unify(&acc, &elem_ty)
                    .map_err(|e| TypeError {
                        message: format!("List element type mismatch: {}", e),
                        span: Span::new(Position::new(1, 1), Position::new(1, 1)),
                    })
            })?;

        Ok(Type::List(Box::new(elem_ty)))
    }

    /// Infer the type of a set literal
    fn infer_set(&mut self, elements: &[Expr]) -> Result<Type, TypeError> {
        if elements.is_empty() {
            // Empty set: can't infer element type
            return Ok(Type::Set(Box::new(Type::Unknown)));
        }

        // Infer type of first element
        let first_ty = self.infer_expr(&elements[0])?.ty;

        // Unify with all other elements
        let elem_ty = elements[1..]
            .iter()
            .try_fold(first_ty, |acc, elem| {
                let elem_ty = self.infer_expr(elem)?.ty;
                self._unifier
                    .unify(&acc, &elem_ty)
                    .map_err(|e| TypeError {
                        message: format!("Set element type mismatch: {}", e),
                        span: Span::new(Position::new(1, 1), Position::new(1, 1)),
                    })
            })?;

        Ok(Type::Set(Box::new(elem_ty)))
    }

    /// Infer the type of a dict literal
    fn infer_dict(&mut self, entries: &[(Expr, Expr)]) -> Result<Type, TypeError> {
        if entries.is_empty() {
            // Empty dict: can't infer key/value types
            return Ok(Type::Dict(Box::new(Type::Unknown), Box::new(Type::Unknown)));
        }

        // Infer type of first entry
        let (first_key, first_value) = &entries[0];
        let first_key_ty = self.infer_expr(first_key)?.ty;
        let first_value_ty = self.infer_expr(first_value)?.ty;

        // Unify with all other entries
        let (key_ty, value_ty) = entries[1..]
            .iter()
            .try_fold((first_key_ty, first_value_ty), |(acc_key, acc_value), (k, v)| {
                let key_ty = self.infer_expr(k)?.ty;
                let value_ty = self.infer_expr(v)?.ty;

                let unified_key = self._unifier
                    .unify(&acc_key, &key_ty)
                    .map_err(|e| TypeError {
                        message: format!("Dict key type mismatch: {}", e),
                        span: Span::new(Position::new(1, 1), Position::new(1, 1)),
                    })?;

                let unified_value = self._unifier
                    .unify(&acc_value, &value_ty)
                    .map_err(|e| TypeError {
                        message: format!("Dict value type mismatch: {}", e),
                        span: Span::new(Position::new(1, 1), Position::new(1, 1)),
                    })?;

                Ok((unified_key, unified_value))
            })?;

        Ok(Type::Dict(Box::new(key_ty), Box::new(value_ty)))
    }

    /// Infer the result type of a binary operation
    /// Per LANG.txt §4.1, type coercion rules:
    /// - Left operand determines type for mixed numeric operations
    /// - String + X always produces String
    fn infer_binary_op(&self, op: &InfixOp, left: &Type, right: &Type) -> Type {
        use InfixOp::*;

        match (op, left, right) {
            // Arithmetic: same-type operands
            (Add | Subtract | Multiply, Type::Int, Type::Int) => Type::Int,
            (Add | Subtract | Multiply, Type::Decimal, Type::Decimal) => Type::Decimal,
            (Divide, Type::Int, Type::Int) => Type::Int, // Integer division
            (Divide, Type::Decimal, Type::Decimal) => Type::Decimal,
            (Modulo, Type::Int, Type::Int) => Type::Int,

            // Mixed numeric: left operand determines type (per LANG.txt §4.1)
            (Add | Subtract | Multiply | Divide, Type::Int, Type::Decimal) => Type::Int,
            (Add | Subtract | Multiply | Divide, Type::Decimal, Type::Int) => Type::Decimal,

            // String concatenation (String + X → String)
            (Add, Type::String, _) => Type::String,

            // Comparison operators: return Bool
            (Equal | NotEqual | LessThan | LessThanOrEqual | GreaterThan | GreaterThanOrEqual, _, _) => {
                Type::Bool
            }

            // Logical operators: Bool && Bool → Bool, Bool || Bool → Bool
            (And | Or, Type::Bool, Type::Bool) => Type::Bool,

            // Range operators: Int..Int → LazySequence<Int>
            (Range | RangeInclusive, Type::Int, Type::Int) => {
                Type::LazySequence(Box::new(Type::Int))
            }

            // Unknown operands or unsupported combinations: fall back to runtime
            _ => Type::Unknown,
        }
    }
}
