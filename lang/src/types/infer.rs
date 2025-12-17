use std::collections::HashMap;
use crate::parser::ast::{Expr, Program, InfixOp, PrefixOp, Stmt, Param, Section};
use crate::types::ty::{Type, TypedExpr, TypedProgram, TypedStmt, TypedSection};
use crate::types::unify::Unifier;
use crate::types::builtins::{builtin_signatures, compute_return_type, BuiltinSignature};
use crate::lexer::token::{Span, Position};

#[derive(Debug)]
pub struct TypeError {
    pub message: String,
    pub span: Span,
}

pub struct TypeInference {
    /// Type environment: variable name -> type
    env: HashMap<String, Type>,

    /// Current type variable counter
    next_type_var: u32,

    /// Unifier for type variables
    unifier: Unifier,

    /// Built-in function signatures
    builtins: HashMap<&'static str, BuiltinSignature>,
}

impl Default for TypeInference {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeInference {
    pub fn new() -> Self {
        Self {
            env: HashMap::new(),
            next_type_var: 0,
            unifier: Unifier::new(),
            builtins: builtin_signatures(),
        }
    }

    pub fn infer_program(&mut self, program: &Program) -> Result<TypedProgram, TypeError> {
        let span = Span::new(Position::new(1, 1), Position::new(1, 1));

        // Infer types for all statements
        let mut typed_statements = Vec::new();
        for stmt in &program.statements {
            let ty = self.infer_stmt_type(stmt)?;
            typed_statements.push(TypedStmt {
                stmt: stmt.clone(),
                ty,
                span: span.clone(),
            });
        }

        // Infer types for all sections
        let mut typed_sections = Vec::new();
        for section in &program.sections {
            let ty = self.infer_section(section)?;
            typed_sections.push(TypedSection {
                section: section.clone(),
                ty,
            });
        }

        Ok(TypedProgram {
            statements: typed_statements,
            sections: typed_sections,
        })
    }

    /// Infer the type of a section
    fn infer_section(&mut self, section: &Section) -> Result<Type, TypeError> {
        match section {
            Section::Input(expr) => Ok(self.infer_expr(expr)?.ty),
            Section::PartOne(expr) => Ok(self.infer_expr(expr)?.ty),
            Section::PartTwo(expr) => Ok(self.infer_expr(expr)?.ty),
            Section::Test { input, part_one, part_two, .. } => {
                // Infer types for all test components, return the input type
                let input_ty = self.infer_expr(input)?.ty;
                if let Some(p1) = part_one {
                    self.infer_expr(p1)?;
                }
                if let Some(p2) = part_two {
                    self.infer_expr(p2)?;
                }
                Ok(input_ty)
            }
        }
    }

    /// Infer the type of a statement (returns Type, not TypedStmt)
    fn infer_stmt_type(&mut self, stmt: &Stmt) -> Result<Type, TypeError> {
        self.infer_stmt(stmt)
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

            // Prefix operations
            Expr::Prefix { op, right } => {
                let right_typed = self.infer_expr(right)?;
                self.infer_prefix_op(op, &right_typed.ty)
            }

            // Binary operations
            Expr::Infix { left, op, right } => {
                // Special handling for pipeline operator
                if *op == InfixOp::Pipeline {
                    self.infer_pipeline(left, right)?
                } else {
                    let left_typed = self.infer_expr(left)?;
                    let right_typed = self.infer_expr(right)?;
                    self.infer_binary_op(op, &left_typed.ty, &right_typed.ty)
                }
            }

            // Collections
            Expr::List(elements) => self.infer_list(elements)?,
            Expr::Set(elements) => self.infer_set(elements)?,
            Expr::Dict(entries) => self.infer_dict(entries)?,

            // Identifiers - look up in environment
            Expr::Identifier(name) => {
                self.env.get(name).cloned().unwrap_or(Type::Unknown)
            }

            // Block expressions
            Expr::Block(stmts) => self.infer_block(stmts)?,

            // Function expressions (lambdas)
            Expr::Function { params, body } => {
                self.infer_function(params, body)?
            }

            // Function calls
            Expr::Call { function, args } => {
                self.infer_call(function, args)?
            }

            // If expressions
            Expr::If { condition: _, then_branch, else_branch } => {
                let then_ty = self.infer_expr(then_branch)?.ty;
                let else_ty = match else_branch {
                    Some(e) => self.infer_expr(e)?.ty,
                    None => Type::Nil, // No else branch returns nil when condition is false
                };
                // Unify the two branches - if they don't match, we get Unknown
                self.unifier.unify(&then_ty, &else_ty).unwrap_or(Type::Unknown)
            }

            // Index expressions (collection[index])
            Expr::Index { collection, index: _ } => {
                let collection_ty = self.infer_expr(collection)?.ty;
                self.infer_index(&collection_ty)
            }

            // Everything else is Unknown for now
            _ => Type::Unknown,
        };

        Ok(TypedExpr {
            expr: expr.clone(),
            ty,
            span,
        })
    }

    /// Infer the type of a pipeline expression (x |> f)
    /// Pipeline is equivalent to f(x), or f(args..., x) for partial applications
    fn infer_pipeline(&mut self, left: &Expr, right: &Expr) -> Result<Type, TypeError> {
        // Infer the left side (the value being piped)
        let left_ty = self.infer_expr(left)?.ty;

        // Handle different right-hand side patterns
        match right {
            // x |> f  →  f(x)
            Expr::Identifier(name) => {
                if let Some(sig) = self.builtins.get(name.as_str()) {
                    return Ok(compute_return_type(sig, &[left_ty]));
                }
                // Unknown function
                Ok(Type::Unknown)
            }

            // x |> f(a, _)  →  f(a, x) (partial application fills in placeholder)
            Expr::Call { function, args } => {
                // Check if there's a placeholder in the args
                let has_placeholder = args.iter().any(|a| matches!(a, Expr::Placeholder));

                if has_placeholder {
                    // Replace placeholder with left value's type
                    let arg_types: Vec<Type> = args
                        .iter()
                        .map(|arg| {
                            if matches!(arg, Expr::Placeholder) {
                                left_ty.clone()
                            } else {
                                self.infer_expr(arg).map(|t| t.ty).unwrap_or(Type::Unknown)
                            }
                        })
                        .collect();

                    // Look up the function
                    if let Expr::Identifier(name) = function.as_ref() {
                        if let Some(sig) = self.builtins.get(name.as_str()) {
                            return Ok(compute_return_type(sig, &arg_types));
                        }
                    }
                }

                // Fall back to inferring the call normally (it may be a partial application)
                let call_ty = self.infer_expr(right)?;
                match call_ty.ty {
                    Type::Function { params: _, ret } => {
                        // Calling the partial with left as argument
                        Ok(*ret)
                    }
                    _ => Ok(Type::Unknown)
                }
            }

            // x |> (some expression that returns a function)
            // This includes parser-generated lambdas from placeholder expressions
            // e.g., filter(|x| x > 0, _) becomes |__arg_0| filter(|x| x > 0, __arg_0)
            Expr::Function { params, body } if params.len() == 1 => {
                // Bind the single parameter to the left type and infer the body
                let old_env = self.env.clone();
                self.env.insert(params[0].name.clone(), left_ty);
                let body_ty = self.infer_expr(body)?.ty;
                self.env = old_env;
                Ok(body_ty)
            }
            _ => {
                let func_ty = self.infer_expr(right)?.ty;
                match func_ty {
                    Type::Function { ret, .. } => Ok(*ret),
                    _ => Ok(Type::Unknown),
                }
            }
        }
    }

    /// Infer the type of a function call
    fn infer_call(&mut self, function: &Expr, args: &[Expr]) -> Result<Type, TypeError> {
        // Infer argument types
        let arg_types: Vec<Type> = args
            .iter()
            .map(|arg| self.infer_expr(arg).map(|t| t.ty))
            .collect::<Result<Vec<_>, _>>()?;

        // Check if function is a direct identifier call to a builtin
        if let Expr::Identifier(name) = function {
            if let Some(sig) = self.builtins.get(name.as_str()) {
                return Ok(compute_return_type(sig, &arg_types));
            }
        }

        // Infer the function type
        let func_ty = self.infer_expr(function)?.ty;

        // If we know the function type, extract the return type
        match func_ty {
            Type::Function { ret, .. } => Ok(*ret),
            _ => Ok(Type::Unknown), // Unknown function type
        }
    }

    /// Infer the type of a function expression (lambda)
    fn infer_function(&mut self, params: &[Param], body: &Expr) -> Result<Type, TypeError> {
        // Save the current environment
        let old_env = self.env.clone();

        // Create type variables for each parameter (Unknown without context)
        let param_types: Vec<Type> = params.iter().map(|param| {
            let ty = Type::Unknown; // Without context, params are Unknown
            self.env.insert(param.name.clone(), ty.clone());
            ty
        }).collect();

        // Infer the body type with parameters in scope
        let body_ty = self.infer_expr(body)?.ty;

        // Restore the environment
        self.env = old_env;

        Ok(Type::Function {
            params: param_types,
            ret: Box::new(body_ty),
        })
    }

    /// Infer the type of a block expression
    /// The block's type is the type of its last expression (or Nil if empty/ends with statement)
    fn infer_block(&mut self, stmts: &[Stmt]) -> Result<Type, TypeError> {
        if stmts.is_empty() {
            return Ok(Type::Nil);
        }

        // Process all statements, get the type of the last one
        let mut last_ty = Type::Nil;
        for stmt in stmts {
            last_ty = self.infer_stmt(stmt)?;
        }
        Ok(last_ty)
    }

    /// Infer the type of a statement
    fn infer_stmt(&mut self, stmt: &Stmt) -> Result<Type, TypeError> {
        match stmt {
            // Expression statement: type is the expression's type
            Stmt::Expr(expr) => Ok(self.infer_expr(expr)?.ty),

            // Let bindings: type is Nil (side-effect only)
            // TODO: track variable types in environment
            Stmt::Let { .. } => Ok(Type::Nil),

            // Return/Break: type is Never (doesn't produce value at this point)
            Stmt::Return(expr) => {
                // Infer the expression type for side effects
                self.infer_expr(expr)?;
                Ok(Type::Never)
            }
            Stmt::Break(expr) => {
                self.infer_expr(expr)?;
                Ok(Type::Never)
            }
        }
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
                self.unifier
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
                self.unifier
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

                let unified_key = self.unifier
                    .unify(&acc_key, &key_ty)
                    .map_err(|e| TypeError {
                        message: format!("Dict key type mismatch: {}", e),
                        span: Span::new(Position::new(1, 1), Position::new(1, 1)),
                    })?;

                let unified_value = self.unifier
                    .unify(&acc_value, &value_ty)
                    .map_err(|e| TypeError {
                        message: format!("Dict value type mismatch: {}", e),
                        span: Span::new(Position::new(1, 1), Position::new(1, 1)),
                    })?;

                Ok((unified_key, unified_value))
            })?;

        Ok(Type::Dict(Box::new(key_ty), Box::new(value_ty)))
    }

    /// Infer the result type of a prefix operation
    fn infer_prefix_op(&self, op: &PrefixOp, operand: &Type) -> Type {
        match (op, operand) {
            // Negation preserves numeric type
            (PrefixOp::Negate, Type::Int) => Type::Int,
            (PrefixOp::Negate, Type::Decimal) => Type::Decimal,

            // Logical not produces Bool
            (PrefixOp::Not, Type::Bool) => Type::Bool,

            // Unknown operands or unsupported combinations: fall back to runtime
            _ => Type::Unknown,
        }
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

    /// Infer the result type of an index expression (collection[index])
    fn infer_index(&self, collection_ty: &Type) -> Type {
        match collection_ty {
            // List<T>[Int] → T
            Type::List(elem_ty) => (**elem_ty).clone(),
            // Set<T>[Int] → T (though semantically unusual)
            Type::Set(elem_ty) => (**elem_ty).clone(),
            // Dict<K, V>[K] → V
            Type::Dict(_key_ty, value_ty) => (**value_ty).clone(),
            // String[Int] → String (single character)
            Type::String => Type::String,
            // LazySequence<T>[Int] → T
            Type::LazySequence(elem_ty) => (**elem_ty).clone(),
            // Unknown collection type
            _ => Type::Unknown,
        }
    }
}
