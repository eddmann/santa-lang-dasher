use crate::lexer::token::{Position, Span};
use crate::parser::ast::{
    Expr, InfixOp, MatchArm, Param, Pattern, PrefixOp, Program, Section, Stmt,
};
use crate::types::builtins::{
    builtin_signatures, compute_expected_lambda_type, compute_return_type, BuiltinSignature,
};
use crate::types::ty::{Type, TypedExpr, TypedProgram, TypedSection, TypedStmt};
use crate::types::unify::Unifier;
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub struct TypeError {
    pub message: String,
    pub span: Span,
}

pub struct TypeInference {
    /// Type environment: variable name -> type
    env: HashMap<String, Type>,

    /// Current type variable counter (for future polymorphic inference)
    #[allow(dead_code)]
    next_type_var: u32,

    /// Unifier for type variables
    unifier: Unifier,

    /// Built-in function signatures
    builtins: HashMap<&'static str, BuiltinSignature>,

    /// User-defined function definitions: name -> (params, body)
    /// Used for call-site type inference - we re-infer the body with concrete arg types
    function_defs: HashMap<String, (Vec<Param>, Box<Expr>)>,

    /// Functions currently being inferred (to prevent infinite recursion for recursive functions)
    inferring: HashSet<String>,
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
            function_defs: HashMap::new(),
            inferring: HashSet::new(),
        }
    }

    /// Get the type environment after inference
    /// This can be passed to codegen for subexpression type lookup
    pub fn get_type_env(&self) -> &HashMap<String, Type> {
        &self.env
    }

    /// Consume self and return the type environment
    pub fn into_type_env(self) -> HashMap<String, Type> {
        self.env
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
                span,
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
            Section::Test {
                input,
                part_one,
                part_two,
                ..
            } => {
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

            // Range expressions: start..end or start..=end or start..
            Expr::Range { start, end, .. } => {
                let start_ty = self.infer_expr(start)?.ty;
                if let Some(end_expr) = end {
                    let end_ty = self.infer_expr(end_expr)?.ty;
                    // If both are Int, result is LazySequence<Int>
                    if matches!(start_ty, Type::Int) && matches!(end_ty, Type::Int) {
                        Type::LazySequence(Box::new(Type::Int))
                    } else {
                        Type::Unknown
                    }
                } else {
                    // Unbounded range: if start is Int, result is LazySequence<Int>
                    if matches!(start_ty, Type::Int) {
                        Type::LazySequence(Box::new(Type::Int))
                    } else {
                        Type::Unknown
                    }
                }
            }

            // Identifiers - look up in environment
            Expr::Identifier(name) => self.env.get(name).cloned().unwrap_or(Type::Unknown),

            // Block expressions
            Expr::Block(stmts) => self.infer_block(stmts)?,

            // Function expressions (lambdas)
            Expr::Function { params, body } => self.infer_function(params, body)?,

            // Function calls
            Expr::Call { function, args } => self.infer_call(function, args)?,

            // If expressions
            Expr::If {
                condition: _,
                then_branch,
                else_branch,
            } => {
                let then_ty = self.infer_expr(then_branch)?.ty;
                let else_ty = match else_branch {
                    Some(e) => self.infer_expr(e)?.ty,
                    None => Type::Nil, // No else branch returns nil when condition is false
                };
                // Unify the two branches - if they don't match, we get Unknown
                self.unifier
                    .unify(&then_ty, &else_ty)
                    .unwrap_or(Type::Unknown)
            }

            // Index expressions (collection[index])
            Expr::Index {
                collection,
                index: _,
            } => {
                let collection_ty = self.infer_expr(collection)?.ty;
                self.infer_index(&collection_ty)
            }

            // Match expressions
            Expr::Match { subject, arms } => {
                let subject_ty = self.infer_expr(subject)?.ty;
                self.infer_match(&subject_ty, arms)?
            }

            // IfLet expressions
            Expr::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                // Infer value type (used to bind pattern variables)
                let value_ty = self.infer_expr(value)?.ty;

                // Save environment
                let old_env = self.env.clone();

                // Bind pattern variables to value type
                self.bind_pattern(pattern, &value_ty);

                // Infer then_branch with pattern bindings in scope
                let then_ty = self.infer_expr(then_branch)?.ty;

                // Restore environment
                self.env = old_env;

                // Infer else_branch (if present)
                let else_ty = match else_branch {
                    Some(e) => self.infer_expr(e)?.ty,
                    None => Type::Nil, // No else branch returns nil when pattern doesn't match
                };

                // Unify the two branches
                self.unifier
                    .unify(&then_ty, &else_ty)
                    .unwrap_or(Type::Unknown)
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
                    _ => Ok(Type::Unknown),
                }
            }

            // x |> (some expression that returns a function)
            // This includes parser-generated lambdas from placeholder expressions
            // e.g., filter(|x| x > 0, _) becomes |__arg_0| filter(|x| x > 0, __arg_0)
            Expr::Function { params, body } if params.len() == 1 => {
                // Bind the single parameter to the left type and infer the body
                let old_env = self.env.clone();
                if let Some(param_name) = params[0].name() {
                    self.env.insert(param_name.to_string(), left_ty);
                }
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
    ///
    /// This implements bidirectional type inference:
    /// - For builtin calls: infer lambda param types from collection element types
    /// - For user-defined calls: re-infer the function body with concrete arg types
    fn infer_call(&mut self, function: &Expr, args: &[Expr]) -> Result<Type, TypeError> {
        // Check if function is a direct identifier call
        if let Expr::Identifier(name) = function {
            // First check builtins
            if let Some(sig) = self.builtins.get(name.as_str()).cloned() {
                return self.infer_builtin_call(&sig, args);
            }

            // Check if it's a user-defined function we can re-infer
            // Skip if we're already inferring this function (recursive call)
            if !self.inferring.contains(name) {
                if let Some((params, body)) = self.function_defs.get(name).cloned() {
                    return self.infer_user_defined_call(name, &params, &body, args);
                }
            }
        }

        // For other calls (lambda expressions, etc.), just infer argument types normally
        let _arg_types: Vec<Type> = args
            .iter()
            .map(|arg| self.infer_expr(arg).map(|t| t.ty))
            .collect::<Result<Vec<_>, _>>()?;

        // Infer the function type
        let func_ty = self.infer_expr(function)?.ty;

        // If we know the function type, extract the return type
        match func_ty {
            Type::Function { ret, .. } => Ok(*ret),
            _ => Ok(Type::Unknown), // Unknown function type
        }
    }

    /// Infer types for a user-defined function call by re-inferring the body
    /// with concrete argument types.
    ///
    /// This is the key to making user-defined function calls type-aware:
    /// - `let add = |a, b| a + b` stores add's definition
    /// - `add(1, 2)` re-infers the body with a:Int, b:Int → returns Int
    fn infer_user_defined_call(
        &mut self,
        name: &str,
        params: &[Param],
        body: &Expr,
        args: &[Expr],
    ) -> Result<Type, TypeError> {
        // Infer argument types
        let arg_types: Vec<Type> = args
            .iter()
            .map(|arg| self.infer_expr(arg).map(|t| t.ty))
            .collect::<Result<Vec<_>, _>>()?;

        // Save current environment
        let old_env = self.env.clone();

        // Mark this function as being inferred to prevent infinite recursion
        self.inferring.insert(name.to_string());

        // Bind parameters to argument types
        for (i, param) in params.iter().enumerate() {
            let arg_ty = arg_types.get(i).cloned().unwrap_or(Type::Unknown);
            if let Some(param_name) = param.name() {
                self.env.insert(param_name.to_string(), arg_ty);
            }
        }

        // Re-infer the body with concrete parameter types
        let body_ty = self.infer_expr(body)?.ty;

        // Restore environment and inferring set
        self.env = old_env;
        self.inferring.remove(name);

        Ok(body_ty)
    }

    /// Infer types for a builtin function call with bidirectional type inference
    ///
    /// The key insight is that for HOF calls like `filter(|x| x > 0, [1,2,3])`:
    /// 1. First, infer the collection type: `[1,2,3]` is `List<Int>`
    /// 2. Then, compute expected lambda type: `Int -> Bool`
    /// 3. Finally, infer the lambda with that expected type to get proper param types
    ///
    /// This also handles user-defined functions passed to builtins:
    /// `map(double, [1,2,3])` where `double = |x| x * 2` will re-infer double
    /// with Int param type to get the correct return type.
    fn infer_builtin_call(
        &mut self,
        sig: &BuiltinSignature,
        args: &[Expr],
    ) -> Result<Type, TypeError> {
        // Phase 1: Infer types for non-function arguments first
        // This gives us the information we need to determine expected function types
        let mut arg_types: Vec<Type> = vec![Type::Unknown; args.len()];

        for (i, arg) in args.iter().enumerate() {
            // Skip functions (lambdas and identifiers that are functions) in the first pass
            let is_function_arg = matches!(arg, Expr::Function { .. })
                || matches!(arg, Expr::Identifier(name) if self.function_defs.contains_key(name));

            if !is_function_arg {
                arg_types[i] = self.infer_expr(arg)?.ty;
            }
        }

        // Phase 2: Now infer function arguments with expected types from context
        for (i, arg) in args.iter().enumerate() {
            match arg {
                // Direct lambda: use bidirectional inference
                Expr::Function { .. } => {
                    let expected_ty = compute_expected_lambda_type(sig, i, &arg_types);
                    arg_types[i] = self.infer_expr_with_expected(arg, expected_ty.as_ref())?.ty;
                }
                // User-defined function reference: re-infer with expected param types
                // Skip if we're already inferring this function (prevent infinite recursion)
                Expr::Identifier(name) if self.function_defs.contains_key(name) && !self.inferring.contains(name) => {
                    let expected_ty = compute_expected_lambda_type(sig, i, &arg_types);
                    arg_types[i] =
                        self.infer_function_ref_with_expected(name, expected_ty.as_ref())?;
                }
                _ => {}
            }
        }

        // Compute return type based on all argument types
        Ok(compute_return_type(sig, &arg_types))
    }

    /// Infer the type of a user-defined function reference with an expected type
    ///
    /// When a user-defined function is passed to a HOF (e.g., `map(double, list)`),
    /// we re-infer its body with the expected parameter types to get the correct return type.
    fn infer_function_ref_with_expected(
        &mut self,
        name: &str,
        expected: Option<&Type>,
    ) -> Result<Type, TypeError> {
        // Check if we're already inferring this function (prevent infinite recursion)
        if self.inferring.contains(name) {
            return Ok(Type::Unknown);
        }

        // Get the function definition
        let (params, body) = match self.function_defs.get(name) {
            Some((p, b)) => (p.clone(), b.clone()),
            None => return Ok(Type::Unknown),
        };

        // Extract expected parameter types
        let expected_params = match expected {
            Some(Type::Function {
                params: expected_params,
                ..
            }) => expected_params.clone(),
            _ => vec![Type::Unknown; params.len()],
        };

        // Save current environment
        let old_env = self.env.clone();

        // Bind parameters to expected types
        for (i, param) in params.iter().enumerate() {
            let param_ty = expected_params.get(i).cloned().unwrap_or(Type::Unknown);
            if let Some(param_name) = param.name() {
                self.env.insert(param_name.to_string(), param_ty.clone());
            }
        }

        // Mark this function as being inferred to prevent infinite recursion
        self.inferring.insert(name.to_string());

        // Re-infer the body with the expected parameter types
        let ret_ty = self.infer_expr(&body)?.ty;

        // Restore environment and inferring set
        self.env = old_env;
        self.inferring.remove(name);

        Ok(Type::Function {
            params: expected_params,
            ret: Box::new(ret_ty),
        })
    }

    /// Infer expression type with an expected type hint for bidirectional inference
    fn infer_expr_with_expected(
        &mut self,
        expr: &Expr,
        expected: Option<&Type>,
    ) -> Result<TypedExpr, TypeError> {
        let span = Span::new(Position::new(1, 1), Position::new(1, 1));

        match expr {
            // For function expressions, use expected type to infer parameter types
            Expr::Function { params, body } => {
                let ty = self.infer_function_with_expected(params, body, expected)?;
                Ok(TypedExpr {
                    expr: expr.clone(),
                    ty,
                    span,
                })
            }
            // For other expressions, fall back to regular inference
            _ => self.infer_expr(expr),
        }
    }

    /// Infer the type of a function expression (lambda) without expected type context
    fn infer_function(&mut self, params: &[Param], body: &Expr) -> Result<Type, TypeError> {
        self.infer_function_with_expected(params, body, None)
    }

    /// Infer the type of a function expression with an optional expected type
    ///
    /// When an expected function type is provided (from bidirectional inference),
    /// we use its parameter types instead of defaulting to Unknown.
    fn infer_function_with_expected(
        &mut self,
        params: &[Param],
        body: &Expr,
        expected: Option<&Type>,
    ) -> Result<Type, TypeError> {
        // Save the current environment
        let old_env = self.env.clone();

        // Determine parameter types: use expected types if available, otherwise Unknown
        let param_types: Vec<Type> = match expected {
            Some(Type::Function {
                params: expected_params,
                ..
            }) => {
                // Use expected parameter types from context
                params
                    .iter()
                    .enumerate()
                    .map(|(i, param)| {
                        let ty = expected_params.get(i).cloned().unwrap_or(Type::Unknown);
                        if let Some(param_name) = param.name() {
                            self.env.insert(param_name.to_string(), ty.clone());
                        }
                        ty
                    })
                    .collect()
            }
            _ => {
                // No expected type - params are Unknown
                params
                    .iter()
                    .map(|param| {
                        let ty = Type::Unknown;
                        if let Some(param_name) = param.name() {
                            self.env.insert(param_name.to_string(), ty.clone());
                        }
                        ty
                    })
                    .collect()
            }
        };

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

            // Let bindings: infer value type and track in environment
            Stmt::Let { pattern, value, .. } => {
                // Infer the type of the value being bound
                let value_ty = self.infer_expr(value)?.ty;

                // If this is a function binding with a simple identifier pattern,
                // store the function definition for call-site type inference
                if let (Pattern::Identifier(name), Expr::Function { params, body }) =
                    (pattern, value)
                {
                    self.function_defs
                        .insert(name.clone(), (params.clone(), body.clone()));
                }

                // Bind pattern variables to their types in the environment
                self.bind_pattern(pattern, &value_ty);

                // Let statement evaluates to the bound value
                Ok(value_ty)
            }

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

    /// Bind pattern variables to their types in the environment
    fn bind_pattern(&mut self, pattern: &Pattern, ty: &Type) {
        match pattern {
            // Simple identifier: bind name to type
            Pattern::Identifier(name) => {
                self.env.insert(name.clone(), ty.clone());
            }
            // Wildcard: doesn't bind anything
            Pattern::Wildcard => {}
            // Literal: doesn't bind anything (used for matching)
            Pattern::Literal(_) => {}
            // Rest identifier in list: binds to same type (remainder of list)
            Pattern::RestIdentifier(name) => {
                self.env.insert(name.clone(), ty.clone());
            }
            // List pattern: destructure and bind each element
            Pattern::List(patterns) => {
                // Get element type from list/sequence
                let elem_ty = match ty {
                    Type::List(elem) | Type::Set(elem) | Type::LazySequence(elem) => {
                        (**elem).clone()
                    }
                    _ => Type::Unknown,
                };
                // Bind each pattern to element type (simplified - doesn't handle rest properly)
                for pat in patterns {
                    self.bind_pattern(pat, &elem_ty);
                }
            }
            // Range pattern: doesn't bind anything
            Pattern::Range { .. } => {}
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

        // Try to unify with all other elements
        // If elements have incompatible types (heterogeneous list/tuple), fall back to Unknown
        let elem_ty = elements[1..].iter().try_fold(first_ty, |acc, elem| {
            let elem_ty = self.infer_expr(elem)?.ty;
            // If unification fails, use Unknown (heterogeneous list)
            Ok(self.unifier.unify(&acc, &elem_ty).unwrap_or(Type::Unknown))
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
        let elem_ty = elements[1..].iter().try_fold(first_ty, |acc, elem| {
            let elem_ty = self.infer_expr(elem)?.ty;
            self.unifier.unify(&acc, &elem_ty).map_err(|e| TypeError {
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
        // If types can't be unified, fall back to Unknown (heterogeneous dicts are valid)
        let (key_ty, value_ty) = entries[1..].iter().fold(
            (first_key_ty, first_value_ty),
            |(acc_key, acc_value), (k, v)| {
                let key_ty = self.infer_expr(k).map(|t| t.ty).unwrap_or(Type::Unknown);
                let value_ty = self.infer_expr(v).map(|t| t.ty).unwrap_or(Type::Unknown);

                let unified_key = self
                    .unifier
                    .unify(&acc_key, &key_ty)
                    .unwrap_or(Type::Unknown);

                let unified_value = self
                    .unifier
                    .unify(&acc_value, &value_ty)
                    .unwrap_or(Type::Unknown);

                (unified_key, unified_value)
            },
        );

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
            (
                Equal | NotEqual | LessThan | LessThanOrEqual | GreaterThan | GreaterThanOrEqual,
                _,
                _,
            ) => Type::Bool,

            // Logical operators: always return Bool (truthiness)
            (And | Or, _, _) => Type::Bool,

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

    /// Infer the type of a match expression
    ///
    /// Match type is the unified type of all arm bodies.
    /// Pattern bindings are added to scope for each arm's body.
    fn infer_match(&mut self, subject_ty: &Type, arms: &[MatchArm]) -> Result<Type, TypeError> {
        if arms.is_empty() {
            return Ok(Type::Never); // Empty match can't produce a value
        }

        let mut result_ty: Option<Type> = None;

        for arm in arms {
            // Save environment
            let old_env = self.env.clone();

            // Bind pattern variables to subject type
            self.bind_pattern(&arm.pattern, subject_ty);

            // Infer guard if present
            if let Some(guard) = &arm.guard {
                self.infer_expr(guard)?;
            }

            // Infer body type
            let body_ty = self.infer_expr(&arm.body)?.ty;

            // Restore environment
            self.env = old_env;

            // Unify with previous arm types
            result_ty = Some(match &result_ty {
                None => body_ty,
                Some(prev_ty) => self
                    .unifier
                    .unify(prev_ty, &body_ty)
                    .unwrap_or(Type::Unknown),
            });
        }

        Ok(result_ty.unwrap_or(Type::Never))
    }
}
