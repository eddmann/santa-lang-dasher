use super::context::CodegenContext;
use crate::parser::ast::{Expr, InfixOp, Literal, MatchArm, Param, Pattern, PrefixOp, Stmt};
use crate::runtime::builtin_registry::builtin_spec;
use crate::types::{Type, TypedExpr};
use inkwell::values::BasicValueEnum;
use inkwell::IntPredicate;
use std::collections::HashSet;

#[derive(Debug)]
pub enum CompileError {
    UnsupportedExpression(String),
    UnsupportedStatement(String),
    UnsupportedPattern(String),
}

// Builtin names are protected per LANG.txt and cannot be shadowed by bindings.

impl<'ctx> CodegenContext<'ctx> {
    pub fn compile_expr(&mut self, expr: &TypedExpr) -> Result<BasicValueEnum<'ctx>, CompileError> {
        match &expr.expr {
            Expr::Integer(n) => Ok(self.compile_integer(*n)),
            Expr::Decimal(f) => Ok(self.compile_decimal(*f)),
            Expr::Boolean(b) => Ok(self.compile_boolean(*b)),
            Expr::Nil => Ok(self.compile_nil()),
            Expr::String(s) => self.compile_string(s),
            Expr::Identifier(name) => {
                // Look up the variable and load its value
                if let Some(alloca) = self.variables.get(name) {
                    let load = self
                        .builder
                        .build_load(self.context.i64_type(), *alloca, name)
                        .unwrap();
                    // If this is a cell variable, unwrap the cell to get the actual value
                    if self.cell_variables.contains(name) {
                        let rt_cell_get = self.get_or_declare_rt_cell_get();
                        let cell_val = self
                            .builder
                            .build_call(rt_cell_get, &[load.into()], &format!("{}_unwrap", name))
                            .unwrap();
                        Ok(cell_val.try_as_basic_value().left().unwrap())
                    } else {
                        Ok(load)
                    }
                } else if let Some(arity) = Self::builtin_value_arity(name) {
                    // Builtin function referenced without being called - create a function value
                    if let Some(result) = self.compile_partial_builtin(name, &[], arity)? {
                        Ok(result)
                    } else {
                        Err(CompileError::UnsupportedExpression(format!(
                            "Failed to create function value for builtin: {}",
                            name
                        )))
                    }
                } else {
                    Err(CompileError::UnsupportedExpression(format!(
                        "Undefined variable: {}",
                        name
                    )))
                }
            }
            Expr::Prefix { op, right } => self.compile_prefix(op, right, &expr.ty),
            Expr::Infix { left, op, right } => self.compile_binary(left, op, right, &expr.ty),
            Expr::List(elements) => self.compile_list(elements),
            Expr::Set(elements) => self.compile_set(elements),
            Expr::Dict(entries) => self.compile_dict(entries),
            Expr::Range {
                start,
                end,
                inclusive,
            } => self.compile_range(start, end.as_deref(), *inclusive),
            Expr::Index { collection, index } => self.compile_index(collection, index),
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => self.compile_if(condition, then_branch, else_branch.as_deref()),
            Expr::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => self.compile_if_let(pattern, value, then_branch, else_branch.as_deref()),
            Expr::Block(stmts) => self.compile_block(stmts),
            Expr::Function { params, body } => self.compile_function(params, body),
            Expr::Call { function, args } => self.compile_call(function, args),
            Expr::InfixCall {
                function,
                left,
                right,
            } => {
                // a `f` b transforms to f(a, b)
                let fn_expr = Expr::Identifier(function.clone());
                let args = vec![(**left).clone(), (**right).clone()];
                self.compile_call(&fn_expr, &args)
            }
            Expr::Match { subject, arms } => self.compile_match(subject, arms),
            Expr::Assignment { name, value } => self.compile_assignment(name, value),
            _ => Err(CompileError::UnsupportedExpression(format!(
                "Expression type not yet implemented: {:?}",
                expr.expr
            ))),
        }
    }

    /// Compile an assignment expression (for mutable variables)
    fn compile_assignment(
        &mut self,
        name: &str,
        value: &Expr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Look up the variable
        let alloca = self.variables.get(name).cloned().ok_or_else(|| {
            CompileError::UnsupportedExpression(format!(
                "Undefined variable for assignment: {}",
                name
            ))
        })?;

        if !self.mutable_variables.contains(name) {
            return Err(CompileError::UnsupportedExpression(format!(
                "Cannot assign to immutable binding: {}",
                name
            )));
        }

        // Compile the value expression
        let value_ty = self.infer_expr_type(value);
        let value_typed = TypedExpr {
            expr: value.clone(),
            ty: value_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let compiled_value = self.compile_expr(&value_typed)?;

        // If this is a cell variable, use rt_cell_set instead of direct store
        if self.cell_variables.contains(name) {
            // Load the cell, then set its value
            let cell = self
                .builder
                .build_load(self.context.i64_type(), alloca, &format!("{}_cell", name))
                .unwrap();
            let rt_cell_set = self.get_or_declare_rt_cell_set();
            let result = self
                .builder
                .build_call(
                    rt_cell_set,
                    &[cell.into(), compiled_value.into()],
                    &format!("{}_set", name),
                )
                .unwrap();
            Ok(result.try_as_basic_value().left().unwrap())
        } else {
            // Direct store for non-cell variables
            self.builder.build_store(alloca, compiled_value).unwrap();
            Ok(compiled_value)
        }
    }

    /// Compile an integer literal to a NaN-boxed tagged value
    /// Tag scheme: (value << 3) | 0b001
    fn compile_integer(&self, value: i64) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();

        // Shift left by 3 and OR with tag 0b001
        let shifted = (value as u64) << 3;
        let tagged = shifted | 0b001;

        i64_type.const_int(tagged, false).into()
    }

    /// Compile a decimal literal to a native f64 value
    /// Decimals are stored as raw f64 bit patterns inside the Value (i64)
    fn compile_decimal(&self, value: f64) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();
        i64_type.const_int(value.to_bits(), false).into()
    }

    /// Compile a boolean literal to a NaN-boxed tagged value
    /// Tag scheme: (bool_value << 3) | 0b011
    /// true: (1 << 3) | 0b011 = 0b1011 = 11
    /// false: (0 << 3) | 0b011 = 0b0011 = 3
    fn compile_boolean(&self, value: bool) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();
        let bool_as_int = if value { 1u64 } else { 0u64 };
        let tagged = (bool_as_int << 3) | 0b011;
        i64_type.const_int(tagged, false).into()
    }

    /// Compile nil literal to a NaN-boxed tagged value
    /// Tag scheme: 0b010
    fn compile_nil(&self) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();
        i64_type.const_int(0b010, false).into()
    }

    /// Compile a string literal by creating a global constant and calling runtime function
    fn compile_string(&mut self, value: &str) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Create a global string constant
        let string_value = self.context.const_string(value.as_bytes(), false);
        let global = self.module.add_global(string_value.get_type(), None, "str");
        global.set_initializer(&string_value);
        global.set_constant(true);
        global.set_unnamed_addr(true);

        // Get pointer to the string data
        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let string_ptr = self
            .builder
            .build_pointer_cast(global.as_pointer_value(), ptr_type, "str_ptr")
            .unwrap();

        // Get or declare rt_string_from_cstr function
        let rt_string_fn = self.get_or_declare_rt_string_from_cstr();

        // Call rt_string_from_cstr(ptr, len)
        let len = self.context.i64_type().const_int(value.len() as u64, false);
        let call_result = self
            .builder
            .build_call(
                rt_string_fn,
                &[string_ptr.into(), len.into()],
                "string_value",
            )
            .unwrap();

        Ok(call_result.try_as_basic_value().left().unwrap())
    }

    /// Get or declare the rt_string_from_cstr runtime function
    fn get_or_declare_rt_string_from_cstr(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_string_from_cstr";

        // Check if already declared
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Declare: extern "C" fn(ptr: *const i8, len: usize) -> Value (i64)
        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[ptr_type.into(), i64_type.into()], false);

        self.module.add_function(fn_name, fn_type, None)
    }

    /// Compile a prefix (unary) operation
    fn compile_prefix(
        &mut self,
        op: &PrefixOp,
        right: &Expr,
        _result_ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Infer the type of the operand
        let right_ty = self.infer_expr_type(right);

        let right_typed = TypedExpr {
            expr: right.clone(),
            ty: right_ty.clone(),
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };

        let right_val = self.compile_expr(&right_typed)?;

        match (op, &right_ty) {
            // Negate integer (FAST PATH)
            (PrefixOp::Negate, Type::Int) => {
                let val = self.unbox_int(right_val);
                // Negate: 0 - val
                let zero = self.context.i64_type().const_zero();
                let result = self.builder.build_int_sub(zero, val, "neg").unwrap();
                Ok(self.box_int(result))
            }

            // Negate decimal (FAST PATH)
            (PrefixOp::Negate, Type::Decimal) => {
                let val = self.unbox_decimal(right_val);
                let result = self.builder.build_float_neg(val, "fneg").unwrap();
                Ok(self.box_decimal(result))
            }

            // Logical NOT on boolean (FAST PATH)
            (PrefixOp::Not, Type::Bool) => {
                // Unbox bool: (value >> 3) & 1
                let val = right_val.into_int_value();
                let shifted = self
                    .builder
                    .build_right_shift(
                        val,
                        self.context.i64_type().const_int(3, false),
                        false,
                        "shift",
                    )
                    .unwrap();
                let bool_val = self
                    .builder
                    .build_and(shifted, self.context.i64_type().const_int(1, false), "mask")
                    .unwrap();

                // XOR with 1 to flip the bit
                let flipped = self
                    .builder
                    .build_xor(bool_val, self.context.i64_type().const_int(1, false), "not")
                    .unwrap();

                // Re-box as boolean
                let shifted_back = self
                    .builder
                    .build_left_shift(
                        flipped,
                        self.context.i64_type().const_int(3, false),
                        "shift_back",
                    )
                    .unwrap();
                let tagged = self
                    .builder
                    .build_or(
                        shifted_back,
                        self.context.i64_type().const_int(0b011, false),
                        "tag",
                    )
                    .unwrap();
                Ok(tagged.into())
            }

            // Unknown types → runtime fallback
            _ => {
                let rt_fn = match op {
                    PrefixOp::Negate => self.get_or_declare_rt_negate(),
                    PrefixOp::Not => self.get_or_declare_rt_not(),
                };

                let call_result = self
                    .builder
                    .build_call(rt_fn, &[right_val.into()], "rt_prefix")
                    .unwrap();

                Ok(call_result.try_as_basic_value().left().unwrap())
            }
        }
    }

    /// Compile a binary operation with type specialization
    fn compile_binary(
        &mut self,
        left: &Expr,
        op: &InfixOp,
        right: &Expr,
        _result_ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Pipeline operator: x |> f transforms to f(x)
        if *op == InfixOp::Pipeline {
            return self.compile_pipeline(left, right);
        }

        // Short-circuit And: a && b
        // If a is falsy, return a. Otherwise evaluate and return b.
        if *op == InfixOp::And {
            return self.compile_short_circuit_and(left, right);
        }

        // Short-circuit Or: a || b
        // If a is truthy, return a. Otherwise evaluate and return b.
        if *op == InfixOp::Or {
            return self.compile_short_circuit_or(left, right);
        }

        // For now, infer types of sub-expressions based on the structure
        // In a full implementation, these would come from the type inference pass
        let left_ty = self.infer_expr_type(left);
        let right_ty = self.infer_expr_type(right);

        let left_typed = TypedExpr {
            expr: left.clone(),
            ty: left_ty.clone(),
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };

        let right_typed = TypedExpr {
            expr: right.clone(),
            ty: right_ty.clone(),
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };

        let left_val = self.compile_expr(&left_typed)?;
        let right_val = self.compile_expr(&right_typed)?;

        // Type-specialized code generation
        match (&left_ty, op, &right_ty) {
            // Int + Int → native add (FAST PATH)
            (Type::Int, InfixOp::Add, Type::Int) => {
                let l = self.unbox_int(left_val);
                let r = self.unbox_int(right_val);
                let result = self.builder.build_int_add(l, r, "add").unwrap();
                Ok(self.box_int(result))
            }

            // Int * Int → native mul (FAST PATH)
            (Type::Int, InfixOp::Multiply, Type::Int) => {
                let l = self.unbox_int(left_val);
                let r = self.unbox_int(right_val);
                let result = self.builder.build_int_mul(l, r, "mul").unwrap();
                Ok(self.box_int(result))
            }

            // Int - Int → native sub (FAST PATH)
            (Type::Int, InfixOp::Subtract, Type::Int) => {
                let l = self.unbox_int(left_val);
                let r = self.unbox_int(right_val);
                let result = self.builder.build_int_sub(l, r, "sub").unwrap();
                Ok(self.box_int(result))
            }

            // Int < Int → native comparison (FAST PATH)
            (Type::Int, InfixOp::LessThan, Type::Int) => {
                let l = self.unbox_int(left_val);
                let r = self.unbox_int(right_val);
                let cmp = self
                    .builder
                    .build_int_compare(IntPredicate::SLT, l, r, "lt")
                    .unwrap();
                Ok(self.box_bool(cmp))
            }

            // Decimal + Decimal → native fadd (FAST PATH)
            (Type::Decimal, InfixOp::Add, Type::Decimal) => {
                let l = self.unbox_decimal(left_val);
                let r = self.unbox_decimal(right_val);
                let result = self.builder.build_float_add(l, r, "fadd").unwrap();
                Ok(self.box_decimal(result))
            }

            // Decimal - Decimal → native fsub (FAST PATH)
            (Type::Decimal, InfixOp::Subtract, Type::Decimal) => {
                let l = self.unbox_decimal(left_val);
                let r = self.unbox_decimal(right_val);
                let result = self.builder.build_float_sub(l, r, "fsub").unwrap();
                Ok(self.box_decimal(result))
            }

            // Decimal * Decimal → native fmul (FAST PATH)
            (Type::Decimal, InfixOp::Multiply, Type::Decimal) => {
                let l = self.unbox_decimal(left_val);
                let r = self.unbox_decimal(right_val);
                let result = self.builder.build_float_mul(l, r, "fmul").unwrap();
                Ok(self.box_decimal(result))
            }

            // Decimal / Decimal → native fdiv (FAST PATH)
            (Type::Decimal, InfixOp::Divide, Type::Decimal) => {
                let l = self.unbox_decimal(left_val);
                let r = self.unbox_decimal(right_val);
                let result = self.builder.build_float_div(l, r, "fdiv").unwrap();
                Ok(self.box_decimal(result))
            }

            // Decimal < Decimal → native comparison (FAST PATH)
            (Type::Decimal, InfixOp::LessThan, Type::Decimal) => {
                let l = self.unbox_decimal(left_val);
                let r = self.unbox_decimal(right_val);
                let cmp = self
                    .builder
                    .build_float_compare(inkwell::FloatPredicate::OLT, l, r, "flt")
                    .unwrap();
                Ok(self.box_bool(cmp))
            }

            // Unknown types → runtime dispatch (SLOW PATH)
            _ => {
                // Call runtime function for dynamic dispatch
                let rt_fn = match op {
                    InfixOp::Add => self.get_or_declare_rt_add(),
                    InfixOp::Subtract => self.get_or_declare_rt_sub(),
                    InfixOp::Multiply => self.get_or_declare_rt_mul(),
                    InfixOp::Divide => self.get_or_declare_rt_div(),
                    InfixOp::Modulo => self.get_or_declare_rt_mod(),
                    InfixOp::Equal => self.get_or_declare_rt_eq(),
                    InfixOp::NotEqual => self.get_or_declare_rt_ne(),
                    InfixOp::LessThan => self.get_or_declare_rt_lt(),
                    InfixOp::LessThanOrEqual => self.get_or_declare_rt_le(),
                    InfixOp::GreaterThan => self.get_or_declare_rt_gt(),
                    InfixOp::GreaterThanOrEqual => self.get_or_declare_rt_ge(),
                    InfixOp::Composition => self.get_or_declare_rt_compose(),
                    _ => {
                        return Err(CompileError::UnsupportedExpression(format!(
                            "Binary operation {:?} not yet supported in runtime fallback",
                            op
                        )))
                    }
                };

                let call_result = self
                    .builder
                    .build_call(rt_fn, &[left_val.into(), right_val.into()], "rt_binop")
                    .unwrap();

                Ok(call_result.try_as_basic_value().left().unwrap())
            }
        }
    }

    /// Compile a pipeline operation: x |> f transforms to f(x)
    ///
    /// Per LANG.txt §4.7, the pipeline operator threads values through function calls.
    /// If the RHS is a call expression, the piped value is appended as the last argument:
    ///   x |> f(a, b)  →  f(a, b, x)
    /// Otherwise it is a simple call:
    ///   x |> f  →  f(x)
    fn compile_pipeline(
        &mut self,
        value: &Expr,
        function: &Expr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // If function is already a Call expression, append the piped value
        if let Expr::Call {
            function: inner_fn,
            args,
        } = function
        {
            let mut new_args = args.clone();
            new_args.push(value.clone());
            return self.compile_call(inner_fn, &new_args);
        }

        // Otherwise, x |> f transforms to f(x)
        self.compile_call(function, std::slice::from_ref(value))
    }

    /// Compile short-circuit AND: a && b
    /// If a is falsy, return false without evaluating b.
    /// Otherwise, evaluate b and return its truthiness as a boolean.
    fn compile_short_circuit_and(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Get the current function
        let function = self
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();

        // Create basic blocks for the short-circuit evaluation
        let eval_right_bb = self.context.append_basic_block(function, "and_eval_right");
        let merge_bb = self.context.append_basic_block(function, "and_merge");

        // Compile left operand
        let left_ty = self.infer_expr_type(left);
        let left_typed = TypedExpr {
            expr: left.clone(),
            ty: left_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let left_val = self.compile_expr(&left_typed)?;

        // Test truthiness of left value using rt_is_truthy
        let rt_is_truthy = self.get_or_declare_rt_is_truthy();
        let is_truthy = self
            .builder
            .build_call(rt_is_truthy, &[left_val.into()], "left_truthy")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap();

        // Convert i64 result to i1 for conditional branch
        let i1_truthy = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                is_truthy.into_int_value(),
                self.context.i64_type().const_zero(),
                "truthy_bool",
            )
            .unwrap();

        // Save the block where we evaluated left
        let left_bb = self.builder.get_insert_block().unwrap();

        // Branch: if truthy, evaluate right; otherwise skip to merge
        self.builder
            .build_conditional_branch(i1_truthy, eval_right_bb, merge_bb)
            .unwrap();

        // Evaluate right operand
        self.builder.position_at_end(eval_right_bb);
        let right_ty = self.infer_expr_type(right);
        let right_typed = TypedExpr {
            expr: right.clone(),
            ty: right_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let right_val = self.compile_expr(&right_typed)?;

        // Convert right value truthiness to boolean Value
        let right_truthy = self
            .builder
            .build_call(rt_is_truthy, &[right_val.into()], "right_truthy")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap();
        let right_bool = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                right_truthy.into_int_value(),
                self.context.i64_type().const_zero(),
                "right_truthy_bool",
            )
            .unwrap();
        let right_boxed = self.box_bool(right_bool);
        let right_bb = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge_bb).unwrap();

        // Merge block: phi node selects between false (if short-circuited) and right truthiness
        self.builder.position_at_end(merge_bb);
        let false_val = self.compile_boolean(false);
        let phi = self
            .builder
            .build_phi(self.context.i64_type(), "and_result")
            .unwrap();
        phi.add_incoming(&[(&false_val, left_bb), (&right_boxed, right_bb)]);

        Ok(phi.as_basic_value())
    }

    /// Compile short-circuit OR: a || b
    /// If a is truthy, return true without evaluating b.
    /// Otherwise, evaluate b and return its truthiness as a boolean.
    fn compile_short_circuit_or(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Get the current function
        let function = self
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();

        // Create basic blocks for the short-circuit evaluation
        let eval_right_bb = self.context.append_basic_block(function, "or_eval_right");
        let merge_bb = self.context.append_basic_block(function, "or_merge");

        // Compile left operand
        let left_ty = self.infer_expr_type(left);
        let left_typed = TypedExpr {
            expr: left.clone(),
            ty: left_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let left_val = self.compile_expr(&left_typed)?;

        // Test truthiness of left value using rt_is_truthy
        let rt_is_truthy = self.get_or_declare_rt_is_truthy();
        let is_truthy = self
            .builder
            .build_call(rt_is_truthy, &[left_val.into()], "left_truthy")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap();

        // Convert i64 result to i1 for conditional branch
        let i1_truthy = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                is_truthy.into_int_value(),
                self.context.i64_type().const_zero(),
                "truthy_bool",
            )
            .unwrap();

        // Save the block where we evaluated left
        let left_bb = self.builder.get_insert_block().unwrap();

        // Branch: if truthy, skip to merge; otherwise evaluate right
        self.builder
            .build_conditional_branch(i1_truthy, merge_bb, eval_right_bb)
            .unwrap();

        // Evaluate right operand
        self.builder.position_at_end(eval_right_bb);
        let right_ty = self.infer_expr_type(right);
        let right_typed = TypedExpr {
            expr: right.clone(),
            ty: right_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let right_val = self.compile_expr(&right_typed)?;

        // Convert right value truthiness to boolean Value
        let right_truthy = self
            .builder
            .build_call(rt_is_truthy, &[right_val.into()], "right_truthy")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap();
        let right_bool = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                right_truthy.into_int_value(),
                self.context.i64_type().const_zero(),
                "right_truthy_bool",
            )
            .unwrap();
        let right_boxed = self.box_bool(right_bool);
        let right_bb = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge_bb).unwrap();

        // Merge block: phi node selects between true (if truthy) and right truthiness
        self.builder.position_at_end(merge_bb);
        let true_val = self.compile_boolean(true);
        let phi = self
            .builder
            .build_phi(self.context.i64_type(), "or_result")
            .unwrap();
        phi.add_incoming(&[(&true_val, left_bb), (&right_boxed, right_bb)]);

        Ok(phi.as_basic_value())
    }

    /// Get or declare the rt_is_truthy runtime function
    fn get_or_declare_rt_is_truthy(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_is_truthy";

        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Declare: extern "C" fn(Value) -> i64 (returns 1 for truthy, 0 for falsy)
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_is_list runtime function
    fn get_or_declare_rt_is_list(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_is_list";

        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Declare: extern "C" fn(Value) -> i64 (returns 1 for list, 0 otherwise)
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_expect_list_len runtime function
    fn get_or_declare_rt_expect_list_len(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_expect_list_len";

        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Declare: extern "C-unwind" fn(Value, Value, Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_is_integer runtime function
    fn get_or_declare_rt_is_integer(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_is_integer";

        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Declare: extern "C" fn(Value) -> i64 (returns 1 for integer, 0 otherwise)
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_add runtime function
    fn get_or_declare_rt_add(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_add")
    }

    /// Get or declare the rt_sub runtime function
    fn get_or_declare_rt_sub(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_sub")
    }

    /// Get or declare the rt_mul runtime function
    fn get_or_declare_rt_mul(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_mul")
    }

    /// Get or declare the rt_div runtime function
    fn get_or_declare_rt_div(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_div")
    }

    /// Get or declare the rt_mod runtime function
    fn get_or_declare_rt_mod(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_mod")
    }

    /// Get or declare the rt_eq runtime function
    fn get_or_declare_rt_eq(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_eq")
    }

    /// Get or declare the rt_ne runtime function
    fn get_or_declare_rt_ne(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_ne")
    }

    /// Get or declare the rt_lt runtime function
    fn get_or_declare_rt_lt(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_lt")
    }

    /// Get or declare the rt_le runtime function
    fn get_or_declare_rt_le(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_le")
    }

    /// Get or declare the rt_gt runtime function
    fn get_or_declare_rt_gt(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_gt")
    }

    /// Get or declare the rt_ge runtime function
    fn get_or_declare_rt_ge(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_ge")
    }

    /// Get or declare the rt_compose runtime function for function composition (>>)
    fn get_or_declare_rt_compose(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_binop("rt_compose")
    }

    /// Helper to get or declare a binary operation runtime function
    /// All have signature: extern "C" fn(Value, Value) -> Value (i64, i64) -> i64
    fn get_or_declare_rt_binop(&self, name: &str) -> inkwell::values::FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function(name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(name, fn_type, None)
    }

    /// Get or declare the rt_negate runtime function
    fn get_or_declare_rt_negate(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_unop("rt_negate")
    }

    /// Get or declare the rt_not runtime function
    fn get_or_declare_rt_not(&self) -> inkwell::values::FunctionValue<'ctx> {
        self.get_or_declare_rt_unop("rt_not")
    }

    /// Helper to get or declare a unary operation runtime function
    /// All have signature: extern "C" fn(Value) -> Value (i64) -> i64
    fn get_or_declare_rt_unop(&self, name: &str) -> inkwell::values::FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function(name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(name, fn_type, None)
    }

    /// Type inference for expressions using the type environment from the inference pass
    ///
    /// This looks up variable types from the type environment, enabling specialized
    /// code generation for expressions involving variables with known types.
    fn infer_expr_type(&self, expr: &Expr) -> Type {
        match expr {
            Expr::Integer(_) => Type::Int,
            Expr::Decimal(_) => Type::Decimal,
            Expr::String(_) => Type::String,
            Expr::Boolean(_) => Type::Bool,
            Expr::Nil => Type::Nil,
            // Look up variable types from the type environment.
            // Avoid specializing mutable bindings because their type can change at runtime.
            Expr::Identifier(name) => {
                if self.mutable_variables.contains(name) {
                    Type::Unknown
                } else {
                    self.type_env.get(name).cloned().unwrap_or(Type::Unknown)
                }
            }
            // For binary operations, infer from operands
            Expr::Infix { left, op, right } => {
                let left_ty = self.infer_expr_type(left);
                let right_ty = self.infer_expr_type(right);
                self.infer_binary_result_type(&left_ty, op, &right_ty)
            }
            // For prefix operations
            Expr::Prefix { op, right } => {
                let right_ty = self.infer_expr_type(right);
                self.infer_prefix_result_type(op, &right_ty)
            }
            // Lists infer element type from first element
            Expr::List(elements) => {
                if elements.is_empty() {
                    Type::List(Box::new(Type::Unknown))
                } else {
                    let elem_ty = self.infer_expr_type(&elements[0]);
                    Type::List(Box::new(elem_ty))
                }
            }
            _ => Type::Unknown,
        }
    }

    /// Infer the result type of a binary operation
    fn infer_binary_result_type(&self, left: &Type, op: &InfixOp, right: &Type) -> Type {
        use InfixOp::*;
        match (left, op, right) {
            // Arithmetic with same types
            (Type::Int, Add | Subtract | Multiply | Divide | Modulo, Type::Int) => Type::Int,
            (Type::Decimal, Add | Subtract | Multiply | Divide, Type::Decimal) => Type::Decimal,
            // Comparisons always return Bool
            (
                _,
                LessThan | LessThanOrEqual | GreaterThan | GreaterThanOrEqual | Equal | NotEqual,
                _,
            ) => Type::Bool,
            // Logical operations always return Bool (truthiness)
            (_, And | Or, _) => Type::Bool,
            // String concatenation
            (Type::String, Add, _) => Type::String,
            // Ranges
            (Type::Int, Range | RangeInclusive, Type::Int) => {
                Type::LazySequence(Box::new(Type::Int))
            }
            _ => Type::Unknown,
        }
    }

    /// Infer the result type of a prefix operation
    fn infer_prefix_result_type(&self, op: &PrefixOp, operand: &Type) -> Type {
        match (op, operand) {
            (PrefixOp::Negate, Type::Int) => Type::Int,
            (PrefixOp::Negate, Type::Decimal) => Type::Decimal,
            (PrefixOp::Not, Type::Bool) => Type::Bool,
            _ => Type::Unknown,
        }
    }

    /// Extract raw i64 from NaN-boxed integer (assumes type is known to be Int)
    fn unbox_int(&self, value: BasicValueEnum<'ctx>) -> inkwell::values::IntValue<'ctx> {
        // Arithmetic right shift by 3 to remove tag bits and restore sign
        let val = value.into_int_value();
        self.builder
            .build_right_shift(
                val,
                self.context.i64_type().const_int(3, false),
                true,
                "unbox_int",
            )
            .unwrap()
    }

    /// Box raw i64 into NaN-boxed integer
    fn box_int(&self, value: inkwell::values::IntValue<'ctx>) -> BasicValueEnum<'ctx> {
        // Shift left by 3 and OR with tag 0b001
        let shifted = self
            .builder
            .build_left_shift(value, self.context.i64_type().const_int(3, false), "shift")
            .unwrap();
        let tagged = self
            .builder
            .build_or(
                shifted,
                self.context.i64_type().const_int(0b001, false),
                "tag",
            )
            .unwrap();
        tagged.into()
    }

    /// Extract raw f64 from a boxed decimal Value (bitcast i64 -> f64)
    fn unbox_decimal(&self, value: BasicValueEnum<'ctx>) -> inkwell::values::FloatValue<'ctx> {
        let casted = self
            .builder
            .build_bit_cast(value.into_int_value(), self.context.f64_type(), "unbox_dec")
            .unwrap();
        casted.into_float_value()
    }

    /// Box raw f64 into a decimal Value (bitcast f64 -> i64)
    fn box_decimal(&self, value: inkwell::values::FloatValue<'ctx>) -> BasicValueEnum<'ctx> {
        let casted = self
            .builder
            .build_bit_cast(value, self.context.i64_type(), "box_dec")
            .unwrap();
        casted.into()
    }

    /// Box boolean into NaN-boxed value
    fn box_bool(&self, value: inkwell::values::IntValue<'ctx>) -> BasicValueEnum<'ctx> {
        // Extend i1 to i64, shift to bit 3, OR with tag 0b011
        let extended = self
            .builder
            .build_int_z_extend(value, self.context.i64_type(), "ext")
            .unwrap();
        let shifted = self
            .builder
            .build_left_shift(
                extended,
                self.context.i64_type().const_int(3, false),
                "shift",
            )
            .unwrap();
        let tagged = self
            .builder
            .build_or(
                shifted,
                self.context.i64_type().const_int(0b011, false),
                "tag",
            )
            .unwrap();
        tagged.into()
    }

    /// Compile a list literal
    fn compile_list(&mut self, elements: &[Expr]) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Check if any elements are spread expressions
        let has_spread = elements.iter().any(|e| matches!(e, Expr::Spread(_)));

        if elements.is_empty() {
            // Empty list: call rt_list_new()
            let rt_list_new = self.get_or_declare_rt_list_new();
            let call_result = self
                .builder
                .build_call(rt_list_new, &[], "empty_list")
                .unwrap();
            Ok(call_result.try_as_basic_value().left().unwrap())
        } else if has_spread {
            // List with spread elements: build incrementally
            // Start with empty list
            let rt_list_new = self.get_or_declare_rt_list_new();
            let mut result = self
                .builder
                .build_call(rt_list_new, &[], "spread_list")
                .unwrap()
                .try_as_basic_value()
                .left()
                .unwrap();

            for element in elements {
                match element {
                    Expr::Spread(inner) => {
                        // Compile the spread expression and concat to list
                        let elem_ty = self.infer_expr_type(inner);
                        let typed_elem = TypedExpr {
                            expr: (**inner).clone(),
                            ty: elem_ty,
                            span: crate::lexer::token::Span::new(
                                crate::lexer::token::Position::new(0, 0),
                                crate::lexer::token::Position::new(0, 0),
                            ),
                        };
                        let spread_val = self.compile_expr(&typed_elem)?;
                        let rt_list_concat = self.get_or_declare_rt_list_concat();
                        result = self
                            .builder
                            .build_call(
                                rt_list_concat,
                                &[result.into(), spread_val.into()],
                                "spread_concat",
                            )
                            .unwrap()
                            .try_as_basic_value()
                            .left()
                            .unwrap();
                    }
                    _ => {
                        // Regular element: push to list
                        let elem_ty = self.infer_expr_type(element);
                        let typed_elem = TypedExpr {
                            expr: element.clone(),
                            ty: elem_ty,
                            span: crate::lexer::token::Span::new(
                                crate::lexer::token::Position::new(0, 0),
                                crate::lexer::token::Position::new(0, 0),
                            ),
                        };
                        let elem_val = self.compile_expr(&typed_elem)?;
                        let rt_list_push = self.get_or_declare_rt_list_push();
                        result = self
                            .builder
                            .build_call(
                                rt_list_push,
                                &[result.into(), elem_val.into()],
                                "list_push",
                            )
                            .unwrap()
                            .try_as_basic_value()
                            .left()
                            .unwrap();
                    }
                }
            }

            Ok(result)
        } else {
            // Non-empty list without spread: compile elements and call rt_list_from_values(values, count)
            let mut compiled_elements = Vec::new();
            for element in elements {
                // Infer type for the element
                let elem_ty = self.infer_expr_type(element);
                let typed_elem = TypedExpr {
                    expr: element.clone(),
                    ty: elem_ty,
                    span: crate::lexer::token::Span::new(
                        crate::lexer::token::Position::new(0, 0),
                        crate::lexer::token::Position::new(0, 0),
                    ),
                };
                let compiled = self.compile_expr(&typed_elem)?;
                compiled_elements.push(compiled);
            }

            // Allocate an array on the stack to hold the elements
            let i64_type = self.context.i64_type();
            let array_type = i64_type.array_type(elements.len() as u32);
            let array_alloca = self
                .builder
                .build_alloca(array_type, "list_elements")
                .unwrap();

            // Store each element in the array
            for (i, elem) in compiled_elements.iter().enumerate() {
                let index = self.context.i64_type().const_int(i as u64, false);
                let elem_ptr = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            array_type,
                            array_alloca,
                            &[self.context.i64_type().const_zero(), index],
                            &format!("elem_ptr_{}", i),
                        )
                        .unwrap()
                };
                self.builder.build_store(elem_ptr, *elem).unwrap();
            }

            // Cast array pointer to *const Value (i64*)
            let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
            let values_ptr = self
                .builder
                .build_pointer_cast(array_alloca, ptr_type, "values_ptr")
                .unwrap();

            // Call rt_list_from_values(values, count)
            let rt_list_from_values = self.get_or_declare_rt_list_from_values();
            let count = self
                .context
                .i64_type()
                .const_int(elements.len() as u64, false);
            let call_result = self
                .builder
                .build_call(
                    rt_list_from_values,
                    &[values_ptr.into(), count.into()],
                    "list",
                )
                .unwrap();

            Ok(call_result.try_as_basic_value().left().unwrap())
        }
    }

    /// Get or declare the rt_list_new runtime function
    fn get_or_declare_rt_list_new(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_list_new";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Declare: extern "C" fn() -> Value (i64)
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_list_from_values runtime function
    fn get_or_declare_rt_list_from_values(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_list_from_values";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Declare: extern "C" fn(values: *const Value, count: usize) -> Value (i64)
        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[ptr_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_list_push runtime function (appends single element)
    fn get_or_declare_rt_list_push(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_list_push";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Declare: extern "C" fn(list: Value, elem: Value) -> Value (i64)
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_list_concat runtime function (concatenates two lists)
    fn get_or_declare_rt_list_concat(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_list_concat";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Declare: extern "C" fn(list1: Value, list2: Value) -> Value (i64)
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Compile a set literal
    fn compile_set(&mut self, elements: &[Expr]) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if elements.is_empty() {
            // Empty set: call rt_set_new()
            let rt_set_new = self.get_or_declare_rt_set_new();
            let call_result = self
                .builder
                .build_call(rt_set_new, &[], "empty_set")
                .unwrap();
            Ok(call_result.try_as_basic_value().left().unwrap())
        } else {
            // Non-empty set: compile elements and call rt_set_from_values(values, count)
            let mut compiled_elements = Vec::new();
            for element in elements {
                let elem_ty = self.infer_expr_type(element);
                let typed_elem = TypedExpr {
                    expr: element.clone(),
                    ty: elem_ty,
                    span: crate::lexer::token::Span::new(
                        crate::lexer::token::Position::new(0, 0),
                        crate::lexer::token::Position::new(0, 0),
                    ),
                };
                let compiled = self.compile_expr(&typed_elem)?;
                compiled_elements.push(compiled);
            }

            // Allocate an array on the stack
            let i64_type = self.context.i64_type();
            let array_type = i64_type.array_type(elements.len() as u32);
            let array_alloca = self
                .builder
                .build_alloca(array_type, "set_elements")
                .unwrap();

            // Store each element in the array
            for (i, elem) in compiled_elements.iter().enumerate() {
                let index = self.context.i64_type().const_int(i as u64, false);
                let elem_ptr = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            array_type,
                            array_alloca,
                            &[self.context.i64_type().const_zero(), index],
                            &format!("elem_ptr_{}", i),
                        )
                        .unwrap()
                };
                self.builder.build_store(elem_ptr, *elem).unwrap();
            }

            // Cast array pointer to *const Value
            let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
            let values_ptr = self
                .builder
                .build_pointer_cast(array_alloca, ptr_type, "values_ptr")
                .unwrap();

            // Call rt_set_from_values(values, count)
            let rt_set_from_values = self.get_or_declare_rt_set_from_values();
            let count = self
                .context
                .i64_type()
                .const_int(elements.len() as u64, false);
            let call_result = self
                .builder
                .build_call(
                    rt_set_from_values,
                    &[values_ptr.into(), count.into()],
                    "set",
                )
                .unwrap();

            Ok(call_result.try_as_basic_value().left().unwrap())
        }
    }

    /// Get or declare the rt_set_new runtime function
    fn get_or_declare_rt_set_new(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_set_new";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_set_from_values runtime function
    fn get_or_declare_rt_set_from_values(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_set_from_values";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[ptr_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Compile a dict literal
    fn compile_dict(
        &mut self,
        entries: &[(Expr, Expr)],
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if entries.is_empty() {
            // Empty dict: call rt_dict_new()
            let rt_dict_new = self.get_or_declare_rt_dict_new();
            let call_result = self
                .builder
                .build_call(rt_dict_new, &[], "empty_dict")
                .unwrap();
            Ok(call_result.try_as_basic_value().left().unwrap())
        } else {
            // Non-empty dict: compile keys and values separately
            let mut compiled_keys = Vec::new();
            let mut compiled_values = Vec::new();

            for (key, value) in entries {
                // Compile key
                let key_ty = self.infer_expr_type(key);
                let typed_key = TypedExpr {
                    expr: key.clone(),
                    ty: key_ty,
                    span: crate::lexer::token::Span::new(
                        crate::lexer::token::Position::new(0, 0),
                        crate::lexer::token::Position::new(0, 0),
                    ),
                };
                let compiled_key = self.compile_expr(&typed_key)?;
                compiled_keys.push(compiled_key);

                // Compile value
                let value_ty = self.infer_expr_type(value);
                let typed_value = TypedExpr {
                    expr: value.clone(),
                    ty: value_ty,
                    span: crate::lexer::token::Span::new(
                        crate::lexer::token::Position::new(0, 0),
                        crate::lexer::token::Position::new(0, 0),
                    ),
                };
                let compiled_value = self.compile_expr(&typed_value)?;
                compiled_values.push(compiled_value);
            }

            // Allocate arrays on the stack for keys and values
            let i64_type = self.context.i64_type();
            let array_type = i64_type.array_type(entries.len() as u32);

            let keys_alloca = self.builder.build_alloca(array_type, "dict_keys").unwrap();
            let values_alloca = self
                .builder
                .build_alloca(array_type, "dict_values")
                .unwrap();

            // Store keys and values
            for (i, (key, value)) in compiled_keys.iter().zip(compiled_values.iter()).enumerate() {
                let index = self.context.i64_type().const_int(i as u64, false);

                // Store key
                let key_ptr = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            array_type,
                            keys_alloca,
                            &[self.context.i64_type().const_zero(), index],
                            &format!("key_ptr_{}", i),
                        )
                        .unwrap()
                };
                self.builder.build_store(key_ptr, *key).unwrap();

                // Store value
                let value_ptr = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            array_type,
                            values_alloca,
                            &[self.context.i64_type().const_zero(), index],
                            &format!("value_ptr_{}", i),
                        )
                        .unwrap()
                };
                self.builder.build_store(value_ptr, *value).unwrap();
            }

            // Cast pointers
            let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
            let keys_ptr = self
                .builder
                .build_pointer_cast(keys_alloca, ptr_type, "keys_ptr")
                .unwrap();
            let values_ptr = self
                .builder
                .build_pointer_cast(values_alloca, ptr_type, "values_ptr")
                .unwrap();

            // Call rt_dict_from_entries(keys, values, count)
            let rt_dict_from_entries = self.get_or_declare_rt_dict_from_entries();
            let count = self
                .context
                .i64_type()
                .const_int(entries.len() as u64, false);
            let call_result = self
                .builder
                .build_call(
                    rt_dict_from_entries,
                    &[keys_ptr.into(), values_ptr.into(), count.into()],
                    "dict",
                )
                .unwrap();

            Ok(call_result.try_as_basic_value().left().unwrap())
        }
    }

    /// Get or declare the rt_dict_new runtime function
    fn get_or_declare_rt_dict_new(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_dict_new";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_dict_from_entries runtime function
    fn get_or_declare_rt_dict_from_entries(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_dict_from_entries";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[ptr_type.into(), ptr_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Compile a range expression
    fn compile_range(
        &mut self,
        start: &Expr,
        end: Option<&Expr>,
        inclusive: bool,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Compile start expression
        let start_ty = self.infer_expr_type(start);
        let start_typed = TypedExpr {
            expr: start.clone(),
            ty: start_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let start_val = self.compile_expr(&start_typed)?;

        // Compile end expression if present
        let end_val = if let Some(end_expr) = end {
            let end_ty = self.infer_expr_type(end_expr);
            let end_typed = TypedExpr {
                expr: end_expr.clone(),
                ty: end_ty,
                span: crate::lexer::token::Span::new(
                    crate::lexer::token::Position::new(0, 0),
                    crate::lexer::token::Position::new(0, 0),
                ),
            };
            self.compile_expr(&end_typed)?
        } else {
            // No end means unbounded range - use a sentinel value (0)
            self.context.i64_type().const_zero().into()
        };

        // Determine which runtime function to call based on range type
        let rt_fn = if end.is_none() {
            // Unbounded range: rt_range_unbounded(start)
            self.get_or_declare_rt_range_unbounded()
        } else if inclusive {
            // Inclusive range: rt_range_inclusive(start, end)
            self.get_or_declare_rt_range_inclusive()
        } else {
            // Exclusive range: rt_range_exclusive(start, end)
            self.get_or_declare_rt_range_exclusive()
        };

        // Call the appropriate runtime function
        let args: &[_] = if end.is_none() {
            &[start_val.into()]
        } else {
            &[start_val.into(), end_val.into()]
        };

        let call_result = self.builder.build_call(rt_fn, args, "range").unwrap();
        Ok(call_result.try_as_basic_value().left().unwrap())
    }

    /// Get or declare the rt_range_inclusive runtime function
    fn get_or_declare_rt_range_inclusive(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_range_inclusive";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_range_exclusive runtime function
    fn get_or_declare_rt_range_exclusive(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_range_exclusive";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_range_unbounded runtime function
    fn get_or_declare_rt_range_unbounded(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_range_unbounded";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Compile an index expression (collection[index])
    fn compile_index(
        &mut self,
        collection: &Expr,
        index: &Expr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Compile collection expression
        let collection_ty = self.infer_expr_type(collection);
        let collection_typed = TypedExpr {
            expr: collection.clone(),
            ty: collection_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let collection_val = self.compile_expr(&collection_typed)?;

        // Compile index expression
        let index_ty = self.infer_expr_type(index);
        let index_typed = TypedExpr {
            expr: index.clone(),
            ty: index_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let index_val = self.compile_expr(&index_typed)?;

        // Call rt_get(index, collection)
        let rt_get = self.get_or_declare_rt_get();
        let call_result = self
            .builder
            .build_call(rt_get, &[index_val.into(), collection_val.into()], "index")
            .unwrap();

        Ok(call_result.try_as_basic_value().left().unwrap())
    }

    /// Compile an if expression with optional else branch
    fn compile_if(
        &mut self,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Get the current function (required for creating basic blocks)
        let current_fn = self
            .builder
            .get_insert_block()
            .and_then(|bb| bb.get_parent())
            .ok_or_else(|| {
                CompileError::UnsupportedExpression(
                    "if expression requires a function context".to_string(),
                )
            })?;

        // Compile the condition
        let cond_ty = self.infer_expr_type(condition);
        let cond_typed = TypedExpr {
            expr: condition.clone(),
            ty: cond_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let cond_val = self.compile_expr(&cond_typed)?;

        // Call rt_is_truthy to handle all value types (not just booleans)
        let rt_is_truthy = self.get_or_declare_rt_is_truthy();
        let is_truthy = self
            .builder
            .build_call(rt_is_truthy, &[cond_val.into()], "is_truthy")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap();

        // Convert i64 result to i1 for conditional branch
        let cond_bool = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                is_truthy.into_int_value(),
                self.context.i64_type().const_zero(),
                "truthy_bool",
            )
            .unwrap();

        // Create basic blocks for then, else, and merge
        let then_bb = self.context.append_basic_block(current_fn, "then");
        let else_bb = self.context.append_basic_block(current_fn, "else");
        let merge_bb = self.context.append_basic_block(current_fn, "merge");

        // Build conditional branch
        self.builder
            .build_conditional_branch(cond_bool, then_bb, else_bb)
            .unwrap();

        // Compile then branch
        self.builder.position_at_end(then_bb);
        let then_ty = self.infer_expr_type(then_branch);
        let then_typed = TypedExpr {
            expr: then_branch.clone(),
            ty: then_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let then_val = self.compile_expr(&then_typed)?;
        self.builder.build_unconditional_branch(merge_bb).unwrap();
        let then_end_bb = self.builder.get_insert_block().unwrap();

        // Compile else branch (or use nil if no else)
        self.builder.position_at_end(else_bb);
        let else_val = if let Some(else_expr) = else_branch {
            let else_ty = self.infer_expr_type(else_expr);
            let else_typed = TypedExpr {
                expr: else_expr.clone(),
                ty: else_ty,
                span: crate::lexer::token::Span::new(
                    crate::lexer::token::Position::new(0, 0),
                    crate::lexer::token::Position::new(0, 0),
                ),
            };
            self.compile_expr(&else_typed)?
        } else {
            self.compile_nil()
        };
        self.builder.build_unconditional_branch(merge_bb).unwrap();
        let else_end_bb = self.builder.get_insert_block().unwrap();

        // Merge block with phi node
        self.builder.position_at_end(merge_bb);
        let phi = self
            .builder
            .build_phi(self.context.i64_type(), "if_result")
            .unwrap();
        phi.add_incoming(&[(&then_val, then_end_bb), (&else_val, else_end_bb)]);

        Ok(phi.as_basic_value())
    }

    /// Compile an if-let expression
    ///
    /// `if let pattern = value { then } else { else }` evaluates value,
    /// checks if it's truthy, and if so binds the pattern and executes then.
    fn compile_if_let(
        &mut self,
        pattern: &Pattern,
        value: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Get the current function
        let current_fn = self
            .builder
            .get_insert_block()
            .and_then(|bb| bb.get_parent())
            .ok_or_else(|| {
                CompileError::UnsupportedExpression(
                    "if-let expression requires a function context".to_string(),
                )
            })?;

        // Compile the value expression
        let value_ty = self.infer_expr_type(value);
        let value_typed = TypedExpr {
            expr: value.clone(),
            ty: value_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let value_val = self.compile_expr(&value_typed)?;

        // Call rt_is_truthy to check if value is truthy
        let rt_is_truthy = self.get_or_declare_rt_is_truthy();
        let is_truthy = self
            .builder
            .build_call(rt_is_truthy, &[value_val.into()], "is_truthy")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap();

        // Convert to bool
        let cond_bool = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                is_truthy.into_int_value(),
                self.context.i64_type().const_zero(),
                "truthy_bool",
            )
            .unwrap();

        // Create basic blocks
        let then_bb = self.context.append_basic_block(current_fn, "if_let_then");
        let else_bb = self.context.append_basic_block(current_fn, "if_let_else");
        let merge_bb = self.context.append_basic_block(current_fn, "if_let_merge");

        // Branch based on truthiness
        self.builder
            .build_conditional_branch(cond_bool, then_bb, else_bb)
            .unwrap();

        // Compile then branch (with pattern binding)
        self.builder.position_at_end(then_bb);

        // Save variables for scoping
        let saved_variables = self.variables.clone();
        let saved_mutable_vars = self.mutable_variables.clone();

        // Bind pattern variables to the value
        self.set_pattern_mutability(pattern, false);
        self.bind_pattern_variables(pattern, value_val)?;

        let then_ty = self.infer_expr_type(then_branch);
        let then_typed = TypedExpr {
            expr: then_branch.clone(),
            ty: then_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let then_val = self.compile_expr(&then_typed)?;

        // Restore variables
        self.variables = saved_variables;
        self.mutable_variables = saved_mutable_vars;

        self.builder.build_unconditional_branch(merge_bb).unwrap();
        let then_end_bb = self.builder.get_insert_block().unwrap();

        // Compile else branch (or nil)
        self.builder.position_at_end(else_bb);
        let else_val = if let Some(else_expr) = else_branch {
            let else_ty = self.infer_expr_type(else_expr);
            let else_typed = TypedExpr {
                expr: else_expr.clone(),
                ty: else_ty,
                span: crate::lexer::token::Span::new(
                    crate::lexer::token::Position::new(0, 0),
                    crate::lexer::token::Position::new(0, 0),
                ),
            };
            self.compile_expr(&else_typed)?
        } else {
            self.compile_nil()
        };
        self.builder.build_unconditional_branch(merge_bb).unwrap();
        let else_end_bb = self.builder.get_insert_block().unwrap();

        // Merge with phi
        self.builder.position_at_end(merge_bb);
        let phi = self
            .builder
            .build_phi(self.context.i64_type(), "if_let_result")
            .unwrap();
        phi.add_incoming(&[(&then_val, then_end_bb), (&else_val, else_end_bb)]);

        Ok(phi.as_basic_value())
    }

    /// Compile a block of statements
    fn compile_block(&mut self, stmts: &[Stmt]) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if stmts.is_empty() {
            // Empty block returns nil
            return Ok(self.compile_nil());
        }

        // Save the current cell_variables set to restore later
        let saved_cell_vars = self.cell_variables.clone();
        // Save the current variables to restore after block (for proper shadowing)
        let saved_variables = self.variables.clone();
        // Save mutable variables for scope restoration
        let saved_mutable_vars = self.mutable_variables.clone();

        // Pre-analyze block to find mutable variables that will be captured by nested closures
        // First, collect all mutable variables that will be declared in this block
        let mut mutable_vars: HashSet<String> = HashSet::new();
        for stmt in stmts {
            if let Stmt::Let {
                mutable: true,
                pattern,
                ..
            } = stmt
            {
                Self::collect_pattern_variables(pattern, &mut mutable_vars);
            }
        }

        // Now analyze the block to find which mutable vars are captured by nested closures
        let bound_vars: HashSet<String> = self.variables.keys().cloned().collect();
        for stmt in stmts {
            match stmt {
                Stmt::Let { value, .. } => {
                    let captures =
                        self.find_mutable_captures_in_expr(value, &mutable_vars, &bound_vars);
                    self.cell_variables.extend(captures);
                }
                Stmt::Expr(expr) | Stmt::Return(expr) | Stmt::Break(expr) => {
                    let captures =
                        self.find_mutable_captures_in_expr(expr, &mutable_vars, &bound_vars);
                    self.cell_variables.extend(captures);
                }
            }
        }

        // Also find self-referencing bindings (e.g., let fib = memoize |n| { fib(...) })
        // These need cell indirection so the closure can access the final value
        let self_refs = Self::find_self_referencing_bindings(stmts, &bound_vars);
        self.cell_variables.extend(self_refs);

        // Find forward references (mutual recursion between functions in this block)
        let forward_refs = Self::find_forward_references(stmts, &bound_vars);
        self.cell_variables.extend(forward_refs);

        let mut last_val = None;

        for (i, stmt) in stmts.iter().enumerate() {
            let is_last = i == stmts.len() - 1;
            match stmt {
                Stmt::Let {
                    mutable,
                    pattern,
                    value,
                } => {
                    // Compile the let statement and get the bound value
                    let bound_val = self.compile_let(pattern, value, *mutable)?;
                    // If this is the last statement, the block returns the bound value
                    if is_last {
                        last_val = Some(bound_val);
                    }
                }
                Stmt::Expr(expr) => {
                    // Expression statements produce a value
                    let expr_ty = self.infer_expr_type(expr);
                    let expr_typed = TypedExpr {
                        expr: expr.clone(),
                        ty: expr_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let val = self.compile_expr(&expr_typed)?;

                    // If this is the last statement, save its value as the block's result
                    if i == stmts.len() - 1 {
                        last_val = Some(val);
                    }
                }
                Stmt::Return(expr) => {
                    if self.function_depth == 0 {
                        return Err(CompileError::UnsupportedStatement(
                            "return outside function".to_string(),
                        ));
                    }
                    // Compile the return value expression
                    let return_ty = self.infer_expr_type(expr);
                    let return_typed = TypedExpr {
                        expr: expr.clone(),
                        ty: return_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let return_val = self.compile_expr(&return_typed)?;

                    // Return from the current function
                    self.builder.build_return(Some(&return_val)).unwrap();

                    // Create a new basic block for any code after return (unreachable)
                    let func = self
                        .builder
                        .get_insert_block()
                        .unwrap()
                        .get_parent()
                        .unwrap();
                    let unreachable_block = self.context.append_basic_block(func, "after_return");
                    self.builder.position_at_end(unreachable_block);
                }
                Stmt::Break(expr) => {
                    // Compile the break value expression
                    let break_ty = self.infer_expr_type(expr);
                    let break_typed = TypedExpr {
                        expr: expr.clone(),
                        ty: break_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let break_val = self.compile_expr(&break_typed)?;

                    // Call rt_break to signal break and store the value
                    let rt_break = self.get_or_declare_rt_break();
                    let result = self
                        .builder
                        .build_call(rt_break, &[break_val.into()], "break_result")
                        .unwrap();

                    // Return from the current function with the break value
                    self.builder
                        .build_return(Some(&result.try_as_basic_value().left().unwrap()))
                        .unwrap();

                    // Create a new basic block for any code after break (unreachable)
                    let func = self
                        .builder
                        .get_insert_block()
                        .unwrap()
                        .get_parent()
                        .unwrap();
                    let unreachable_block = self.context.append_basic_block(func, "after_break");
                    self.builder.position_at_end(unreachable_block);
                }
            }
        }

        // Restore the cell_variables set (local cell vars should not leak out)
        self.cell_variables = saved_cell_vars;
        // Restore the variables to restore proper scoping (inner scope variables go out of scope)
        self.variables = saved_variables;
        // Restore mutable variable bindings
        self.mutable_variables = saved_mutable_vars;

        // Return the last expression value, or nil if the last statement wasn't an expression
        Ok(last_val.unwrap_or_else(|| self.compile_nil()))
    }

    /// Get or declare the rt_get runtime function for indexing
    fn get_or_declare_rt_get(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_get";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // rt_get(index: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_size runtime function
    fn get_or_declare_rt_size(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_size";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    fn get_or_declare_rt_skip(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_skip";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // rt_skip(count: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    fn get_or_declare_rt_take(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_take";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // rt_take(count: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    // ===== Phase 16: Pattern Matching =====

    /// Compile a match expression
    ///
    /// Generates a decision tree of comparisons and branches for each arm.
    /// Each arm is checked in order, and the first matching pattern's body is executed.
    fn compile_match(
        &mut self,
        subject: &Expr,
        arms: &[MatchArm],
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Get the current function
        let current_fn = self
            .builder
            .get_insert_block()
            .and_then(|bb| bb.get_parent())
            .ok_or_else(|| {
                CompileError::UnsupportedExpression(
                    "match expression requires a function context".to_string(),
                )
            })?;

        // Compile the subject expression
        let subject_ty = self.infer_expr_type(subject);
        let subject_typed = TypedExpr {
            expr: subject.clone(),
            ty: subject_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let subject_val = self.compile_expr(&subject_typed)?;

        // Create the merge block where all arms converge
        let merge_bb = self.context.append_basic_block(current_fn, "match_merge");

        // Track incoming values for the phi node
        let mut incoming: Vec<(BasicValueEnum<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)> =
            Vec::new();

        // Create blocks for each arm
        let arm_blocks: Vec<_> = arms
            .iter()
            .enumerate()
            .map(|(i, _)| {
                self.context
                    .append_basic_block(current_fn, &format!("match_arm_{}", i))
            })
            .collect();

        // Create a fallthrough block for when no pattern matches (returns nil)
        let no_match_bb = self
            .context
            .append_basic_block(current_fn, "match_no_match");

        // Generate pattern tests - each test branches to arm body on match, or continues to next test
        // We need to create test blocks for each arm (separate from body blocks)
        let test_blocks: Vec<_> = arms
            .iter()
            .enumerate()
            .map(|(i, _)| {
                self.context
                    .append_basic_block(current_fn, &format!("match_test_{}", i))
            })
            .collect();

        // Branch from current position to first test block
        self.builder
            .build_unconditional_branch(test_blocks[0])
            .unwrap();

        // Generate pattern tests and branches for each arm
        for (i, arm) in arms.iter().enumerate() {
            let arm_bb = arm_blocks[i];
            let next_bb = if i + 1 < test_blocks.len() {
                test_blocks[i + 1]
            } else {
                no_match_bb
            };

            // Position builder at this arm's test block
            self.builder.position_at_end(test_blocks[i]);

            // Build pattern match test and conditional branch
            self.compile_pattern_test(&arm.pattern, subject_val, arm_bb, next_bb, &arm.guard)?;
        }

        // Compile the body for each arm that matches
        for (i, arm) in arms.iter().enumerate() {
            self.builder.position_at_end(arm_blocks[i]);

            // Save current variables for scoping
            let saved_variables = self.variables.clone();
            let saved_mutable_vars = self.mutable_variables.clone();

            // Bind pattern variables (pattern bindings are immutable)
            self.set_pattern_mutability(&arm.pattern, false);
            self.bind_pattern_variables(&arm.pattern, subject_val)?;

            // Compile the body
            let body_ty = self.infer_expr_type(&arm.body);
            let body_typed = TypedExpr {
                expr: arm.body.clone(),
                ty: body_ty,
                span: crate::lexer::token::Span::new(
                    crate::lexer::token::Position::new(0, 0),
                    crate::lexer::token::Position::new(0, 0),
                ),
            };
            let body_val = self.compile_expr(&body_typed)?;

            // Restore variables (pattern bindings go out of scope)
            self.variables = saved_variables;
            self.mutable_variables = saved_mutable_vars;

            // Get current block BEFORE branching (builder position changes after branch)
            let current_bb = self.builder.get_insert_block().unwrap();

            // Branch to merge
            self.builder.build_unconditional_branch(merge_bb).unwrap();
            incoming.push((body_val, current_bb));
        }

        // No match fallthrough - return nil
        self.builder.position_at_end(no_match_bb);
        let nil_val = self.compile_nil();
        self.builder.build_unconditional_branch(merge_bb).unwrap();
        incoming.push((nil_val, no_match_bb));

        // Merge block with phi
        self.builder.position_at_end(merge_bb);
        let phi = self
            .builder
            .build_phi(self.context.i64_type(), "match_result")
            .unwrap();
        for (val, bb) in incoming {
            phi.add_incoming(&[(&val, bb)]);
        }

        Ok(phi.as_basic_value())
    }

    /// Compile a pattern test and branch to the appropriate block
    fn compile_pattern_test(
        &mut self,
        pattern: &Pattern,
        subject: BasicValueEnum<'ctx>,
        match_bb: inkwell::basic_block::BasicBlock<'ctx>,
        no_match_bb: inkwell::basic_block::BasicBlock<'ctx>,
        guard: &Option<Expr>,
    ) -> Result<(), CompileError> {
        match pattern {
            Pattern::Wildcard => {
                // Wildcard always matches
                if let Some(guard_expr) = guard {
                    // Bind pattern variables first (none for wildcard, but still need to check guard)
                    let guard_ty = self.infer_expr_type(guard_expr);
                    let guard_typed = TypedExpr {
                        expr: guard_expr.clone(),
                        ty: guard_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let guard_val = self.compile_expr(&guard_typed)?;
                    let guard_bool = self.value_to_bool(guard_val);
                    self.builder
                        .build_conditional_branch(guard_bool, match_bb, no_match_bb)
                        .unwrap();
                } else {
                    self.builder.build_unconditional_branch(match_bb).unwrap();
                }
            }
            Pattern::Identifier(_) => {
                // Identifier pattern always matches (binds subject to name)
                if let Some(guard_expr) = guard {
                    // Need to bind the identifier first so guard can reference it
                    let saved_variables = self.variables.clone();
                    let saved_mutable_vars = self.mutable_variables.clone();
                    self.set_pattern_mutability(pattern, false);
                    self.bind_pattern_variables(pattern, subject)?;

                    let guard_ty = self.infer_expr_type(guard_expr);
                    let guard_typed = TypedExpr {
                        expr: guard_expr.clone(),
                        ty: guard_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let guard_val = self.compile_expr(&guard_typed)?;
                    let guard_bool = self.value_to_bool(guard_val);

                    // Restore variables (they'll be re-bound in the arm body)
                    self.variables = saved_variables;
                    self.mutable_variables = saved_mutable_vars;

                    self.builder
                        .build_conditional_branch(guard_bool, match_bb, no_match_bb)
                        .unwrap();
                } else {
                    self.builder.build_unconditional_branch(match_bb).unwrap();
                }
            }
            Pattern::Literal(lit) => {
                // Compare subject to literal
                let lit_val = self.compile_literal(lit);
                let rt_eq = self.get_or_declare_rt_eq();
                let eq_result = self
                    .builder
                    .build_call(rt_eq, &[subject.into(), lit_val.into()], "eq_result")
                    .unwrap();
                let eq_val = eq_result.try_as_basic_value().left().unwrap();
                let eq_bool = self.value_to_bool(eq_val);

                if let Some(guard_expr) = guard {
                    // Create a guard test block
                    let current_fn = self
                        .builder
                        .get_insert_block()
                        .unwrap()
                        .get_parent()
                        .unwrap();
                    let guard_bb = self.context.append_basic_block(current_fn, "guard_test");

                    // Branch to guard test if pattern matches, else to no_match
                    self.builder
                        .build_conditional_branch(eq_bool, guard_bb, no_match_bb)
                        .unwrap();

                    // In guard block, test the guard
                    self.builder.position_at_end(guard_bb);
                    let guard_ty = self.infer_expr_type(guard_expr);
                    let guard_typed = TypedExpr {
                        expr: guard_expr.clone(),
                        ty: guard_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let guard_val = self.compile_expr(&guard_typed)?;
                    let guard_bool = self.value_to_bool(guard_val);
                    self.builder
                        .build_conditional_branch(guard_bool, match_bb, no_match_bb)
                        .unwrap();
                } else {
                    self.builder
                        .build_conditional_branch(eq_bool, match_bb, no_match_bb)
                        .unwrap();
                }
            }
            Pattern::Range {
                start,
                end,
                inclusive,
            } => {
                // Only match integer subjects; non-integers fail to match (no error)
                let rt_is_integer = self.get_or_declare_rt_is_integer();
                let is_int = self
                    .builder
                    .build_call(rt_is_integer, &[subject.into()], "range_is_int")
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap();
                let is_int_bool = self
                    .builder
                    .build_int_compare(
                        IntPredicate::NE,
                        is_int.into_int_value(),
                        self.context.i64_type().const_zero(),
                        "range_is_int_bool",
                    )
                    .unwrap();

                // Branch to range check only if integer
                let current_fn = self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_parent()
                    .unwrap();
                let range_check_bb =
                    self.context.append_basic_block(current_fn, "range_check");
                self.builder
                    .build_conditional_branch(is_int_bool, range_check_bb, no_match_bb)
                    .unwrap();
                self.builder.position_at_end(range_check_bb);

                // Check if subject is >= start and (< end or <= end depending on inclusive)
                let start_val = self.compile_integer(*start);
                let subject_int = subject.into_int_value();
                let start_int = start_val.into_int_value();

                // subject >= start
                let ge_start = self
                    .builder
                    .build_int_compare(IntPredicate::SGE, subject_int, start_int, "ge_start")
                    .unwrap();

                let in_range = if let Some(e) = end {
                    let end_val = self.compile_integer(*e);
                    let end_int = end_val.into_int_value();

                    let cmp = if *inclusive {
                        // subject <= end
                        self.builder
                            .build_int_compare(IntPredicate::SLE, subject_int, end_int, "le_end")
                            .unwrap()
                    } else {
                        // subject < end
                        self.builder
                            .build_int_compare(IntPredicate::SLT, subject_int, end_int, "lt_end")
                            .unwrap()
                    };

                    // Combine: subject >= start AND subject </<=end
                    self.builder.build_and(ge_start, cmp, "in_range").unwrap()
                } else {
                    // Unbounded end: just subject >= start
                    ge_start
                };

                if let Some(guard_expr) = guard {
                    let current_fn = self
                        .builder
                        .get_insert_block()
                        .unwrap()
                        .get_parent()
                        .unwrap();
                    let guard_bb = self.context.append_basic_block(current_fn, "guard_test");
                    self.builder
                        .build_conditional_branch(in_range, guard_bb, no_match_bb)
                        .unwrap();

                    self.builder.position_at_end(guard_bb);
                    let guard_ty = self.infer_expr_type(guard_expr);
                    let guard_typed = TypedExpr {
                        expr: guard_expr.clone(),
                        ty: guard_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let guard_val = self.compile_expr(&guard_typed)?;
                    let guard_bool = self.value_to_bool(guard_val);
                    self.builder
                        .build_conditional_branch(guard_bool, match_bb, no_match_bb)
                        .unwrap();
                } else {
                    self.builder
                        .build_conditional_branch(in_range, match_bb, no_match_bb)
                        .unwrap();
                }
            }
            Pattern::List(patterns) => {
                let success_bb =
                    self.compile_list_pattern_match(subject, patterns, no_match_bb, "list_pat")?;
                self.builder.position_at_end(success_bb);

                // All elements matched - check guard if present
                if let Some(guard_expr) = guard {
                    // Bind variables for guard evaluation
                    let saved_variables = self.variables.clone();
                    let saved_mutable_vars = self.mutable_variables.clone();
                    self.set_pattern_mutability(pattern, false);
                    self.bind_pattern_variables(pattern, subject)?;

                    let guard_ty = self.infer_expr_type(guard_expr);
                    let guard_typed = TypedExpr {
                        expr: guard_expr.clone(),
                        ty: guard_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let guard_val = self.compile_expr(&guard_typed)?;
                    let guard_bool = self.value_to_bool(guard_val);

                    self.variables = saved_variables;
                    self.mutable_variables = saved_mutable_vars;
                    self.builder
                        .build_conditional_branch(guard_bool, match_bb, no_match_bb)
                        .unwrap();
                } else {
                    self.builder.build_unconditional_branch(match_bb).unwrap();
                }
            }
            Pattern::RestIdentifier(_) => {
                // Rest pattern can only appear inside a list pattern
                return Err(CompileError::UnsupportedPattern(
                    "Rest pattern (..) can only appear inside list patterns".to_string(),
                ));
            }
        }
        Ok(())
    }

    /// Validate pattern bindings (currently allows all valid patterns including builtin names)
    fn validate_pattern_bindings(&self, pattern: &Pattern) -> Result<(), CompileError> {
        match pattern {
            Pattern::Identifier(_) | Pattern::RestIdentifier(_) => Ok(()),
            Pattern::List(patterns) => {
                for pat in patterns {
                    self.validate_pattern_bindings(pat)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn list_pattern_len_requirements(patterns: &[Pattern]) -> (usize, bool) {
        let mut expected = 0usize;
        let mut has_rest = false;
        for pat in patterns {
            if matches!(pat, Pattern::RestIdentifier(_)) {
                has_rest = true;
            } else {
                expected += 1;
            }
        }
        (expected, has_rest)
    }

    fn emit_list_pattern_check(
        &mut self,
        list_val: BasicValueEnum<'ctx>,
        patterns: &[Pattern],
        name: &str,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let (expected, has_rest) = Self::list_pattern_len_requirements(patterns);
        let rt_expect_list_len = self.get_or_declare_rt_expect_list_len();
        let expected_val = self.compile_integer(expected as i64);
        let has_rest_val = self.compile_integer(if has_rest { 1 } else { 0 });
        let checked = self
            .builder
            .build_call(
                rt_expect_list_len,
                &[list_val.into(), expected_val.into(), has_rest_val.into()],
                name,
            )
            .unwrap();
        Ok(checked.try_as_basic_value().left().unwrap())
    }

    /// Bind pattern variables to the subject value
    fn bind_pattern_variables(
        &mut self,
        pattern: &Pattern,
        subject: BasicValueEnum<'ctx>,
    ) -> Result<(), CompileError> {
        self.validate_pattern_bindings(pattern)?;
        match pattern {
            Pattern::Wildcard => {
                // Nothing to bind
                Ok(())
            }
            Pattern::Identifier(name) => {
                // Bind the subject to this name
                let alloca = self
                    .builder
                    .build_alloca(self.context.i64_type(), name)
                    .unwrap();
                self.builder.build_store(alloca, subject).unwrap();
                self.variables.insert(name.clone(), alloca);
                Ok(())
            }
            Pattern::Literal(_) | Pattern::Range { .. } => {
                // No variables to bind
                Ok(())
            }
            Pattern::List(patterns) => {
                let list_val = self.emit_list_pattern_check(subject, patterns, "list_bind_check")?;
                // Bind variables in list patterns
                // First find the rest pattern position (if any)
                let mut rest_position = None;
                for (i, p) in patterns.iter().enumerate() {
                    if matches!(p, Pattern::RestIdentifier(_)) {
                        rest_position = Some(i);
                        break;
                    }
                }

                // Count patterns after rest
                let patterns_after_rest = if let Some(rest_pos) = rest_position {
                    patterns.len() - rest_pos - 1
                } else {
                    0
                };

                // Get subject's length for computing indices from end
                let rt_size = self.get_or_declare_rt_size();
                let size_result = self
                    .builder
                    .build_call(rt_size, &[list_val.into()], "subject_size")
                    .unwrap();
                let size_val = size_result.try_as_basic_value().left().unwrap();
                let size_int = size_val.into_int_value();
                let actual_len = self
                    .builder
                    .build_right_shift(
                        size_int,
                        self.context.i64_type().const_int(3, false),
                        false,
                        "actual_len",
                    )
                    .unwrap();

                let mut after_rest_offset = 0usize;
                for (i, p) in patterns.iter().enumerate() {
                    let is_after_rest = rest_position.is_some_and(|pos| i > pos);

                    match p {
                        Pattern::Identifier(name) => {
                            // Compute index based on position relative to rest
                            let elem_val = if is_after_rest {
                                // Element after rest: compute index from end
                                let offset_from_end =
                                    (patterns_after_rest - after_rest_offset) as u64;
                                let idx_from_end = self
                                    .builder
                                    .build_int_sub(
                                        actual_len,
                                        self.context.i64_type().const_int(offset_from_end, false),
                                        "idx_from_end",
                                    )
                                    .unwrap();

                                // Convert to tagged integer
                                let tagged_idx = self
                                    .builder
                                    .build_left_shift(
                                        idx_from_end,
                                        self.context.i64_type().const_int(3, false),
                                        "shift_idx",
                                    )
                                    .unwrap();
                                let tagged_idx = self
                                    .builder
                                    .build_or(
                                        tagged_idx,
                                        self.context.i64_type().const_int(0b001, false),
                                        "tag_idx",
                                    )
                                    .unwrap();

                                let rt_get = self.get_or_declare_rt_get();
                                let elem_result = self
                                    .builder
                                    .build_call(
                                        rt_get,
                                        &[tagged_idx.into(), list_val.into()],
                                        &format!("elem_from_end_{}", after_rest_offset),
                                    )
                                    .unwrap();
                                after_rest_offset += 1;
                                elem_result.try_as_basic_value().left().unwrap()
                            } else {
                                // Element before rest (or no rest): use direct index
                                let idx_val = self.compile_integer(i as i64);
                                let rt_get = self.get_or_declare_rt_get();
                                let elem_result = self
                                    .builder
                                    .build_call(
                                        rt_get,
                                        &[idx_val.into(), list_val.into()],
                                        &format!("elem_{}", i),
                                    )
                                    .unwrap();
                                elem_result.try_as_basic_value().left().unwrap()
                            };

                            let alloca = self
                                .builder
                                .build_alloca(self.context.i64_type(), name)
                                .unwrap();
                            self.builder.build_store(alloca, elem_val).unwrap();
                            self.variables.insert(name.clone(), alloca);
                        }
                        Pattern::RestIdentifier(name) => {
                            if name.is_empty() {
                                // Bare rest (..) ignores remaining elements
                                continue;
                            }
                            // Bind the rest of the list to this name
                            // We need to slice from current position (i) to (len - patterns_after_rest)
                            // Use rt_skip to skip the first 'i' elements
                            let rt_skip = self.get_or_declare_rt_skip();
                            let skip_count = self.compile_integer(i as i64);
                            let after_skip = self
                                .builder
                                .build_call(
                                    rt_skip,
                                    &[skip_count.into(), list_val.into()],
                                    "after_skip",
                                )
                                .unwrap();
                            let after_skip_val = after_skip.try_as_basic_value().left().unwrap();

                            // Now take (len - patterns_after_rest - i) elements from after_skip
                            // That's (actual_len - patterns_after_rest - i) elements
                            // But we can compute: we want actual_len - i - patterns_after_rest
                            let total_skip = self
                                .context
                                .i64_type()
                                .const_int((i + patterns_after_rest) as u64, false);
                            let rest_len = self
                                .builder
                                .build_int_sub(actual_len, total_skip, "rest_len")
                                .unwrap();

                            // Convert to tagged integer
                            let tagged_rest_len = self
                                .builder
                                .build_left_shift(
                                    rest_len,
                                    self.context.i64_type().const_int(3, false),
                                    "shift_rest_len",
                                )
                                .unwrap();
                            let tagged_rest_len = self
                                .builder
                                .build_or(
                                    tagged_rest_len,
                                    self.context.i64_type().const_int(0b001, false),
                                    "tag_rest_len",
                                )
                                .unwrap();

                            let rt_take = self.get_or_declare_rt_take();
                            let rest_result = self
                                .builder
                                .build_call(
                                    rt_take,
                                    &[tagged_rest_len.into(), after_skip_val.into()],
                                    "rest_val",
                                )
                                .unwrap();
                            let rest_val = rest_result.try_as_basic_value().left().unwrap();

                            let alloca = self
                                .builder
                                .build_alloca(self.context.i64_type(), name)
                                .unwrap();
                            self.builder.build_store(alloca, rest_val).unwrap();
                            self.variables.insert(name.clone(), alloca);
                        }
                        Pattern::Wildcard | Pattern::Literal(_) => {
                            // No binding needed
                            if is_after_rest {
                                after_rest_offset += 1;
                            }
                        }
                        Pattern::List(nested_patterns) => {
                            // Nested list - get the element first (considering rest position)
                            let nested_elem = if is_after_rest {
                                // Element after rest: compute index from end
                                let offset_from_end =
                                    (patterns_after_rest - after_rest_offset) as u64;
                                let idx_from_end = self
                                    .builder
                                    .build_int_sub(
                                        actual_len,
                                        self.context.i64_type().const_int(offset_from_end, false),
                                        "nested_idx_from_end",
                                    )
                                    .unwrap();

                                let tagged_idx = self
                                    .builder
                                    .build_left_shift(
                                        idx_from_end,
                                        self.context.i64_type().const_int(3, false),
                                        "shift_nested_idx",
                                    )
                                    .unwrap();
                                let tagged_idx = self
                                    .builder
                                    .build_or(
                                        tagged_idx,
                                        self.context.i64_type().const_int(0b001, false),
                                        "tag_nested_idx",
                                    )
                                    .unwrap();

                                let rt_get = self.get_or_declare_rt_get();
                                let nested_elem_result = self
                                    .builder
                                    .build_call(
                                        rt_get,
                                        &[tagged_idx.into(), list_val.into()],
                                        &format!("nested_elem_from_end_{}", after_rest_offset),
                                    )
                                    .unwrap();
                                after_rest_offset += 1;
                                nested_elem_result.try_as_basic_value().left().unwrap()
                            } else {
                                let idx_val = self.compile_integer(i as i64);
                                let rt_get = self.get_or_declare_rt_get();
                                let nested_elem_result = self
                                    .builder
                                    .build_call(
                                        rt_get,
                                        &[idx_val.into(), list_val.into()],
                                        &format!("nested_elem_{}", i),
                                    )
                                    .unwrap();
                                nested_elem_result.try_as_basic_value().left().unwrap()
                            };

                            // Bind variables in the nested pattern (supports deep nesting + rest)
                            self.bind_pattern_variables(
                                &Pattern::List(nested_patterns.clone()),
                                nested_elem,
                            )?;
                        }
                        _ => {}
                    }
                }
                Ok(())
            }
            Pattern::RestIdentifier(_) => {
                // Rest pattern on its own - shouldn't happen
                Ok(())
            }
        }
    }

    /// Compile a literal value
    fn compile_literal(&mut self, lit: &Literal) -> BasicValueEnum<'ctx> {
        match lit {
            Literal::Integer(n) => self.compile_integer(*n),
            Literal::Decimal(f) => self.compile_decimal(*f),
            Literal::Boolean(b) => self.compile_boolean(*b),
            Literal::String(s) => self
                .compile_string(s)
                .unwrap_or_else(|_| self.compile_nil()),
            Literal::Nil => self.compile_nil(),
        }
    }

    /// Convert a NaN-boxed value to a boolean for conditional branching
    fn value_to_bool(&self, value: BasicValueEnum<'ctx>) -> inkwell::values::IntValue<'ctx> {
        // Extract the boolean from NaN-boxed value
        // Boolean tag is 0b010, value is in upper bits
        let int_val = value.into_int_value();
        let shifted = self
            .builder
            .build_right_shift(
                int_val,
                self.context.i64_type().const_int(3, false),
                false,
                "shift",
            )
            .unwrap();
        self.builder
            .build_int_truncate(shifted, self.context.bool_type(), "to_bool")
            .unwrap()
    }

    /// Compile a statement
    pub fn compile_stmt(&mut self, stmt: &Stmt) -> Result<(), CompileError> {
        match stmt {
            Stmt::Let {
                mutable,
                pattern,
                value,
            } => {
                // compile_let returns the value, but compile_stmt ignores it
                self.compile_let(pattern, value, *mutable)?;
                Ok(())
            }
            Stmt::Return(_) | Stmt::Break(_) | Stmt::Expr(_) => {
                Err(CompileError::UnsupportedStatement(format!(
                    "Statement type not yet implemented: {:?}",
                    stmt
                )))
            }
        }
    }

    /// Compile a let binding
    /// Returns the compiled value for use when let is the last statement in a block
    fn compile_let(
        &mut self,
        pattern: &Pattern,
        value: &Expr,
        mutable: bool,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        self.validate_pattern_bindings(pattern)?;
        self.set_pattern_mutability(pattern, mutable);
        match pattern {
            Pattern::Identifier(name) => {
                // For recursive function bindings, we need to pre-allocate the variable
                // so the function body can reference itself
                let is_function = matches!(value, Expr::Function { .. });

                // Check if this variable needs to be cell-wrapped
                // This happens when:
                // 1. It's mutable AND captured by a nested closure
                // 2. It's a self-referencing binding (e.g., let fib = memoize |n| fib(...))
                let needs_cell = self.cell_variables.contains(name);

                // Check if the variable was already forward-declared (for mutual recursion support)
                // If so, reuse the existing alloca; otherwise create a new one
                let already_forward_declared = self.variables.contains_key(name);
                let alloca = if let Some(existing) = self.variables.get(name) {
                    *existing
                } else {
                    self.builder
                        .build_alloca(self.context.i64_type(), name)
                        .unwrap()
                };

                // For self-referencing bindings (both functions and non-functions),
                // we need to create the cell BEFORE compiling so the value expression
                // can capture a reference to the cell.
                // But skip cell creation if already forward-declared (cell already exists).
                if needs_cell && !already_forward_declared {
                    // Create a cell with nil initially
                    let rt_cell_new = self.get_or_declare_rt_cell_new();
                    let nil_val = self.compile_nil();
                    let cell = self
                        .builder
                        .build_call(
                            rt_cell_new,
                            &[nil_val.into()],
                            &format!("{}_cell_init", name),
                        )
                        .unwrap();
                    // Store the cell in the alloca
                    self.builder
                        .build_store(alloca, cell.try_as_basic_value().left().unwrap())
                        .unwrap();
                    // Register the variable so nested closures can capture the cell
                    self.variables.insert(name.clone(), alloca);
                } else if is_function && !already_forward_declared {
                    // Non-cell function: Register the variable BEFORE compiling
                    // This allows the function body to capture a reference to itself
                    self.variables.insert(name.clone(), alloca);
                }

                // Compile the value expression
                // For functions, pass the binding name for TCO support
                let value_compiled = if let Expr::Function { params, body } = value {
                    self.compile_function_with_name(params, body, Some(name.clone()))?
                } else {
                    let value_ty = self.infer_expr_type(value);
                    let value_typed = TypedExpr {
                        expr: value.clone(),
                        ty: value_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    self.compile_expr(&value_typed)?
                };

                // Handle the final value based on whether it's a cell variable
                if needs_cell {
                    // Cell was already created - now set its value
                    let cell = self
                        .builder
                        .build_load(
                            self.context.i64_type(),
                            alloca,
                            &format!("{}_cell_load", name),
                        )
                        .unwrap();
                    let rt_cell_set = self.get_or_declare_rt_cell_set();
                    self.builder
                        .build_call(
                            rt_cell_set,
                            &[cell.into(), value_compiled.into()],
                            &format!("{}_cell_set", name),
                        )
                        .unwrap();
                } else {
                    // Regular variable - just store the value
                    self.builder.build_store(alloca, value_compiled).unwrap();
                }

                // Register the variable (for non-functions, or update if already registered)
                if !is_function && !needs_cell {
                    // Only register here if we didn't already register for cell handling
                    self.variables.insert(name.clone(), alloca);
                }

                Ok(value_compiled)
            }
            Pattern::List(patterns) => {
                // Compile the value expression first
                let value_ty = self.infer_expr_type(value);
                let value_typed = TypedExpr {
                    expr: value.clone(),
                    ty: value_ty,
                    span: crate::lexer::token::Span::new(
                        crate::lexer::token::Position::new(0, 0),
                        crate::lexer::token::Position::new(0, 0),
                    ),
                };
                let list_val = self.compile_expr(&value_typed)?;

                // Bind patterns to the list value
                self.compile_pattern_binding_list(patterns, list_val)?;
                Ok(list_val)
            }
            _ => Err(CompileError::UnsupportedPattern(format!(
                "Pattern type not yet implemented: {:?}",
                pattern
            ))),
        }
    }

    /// Bind a list of patterns to elements of a list value
    /// Supports nested patterns, rest patterns, and wildcards
    fn compile_pattern_binding_list(
        &mut self,
        patterns: &[Pattern],
        list_val: BasicValueEnum<'ctx>,
    ) -> Result<(), CompileError> {
        for pat in patterns {
            self.validate_pattern_bindings(pat)?;
        }
        let list_val = self.emit_list_pattern_check(list_val, patterns, "list_destructure_check")?;
        let rt_get = self.get_or_declare_rt_get();
        let rt_skip = self.get_or_declare_rt_skip();
        let rt_take = self.get_or_declare_rt_take();
        let rt_size = self.get_or_declare_rt_size();

        let rest_pos = patterns
            .iter()
            .position(|p| matches!(p, Pattern::RestIdentifier(_)));
        let patterns_after_rest = if let Some(pos) = rest_pos {
            patterns.len() - pos - 1
        } else {
            0
        };

        let actual_len = if rest_pos.is_some() {
            let size_result = self
                .builder
                .build_call(rt_size, &[list_val.into()], "list_size")
                .unwrap();
            let size_val = size_result.try_as_basic_value().left().unwrap();
            let size_int = size_val.into_int_value();
            Some(
                self.builder
                    .build_right_shift(
                        size_int,
                        self.context.i64_type().const_int(3, false),
                        false,
                        "actual_len",
                    )
                    .unwrap(),
            )
        } else {
            None
        };

        let mut after_rest_offset = 0usize;
        for (i, pat) in patterns.iter().enumerate() {
            let is_after_rest = rest_pos.is_some_and(|pos| i > pos);

            match pat {
                Pattern::Identifier(name) => {
                    let elem = if is_after_rest {
                        let actual_len = actual_len.expect("rest position requires list length");
                        let offset_from_end = (patterns_after_rest - after_rest_offset) as u64;
                        let idx_from_end = self
                            .builder
                            .build_int_sub(
                                actual_len,
                                self.context.i64_type().const_int(offset_from_end, false),
                                "idx_from_end",
                            )
                            .unwrap();

                        let tagged_idx = self
                            .builder
                            .build_left_shift(
                                idx_from_end,
                                self.context.i64_type().const_int(3, false),
                                "shift_idx",
                            )
                            .unwrap();
                        let tagged_idx = self
                            .builder
                            .build_or(
                                tagged_idx,
                                self.context.i64_type().const_int(0b001, false),
                                "tag_idx",
                            )
                            .unwrap();

                        let elem_result = self
                            .builder
                            .build_call(
                                rt_get,
                                &[tagged_idx.into(), list_val.into()],
                                &format!("destructure_from_end_{}", after_rest_offset),
                            )
                            .unwrap();
                        after_rest_offset += 1;
                        elem_result.try_as_basic_value().left().unwrap()
                    } else {
                        let index_val = self.compile_integer(i as i64);
                        let elem_result = self
                            .builder
                            .build_call(
                                rt_get,
                                &[index_val.into(), list_val.into()],
                                &format!("destructure_{}", name),
                            )
                            .unwrap();
                        elem_result.try_as_basic_value().left().unwrap()
                    };

                    let alloca = self
                        .builder
                        .build_alloca(self.context.i64_type(), name)
                        .unwrap();
                    self.builder.build_store(alloca, elem).unwrap();
                    self.variables.insert(name.clone(), alloca);
                }
                Pattern::Wildcard => {
                    if is_after_rest {
                        after_rest_offset += 1;
                    }
                }
                Pattern::List(nested_patterns) => {
                    let nested_list = if is_after_rest {
                        let actual_len = actual_len.expect("rest position requires list length");
                        let offset_from_end = (patterns_after_rest - after_rest_offset) as u64;
                        let idx_from_end = self
                            .builder
                            .build_int_sub(
                                actual_len,
                                self.context.i64_type().const_int(offset_from_end, false),
                                "nested_idx_from_end",
                            )
                            .unwrap();

                        let tagged_idx = self
                            .builder
                            .build_left_shift(
                                idx_from_end,
                                self.context.i64_type().const_int(3, false),
                                "shift_nested_idx",
                            )
                            .unwrap();
                        let tagged_idx = self
                            .builder
                            .build_or(
                                tagged_idx,
                                self.context.i64_type().const_int(0b001, false),
                                "tag_nested_idx",
                            )
                            .unwrap();

                        let nested_elem_result = self
                            .builder
                            .build_call(
                                rt_get,
                                &[tagged_idx.into(), list_val.into()],
                                &format!("destructure_nested_from_end_{}", after_rest_offset),
                            )
                            .unwrap();
                        after_rest_offset += 1;
                        nested_elem_result.try_as_basic_value().left().unwrap()
                    } else {
                        let index_val = self.compile_integer(i as i64);
                        let nested_elem_result = self
                            .builder
                            .build_call(
                                rt_get,
                                &[index_val.into(), list_val.into()],
                                &format!("destructure_nested_{}", i),
                            )
                            .unwrap();
                        nested_elem_result.try_as_basic_value().left().unwrap()
                    };

                    self.compile_pattern_binding_list(nested_patterns, nested_list)?;
                }
                Pattern::RestIdentifier(name) => {
                    if name.is_empty() {
                        // Bare rest (..) ignores remaining elements
                        continue;
                    }
                    let skip_count = self.compile_integer(i as i64);
                    let after_skip = self
                        .builder
                        .build_call(
                            rt_skip,
                            &[skip_count.into(), list_val.into()],
                            &format!("destructure_rest_{}", name),
                        )
                        .unwrap();
                    let after_skip_val = after_skip.try_as_basic_value().left().unwrap();

                    let rest_val = if patterns_after_rest == 0 {
                        after_skip_val
                    } else {
                        let actual_len =
                            actual_len.expect("rest position requires list length");
                        let total_skip = self
                            .context
                            .i64_type()
                            .const_int((i + patterns_after_rest) as u64, false);
                        let rest_len = self
                            .builder
                            .build_int_sub(actual_len, total_skip, "rest_len")
                            .unwrap();

                        let tagged_rest_len = self
                            .builder
                            .build_left_shift(
                                rest_len,
                                self.context.i64_type().const_int(3, false),
                                "shift_rest_len",
                            )
                            .unwrap();
                        let tagged_rest_len = self
                            .builder
                            .build_or(
                                tagged_rest_len,
                                self.context.i64_type().const_int(0b001, false),
                                "tag_rest_len",
                            )
                            .unwrap();

                        let rest_result = self
                            .builder
                            .build_call(
                                rt_take,
                                &[tagged_rest_len.into(), after_skip_val.into()],
                                "rest_val",
                            )
                            .unwrap();
                        rest_result.try_as_basic_value().left().unwrap()
                    };

                    let alloca = self
                        .builder
                        .build_alloca(self.context.i64_type(), name)
                        .unwrap();
                    self.builder.build_store(alloca, rest_val).unwrap();
                    self.variables.insert(name.clone(), alloca);
                }
                _ => {
                    return Err(CompileError::UnsupportedPattern(format!(
                        "Pattern type not supported in list destructuring: {:?}",
                        pat
                    )));
                }
            }
        }
        Ok(())
    }

    fn compile_list_pattern_match(
        &mut self,
        subject: BasicValueEnum<'ctx>,
        patterns: &[Pattern],
        no_match_bb: inkwell::basic_block::BasicBlock<'ctx>,
        name_prefix: &str,
    ) -> Result<inkwell::basic_block::BasicBlock<'ctx>, CompileError> {
        let current_fn = self
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();

        let rt_is_list = self.get_or_declare_rt_is_list();
        let is_list_val = self
            .builder
            .build_call(rt_is_list, &[subject.into()], "is_list")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_int_value();
        let is_list_bool = self
            .builder
            .build_int_compare(
                IntPredicate::NE,
                is_list_val,
                self.context.i64_type().const_zero(),
                "is_list_bool",
            )
            .unwrap();
        let list_check_bb = self
            .context
            .append_basic_block(current_fn, &format!("{name_prefix}_list_check"));
        self.builder
            .build_conditional_branch(is_list_bool, list_check_bb, no_match_bb)
            .unwrap();
        self.builder.position_at_end(list_check_bb);

        let mut fixed_count = 0usize;
        let mut rest_position = None;
        for (i, p) in patterns.iter().enumerate() {
            if matches!(p, Pattern::RestIdentifier(_)) {
                rest_position = Some(i);
            } else {
                fixed_count += 1;
            }
        }
        let has_rest = rest_position.is_some();

        let rt_size = self.get_or_declare_rt_size();
        let size_result = self
            .builder
            .build_call(rt_size, &[subject.into()], "list_size")
            .unwrap();
        let size_val = size_result.try_as_basic_value().left().unwrap();
        let size_int = size_val.into_int_value();
        let actual_len = self
            .builder
            .build_right_shift(
                size_int,
                self.context.i64_type().const_int(3, false),
                false,
                "actual_len",
            )
            .unwrap();

        let expected_len = self.context.i64_type().const_int(fixed_count as u64, false);
        let len_ok = if has_rest {
            self.builder
                .build_int_compare(IntPredicate::UGE, actual_len, expected_len, "len_ge")
                .unwrap()
        } else {
            self.builder
                .build_int_compare(IntPredicate::EQ, actual_len, expected_len, "len_eq")
                .unwrap()
        };

        let check_elements_bb = self
            .context
            .append_basic_block(current_fn, &format!("{name_prefix}_check_elements"));
        self.builder
            .build_conditional_branch(len_ok, check_elements_bb, no_match_bb)
            .unwrap();
        self.builder.position_at_end(check_elements_bb);

        let patterns_after_rest = if let Some(rest_pos) = rest_position {
            patterns.len() - rest_pos - 1
        } else {
            0
        };

        let rt_get = self.get_or_declare_rt_get();
        let mut elem_idx = 0usize;
        let mut after_rest_offset = 0usize;
        for (i, p) in patterns.iter().enumerate() {
            if matches!(p, Pattern::RestIdentifier(_)) {
                continue;
            }

            let is_after_rest = rest_position.is_some_and(|pos| i > pos);
            let elem_val = if is_after_rest {
                let offset_from_end = (patterns_after_rest - after_rest_offset) as u64;
                let idx_from_end = self
                    .builder
                    .build_int_sub(
                        actual_len,
                        self.context.i64_type().const_int(offset_from_end, false),
                        "idx_from_end",
                    )
                    .unwrap();
                let tagged_idx = self
                    .builder
                    .build_left_shift(
                        idx_from_end,
                        self.context.i64_type().const_int(3, false),
                        "shift_idx",
                    )
                    .unwrap();
                let tagged_idx = self
                    .builder
                    .build_or(
                        tagged_idx,
                        self.context.i64_type().const_int(0b001, false),
                        "tag_idx",
                    )
                    .unwrap();
                let elem_result = self
                    .builder
                    .build_call(
                        rt_get,
                        &[tagged_idx.into(), subject.into()],
                        &format!("{name_prefix}_elem_from_end_{after_rest_offset}"),
                    )
                    .unwrap();
                after_rest_offset += 1;
                elem_result.try_as_basic_value().left().unwrap()
            } else {
                let idx_val = self.compile_integer(i as i64);
                let elem_result = self
                    .builder
                    .build_call(
                        rt_get,
                        &[idx_val.into(), subject.into()],
                        &format!("{name_prefix}_elem_{i}"),
                    )
                    .unwrap();
                elem_result.try_as_basic_value().left().unwrap()
            };

            match p {
                Pattern::Wildcard | Pattern::Identifier(_) => {
                    // Always matches
                }
                Pattern::Literal(lit) => {
                    let lit_val = self.compile_literal(lit);
                    let rt_eq = self.get_or_declare_rt_eq();
                    let eq_result = self
                        .builder
                        .build_call(rt_eq, &[elem_val.into(), lit_val.into()], "elem_eq")
                        .unwrap();
                    let eq_val = eq_result.try_as_basic_value().left().unwrap();
                    let eq_bool = self.value_to_bool(eq_val);

                    let next_bb = self.context.append_basic_block(
                        current_fn,
                        &format!("{name_prefix}_check_elem_{}", elem_idx + 1),
                    );
                    self.builder
                        .build_conditional_branch(eq_bool, next_bb, no_match_bb)
                        .unwrap();
                    self.builder.position_at_end(next_bb);
                }
                Pattern::Range {
                    start,
                    end,
                    inclusive,
                } => {
                    // Only match integer elements; non-integers fail to match (no error)
                    let rt_is_integer = self.get_or_declare_rt_is_integer();
                    let is_int = self
                        .builder
                        .build_call(rt_is_integer, &[elem_val.into()], "elem_is_int")
                        .unwrap()
                        .try_as_basic_value()
                        .left()
                        .unwrap();
                    let is_int_bool = self
                        .builder
                        .build_int_compare(
                            IntPredicate::NE,
                            is_int.into_int_value(),
                            self.context.i64_type().const_zero(),
                            "elem_is_int_bool",
                        )
                        .unwrap();

                    let range_check_bb = self.context.append_basic_block(
                        current_fn,
                        &format!("{name_prefix}_range_check_{i}"),
                    );
                    self.builder
                        .build_conditional_branch(is_int_bool, range_check_bb, no_match_bb)
                        .unwrap();
                    self.builder.position_at_end(range_check_bb);

                    let start_val = self.compile_integer(*start);
                    let elem_int = elem_val.into_int_value();
                    let start_int = start_val.into_int_value();

                    let ge_start = self
                        .builder
                        .build_int_compare(
                            IntPredicate::SGE,
                            elem_int,
                            start_int,
                            "elem_ge_start",
                        )
                        .unwrap();

                    let in_range = if let Some(e) = end {
                        let end_val = self.compile_integer(*e);
                        let end_int = end_val.into_int_value();

                        let cmp = if *inclusive {
                            IntPredicate::SLE
                        } else {
                            IntPredicate::SLT
                        };
                        let lt_end = self
                            .builder
                            .build_int_compare(cmp, elem_int, end_int, "elem_lt_end")
                            .unwrap();

                        self.builder
                            .build_and(ge_start, lt_end, "in_range")
                            .unwrap()
                    } else {
                        ge_start
                    };

                    let next_bb = self.context.append_basic_block(
                        current_fn,
                        &format!("{name_prefix}_check_elem_{}", elem_idx + 1),
                    );
                    self.builder
                        .build_conditional_branch(in_range, next_bb, no_match_bb)
                        .unwrap();
                    self.builder.position_at_end(next_bb);
                }
                Pattern::List(nested_patterns) => {
                    let nested_prefix = format!("{name_prefix}_nested_{i}");
                    let nested_success = self.compile_list_pattern_match(
                        elem_val,
                        nested_patterns,
                        no_match_bb,
                        &nested_prefix,
                    )?;
                    self.builder.position_at_end(nested_success);
                }
                _ => {
                    return Err(CompileError::UnsupportedPattern(format!(
                        "Pattern type not supported in list: {:?}",
                        p
                    )));
                }
            }

            elem_idx += 1;
        }

        Ok(self.builder.get_insert_block().unwrap())
    }

    // ===== Phase 9: Closures & Function Calls =====
    // ===== Phase 15: Tail-Call Optimization =====

    /// Compile a function expression into a closure
    ///
    /// This creates:
    /// 1. A new LLVM function for the closure body
    /// 2. A call to rt_make_closure to create the closure object
    fn compile_function(
        &mut self,
        params: &[Param],
        body: &Expr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Anonymous function - no TCO self-name
        self.compile_function_with_name(params, body, None)
    }

    /// Compile a function expression with optional self-name for TCO
    ///
    /// When `self_name` is provided, enables tail-call optimization for
    /// self-recursive calls within the function body.
    fn compile_function_with_name(
        &mut self,
        params: &[Param],
        body: &Expr,
        self_name: Option<String>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        for param in params {
            self.validate_pattern_bindings(&param.pattern)?;
        }
        // Generate a unique name for this closure function
        static CLOSURE_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let closure_id = CLOSURE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let closure_name = format!("closure_{}", closure_id);

        // Analyze what variables this closure captures from the enclosing scope
        let captured_vars: Vec<String> = self
            .find_captured_variables(params, body)
            .into_iter()
            .collect();

        // Create the closure function type
        // Signature: fn(env: *ClosureObject, argc: u32, argv: *Value) -> Value (i64)
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();
        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));

        let closure_fn_type =
            i64_type.fn_type(&[ptr_type.into(), i32_type.into(), ptr_type.into()], false);

        // Create the closure function
        let closure_fn = self
            .module
            .add_function(&closure_name, closure_fn_type, None);

        // For TCO: Create a "start" block that loads parameters, then jumps to "body"
        // For tail calls, we jump back to "body" after updating parameter allocas
        let entry_block = self.context.append_basic_block(closure_fn, "entry");
        let body_block = self.context.append_basic_block(closure_fn, "body");

        // Save current builder position and state
        let saved_block = self.builder.get_insert_block();
        let saved_variables = self.variables.clone();
        let saved_tco_state = self.tco_state.clone();
        let saved_cell_vars = self.cell_variables.clone();
        let saved_mutable_vars = self.mutable_variables.clone();
        let saved_function_depth = self.function_depth;

        // Position builder at the closure function's entry
        self.builder.position_at_end(entry_block);

        // Get function parameters
        let env_ptr = closure_fn.get_nth_param(0).unwrap().into_pointer_value();
        let _argc = closure_fn.get_nth_param(1).unwrap().into_int_value();
        let argv = closure_fn.get_nth_param(2).unwrap().into_pointer_value();

        // Clear variables for the closure's scope
        self.variables.clear();
        self.mutable_variables.clear();
        self.function_depth = saved_function_depth + 1;

        // Determine which captured variables are cells (they were cell vars in the outer scope)
        // These need to remain as cell vars in this scope too
        // NOTE: We use the CURRENT cell_variables (not saved_cell_vars) because the outer
        // scope's block analysis may have added cell vars AFTER we saved the state.
        let outer_cell_vars = self.cell_variables.clone();
        let captured_cell_vars: HashSet<String> = captured_vars
            .iter()
            .filter(|name| outer_cell_vars.contains(*name))
            .cloned()
            .collect();
        self.cell_variables = captured_cell_vars;

        let captured_mutable_vars: HashSet<String> = captured_vars
            .iter()
            .filter(|name| saved_mutable_vars.contains(*name))
            .cloned()
            .collect();
        self.mutable_variables = captured_mutable_vars;

        // Track parameter allocas for TCO
        let mut param_allocas = Vec::new();

        // Load parameters from argv into local variables
        for (i, param) in params.iter().enumerate() {
            // Check if this is a rest parameter
            if let Pattern::RestIdentifier(rest_name) = &param.pattern {
                // Rest parameter: collect all remaining args into a list
                // We need to create a list from argv[i..argc]

                // Calculate number of rest args: argc - i
                let start_idx = self.context.i64_type().const_int(i as u64, false);
                let argc_i64 = self
                    .builder
                    .build_int_z_extend(_argc, i64_type, "argc_ext")
                    .unwrap();
                let rest_count = self
                    .builder
                    .build_int_sub(argc_i64, start_idx, "rest_count")
                    .unwrap();

                // Use rt_list_from_values to create the list
                // We pass a pointer to argv[i] and the count
                let rest_argv = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            i64_type,
                            argv,
                            &[start_idx],
                            "rest_argv",
                        )
                        .unwrap()
                };

                // rt_list_from_values expects (ptr, count) with count as i64/usize
                let rt_list_from_values = self.get_or_declare_rt_list_from_values();
                let rest_list = self
                    .builder
                    .build_call(
                        rt_list_from_values,
                        &[rest_argv.into(), rest_count.into()],
                        "rest_args",
                    )
                    .unwrap();

                let rest_val = rest_list.try_as_basic_value().left().unwrap();
                let alloca = self.builder.build_alloca(i64_type, rest_name).unwrap();
                self.builder.build_store(alloca, rest_val).unwrap();
                self.variables.insert(rest_name.clone(), alloca);
                self.mutable_variables.remove(rest_name);
                // Rest param is always last, no need to continue
                break;
            }

            // Calculate pointer to argv[i]
            let index = self.context.i64_type().const_int(i as u64, false);
            let arg_ptr = unsafe {
                self.builder
                    .build_in_bounds_gep(i64_type, argv, &[index], &format!("arg_ptr_{}", i))
                    .unwrap()
            };

            // Load the argument value
            let arg_val = self
                .builder
                .build_load(i64_type, arg_ptr, &format!("arg_{}", i))
                .unwrap();

            // Bind the parameter based on its pattern type
            if let Some(param_name) = param.name() {
                // Simple identifier parameter - create an alloca and bind directly
                let alloca = self.builder.build_alloca(i64_type, param_name).unwrap();
                self.builder.build_store(alloca, arg_val).unwrap();
                self.variables.insert(param_name.to_string(), alloca);
                self.mutable_variables.remove(param_name);
                param_allocas.push(alloca);
            } else {
                // Pattern parameter (e.g., [a, b]) - use pattern binding
                self.bind_pattern_variables(&param.pattern, arg_val)?;
                self.set_pattern_mutability(&param.pattern, false);
                // No single alloca for TCO with pattern params
            }
        }

        // Load captured variables from the closure environment
        // The closure object has captures stored after the header fields
        // We call rt_get_capture(env_ptr, index) to get each captured value
        for (i, var_name) in captured_vars.iter().enumerate() {
            let rt_get_capture = self.get_or_declare_rt_get_capture();
            let capture_index = self.context.i64_type().const_int(i as u64, false);

            let captured_val = self
                .builder
                .build_call(
                    rt_get_capture,
                    &[env_ptr.into(), capture_index.into()],
                    &format!("cap_{}", var_name),
                )
                .unwrap();

            // Create an alloca for this captured variable
            let alloca = self.builder.build_alloca(i64_type, var_name).unwrap();
            self.builder
                .build_store(alloca, captured_val.try_as_basic_value().left().unwrap())
                .unwrap();
            self.variables.insert(var_name.clone(), alloca);
        }

        // Jump from entry to body (for TCO, tail calls will jump directly to body_block)
        self.builder.build_unconditional_branch(body_block).unwrap();

        // Position at the body block
        self.builder.position_at_end(body_block);

        // Set up TCO state for compiling the body
        self.tco_state = Some(super::context::TcoState {
            self_name,
            entry_block: body_block, // Tail calls jump to body_block
            param_allocas,
        });

        // Compile the body (in tail position - any self-recursive calls here are tail calls)
        let body_result = self.compile_expr_in_tail_position(body)?;

        // Return the result
        self.builder.build_return(Some(&body_result)).unwrap();

        // Restore builder position and state
        self.tco_state = saved_tco_state;
        if let Some(block) = saved_block {
            self.builder.position_at_end(block);
        }

        // Now create the closure object by calling rt_make_closure
        // Note: We need to use saved_variables to get capture values BEFORE restoring self.variables
        let fn_ptr = closure_fn.as_global_value().as_pointer_value();

        // Calculate arity: count non-rest parameters
        // A rest parameter (|..args| or |a, ..rest|) doesn't count toward arity
        // because it accepts 0+ additional arguments
        let required_params = params
            .iter()
            .filter(|p| !matches!(p.pattern, Pattern::RestIdentifier(_)))
            .count();
        let arity = self
            .context
            .i32_type()
            .const_int(required_params as u64, false);

        // Create array of captured values
        let captures_count = captured_vars.len();
        let captures_ptr = if captures_count == 0 {
            self.context
                .ptr_type(inkwell::AddressSpace::from(0))
                .const_null()
        } else {
            // Allocate stack space for captures array
            let array_type = i64_type.array_type(captures_count as u32);
            let array_alloca = self.builder.build_alloca(array_type, "captures").unwrap();

            // Store each captured value
            for (i, var_name) in captured_vars.iter().enumerate() {
                // Get the captured variable's current value from saved_variables
                let var_ptr = saved_variables.get(var_name).ok_or_else(|| {
                    CompileError::UnsupportedExpression(format!("Undefined capture: {}", var_name))
                })?;
                let var_val = self
                    .builder
                    .build_load(i64_type, *var_ptr, var_name)
                    .unwrap();

                // Store in captures array
                let index = self.context.i64_type().const_int(i as u64, false);
                let elem_ptr = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            array_type,
                            array_alloca,
                            &[self.context.i64_type().const_zero(), index],
                            &format!("cap_ptr_{}", i),
                        )
                        .unwrap()
                };
                self.builder.build_store(elem_ptr, var_val).unwrap();
            }

            // Cast to pointer
            self.builder
                .build_pointer_cast(array_alloca, ptr_type, "captures_ptr")
                .unwrap()
        };

        // Now restore self.variables and cell_variables
        self.variables = saved_variables;
        self.cell_variables = saved_cell_vars;
        self.mutable_variables = saved_mutable_vars;
        self.function_depth = saved_function_depth;

        let captures_count_val = self
            .context
            .i64_type()
            .const_int(captures_count as u64, false);

        let rt_make_closure = self.get_or_declare_rt_make_closure();
        let closure_result = self
            .builder
            .build_call(
                rt_make_closure,
                &[
                    fn_ptr.into(),
                    arity.into(),
                    captures_ptr.into(),
                    captures_count_val.into(),
                ],
                "closure",
            )
            .unwrap();

        Ok(closure_result.try_as_basic_value().left().unwrap())
    }

    /// Compile an expression in tail position (for TCO)
    ///
    /// When in tail position and we encounter a self-recursive call,
    /// we can optimize it to a jump instead of a call.
    fn compile_expr_in_tail_position(
        &mut self,
        expr: &Expr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        match expr {
            // If expressions: both branches are in tail position
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => self.compile_if_tail(condition, then_branch, else_branch.as_deref()),
            // If-let expressions: both branches are in tail position
            Expr::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => self.compile_if_let_tail(pattern, value, then_branch, else_branch.as_deref()),
            // Match expressions: arm bodies are in tail position
            Expr::Match { subject, arms } => self.compile_match_tail(subject, arms),
            // Function calls might be tail calls
            Expr::Call { function, args } => {
                // Check if this is a self-recursive tail call
                if let Some(ref tco) = self.tco_state {
                    if let (Some(ref self_name), Expr::Identifier(name)) =
                        (&tco.self_name, function.as_ref())
                    {
                        if name == self_name && args.len() == tco.param_allocas.len() {
                            // This is a self-recursive tail call! Optimize it.
                            return self.compile_tail_call(args);
                        }
                    }
                }
                // Not a tail call, compile normally
                self.compile_call(function, args)
            }
            // Blocks: last expression is in tail position
            Expr::Block(stmts) => self.compile_block_tail(stmts),
            // All other expressions compile normally
            _ => {
                let ty = self.infer_expr_type(expr);
                let typed = TypedExpr {
                    expr: expr.clone(),
                    ty,
                    span: crate::lexer::token::Span::new(
                        crate::lexer::token::Position::new(0, 0),
                        crate::lexer::token::Position::new(0, 0),
                    ),
                };
                self.compile_expr(&typed)
            }
        }
    }

    /// Compile an optimized tail call (jump instead of call)
    fn compile_tail_call(&mut self, args: &[Expr]) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let tco = self.tco_state.clone().unwrap();

        // First, evaluate all arguments to temporaries
        // (We must do this BEFORE updating param allocas, in case args reference params)
        let mut arg_values = Vec::new();
        for arg in args {
            let arg_ty = self.infer_expr_type(arg);
            let arg_typed = TypedExpr {
                expr: arg.clone(),
                ty: arg_ty,
                span: crate::lexer::token::Span::new(
                    crate::lexer::token::Position::new(0, 0),
                    crate::lexer::token::Position::new(0, 0),
                ),
            };
            let val = self.compile_expr(&arg_typed)?;
            arg_values.push(val);
        }

        // Now update param allocas with new values
        for (alloca, val) in tco.param_allocas.iter().zip(arg_values.iter()) {
            self.builder.build_store(*alloca, *val).unwrap();
        }

        // Jump to the body block
        self.builder
            .build_unconditional_branch(tco.entry_block)
            .unwrap();

        // Create a new block for any code after this (unreachable, but LLVM needs it)
        let current_fn = self
            .builder
            .get_insert_block()
            .and_then(|bb| bb.get_parent())
            .ok_or_else(|| {
                CompileError::UnsupportedExpression(
                    "tail call requires a function context".to_string(),
                )
            })?;
        let unreachable_bb = self.context.append_basic_block(current_fn, "unreachable");
        self.builder.position_at_end(unreachable_bb);

        // Return a dummy value (this code is unreachable)
        Ok(self.compile_nil())
    }

    /// Compile an if expression with tail-position awareness
    fn compile_if_tail(
        &mut self,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Get the current function
        let current_fn = self
            .builder
            .get_insert_block()
            .and_then(|bb| bb.get_parent())
            .ok_or_else(|| {
                CompileError::UnsupportedExpression(
                    "if expression requires a function context".to_string(),
                )
            })?;

        // Compile the condition
        let cond_ty = self.infer_expr_type(condition);
        let cond_typed = TypedExpr {
            expr: condition.clone(),
            ty: cond_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let cond_val = self.compile_expr(&cond_typed)?;

        // Call rt_is_truthy to handle all value types (not just booleans)
        let rt_is_truthy = self.get_or_declare_rt_is_truthy();
        let is_truthy = self
            .builder
            .build_call(rt_is_truthy, &[cond_val.into()], "is_truthy")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap();

        // Convert i64 result to i1 for conditional branch
        let cond_bool = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                is_truthy.into_int_value(),
                self.context.i64_type().const_zero(),
                "truthy_bool",
            )
            .unwrap();

        // Create basic blocks
        let then_bb = self.context.append_basic_block(current_fn, "then");
        let else_bb = self.context.append_basic_block(current_fn, "else");
        let merge_bb = self.context.append_basic_block(current_fn, "merge");

        // Branch based on condition
        self.builder
            .build_conditional_branch(cond_bool, then_bb, else_bb)
            .unwrap();

        // Compile then branch (in tail position)
        self.builder.position_at_end(then_bb);
        let then_val = self.compile_expr_in_tail_position(then_branch)?;
        // Check if we need a branch to merge (tail calls don't)
        let then_needs_branch = self
            .builder
            .get_insert_block()
            .map(|bb| bb.get_terminator().is_none())
            .unwrap_or(false);
        if then_needs_branch {
            self.builder.build_unconditional_branch(merge_bb).unwrap();
        }
        let then_end_bb = self.builder.get_insert_block().unwrap();

        // Compile else branch (in tail position)
        self.builder.position_at_end(else_bb);
        let else_val = if let Some(else_expr) = else_branch {
            self.compile_expr_in_tail_position(else_expr)?
        } else {
            self.compile_nil()
        };
        let else_needs_branch = self
            .builder
            .get_insert_block()
            .map(|bb| bb.get_terminator().is_none())
            .unwrap_or(false);
        if else_needs_branch {
            self.builder.build_unconditional_branch(merge_bb).unwrap();
        }
        let else_end_bb = self.builder.get_insert_block().unwrap();

        // Merge block with phi node
        self.builder.position_at_end(merge_bb);

        // Only add phi incoming if the branch doesn't have a terminator (wasn't a tail call)
        let phi = self
            .builder
            .build_phi(self.context.i64_type(), "if_result")
            .unwrap();
        if then_needs_branch {
            phi.add_incoming(&[(&then_val, then_end_bb)]);
        }
        if else_needs_branch {
            phi.add_incoming(&[(&else_val, else_end_bb)]);
        }

        Ok(phi.as_basic_value())
    }

    /// Compile an if-let expression with tail-position awareness
    fn compile_if_let_tail(
        &mut self,
        pattern: &Pattern,
        value: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Get the current function
        let current_fn = self
            .builder
            .get_insert_block()
            .and_then(|bb| bb.get_parent())
            .ok_or_else(|| {
                CompileError::UnsupportedExpression(
                    "if-let expression requires a function context".to_string(),
                )
            })?;

        // Compile the value expression
        let value_ty = self.infer_expr_type(value);
        let value_typed = TypedExpr {
            expr: value.clone(),
            ty: value_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let value_val = self.compile_expr(&value_typed)?;

        // Call rt_is_truthy to check if value is truthy
        let rt_is_truthy = self.get_or_declare_rt_is_truthy();
        let is_truthy = self
            .builder
            .build_call(rt_is_truthy, &[value_val.into()], "is_truthy")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap();

        // Convert to bool
        let cond_bool = self
            .builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                is_truthy.into_int_value(),
                self.context.i64_type().const_zero(),
                "truthy_bool",
            )
            .unwrap();

        // Create basic blocks
        let then_bb = self.context.append_basic_block(current_fn, "if_let_then");
        let else_bb = self.context.append_basic_block(current_fn, "if_let_else");
        let merge_bb = self.context.append_basic_block(current_fn, "if_let_merge");

        // Branch based on truthiness
        self.builder
            .build_conditional_branch(cond_bool, then_bb, else_bb)
            .unwrap();

        // Compile then branch (with pattern binding, in tail position)
        self.builder.position_at_end(then_bb);
        let saved_variables = self.variables.clone();
        let saved_mutable_vars = self.mutable_variables.clone();
        self.set_pattern_mutability(pattern, false);
        self.bind_pattern_variables(pattern, value_val)?;
        let then_val = self.compile_expr_in_tail_position(then_branch)?;
        self.variables = saved_variables;
        self.mutable_variables = saved_mutable_vars;
        let then_needs_branch = self
            .builder
            .get_insert_block()
            .map(|bb| bb.get_terminator().is_none())
            .unwrap_or(false);
        if then_needs_branch {
            self.builder.build_unconditional_branch(merge_bb).unwrap();
        }
        let then_end_bb = self.builder.get_insert_block().unwrap();

        // Compile else branch (in tail position)
        self.builder.position_at_end(else_bb);
        let else_val = if let Some(else_expr) = else_branch {
            self.compile_expr_in_tail_position(else_expr)?
        } else {
            self.compile_nil()
        };
        let else_needs_branch = self
            .builder
            .get_insert_block()
            .map(|bb| bb.get_terminator().is_none())
            .unwrap_or(false);
        if else_needs_branch {
            self.builder.build_unconditional_branch(merge_bb).unwrap();
        }
        let else_end_bb = self.builder.get_insert_block().unwrap();

        // Merge block with phi node
        self.builder.position_at_end(merge_bb);
        let phi = self
            .builder
            .build_phi(self.context.i64_type(), "if_let_result")
            .unwrap();
        if then_needs_branch {
            phi.add_incoming(&[(&then_val, then_end_bb)]);
        }
        if else_needs_branch {
            phi.add_incoming(&[(&else_val, else_end_bb)]);
        }

        Ok(phi.as_basic_value())
    }

    /// Compile a match expression with arm bodies in tail position (for TCO)
    ///
    /// Similar to `compile_match` but arm bodies are compiled with tail-position awareness.
    fn compile_match_tail(
        &mut self,
        subject: &Expr,
        arms: &[MatchArm],
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Get the current function
        let current_fn = self
            .builder
            .get_insert_block()
            .and_then(|bb| bb.get_parent())
            .ok_or_else(|| {
                CompileError::UnsupportedExpression(
                    "match expression requires a function context".to_string(),
                )
            })?;

        // Compile the subject expression
        let subject_ty = self.infer_expr_type(subject);
        let subject_typed = TypedExpr {
            expr: subject.clone(),
            ty: subject_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let subject_val = self.compile_expr(&subject_typed)?;

        // Create the merge block where all arms converge
        let merge_bb = self.context.append_basic_block(current_fn, "match_merge");

        // Track incoming values for the phi node
        let mut incoming: Vec<(BasicValueEnum<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)> =
            Vec::new();

        // Create blocks for each arm
        let arm_blocks: Vec<_> = arms
            .iter()
            .enumerate()
            .map(|(i, _)| {
                self.context
                    .append_basic_block(current_fn, &format!("match_arm_{}", i))
            })
            .collect();

        // Create a fallthrough block for when no pattern matches (returns nil)
        let no_match_bb = self
            .context
            .append_basic_block(current_fn, "match_no_match");

        // Generate pattern tests
        let test_blocks: Vec<_> = arms
            .iter()
            .enumerate()
            .map(|(i, _)| {
                self.context
                    .append_basic_block(current_fn, &format!("match_test_{}", i))
            })
            .collect();

        // Branch from current position to first test block
        self.builder
            .build_unconditional_branch(test_blocks[0])
            .unwrap();

        // Generate pattern tests and branches for each arm
        for (i, arm) in arms.iter().enumerate() {
            let arm_bb = arm_blocks[i];
            let next_bb = if i + 1 < test_blocks.len() {
                test_blocks[i + 1]
            } else {
                no_match_bb
            };

            self.builder.position_at_end(test_blocks[i]);
            self.compile_pattern_test(&arm.pattern, subject_val, arm_bb, next_bb, &arm.guard)?;
        }

        // Compile the body for each arm IN TAIL POSITION
        for (i, arm) in arms.iter().enumerate() {
            self.builder.position_at_end(arm_blocks[i]);

            // Save current variables for scoping
            let saved_variables = self.variables.clone();
            let saved_mutable_vars = self.mutable_variables.clone();

            // Bind pattern variables (pattern bindings are immutable)
            self.set_pattern_mutability(&arm.pattern, false);
            self.bind_pattern_variables(&arm.pattern, subject_val)?;

            // Compile the body IN TAIL POSITION
            let body_val = self.compile_expr_in_tail_position(&arm.body)?;

            // Restore variables (pattern bindings go out of scope)
            self.variables = saved_variables;
            self.mutable_variables = saved_mutable_vars;

            // Check if we need a branch to merge (tail calls don't need it)
            let needs_branch = self
                .builder
                .get_insert_block()
                .map(|bb| bb.get_terminator().is_none())
                .unwrap_or(false);

            if needs_branch {
                let current_bb = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge_bb).unwrap();
                incoming.push((body_val, current_bb));
            }
        }

        // No match fallthrough - return nil
        self.builder.position_at_end(no_match_bb);
        let nil_val = self.compile_nil();
        self.builder.build_unconditional_branch(merge_bb).unwrap();
        incoming.push((nil_val, no_match_bb));

        // Merge block with phi
        self.builder.position_at_end(merge_bb);
        let phi = self
            .builder
            .build_phi(self.context.i64_type(), "match_result")
            .unwrap();
        for (val, bb) in incoming {
            phi.add_incoming(&[(&val, bb)]);
        }

        Ok(phi.as_basic_value())
    }

    /// Compile a block with the last expression in tail position
    fn compile_block_tail(&mut self, stmts: &[Stmt]) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if stmts.is_empty() {
            return Ok(self.compile_nil());
        }

        // Save the current cell_variables set to restore later
        let saved_cell_vars = self.cell_variables.clone();
        // Save the current variables to restore after block (for proper shadowing)
        let saved_variables = self.variables.clone();
        // Save mutable variables for scope restoration
        let saved_mutable_vars = self.mutable_variables.clone();

        // Pre-analyze block to find mutable variables that will be captured by nested closures
        let mut mutable_vars: HashSet<String> = HashSet::new();
        for stmt in stmts {
            if let Stmt::Let {
                mutable: true,
                pattern,
                ..
            } = stmt
            {
                Self::collect_pattern_variables(pattern, &mut mutable_vars);
            }
        }

        // Analyze the block to find which mutable vars are captured by nested closures
        let bound_vars: HashSet<String> = self.variables.keys().cloned().collect();
        for stmt in stmts {
            match stmt {
                Stmt::Let { value, .. } => {
                    let captures =
                        self.find_mutable_captures_in_expr(value, &mutable_vars, &bound_vars);
                    self.cell_variables.extend(captures);
                }
                Stmt::Expr(expr) | Stmt::Return(expr) | Stmt::Break(expr) => {
                    let captures =
                        self.find_mutable_captures_in_expr(expr, &mutable_vars, &bound_vars);
                    self.cell_variables.extend(captures);
                }
            }
        }

        // Also find self-referencing bindings (e.g., let fib = memoize |n| { fib(...) })
        // These need cell indirection so the closure can access the final value
        let self_refs = Self::find_self_referencing_bindings(stmts, &bound_vars);
        self.cell_variables.extend(self_refs);

        // Find forward references (mutual recursion between functions in this block)
        let forward_refs = Self::find_forward_references(stmts, &bound_vars);
        self.cell_variables.extend(forward_refs);

        let mut last_val = None;

        for (i, stmt) in stmts.iter().enumerate() {
            let is_last = i == stmts.len() - 1;

            match stmt {
                Stmt::Let {
                    mutable,
                    pattern,
                    value,
                } => {
                    // Compile the let statement and get the bound value
                    let bound_val = self.compile_let(pattern, value, *mutable)?;
                    // If this is the last statement, the block returns the bound value
                    if is_last {
                        last_val = Some(bound_val);
                    }
                }
                Stmt::Expr(expr) => {
                    if is_last {
                        // Last expression is in tail position
                        last_val = Some(self.compile_expr_in_tail_position(expr)?);
                    } else {
                        let expr_ty = self.infer_expr_type(expr);
                        let expr_typed = TypedExpr {
                            expr: expr.clone(),
                            ty: expr_ty,
                            span: crate::lexer::token::Span::new(
                                crate::lexer::token::Position::new(0, 0),
                                crate::lexer::token::Position::new(0, 0),
                            ),
                        };
                        self.compile_expr(&expr_typed)?;
                    }
                }
                Stmt::Return(expr) => {
                    if self.function_depth == 0 {
                        return Err(CompileError::UnsupportedStatement(
                            "return outside function".to_string(),
                        ));
                    }
                    // Compile the return value expression
                    let return_ty = self.infer_expr_type(expr);
                    let return_typed = TypedExpr {
                        expr: expr.clone(),
                        ty: return_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let return_val = self.compile_expr(&return_typed)?;

                    // Return from the current function
                    self.builder.build_return(Some(&return_val)).unwrap();

                    // Create a new basic block for any code after return (unreachable)
                    let func = self
                        .builder
                        .get_insert_block()
                        .unwrap()
                        .get_parent()
                        .unwrap();
                    let unreachable_block = self.context.append_basic_block(func, "after_return");
                    self.builder.position_at_end(unreachable_block);
                }
                Stmt::Break(expr) => {
                    // Compile the break value expression
                    let break_ty = self.infer_expr_type(expr);
                    let break_typed = TypedExpr {
                        expr: expr.clone(),
                        ty: break_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    let break_val = self.compile_expr(&break_typed)?;

                    // Call rt_break to signal break and store the value
                    let rt_break = self.get_or_declare_rt_break();
                    let result = self
                        .builder
                        .build_call(rt_break, &[break_val.into()], "break_result")
                        .unwrap();

                    // Return from the current function with the break value
                    self.builder
                        .build_return(Some(&result.try_as_basic_value().left().unwrap()))
                        .unwrap();

                    // Create a new basic block for any code after break (unreachable)
                    let func = self
                        .builder
                        .get_insert_block()
                        .unwrap()
                        .get_parent()
                        .unwrap();
                    let unreachable_block =
                        self.context.append_basic_block(func, "after_break_tail");
                    self.builder.position_at_end(unreachable_block);
                }
            }
        }

        // Restore the cell_variables set
        self.cell_variables = saved_cell_vars;
        // Restore the variables to restore proper scoping (inner scope variables go out of scope)
        self.variables = saved_variables;
        // Restore mutable variable bindings
        self.mutable_variables = saved_mutable_vars;

        Ok(last_val.unwrap_or_else(|| self.compile_nil()))
    }

    /// Extract all variable names from a pattern
    fn collect_pattern_variables(pattern: &Pattern, vars: &mut HashSet<String>) {
        match pattern {
            Pattern::Identifier(name) => {
                vars.insert(name.clone());
            }
            Pattern::RestIdentifier(name) => {
                if !name.is_empty() {
                    vars.insert(name.clone());
                }
            }
            Pattern::List(patterns) => {
                for p in patterns {
                    Self::collect_pattern_variables(p, vars);
                }
            }
            Pattern::Wildcard | Pattern::Literal(_) | Pattern::Range { .. } => {}
        }
    }

    /// Mark variables in a pattern as mutable or immutable in the current scope.
    fn set_pattern_mutability(&mut self, pattern: &Pattern, is_mutable: bool) {
        let mut names = HashSet::new();
        Self::collect_pattern_variables(pattern, &mut names);
        for name in names {
            if is_mutable {
                self.mutable_variables.insert(name);
            } else {
                self.mutable_variables.remove(&name);
            }
        }
    }

    /// Find variables that need to be captured by a closure
    fn find_captured_variables(&self, params: &[Param], body: &Expr) -> HashSet<String> {
        let mut free_vars = HashSet::new();
        let mut param_names = HashSet::new();
        for param in params {
            Self::collect_pattern_variables(&param.pattern, &mut param_names);
        }

        Self::collect_free_variables(body, &param_names, &mut free_vars);

        // Filter to only variables that exist in the current scope
        free_vars
            .into_iter()
            .filter(|name| self.variables.contains_key(name))
            .collect()
    }

    /// Recursively collect free variables in an expression
    fn collect_free_variables(expr: &Expr, bound: &HashSet<String>, free: &mut HashSet<String>) {
        match expr {
            Expr::Identifier(name) => {
                if !bound.contains(name) {
                    free.insert(name.clone());
                }
            }
            Expr::Infix { left, right, .. } => {
                Self::collect_free_variables(left, bound, free);
                Self::collect_free_variables(right, bound, free);
            }
            Expr::Prefix { right, .. } => {
                Self::collect_free_variables(right, bound, free);
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                Self::collect_free_variables(condition, bound, free);
                Self::collect_free_variables(then_branch, bound, free);
                if let Some(else_br) = else_branch {
                    Self::collect_free_variables(else_br, bound, free);
                }
            }
            Expr::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                Self::collect_free_variables(value, bound, free);
                // Pattern bindings are in scope for then_branch
                let mut new_bound = bound.clone();
                Self::collect_pattern_variables(pattern, &mut new_bound);
                Self::collect_free_variables(then_branch, &new_bound, free);
                if let Some(else_br) = else_branch {
                    Self::collect_free_variables(else_br, bound, free);
                }
            }
            Expr::Call { function, args } => {
                Self::collect_free_variables(function, bound, free);
                for arg in args {
                    Self::collect_free_variables(arg, bound, free);
                }
            }
            Expr::Function { params, body } => {
                // Add params to bound set for nested function
                let mut new_bound = bound.clone();
                for param in params {
                    Self::collect_pattern_variables(&param.pattern, &mut new_bound);
                }
                Self::collect_free_variables(body, &new_bound, free);
            }
            Expr::Block(stmts) => {
                let mut new_bound = bound.clone();
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { pattern, value, .. } => {
                            // First collect from value (before adding binding)
                            Self::collect_free_variables(value, &new_bound, free);
                            // Then add binding
                            if let Pattern::Identifier(name) = pattern {
                                new_bound.insert(name.clone());
                            }
                        }
                        Stmt::Expr(e) => {
                            Self::collect_free_variables(e, &new_bound, free);
                        }
                        Stmt::Return(e) | Stmt::Break(e) => {
                            Self::collect_free_variables(e, &new_bound, free);
                        }
                    }
                }
            }
            Expr::List(elements) => {
                for elem in elements {
                    Self::collect_free_variables(elem, bound, free);
                }
            }
            Expr::Set(elements) => {
                for elem in elements {
                    Self::collect_free_variables(elem, bound, free);
                }
            }
            Expr::Dict(entries) => {
                for (k, v) in entries {
                    Self::collect_free_variables(k, bound, free);
                    Self::collect_free_variables(v, bound, free);
                }
            }
            Expr::Index { collection, index } => {
                Self::collect_free_variables(collection, bound, free);
                Self::collect_free_variables(index, bound, free);
            }
            Expr::Range { start, end, .. } => {
                Self::collect_free_variables(start, bound, free);
                if let Some(e) = end {
                    Self::collect_free_variables(e, bound, free);
                }
            }
            Expr::Match { subject, arms } => {
                Self::collect_free_variables(subject, bound, free);
                for arm in arms {
                    // Extend bound set with pattern variables
                    let mut new_bound = bound.clone();
                    Self::collect_pattern_bindings(&arm.pattern, &mut new_bound);

                    // Collect from guard if present
                    if let Some(guard) = &arm.guard {
                        Self::collect_free_variables(guard, &new_bound, free);
                    }

                    // Collect from body
                    Self::collect_free_variables(&arm.body, &new_bound, free);
                }
            }
            Expr::Assignment { name, value } => {
                // The target variable and the value both contribute free variables
                if !bound.contains(name) {
                    free.insert(name.clone());
                }
                Self::collect_free_variables(value, bound, free);
            }
            Expr::InfixCall {
                function,
                left,
                right,
            } => {
                // a `f` b - collect from function and both operands
                // The function name is a string, so check if it's a free variable
                if !bound.contains(function) {
                    free.insert(function.clone());
                }
                Self::collect_free_variables(left, bound, free);
                Self::collect_free_variables(right, bound, free);
            }
            Expr::Spread(inner) => {
                Self::collect_free_variables(inner, bound, free);
            }
            // Literals and constants have no free variables
            Expr::Integer(_)
            | Expr::Decimal(_)
            | Expr::String(_)
            | Expr::Boolean(_)
            | Expr::Nil
            | Expr::Placeholder => {}
            // Other expressions - add as needed
            _ => {}
        }
    }

    /// Collect variable bindings introduced by a pattern
    fn collect_pattern_bindings(pattern: &Pattern, bound: &mut HashSet<String>) {
        match pattern {
            Pattern::Identifier(name) => {
                bound.insert(name.clone());
            }
            Pattern::RestIdentifier(name) => {
                if !name.is_empty() {
                    bound.insert(name.clone());
                }
            }
            Pattern::List(patterns) => {
                for p in patterns {
                    Self::collect_pattern_bindings(p, bound);
                }
            }
            // Wildcard, Literal, Range don't introduce bindings
            Pattern::Wildcard | Pattern::Literal(_) | Pattern::Range { .. } => {}
        }
    }

    /// Check if an expression contains a nested closure that references the given variable name.
    /// This is used to detect self-referencing bindings like:
    ///   let fib = memoize |n| { fib(n-1) + fib(n-2) }
    /// where `fib` is referenced inside the closure before it's assigned.
    fn value_has_self_reference(name: &str, expr: &Expr, bound: &HashSet<String>) -> bool {
        match expr {
            // When we hit a nested closure, check if it references `name`
            Expr::Function { params, body } => {
                // Variables bound by this closure's parameters
                let mut inner_bound = bound.clone();
                for param in params {
                    Self::collect_pattern_variables(&param.pattern, &mut inner_bound);
                }

                // Check if `name` is a free variable in this closure
                // collect_free_variables already handles nested closures recursively,
                // so we don't need a separate recursive call here
                let mut free_vars = HashSet::new();
                Self::collect_free_variables(body, &inner_bound, &mut free_vars);

                free_vars.contains(name) && !bound.contains(name)
            }

            // Recurse into subexpressions
            Expr::Infix { left, right, .. } => {
                Self::value_has_self_reference(name, left, bound)
                    || Self::value_has_self_reference(name, right, bound)
            }
            Expr::Prefix { right, .. } => Self::value_has_self_reference(name, right, bound),
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                Self::value_has_self_reference(name, condition, bound)
                    || Self::value_has_self_reference(name, then_branch, bound)
                    || else_branch
                        .as_ref()
                        .is_some_and(|e| Self::value_has_self_reference(name, e, bound))
            }
            Expr::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                if Self::value_has_self_reference(name, value, bound) {
                    return true;
                }
                let mut inner_bound = bound.clone();
                Self::collect_pattern_variables(pattern, &mut inner_bound);
                Self::value_has_self_reference(name, then_branch, &inner_bound)
                    || else_branch
                        .as_ref()
                        .is_some_and(|e| Self::value_has_self_reference(name, e, bound))
            }
            Expr::Call { function, args } => {
                Self::value_has_self_reference(name, function, bound)
                    || args
                        .iter()
                        .any(|arg| Self::value_has_self_reference(name, arg, bound))
            }
            Expr::Block(stmts) => {
                let mut new_bound = bound.clone();
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { pattern, value, .. } => {
                            if Self::value_has_self_reference(name, value, &new_bound) {
                                return true;
                            }
                            if let Pattern::Identifier(n) = pattern {
                                new_bound.insert(n.clone());
                            }
                        }
                        Stmt::Expr(e) | Stmt::Return(e) | Stmt::Break(e) => {
                            if Self::value_has_self_reference(name, e, &new_bound) {
                                return true;
                            }
                        }
                    }
                }
                false
            }
            Expr::List(elements) | Expr::Set(elements) => elements
                .iter()
                .any(|e| Self::value_has_self_reference(name, e, bound)),
            Expr::Dict(entries) => entries.iter().any(|(k, v)| {
                Self::value_has_self_reference(name, k, bound)
                    || Self::value_has_self_reference(name, v, bound)
            }),
            Expr::Index { collection, index } => {
                Self::value_has_self_reference(name, collection, bound)
                    || Self::value_has_self_reference(name, index, bound)
            }
            Expr::Range { start, end, .. } => {
                Self::value_has_self_reference(name, start, bound)
                    || end
                        .as_ref()
                        .is_some_and(|e| Self::value_has_self_reference(name, e, bound))
            }
            Expr::Match { subject, arms } => {
                if Self::value_has_self_reference(name, subject, bound) {
                    return true;
                }
                for arm in arms {
                    let mut arm_bound = bound.clone();
                    Self::collect_pattern_bindings(&arm.pattern, &mut arm_bound);
                    if let Some(guard) = &arm.guard {
                        if Self::value_has_self_reference(name, guard, &arm_bound) {
                            return true;
                        }
                    }
                    if Self::value_has_self_reference(name, &arm.body, &arm_bound) {
                        return true;
                    }
                }
                false
            }
            Expr::Assignment { value, .. } => Self::value_has_self_reference(name, value, bound),
            Expr::Spread(inner) => Self::value_has_self_reference(name, inner, bound),
            // Terminals - no self-reference possible
            _ => false,
        }
    }

    /// Find let bindings in a block that have self-referencing closures.
    /// These need cell indirection so the closure can access the final value.
    pub fn find_self_referencing_bindings(
        stmts: &[Stmt],
        bound: &HashSet<String>,
    ) -> HashSet<String> {
        let mut self_refs = HashSet::new();
        let mut current_bound = bound.clone();

        for stmt in stmts {
            if let Stmt::Let {
                pattern: Pattern::Identifier(name),
                value,
                ..
            } = stmt
            {
                // Check if the value expression has a nested closure that references `name`
                if Self::value_has_self_reference(name, value, &current_bound) {
                    self_refs.insert(name.clone());
                }
                current_bound.insert(name.clone());
            }
        }

        self_refs
    }

    /// Find bindings that have forward references (reference bindings defined later).
    /// This handles mutual recursion between top-level functions.
    /// Both the referencing binding AND the referenced binding need cell indirection.
    pub fn find_forward_references(
        stmts: &[Stmt],
        bound: &HashSet<String>,
    ) -> HashSet<String> {
        // First, collect all top-level binding names
        let mut all_names: HashSet<String> = HashSet::new();
        for stmt in stmts {
            if let Stmt::Let {
                pattern: Pattern::Identifier(name),
                ..
            } = stmt
            {
                all_names.insert(name.clone());
            }
        }

        let mut forward_refs = HashSet::new();
        let mut defined_so_far = bound.clone();

        for stmt in stmts {
            if let Stmt::Let {
                pattern: Pattern::Identifier(name),
                value,
                ..
            } = stmt
            {
                // Find free variables in the value expression
                let mut free_vars = HashSet::new();
                Self::collect_free_variables(value, &defined_so_far, &mut free_vars);

                // Check if any free variable is a top-level binding defined later
                for var in &free_vars {
                    if all_names.contains(var) && !defined_so_far.contains(var) {
                        // This is a forward reference - both bindings need cells
                        forward_refs.insert(name.clone());
                        forward_refs.insert(var.clone());
                    }
                }

                defined_so_far.insert(name.clone());
            }
        }

        forward_refs
    }

    /// Find mutable variables that are captured by nested closures.
    ///
    /// These variables need to be wrapped in cells so the inner closure
    /// can share mutable state with the outer scope.
    pub fn find_mutable_captures_in_expr(
        &self,
        expr: &Expr,
        mutable_vars: &HashSet<String>,
        bound: &HashSet<String>,
    ) -> HashSet<String> {
        let mut captured = HashSet::new();
        Self::collect_mutable_captures_recursive(expr, mutable_vars, bound, &mut captured);
        captured
    }

    /// Recursively find mutable variables that are captured by nested closures
    fn collect_mutable_captures_recursive(
        expr: &Expr,
        mutable_vars: &HashSet<String>,
        bound: &HashSet<String>,
        captured: &mut HashSet<String>,
    ) {
        match expr {
            // When we hit a nested closure, check what mutable vars it captures
            Expr::Function { params, body } => {
                // Variables bound by this closure's parameters
                let mut inner_bound = bound.clone();
                for param in params {
                    Self::collect_pattern_variables(&param.pattern, &mut inner_bound);
                }

                // Find free variables in the closure body
                // collect_free_variables already handles nested closures recursively
                let mut free_vars = HashSet::new();
                Self::collect_free_variables(body, &inner_bound, &mut free_vars);

                // Any free variable that's also in mutable_vars needs to be cell-wrapped
                for var in free_vars {
                    if mutable_vars.contains(&var) && !bound.contains(&var) {
                        captured.insert(var);
                    }
                }
            }

            // Recurse into subexpressions
            Expr::Infix { left, right, .. } => {
                Self::collect_mutable_captures_recursive(left, mutable_vars, bound, captured);
                Self::collect_mutable_captures_recursive(right, mutable_vars, bound, captured);
            }
            Expr::Prefix { right, .. } => {
                Self::collect_mutable_captures_recursive(right, mutable_vars, bound, captured);
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                Self::collect_mutable_captures_recursive(condition, mutable_vars, bound, captured);
                Self::collect_mutable_captures_recursive(
                    then_branch,
                    mutable_vars,
                    bound,
                    captured,
                );
                if let Some(else_br) = else_branch {
                    Self::collect_mutable_captures_recursive(
                        else_br,
                        mutable_vars,
                        bound,
                        captured,
                    );
                }
            }
            Expr::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                Self::collect_mutable_captures_recursive(value, mutable_vars, bound, captured);
                let mut new_bound = bound.clone();
                Self::collect_pattern_variables(pattern, &mut new_bound);
                Self::collect_mutable_captures_recursive(
                    then_branch,
                    mutable_vars,
                    &new_bound,
                    captured,
                );
                if let Some(else_br) = else_branch {
                    Self::collect_mutable_captures_recursive(
                        else_br,
                        mutable_vars,
                        bound,
                        captured,
                    );
                }
            }
            Expr::Call { function, args } => {
                Self::collect_mutable_captures_recursive(function, mutable_vars, bound, captured);
                for arg in args {
                    Self::collect_mutable_captures_recursive(arg, mutable_vars, bound, captured);
                }
            }
            Expr::Block(stmts) => {
                let mut new_bound = bound.clone();
                let mut new_mutable = mutable_vars.clone();
                for stmt in stmts {
                    match stmt {
                        Stmt::Let {
                            mutable,
                            pattern,
                            value,
                        } => {
                            Self::collect_mutable_captures_recursive(
                                value,
                                &new_mutable,
                                &new_bound,
                                captured,
                            );
                            if let Pattern::Identifier(name) = pattern {
                                new_bound.insert(name.clone());
                                if *mutable {
                                    new_mutable.insert(name.clone());
                                }
                            }
                        }
                        Stmt::Expr(e) | Stmt::Return(e) | Stmt::Break(e) => {
                            Self::collect_mutable_captures_recursive(
                                e,
                                &new_mutable,
                                &new_bound,
                                captured,
                            );
                        }
                    }
                }
            }
            Expr::List(elements) | Expr::Set(elements) => {
                for elem in elements {
                    Self::collect_mutable_captures_recursive(elem, mutable_vars, bound, captured);
                }
            }
            Expr::Dict(entries) => {
                for (k, v) in entries {
                    Self::collect_mutable_captures_recursive(k, mutable_vars, bound, captured);
                    Self::collect_mutable_captures_recursive(v, mutable_vars, bound, captured);
                }
            }
            Expr::Index { collection, index } => {
                Self::collect_mutable_captures_recursive(collection, mutable_vars, bound, captured);
                Self::collect_mutable_captures_recursive(index, mutable_vars, bound, captured);
            }
            Expr::Range { start, end, .. } => {
                Self::collect_mutable_captures_recursive(start, mutable_vars, bound, captured);
                if let Some(e) = end {
                    Self::collect_mutable_captures_recursive(e, mutable_vars, bound, captured);
                }
            }
            Expr::Match { subject, arms } => {
                Self::collect_mutable_captures_recursive(subject, mutable_vars, bound, captured);
                for arm in arms {
                    let mut arm_bound = bound.clone();
                    Self::collect_pattern_bindings(&arm.pattern, &mut arm_bound);
                    if let Some(guard) = &arm.guard {
                        Self::collect_mutable_captures_recursive(
                            guard,
                            mutable_vars,
                            &arm_bound,
                            captured,
                        );
                    }
                    Self::collect_mutable_captures_recursive(
                        &arm.body,
                        mutable_vars,
                        &arm_bound,
                        captured,
                    );
                }
            }
            Expr::Assignment { name: _, value } => {
                Self::collect_mutable_captures_recursive(value, mutable_vars, bound, captured);
            }
            // Terminals - no recursion needed
            _ => {}
        }
    }

    /// Compile a function call
    fn compile_call(
        &mut self,
        function: &Expr,
        args: &[Expr],
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Check if this is a call with a single spread argument: f(..collection)
        if args.len() == 1 {
            if let Expr::Spread(inner) = &args[0] {
                // Special case: builtin variadic functions with spread
                if let Expr::Identifier(name) = function {
                    match name.as_str() {
                        "zip" => {
                            return self.compile_builtin_spread_call("zip", inner);
                        }
                        // For max/min/union/intersection, spreading a list is equivalent to
                        // passing the list directly since they accept a single collection argument
                        "max" | "min" | "union" | "intersection" => {
                            // Compile inner as the collection and call the builtin with it
                            let inner_ty = self.infer_expr_type(inner);
                            let inner_typed = TypedExpr {
                                expr: (**inner).clone(),
                                ty: inner_ty,
                                span: crate::lexer::token::Span::new(
                                    crate::lexer::token::Position::new(0, 0),
                                    crate::lexer::token::Position::new(0, 0),
                                ),
                            };
                            let collection = self.compile_expr(&inner_typed)?;
                            let rt_fn = match name.as_str() {
                                "max" => self.get_or_declare_rt_max(),
                                "min" => self.get_or_declare_rt_min(),
                                "union" => self.get_or_declare_rt_union_all(),
                                "intersection" => self.get_or_declare_rt_intersection_all(),
                                _ => unreachable!(),
                            };
                            let result = self
                                .builder
                                .build_call(rt_fn, &[collection.into()], &format!("{}_result", name))
                                .unwrap();
                            return Ok(result.try_as_basic_value().left().unwrap());
                        }
                        _ => {}
                    }
                }

                // For non-builtin functions, use rt_apply
                let fn_ty = self.infer_expr_type(function);
                let fn_typed = TypedExpr {
                    expr: function.clone(),
                    ty: fn_ty,
                    span: crate::lexer::token::Span::new(
                        crate::lexer::token::Position::new(0, 0),
                        crate::lexer::token::Position::new(0, 0),
                    ),
                };
                let fn_val = self.compile_expr(&fn_typed)?;

                // Compile the spread argument (the collection)
                let inner_ty = self.infer_expr_type(inner);
                let inner_typed = TypedExpr {
                    expr: (**inner).clone(),
                    ty: inner_ty,
                    span: crate::lexer::token::Span::new(
                        crate::lexer::token::Position::new(0, 0),
                        crate::lexer::token::Position::new(0, 0),
                    ),
                };
                let collection_val = self.compile_expr(&inner_typed)?;

                // Call rt_apply(fn, collection) which applies fn to collection elements as args
                let rt_apply = self.get_or_declare_rt_apply();
                let result = self
                    .builder
                    .build_call(
                        rt_apply,
                        &[fn_val.into(), collection_val.into()],
                        "apply_result",
                    )
                    .unwrap();
                return Ok(result.try_as_basic_value().left().unwrap());
            }
        }

        // Check if this is a call to a builtin function
        // But only if there's no user-defined variable with the same name (user shadows builtin)
        if let Expr::Identifier(name) = function {
            if !self.variables.contains_key(name) {
                if let Some(result) = self.try_compile_builtin_call(name, args)? {
                    return Ok(result);
                }
            }
        }

        // Compile the function expression
        let fn_ty = self.infer_expr_type(function);
        let fn_typed = TypedExpr {
            expr: function.clone(),
            ty: fn_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let fn_val = self.compile_expr(&fn_typed)?;

        // Compile arguments
        let mut compiled_args = Vec::new();
        for arg in args {
            let arg_ty = self.infer_expr_type(arg);
            let arg_typed = TypedExpr {
                expr: arg.clone(),
                ty: arg_ty,
                span: crate::lexer::token::Span::new(
                    crate::lexer::token::Position::new(0, 0),
                    crate::lexer::token::Position::new(0, 0),
                ),
            };
            let compiled = self.compile_expr(&arg_typed)?;
            compiled_args.push(compiled);
        }

        // Allocate an array on the stack for arguments
        let i64_type = self.context.i64_type();
        let argc = args.len();

        let argv_ptr = if argc == 0 {
            // No arguments, use null pointer
            self.context
                .ptr_type(inkwell::AddressSpace::from(0))
                .const_null()
        } else {
            // Allocate stack space for arguments
            let array_type = i64_type.array_type(argc as u32);
            let array_alloca = self.builder.build_alloca(array_type, "call_args").unwrap();

            // Store each argument
            for (i, arg) in compiled_args.iter().enumerate() {
                let index = self.context.i64_type().const_int(i as u64, false);
                let elem_ptr = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            array_type,
                            array_alloca,
                            &[self.context.i64_type().const_zero(), index],
                            &format!("arg_ptr_{}", i),
                        )
                        .unwrap()
                };
                self.builder.build_store(elem_ptr, *arg).unwrap();
            }

            // Cast to pointer
            let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
            self.builder
                .build_pointer_cast(array_alloca, ptr_type, "argv_ptr")
                .unwrap()
        };

        // Call rt_call(callee, argc, argv)
        let rt_call = self.get_or_declare_rt_call();
        let argc_val = self.context.i32_type().const_int(argc as u64, false);

        let call_result = self
            .builder
            .build_call(
                rt_call,
                &[fn_val.into(), argc_val.into(), argv_ptr.into()],
                "call_result",
            )
            .unwrap();

        Ok(call_result.try_as_basic_value().left().unwrap())
    }

    /// Arity used for partial application of builtins.
    fn get_builtin_arity(name: &str) -> Option<usize> {
        builtin_spec(name).and_then(|spec| spec.partial_arity)
    }

    /// Arity used when a builtin is referenced as a function value.
    fn builtin_value_arity(name: &str) -> Option<usize> {
        builtin_spec(name).and_then(|spec| spec.value_arity)
    }

    /// Compile a builtin variadic function call with a spread argument.
    /// For example: zip(..collection) calls rt_zip_spread(collection)
    fn compile_builtin_spread_call(
        &mut self,
        name: &str,
        collection: &Expr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        // Compile the collection expression
        let coll_ty = self.infer_expr_type(collection);
        let coll_typed = TypedExpr {
            expr: collection.clone(),
            ty: coll_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        let coll_val = self.compile_expr(&coll_typed)?;

        // Call the appropriate spread version of the builtin
        let rt_fn = match name {
            "zip" => self.get_or_declare_rt_zip_spread(),
            _ => {
                return Err(CompileError::UnsupportedExpression(format!(
                    "Builtin {} does not support spread",
                    name
                )))
            }
        };

        let result = self
            .builder
            .build_call(
                rt_fn,
                &[coll_val.into()],
                &format!("{}_spread_result", name),
            )
            .unwrap();

        Ok(result.try_as_basic_value().left().unwrap())
    }

    /// Try to compile a call to a builtin function.
    /// Returns Some(result) if the function is a known builtin, None otherwise.
    /// Supports partial application: if called with fewer args than expected,
    /// returns a closure that captures the provided args.
    fn try_compile_builtin_call(
        &mut self,
        name: &str,
        args: &[Expr],
    ) -> Result<Option<BasicValueEnum<'ctx>>, CompileError> {
        // Check for partial application
        if let Some(arity) = Self::get_builtin_arity(name) {
            if args.len() < arity {
                // Create a partial application: |remaining_args...| builtin(provided_args..., remaining_args...)
                return self.compile_partial_builtin(name, args, arity);
            }
        }

        match name {
            "puts" => {
                // puts(..values) - print values to stdout
                // Compile all arguments
                let mut compiled_args = Vec::new();
                for arg in args {
                    let arg_ty = self.infer_expr_type(arg);
                    let arg_typed = TypedExpr {
                        expr: arg.clone(),
                        ty: arg_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    compiled_args.push(self.compile_expr(&arg_typed)?);
                }

                // Call rt_puts(argc, argv)
                let rt_puts = self.get_or_declare_rt_puts();
                let argc = args.len();
                let i64_type = self.context.i64_type();
                let argc_val = self.context.i32_type().const_int(argc as u64, false);

                let argv_ptr = if argc == 0 {
                    self.context
                        .ptr_type(inkwell::AddressSpace::from(0))
                        .const_null()
                } else {
                    // Allocate stack space for arguments
                    let array_type = i64_type.array_type(argc as u32);
                    let array_alloca = self.builder.build_alloca(array_type, "puts_args").unwrap();

                    // Store each argument
                    for (i, arg) in compiled_args.iter().enumerate() {
                        let index = i64_type.const_int(i as u64, false);
                        let elem_ptr = unsafe {
                            self.builder
                                .build_in_bounds_gep(
                                    array_type,
                                    array_alloca,
                                    &[i64_type.const_zero(), index],
                                    &format!("puts_arg_ptr_{}", i),
                                )
                                .unwrap()
                        };
                        self.builder.build_store(elem_ptr, *arg).unwrap();
                    }

                    // Cast to pointer
                    let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
                    self.builder
                        .build_pointer_cast(array_alloca, ptr_type, "puts_argv")
                        .unwrap()
                };

                let result = self
                    .builder
                    .build_call(rt_puts, &[argc_val.into(), argv_ptr.into()], "puts_result")
                    .unwrap();

                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "__time_nanos" => {
                // __time_nanos() - get current time in nanoseconds (for timing)
                // Takes no arguments, returns i64
                let rt_time_nanos = self.get_or_declare_rt_time_nanos();
                let result = self
                    .builder
                    .build_call(rt_time_nanos, &[], "time_nanos_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "__get_args" => {
                // __get_args() - get command line arguments (excluding program name)
                // Takes no arguments, returns list of strings
                let rt_get_args = self.get_or_declare_rt_get_args();
                let result = self
                    .builder
                    .build_call(rt_get_args, &[], "get_args_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "__print_result" => {
                // __print_result(label, value, time_nanos) - print colored solution result
                if args.len() != 3 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "__print_result expects 3 arguments, got {}",
                        args.len()
                    )));
                }
                let label = self.compile_arg(&args[0])?;
                let value = self.compile_arg(&args[1])?;
                let time_nanos = self.compile_arg(&args[2])?;
                let rt_print_result = self.get_or_declare_rt_print_result();
                self.builder
                    .build_call(
                        rt_print_result,
                        &[label.into(), value.into(), time_nanos.into()],
                        "",
                    )
                    .unwrap();
                Ok(Some(self.context.i64_type().const_int(0, false).into()))
            }
            "__print_test_header" => {
                // __print_test_header(test_num, is_slow) - print test case header
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "__print_test_header expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let test_num = self.compile_arg(&args[0])?;
                let is_slow = self.compile_arg(&args[1])?;
                let rt_print_test_header = self.get_or_declare_rt_print_test_header();
                self.builder
                    .build_call(rt_print_test_header, &[test_num.into(), is_slow.into()], "")
                    .unwrap();
                Ok(Some(self.context.i64_type().const_int(0, false).into()))
            }
            "__print_test_result" => {
                // __print_test_result(label, actual, expected, time_nanos) - print test result
                // Returns true if passed, false if failed
                if args.len() != 4 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "__print_test_result expects 4 arguments, got {}",
                        args.len()
                    )));
                }
                let label = self.compile_arg(&args[0])?;
                let actual = self.compile_arg(&args[1])?;
                let expected = self.compile_arg(&args[2])?;
                let time_nanos = self.compile_arg(&args[3])?;
                let rt_print_test_result = self.get_or_declare_rt_print_test_result();
                let result = self
                    .builder
                    .build_call(
                        rt_print_test_result,
                        &[
                            label.into(),
                            actual.into(),
                            expected.into(),
                            time_nanos.into(),
                        ],
                        "test_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "__print_newline" => {
                // __print_newline() - print a blank line
                let rt_print_newline = self.get_or_declare_rt_print_newline();
                self.builder.build_call(rt_print_newline, &[], "").unwrap();
                Ok(Some(self.context.i64_type().const_int(0, false).into()))
            }
            "sum" => {
                // sum(collection) - sum all elements
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "sum expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_sum = self.get_or_declare_rt_sum();
                let result = self
                    .builder
                    .build_call(rt_sum, &[collection.into()], "sum_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "fold" => {
                // fold(initial, folder, collection)
                if args.len() != 3 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "fold expects 3 arguments, got {}",
                        args.len()
                    )));
                }
                let initial = self.compile_arg(&args[0])?;
                let folder = self.compile_arg(&args[1])?;
                let collection = self.compile_arg(&args[2])?;
                let rt_fold = self.get_or_declare_rt_fold();
                let result = self
                    .builder
                    .build_call(
                        rt_fold,
                        &[initial.into(), folder.into(), collection.into()],
                        "fold_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "memoize" => {
                // memoize(function) - wrap a function with memoization cache
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "memoize expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let func_arg = self.compile_arg(&args[0])?;
                let rt_memoize = self.get_or_declare_rt_memoize();
                let result = self
                    .builder
                    .build_call(rt_memoize, &[func_arg.into()], "memoize_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "map" => {
                // map(mapper, collection) - transform each element
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "map expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let mapper = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_map = self.get_or_declare_rt_map();
                let result = self
                    .builder
                    .build_call(rt_map, &[mapper.into(), collection.into()], "map_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "filter" => {
                // filter(predicate, collection) - keep matching elements
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "filter expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let predicate = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_filter = self.get_or_declare_rt_filter();
                let result = self
                    .builder
                    .build_call(
                        rt_filter,
                        &[predicate.into(), collection.into()],
                        "filter_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "reduce" => {
                // reduce(reducer, collection) - reduce with first element as initial
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "reduce expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let reducer = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_reduce = self.get_or_declare_rt_reduce();
                let result = self
                    .builder
                    .build_call(
                        rt_reduce,
                        &[reducer.into(), collection.into()],
                        "reduce_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "first" => {
                // first(collection) - get first element
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "first expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_first = self.get_or_declare_rt_first();
                let result = self
                    .builder
                    .build_call(rt_first, &[collection.into()], "first_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "second" => {
                // second(collection) - get second element
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "second expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_second = self.get_or_declare_rt_second();
                let result = self
                    .builder
                    .build_call(rt_second, &[collection.into()], "second_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "last" => {
                // last(collection) - get last element
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "last expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_last = self.get_or_declare_rt_last();
                let result = self
                    .builder
                    .build_call(rt_last, &[collection.into()], "last_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "rest" => {
                // rest(collection) - get all elements except first
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "rest expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_rest = self.get_or_declare_rt_rest();
                let result = self
                    .builder
                    .build_call(rt_rest, &[collection.into()], "rest_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "size" => {
                // size(collection) - get number of elements
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "size expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_size = self.get_or_declare_rt_size();
                let result = self
                    .builder
                    .build_call(rt_size, &[collection.into()], "size_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "get" => {
                // get(index, collection) - get element at index
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "get expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let index = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_get = self.get_or_declare_rt_get();
                let result = self
                    .builder
                    .build_call(rt_get, &[index.into(), collection.into()], "get_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "id" => {
                // id(value) - identity function, returns its argument unchanged
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "id expects 1 argument, got {}",
                        args.len()
                    )));
                }
                // Simply return the argument unchanged - no runtime call needed
                let value = self.compile_arg(&args[0])?;
                Ok(Some(value))
            }
            "int" => {
                // int(value) - convert to integer
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "int expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_int = self.get_or_declare_rt_int();
                let result = self
                    .builder
                    .build_call(rt_int, &[value.into()], "int_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "ints" => {
                // ints(string) - extract all integers from string
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "ints expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_ints = self.get_or_declare_rt_ints();
                let result = self
                    .builder
                    .build_call(rt_ints, &[value.into()], "ints_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "list" => {
                // list(value) - convert to list
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "list expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_list = self.get_or_declare_rt_list();
                let result = self
                    .builder
                    .build_call(rt_list, &[value.into()], "list_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "set" => {
                // set(value) - convert to set
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "set expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_set = self.get_or_declare_rt_set();
                let result = self
                    .builder
                    .build_call(rt_set, &[value.into()], "set_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "dict" => {
                // dict(value) - convert to dict
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "dict expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_dict = self.get_or_declare_rt_dict();
                let result = self
                    .builder
                    .build_call(rt_dict, &[value.into()], "dict_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "keys" => {
                // keys(dict) - get dict keys as list
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "keys expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_keys = self.get_or_declare_rt_keys();
                let result = self
                    .builder
                    .build_call(rt_keys, &[collection.into()], "keys_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "values" => {
                // values(dict) - get dict values as list
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "values expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_values = self.get_or_declare_rt_values();
                let result = self
                    .builder
                    .build_call(rt_values, &[collection.into()], "values_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "each" => {
                // each(fn, collection) - apply fn to each element for side effects
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "each expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let func = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_each = self.get_or_declare_rt_each();
                let result = self
                    .builder
                    .build_call(rt_each, &[func.into(), collection.into()], "each_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "find" => {
                // find(predicate, collection) - find first matching element
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "find expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let predicate = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_find = self.get_or_declare_rt_find();
                let result = self
                    .builder
                    .build_call(
                        rt_find,
                        &[predicate.into(), collection.into()],
                        "find_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "count" => {
                // count(predicate, collection) - count matching elements
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "count expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let predicate = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_count = self.get_or_declare_rt_count();
                let result = self
                    .builder
                    .build_call(
                        rt_count,
                        &[predicate.into(), collection.into()],
                        "count_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "flat_map" => {
                // flat_map(mapper, collection) - map and flatten
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "flat_map expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let mapper = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_flat_map = self.get_or_declare_rt_flat_map();
                let result = self
                    .builder
                    .build_call(
                        rt_flat_map,
                        &[mapper.into(), collection.into()],
                        "flat_map_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "filter_map" => {
                // filter_map(mapper, collection) - map and keep truthy
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "filter_map expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let mapper = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_filter_map = self.get_or_declare_rt_filter_map();
                let result = self
                    .builder
                    .build_call(
                        rt_filter_map,
                        &[mapper.into(), collection.into()],
                        "filter_map_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "find_map" => {
                // find_map(mapper, collection) - find first truthy mapped
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "find_map expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let mapper = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_find_map = self.get_or_declare_rt_find_map();
                let result = self
                    .builder
                    .build_call(
                        rt_find_map,
                        &[mapper.into(), collection.into()],
                        "find_map_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "scan" => {
                // scan(initial, folder, collection) - fold with intermediate results
                if args.len() != 3 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "scan expects 3 arguments, got {}",
                        args.len()
                    )));
                }
                let initial = self.compile_arg(&args[0])?;
                let folder = self.compile_arg(&args[1])?;
                let collection = self.compile_arg(&args[2])?;
                let rt_scan = self.get_or_declare_rt_scan();
                let result = self
                    .builder
                    .build_call(
                        rt_scan,
                        &[initial.into(), folder.into(), collection.into()],
                        "scan_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "fold_s" => {
                // fold_s(initial, folder, collection) - fold with state
                if args.len() != 3 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "fold_s expects 3 arguments, got {}",
                        args.len()
                    )));
                }
                let initial = self.compile_arg(&args[0])?;
                let folder = self.compile_arg(&args[1])?;
                let collection = self.compile_arg(&args[2])?;
                let rt_fold_s = self.get_or_declare_rt_fold_s();
                let result = self
                    .builder
                    .build_call(
                        rt_fold_s,
                        &[initial.into(), folder.into(), collection.into()],
                        "fold_s_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "max" => {
                // max(collection) - get maximum element from collection
                // max(a, b) - get maximum of two values
                // max(a, b, c, ...) - get maximum of multiple values (variadic)
                match args.len() {
                    0 => Err(CompileError::UnsupportedExpression(
                        "max expects at least 1 argument".to_string(),
                    )),
                    1 => {
                        let collection = self.compile_arg(&args[0])?;
                        let rt_max = self.get_or_declare_rt_max();
                        let result = self
                            .builder
                            .build_call(rt_max, &[collection.into()], "max_result")
                            .unwrap();
                        Ok(Some(result.try_as_basic_value().left().unwrap()))
                    }
                    2 => {
                        let a = self.compile_arg(&args[0])?;
                        let b = self.compile_arg(&args[1])?;
                        let rt_max2 = self.get_or_declare_rt_max2();
                        let result = self
                            .builder
                            .build_call(rt_max2, &[a.into(), b.into()], "max2_result")
                            .unwrap();
                        Ok(Some(result.try_as_basic_value().left().unwrap()))
                    }
                    _ => {
                        // Variadic: create a list and call rt_max on it
                        let mut compiled_args = Vec::new();
                        for arg in args {
                            compiled_args.push(self.compile_arg(arg)?);
                        }
                        // Build the list using rt_list_from_values
                        let i64_type = self.context.i64_type();
                        let array_type = i64_type.array_type(args.len() as u32);
                        let array_alloca = self.builder.build_alloca(array_type, "max_args").unwrap();
                        for (i, arg) in compiled_args.iter().enumerate() {
                            let index = i64_type.const_int(i as u64, false);
                            let elem_ptr = unsafe {
                                self.builder
                                    .build_in_bounds_gep(
                                        array_type,
                                        array_alloca,
                                        &[i64_type.const_zero(), index],
                                        &format!("max_arg_ptr_{}", i),
                                    )
                                    .unwrap()
                            };
                            self.builder.build_store(elem_ptr, *arg).unwrap();
                        }
                        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
                        let argv = self
                            .builder
                            .build_pointer_cast(array_alloca, ptr_type, "max_argv")
                            .unwrap();
                        let count = i64_type.const_int(args.len() as u64, false);
                        let rt_list_from_values = self.get_or_declare_rt_list_from_values();
                        let list = self
                            .builder
                            .build_call(rt_list_from_values, &[argv.into(), count.into()], "max_list")
                            .unwrap();
                        let list_val = list.try_as_basic_value().left().unwrap();
                        // Now call rt_max on the list
                        let rt_max = self.get_or_declare_rt_max();
                        let result = self
                            .builder
                            .build_call(rt_max, &[list_val.into()], "max_result")
                            .unwrap();
                        Ok(Some(result.try_as_basic_value().left().unwrap()))
                    }
                }
            }
            "min" => {
                // min(collection) - get minimum element from collection
                // min(a, b) - get minimum of two values
                match args.len() {
                    1 => {
                        let collection = self.compile_arg(&args[0])?;
                        let rt_min = self.get_or_declare_rt_min();
                        let result = self
                            .builder
                            .build_call(rt_min, &[collection.into()], "min_result")
                            .unwrap();
                        Ok(Some(result.try_as_basic_value().left().unwrap()))
                    }
                    2 => {
                        let a = self.compile_arg(&args[0])?;
                        let b = self.compile_arg(&args[1])?;
                        let rt_min2 = self.get_or_declare_rt_min2();
                        let result = self
                            .builder
                            .build_call(rt_min2, &[a.into(), b.into()], "min2_result")
                            .unwrap();
                        Ok(Some(result.try_as_basic_value().left().unwrap()))
                    }
                    _ => Err(CompileError::UnsupportedExpression(format!(
                        "min expects 1 or 2 arguments, got {}",
                        args.len()
                    ))),
                }
            }
            "skip" => {
                // skip(n, collection) - skip first n elements
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "skip expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let n = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_skip = self.get_or_declare_rt_skip();
                let result = self
                    .builder
                    .build_call(rt_skip, &[n.into(), collection.into()], "skip_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "take" => {
                // take(n, collection) - take first n elements
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "take expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let n = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_take = self.get_or_declare_rt_take();
                let result = self
                    .builder
                    .build_call(rt_take, &[n.into(), collection.into()], "take_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "sort" => {
                // sort(comparator, collection) - sort collection
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "sort expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let comparator = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_sort = self.get_or_declare_rt_sort();
                let result = self
                    .builder
                    .build_call(
                        rt_sort,
                        &[comparator.into(), collection.into()],
                        "sort_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "reverse" => {
                // reverse(collection) - reverse collection
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "reverse expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_reverse = self.get_or_declare_rt_reverse();
                let result = self
                    .builder
                    .build_call(rt_reverse, &[collection.into()], "reverse_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "rotate" => {
                // rotate(steps, collection) - rotate collection
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "rotate expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let steps = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_rotate = self.get_or_declare_rt_rotate();
                let result = self
                    .builder
                    .build_call(
                        rt_rotate,
                        &[steps.into(), collection.into()],
                        "rotate_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "chunk" => {
                // chunk(size, collection) - split into chunks
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "chunk expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let size_arg = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_chunk = self.get_or_declare_rt_chunk();
                let result = self
                    .builder
                    .build_call(
                        rt_chunk,
                        &[size_arg.into(), collection.into()],
                        "chunk_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "union" => {
                // union(..collections) - set union of all collections
                // Can be called with multiple args or a single list of collections
                if args.is_empty() {
                    return Err(CompileError::UnsupportedExpression(
                        "union requires at least 1 argument".to_string(),
                    ));
                }

                // Compile all arguments
                let mut compiled_args = Vec::new();
                for arg in args {
                    compiled_args.push(self.compile_arg(arg)?);
                }

                // Create a list from the arguments using rt_list_from_values
                let i64_type = self.context.i64_type();
                let argc = compiled_args.len();
                let array_type = i64_type.array_type(argc as u32);
                let array_alloca = self.builder.build_alloca(array_type, "union_args").unwrap();

                // Store each argument in the array
                for (i, arg) in compiled_args.iter().enumerate() {
                    let index = i64_type.const_int(i as u64, false);
                    let elem_ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(
                                array_type,
                                array_alloca,
                                &[i64_type.const_zero(), index],
                                &format!("union_arg_ptr_{}", i),
                            )
                            .unwrap()
                    };
                    self.builder.build_store(elem_ptr, *arg).unwrap();
                }

                // Create list from the array
                let rt_list_from_values = self.get_or_declare_rt_list_from_values();
                let list = self
                    .builder
                    .build_call(
                        rt_list_from_values,
                        &[
                            array_alloca.into(),
                            i64_type.const_int(argc as u64, false).into(),
                        ],
                        "union_list",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap();

                // Call rt_union_all(list)
                let rt_union_all = self.get_or_declare_rt_union_all();
                let result = self
                    .builder
                    .build_call(rt_union_all, &[list.into()], "union_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "intersection" => {
                // intersection(..collections) - set intersection of all collections
                // Can be called with multiple args or a single list of collections
                if args.is_empty() {
                    return Err(CompileError::UnsupportedExpression(
                        "intersection requires at least 1 argument".to_string(),
                    ));
                }

                // Compile all arguments
                let mut compiled_args = Vec::new();
                for arg in args {
                    compiled_args.push(self.compile_arg(arg)?);
                }

                // Create a list from the arguments using rt_list_from_values
                let i64_type = self.context.i64_type();
                let argc = compiled_args.len();
                let array_type = i64_type.array_type(argc as u32);
                let array_alloca = self
                    .builder
                    .build_alloca(array_type, "intersection_args")
                    .unwrap();

                // Store each argument in the array
                for (i, arg) in compiled_args.iter().enumerate() {
                    let index = i64_type.const_int(i as u64, false);
                    let elem_ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(
                                array_type,
                                array_alloca,
                                &[i64_type.const_zero(), index],
                                &format!("intersection_arg_ptr_{}", i),
                            )
                            .unwrap()
                    };
                    self.builder.build_store(elem_ptr, *arg).unwrap();
                }

                // Create list from the array
                let rt_list_from_values = self.get_or_declare_rt_list_from_values();
                let list = self
                    .builder
                    .build_call(
                        rt_list_from_values,
                        &[
                            array_alloca.into(),
                            i64_type.const_int(argc as u64, false).into(),
                        ],
                        "intersection_list",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap();

                // Call rt_intersection_all(list)
                let rt_intersection_all = self.get_or_declare_rt_intersection_all();
                let result = self
                    .builder
                    .build_call(rt_intersection_all, &[list.into()], "intersection_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "includes?" => {
                // includes?(collection, value) - check if value is in collection
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "includes? expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let value = self.compile_arg(&args[1])?;
                let rt_includes = self.get_or_declare_rt_includes();
                let result = self
                    .builder
                    .build_call(
                        rt_includes,
                        &[collection.into(), value.into()],
                        "includes_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "excludes?" => {
                // excludes?(collection, value) - check if value is not in collection
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "excludes? expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let value = self.compile_arg(&args[1])?;
                let rt_excludes = self.get_or_declare_rt_excludes();
                let result = self
                    .builder
                    .build_call(
                        rt_excludes,
                        &[collection.into(), value.into()],
                        "excludes_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "any?" => {
                // any?(predicate, collection) - check if any element matches
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "any? expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let predicate = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_any = self.get_or_declare_rt_any();
                let result = self
                    .builder
                    .build_call(rt_any, &[predicate.into(), collection.into()], "any_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "all?" => {
                // all?(predicate, collection) - check if all elements match
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "all? expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let predicate = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_all = self.get_or_declare_rt_all();
                let result = self
                    .builder
                    .build_call(rt_all, &[predicate.into(), collection.into()], "all_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "lines" => {
                // lines(string) - split string into lines
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "lines expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let string = self.compile_arg(&args[0])?;
                let rt_lines = self.get_or_declare_rt_lines();
                let result = self
                    .builder
                    .build_call(rt_lines, &[string.into()], "lines_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "split" => {
                // split(separator, string) - split string by separator
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "split expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let separator = self.compile_arg(&args[0])?;
                let string = self.compile_arg(&args[1])?;
                let rt_split = self.get_or_declare_rt_split();
                let result = self
                    .builder
                    .build_call(rt_split, &[separator.into(), string.into()], "split_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "join" => {
                // join(separator, collection) - join collection with separator
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "join expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let separator = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_join = self.get_or_declare_rt_join();
                let result = self
                    .builder
                    .build_call(
                        rt_join,
                        &[separator.into(), collection.into()],
                        "join_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "upper" => {
                // upper(string) - convert to uppercase
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "upper expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let string = self.compile_arg(&args[0])?;
                let rt_upper = self.get_or_declare_rt_upper();
                let result = self
                    .builder
                    .build_call(rt_upper, &[string.into()], "upper_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "lower" => {
                // lower(string) - convert to lowercase
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "lower expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let string = self.compile_arg(&args[0])?;
                let rt_lower = self.get_or_declare_rt_lower();
                let result = self
                    .builder
                    .build_call(rt_lower, &[string.into()], "lower_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "replace" => {
                // replace(from, to, string) - replace occurrences
                if args.len() != 3 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "replace expects 3 arguments, got {}",
                        args.len()
                    )));
                }
                let from = self.compile_arg(&args[0])?;
                let to = self.compile_arg(&args[1])?;
                let string = self.compile_arg(&args[2])?;
                let rt_replace = self.get_or_declare_rt_replace();
                let result = self
                    .builder
                    .build_call(
                        rt_replace,
                        &[from.into(), to.into(), string.into()],
                        "replace_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "abs" => {
                // abs(value) - absolute value
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "abs expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_abs = self.get_or_declare_rt_abs();
                let result = self
                    .builder
                    .build_call(rt_abs, &[value.into()], "abs_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "signum" => {
                // signum(value) - sign of value
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "signum expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_signum = self.get_or_declare_rt_signum();
                let result = self
                    .builder
                    .build_call(rt_signum, &[value.into()], "signum_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "type" => {
                // type(value) - get type name
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "type expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_type = self.get_or_declare_rt_type();
                let result = self
                    .builder
                    .build_call(rt_type, &[value.into()], "type_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "str" => {
                // str(value) - convert value to string
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "str expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_str = self.get_or_declare_rt_str();
                let result = self
                    .builder
                    .build_call(rt_str, &[value.into()], "str_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "or" => {
                // or(a, b) - return a if truthy, else b
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "or expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let a = self.compile_arg(&args[0])?;
                let b = self.compile_arg(&args[1])?;
                let rt_or = self.get_or_declare_rt_or();
                let result = self
                    .builder
                    .build_call(rt_or, &[a.into(), b.into()], "or_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "and" => {
                // and(a, b) - return b if a is truthy, else a
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "and expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let a = self.compile_arg(&args[0])?;
                let b = self.compile_arg(&args[1])?;
                let rt_and = self.get_or_declare_rt_and();
                let result = self
                    .builder
                    .build_call(rt_and, &[a.into(), b.into()], "and_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "read" => {
                // read(path) - read file contents
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "read expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let path = self.compile_arg(&args[0])?;
                let rt_read = self.get_or_declare_rt_read();
                let result = self
                    .builder
                    .build_call(rt_read, &[path.into()], "read_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "env" => {
                // env() - REPL environment (no-op in AOT)
                if !args.is_empty() {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "env expects 0 arguments, got {}",
                        args.len()
                    )));
                }
                let rt_env = self.get_or_declare_rt_env();
                let result = self.builder.build_call(rt_env, &[], "env_result").unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "push" => {
                // push(value, collection) - add value to collection
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "push expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_push = self.get_or_declare_rt_push();
                let result = self
                    .builder
                    .build_call(rt_push, &[value.into(), collection.into()], "push_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "assoc" => {
                // assoc(key, value, collection) - associate key with value
                if args.len() != 3 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "assoc expects 3 arguments, got {}",
                        args.len()
                    )));
                }
                let key = self.compile_arg(&args[0])?;
                let value = self.compile_arg(&args[1])?;
                let collection = self.compile_arg(&args[2])?;
                let rt_assoc = self.get_or_declare_rt_assoc();
                let result = self
                    .builder
                    .build_call(
                        rt_assoc,
                        &[key.into(), value.into(), collection.into()],
                        "assoc_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "update" => {
                // update(key, updater, collection) - update key using updater function
                if args.len() != 3 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "update expects 3 arguments, got {}",
                        args.len()
                    )));
                }
                let key = self.compile_arg(&args[0])?;
                let updater = self.compile_arg(&args[1])?;
                let collection = self.compile_arg(&args[2])?;
                let rt_update = self.get_or_declare_rt_update();
                let result = self
                    .builder
                    .build_call(
                        rt_update,
                        &[key.into(), updater.into(), collection.into()],
                        "update_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "update_d" => {
                // update_d(key, default, updater, collection) - update with default
                if args.len() != 4 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "update_d expects 4 arguments, got {}",
                        args.len()
                    )));
                }
                let key = self.compile_arg(&args[0])?;
                let default = self.compile_arg(&args[1])?;
                let updater = self.compile_arg(&args[2])?;
                let collection = self.compile_arg(&args[3])?;
                let rt_update_d = self.get_or_declare_rt_update_d();
                let result = self
                    .builder
                    .build_call(
                        rt_update_d,
                        &[
                            key.into(),
                            default.into(),
                            updater.into(),
                            collection.into(),
                        ],
                        "update_d_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "vec_add" => {
                // vec_add(a, b) - element-wise addition of lists
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "vec_add expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let a = self.compile_arg(&args[0])?;
                let b = self.compile_arg(&args[1])?;
                let rt_vec_add = self.get_or_declare_rt_vec_add();
                let result = self
                    .builder
                    .build_call(rt_vec_add, &[a.into(), b.into()], "vec_add_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "bit_and" => {
                // bit_and(a, b) - bitwise AND
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "bit_and expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let a = self.compile_arg(&args[0])?;
                let b = self.compile_arg(&args[1])?;
                let rt_bit_and = self.get_or_declare_rt_bit_and();
                let result = self
                    .builder
                    .build_call(rt_bit_and, &[a.into(), b.into()], "bit_and_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "bit_or" => {
                // bit_or(a, b) - bitwise OR
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "bit_or expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let a = self.compile_arg(&args[0])?;
                let b = self.compile_arg(&args[1])?;
                let rt_bit_or = self.get_or_declare_rt_bit_or();
                let result = self
                    .builder
                    .build_call(rt_bit_or, &[a.into(), b.into()], "bit_or_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "bit_xor" => {
                // bit_xor(a, b) - bitwise XOR
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "bit_xor expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let a = self.compile_arg(&args[0])?;
                let b = self.compile_arg(&args[1])?;
                let rt_bit_xor = self.get_or_declare_rt_bit_xor();
                let result = self
                    .builder
                    .build_call(rt_bit_xor, &[a.into(), b.into()], "bit_xor_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "bit_not" => {
                // bit_not(value) - bitwise NOT
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "bit_not expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_bit_not = self.get_or_declare_rt_bit_not();
                let result = self
                    .builder
                    .build_call(rt_bit_not, &[value.into()], "bit_not_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "bit_shift_left" => {
                // bit_shift_left(value, shift) - bitwise left shift
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "bit_shift_left expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let shift = self.compile_arg(&args[1])?;
                let rt_bit_shift_left = self.get_or_declare_rt_bit_shift_left();
                let result = self
                    .builder
                    .build_call(
                        rt_bit_shift_left,
                        &[value.into(), shift.into()],
                        "bit_shift_left_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "bit_shift_right" => {
                // bit_shift_right(value, shift) - bitwise right shift
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "bit_shift_right expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let shift = self.compile_arg(&args[1])?;
                let rt_bit_shift_right = self.get_or_declare_rt_bit_shift_right();
                let result = self
                    .builder
                    .build_call(
                        rt_bit_shift_right,
                        &[value.into(), shift.into()],
                        "bit_shift_right_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "repeat" => {
                // repeat(value) - create infinite sequence repeating value
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "repeat expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_repeat = self.get_or_declare_rt_repeat();
                let result = self
                    .builder
                    .build_call(rt_repeat, &[value.into()], "repeat_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "cycle" => {
                // cycle(collection) - cycle through collection infinitely
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "cycle expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let collection = self.compile_arg(&args[0])?;
                let rt_cycle = self.get_or_declare_rt_cycle();
                let result = self
                    .builder
                    .build_call(rt_cycle, &[collection.into()], "cycle_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "iterate" => {
                // iterate(generator, initial) - generate infinite sequence by repeated application
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "iterate expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let generator = self.compile_arg(&args[0])?;
                let initial = self.compile_arg(&args[1])?;
                let rt_iterate = self.get_or_declare_rt_iterate();
                let result = self
                    .builder
                    .build_call(
                        rt_iterate,
                        &[generator.into(), initial.into()],
                        "iterate_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "combinations" => {
                // combinations(size, collection) - generate all combinations of given size
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "combinations expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let size = self.compile_arg(&args[0])?;
                let collection = self.compile_arg(&args[1])?;
                let rt_combinations = self.get_or_declare_rt_combinations();
                let result = self
                    .builder
                    .build_call(
                        rt_combinations,
                        &[size.into(), collection.into()],
                        "combinations_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "range" => {
                // range(from, to, step) - generate range with custom step
                if args.len() != 3 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "range expects 3 arguments, got {}",
                        args.len()
                    )));
                }

                let from = self.compile_arg(&args[0])?;
                let to = self.compile_arg(&args[1])?;
                let step = self.compile_arg(&args[2])?;
                let rt_range = self.get_or_declare_rt_range();
                let result = self
                    .builder
                    .build_call(
                        rt_range,
                        &[from.into(), to.into(), step.into()],
                        "range_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "zip" => {
                // zip(collection, ..collections) - zip multiple collections
                // Variadic function similar to puts
                if args.is_empty() {
                    return Err(CompileError::UnsupportedExpression(
                        "zip expects at least 1 argument".to_string(),
                    ));
                }

                // If only 1 argument, create a partial application: |x| zip(arg, x)
                // This enables patterns like: zip(1..) >> map(f) >> sum
                if args.len() == 1 {
                    // Create a lambda: |x| zip(first_arg, x)
                    let param = crate::parser::ast::Param::simple("x".to_string());
                    let body = Expr::Call {
                        function: Box::new(Expr::Identifier("zip".to_string())),
                        args: vec![args[0].clone(), Expr::Identifier("x".to_string())],
                    };
                    let lambda = Expr::Function {
                        params: vec![param],
                        body: Box::new(body),
                    };
                    let lambda_ty = self.infer_expr_type(&lambda);
                    let lambda_typed = TypedExpr {
                        expr: lambda,
                        ty: lambda_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    return Ok(Some(self.compile_expr(&lambda_typed)?));
                }

                // Compile all arguments
                let mut compiled_args = Vec::new();
                for arg in args {
                    let arg_ty = self.infer_expr_type(arg);
                    let arg_typed = TypedExpr {
                        expr: arg.clone(),
                        ty: arg_ty,
                        span: crate::lexer::token::Span::new(
                            crate::lexer::token::Position::new(0, 0),
                            crate::lexer::token::Position::new(0, 0),
                        ),
                    };
                    compiled_args.push(self.compile_expr(&arg_typed)?);
                }

                // Call rt_zip(argc, argv)
                let rt_zip = self.get_or_declare_rt_zip();
                let argc = args.len();
                let i64_type = self.context.i64_type();
                let argc_val = self.context.i32_type().const_int(argc as u64, false);

                let argv_ptr = if argc == 0 {
                    self.context
                        .ptr_type(inkwell::AddressSpace::from(0))
                        .const_null()
                } else {
                    // Allocate stack space for arguments
                    let array_type = i64_type.array_type(argc as u32);
                    let array_alloca = self.builder.build_alloca(array_type, "zip_args").unwrap();

                    // Store each argument
                    for (i, arg) in compiled_args.iter().enumerate() {
                        let index = i64_type.const_int(i as u64, false);
                        let elem_ptr = unsafe {
                            self.builder
                                .build_in_bounds_gep(
                                    array_type,
                                    array_alloca,
                                    &[i64_type.const_zero(), index],
                                    &format!("zip_arg_ptr_{}", i),
                                )
                                .unwrap()
                        };
                        self.builder.build_store(elem_ptr, *arg).unwrap();
                    }

                    // Cast to pointer
                    let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
                    self.builder
                        .build_pointer_cast(array_alloca, ptr_type, "zip_argv")
                        .unwrap()
                };

                let result = self
                    .builder
                    .build_call(rt_zip, &[argc_val.into(), argv_ptr.into()], "zip_result")
                    .unwrap();

                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "regex_match" => {
                // regex_match(pattern, string) - match regex and return captures
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "regex_match expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let pattern = self.compile_arg(&args[0])?;
                let string = self.compile_arg(&args[1])?;
                let rt_regex_match = self.get_or_declare_rt_regex_match();
                let result = self
                    .builder
                    .build_call(
                        rt_regex_match,
                        &[pattern.into(), string.into()],
                        "regex_match_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "regex_match_all" => {
                // regex_match_all(pattern, string) - match all occurrences
                if args.len() != 2 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "regex_match_all expects 2 arguments, got {}",
                        args.len()
                    )));
                }
                let pattern = self.compile_arg(&args[0])?;
                let string = self.compile_arg(&args[1])?;
                let rt_regex_match_all = self.get_or_declare_rt_regex_match_all();
                let result = self
                    .builder
                    .build_call(
                        rt_regex_match_all,
                        &[pattern.into(), string.into()],
                        "regex_match_all_result",
                    )
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            "md5" => {
                // md5(value) - compute MD5 hash
                if args.len() != 1 {
                    return Err(CompileError::UnsupportedExpression(format!(
                        "md5 expects 1 argument, got {}",
                        args.len()
                    )));
                }
                let value = self.compile_arg(&args[0])?;
                let rt_md5 = self.get_or_declare_rt_md5();
                let result = self
                    .builder
                    .build_call(rt_md5, &[value.into()], "md5_result")
                    .unwrap();
                Ok(Some(result.try_as_basic_value().left().unwrap()))
            }
            _ => Ok(None), // Not a builtin, let compile_call handle it
        }
    }

    /// Compile a partial application of a builtin function.
    /// Creates a lambda that captures the provided args and takes the remaining args.
    fn compile_partial_builtin(
        &mut self,
        name: &str,
        provided_args: &[Expr],
        arity: usize,
    ) -> Result<Option<BasicValueEnum<'ctx>>, CompileError> {
        use crate::parser::ast::Param;

        let remaining = arity - provided_args.len();

        // Generate parameter names for remaining args
        let params: Vec<Param> = (0..remaining)
            .map(|i| Param::simple(format!("__partial_arg_{}", i)))
            .collect();

        // Build the full argument list: provided_args... + remaining params as identifiers
        let mut all_args: Vec<Expr> = provided_args.to_vec();
        for param in &params {
            all_args.push(Expr::Identifier(param.name().unwrap().to_string()));
        }

        // Create the call expression: builtin(all_args...)
        let body = Expr::Call {
            function: Box::new(Expr::Identifier(name.to_string())),
            args: all_args,
        };

        // Create the function: |params...| body
        let func = Expr::Function {
            params,
            body: Box::new(body),
        };

        // Compile the function
        let func_ty = self.infer_expr_type(&func);
        let func_typed = TypedExpr {
            expr: func,
            ty: func_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };

        let result = self.compile_expr(&func_typed)?;
        Ok(Some(result))
    }

    /// Get or declare the rt_time_nanos runtime function
    fn get_or_declare_rt_time_nanos(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_time_nanos";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: () -> i64
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_get_args runtime function
    fn get_or_declare_rt_get_args(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_get_args";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: () -> i64 (returns list of strings)
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_print_result runtime function
    fn get_or_declare_rt_print_result(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_print_result";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (label: i64, value: i64, time_nanos: i64) -> void
        let i64_type = self.context.i64_type();
        let void_type = self.context.void_type();
        let fn_type =
            void_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_print_test_header runtime function
    fn get_or_declare_rt_print_test_header(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_print_test_header";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (test_num: i64, is_slow: i64) -> void
        let i64_type = self.context.i64_type();
        let void_type = self.context.void_type();
        let fn_type = void_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_print_test_result runtime function
    fn get_or_declare_rt_print_test_result(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_print_test_result";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (label: i64, actual: i64, expected: i64, time_nanos: i64) -> i64 (bool)
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(
            &[
                i64_type.into(),
                i64_type.into(),
                i64_type.into(),
                i64_type.into(),
            ],
            false,
        );
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_print_newline runtime function
    fn get_or_declare_rt_print_newline(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_print_newline";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: () -> void
        let void_type = self.context.void_type();
        let fn_type = void_type.fn_type(&[], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_puts runtime function
    fn get_or_declare_rt_puts(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_puts";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (argc: i32, argv: ptr) -> i64
        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let i32_type = self.context.i32_type();
        let i64_type = self.context.i64_type();

        let fn_type = i64_type.fn_type(&[i32_type.into(), ptr_type.into()], false);

        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_make_closure runtime function
    fn get_or_declare_rt_make_closure(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_make_closure";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (fn_ptr: ptr, arity: i32, captures_ptr: ptr, captures_count: i64) -> i64
        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let i32_type = self.context.i32_type();
        let i64_type = self.context.i64_type();

        let fn_type = i64_type.fn_type(
            &[
                ptr_type.into(),
                i32_type.into(),
                ptr_type.into(),
                i64_type.into(),
            ],
            false,
        );

        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_call runtime function
    fn get_or_declare_rt_call(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_call";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (callee: i64, argc: i32, argv: ptr) -> i64
        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let i32_type = self.context.i32_type();
        let i64_type = self.context.i64_type();

        let fn_type = i64_type.fn_type(&[i64_type.into(), i32_type.into(), ptr_type.into()], false);

        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_apply runtime function (for spread arguments)
    fn get_or_declare_rt_apply(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_apply";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (callee: i64, collection: i64) -> i64
        // Applies callee to elements of collection as arguments
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_get_capture runtime function
    fn get_or_declare_rt_get_capture(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_get_capture";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (env_ptr: ptr, index: i64) -> i64
        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let i64_type = self.context.i64_type();

        let fn_type = i64_type.fn_type(&[ptr_type.into(), i64_type.into()], false);

        self.module.add_function(fn_name, fn_type, None)
    }

    /// Helper to compile an argument expression
    fn compile_arg(&mut self, arg: &Expr) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let arg_ty = self.infer_expr_type(arg);
        let arg_typed = TypedExpr {
            expr: arg.clone(),
            ty: arg_ty,
            span: crate::lexer::token::Span::new(
                crate::lexer::token::Position::new(0, 0),
                crate::lexer::token::Position::new(0, 0),
            ),
        };
        self.compile_expr(&arg_typed)
    }

    /// Get or declare the rt_sum runtime function
    fn get_or_declare_rt_sum(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_sum";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_fold runtime function
    fn get_or_declare_rt_fold(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_fold";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (initial: Value, folder: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_break runtime function
    fn get_or_declare_rt_break(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_break";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (value: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_memoize runtime function
    fn get_or_declare_rt_memoize(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_memoize";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (func: Value) -> Value (returns memoized closure)
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_map runtime function
    fn get_or_declare_rt_map(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_map";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (mapper: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_filter runtime function
    fn get_or_declare_rt_filter(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_filter";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (predicate: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_reduce runtime function
    fn get_or_declare_rt_reduce(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_reduce";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (reducer: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_first runtime function
    fn get_or_declare_rt_first(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_first";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_second runtime function
    fn get_or_declare_rt_second(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_second";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_last runtime function
    fn get_or_declare_rt_last(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_last";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_rest runtime function
    fn get_or_declare_rt_rest(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_rest";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_int runtime function
    fn get_or_declare_rt_int(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_int";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (value: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_ints runtime function
    fn get_or_declare_rt_ints(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_ints";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (string: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_list runtime function
    fn get_or_declare_rt_list(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_list";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (value: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_set runtime function
    fn get_or_declare_rt_set(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_set";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (value: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_dict runtime function
    fn get_or_declare_rt_dict(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_dict";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (value: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_keys runtime function
    fn get_or_declare_rt_keys(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_keys";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_values runtime function
    fn get_or_declare_rt_values(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_values";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_each runtime function
    fn get_or_declare_rt_each(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_each";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (func: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_find runtime function
    fn get_or_declare_rt_find(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_find";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (predicate: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_count runtime function
    fn get_or_declare_rt_count(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_count";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (predicate: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_flat_map runtime function
    fn get_or_declare_rt_flat_map(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_flat_map";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_filter_map runtime function
    fn get_or_declare_rt_filter_map(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_filter_map";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_find_map runtime function
    fn get_or_declare_rt_find_map(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_find_map";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_scan runtime function
    fn get_or_declare_rt_scan(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_scan";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_fold_s runtime function
    fn get_or_declare_rt_fold_s(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_fold_s";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_max runtime function
    fn get_or_declare_rt_max(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_max";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_min runtime function
    fn get_or_declare_rt_min(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_min";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_max2 runtime function (2-argument max)
    fn get_or_declare_rt_max2(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_max2";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_min2 runtime function (2-argument min)
    fn get_or_declare_rt_min2(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_min2";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_sort runtime function
    fn get_or_declare_rt_sort(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_sort";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_reverse runtime function
    fn get_or_declare_rt_reverse(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_reverse";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_rotate runtime function
    fn get_or_declare_rt_rotate(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_rotate";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_chunk runtime function
    fn get_or_declare_rt_chunk(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_chunk";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_union_all runtime function (variadic via list)
    fn get_or_declare_rt_union_all(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_union_all";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_intersection_all runtime function (variadic via list)
    fn get_or_declare_rt_intersection_all(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_intersection_all";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_includes runtime function
    fn get_or_declare_rt_includes(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_includes";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_excludes runtime function
    fn get_or_declare_rt_excludes(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_excludes";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_any runtime function
    fn get_or_declare_rt_any(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_any";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_all runtime function
    fn get_or_declare_rt_all(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_all";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_lines runtime function
    fn get_or_declare_rt_lines(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_lines";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_split runtime function
    fn get_or_declare_rt_split(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_split";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_join runtime function
    fn get_or_declare_rt_join(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_join";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_upper runtime function
    fn get_or_declare_rt_upper(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_upper";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_lower runtime function
    fn get_or_declare_rt_lower(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_lower";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_replace runtime function
    fn get_or_declare_rt_replace(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_replace";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_abs runtime function
    fn get_or_declare_rt_abs(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_abs";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_signum runtime function
    fn get_or_declare_rt_signum(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_signum";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_type runtime function
    fn get_or_declare_rt_type(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_type";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_str runtime function
    fn get_or_declare_rt_str(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_str";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_or runtime function
    fn get_or_declare_rt_or(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_or";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_and runtime function
    fn get_or_declare_rt_and(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_and";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_read runtime function
    fn get_or_declare_rt_read(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_read";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_env runtime function
    fn get_or_declare_rt_env(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_env";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    // ===== Collection Modification Functions =====

    /// Get or declare the rt_push runtime function
    fn get_or_declare_rt_push(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_push";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: rt_push(value: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_assoc runtime function
    fn get_or_declare_rt_assoc(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_assoc";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: rt_assoc(key: Value, value: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_update runtime function
    fn get_or_declare_rt_update(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_update";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: rt_update(key: Value, updater: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_update_d runtime function
    fn get_or_declare_rt_update_d(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_update_d";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: rt_update_d(key: Value, default: Value, updater: Value, collection: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(
            &[
                i64_type.into(),
                i64_type.into(),
                i64_type.into(),
                i64_type.into(),
            ],
            false,
        );
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_vec_add runtime function
    fn get_or_declare_rt_vec_add(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_vec_add";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: rt_vec_add(a: Value, b: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    // ===== Bitwise Functions =====

    /// Get or declare the rt_bit_and runtime function
    fn get_or_declare_rt_bit_and(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_bit_and";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_bit_or runtime function
    fn get_or_declare_rt_bit_or(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_bit_or";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_bit_xor runtime function
    fn get_or_declare_rt_bit_xor(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_bit_xor";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_bit_not runtime function
    fn get_or_declare_rt_bit_not(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_bit_not";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_bit_shift_left runtime function
    fn get_or_declare_rt_bit_shift_left(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_bit_shift_left";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_bit_shift_right runtime function
    fn get_or_declare_rt_bit_shift_right(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_bit_shift_right";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    // ===== Sequence Generator Functions =====

    /// Get or declare the rt_repeat runtime function
    fn get_or_declare_rt_repeat(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_repeat";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_cycle runtime function
    fn get_or_declare_rt_cycle(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_cycle";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_iterate runtime function
    fn get_or_declare_rt_iterate(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_iterate";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_combinations runtime function
    fn get_or_declare_rt_combinations(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_combinations";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_range_fn runtime function
    fn get_or_declare_rt_range(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_range_fn";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_zip runtime function
    fn get_or_declare_rt_zip(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_zip";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (argc: i32, argv: ptr) -> i64
        let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
        let i32_type = self.context.i32_type();
        let i64_type = self.context.i64_type();

        let fn_type = i64_type.fn_type(&[i32_type.into(), ptr_type.into()], false);

        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_zip_spread runtime function (for spread arguments)
    fn get_or_declare_rt_zip_spread(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_zip_spread";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: (collection: i64) -> i64
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    // ===== String/Regex Functions =====

    /// Get or declare the rt_regex_match runtime function
    fn get_or_declare_rt_regex_match(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_regex_match";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_regex_match_all runtime function
    fn get_or_declare_rt_regex_match_all(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_regex_match_all";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_md5 runtime function
    fn get_or_declare_rt_md5(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_md5";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    // ===== Mutable Cell Functions =====

    /// Get or declare the rt_cell_new runtime function
    fn get_or_declare_rt_cell_new(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_cell_new";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: rt_cell_new(value: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_cell_get runtime function
    fn get_or_declare_rt_cell_get(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_cell_get";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: rt_cell_get(cell: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }

    /// Get or declare the rt_cell_set runtime function
    fn get_or_declare_rt_cell_set(&self) -> inkwell::values::FunctionValue<'ctx> {
        let fn_name = "rt_cell_set";
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }

        // Signature: rt_cell_set(cell: Value, value: Value) -> Value
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
        self.module.add_function(fn_name, fn_type, None)
    }
}
