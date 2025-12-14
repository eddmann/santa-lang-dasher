use crate::types::{TypedExpr, Type};
use crate::parser::ast::{Expr, InfixOp};
use inkwell::values::BasicValueEnum;
use inkwell::IntPredicate;
use super::context::CodegenContext;

#[derive(Debug)]
pub enum CompileError {
    UnsupportedExpression(String),
}

impl<'ctx> CodegenContext<'ctx> {
    pub fn compile_expr(&mut self, expr: &TypedExpr) -> Result<BasicValueEnum<'ctx>, CompileError> {
        match &expr.expr {
            Expr::Integer(n) => Ok(self.compile_integer(*n)),
            Expr::Decimal(f) => Ok(self.compile_decimal(*f)),
            Expr::Boolean(b) => Ok(self.compile_boolean(*b)),
            Expr::Nil => Ok(self.compile_nil()),
            Expr::String(s) => self.compile_string(s),
            Expr::Infix { left, op, right } => {
                self.compile_binary(left, op, right, &expr.ty)
            },
            Expr::List(elements) => {
                self.compile_list(elements)
            },
            Expr::Set(elements) => {
                self.compile_set(elements)
            },
            Expr::Dict(entries) => {
                self.compile_dict(entries)
            },
            _ => Err(CompileError::UnsupportedExpression(
                format!("Expression type not yet implemented: {:?}", expr.expr)
            )),
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
    /// Decimals are stored as actual f64 (non-NaN range), not tagged
    fn compile_decimal(&self, value: f64) -> BasicValueEnum<'ctx> {
        let f64_type = self.context.f64_type();
        f64_type.const_float(value).into()
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
        let string_ptr = self.builder.build_pointer_cast(
            global.as_pointer_value(),
            ptr_type,
            "str_ptr"
        ).unwrap();

        // Get or declare rt_string_from_cstr function
        let rt_string_fn = self.get_or_declare_rt_string_from_cstr();

        // Call rt_string_from_cstr(ptr, len)
        let len = self.context.i64_type().const_int(value.len() as u64, false);
        let call_result = self.builder.build_call(
            rt_string_fn,
            &[string_ptr.into(), len.into()],
            "string_value"
        ).unwrap();

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

    /// Compile a binary operation with type specialization
    fn compile_binary(
        &mut self,
        left: &Expr,
        op: &InfixOp,
        right: &Expr,
        _result_ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
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
                let cmp = self.builder.build_int_compare(IntPredicate::SLT, l, r, "lt").unwrap();
                Ok(self.box_bool(cmp))
            }

            // Decimal + Decimal → native fadd (FAST PATH)
            (Type::Decimal, InfixOp::Add, Type::Decimal) => {
                let l = left_val.into_float_value();
                let r = right_val.into_float_value();
                let result = self.builder.build_float_add(l, r, "fadd").unwrap();
                Ok(result.into())
            }

            // Decimal - Decimal → native fsub (FAST PATH)
            (Type::Decimal, InfixOp::Subtract, Type::Decimal) => {
                let l = left_val.into_float_value();
                let r = right_val.into_float_value();
                let result = self.builder.build_float_sub(l, r, "fsub").unwrap();
                Ok(result.into())
            }

            // Decimal * Decimal → native fmul (FAST PATH)
            (Type::Decimal, InfixOp::Multiply, Type::Decimal) => {
                let l = left_val.into_float_value();
                let r = right_val.into_float_value();
                let result = self.builder.build_float_mul(l, r, "fmul").unwrap();
                Ok(result.into())
            }

            // Decimal / Decimal → native fdiv (FAST PATH)
            (Type::Decimal, InfixOp::Divide, Type::Decimal) => {
                let l = left_val.into_float_value();
                let r = right_val.into_float_value();
                let result = self.builder.build_float_div(l, r, "fdiv").unwrap();
                Ok(result.into())
            }

            // Decimal < Decimal → native comparison (FAST PATH)
            (Type::Decimal, InfixOp::LessThan, Type::Decimal) => {
                let l = left_val.into_float_value();
                let r = right_val.into_float_value();
                let cmp = self.builder.build_float_compare(inkwell::FloatPredicate::OLT, l, r, "flt").unwrap();
                Ok(self.box_bool(cmp))
            }

            // Unknown types → runtime dispatch (SLOW PATH)
            // TODO: Implement runtime function calls in later task
            _ => Err(CompileError::UnsupportedExpression(
                format!("Binary operation {:?} with types {:?} + {:?} not yet implemented", op, left_ty, right_ty)
            )),
        }
    }

    /// Simple type inference for expressions (temporary until full type inference integration)
    fn infer_expr_type(&self, expr: &Expr) -> Type {
        match expr {
            Expr::Integer(_) => Type::Int,
            Expr::Decimal(_) => Type::Decimal,
            Expr::String(_) => Type::String,
            Expr::Boolean(_) => Type::Bool,
            Expr::Nil => Type::Nil,
            _ => Type::Unknown,
        }
    }

    /// Extract raw i64 from NaN-boxed integer (assumes type is known to be Int)
    fn unbox_int(&self, value: BasicValueEnum<'ctx>) -> inkwell::values::IntValue<'ctx> {
        // Arithmetic right shift by 3 to remove tag bits and restore sign
        let val = value.into_int_value();
        self.builder.build_right_shift(val, self.context.i64_type().const_int(3, false), true, "unbox_int").unwrap()
    }

    /// Box raw i64 into NaN-boxed integer
    fn box_int(&self, value: inkwell::values::IntValue<'ctx>) -> BasicValueEnum<'ctx> {
        // Shift left by 3 and OR with tag 0b001
        let shifted = self.builder.build_left_shift(value, self.context.i64_type().const_int(3, false), "shift").unwrap();
        let tagged = self.builder.build_or(shifted, self.context.i64_type().const_int(0b001, false), "tag").unwrap();
        tagged.into()
    }

    /// Box boolean into NaN-boxed value
    fn box_bool(&self, value: inkwell::values::IntValue<'ctx>) -> BasicValueEnum<'ctx> {
        // Extend i1 to i64, shift to bit 3, OR with tag 0b011
        let extended = self.builder.build_int_z_extend(value, self.context.i64_type(), "ext").unwrap();
        let shifted = self.builder.build_left_shift(extended, self.context.i64_type().const_int(3, false), "shift").unwrap();
        let tagged = self.builder.build_or(shifted, self.context.i64_type().const_int(0b011, false), "tag").unwrap();
        tagged.into()
    }

    /// Compile a list literal
    fn compile_list(&mut self, elements: &[Expr]) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if elements.is_empty() {
            // Empty list: call rt_list_new()
            let rt_list_new = self.get_or_declare_rt_list_new();
            let call_result = self.builder.build_call(rt_list_new, &[], "empty_list").unwrap();
            Ok(call_result.try_as_basic_value().left().unwrap())
        } else {
            // Non-empty list: compile elements and call rt_list_from_values(values, count)
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
            let array_alloca = self.builder.build_alloca(array_type, "list_elements").unwrap();

            // Store each element in the array
            for (i, elem) in compiled_elements.iter().enumerate() {
                let index = self.context.i64_type().const_int(i as u64, false);
                let elem_ptr = unsafe {
                    self.builder.build_in_bounds_gep(
                        array_type,
                        array_alloca,
                        &[self.context.i64_type().const_zero(), index],
                        &format!("elem_ptr_{}", i)
                    ).unwrap()
                };
                self.builder.build_store(elem_ptr, *elem).unwrap();
            }

            // Cast array pointer to *const Value (i64*)
            let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
            let values_ptr = self.builder.build_pointer_cast(array_alloca, ptr_type, "values_ptr").unwrap();

            // Call rt_list_from_values(values, count)
            let rt_list_from_values = self.get_or_declare_rt_list_from_values();
            let count = self.context.i64_type().const_int(elements.len() as u64, false);
            let call_result = self.builder.build_call(
                rt_list_from_values,
                &[values_ptr.into(), count.into()],
                "list"
            ).unwrap();

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

    /// Compile a set literal
    fn compile_set(&mut self, elements: &[Expr]) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if elements.is_empty() {
            // Empty set: call rt_set_new()
            let rt_set_new = self.get_or_declare_rt_set_new();
            let call_result = self.builder.build_call(rt_set_new, &[], "empty_set").unwrap();
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
            let array_alloca = self.builder.build_alloca(array_type, "set_elements").unwrap();

            // Store each element in the array
            for (i, elem) in compiled_elements.iter().enumerate() {
                let index = self.context.i64_type().const_int(i as u64, false);
                let elem_ptr = unsafe {
                    self.builder.build_in_bounds_gep(
                        array_type,
                        array_alloca,
                        &[self.context.i64_type().const_zero(), index],
                        &format!("elem_ptr_{}", i)
                    ).unwrap()
                };
                self.builder.build_store(elem_ptr, *elem).unwrap();
            }

            // Cast array pointer to *const Value
            let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
            let values_ptr = self.builder.build_pointer_cast(array_alloca, ptr_type, "values_ptr").unwrap();

            // Call rt_set_from_values(values, count)
            let rt_set_from_values = self.get_or_declare_rt_set_from_values();
            let count = self.context.i64_type().const_int(elements.len() as u64, false);
            let call_result = self.builder.build_call(
                rt_set_from_values,
                &[values_ptr.into(), count.into()],
                "set"
            ).unwrap();

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
    fn compile_dict(&mut self, entries: &[(Expr, Expr)]) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if entries.is_empty() {
            // Empty dict: call rt_dict_new()
            let rt_dict_new = self.get_or_declare_rt_dict_new();
            let call_result = self.builder.build_call(rt_dict_new, &[], "empty_dict").unwrap();
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
            let values_alloca = self.builder.build_alloca(array_type, "dict_values").unwrap();

            // Store keys and values
            for (i, (key, value)) in compiled_keys.iter().zip(compiled_values.iter()).enumerate() {
                let index = self.context.i64_type().const_int(i as u64, false);

                // Store key
                let key_ptr = unsafe {
                    self.builder.build_in_bounds_gep(
                        array_type,
                        keys_alloca,
                        &[self.context.i64_type().const_zero(), index],
                        &format!("key_ptr_{}", i)
                    ).unwrap()
                };
                self.builder.build_store(key_ptr, *key).unwrap();

                // Store value
                let value_ptr = unsafe {
                    self.builder.build_in_bounds_gep(
                        array_type,
                        values_alloca,
                        &[self.context.i64_type().const_zero(), index],
                        &format!("value_ptr_{}", i)
                    ).unwrap()
                };
                self.builder.build_store(value_ptr, *value).unwrap();
            }

            // Cast pointers
            let ptr_type = self.context.ptr_type(inkwell::AddressSpace::from(0));
            let keys_ptr = self.builder.build_pointer_cast(keys_alloca, ptr_type, "keys_ptr").unwrap();
            let values_ptr = self.builder.build_pointer_cast(values_alloca, ptr_type, "values_ptr").unwrap();

            // Call rt_dict_from_entries(keys, values, count)
            let rt_dict_from_entries = self.get_or_declare_rt_dict_from_entries();
            let count = self.context.i64_type().const_int(entries.len() as u64, false);
            let call_result = self.builder.build_call(
                rt_dict_from_entries,
                &[keys_ptr.into(), values_ptr.into(), count.into()],
                "dict"
            ).unwrap();

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
}
