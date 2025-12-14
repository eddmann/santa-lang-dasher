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
            Expr::Infix { left, op, right } => {
                self.compile_binary(left, op, right, &expr.ty)
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
}
