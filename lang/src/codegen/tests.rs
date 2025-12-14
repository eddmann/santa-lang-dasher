use inkwell::context::Context;
use crate::parser::ast::{Expr, InfixOp};
use crate::lexer::token::{Span, Position};
use crate::types::{TypedExpr, Type};

#[test]
fn codegen_context_creation() {
    let context = Context::create();
    let _codegen = super::context::CodegenContext::new(&context, "test_module");
}

#[test]
fn codegen_integer_literal() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");

    // Create typed expression for integer literal 42
    let expr = TypedExpr {
        expr: Expr::Integer(42),
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 2)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr).unwrap();

    // Verify it's an i64 constant with the right tagged value
    // Integer 42 should be tagged as: (42 << 3) | 0b001 = 336 + 1 = 337
    assert!(result.is_int_value());
    let int_val = result.into_int_value();
    assert_eq!(int_val.get_type().get_bit_width(), 64);
}

#[test]
fn codegen_int_add_int_specialized() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");

    // Create a test function to position the builder
    codegen.create_test_function();

    // Create typed expression for: 1 + 2
    // Both operands are known to be Int, so we should generate native LLVM add
    let left = TypedExpr {
        expr: Expr::Integer(1),
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 1)),
    };

    let right = TypedExpr {
        expr: Expr::Integer(2),
        ty: Type::Int,
        span: Span::new(Position::new(1, 5), Position::new(1, 5)),
    };

    let expr = TypedExpr {
        expr: Expr::Infix {
            left: Box::new(left.expr.clone()),
            op: InfixOp::Add,
            right: Box::new(right.expr.clone()),
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 5)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr).unwrap();

    // Verify it's an i64 value (result of the addition)
    assert!(result.is_int_value());
    let int_val = result.into_int_value();
    assert_eq!(int_val.get_type().get_bit_width(), 64);
}
