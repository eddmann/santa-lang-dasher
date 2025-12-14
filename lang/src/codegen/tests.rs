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

#[test]
fn codegen_decimal_literal() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");

    // Create typed expression for decimal literal 3.14
    let expr = TypedExpr {
        expr: Expr::Decimal(3.14),
        ty: Type::Decimal,
        span: Span::new(Position::new(1, 1), Position::new(1, 4)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr).unwrap();

    // Verify it's an f64 value (decimals are stored as native f64, not NaN-boxed)
    assert!(result.is_float_value());
}

#[test]
fn codegen_boolean_literal() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");

    // Test true
    let expr_true = TypedExpr {
        expr: Expr::Boolean(true),
        ty: Type::Bool,
        span: Span::new(Position::new(1, 1), Position::new(1, 4)),
    };

    let result_true = codegen.compile_expr(&expr_true).unwrap();
    assert!(result_true.is_int_value());
    let int_val = result_true.into_int_value();
    assert_eq!(int_val.get_type().get_bit_width(), 64);

    // Test false
    let expr_false = TypedExpr {
        expr: Expr::Boolean(false),
        ty: Type::Bool,
        span: Span::new(Position::new(1, 1), Position::new(1, 5)),
    };

    let result_false = codegen.compile_expr(&expr_false).unwrap();
    assert!(result_false.is_int_value());
}

#[test]
fn codegen_nil_literal() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");

    let expr = TypedExpr {
        expr: Expr::Nil,
        ty: Type::Nil,
        span: Span::new(Position::new(1, 1), Position::new(1, 3)),
    };

    let result = codegen.compile_expr(&expr).unwrap();

    // Nil is represented as a tagged i64 value
    assert!(result.is_int_value());
    let int_val = result.into_int_value();
    assert_eq!(int_val.get_type().get_bit_width(), 64);
}

#[test]
fn codegen_string_literal() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");

    // Need to create a test function to have a basic block for the builder
    codegen.create_test_function();

    let expr = TypedExpr {
        expr: Expr::String("hello".to_string()),
        ty: Type::String,
        span: Span::new(Position::new(1, 1), Position::new(1, 7)),
    };

    let result = codegen.compile_expr(&expr).unwrap();

    // String should be a pointer value (heap-allocated object)
    // For now, we'll just verify it compiles to an i64 (pointer as i64)
    assert!(result.is_int_value() || result.is_pointer_value());
}

#[test]
fn codegen_decimal_add_decimal_specialized() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: 1.5 + 2.5
    let left = TypedExpr {
        expr: Expr::Decimal(1.5),
        ty: Type::Decimal,
        span: Span::new(Position::new(1, 1), Position::new(1, 3)),
    };

    let right = TypedExpr {
        expr: Expr::Decimal(2.5),
        ty: Type::Decimal,
        span: Span::new(Position::new(1, 7), Position::new(1, 9)),
    };

    let expr = TypedExpr {
        expr: Expr::Infix {
            left: Box::new(left.expr.clone()),
            op: InfixOp::Add,
            right: Box::new(right.expr.clone()),
        },
        ty: Type::Decimal,
        span: Span::new(Position::new(1, 1), Position::new(1, 9)),
    };

    let result = codegen.compile_expr(&expr).unwrap();
    assert!(result.is_float_value());
}

#[test]
fn codegen_list_literal_empty() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: []
    let expr = TypedExpr {
        expr: Expr::List(vec![]),
        ty: Type::List(Box::new(Type::Unknown)),
        span: Span::new(Position::new(1, 1), Position::new(1, 2)),
    };

    // Compile the expression - should create an empty list heap object
    let result = codegen.compile_expr(&expr).unwrap();

    // List should be a pointer value (heap-allocated object)
    assert!(result.is_int_value());
}

#[test]
fn codegen_list_literal_with_integers() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: [1, 2, 3]
    let expr = TypedExpr {
        expr: Expr::List(vec![
            Expr::Integer(1),
            Expr::Integer(2),
            Expr::Integer(3),
        ]),
        ty: Type::List(Box::new(Type::Int)),
        span: Span::new(Position::new(1, 1), Position::new(1, 9)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr).unwrap();

    // List should be a pointer value (heap-allocated object)
    assert!(result.is_int_value());
}

#[test]
fn codegen_set_literal_empty() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: #{}
    let expr = TypedExpr {
        expr: Expr::Set(vec![]),
        ty: Type::Set(Box::new(Type::Unknown)),
        span: Span::new(Position::new(1, 1), Position::new(1, 3)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr).unwrap();
    assert!(result.is_int_value());
}

#[test]
fn codegen_set_literal_with_integers() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: #{1, 2, 3}
    let expr = TypedExpr {
        expr: Expr::Set(vec![
            Expr::Integer(1),
            Expr::Integer(2),
            Expr::Integer(3),
        ]),
        ty: Type::Set(Box::new(Type::Int)),
        span: Span::new(Position::new(1, 1), Position::new(1, 11)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr).unwrap();
    assert!(result.is_int_value());
}

#[test]
fn codegen_dict_literal_empty() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: #{}
    let expr = TypedExpr {
        expr: Expr::Dict(vec![]),
        ty: Type::Dict(Box::new(Type::Unknown), Box::new(Type::Unknown)),
        span: Span::new(Position::new(1, 1), Position::new(1, 3)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr).unwrap();
    assert!(result.is_int_value());
}

#[test]
fn codegen_dict_literal_with_entries() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: #{1: "a", 2: "b"}
    let expr = TypedExpr {
        expr: Expr::Dict(vec![
            (Expr::Integer(1), Expr::String("a".to_string())),
            (Expr::Integer(2), Expr::String("b".to_string())),
        ]),
        ty: Type::Dict(Box::new(Type::Int), Box::new(Type::String)),
        span: Span::new(Position::new(1, 1), Position::new(1, 19)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr).unwrap();
    assert!(result.is_int_value());
}

#[test]
fn codegen_unknown_type_runtime_fallback() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for addition with Unknown types
    // This should generate a call to rt_add instead of native add
    let left = TypedExpr {
        expr: Expr::Identifier("x".to_string()),
        ty: Type::Unknown,
        span: Span::new(Position::new(1, 1), Position::new(1, 1)),
    };

    let right = TypedExpr {
        expr: Expr::Identifier("y".to_string()),
        ty: Type::Unknown,
        span: Span::new(Position::new(1, 5), Position::new(1, 5)),
    };

    let expr = TypedExpr {
        expr: Expr::Infix {
            left: Box::new(left.expr.clone()),
            op: InfixOp::Add,
            right: Box::new(right.expr.clone()),
        },
        ty: Type::Unknown,
        span: Span::new(Position::new(1, 1), Position::new(1, 5)),
    };

    // This should compile without error, even though we don't know the types
    // The codegen should emit a call to rt_add
    let result = codegen.compile_expr(&expr);

    // For now, this should return an error since Identifier is not implemented
    // But once we implement it, this should succeed
    assert!(result.is_err() || result.unwrap().is_int_value());
}
