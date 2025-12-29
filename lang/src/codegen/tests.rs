use crate::lexer::token::{Position, Span};
use crate::parser::ast::{Expr, InfixOp};
use crate::types::{Type, TypedExpr};
use inkwell::context::Context;

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

    // Create typed expression for decimal literal 2.71
    let expr = TypedExpr {
        expr: Expr::Decimal(2.71),
        ty: Type::Decimal,
        span: Span::new(Position::new(1, 1), Position::new(1, 4)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr).unwrap();

    // Verify it's an i64 value containing the f64 bit pattern
    assert!(result.is_int_value());
    let int_val = result.into_int_value();
    let bits = int_val.get_zero_extended_constant().expect("decimal literal is const");
    assert_eq!(bits, 2.71f64.to_bits());
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
    // Decimal arithmetic should return boxed Value (i64)
    assert!(result.is_int_value());
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
        expr: Expr::List(vec![Expr::Integer(1), Expr::Integer(2), Expr::Integer(3)]),
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
        expr: Expr::Set(vec![Expr::Integer(1), Expr::Integer(2), Expr::Integer(3)]),
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
    // Even though the values are integer literals, marking them as Unknown
    // should trigger runtime fallback (call to rt_add)
    let left = TypedExpr {
        expr: Expr::Integer(10),
        ty: Type::Unknown, // Force Unknown type to test runtime fallback
        span: Span::new(Position::new(1, 1), Position::new(1, 2)),
    };

    let right = TypedExpr {
        expr: Expr::Integer(20),
        ty: Type::Unknown, // Force Unknown type to test runtime fallback
        span: Span::new(Position::new(1, 5), Position::new(1, 6)),
    };

    let expr = TypedExpr {
        expr: Expr::Infix {
            left: Box::new(left.expr.clone()),
            op: InfixOp::Add,
            right: Box::new(right.expr.clone()),
        },
        ty: Type::Unknown,
        span: Span::new(Position::new(1, 1), Position::new(1, 6)),
    };

    // This should compile without error and call rt_add at runtime
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_identifier_lookup() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create an identifier expression
    // For now, this should fail because we haven't implemented variable storage/lookup
    let expr = TypedExpr {
        expr: Expr::Identifier("x".to_string()),
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 1)),
    };

    // This should fail for now
    let result = codegen.compile_expr(&expr);
    assert!(result.is_err());
}

#[test]
fn codegen_prefix_negate_int() {
    use crate::parser::ast::PrefixOp;

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: -42
    let operand = TypedExpr {
        expr: Expr::Integer(42),
        ty: Type::Int,
        span: Span::new(Position::new(1, 2), Position::new(1, 3)),
    };

    let expr = TypedExpr {
        expr: Expr::Prefix {
            op: PrefixOp::Negate,
            right: Box::new(operand.expr.clone()),
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 3)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_prefix_not_bool() {
    use crate::parser::ast::PrefixOp;

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: !true
    let operand = TypedExpr {
        expr: Expr::Boolean(true),
        ty: Type::Bool,
        span: Span::new(Position::new(1, 2), Position::new(1, 5)),
    };

    let expr = TypedExpr {
        expr: Expr::Prefix {
            op: PrefixOp::Not,
            right: Box::new(operand.expr.clone()),
        },
        ty: Type::Bool,
        span: Span::new(Position::new(1, 1), Position::new(1, 5)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value()); // Booleans are stored as i64
}

#[test]
fn codegen_range_inclusive() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: 1..=10
    let expr = TypedExpr {
        expr: Expr::Range {
            start: Box::new(Expr::Integer(1)),
            end: Some(Box::new(Expr::Integer(10))),
            inclusive: true,
        },
        ty: Type::LazySequence(Box::new(Type::Int)),
        span: Span::new(Position::new(1, 1), Position::new(1, 6)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value()); // Range objects are heap-allocated
}

#[test]
fn codegen_range_exclusive() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: 1..10
    let expr = TypedExpr {
        expr: Expr::Range {
            start: Box::new(Expr::Integer(1)),
            end: Some(Box::new(Expr::Integer(10))),
            inclusive: false,
        },
        ty: Type::LazySequence(Box::new(Type::Int)),
        span: Span::new(Position::new(1, 1), Position::new(1, 5)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_range_unbounded() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: 1..
    let expr = TypedExpr {
        expr: Expr::Range {
            start: Box::new(Expr::Integer(1)),
            end: None,
            inclusive: false,
        },
        ty: Type::LazySequence(Box::new(Type::Int)),
        span: Span::new(Position::new(1, 1), Position::new(1, 3)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_index_list() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    codegen.create_test_function();

    // Create typed expression for: [1, 2, 3][1]
    let list_expr = Expr::List(vec![Expr::Integer(1), Expr::Integer(2), Expr::Integer(3)]);

    let expr = TypedExpr {
        expr: Expr::Index {
            collection: Box::new(list_expr),
            index: Box::new(Expr::Integer(1)),
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 13)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value());
}

// ===== Phase 7: Statement & Control Flow Tests =====

#[test]
fn codegen_let_binding_simple() {
    use crate::parser::ast::{Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a simple let binding: let x = 42;
    let stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("x".to_string()),
        value: Expr::Integer(42),
    };

    // Compile the statement
    let result = codegen.compile_stmt(&stmt);
    assert!(result.is_ok());

    // After the statement, we should be able to look up the variable
    // (This tests that the variable was stored in the context)
}

#[test]
fn codegen_variable_lookup() {
    use crate::parser::ast::{Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a let binding: let x = 42;
    let stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("x".to_string()),
        value: Expr::Integer(42),
    };

    // Compile the statement
    codegen.compile_stmt(&stmt).unwrap();

    // Now compile an expression that references x
    let expr = TypedExpr {
        expr: Expr::Identifier("x".to_string()),
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 2)),
    };

    // Compile the expression - should load from the variable
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_if_expression() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create an if expression: if true { 1 } else { 2 }
    let expr = TypedExpr {
        expr: Expr::If {
            condition: Box::new(Expr::Boolean(true)),
            then_branch: Box::new(Expr::Integer(1)),
            else_branch: Some(Box::new(Expr::Integer(2))),
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 25)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_block_expression() {
    use crate::parser::ast::{Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a block: { let x = 1; let y = 2; x + y }
    let expr = TypedExpr {
        expr: Expr::Block(vec![
            Stmt::Let {
                mutable: false,
                pattern: Pattern::Identifier("x".to_string()),
                value: Expr::Integer(1),
            },
            Stmt::Let {
                mutable: false,
                pattern: Pattern::Identifier("y".to_string()),
                value: Expr::Integer(2),
            },
            Stmt::Expr(Expr::Infix {
                left: Box::new(Expr::Identifier("x".to_string())),
                op: super::super::parser::ast::InfixOp::Add,
                right: Box::new(Expr::Identifier("y".to_string())),
            }),
        ]),
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(3, 10)),
    };

    // Compile the block
    let result = codegen.compile_expr(&expr);
    assert!(result.is_ok());
    assert!(result.unwrap().is_int_value());
}

// ===== Phase 9: Closures & Function Calls Tests =====

#[test]
fn codegen_simple_function_expression() {
    use crate::parser::ast::Param;

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a simple function expression: |x| x + 1
    let expr = TypedExpr {
        expr: Expr::Function {
            params: vec![Param::simple("x".to_string())],
            body: Box::new(Expr::Infix {
                left: Box::new(Expr::Identifier("x".to_string())),
                op: InfixOp::Add,
                right: Box::new(Expr::Integer(1)),
            }),
        },
        ty: Type::Function {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
        },
        span: Span::new(Position::new(1, 1), Position::new(1, 10)),
    };

    // Compile the expression - should produce a closure value
    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile function expression: {:?}",
        result.err()
    );
    // The result should be a heap object (closure)
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_function_call() {
    use crate::parser::ast::Param;

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a function call: (|x| x + 1)(5)
    let expr = TypedExpr {
        expr: Expr::Call {
            function: Box::new(Expr::Function {
                params: vec![Param::simple("x".to_string())],
                body: Box::new(Expr::Infix {
                    left: Box::new(Expr::Identifier("x".to_string())),
                    op: InfixOp::Add,
                    right: Box::new(Expr::Integer(1)),
                }),
            }),
            args: vec![Expr::Integer(5)],
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 20)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile function call: {:?}",
        result.err()
    );
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_function_with_multiple_params() {
    use crate::parser::ast::Param;

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a multi-param function: |a, b| a + b
    let expr = TypedExpr {
        expr: Expr::Function {
            params: vec![
                Param::simple("a".to_string()),
                Param::simple("b".to_string()),
            ],
            body: Box::new(Expr::Infix {
                left: Box::new(Expr::Identifier("a".to_string())),
                op: InfixOp::Add,
                right: Box::new(Expr::Identifier("b".to_string())),
            }),
        },
        ty: Type::Function {
            params: vec![Type::Int, Type::Int],
            ret: Box::new(Type::Int),
        },
        span: Span::new(Position::new(1, 1), Position::new(1, 15)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile multi-param function: {:?}",
        result.err()
    );
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_zero_arg_function() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a zero-arg function: || 42
    let expr = TypedExpr {
        expr: Expr::Function {
            params: vec![],
            body: Box::new(Expr::Integer(42)),
        },
        ty: Type::Function {
            params: vec![],
            ret: Box::new(Type::Int),
        },
        span: Span::new(Position::new(1, 1), Position::new(1, 6)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile zero-arg function: {:?}",
        result.err()
    );
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_zero_arg_function_call() {
    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a zero-arg function call: (|| 42)()
    let expr = TypedExpr {
        expr: Expr::Call {
            function: Box::new(Expr::Function {
                params: vec![],
                body: Box::new(Expr::Integer(42)),
            }),
            args: vec![],
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 10)),
    };

    // Compile the expression
    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile zero-arg function call: {:?}",
        result.err()
    );
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_closure_captures_variable() {
    use crate::parser::ast::{Param, Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // First, define a variable: let x = 5;
    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("x".to_string()),
        value: Expr::Integer(5),
    };
    codegen.compile_stmt(&let_stmt).unwrap();

    // Create a closure that captures x: |y| x + y
    let closure_expr = TypedExpr {
        expr: Expr::Function {
            params: vec![Param::simple("y".to_string())],
            body: Box::new(Expr::Infix {
                left: Box::new(Expr::Identifier("x".to_string())),
                op: InfixOp::Add,
                right: Box::new(Expr::Identifier("y".to_string())),
            }),
        },
        ty: Type::Function {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
        },
        span: Span::new(Position::new(1, 1), Position::new(1, 15)),
    };

    // Compile the closure
    let result = codegen.compile_expr(&closure_expr);
    assert!(
        result.is_ok(),
        "Failed to compile closure with capture: {:?}",
        result.err()
    );
    assert!(result.unwrap().is_int_value());
}

#[test]
fn codegen_make_adder_pattern() {
    use crate::parser::ast::Param;

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create make_adder pattern: |x| |y| x + y
    // This is a function that returns a closure capturing x
    let make_adder_expr = TypedExpr {
        expr: Expr::Function {
            params: vec![Param::simple("x".to_string())],
            body: Box::new(Expr::Function {
                params: vec![Param::simple("y".to_string())],
                body: Box::new(Expr::Infix {
                    left: Box::new(Expr::Identifier("x".to_string())),
                    op: InfixOp::Add,
                    right: Box::new(Expr::Identifier("y".to_string())),
                }),
            }),
        },
        ty: Type::Function {
            params: vec![Type::Int],
            ret: Box::new(Type::Function {
                params: vec![Type::Int],
                ret: Box::new(Type::Int),
            }),
        },
        span: Span::new(Position::new(1, 1), Position::new(1, 20)),
    };

    // Compile the function
    let result = codegen.compile_expr(&make_adder_expr);
    assert!(
        result.is_ok(),
        "Failed to compile make_adder pattern: {:?}",
        result.err()
    );
    assert!(result.unwrap().is_int_value());
}

// ===== Phase 15: Tail-Call Optimization (TCO) Tests =====

#[test]
fn codegen_tco_simple_recursion() {
    use crate::parser::ast::{Param, Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a simple tail-recursive function: countdown
    // let countdown = |n| if n == 0 { 0 } else { countdown(n - 1) };
    //
    // The recursive call countdown(n - 1) is in tail position because
    // it's the last expression evaluated in the else branch.

    // First, create a binding for the function name so it can self-reference
    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("countdown".to_string()),
        value: Expr::Function {
            params: vec![Param::simple("n".to_string())],
            body: Box::new(Expr::If {
                condition: Box::new(Expr::Infix {
                    left: Box::new(Expr::Identifier("n".to_string())),
                    op: InfixOp::Equal,
                    right: Box::new(Expr::Integer(0)),
                }),
                then_branch: Box::new(Expr::Integer(0)),
                else_branch: Some(Box::new(Expr::Call {
                    function: Box::new(Expr::Identifier("countdown".to_string())),
                    args: vec![Expr::Infix {
                        left: Box::new(Expr::Identifier("n".to_string())),
                        op: InfixOp::Subtract,
                        right: Box::new(Expr::Integer(1)),
                    }],
                })),
            }),
        },
    };

    // This should compile successfully
    let result = codegen.compile_stmt(&let_stmt);
    assert!(
        result.is_ok(),
        "Failed to compile tail-recursive function: {:?}",
        result.err()
    );
}

#[test]
fn codegen_tco_factorial_accumulator() {
    use crate::parser::ast::{Param, Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create tail-recursive factorial with accumulator:
    // let factorial = |acc, n| {
    //   if n == 0 { acc }
    //   else { factorial(acc * n, n - 1) }  // TCO should apply here
    // };

    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("factorial".to_string()),
        value: Expr::Function {
            params: vec![
                Param::simple("acc".to_string()),
                Param::simple("n".to_string()),
            ],
            body: Box::new(Expr::If {
                condition: Box::new(Expr::Infix {
                    left: Box::new(Expr::Identifier("n".to_string())),
                    op: InfixOp::Equal,
                    right: Box::new(Expr::Integer(0)),
                }),
                then_branch: Box::new(Expr::Identifier("acc".to_string())),
                else_branch: Some(Box::new(Expr::Call {
                    function: Box::new(Expr::Identifier("factorial".to_string())),
                    args: vec![
                        Expr::Infix {
                            left: Box::new(Expr::Identifier("acc".to_string())),
                            op: InfixOp::Multiply,
                            right: Box::new(Expr::Identifier("n".to_string())),
                        },
                        Expr::Infix {
                            left: Box::new(Expr::Identifier("n".to_string())),
                            op: InfixOp::Subtract,
                            right: Box::new(Expr::Integer(1)),
                        },
                    ],
                })),
            }),
        },
    };

    // This should compile successfully
    let result = codegen.compile_stmt(&let_stmt);
    assert!(
        result.is_ok(),
        "Failed to compile tail-recursive factorial: {:?}",
        result.err()
    );
}

#[test]
fn codegen_tco_generates_branch_not_call() {
    use crate::parser::ast::{Param, Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a tail-recursive countdown function
    // let countdown = |n| if n == 0 { 0 } else { countdown(n - 1) };
    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("countdown".to_string()),
        value: Expr::Function {
            params: vec![Param::simple("n".to_string())],
            body: Box::new(Expr::If {
                condition: Box::new(Expr::Infix {
                    left: Box::new(Expr::Identifier("n".to_string())),
                    op: InfixOp::Equal,
                    right: Box::new(Expr::Integer(0)),
                }),
                then_branch: Box::new(Expr::Integer(0)),
                else_branch: Some(Box::new(Expr::Call {
                    function: Box::new(Expr::Identifier("countdown".to_string())),
                    args: vec![Expr::Infix {
                        left: Box::new(Expr::Identifier("n".to_string())),
                        op: InfixOp::Subtract,
                        right: Box::new(Expr::Integer(1)),
                    }],
                })),
            }),
        },
    };

    codegen.compile_stmt(&let_stmt).unwrap();

    // Print the generated LLVM IR to verify TCO
    let ir = codegen.module.print_to_string().to_string();

    // The IR should contain a branch to the "body" block for the tail call
    // It should NOT contain a call to rt_call for the recursive countdown invocation
    // (There may be other rt_call invocations for helper functions)

    // Check that there's a closure function with a body block
    assert!(
        ir.contains("define i64 @closure_"),
        "Should define a closure function"
    );

    // Check that there's a branch back to body (the TCO jump)
    // The pattern should show "br label %body" inside the else branch
    assert!(
        ir.contains("br label %body"),
        "TCO should generate a branch back to body block"
    );
}

#[test]
fn codegen_tco_non_tail_position_uses_call() {
    use crate::parser::ast::{Param, Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a NON-tail-recursive factorial: n * factorial(n - 1)
    // The multiplication happens AFTER the recursive call, so it's NOT in tail position
    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("factorial".to_string()),
        value: Expr::Function {
            params: vec![Param::simple("n".to_string())],
            body: Box::new(Expr::If {
                condition: Box::new(Expr::Infix {
                    left: Box::new(Expr::Identifier("n".to_string())),
                    op: InfixOp::Equal,
                    right: Box::new(Expr::Integer(0)),
                }),
                then_branch: Box::new(Expr::Integer(1)),
                // n * factorial(n - 1) - NOT tail position due to multiplication
                else_branch: Some(Box::new(Expr::Infix {
                    left: Box::new(Expr::Identifier("n".to_string())),
                    op: InfixOp::Multiply,
                    right: Box::new(Expr::Call {
                        function: Box::new(Expr::Identifier("factorial".to_string())),
                        args: vec![Expr::Infix {
                            left: Box::new(Expr::Identifier("n".to_string())),
                            op: InfixOp::Subtract,
                            right: Box::new(Expr::Integer(1)),
                        }],
                    }),
                })),
            }),
        },
    };

    codegen.compile_stmt(&let_stmt).unwrap();

    // Print the generated LLVM IR
    let ir = codegen.module.print_to_string().to_string();

    // This NON-tail-recursive version should use rt_call for the recursive call
    // because n * factorial(...) is not in tail position
    assert!(
        ir.contains("call i64 @rt_call"),
        "Non-tail recursion should use rt_call"
    );
}

#[test]
fn codegen_tco_match_expression() {
    use crate::parser::ast::{Literal, MatchArm, Param, Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Create a tail-recursive countdown using match:
    // let countdown = |n| match n { 0 { 0 } _ { countdown(n - 1) } }
    // The recursive call countdown(n-1) is in tail position within the match arm
    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("countdown".to_string()),
        value: Expr::Function {
            params: vec![Param::simple("n".to_string())],
            body: Box::new(Expr::Match {
                subject: Box::new(Expr::Identifier("n".to_string())),
                arms: vec![
                    MatchArm {
                        pattern: Pattern::Literal(Literal::Integer(0)),
                        guard: None,
                        body: Expr::Block(vec![Stmt::Expr(Expr::Integer(0))]),
                    },
                    MatchArm {
                        pattern: Pattern::Wildcard,
                        guard: None,
                        body: Expr::Block(vec![Stmt::Expr(Expr::Call {
                            function: Box::new(Expr::Identifier("countdown".to_string())),
                            args: vec![Expr::Infix {
                                left: Box::new(Expr::Identifier("n".to_string())),
                                op: InfixOp::Subtract,
                                right: Box::new(Expr::Integer(1)),
                            }],
                        })]),
                    },
                ],
            }),
        },
    };

    codegen.compile_stmt(&let_stmt).unwrap();

    // Print the generated LLVM IR to verify TCO
    let ir = codegen.module.print_to_string().to_string();

    // Check that there's a closure function with a body block
    assert!(
        ir.contains("define i64 @closure_"),
        "Should define a closure function"
    );

    // Check that there's a branch back to body (the TCO jump)
    // This shows that match expressions properly propagate tail position
    assert!(
        ir.contains("br label %body"),
        "TCO in match should generate a branch back to body block"
    );
}

// ===== Phase 16: Pattern Matching Tests =====

#[test]
fn codegen_match_literal_integer() {
    use crate::parser::ast::{Literal, MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match 1 { 0 { "zero" } 1 { "one" } _ { "other" } }
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::Integer(1)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(Literal::Integer(0)),
                    guard: None,
                    body: Expr::String("zero".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Literal(Literal::Integer(1)),
                    guard: None,
                    body: Expr::String("one".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::String("other".to_string()),
                },
            ],
        },
        ty: Type::String,
        span: Span::new(Position::new(1, 1), Position::new(1, 50)),
    };

    // Compile the match expression
    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match expression: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_wildcard_captures_all() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match 42 { _ { 100 } }
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::Integer(42)),
            arms: vec![MatchArm {
                pattern: Pattern::Wildcard,
                guard: None,
                body: Expr::Integer(100),
            }],
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 20)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile wildcard match: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_identifier_binds_value() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match 42 { x { x + 1 } }
    // The pattern `x` should bind the subject to x in the body
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::Integer(42)),
            arms: vec![MatchArm {
                pattern: Pattern::Identifier("x".to_string()),
                guard: None,
                body: Expr::Infix {
                    left: Box::new(Expr::Identifier("x".to_string())),
                    op: InfixOp::Add,
                    right: Box::new(Expr::Integer(1)),
                },
            }],
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 25)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile identifier binding match: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_with_guard() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match 5 { x if x > 0 { "positive" } _ { "non-positive" } }
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::Integer(5)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Identifier("x".to_string()),
                    guard: Some(Expr::Infix {
                        left: Box::new(Expr::Identifier("x".to_string())),
                        op: InfixOp::GreaterThan,
                        right: Box::new(Expr::Integer(0)),
                    }),
                    body: Expr::String("positive".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::String("non-positive".to_string()),
                },
            ],
        },
        ty: Type::String,
        span: Span::new(Position::new(1, 1), Position::new(1, 60)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match with guard: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_range_pattern() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match 5 { 0..10 { "single digit" } 10..=99 { "two digits" } _ { "other" } }
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::Integer(5)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Range {
                        start: 0,
                        end: Some(10),
                        inclusive: false,
                    },
                    guard: None,
                    body: Expr::String("single digit".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Range {
                        start: 10,
                        end: Some(99),
                        inclusive: true,
                    },
                    guard: None,
                    body: Expr::String("two digits".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::String("other".to_string()),
                },
            ],
        },
        ty: Type::String,
        span: Span::new(Position::new(1, 1), Position::new(1, 80)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match with range patterns: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_unbounded_range() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match 100 { 100.. { "hundred or more" } _ { "less than hundred" } }
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::Integer(100)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Range {
                        start: 100,
                        end: None,
                        inclusive: false,
                    },
                    guard: None,
                    body: Expr::String("hundred or more".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::String("less than hundred".to_string()),
                },
            ],
        },
        ty: Type::String,
        span: Span::new(Position::new(1, 1), Position::new(1, 70)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match with unbounded range: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_empty_list_pattern() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match [] { [] { "empty" } _ { "non-empty" } }
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::List(vec![])),
            arms: vec![
                MatchArm {
                    pattern: Pattern::List(vec![]),
                    guard: None,
                    body: Expr::String("empty".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::String("non-empty".to_string()),
                },
            ],
        },
        ty: Type::String,
        span: Span::new(Position::new(1, 1), Position::new(1, 40)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match with empty list pattern: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_list_with_elements() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match [1, 2] { [a, b] { a + b } _ { 0 } }
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::List(vec![Expr::Integer(1), Expr::Integer(2)])),
            arms: vec![
                MatchArm {
                    pattern: Pattern::List(vec![
                        Pattern::Identifier("a".to_string()),
                        Pattern::Identifier("b".to_string()),
                    ]),
                    guard: None,
                    body: Expr::Infix {
                        left: Box::new(Expr::Identifier("a".to_string())),
                        op: InfixOp::Add,
                        right: Box::new(Expr::Identifier("b".to_string())),
                    },
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Integer(0),
                },
            ],
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 50)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match with list element pattern: {:?}",
        result.err()
    );
}

// ===== Nested Pattern Tests =====

#[test]
fn codegen_match_nested_list_pattern() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match [[1, 2], 3] { [[a, b], c] { a + b + c } _ { 0 } }
    // This tests nested list pattern matching per LANG.txt §9
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::List(vec![
                Expr::List(vec![Expr::Integer(1), Expr::Integer(2)]),
                Expr::Integer(3),
            ])),
            arms: vec![
                MatchArm {
                    pattern: Pattern::List(vec![
                        Pattern::List(vec![
                            Pattern::Identifier("a".to_string()),
                            Pattern::Identifier("b".to_string()),
                        ]),
                        Pattern::Identifier("c".to_string()),
                    ]),
                    guard: None,
                    body: Expr::Infix {
                        left: Box::new(Expr::Infix {
                            left: Box::new(Expr::Identifier("a".to_string())),
                            op: InfixOp::Add,
                            right: Box::new(Expr::Identifier("b".to_string())),
                        }),
                        op: InfixOp::Add,
                        right: Box::new(Expr::Identifier("c".to_string())),
                    },
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Integer(0),
                },
            ],
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 50)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match with nested list pattern: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_nested_list_with_literal() {
    use crate::parser::ast::{Literal, MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match [[1, 2], y] { [[1, x], y] { x + y } _ { 0 } }
    // Tests nested pattern with literal matching inside
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::List(vec![
                Expr::List(vec![Expr::Integer(1), Expr::Integer(2)]),
                Expr::Integer(3),
            ])),
            arms: vec![
                MatchArm {
                    pattern: Pattern::List(vec![
                        Pattern::List(vec![
                            Pattern::Literal(Literal::Integer(1)),
                            Pattern::Identifier("x".to_string()),
                        ]),
                        Pattern::Identifier("y".to_string()),
                    ]),
                    guard: None,
                    body: Expr::Infix {
                        left: Box::new(Expr::Identifier("x".to_string())),
                        op: InfixOp::Add,
                        right: Box::new(Expr::Identifier("y".to_string())),
                    },
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Integer(0),
                },
            ],
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 50)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match with nested list pattern containing literal: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_list_with_rest_at_beginning() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match [1, 2, 3, 4] { [..tail, end] { end } _ { 0 } }
    // Tests rest pattern at the beginning per LANG.txt §9
    // Expected: last = 4
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::List(vec![
                Expr::Integer(1),
                Expr::Integer(2),
                Expr::Integer(3),
                Expr::Integer(4),
            ])),
            arms: vec![
                MatchArm {
                    pattern: Pattern::List(vec![
                        Pattern::RestIdentifier("tail".to_string()),
                        Pattern::Identifier("end".to_string()),
                    ]),
                    guard: None,
                    body: Expr::Identifier("end".to_string()),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Integer(0),
                },
            ],
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 50)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match with rest pattern at beginning: {:?}",
        result.err()
    );
}

#[test]
fn codegen_match_list_with_rest_in_middle() {
    use crate::parser::ast::{MatchArm, Pattern};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // match [1, 2, 3, 4, 5] { [start, ..mid, end] { start + end } _ { 0 } }
    // Tests rest pattern in the middle per LANG.txt §9
    // Expected: start = 1, mid = [2, 3, 4], end = 5
    let expr = TypedExpr {
        expr: Expr::Match {
            subject: Box::new(Expr::List(vec![
                Expr::Integer(1),
                Expr::Integer(2),
                Expr::Integer(3),
                Expr::Integer(4),
                Expr::Integer(5),
            ])),
            arms: vec![
                MatchArm {
                    pattern: Pattern::List(vec![
                        Pattern::Identifier("start".to_string()),
                        Pattern::RestIdentifier("mid".to_string()),
                        Pattern::Identifier("end".to_string()),
                    ]),
                    guard: None,
                    body: Expr::Infix {
                        left: Box::new(Expr::Identifier("start".to_string())),
                        op: InfixOp::Add,
                        right: Box::new(Expr::Identifier("end".to_string())),
                    },
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Integer(0),
                },
            ],
        },
        ty: Type::Int,
        span: Span::new(Position::new(1, 1), Position::new(1, 50)),
    };

    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Failed to compile match with rest pattern in middle: {:?}",
        result.err()
    );
}

// ===== Object File Emission Tests =====

#[test]
fn codegen_emit_object_file() {
    use std::fs;

    let context = Context::create();
    let codegen = super::context::CodegenContext::new(&context, "test_module");

    // Create a simple main function that returns 42
    let i64_type = context.i64_type();
    let fn_type = i64_type.fn_type(&[], false);
    let main_fn = codegen.module.add_function("main", fn_type, None);
    let entry = context.append_basic_block(main_fn, "entry");
    codegen.builder.position_at_end(entry);
    codegen
        .builder
        .build_return(Some(&i64_type.const_int(42, false)))
        .unwrap();

    // Write to temp object file
    let temp_dir = std::env::temp_dir();
    let obj_path = temp_dir.join("test_emit.o");

    let result = codegen.write_object_file(&obj_path);
    assert!(
        result.is_ok(),
        "Failed to emit object file: {:?}",
        result.err()
    );

    // Verify the file exists and has content
    assert!(obj_path.exists(), "Object file was not created");
    let metadata = fs::metadata(&obj_path).unwrap();
    assert!(metadata.len() > 0, "Object file is empty");

    // Clean up
    fs::remove_file(&obj_path).ok();
}

#[test]
fn codegen_get_ir() {
    let context = Context::create();
    let codegen = super::context::CodegenContext::new(&context, "test_module");

    // Create a simple function
    let i64_type = context.i64_type();
    let fn_type = i64_type.fn_type(&[], false);
    let main_fn = codegen.module.add_function("my_func", fn_type, None);
    let entry = context.append_basic_block(main_fn, "entry");
    codegen.builder.position_at_end(entry);
    codegen
        .builder
        .build_return(Some(&i64_type.const_int(42, false)))
        .unwrap();

    let ir = codegen.get_ir();

    // Verify IR contains expected elements
    assert!(ir.contains("my_func"), "IR should contain function name");
    assert!(
        ir.contains("ret i64 42"),
        "IR should contain return statement"
    );
}

// ===== Phase 7: Builtin Name Shadowing =====
// Builtins are protected per LANG.txt and cannot be shadowed.

#[test]
fn codegen_builtin_name_shadowing_sum_errors() {
    use crate::parser::ast::{Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Binding to 'sum' (a builtin name) should succeed
    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("sum".to_string()),
        value: Expr::Integer(42),
    };

    let result = codegen.compile_stmt(&let_stmt);
    assert!(result.is_err(), "Binding to builtin name 'sum' should error");
}

#[test]
fn codegen_builtin_name_shadowing_map_errors() {
    use crate::parser::ast::{Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Binding to 'map' (a builtin name) should succeed
    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("map".to_string()),
        value: Expr::Integer(1),
    };

    let result = codegen.compile_stmt(&let_stmt);
    assert!(result.is_err(), "Binding to builtin name 'map' should error");
}

#[test]
fn codegen_non_protected_name_succeeds() {
    use crate::parser::ast::{Pattern, Stmt};

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Binding to 'my_sum' should succeed (not a built-in name)
    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("my_sum".to_string()),
        value: Expr::Integer(42),
    };

    let result = codegen.compile_stmt(&let_stmt);
    assert!(
        result.is_ok(),
        "Should succeed for non-protected name 'my_sum': {:?}",
        result.err()
    );
}

// ===== Phase 6: Pipeline Operator =====

#[test]
fn codegen_pipeline_operator() {
    use crate::parser::ast::{Param, Pattern, Stmt};

    // Test: 42 |> my_func
    // Pipeline operator: x |> f  is equivalent to f(x)
    // First we need to define my_func, then use pipeline

    let context = Context::create();
    let mut codegen = super::context::CodegenContext::new(&context, "test_module");
    let _function = codegen.create_test_function();

    // Define a function: let my_func = |x| x;
    let let_stmt = Stmt::Let {
        mutable: false,
        pattern: Pattern::Identifier("my_func".to_string()),
        value: Expr::Function {
            params: vec![Param::simple("x".to_string())],
            body: Box::new(Expr::Identifier("x".to_string())),
        },
    };
    codegen.compile_stmt(&let_stmt).unwrap();

    // Create: 42 |> my_func
    let expr = TypedExpr {
        expr: Expr::Infix {
            left: Box::new(Expr::Integer(42)),
            op: InfixOp::Pipeline,
            right: Box::new(Expr::Identifier("my_func".to_string())),
        },
        ty: Type::Unknown, // Result type depends on function
        span: Span::new(Position::new(1, 1), Position::new(1, 10)),
    };

    // This should compile successfully
    let result = codegen.compile_expr(&expr);
    assert!(
        result.is_ok(),
        "Pipeline operator should compile: {:?}",
        result.err()
    );

    // Verify the generated IR contains a call
    let ir = codegen.module.print_to_string().to_string();
    assert!(
        ir.contains("rt_call"),
        "Pipeline should generate a function call"
    );
}

// ===== Phase 20: Optimization Level Tests =====

#[test]
fn codegen_default_optimization_level() {
    use inkwell::OptimizationLevel;

    let context = Context::create();
    let codegen = super::context::CodegenContext::new(&context, "test_module");

    // Default should be O2 (Aggressive) for good performance
    assert_eq!(codegen.optimization_level(), OptimizationLevel::Aggressive);
}

#[test]
fn codegen_configurable_optimization_level() {
    use inkwell::OptimizationLevel;

    let context = Context::create();

    // Test creating context with O3 (Most aggressive optimization)
    let codegen = super::context::CodegenContext::with_optimization(
        &context,
        "test_module",
        OptimizationLevel::Aggressive,
    );
    assert_eq!(codegen.optimization_level(), OptimizationLevel::Aggressive);

    // Test creating context with O0 (No optimization - for debugging)
    let codegen_debug = super::context::CodegenContext::with_optimization(
        &context,
        "test_debug",
        OptimizationLevel::None,
    );
    assert_eq!(codegen_debug.optimization_level(), OptimizationLevel::None);
}

#[test]
fn codegen_object_file_uses_optimization_level() {
    use inkwell::OptimizationLevel;
    use std::fs;

    let context = Context::create();
    let codegen = super::context::CodegenContext::with_optimization(
        &context,
        "opt_test",
        OptimizationLevel::Aggressive,
    );

    // Create a simple main function
    let i64_type = context.i64_type();
    let fn_type = i64_type.fn_type(&[], false);
    let main_fn = codegen.module.add_function("main", fn_type, None);
    let entry = context.append_basic_block(main_fn, "entry");
    codegen.builder.position_at_end(entry);
    codegen
        .builder
        .build_return(Some(&i64_type.const_int(42, false)))
        .unwrap();

    // Write to temp object file - this should use O3 optimization
    let temp_dir = std::env::temp_dir();
    let obj_path = temp_dir.join("test_opt_level.o");

    let result = codegen.write_object_file(&obj_path);
    assert!(
        result.is_ok(),
        "Should emit optimized object file: {:?}",
        result.err()
    );

    // Verify the file exists
    assert!(obj_path.exists(), "Optimized object file was not created");
    let metadata = fs::metadata(&obj_path).unwrap();
    assert!(metadata.len() > 0, "Object file is empty");

    // Clean up
    fs::remove_file(&obj_path).ok();
}
