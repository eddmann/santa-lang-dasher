use crate::lexer::lex;
use crate::parser::ast::{Expr, Pattern};
use crate::parser::{parse, Parser};
use crate::types::infer::TypeInference;
use crate::types::ty::{Type, TypedProgram};

fn infer_type(source: &str) -> Type {
    let tokens = lex(source).unwrap();
    let expr = parse(tokens).unwrap();
    let mut inference = TypeInference::new();
    let typed_expr = inference.infer_expr(&expr).unwrap();
    typed_expr.ty
}

fn infer_program(source: &str) -> TypedProgram {
    let tokens = lex(source).unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap();
    let mut inference = TypeInference::new();
    inference.infer_program(&program).unwrap()
}

// ===== Literal Tests =====

#[test]
fn infer_integer_literal() {
    let ty = infer_type("42");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_decimal_literal() {
    let ty = infer_type("3.14");
    assert_eq!(ty, Type::Decimal);
}

#[test]
fn infer_string_literal() {
    let ty = infer_type("\"hello\"");
    assert_eq!(ty, Type::String);
}

#[test]
fn infer_boolean_literal() {
    let ty = infer_type("true");
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_nil_literal() {
    let ty = infer_type("nil");
    assert_eq!(ty, Type::Nil);
}

// ===== Binary Operator Tests =====

#[test]
fn infer_int_add_int() {
    // Per LANG.txt §4.1: Int + Int → Int
    let ty = infer_type("1 + 2");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_decimal_add_decimal() {
    // Per LANG.txt §4.1: Decimal + Decimal → Decimal
    let ty = infer_type("1.0 + 2.0");
    assert_eq!(ty, Type::Decimal);
}

#[test]
fn infer_int_add_decimal() {
    // Per LANG.txt §4.1: Left operand determines type
    let ty = infer_type("1 + 2.0");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_decimal_add_int() {
    // Per LANG.txt §4.1: Left operand determines type
    let ty = infer_type("1.0 + 2");
    assert_eq!(ty, Type::Decimal);
}

#[test]
fn infer_int_multiply_int() {
    // Int * Int → Int
    let ty = infer_type("3 * 4");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_int_subtract_int() {
    // Int - Int → Int
    let ty = infer_type("10 - 3");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_int_divide_int() {
    // Int / Int → Int (floored division)
    let ty = infer_type("7 / 2");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_int_modulo_int() {
    // Int % Int → Int
    let ty = infer_type("7 % 3");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_comparison_returns_bool() {
    // Comparison operators return Bool
    let ty = infer_type("1 < 2");
    assert_eq!(ty, Type::Bool);

    let ty = infer_type("1 <= 2");
    assert_eq!(ty, Type::Bool);

    let ty = infer_type("1 > 2");
    assert_eq!(ty, Type::Bool);

    let ty = infer_type("1 >= 2");
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_equality_returns_bool() {
    // Equality operators return Bool
    let ty = infer_type("1 == 2");
    assert_eq!(ty, Type::Bool);

    let ty = infer_type("1 != 2");
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_logical_and_or() {
    // Logical operators: Bool && Bool → Bool
    let ty = infer_type("true && false");
    assert_eq!(ty, Type::Bool);

    let ty = infer_type("true || false");
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_string_concatenation() {
    // String + X → String (type coercion)
    let ty = infer_type("\"hello\" + \"world\"");
    assert_eq!(ty, Type::String);
}

// ===== Collection Type Tests =====

#[test]
fn infer_list_of_integers() {
    // [1, 2, 3] → List<Int>
    let ty = infer_type("[1, 2, 3]");
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_list_of_strings() {
    // ["a", "b"] → List<String>
    let ty = infer_type("[\"a\", \"b\"]");
    assert_eq!(ty, Type::List(Box::new(Type::String)));
}

#[test]
fn infer_empty_list() {
    // [] → List<Unknown> (can't infer element type)
    let ty = infer_type("[]");
    assert_eq!(ty, Type::List(Box::new(Type::Unknown)));
}

#[test]
fn infer_set_of_integers() {
    // #{1, 2, 3} → Set<Int>
    let ty = infer_type("#{1, 2, 3}");
    assert_eq!(ty, Type::Set(Box::new(Type::Int)));
}

#[test]
fn infer_empty_set() {
    // {} → Set<Unknown> (empty braces in expression position)
    let ty = infer_type("{}");
    assert_eq!(ty, Type::Set(Box::new(Type::Unknown)));
}

#[test]
fn infer_dict_literal() {
    // #{1: "a", 2: "b"} → Dict<Int, String>
    let ty = infer_type("#{1: \"a\", 2: \"b\"}");
    assert_eq!(ty, Type::Dict(Box::new(Type::Int), Box::new(Type::String)));
}

#[test]
fn infer_range() {
    // 1..10 → LazySequence<Int>
    let ty = infer_type("1..10");
    assert_eq!(ty, Type::LazySequence(Box::new(Type::Int)));
}

// ===== Prefix Operator Tests =====

#[test]
fn infer_negation_int() {
    // -42 → Int
    let ty = infer_type("-42");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_negation_decimal() {
    // -3.14 → Decimal
    let ty = infer_type("-3.14");
    assert_eq!(ty, Type::Decimal);
}

#[test]
fn infer_not_bool() {
    // !true → Bool
    let ty = infer_type("!true");
    assert_eq!(ty, Type::Bool);
}

// ===== If Expression Tests =====

#[test]
fn infer_if_same_types() {
    // if true { 1 } else { 2 } → Int
    let ty = infer_type("if true { 1 } else { 2 }");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_no_else() {
    // if true { 1 } → Int (no else returns nil, but we unify with Int → Unknown or Int)
    // Per LANG.txt, if without else returns nil when condition is false
    // Result type should be Unknown since branches don't match
    let ty = infer_type("if true { 1 }");
    assert_eq!(ty, Type::Unknown);
}

#[test]
fn infer_if_mixed_branches() {
    // if cond { 1 } else { "x" } → Unknown (can't unify Int and String)
    let ty = infer_type("if true { 1 } else { \"x\" }");
    assert_eq!(ty, Type::Unknown);
}

// ===== Block Expression Tests =====

#[test]
fn infer_set_single_literal() {
    // { 42 } → Set<Int> (single literal in braces is a Set)
    let ty = infer_type("{ 42 }");
    assert_eq!(ty, Type::Set(Box::new(Type::Int)));
}

#[test]
fn infer_set_single_computed_expr() {
    // { 1 + 1 } → Set<Int> (expression position braces are set literals)
    let ty = infer_type("{ 1 + 1 }");
    assert_eq!(ty, Type::Set(Box::new(Type::Int)));
}

#[test]
fn infer_block_multiple_exprs() {
    // { 1; 2; 3 } → Int (last expression's type)
    let ty = infer_type("{ 1; 2; 3 }");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_empty_braces_in_expression_position() {
    // { } in expression position → Set<Unknown> (per PLAN.md §3.5)
    // Empty braces are disambiguated as Set when in expression context
    let ty = infer_type("{}");
    assert_eq!(ty, Type::Set(Box::new(Type::Unknown)));
}

// ===== Identifier Tests =====

#[test]
fn infer_unknown_identifier() {
    // Undefined variable returns Unknown (will be looked up at runtime or is a builtin)
    let ty = infer_type("x");
    assert_eq!(ty, Type::Unknown);
}

// ===== Function Expression Tests =====

#[test]
fn infer_simple_lambda() {
    // |x| x + 1 → Function { params: [Unknown], ret: Unknown }
    // Without context, we can't infer parameter types
    let ty = infer_type("|x| x + 1");
    match ty {
        Type::Function { params, ret: _ } => {
            // Parameters should be Unknown without context
            assert_eq!(params.len(), 1);
        }
        _ => panic!("Expected Function type, got {:?}", ty),
    }
}

#[test]
fn infer_constant_lambda() {
    // || 42 → Function { params: [], ret: Int }
    let ty = infer_type("|| 42");
    assert_eq!(
        ty,
        Type::Function {
            params: vec![],
            ret: Box::new(Type::Int),
        }
    );
}

#[test]
fn infer_multi_param_lambda() {
    // |a, b| a + b → Function { params: [Unknown, Unknown], ret: Unknown }
    let ty = infer_type("|a, b| a + b");
    match ty {
        Type::Function { params, ret: _ } => {
            assert_eq!(params.len(), 2);
        }
        _ => panic!("Expected Function type, got {:?}", ty),
    }
}

// ===== Function Call Tests =====

#[test]
fn infer_builtin_int() {
    // int("42") → Int
    let ty = infer_type("int(\"42\")");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_builtin_size() {
    // size([1, 2, 3]) → Int
    let ty = infer_type("size([1, 2, 3])");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_builtin_lines() {
    // lines("a\nb") → List<String>
    let ty = infer_type("lines(\"a\\nb\")");
    assert_eq!(ty, Type::List(Box::new(Type::String)));
}

#[test]
fn infer_builtin_ints() {
    // ints("1 2 3") → List<Int>
    let ty = infer_type("ints(\"1 2 3\")");
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_builtin_first() {
    // first([1, 2, 3]) → Int (element type of List<Int>)
    let ty = infer_type("first([1, 2, 3])");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_builtin_filter() {
    // filter(|x| x > 0, [1, 2, 3]) → List<Int> (same type as input collection)
    let ty = infer_type("filter(|x| x > 0, [1, 2, 3])");
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_builtin_fold() {
    // fold(0, |a, b| a + b, [1, 2, 3]) → Int (same type as initial value)
    let ty = infer_type("fold(0, |a, b| a + b, [1, 2, 3])");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_unknown_function_call() {
    // unknown_fn(42) → Unknown (not a builtin)
    let ty = infer_type("unknown_fn(42)");
    assert_eq!(ty, Type::Unknown);
}

// ===== Pipeline Operator Tests =====

#[test]
fn infer_pipeline_to_builtin() {
    // "a\nb" |> lines → List<String>
    let ty = infer_type("\"a\\nb\" |> lines");
    assert_eq!(ty, Type::List(Box::new(Type::String)));
}

#[test]
fn infer_pipeline_chain() {
    // "1\n2" |> lines |> size → Int
    let ty = infer_type("\"1\\n2\" |> lines |> size");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_pipeline_with_partial_creates_function() {
    // filter(|x| x > 0, _) creates a partial application (function)
    // The _ placeholder makes the entire expression a partial application
    // So the result type is Function, not List<Int>
    let ty = infer_type("filter(|x| x > 0, _)");
    match ty {
        Type::Function { params, .. } => {
            // The partial has one parameter (the placeholder)
            assert_eq!(params.len(), 1);
        }
        _ => panic!("Expected Function type, got {:?}", ty),
    }
}

// ===== Index Expression Tests =====

#[test]
fn infer_list_index() {
    // [1, 2, 3][0] → Int
    let ty = infer_type("[1, 2, 3][0]");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_dict_index() {
    // #{"a": 1, "b": 2}["a"] → Int
    let ty = infer_type("#{\"a\": 1, \"b\": 2}[\"a\"]");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_string_index() {
    // "hello"[0] → String (single character)
    let ty = infer_type("\"hello\"[0]");
    assert_eq!(ty, Type::String);
}

#[test]
fn infer_nested_list_index() {
    // [[1, 2], [3, 4]][0] → List<Int>
    let ty = infer_type("[[1, 2], [3, 4]][0]");
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

// ===== Program Inference Tests =====

#[test]
fn infer_program_simple_statements() {
    // Program with just expression statements
    let program = infer_program("42");
    assert_eq!(program.statements.len(), 1);
    assert_eq!(program.statements[0].ty, Type::Int);
}

#[test]
fn infer_program_multiple_statements() {
    // Multiple statements, each gets a type
    let program = infer_program(
        r#"
let x = 1
let y = "hello"
x + 2
"#,
    );
    // 3 statements: let x, let y, expression x + 2
    assert_eq!(program.statements.len(), 3);
    // With proper let binding tracking, x should be Int, so x + 2 should be Int
    assert_eq!(
        program.statements[2].ty,
        Type::Int,
        "x + 2 should be Int since x is bound to Int"
    );
}

#[test]
fn infer_let_binding_tracks_type() {
    // let x = 1 should track x as Int in the environment
    // Then x + 2 should infer as Int (not Unknown)
    let program = infer_program("let x = 1\nx + 2");
    assert_eq!(program.statements.len(), 2);
    // Second statement (x + 2) should be Int because x is tracked as Int
    assert_eq!(program.statements[1].ty, Type::Int);
}

#[test]
fn infer_let_binding_string() {
    // let s = "hello" should track s as String
    let program = infer_program("let s = \"hello\"\ns + \" world\"");
    assert_eq!(program.statements.len(), 2);
    // String + String should be String
    assert_eq!(program.statements[1].ty, Type::String);
}

#[test]
fn infer_let_binding_list() {
    // let xs = [1, 2, 3] should track xs as List<Int>
    // Then first(xs) should return Int
    let program = infer_program("let xs = [1, 2, 3]\nfirst(xs)");
    assert_eq!(program.statements.len(), 2);
    assert_eq!(program.statements[1].ty, Type::Int);
}

#[test]
fn infer_let_binding_used_in_builtin() {
    // let xs = [1, 2, 3]
    // map(|x| x * 2, xs)
    // Lambda param should be inferred from xs's element type
    let program = infer_program("let xs = [1, 2, 3]\nmap(|x| x * 2, xs)");
    assert_eq!(program.statements.len(), 2);
    // map returns List<T> where T is the lambda return type
    // x * 2 where x: Int returns Int, so result is List<Int>
    assert_eq!(program.statements[1].ty, Type::List(Box::new(Type::Int)));
}

// ===== User-Defined Function Call Inference Tests =====
// These tests verify that calling user-defined functions infers proper return types

#[test]
fn infer_user_defined_function_call_int() {
    // let add = |a, b| a + b
    // add(1, 2)  → should infer as Int because 1 and 2 are Int
    let program = infer_program("let add = |a, b| a + b\nadd(1, 2)");
    assert_eq!(program.statements.len(), 2);
    // The call add(1, 2) should return Int
    assert_eq!(
        program.statements[1].ty,
        Type::Int,
        "add(1, 2) should be Int"
    );
}

#[test]
fn infer_user_defined_function_call_string() {
    // let greet = |name| "Hello, " + name
    // greet("World")  → should infer as String
    let program = infer_program("let greet = |name| \"Hello, \" + name\ngreet(\"World\")");
    assert_eq!(program.statements.len(), 2);
    assert_eq!(
        program.statements[1].ty,
        Type::String,
        "greet(\"World\") should be String"
    );
}

#[test]
fn infer_user_defined_function_call_with_comparison() {
    // let is_positive = |x| x > 0
    // is_positive(5)  → should infer as Bool
    let program = infer_program("let is_positive = |x| x > 0\nis_positive(5)");
    assert_eq!(program.statements.len(), 2);
    assert_eq!(
        program.statements[1].ty,
        Type::Bool,
        "is_positive(5) should be Bool"
    );
}

#[test]
fn infer_user_defined_function_nested_call() {
    // let double = |x| x * 2
    // let quad = |x| double(double(x))
    // quad(3)  → should infer as Int
    let program =
        infer_program("let double = |x| x * 2\nlet quad = |x| double(double(x))\nquad(3)");
    assert_eq!(program.statements.len(), 3);
    assert_eq!(program.statements[2].ty, Type::Int, "quad(3) should be Int");
}

#[test]
fn infer_user_defined_function_used_in_map() {
    // let double = |x| x * 2
    // map(double, [1, 2, 3])  → should infer as List<Int>
    let program = infer_program("let double = |x| x * 2\nmap(double, [1, 2, 3])");
    assert_eq!(program.statements.len(), 2);
    assert_eq!(
        program.statements[1].ty,
        Type::List(Box::new(Type::Int)),
        "map(double, [1,2,3]) should be List<Int>"
    );
}

// ===== Match Expression Type Inference Tests =====

#[test]
fn infer_match_all_int_arms() {
    // match 1 { 1 { 10 } 2 { 20 } _ { 0 } }
    // All arms return Int → result is Int
    let ty = infer_type("match 1 { 1 { 10 } 2 { 20 } _ { 0 } }");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_match_all_string_arms() {
    // match 1 { 1 { "one" } _ { "other" } }
    // All arms return String → result is String
    let ty = infer_type("match 1 { 1 { \"one\" } _ { \"other\" } }");
    assert_eq!(ty, Type::String);
}

#[test]
fn infer_match_with_variable_binding() {
    // match [1, 2, 3] { [x, ..rest] { x * 2 } _ { 0 } }
    // x is bound to first element (Int), x * 2 is Int
    let ty = infer_type("match [1, 2, 3] { [x, ..rest] { x * 2 } _ { 0 } }");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_match_with_guard() {
    // match 5 { x if x > 0 { x + 1 } _ { 0 } }
    // x is bound to subject (Int), x + 1 is Int
    let ty = infer_type("match 5 { x if x > 0 { x + 1 } _ { 0 } }");
    assert_eq!(ty, Type::Int);
}

// IfLet expression type inference
// Note: Parser doesn't support "if let" syntax yet, so we construct AST manually

fn infer_ast_type(expr: &Expr) -> Type {
    let mut inference = TypeInference::new();
    inference.infer_expr(expr).unwrap().ty
}

#[test]
fn infer_if_let_simple() {
    // if let x = 42 { x * 2 } else { 0 }
    // x is bound to Int, x * 2 is Int, else is Int, result is Int
    use crate::parser::ast::InfixOp;
    let expr = Expr::IfLet {
        pattern: Pattern::Identifier("x".to_string()),
        value: Box::new(Expr::Integer(42)),
        then_branch: Box::new(Expr::Infix {
            left: Box::new(Expr::Identifier("x".to_string())),
            op: InfixOp::Multiply,
            right: Box::new(Expr::Integer(2)),
        }),
        else_branch: Some(Box::new(Expr::Integer(0))),
    };
    let ty = infer_ast_type(&expr);
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_let_no_else() {
    // if let x = "hello" { x }
    // No else branch returns Nil when pattern doesn't match
    // Both branches should unify to String or Unknown
    let expr = Expr::IfLet {
        pattern: Pattern::Identifier("x".to_string()),
        value: Box::new(Expr::String("hello".to_string())),
        then_branch: Box::new(Expr::Identifier("x".to_string())),
        else_branch: None,
    };
    let ty = infer_ast_type(&expr);
    // With no else, result type is Unknown (can't unify String and Nil)
    assert_eq!(ty, Type::Unknown);
}

#[test]
fn infer_if_let_list_destructure() {
    // if let [a, ..rest] = [1, 2, 3] { a } else { 0 }
    // a is bound to Int (element type), result is Int
    let expr = Expr::IfLet {
        pattern: Pattern::List(vec![
            Pattern::Identifier("a".to_string()),
            Pattern::RestIdentifier("rest".to_string()),
        ]),
        value: Box::new(Expr::List(vec![
            Expr::Integer(1),
            Expr::Integer(2),
            Expr::Integer(3),
        ])),
        then_branch: Box::new(Expr::Identifier("a".to_string())),
        else_branch: Some(Box::new(Expr::Integer(0))),
    };
    let ty = infer_ast_type(&expr);
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_program_with_input_section() {
    // Program with input section
    let program = infer_program(
        r#"
input: "test data"
"#,
    );
    assert_eq!(program.sections.len(), 1);
    assert_eq!(program.sections[0].ty, Type::String);
}

#[test]
fn infer_program_with_part_one() {
    // Program with part_one section
    let program = infer_program(
        r#"
input: 42
part_one: input * 2
"#,
    );
    assert_eq!(program.sections.len(), 2);
    // input: 42 → Int
    assert_eq!(program.sections[0].ty, Type::Int);
    // part_one: input * 2 → Unknown (input not tracked in simple implementation)
}

// ===== Closure Parameter Type Inference Tests =====
// These tests verify that lambda parameters get their types inferred from context
// by checking that the body operations are correctly typed (which proves the params were typed)

#[test]
fn infer_lambda_param_from_filter_context() {
    // filter(|x| x > 0, [1, 2, 3])
    //   - [1, 2, 3] is List<Int>
    //   - filter's signature: (T -> Bool, List<T>) -> List<T>
    //   - Result: List<Int>
    //
    // The return type proves the inference worked: if the collection type wasn't
    // propagated through, we'd get Unknown instead of List<Int>
    let ty = infer_type("filter(|x| x > 0, [1, 2, 3])");
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_lambda_param_from_map_context() {
    // map(|x| x * 2, [1, 2, 3])
    //   - [1, 2, 3] is List<Int>
    //   - map's signature: (T -> U, List<T>) -> List<U>
    //   - x: Int (inferred from List<Int>), so x * 2: Int
    //   - Result: List<Int>
    //
    // The return type List<Int> proves that:
    // 1. The lambda was correctly typed as (Int) -> Int
    // 2. x was inferred as Int (otherwise x * 2 would be Unknown)
    // 3. The map result type used the lambda's return type
    let ty = infer_type("map(|x| x * 2, [1, 2, 3])");
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_lambda_param_from_map_unknown_without_context() {
    // Without collection type information, x * 2 would be Unknown
    // This test verifies that bidirectional inference is actually doing something:
    // |x| x * 2 alone has Unknown parameter type, giving Unknown result
    let ty = infer_type("|x| x * 2");
    match ty {
        Type::Function { params, ret } => {
            assert_eq!(
                params[0],
                Type::Unknown,
                "Without context, param should be Unknown"
            );
            assert_eq!(
                *ret,
                Type::Unknown,
                "Without context, Unknown * Int = Unknown"
            );
        }
        _ => panic!("Expected Function type"),
    }
}

#[test]
fn infer_lambda_param_from_fold_context() {
    // fold(0, |acc, x| acc + x, [1, 2, 3])
    //   - initial = 0: Int
    //   - [1, 2, 3] is List<Int>
    //   - fold's signature: (T, (T, U) -> T, List<U>) -> T
    //   - acc: Int (from initial), x: Int (from list element)
    //   - Result: Int
    let ty = infer_type("fold(0, |acc, x| acc + x, [1, 2, 3])");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_lambda_param_from_reduce_context() {
    // reduce(|a, b| a + b, [1, 2, 3])
    //   - [1, 2, 3] is List<Int>
    //   - reduce's signature: ((T, T) -> T, List<T>) -> T
    //   - a: Int, b: Int (from element type)
    //   - Result: Int
    let ty = infer_type("reduce(|a, b| a + b, [1, 2, 3])");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_lambda_param_decimal_list() {
    // Test with Decimal list to ensure type propagation works for different types
    // map(|x| x * 2.0, [1.0, 2.0, 3.0])
    //   - [1.0, 2.0, 3.0] is List<Decimal>
    //   - x: Decimal, x * 2.0: Decimal
    //   - Result: List<Decimal>
    let ty = infer_type("map(|x| x * 2.0, [1.0, 2.0, 3.0])");
    assert_eq!(ty, Type::List(Box::new(Type::Decimal)));
}

#[test]
fn infer_lambda_param_string_list() {
    // Test with String list
    // map(|s| s + \"!\", [\"a\", \"b\"])
    //   - List<String>
    //   - s: String, s + "!": String
    //   - Result: List<String>
    let ty = infer_type("map(|s| s + \"!\", [\"a\", \"b\"])");
    assert_eq!(ty, Type::List(Box::new(Type::String)));
}

#[test]
fn builtin_registry_matches_type_signatures() {
    use crate::runtime::builtin_registry::BUILTIN_SPECS;
    use crate::types::builtins::builtin_signatures;
    use std::collections::HashSet;

    let registry: HashSet<&'static str> = BUILTIN_SPECS.iter().map(|spec| spec.name).collect();
    let sigs = builtin_signatures();
    let sig_names: HashSet<&'static str> = sigs.keys().copied().collect();

    assert_eq!(registry, sig_names);
}
