use crate::lexer::lex;
use crate::parser::{parse, Parser};
use crate::types::ty::{Type, TypedProgram};
use crate::types::infer::TypeInference;

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
    assert_eq!(
        ty,
        Type::Dict(Box::new(Type::Int), Box::new(Type::String))
    );
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
fn infer_block_single_expr() {
    // { 42 } → Int
    let ty = infer_type("{ 42 }");
    assert_eq!(ty, Type::Int);
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
    let program = infer_program(r#"
let x = 1
let y = "hello"
x + 2
"#);
    // 3 statements: let x, let y, expression x + 2
    assert_eq!(program.statements.len(), 3);
    // The last expression x+2 would be Unknown (x is unknown without env tracking)
    // This is expected behavior for now
}

#[test]
fn infer_program_with_input_section() {
    // Program with input section
    let program = infer_program(r#"
input: "test data"
"#);
    assert_eq!(program.sections.len(), 1);
    assert_eq!(program.sections[0].ty, Type::String);
}

#[test]
fn infer_program_with_part_one() {
    // Program with part_one section
    let program = infer_program(r#"
input: 42
part_one: input * 2
"#);
    assert_eq!(program.sections.len(), 2);
    // input: 42 → Int
    assert_eq!(program.sections[0].ty, Type::Int);
    // part_one: input * 2 → Unknown (input not tracked in simple implementation)
}
