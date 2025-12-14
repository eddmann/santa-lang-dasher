use crate::lexer::lex;
use crate::parser::parse;
use crate::types::ty::Type;
use crate::types::infer::TypeInference;

fn infer_type(source: &str) -> Type {
    let tokens = lex(source).unwrap();
    let expr = parse(tokens).unwrap();
    let mut inference = TypeInference::new();
    let typed_expr = inference.infer_expr(&expr).unwrap();
    typed_expr.ty
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
