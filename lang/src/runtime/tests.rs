use super::value::Value;

// ===== NaN-boxing Tests =====

#[test]
fn value_from_small_integer() {
    // Small integers (within 51 bits) should be inline NaN-boxed
    let v = Value::from_integer(42);
    assert!(v.is_integer());
    assert_eq!(v.as_integer(), Some(42));
}

#[test]
fn value_from_zero() {
    let v = Value::from_integer(0);
    assert!(v.is_integer());
    assert_eq!(v.as_integer(), Some(0));
}

#[test]
fn value_from_negative_integer() {
    let v = Value::from_integer(-123);
    assert!(v.is_integer());
    assert_eq!(v.as_integer(), Some(-123));
}

#[test]
fn value_from_nil() {
    let v = Value::nil();
    assert!(v.is_nil());
    assert!(!v.is_integer());
}

#[test]
fn value_from_boolean_true() {
    let v = Value::from_bool(true);
    assert!(v.is_boolean());
    assert_eq!(v.as_bool(), Some(true));
}

#[test]
fn value_from_boolean_false() {
    let v = Value::from_bool(false);
    assert!(v.is_boolean());
    assert_eq!(v.as_bool(), Some(false));
}

#[test]
fn value_from_decimal() {
    let v = Value::from_decimal(3.14);
    assert!(!v.is_integer());
    assert_eq!(v.as_decimal(), Some(3.14));
}

// ===== Large Integer Tests =====

#[test]
fn value_large_integer() {
    // 61-bit integers can be stored inline (3 bits lost to tag)
    let large = (1i64 << 60) - 1;  // Max 61-bit positive
    let v = Value::from_integer(large);
    assert!(v.is_integer());
    assert_eq!(v.as_integer(), Some(large));

    let small = -(1i64 << 60);  // Min 61-bit negative
    let v = Value::from_integer(small);
    assert!(v.is_integer());
    assert_eq!(v.as_integer(), Some(small));

    // TODO: Larger integers will need heap boxing (Phase 5 later)
    // For now, they wrap around (which is acceptable for MVP)
}

// ===== Truthiness Tests (LANG.txt §14.1) =====

#[test]
fn value_truthiness() {
    // Falsy values
    assert!(!Value::from_bool(false).is_truthy());
    assert!(!Value::nil().is_truthy());
    assert!(!Value::from_integer(0).is_truthy());
    assert!(!Value::from_decimal(0.0).is_truthy());
    // TODO: empty string, empty list once we have those

    // Truthy values
    assert!(Value::from_bool(true).is_truthy());
    assert!(Value::from_integer(1).is_truthy());
    assert!(Value::from_integer(-1).is_truthy());
    assert!(Value::from_decimal(3.14).is_truthy());
}

// ===== Heap Object Tests =====

#[test]
fn value_from_string() {
    let v = Value::from_string("hello");
    assert!(v.is_heap_object());
    assert_eq!(v.as_string(), Some("hello"));
}

#[test]
fn value_empty_string_is_falsy() {
    let v = Value::from_string("");
    assert!(!v.is_truthy());
}

#[test]
fn value_nonempty_string_is_truthy() {
    let v = Value::from_string("hello");
    assert!(v.is_truthy());
}

// ===== Grapheme Cluster String Indexing Tests (LANG.txt §3.3) =====

#[test]
fn string_grapheme_indexing_simple() {
    let v = Value::from_string("hello");
    assert_eq!(v.grapheme_at(0), Some("h"));
    assert_eq!(v.grapheme_at(1), Some("e"));
    assert_eq!(v.grapheme_at(4), Some("o"));
    assert_eq!(v.grapheme_at(5), None);
}

#[test]
fn string_grapheme_indexing_emoji() {
    // Family emoji is a single grapheme cluster (LANG.txt §3.3 example)
    let v = Value::from_string("👨‍👩‍👧‍👦");
    assert_eq!(v.grapheme_at(0), Some("👨‍👩‍👧‍👦"));
    assert_eq!(v.grapheme_at(1), None);
}

#[test]
fn string_grapheme_indexing_multiple_emoji() {
    let v = Value::from_string("❤🍕");
    assert_eq!(v.grapheme_at(0), Some("❤"));
    assert_eq!(v.grapheme_at(1), Some("🍕"));
    assert_eq!(v.grapheme_at(2), None);
}

#[test]
fn string_grapheme_length() {
    let v = Value::from_string("hello");
    assert_eq!(v.grapheme_len(), 5);

    let v = Value::from_string("❤🍕");
    assert_eq!(v.grapheme_len(), 2);

    let v = Value::from_string("👨‍👩‍👧‍👦");
    assert_eq!(v.grapheme_len(), 1);
}

// ===== Reference Counting Tests =====

use crate::runtime::refcount::{rt_incref, rt_decref, rt_get_refcount};

#[test]
fn refcount_string_starts_at_one() {
    let v = Value::from_string("hello");
    assert_eq!(rt_get_refcount(v), 1);
}

#[test]
fn refcount_increment() {
    let v = Value::from_string("hello");
    rt_incref(v);
    assert_eq!(rt_get_refcount(v), 2);
    rt_incref(v);
    assert_eq!(rt_get_refcount(v), 3);
}

#[test]
fn refcount_decrement() {
    let v = Value::from_string("hello");
    rt_incref(v);
    rt_incref(v);
    assert_eq!(rt_get_refcount(v), 3);
    rt_decref(v);
    assert_eq!(rt_get_refcount(v), 2);
    rt_decref(v);
    assert_eq!(rt_get_refcount(v), 1);
}

#[test]
fn refcount_primitives_ignored() {
    // Primitives (integers, booleans, nil, decimals) should not be refcounted
    let v = Value::from_integer(42);
    rt_incref(v);  // Should do nothing
    rt_decref(v);  // Should do nothing
    // No assertion - just shouldn't crash
}

// ===== Runtime Operations Tests =====

use crate::runtime::operations::{rt_add, rt_sub, rt_mul, rt_div, rt_mod};

#[test]
fn runtime_add_integers() {
    let left = Value::from_integer(10);
    let right = Value::from_integer(32);
    let result = rt_add(left, right);

    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(42));
}

#[test]
fn runtime_add_decimals() {
    let left = Value::from_decimal(1.5);
    let right = Value::from_decimal(2.5);
    let result = rt_add(left, right);

    assert!(result.as_decimal().is_some());
    assert_eq!(result.as_decimal(), Some(4.0));
}

#[test]
fn runtime_add_int_decimal_left_wins() {
    // Per LANG.txt §4.1: left operand type determines result type
    let left = Value::from_integer(10);
    let right = Value::from_decimal(5.5);
    let result = rt_add(left, right);

    // Left is Int, so result should be Int (10 + 5 = 15, decimal truncated)
    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(15));
}

#[test]
fn runtime_add_decimal_int_left_wins() {
    // Per LANG.txt §4.1: left operand type determines result type
    let left = Value::from_decimal(10.0);
    let right = Value::from_integer(5);
    let result = rt_add(left, right);

    // Left is Decimal, so result should be Decimal
    assert!(result.as_decimal().is_some());
    assert_eq!(result.as_decimal(), Some(15.0));
}

#[test]
fn runtime_add_string_concatenation() {
    let left = Value::from_string("Hello, ");
    let right = Value::from_string("World!");
    let result = rt_add(left, right);

    assert!(result.as_string().is_some());
    assert_eq!(result.as_string(), Some("Hello, World!"));
}

#[test]
fn runtime_add_string_coerces_right() {
    // String + X coerces X to string
    let left = Value::from_string("Answer: ");
    let right = Value::from_integer(42);
    let result = rt_add(left, right);

    assert!(result.as_string().is_some());
    assert_eq!(result.as_string(), Some("Answer: 42"));
}

#[test]
fn runtime_subtract_integers() {
    let left = Value::from_integer(50);
    let right = Value::from_integer(8);
    let result = rt_sub(left, right);

    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(42));
}

#[test]
fn runtime_multiply_integers() {
    let left = Value::from_integer(6);
    let right = Value::from_integer(7);
    let result = rt_mul(left, right);

    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(42));
}

#[test]
fn runtime_divide_integers() {
    let left = Value::from_integer(84);
    let right = Value::from_integer(2);
    let result = rt_div(left, right);

    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(42));
}

#[test]
fn runtime_floored_division_negative_numerator() {
    // -7 / 2 should be -4 (Python-style floored division, NOT -3)
    let left = Value::from_integer(-7);
    let right = Value::from_integer(2);
    let result = rt_div(left, right);

    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(-4));
}

#[test]
fn runtime_floored_division_negative_denominator() {
    // 7 / -2 should be -4 (NOT -3)
    let left = Value::from_integer(7);
    let right = Value::from_integer(-2);
    let result = rt_div(left, right);

    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(-4));
}

#[test]
fn runtime_modulo_integers() {
    let left = Value::from_integer(10);
    let right = Value::from_integer(3);
    let result = rt_mod(left, right);

    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn runtime_floored_modulo_negative_numerator() {
    // -7 % 3 should be 2 (Python-style floored modulo, NOT -1)
    let left = Value::from_integer(-7);
    let right = Value::from_integer(3);
    let result = rt_mod(left, right);

    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn runtime_floored_modulo_negative_denominator() {
    // 7 % -3 should be -2 (NOT 1)
    let left = Value::from_integer(7);
    let right = Value::from_integer(-3);
    let result = rt_mod(left, right);

    assert!(result.is_integer());
    assert_eq!(result.as_integer(), Some(-2));
}

// ===== Comparison Operations Tests =====

use crate::runtime::operations::{rt_eq, rt_lt};

#[test]
fn runtime_eq_integers_equal() {
    let left = Value::from_integer(42);
    let right = Value::from_integer(42);
    let result = rt_eq(left, right);

    assert!(result.is_boolean());
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn runtime_eq_integers_not_equal() {
    let left = Value::from_integer(42);
    let right = Value::from_integer(43);
    let result = rt_eq(left, right);

    assert!(result.is_boolean());
    assert_eq!(result.as_bool(), Some(false));
}

#[test]
fn runtime_lt_integers() {
    let left = Value::from_integer(10);
    let right = Value::from_integer(20);
    let result = rt_lt(left, right);

    assert!(result.is_boolean());
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn runtime_lt_integers_false() {
    let left = Value::from_integer(20);
    let right = Value::from_integer(10);
    let result = rt_lt(left, right);

    assert!(result.is_boolean());
    assert_eq!(result.as_bool(), Some(false));
}

#[test]
fn runtime_lt_decimals() {
    let left = Value::from_decimal(1.5);
    let right = Value::from_decimal(2.5);
    let result = rt_lt(left, right);

    assert!(result.is_boolean());
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn runtime_lt_strings() {
    let left = Value::from_string("abc");
    let right = Value::from_string("def");
    let result = rt_lt(left, right);

    assert!(result.is_boolean());
    assert_eq!(result.as_bool(), Some(true));
}
