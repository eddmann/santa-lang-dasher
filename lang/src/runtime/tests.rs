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
