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

// ===== Built-in Function Tests (Phase 10) =====

use crate::runtime::builtins::rt_int;

// int() function tests per LANG.txt §11.1
#[test]
fn builtin_int_identity() {
    // int(5) → 5
    let v = Value::from_integer(5);
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(5));
}

#[test]
fn builtin_int_from_decimal_rounds_up() {
    // int(3.7) → 4
    let v = Value::from_decimal(3.7);
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(4));
}

#[test]
fn builtin_int_from_decimal_rounds_half_away_from_zero_positive() {
    // int(3.5) → 4 (half rounds away from zero)
    let v = Value::from_decimal(3.5);
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(4));
}

#[test]
fn builtin_int_from_decimal_rounds_half_away_from_zero_negative() {
    // int(-3.5) → -4 (half rounds away from zero)
    let v = Value::from_decimal(-3.5);
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(-4));
}

#[test]
fn builtin_int_from_decimal_negative_rounds_up() {
    // int(-5.5) → -6
    let v = Value::from_decimal(-5.5);
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(-6));
}

#[test]
fn builtin_int_from_string_valid() {
    // int("42") → 42
    let v = Value::from_string("42");
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(42));
}

#[test]
fn builtin_int_from_string_negative() {
    // int("-17") → -17
    let v = Value::from_string("-17");
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(-17));
}

#[test]
fn builtin_int_from_string_invalid() {
    // int("abc") → 0 (parse failure)
    let v = Value::from_string("abc");
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(0));
}

#[test]
fn builtin_int_from_bool_true() {
    // int(true) → 1
    let v = Value::from_bool(true);
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_int_from_bool_false() {
    // int(false) → 0
    let v = Value::from_bool(false);
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(0));
}

#[test]
fn builtin_int_from_nil() {
    // int(nil) → 0
    let v = Value::nil();
    let result = rt_int(v);
    assert_eq!(result.as_integer(), Some(0));
}

// ints() function tests per LANG.txt §11.1
use crate::runtime::builtins::rt_ints;

#[test]
fn builtin_ints_comma_separated() {
    // ints("1,2,3") → [1, 2, 3]
    let v = Value::from_string("1,2,3");
    let result = rt_ints(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_integer(), Some(1));
    assert_eq!(list[1].as_integer(), Some(2));
    assert_eq!(list[2].as_integer(), Some(3));
}

#[test]
fn builtin_ints_mixed_text() {
    // ints("15a20b35") → [15, 20, 35]
    let v = Value::from_string("15a20b35");
    let result = rt_ints(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_integer(), Some(15));
    assert_eq!(list[1].as_integer(), Some(20));
    assert_eq!(list[2].as_integer(), Some(35));
}

#[test]
fn builtin_ints_with_negatives() {
    // ints("x: 10, y: -5") → [10, -5]
    let v = Value::from_string("x: 10, y: -5");
    let result = rt_ints(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 2);
    assert_eq!(list[0].as_integer(), Some(10));
    assert_eq!(list[1].as_integer(), Some(-5));
}

#[test]
fn builtin_ints_no_numbers() {
    // ints("no numbers") → []
    let v = Value::from_string("no numbers");
    let result = rt_ints(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 0);
}

#[test]
fn builtin_ints_non_string_returns_empty() {
    // ints on non-string returns empty list
    let v = Value::from_integer(42);
    let result = rt_ints(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 0);
}

// list() function tests per LANG.txt §11.1
use crate::runtime::builtins::rt_list;

#[test]
fn builtin_list_from_list() {
    // list([1, 2, 3]) → [1, 2, 3] (identity)
    let v = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_list(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_integer(), Some(1));
}

#[test]
fn builtin_list_from_set() {
    // list({1, 2, 3}) → [1, 2, 3] (order is implementation-defined)
    let v = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_list(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
}

#[test]
fn builtin_list_from_string() {
    // list("ab") → ["a", "b"]
    let v = Value::from_string("ab");
    let result = rt_list(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 2);
    assert_eq!(list[0].as_string(), Some("a"));
    assert_eq!(list[1].as_string(), Some("b"));
}

#[test]
fn builtin_list_from_dict() {
    // list(#{1: 2, 3: 4}) → [[1, 2], [3, 4]] (list of [key, value] tuples)
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    let v = Value::from_dict(entries);
    let result = rt_list(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 1);
    // First element should be a [key, value] tuple
    let tuple = list[0].as_list().expect("tuple should be a list");
    assert_eq!(tuple.len(), 2);
}

// set() function tests per LANG.txt §11.1
use crate::runtime::builtins::rt_set;

#[test]
fn builtin_set_from_list() {
    // set([1, 2, 2, 3]) → {1, 2, 3}
    let v = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_set(v);
    let set = result.as_set().expect("should be a set");
    assert_eq!(set.len(), 3);
}

#[test]
fn builtin_set_from_set() {
    // set({1, 2, 3}) → {1, 2, 3} (identity)
    let v = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_set(v);
    let set = result.as_set().expect("should be a set");
    assert_eq!(set.len(), 3);
}

#[test]
fn builtin_set_from_string() {
    // set("aab") → {"a", "b"}
    let v = Value::from_string("aab");
    let result = rt_set(v);
    let set = result.as_set().expect("should be a set");
    assert_eq!(set.len(), 2);
}

// dict() function tests per LANG.txt §11.1
use crate::runtime::builtins::rt_dict;

#[test]
fn builtin_dict_from_list_of_tuples() {
    // dict([[1, 2], [3, 4]]) → #{1: 2, 3: 4}
    let tuple1 = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let tuple2 = Value::from_list(vec![
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let v = Value::from_list(vec![tuple1, tuple2].into_iter().collect());
    let result = rt_dict(v);
    let dict = result.as_dict().expect("should be a dict");
    assert_eq!(dict.len(), 2);
    assert_eq!(dict.get(&Value::from_integer(1)), Some(&Value::from_integer(2)));
    assert_eq!(dict.get(&Value::from_integer(3)), Some(&Value::from_integer(4)));
}

#[test]
fn builtin_dict_from_dict() {
    // dict(#{1: 2, 3: 4}) → #{1: 2, 3: 4} (identity)
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    entries.insert(Value::from_integer(3), Value::from_integer(4));
    let v = Value::from_dict(entries);
    let result = rt_dict(v);
    let dict = result.as_dict().expect("should be a dict");
    assert_eq!(dict.len(), 2);
}

// ===== Collection Access Functions (§11.2) =====

use crate::runtime::builtins::{rt_get, rt_size, rt_first, rt_second, rt_last, rt_rest, rt_keys, rt_values};

// get() tests
#[test]
fn builtin_get_list() {
    // get(1, [1, 2]) → 2
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_get(Value::from_integer(1), list);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_get_list_out_of_bounds() {
    // get(5, [1, 2]) → nil
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_get(Value::from_integer(5), list);
    assert!(result.is_nil());
}

#[test]
fn builtin_get_set_membership() {
    // get(1, {1, 2}) → 1 (found)
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_get(Value::from_integer(1), set);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_get_set_not_found() {
    // get(3, {1, 2}) → nil
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_get(Value::from_integer(3), set);
    assert!(result.is_nil());
}

#[test]
fn builtin_get_dict() {
    // get(1, #{1: 2, 3: 4}) → 2
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    entries.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(entries);
    let result = rt_get(Value::from_integer(1), dict);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_get_string() {
    // get(1, "hello") → "e"
    let s = Value::from_string("hello");
    let result = rt_get(Value::from_integer(1), s);
    assert_eq!(result.as_string(), Some("e"));
}

// size() tests
#[test]
fn builtin_size_list() {
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_size(list);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_size_set() {
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_size(set);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_size_dict() {
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    entries.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(entries);
    let result = rt_size(dict);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_size_string() {
    let s = Value::from_string("hello");
    let result = rt_size(s);
    assert_eq!(result.as_integer(), Some(5));
}

// first() tests
#[test]
fn builtin_first_list() {
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_first(list);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_first_empty_list() {
    let list = Value::from_list(im::Vector::new());
    let result = rt_first(list);
    assert!(result.is_nil());
}

#[test]
fn builtin_first_string() {
    let s = Value::from_string("ab");
    let result = rt_first(s);
    assert_eq!(result.as_string(), Some("a"));
}

// second() tests
#[test]
fn builtin_second_list() {
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_second(list);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_second_list_too_short() {
    let list = Value::from_list(vec![
        Value::from_integer(1),
    ].into_iter().collect());
    let result = rt_second(list);
    assert!(result.is_nil());
}

// last() tests
#[test]
fn builtin_last_list() {
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_last(list);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_last_empty_list() {
    let list = Value::from_list(im::Vector::new());
    let result = rt_last(list);
    assert!(result.is_nil());
}

// rest() tests
#[test]
fn builtin_rest_list() {
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_rest(list);
    let rest = result.as_list().expect("should be a list");
    assert_eq!(rest.len(), 2);
    assert_eq!(rest[0].as_integer(), Some(2));
    assert_eq!(rest[1].as_integer(), Some(3));
}

#[test]
fn builtin_rest_empty_list() {
    let list = Value::from_list(im::Vector::new());
    let result = rt_rest(list);
    let rest = result.as_list().expect("should be a list");
    assert!(rest.is_empty());
}

#[test]
fn builtin_rest_string() {
    let s = Value::from_string("abc");
    let result = rt_rest(s);
    assert_eq!(result.as_string(), Some("bc"));
}

// keys() and values() tests
#[test]
fn builtin_keys_dict() {
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    let dict = Value::from_dict(entries);
    let result = rt_keys(dict);
    let keys = result.as_list().expect("should be a list");
    assert_eq!(keys.len(), 1);
    assert_eq!(keys[0].as_integer(), Some(1));
}

#[test]
fn builtin_values_dict() {
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    let dict = Value::from_dict(entries);
    let result = rt_values(dict);
    let values = result.as_list().expect("should be a list");
    assert_eq!(values.len(), 1);
    assert_eq!(values[0].as_integer(), Some(2));
}

// ===== Collection Modification Functions (§11.3) =====

use crate::runtime::builtins::{rt_push, rt_assoc};

// push() tests
#[test]
fn builtin_push_list() {
    // push(3, [1, 2]) → [1, 2, 3]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_push(Value::from_integer(3), list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 3);
    assert_eq!(new_list[0].as_integer(), Some(1));
    assert_eq!(new_list[1].as_integer(), Some(2));
    assert_eq!(new_list[2].as_integer(), Some(3));
}

#[test]
fn builtin_push_set() {
    // push(3, {1, 2}) → {1, 2, 3}
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_push(Value::from_integer(3), set);
    let new_set = result.as_set().expect("should be a set");
    assert_eq!(new_set.len(), 3);
    assert!(new_set.contains(&Value::from_integer(3)));
}

#[test]
fn builtin_push_set_already_present() {
    // push(1, {1, 2}) → {1, 2} (no change)
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_push(Value::from_integer(1), set);
    let new_set = result.as_set().expect("should be a set");
    assert_eq!(new_set.len(), 2);
}

// assoc() tests
#[test]
fn builtin_assoc_list() {
    // assoc(0, 3, [1, 2]) → [3, 2]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_assoc(Value::from_integer(0), Value::from_integer(3), list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 2);
    assert_eq!(new_list[0].as_integer(), Some(3));
    assert_eq!(new_list[1].as_integer(), Some(2));
}

#[test]
fn builtin_assoc_list_beyond_bounds() {
    // assoc(1, 1, []) → [nil, 1]
    let list = Value::from_list(im::Vector::new());
    let result = rt_assoc(Value::from_integer(1), Value::from_integer(1), list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 2);
    assert!(new_list[0].is_nil());
    assert_eq!(new_list[1].as_integer(), Some(1));
}

#[test]
fn builtin_assoc_dict_replace() {
    // assoc(1, 1, #{1: 2, 3: 4}) → #{1: 1, 3: 4}
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    entries.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(entries);
    let result = rt_assoc(Value::from_integer(1), Value::from_integer(1), dict);
    let new_dict = result.as_dict().expect("should be a dict");
    assert_eq!(new_dict.len(), 2);
    assert_eq!(new_dict.get(&Value::from_integer(1)), Some(&Value::from_integer(1)));
}

#[test]
fn builtin_assoc_dict_add() {
    // assoc(0, 1, #{1: 2}) → #{1: 2, 0: 1}
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    let dict = Value::from_dict(entries);
    let result = rt_assoc(Value::from_integer(0), Value::from_integer(1), dict);
    let new_dict = result.as_dict().expect("should be a dict");
    assert_eq!(new_dict.len(), 2);
    assert_eq!(new_dict.get(&Value::from_integer(0)), Some(&Value::from_integer(1)));
}
