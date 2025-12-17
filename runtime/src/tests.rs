use super::value::Value;
use super::builtins::format_value;

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
    assert!(!Value::from_string("").is_truthy());
    assert!(!Value::from_list(im::Vector::new()).is_truthy());

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

use crate::refcount::{rt_incref, rt_decref, rt_get_refcount};

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

#[test]
fn refcount_closure_decrefs_captures_on_free() {
    use crate::heap::ClosureObject;

    // Create a string value to be captured
    let captured_str = Value::from_string("captured");
    assert_eq!(rt_get_refcount(captured_str), 1);

    // Increment the string's refcount (simulating it being used elsewhere)
    rt_incref(captured_str);
    assert_eq!(rt_get_refcount(captured_str), 2);

    // Create a closure that captures this string
    // The dummy function pointer is never called, we just test refcounting
    extern "C" fn dummy_fn(_env: *const (), _argc: u32, _argv: *const Value) -> Value {
        Value::nil()
    }
    let closure = ClosureObject::new(dummy_fn as *const (), 0, vec![captured_str]);
    let closure_val = Value::from_closure(closure);
    assert_eq!(rt_get_refcount(closure_val), 1);

    // Decrement closure refcount to 0 - should free and decref captures
    rt_decref(closure_val);

    // The captured string should now have refcount 1 (decremented from 2)
    assert_eq!(rt_get_refcount(captured_str), 1);
}

#[test]
fn refcount_memoized_closure_decrefs_inner_closure_on_free() {
    use crate::heap::{ClosureObject, MemoizedClosureObject};

    // Create an inner closure
    extern "C" fn dummy_fn(_env: *const (), _argc: u32, _argv: *const Value) -> Value {
        Value::nil()
    }
    let inner = ClosureObject::new(dummy_fn as *const (), 0, vec![]);
    let inner_val = Value::from_closure(inner);
    assert_eq!(rt_get_refcount(inner_val), 1);

    // Increment inner closure refcount (simulating it being used elsewhere)
    rt_incref(inner_val);
    assert_eq!(rt_get_refcount(inner_val), 2);

    // Create a memoized closure wrapping the inner closure
    let memoized = MemoizedClosureObject::new(inner_val, 0);
    let memoized_val = Value::from_memoized_closure(memoized);
    assert_eq!(rt_get_refcount(memoized_val), 1);

    // Decrement memoized closure refcount to 0 - should free and decref inner
    rt_decref(memoized_val);

    // The inner closure should now have refcount 1 (decremented from 2)
    assert_eq!(rt_get_refcount(inner_val), 1);
}

#[test]
fn refcount_lazy_sequence_decrefs_value_on_free() {
    use crate::heap::LazySequenceObject;

    // Create a string value to be repeated
    let repeated_str = Value::from_string("repeat me");
    assert_eq!(rt_get_refcount(repeated_str), 1);

    // Increment the string's refcount (simulating it being used elsewhere)
    rt_incref(repeated_str);
    assert_eq!(rt_get_refcount(repeated_str), 2);

    // Create a repeat lazy sequence containing this string
    let lazy_seq = LazySequenceObject::repeat(repeated_str);
    let lazy_val = Value::from_lazy_sequence(lazy_seq);
    assert_eq!(rt_get_refcount(lazy_val), 1);

    // Decrement lazy sequence refcount to 0 - should free and decref the repeated value
    rt_decref(lazy_val);

    // The repeated string should now have refcount 1 (decremented from 2)
    assert_eq!(rt_get_refcount(repeated_str), 1);
}

// ===== Runtime Operations Tests =====

use crate::operations::{rt_add, rt_sub, rt_mul, rt_div, rt_mod};

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

// List + List concatenation per LANG.txt §4
#[test]
fn runtime_add_list_concatenation() {
    // [1, 2] + [3, 4] → [1, 2, 3, 4]
    let left = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let right = Value::from_list(vec![
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let result = rt_add(left, right);

    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 4);
    assert_eq!(list[0].as_integer(), Some(1));
    assert_eq!(list[1].as_integer(), Some(2));
    assert_eq!(list[2].as_integer(), Some(3));
    assert_eq!(list[3].as_integer(), Some(4));
}

// Set + Set union per LANG.txt §4
#[test]
fn runtime_add_set_union() {
    // {1, 2} + {2, 3} → {1, 2, 3}
    let left = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let right = Value::from_set(vec![
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_add(left, right);

    let set = result.as_set().expect("should be a set");
    assert_eq!(set.len(), 3);
    assert!(set.contains(&Value::from_integer(1)));
    assert!(set.contains(&Value::from_integer(2)));
    assert!(set.contains(&Value::from_integer(3)));
}

// Dict + Dict merge per LANG.txt §4
#[test]
fn runtime_add_dict_merge() {
    // #{1: 2, 3: 4} + #{3: 5, 6: 7} → #{1: 2, 3: 5, 6: 7} (right precedence)
    let mut left_entries = im::HashMap::new();
    left_entries.insert(Value::from_integer(1), Value::from_integer(2));
    left_entries.insert(Value::from_integer(3), Value::from_integer(4));
    let left = Value::from_dict(left_entries);

    let mut right_entries = im::HashMap::new();
    right_entries.insert(Value::from_integer(3), Value::from_integer(5));
    right_entries.insert(Value::from_integer(6), Value::from_integer(7));
    let right = Value::from_dict(right_entries);

    let result = rt_add(left, right);

    let dict = result.as_dict().expect("should be a dict");
    assert_eq!(dict.len(), 3);
    assert_eq!(dict.get(&Value::from_integer(1)), Some(&Value::from_integer(2)));
    assert_eq!(dict.get(&Value::from_integer(3)), Some(&Value::from_integer(5))); // Right wins
    assert_eq!(dict.get(&Value::from_integer(6)), Some(&Value::from_integer(7)));
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

#[test]
#[should_panic(expected = "Division by zero")]
fn runtime_division_by_zero_panics() {
    // Per LANG.txt §15.5: 10 / 0 → RuntimeErr
    let left = Value::from_integer(10);
    let right = Value::from_integer(0);
    let _result = rt_div(left, right);  // Should panic
}

#[test]
#[should_panic(expected = "Division by zero")]
fn runtime_modulo_by_zero_panics() {
    // Per LANG.txt §15.5: modulo by zero → RuntimeErr
    let left = Value::from_integer(10);
    let right = Value::from_integer(0);
    let _result = rt_mod(left, right);  // Should panic
}

// ===== Comparison Operations Tests =====

use crate::operations::{rt_eq, rt_lt};

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

#[test]
#[should_panic(expected = "Cannot compare")]
fn runtime_lt_lists_panics() {
    // Per LANG.txt §4.4: Lists are not comparable
    // [1, 2] < [3, 4] → RuntimeErr
    let left = Value::from_list(vec![Value::from_integer(1), Value::from_integer(2)].into_iter().collect());
    let right = Value::from_list(vec![Value::from_integer(3), Value::from_integer(4)].into_iter().collect());
    let _result = rt_lt(left, right);  // Should panic
}

#[test]
#[should_panic(expected = "Cannot compare")]
fn runtime_lt_sets_panics() {
    // Per LANG.txt §4.4: Sets are not comparable
    let left = Value::from_set(vec![Value::from_integer(1)].into_iter().collect());
    let right = Value::from_set(vec![Value::from_integer(2)].into_iter().collect());
    let _result = rt_lt(left, right);  // Should panic
}

#[test]
#[should_panic(expected = "Cannot compare")]
fn runtime_lt_mixed_types_panics() {
    // Per LANG.txt §4.4: Comparing different non-numeric types is an error
    let left = Value::from_integer(1);
    let right = Value::from_list(vec![Value::from_integer(1)].into_iter().collect());
    let _result = rt_lt(left, right);  // Should panic
}

// ===== Hashability Tests =====

#[test]
fn hashability_primitives_are_hashable() {
    assert!(Value::from_integer(42).is_hashable());
    assert!(Value::nil().is_hashable());
    assert!(Value::from_bool(true).is_hashable());
    assert!(Value::from_decimal(3.14).is_hashable());
    assert!(Value::from_string("hello").is_hashable());
}

#[test]
fn hashability_sets_are_hashable() {
    let set = Value::from_set(vec![Value::from_integer(1)].into_iter().collect());
    assert!(set.is_hashable());
}

#[test]
fn hashability_lists_with_hashable_elements() {
    let list = Value::from_list(vec![Value::from_integer(1), Value::from_string("a")].into_iter().collect());
    assert!(list.is_hashable());
}

#[test]
fn hashability_dicts_not_hashable() {
    let dict = Value::from_dict(im::HashMap::new());
    assert!(!dict.is_hashable());
}

#[test]
#[should_panic(expected = "not hashable")]
fn runtime_push_dict_to_set_panics() {
    // Per LANG.txt §3.11, §15.5: Dictionaries are not hashable
    // {#{a: 1}} → RuntimeErr
    let set = Value::from_set(im::HashSet::new());
    let dict = Value::from_dict(im::HashMap::new());
    let _result = rt_push(dict, set);  // Should panic
}

#[test]
#[should_panic(expected = "not hashable")]
fn runtime_assoc_dict_key_panics() {
    // Per LANG.txt §3.11, §15.5: Dictionaries are not hashable as keys
    // #{(#{a: 1}): "value"} → RuntimeErr
    use crate::builtins::rt_assoc;
    let dict = Value::from_dict(im::HashMap::new());
    let key = Value::from_dict(im::HashMap::new()); // Dict as key
    let value = Value::from_string("value");
    let _result = rt_assoc(key, value, dict);  // Should panic
}

// ===== Built-in Function Tests (Phase 10) =====

use crate::builtins::rt_int;

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
use crate::builtins::rt_ints;

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
use crate::builtins::rt_list;

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

#[test]
fn builtin_list_from_range() {
    // list(1..5) → [1, 2, 3, 4]
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_list(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 4);
    assert_eq!(list[0].as_integer(), Some(1));
    assert_eq!(list[1].as_integer(), Some(2));
    assert_eq!(list[2].as_integer(), Some(3));
    assert_eq!(list[3].as_integer(), Some(4));
}

#[test]
fn builtin_list_from_inclusive_range() {
    // list(1..=3) → [1, 2, 3]
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(3), true, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_list(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_integer(), Some(1));
    assert_eq!(list[1].as_integer(), Some(2));
    assert_eq!(list[2].as_integer(), Some(3));
}

// set() function tests per LANG.txt §11.1
use crate::builtins::rt_set;

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

#[test]
fn builtin_set_from_range() {
    // set(1..5) → {1, 2, 3, 4}
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_set(v);
    let set = result.as_set().expect("should be a set");
    assert_eq!(set.len(), 4);
    assert!(set.contains(&Value::from_integer(1)));
    assert!(set.contains(&Value::from_integer(2)));
    assert!(set.contains(&Value::from_integer(3)));
    assert!(set.contains(&Value::from_integer(4)));
}

// dict() function tests per LANG.txt §11.1
use crate::builtins::rt_dict;

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

use crate::builtins::{rt_get, rt_size, rt_first, rt_second, rt_last, rt_rest, rt_keys, rt_values};

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

#[test]
fn builtin_size_range() {
    // size(1..5) → 4 (bounded range)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_size(v);
    assert_eq!(result.as_integer(), Some(4));
}

#[test]
fn builtin_size_inclusive_range() {
    // size(1..=5) → 5 (inclusive bounded range)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), true, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_size(v);
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

#[test]
fn builtin_first_range() {
    // first(1..5) → 1
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_first(v);
    assert_eq!(result.as_integer(), Some(1));
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

#[test]
fn builtin_second_range() {
    // second(1..5) → 2
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_second(v);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_second_range_too_short() {
    // second(1..2) → nil (only has one element: 1)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(2), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_second(v);
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

#[test]
fn builtin_last_range() {
    // last(1..5) → 4 (exclusive range)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_last(v);
    assert_eq!(result.as_integer(), Some(4));
}

#[test]
fn builtin_last_inclusive_range() {
    // last(1..=5) → 5 (inclusive range)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), true, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_last(v);
    assert_eq!(result.as_integer(), Some(5));
}

#[test]
fn builtin_last_descending_range() {
    // last(5..1) → 2 (descending, exclusive)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(5, Some(1), false, -1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_last(v);
    assert_eq!(result.as_integer(), Some(2));
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

#[test]
fn builtin_rest_range() {
    // rest(1..5) → lazy sequence starting at 2
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_rest(v);
    // rest returns a LazySequence, convert to list to check
    let list = rt_list(result);
    let elements = list.as_list().expect("should be a list");
    assert_eq!(elements.len(), 3);
    assert_eq!(elements[0].as_integer(), Some(2));
    assert_eq!(elements[1].as_integer(), Some(3));
    assert_eq!(elements[2].as_integer(), Some(4));
}

#[test]
fn builtin_rest_range_single_element() {
    // rest(1..2) → empty (only has one element: 1)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(2), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_rest(v);
    let list = rt_list(result);
    let elements = list.as_list().expect("should be a list");
    assert!(elements.is_empty());
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

use crate::builtins::{rt_push, rt_assoc};

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

// ===== Transformation Functions (§11.4) =====

use crate::builtins::rt_map;
use crate::heap::ClosureObject;

/// Helper: create a test closure from a Rust function
///
/// This creates a closure value that wraps a Rust function.
/// The function signature must match the closure calling convention:
///   fn(env: *const ClosureObject, argc: u32, argv: *const Value) -> Value
fn make_test_closure(
    func: extern "C" fn(*const ClosureObject, u32, *const Value) -> Value,
    arity: u32,
) -> Value {
    let closure = ClosureObject::new(func as *const (), arity, Vec::new());
    Value::from_closure(closure)
}

/// Test closure: adds 1 to its argument (integer)
extern "C" fn add_one_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::nil();
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_integer(i + 1)
    } else {
        Value::nil()
    }
}

/// Test closure: doubles a string
extern "C" fn double_string_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::nil();
    }
    let arg = unsafe { *argv };
    if let Some(s) = arg.as_string() {
        Value::from_string(format!("{}{}", s, s))
    } else {
        Value::nil()
    }
}

// map() tests per LANG.txt §11.4
#[test]
fn builtin_map_list() {
    // map(_ + 1, [1, 2]) → [2, 3]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let mapper = make_test_closure(add_one_closure, 1);
    let result = rt_map(mapper, list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 2);
    assert_eq!(new_list[0].as_integer(), Some(2));
    assert_eq!(new_list[1].as_integer(), Some(3));
}

#[test]
fn builtin_map_set() {
    // map(_ + 1, {1, 2}) → {2, 3}
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let mapper = make_test_closure(add_one_closure, 1);
    let result = rt_map(mapper, set);
    let new_set = result.as_set().expect("should be a set");
    assert_eq!(new_set.len(), 2);
    assert!(new_set.contains(&Value::from_integer(2)));
    assert!(new_set.contains(&Value::from_integer(3)));
}

#[test]
fn builtin_map_dict_value_only() {
    // map(_ + 1, #{1: 2, 3: 4}) → #{1: 3, 3: 5}
    // When mapper takes single arg, it receives value only
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    entries.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(entries);
    let mapper = make_test_closure(add_one_closure, 1);
    let result = rt_map(mapper, dict);
    let new_dict = result.as_dict().expect("should be a dict");
    assert_eq!(new_dict.len(), 2);
    assert_eq!(new_dict.get(&Value::from_integer(1)), Some(&Value::from_integer(3)));
    assert_eq!(new_dict.get(&Value::from_integer(3)), Some(&Value::from_integer(5)));
}

#[test]
fn builtin_map_string() {
    // map(_ * 2, "ab") → ["aa", "bb"]
    // String map returns List
    let s = Value::from_string("ab");
    let mapper = make_test_closure(double_string_closure, 1);
    let result = rt_map(mapper, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 2);
    assert_eq!(list[0].as_string(), Some("aa"));
    assert_eq!(list[1].as_string(), Some("bb"));
}

#[test]
fn builtin_map_empty_list() {
    // map(_ + 1, []) → []
    let list = Value::from_list(im::Vector::new());
    let mapper = make_test_closure(add_one_closure, 1);
    let result = rt_map(mapper, list);
    let new_list = result.as_list().expect("should be a list");
    assert!(new_list.is_empty());
}

// ===== filter() tests per LANG.txt §11.4 =====

use crate::builtins::rt_filter;

/// Test closure: returns true if value == 1
extern "C" fn equals_one_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::from_bool(false);
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_bool(i == 1)
    } else {
        Value::from_bool(false)
    }
}

/// Test closure: returns true if value > 1
extern "C" fn greater_than_one_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::from_bool(false);
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_bool(i > 1)
    } else {
        Value::from_bool(false)
    }
}

/// Test closure: returns true if string == "a"
extern "C" fn equals_a_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::from_bool(false);
    }
    let arg = unsafe { *argv };
    if let Some(s) = arg.as_string() {
        Value::from_bool(s == "a")
    } else {
        Value::from_bool(false)
    }
}

#[test]
fn builtin_filter_list() {
    // filter(_ == 1, [1, 2]) → [1]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let predicate = make_test_closure(equals_one_closure, 1);
    let result = rt_filter(predicate, list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 1);
    assert_eq!(new_list[0].as_integer(), Some(1));
}

#[test]
fn builtin_filter_set() {
    // filter(_ == 1, {1, 2}) → {1}
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let predicate = make_test_closure(equals_one_closure, 1);
    let result = rt_filter(predicate, set);
    let new_set = result.as_set().expect("should be a set");
    assert_eq!(new_set.len(), 1);
    assert!(new_set.contains(&Value::from_integer(1)));
}

#[test]
fn builtin_filter_dict_value_only() {
    // filter(_ == 2, #{1: 2, 3: 4}) → #{1: 2}
    // Predicate receives value only
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    entries.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(entries);

    // Create predicate that checks if value == 2
    extern "C" fn equals_two_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(i) = arg.as_integer() {
            Value::from_bool(i == 2)
        } else {
            Value::from_bool(false)
        }
    }

    let predicate = make_test_closure(equals_two_closure, 1);
    let result = rt_filter(predicate, dict);
    let new_dict = result.as_dict().expect("should be a dict");
    assert_eq!(new_dict.len(), 1);
    assert_eq!(new_dict.get(&Value::from_integer(1)), Some(&Value::from_integer(2)));
}

#[test]
fn builtin_filter_string() {
    // filter(_ == "a", "ab") → ["a"]
    // String filter returns List
    let s = Value::from_string("ab");
    let predicate = make_test_closure(equals_a_closure, 1);
    let result = rt_filter(predicate, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 1);
    assert_eq!(list[0].as_string(), Some("a"));
}

#[test]
fn builtin_filter_empty_list() {
    // filter(_ == 1, []) → []
    let list = Value::from_list(im::Vector::new());
    let predicate = make_test_closure(equals_one_closure, 1);
    let result = rt_filter(predicate, list);
    let new_list = result.as_list().expect("should be a list");
    assert!(new_list.is_empty());
}

#[test]
fn builtin_filter_none_match() {
    // filter(_ > 1, [1]) → []
    let list = Value::from_list(vec![
        Value::from_integer(1),
    ].into_iter().collect());
    let predicate = make_test_closure(greater_than_one_closure, 1);
    let result = rt_filter(predicate, list);
    let new_list = result.as_list().expect("should be a list");
    assert!(new_list.is_empty());
}

/// Test closure: returns truthy if value is odd (v % 2 != 0)
extern "C" fn is_odd_predicate_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::from_bool(false);
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_bool(i % 2 != 0)
    } else {
        Value::from_bool(false)
    }
}

// ===== filter() Range/LazySequence Tests (§11.4) =====

#[test]
fn builtin_filter_range_exclusive() {
    // filter(_ % 2, 1..5) |> list → [1, 3]
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(5), false, 1));
    let predicate = make_test_closure(is_odd_predicate_closure, 1);
    let result = rt_filter(predicate, range);
    // filter on LazySequence returns LazySequence
    assert!(result.is_lazy_sequence(), "filter on range should return LazySequence");
    // Convert to list to check values
    let list_result = rt_list(result);
    let list = list_result.as_list().expect("should convert to list");
    assert_eq!(list.len(), 2);
    assert_eq!(list[0].as_integer(), Some(1));
    assert_eq!(list[1].as_integer(), Some(3));
}

#[test]
fn builtin_filter_range_inclusive() {
    // filter(_ % 2, 1..=5) |> list → [1, 3, 5]
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(5), true, 1));
    let predicate = make_test_closure(is_odd_predicate_closure, 1);
    let result = rt_filter(predicate, range);
    assert!(result.is_lazy_sequence(), "filter on range should return LazySequence");
    let list_result = rt_list(result);
    let list = list_result.as_list().expect("should convert to list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_integer(), Some(1));
    assert_eq!(list[1].as_integer(), Some(3));
    assert_eq!(list[2].as_integer(), Some(5));
}

#[test]
fn builtin_filter_range_unbounded_take() {
    // filter(_ % 2, 0..) |> take(3) → [1, 3, 5]
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(0, None, false, 1));
    let predicate = make_test_closure(is_odd_predicate_closure, 1);
    let filtered = rt_filter(predicate, range);
    assert!(filtered.is_lazy_sequence(), "filter on range should return LazySequence");
    // Take first 3 odd numbers
    let taken = rt_take(Value::from_integer(3), filtered);
    let list = taken.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_integer(), Some(1));
    assert_eq!(list[1].as_integer(), Some(3));
    assert_eq!(list[2].as_integer(), Some(5));
}

// ===== flat_map() tests per LANG.txt §11.4 =====

use crate::builtins::rt_flat_map;

/// Test closure: doubles each list element: |x| [x, x * 2]
extern "C" fn duplicate_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::from_list(im::Vector::new());
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_list(vec![
            Value::from_integer(i),
            Value::from_integer(i * 2),
        ].into_iter().collect())
    } else {
        Value::from_list(im::Vector::new())
    }
}

/// Test closure: identity for list elements (returns input * 2 as per LANG.txt example)
extern "C" fn double_list_elements_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::from_list(im::Vector::new());
    }
    let arg = unsafe { *argv };
    if let Some(list) = arg.as_list() {
        // Double each element of the input list
        let doubled: im::Vector<Value> = list
            .iter()
            .map(|v| {
                if let Some(i) = v.as_integer() {
                    Value::from_integer(i * 2)
                } else {
                    *v
                }
            })
            .collect();
        Value::from_list(doubled)
    } else {
        Value::from_list(im::Vector::new())
    }
}

#[test]
fn builtin_flat_map_list() {
    // flat_map(_ * 2, [[1, 2], [3, 4]]) → [2, 4, 6, 8]
    let inner1 = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let inner2 = Value::from_list(vec![
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let list = Value::from_list(vec![inner1, inner2].into_iter().collect());
    let mapper = make_test_closure(double_list_elements_closure, 1);
    let result = rt_flat_map(mapper, list);
    let flat = result.as_list().expect("should be a list");
    assert_eq!(flat.len(), 4);
    assert_eq!(flat[0].as_integer(), Some(2));
    assert_eq!(flat[1].as_integer(), Some(4));
    assert_eq!(flat[2].as_integer(), Some(6));
    assert_eq!(flat[3].as_integer(), Some(8));
}

#[test]
fn builtin_flat_map_expand() {
    // flat_map(|x| [x, x * 2], [1, 2]) → [1, 2, 2, 4]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let mapper = make_test_closure(duplicate_closure, 1);
    let result = rt_flat_map(mapper, list);
    let flat = result.as_list().expect("should be a list");
    assert_eq!(flat.len(), 4);
    assert_eq!(flat[0].as_integer(), Some(1));
    assert_eq!(flat[1].as_integer(), Some(2));
    assert_eq!(flat[2].as_integer(), Some(2));
    assert_eq!(flat[3].as_integer(), Some(4));
}

#[test]
fn builtin_flat_map_empty() {
    // flat_map(|x| [x, x * 2], []) → []
    let list = Value::from_list(im::Vector::new());
    let mapper = make_test_closure(duplicate_closure, 1);
    let result = rt_flat_map(mapper, list);
    let flat = result.as_list().expect("should be a list");
    assert!(flat.is_empty());
}

#[test]
fn builtin_flat_map_range() {
    // flat_map(|x| [x, x * 2], 1..4) → [1, 2, 2, 4, 3, 6]
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(4), false, 1);
    let v = Value::from_lazy_sequence(range);
    let mapper = make_test_closure(duplicate_closure, 1);
    let result = rt_flat_map(mapper, v);
    let flat = result.as_list().expect("should be a list");
    assert_eq!(flat.len(), 6);
    assert_eq!(flat[0].as_integer(), Some(1));
    assert_eq!(flat[1].as_integer(), Some(2));
    assert_eq!(flat[2].as_integer(), Some(2));
    assert_eq!(flat[3].as_integer(), Some(4));
    assert_eq!(flat[4].as_integer(), Some(3));
    assert_eq!(flat[5].as_integer(), Some(6));
}

// ===== filter_map() tests per LANG.txt §11.4 =====

use crate::builtins::rt_filter_map;

/// Test closure: returns doubled value if odd, nil otherwise
/// |v| if v % 2 { v * 2 }
extern "C" fn double_if_odd_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::nil();
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        if i % 2 != 0 {
            Value::from_integer(i * 2)
        } else {
            Value::nil()
        }
    } else {
        Value::nil()
    }
}

#[test]
fn builtin_filter_map_list() {
    // [1, 2, 3, 4] |> filter_map(|v| if v % 2 { v * 2 }) → [2, 6]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let mapper = make_test_closure(double_if_odd_closure, 1);
    let result = rt_filter_map(mapper, list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 2);
    assert_eq!(new_list[0].as_integer(), Some(2));   // 1 * 2
    assert_eq!(new_list[1].as_integer(), Some(6));   // 3 * 2
}

#[test]
fn builtin_filter_map_set() {
    // {1, 2, 3, 4} |> filter_map(|v| if v % 2 { v * 2 }) → {2, 6}
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let mapper = make_test_closure(double_if_odd_closure, 1);
    let result = rt_filter_map(mapper, set);
    let new_set = result.as_set().expect("should be a set");
    assert_eq!(new_set.len(), 2);
    assert!(new_set.contains(&Value::from_integer(2)));
    assert!(new_set.contains(&Value::from_integer(6)));
}

#[test]
fn builtin_filter_map_empty() {
    let list = Value::from_list(im::Vector::new());
    let mapper = make_test_closure(double_if_odd_closure, 1);
    let result = rt_filter_map(mapper, list);
    let new_list = result.as_list().expect("should be a list");
    assert!(new_list.is_empty());
}

#[test]
fn builtin_filter_map_range() {
    // 1..5 |> filter_map(|v| if v % 2 { v * 2 }) → [2, 6]
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let mapper = make_test_closure(double_if_odd_closure, 1);
    let result = rt_filter_map(mapper, v);
    let filtered = result.as_list().expect("should be a list");
    assert_eq!(filtered.len(), 2);
    assert_eq!(filtered[0].as_integer(), Some(2)); // 1 * 2
    assert_eq!(filtered[1].as_integer(), Some(6)); // 3 * 2
}

// ===== find_map() tests per LANG.txt §11.4 =====

use crate::builtins::rt_find_map;

#[test]
fn builtin_find_map_list() {
    // [1, 2] |> find_map(|v| if v % 2 { v * 2 }) → 2
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let mapper = make_test_closure(double_if_odd_closure, 1);
    let result = rt_find_map(mapper, list);
    assert_eq!(result.as_integer(), Some(2)); // 1 * 2
}

#[test]
fn builtin_find_map_no_match() {
    // [2, 4] |> find_map(|v| if v % 2 { v * 2 }) → nil
    let list = Value::from_list(vec![
        Value::from_integer(2),
        Value::from_integer(4),
    ].into_iter().collect());
    let mapper = make_test_closure(double_if_odd_closure, 1);
    let result = rt_find_map(mapper, list);
    assert!(result.is_nil());
}

#[test]
fn builtin_find_map_empty() {
    let list = Value::from_list(im::Vector::new());
    let mapper = make_test_closure(double_if_odd_closure, 1);
    let result = rt_find_map(mapper, list);
    assert!(result.is_nil());
}

#[test]
fn builtin_find_map_range() {
    // 1..5 |> find_map(|v| if v % 2 { v * 2 }) → 2
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let mapper = make_test_closure(double_if_odd_closure, 1);
    let result = rt_find_map(mapper, v);
    assert_eq!(result.as_integer(), Some(2)); // 1 * 2
}

#[test]
fn builtin_find_map_range_no_match() {
    // 2..5 (step 2) |> find_map(|v| if v % 2 { v * 2 }) → nil (all even)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(2, Some(6), false, 2);
    let v = Value::from_lazy_sequence(range);
    let mapper = make_test_closure(double_if_odd_closure, 1);
    let result = rt_find_map(mapper, v);
    assert!(result.is_nil()); // 2, 4 are both even
}

// ===== Reduction Functions (§11.5) =====

use crate::builtins::{rt_reduce, rt_fold, rt_scan, rt_each};

/// Test closure: adds two integers (acc + val)
extern "C" fn sum_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 2 || argv.is_null() {
        return Value::nil();
    }
    let acc = unsafe { *argv };
    let val = unsafe { *argv.add(1) };
    if let (Some(a), Some(v)) = (acc.as_integer(), val.as_integer()) {
        Value::from_integer(a + v)
    } else {
        Value::nil()
    }
}

// reduce() tests
#[test]
fn builtin_reduce_list() {
    // reduce(+, [1, 2]) → 3
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let reducer = make_test_closure(sum_closure, 2);
    let result = rt_reduce(reducer, list);
    assert_eq!(result.as_integer(), Some(3));
}

#[test]
fn builtin_reduce_multiple() {
    // reduce(+, [1, 2, 3, 4]) → 10
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let reducer = make_test_closure(sum_closure, 2);
    let result = rt_reduce(reducer, list);
    assert_eq!(result.as_integer(), Some(10));
}

#[test]
fn builtin_reduce_single_element() {
    // reduce(+, [5]) → 5
    let list = Value::from_list(vec![
        Value::from_integer(5),
    ].into_iter().collect());
    let reducer = make_test_closure(sum_closure, 2);
    let result = rt_reduce(reducer, list);
    assert_eq!(result.as_integer(), Some(5));
}

#[test]
fn builtin_reduce_set() {
    // reduce(+, {1, 2}) → 3 (order not guaranteed, but sum is same)
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let reducer = make_test_closure(sum_closure, 2);
    let result = rt_reduce(reducer, set);
    assert_eq!(result.as_integer(), Some(3));
}

#[test]
#[should_panic(expected = "reduce on empty collection")]
fn builtin_reduce_empty_panics() {
    // Per LANG.txt §11.5: reduce on empty collection → RuntimeErr
    let list = Value::from_list(im::Vector::new());
    let reducer = make_test_closure(sum_closure, 2);
    let _result = rt_reduce(reducer, list);  // Should panic
}

// fold() tests
#[test]
fn builtin_fold_list() {
    // fold(0, +, [1, 2]) → 3
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(0);
    let result = rt_fold(initial, folder, list);
    assert_eq!(result.as_integer(), Some(3));
}

#[test]
fn builtin_fold_with_initial() {
    // fold(10, +, [1, 2]) → 13
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(10);
    let result = rt_fold(initial, folder, list);
    assert_eq!(result.as_integer(), Some(13));
}

#[test]
fn builtin_fold_empty_returns_initial() {
    // fold(0, +, []) → 0
    let list = Value::from_list(im::Vector::new());
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(42);
    let result = rt_fold(initial, folder, list);
    assert_eq!(result.as_integer(), Some(42));
}

#[test]
fn builtin_fold_set() {
    // fold(0, +, {1, 2}) → 3
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(0);
    let result = rt_fold(initial, folder, set);
    assert_eq!(result.as_integer(), Some(3));
}

// scan() tests
#[test]
fn builtin_scan_list() {
    // scan(0, +, [1, 2]) → [1, 3]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(0);
    let result = rt_scan(initial, folder, list);
    let scanned = result.as_list().expect("should be a list");
    assert_eq!(scanned.len(), 2);
    assert_eq!(scanned[0].as_integer(), Some(1));  // 0 + 1
    assert_eq!(scanned[1].as_integer(), Some(3));  // 1 + 2
}

#[test]
fn builtin_scan_empty() {
    // scan(0, +, []) → []
    let list = Value::from_list(im::Vector::new());
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(0);
    let result = rt_scan(initial, folder, list);
    let scanned = result.as_list().expect("should be a list");
    assert!(scanned.is_empty());
}

// fold_s() tests
use crate::builtins::rt_fold_s;

/// Test closure for fold_s: Fibonacci pattern |[a, b], _| [b, a + b]
extern "C" fn fibonacci_folder(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 2 || argv.is_null() {
        return Value::nil();
    }
    let state = unsafe { *argv };
    // Second arg is the iteration value which we ignore for fibonacci

    if let Some(list) = state.as_list() {
        if list.len() >= 2 {
            let a = list[0].as_integer().unwrap_or(0);
            let b = list[1].as_integer().unwrap_or(0);
            // Return [b, a + b]
            return Value::from_list(vec![
                Value::from_integer(b),
                Value::from_integer(a + b),
            ].into_iter().collect());
        }
    }
    Value::nil()
}

#[test]
fn builtin_fold_s_fibonacci() {
    // fold_s([0, 1], |[a, b], _| [b, a + b], 1..10) → 55
    // This computes fib(10) using state
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
        Value::from_integer(4),
        Value::from_integer(5),
        Value::from_integer(6),
        Value::from_integer(7),
        Value::from_integer(8),
        Value::from_integer(9),
    ].into_iter().collect());
    let folder = make_test_closure(fibonacci_folder, 2);
    let initial = Value::from_list(vec![
        Value::from_integer(0),
        Value::from_integer(1),
    ].into_iter().collect());
    let result = rt_fold_s(initial, folder, list);
    // After 9 iterations starting from [0, 1]:
    // [0,1] -> [1,1] -> [1,2] -> [2,3] -> [3,5] -> [5,8] -> [8,13] -> [13,21] -> [21,34] -> [34,55]
    // First element is 34
    assert_eq!(result.as_integer(), Some(34));
}

#[test]
fn builtin_fold_s_empty_returns_first_of_initial() {
    // fold_s([42, 0], fn, []) → 42
    let list = Value::from_list(im::Vector::new());
    let folder = make_test_closure(fibonacci_folder, 2);
    let initial = Value::from_list(vec![
        Value::from_integer(42),
        Value::from_integer(0),
    ].into_iter().collect());
    let result = rt_fold_s(initial, folder, list);
    assert_eq!(result.as_integer(), Some(42));
}

#[test]
fn builtin_fold_s_with_range() {
    // fold_s([0, 1], |[a, b], _| [b, a + b], 1..10) → 34
    // This computes fibonacci using range instead of list
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(10), false, 1));
    let folder = make_test_closure(fibonacci_folder, 2);
    let initial = Value::from_list(vec![
        Value::from_integer(0),
        Value::from_integer(1),
    ].into_iter().collect());
    let result = rt_fold_s(initial, folder, range);
    // After 9 iterations (1..10 has 9 elements) starting from [0, 1]:
    // [0,1] -> [1,1] -> [1,2] -> [2,3] -> [3,5] -> [5,8] -> [8,13] -> [13,21] -> [21,34]
    // First element is 34
    assert_eq!(result.as_integer(), Some(34));
}

// each() tests
#[test]
fn builtin_each_returns_nil() {
    // each always returns nil
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let mapper = make_test_closure(add_one_closure, 1);
    let result = rt_each(mapper, list);
    assert!(result.is_nil());
}

#[test]
fn builtin_each_empty_returns_nil() {
    let list = Value::from_list(im::Vector::new());
    let mapper = make_test_closure(add_one_closure, 1);
    let result = rt_each(mapper, list);
    assert!(result.is_nil());
}

#[test]
fn builtin_each_with_range() {
    // each should iterate over bounded range and return nil
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(4), false, 1));
    let mapper = make_test_closure(add_one_closure, 1);
    let result = rt_each(mapper, range);
    // each always returns nil
    assert!(result.is_nil());
}

// ===== Search Functions (§11.7) =====

use crate::builtins::rt_find;

/// Test closure: returns truthy if value is odd (v % 2 != 0)
extern "C" fn is_odd_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::from_bool(false);
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_bool(i % 2 != 0)
    } else {
        Value::from_bool(false)
    }
}

// find() tests per LANG.txt §11.7
#[test]
fn builtin_find_list() {
    // find(_ % 2, [1, 2]) → 1
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let predicate = make_test_closure(is_odd_closure, 1);
    let result = rt_find(predicate, list);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_find_list_no_match() {
    // find(_ % 2, [2, 4]) → nil
    let list = Value::from_list(vec![
        Value::from_integer(2),
        Value::from_integer(4),
    ].into_iter().collect());
    let predicate = make_test_closure(is_odd_closure, 1);
    let result = rt_find(predicate, list);
    assert!(result.is_nil());
}

#[test]
fn builtin_find_set() {
    // find(_ % 2, {1, 2}) → 1
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let predicate = make_test_closure(is_odd_closure, 1);
    let result = rt_find(predicate, set);
    // Set iteration order is not guaranteed, but since 1 is odd it should be found
    assert!(result.as_integer().is_some());
    let i = result.as_integer().unwrap();
    assert!(i % 2 != 0); // Should be an odd number
}

#[test]
fn builtin_find_string() {
    // find(_ == "b", "ab") → "b"
    extern "C" fn equals_b_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(s) = arg.as_string() {
            Value::from_bool(s == "b")
        } else {
            Value::from_bool(false)
        }
    }
    let s = Value::from_string("ab");
    let predicate = make_test_closure(equals_b_closure, 1);
    let result = rt_find(predicate, s);
    assert_eq!(result.as_string(), Some("b"));
}

#[test]
fn builtin_find_empty_list() {
    // find(_ % 2, []) → nil
    let list = Value::from_list(im::Vector::new());
    let predicate = make_test_closure(is_odd_closure, 1);
    let result = rt_find(predicate, list);
    assert!(result.is_nil());
}

#[test]
fn builtin_find_range() {
    // find(_ > 5, 1..10) → 6
    use crate::heap::LazySequenceObject;
    extern "C" fn greater_than_5(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(i) = arg.as_integer() {
            Value::from_bool(i > 5)
        } else {
            Value::from_bool(false)
        }
    }
    let range = LazySequenceObject::range(1, Some(10), false, 1);
    let v = Value::from_lazy_sequence(range);
    let predicate = make_test_closure(greater_than_5, 1);
    let result = rt_find(predicate, v);
    assert_eq!(result.as_integer(), Some(6));
}

#[test]
fn builtin_find_range_no_match() {
    // find(_ > 100, 1..5) → nil
    use crate::heap::LazySequenceObject;
    extern "C" fn greater_than_100(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(i) = arg.as_integer() {
            Value::from_bool(i > 100)
        } else {
            Value::from_bool(false)
        }
    }
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let predicate = make_test_closure(greater_than_100, 1);
    let result = rt_find(predicate, v);
    assert!(result.is_nil());
}

#[test]
fn builtin_find_filtered_range() {
    // find(_ > 2, filter(_ % 2, 1..10)) → 3
    // First odd > 2 in range 1..10 is 3
    use crate::heap::LazySequenceObject;

    extern "C" fn greater_than_2(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(i) = arg.as_integer() {
            Value::from_bool(i > 2)
        } else {
            Value::from_bool(false)
        }
    }

    // Create range 1..10
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(10), false, 1));
    // Filter to odd numbers
    let is_odd_pred = make_test_closure(is_odd_closure, 1);
    let filtered = rt_filter(is_odd_pred, range);
    // Find first > 2
    let find_pred = make_test_closure(greater_than_2, 1);
    let result = rt_find(find_pred, filtered);
    assert_eq!(result.as_integer(), Some(3), "first odd > 2 should be 3");
}

// count() tests per LANG.txt §11.7
use crate::builtins::rt_count;

#[test]
fn builtin_count_list() {
    // count(_ % 2, [1, 2, 3, 4]) → 2
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let predicate = make_test_closure(is_odd_closure, 1);
    let result = rt_count(predicate, list);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_count_set() {
    // count(_ % 2, {1, 2, 3, 4}) → 2
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let predicate = make_test_closure(is_odd_closure, 1);
    let result = rt_count(predicate, set);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_count_string() {
    // count(_ == "a", "abab") → 2
    extern "C" fn count_a_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(s) = arg.as_string() {
            Value::from_bool(s == "a")
        } else {
            Value::from_bool(false)
        }
    }
    let s = Value::from_string("abab");
    let predicate = make_test_closure(count_a_closure, 1);
    let result = rt_count(predicate, s);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_count_empty_list() {
    // count(_ % 2, []) → 0
    let list = Value::from_list(im::Vector::new());
    let predicate = make_test_closure(is_odd_closure, 1);
    let result = rt_count(predicate, list);
    assert_eq!(result.as_integer(), Some(0));
}

#[test]
fn builtin_count_none_match() {
    // count(_ % 2, [2, 4]) → 0
    let list = Value::from_list(vec![
        Value::from_integer(2),
        Value::from_integer(4),
    ].into_iter().collect());
    let predicate = make_test_closure(is_odd_closure, 1);
    let result = rt_count(predicate, list);
    assert_eq!(result.as_integer(), Some(0));
}

#[test]
fn builtin_count_range() {
    // count(_ % 2, 1..10) → 5 (counts: 1, 3, 5, 7, 9)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(10), false, 1);
    let v = Value::from_lazy_sequence(range);
    let predicate = make_test_closure(is_odd_closure, 1);
    let result = rt_count(predicate, v);
    assert_eq!(result.as_integer(), Some(5));
}

#[test]
fn builtin_count_filtered_range() {
    // Count even numbers in a filtered range of odd numbers → 0
    // filter(_ % 2, 1..10) gives [1, 3, 5, 7, 9] - all odd
    // count(_ % 2 == 0, [1, 3, 5, 7, 9]) → 0
    use crate::heap::LazySequenceObject;

    extern "C" fn is_even(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(i) = arg.as_integer() {
            Value::from_bool(i % 2 == 0)
        } else {
            Value::from_bool(false)
        }
    }

    // Create range 1..10
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(10), false, 1));
    // Filter to odd numbers only
    let is_odd_pred = make_test_closure(is_odd_closure, 1);
    let filtered = rt_filter(is_odd_pred, range);
    // Count even numbers (should be 0 since all filtered values are odd)
    let is_even_pred = make_test_closure(is_even, 1);
    let result = rt_count(is_even_pred, filtered);
    assert_eq!(result.as_integer(), Some(0), "no even numbers in filtered odd range");
}

#[test]
fn builtin_count_filtered_range_with_matches() {
    // Count numbers > 5 in a filtered range of odd numbers
    // filter(_ % 2, 1..10) gives [1, 3, 5, 7, 9]
    // count(_ > 5, [1, 3, 5, 7, 9]) → 2 (7 and 9)
    use crate::heap::LazySequenceObject;

    extern "C" fn greater_than_5(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(i) = arg.as_integer() {
            Value::from_bool(i > 5)
        } else {
            Value::from_bool(false)
        }
    }

    // Create range 1..10
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(10), false, 1));
    // Filter to odd numbers only
    let is_odd_pred = make_test_closure(is_odd_closure, 1);
    let filtered = rt_filter(is_odd_pred, range);
    // Count numbers > 5
    let gt5_pred = make_test_closure(greater_than_5, 1);
    let result = rt_count(gt5_pred, filtered);
    assert_eq!(result.as_integer(), Some(2), "7 and 9 are > 5");
}

// ===== Aggregation Functions (§11.8) =====

use crate::builtins::{rt_sum, rt_max, rt_min};

// sum() tests per LANG.txt §11.8
#[test]
fn builtin_sum_list() {
    // sum([1, 2]) → 3
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_sum(list);
    assert_eq!(result.as_integer(), Some(3));
}

#[test]
fn builtin_sum_list_decimals() {
    // sum([1.5, 2.5]) → 4.0
    let list = Value::from_list(vec![
        Value::from_decimal(1.5),
        Value::from_decimal(2.5),
    ].into_iter().collect());
    let result = rt_sum(list);
    assert_eq!(result.as_decimal(), Some(4.0));
}

#[test]
fn builtin_sum_empty_list() {
    // sum([]) → 0
    let list = Value::from_list(im::Vector::new());
    let result = rt_sum(list);
    assert_eq!(result.as_integer(), Some(0));
}

#[test]
fn builtin_sum_set() {
    // sum({1, 2}) → 3
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_sum(set);
    assert_eq!(result.as_integer(), Some(3));
}

#[test]
fn builtin_sum_dict_values() {
    // sum(#{1: 2, 3: 4}) → 6 (sums values)
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    entries.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(entries);
    let result = rt_sum(dict);
    assert_eq!(result.as_integer(), Some(6));
}

#[test]
fn builtin_sum_range() {
    // sum(1..5) → 1+2+3+4 = 10
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_sum(v);
    assert_eq!(result.as_integer(), Some(10));
}

#[test]
fn builtin_sum_inclusive_range() {
    // sum(1..=5) → 1+2+3+4+5 = 15
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), true, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_sum(v);
    assert_eq!(result.as_integer(), Some(15));
}

#[test]
fn builtin_sum_large_range() {
    // sum(1..=100) → 5050 (Gauss sum)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(100), true, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_sum(v);
    assert_eq!(result.as_integer(), Some(5050));
}

// max() tests per LANG.txt §11.8
#[test]
fn builtin_max_list() {
    // max([1, 2]) → 2
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_max(list);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_max_empty_list() {
    // max([]) → nil
    let list = Value::from_list(im::Vector::new());
    let result = rt_max(list);
    assert!(result.is_nil());
}

#[test]
fn builtin_max_set() {
    // max({1, 2}) → 2
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_max(set);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_max_dict_values() {
    // max(#{1: 2, 3: 4}) → 4 (max of values)
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    entries.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(entries);
    let result = rt_max(dict);
    assert_eq!(result.as_integer(), Some(4));
}

#[test]
fn builtin_max_range() {
    // max(1..5) → 4 (ascending, exclusive)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_max(v);
    assert_eq!(result.as_integer(), Some(4));
}

#[test]
fn builtin_max_descending_range() {
    // max(5..1) → 5 (descending, max is first)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(5, Some(1), false, -1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_max(v);
    assert_eq!(result.as_integer(), Some(5));
}

// min() tests per LANG.txt §11.8
#[test]
fn builtin_min_list() {
    // min([1, 2]) → 1
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_min(list);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_min_empty_list() {
    // min([]) → nil
    let list = Value::from_list(im::Vector::new());
    let result = rt_min(list);
    assert!(result.is_nil());
}

#[test]
fn builtin_min_set() {
    // min({1, 2}) → 1
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_min(set);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_min_dict_values() {
    // min(#{1: 2, 3: 4}) → 2 (min of values)
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    entries.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(entries);
    let result = rt_min(dict);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_min_range() {
    // min(1..5) → 1 (ascending, min is first)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_min(v);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_min_descending_range() {
    // min(5..1) → 2 (descending, exclusive, min is last)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(5, Some(1), false, -1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_min(v);
    assert_eq!(result.as_integer(), Some(2));
}

// ===== Sequence Manipulation Functions (§11.9) =====

use crate::builtins::{rt_skip, rt_take, rt_sort, rt_reverse, rt_rotate, rt_chunk};

// skip() tests per LANG.txt §11.9
#[test]
fn builtin_skip_list() {
    // skip(1, [1, 2, 3]) → [2, 3]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_skip(Value::from_integer(1), list);
    let skipped = result.as_list().expect("should be a list");
    assert_eq!(skipped.len(), 2);
    assert_eq!(skipped[0].as_integer(), Some(2));
    assert_eq!(skipped[1].as_integer(), Some(3));
}

#[test]
fn builtin_skip_list_all() {
    // skip(5, [1, 2, 3]) → []
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_skip(Value::from_integer(5), list);
    let skipped = result.as_list().expect("should be a list");
    assert!(skipped.is_empty());
}

#[test]
fn builtin_skip_set() {
    // skip(1, {1, 2, 3}) → {?, ?} (order not guaranteed)
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_skip(Value::from_integer(1), set);
    let skipped = result.as_set().expect("should be a set");
    assert_eq!(skipped.len(), 2);
}

#[test]
fn builtin_skip_range() {
    // skip(2, 1..5) → LazySequence(3..5) → [3, 4]
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_skip(Value::from_integer(2), v);
    // Result should be a LazySequence, convert to list to verify
    let list = rt_list(result);
    let elements = list.as_list().expect("should be a list");
    assert_eq!(elements.len(), 2);
    assert_eq!(elements[0].as_integer(), Some(3));
    assert_eq!(elements[1].as_integer(), Some(4));
}

#[test]
fn builtin_skip_range_all() {
    // skip(10, 1..5) → empty
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_skip(Value::from_integer(10), v);
    let list = rt_list(result);
    let elements = list.as_list().expect("should be a list");
    assert!(elements.is_empty());
}

// take() tests per LANG.txt §11.9
#[test]
fn builtin_take_list() {
    // take(2, [1, 2, 3]) → [1, 2]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_take(Value::from_integer(2), list);
    let taken = result.as_list().expect("should be a list");
    assert_eq!(taken.len(), 2);
    assert_eq!(taken[0].as_integer(), Some(1));
    assert_eq!(taken[1].as_integer(), Some(2));
}

#[test]
fn builtin_take_list_more_than_size() {
    // take(5, [1, 2]) → [1, 2]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_take(Value::from_integer(5), list);
    let taken = result.as_list().expect("should be a list");
    assert_eq!(taken.len(), 2);
}

#[test]
fn builtin_take_set() {
    // take(2, {1, 2, 3}) → [?, ?] (order not guaranteed, returns list)
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_take(Value::from_integer(2), set);
    let taken = result.as_list().expect("should be a list");
    assert_eq!(taken.len(), 2);
}

#[test]
fn builtin_take_range() {
    // take(2, 1..5) → [1, 2]
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_take(Value::from_integer(2), v);
    let taken = result.as_list().expect("should be a list");
    assert_eq!(taken.len(), 2);
    assert_eq!(taken[0].as_integer(), Some(1));
    assert_eq!(taken[1].as_integer(), Some(2));
}

#[test]
fn builtin_take_range_more_than_size() {
    // take(10, 1..5) → [1, 2, 3, 4]
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_take(Value::from_integer(10), v);
    let taken = result.as_list().expect("should be a list");
    assert_eq!(taken.len(), 4);
}

// sort() tests per LANG.txt §11.9
/// Test closure: subtraction comparator (a - b)
extern "C" fn subtraction_comparator(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 2 || argv.is_null() {
        return Value::from_integer(0);
    }
    let a = unsafe { *argv };
    let b = unsafe { *argv.add(1) };
    if let (Some(ai), Some(bi)) = (a.as_integer(), b.as_integer()) {
        Value::from_integer(ai - bi)
    } else {
        Value::from_integer(0)
    }
}

/// Test closure: greater-than comparator (a > b)
extern "C" fn greater_comparator(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 2 || argv.is_null() {
        return Value::from_bool(false);
    }
    let a = unsafe { *argv };
    let b = unsafe { *argv.add(1) };
    if let (Some(ai), Some(bi)) = (a.as_integer(), b.as_integer()) {
        Value::from_bool(ai > bi)
    } else {
        Value::from_bool(false)
    }
}

/// Test closure: less-than comparator (a < b)
extern "C" fn less_comparator(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 2 || argv.is_null() {
        return Value::from_bool(false);
    }
    let a = unsafe { *argv };
    let b = unsafe { *argv.add(1) };
    if let (Some(ai), Some(bi)) = (a.as_integer(), b.as_integer()) {
        Value::from_bool(ai < bi)
    } else {
        Value::from_bool(false)
    }
}

#[test]
fn builtin_sort_ascending() {
    // sort(<, [3, 2, 1]) → [1, 2, 3]
    let list = Value::from_list(vec![
        Value::from_integer(3),
        Value::from_integer(2),
        Value::from_integer(1),
    ].into_iter().collect());
    let comparator = make_test_closure(less_comparator, 2);
    let result = rt_sort(comparator, list);
    let sorted = result.as_list().expect("should be a list");
    assert_eq!(sorted.len(), 3);
    assert_eq!(sorted[0].as_integer(), Some(1));
    assert_eq!(sorted[1].as_integer(), Some(2));
    assert_eq!(sorted[2].as_integer(), Some(3));
}

#[test]
fn builtin_sort_descending() {
    // sort(>, [3, 2, 1]) → [3, 2, 1] (already descending)
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let comparator = make_test_closure(greater_comparator, 2);
    let result = rt_sort(comparator, list);
    let sorted = result.as_list().expect("should be a list");
    assert_eq!(sorted.len(), 3);
    assert_eq!(sorted[0].as_integer(), Some(3));
    assert_eq!(sorted[1].as_integer(), Some(2));
    assert_eq!(sorted[2].as_integer(), Some(1));
}

#[test]
fn builtin_sort_with_subtraction() {
    // sort(-, [3, 2, 1]) → [1, 2, 3]
    let list = Value::from_list(vec![
        Value::from_integer(3),
        Value::from_integer(2),
        Value::from_integer(1),
    ].into_iter().collect());
    let comparator = make_test_closure(subtraction_comparator, 2);
    let result = rt_sort(comparator, list);
    let sorted = result.as_list().expect("should be a list");
    assert_eq!(sorted.len(), 3);
    assert_eq!(sorted[0].as_integer(), Some(1));
    assert_eq!(sorted[1].as_integer(), Some(2));
    assert_eq!(sorted[2].as_integer(), Some(3));
}

#[test]
fn builtin_sort_range() {
    // sort(>, 1..5) → [4, 3, 2, 1] (descending)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let comparator = make_test_closure(greater_comparator, 2);
    let result = rt_sort(comparator, v);
    let sorted = result.as_list().expect("should be a list");
    assert_eq!(sorted.len(), 4);
    assert_eq!(sorted[0].as_integer(), Some(4));
    assert_eq!(sorted[1].as_integer(), Some(3));
    assert_eq!(sorted[2].as_integer(), Some(2));
    assert_eq!(sorted[3].as_integer(), Some(1));
}

// reverse() tests per LANG.txt §11.9
#[test]
fn builtin_reverse_list() {
    // reverse([1, 2, 3]) → [3, 2, 1]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_reverse(list);
    let reversed = result.as_list().expect("should be a list");
    assert_eq!(reversed.len(), 3);
    assert_eq!(reversed[0].as_integer(), Some(3));
    assert_eq!(reversed[1].as_integer(), Some(2));
    assert_eq!(reversed[2].as_integer(), Some(1));
}

#[test]
fn builtin_reverse_string() {
    // reverse("abc") → "cba"
    let s = Value::from_string("abc");
    let result = rt_reverse(s);
    assert_eq!(result.as_string(), Some("cba"));
}

#[test]
fn builtin_reverse_empty_list() {
    // reverse([]) → []
    let list = Value::from_list(im::Vector::new());
    let result = rt_reverse(list);
    let reversed = result.as_list().expect("should be a list");
    assert!(reversed.is_empty());
}

#[test]
fn builtin_reverse_range() {
    // reverse(1..5) → [4, 3, 2, 1]
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_reverse(v);
    // reverse returns a list for bounded sequences
    let reversed = result.as_list().expect("should be a list");
    assert_eq!(reversed.len(), 4);
    assert_eq!(reversed[0].as_integer(), Some(4));
    assert_eq!(reversed[1].as_integer(), Some(3));
    assert_eq!(reversed[2].as_integer(), Some(2));
    assert_eq!(reversed[3].as_integer(), Some(1));
}

// rotate() tests per LANG.txt §11.9
#[test]
fn builtin_rotate_positive() {
    // rotate(1, [1, 2, 3]) → [3, 1, 2]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_rotate(Value::from_integer(1), list);
    let rotated = result.as_list().expect("should be a list");
    assert_eq!(rotated.len(), 3);
    assert_eq!(rotated[0].as_integer(), Some(3));
    assert_eq!(rotated[1].as_integer(), Some(1));
    assert_eq!(rotated[2].as_integer(), Some(2));
}

#[test]
fn builtin_rotate_negative() {
    // rotate(-1, [1, 2, 3]) → [2, 3, 1]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_rotate(Value::from_integer(-1), list);
    let rotated = result.as_list().expect("should be a list");
    assert_eq!(rotated.len(), 3);
    assert_eq!(rotated[0].as_integer(), Some(2));
    assert_eq!(rotated[1].as_integer(), Some(3));
    assert_eq!(rotated[2].as_integer(), Some(1));
}

#[test]
fn builtin_rotate_multiple() {
    // rotate(2, [1, 2, 3, 4]) → [3, 4, 1, 2]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let result = rt_rotate(Value::from_integer(2), list);
    let rotated = result.as_list().expect("should be a list");
    assert_eq!(rotated.len(), 4);
    assert_eq!(rotated[0].as_integer(), Some(3));
    assert_eq!(rotated[1].as_integer(), Some(4));
    assert_eq!(rotated[2].as_integer(), Some(1));
    assert_eq!(rotated[3].as_integer(), Some(2));
}

// chunk() tests per LANG.txt §11.9
#[test]
fn builtin_chunk_even() {
    // chunk(2, [1, 2, 3, 4]) → [[1, 2], [3, 4]]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let result = rt_chunk(Value::from_integer(2), list);
    let chunks = result.as_list().expect("should be a list");
    assert_eq!(chunks.len(), 2);

    let chunk1 = chunks[0].as_list().expect("chunk should be a list");
    assert_eq!(chunk1.len(), 2);
    assert_eq!(chunk1[0].as_integer(), Some(1));
    assert_eq!(chunk1[1].as_integer(), Some(2));

    let chunk2 = chunks[1].as_list().expect("chunk should be a list");
    assert_eq!(chunk2.len(), 2);
    assert_eq!(chunk2[0].as_integer(), Some(3));
    assert_eq!(chunk2[1].as_integer(), Some(4));
}

#[test]
fn builtin_chunk_uneven() {
    // chunk(2, [1, 2, 3]) → [[1, 2], [3]]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_chunk(Value::from_integer(2), list);
    let chunks = result.as_list().expect("should be a list");
    assert_eq!(chunks.len(), 2);

    let chunk1 = chunks[0].as_list().expect("chunk should be a list");
    assert_eq!(chunk1.len(), 2);

    let chunk2 = chunks[1].as_list().expect("chunk should be a list");
    assert_eq!(chunk2.len(), 1);
    assert_eq!(chunk2[0].as_integer(), Some(3));
}

#[test]
fn builtin_chunk_empty() {
    // chunk(2, []) → []
    let list = Value::from_list(im::Vector::new());
    let result = rt_chunk(Value::from_integer(2), list);
    let chunks = result.as_list().expect("should be a list");
    assert!(chunks.is_empty());
}

// ===== Set Operations (§11.10) =====

use crate::builtins::{rt_union, rt_intersection};

// union() tests per LANG.txt §11.10
#[test]
fn builtin_union_sets() {
    // union({1, 2}, {2, 3}) → {1, 2, 3}
    let set1 = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let set2 = Value::from_set(vec![
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_union(set1, set2);
    let union_set = result.as_set().expect("should be a set");
    assert_eq!(union_set.len(), 3);
    assert!(union_set.contains(&Value::from_integer(1)));
    assert!(union_set.contains(&Value::from_integer(2)));
    assert!(union_set.contains(&Value::from_integer(3)));
}

#[test]
fn builtin_union_list_and_set() {
    // union([1, 2], {2, 3}) → {1, 2, 3}
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let set = Value::from_set(vec![
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_union(list, set);
    let union_set = result.as_set().expect("should be a set");
    assert_eq!(union_set.len(), 3);
}

// intersection() tests per LANG.txt §11.10
#[test]
fn builtin_intersection_sets() {
    // intersection({1, 2}, {2, 3}) → {2}
    let set1 = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let set2 = Value::from_set(vec![
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_intersection(set1, set2);
    let isect = result.as_set().expect("should be a set");
    assert_eq!(isect.len(), 1);
    assert!(isect.contains(&Value::from_integer(2)));
}

#[test]
fn builtin_intersection_no_common() {
    // intersection({1, 2}, {3, 4}) → {}
    let set1 = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let set2 = Value::from_set(vec![
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let result = rt_intersection(set1, set2);
    let isect = result.as_set().expect("should be a set");
    assert!(isect.is_empty());
}

// union() with Range support per LANG.txt §11.10
#[test]
fn builtin_union_with_range() {
    // union({1, 2}, 1..4) → {1, 2, 3}
    // Per LANG.txt: union({1, 2}, [2, 3], 1..4, "abc") → {1, 2, 3, "a", "b", "c"}
    use crate::heap::LazySequenceObject;
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(4), false, 1));
    let result = rt_union(set, range);
    let union_set = result.as_set().expect("should be a set");
    assert_eq!(union_set.len(), 3); // {1, 2, 3}
    assert!(union_set.contains(&Value::from_integer(1)));
    assert!(union_set.contains(&Value::from_integer(2)));
    assert!(union_set.contains(&Value::from_integer(3)));
}

// union() with String support per LANG.txt §11.10
#[test]
fn builtin_union_with_string() {
    // union({1, 2}, "ab") → {1, 2, "a", "b"}
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let string = Value::from_string("ab");
    let result = rt_union(set, string);
    let union_set = result.as_set().expect("should be a set");
    assert_eq!(union_set.len(), 4); // {1, 2, "a", "b"}
    assert!(union_set.contains(&Value::from_integer(1)));
    assert!(union_set.contains(&Value::from_integer(2)));
    assert!(union_set.contains(&Value::from_string("a")));
    assert!(union_set.contains(&Value::from_string("b")));
}

// intersection() with Range support per LANG.txt §11.10
#[test]
fn builtin_intersection_with_range() {
    // intersection({1, 2, 3}, 2..5) → {2, 3}
    use crate::heap::LazySequenceObject;
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let range = Value::from_lazy_sequence(LazySequenceObject::range(2, Some(5), false, 1));
    let result = rt_intersection(set, range);
    let isect = result.as_set().expect("should be a set");
    assert_eq!(isect.len(), 2); // {2, 3}
    assert!(isect.contains(&Value::from_integer(2)));
    assert!(isect.contains(&Value::from_integer(3)));
}

// ===== Predicates (§11.11) =====

use crate::builtins::{rt_includes, rt_excludes, rt_any, rt_all};

// includes?() tests per LANG.txt §11.11
#[test]
fn builtin_includes_list() {
    // includes?([1, 2], 1) → true
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_includes(list, Value::from_integer(1));
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_includes_list_false() {
    // includes?([1, 2], 3) → false
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_includes(list, Value::from_integer(3));
    assert_eq!(result.as_bool(), Some(false));
}

#[test]
fn builtin_includes_set() {
    // includes?({1, 2}, 1) → true
    let set = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_includes(set, Value::from_integer(1));
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_includes_dict_key() {
    // includes?(#{"a": 1}, "a") → true (checks keys)
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_string("a"), Value::from_integer(1));
    let dict = Value::from_dict(entries);
    let result = rt_includes(dict, Value::from_string("a"));
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_includes_string() {
    // includes?("ab", "a") → true
    let s = Value::from_string("ab");
    let result = rt_includes(s, Value::from_string("a"));
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_includes_range() {
    // includes?(1..10, 5) → true
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(10), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_includes(v, Value::from_integer(5));
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_includes_range_false() {
    // includes?(1..5, 10) → false
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let result = rt_includes(v, Value::from_integer(10));
    assert_eq!(result.as_bool(), Some(false));
}

// excludes?() tests per LANG.txt §11.11
#[test]
fn builtin_excludes_list() {
    // excludes?([1, 2], 3) → true
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_excludes(list, Value::from_integer(3));
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_excludes_list_false() {
    // excludes?([1, 2], 1) → false
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_excludes(list, Value::from_integer(1));
    assert_eq!(result.as_bool(), Some(false));
}

// any?() tests per LANG.txt §11.11
#[test]
fn builtin_any_list_true() {
    // any?(_ == 1, [1, 2]) → true
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let predicate = make_test_closure(equals_one_closure, 1);
    let result = rt_any(predicate, list);
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_any_list_false() {
    // any?(_ == 1, [2, 3]) → false
    let list = Value::from_list(vec![
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let predicate = make_test_closure(equals_one_closure, 1);
    let result = rt_any(predicate, list);
    assert_eq!(result.as_bool(), Some(false));
}

#[test]
fn builtin_any_empty_list() {
    // any?(_ == 1, []) → false
    let list = Value::from_list(im::Vector::new());
    let predicate = make_test_closure(equals_one_closure, 1);
    let result = rt_any(predicate, list);
    assert_eq!(result.as_bool(), Some(false));
}

#[test]
fn builtin_any_range_true() {
    // any?(_ % 2 == 0, 1..5) → true (2 and 4 are even)
    use crate::heap::LazySequenceObject;
    extern "C" fn is_even(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(i) = arg.as_integer() {
            Value::from_bool(i % 2 == 0)
        } else {
            Value::from_bool(false)
        }
    }
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let predicate = make_test_closure(is_even, 1);
    let result = rt_any(predicate, v);
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_any_range_false() {
    // any?(_ > 10, 1..5) → false
    use crate::heap::LazySequenceObject;
    extern "C" fn greater_than_10(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(i) = arg.as_integer() {
            Value::from_bool(i > 10)
        } else {
            Value::from_bool(false)
        }
    }
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let predicate = make_test_closure(greater_than_10, 1);
    let result = rt_any(predicate, v);
    assert_eq!(result.as_bool(), Some(false));
}

// all?() tests per LANG.txt §11.11
/// Test closure: returns true if value > 0
extern "C" fn positive_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::from_bool(false);
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_bool(i > 0)
    } else {
        Value::from_bool(false)
    }
}

#[test]
fn builtin_all_list_true() {
    // all?(_ > 0, [1, 2]) → true
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let predicate = make_test_closure(positive_closure, 1);
    let result = rt_all(predicate, list);
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_all_list_false() {
    // all?(_ > 0, [-1, 2]) → false
    let list = Value::from_list(vec![
        Value::from_integer(-1),
        Value::from_integer(2),
    ].into_iter().collect());
    let predicate = make_test_closure(positive_closure, 1);
    let result = rt_all(predicate, list);
    assert_eq!(result.as_bool(), Some(false));
}

#[test]
fn builtin_all_empty_list() {
    // all?(_ > 0, []) → true (vacuous truth)
    let list = Value::from_list(im::Vector::new());
    let predicate = make_test_closure(positive_closure, 1);
    let result = rt_all(predicate, list);
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_all_range_true() {
    // all?(_ > 0, 1..5) → true (1, 2, 3, 4 are all positive)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(1, Some(5), false, 1);
    let v = Value::from_lazy_sequence(range);
    let predicate = make_test_closure(positive_closure, 1);
    let result = rt_all(predicate, v);
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn builtin_all_range_false() {
    // all?(_ > 0, -2..3) → false (-2, -1, 0 are not positive)
    use crate::heap::LazySequenceObject;
    let range = LazySequenceObject::range(-2, Some(3), false, 1);
    let v = Value::from_lazy_sequence(range);
    let predicate = make_test_closure(positive_closure, 1);
    let result = rt_all(predicate, v);
    assert_eq!(result.as_bool(), Some(false));
}

// ===== Lazy Sequence Functions (§11.12-11.13) =====

use crate::builtins::{rt_repeat, rt_cycle, rt_iterate, rt_combinations, rt_range_fn};

#[test]
fn builtin_repeat_generates_lazy_sequence() {
    // repeat(1) returns a LazySequence
    let result = rt_repeat(Value::from_integer(1));
    assert!(result.is_lazy_sequence());
}

#[test]
fn builtin_repeat_take_produces_list() {
    // repeat(1) |> take(3) → [1, 1, 1]
    let lazy = rt_repeat(Value::from_integer(1));
    let result = rt_take(Value::from_integer(3), lazy);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_integer(), Some(1));
    assert_eq!(list[1].as_integer(), Some(1));
    assert_eq!(list[2].as_integer(), Some(1));
}

#[test]
fn builtin_repeat_string() {
    // repeat("x") |> take(3) → ["x", "x", "x"]
    let lazy = rt_repeat(Value::from_string("x"));
    let result = rt_take(Value::from_integer(3), lazy);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_string(), Some("x"));
    assert_eq!(list[1].as_string(), Some("x"));
    assert_eq!(list[2].as_string(), Some("x"));
}

// cycle() tests
#[test]
fn builtin_cycle_generates_lazy_sequence() {
    // cycle([1, 2, 3]) returns a LazySequence
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_cycle(list);
    assert!(result.is_lazy_sequence());
}

#[test]
fn builtin_cycle_take_produces_list() {
    // cycle([1, 2, 3]) |> take(7) → [1, 2, 3, 1, 2, 3, 1]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let lazy = rt_cycle(list);
    let result = rt_take(Value::from_integer(7), lazy);
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 7);
    assert_eq!(out[0].as_integer(), Some(1));
    assert_eq!(out[1].as_integer(), Some(2));
    assert_eq!(out[2].as_integer(), Some(3));
    assert_eq!(out[3].as_integer(), Some(1));
    assert_eq!(out[4].as_integer(), Some(2));
    assert_eq!(out[5].as_integer(), Some(3));
    assert_eq!(out[6].as_integer(), Some(1));
}

#[test]
fn builtin_cycle_string() {
    // cycle("abc") |> take(7) → ["a", "b", "c", "a", "b", "c", "a"]
    let s = Value::from_string("abc");
    let lazy = rt_cycle(s);
    let result = rt_take(Value::from_integer(7), lazy);
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 7);
    assert_eq!(out[0].as_string(), Some("a"));
    assert_eq!(out[1].as_string(), Some("b"));
    assert_eq!(out[2].as_string(), Some("c"));
    assert_eq!(out[3].as_string(), Some("a"));
}

// iterate() tests
#[test]
fn builtin_iterate_generates_lazy_sequence() {
    // iterate(_ + 1, 0) returns a LazySequence
    let generator = make_test_closure(add_one_closure, 1);
    let result = rt_iterate(generator, Value::from_integer(0));
    assert!(result.is_lazy_sequence());
}

#[test]
fn builtin_iterate_take_produces_list() {
    // iterate(_ + 1, 0) |> take(5) → [0, 1, 2, 3, 4]
    let generator = make_test_closure(add_one_closure, 1);
    let lazy = rt_iterate(generator, Value::from_integer(0));
    let result = rt_take(Value::from_integer(5), lazy);
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 5);
    assert_eq!(out[0].as_integer(), Some(0));
    assert_eq!(out[1].as_integer(), Some(1));
    assert_eq!(out[2].as_integer(), Some(2));
    assert_eq!(out[3].as_integer(), Some(3));
    assert_eq!(out[4].as_integer(), Some(4));
}

/// Test closure: doubles a value
extern "C" fn double_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::nil();
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_integer(i * 2)
    } else {
        Value::nil()
    }
}

#[test]
fn builtin_iterate_doubling() {
    // iterate(_ * 2, 1) |> take(5) → [1, 2, 4, 8, 16]
    let generator = make_test_closure(double_closure, 1);
    let lazy = rt_iterate(generator, Value::from_integer(1));
    let result = rt_take(Value::from_integer(5), lazy);
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 5);
    assert_eq!(out[0].as_integer(), Some(1));
    assert_eq!(out[1].as_integer(), Some(2));
    assert_eq!(out[2].as_integer(), Some(4));
    assert_eq!(out[3].as_integer(), Some(8));
    assert_eq!(out[4].as_integer(), Some(16));
}

// combinations() tests
#[test]
fn builtin_combinations_generates_lazy_sequence() {
    // combinations(2, [1, 2, 3]) returns a LazySequence
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_combinations(Value::from_integer(2), list);
    assert!(result.is_lazy_sequence());
}

#[test]
fn builtin_combinations_produces_correct_combinations() {
    // combinations(2, [1, 2, 3]) → [[1, 2], [1, 3], [2, 3]]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let lazy = rt_combinations(Value::from_integer(2), list);
    let result = rt_take(Value::from_integer(10), lazy);  // Take more than exists
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 3);

    // First combination: [1, 2]
    let c1 = out[0].as_list().expect("should be a list");
    assert_eq!(c1.len(), 2);
    assert_eq!(c1[0].as_integer(), Some(1));
    assert_eq!(c1[1].as_integer(), Some(2));

    // Second combination: [1, 3]
    let c2 = out[1].as_list().expect("should be a list");
    assert_eq!(c2.len(), 2);
    assert_eq!(c2[0].as_integer(), Some(1));
    assert_eq!(c2[1].as_integer(), Some(3));

    // Third combination: [2, 3]
    let c3 = out[2].as_list().expect("should be a list");
    assert_eq!(c3.len(), 2);
    assert_eq!(c3[0].as_integer(), Some(2));
    assert_eq!(c3[1].as_integer(), Some(3));
}

// range() function tests
#[test]
fn builtin_range_fn_generates_lazy_sequence() {
    // range(0, 10, 1) returns a LazySequence
    let result = rt_range_fn(
        Value::from_integer(0),
        Value::from_integer(10),
        Value::from_integer(1),
    );
    assert!(result.is_lazy_sequence());
}

#[test]
fn builtin_range_fn_with_step() {
    // range(0, 10, 2) |> take(5) → [0, 2, 4, 6, 8]
    let lazy = rt_range_fn(
        Value::from_integer(0),
        Value::from_integer(10),
        Value::from_integer(2),
    );
    let result = rt_take(Value::from_integer(5), lazy);
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 5);
    assert_eq!(out[0].as_integer(), Some(0));
    assert_eq!(out[1].as_integer(), Some(2));
    assert_eq!(out[2].as_integer(), Some(4));
    assert_eq!(out[3].as_integer(), Some(6));
    assert_eq!(out[4].as_integer(), Some(8));
}

// Unbounded range tests (conceptually similar to 0..)
#[test]
fn builtin_unbounded_range_take() {
    // Simulating 0.. with range(0, nil, 1) isn't directly supported,
    // but we can use iterate(_ + 1, 0) |> take(5)
    // which should work the same way
    let generator = make_test_closure(add_one_closure, 1);
    let lazy = rt_iterate(generator, Value::from_integer(0));
    let result = rt_take(Value::from_integer(5), lazy);
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 5);
    assert_eq!(out[0].as_integer(), Some(0));
    assert_eq!(out[1].as_integer(), Some(1));
    assert_eq!(out[2].as_integer(), Some(2));
    assert_eq!(out[3].as_integer(), Some(3));
    assert_eq!(out[4].as_integer(), Some(4));
}

#[test]
fn builtin_unbounded_range_first() {
    // first(iterate(_ + 1, 1)) → 1
    let generator = make_test_closure(add_one_closure, 1);
    let lazy = rt_iterate(generator, Value::from_integer(1));
    let result = rt_first(lazy);
    assert_eq!(result.as_integer(), Some(1));
}

// Lazy map/filter composition tests
#[test]
fn lazy_map_on_repeat() {
    // map(_ + 1, repeat(1)) |> take(3) → [2, 2, 2]
    // First, create repeat(1)
    let repeat_lazy = rt_repeat(Value::from_integer(1));
    // Apply map with add_one_closure
    let mapper = make_test_closure(add_one_closure, 1);
    let mapped = rt_map(mapper, repeat_lazy);
    // Take 3 elements
    let result = rt_take(Value::from_integer(3), mapped);
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 3);
    assert_eq!(out[0].as_integer(), Some(2));
    assert_eq!(out[1].as_integer(), Some(2));
    assert_eq!(out[2].as_integer(), Some(2));
}

/// Test closure: checks if a value is even
extern "C" fn is_even_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::from_bool(false);
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_bool(i % 2 == 0)
    } else {
        Value::from_bool(false)
    }
}

#[test]
fn lazy_filter_on_cycle() {
    // filter(_ != 2, cycle([1, 2, 3])) |> take(3) → [1, 3, 1]
    // Create cycle([1, 2, 3])
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let cycle_lazy = rt_cycle(list);

    // Create a filter that removes 2s
    extern "C" fn not_two_closure(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
        if argc != 1 || argv.is_null() {
            return Value::from_bool(false);
        }
        let arg = unsafe { *argv };
        if let Some(i) = arg.as_integer() {
            Value::from_bool(i != 2)
        } else {
            Value::from_bool(false)
        }
    }

    let predicate = make_test_closure(not_two_closure, 1);
    let filtered = rt_filter(predicate, cycle_lazy);

    // Take 3 elements
    let result = rt_take(Value::from_integer(3), filtered);
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 3);
    assert_eq!(out[0].as_integer(), Some(1));
    assert_eq!(out[1].as_integer(), Some(3));
    assert_eq!(out[2].as_integer(), Some(1));
}

// ===== Phase 14: String Functions (§11.14) =====

use crate::builtins::{rt_lines, rt_split, rt_md5, rt_upper, rt_lower, rt_replace, rt_join};

// lines() function tests per LANG.txt §11.14
#[test]
fn builtin_lines_basic() {
    // lines("a\nb\nc") → ["a", "b", "c"]
    let v = Value::from_string("a\nb\nc");
    let result = rt_lines(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_string(), Some("a"));
    assert_eq!(list[1].as_string(), Some("b"));
    assert_eq!(list[2].as_string(), Some("c"));
}

#[test]
fn builtin_lines_single_line() {
    // lines("single line") → ["single line"]
    let v = Value::from_string("single line");
    let result = rt_lines(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 1);
    assert_eq!(list[0].as_string(), Some("single line"));
}

#[test]
fn builtin_lines_empty_string() {
    // lines("") → [""]
    let v = Value::from_string("");
    let result = rt_lines(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 1);
    assert_eq!(list[0].as_string(), Some(""));
}

#[test]
fn builtin_lines_non_string() {
    // lines on non-string returns empty list
    let v = Value::from_integer(42);
    let result = rt_lines(v);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 0);
}

// split() function tests per LANG.txt §11.14
#[test]
fn builtin_split_comma() {
    // split(",", "a,b,c") → ["a", "b", "c"]
    let sep = Value::from_string(",");
    let s = Value::from_string("a,b,c");
    let result = rt_split(sep, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_string(), Some("a"));
    assert_eq!(list[1].as_string(), Some("b"));
    assert_eq!(list[2].as_string(), Some("c"));
}

#[test]
fn builtin_split_space() {
    // split(" ", "hello world") → ["hello", "world"]
    let sep = Value::from_string(" ");
    let s = Value::from_string("hello world");
    let result = rt_split(sep, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 2);
    assert_eq!(list[0].as_string(), Some("hello"));
    assert_eq!(list[1].as_string(), Some("world"));
}

#[test]
fn builtin_split_empty_separator() {
    // split("", "abc") → ["a", "b", "c"] (split into characters)
    let sep = Value::from_string("");
    let s = Value::from_string("abc");
    let result = rt_split(sep, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_string(), Some("a"));
    assert_eq!(list[1].as_string(), Some("b"));
    assert_eq!(list[2].as_string(), Some("c"));
}

// md5() function tests per LANG.txt §11.14
#[test]
fn builtin_md5_hello() {
    // md5("hello") → "5d41402abc4b2a76b9719d911017c592"
    let v = Value::from_string("hello");
    let result = rt_md5(v);
    assert_eq!(result.as_string(), Some("5d41402abc4b2a76b9719d911017c592"));
}

#[test]
fn builtin_md5_empty() {
    // md5("") → "d41d8cd98f00b204e9800998ecf8427e"
    let v = Value::from_string("");
    let result = rt_md5(v);
    assert_eq!(result.as_string(), Some("d41d8cd98f00b204e9800998ecf8427e"));
}

#[test]
fn builtin_md5_santa() {
    // md5("Santa") → "2f621a9cbf3a35ebd4a0b3b470124ba9"
    // Note: LANG.txt has incorrect hash; this is the actual MD5 of "Santa"
    let v = Value::from_string("Santa");
    let result = rt_md5(v);
    assert_eq!(result.as_string(), Some("2f621a9cbf3a35ebd4a0b3b470124ba9"));
}

// upper() function tests per LANG.txt §11.14
#[test]
fn builtin_upper() {
    // upper("hello") → "HELLO"
    let v = Value::from_string("hello");
    let result = rt_upper(v);
    assert_eq!(result.as_string(), Some("HELLO"));
}

#[test]
fn builtin_upper_mixed() {
    // upper("Hello World") → "HELLO WORLD"
    let v = Value::from_string("Hello World");
    let result = rt_upper(v);
    assert_eq!(result.as_string(), Some("HELLO WORLD"));
}

// lower() function tests per LANG.txt §11.14
#[test]
fn builtin_lower() {
    // lower("HELLO") → "hello"
    let v = Value::from_string("HELLO");
    let result = rt_lower(v);
    assert_eq!(result.as_string(), Some("hello"));
}

#[test]
fn builtin_lower_mixed() {
    // lower("Hello World") → "hello world"
    let v = Value::from_string("Hello World");
    let result = rt_lower(v);
    assert_eq!(result.as_string(), Some("hello world"));
}

// replace() function tests per LANG.txt §11.14
#[test]
fn builtin_replace_basic() {
    // replace("a", "x", "banana") → "bxnxnx"
    let from = Value::from_string("a");
    let to = Value::from_string("x");
    let s = Value::from_string("banana");
    let result = rt_replace(from, to, s);
    assert_eq!(result.as_string(), Some("bxnxnx"));
}

#[test]
fn builtin_replace_word() {
    // replace("world", "Santa", "hello world") → "hello Santa"
    let from = Value::from_string("world");
    let to = Value::from_string("Santa");
    let s = Value::from_string("hello world");
    let result = rt_replace(from, to, s);
    assert_eq!(result.as_string(), Some("hello Santa"));
}

// join() function tests per LANG.txt §11.14
#[test]
fn builtin_join_list() {
    // join(", ", [1, 2, 3]) → "1, 2, 3"
    let sep = Value::from_string(", ");
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let result = rt_join(sep, list);
    assert_eq!(result.as_string(), Some("1, 2, 3"));
}

#[test]
fn builtin_join_strings() {
    // join("-", ["a", "b", "c"]) → "a-b-c"
    let sep = Value::from_string("-");
    let list = Value::from_list(vec![
        Value::from_string("a".to_string()),
        Value::from_string("b".to_string()),
        Value::from_string("c".to_string()),
    ].into_iter().collect());
    let result = rt_join(sep, list);
    assert_eq!(result.as_string(), Some("a-b-c"));
}

// regex_match() function tests per LANG.txt §11.14
use crate::builtins::{rt_regex_match, rt_regex_match_all};

#[test]
fn builtin_regex_match_single_capture() {
    // regex_match("(\\d+)", "abc123") → ["123"]
    let pat = Value::from_string(r"(\d+)");
    let s = Value::from_string("abc123");
    let result = rt_regex_match(pat, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 1);
    assert_eq!(list[0].as_string(), Some("123"));
}

#[test]
fn builtin_regex_match_multiple_captures() {
    // regex_match("(\\w+):(\\d+)", "port:8080") → ["port", "8080"]
    let pat = Value::from_string(r"(\w+):(\d+)");
    let s = Value::from_string("port:8080");
    let result = rt_regex_match(pat, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 2);
    assert_eq!(list[0].as_string(), Some("port"));
    assert_eq!(list[1].as_string(), Some("8080"));
}

#[test]
fn builtin_regex_match_no_capture_groups() {
    // regex_match("\\d+", "abc123") → [] (no capture groups)
    let pat = Value::from_string(r"\d+");
    let s = Value::from_string("abc123");
    let result = rt_regex_match(pat, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 0);
}

#[test]
fn builtin_regex_match_no_match() {
    // regex_match("(\\d+)", "no numbers") → [] (no match)
    let pat = Value::from_string(r"(\d+)");
    let s = Value::from_string("no numbers");
    let result = rt_regex_match(pat, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 0);
}

#[test]
fn builtin_regex_match_all_basic() {
    // regex_match_all("\\d+", "a1b2c3") → ["1", "2", "3"]
    let pat = Value::from_string(r"\d+");
    let s = Value::from_string("a1b2c3");
    let result = rt_regex_match_all(pat, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_string(), Some("1"));
    assert_eq!(list[1].as_string(), Some("2"));
    assert_eq!(list[2].as_string(), Some("3"));
}

#[test]
fn builtin_regex_match_all_words() {
    // regex_match_all("\\w+", "hello world") → ["hello", "world"]
    let pat = Value::from_string(r"\w+");
    let s = Value::from_string("hello world");
    let result = rt_regex_match_all(pat, s);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 2);
    assert_eq!(list[0].as_string(), Some("hello"));
    assert_eq!(list[1].as_string(), Some("world"));
}

#[test]
#[should_panic(expected = "RuntimeError")]
fn builtin_regex_match_invalid_pattern_panics() {
    // regex_match("(unclosed", "x") → RuntimeErr per LANG.txt
    let pat = Value::from_string("(unclosed");
    let s = Value::from_string("test");
    rt_regex_match(pat, s);
}

#[test]
#[should_panic(expected = "RuntimeError")]
fn builtin_regex_match_all_invalid_pattern_panics() {
    // regex_match_all("(unclosed", "x") → RuntimeErr per LANG.txt
    let pat = Value::from_string("(unclosed");
    let s = Value::from_string("test");
    rt_regex_match_all(pat, s);
}

// ===== Phase 14: Math Functions (§11.15) =====

use crate::builtins::{rt_abs, rt_signum, rt_vec_add};

// abs() function tests per LANG.txt §11.15
#[test]
fn builtin_abs_positive_int() {
    // abs(5) → 5
    let v = Value::from_integer(5);
    let result = rt_abs(v);
    assert_eq!(result.as_integer(), Some(5));
}

#[test]
fn builtin_abs_negative_int() {
    // abs(-5) → 5
    let v = Value::from_integer(-5);
    let result = rt_abs(v);
    assert_eq!(result.as_integer(), Some(5));
}

#[test]
fn builtin_abs_zero() {
    // abs(0) → 0
    let v = Value::from_integer(0);
    let result = rt_abs(v);
    assert_eq!(result.as_integer(), Some(0));
}

#[test]
fn builtin_abs_negative_decimal() {
    // abs(-3.7) → 3.7
    let v = Value::from_decimal(-3.7);
    let result = rt_abs(v);
    assert_eq!(result.as_decimal(), Some(3.7));
}

#[test]
fn builtin_abs_positive_decimal() {
    // abs(3.7) → 3.7
    let v = Value::from_decimal(3.7);
    let result = rt_abs(v);
    assert_eq!(result.as_decimal(), Some(3.7));
}

// signum() function tests per LANG.txt §11.15
#[test]
fn builtin_signum_positive() {
    // signum(5) → 1
    let v = Value::from_integer(5);
    let result = rt_signum(v);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_signum_zero() {
    // signum(0) → 0
    let v = Value::from_integer(0);
    let result = rt_signum(v);
    assert_eq!(result.as_integer(), Some(0));
}

#[test]
fn builtin_signum_negative() {
    // signum(-3) → -1
    let v = Value::from_integer(-3);
    let result = rt_signum(v);
    assert_eq!(result.as_integer(), Some(-1));
}

#[test]
fn builtin_signum_positive_decimal() {
    // signum(5.5) → 1
    let v = Value::from_decimal(5.5);
    let result = rt_signum(v);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_signum_negative_decimal() {
    // signum(-5.5) → -1
    let v = Value::from_decimal(-5.5);
    let result = rt_signum(v);
    assert_eq!(result.as_integer(), Some(-1));
}

// vec_add() function tests per LANG.txt §11.15
#[test]
fn builtin_vec_add_basic() {
    // vec_add([1, 2], [3, 4]) → [4, 6]
    let a = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let b = Value::from_list(vec![
        Value::from_integer(3),
        Value::from_integer(4),
    ].into_iter().collect());
    let result = rt_vec_add(a, b);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 2);
    assert_eq!(list[0].as_integer(), Some(4));
    assert_eq!(list[1].as_integer(), Some(6));
}

#[test]
fn builtin_vec_add_three_elements() {
    // vec_add([1, 2, 3], [4, 5, 6]) → [5, 7, 9]
    let a = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let b = Value::from_list(vec![
        Value::from_integer(4),
        Value::from_integer(5),
        Value::from_integer(6),
    ].into_iter().collect());
    let result = rt_vec_add(a, b);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_integer(), Some(5));
    assert_eq!(list[1].as_integer(), Some(7));
    assert_eq!(list[2].as_integer(), Some(9));
}

#[test]
fn builtin_vec_add_shorter_list() {
    // vec_add([1, 2, 3], [10, 20]) → [11, 22] (shorter list determines length)
    let a = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let b = Value::from_list(vec![
        Value::from_integer(10),
        Value::from_integer(20),
    ].into_iter().collect());
    let result = rt_vec_add(a, b);
    let list = result.as_list().expect("should be a list");
    assert_eq!(list.len(), 2);
    assert_eq!(list[0].as_integer(), Some(11));
    assert_eq!(list[1].as_integer(), Some(22));
}

// ===== Phase 14: Bitwise Functions (§4.5) =====

use crate::builtins::{rt_bit_and, rt_bit_or, rt_bit_xor, rt_bit_not, rt_bit_shift_left, rt_bit_shift_right};

// bit_and() tests per LANG.txt §4.5
#[test]
fn builtin_bit_and() {
    // bit_and(12, 10) → 8  (1100 & 1010 = 1000)
    let a = Value::from_integer(12);
    let b = Value::from_integer(10);
    let result = rt_bit_and(a, b);
    assert_eq!(result.as_integer(), Some(8));
}

// bit_or() tests per LANG.txt §4.5
#[test]
fn builtin_bit_or() {
    // bit_or(12, 10) → 14 (1100 | 1010 = 1110)
    let a = Value::from_integer(12);
    let b = Value::from_integer(10);
    let result = rt_bit_or(a, b);
    assert_eq!(result.as_integer(), Some(14));
}

// bit_xor() tests per LANG.txt §4.5
#[test]
fn builtin_bit_xor() {
    // bit_xor(12, 10) → 6  (1100 ^ 1010 = 0110)
    let a = Value::from_integer(12);
    let b = Value::from_integer(10);
    let result = rt_bit_xor(a, b);
    assert_eq!(result.as_integer(), Some(6));
}

// bit_not() tests per LANG.txt §4.5
#[test]
fn builtin_bit_not() {
    // bit_not(12) → -13 (bitwise complement)
    let v = Value::from_integer(12);
    let result = rt_bit_not(v);
    assert_eq!(result.as_integer(), Some(-13));
}

#[test]
fn builtin_bit_not_zero() {
    // bit_not(0) → -1
    let v = Value::from_integer(0);
    let result = rt_bit_not(v);
    assert_eq!(result.as_integer(), Some(-1));
}

// bit_shift_left() tests per LANG.txt §4.5
#[test]
fn builtin_bit_shift_left() {
    // bit_shift_left(1, 3) → 8  (1 << 3 = 1000)
    let v = Value::from_integer(1);
    let s = Value::from_integer(3);
    let result = rt_bit_shift_left(v, s);
    assert_eq!(result.as_integer(), Some(8));
}

#[test]
fn builtin_bit_shift_left_multiple() {
    // bit_shift_left(5, 2) → 20 (101 << 2 = 10100)
    let v = Value::from_integer(5);
    let s = Value::from_integer(2);
    let result = rt_bit_shift_left(v, s);
    assert_eq!(result.as_integer(), Some(20));
}

// bit_shift_right() tests per LANG.txt §4.5
#[test]
fn builtin_bit_shift_right() {
    // bit_shift_right(8, 2) → 2  (1000 >> 2 = 10)
    let v = Value::from_integer(8);
    let s = Value::from_integer(2);
    let result = rt_bit_shift_right(v, s);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_bit_shift_right_multiple() {
    // bit_shift_right(20, 2) → 5 (10100 >> 2 = 101)
    let v = Value::from_integer(20);
    let s = Value::from_integer(2);
    let result = rt_bit_shift_right(v, s);
    assert_eq!(result.as_integer(), Some(5));
}

// ===== Phase 14: Utility Functions (§11.16) =====

use crate::builtins::{rt_id, rt_type, rt_or, rt_and};

// id() function tests per LANG.txt §11.16
#[test]
fn builtin_id_integer() {
    // id(42) → 42
    let v = Value::from_integer(42);
    let result = rt_id(v);
    assert_eq!(result.as_integer(), Some(42));
}

#[test]
fn builtin_id_string() {
    // id("hello") → "hello"
    let v = Value::from_string("hello");
    let result = rt_id(v);
    assert_eq!(result.as_string(), Some("hello"));
}

#[test]
fn builtin_id_bool() {
    // id(true) → true
    let v = Value::from_bool(true);
    let result = rt_id(v);
    assert_eq!(result.as_bool(), Some(true));
}

// type() function tests per LANG.txt §11.16
#[test]
fn builtin_type_integer() {
    // type(42) → "Integer"
    let v = Value::from_integer(42);
    let result = rt_type(v);
    assert_eq!(result.as_string(), Some("Integer"));
}

#[test]
fn builtin_type_decimal() {
    // type(3.14) → "Decimal"
    let v = Value::from_decimal(3.14);
    let result = rt_type(v);
    assert_eq!(result.as_string(), Some("Decimal"));
}

#[test]
fn builtin_type_string() {
    // type("hello") → "String"
    let v = Value::from_string("hello");
    let result = rt_type(v);
    assert_eq!(result.as_string(), Some("String"));
}

#[test]
fn builtin_type_boolean() {
    // type(true) → "Boolean"
    let v = Value::from_bool(true);
    let result = rt_type(v);
    assert_eq!(result.as_string(), Some("Boolean"));
}

#[test]
fn builtin_type_nil() {
    // type(nil) → "Nil"
    let v = Value::nil();
    let result = rt_type(v);
    assert_eq!(result.as_string(), Some("Nil"));
}

#[test]
fn builtin_type_list() {
    // type([1, 2, 3]) → "List"
    let v = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_type(v);
    assert_eq!(result.as_string(), Some("List"));
}

#[test]
fn builtin_type_set() {
    // type({1, 2, 3}) → "Set"
    let v = Value::from_set(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let result = rt_type(v);
    assert_eq!(result.as_string(), Some("Set"));
}

#[test]
fn builtin_type_dict() {
    // type(#{a: 1}) → "Dictionary"
    let mut entries = im::HashMap::new();
    entries.insert(Value::from_integer(1), Value::from_integer(2));
    let v = Value::from_dict(entries);
    let result = rt_type(v);
    assert_eq!(result.as_string(), Some("Dictionary"));
}

// or() function tests per LANG.txt §11.16
#[test]
fn builtin_or_first_truthy() {
    // or(1, 2) → 1 (first truthy value)
    let a = Value::from_integer(1);
    let b = Value::from_integer(2);
    let result = rt_or(a, b);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_or_first_falsy() {
    // or(0, 2) → 2 (second value when first is falsy)
    let a = Value::from_integer(0);
    let b = Value::from_integer(2);
    let result = rt_or(a, b);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_or_both_falsy() {
    // or(0, false) → false (second value)
    let a = Value::from_integer(0);
    let b = Value::from_bool(false);
    let result = rt_or(a, b);
    assert_eq!(result.as_bool(), Some(false));
}

#[test]
fn builtin_or_nil() {
    // or(nil, "default") → "default"
    let a = Value::nil();
    let b = Value::from_string("default");
    let result = rt_or(a, b);
    assert_eq!(result.as_string(), Some("default"));
}

// and() function tests per LANG.txt §11.16
#[test]
fn builtin_and_first_falsy() {
    // and(0, 2) → 0 (first falsy value)
    let a = Value::from_integer(0);
    let b = Value::from_integer(2);
    let result = rt_and(a, b);
    assert_eq!(result.as_integer(), Some(0));
}

#[test]
fn builtin_and_both_truthy() {
    // and(1, 2) → 2 (second value when both truthy)
    let a = Value::from_integer(1);
    let b = Value::from_integer(2);
    let result = rt_and(a, b);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_and_nil() {
    // and(nil, "hello") → nil
    let a = Value::nil();
    let b = Value::from_string("hello");
    let result = rt_and(a, b);
    assert!(result.is_nil());
}

// ============================================================================
// External Functions (§13)
// ============================================================================

#[test]
fn format_value_integer() {
    let v = Value::from_integer(42);
    assert_eq!(format_value(&v), "42");
}

#[test]
fn format_value_decimal() {
    let v = Value::from_decimal(3.14);
    assert!(format_value(&v).starts_with("3.14"));
}

#[test]
fn format_value_string() {
    let v = Value::from_string("hello");
    assert_eq!(format_value(&v), "hello");
}

#[test]
fn format_value_bool_true() {
    let v = Value::from_bool(true);
    assert_eq!(format_value(&v), "true");
}

#[test]
fn format_value_bool_false() {
    let v = Value::from_bool(false);
    assert_eq!(format_value(&v), "false");
}

#[test]
fn format_value_nil() {
    let v = Value::nil();
    assert_eq!(format_value(&v), "nil");
}

#[test]
fn format_value_list() {
    let v = Value::from_list(im::vector![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ]);
    assert_eq!(format_value(&v), "[1, 2, 3]");
}

// ===== External Function Tests (LANG.txt §13) =====

use super::builtins::rt_read;

#[test]
fn read_local_file() {
    // Create a temporary file with known content
    let temp_dir = std::env::temp_dir();
    let test_file = temp_dir.join("santa_test_read.txt");
    std::fs::write(&test_file, "hello world").unwrap();

    // Call rt_read with the file path
    let path = Value::from_string(test_file.to_str().unwrap());
    let result = rt_read(path);

    // Should return the file contents as a string
    assert_eq!(result.as_string(), Some("hello world"));

    // Cleanup
    std::fs::remove_file(&test_file).ok();
}

#[test]
fn read_nonexistent_file_returns_nil() {
    // Attempting to read a non-existent file should return nil
    let path = Value::from_string("/nonexistent/file/path.txt");
    let result = rt_read(path);
    assert!(result.is_nil());
}

#[test]
fn read_aoc_cached_input() {
    // If the AOC input is already cached, read should return it
    use super::builtins::get_aoc_cache_path;

    let cache_path = get_aoc_cache_path(2022, 1);
    let cache_dir = cache_path.parent().unwrap();
    std::fs::create_dir_all(cache_dir).unwrap();
    std::fs::write(&cache_path, "cached input data").unwrap();

    let path = Value::from_string("aoc://2022/1");
    let result = rt_read(path);

    assert_eq!(result.as_string(), Some("cached input data"));

    // Cleanup
    std::fs::remove_file(&cache_path).ok();
}

#[test]
fn read_aoc_invalid_url_returns_nil() {
    // Invalid aoc:// URLs should return nil
    let path = Value::from_string("aoc://invalid");
    let result = rt_read(path);
    assert!(result.is_nil());

    let path = Value::from_string("aoc://2022");
    let result = rt_read(path);
    assert!(result.is_nil());

    let path = Value::from_string("aoc://abc/def");
    let result = rt_read(path);
    assert!(result.is_nil());
}

// ===== LazySequence fold/reduce/scan Tests (§11.5 + §11.12) =====

use crate::heap::LazySequenceObject;

#[test]
fn builtin_fold_lazy_range() {
    // fold(0, +, 1..5) → 1+2+3+4 = 10
    // Range 1..5 is exclusive, so [1, 2, 3, 4]
    let lazy = LazySequenceObject::range(1, Some(5), false, 1);
    let range_val = Value::from_lazy_sequence(lazy);
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(0);
    let result = rt_fold(initial, folder, range_val);
    assert_eq!(result.as_integer(), Some(10));
}

#[test]
fn builtin_fold_lazy_range_inclusive() {
    // fold(0, +, 1..=5) → 1+2+3+4+5 = 15
    let lazy = LazySequenceObject::range(1, Some(5), true, 1);
    let range_val = Value::from_lazy_sequence(lazy);
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(0);
    let result = rt_fold(initial, folder, range_val);
    assert_eq!(result.as_integer(), Some(15));
}

#[test]
fn builtin_fold_lazy_range_empty() {
    // fold(42, +, 5..5) → 42 (empty range)
    let lazy = LazySequenceObject::range(5, Some(5), false, 1);
    let range_val = Value::from_lazy_sequence(lazy);
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(42);
    let result = rt_fold(initial, folder, range_val);
    assert_eq!(result.as_integer(), Some(42));
}

#[test]
fn builtin_reduce_lazy_range() {
    // reduce(+, 1..5) → 1+2+3+4 = 10
    // First element (1) is the initial accumulator, then 2,3,4 are folded
    let lazy = LazySequenceObject::range(1, Some(5), false, 1);
    let range_val = Value::from_lazy_sequence(lazy);
    let reducer = make_test_closure(sum_closure, 2);
    let result = rt_reduce(reducer, range_val);
    assert_eq!(result.as_integer(), Some(10));
}

#[test]
fn builtin_reduce_lazy_range_inclusive() {
    // reduce(+, 1..=5) → 1+2+3+4+5 = 15
    let lazy = LazySequenceObject::range(1, Some(5), true, 1);
    let range_val = Value::from_lazy_sequence(lazy);
    let reducer = make_test_closure(sum_closure, 2);
    let result = rt_reduce(reducer, range_val);
    assert_eq!(result.as_integer(), Some(15));
}

#[test]
fn builtin_reduce_lazy_range_single_element() {
    // reduce(+, 5..=5) → 5 (single element range)
    let lazy = LazySequenceObject::range(5, Some(5), true, 1);
    let range_val = Value::from_lazy_sequence(lazy);
    let reducer = make_test_closure(sum_closure, 2);
    let result = rt_reduce(reducer, range_val);
    assert_eq!(result.as_integer(), Some(5));
}

#[test]
#[should_panic(expected = "reduce on empty collection")]
fn builtin_reduce_lazy_range_empty_panics() {
    // Per LANG.txt §11.5: reduce(+, 5..5) → RuntimeErr (empty range)
    let lazy = LazySequenceObject::range(5, Some(5), false, 1);
    let range_val = Value::from_lazy_sequence(lazy);
    let reducer = make_test_closure(sum_closure, 2);
    let _result = rt_reduce(reducer, range_val);  // Should panic
}

#[test]
fn builtin_scan_lazy_range() {
    // scan(0, +, 1..5) → [1, 3, 6, 10]
    // Intermediate sums: 0+1=1, 1+2=3, 3+3=6, 6+4=10
    let lazy = LazySequenceObject::range(1, Some(5), false, 1);
    let range_val = Value::from_lazy_sequence(lazy);
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(0);
    let result = rt_scan(initial, folder, range_val);

    let result_list = result.as_list().expect("should be a list");
    assert_eq!(result_list.len(), 4);
    assert_eq!(result_list[0].as_integer(), Some(1));
    assert_eq!(result_list[1].as_integer(), Some(3));
    assert_eq!(result_list[2].as_integer(), Some(6));
    assert_eq!(result_list[3].as_integer(), Some(10));
}

#[test]
fn builtin_scan_lazy_range_empty() {
    // scan(0, +, 5..5) → [] (empty range)
    let lazy = LazySequenceObject::range(5, Some(5), false, 1);
    let range_val = Value::from_lazy_sequence(lazy);
    let folder = make_test_closure(sum_closure, 2);
    let initial = Value::from_integer(0);
    let result = rt_scan(initial, folder, range_val);

    let result_list = result.as_list().expect("should be a list");
    assert!(result_list.is_empty());
}

// ============================================================================
// Memoize (§11.16)
// ============================================================================

use crate::builtins::{rt_memoize, rt_call_memoized};

#[test]
fn builtin_memoize_returns_closure() {
    // memoize(|x| x + 1) should return a closure
    let func = make_test_closure(add_one_closure, 1);
    let memoized = rt_memoize(func);
    assert!(memoized.is_closure() || memoized.is_memoized_closure(), "memoize should return a callable");
}

#[test]
fn builtin_memoize_basic_call() {
    // memoize(|x| x + 1)(5) → 6
    let func = make_test_closure(add_one_closure, 1);
    let memoized = rt_memoize(func);

    // Call the memoized function
    let args = [Value::from_integer(5)];
    let result = unsafe { rt_call_memoized(memoized, args.len() as u32, args.as_ptr()) };
    assert_eq!(result.as_integer(), Some(6));
}

#[test]
fn builtin_memoize_caches_results() {
    // Calling memoize(f)(5) twice should return the same result
    let func = make_test_closure(add_one_closure, 1);
    let memoized = rt_memoize(func);

    let args = [Value::from_integer(5)];
    let result1 = unsafe { rt_call_memoized(memoized, args.len() as u32, args.as_ptr()) };
    let result2 = unsafe { rt_call_memoized(memoized, args.len() as u32, args.as_ptr()) };

    assert_eq!(result1.as_integer(), Some(6));
    assert_eq!(result2.as_integer(), Some(6));
}

// ===== zip() Tests (§11.12) =====

use crate::builtins::rt_zip;

#[test]
fn builtin_zip_two_lists() {
    // zip([1, 2, 3], ["a", "b", "c"]) → [[1, "a"], [2, "b"], [3, "c"]]
    let list1 = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let list2 = Value::from_list(vec![
        Value::from_string("a"),
        Value::from_string("b"),
        Value::from_string("c"),
    ].into_iter().collect());

    let result = rt_zip(2, [list1, list2].as_ptr());
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 3);

    // First tuple: [1, "a"]
    let first = out[0].as_list().expect("should be a list");
    assert_eq!(first.len(), 2);
    assert_eq!(first[0].as_integer(), Some(1));
    assert_eq!(first[1].as_string(), Some("a"));

    // Second tuple: [2, "b"]
    let second = out[1].as_list().expect("should be a list");
    assert_eq!(second[0].as_integer(), Some(2));
    assert_eq!(second[1].as_string(), Some("b"));

    // Third tuple: [3, "c"]
    let third = out[2].as_list().expect("should be a list");
    assert_eq!(third[0].as_integer(), Some(3));
    assert_eq!(third[1].as_string(), Some("c"));
}

#[test]
fn builtin_zip_different_lengths_stops_at_shortest() {
    // zip([1, 2], ["a", "b", "c", "d"]) → [[1, "a"], [2, "b"]]
    let list1 = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let list2 = Value::from_list(vec![
        Value::from_string("a"),
        Value::from_string("b"),
        Value::from_string("c"),
        Value::from_string("d"),
    ].into_iter().collect());

    let result = rt_zip(2, [list1, list2].as_ptr());
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 2);  // Stops at shortest (2 elements)
}

#[test]
fn builtin_zip_three_collections() {
    // zip([1, 2], ["a", "b"], [10, 20]) → [[1, "a", 10], [2, "b", 20]]
    let list1 = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let list2 = Value::from_list(vec![
        Value::from_string("a"),
        Value::from_string("b"),
    ].into_iter().collect());
    let list3 = Value::from_list(vec![
        Value::from_integer(10),
        Value::from_integer(20),
    ].into_iter().collect());

    let result = rt_zip(3, [list1, list2, list3].as_ptr());
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 2);

    // First tuple: [1, "a", 10]
    let first = out[0].as_list().expect("should be a list");
    assert_eq!(first.len(), 3);
    assert_eq!(first[0].as_integer(), Some(1));
    assert_eq!(first[1].as_string(), Some("a"));
    assert_eq!(first[2].as_integer(), Some(10));
}

#[test]
fn builtin_zip_with_string() {
    // zip([1, 2, 3], "abc") → [[1, "a"], [2, "b"], [3, "c"]]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());
    let string = Value::from_string("abc");

    let result = rt_zip(2, [list, string].as_ptr());
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 3);

    let first = out[0].as_list().expect("should be a list");
    assert_eq!(first[0].as_integer(), Some(1));
    assert_eq!(first[1].as_string(), Some("a"));
}

#[test]
fn builtin_zip_with_range_and_finite() {
    // zip(0.., [1.5, 2.5, 3.5]) → [[0, 1.5], [1, 2.5], [2, 3.5]] (list, not lazy)
    let range = Value::from_lazy_sequence(LazySequenceObject::range(0, None, false, 1));
    let list = Value::from_list(vec![
        Value::from_decimal(1.5),
        Value::from_decimal(2.5),
        Value::from_decimal(3.5),
    ].into_iter().collect());

    let result = rt_zip(2, [range, list].as_ptr());
    // Since one collection is finite, result should be a List
    let out = result.as_list().expect("should be a list when any input is finite");
    assert_eq!(out.len(), 3);

    let first = out[0].as_list().expect("should be a list");
    assert_eq!(first[0].as_integer(), Some(0));
    assert_eq!(first[1].as_decimal(), Some(1.5));

    let third = out[2].as_list().expect("should be a list");
    assert_eq!(third[0].as_integer(), Some(2));
    assert_eq!(third[1].as_decimal(), Some(3.5));
}

#[test]
fn builtin_zip_two_infinite_returns_lazy() {
    // zip(0.., 1..) → LazySequence
    let range1 = Value::from_lazy_sequence(LazySequenceObject::range(0, None, false, 1));
    let range2 = Value::from_lazy_sequence(LazySequenceObject::range(1, None, false, 1));

    let result = rt_zip(2, [range1, range2].as_ptr());
    // When all collections are infinite, result should be LazySequence
    assert!(result.is_lazy_sequence(), "should return LazySequence when all inputs are infinite");
}

#[test]
fn builtin_zip_infinite_take() {
    // zip(0.., 1..) |> take(3) → [[0, 1], [1, 2], [2, 3]]
    let range1 = Value::from_lazy_sequence(LazySequenceObject::range(0, None, false, 1));
    let range2 = Value::from_lazy_sequence(LazySequenceObject::range(1, None, false, 1));

    let lazy = rt_zip(2, [range1, range2].as_ptr());
    let result = rt_take(Value::from_integer(3), lazy);
    let out = result.as_list().expect("should be a list after take");
    assert_eq!(out.len(), 3);

    let first = out[0].as_list().expect("should be a list");
    assert_eq!(first[0].as_integer(), Some(0));
    assert_eq!(first[1].as_integer(), Some(1));

    let second = out[1].as_list().expect("should be a list");
    assert_eq!(second[0].as_integer(), Some(1));
    assert_eq!(second[1].as_integer(), Some(2));

    let third = out[2].as_list().expect("should be a list");
    assert_eq!(third[0].as_integer(), Some(2));
    assert_eq!(third[1].as_integer(), Some(3));
}

#[test]
fn builtin_zip_empty_list() {
    // zip([], [1, 2, 3]) → []
    let empty = Value::from_list(im::Vector::new());
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3),
    ].into_iter().collect());

    let result = rt_zip(2, [empty, list].as_ptr());
    let out = result.as_list().expect("should be a list");
    assert_eq!(out.len(), 0);
}

// ============================================================================
// update() tests per LANG.txt §11.3
// ============================================================================

use super::builtins::rt_update;

#[test]
fn builtin_update_list_existing() {
    // update(0, _ + 1, [1, 2]) → [2, 2]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let updater = make_test_closure(add_one_closure, 1);
    let result = rt_update(Value::from_integer(0), updater, list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 2);
    assert_eq!(new_list[0].as_integer(), Some(2));
    assert_eq!(new_list[1].as_integer(), Some(2));
}

/// Test closure: ignores argument, returns 1
extern "C" fn constant_one_closure(_env: *const ClosureObject, _argc: u32, _argv: *const Value) -> Value {
    Value::from_integer(1)
}

#[test]
fn builtin_update_list_fills_with_nil() {
    // update(1, || 1, []) → [nil, 1]
    let list = Value::from_list(im::Vector::new());
    let updater = make_test_closure(constant_one_closure, 0);
    let result = rt_update(Value::from_integer(1), updater, list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 2);
    assert!(new_list[0].is_nil());
    assert_eq!(new_list[1].as_integer(), Some(1));
}

#[test]
fn builtin_update_dict_new_key() {
    // update(0, || 1, #{}) → #{0: 1}
    let dict = Value::from_dict(im::HashMap::new());
    let updater = make_test_closure(constant_one_closure, 0);
    let result = rt_update(Value::from_integer(0), updater, dict);
    let new_dict = result.as_dict().expect("should be a dict");
    assert_eq!(new_dict.len(), 1);
    assert_eq!(new_dict.get(&Value::from_integer(0)).map(|v| v.as_integer()), Some(Some(1)));
}

#[test]
fn builtin_update_dict_existing_key() {
    // update(1, _ + 1, #{1: 2, 3: 4}) → #{1: 3, 3: 4}
    let mut dict_data = im::HashMap::new();
    dict_data.insert(Value::from_integer(1), Value::from_integer(2));
    dict_data.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(dict_data);
    let updater = make_test_closure(add_one_closure, 1);
    let result = rt_update(Value::from_integer(1), updater, dict);
    let new_dict = result.as_dict().expect("should be a dict");
    assert_eq!(new_dict.len(), 2);
    assert_eq!(new_dict.get(&Value::from_integer(1)).map(|v| v.as_integer()), Some(Some(3)));
    assert_eq!(new_dict.get(&Value::from_integer(3)).map(|v| v.as_integer()), Some(Some(4)));
}

// ============================================================================
// update_d() tests per LANG.txt §11.3
// ============================================================================

use super::builtins::rt_update_d;

#[test]
fn builtin_update_d_list_existing() {
    // update_d(0, 0, _ + 1, [1, 2]) → [2, 2]
    let list = Value::from_list(vec![
        Value::from_integer(1),
        Value::from_integer(2),
    ].into_iter().collect());
    let updater = make_test_closure(add_one_closure, 1);
    let result = rt_update_d(Value::from_integer(0), Value::from_integer(0), updater, list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 2);
    assert_eq!(new_list[0].as_integer(), Some(2));
    assert_eq!(new_list[1].as_integer(), Some(2));
}

#[test]
fn builtin_update_d_list_fills_with_nil_uses_default() {
    // update_d(1, 0, _ + 1, []) → [nil, 1]
    let list = Value::from_list(im::Vector::new());
    let updater = make_test_closure(add_one_closure, 1);
    let result = rt_update_d(Value::from_integer(1), Value::from_integer(0), updater, list);
    let new_list = result.as_list().expect("should be a list");
    assert_eq!(new_list.len(), 2);
    assert!(new_list[0].is_nil());
    assert_eq!(new_list[1].as_integer(), Some(1)); // 0 + 1 = 1
}

#[test]
fn builtin_update_d_dict_new_key_uses_default() {
    // update_d(0, 0, _ + 1, #{}) → #{0: 1}
    let dict = Value::from_dict(im::HashMap::new());
    let updater = make_test_closure(add_one_closure, 1);
    let result = rt_update_d(Value::from_integer(0), Value::from_integer(0), updater, dict);
    let new_dict = result.as_dict().expect("should be a dict");
    assert_eq!(new_dict.len(), 1);
    assert_eq!(new_dict.get(&Value::from_integer(0)).map(|v| v.as_integer()), Some(Some(1))); // 0 + 1 = 1
}

#[test]
fn builtin_update_d_dict_existing_key() {
    // update_d(1, 0, _ + 1, #{1: 2, 3: 4}) → #{1: 3, 3: 4}
    let mut dict_data = im::HashMap::new();
    dict_data.insert(Value::from_integer(1), Value::from_integer(2));
    dict_data.insert(Value::from_integer(3), Value::from_integer(4));
    let dict = Value::from_dict(dict_data);
    let updater = make_test_closure(add_one_closure, 1);
    let result = rt_update_d(Value::from_integer(1), Value::from_integer(0), updater, dict);
    let new_dict = result.as_dict().expect("should be a dict");
    assert_eq!(new_dict.len(), 2);
    assert_eq!(new_dict.get(&Value::from_integer(1)).map(|v| v.as_integer()), Some(Some(3)));
    assert_eq!(new_dict.get(&Value::from_integer(3)).map(|v| v.as_integer()), Some(Some(4)));
}

// ===== get() Range/LazySequence Tests (§11.2) =====

#[test]
fn builtin_get_range_exclusive() {
    // get(1, 1..5) → 2
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(5), false, 1));
    let result = rt_get(Value::from_integer(1), range);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_get_range_inclusive() {
    // get(1, 1..=5) → 2
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(5), true, 1));
    let result = rt_get(Value::from_integer(1), range);
    assert_eq!(result.as_integer(), Some(2));
}

#[test]
fn builtin_get_range_unbounded() {
    // get(1, 0..) → 1
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(0, None, false, 1));
    let result = rt_get(Value::from_integer(1), range);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_get_range_out_of_bounds() {
    // get(10, 1..5) → nil (out of bounds)
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(5), false, 1));
    let result = rt_get(Value::from_integer(10), range);
    assert!(result.is_nil());
}

#[test]
fn builtin_get_range_negative_index() {
    // get(-1, 1..5) → nil (negative index not supported)
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(5), false, 1));
    let result = rt_get(Value::from_integer(-1), range);
    assert!(result.is_nil());
}

#[test]
fn builtin_get_range_first_element() {
    // get(0, 1..5) → 1
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(5), false, 1));
    let result = rt_get(Value::from_integer(0), range);
    assert_eq!(result.as_integer(), Some(1));
}

#[test]
fn builtin_get_range_last_element_exclusive() {
    // get(3, 1..5) → 4 (last element of [1,2,3,4])
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(1, Some(5), false, 1));
    let result = rt_get(Value::from_integer(3), range);
    assert_eq!(result.as_integer(), Some(4));
}

#[test]
fn builtin_get_range_descending() {
    // get(1, 5..1) → 4 (descending range: [5,4,3,2])
    use crate::heap::LazySequenceObject;
    let range = Value::from_lazy_sequence(LazySequenceObject::range(5, Some(1), false, -1));
    let result = rt_get(Value::from_integer(1), range);
    assert_eq!(result.as_integer(), Some(4));
}

// ===== Non-Callable Error Tests =====

use crate::operations::rt_call;

#[test]
#[should_panic(expected = "Integer is not callable")]
fn runtime_call_integer_not_callable() {
    // Calling an integer should produce RuntimeErr
    let callee = Value::from_integer(42);
    let args: Vec<Value> = vec![];
    let _result = rt_call(callee, 0, args.as_ptr());
}

#[test]
#[should_panic(expected = "String is not callable")]
fn runtime_call_string_not_callable() {
    // Calling a string should produce RuntimeErr
    let callee = Value::from_string("hello".to_string());
    let args: Vec<Value> = vec![];
    let _result = rt_call(callee, 0, args.as_ptr());
}

#[test]
#[should_panic(expected = "List is not callable")]
fn runtime_call_list_not_callable() {
    // Calling a list should produce RuntimeErr
    let callee = Value::from_list(im::vector![Value::from_integer(1), Value::from_integer(2)]);
    let args: Vec<Value> = vec![];
    let _result = rt_call(callee, 0, args.as_ptr());
}

// ===== Collection String Representation Tests =====
// Note: format_value is already imported from builtins at line 2

#[test]
fn format_list() {
    // List should format as [elem1, elem2, ...]
    let list = Value::from_list(im::vector![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3)
    ]);
    assert_eq!(format_value(&list), "[1, 2, 3]");
}

#[test]
fn format_empty_list() {
    let list = Value::from_list(im::Vector::new());
    assert_eq!(format_value(&list), "[]");
}

#[test]
fn format_set() {
    // Set should format as {elem1, elem2, ...}
    // Note: order may vary since sets are unordered
    let set = Value::from_set(im::hashset![Value::from_integer(42)]);
    assert_eq!(format_value(&set), "{42}");
}

#[test]
fn format_empty_set() {
    let set = Value::from_set(im::HashSet::new());
    assert_eq!(format_value(&set), "{}");
}

#[test]
fn format_dict() {
    // Dict should format as #{key: value, ...}
    // Note: existing format_value doesn't add quotes around string keys
    let mut dict = im::HashMap::new();
    dict.insert(Value::from_string("a".to_string()), Value::from_integer(1));
    let dict_val = Value::from_dict(dict);
    assert_eq!(format_value(&dict_val), "#{a: 1}");
}

#[test]
fn format_empty_dict() {
    let dict = Value::from_dict(im::HashMap::new());
    assert_eq!(format_value(&dict), "#{}");
}

#[test]
fn format_nested_list() {
    // Nested collections should format recursively
    let inner = Value::from_list(im::vector![Value::from_integer(1), Value::from_integer(2)]);
    let outer = Value::from_list(im::vector![inner, Value::from_integer(3)]);
    assert_eq!(format_value(&outer), "[[1, 2], 3]");
}

#[test]
fn format_function() {
    // Functions should format as <function>
    use crate::heap::ClosureObject;
    // Define an extern "C" function (cannot be a closure for extern "C" ABI)
    extern "C" fn dummy_fn(_: *const ClosureObject, _: u32, _: *const Value) -> Value {
        Value::nil()
    }
    let closure = ClosureObject::new(dummy_fn as *const (), 0, vec![]);
    let closure_val = Value::from_closure(closure);
    assert_eq!(format_value(&closure_val), "<function>");
}

// ===== Deep Equality Tests =====

#[test]
fn deep_equality_lists_equal() {
    // [1, 2, 3] == [1, 2, 3] should be true
    let list1 = Value::from_list(im::vector![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3)
    ]);
    let list2 = Value::from_list(im::vector![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3)
    ]);
    assert_eq!(list1, list2);
}

#[test]
fn deep_equality_lists_not_equal() {
    // [1, 2, 3] == [1, 2, 4] should be false
    let list1 = Value::from_list(im::vector![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3)
    ]);
    let list2 = Value::from_list(im::vector![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(4)
    ]);
    assert_ne!(list1, list2);
}

#[test]
fn deep_equality_nested_lists() {
    // [[1, 2], [3, 4]] == [[1, 2], [3, 4]] should be true
    let inner1 = Value::from_list(im::vector![Value::from_integer(1), Value::from_integer(2)]);
    let inner2 = Value::from_list(im::vector![Value::from_integer(3), Value::from_integer(4)]);
    let outer1 = Value::from_list(im::vector![inner1.clone(), inner2.clone()]);

    let inner3 = Value::from_list(im::vector![Value::from_integer(1), Value::from_integer(2)]);
    let inner4 = Value::from_list(im::vector![Value::from_integer(3), Value::from_integer(4)]);
    let outer2 = Value::from_list(im::vector![inner3, inner4]);

    assert_eq!(outer1, outer2);
}

#[test]
fn deep_equality_sets_equal() {
    // {1, 2} == {1, 2} should be true
    let set1 = Value::from_set(im::hashset![Value::from_integer(1), Value::from_integer(2)]);
    let set2 = Value::from_set(im::hashset![Value::from_integer(2), Value::from_integer(1)]);
    assert_eq!(set1, set2);
}

#[test]
fn deep_equality_dicts_equal() {
    // #{a: 1} == #{a: 1} should be true
    let mut dict1 = im::HashMap::new();
    dict1.insert(Value::from_string("a".to_string()), Value::from_integer(1));
    let dict1_val = Value::from_dict(dict1);

    let mut dict2 = im::HashMap::new();
    dict2.insert(Value::from_string("a".to_string()), Value::from_integer(1));
    let dict2_val = Value::from_dict(dict2);

    assert_eq!(dict1_val, dict2_val);
}

// ===== Deep Hashing Tests =====

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn compute_hash(value: &Value) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn deep_hash_lists_equal_hash() {
    // Equal lists should have equal hashes
    let list1 = Value::from_list(im::vector![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3)
    ]);
    let list2 = Value::from_list(im::vector![
        Value::from_integer(1),
        Value::from_integer(2),
        Value::from_integer(3)
    ]);
    assert_eq!(compute_hash(&list1), compute_hash(&list2));
}

#[test]
fn deep_hash_lists_different_hash() {
    // Different lists should (usually) have different hashes
    let list1 = Value::from_list(im::vector![Value::from_integer(1), Value::from_integer(2)]);
    let list2 = Value::from_list(im::vector![Value::from_integer(1), Value::from_integer(3)]);
    assert_ne!(compute_hash(&list1), compute_hash(&list2));
}

#[test]
fn deep_hash_nested_lists() {
    // Equal nested lists should have equal hashes
    let inner1 = Value::from_list(im::vector![Value::from_integer(1), Value::from_integer(2)]);
    let outer1 = Value::from_list(im::vector![inner1.clone(), Value::from_integer(3)]);

    let inner2 = Value::from_list(im::vector![Value::from_integer(1), Value::from_integer(2)]);
    let outer2 = Value::from_list(im::vector![inner2, Value::from_integer(3)]);

    assert_eq!(compute_hash(&outer1), compute_hash(&outer2));
}

// ===== HTTP Fetching Tests =====
// Note: rt_read is already imported from builtins at line 4434

#[test]
fn read_https_url() {
    // Test fetching from a public HTTPS endpoint
    // example.com is a very stable test domain maintained by IANA
    let url = Value::from_string("https://example.com/".to_string());
    let result = rt_read(url);

    // Should return a non-nil string containing HTML
    assert!(!result.is_nil(), "HTTPS fetch should not return nil");
    let content = result.as_string().expect("Result should be a string");
    assert!(content.contains("Example Domain"), "Should contain example.com content");
}

#[test]
fn read_http_url() {
    // Test fetching from HTTP (example.com supports both HTTP and HTTPS)
    let url = Value::from_string("http://example.com/".to_string());
    let result = rt_read(url);

    // Should return a non-nil string
    assert!(!result.is_nil(), "HTTP fetch should not return nil");
    assert!(result.as_string().is_some(), "Result should be a string");
}

#[test]
fn read_invalid_url_returns_nil() {
    // Test that invalid URLs return nil gracefully
    let url = Value::from_string("https://this-domain-definitely-does-not-exist-12345.invalid/".to_string());
    let result = rt_read(url);

    // Should return nil for network errors
    assert!(result.is_nil(), "Invalid URL should return nil");
}

// ===== Function Composition Tests =====

use crate::operations::rt_compose;

/// Test closure for composition: adds 1 to its argument
extern "C" fn compose_test_inc(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::nil();
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_integer(i + 1)
    } else {
        Value::nil()
    }
}

/// Test closure for composition: doubles its argument
extern "C" fn compose_test_double(_env: *const ClosureObject, argc: u32, argv: *const Value) -> Value {
    if argc != 1 || argv.is_null() {
        return Value::nil();
    }
    let arg = unsafe { *argv };
    if let Some(i) = arg.as_integer() {
        Value::from_integer(i * 2)
    } else {
        Value::nil()
    }
}

#[test]
fn compose_two_functions() {
    // Test: inc >> double should apply inc first, then double
    // (inc >> double)(5) = double(inc(5)) = double(6) = 12
    let inc = ClosureObject::new(compose_test_inc as *const (), 1, vec![]);
    let inc_val = Value::from_closure(inc);

    let double = ClosureObject::new(compose_test_double as *const (), 1, vec![]);
    let double_val = Value::from_closure(double);

    let composed = rt_compose(inc_val, double_val);

    // Call composed with 5
    let args = [Value::from_integer(5)];
    let result = rt_call(composed, 1, args.as_ptr());

    // inc(5) = 6, double(6) = 12
    assert_eq!(result.as_integer(), Some(12));
}

#[test]
fn compose_three_functions() {
    // Test: inc >> double >> inc should apply: inc first, double second, inc third
    // (inc >> double >> inc)(5) = inc(double(inc(5))) = inc(double(6)) = inc(12) = 13
    let inc1 = ClosureObject::new(compose_test_inc as *const (), 1, vec![]);
    let inc1_val = Value::from_closure(inc1);

    let double = ClosureObject::new(compose_test_double as *const (), 1, vec![]);
    let double_val = Value::from_closure(double);

    let inc2 = ClosureObject::new(compose_test_inc as *const (), 1, vec![]);
    let inc2_val = Value::from_closure(inc2);

    // Compose inc >> double first
    let composed1 = rt_compose(inc1_val, double_val);
    // Then compose (inc >> double) >> inc
    let composed2 = rt_compose(composed1, inc2_val);

    // Call composed with 5
    let args = [Value::from_integer(5)];
    let result = rt_call(composed2, 1, args.as_ptr());

    // inc(5) = 6, double(6) = 12, inc(12) = 13
    assert_eq!(result.as_integer(), Some(13));
}

// Note: Error case tests for rt_compose (non-callable arguments) are covered
// by the examples/composition.santa integration test. Unit tests for panic
// cases don't work well with the extern "C" function signatures.
