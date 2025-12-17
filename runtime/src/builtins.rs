//! Built-in functions for santa-lang runtime
//!
//! These functions are called from LLVM-compiled code via FFI.
//! LANG.txt Reference: §11 Built-in Functions

use super::value::Value;
use super::heap::{LazySequenceObject, LazySeqKind, ClosureObject};
use super::operations::{rt_add, runtime_error, type_name};
use regex::Regex;

// ============================================================================
// §11.1 Type Conversion Functions
// ============================================================================

/// `int(value)` → Integer
///
/// Parse value to Integer. Returns `0` on failure.
/// Per LANG.txt §11.1:
/// - Integer (identity): int(5) → 5
/// - Decimal (rounds to nearest, half away from zero): int(3.5) → 4, int(-3.5) → -4
/// - String: int("42") → 42, int("abc") → 0
/// - Boolean: int(true) → 1, int(false) → 0
#[no_mangle]
pub extern "C" fn rt_int(value: Value) -> Value {
    // Integer (identity)
    if let Some(i) = value.as_integer() {
        return Value::from_integer(i);
    }

    // Boolean - check before decimal since booleans might be misdetected
    if let Some(b) = value.as_bool() {
        return Value::from_integer(if b { 1 } else { 0 });
    }

    // Nil - check before decimal
    if value.is_nil() {
        return Value::from_integer(0);
    }

    // String - check before decimal since strings are heap objects
    if let Some(s) = value.as_string() {
        return match s.trim().parse::<i64>() {
            Ok(i) => Value::from_integer(i),
            Err(_) => Value::from_integer(0), // Return 0 on parse failure
        };
    }

    // Decimal (round half away from zero) - check last since it's a catch-all
    if let Some(d) = value.as_decimal() {
        return Value::from_integer(round_half_away_from_zero(d));
    }

    // Other types return 0
    Value::from_integer(0)
}

/// Round to nearest integer, with ties going away from zero
/// This is the "round half away from zero" rounding mode.
/// Examples:
///   3.5 → 4, -3.5 → -4
///   3.7 → 4, -3.7 → -4
///   3.4 → 3, -3.4 → -3
fn round_half_away_from_zero(d: f64) -> i64 {
    if d >= 0.0 {
        (d + 0.5).floor() as i64
    } else {
        (d - 0.5).ceil() as i64
    }
}

/// `ints(string)` → List[Integer]
///
/// Extract all parseable integers from a string using the regex pattern `(-?[0-9]+)`.
/// Per LANG.txt §11.1:
/// - ints("1,2,3") → [1, 2, 3]
/// - ints("15a20b35") → [15, 20, 35]
/// - ints("x: 10, y: -5") → [10, -5]
/// - ints("no numbers") → []
#[no_mangle]
pub extern "C" fn rt_ints(value: Value) -> Value {
    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => return Value::from_list(im::Vector::new()),
    };

    // Use regex to extract all integers (including negative)
    let re = Regex::new(r"-?[0-9]+").expect("valid regex");
    let integers: im::Vector<Value> = re
        .find_iter(s)
        .filter_map(|m| m.as_str().parse::<i64>().ok())
        .map(Value::from_integer)
        .collect();

    Value::from_list(integers)
}

/// `list(value)` → List
///
/// Convert to List representation.
/// Per LANG.txt §11.1:
/// - List (identity): list([1, 2, 3]) → [1, 2, 3]
/// - Set: list({1, 2, 3}) → [1, 2, 3]
/// - Dictionary: list(#{1: 2, 3: 4}) → [[1, 2], [3, 4]] (list of [key, value] tuples)
/// - String: list("ab") → ["a", "b"] (each grapheme cluster)
/// - Range/LazySequence: forces evaluation to list (bounded sequences only)
#[no_mangle]
pub extern "C" fn rt_list(value: Value) -> Value {
    use unicode_segmentation::UnicodeSegmentation;

    // List (identity)
    if let Some(list) = value.as_list() {
        return Value::from_list(list.clone());
    }

    // Set → List
    if let Some(set) = value.as_set() {
        let list: im::Vector<Value> = set.iter().copied().collect();
        return Value::from_list(list);
    }

    // Dict → List of [key, value] tuples
    if let Some(dict) = value.as_dict() {
        let list: im::Vector<Value> = dict
            .iter()
            .map(|(k, v)| {
                let tuple: im::Vector<Value> = vec![*k, *v].into_iter().collect();
                Value::from_list(tuple)
            })
            .collect();
        return Value::from_list(list);
    }

    // String → List of grapheme clusters
    if let Some(s) = value.as_string() {
        let list: im::Vector<Value> = s
            .graphemes(true)
            .map(|g| Value::from_string(g.to_string()))
            .collect();
        return Value::from_list(list);
    }

    // LazySequence (including Range) → Force evaluation to list
    if let Some(lazy_seq) = value.as_lazy_sequence() {
        // Use collect_bounded_lazy which handles Map, Filter, and other lazy kinds
        // that require closure evaluation
        return Value::from_list(collect_bounded_lazy(lazy_seq));
    }

    // Other types return empty list
    Value::from_list(im::Vector::new())
}

/// `set(value)` → Set
///
/// Convert to Set representation.
/// Per LANG.txt §11.1:
/// - List: set([1, 2, 2, 3]) → {1, 2, 3}
/// - Set (identity): set({1, 2, 3}) → {1, 2, 3}
/// - String: set("aab") → {"a", "b"} (each grapheme cluster)
/// - Range/LazySequence: set(1..5) → {1, 2, 3, 4} (bounded sequences only)
#[no_mangle]
pub extern "C" fn rt_set(value: Value) -> Value {
    use unicode_segmentation::UnicodeSegmentation;

    // List → Set
    if let Some(list) = value.as_list() {
        let set: im::HashSet<Value> = list.iter().copied().collect();
        return Value::from_set(set);
    }

    // Set (identity)
    if let Some(set) = value.as_set() {
        return Value::from_set(set.clone());
    }

    // String → Set of grapheme clusters
    if let Some(s) = value.as_string() {
        let set: im::HashSet<Value> = s
            .graphemes(true)
            .map(|g| Value::from_string(g.to_string()))
            .collect();
        return Value::from_set(set);
    }

    // LazySequence (including Range) → Force evaluation to set
    if let Some(lazy_seq) = value.as_lazy_sequence() {
        let mut result: im::HashSet<Value> = im::HashSet::new();
        let mut current = lazy_seq.clone();

        // Iterate through the lazy sequence, collecting values
        // Note: Only works for bounded sequences
        while let Some((val, next_seq)) = current.next() {
            result.insert(val);
            current = *next_seq;
        }
        return Value::from_set(result);
    }

    // Other types return empty set
    Value::from_set(im::HashSet::new())
}

/// `dict(value)` → Dictionary
///
/// Convert to Dictionary representation.
/// Per LANG.txt §11.1:
/// - List of tuples: dict([[1, 2], [3, 4]]) → #{1: 2, 3: 4}
/// - Dictionary (identity): dict(#{1: 2, 3: 4}) → #{1: 2, 3: 4}
#[no_mangle]
pub extern "C" fn rt_dict(value: Value) -> Value {
    // Dictionary (identity)
    if let Some(dict) = value.as_dict() {
        return Value::from_dict(dict.clone());
    }

    // List of [key, value] tuples → Dict
    if let Some(list) = value.as_list() {
        let mut dict = im::HashMap::new();
        for item in list.iter() {
            if let Some(tuple) = item.as_list() {
                if tuple.len() >= 2 {
                    dict.insert(tuple[0], tuple[1]);
                }
            }
        }
        return Value::from_dict(dict);
    }

    // Other types return empty dict
    Value::from_dict(im::HashMap::new())
}

// ============================================================================
// §11.2 Collection Access Functions
// ============================================================================

/// `get(index, collection)` → Value | Nil
///
/// Get element at index following indexing rules. Returns `nil` if not found.
/// Per LANG.txt §11.2:
/// - List: get(1, [1, 2]) → 2; get(5, [1, 2]) → nil
/// - Set: get(1, {1, 2}) → 1 (membership check); get(3, {1, 2}) → nil
/// - Dictionary: get(1, #{1: 2, 3: 4}) → 2
/// - String: get(1, "hello") → "e"
#[no_mangle]
pub extern "C" fn rt_get(index: Value, collection: Value) -> Value {
    // List - index by integer
    if let Some(list) = collection.as_list() {
        if let Some(i) = index.as_integer() {
            if i >= 0 && (i as usize) < list.len() {
                return list[i as usize];
            }
        }
        return Value::nil();
    }

    // Set - membership check
    if let Some(set) = collection.as_set() {
        if set.contains(&index) {
            return index; // Return the value itself if found
        }
        return Value::nil();
    }

    // Dictionary - key lookup
    if let Some(dict) = collection.as_dict() {
        return dict.get(&index).copied().unwrap_or_else(Value::nil);
    }

    // String - index by integer to get grapheme
    if let Some(s) = collection.as_string() {
        if let Some(i) = index.as_integer() {
            if i >= 0 {
                use unicode_segmentation::UnicodeSegmentation;
                if let Some(g) = s.graphemes(true).nth(i as usize) {
                    return Value::from_string(g.to_string());
                }
            }
        }
        return Value::nil();
    }

    // LazySequence (including Range) - index by integer
    if let Some(lazy_seq) = collection.as_lazy_sequence() {
        if let Some(i) = index.as_integer() {
            if i < 0 {
                return Value::nil();
            }
            let idx = i as usize;

            use crate::heap::LazySeqKind;
            match &lazy_seq.kind {
                // Range - O(1) direct calculation
                LazySeqKind::Range { current, end, inclusive, step } => {
                    // Calculate the size of the range for bounds checking
                    if let Some(end_val) = end {
                        let size = if *step > 0 {
                            if *inclusive {
                                ((end_val - current) / step + 1) as usize
                            } else {
                                ((end_val - current + step - 1) / step).max(0) as usize
                            }
                        } else {
                            // step < 0 (descending)
                            let step_abs = step.abs();
                            if *inclusive {
                                ((current - end_val) / step_abs + 1) as usize
                            } else {
                                ((current - end_val + step_abs - 1) / step_abs).max(0) as usize
                            }
                        };

                        if idx >= size {
                            return Value::nil();
                        }
                    }
                    // Unbounded range: always valid for non-negative index

                    // Calculate value: start + index * step
                    let value = current + (idx as i64) * step;
                    return Value::from_integer(value);
                }

                // For other LazySequence types, iterate to the index
                _ => {
                    // Clone and iterate - less efficient but general
                    let mut current_seq: Box<crate::heap::LazySequenceObject> = Box::new(lazy_seq.clone());
                    for _ in 0..idx {
                        match current_seq.next() {
                            Some((_val, next_seq)) => {
                                current_seq = next_seq;
                            }
                            None => return Value::nil(),
                        }
                    }
                    if let Some((val, _next_seq)) = current_seq.next() {
                        return val;
                    }
                    return Value::nil();
                }
            }
        }
        return Value::nil();
    }

    Value::nil()
}

/// `size(collection)` → Integer
///
/// Get number of elements in a collection.
/// Per LANG.txt §11.2:
/// - List: size([1, 2]) → 2
/// - Set: size({1, 2}) → 2
/// - Dictionary: size(#{1: 2, 3: 4}) → 2
/// - String: size("hello") → 5 (grapheme count)
/// - Range (bounded): size(1..5) → 4
#[no_mangle]
pub extern "C" fn rt_size(collection: Value) -> Value {
    // List
    if let Some(list) = collection.as_list() {
        return Value::from_integer(list.len() as i64);
    }

    // Set
    if let Some(set) = collection.as_set() {
        return Value::from_integer(set.len() as i64);
    }

    // Dictionary
    if let Some(dict) = collection.as_dict() {
        return Value::from_integer(dict.len() as i64);
    }

    // String (grapheme count)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        return Value::from_integer(s.graphemes(true).count() as i64);
    }

    // Range (bounded only) - calculate size directly without iterating
    if let Some(lazy_seq) = collection.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        if let LazySeqKind::Range { current, end: Some(end_val), inclusive, step } = &lazy_seq.kind {
            // Calculate the number of elements in the range
            let start = *current;
            let end = *end_val;
            let step = *step;

            // Handle different range directions
            let count = if step > 0 {
                if start > end || (start == end && !*inclusive) {
                    0
                } else if *inclusive {
                    ((end - start) / step) + 1
                } else {
                    ((end - start - 1) / step) + 1
                }
            } else {
                // step < 0 (descending)
                if start < end || (start == end && !*inclusive) {
                    0
                } else if *inclusive {
                    ((start - end) / (-step)) + 1
                } else {
                    ((start - end - 1) / (-step)) + 1
                }
            };

            return Value::from_integer(count.max(0));
        }
        // Unbounded ranges return 0 (undefined size)
    }

    Value::from_integer(0)
}

/// `first(collection)` → Value | Nil
///
/// Get first element. Returns `nil` if collection is empty.
/// Per LANG.txt §11.2:
/// - List: first([1, 2]) → 1; first([]) → nil
/// - Set: first({1, 2}) → 1
/// - String: first("ab") → "a"
#[no_mangle]
pub extern "C" fn rt_first(collection: Value) -> Value {
    // List
    if let Some(list) = collection.as_list() {
        return list.front().copied().unwrap_or_else(Value::nil);
    }

    // Set
    if let Some(set) = collection.as_set() {
        return set.iter().next().copied().unwrap_or_else(Value::nil);
    }

    // String
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        if let Some(g) = s.graphemes(true).next() {
            return Value::from_string(g.to_string());
        }
        return Value::nil();
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        // Handle Iterate specially - get first value
        if let LazySeqKind::Iterate { current, .. } = &lazy.kind {
            return *current;
        }
        // For other lazy sequences, use next()
        if let Some((val, _)) = lazy.next() {
            return val;
        }
        return Value::nil();
    }

    Value::nil()
}

/// `second(collection)` → Value | Nil
///
/// Get second element. Returns `nil` if collection has fewer than 2 elements.
/// Per LANG.txt §11.2:
/// - List: second([1, 2]) → 2; second([1]) → nil
/// - Set: second({1, 2}) → 2
/// - String: second("ab") → "b"
/// - Range/LazySequence: second(1..5) → 2
#[no_mangle]
pub extern "C" fn rt_second(collection: Value) -> Value {
    // List
    if let Some(list) = collection.as_list() {
        return list.get(1).copied().unwrap_or_else(Value::nil);
    }

    // Set
    if let Some(set) = collection.as_set() {
        return set.iter().nth(1).copied().unwrap_or_else(Value::nil);
    }

    // String
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        if let Some(g) = s.graphemes(true).nth(1) {
            return Value::from_string(g.to_string());
        }
        return Value::nil();
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        // Get first, then second
        if let Some((_, next_seq)) = lazy.next() {
            if let Some((second_val, _)) = next_seq.next() {
                return second_val;
            }
        }
        return Value::nil();
    }

    Value::nil()
}

/// `last(collection)` → Value | Nil
///
/// Get last element. Returns `nil` if collection is empty.
/// Per LANG.txt §11.2:
/// - List: last([1, 2]) → 2; last([]) → nil
/// - Set: last({1, 2}) → 2
/// - String: last("ab") → "b"
/// - Range (bounded): last(1..5) → 4, last(1..=5) → 5
#[no_mangle]
pub extern "C" fn rt_last(collection: Value) -> Value {
    // List
    if let Some(list) = collection.as_list() {
        return list.back().copied().unwrap_or_else(Value::nil);
    }

    // Set
    if let Some(set) = collection.as_set() {
        return set.iter().last().copied().unwrap_or_else(Value::nil);
    }

    // String
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        if let Some(g) = s.graphemes(true).next_back() {
            return Value::from_string(g.to_string());
        }
        return Value::nil();
    }

    // LazySequence - for bounded sequences, iterate to find last
    if let Some(lazy) = collection.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        // For Range, calculate last directly (O(1))
        if let LazySeqKind::Range { current, end: Some(end_val), inclusive, step } = &lazy.kind {
            let start = *current;
            let end = *end_val;
            let step = *step;

            // Calculate size first to check if range is non-empty
            let is_empty = if step > 0 {
                start > end || (start == end && !*inclusive)
            } else {
                start < end || (start == end && !*inclusive)
            };

            if is_empty {
                return Value::nil();
            }

            // Calculate last element
            let last = if *inclusive {
                end
            } else if step > 0 {
                // For exclusive ascending: last = end - step (adjusted if needed)
                let n = (end - start - 1) / step;
                start + n * step
            } else {
                // For exclusive descending: last = end - step
                let n = (start - end - 1) / (-step);
                start + n * step
            };

            return Value::from_integer(last);
        }
        // For other lazy sequences, iterate (only works for bounded)
        let mut last_val = None;
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            last_val = Some(val);
            current = *next_seq;
        }
        return last_val.unwrap_or_else(Value::nil);
    }

    Value::nil()
}

/// `rest(collection)` → Collection
///
/// Get all but first element. Returns empty collection if input has ≤1 element.
/// Per LANG.txt §11.2:
/// - List: rest([1, 2]) → [2]; rest([1]) → []
/// - Set: rest({1, 2}) → {2}
/// - String: rest("ab") → "b"
/// - Range/LazySequence: rest(1..5) → LazySequence(2..5)
#[no_mangle]
pub extern "C" fn rt_rest(collection: Value) -> Value {
    // List
    if let Some(list) = collection.as_list() {
        if list.is_empty() {
            return Value::from_list(im::Vector::new());
        }
        return Value::from_list(list.clone().split_off(1));
    }

    // Set
    if let Some(set) = collection.as_set() {
        let mut iter = set.iter();
        iter.next(); // Skip first
        let rest: im::HashSet<Value> = iter.copied().collect();
        return Value::from_set(rest);
    }

    // String
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        let rest: String = s.graphemes(true).skip(1).collect();
        return Value::from_string(rest);
    }

    // LazySequence (including Range) - return rest as a new LazySequence
    if let Some(lazy) = collection.as_lazy_sequence() {
        // Get first element, return the "next" sequence
        if let Some((_, next_seq)) = lazy.next() {
            return Value::from_lazy_sequence(next_seq);
        }
        // Empty sequence - return empty list
        return Value::from_list(im::Vector::new());
    }

    Value::from_list(im::Vector::new())
}

/// `keys(dictionary)` → List
///
/// Get dictionary keys as a List.
/// Per LANG.txt §11.2:
/// - keys(#{1: 2, 3: 4}) → [1, 3]
#[no_mangle]
pub extern "C" fn rt_keys(collection: Value) -> Value {
    if let Some(dict) = collection.as_dict() {
        let keys: im::Vector<Value> = dict.keys().copied().collect();
        return Value::from_list(keys);
    }

    Value::from_list(im::Vector::new())
}

/// `values(dictionary)` → List
///
/// Get dictionary values as a List.
/// Per LANG.txt §11.2:
/// - values(#{1: 2, 3: 4}) → [2, 4]
#[no_mangle]
pub extern "C" fn rt_values(collection: Value) -> Value {
    if let Some(dict) = collection.as_dict() {
        let values: im::Vector<Value> = dict.values().copied().collect();
        return Value::from_list(values);
    }

    Value::from_list(im::Vector::new())
}

// ============================================================================
// §11.3 Collection Modification Functions
// ============================================================================

/// `push(value, collection)` → Collection
///
/// Add a new value to a collection. Returns new collection (immutable).
/// Per LANG.txt §11.3:
/// - List: push(3, [1, 2]) → [1, 2, 3] (appends to end)
/// - Set: push(3, {1, 2}) → {1, 2, 3}; push(1, {1, 2}) → {1, 2}
///
/// Per LANG.txt §3.11: Pushing a non-hashable value to a Set produces RuntimeErr.
#[no_mangle]
pub extern "C-unwind" fn rt_push(value: Value, collection: Value) -> Value {
    // List - append to end
    if let Some(list) = collection.as_list() {
        let mut new_list = list.clone();
        new_list.push_back(value);
        return Value::from_list(new_list);
    }

    // Set - insert (no-op if already present)
    if let Some(set) = collection.as_set() {
        // Check hashability per LANG.txt §3.11
        if !value.is_hashable() {
            runtime_error(&format!(
                "{} is not hashable and cannot be added to a Set",
                type_name(&value)
            ));
        }
        let new_set = set.update(value);
        return Value::from_set(new_set);
    }

    // Unsupported type - return original collection
    collection
}

/// `assoc(key, value, collection)` → Collection
///
/// Associate the provided key/index with the given value. Returns new collection (immutable).
/// Per LANG.txt §11.3:
/// - List: assoc(0, 3, [1, 2]) → [3, 2]; fills with nil if beyond size
/// - Dictionary: assoc(1, 1, #{1: 2, 3: 4}) → #{1: 1, 3: 4}
///
/// Per LANG.txt §3.11: Using a non-hashable key in a Dictionary produces RuntimeErr.
#[no_mangle]
pub extern "C-unwind" fn rt_assoc(key: Value, value: Value, collection: Value) -> Value {
    // List - replace at index, filling with nil if needed
    if let Some(list) = collection.as_list() {
        if let Some(index) = key.as_integer() {
            if index >= 0 {
                let idx = index as usize;
                let mut new_list = list.clone();

                // Fill with nil if index is beyond current size
                while new_list.len() <= idx {
                    new_list.push_back(Value::nil());
                }

                // Set the value at index
                new_list.set(idx, value);
                return Value::from_list(new_list);
            }
        }
        return Value::from_list(list.clone());
    }

    // Dictionary - insert or update
    if let Some(dict) = collection.as_dict() {
        // Check hashability per LANG.txt §3.11
        if !key.is_hashable() {
            runtime_error(&format!(
                "{} is not hashable and cannot be used as a Dictionary key",
                type_name(&key)
            ));
        }
        let new_dict = dict.update(key, value);
        return Value::from_dict(new_dict);
    }

    // Unsupported type - return original collection
    collection
}

// ============================================================================
// §11.3.1 Update Functions (requires call_closure helper)
// ============================================================================

/// Helper: call a closure with the given arguments
///
/// This is an internal helper for transformation functions and memoized closure calls.
pub fn call_closure(closure: &ClosureObject, args: &[Value]) -> Value {
    // Cast the function pointer to the expected signature
    let fn_ptr: extern "C" fn(*const ClosureObject, u32, *const Value) -> Value =
        unsafe { std::mem::transmute(closure.function_ptr) };

    // Call the function with the closure environment and arguments
    fn_ptr(
        closure as *const ClosureObject,
        args.len() as u32,
        args.as_ptr(),
    )
}

/// `update(key, updater, collection)` → Collection
///
/// Update the given index/key using a pure updater function. The updater
/// receives the current value (or `nil` if not present).
///
/// Per LANG.txt §11.3:
/// - List: update(0, _ + 1, [1, 2]) → [2, 2]; fills with nil if index beyond current size
/// - Dictionary: update(0, || 1, #{}) → #{0: 1}; update(1, _ + 1, #{1: 2}) → #{1: 3}
#[no_mangle]
pub extern "C-unwind" fn rt_update(key: Value, updater: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return original collection
    let closure = match updater.as_closure() {
        Some(c) => c,
        None => return collection,
    };

    // List - update at index, filling with nil if needed
    if let Some(list) = collection.as_list() {
        if let Some(index) = key.as_integer() {
            if index >= 0 {
                let idx = index as usize;
                let mut new_list = list.clone();

                // Fill with nil if index is beyond current size
                while new_list.len() <= idx {
                    new_list.push_back(Value::nil());
                }

                // Get current value (might be nil if we just extended)
                let current = new_list.get(idx).cloned().unwrap_or_else(Value::nil);

                // Call updater with current value
                let new_value = call_closure(closure, &[current]);

                // Set the new value at index
                new_list.set(idx, new_value);
                return Value::from_list(new_list);
            }
        }
        return Value::from_list(list.clone());
    }

    // Dictionary - update key
    if let Some(dict) = collection.as_dict() {
        // Check hashability per LANG.txt §3.11
        if !key.is_hashable() {
            runtime_error(&format!(
                "{} is not hashable and cannot be used as a Dictionary key",
                type_name(&key)
            ));
        }

        // Get current value (or nil if not present)
        let current = dict.get(&key).cloned().unwrap_or_else(Value::nil);

        // Call updater with current value
        let new_value = call_closure(closure, &[current]);

        // Update the dictionary
        let new_dict = dict.update(key, new_value);
        return Value::from_dict(new_dict);
    }

    // Unsupported type - return original collection
    collection
}

/// `update_d(key, default, updater, collection)` → Collection
///
/// Update using a pure updater function, with a default value if key doesn't exist.
///
/// Per LANG.txt §11.3:
/// - List: update_d(0, 0, _ + 1, [1, 2]) → [2, 2]; fills with nil at missing indices
/// - Dictionary: update_d(0, 0, _ + 1, #{}) → #{0: 1}
#[no_mangle]
pub extern "C-unwind" fn rt_update_d(key: Value, default: Value, updater: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return original collection
    let closure = match updater.as_closure() {
        Some(c) => c,
        None => return collection,
    };

    // List - update at index, filling with nil if needed
    if let Some(list) = collection.as_list() {
        if let Some(index) = key.as_integer() {
            if index >= 0 {
                let idx = index as usize;
                let mut new_list = list.clone();

                // Fill with nil if index is beyond current size
                while new_list.len() <= idx {
                    new_list.push_back(Value::nil());
                }

                // Get current value, or use default if nil
                let current_raw = new_list.get(idx).cloned().unwrap_or_else(Value::nil);
                let current = if current_raw.is_nil() { default } else { current_raw };

                // Call updater with current value (or default)
                let new_value = call_closure(closure, &[current]);

                // Set the new value at index
                new_list.set(idx, new_value);
                return Value::from_list(new_list);
            }
        }
        return Value::from_list(list.clone());
    }

    // Dictionary - update key with default
    if let Some(dict) = collection.as_dict() {
        // Check hashability per LANG.txt §3.11
        if !key.is_hashable() {
            runtime_error(&format!(
                "{} is not hashable and cannot be used as a Dictionary key",
                type_name(&key)
            ));
        }

        // Get current value, or use default if not present
        let current = dict.get(&key).cloned().unwrap_or(default);

        // Call updater with current value (or default)
        let new_value = call_closure(closure, &[current]);

        // Update the dictionary
        let new_dict = dict.update(key, new_value);
        return Value::from_dict(new_dict);
    }

    // Unsupported type - return original collection
    collection
}

// ============================================================================
// §11.4 Transformation Functions
// ============================================================================

/// `map(mapper, collection)` → Collection
///
/// Apply a pure mapper function to each element. Returns same collection type
/// (except String → List).
///
/// Per LANG.txt §11.4:
/// - List: map(_ + 1, [1, 2]) → [2, 3]
/// - Set: map(_ + 1, {1, 2}) → {2, 3}
/// - Dictionary: map(_ + 1, #{1: 2, 3: 4}) → #{1: 3, 3: 5}
///   - Mapper receives value only (for 1-arg mapper)
///   - Mapper receives (value, key) for 2-arg mapper
/// - String: map(_ * 2, "ab") → ["aa", "bb"] (returns List)
#[no_mangle]
pub extern "C" fn rt_map(mapper: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return empty collection
    let closure = match mapper.as_closure() {
        Some(c) => c,
        None => return Value::from_list(im::Vector::new()),
    };

    // List → List
    if let Some(list) = collection.as_list() {
        let mapped: im::Vector<Value> = list
            .iter()
            .map(|v| call_closure(closure, &[*v]))
            .collect();
        return Value::from_list(mapped);
    }

    // Set → Set
    if let Some(set) = collection.as_set() {
        let mapped: im::HashSet<Value> = set
            .iter()
            .map(|v| call_closure(closure, &[*v]))
            .collect();
        return Value::from_set(mapped);
    }

    // Dict → Dict (mapper receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = closure.arity >= 2;
        let mapped: im::HashMap<Value, Value> = dict
            .iter()
            .map(|(k, v)| {
                let new_value = if is_two_arg {
                    call_closure(closure, &[*v, *k])
                } else {
                    call_closure(closure, &[*v])
                };
                (*k, new_value)
            })
            .collect();
        return Value::from_dict(mapped);
    }

    // String → List (each grapheme cluster)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        let mapped: im::Vector<Value> = s
            .graphemes(true)
            .map(|g| {
                let char_val = Value::from_string(g.to_string());
                call_closure(closure, &[char_val])
            })
            .collect();
        return Value::from_list(mapped);
    }

    // LazySequence (including Ranges) → LazySequence (lazy map)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let lazy_map = LazySequenceObject::new(LazySeqKind::Map {
            source: Box::new(lazy.clone()),
            mapper,
        });
        return Value::from_lazy_sequence(lazy_map);
    }

    // Unsupported type - return empty list
    Value::from_list(im::Vector::new())
}

/// `filter(predicate, collection)` → Collection
///
/// Keep elements where predicate returns truthy. Returns same collection type
/// (except String → List).
///
/// Per LANG.txt §11.4:
/// - List: filter(_ == 1, [1, 2]) → [1]
/// - Set: filter(_ == 1, {1, 2}) → {1}
/// - Dictionary: filter(_ == 2, #{1: 2, 3: 4}) → #{1: 2}
///   - Predicate receives value only (for 1-arg predicate)
///   - Predicate receives (value, key) for 2-arg predicate
/// - String: filter(_ == "a", "ab") → ["a"] (returns List)
#[no_mangle]
pub extern "C" fn rt_filter(predicate: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return empty collection
    let closure = match predicate.as_closure() {
        Some(c) => c,
        None => return Value::from_list(im::Vector::new()),
    };

    // List → List
    if let Some(list) = collection.as_list() {
        let filtered: im::Vector<Value> = list
            .iter()
            .filter(|v| call_closure(closure, &[**v]).is_truthy())
            .copied()
            .collect();
        return Value::from_list(filtered);
    }

    // Set → Set
    if let Some(set) = collection.as_set() {
        let filtered: im::HashSet<Value> = set
            .iter()
            .filter(|v| call_closure(closure, &[**v]).is_truthy())
            .copied()
            .collect();
        return Value::from_set(filtered);
    }

    // Dict → Dict (predicate receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = closure.arity >= 2;
        let filtered: im::HashMap<Value, Value> = dict
            .iter()
            .filter(|(k, v)| {
                let keep = if is_two_arg {
                    call_closure(closure, &[**v, **k])
                } else {
                    call_closure(closure, &[**v])
                };
                keep.is_truthy()
            })
            .map(|(k, v)| (*k, *v))
            .collect();
        return Value::from_dict(filtered);
    }

    // String → List (each grapheme cluster that passes predicate)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        let filtered: im::Vector<Value> = s
            .graphemes(true)
            .filter_map(|g| {
                let char_val = Value::from_string(g.to_string());
                if call_closure(closure, &[char_val]).is_truthy() {
                    Some(Value::from_string(g.to_string()))
                } else {
                    None
                }
            })
            .collect();
        return Value::from_list(filtered);
    }

    // LazySequence (including Ranges) → LazySequence (lazy filter)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let lazy_filter = LazySequenceObject::new(LazySeqKind::Filter {
            source: Box::new(lazy.clone()),
            predicate,
        });
        return Value::from_lazy_sequence(lazy_filter);
    }

    // Unsupported type - return empty list
    Value::from_list(im::Vector::new())
}

/// `flat_map(mapper, collection)` → List
///
/// Apply mapper and flatten resulting lists into a single list.
///
/// Per LANG.txt §11.4:
/// - flat_map(_ * 2, [[1, 2], [3, 4]]) → [2, 4, 6, 8]
/// - flat_map(|x| [x, x * 2], [1, 2]) → [1, 2, 2, 4]
/// - flat_map(|x| [x, x * 2], 1..4) → [1, 2, 2, 4, 3, 6]  (Range support)
#[no_mangle]
pub extern "C" fn rt_flat_map(mapper: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return empty list
    let closure = match mapper.as_closure() {
        Some(c) => c,
        None => return Value::from_list(im::Vector::new()),
    };

    let mut result: im::Vector<Value> = im::Vector::new();

    // Helper to add mapped result elements to result
    let mut extend_result = |mapped: Value| {
        if let Some(list) = mapped.as_list() {
            for v in list.iter() {
                result.push_back(*v);
            }
        }
        // If the mapper returns non-list, we could add it directly,
        // but per spec flat_map expects mapper to return lists
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            let mapped = call_closure(closure, &[*v]);
            extend_result(mapped);
        }
        return Value::from_list(result);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            let mapped = call_closure(closure, &[*v]);
            extend_result(mapped);
        }
        return Value::from_list(result);
    }

    // Dict (mapper receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = closure.arity >= 2;
        for (k, v) in dict.iter() {
            let mapped = if is_two_arg {
                call_closure(closure, &[*v, *k])
            } else {
                call_closure(closure, &[*v])
            };
            extend_result(mapped);
        }
        return Value::from_list(result);
    }

    // String
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            let mapped = call_closure(closure, &[char_val]);
            extend_result(mapped);
        }
        return Value::from_list(result);
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            let mapped = call_closure(closure, &[val]);
            extend_result(mapped);
            current = *next_seq;
        }
        return Value::from_list(result);
    }

    // Unsupported type - return empty list
    Value::from_list(im::Vector::new())
}

/// `filter_map(mapper, collection)` → Collection
///
/// Map and filter in one pass - keeps only truthy mapped results.
/// Returns same collection type (except String → List, Range → List).
///
/// Per LANG.txt §11.4:
/// - [1, 2, 3, 4] |> filter_map(|v| if v % 2 { v * 2 }) → [2, 6]
/// - 1..5 |> filter_map(|v| if v % 2 { v * 2 }) → [2, 6]  (Range support)
#[no_mangle]
pub extern "C" fn rt_filter_map(mapper: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return empty collection
    let closure = match mapper.as_closure() {
        Some(c) => c,
        None => return Value::from_list(im::Vector::new()),
    };

    // List → List
    if let Some(list) = collection.as_list() {
        let filtered: im::Vector<Value> = list
            .iter()
            .filter_map(|v| {
                let mapped = call_closure(closure, &[*v]);
                if mapped.is_truthy() {
                    Some(mapped)
                } else {
                    None
                }
            })
            .collect();
        return Value::from_list(filtered);
    }

    // Set → Set
    if let Some(set) = collection.as_set() {
        let filtered: im::HashSet<Value> = set
            .iter()
            .filter_map(|v| {
                let mapped = call_closure(closure, &[*v]);
                if mapped.is_truthy() {
                    Some(mapped)
                } else {
                    None
                }
            })
            .collect();
        return Value::from_set(filtered);
    }

    // Dict → Dict (mapper receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = closure.arity >= 2;
        let filtered: im::HashMap<Value, Value> = dict
            .iter()
            .filter_map(|(k, v)| {
                let mapped = if is_two_arg {
                    call_closure(closure, &[*v, *k])
                } else {
                    call_closure(closure, &[*v])
                };
                if mapped.is_truthy() {
                    Some((*k, mapped))
                } else {
                    None
                }
            })
            .collect();
        return Value::from_dict(filtered);
    }

    // String → List
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        let filtered: im::Vector<Value> = s
            .graphemes(true)
            .filter_map(|g| {
                let char_val = Value::from_string(g.to_string());
                let mapped = call_closure(closure, &[char_val]);
                if mapped.is_truthy() {
                    Some(mapped)
                } else {
                    None
                }
            })
            .collect();
        return Value::from_list(filtered);
    }

    // LazySequence (including Range) → List
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut result: im::Vector<Value> = im::Vector::new();
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            let mapped = call_closure(closure, &[val]);
            if mapped.is_truthy() {
                result.push_back(mapped);
            }
            current = *next_seq;
        }
        return Value::from_list(result);
    }

    // Unsupported type - return empty list
    Value::from_list(im::Vector::new())
}

/// `find_map(mapper, collection)` → Value | Nil
///
/// Find first element where mapper returns truthy, return that mapped value.
///
/// Per LANG.txt §11.4:
/// - [1, 2] |> find_map(|v| if v % 2 { v * 2 }) → 2
/// - 1..5 |> find_map(|v| if v % 2 { v * 2 }) → 2  (Range support)
#[no_mangle]
pub extern "C" fn rt_find_map(mapper: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return nil
    let closure = match mapper.as_closure() {
        Some(c) => c,
        None => return Value::nil(),
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            let mapped = call_closure(closure, &[*v]);
            if mapped.is_truthy() {
                return mapped;
            }
        }
        return Value::nil();
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            let mapped = call_closure(closure, &[*v]);
            if mapped.is_truthy() {
                return mapped;
            }
        }
        return Value::nil();
    }

    // Dict (mapper receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = closure.arity >= 2;
        for (k, v) in dict.iter() {
            let mapped = if is_two_arg {
                call_closure(closure, &[*v, *k])
            } else {
                call_closure(closure, &[*v])
            };
            if mapped.is_truthy() {
                return mapped;
            }
        }
        return Value::nil();
    }

    // String
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            let mapped = call_closure(closure, &[char_val]);
            if mapped.is_truthy() {
                return mapped;
            }
        }
        return Value::nil();
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            let mapped = call_closure(closure, &[val]);
            if mapped.is_truthy() {
                return mapped;
            }
            current = *next_seq;
        }
        return Value::nil();
    }

    // Unsupported type - return nil
    Value::nil()
}

// ============================================================================
// §11.5 Reduction Functions
// ============================================================================

/// `reduce(reducer, collection)` → Value
///
/// Apply a pure reducer function, using first element as initial accumulator.
/// **Throws RuntimeErr if collection is empty.**
///
/// Per LANG.txt §11.5:
/// - reduce(+, [1, 2]) → 3
/// - reduce(+, {1, 2}) → 3
/// - reduce(+, []) → RuntimeErr
#[no_mangle]
pub extern "C-unwind" fn rt_reduce(reducer: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return nil
    let closure = match reducer.as_closure() {
        Some(c) => c,
        None => return Value::nil(),
    };

    // Helper for the common reduction logic
    // Returns None if the collection is empty
    fn do_reduce(
        closure: &ClosureObject,
        mut iter: impl Iterator<Item = Value>,
    ) -> Option<Value> {
        // Get first element as initial accumulator
        let mut acc = iter.next()?;

        // Reduce over remaining elements
        for v in iter {
            acc = call_closure(closure, &[acc, v]);
        }

        Some(acc)
    }

    // List
    if let Some(list) = collection.as_list() {
        return match do_reduce(closure, list.iter().copied()) {
            Some(v) => v,
            None => runtime_error("reduce on empty collection"),
        };
    }

    // Set
    if let Some(set) = collection.as_set() {
        return match do_reduce(closure, set.iter().copied()) {
            Some(v) => v,
            None => runtime_error("reduce on empty collection"),
        };
    }

    // Dict (reducer receives acc, value, or acc, value, key for 3-arg)
    if let Some(dict) = collection.as_dict() {
        let is_three_arg = closure.arity >= 3;
        let mut iter = dict.iter();

        // Get first element as initial accumulator
        let (_, first_v) = match iter.next() {
            Some(kv) => kv,
            None => runtime_error("reduce on empty collection"),
        };
        let mut acc = *first_v;

        // Reduce over remaining elements
        for (k, v) in iter {
            acc = if is_three_arg {
                call_closure(closure, &[acc, *v, *k])
            } else {
                call_closure(closure, &[acc, *v])
            };
        }

        return acc;
    }

    // String (each grapheme)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        let graphemes: Vec<_> = s.graphemes(true).collect();
        if graphemes.is_empty() {
            runtime_error("reduce on empty collection");
        }

        let mut acc = Value::from_string(graphemes[0].to_string());
        for g in &graphemes[1..] {
            let char_val = Value::from_string((*g).to_string());
            acc = call_closure(closure, &[acc, char_val]);
        }

        return acc;
    }

    // LazySequence - iterate using next(), first element is initial accumulator
    // WARNING: Unbounded sequences will loop forever unless break is used
    if let Some(lazy) = collection.as_lazy_sequence() {
        // Get first element as initial accumulator
        let (first_val, mut current) = match lazy.next() {
            Some((v, next)) => (v, *next),
            None => runtime_error("reduce on empty collection"),
        };

        let mut acc = first_val;
        while let Some((val, next_lazy)) = current.next() {
            acc = call_closure(closure, &[acc, val]);
            current = *next_lazy;
        }
        return acc;
    }

    Value::nil()
}

/// `fold(initial, folder, collection)` → Value
///
/// Fold with explicit initial value. Returns initial if collection is empty.
/// Supports early termination via `break` statement in the folder closure.
///
/// Per LANG.txt §11.5:
/// - fold(0, +, [1, 2]) → 3
/// - fold(0, +, []) → 0
#[no_mangle]
pub extern "C" fn rt_fold(initial: Value, folder: Value, collection: Value) -> Value {
    use crate::break_handling::{break_occurred, take_break_value, reset_break_state};

    // Reset break state at the start of iteration
    reset_break_state();

    // Get the closure - if not a closure, return initial
    let closure = match folder.as_closure() {
        Some(c) => c,
        None => return initial,
    };

    let mut acc = initial;

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            acc = call_closure(closure, &[acc, *v]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return acc;
            }
        }
        return acc;
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            acc = call_closure(closure, &[acc, *v]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return acc;
            }
        }
        return acc;
    }

    // Dict (folder receives acc, value, or acc, value, key for 3-arg)
    if let Some(dict) = collection.as_dict() {
        let is_three_arg = closure.arity >= 3;
        for (k, v) in dict.iter() {
            acc = if is_three_arg {
                call_closure(closure, &[acc, *v, *k])
            } else {
                call_closure(closure, &[acc, *v])
            };
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return acc;
            }
        }
        return acc;
    }

    // String (each grapheme)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            acc = call_closure(closure, &[acc, char_val]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return acc;
            }
        }
        return acc;
    }

    // LazySequence - iterate using next() until exhausted
    // Break support allows termination of unbounded sequences
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current = lazy.clone();
        while let Some((val, next_lazy)) = current.next() {
            acc = call_closure(closure, &[acc, val]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return acc;
            }
            current = *next_lazy;
        }
        return acc;
    }

    acc
}

/// `scan(initial, folder, collection)` → List
///
/// Return all intermediate fold results as a list.
///
/// Per LANG.txt §11.5:
/// - scan(0, +, [1, 2]) → [1, 3]
#[no_mangle]
pub extern "C" fn rt_scan(initial: Value, folder: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return empty list
    let closure = match folder.as_closure() {
        Some(c) => c,
        None => return Value::from_list(im::Vector::new()),
    };

    let mut acc = initial;
    let mut results: im::Vector<Value> = im::Vector::new();

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            acc = call_closure(closure, &[acc, *v]);
            results.push_back(acc);
        }
        return Value::from_list(results);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            acc = call_closure(closure, &[acc, *v]);
            results.push_back(acc);
        }
        return Value::from_list(results);
    }

    // Dict (folder receives acc, value, or acc, value, key for 3-arg)
    if let Some(dict) = collection.as_dict() {
        let is_three_arg = closure.arity >= 3;
        for (k, v) in dict.iter() {
            acc = if is_three_arg {
                call_closure(closure, &[acc, *v, *k])
            } else {
                call_closure(closure, &[acc, *v])
            };
            results.push_back(acc);
        }
        return Value::from_list(results);
    }

    // String (each grapheme)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            acc = call_closure(closure, &[acc, char_val]);
            results.push_back(acc);
        }
        return Value::from_list(results);
    }

    // LazySequence - collect intermediate results
    // WARNING: Unbounded sequences will loop forever unless break is used
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current = lazy.clone();
        while let Some((val, next_lazy)) = current.next() {
            acc = call_closure(closure, &[acc, val]);
            results.push_back(acc);
            current = *next_lazy;
        }
        return Value::from_list(results);
    }

    Value::from_list(results)
}

/// `fold_s(initial, folder, collection)` → Value
///
/// Fold with state that passes through each step. The accumulator is a list
/// where the first element is the result and remaining elements are state.
/// Only the first element is returned at the end.
///
/// Per LANG.txt §11.5:
/// - fold_s([0, 1], |[a, b], _| [b, a + b], 1..10) → 55 (Fibonacci)
#[no_mangle]
pub extern "C" fn rt_fold_s(initial: Value, folder: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return first element of initial
    let closure = match folder.as_closure() {
        Some(c) => c,
        None => {
            // Return first element of initial if it's a list
            if let Some(list) = initial.as_list() {
                return list.front().copied().unwrap_or_else(Value::nil);
            }
            return initial;
        }
    };

    let mut acc = initial;

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            acc = call_closure(closure, &[acc, *v]);
        }
        // Return first element of final state
        if let Some(state_list) = acc.as_list() {
            return state_list.front().copied().unwrap_or_else(Value::nil);
        }
        return acc;
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            acc = call_closure(closure, &[acc, *v]);
        }
        if let Some(state_list) = acc.as_list() {
            return state_list.front().copied().unwrap_or_else(Value::nil);
        }
        return acc;
    }

    // Dict
    if let Some(dict) = collection.as_dict() {
        let is_three_arg = closure.arity >= 3;
        for (k, v) in dict.iter() {
            acc = if is_three_arg {
                call_closure(closure, &[acc, *v, *k])
            } else {
                call_closure(closure, &[acc, *v])
            };
        }
        if let Some(state_list) = acc.as_list() {
            return state_list.front().copied().unwrap_or_else(Value::nil);
        }
        return acc;
    }

    // String (each grapheme)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            acc = call_closure(closure, &[acc, char_val]);
        }
        if let Some(state_list) = acc.as_list() {
            return state_list.front().copied().unwrap_or_else(Value::nil);
        }
        return acc;
    }

    // LazySequence (including Ranges) - iterate through the sequence
    // WARNING: Unbounded sequences will loop forever unless break is used
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current = lazy.clone();
        while let Some((val, next_lazy)) = current.next() {
            acc = call_closure(closure, &[acc, val]);
            current = *next_lazy;
        }
        if let Some(state_list) = acc.as_list() {
            return state_list.front().copied().unwrap_or_else(Value::nil);
        }
        return acc;
    }

    // For empty collection, return first element of initial
    if let Some(state_list) = acc.as_list() {
        return state_list.front().copied().unwrap_or_else(Value::nil);
    }
    acc
}

// ============================================================================
// §11.6 Iteration
// ============================================================================

// ============================================================================
// §11.7 Search Functions
// ============================================================================

/// `find(predicate, collection)` → Value | Nil
///
/// Find first element where predicate returns truthy. Returns `nil` if not found.
///
/// Per LANG.txt §11.7:
/// - find(_ % 2, [1, 2]) → 1
/// - find(_ % 2, {1, 2}) → 1
/// - find(_ == "b", "ab") → "b"
/// - find(_ > 5, 1..10) → 6  (Range support)
#[no_mangle]
pub extern "C" fn rt_find(predicate: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return nil
    let closure = match predicate.as_closure() {
        Some(c) => c,
        None => return Value::nil(),
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            if call_closure(closure, &[*v]).is_truthy() {
                return *v;
            }
        }
        return Value::nil();
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            if call_closure(closure, &[*v]).is_truthy() {
                return *v;
            }
        }
        return Value::nil();
    }

    // Dict (predicate receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = closure.arity >= 2;
        for (k, v) in dict.iter() {
            let matches = if is_two_arg {
                call_closure(closure, &[*v, *k])
            } else {
                call_closure(closure, &[*v])
            };
            if matches.is_truthy() {
                return *v;
            }
        }
        return Value::nil();
    }

    // String (each grapheme)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            if call_closure(closure, &[char_val]).is_truthy() {
                return Value::from_string(g.to_string());
            }
        }
        return Value::nil();
    }

    // LazySequence (including Range, Map, Filter, etc.)
    if let Some(lazy) = collection.as_lazy_sequence() {
        return find_in_lazy(lazy, closure);
    }

    Value::nil()
}

/// Helper to find first matching element in any lazy sequence
/// Handles all lazy sequence variants including Map, Filter, and Iterate
fn find_in_lazy(lazy: &LazySequenceObject, predicate: &ClosureObject) -> Value {
    // Safety limit to prevent infinite loops
    const MAX_ITERATIONS: usize = 10_000_000;

    match &lazy.kind {
        LazySeqKind::Repeat { value } => {
            // Repeat is infinite - check the repeated value once
            if call_closure(predicate, &[*value]).is_truthy() {
                return *value;
            }
            // If not found in first iteration, will never be found - return nil
            Value::nil()
        }

        LazySeqKind::Cycle { source, index } => {
            if source.is_empty() {
                return Value::nil();
            }
            // Check each element in the source once
            for (i, _val) in source.iter().enumerate() {
                let check_idx = (*index + i) % source.len();
                if call_closure(predicate, &[source[check_idx]]).is_truthy() {
                    return source[check_idx];
                }
            }
            Value::nil()
        }

        LazySeqKind::Range { current, end, inclusive, step } => {
            let mut cur = *current;
            for _ in 0..MAX_ITERATIONS {
                // Check if exhausted
                if let Some(end_val) = end {
                    let at_end = if *inclusive {
                        if *step > 0 { cur > *end_val } else { cur < *end_val }
                    } else if *step > 0 {
                        cur >= *end_val
                    } else {
                        cur <= *end_val
                    };
                    if at_end {
                        return Value::nil();
                    }
                }
                let val = Value::from_integer(cur);
                if call_closure(predicate, &[val]).is_truthy() {
                    return val;
                }
                cur += step;
            }
            Value::nil()
        }

        LazySeqKind::Iterate { generator, current } => {
            if let Some(gen_closure) = generator.as_closure() {
                let mut cur = *current;
                for _ in 0..MAX_ITERATIONS {
                    if call_closure(predicate, &[cur]).is_truthy() {
                        return cur;
                    }
                    cur = call_closure(gen_closure, &[cur]);
                }
            }
            Value::nil()
        }

        LazySeqKind::Map { source, mapper } => {
            if let Some(map_closure) = mapper.as_closure() {
                // Iterate through source elements, map each, check predicate
                let source_elements = collect_bounded_lazy(source);
                for val in source_elements {
                    let mapped = call_closure(map_closure, &[val]);
                    if call_closure(predicate, &[mapped]).is_truthy() {
                        return mapped;
                    }
                }
            }
            Value::nil()
        }

        LazySeqKind::Filter { source, predicate: filter_pred } => {
            if let Some(filter_closure) = filter_pred.as_closure() {
                // Iterate through source elements, filter, then check predicate
                let source_elements = collect_bounded_lazy(source);
                for val in source_elements {
                    if call_closure(filter_closure, &[val]).is_truthy()
                        && call_closure(predicate, &[val]).is_truthy() {
                            return val;
                        }
                }
            }
            Value::nil()
        }

        LazySeqKind::Skip { source, remaining } => {
            let source_elements = collect_bounded_lazy(source);
            for (i, val) in source_elements.into_iter().enumerate() {
                if i >= *remaining
                    && call_closure(predicate, &[val]).is_truthy() {
                        return val;
                    }
            }
            Value::nil()
        }

        LazySeqKind::Combinations { source, size, indices, done } => {
            if *done || source.is_empty() || *size == 0 || *size > source.len() {
                return Value::nil();
            }

            let mut current_indices = indices.clone();
            let n = source.len();

            for _ in 0..MAX_ITERATIONS {
                let combination: im::Vector<Value> = current_indices
                    .iter()
                    .map(|&i| source[i])
                    .collect();
                let val = Value::from_list(combination);

                if call_closure(predicate, &[val]).is_truthy() {
                    return val;
                }

                // Advance to next combination
                let mut i = *size - 1;
                while current_indices[i] == n - size + i {
                    if i == 0 {
                        return Value::nil(); // All combinations exhausted
                    }
                    i -= 1;
                }
                current_indices[i] += 1;
                for j in (i + 1)..*size {
                    current_indices[j] = current_indices[j - 1] + 1;
                }
            }
            Value::nil()
        }

        LazySeqKind::Zip { sources } => {
            if sources.is_empty() {
                return Value::nil();
            }

            let source_vecs: Vec<im::Vector<Value>> = sources
                .iter()
                .map(collect_bounded_lazy)
                .collect();

            let min_len = source_vecs.iter().map(|v| v.len()).min().unwrap_or(0);

            for i in 0..min_len {
                let tuple: im::Vector<Value> = source_vecs
                    .iter()
                    .map(|v| v[i])
                    .collect();
                let val = Value::from_list(tuple);
                if call_closure(predicate, &[val]).is_truthy() {
                    return val;
                }
            }
            Value::nil()
        }
    }
}

/// `count(predicate, collection)` → Integer
///
/// Count elements where predicate returns truthy.
///
/// Per LANG.txt §11.7:
/// - count(_ % 2, [1, 2, 3, 4]) → 2
/// - count(_ % 2, {1, 2, 3, 4}) → 2
/// - count(_ == "a", "ab") → 1
/// - count(_ % 2, 1..10) → 5  (Range support)
#[no_mangle]
pub extern "C" fn rt_count(predicate: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return 0
    let closure = match predicate.as_closure() {
        Some(c) => c,
        None => return Value::from_integer(0),
    };

    let mut count: i64 = 0;

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            if call_closure(closure, &[*v]).is_truthy() {
                count += 1;
            }
        }
        return Value::from_integer(count);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            if call_closure(closure, &[*v]).is_truthy() {
                count += 1;
            }
        }
        return Value::from_integer(count);
    }

    // Dict (predicate receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = closure.arity >= 2;
        for (k, v) in dict.iter() {
            let matches = if is_two_arg {
                call_closure(closure, &[*v, *k])
            } else {
                call_closure(closure, &[*v])
            };
            if matches.is_truthy() {
                count += 1;
            }
        }
        return Value::from_integer(count);
    }

    // String (each grapheme)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            if call_closure(closure, &[char_val]).is_truthy() {
                count += 1;
            }
        }
        return Value::from_integer(count);
    }

    // LazySequence (including Range, Map, Filter, etc.)
    if let Some(lazy) = collection.as_lazy_sequence() {
        return Value::from_integer(count_in_lazy(lazy, closure));
    }

    Value::from_integer(count)
}

/// Helper to count matching elements in any lazy sequence
/// Handles all lazy sequence variants including Map, Filter, and Iterate
fn count_in_lazy(lazy: &LazySequenceObject, predicate: &ClosureObject) -> i64 {
    // Safety limit to prevent infinite loops
    const MAX_ITERATIONS: usize = 10_000_000;
    let mut count: i64 = 0;

    match &lazy.kind {
        LazySeqKind::Repeat { value } => {
            // Repeat is infinite - count would be infinite if match
            // Just return 0 since we can't reasonably count infinite elements
            if call_closure(predicate, &[*value]).is_truthy() {
                // Would be infinite, return 0 as placeholder
            }
            0
        }

        LazySeqKind::Cycle { source, .. } => {
            if source.is_empty() {
                return 0;
            }
            // Count matches in one full cycle
            for val in source.iter() {
                if call_closure(predicate, &[*val]).is_truthy() {
                    count += 1;
                }
            }
            count
        }

        LazySeqKind::Range { current, end, inclusive, step } => {
            let mut cur = *current;
            for _ in 0..MAX_ITERATIONS {
                // Check if exhausted
                if let Some(end_val) = end {
                    let at_end = if *inclusive {
                        if *step > 0 { cur > *end_val } else { cur < *end_val }
                    } else if *step > 0 {
                        cur >= *end_val
                    } else {
                        cur <= *end_val
                    };
                    if at_end {
                        return count;
                    }
                } else {
                    // Unbounded range - can't count all elements
                    return count;
                }
                let val = Value::from_integer(cur);
                if call_closure(predicate, &[val]).is_truthy() {
                    count += 1;
                }
                cur += step;
            }
            count
        }

        LazySeqKind::Iterate { .. } => {
            // Iterate is potentially infinite, return 0
            0
        }

        LazySeqKind::Map { source, mapper } => {
            if let Some(map_closure) = mapper.as_closure() {
                let source_elements = collect_bounded_lazy(source);
                for val in source_elements {
                    let mapped = call_closure(map_closure, &[val]);
                    if call_closure(predicate, &[mapped]).is_truthy() {
                        count += 1;
                    }
                }
            }
            count
        }

        LazySeqKind::Filter { source, predicate: filter_pred } => {
            if let Some(filter_closure) = filter_pred.as_closure() {
                let source_elements = collect_bounded_lazy(source);
                for val in source_elements {
                    if call_closure(filter_closure, &[val]).is_truthy()
                        && call_closure(predicate, &[val]).is_truthy() {
                            count += 1;
                        }
                }
            }
            count
        }

        LazySeqKind::Skip { source, remaining } => {
            let source_elements = collect_bounded_lazy(source);
            for (i, val) in source_elements.into_iter().enumerate() {
                if i >= *remaining
                    && call_closure(predicate, &[val]).is_truthy() {
                        count += 1;
                    }
            }
            count
        }

        LazySeqKind::Combinations { source, size, indices, done } => {
            if *done || source.is_empty() || *size == 0 || *size > source.len() {
                return 0;
            }

            let mut current_indices = indices.clone();
            let n = source.len();

            for _ in 0..MAX_ITERATIONS {
                let combination: im::Vector<Value> = current_indices
                    .iter()
                    .map(|&i| source[i])
                    .collect();
                let val = Value::from_list(combination);

                if call_closure(predicate, &[val]).is_truthy() {
                    count += 1;
                }

                // Advance to next combination
                let mut i = *size - 1;
                while current_indices[i] == n - size + i {
                    if i == 0 {
                        return count; // All combinations exhausted
                    }
                    i -= 1;
                }
                current_indices[i] += 1;
                for j in (i + 1)..*size {
                    current_indices[j] = current_indices[j - 1] + 1;
                }
            }
            count
        }

        LazySeqKind::Zip { sources } => {
            if sources.is_empty() {
                return 0;
            }

            let source_vecs: Vec<im::Vector<Value>> = sources
                .iter()
                .map(collect_bounded_lazy)
                .collect();

            let min_len = source_vecs.iter().map(|v| v.len()).min().unwrap_or(0);

            for i in 0..min_len {
                let tuple: im::Vector<Value> = source_vecs
                    .iter()
                    .map(|v| v[i])
                    .collect();
                let val = Value::from_list(tuple);
                if call_closure(predicate, &[val]).is_truthy() {
                    count += 1;
                }
            }
            count
        }
    }
}

// ============================================================================
// §11.8 Aggregation Functions
// ============================================================================

/// `sum(collection)` → Integer | Decimal
///
/// Sum all numeric elements. Returns 0 for empty collections.
///
/// Per LANG.txt §11.8:
/// - sum([1, 2]) → 3
/// - sum([1.5, 2.5]) → 4.0
/// - sum([]) → 0
/// - sum(#{1: 2, 3: 4}) → 6 (sums values)
/// - sum(1..=100) → 5050 (O(1) using arithmetic sequence formula)
#[no_mangle]
pub extern "C" fn rt_sum(collection: Value) -> Value {
    let mut int_sum: i64 = 0;
    let mut dec_sum: f64 = 0.0;
    let mut has_decimal = false;

    // Helper to add a value to the sum
    let mut add_value = |v: Value| {
        if let Some(i) = v.as_integer() {
            int_sum += i;
        } else if let Some(d) = v.as_decimal() {
            dec_sum += d;
            has_decimal = true;
        }
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            add_value(*v);
        }
        return if has_decimal {
            Value::from_decimal(int_sum as f64 + dec_sum)
        } else {
            Value::from_integer(int_sum)
        };
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            add_value(*v);
        }
        return if has_decimal {
            Value::from_decimal(int_sum as f64 + dec_sum)
        } else {
            Value::from_integer(int_sum)
        };
    }

    // Dict (sums values)
    if let Some(dict) = collection.as_dict() {
        for v in dict.values() {
            add_value(*v);
        }
        return if has_decimal {
            Value::from_decimal(int_sum as f64 + dec_sum)
        } else {
            Value::from_integer(int_sum)
        };
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        // For Range, use arithmetic sequence sum formula: sum = n * (first + last) / 2
        if let LazySeqKind::Range { current, end: Some(end_val), inclusive, step } = &lazy.kind {
            let start = *current;
            let end = *end_val;
            let step = *step;

            // Calculate size
            let count = if step > 0 {
                if start > end || (start == end && !*inclusive) {
                    0
                } else if *inclusive {
                    ((end - start) / step) + 1
                } else {
                    ((end - start - 1) / step) + 1
                }
            } else if start < end || (start == end && !*inclusive) {
                0
            } else if *inclusive {
                ((start - end) / (-step)) + 1
            } else {
                ((start - end - 1) / (-step)) + 1
            };

            if count <= 0 {
                return Value::from_integer(0);
            }

            // Calculate last element
            let last = start + (count - 1) * step;

            // Sum using arithmetic sequence formula: sum = n * (first + last) / 2
            let sum = count * (start + last) / 2;
            return Value::from_integer(sum);
        }

        // For other lazy sequences, iterate
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            add_value(val);
            current = *next_seq;
        }
        return if has_decimal {
            Value::from_decimal(int_sum as f64 + dec_sum)
        } else {
            Value::from_integer(int_sum)
        };
    }

    Value::from_integer(0)
}

/// Helper: compare two values for ordering
/// Returns Some(Ordering) for comparable values, None for incomparable
fn compare_values(a: Value, b: Value) -> Option<std::cmp::Ordering> {

    // Both integers
    if let (Some(ai), Some(bi)) = (a.as_integer(), b.as_integer()) {
        return Some(ai.cmp(&bi));
    }

    // Both decimals
    if let (Some(ad), Some(bd)) = (a.as_decimal(), b.as_decimal()) {
        return ad.partial_cmp(&bd);
    }

    // Integer and decimal - compare as decimals
    if let (Some(ai), Some(bd)) = (a.as_integer(), b.as_decimal()) {
        return (ai as f64).partial_cmp(&bd);
    }
    if let (Some(ad), Some(bi)) = (a.as_decimal(), b.as_integer()) {
        return ad.partial_cmp(&(bi as f64));
    }

    // Both strings
    if let (Some(sa), Some(sb)) = (a.as_string(), b.as_string()) {
        return Some(sa.cmp(sb));
    }

    None
}

/// `max(collection)` → Value | Nil
///
/// Find the largest element. Returns nil for empty collections.
///
/// Per LANG.txt §11.8:
/// - max([1, 2]) → 2
/// - max([]) → nil
/// - max(#{1: 2, 3: 4}) → 4 (max of values)
/// - max(1..5) → 4 (O(1) for bounded ranges)
#[no_mangle]
pub extern "C" fn rt_max(collection: Value) -> Value {
    use std::cmp::Ordering;

    let mut max_val: Option<Value> = None;

    let mut update_max = |v: Value| {
        match max_val {
            None => max_val = Some(v),
            Some(current) => {
                if let Some(Ordering::Greater) = compare_values(v, current) {
                    max_val = Some(v);
                }
            }
        }
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            update_max(*v);
        }
        return max_val.unwrap_or_else(Value::nil);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            update_max(*v);
        }
        return max_val.unwrap_or_else(Value::nil);
    }

    // Dict (max of values)
    if let Some(dict) = collection.as_dict() {
        for v in dict.values() {
            update_max(*v);
        }
        return max_val.unwrap_or_else(Value::nil);
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        // For Range, max is first (descending) or last (ascending)
        if let LazySeqKind::Range { current, end: Some(end_val), inclusive, step } = &lazy.kind {
            let start = *current;
            let end = *end_val;
            let step = *step;

            // Check if empty
            let is_empty = if step > 0 {
                start > end || (start == end && !*inclusive)
            } else {
                start < end || (start == end && !*inclusive)
            };

            if is_empty {
                return Value::nil();
            }

            // For ascending, max is last; for descending, max is first
            if step > 0 {
                // Calculate last element
                let count = if *inclusive {
                    ((end - start) / step) + 1
                } else {
                    ((end - start - 1) / step) + 1
                };
                let last = start + (count - 1) * step;
                return Value::from_integer(last);
            } else {
                // Descending: max is first
                return Value::from_integer(start);
            }
        }

        // For other lazy sequences, iterate
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            update_max(val);
            current = *next_seq;
        }
        return max_val.unwrap_or_else(Value::nil);
    }

    Value::nil()
}

/// `min(collection)` → Value | Nil
///
/// Find the smallest element. Returns nil for empty collections.
///
/// Per LANG.txt §11.8:
/// - min([1, 2]) → 1
/// - min([]) → nil
/// - min(#{1: 2, 3: 4}) → 2 (min of values)
/// - min(1..5) → 1 (O(1) for bounded ranges)
#[no_mangle]
pub extern "C" fn rt_min(collection: Value) -> Value {
    use std::cmp::Ordering;

    let mut min_val: Option<Value> = None;

    let mut update_min = |v: Value| {
        match min_val {
            None => min_val = Some(v),
            Some(current) => {
                if let Some(Ordering::Less) = compare_values(v, current) {
                    min_val = Some(v);
                }
            }
        }
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            update_min(*v);
        }
        return min_val.unwrap_or_else(Value::nil);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            update_min(*v);
        }
        return min_val.unwrap_or_else(Value::nil);
    }

    // Dict (min of values)
    if let Some(dict) = collection.as_dict() {
        for v in dict.values() {
            update_min(*v);
        }
        return min_val.unwrap_or_else(Value::nil);
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        // For Range, min is first (ascending) or last (descending)
        if let LazySeqKind::Range { current, end: Some(end_val), inclusive, step } = &lazy.kind {
            let start = *current;
            let end = *end_val;
            let step = *step;

            // Check if empty
            let is_empty = if step > 0 {
                start > end || (start == end && !*inclusive)
            } else {
                start < end || (start == end && !*inclusive)
            };

            if is_empty {
                return Value::nil();
            }

            // For ascending, min is first; for descending, min is last
            if step > 0 {
                // Ascending: min is first
                return Value::from_integer(start);
            } else {
                // Calculate last element
                let count = if *inclusive {
                    ((start - end) / (-step)) + 1
                } else {
                    ((start - end - 1) / (-step)) + 1
                };
                let last = start + (count - 1) * step;
                return Value::from_integer(last);
            }
        }

        // For other lazy sequences, iterate
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            update_min(val);
            current = *next_seq;
        }
        return min_val.unwrap_or_else(Value::nil);
    }

    Value::nil()
}

// ============================================================================
// §11.9 Sequence Manipulation
// ============================================================================

/// `skip(total, collection)` → Collection
///
/// Skip n elements from the collection.
///
/// Per LANG.txt §11.9:
/// - skip(1, [1, 2, 3]) → [2, 3]
/// - skip(1, {1, 2, 3}) → {2, 3}
/// - skip(2, 1..5) → LazySequence(3..5)
#[no_mangle]
pub extern "C" fn rt_skip(total: Value, collection: Value) -> Value {
    let n = total.as_integer().unwrap_or(0) as usize;

    // List
    if let Some(list) = collection.as_list() {
        let result: im::Vector<Value> = list.iter().skip(n).copied().collect();
        return Value::from_list(result);
    }

    // Set
    if let Some(set) = collection.as_set() {
        let result: im::HashSet<Value> = set.iter().skip(n).copied().collect();
        return Value::from_set(result);
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        use crate::heap::{LazySeqKind, LazySequenceObject};
        // For Range, adjust the start position
        if let LazySeqKind::Range { current, end, inclusive, step } = &lazy.kind {
            let new_start = current + (n as i64) * step;
            return Value::from_lazy_sequence(LazySequenceObject::range(
                new_start,
                *end,
                *inclusive,
                *step,
            ));
        }

        // For other lazy sequences, use Skip wrapper
        return Value::from_lazy_sequence(LazySequenceObject::new(LazySeqKind::Skip {
            source: Box::new(lazy.clone()),
            remaining: n,
        }));
    }

    collection
}

/// `take(total, collection)` → List
///
/// Take n elements from the collection. Returns List.
///
/// Per LANG.txt §11.9:
/// - take(2, [1, 2, 3]) → [1, 2]
/// - take(2, {1, 2, 3}) → [1, 2]
/// - take(2, 1..5) → [1, 2]
#[no_mangle]
pub extern "C" fn rt_take(total: Value, collection: Value) -> Value {
    let n = total.as_integer().unwrap_or(0) as usize;

    // List
    if let Some(list) = collection.as_list() {
        let result: im::Vector<Value> = list.iter().take(n).copied().collect();
        return Value::from_list(result);
    }

    // Set (returns List per spec)
    if let Some(set) = collection.as_set() {
        let result: im::Vector<Value> = set.iter().take(n).copied().collect();
        return Value::from_list(result);
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let result = take_from_lazy_full(n, lazy);
        return Value::from_list(result);
    }

    Value::from_list(im::Vector::new())
}

/// `sort(comparator, collection)` → List
///
/// Sort by comparator function. Comparator can return boolean (false = a < b)
/// or integer (negative = a < b, 0 = equal, positive = a > b).
///
/// Per LANG.txt §11.9:
/// - sort(<, [3, 2, 1]) → [1, 2, 3]
/// - sort(>, [3, 2, 1]) → [3, 2, 1]
/// - sort(-, [3, 2, 1]) → [1, 2, 3]
/// - sort(>, 1..5) → [4, 3, 2, 1]
#[no_mangle]
pub extern "C" fn rt_sort(comparator: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return the collection unchanged
    let closure = match comparator.as_closure() {
        Some(c) => c,
        None => return collection,
    };

    // Helper to sort items
    let sort_items = |items: &mut Vec<Value>| {
        items.sort_by(|a, b| {
            let result = call_closure(closure, &[*a, *b]);

            // Check if result is boolean
            if let Some(bool_val) = result.as_bool() {
                // Per LANG.txt: comparator(a, b) returns true means "a comes before b"
                // For sort(<, ..): a < b returns true, so a should come first (Less)
                // For sort(>, ..): a > b returns true, so a should come first (Less)
                if bool_val {
                    std::cmp::Ordering::Less
                } else {
                    std::cmp::Ordering::Greater
                }
            }
            // Check if result is integer
            else if let Some(int_val) = result.as_integer() {
                int_val.cmp(&0)
            }
            // Default to equal
            else {
                std::cmp::Ordering::Equal
            }
        });
    };

    // List
    if let Some(list) = collection.as_list() {
        let mut items: Vec<Value> = list.iter().copied().collect();
        sort_items(&mut items);
        return Value::from_list(items.into_iter().collect());
    }

    // LazySequence (including Range) - collect and sort
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut items: Vec<Value> = Vec::new();
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            items.push(val);
            current = *next_seq;
        }
        sort_items(&mut items);
        return Value::from_list(items.into_iter().collect());
    }

    collection
}

/// `reverse(collection)` → Collection
///
/// Reverse the order of elements.
///
/// Per LANG.txt §11.9:
/// - reverse([1, 2, 3]) → [3, 2, 1]
/// - reverse("abc") → "cba"
/// - reverse(1..5) → [4, 3, 2, 1]
#[no_mangle]
pub extern "C" fn rt_reverse(collection: Value) -> Value {
    // List
    if let Some(list) = collection.as_list() {
        let result: im::Vector<Value> = list.iter().rev().copied().collect();
        return Value::from_list(result);
    }

    // String
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        let reversed: String = s.graphemes(true).rev().collect();
        return Value::from_string(reversed);
    }

    // LazySequence (including Range) - collect and reverse for bounded sequences
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut elements: Vec<Value> = Vec::new();
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            elements.push(val);
            current = *next_seq;
        }
        elements.reverse();
        return Value::from_list(elements.into_iter().collect());
    }

    collection
}

/// `rotate(steps, collection)` → List
///
/// Rotate list by n steps.
/// Positive = forward (last moves to start)
/// Negative = backward (first moves to end)
///
/// Per LANG.txt §11.9:
/// - rotate(1, [1, 2, 3]) → [3, 1, 2]
/// - rotate(-1, [1, 2, 3]) → [2, 3, 1]
#[no_mangle]
pub extern "C" fn rt_rotate(steps: Value, collection: Value) -> Value {
    let n = steps.as_integer().unwrap_or(0);

    // List
    if let Some(list) = collection.as_list() {
        let len = list.len();
        if len == 0 {
            return collection;
        }

        // Normalize the rotation amount
        // Positive rotation: move last n elements to front
        // Negative rotation: move first |n| elements to end
        let rotate_by = if n >= 0 {
            (n as usize) % len
        } else {
            len - ((-n) as usize % len)
        };

        if rotate_by == 0 {
            return collection;
        }

        // Split the list and swap
        let split_at = len - rotate_by;
        let (front, back) = list.clone().split_at(split_at);
        let mut result = im::Vector::new();
        result.append(back);
        result.append(front);

        return Value::from_list(result);
    }

    collection
}

/// `chunk(size, collection)` → List[List]
///
/// Split into chunks of given size. Last chunk may be smaller.
///
/// Per LANG.txt §11.9:
/// - chunk(2, [1, 2, 3]) → [[1, 2], [3]]
/// - chunk(2, [1, 2, 3, 4]) → [[1, 2], [3, 4]]
#[no_mangle]
pub extern "C" fn rt_chunk(size: Value, collection: Value) -> Value {
    let chunk_size = size.as_integer().unwrap_or(1) as usize;
    if chunk_size == 0 {
        return Value::from_list(im::Vector::new());
    }

    // List
    if let Some(list) = collection.as_list() {
        let mut chunks: im::Vector<Value> = im::Vector::new();
        let mut current_chunk: im::Vector<Value> = im::Vector::new();

        for v in list.iter() {
            current_chunk.push_back(*v);
            if current_chunk.len() == chunk_size {
                chunks.push_back(Value::from_list(current_chunk));
                current_chunk = im::Vector::new();
            }
        }

        // Don't forget the last partial chunk
        if !current_chunk.is_empty() {
            chunks.push_back(Value::from_list(current_chunk));
        }

        return Value::from_list(chunks);
    }

    Value::from_list(im::Vector::new())
}

// ============================================================================
// §11.10 Set Operations
// ============================================================================

/// Helper: extract elements from a collection as an iterator
/// Per LANG.txt §11.10, supports List, Set, Range, String
fn collect_elements(v: Value) -> Vec<Value> {
    if let Some(list) = v.as_list() {
        return list.iter().copied().collect();
    }
    if let Some(set) = v.as_set() {
        return set.iter().copied().collect();
    }
    // Range (LazySequence) - iterate to collect bounded range elements
    if let Some(lazy) = v.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        // Only collect bounded ranges (unbounded would be infinite)
        if let LazySeqKind::Range { end: Some(_), .. } = &lazy.kind {
            let mut result = Vec::new();
            let mut current = lazy.clone();
            while let Some((val, next_seq)) = current.next() {
                result.push(val);
                current = *next_seq;
            }
            return result;
        }
    }
    // String - split into grapheme clusters
    if let Some(s) = v.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        return s.graphemes(true).map(|g| Value::from_string(g.to_string())).collect();
    }
    vec![]
}

/// `union(collection1, collection2)` → Set
///
/// Elements found in any of the collections.
///
/// Per LANG.txt §11.10:
/// - union({1, 2}, {2, 3}) → {1, 2, 3}
#[no_mangle]
pub extern "C" fn rt_union(collection1: Value, collection2: Value) -> Value {
    let mut result: im::HashSet<Value> = im::HashSet::new();

    for v in collect_elements(collection1) {
        result.insert(v);
    }
    for v in collect_elements(collection2) {
        result.insert(v);
    }

    Value::from_set(result)
}

/// `intersection(collection1, collection2)` → Set
///
/// Elements found in all collections.
///
/// Per LANG.txt §11.10:
/// - intersection({1, 2}, {2, 3}) → {2}
#[no_mangle]
pub extern "C" fn rt_intersection(collection1: Value, collection2: Value) -> Value {
    let set1: im::HashSet<Value> = collect_elements(collection1).into_iter().collect();
    let set2: im::HashSet<Value> = collect_elements(collection2).into_iter().collect();

    // Find common elements
    let result: im::HashSet<Value> = set1.iter()
        .filter(|v| set2.contains(*v))
        .copied()
        .collect();

    Value::from_set(result)
}

// ============================================================================
// §11.11 Predicates
// ============================================================================

/// `includes?(collection, value)` → Boolean
///
/// Check if value is present in collection.
/// For Dictionary, checks if value is a key.
///
/// Per LANG.txt §11.11:
/// - includes?([1, 2], 1) → true
/// - includes?({1, 2}, 1) → true
/// - includes?(#{"a": 1}, "a") → true
/// - includes?("ab", "a") → true
/// - includes?(1..10, 5) → true  (Range support with O(1) optimization)
#[no_mangle]
pub extern "C" fn rt_includes(collection: Value, value: Value) -> Value {
    // List
    if let Some(list) = collection.as_list() {
        let found = list.iter().any(|v| *v == value);
        return Value::from_bool(found);
    }

    // Set
    if let Some(set) = collection.as_set() {
        return Value::from_bool(set.contains(&value));
    }

    // Dict (checks keys)
    if let Some(dict) = collection.as_dict() {
        return Value::from_bool(dict.contains_key(&value));
    }

    // String (checks if substring exists)
    if let (Some(haystack), Some(needle)) = (collection.as_string(), value.as_string()) {
        return Value::from_bool(haystack.contains(needle));
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        // O(1) for bounded Range: check if value is within bounds and matches step
        if let LazySeqKind::Range { current, end: Some(end_val), inclusive, step } = &lazy.kind {
            if let Some(val_int) = value.as_integer() {
                // Check bounds
                let in_bounds = if *inclusive {
                    if *step > 0 {
                        val_int >= *current && val_int <= *end_val
                    } else {
                        val_int <= *current && val_int >= *end_val
                    }
                } else if *step > 0 {
                    val_int >= *current && val_int < *end_val
                } else {
                    val_int <= *current && val_int > *end_val
                };
                // Check that value aligns with step
                let aligned = (val_int - current) % step == 0;
                return Value::from_bool(in_bounds && aligned);
            }
        }
        // For other lazy sequences, iterate
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            if val == value {
                return Value::from_bool(true);
            }
            current = *next_seq;
        }
        return Value::from_bool(false);
    }

    Value::from_bool(false)
}

/// `excludes?(collection, value)` → Boolean
///
/// Check if value is NOT present in collection.
///
/// Per LANG.txt §11.11:
/// - excludes?([1, 2], 3) → true
#[no_mangle]
pub extern "C" fn rt_excludes(collection: Value, value: Value) -> Value {
    let includes = rt_includes(collection, value);
    if let Some(b) = includes.as_bool() {
        Value::from_bool(!b)
    } else {
        Value::from_bool(true)
    }
}

/// `any?(predicate, collection)` → Boolean
///
/// Check if any element matches predicate.
///
/// Per LANG.txt §11.11:
/// - any?(_ == 1, [1, 2]) → true
/// - any?(_ == 1, [2, 3]) → false
/// - any?(_ % 2 == 0, 1..5) → true  (Range support)
#[no_mangle]
pub extern "C" fn rt_any(predicate: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return false
    let closure = match predicate.as_closure() {
        Some(c) => c,
        None => return Value::from_bool(false),
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            if call_closure(closure, &[*v]).is_truthy() {
                return Value::from_bool(true);
            }
        }
        return Value::from_bool(false);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            if call_closure(closure, &[*v]).is_truthy() {
                return Value::from_bool(true);
            }
        }
        return Value::from_bool(false);
    }

    // String
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            if call_closure(closure, &[char_val]).is_truthy() {
                return Value::from_bool(true);
            }
        }
        return Value::from_bool(false);
    }

    // LazySequence (including Range)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current = lazy.clone();
        while let Some((val, next_seq)) = current.next() {
            if call_closure(closure, &[val]).is_truthy() {
                return Value::from_bool(true);
            }
            current = *next_seq;
        }
        return Value::from_bool(false);
    }

    Value::from_bool(false)
}

/// `all?(predicate, collection)` → Boolean
///
/// Check if all elements match predicate.
///
/// Per LANG.txt §11.11:
/// - all?(_ > 0, [1, 2]) → true
/// - all?(_ > 0, [-1, 2]) → false
/// - all?(_ > 0, []) → true (vacuous truth)
/// - all?(_ > 0, 1..5) → true  (bounded Range support)
#[no_mangle]
pub extern "C" fn rt_all(predicate: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return true (vacuous)
    let closure = match predicate.as_closure() {
        Some(c) => c,
        None => return Value::from_bool(true),
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            if !call_closure(closure, &[*v]).is_truthy() {
                return Value::from_bool(false);
            }
        }
        return Value::from_bool(true);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            if !call_closure(closure, &[*v]).is_truthy() {
                return Value::from_bool(false);
            }
        }
        return Value::from_bool(true);
    }

    // String
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            if !call_closure(closure, &[char_val]).is_truthy() {
                return Value::from_bool(false);
            }
        }
        return Value::from_bool(true);
    }

    // Range (bounded only, per spec)
    if let Some(lazy) = collection.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        if let LazySeqKind::Range { end: Some(_), .. } = &lazy.kind {
            // Bounded range - iterate and check
            let mut current = lazy.clone();
            while let Some((val, next_seq)) = current.next() {
                if !call_closure(closure, &[val]).is_truthy() {
                    return Value::from_bool(false);
                }
                current = *next_seq;
            }
            return Value::from_bool(true);
        }
        // Unbounded lazy sequences not supported per spec
    }

    Value::from_bool(true)
}

// ============================================================================
// §11.6 Iteration
// ============================================================================

/// `each(side_effect, collection)` → Nil
///
/// Apply a side-effecting function to each element. Always returns nil.
///
/// Per LANG.txt §11.6:
/// - each(|v| acc = acc + v, [1, 2]) then acc is 3
#[no_mangle]
pub extern "C" fn rt_each(side_effect: Value, collection: Value) -> Value {
    // Get the closure - if not a closure, return nil
    let closure = match side_effect.as_closure() {
        Some(c) => c,
        None => return Value::nil(),
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            call_closure(closure, &[*v]);
        }
        return Value::nil();
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            call_closure(closure, &[*v]);
        }
        return Value::nil();
    }

    // Dict (callback receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = closure.arity >= 2;
        for (k, v) in dict.iter() {
            if is_two_arg {
                call_closure(closure, &[*v, *k]);
            } else {
                call_closure(closure, &[*v]);
            }
        }
        return Value::nil();
    }

    // String (each grapheme)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            call_closure(closure, &[char_val]);
        }
        return Value::nil();
    }

    // LazySequence (including Ranges) - iterate through the sequence
    // WARNING: Unbounded sequences will loop forever
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current = lazy.clone();
        while let Some((val, next_lazy)) = current.next() {
            call_closure(closure, &[val]);
            current = *next_lazy;
        }
        return Value::nil();
    }

    Value::nil()
}

// ============================================================================
// §11.12-11.13 Lazy Sequence Functions
// ============================================================================

/// `repeat(value)` → LazySequence
///
/// Generate a lazy sequence that repeats value indefinitely.
///
/// Per LANG.txt §11.12:
/// - repeat(1) |> take(3) → [1, 1, 1]
/// - repeat("x") |> take(3) → ["x", "x", "x"]
#[no_mangle]
pub extern "C" fn rt_repeat(value: Value) -> Value {
    let lazy = LazySequenceObject::repeat(value);
    Value::from_lazy_sequence(lazy)
}

/// `cycle(collection)` → LazySequence
///
/// Generate a lazy sequence that cycles through elements indefinitely.
///
/// Per LANG.txt §11.12:
/// - cycle([1, 2, 3]) |> take(7) → [1, 2, 3, 1, 2, 3, 1]
#[no_mangle]
pub extern "C" fn rt_cycle(collection: Value) -> Value {
    // Get elements from collection as a Vector
    let source = if let Some(list) = collection.as_list() {
        list.clone()
    } else if let Some(set) = collection.as_set() {
        set.iter().copied().collect()
    } else if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        s.graphemes(true)
            .map(|g| Value::from_string(g.to_string()))
            .collect()
    } else {
        // Return empty lazy sequence
        return Value::from_lazy_sequence(LazySequenceObject::cycle(im::Vector::new()));
    };

    let lazy = LazySequenceObject::cycle(source);
    Value::from_lazy_sequence(lazy)
}

/// `iterate(generator, initial)` → LazySequence
///
/// Generate a lazy sequence by repeatedly applying generator function to previous result.
///
/// Per LANG.txt §11.12:
/// - iterate(_ + 1, 0) |> take(5) → [0, 1, 2, 3, 4]
/// - iterate(_ * 2, 1) |> take(5) → [1, 2, 4, 8, 16]
#[no_mangle]
pub extern "C" fn rt_iterate(generator: Value, initial: Value) -> Value {
    let lazy = LazySequenceObject::iterate(generator, initial);
    Value::from_lazy_sequence(lazy)
}

/// `combinations(size, collection)` → LazySequence
///
/// Generate all combinations of given size from collection.
///
/// Per LANG.txt §11.12:
/// - combinations(2, [1, 2, 3]) |> list → [[1, 2], [1, 3], [2, 3]]
#[no_mangle]
pub extern "C" fn rt_combinations(size: Value, collection: Value) -> Value {
    let k = size.as_integer().unwrap_or(0) as usize;

    // Get elements from collection
    let source: Vec<Value> = if let Some(list) = collection.as_list() {
        list.iter().copied().collect()
    } else if let Some(set) = collection.as_set() {
        set.iter().copied().collect()
    } else {
        return Value::from_lazy_sequence(LazySequenceObject::new(
            LazySeqKind::Combinations {
                source: vec![],
                size: k,
                indices: vec![],
                done: true,
            },
        ));
    };

    if k == 0 || k > source.len() {
        return Value::from_lazy_sequence(LazySequenceObject::new(
            LazySeqKind::Combinations {
                source,
                size: k,
                indices: vec![],
                done: true,
            },
        ));
    }

    // Initialize indices for first combination
    let indices: Vec<usize> = (0..k).collect();

    Value::from_lazy_sequence(LazySequenceObject::new(
        LazySeqKind::Combinations {
            source,
            size: k,
            indices,
            done: false,
        },
    ))
}

/// `range(from, to, step)` → LazySequence
///
/// Generate a range sequence with custom step.
/// Unlike `..` and `..=` syntax, this always returns a LazySequence.
///
/// Per LANG.txt §11.12:
/// - range(0, 10, 2) |> take(3) → [0, 2, 4]
#[no_mangle]
pub extern "C" fn rt_range_fn(from: Value, to: Value, step: Value) -> Value {
    let start = from.as_integer().unwrap_or(0);
    let end = to.as_integer();
    let step_val = step.as_integer().unwrap_or(1);

    let lazy = LazySequenceObject::range(start, end, false, step_val);
    Value::from_lazy_sequence(lazy)
}

/// `zip(collection, ..collections)` → List | LazySequence
///
/// Aggregate multiple collections into tuples. Stops when shortest collection is exhausted.
///
/// Per LANG.txt §11.12:
/// - If ANY collection has finite size → returns List
/// - If ALL collections are infinite (unbounded ranges or lazy sequences) → returns LazySequence
///
/// Examples:
/// - zip([1, 2, 3], ["a", "b", "c"]) → [[1, "a"], [2, "b"], [3, "c"]]
/// - zip(0.., 1..) |> take(3) → [[0, 1], [1, 2], [2, 3]]
///
/// # Safety
/// - argc must be the correct number of elements pointed to by argv
/// - argv must point to valid Value array or be null if argc is 0
#[no_mangle]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn rt_zip(argc: u32, argv: *const Value) -> Value {
    if argc == 0 || argv.is_null() {
        return Value::from_list(im::Vector::new());
    }

    let args = unsafe { std::slice::from_raw_parts(argv, argc as usize) };

    // Check if all collections are infinite lazy sequences
    let all_infinite = args.iter().all(is_infinite_lazy_sequence);

    if all_infinite {
        // All infinite → return LazySequence
        let sources: Vec<LazySequenceObject> = args
            .iter()
            .filter_map(|v| v.as_lazy_sequence().cloned())
            .collect();

        return Value::from_lazy_sequence(LazySequenceObject::new(LazySeqKind::Zip { sources }));
    }

    // At least one finite collection → evaluate immediately
    // First pass: find minimum finite length
    let min_finite_len = args
        .iter()
        .filter_map(get_finite_length)
        .min()
        .unwrap_or(0);

    // Second pass: convert each collection to a vector of elements, taking at most min_finite_len
    let collections: Vec<im::Vector<Value>> = args
        .iter()
        .map(|v| collection_to_vector(*v, min_finite_len))
        .collect();

    // Build result list of tuples
    let mut result = im::Vector::new();
    for i in 0..min_finite_len {
        let tuple: im::Vector<Value> = collections
            .iter()
            .map(|c| c.get(i).copied().unwrap_or_else(Value::nil))
            .collect();
        result.push_back(Value::from_list(tuple));
    }

    Value::from_list(result)
}

/// Check if a value is an infinite lazy sequence (unbounded range or non-Range lazy)
fn is_infinite_lazy_sequence(v: &Value) -> bool {
    if let Some(lazy) = v.as_lazy_sequence() {
        match &lazy.kind {
            // Unbounded range (no end)
            LazySeqKind::Range { end: None, .. } => true,
            // Repeat and Cycle are infinite
            LazySeqKind::Repeat { .. } => true,
            LazySeqKind::Cycle { .. } => true,
            // Iterate is infinite
            LazySeqKind::Iterate { .. } => true,
            // Map/Filter of infinite source is infinite
            LazySeqKind::Map { source, .. } | LazySeqKind::Filter { source, .. } => {
                is_infinite_lazy_sequence(&Value::from_lazy_sequence(source.clone()))
            }
            // Zip of all infinite sources is infinite
            LazySeqKind::Zip { sources } => sources
                .iter()
                .all(|s| is_infinite_lazy_sequence(&Value::from_lazy_sequence(Box::new(s.clone())))),
            // Bounded range has an end
            LazySeqKind::Range { end: Some(_), .. } => false,
            // Skip preserves finiteness of source
            LazySeqKind::Skip { source, .. } => {
                is_infinite_lazy_sequence(&Value::from_lazy_sequence(source.clone()))
            }
            // Combinations is always finite
            LazySeqKind::Combinations { .. } => false,
        }
    } else {
        false
    }
}

/// Get the finite length of a collection, or None if infinite
fn get_finite_length(v: &Value) -> Option<usize> {
    if let Some(list) = v.as_list() {
        Some(list.len())
    } else if let Some(set) = v.as_set() {
        Some(set.len())
    } else if let Some(s) = v.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        Some(s.graphemes(true).count())
    } else if let Some(lazy) = v.as_lazy_sequence() {
        get_lazy_finite_length(lazy)
    } else {
        Some(0)
    }
}

/// Get the finite length of a lazy sequence, or None if infinite
fn get_lazy_finite_length(lazy: &LazySequenceObject) -> Option<usize> {
    match &lazy.kind {
        LazySeqKind::Range { current, end, inclusive, step } => {
            if let Some(end_val) = end {
                // Calculate range length
                let diff = end_val - current;
                if *step == 0 {
                    return Some(0);
                }
                let len = if *inclusive {
                    (diff / step) + 1
                } else {
                    diff / step
                };
                Some(len.max(0) as usize)
            } else {
                None // Unbounded
            }
        }
        LazySeqKind::Repeat { .. } => None,
        LazySeqKind::Cycle { .. } => None,
        LazySeqKind::Iterate { .. } => None,
        LazySeqKind::Map { source, .. } | LazySeqKind::Filter { source, .. } => {
            get_lazy_finite_length(source)
        }
        LazySeqKind::Skip { source, remaining } => {
            get_lazy_finite_length(source).map(|len| len.saturating_sub(*remaining))
        }
        LazySeqKind::Combinations { source, size, .. } => {
            // n choose k
            if *size > source.len() {
                Some(0)
            } else {
                Some(binomial(source.len(), *size))
            }
        }
        LazySeqKind::Zip { sources } => {
            // Zip length is min of all source lengths
            sources
                .iter()
                .map(get_lazy_finite_length)
                .try_fold(usize::MAX, |min, len| len.map(|l| min.min(l)))
        }
    }
}

/// Calculate binomial coefficient (n choose k)
fn binomial(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    let mut result = 1;
    for i in 0..k {
        result = result * (n - i) / (i + 1);
    }
    result
}

/// Convert any collection value to a vector of elements (up to max_len)
fn collection_to_vector(v: Value, max_len: usize) -> im::Vector<Value> {
    if let Some(list) = v.as_list() {
        list.iter().take(max_len).copied().collect()
    } else if let Some(set) = v.as_set() {
        set.iter().take(max_len).copied().collect()
    } else if let Some(s) = v.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        s.graphemes(true)
            .take(max_len)
            .map(|g| Value::from_string(g.to_string()))
            .collect()
    } else if let Some(lazy) = v.as_lazy_sequence() {
        take_from_lazy_full(max_len, lazy)
    } else {
        im::Vector::new()
    }
}

/// Collect all elements from a bounded lazy sequence.
/// For unbounded sequences, this will loop forever - caller must ensure sequence is bounded.
/// Handles all lazy sequence variants including Map, Filter, and Iterate.
fn collect_bounded_lazy(lazy: &LazySequenceObject) -> im::Vector<Value> {
    let mut result: im::Vector<Value> = im::Vector::new();
    collect_bounded_lazy_recursive(&mut result, lazy);
    result
}

/// Recursively collect all elements from a bounded lazy sequence
fn collect_bounded_lazy_recursive(
    result: &mut im::Vector<Value>,
    lazy: &LazySequenceObject,
) {
    // Safety limit to prevent infinite loops (for unbounded sequences called incorrectly)
    const MAX_ELEMENTS: usize = 10_000_000;

    match &lazy.kind {
        LazySeqKind::Repeat { .. } | LazySeqKind::Cycle { .. } => {
            // These are infinite - cannot collect all elements
            // Return empty (caller should use take instead)
        }

        LazySeqKind::Iterate { generator, current } => {
            // Iterate is potentially infinite, but we'll try to collect with a limit
            // In practice, users should use take() for iterate sequences
            if let Some(gen_closure) = generator.as_closure() {
                let mut cur = *current;
                for _ in 0..MAX_ELEMENTS {
                    result.push_back(cur);
                    cur = call_closure(gen_closure, &[cur]);
                }
            }
        }

        LazySeqKind::Range { current, end, inclusive, step } => {
            if end.is_none() {
                // Unbounded range - cannot collect all elements
                return;
            }
            let mut cur = *current;
            for _ in 0..MAX_ELEMENTS {
                // Check if exhausted
                if let Some(end_val) = end {
                    let at_end = if *inclusive {
                        if *step > 0 { cur > *end_val } else { cur < *end_val }
                    } else if *step > 0 {
                        cur >= *end_val
                    } else {
                        cur <= *end_val
                    };
                    if at_end {
                        return;
                    }
                }
                result.push_back(Value::from_integer(cur));
                cur += step;
            }
        }

        LazySeqKind::Map { source, mapper } => {
            if let Some(map_closure) = mapper.as_closure() {
                // First collect all source elements
                let source_elements = collect_bounded_lazy(source);
                for val in source_elements {
                    let mapped = call_closure(map_closure, &[val]);
                    result.push_back(mapped);
                }
            }
        }

        LazySeqKind::Filter { source, predicate } => {
            if let Some(pred_closure) = predicate.as_closure() {
                // First collect all source elements
                let source_elements = collect_bounded_lazy(source);
                for val in source_elements {
                    if call_closure(pred_closure, &[val]).is_truthy() {
                        result.push_back(val);
                    }
                }
            }
        }

        LazySeqKind::Skip { source, remaining } => {
            let source_elements = collect_bounded_lazy(source);
            for (i, val) in source_elements.into_iter().enumerate() {
                if i >= *remaining {
                    result.push_back(val);
                }
            }
        }

        LazySeqKind::Combinations { source, size, indices, done } => {
            if *done || source.is_empty() || *size == 0 || *size > source.len() {
                return;
            }

            let mut current_indices = indices.clone();
            let n = source.len();

            for _ in 0..MAX_ELEMENTS {
                // Get current combination
                let combination: im::Vector<Value> = current_indices
                    .iter()
                    .map(|&i| source[i])
                    .collect();
                result.push_back(Value::from_list(combination));

                // Advance to next combination
                let mut i = *size - 1;

                // Find the rightmost index that can be incremented
                while current_indices[i] == n - size + i {
                    if i == 0 {
                        return; // All combinations exhausted
                    }
                    i -= 1;
                }

                // Increment this index and reset all subsequent indices
                current_indices[i] += 1;
                for j in (i + 1)..*size {
                    current_indices[j] = current_indices[j - 1] + 1;
                }
            }
        }

        LazySeqKind::Zip { sources } => {
            // For zip, we need to collect from all sources and zip them
            // This is complex - for now, collect what we can
            if sources.is_empty() {
                return;
            }

            // Collect all sources
            let source_vecs: Vec<im::Vector<Value>> = sources
                .iter()
                .map(collect_bounded_lazy)
                .collect();

            // Find minimum length
            let min_len = source_vecs.iter().map(|v| v.len()).min().unwrap_or(0);

            for i in 0..min_len {
                let tuple: im::Vector<Value> = source_vecs
                    .iter()
                    .map(|v| v[i])
                    .collect();
                result.push_back(Value::from_list(tuple));
            }
        }
    }
}

/// Fully featured helper function to take n elements from any lazy sequence
/// Handles all lazy sequence variants including Map, Filter, and Iterate
fn take_from_lazy_full(n: usize, lazy: &LazySequenceObject) -> im::Vector<Value> {
    let mut result: im::Vector<Value> = im::Vector::new();
    let mut remaining = n;

    // We need to recursively evaluate the lazy sequence
    take_from_lazy_recursive(&mut result, &mut remaining, lazy);

    result
}

/// Recursively take elements from a lazy sequence
fn take_from_lazy_recursive(
    result: &mut im::Vector<Value>,
    remaining: &mut usize,
    lazy: &LazySequenceObject,
) {
    if *remaining == 0 {
        return;
    }

    match &lazy.kind {
        LazySeqKind::Repeat { value } => {
            while *remaining > 0 {
                result.push_back(*value);
                *remaining -= 1;
            }
        }

        LazySeqKind::Cycle { source, index } => {
            if source.is_empty() {
                return;
            }
            let mut idx = *index;
            while *remaining > 0 {
                result.push_back(source[idx]);
                *remaining -= 1;
                idx = (idx + 1) % source.len();
            }
        }

        LazySeqKind::Range { current, end, inclusive, step } => {
            let mut cur = *current;
            while *remaining > 0 {
                // Check if exhausted
                if let Some(end_val) = end {
                    let at_end = if *inclusive {
                        if *step > 0 { cur > *end_val } else { cur < *end_val }
                    } else if *step > 0 {
                        cur >= *end_val
                    } else {
                        cur <= *end_val
                    };
                    if at_end {
                        return;
                    }
                }
                result.push_back(Value::from_integer(cur));
                *remaining -= 1;
                cur += step;
            }
        }

        LazySeqKind::Iterate { generator, current } => {
            if let Some(gen_closure) = generator.as_closure() {
                let mut cur = *current;
                while *remaining > 0 {
                    result.push_back(cur);
                    *remaining -= 1;
                    cur = call_closure(gen_closure, &[cur]);
                }
            }
        }

        LazySeqKind::Map { source, mapper } => {
            if let Some(map_closure) = mapper.as_closure() {
                // Collect source elements and map them
                let source_elements = take_from_lazy_full(*remaining, source);
                for val in source_elements {
                    if *remaining == 0 {
                        break;
                    }
                    let mapped = call_closure(map_closure, &[val]);
                    result.push_back(mapped);
                    *remaining -= 1;
                }
            }
        }

        LazySeqKind::Filter { source, predicate } => {
            if let Some(pred_closure) = predicate.as_closure() {
                // We need to potentially fetch more elements than remaining
                // because some might be filtered out
                // Use a reasonable batch size
                let batch_size = (*remaining).max(100);
                let mut offset = 0;

                while *remaining > 0 {
                    // Create a Skip sequence to offset into the source
                    let source_with_skip = if offset > 0 {
                        LazySequenceObject::new(LazySeqKind::Skip {
                            source: source.clone(),
                            remaining: offset,
                        })
                    } else {
                        source.clone()
                    };

                    let source_elements = take_from_lazy_full(batch_size, &source_with_skip);
                    if source_elements.is_empty() {
                        break; // Source exhausted
                    }

                    for val in source_elements {
                        if *remaining == 0 {
                            break;
                        }
                        offset += 1;
                        if call_closure(pred_closure, &[val]).is_truthy() {
                            result.push_back(val);
                            *remaining -= 1;
                        }
                    }
                }
            }
        }

        LazySeqKind::Skip { source, remaining: skip_remaining } => {
            // Create a new source that skips the required elements
            let source_elements = take_from_lazy_full(*remaining + skip_remaining, source);
            for (i, val) in source_elements.into_iter().enumerate() {
                if i < *skip_remaining {
                    continue;
                }
                if *remaining == 0 {
                    break;
                }
                result.push_back(val);
                *remaining -= 1;
            }
        }

        LazySeqKind::Combinations { source, size, indices, done } => {
            if *done || source.is_empty() || *size == 0 || *size > source.len() {
                return;
            }

            let mut current_indices = indices.clone();
            let n = source.len();

            while *remaining > 0 {
                // Check if done
                if current_indices.is_empty() || current_indices[0] > n - size {
                    return;
                }

                // Get current combination
                let combination: im::Vector<Value> = current_indices
                    .iter()
                    .map(|&i| source[i])
                    .collect();
                result.push_back(Value::from_list(combination));
                *remaining -= 1;

                // Advance to next combination
                let mut i = size - 1;

                // Find the rightmost index that can be incremented
                while current_indices[i] == n - size + i {
                    if i == 0 {
                        // All combinations exhausted
                        return;
                    }
                    i -= 1;
                }

                // Increment this index and reset all subsequent indices
                current_indices[i] += 1;
                for j in (i + 1)..*size {
                    current_indices[j] = current_indices[j - 1] + 1;
                }
            }
        }

        LazySeqKind::Zip { sources } => {
            // For each element, we need to take one element from each source
            // and combine them into a tuple
            if sources.is_empty() {
                return;
            }

            let mut indices: Vec<usize> = vec![0; sources.len()];

            while *remaining > 0 {
                // Take one element from each source at current index
                let mut tuple = im::Vector::new();
                let mut all_have_elements = true;

                for (i, source) in sources.iter().enumerate() {
                    // Take (indices[i] + 1) elements and get the last one
                    let elements = take_from_lazy_full(indices[i] + 1, source);
                    if elements.len() <= indices[i] {
                        // This source is exhausted
                        all_have_elements = false;
                        break;
                    }
                    tuple.push_back(elements[indices[i]]);
                }

                if !all_have_elements {
                    break;
                }

                result.push_back(Value::from_list(tuple));
                *remaining -= 1;

                // Advance all indices
                for idx in &mut indices {
                    *idx += 1;
                }
            }
        }
    }
}

// ============================================================================
// §11.14 String Functions
// ============================================================================

/// `lines(string)` → List[String]
///
/// Split string on newline characters (`\n`).
///
/// Per LANG.txt §11.14:
/// - lines("a\nb\nc") → ["a", "b", "c"]
/// - lines("single line") → ["single line"]
/// - lines("") → [""]
#[no_mangle]
pub extern "C" fn rt_lines(value: Value) -> Value {
    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => return Value::from_list(im::Vector::new()),
    };

    // Split on newlines
    let parts: im::Vector<Value> = s
        .split('\n')
        .map(|part| Value::from_string(part.to_string()))
        .collect();

    Value::from_list(parts)
}

/// `split(separator, string)` → List[String]
///
/// Split string by separator.
///
/// Per LANG.txt §11.14:
/// - split(",", "a,b,c") → ["a", "b", "c"]
/// - split(" ", "hello world") → ["hello", "world"]
/// - split("", "abc") → ["a", "b", "c"] (split into characters/graphemes)
#[no_mangle]
pub extern "C" fn rt_split(separator: Value, string: Value) -> Value {
    // Both must be strings
    let sep = match separator.as_string() {
        Some(s) => s,
        None => return Value::from_list(im::Vector::new()),
    };
    let s = match string.as_string() {
        Some(s) => s,
        None => return Value::from_list(im::Vector::new()),
    };

    // Empty separator: split into grapheme clusters
    if sep.is_empty() {
        use unicode_segmentation::UnicodeSegmentation;
        let parts: im::Vector<Value> = s
            .graphemes(true)
            .map(|g| Value::from_string(g.to_string()))
            .collect();
        return Value::from_list(parts);
    }

    // Normal split
    let parts: im::Vector<Value> = s
        .split(sep)
        .map(|part| Value::from_string(part.to_string()))
        .collect();

    Value::from_list(parts)
}

/// `regex_match(pattern, string)` → List[String]
///
/// Match and return capture groups only (NOT the full match).
///
/// Per LANG.txt §11.14:
/// - regex_match("(\\d+)", "abc123") → ["123"]
/// - regex_match("(\\w+):(\\d+)", "port:8080") → ["port", "8080"]
/// - regex_match("\\d+", "abc123") → [] (no capture groups)
/// - regex_match("(\\d+)", "no numbers") → [] (no match)
#[no_mangle]
pub extern "C-unwind" fn rt_regex_match(pattern: Value, string: Value) -> Value {
    // Both must be strings
    let pat = match pattern.as_string() {
        Some(s) => s,
        None => return Value::from_list(im::Vector::new()),
    };
    let s = match string.as_string() {
        Some(s) => s,
        None => return Value::from_list(im::Vector::new()),
    };

    // Compile regex - RuntimeErr on invalid pattern per LANG.txt
    let re = match Regex::new(pat) {
        Ok(r) => r,
        Err(e) => runtime_error(&format!("invalid regex pattern '{}': {}", pat, e)),
    };

    // Find first match and return capture groups only
    match re.captures(s) {
        Some(caps) => {
            // Skip group 0 (full match), return only capture groups
            let groups: im::Vector<Value> = caps
                .iter()
                .skip(1) // Skip group 0 (full match)
                .filter_map(|m| m.map(|g| Value::from_string(g.as_str().to_string())))
                .collect();
            Value::from_list(groups)
        }
        None => Value::from_list(im::Vector::new()),
    }
}

/// `regex_match_all(pattern, string)` → List[String]
///
/// Match all occurrences of pattern (entire match, not just groups).
///
/// Per LANG.txt §11.14:
/// - regex_match_all("\\d+", "a1b2c3") → ["1", "2", "3"]
/// - regex_match_all("\\w+", "hello world") → ["hello", "world"]
#[no_mangle]
pub extern "C-unwind" fn rt_regex_match_all(pattern: Value, string: Value) -> Value {
    // Both must be strings
    let pat = match pattern.as_string() {
        Some(s) => s,
        None => return Value::from_list(im::Vector::new()),
    };
    let s = match string.as_string() {
        Some(s) => s,
        None => return Value::from_list(im::Vector::new()),
    };

    // Compile regex - RuntimeErr on invalid pattern per LANG.txt
    let re = match Regex::new(pat) {
        Ok(r) => r,
        Err(e) => runtime_error(&format!("invalid regex pattern '{}': {}", pat, e)),
    };

    // Find all matches
    let matches: im::Vector<Value> = re
        .find_iter(s)
        .map(|m| Value::from_string(m.as_str().to_string()))
        .collect();

    Value::from_list(matches)
}

/// `md5(value)` → String
///
/// Return the MD5 hash of a string as a lowercase hexadecimal string.
///
/// Per LANG.txt §11.14:
/// - md5("hello") → "5d41402abc4b2a76b9719d911017c592"
/// - md5("") → "d41d8cd98f00b204e9800998ecf8427e"
#[no_mangle]
pub extern "C" fn rt_md5(value: Value) -> Value {
    use md5::{Md5, Digest};

    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => return Value::from_string("".to_string()),
    };

    // Compute MD5 hash
    let mut hasher = Md5::new();
    hasher.update(s.as_bytes());
    let result = hasher.finalize();

    // Convert to lowercase hex string
    let hex: String = result.iter().map(|b| format!("{:02x}", b)).collect();

    Value::from_string(hex)
}

/// `upper(string)` → String
///
/// Convert string to uppercase.
///
/// Per LANG.txt §11.14:
/// - upper("hello") → "HELLO"
#[no_mangle]
pub extern "C" fn rt_upper(value: Value) -> Value {
    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => return Value::from_string("".to_string()),
    };

    Value::from_string(s.to_uppercase())
}

/// `lower(string)` → String
///
/// Convert string to lowercase.
///
/// Per LANG.txt §11.14:
/// - lower("HELLO") → "hello"
#[no_mangle]
pub extern "C" fn rt_lower(value: Value) -> Value {
    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => return Value::from_string("".to_string()),
    };

    Value::from_string(s.to_lowercase())
}

/// `replace(from, to, string)` → String
///
/// Replace all occurrences of substring.
///
/// Per LANG.txt §11.14:
/// - replace("a", "x", "banana") → "bxnxnx"
/// - replace("world", "Santa", "hello world") → "hello Santa"
#[no_mangle]
pub extern "C" fn rt_replace(from: Value, to: Value, string: Value) -> Value {
    // All must be strings
    let from_str = match from.as_string() {
        Some(s) => s,
        None => return string,
    };
    let to_str = match to.as_string() {
        Some(s) => s,
        None => return string,
    };
    let s = match string.as_string() {
        Some(s) => s,
        None => return Value::from_string("".to_string()),
    };

    Value::from_string(s.replace(from_str, to_str))
}

/// `join(separator, collection)` → String
///
/// Join elements into a string with separator.
///
/// Per LANG.txt §11.14:
/// - join(", ", [1, 2, 3]) → "1, 2, 3"
/// - join("-", ["a", "b", "c"]) → "a-b-c"
#[no_mangle]
pub extern "C" fn rt_join(separator: Value, collection: Value) -> Value {
    // Separator must be a string
    let sep = match separator.as_string() {
        Some(s) => s.to_string(),
        None => "".to_string(),
    };

    // Helper to convert value to string representation
    fn value_to_string(v: Value) -> String {
        if let Some(s) = v.as_string() {
            s.to_string()
        } else if let Some(i) = v.as_integer() {
            i.to_string()
        } else if let Some(d) = v.as_decimal() {
            d.to_string()
        } else if let Some(b) = v.as_bool() {
            if b { "true".to_string() } else { "false".to_string() }
        } else if v.is_nil() {
            "nil".to_string()
        } else {
            // For collections and other types, use a placeholder
            "<value>".to_string()
        }
    }

    // List
    if let Some(list) = collection.as_list() {
        let parts: Vec<String> = list.iter().map(|v| value_to_string(*v)).collect();
        return Value::from_string(parts.join(&sep));
    }

    // Set
    if let Some(set) = collection.as_set() {
        let parts: Vec<String> = set.iter().map(|v| value_to_string(*v)).collect();
        return Value::from_string(parts.join(&sep));
    }

    // String (treat as list of graphemes)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        let parts: Vec<&str> = s.graphemes(true).collect();
        return Value::from_string(parts.join(&sep));
    }

    Value::from_string("".to_string())
}

// ============================================================================
// §11.15 Math Functions
// ============================================================================

/// `abs(value)` → Integer | Decimal
///
/// Return the absolute value of a number.
///
/// Per LANG.txt §11.15:
/// - abs(-5) → 5
/// - abs(5) → 5
/// - abs(-3.7) → 3.7
#[no_mangle]
pub extern "C" fn rt_abs(value: Value) -> Value {
    // Integer
    if let Some(i) = value.as_integer() {
        return Value::from_integer(i.abs());
    }

    // Decimal
    if let Some(d) = value.as_decimal() {
        return Value::from_decimal(d.abs());
    }

    // Other types - return 0
    Value::from_integer(0)
}

/// `signum(value)` → Integer
///
/// Return the sign of a number: -1 (negative), 0 (zero), or 1 (positive).
///
/// Per LANG.txt §11.15:
/// - signum(5) → 1
/// - signum(0) → 0
/// - signum(-3) → -1
/// - signum(5.5) → 1
/// - signum(-5.5) → -1
#[no_mangle]
pub extern "C" fn rt_signum(value: Value) -> Value {
    // Integer
    if let Some(i) = value.as_integer() {
        return Value::from_integer(i.signum());
    }

    // Decimal
    if let Some(d) = value.as_decimal() {
        if d > 0.0 {
            return Value::from_integer(1);
        } else if d < 0.0 {
            return Value::from_integer(-1);
        } else {
            return Value::from_integer(0);
        }
    }

    // Other types - return 0
    Value::from_integer(0)
}

/// `vec_add(a, b)` → List
///
/// Vector addition: element-wise sum of two lists.
/// Result length equals shorter list.
///
/// Per LANG.txt §11.15:
/// - vec_add([1, 2], [3, 4]) → [4, 6]
/// - vec_add([1, 2, 3], [10, 20]) → [11, 22]
#[no_mangle]
pub extern "C" fn rt_vec_add(a: Value, b: Value) -> Value {
    // Both must be lists
    let list_a = match a.as_list() {
        Some(l) => l,
        None => return Value::from_list(im::Vector::new()),
    };
    let list_b = match b.as_list() {
        Some(l) => l,
        None => return Value::from_list(im::Vector::new()),
    };

    // Element-wise addition, result length equals shorter list
    let result: im::Vector<Value> = list_a
        .iter()
        .zip(list_b.iter())
        .map(|(va, vb)| {
            // Add the two values using rt_add
            rt_add(*va, *vb)
        })
        .collect();

    Value::from_list(result)
}

// ============================================================================
// §4.5 Bitwise Functions
// ============================================================================

/// `bit_and(a, b)` → Integer
///
/// Bitwise AND.
///
/// Per LANG.txt §4.5:
/// - bit_and(12, 10) → 8  (1100 & 1010 = 1000)
#[no_mangle]
pub extern "C" fn rt_bit_and(a: Value, b: Value) -> Value {
    let ia = a.as_integer().unwrap_or(0);
    let ib = b.as_integer().unwrap_or(0);
    Value::from_integer(ia & ib)
}

/// `bit_or(a, b)` → Integer
///
/// Bitwise OR.
///
/// Per LANG.txt §4.5:
/// - bit_or(12, 10) → 14 (1100 | 1010 = 1110)
#[no_mangle]
pub extern "C" fn rt_bit_or(a: Value, b: Value) -> Value {
    let ia = a.as_integer().unwrap_or(0);
    let ib = b.as_integer().unwrap_or(0);
    Value::from_integer(ia | ib)
}

/// `bit_xor(a, b)` → Integer
///
/// Bitwise XOR.
///
/// Per LANG.txt §4.5:
/// - bit_xor(12, 10) → 6  (1100 ^ 1010 = 0110)
#[no_mangle]
pub extern "C" fn rt_bit_xor(a: Value, b: Value) -> Value {
    let ia = a.as_integer().unwrap_or(0);
    let ib = b.as_integer().unwrap_or(0);
    Value::from_integer(ia ^ ib)
}

/// `bit_not(value)` → Integer
///
/// Bitwise NOT (complement).
///
/// Per LANG.txt §4.5:
/// - bit_not(12) → -13 (bitwise complement)
#[no_mangle]
pub extern "C" fn rt_bit_not(value: Value) -> Value {
    let i = value.as_integer().unwrap_or(0);
    Value::from_integer(!i)
}

/// `bit_shift_left(value, shift)` → Integer
///
/// Left shift.
///
/// Per LANG.txt §4.5:
/// - bit_shift_left(1, 3) → 8  (1 << 3 = 1000)
#[no_mangle]
pub extern "C" fn rt_bit_shift_left(value: Value, shift: Value) -> Value {
    let i = value.as_integer().unwrap_or(0);
    let s = shift.as_integer().unwrap_or(0);
    // Clamp shift to valid range (0-63 for i64)
    if !(0..=63).contains(&s) {
        return Value::from_integer(0);
    }
    Value::from_integer(i << s)
}

/// `bit_shift_right(value, shift)` → Integer
///
/// Right shift (arithmetic shift for signed integers).
///
/// Per LANG.txt §4.5:
/// - bit_shift_right(8, 2) → 2  (1000 >> 2 = 10)
#[no_mangle]
pub extern "C" fn rt_bit_shift_right(value: Value, shift: Value) -> Value {
    let i = value.as_integer().unwrap_or(0);
    let s = shift.as_integer().unwrap_or(0);
    // Clamp shift to valid range (0-63 for i64)
    if !(0..=63).contains(&s) {
        return Value::from_integer(0);
    }
    Value::from_integer(i >> s)
}

// ============================================================================
// §11.16 Utility Functions
// ============================================================================

/// `id(value)` → Value
///
/// Identity function - returns its argument unchanged.
///
/// Per LANG.txt §11.16:
/// - id(42) → 42
/// - Useful for cases where a function is needed but no transformation required
#[no_mangle]
pub extern "C" fn rt_id(value: Value) -> Value {
    value
}

/// `type(value)` → String
///
/// Return the type name of a value as a string.
///
/// Per LANG.txt §11.16:
/// - type(42) → "Integer"
/// - type(3.14) → "Decimal"
/// - type("hello") → "String"
/// - type(true) → "Boolean"
/// - type(nil) → "Nil"
/// - type([1, 2, 3]) → "List"
/// - type({1, 2, 3}) → "Set"
/// - type(#{a: 1}) → "Dictionary"
/// - type(1..) → "LazySequence"
/// - type(|x| x) → "Function"
#[no_mangle]
pub extern "C" fn rt_type(value: Value) -> Value {
    // Check types in a specific order
    if value.is_nil() {
        return Value::from_string("Nil".to_string());
    }
    if value.is_boolean() {
        return Value::from_string("Boolean".to_string());
    }
    if value.is_integer() {
        return Value::from_string("Integer".to_string());
    }
    if value.as_decimal().is_some() {
        return Value::from_string("Decimal".to_string());
    }
    if value.as_string().is_some() {
        return Value::from_string("String".to_string());
    }
    if value.as_list().is_some() {
        return Value::from_string("List".to_string());
    }
    if value.as_set().is_some() {
        return Value::from_string("Set".to_string());
    }
    if value.as_dict().is_some() {
        return Value::from_string("Dictionary".to_string());
    }
    if value.as_lazy_sequence().is_some() {
        return Value::from_string("LazySequence".to_string());
    }
    if value.as_closure().is_some() {
        return Value::from_string("Function".to_string());
    }

    Value::from_string("Unknown".to_string())
}

/// `or(a, b)` → Value
///
/// Logical OR function - returns first truthy value, or second value if first is falsy.
///
/// Per LANG.txt §11.16:
/// - or(1, 2) → 1
/// - or(nil, 2) → 2
/// - or(0, false) → false
#[no_mangle]
pub extern "C" fn rt_or(a: Value, b: Value) -> Value {
    if a.is_truthy() {
        a
    } else {
        b
    }
}

/// `and(a, b)` → Value
///
/// Logical AND function - returns first falsy value, or second value if first is truthy.
///
/// Per LANG.txt §11.16:
/// - and(1, 2) → 2
/// - and(nil, 2) → nil
/// - and(0, 2) → 0
#[no_mangle]
pub extern "C" fn rt_and(a: Value, b: Value) -> Value {
    if a.is_truthy() {
        b
    } else {
        a
    }
}

// ============================================================================
// §13 External Functions
// ============================================================================

/// Format a Value as a string representation (for display/printing)
pub fn format_value(value: &Value) -> String {
    // Check type and format accordingly
    if value.is_nil() {
        return "nil".to_string();
    }

    if let Some(b) = value.as_bool() {
        return if b { "true" } else { "false" }.to_string();
    }

    if let Some(n) = value.as_integer() {
        return n.to_string();
    }

    if let Some(d) = value.as_decimal() {
        return d.to_string();
    }

    if let Some(s) = value.as_string() {
        return s.to_string();
    }

    if let Some(list) = value.as_list() {
        let items: Vec<String> = list.iter().map(format_value).collect();
        return format!("[{}]", items.join(", "));
    }

    if let Some(set) = value.as_set() {
        let items: Vec<String> = set.iter().map(format_value).collect();
        return format!("{{{}}}", items.join(", "));
    }

    if let Some(dict) = value.as_dict() {
        let items: Vec<String> = dict.iter()
            .map(|(k, v)| format!("{}: {}", format_value(k), format_value(v)))
            .collect();
        return format!("#{{{}}}", items.join(", "));
    }

    if value.as_closure().is_some() {
        return "<function>".to_string();
    }

    if value.as_lazy_sequence().is_some() {
        return "<lazy-sequence>".to_string();
    }

    "<unknown>".to_string()
}

/// `puts(..values)` → Nil
///
/// Print values to stdout, separated by spaces, followed by newline.
/// Returns nil.
///
/// Per LANG.txt §13:
/// - puts("Hello", "World") prints "Hello World\n"
/// - puts(42) prints "42\n"
///
/// # Safety
/// The caller must ensure:
/// - `argv` points to a valid array of `argc` Values
/// - The pointer remains valid for the duration of the call
#[no_mangle]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn rt_puts(argc: u32, argv: *const Value) -> Value {
    if argc == 0 {
        println!();
        return Value::nil();
    }

    // Safety: Caller guarantees valid argc/argv from LLVM-generated code
    let args: &[Value] = unsafe { std::slice::from_raw_parts(argv, argc as usize) };

    let formatted: Vec<String> = args.iter().map(format_value).collect();
    println!("{}", formatted.join(" "));

    Value::nil()
}

/// Helper for calling rt_puts with two arguments (common case in runner)
#[no_mangle]
pub extern "C" fn rt_puts_two(a: Value, b: Value) -> Value {
    let formatted = format!("{} {}", format_value(&a), format_value(&b));
    println!("{}", formatted);
    Value::nil()
}

/// Get the current time in nanoseconds since program start.
/// Uses a relative timestamp to avoid large number overflow in NaN-boxing.
/// Used for timing measurements in the runner.
#[no_mangle]
pub extern "C" fn rt_time_nanos() -> Value {
    use std::time::Instant;
    use std::sync::OnceLock;

    static START_TIME: OnceLock<Instant> = OnceLock::new();
    let start = START_TIME.get_or_init(Instant::now);
    let elapsed_nanos = start.elapsed().as_nanos() as i64;
    Value::from_integer(elapsed_nanos)
}

/// Get the cache path for an AOC input file.
/// Path: ~/.cache/dasher/aoc/YEAR/DAY.txt
pub fn get_aoc_cache_path(year: u32, day: u32) -> std::path::PathBuf {
    let cache_dir = dirs::cache_dir()
        .unwrap_or_else(|| std::path::PathBuf::from(".cache"));
    cache_dir
        .join("dasher")
        .join("aoc")
        .join(year.to_string())
        .join(format!("{}.txt", day))
}

/// Get the AOC session cookie.
/// Tries (in order):
/// 1. AOC_SESSION environment variable
/// 2. ~/.config/dasher/session.txt
fn get_aoc_session() -> Option<String> {
    // First try environment variable
    if let Ok(session) = std::env::var("AOC_SESSION") {
        if !session.is_empty() {
            return Some(session);
        }
    }

    // Then try config file
    let config_dir = dirs::config_dir()?;
    let session_file = config_dir.join("dasher").join("session.txt");
    std::fs::read_to_string(session_file).ok().map(|s| s.trim().to_string())
}

/// Parse an aoc:// URL and return (year, day) or None if invalid.
fn parse_aoc_url(url: &str) -> Option<(u32, u32)> {
    let rest = url.strip_prefix("aoc://")?;
    let parts: Vec<&str> = rest.split('/').collect();
    if parts.len() != 2 {
        return None;
    }
    let year: u32 = parts[0].parse().ok()?;
    let day: u32 = parts[1].parse().ok()?;

    // Validate year/day ranges (AOC started in 2015, days 1-25)
    if year < 2015 || !(1..=25).contains(&day) {
        return None;
    }
    Some((year, day))
}

/// Fetch AOC input from adventofcode.com.
/// Returns the input string or None on error.
fn fetch_aoc_input(year: u32, day: u32, session: &str) -> Option<String> {
    let url = format!("https://adventofcode.com/{}/day/{}/input", year, day);

    // Use a synchronous HTTP client
    // For simplicity, we'll shell out to curl since we're in an FFI context
    // A proper implementation would use reqwest or ureq
    let output = std::process::Command::new("curl")
        .arg("-s")
        .arg("-f")  // Fail silently on HTTP errors
        .arg("-H")
        .arg(format!("Cookie: session={}", session))
        .arg(&url)
        .output()
        .ok()?;

    if output.status.success() {
        String::from_utf8(output.stdout).ok()
    } else {
        None
    }
}

/// Fetch content from an HTTP or HTTPS URL.
///
/// Returns the response body as a String, or nil on error.
fn read_http_url(url: &str) -> Value {
    match ureq::get(url).call() {
        Ok(response) => {
            // Read the response body as a string
            match response.into_string() {
                Ok(body) => Value::from_string(&body),
                Err(_) => Value::nil(), // Failed to read body
            }
        }
        Err(_) => Value::nil(), // Network or HTTP error
    }
}

/// Read AOC input, using cache if available.
fn read_aoc_input(url: &str) -> Value {
    let (year, day) = match parse_aoc_url(url) {
        Some(v) => v,
        None => return Value::nil(),
    };

    // Check cache first
    let cache_path = get_aoc_cache_path(year, day);
    if let Ok(contents) = std::fs::read_to_string(&cache_path) {
        return Value::from_string(&contents);
    }

    // Need to fetch - check for session
    let session = match get_aoc_session() {
        Some(s) => s,
        None => {
            eprintln!("Error: AOC session not found. Set AOC_SESSION environment variable or create ~/.config/dasher/session.txt");
            return Value::nil();
        }
    };

    // Fetch from AOC
    let input = match fetch_aoc_input(year, day, &session) {
        Some(s) => s,
        None => {
            eprintln!("Error: Failed to fetch AOC input for {}/{}", year, day);
            return Value::nil();
        }
    };

    // Cache for future use
    if let Some(parent) = cache_path.parent() {
        std::fs::create_dir_all(parent).ok();
    }
    std::fs::write(&cache_path, &input).ok();

    Value::from_string(&input)
}

/// `read(path)` → String
///
/// Read file contents from a path. Supports multiple schemes:
/// - Local files: `read("./input.txt")` or `read("/absolute/path.txt")`
/// - HTTP(S): `read("https://example.com/data.txt")`
/// - AOC: `read("aoc://year/day")` - fetches puzzle input with caching
///
/// Per LANG.txt §13:
/// - Returns file contents as a String
/// - Returns nil on error (file not found, permission denied, network error, etc.)
#[no_mangle]
pub extern "C" fn rt_read(path: Value) -> Value {
    let path_str = match path.as_string() {
        Some(s) => s,
        None => return Value::nil(), // Invalid argument type
    };

    // Check for URL schemes
    if path_str.starts_with("http://") || path_str.starts_with("https://") {
        return read_http_url(path_str);
    }

    if path_str.starts_with("aoc://") {
        return read_aoc_input(path_str);
    }

    // Local file read
    match std::fs::read_to_string(path_str) {
        Ok(contents) => Value::from_string(&contents),
        Err(_) => Value::nil(),
    }
}

// ============================================================================
// §11.16 Memoization
// ============================================================================

use super::heap::MemoizedClosureObject;

/// `memoize(function)` → Function
///
/// Return a memoized version of a function. Caches results based on arguments
/// for improved performance on repeated calls with same arguments.
///
/// Per LANG.txt §8.10:
/// - Takes a function (closure) as input
/// - Returns a new callable that caches results
/// - Cache key is the tuple of arguments
///
/// ```santa
/// let fib = memoize |n| {
///   if n > 1 { fib(n - 1) + fib(n - 2) } else { n }
/// };
/// fib(50)  // Computed efficiently
/// ```
#[no_mangle]
pub extern "C" fn rt_memoize(func: Value) -> Value {
    // Verify the input is a closure
    let closure = match func.as_closure() {
        Some(c) => c,
        None => return Value::nil(), // Not a closure - return nil
    };

    // Create a memoized wrapper around the closure
    let arity = closure.arity;
    let memoized = MemoizedClosureObject::new(func, arity);
    Value::from_memoized_closure(memoized)
}

/// Call a memoized closure with the given arguments
///
/// This function handles the caching logic:
/// 1. Check if arguments are in cache
/// 2. If cached, return cached result
/// 3. If not cached, call the inner closure, cache result, return it
///
/// # Safety
///
/// - `argv` must be a valid pointer to an array of `argc` Values, or null if `argc` is 0
/// - The caller must ensure the Values in argv are valid for the duration of the call
#[no_mangle]
pub unsafe extern "C" fn rt_call_memoized(callee: Value, argc: u32, argv: *const Value) -> Value {
    // Try as memoized closure first
    if let Some(memoized) = callee.as_memoized_closure() {
        // Collect arguments into a vector for cache lookup
        let args: Vec<Value> = if argc == 0 || argv.is_null() {
            Vec::new()
        } else {
            unsafe { std::slice::from_raw_parts(argv, argc as usize).to_vec() }
        };

        // Check cache first
        if let Some(cached) = memoized.get_cached(&args) {
            return cached;
        }

        // Not in cache - call the inner closure
        let inner_closure = memoized.inner_closure;
        if let Some(closure) = inner_closure.as_closure() {
            // Call the inner closure
            let result = call_closure(closure, &args);

            // Cache the result
            memoized.cache_result(args, result);

            return result;
        }

        // Inner value is not a closure - shouldn't happen with rt_memoize
        return Value::nil();
    }

    // Also handle regular closures for compatibility
    if let Some(closure) = callee.as_closure() {
        let args: Vec<Value> = if argc == 0 || argv.is_null() {
            Vec::new()
        } else {
            unsafe { std::slice::from_raw_parts(argv, argc as usize).to_vec() }
        };
        return call_closure(closure, &args);
    }

    // Not callable
    Value::nil()
}
