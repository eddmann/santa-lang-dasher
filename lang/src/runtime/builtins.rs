//! Built-in functions for santa-lang runtime
//!
//! These functions are called from LLVM-compiled code via FFI.
//! LANG.txt Reference: §11 Built-in Functions

use super::value::Value;
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
/// - Range/LazySequence: forces evaluation to list (TODO)
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

    // TODO: Range and LazySequence support

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
/// - Range: set(1..5) → {1, 2, 3, 4} (TODO)
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

    // TODO: Range support

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

    // TODO: Range, LazySequence support

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

    // TODO: Range (bounded only)

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

    // TODO: Range, LazySequence

    Value::nil()
}

/// `second(collection)` → Value | Nil
///
/// Get second element. Returns `nil` if collection has fewer than 2 elements.
/// Per LANG.txt §11.2:
/// - List: second([1, 2]) → 2; second([1]) → nil
/// - Set: second({1, 2}) → 2
/// - String: second("ab") → "b"
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

    // TODO: Range, LazySequence

    Value::nil()
}

/// `last(collection)` → Value | Nil
///
/// Get last element. Returns `nil` if collection is empty.
/// Per LANG.txt §11.2:
/// - List: last([1, 2]) → 2; last([]) → nil
/// - Set: last({1, 2}) → 2
/// - String: last("ab") → "b"
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

    // TODO: Range (bounded only)

    Value::nil()
}

/// `rest(collection)` → Collection
///
/// Get all but first element. Returns empty collection if input has ≤1 element.
/// Per LANG.txt §11.2:
/// - List: rest([1, 2]) → [2]; rest([1]) → []
/// - Set: rest({1, 2}) → {2}
/// - String: rest("ab") → "b"
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

    // TODO: Range, LazySequence

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
#[no_mangle]
pub extern "C" fn rt_push(value: Value, collection: Value) -> Value {
    // List - append to end
    if let Some(list) = collection.as_list() {
        let mut new_list = list.clone();
        new_list.push_back(value);
        return Value::from_list(new_list);
    }

    // Set - insert (no-op if already present)
    if let Some(set) = collection.as_set() {
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
#[no_mangle]
pub extern "C" fn rt_assoc(key: Value, value: Value, collection: Value) -> Value {
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
        let new_dict = dict.update(key, value);
        return Value::from_dict(new_dict);
    }

    // Unsupported type - return original collection
    collection
}
