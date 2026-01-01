//! Built-in functions for santa-lang runtime
//!
//! These functions are called from LLVM-compiled code via FFI.
//! LANG.txt Reference: §11 Built-in Functions

use super::heap::{ClosureObject, LazySeqKind, LazySequenceObject};
use super::operations::{is_infinite_lazy_sequence, rt_add, rt_eq, runtime_error, type_name};
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
pub extern "C-unwind" fn rt_ints(value: Value) -> Value {
    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => runtime_error("ints(string) expects a String"),
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
        if is_infinite_lazy_sequence(lazy_seq) {
            runtime_error("Cannot materialize unbounded lazy sequence");
        }
        // Use collect_bounded_lazy which handles Map, Filter, and other lazy kinds
        // that require closure evaluation
        return Value::from_list(collect_bounded_lazy(lazy_seq));
    }

    runtime_error("list(value) expects List, Set, Dictionary, String, Range, or LazySequence")
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
        for elem in list.iter() {
            if elem.as_lazy_sequence().is_some() {
                runtime_error("LazySequence is not hashable and cannot be added to a Set");
            }
            if !elem.is_hashable() {
                runtime_error(&format!(
                    "{} is not hashable and cannot be added to a Set",
                    type_name(elem)
                ));
            }
        }
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

    // LazySequence (including Range, Map, Filter, etc.) → Force evaluation to set
    if let Some(lazy_seq) = value.as_lazy_sequence() {
        if is_infinite_lazy_sequence(lazy_seq) {
            runtime_error("Cannot materialize unbounded lazy sequence");
        }
        // Use collect_bounded_lazy which handles Map, Filter, and other lazy kinds
        // that require closure evaluation
        let elements = collect_bounded_lazy(lazy_seq);
        for elem in elements.iter() {
            if elem.as_lazy_sequence().is_some() {
                runtime_error("LazySequence is not hashable and cannot be added to a Set");
            }
            if !elem.is_hashable() {
                runtime_error(&format!(
                    "{} is not hashable and cannot be added to a Set",
                    type_name(elem)
                ));
            }
        }
        let set: im::HashSet<Value> = elements.iter().copied().collect();
        return Value::from_set(set);
    }

    runtime_error("set(value) expects List, Set, String, Range, or LazySequence")
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
                if tuple.len() < 2 {
                    runtime_error("dict(value) expects list of [key, value] tuples");
                }
                let key = tuple[0];
                if !key.is_hashable() {
                    runtime_error(&format!(
                        "{} is not hashable and cannot be used as a Dictionary key",
                        type_name(&key)
                    ));
                }
                dict.insert(tuple[0], tuple[1]);
            } else {
                runtime_error("dict(value) expects list of [key, value] tuples");
            }
        }
        return Value::from_dict(dict);
    }

    runtime_error("dict(value) expects List or Dictionary")
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
    // List - index by integer or slice by range
    if let Some(list) = collection.as_list() {
        // Check if index is a range for slicing
        if let Some(range) = index.as_lazy_sequence() {
            use crate::heap::LazySeqKind;
            if let LazySeqKind::Range {
                current,
                end,
                inclusive,
                step: _,  // Accept any step - we use start/end for slicing
            } = &range.kind
            {
                let len = list.len() as i64;
                let start = *current;

                // Normalize start (handle negative indexing)
                let start_norm = if start < 0 { (len + start).max(0) } else { start.min(len) };

                // Calculate end index (handle negative indexing)
                let end_idx = match end {
                    Some(e) => {
                        let e = *e;
                        // Normalize negative index
                        let e_norm = if e < 0 { len + e } else { e };
                        if *inclusive {
                            (e_norm + 1).min(len)
                        } else {
                            e_norm.min(len)
                        }
                    }
                    None => len, // Unbounded: slice to end
                };

                if start_norm <= len && end_idx >= start_norm && end_idx >= 0 {
                    // Use im::Vector's native split_off + take for O(log n) performance
                    // clone() is O(1) for im::Vector due to structural sharing
                    let slice_len = (end_idx - start_norm) as usize;
                    let slice = list.clone().split_off(start_norm as usize).take(slice_len);
                    return Value::from_list(slice);
                }
                return Value::from_list(im::Vector::new());
            }
        }
        // Regular integer index (supports negative indexing)
        // Per LANG.txt: [10, 20, 30][-1] → 30 (from end)
        if let Some(i) = index.as_integer() {
            let len = list.len() as i64;
            let idx = if i < 0 { len + i } else { i };
            if idx >= 0 && idx < len {
                return list[idx as usize];
            }
            return Value::nil();
        }
        runtime_error("get(index, collection) expects Integer or Range index for List");
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

    // String - index by integer to get grapheme, or slice by range
    // Uses cached grapheme boundaries for O(1) access after first indexing
    if collection.as_string().is_some() {
        // Check if index is a range for slicing
        if let Some(range) = index.as_lazy_sequence() {
            use crate::heap::LazySeqKind;
            if let LazySeqKind::Range {
                current,
                end,
                inclusive,
                step: _,  // Accept any step - we use start/end for slicing
            } = &range.kind
            {
                let len = collection.grapheme_len() as i64;
                let start = *current;

                // Normalize start (handle negative indexing)
                let start_norm = if start < 0 { (len + start).max(0) } else { start.min(len) };

                // Calculate end index (handle negative indexing)
                let end_idx = match end {
                    Some(e) => {
                        let e = *e;
                        // Normalize negative index
                        let e_norm = if e < 0 { len + e } else { e };
                        if *inclusive {
                            (e_norm + 1).min(len)
                        } else {
                            e_norm.min(len)
                        }
                    }
                    None => len, // Unbounded: slice to end
                };

                if start_norm <= len && end_idx >= start_norm && end_idx >= 0 {
                    // Use cached grapheme_slice for O(1) slicing
                    if let Some(slice) = collection.grapheme_slice(start_norm as usize, end_idx as usize) {
                        return Value::from_string(slice.to_string());
                    }
                }
                return Value::from_string(String::new());
            }
        }
        // Regular integer index (supports negative indexing)
        // Per LANG.txt: "hello"[-1] → "o"
        if let Some(i) = index.as_integer() {
            if i < 0 {
                // Use cached grapheme_at_neg for O(1) negative indexing
                if let Some(grapheme) = collection.grapheme_at_neg(i) {
                    return Value::from_string(grapheme.to_string());
                }
                return Value::nil();
            } else {
                // Use cached grapheme_at for O(1) positive indexing
                if let Some(grapheme) = collection.grapheme_at(i as usize) {
                    return Value::from_string(grapheme.to_string());
                }
                return Value::nil();
            }
        }
        runtime_error("get(index, collection) expects Integer or Range index for String");
    }

    // LazySequence (including Range) - index by integer
    if let Some(lazy_seq) = collection.as_lazy_sequence() {
        if let Some(i) = index.as_integer() {
            if i < 0 {
                return Value::nil();
            }
            let idx = i as usize;
            return lazy_nth(lazy_seq, idx).unwrap_or_else(Value::nil);
        }
        runtime_error("get(index, collection) expects Integer index for LazySequence");
    }

    runtime_error("get(index, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
}

/// Get the nth element of a lazy sequence without materializing it.
/// Returns None if the sequence is exhausted before reaching idx.
fn lazy_nth(lazy: &LazySequenceObject, idx: usize) -> Option<Value> {
    use crate::heap::LazySeqKind;

    match &lazy.kind {
        // Range - O(1) direct calculation
        LazySeqKind::Range {
            current,
            end,
            inclusive,
            step,
        } => {
            if *step == 0 {
                return None;
            }
            if let Some(end_val) = end {
                let size = if *step > 0 {
                    if *inclusive {
                        if *current > *end_val {
                            0
                        } else {
                            ((*end_val - *current) / *step + 1) as usize
                        }
                    } else if *current >= *end_val {
                        0
                    } else {
                        ((*end_val - *current - 1) / *step + 1) as usize
                    }
                } else {
                    let step_abs = step.abs();
                    if *inclusive {
                        if *current < *end_val {
                            0
                        } else {
                            ((*current - *end_val) / step_abs + 1) as usize
                        }
                    } else if *current <= *end_val {
                        0
                    } else {
                        ((*current - *end_val - 1) / step_abs + 1) as usize
                    }
                };

                if idx >= size {
                    return None;
                }
            }

            let value = *current + (idx as i64) * *step;
            return Some(Value::from_integer(value));
        }

        // Repeat - infinite, always same value
        LazySeqKind::Repeat { value } => Some(*value),

        // Cycle - infinite if source non-empty
        LazySeqKind::Cycle { source, index } => {
            if source.is_empty() {
                None
            } else {
                let pos = (*index + idx) % source.len();
                Some(source[pos])
            }
        }

        // Iterate - use mutable cached state for forward access
        LazySeqKind::Iterate {
            generator,
            current,
            index: cached_index,
        } => {
            let mut cur_idx = *cached_index.borrow();
            let mut cur_val = *current.borrow();

            if idx < cur_idx {
                return None;
            }

            while cur_idx < idx {
                cur_val = call_value(*generator, &[cur_val]);
                cur_idx += 1;
            }

            *current.borrow_mut() = cur_val;
            *cached_index.borrow_mut() = cur_idx;

            Some(cur_val)
        }

        // Skip - delegate to source with offset
        LazySeqKind::Skip { source, remaining } => lazy_nth(source, remaining + idx),

        // Map - apply mapper to source element
        LazySeqKind::Map { source, mapper } => {
            let val = lazy_nth(source, idx)?;
            Some(call_value(*mapper, &[val]))
        }

        // Filter - iterate until the idx-th matching element
        LazySeqKind::Filter { source, predicate } => {
            let mut count = 0usize;
            let mut current = source.clone();
            loop {
                let (val, next_source) = lazy_next_with_closures(&current)?;
                if call_value(*predicate, &[val]).is_truthy() {
                    if count == idx {
                        return Some(val);
                    }
                    count += 1;
                }
                current = next_source;
            }
        }

        // Zip - nth element from each source
        LazySeqKind::Zip { sources } => {
            let mut tuple = im::Vector::new();
            for src in sources {
                let val = lazy_nth(src, idx)?;
                tuple.push_back(val);
            }
            Some(Value::from_list(tuple))
        }

        // Combinations and other simple kinds - iterate
        _ => {
            let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
            for _ in 0..idx {
                let (_val, next_seq) = lazy_next_with_closures(&current)?;
                current = next_seq;
            }
            let (val, _next_seq) = lazy_next_with_closures(&current)?;
            Some(val)
        }
    }
}

/// Get the next value from any lazy sequence, evaluating closures as needed.
fn lazy_next_with_closures(
    lazy: &LazySequenceObject,
) -> Option<(Value, Box<LazySequenceObject>)> {
    use crate::heap::LazySeqKind;

    match &lazy.kind {
        LazySeqKind::Map { source, mapper } => {
            let (val, next_source) = lazy_next_with_closures(source)?;
            let mapped = call_value(*mapper, &[val]);
            Some((
                mapped,
                LazySequenceObject::new(LazySeqKind::Map {
                    source: next_source,
                    mapper: *mapper,
                }),
            ))
        }
        LazySeqKind::Filter { source, predicate } => {
            let mut current = source.clone();
            loop {
                let (val, next_source) = lazy_next_with_closures(&current)?;
                if call_value(*predicate, &[val]).is_truthy() {
                    return Some((
                        val,
                        LazySequenceObject::new(LazySeqKind::Filter {
                            source: next_source,
                            predicate: *predicate,
                        }),
                    ));
                }
                current = next_source;
            }
        }
        LazySeqKind::FilterMap { source, mapper } => {
            let mut current = source.clone();
            loop {
                let (val, next_source) = lazy_next_with_closures(&current)?;
                let mapped = call_value(*mapper, &[val]);
                if mapped.is_truthy() {
                    return Some((
                        mapped,
                        LazySequenceObject::new(LazySeqKind::FilterMap {
                            source: next_source,
                            mapper: *mapper,
                        }),
                    ));
                }
                current = next_source;
            }
        }
        LazySeqKind::Zip { sources } => {
            let mut values = im::Vector::new();
            let mut next_sources = Vec::with_capacity(sources.len());
            for src in sources {
                let (val, next_src) = lazy_next_with_closures(src)?;
                values.push_back(val);
                next_sources.push(*next_src);
            }
            Some((
                Value::from_list(values),
                LazySequenceObject::new(LazySeqKind::Zip {
                    sources: next_sources,
                }),
            ))
        }
        LazySeqKind::Iterate {
            generator,
            current,
            index,
        } => {
            let cur = *current.borrow();
            let next_val = call_value(*generator, &[cur]);
            *current.borrow_mut() = next_val;
            *index.borrow_mut() += 1;
            Some((
                cur,
                LazySequenceObject::new(LazySeqKind::Iterate {
                    generator: *generator,
                    current: current.clone(),
                    index: index.clone(),
                }),
            ))
        }
        LazySeqKind::Skip { source, remaining } => {
            let mut current = source.clone();
            let mut to_skip = *remaining;
            while to_skip > 0 {
                let (_val, next_source) = lazy_next_with_closures(&current)?;
                current = next_source;
                to_skip -= 1;
            }
            let (val, next_source) = lazy_next_with_closures(&current)?;
            Some((
                val,
                LazySequenceObject::new(LazySeqKind::Skip {
                    source: next_source,
                    remaining: 0,
                }),
            ))
        }
        _ => lazy.next(),
    }
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

    // LazySequence - need to handle different kinds
    if let Some(lazy_seq) = collection.as_lazy_sequence() {
        if is_infinite_lazy_sequence(lazy_seq) {
            runtime_error("size on unbounded lazy sequence");
        }
        use crate::heap::LazySeqKind;

        // Range (bounded only) - calculate size directly without iterating
        if let LazySeqKind::Range {
            current,
            end: Some(end_val),
            inclusive,
            step,
        } = &lazy_seq.kind
        {
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

        // For Map, Filter, Zip - force to list and count
        // (only works for bounded sequences; unbounded would hang)
        let needs_forcing = matches!(
            &lazy_seq.kind,
            LazySeqKind::Map { .. }
                | LazySeqKind::Filter { .. }
                | LazySeqKind::FilterMap { .. }
                | LazySeqKind::Zip { .. }
                | LazySeqKind::Skip { .. }
                | LazySeqKind::Combinations { .. }
        );

        if needs_forcing {
            let elements = collect_bounded_lazy(lazy_seq);
            return Value::from_integer(elements.len() as i64);
        }

        // Unbounded/infinite sequences (Repeat, Cycle, Iterate, unbounded Range)
        runtime_error("size on unbounded lazy sequence");
    }

    runtime_error("size(collection) expects List, Set, Dictionary, String, Range, or LazySequence")
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
        let current: Box<LazySequenceObject> = Box::new(lazy.clone());
        if let Some((val, _)) = lazy_next_with_closures(&current) {
            return val;
        }
        return Value::nil();
    }

    runtime_error("first(collection) expects List, Set, String, Range, or LazySequence")
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
        let current: Box<LazySequenceObject> = Box::new(lazy.clone());
        if let Some((_, next_seq)) = lazy_next_with_closures(&current) {
            if let Some((second_val, _)) = lazy_next_with_closures(&next_seq) {
                return second_val;
            }
        }
        return Value::nil();
    }

    runtime_error("second(collection) expects List, Set, String, Range, or LazySequence")
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
        if is_infinite_lazy_sequence(lazy) {
            runtime_error("last on unbounded lazy sequence");
        }
        use crate::heap::LazySeqKind;
        // For Range, calculate last directly (O(1))
        if let LazySeqKind::Range {
            current,
            end: Some(end_val),
            inclusive,
            step,
        } = &lazy.kind
        {
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
        // For other lazy sequences (including Map, Filter, Zip), collect and get last
        let elements = collect_bounded_lazy(lazy);
        return elements.last().copied().unwrap_or_else(Value::nil);
    }

    runtime_error("last(collection) expects List, Set, String, or bounded Range/LazySequence")
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
        if let Some((_, next_seq)) = lazy_next_with_closures(&Box::new(lazy.clone())) {
            return Value::from_lazy_sequence(next_seq);
        }
        // Empty sequence - return empty list
        return Value::from_list(im::Vector::new());
    }

    runtime_error("rest(collection) expects List, Set, String, Range, or LazySequence")
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

    runtime_error("keys(dictionary) expects Dictionary")
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

    runtime_error("values(dictionary) expects Dictionary")
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

    runtime_error("push(value, collection) expects List or Set")
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
            return Value::from_list(list.clone());
        }
        runtime_error("assoc(key, value, collection) expects Integer index for List");
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

    runtime_error("assoc(key, value, collection) expects List or Dictionary")
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

/// Call any callable value (closure, partial application, memoized closure) with arguments.
/// This is the internal Rust equivalent of rt_call for use within builtins.
pub fn call_value(callee: Value, args: &[Value]) -> Value {
    crate::operations::rt_call(callee, args.len() as u32, args.as_ptr())
}

/// Get the effective arity of any callable value.
/// Returns None if the value is not callable.
pub fn get_callable_arity(callee: &Value) -> Option<u32> {
    if let Some(closure) = callee.as_closure() {
        Some(closure.arity)
    } else if let Some(partial) = callee.as_partial_application() {
        Some(partial.remaining_arity)
    } else if let Some(memoized) = callee.as_memoized_closure() {
        get_callable_arity(&memoized.inner_closure)
    } else {
        None
    }
}

/// Check if a value is callable (closure, partial application, or memoized closure)
pub fn is_callable(callee: &Value) -> bool {
    callee.as_closure().is_some()
        || callee.as_partial_application().is_some()
        || callee.as_memoized_closure().is_some()
}

fn expect_callable_arity(name: &str, callee: &Value) -> u32 {
    get_callable_arity(callee)
        .unwrap_or_else(|| runtime_error(&format!("{name} expects a function")))
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
    if !is_callable(&updater) {
        runtime_error("update(key, updater, collection) expects a function");
    }
    let arity = expect_callable_arity("update(key, updater, collection)", &updater);

    let call_updater = |current: Value| match arity {
        0 => call_value(updater, &[]),
        1 => call_value(updater, &[current]),
        _ => runtime_error("update(key, updater, collection) expects arity 0 or 1"),
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
                let new_value = call_updater(current);

                // Set the new value at index
                new_list.set(idx, new_value);
                return Value::from_list(new_list);
            }
            return Value::from_list(list.clone());
        }
        runtime_error("update(key, updater, collection) expects Integer index for List");
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
        let new_value = call_updater(current);

        // Update the dictionary
        let new_dict = dict.update(key, new_value);
        return Value::from_dict(new_dict);
    }

    runtime_error("update(key, updater, collection) expects List or Dictionary")
}

/// `update_d(key, default, updater, collection)` → Collection
///
/// Update using a pure updater function, with a default value if key doesn't exist.
///
/// Per LANG.txt §11.3:
/// - List: update_d(0, 0, _ + 1, [1, 2]) → [2, 2]; fills with nil at missing indices
/// - Dictionary: update_d(0, 0, _ + 1, #{}) → #{0: 1}
#[no_mangle]
pub extern "C-unwind" fn rt_update_d(
    key: Value,
    default: Value,
    updater: Value,
    collection: Value,
) -> Value {
    if !is_callable(&updater) {
        runtime_error("update_d(key, default, updater, collection) expects a function");
    }
    let arity = expect_callable_arity("update_d(key, default, updater, collection)", &updater);
    let call_updater = |current: Value| match arity {
        0 => call_value(updater, &[]),
        1 => call_value(updater, &[current]),
        _ => runtime_error("update_d(key, default, updater, collection) expects arity 0 or 1"),
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
                let current = if current_raw.is_nil() {
                    default
                } else {
                    current_raw
                };

                // Call updater with current value (or default)
                let new_value = call_updater(current);

                // Set the new value at index
                new_list.set(idx, new_value);
                return Value::from_list(new_list);
            }
            return Value::from_list(list.clone());
        }
        runtime_error("update_d(key, default, updater, collection) expects Integer index for List");
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
        let new_value = call_updater(current);

        // Update the dictionary
        let new_dict = dict.update(key, new_value);
        return Value::from_dict(new_dict);
    }

    runtime_error("update_d(key, default, updater, collection) expects List or Dictionary")
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
    // Check if mapper is callable
    let arity = expect_callable_arity("map(mapper, collection)", &mapper);

    // List → List
    if let Some(list) = collection.as_list() {
        let mapped: im::Vector<Value> = list.iter().map(|v| call_value(mapper, &[*v])).collect();
        return Value::from_list(mapped);
    }

    // Set → Set
    if let Some(set) = collection.as_set() {
        let mut mapped: im::HashSet<Value> = im::HashSet::new();
        for v in set.iter() {
            let new_val = call_value(mapper, &[*v]);
            if !new_val.is_hashable() {
                runtime_error(&format!(
                    "{} is not hashable and cannot be added to a Set",
                    type_name(&new_val)
                ));
            }
            mapped.insert(new_val);
        }
        return Value::from_set(mapped);
    }

    // Dict → Dict (mapper receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = arity >= 2;
        let mapped: im::HashMap<Value, Value> = dict
            .iter()
            .map(|(k, v)| {
                let new_value = if is_two_arg {
                    call_value(mapper, &[*v, *k])
                } else {
                    call_value(mapper, &[*v])
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
                call_value(mapper, &[char_val])
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

    runtime_error("map(mapper, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
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
    // Check if predicate is callable
    let arity = expect_callable_arity("filter(predicate, collection)", &predicate);

    // List → List
    if let Some(list) = collection.as_list() {
        let filtered: im::Vector<Value> = list
            .iter()
            .filter(|v| call_value(predicate, &[**v]).is_truthy())
            .copied()
            .collect();
        return Value::from_list(filtered);
    }

    // Set → Set
    if let Some(set) = collection.as_set() {
        let filtered: im::HashSet<Value> = set
            .iter()
            .filter(|v| call_value(predicate, &[**v]).is_truthy())
            .copied()
            .collect();
        return Value::from_set(filtered);
    }

    // Dict → Dict (predicate receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = arity >= 2;
        let filtered: im::HashMap<Value, Value> = dict
            .iter()
            .filter(|(k, v)| {
                let keep = if is_two_arg {
                    call_value(predicate, &[**v, **k])
                } else {
                    call_value(predicate, &[**v])
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
                if call_value(predicate, &[char_val]).is_truthy() {
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

    runtime_error("filter(predicate, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
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
    if !is_callable(&mapper) {
        runtime_error("flat_map(mapper, collection) expects a function");
    }
    let arity = expect_callable_arity("flat_map(mapper, collection)", &mapper);

    let mut result: im::Vector<Value> = im::Vector::new();

    // Helper to add mapped result elements to result
    let mut extend_result = |mapped: Value| {
        if let Some(list) = mapped.as_list() {
            for v in list.iter() {
                result.push_back(*v);
            }
        } else if let Some(lazy) = mapped.as_lazy_sequence() {
            // Handle lazy sequences (e.g., from map, filter, ranges)
            let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
            while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
                result.push_back(val);
                current = next_seq;
            }
        }
        // If the mapper returns non-collection, we ignore it per spec
    };

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            let mapped = call_value(mapper, &[*v]);
            extend_result(mapped);
        }
        return Value::from_list(result);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            let mapped = call_value(mapper, &[*v]);
            extend_result(mapped);
        }
        return Value::from_list(result);
    }

    // Dict (mapper receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = arity >= 2;
        for (k, v) in dict.iter() {
            let mapped = if is_two_arg {
                call_value(mapper, &[*v, *k])
            } else {
                call_value(mapper, &[*v])
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
            let mapped = call_value(mapper, &[char_val]);
            extend_result(mapped);
        }
        return Value::from_list(result);
    }

    // LazySequence (including Range, Map, Filter, Iterate, etc.)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
            let mapped = call_value(mapper, &[val]);
            extend_result(mapped);
            current = next_seq;
        }
        return Value::from_list(result);
    }

    runtime_error("flat_map(mapper, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
}

/// `filter_map(mapper, collection)` → Collection
///
/// Map and filter in one pass - keeps only truthy mapped results.
/// Returns same collection type (except String → List, Range/LazySequence → LazySequence).
///
/// Per LANG.txt §11.4:
/// - [1, 2, 3, 4] |> filter_map(|v| if v % 2 { v * 2 }) → [2, 6]
/// - 1..5 |> filter_map(|v| if v % 2 { v * 2 }) → [2, 6]  (Range support)
#[no_mangle]
pub extern "C" fn rt_filter_map(mapper: Value, collection: Value) -> Value {
    if !is_callable(&mapper) {
        runtime_error("filter_map(mapper, collection) expects a function");
    }
    let arity = expect_callable_arity("filter_map(mapper, collection)", &mapper);

    // List → List
    if let Some(list) = collection.as_list() {
        let filtered: im::Vector<Value> = list
            .iter()
            .filter_map(|v| {
                let mapped = call_value(mapper, &[*v]);
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
        let mut filtered: im::HashSet<Value> = im::HashSet::new();
        for v in set.iter() {
            let mapped = call_value(mapper, &[*v]);
            if mapped.is_truthy() {
                if !mapped.is_hashable() {
                    runtime_error(&format!(
                        "{} is not hashable and cannot be added to a Set",
                        type_name(&mapped)
                    ));
                }
                filtered.insert(mapped);
            }
        }
        return Value::from_set(filtered);
    }

    // Dict → Dict (mapper receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = arity >= 2;
        let filtered: im::HashMap<Value, Value> = dict
            .iter()
            .filter_map(|(k, v)| {
                let mapped = if is_two_arg {
                    call_value(mapper, &[*v, *k])
                } else {
                    call_value(mapper, &[*v])
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
                let mapped = call_value(mapper, &[char_val]);
                if mapped.is_truthy() {
                    Some(mapped)
                } else {
                    None
                }
            })
            .collect();
        return Value::from_list(filtered);
    }

    // LazySequence (including Range) → LazySequence
    if let Some(lazy) = collection.as_lazy_sequence() {
        let lazy_filter_map = LazySequenceObject::new(LazySeqKind::FilterMap {
            source: Box::new(lazy.clone()),
            mapper,
        });
        return Value::from_lazy_sequence(lazy_filter_map);
    }

    runtime_error(
        "filter_map(mapper, collection) expects List, Set, Dictionary, String, Range, or LazySequence",
    )
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
    if !is_callable(&mapper) {
        runtime_error("find_map(mapper, collection) expects a function");
    }
    let arity = expect_callable_arity("find_map(mapper, collection)", &mapper);

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            let mapped = call_value(mapper, &[*v]);
            if mapped.is_truthy() {
                return mapped;
            }
        }
        return Value::nil();
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            let mapped = call_value(mapper, &[*v]);
            if mapped.is_truthy() {
                return mapped;
            }
        }
        return Value::nil();
    }

    // Dict (mapper receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = arity >= 2;
        for (k, v) in dict.iter() {
            let mapped = if is_two_arg {
                call_value(mapper, &[*v, *k])
            } else {
                call_value(mapper, &[*v])
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
            let mapped = call_value(mapper, &[char_val]);
            if mapped.is_truthy() {
                return mapped;
            }
        }
        return Value::nil();
    }

    // LazySequence (including Range, Map, Filter, Iterate, etc.)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
            let mapped = call_value(mapper, &[val]);
            if mapped.is_truthy() {
                return mapped;
            }
            current = next_seq;
        }
        return Value::nil();
    }

    runtime_error("find_map(mapper, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
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
    use crate::break_handling::{break_occurred, enter_iteration, exit_iteration, take_break_value};

    enter_iteration();
    struct IterationGuard;
    impl Drop for IterationGuard {
        fn drop(&mut self) {
            exit_iteration();
        }
    }
    let _guard = IterationGuard;

    // Check if reducer is callable
    if !is_callable(&reducer) {
        runtime_error("reduce(reducer, collection) expects a function");
    }
    let arity = expect_callable_arity("reduce(reducer, collection)", &reducer);

    // Helper for the common reduction logic
    // Returns None if the collection is empty
    fn do_reduce(
        reducer: Value,
        mut iter: impl Iterator<Item = Value>,
    ) -> Option<Value> {
        // Get first element as initial accumulator
        let mut acc = iter.next()?;

        // Reduce over remaining elements
        for v in iter {
            acc = call_value(reducer, &[acc, v]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return Some(break_val);
                }
                return Some(acc);
            }
        }

        Some(acc)
    }

    // List
    if let Some(list) = collection.as_list() {
        return match do_reduce(reducer, list.iter().copied()) {
            Some(v) => v,
            None => runtime_error("reduce on empty collection"),
        };
    }

    // Set
    if let Some(set) = collection.as_set() {
        return match do_reduce(reducer, set.iter().copied()) {
            Some(v) => v,
            None => runtime_error("reduce on empty collection"),
        };
    }

    // Dict (reducer receives acc, value, or acc, value, key for 3-arg)
    if let Some(dict) = collection.as_dict() {
        let is_three_arg = arity >= 3;
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
                call_value(reducer, &[acc, *v, *k])
            } else {
                call_value(reducer, &[acc, *v])
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
        let graphemes: Vec<_> = s.graphemes(true).collect();
        if graphemes.is_empty() {
            runtime_error("reduce on empty collection");
        }

        let mut acc = Value::from_string(graphemes[0].to_string());
        for g in &graphemes[1..] {
            let char_val = Value::from_string((*g).to_string());
            acc = call_value(reducer, &[acc, char_val]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return acc;
            }
        }

        return acc;
    }

    // LazySequence - reduce lazily to support unbounded sequences with break
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        let (first_val, next_seq) = match lazy_next_with_closures(&current) {
            Some(v) => v,
            None => runtime_error("reduce on empty collection"),
        };
        let mut acc = first_val;
        current = next_seq;

        while let Some((val, next_lazy)) = lazy_next_with_closures(&current) {
            acc = call_value(reducer, &[acc, val]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return acc;
            }
            current = next_lazy;
        }

        return acc;
    }

    runtime_error("reduce(reducer, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
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
    use crate::break_handling::{break_occurred, enter_iteration, exit_iteration, take_break_value};

    // Enter iteration context and reset break state
    enter_iteration();
    struct IterationGuard;
    impl Drop for IterationGuard {
        fn drop(&mut self) {
            exit_iteration();
        }
    }
    let _guard = IterationGuard;

    if !is_callable(&folder) {
        runtime_error("fold(initial, folder, collection) expects a function");
    }
    let arity = expect_callable_arity("fold(initial, folder, collection)", &folder);

    let mut acc = initial;

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            acc = call_value(folder, &[acc, *v]);
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
            acc = call_value(folder, &[acc, *v]);
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
        let is_three_arg = arity >= 3;
        for (k, v) in dict.iter() {
            acc = if is_three_arg {
                call_value(folder, &[acc, *v, *k])
            } else {
                call_value(folder, &[acc, *v])
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
            acc = call_value(folder, &[acc, char_val]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return acc;
            }
        }
        return acc;
    }

    // LazySequence - iterate lazily for all variants
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_lazy)) = lazy_next_with_closures(&current) {
            acc = call_value(folder, &[acc, val]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return acc;
            }
            current = next_lazy;
        }
        return acc;
    }

    runtime_error("fold(initial, folder, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
}

/// `scan(initial, folder, collection)` → List
///
/// Return all intermediate fold results as a list.
/// The initial value is included as the first element (matching reference implementations).
///
/// - scan(0, +, [1, 2]) → [0, 1, 3]
#[no_mangle]
pub extern "C" fn rt_scan(initial: Value, folder: Value, collection: Value) -> Value {
    if !is_callable(&folder) {
        runtime_error("scan(initial, folder, collection) expects a function");
    }
    let arity = expect_callable_arity("scan(initial, folder, collection)", &folder);

    let mut acc = initial;
    let mut results: im::Vector<Value> = im::Vector::new();

    // Include initial value as first element (per reference implementations)
    results.push_back(acc);

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            acc = call_value(folder, &[acc, *v]);
            results.push_back(acc);
        }
        return Value::from_list(results);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            acc = call_value(folder, &[acc, *v]);
            results.push_back(acc);
        }
        return Value::from_list(results);
    }

    // Dict (folder receives acc, value, or acc, value, key for 3-arg)
    if let Some(dict) = collection.as_dict() {
        let is_three_arg = arity >= 3;
        for (k, v) in dict.iter() {
            acc = if is_three_arg {
                call_value(folder, &[acc, *v, *k])
            } else {
                call_value(folder, &[acc, *v])
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
            acc = call_value(folder, &[acc, char_val]);
            results.push_back(acc);
        }
        return Value::from_list(results);
    }

    // LazySequence - only bounded ranges are supported per LANG.txt
    if let Some(lazy) = collection.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        match &lazy.kind {
            LazySeqKind::Range { end: Some(_), .. } => {
                let mut current = lazy.clone();
                while let Some((val, next_lazy)) = current.next() {
                    acc = call_value(folder, &[acc, val]);
                    results.push_back(acc);
                    current = *next_lazy;
                }
                return Value::from_list(results);
            }
            LazySeqKind::Range { end: None, .. } => {
                runtime_error("scan does not support unbounded ranges");
            }
            _ => {
                runtime_error("scan does not support lazy sequences");
            }
        }
    }

    runtime_error("scan(initial, folder, collection) expects List, Set, Dictionary, String, or Range")
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
    if !is_callable(&folder) {
        runtime_error("fold_s(initial, folder, collection) expects a function");
    }
    let arity = expect_callable_arity("fold_s(initial, folder, collection)", &folder);

    let mut acc = initial;

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            acc = call_value(folder, &[acc, *v]);
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
            acc = call_value(folder, &[acc, *v]);
        }
        if let Some(state_list) = acc.as_list() {
            return state_list.front().copied().unwrap_or_else(Value::nil);
        }
        return acc;
    }

    // Dict
    if let Some(dict) = collection.as_dict() {
        let is_three_arg = arity >= 3;
        for (k, v) in dict.iter() {
            acc = if is_three_arg {
                call_value(folder, &[acc, *v, *k])
            } else {
                call_value(folder, &[acc, *v])
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
            acc = call_value(folder, &[acc, char_val]);
        }
        if let Some(state_list) = acc.as_list() {
            return state_list.front().copied().unwrap_or_else(Value::nil);
        }
        return acc;
    }

    // LazySequence (including Ranges) - iterate through the sequence
    // WARNING: Unbounded sequences will loop forever unless break is used
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_lazy)) = lazy_next_with_closures(&current) {
            acc = call_value(folder, &[acc, val]);
            current = next_lazy;
        }
        if let Some(state_list) = acc.as_list() {
            return state_list.front().copied().unwrap_or_else(Value::nil);
        }
        return acc;
    }

    runtime_error("fold_s(initial, folder, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
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
    if !is_callable(&predicate) {
        runtime_error("find(predicate, collection) expects a function");
    }
    let arity = expect_callable_arity("find(predicate, collection)", &predicate);

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            if call_value(predicate, &[*v]).is_truthy() {
                return *v;
            }
        }
        return Value::nil();
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            if call_value(predicate, &[*v]).is_truthy() {
                return *v;
            }
        }
        return Value::nil();
    }

    // Dict (predicate receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = arity >= 2;
        for (k, v) in dict.iter() {
            let matches = if is_two_arg {
                call_value(predicate, &[*v, *k])
            } else {
                call_value(predicate, &[*v])
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
            if call_value(predicate, &[char_val]).is_truthy() {
                return Value::from_string(g.to_string());
            }
        }
        return Value::nil();
    }

    // LazySequence (including Range, Map, Filter, etc.)
    if let Some(lazy) = collection.as_lazy_sequence() {
        return find_in_lazy(lazy, predicate);
    }

    runtime_error("find(predicate, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
}

/// Helper to find first matching element in any lazy sequence
/// Handles all lazy sequence variants including Map, Filter, and Iterate
fn find_in_lazy(lazy: &LazySequenceObject, predicate: Value) -> Value {
    let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
    while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
        if call_value(predicate, &[val]).is_truthy() {
            return val;
        }
        current = next_seq;
    }
    Value::nil()
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
    if !is_callable(&predicate) {
        runtime_error("count(predicate, collection) expects a function");
    }
    let arity = expect_callable_arity("count(predicate, collection)", &predicate);

    let mut count: i64 = 0;

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            if call_value(predicate, &[*v]).is_truthy() {
                count += 1;
            }
        }
        return Value::from_integer(count);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            if call_value(predicate, &[*v]).is_truthy() {
                count += 1;
            }
        }
        return Value::from_integer(count);
    }

    // Dict (predicate receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = arity >= 2;
        for (k, v) in dict.iter() {
            let matches = if is_two_arg {
                call_value(predicate, &[*v, *k])
            } else {
                call_value(predicate, &[*v])
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
            if call_value(predicate, &[char_val]).is_truthy() {
                count += 1;
            }
        }
        return Value::from_integer(count);
    }

    // LazySequence (Range only)
    if let Some(lazy) = collection.as_lazy_sequence() {
        return Value::from_integer(count_in_lazy(lazy, predicate));
    }

    runtime_error("count(predicate, collection) expects List, Set, Dictionary, String, or Range")
}

/// Helper to count matching elements in any lazy sequence
/// Handles all lazy sequence variants including Map, Filter, and Iterate
fn count_in_lazy(lazy: &LazySequenceObject, predicate: Value) -> i64 {
    let mut count: i64 = 0;

    match &lazy.kind {
        LazySeqKind::Range {
            current,
            end,
            inclusive,
            step,
        } => {
            let end_val = match end {
                Some(v) => *v,
                None => runtime_error("count does not support unbounded ranges"),
            };
            let mut cur = *current;
            loop {
                let at_end = if *inclusive {
                    if *step > 0 {
                        cur > end_val
                    } else {
                        cur < end_val
                    }
                } else if *step > 0 {
                    cur >= end_val
                } else {
                    cur <= end_val
                };
                if at_end {
                    return count;
                }
                let val = Value::from_integer(cur);
                if call_value(predicate, &[val]).is_truthy() {
                    count += 1;
                }
                cur += step;
            }
        }
        _ => runtime_error("count does not support lazy sequences"),
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
pub extern "C-unwind" fn rt_sum(collection: Value) -> Value {
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
        } else {
            runtime_error(&format!(
                "sum expects numeric elements, got {}",
                type_name(&v)
            ));
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
        if is_infinite_lazy_sequence(lazy) {
            runtime_error("sum on unbounded lazy sequence");
        }
        use crate::heap::LazySeqKind;
        // For Range, use arithmetic sequence sum formula: sum = n * (first + last) / 2
        if let LazySeqKind::Range {
            current,
            end: Some(end_val),
            inclusive,
            step,
        } = &lazy.kind
        {
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

        // For other lazy sequences (including Map, Filter, Zip which need closure evaluation),
        // use collect_bounded_lazy which handles all variants properly
        let elements = collect_bounded_lazy(lazy);
        for v in elements.iter() {
            add_value(*v);
        }
        return if has_decimal {
            Value::from_decimal(int_sum as f64 + dec_sum)
        } else {
            Value::from_integer(int_sum)
        };
    }

    runtime_error("sum(collection) expects List, Set, Dictionary, Range, or LazySequence")
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

fn compare_or_error(op: &str, a: Value, b: Value) -> std::cmp::Ordering {
    match compare_values(a, b) {
        Some(order) => order,
        None => runtime_error(&format!(
            "{op} expects comparable elements, got {} and {}",
            type_name(&a),
            type_name(&b)
        )),
    }
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
pub extern "C-unwind" fn rt_max(collection: Value) -> Value {
    use std::cmp::Ordering;

    let mut max_val: Option<Value> = None;

    let mut update_max = |v: Value| match max_val {
        None => {
            compare_or_error("max", v, v);
            max_val = Some(v)
        }
        Some(current) => {
            if let Ordering::Greater = compare_or_error("max", v, current) {
                max_val = Some(v);
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
        if is_infinite_lazy_sequence(lazy) {
            runtime_error("max on unbounded lazy sequence");
        }
        use crate::heap::LazySeqKind;
        // For Range, max is first (descending) or last (ascending)
        if let LazySeqKind::Range {
            current,
            end: Some(end_val),
            inclusive,
            step,
        } = &lazy.kind
        {
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

        // For other lazy sequences (including Map, Filter, Zip), collect and iterate
        let elements = collect_bounded_lazy(lazy);
        for v in elements.iter() {
            update_max(*v);
        }
        return max_val.unwrap_or_else(Value::nil);
    }

    runtime_error("max(collection) expects List, Set, Dictionary, Range, or LazySequence")
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
pub extern "C-unwind" fn rt_min(collection: Value) -> Value {
    use std::cmp::Ordering;

    let mut min_val: Option<Value> = None;

    let mut update_min = |v: Value| match min_val {
        None => {
            compare_or_error("min", v, v);
            min_val = Some(v)
        }
        Some(current) => {
            if let Ordering::Less = compare_or_error("min", v, current) {
                min_val = Some(v);
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
        if is_infinite_lazy_sequence(lazy) {
            runtime_error("min on unbounded lazy sequence");
        }
        use crate::heap::LazySeqKind;
        // For Range, min is first (ascending) or last (descending)
        if let LazySeqKind::Range {
            current,
            end: Some(end_val),
            inclusive,
            step,
        } = &lazy.kind
        {
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

        // For other lazy sequences (including Map, Filter, Zip), collect and iterate
        let elements = collect_bounded_lazy(lazy);
        for v in elements.iter() {
            update_min(*v);
        }
        return min_val.unwrap_or_else(Value::nil);
    }

    runtime_error("min(collection) expects List, Set, Dictionary, Range, or LazySequence")
}

/// `max(a, b)` → Maximum of two values
///
/// Returns the larger of two values.
#[no_mangle]
pub extern "C-unwind" fn rt_max2(a: Value, b: Value) -> Value {
    use std::cmp::Ordering;
    match compare_values(a, b) {
        Some(Ordering::Greater) | Some(Ordering::Equal) => a,
        Some(Ordering::Less) => b,
        None => runtime_error(&format!(
            "max expects comparable elements, got {} and {}",
            type_name(&a),
            type_name(&b)
        )),
    }
}

/// `min(a, b)` → Minimum of two values
///
/// Returns the smaller of two values.
#[no_mangle]
pub extern "C-unwind" fn rt_min2(a: Value, b: Value) -> Value {
    use std::cmp::Ordering;
    match compare_values(a, b) {
        Some(Ordering::Less) | Some(Ordering::Equal) => a,
        Some(Ordering::Greater) => b,
        None => runtime_error(&format!(
            "min expects comparable elements, got {} and {}",
            type_name(&a),
            type_name(&b)
        )),
    }
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
pub extern "C-unwind" fn rt_skip(total: Value, collection: Value) -> Value {
    let n = total
        .as_integer()
        .unwrap_or_else(|| runtime_error("skip(total, collection) expects Integer total"))
        as usize;

    // List - use split_off for O(log n) instead of O(n) iterator
    if let Some(list) = collection.as_list() {
        if n >= list.len() {
            return Value::from_list(im::Vector::new());
        }
        // split_off gives us [n..] in O(log n) time
        let result = list.clone().split_off(n);
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
        if let LazySeqKind::Range {
            current,
            end,
            inclusive,
            step,
        } = &lazy.kind
        {
            let new_start = current + (n as i64) * step;
            // Check if skip moved past the end - return empty range instead of invalid one
            if let Some(end_val) = end {
                let past_end = if *step > 0 {
                    if *inclusive {
                        new_start > *end_val
                    } else {
                        new_start >= *end_val
                    }
                } else if *inclusive {
                    new_start < *end_val
                } else {
                    new_start <= *end_val
                };
                if past_end {
                    // Return an empty range (start == end, exclusive)
                    return Value::from_lazy_sequence(LazySequenceObject::new(
                        LazySeqKind::Range {
                            current: 0,
                            end: Some(0),
                            inclusive: false,
                            step: 1,
                        },
                    ));
                }
            }
            return Value::from_lazy_sequence(LazySequenceObject::range(
                new_start, *end, *inclusive, *step,
            ));
        }

        // For other lazy sequences, use Skip wrapper
        return Value::from_lazy_sequence(LazySequenceObject::new(LazySeqKind::Skip {
            source: Box::new(lazy.clone()),
            remaining: n,
        }));
    }

    runtime_error("skip(total, collection) expects List, Set, Range, or LazySequence")
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
pub extern "C-unwind" fn rt_take(total: Value, collection: Value) -> Value {
    let n = total
        .as_integer()
        .unwrap_or_else(|| runtime_error("take(total, collection) expects Integer total"))
        as usize;

    // List - use take for O(log n) instead of O(n) iterator
    if let Some(list) = collection.as_list() {
        if n >= list.len() {
            return Value::from_list(list.clone());
        }
        // take(n) gives us [0..n] in O(log n) time for im::Vector
        let result = list.take(n);
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

    runtime_error("take(total, collection) expects List, Set, Range, or LazySequence")
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
/// - sort(|a, b| a % 2 < b % 2, [1, 2, 3, 4]) → [2, 4, 1, 3]
#[no_mangle]
pub extern "C-unwind" fn rt_sort(comparator: Value, collection: Value) -> Value {
    if !is_callable(&comparator) {
        runtime_error("sort(comparator, collection) expects a function");
    }

    // Helper to sort items - uses call_value to handle all callable types
    let sort_items = |items: &mut Vec<Value>| {
        items.sort_by(|a, b| {
            let result = call_value(comparator, &[*a, *b]);

            // Check if result is boolean
            if let Some(bool_val) = result.as_bool() {
                // When comparator returns true, a should come AFTER b (to match Comet behavior)
                // This gives: sort(<, [3,1,2]) → [3,2,1] (descending)
                //             sort(>, [1,2,3]) → [1,2,3] (ascending)
                if bool_val {
                    std::cmp::Ordering::Greater
                } else {
                    std::cmp::Ordering::Less
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

    if let Some(list) = collection.as_list() {
        let mut items: Vec<Value> = list.iter().copied().collect();
        sort_items(&mut items);
        return Value::from_list(items.into_iter().collect());
    }
    runtime_error("sort(comparator, collection) expects List")
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
pub extern "C-unwind" fn rt_reverse(collection: Value) -> Value {
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

    // Range (bounded only) - collect and reverse
    if let Some(lazy) = collection.as_lazy_sequence() {
        match &lazy.kind {
            LazySeqKind::Range { end: Some(_), .. } => {}
            LazySeqKind::Range { end: None, .. } => {
                runtime_error("reverse on unbounded range");
            }
            _ => {
                runtime_error("reverse(collection) expects List, String, or Range");
            }
        }

        let mut elements: Vec<Value> = Vec::new();
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
            elements.push(val);
            current = next_seq;
        }
        elements.reverse();
        return Value::from_list(elements.into_iter().collect());
    }

    runtime_error("reverse(collection) expects List, String, or Range")
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
pub extern "C-unwind" fn rt_rotate(steps: Value, collection: Value) -> Value {
    let n = steps
        .as_integer()
        .unwrap_or_else(|| runtime_error("rotate(steps, collection) expects Integer steps"));

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

    runtime_error("rotate(steps, collection) expects List")
}

/// `chunk(size, collection)` → List[List]
///
/// Split into chunks of given size. Last chunk may be smaller.
///
/// Per LANG.txt §11.9:
/// - chunk(2, [1, 2, 3]) → [[1, 2], [3]]
/// - chunk(2, [1, 2, 3, 4]) → [[1, 2], [3, 4]]
#[no_mangle]
pub extern "C-unwind" fn rt_chunk(size: Value, collection: Value) -> Value {
    let chunk_size = size
        .as_integer()
        .unwrap_or_else(|| runtime_error("chunk(size, collection) expects Integer size"));
    if chunk_size <= 0 {
        runtime_error("chunk(size, collection) expects size > 0");
    }
    let chunk_size = chunk_size as usize;

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

    // String - split into chunks of grapheme clusters
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        let graphemes: Vec<&str> = s.graphemes(true).collect();
        let mut chunks: im::Vector<Value> = im::Vector::new();

        for chunk in graphemes.chunks(chunk_size) {
            let chunk_str: String = chunk.concat();
            chunks.push_back(Value::from_string(&chunk_str));
        }

        return Value::from_list(chunks);
    }

    runtime_error("chunk(size, collection) expects List or String")
}

// ============================================================================
// §11.10 Set Operations
// ============================================================================

/// Helper: extract elements from a collection as an iterator
/// Per LANG.txt §11.10, supports List, Set, Range, String
fn collect_elements(v: Value) -> Vec<Value> {
    let elements: Vec<Value> = if let Some(list) = v.as_list() {
        list.iter().copied().collect()
    } else if let Some(set) = v.as_set() {
        set.iter().copied().collect()
    } else if let Some(lazy) = v.as_lazy_sequence() {
        use crate::heap::LazySeqKind;
        // Check for unbounded ranges first
        if let LazySeqKind::Range { end: None, .. } = &lazy.kind {
            runtime_error("set operations do not support unbounded ranges");
        }
        // Collect all elements from the lazy sequence (including Map, Filter, etc.)
        let mut result = Vec::new();
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
            result.push(val);
            current = next_seq;
        }
        result
    } else if let Some(s) = v.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        s.graphemes(true)
            .map(|g| Value::from_string(g.to_string()))
            .collect()
    } else {
        runtime_error("set operations expect List, Set, String, LazySequence, or Range");
    };

    elements
}

/// Helper: check that all elements are hashable before inserting into a set
fn check_hashable(elements: &[Value]) {
    for elem in elements {
        if !elem.is_hashable() {
            runtime_error(&format!(
                "{} is not hashable and cannot be added to a Set",
                type_name(elem)
            ));
        }
    }
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

    let elems1 = collect_elements(collection1);
    check_hashable(&elems1);
    for v in elems1 {
        result.insert(v);
    }
    let elems2 = collect_elements(collection2);
    check_hashable(&elems2);
    for v in elems2 {
        result.insert(v);
    }

    Value::from_set(result)
}

/// `union(..collections)` → Set
///
/// Elements found in any of the provided collections.
/// Can be called with multiple arguments (packaged as a list) or a single list of collections.
///
/// Per LANG.txt §11.10:
/// - union({1, 2}, [2, 3], 1..4) → {1, 2, 3}
/// - union([{1, 2}, [2, 3], 1..4]) → {1, 2, 3}
#[no_mangle]
pub extern "C" fn rt_union_all(collections: Value) -> Value {
    // Get the list of collections
    let list = match collections.as_list() {
        Some(l) => l,
        None => {
            // Single non-list value - return its elements as a set
            let elems = collect_elements(collections);
            check_hashable(&elems);
            return Value::from_set(elems.into_iter().collect());
        }
    };

    if list.is_empty() {
        return Value::from_set(im::HashSet::new());
    }

    // Check if this is a single list of collections or multiple collections
    // If there's one element and it's a list/set/lazy, treat it as a list of collections
    let collections_to_union: Vec<Value> = if list.len() == 1 {
        let first = list[0];
        if first.as_list().is_some()
            || first.as_set().is_some()
            || first.as_lazy_sequence().is_some()
        {
            // Single argument that is a collection - check if it contains collections
            let elements: Vec<Value> = collect_elements(first);
            // Check if first element is itself a collection
            if !elements.is_empty()
                && (elements[0].as_list().is_some()
                    || elements[0].as_set().is_some()
                    || elements[0].as_lazy_sequence().is_some())
            {
                // It's a list of collections - use the elements as collections
                elements
            } else {
                // Single collection - just return its elements as a set
                check_hashable(&elements);
                return Value::from_set(elements.into_iter().collect());
            }
        } else {
            // Single non-collection argument
            let elems = collect_elements(first);
            check_hashable(&elems);
            return Value::from_set(elems.into_iter().collect());
        }
    } else {
        // Multiple arguments - use them directly
        list.iter().copied().collect()
    };

    // Union all collections
    let mut result: im::HashSet<Value> = im::HashSet::new();
    for coll in collections_to_union {
        let elems = collect_elements(coll);
        check_hashable(&elems);
        for elem in elems {
            result.insert(elem);
        }
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
    let elems1 = collect_elements(collection1);
    check_hashable(&elems1);
    let set1: im::HashSet<Value> = elems1.into_iter().collect();
    let elems2 = collect_elements(collection2);
    check_hashable(&elems2);
    let set2: im::HashSet<Value> = elems2.into_iter().collect();

    // Find common elements
    let result: im::HashSet<Value> = set1.iter().filter(|v| set2.contains(*v)).copied().collect();

    Value::from_set(result)
}

/// `intersection(..collections)` → Set
///
/// Elements found in all of the provided collections.
/// Can be called with multiple arguments (packaged as a list) or a single list of collections.
///
/// Per LANG.txt §11.10:
/// - intersection({1, 2}, [2, 3], 1..4) → {2}
/// - intersection([{1, 2}, [2, 3], 1..4]) → {2}
#[no_mangle]
pub extern "C" fn rt_intersection_all(collections: Value) -> Value {
    // Get the list of collections
    let list = match collections.as_list() {
        Some(l) => l,
        None => return Value::from_set(im::HashSet::new()),
    };

    if list.is_empty() {
        return Value::from_set(im::HashSet::new());
    }

    // Check if this is a single list of collections or multiple collections
    // If there's one element and it's a list, treat it as a list of collections
    let collections_to_intersect: Vec<Value> = if list.len() == 1 {
        if let Some(inner_list) = list[0].as_list() {
            // Single argument that is a list - treat as list of collections
            inner_list.iter().copied().collect()
        } else {
            // Single non-list argument - just return its elements as a set
            return Value::from_set(collect_elements(list[0]).into_iter().collect());
        }
    } else {
        // Multiple arguments - use them directly
        list.iter().copied().collect()
    };

    if collections_to_intersect.is_empty() {
        return Value::from_set(im::HashSet::new());
    }

    // Start with the first collection
    let mut result: im::HashSet<Value> = collect_elements(collections_to_intersect[0])
        .into_iter()
        .collect();

    // Intersect with each subsequent collection
    for coll in collections_to_intersect.iter().skip(1) {
        let other: im::HashSet<Value> = collect_elements(*coll).into_iter().collect();
        result = result
            .iter()
            .filter(|v| other.contains(*v))
            .copied()
            .collect();
    }

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
        if let LazySeqKind::Range {
            current,
            end: Some(end_val),
            inclusive,
            step,
        } = &lazy.kind
        {
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
        // Fall back to lazy iteration for all lazy sequence kinds
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
            if val == value {
                return Value::from_bool(true);
            }
            current = next_seq;
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
    if !is_callable(&predicate) {
        runtime_error("any?(predicate, collection) expects a function");
    }
    let _arity = expect_callable_arity("any?(predicate, collection)", &predicate);

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            if call_value(predicate, &[*v]).is_truthy() {
                return Value::from_bool(true);
            }
        }
        return Value::from_bool(false);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            if call_value(predicate, &[*v]).is_truthy() {
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
            if call_value(predicate, &[char_val]).is_truthy() {
                return Value::from_bool(true);
            }
        }
        return Value::from_bool(false);
    }

    // LazySequence (including Range, Map, Filter, Zip, Iterate)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
            if call_value(predicate, &[val]).is_truthy() {
                return Value::from_bool(true);
            }
            current = next_seq;
        }
        return Value::from_bool(false);
    }

    runtime_error("any?(predicate, collection) expects List, Set, String, Range, or LazySequence")
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
    if !is_callable(&predicate) {
        runtime_error("all?(predicate, collection) expects a function");
    }
    let _arity = expect_callable_arity("all?(predicate, collection)", &predicate);

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            if !call_value(predicate, &[*v]).is_truthy() {
                return Value::from_bool(false);
            }
        }
        return Value::from_bool(true);
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            if !call_value(predicate, &[*v]).is_truthy() {
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
            if !call_value(predicate, &[char_val]).is_truthy() {
                return Value::from_bool(false);
            }
        }
        return Value::from_bool(true);
    }

    // LazySequence (including Range, Map, Filter, Zip, Iterate)
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
            if !call_value(predicate, &[val]).is_truthy() {
                return Value::from_bool(false);
            }
            current = next_seq;
        }
        return Value::from_bool(true);
    }

    // Dict (iterates over values, or (value, key) for 2-arg predicates)
    if let Some(dict) = collection.as_dict() {
        let arity = expect_callable_arity("all?(predicate, collection)", &predicate);
        let is_two_arg = arity >= 2;
        for (k, v) in dict.iter() {
            let result = if is_two_arg {
                call_value(predicate, &[*v, *k])
            } else {
                call_value(predicate, &[*v])
            };
            if !result.is_truthy() {
                return Value::from_bool(false);
            }
        }
        return Value::from_bool(true);
    }

    runtime_error("all?(predicate, collection) expects List, Set, String, Range, LazySequence, or Dictionary")
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
    use crate::break_handling::{break_occurred, enter_iteration, exit_iteration, take_break_value};

    enter_iteration();
    struct IterationGuard;
    impl Drop for IterationGuard {
        fn drop(&mut self) {
            exit_iteration();
        }
    }
    let _guard = IterationGuard;

    if !is_callable(&side_effect) {
        runtime_error("each(side_effect, collection) expects a function");
    }
    let arity = expect_callable_arity("each(side_effect, collection)", &side_effect);

    // List
    if let Some(list) = collection.as_list() {
        for v in list.iter() {
            call_value(side_effect, &[*v]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return Value::nil();
            }
        }
        return Value::nil();
    }

    // Set
    if let Some(set) = collection.as_set() {
        for v in set.iter() {
            call_value(side_effect, &[*v]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return Value::nil();
            }
        }
        return Value::nil();
    }

    // Dict (callback receives value, or (value, key) for 2-arg)
    if let Some(dict) = collection.as_dict() {
        let is_two_arg = arity >= 2;
        for (k, v) in dict.iter() {
            if is_two_arg {
                call_value(side_effect, &[*v, *k]);
            } else {
                call_value(side_effect, &[*v]);
            }
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return Value::nil();
            }
        }
        return Value::nil();
    }

    // String (each grapheme)
    if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        for g in s.graphemes(true) {
            let char_val = Value::from_string(g.to_string());
            call_value(side_effect, &[char_val]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return Value::nil();
            }
        }
        return Value::nil();
    }

    // LazySequence (including Ranges) - iterate through the sequence
    // WARNING: Unbounded sequences will loop forever
    if let Some(lazy) = collection.as_lazy_sequence() {
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_lazy)) = lazy_next_with_closures(&current) {
            call_value(side_effect, &[val]);
            if break_occurred() {
                if let Some(break_val) = take_break_value() {
                    return break_val;
                }
                return Value::nil();
            }
            current = next_lazy;
        }
        return Value::nil();
    }

    runtime_error("each(side_effect, collection) expects List, Set, Dictionary, String, Range, or LazySequence")
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
pub extern "C-unwind" fn rt_cycle(collection: Value) -> Value {
    // Get elements from collection as a Vector
    let source = if let Some(list) = collection.as_list() {
        list.clone()
    } else if let Some(s) = collection.as_string() {
        use unicode_segmentation::UnicodeSegmentation;
        s.graphemes(true)
            .map(|g| Value::from_string(g.to_string()))
            .collect()
    } else {
        runtime_error("cycle(collection) expects List or String");
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
pub extern "C-unwind" fn rt_combinations(size: Value, collection: Value) -> Value {
    let k = size
        .as_integer()
        .unwrap_or_else(|| runtime_error("combinations(size, collection) expects Integer size"))
        as usize;

    // Get elements from collection
    let source: Vec<Value> = if let Some(list) = collection.as_list() {
        list.iter().copied().collect()
    } else {
        runtime_error("combinations(size, collection) expects List");
    };

    if k == 0 || k > source.len() {
        return Value::from_lazy_sequence(LazySequenceObject::new(LazySeqKind::Combinations {
            source,
            size: k,
            indices: vec![],
            done: true,
        }));
    }

    // Initialize indices for first combination
    let indices: Vec<usize> = (0..k).collect();

    Value::from_lazy_sequence(LazySequenceObject::new(LazySeqKind::Combinations {
        source,
        size: k,
        indices,
        done: false,
    }))
}

/// `range(from, to, step)` → LazySequence
///
/// Generate a range sequence with custom step.
/// Unlike `..` and `..=` syntax, this always returns a LazySequence.
///
/// Per LANG.txt §11.13:
/// - range(0, 10, 2) |> list → [0, 2, 4, 6, 8, 10] (inclusive)
#[no_mangle]
pub extern "C" fn rt_range_fn(from: Value, to: Value, step: Value) -> Value {
    let start = from.as_integer().unwrap_or_else(|| {
        runtime_error("range(from, to, step) expects Integer for 'from'")
    });
    let end = to
        .as_integer()
        .unwrap_or_else(|| runtime_error("range(from, to, step) expects Integer for 'to'"));
    let step_val = step
        .as_integer()
        .unwrap_or_else(|| runtime_error("range(from, to, step) expects Integer for 'step'"));

    if step_val == 0 {
        runtime_error("range(from, to, step) requires non-zero step");
    }

    // Validate step direction unless start == end
    if start != end {
        if (end > start && step_val < 0) || (end < start && step_val > 0) {
            runtime_error("range(from, to, step) step direction does not match range");
        }
    }

    // Per LANG.txt §11.13, range(from, to, step) is inclusive of 'to'
    let lazy = LazySequenceObject::range(start, Some(end), true, step_val);
    Value::from_lazy_sequence(lazy)
}

/// `start..end` → LazySequence (exclusive range)
///
/// Create an exclusive range from start to end (end not included).
/// Called by codegen for range syntax.
#[no_mangle]
pub extern "C" fn rt_range_exclusive(start: Value, end: Value) -> Value {
    let start_val = start
        .as_integer()
        .unwrap_or_else(|| runtime_error("range start expects Integer"));
    let end_val = end
        .as_integer()
        .unwrap_or_else(|| runtime_error("range end expects Integer"));

    // Determine step based on direction
    let step = if end_val < start_val {
            -1
        } else {
            1
        };

    let lazy = LazySequenceObject::range(start_val, Some(end_val), false, step);
    Value::from_lazy_sequence(lazy)
}

/// `start..=end` → LazySequence (inclusive range)
///
/// Create an inclusive range from start to end (end included).
/// Called by codegen for inclusive range syntax.
#[no_mangle]
pub extern "C" fn rt_range_inclusive(start: Value, end: Value) -> Value {
    let start_val = start
        .as_integer()
        .unwrap_or_else(|| runtime_error("range start expects Integer"));
    let end_val = end
        .as_integer()
        .unwrap_or_else(|| runtime_error("range end expects Integer"));

    // Determine step based on direction
    let step = if end_val < start_val {
            -1
        } else {
            1
        };

    let lazy = LazySequenceObject::range(start_val, Some(end_val), true, step);
    Value::from_lazy_sequence(lazy)
}

/// `start..` → LazySequence (unbounded range)
///
/// Create an unbounded range starting from start.
/// Called by codegen for infinite range syntax.
#[no_mangle]
pub extern "C" fn rt_range_unbounded(start: Value) -> Value {
    let start_val = start
        .as_integer()
        .unwrap_or_else(|| runtime_error("range start expects Integer"));
    let lazy = LazySequenceObject::range(start_val, None, false, 1);
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
    let all_infinite = args.iter().all(|v| {
        v.as_lazy_sequence()
            .map(is_infinite_lazy_sequence)
            .unwrap_or(false)
    });

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
    let min_finite_len = args.iter().filter_map(get_finite_length).min().unwrap_or(0);

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

/// zip with spread - takes a collection of collections and zips them
#[no_mangle]
pub extern "C" fn rt_zip_spread(collection: Value) -> Value {
    // Extract elements from the collection
    let args: Vec<Value> = if let Some(list) = collection.as_list() {
        list.iter().copied().collect()
    } else if let Some(lazy) = collection.as_lazy_sequence() {
        if is_infinite_lazy_sequence(lazy) {
            runtime_error("Cannot spread unbounded lazy sequence");
        }
        // Materialize lazy sequence
        let mut result = Vec::new();
        let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
        while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
            result.push(val);
            current = next_seq;
        }
        result
    } else {
        // Single element - wrap in vec
        vec![collection]
    };

    // Call rt_zip with the extracted elements
    rt_zip(args.len() as u32, args.as_ptr())
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
        LazySeqKind::Range {
            current,
            end,
            inclusive,
            step,
        } => {
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
        LazySeqKind::Map { source, .. }
        | LazySeqKind::Filter { source, .. }
        | LazySeqKind::FilterMap { source, .. } => {
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
pub fn collect_bounded_lazy(lazy: &LazySequenceObject) -> im::Vector<Value> {
    if is_infinite_lazy_sequence(lazy) {
        runtime_error("Cannot materialize unbounded lazy sequence");
    }

    let mut result: im::Vector<Value> = im::Vector::new();
    let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
    while let Some((val, next_seq)) = lazy_next_with_closures(&current) {
        result.push_back(val);
        current = next_seq;
    }
    result
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

        LazySeqKind::Range {
            current,
            end,
            inclusive,
            step,
        } => {
            let mut cur = *current;
            while *remaining > 0 {
                // Check if exhausted
                if let Some(end_val) = end {
                    let at_end = if *inclusive {
                        if *step > 0 {
                            cur > *end_val
                        } else {
                            cur < *end_val
                        }
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

        LazySeqKind::Iterate {
            generator,
            current,
            index: _,
        } => {
            // Generator can be a closure, partial application, or memoized closure
            let mut cur = *current.borrow();
            while *remaining > 0 {
                result.push_back(cur);
                *remaining -= 1;
                cur = call_value(*generator, &[cur]);
            }
        }

        LazySeqKind::Map { source, mapper } => {
            // Collect source elements and map them
            let source_elements = take_from_lazy_full(*remaining, source);
            for val in source_elements {
                if *remaining == 0 {
                    break;
                }
                let mapped = call_value(*mapper, &[val]);
                result.push_back(mapped);
                *remaining -= 1;
            }
        }

        LazySeqKind::Filter { source, predicate } => {
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
                    if call_value(*predicate, &[val]).is_truthy() {
                        result.push_back(val);
                        *remaining -= 1;
                    }
                }
            }
        }

        LazySeqKind::FilterMap { .. } => {
            let mut current: Box<LazySequenceObject> = Box::new(lazy.clone());
            while *remaining > 0 {
                let (val, next_seq) = match lazy_next_with_closures(&current) {
                    Some(v) => v,
                    None => return,
                };
                result.push_back(val);
                *remaining -= 1;
                current = next_seq;
            }
        }

        LazySeqKind::Skip {
            source,
            remaining: skip_remaining,
        } => {
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

        LazySeqKind::Combinations {
            source,
            size,
            indices,
            done,
        } => {
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
                let combination: im::Vector<Value> =
                    current_indices.iter().map(|&i| source[i]).collect();
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
/// - lines("") → []
/// - lines("a\nb\n") → ["a", "b"] (trailing empty lines filtered)
#[no_mangle]
pub extern "C-unwind" fn rt_lines(value: Value) -> Value {
    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => runtime_error("lines(string) expects a String"),
    };

    // Split on newlines, filtering empty trailing lines
    let parts: im::Vector<Value> = s
        .split('\n')
        .filter(|part| !part.is_empty())
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
pub extern "C-unwind" fn rt_split(separator: Value, string: Value) -> Value {
    // Both must be strings
    let sep = match separator.as_string() {
        Some(s) => s,
        None => runtime_error("split(separator, string) expects String arguments"),
    };
    let s = match string.as_string() {
        Some(s) => s,
        None => runtime_error("split(separator, string) expects String arguments"),
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
        None => runtime_error("regex_match(pattern, string) expects String arguments"),
    };
    let s = match string.as_string() {
        Some(s) => s,
        None => runtime_error("regex_match(pattern, string) expects String arguments"),
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
        None => runtime_error("regex_match_all(pattern, string) expects String arguments"),
    };
    let s = match string.as_string() {
        Some(s) => s,
        None => runtime_error("regex_match_all(pattern, string) expects String arguments"),
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
    use md5::{Digest, Md5};

    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => runtime_error("md5(value) expects a String"),
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
pub extern "C-unwind" fn rt_upper(value: Value) -> Value {
    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => runtime_error("upper(string) expects a String"),
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
pub extern "C-unwind" fn rt_lower(value: Value) -> Value {
    // Only works on strings
    let s = match value.as_string() {
        Some(s) => s,
        None => runtime_error("lower(string) expects a String"),
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
pub extern "C-unwind" fn rt_replace(from: Value, to: Value, string: Value) -> Value {
    // All must be strings
    let from_str = match from.as_string() {
        Some(s) => s,
        None => runtime_error("replace(from, to, string) expects String arguments"),
    };
    let to_str = match to.as_string() {
        Some(s) => s,
        None => runtime_error("replace(from, to, string) expects String arguments"),
    };
    let s = match string.as_string() {
        Some(s) => s,
        None => runtime_error("replace(from, to, string) expects String arguments"),
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
pub extern "C-unwind" fn rt_join(separator: Value, collection: Value) -> Value {
    // Separator must be a string
    let sep = match separator.as_string() {
        Some(s) => s.to_string(),
        None => runtime_error("join(separator, collection) expects String separator"),
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
            if b {
                "true".to_string()
            } else {
                "false".to_string()
            }
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

    runtime_error("join(separator, collection) expects List or Set collection")
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
pub extern "C-unwind" fn rt_abs(value: Value) -> Value {
    // Integer
    if let Some(i) = value.as_integer() {
        return Value::from_integer(i.abs());
    }

    // Decimal
    if let Some(d) = value.as_decimal() {
        return Value::from_decimal(d.abs());
    }

    runtime_error("abs(value) expects Integer or Decimal")
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
pub extern "C-unwind" fn rt_signum(value: Value) -> Value {
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

    runtime_error("signum(value) expects Integer or Decimal")
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
pub extern "C-unwind" fn rt_vec_add(a: Value, b: Value) -> Value {
    // Both must be lists
    let list_a = match a.as_list() {
        Some(l) => l,
        None => runtime_error("vec_add(a, b) expects List arguments"),
    };
    let list_b = match b.as_list() {
        Some(l) => l,
        None => runtime_error("vec_add(a, b) expects List arguments"),
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
pub extern "C-unwind" fn rt_bit_and(a: Value, b: Value) -> Value {
    let ia = a
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_and(a, b) expects Integer arguments"));
    let ib = b
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_and(a, b) expects Integer arguments"));
    Value::from_integer(ia & ib)
}

/// `bit_or(a, b)` → Integer
///
/// Bitwise OR.
///
/// Per LANG.txt §4.5:
/// - bit_or(12, 10) → 14 (1100 | 1010 = 1110)
#[no_mangle]
pub extern "C-unwind" fn rt_bit_or(a: Value, b: Value) -> Value {
    let ia = a
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_or(a, b) expects Integer arguments"));
    let ib = b
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_or(a, b) expects Integer arguments"));
    Value::from_integer(ia | ib)
}

/// `bit_xor(a, b)` → Integer
///
/// Bitwise XOR.
///
/// Per LANG.txt §4.5:
/// - bit_xor(12, 10) → 6  (1100 ^ 1010 = 0110)
#[no_mangle]
pub extern "C-unwind" fn rt_bit_xor(a: Value, b: Value) -> Value {
    let ia = a
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_xor(a, b) expects Integer arguments"));
    let ib = b
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_xor(a, b) expects Integer arguments"));
    Value::from_integer(ia ^ ib)
}

/// `bit_not(value)` → Integer
///
/// Bitwise NOT (complement).
///
/// Per LANG.txt §4.5:
/// - bit_not(12) → -13 (bitwise complement)
#[no_mangle]
pub extern "C-unwind" fn rt_bit_not(value: Value) -> Value {
    let i = value
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_not(value) expects Integer"));
    Value::from_integer(!i)
}

/// `bit_shift_left(value, shift)` → Integer
///
/// Left shift.
///
/// Per LANG.txt §4.5:
/// - bit_shift_left(1, 3) → 8  (1 << 3 = 1000)
#[no_mangle]
pub extern "C-unwind" fn rt_bit_shift_left(value: Value, shift: Value) -> Value {
    let i = value
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_shift_left(value, shift) expects Integer arguments"));
    let s = shift
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_shift_left(value, shift) expects Integer arguments"));
    // Clamp shift to valid range (0-63 for i64)
    if !(0..=63).contains(&s) {
        runtime_error("bit_shift_left(value, shift) expects shift in 0..=63");
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
pub extern "C-unwind" fn rt_bit_shift_right(value: Value, shift: Value) -> Value {
    let i = value
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_shift_right(value, shift) expects Integer arguments"));
    let s = shift
        .as_integer()
        .unwrap_or_else(|| runtime_error("bit_shift_right(value, shift) expects Integer arguments"));
    // Clamp shift to valid range (0-63 for i64)
    if !(0..=63).contains(&s) {
        runtime_error("bit_shift_right(value, shift) expects shift in 0..=63");
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
/// - type(1..10) → "BoundedRange"
/// - type(1..) → "UnboundedRange"
/// - type(1.. |> map(_ + 1)) → "LazySequence"
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
    if let Some(lazy) = value.as_lazy_sequence() {
        match &lazy.kind {
            LazySeqKind::Range { end: Some(_), .. } => {
                return Value::from_string("BoundedRange".to_string());
            }
            LazySeqKind::Range { end: None, .. } => {
                return Value::from_string("UnboundedRange".to_string());
            }
            _ => return Value::from_string("LazySequence".to_string()),
        }
    }
    if value.as_closure().is_some()
        || value.as_partial_application().is_some()
        || value.as_memoized_closure().is_some()
    {
        return Value::from_string("Function".to_string());
    }

    Value::from_string("Unknown".to_string())
}

/// `str(value)` → String
///
/// Convert a value to its string representation.
///
/// Per LANG.txt §11.15:
/// - str(42) → "42"
/// - str(3.14) → "3.14"
/// - str([1, 2, 3]) → "[1, 2, 3]"
#[no_mangle]
pub extern "C" fn rt_str(value: Value) -> Value {
    Value::from_string(format_value(&value))
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
/// Strings are wrapped in quotes to match other implementations (Blitzen, etc.)
pub fn format_value(value: &Value) -> String {
    format_value_inner(value, true)
}

/// Format a Value for puts output (strings without quotes for parsing)
pub fn print_value(value: &Value) -> String {
    format_value_inner(value, false)
}

fn format_value_inner(value: &Value, quote_strings: bool) -> String {
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
        return format_decimal(d);
    }

    if let Some(s) = value.as_string() {
        if quote_strings {
            return format!("\"{}\"", s);
        } else {
            return s.to_string();
        }
    }

    if let Some(list) = value.as_list() {
        let items: Vec<String> = list
            .iter()
            .map(|v| format_value_inner(v, quote_strings))
            .collect();
        return format!("[{}]", items.join(", "));
    }

    if let Some(set) = value.as_set() {
        let items: Vec<String> = set
            .iter()
            .map(|v| format_value_inner(v, quote_strings))
            .collect();
        return format!("{{{}}}", items.join(", "));
    }

    if let Some(dict) = value.as_dict() {
        let items: Vec<String> = dict
            .iter()
            .map(|(k, v)| {
                format!(
                    "{}: {}",
                    format_value_inner(k, quote_strings),
                    format_value_inner(v, quote_strings)
                )
            })
            .collect();
        return format!("#{{{}}}", items.join(", "));
    }

    if value.as_closure().is_some()
        || value.as_partial_application().is_some()
        || value.as_memoized_closure().is_some()
    {
        return "<function>".to_string();
    }

    if value.as_lazy_sequence().is_some() {
        return "<lazy-sequence>".to_string();
    }

    "<unknown>".to_string()
}

fn format_decimal(value: f64) -> String {
    let s = value.to_string();
    if s.contains('.') || s.contains('e') || s.contains('E') {
        s
    } else {
        format!("{s}.0")
    }
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

    let formatted: Vec<String> = args.iter().map(print_value).collect();
    println!("{}", formatted.join(" "));

    Value::nil()
}

/// Helper for calling rt_puts with two arguments (common case in runner)
#[no_mangle]
pub extern "C" fn rt_puts_two(a: Value, b: Value) -> Value {
    let formatted = format!("{} {}", print_value(&a), print_value(&b));
    println!("{}", formatted);
    Value::nil()
}

/// Get the current time in nanoseconds since program start.
/// Uses a relative timestamp to avoid large number overflow in NaN-boxing.
/// Used for timing measurements in the runner.
#[no_mangle]
pub extern "C" fn rt_time_nanos() -> Value {
    use std::sync::OnceLock;
    use std::time::Instant;

    static START_TIME: OnceLock<Instant> = OnceLock::new();
    let start = START_TIME.get_or_init(Instant::now);
    let elapsed_nanos = start.elapsed().as_nanos() as i64;
    Value::from_integer(elapsed_nanos)
}

// ============================================================================
// CLI Output Functions (for standalone compiled executables)
// ============================================================================

/// Get command line arguments (excluding program name).
/// Returns a list of strings.
#[no_mangle]
pub extern "C" fn rt_get_args() -> Value {
    let args: im::Vector<Value> = std::env::args()
        .skip(1) // Skip program name
        .map(|s| Value::from_string(&s))
        .collect();
    Value::from_list(args)
}

/// Print solution result with colors and timing.
/// label: "Part 1" or "Part 2"
/// value: the result value
/// time_nanos: execution time in nanoseconds
#[no_mangle]
pub extern "C" fn rt_print_result(label: Value, value: Value, time_nanos: Value) {
    let label_str = label.as_string().unwrap_or("Result");
    let time_ms = time_nanos.as_integer().unwrap_or(0) / 1_000_000;
    println!(
        "{}: \x1b[32m{}\x1b[0m \x1b[90m{}ms\x1b[0m",
        label_str,
        format_value(&value),
        time_ms
    );
}

/// Print test case header.
/// test_num: test number (1-based)
/// is_slow: whether this test is marked @slow
#[no_mangle]
pub extern "C" fn rt_print_test_header(test_num: Value, is_slow: Value) {
    let num = test_num.as_integer().unwrap_or(0);
    if is_slow.as_bool().unwrap_or(false) {
        println!("\x1b[4mTestcase #{}\x1b[0m \x1b[33m(slow)\x1b[0m", num);
    } else {
        println!("\x1b[4mTestcase #{}\x1b[0m", num);
    }
}

/// Print test result (pass or fail).
/// Returns true if passed, false if failed.
/// label: "Part 1" or "Part 2"
/// actual: the computed value
/// expected: the expected value
/// time_nanos: execution time in nanoseconds
#[no_mangle]
pub extern "C" fn rt_print_test_result(
    label: Value,
    actual: Value,
    expected: Value,
    time_nanos: Value,
) -> Value {
    let label_str = label.as_string().unwrap_or("Result");
    let time_ms = time_nanos.as_integer().unwrap_or(0) / 1_000_000;
    let passed = rt_eq(actual, expected).as_bool().unwrap_or(false);

    if passed {
        println!(
            "{}: {} \x1b[32m✔\x1b[0m \x1b[90m{}ms\x1b[0m",
            label_str,
            format_value(&actual),
            time_ms
        );
    } else {
        println!(
            "{}: {} \x1b[31m✘ (Expected: {})\x1b[0m",
            label_str,
            format_value(&actual),
            format_value(&expected)
        );
    }
    Value::from_bool(passed)
}

/// Print a blank line (for separating test cases).
#[no_mangle]
pub extern "C" fn rt_print_newline() {
    println!();
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
    std::fs::read_to_string(session_file)
        .ok()
        .map(|s| s.trim().to_string())
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

/// Generate cache filename for AOC input based on year/day.
/// Returns filename like "aoc2022_day05.input" (day zero-padded).
fn aoc_cache_filename(year: u32, day: u32) -> String {
    format!("aoc{}_day{:02}.input", year, day)
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
        .arg("-f") // Fail silently on HTTP errors
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

/// Resolve AOC input at compile time.
/// Checks for aoc<YEAR>_day<DD>.input file, fetches and saves if not found.
/// Used by CLI compile mode to bake input into compiled binaries.
pub fn resolve_aoc_input(url: &str, script_path: &std::path::Path) -> Option<String> {
    let (year, day) = parse_aoc_url(url)?;

    // Cache file is named by URL pattern, placed in same directory as script
    let script_dir = script_path.parent()?;
    let local_input = script_dir.join(aoc_cache_filename(year, day));

    // Check local file first
    if let Ok(contents) = std::fs::read_to_string(&local_input) {
        return Some(contents);
    }

    // Fetch and save to local file
    let session = get_aoc_session()?;
    let input = fetch_aoc_input(year, day, &session)?;
    std::fs::write(&local_input, &input).ok();
    Some(input)
}

/// Fetch content from an HTTP or HTTPS URL using curl.
///
/// Returns the response body as a String, or nil on error.
fn read_http_url(url: &str) -> Value {
    let output = std::process::Command::new("curl")
        .arg("-s")
        .arg("-f") // Fail silently on HTTP errors
        .arg("-L") // Follow redirects
        .arg(url)
        .output();

    match output {
        Ok(result) if result.status.success() => {
            match String::from_utf8(result.stdout) {
                Ok(body) => Value::from_string(&body),
                Err(_) => Value::nil(),
            }
        }
        _ => Value::nil(),
    }
}

/// Read AOC input, using aoc<YEAR>_day<DD>.input file next to the script.
fn read_aoc_input(url: &str) -> Value {
    let (year, day) = match parse_aoc_url(url) {
        Some(v) => v,
        None => return Value::nil(),
    };

    // Check for script path from environment
    if let Ok(script_path) = std::env::var("DASHER_SCRIPT_PATH") {
        let script_path = std::path::Path::new(&script_path);

        // Cache file is named by URL pattern, placed in same directory as script
        let script_dir = match script_path.parent() {
            Some(d) => d,
            None => return Value::nil(),
        };
        let local_input = script_dir.join(aoc_cache_filename(year, day));

        // Check if cache file exists
        if let Ok(contents) = std::fs::read_to_string(&local_input) {
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

        // Save to cache file for future use
        std::fs::write(&local_input, &input).ok();

        return Value::from_string(&input);
    }

    // No script context - compiled binaries should have input baked in
    eprintln!("Error: No script context for AOC input (compiled binaries should have input baked in)");
    Value::nil()
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
        None => runtime_error("read(path) expects a String"),
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

/// `env()` → Nil
///
/// REPL-only in LANG.txt; in AOT/CLI it is a no-op that returns nil.
#[no_mangle]
pub extern "C" fn rt_env() -> Value {
    Value::nil()
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
    if !is_callable(&func) {
        runtime_error("memoize(function) expects a function");
    }
    if func.as_memoized_closure().is_some() {
        return func;
    }

    // Create a memoized wrapper around the closure
    let arity = expect_callable_arity("memoize(function)", &func);
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
    crate::operations::rt_call(callee, argc, argv)
}

// ============================================================================
// §11.16 Metaprogramming
// ============================================================================

/// `evaluate(source)` → Value
///
/// Parse and evaluate a string as a Santa expression. For AOT compilation,
/// this supports a subset of expressions (literal values): integers, decimals,
/// strings, lists, sets, and dictionaries.
///
/// Per LANG.txt Appendix B:
/// - evaluate("[1, 2, 3]") → [1, 2, 3]
/// - evaluate("42") → 42
/// - evaluate("\"hello\"") → "hello"
#[no_mangle]
pub extern "C-unwind" fn rt_evaluate(source: Value) -> Value {
    let code = match source.as_string() {
        Some(s) => s,
        None => runtime_error("evaluate(source) expects String"),
    };

    // Parse the literal value
    let mut parser = LiteralParser::new(code);
    match parser.parse() {
        Ok(val) => val,
        Err(msg) => runtime_error(&format!("evaluate: {}", msg)),
    }
}

/// Simple parser for literal values (integers, lists, etc.)
/// Used by evaluate() builtin for AOT compilation where full runtime
/// compilation is not available.
struct LiteralParser<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> LiteralParser<'a> {
    fn new(source: &'a str) -> Self {
        LiteralParser {
            chars: source.chars().peekable(),
        }
    }

    fn skip_whitespace(&mut self) {
        while self.chars.peek().map_or(false, |c| c.is_whitespace()) {
            self.chars.next();
        }
    }

    fn parse(&mut self) -> Result<Value, String> {
        self.skip_whitespace();
        let result = self.parse_value()?;
        self.skip_whitespace();
        if self.chars.peek().is_some() {
            return Err("unexpected characters after value".to_string());
        }
        Ok(result)
    }

    fn parse_value(&mut self) -> Result<Value, String> {
        self.skip_whitespace();

        match self.chars.peek() {
            Some('[') => self.parse_list(),
            Some('{') => self.parse_set_or_dict(),
            Some('"') => self.parse_string(),
            Some('-') | Some('0'..='9') => self.parse_number(),
            Some('t') | Some('f') => self.parse_bool(),
            Some('n') => self.parse_nil(),
            Some(c) => Err(format!("unexpected character: '{}'", c)),
            None => Err("unexpected end of input".to_string()),
        }
    }

    fn parse_list(&mut self) -> Result<Value, String> {
        self.chars.next(); // consume '['
        self.skip_whitespace();

        let mut elements = im::Vector::new();

        if self.chars.peek() == Some(&']') {
            self.chars.next();
            return Ok(Value::from_list(elements));
        }

        loop {
            elements.push_back(self.parse_value()?);
            self.skip_whitespace();

            match self.chars.peek() {
                Some(',') => {
                    self.chars.next();
                    self.skip_whitespace();
                }
                Some(']') => {
                    self.chars.next();
                    return Ok(Value::from_list(elements));
                }
                Some(c) => return Err(format!("expected ',' or ']', got '{}'", c)),
                None => return Err("unterminated list".to_string()),
            }
        }
    }

    fn parse_set_or_dict(&mut self) -> Result<Value, String> {
        self.chars.next(); // consume '{'
        self.skip_whitespace();

        // Empty set
        if self.chars.peek() == Some(&'}') {
            self.chars.next();
            return Ok(Value::from_set(im::HashSet::new()));
        }

        // Parse first element to determine if it's a dict
        let first = self.parse_value()?;
        self.skip_whitespace();

        // Check if this is a dictionary (has ':')
        if self.chars.peek() == Some(&':') {
            self.chars.next(); // consume ':'
            self.skip_whitespace();
            let first_val = self.parse_value()?;
            self.skip_whitespace();

            let mut dict = im::HashMap::new();
            dict.insert(first, first_val);

            loop {
                match self.chars.peek() {
                    Some(',') => {
                        self.chars.next();
                        self.skip_whitespace();
                        let key = self.parse_value()?;
                        self.skip_whitespace();
                        if self.chars.next() != Some(':') {
                            return Err("expected ':' in dictionary".to_string());
                        }
                        self.skip_whitespace();
                        let val = self.parse_value()?;
                        self.skip_whitespace();
                        dict.insert(key, val);
                    }
                    Some('}') => {
                        self.chars.next();
                        return Ok(Value::from_dict(dict));
                    }
                    Some(c) => return Err(format!("expected ',' or '}}', got '{}'", c)),
                    None => return Err("unterminated dictionary".to_string()),
                }
            }
        } else {
            // It's a set
            let mut set = im::HashSet::new();
            if !first.is_hashable() {
                runtime_error(&format!(
                    "{} is not hashable and cannot be added to a Set",
                    type_name(&first)
                ));
            }
            set.insert(first);

            loop {
                match self.chars.peek() {
                    Some(',') => {
                        self.chars.next();
                        self.skip_whitespace();
                        let elem = self.parse_value()?;
                        if !elem.is_hashable() {
                            runtime_error(&format!(
                                "{} is not hashable and cannot be added to a Set",
                                type_name(&elem)
                            ));
                        }
                        set.insert(elem);
                        self.skip_whitespace();
                    }
                    Some('}') => {
                        self.chars.next();
                        return Ok(Value::from_set(set));
                    }
                    Some(c) => return Err(format!("expected ',' or '}}', got '{}'", c)),
                    None => return Err("unterminated set".to_string()),
                }
            }
        }
    }

    fn parse_string(&mut self) -> Result<Value, String> {
        self.chars.next(); // consume opening '"'
        let mut s = String::new();

        loop {
            match self.chars.next() {
                Some('"') => return Ok(Value::from_string(s)),
                Some('\\') => match self.chars.next() {
                    Some('n') => s.push('\n'),
                    Some('t') => s.push('\t'),
                    Some('r') => s.push('\r'),
                    Some('\\') => s.push('\\'),
                    Some('"') => s.push('"'),
                    Some(c) => s.push(c),
                    None => return Err("unterminated string escape".to_string()),
                },
                Some(c) => s.push(c),
                None => return Err("unterminated string".to_string()),
            }
        }
    }

    fn parse_number(&mut self) -> Result<Value, String> {
        let mut num_str = String::new();
        let mut has_decimal = false;

        // Handle negative sign
        if self.chars.peek() == Some(&'-') {
            num_str.push('-');
            self.chars.next();
        }

        // Parse digits
        while let Some(&c) = self.chars.peek() {
            if c.is_ascii_digit() {
                num_str.push(c);
                self.chars.next();
            } else if c == '.' && !has_decimal {
                has_decimal = true;
                num_str.push(c);
                self.chars.next();
            } else if c == '_' {
                // Skip underscores in numbers (e.g., 1_000_000)
                self.chars.next();
            } else {
                break;
            }
        }

        if has_decimal {
            num_str
                .parse::<f64>()
                .map(Value::from_decimal)
                .map_err(|_| format!("invalid decimal: {}", num_str))
        } else {
            num_str
                .parse::<i64>()
                .map(Value::from_integer)
                .map_err(|_| format!("invalid integer: {}", num_str))
        }
    }

    fn parse_bool(&mut self) -> Result<Value, String> {
        if self.try_consume("true") {
            Ok(Value::from_bool(true))
        } else if self.try_consume("false") {
            Ok(Value::from_bool(false))
        } else {
            Err("expected 'true' or 'false'".to_string())
        }
    }

    fn parse_nil(&mut self) -> Result<Value, String> {
        if self.try_consume("nil") {
            Ok(Value::nil())
        } else {
            Err("expected 'nil'".to_string())
        }
    }

    fn try_consume(&mut self, keyword: &str) -> bool {
        let mut chars_copy = self.chars.clone();
        for expected_char in keyword.chars() {
            match chars_copy.next() {
                Some(c) if c == expected_char => continue,
                _ => return false,
            }
        }
        // Make sure keyword is not followed by alphanumeric
        if chars_copy.peek().map_or(false, |c| c.is_alphanumeric()) {
            return false;
        }
        // Consume the characters
        for _ in keyword.chars() {
            self.chars.next();
        }
        true
    }
}
