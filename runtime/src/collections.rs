use super::heap::{DictObject, ListObject, SetObject};
use super::builtins::collect_bounded_lazy;
use super::operations::{is_infinite_lazy_sequence, runtime_error, type_name};
use super::value::Value;
use im;

/// Create an empty list
#[no_mangle]
pub extern "C" fn rt_list_new() -> Value {
    let list = ListObject::new(im::Vector::new());
    Value::from_heap_ptr(Box::into_raw(list))
}

/// Create a list from an array of values
///
/// # Safety
/// The caller must ensure that `values` points to a valid array of `count` Values.
#[no_mangle]
pub unsafe extern "C" fn rt_list_from_values(values: *const Value, count: usize) -> Value {
    let values_slice = std::slice::from_raw_parts(values, count);
    let vector = values_slice.iter().copied().collect();
    let list = ListObject::new(vector);
    Value::from_heap_ptr(Box::into_raw(list))
}

/// Push a single element to the end of a list
/// Returns a new list with the element appended.
#[no_mangle]
pub extern "C" fn rt_list_push(list: Value, elem: Value) -> Value {
    if let Some(l) = list.as_list() {
        let mut new_list = l.clone();
        new_list.push_back(elem);
        Value::from_list(new_list)
    } else {
        // If not a list, create a new list with just this element
        let mut new_list = im::Vector::new();
        new_list.push_back(elem);
        Value::from_list(new_list)
    }
}

/// Concatenate two lists (or a list with a lazy sequence)
/// Returns a new list with all elements from both collections.
#[no_mangle]
pub extern "C" fn rt_list_concat(list1: Value, list2: Value) -> Value {
    let mut result = if let Some(l) = list1.as_list() {
        l.clone()
    } else {
        im::Vector::new()
    };

    // Handle list2 as list or lazy sequence
    if let Some(l2) = list2.as_list() {
        result.append(l2.clone());
    } else if let Some(lazy) = list2.as_lazy_sequence() {
        if is_infinite_lazy_sequence(lazy) {
            runtime_error("Cannot spread unbounded lazy sequence");
        }
        let items = collect_bounded_lazy(lazy);
        result.append(items);
    }

    Value::from_list(result)
}

/// Create an empty set
#[no_mangle]
pub extern "C" fn rt_set_new() -> Value {
    let set = SetObject::new(im::HashSet::new());
    Value::from_heap_ptr(Box::into_raw(set))
}

/// Create a set from an array of values
///
/// # Safety
/// The caller must ensure that `values` points to a valid array of `count` Values.
#[no_mangle]
pub unsafe extern "C" fn rt_set_from_values(values: *const Value, count: usize) -> Value {
    let values_slice = std::slice::from_raw_parts(values, count);
    for value in values_slice.iter() {
        if value.as_lazy_sequence().is_some() {
            runtime_error("LazySequence is not hashable and cannot be added to a Set");
        }
        if !value.is_hashable() {
            runtime_error(&format!(
                "{} is not hashable and cannot be added to a Set",
                type_name(value)
            ));
        }
    }
    let hashset = values_slice.iter().copied().collect();
    let set = SetObject::new(hashset);
    Value::from_heap_ptr(Box::into_raw(set))
}

/// Create an empty dict
#[no_mangle]
pub extern "C" fn rt_dict_new() -> Value {
    let dict = DictObject::new(im::HashMap::new());
    Value::from_heap_ptr(Box::into_raw(dict))
}

/// Create a dict from arrays of keys and values
///
/// # Safety
/// The caller must ensure that `keys` and `values` both point to valid arrays of `count` Values.
#[no_mangle]
pub unsafe extern "C" fn rt_dict_from_entries(
    keys: *const Value,
    values: *const Value,
    count: usize,
) -> Value {
    let keys_slice = std::slice::from_raw_parts(keys, count);
    let values_slice = std::slice::from_raw_parts(values, count);

    for key in keys_slice.iter() {
        if key.as_lazy_sequence().is_some() {
            runtime_error("LazySequence is not hashable and cannot be used as a Dictionary key");
        }
        if !key.is_hashable() {
            runtime_error(&format!(
                "{} is not hashable and cannot be used as a Dictionary key",
                type_name(key)
            ));
        }
    }

    let hashmap = keys_slice
        .iter()
        .zip(values_slice.iter())
        .map(|(k, v)| (*k, *v))
        .collect();

    let dict = DictObject::new(hashmap);
    Value::from_heap_ptr(Box::into_raw(dict))
}
