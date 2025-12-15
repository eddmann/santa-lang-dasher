use super::value::Value;
use super::heap::{ListObject, SetObject, DictObject};
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
pub unsafe extern "C" fn rt_dict_from_entries(keys: *const Value, values: *const Value, count: usize) -> Value {
    let keys_slice = std::slice::from_raw_parts(keys, count);
    let values_slice = std::slice::from_raw_parts(values, count);

    let hashmap = keys_slice.iter()
        .zip(values_slice.iter())
        .map(|(k, v)| (*k, *v))
        .collect();

    let dict = DictObject::new(hashmap);
    Value::from_heap_ptr(Box::into_raw(dict))
}
