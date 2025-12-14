// Reference counting operations for heap-allocated values

use super::value::Value;
use super::heap::ObjectHeader;
use std::sync::atomic::Ordering;

/// Increment reference count for heap-allocated values
#[no_mangle]
pub extern "C" fn rt_incref(value: Value) {
    if let Some(header_ptr) = value.as_heap_ptr::<ObjectHeader>() {
        unsafe {
            (*header_ptr).refcount.fetch_add(1, Ordering::Relaxed);
        }
    }
    // Primitives (integers, booleans, nil, decimals) are ignored
}

/// Decrement reference count and free if it reaches zero
#[no_mangle]
pub extern "C" fn rt_decref(value: Value) {
    if let Some(header_ptr) = value.as_heap_ptr::<ObjectHeader>() {
        unsafe {
            let old_count = (*header_ptr).refcount.fetch_sub(1, Ordering::Release);
            if old_count == 1 {
                // Refcount reached zero, need to free
                std::sync::atomic::fence(Ordering::Acquire);
                rt_free(value);
            }
        }
    }
    // Primitives (integers, booleans, nil, decimals) are ignored
}

/// Get current reference count (for testing)
pub fn rt_get_refcount(value: Value) -> u32 {
    if let Some(header_ptr) = value.as_heap_ptr::<ObjectHeader>() {
        unsafe {
            (*header_ptr).refcount.load(Ordering::Relaxed)
        }
    } else {
        0  // Primitives don't have refcounts
    }
}

/// Free a heap object (called when refcount reaches zero)
unsafe fn rt_free(value: Value) {
    use super::heap::TypeTag;

    if let Some(header_ptr) = value.as_heap_ptr::<ObjectHeader>() {
        match (*header_ptr).type_tag {
            TypeTag::String => {
                let ptr = header_ptr as *mut super::heap::StringObject;
                drop(Box::from_raw(ptr));
            }
            TypeTag::List => {
                let ptr = header_ptr as *mut super::heap::ListObject;
                // Need to decref all elements before freeing
                let list = &(*ptr).data;
                for elem in list.iter() {
                    rt_decref(*elem);
                }
                drop(Box::from_raw(ptr));
            }
            TypeTag::Set => {
                let ptr = header_ptr as *mut super::heap::SetObject;
                // Need to decref all elements before freeing
                let set = &(*ptr).data;
                for elem in set.iter() {
                    rt_decref(*elem);
                }
                drop(Box::from_raw(ptr));
            }
            TypeTag::Dict => {
                let ptr = header_ptr as *mut super::heap::DictObject;
                // Need to decref all keys and values before freeing
                let dict = &(*ptr).data;
                for (key, val) in dict.iter() {
                    rt_decref(*key);
                    rt_decref(*val);
                }
                drop(Box::from_raw(ptr));
            }
            TypeTag::MutableCell => {
                let ptr = header_ptr as *mut super::heap::MutableCellObject;
                // Decref the contained value
                rt_decref((*ptr).value);
                drop(Box::from_raw(ptr));
            }
            _ => {
                // Other types not implemented yet
                // For now, just leak the memory
                // TODO: Implement for Function, Closure, LazySequence, etc.
            }
        }
    }
}
