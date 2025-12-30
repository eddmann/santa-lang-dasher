// Reference counting operations for heap-allocated values

use super::heap::ObjectHeader;
use super::value::Value;
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
        unsafe { (*header_ptr).refcount.load(Ordering::Relaxed) }
    } else {
        0 // Primitives don't have refcounts
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
            TypeTag::Closure => {
                let ptr = header_ptr as *mut super::heap::ClosureObject;
                // Decref all captured values before freeing
                for capture in &(*ptr).captures {
                    rt_decref(*capture);
                }
                drop(Box::from_raw(ptr));
            }
            TypeTag::MemoizedClosure => {
                let ptr = header_ptr as *mut super::heap::MemoizedClosureObject;
                // Decref the inner closure
                rt_decref((*ptr).inner_closure);
                // Decref all cached keys and values
                let cache = (*ptr).cache.borrow();
                for (args, result) in cache.iter() {
                    for arg in args {
                        rt_decref(*arg);
                    }
                    rt_decref(*result);
                }
                drop(cache);
                drop(Box::from_raw(ptr));
            }
            TypeTag::LazySequence => {
                let ptr = header_ptr as *mut super::heap::LazySequenceObject;
                // Decref all Values contained in the lazy sequence
                free_lazy_seq_values(&(*ptr).kind);
                drop(Box::from_raw(ptr));
            }
            TypeTag::Decimal | TypeTag::BoxedInteger => {
                // These types don't contain nested Values, just free directly
                drop(Box::from_raw(header_ptr as *mut ObjectHeader));
            }
            TypeTag::Function => {
                // Function type is not used - all functions are Closures
                // Just free the allocation if it ever appears
                drop(Box::from_raw(header_ptr as *mut ObjectHeader));
            }
            TypeTag::PartialApplication => {
                let ptr = header_ptr as *mut super::heap::PartialApplicationObject;
                // Decref the original closure
                rt_decref((*ptr).closure);
                // Decref all accumulated arguments
                for arg in &(*ptr).args {
                    rt_decref(*arg);
                }
                drop(Box::from_raw(ptr));
            }
        }
    }
}

/// Helper to decref all Values contained in a LazySeqKind
unsafe fn free_lazy_seq_values(kind: &super::heap::LazySeqKind) {
    use super::heap::LazySeqKind;

    match kind {
        LazySeqKind::Repeat { value } => {
            rt_decref(*value);
        }
        LazySeqKind::Cycle { source, .. } => {
            for elem in source.iter() {
                rt_decref(*elem);
            }
        }
        LazySeqKind::Iterate {
            generator,
            current,
            index: _,
        } => {
            rt_decref(*generator);
            rt_decref(*current.borrow());
        }
        LazySeqKind::Range { .. } => {
            // No Values to decref
        }
        LazySeqKind::Map { source, mapper } => {
            free_lazy_seq_values(&source.kind);
            rt_decref(*mapper);
        }
        LazySeqKind::Filter { source, predicate } => {
            free_lazy_seq_values(&source.kind);
            rt_decref(*predicate);
        }
        LazySeqKind::FilterMap { source, mapper } => {
            free_lazy_seq_values(&source.kind);
            rt_decref(*mapper);
        }
        LazySeqKind::Skip { source, .. } => {
            free_lazy_seq_values(&source.kind);
        }
        LazySeqKind::Combinations { source, .. } => {
            for elem in source.iter() {
                rt_decref(*elem);
            }
        }
        LazySeqKind::Zip { sources } => {
            for seq in sources.iter() {
                free_lazy_seq_values(&seq.kind);
            }
        }
    }
}
