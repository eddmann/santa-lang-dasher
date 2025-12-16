use super::value::Value;

/// Terminate execution with a runtime error.
///
/// Per LANG.txt §15.5, serious errors terminate execution with a RuntimeErr.
/// This function prints to stderr and exits with code 2.
///
/// Note: This function is marked as allowing unwinding panic for tests,
/// but in production use it will terminate the process.
#[cfg_attr(test, allow(unreachable_code))]
pub fn runtime_error(message: &str) -> ! {
    // In test builds, we use a testing flag to control behavior
    #[cfg(test)]
    {
        // For tests, panic with a message that can be caught
        panic!("RuntimeError: {}", message);
    }

    #[cfg(not(test))]
    {
        eprintln!("RuntimeError: {}", message);
        std::process::exit(2)
    }
}

/// Get a human-readable type name for a Value (for error messages)
pub fn type_name(value: &Value) -> &'static str {
    if value.is_integer() {
        "Integer"
    } else if value.is_nil() {
        "Nil"
    } else if value.is_boolean() {
        "Boolean"
    } else if value.as_decimal().is_some() {
        "Decimal"
    } else if value.as_string().is_some() {
        "String"
    } else if value.as_list().is_some() {
        "List"
    } else if value.as_set().is_some() {
        "Set"
    } else if value.as_dict().is_some() {
        "Dictionary"
    } else if value.as_closure().is_some() {
        "Function"
    } else if value.as_lazy_sequence().is_some() {
        "LazySequence"
    } else {
        "Unknown"
    }
}

/// Add two values following santa-lang semantics
///
/// Per LANG.txt §4.1:
/// - Integer + Integer → Integer
/// - Decimal + Decimal → Decimal
/// - Integer + Decimal → Integer (left type wins)
/// - Decimal + Integer → Decimal (left type wins)
/// - String + X → String (coerce X to string)
/// - List + List → List (concatenation)
/// - Set + Set → Set (union)
/// - Dict + Dict → Dict (merge)
#[no_mangle]
pub extern "C" fn rt_add(left: Value, right: Value) -> Value {
    // Handle integers
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        return Value::from_integer(l + r);
    }

    // Handle decimals
    if let (Some(l), Some(r)) = (left.as_decimal(), right.as_decimal()) {
        return Value::from_decimal(l + r);
    }

    // Handle mixed Integer + Decimal (left type wins)
    if let Some(l) = left.as_integer() {
        if let Some(r) = right.as_decimal() {
            // Left is Int, result is Int
            return Value::from_integer(l + r as i64);
        }
    }

    // Handle mixed Decimal + Integer (left type wins)
    if let Some(l) = left.as_decimal() {
        if let Some(r) = right.as_integer() {
            // Left is Decimal, result is Decimal
            return Value::from_decimal(l + r as f64);
        }
    }

    // Handle String + X (coerce right to string)
    if let Some(l) = left.as_string() {
        let r_str = value_to_string(&right);
        return Value::from_string(format!("{}{}", l, r_str));
    }

    // Handle List + List (concatenation) per LANG.txt §4
    if let (Some(l), Some(r)) = (left.as_list(), right.as_list()) {
        let mut result = l.clone();
        result.append(r.clone());
        return Value::from_list(result);
    }

    // Handle Set + Set (union) per LANG.txt §4
    if let (Some(l), Some(r)) = (left.as_set(), right.as_set()) {
        let result = l.clone().union(r.clone());
        return Value::from_set(result);
    }

    // Handle Dict + Dict (merge, right precedence) per LANG.txt §4
    if let (Some(l), Some(r)) = (left.as_dict(), right.as_dict()) {
        // Union with right entries overwriting left entries when keys clash
        // im::HashMap::union keeps left values on collision, so we need r.union(l)
        // then the right values win when there are conflicts
        let result = r.clone().union(l.clone());
        return Value::from_dict(result);
    }

    // Unsupported operation - return nil
    Value::nil()
}

/// Subtract two values
#[no_mangle]
pub extern "C" fn rt_sub(left: Value, right: Value) -> Value {
    // Handle integers
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        return Value::from_integer(l - r);
    }

    // Handle decimals
    if let (Some(l), Some(r)) = (left.as_decimal(), right.as_decimal()) {
        return Value::from_decimal(l - r);
    }

    // Handle mixed Integer + Decimal (left type wins)
    if let Some(l) = left.as_integer() {
        if let Some(r) = right.as_decimal() {
            return Value::from_integer(l - r as i64);
        }
    }

    // Handle mixed Decimal + Integer (left type wins)
    if let Some(l) = left.as_decimal() {
        if let Some(r) = right.as_integer() {
            return Value::from_decimal(l - r as f64);
        }
    }

    Value::nil()
}

/// Multiply two values
#[no_mangle]
pub extern "C" fn rt_mul(left: Value, right: Value) -> Value {
    // Handle integers
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        return Value::from_integer(l * r);
    }

    // Handle decimals
    if let (Some(l), Some(r)) = (left.as_decimal(), right.as_decimal()) {
        return Value::from_decimal(l * r);
    }

    // Handle mixed Integer + Decimal (left type wins)
    if let Some(l) = left.as_integer() {
        if let Some(r) = right.as_decimal() {
            return Value::from_integer(l * r as i64);
        }
    }

    // Handle mixed Decimal + Integer (left type wins)
    if let Some(l) = left.as_decimal() {
        if let Some(r) = right.as_integer() {
            return Value::from_decimal(l * r as f64);
        }
    }

    Value::nil()
}

/// Divide two values using Python-style floored division
///
/// Per LANG.txt §4 and PLAN.md §8.3:
/// - Integer / Integer uses floored division (rounds toward negative infinity)
/// - -7 / 2 = -4 (NOT -3 like Rust's default)
/// - 7 / -2 = -4 (NOT -3)
#[no_mangle]
pub extern "C-unwind" fn rt_div(left: Value, right: Value) -> Value {
    // Handle integers with floored division
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        if r == 0 {
            runtime_error("Division by zero");
        }
        return Value::from_integer(floored_div(l, r));
    }

    // Handle decimals (normal division)
    if let (Some(l), Some(r)) = (left.as_decimal(), right.as_decimal()) {
        if r == 0.0 {
            runtime_error("Division by zero");
        }
        return Value::from_decimal(l / r);
    }

    // Handle mixed Integer + Decimal (left type wins)
    if let Some(l) = left.as_integer() {
        if let Some(r) = right.as_decimal() {
            if r == 0.0 {
                runtime_error("Division by zero");
            }
            return Value::from_integer((l as f64 / r) as i64);
        }
    }

    // Handle mixed Decimal + Integer (left type wins)
    if let Some(l) = left.as_decimal() {
        if let Some(r) = right.as_integer() {
            if r == 0 {
                runtime_error("Division by zero");
            }
            return Value::from_decimal(l / r as f64);
        }
    }

    Value::nil()
}

/// Modulo operation using Python-style floored modulo
///
/// Per LANG.txt and PLAN.md §8.3:
/// - Result has same sign as divisor (NOT same sign as dividend like Rust)
/// - -7 % 3 = 2 (NOT -1 like Rust)
/// - 7 % -3 = -2 (NOT 1 like Rust)
#[no_mangle]
pub extern "C-unwind" fn rt_mod(left: Value, right: Value) -> Value {
    // Handle integers with floored modulo
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        if r == 0 {
            runtime_error("Division by zero");
        }
        return Value::from_integer(floored_mod(l, r));
    }

    // TODO: Handle decimals if needed (LANG.txt doesn't specify decimal modulo)

    Value::nil()
}

/// Python-style floored division
///
/// Rounds toward negative infinity, NOT toward zero like Rust's default
fn floored_div(a: i64, b: i64) -> i64 {
    let q = a / b;
    let r = a % b;
    // Adjust if remainder has different sign than divisor
    if (r != 0) && ((r < 0) != (b < 0)) {
        q - 1
    } else {
        q
    }
}

/// Python-style floored modulo
///
/// Result has same sign as divisor (b), NOT same sign as dividend (a)
fn floored_mod(a: i64, b: i64) -> i64 {
    ((a % b) + b) % b
}

// ===== Comparison Operations =====

/// Equality comparison
#[no_mangle]
pub extern "C" fn rt_eq(left: Value, right: Value) -> Value {
    // Use Value's PartialEq implementation
    Value::from_bool(left == right)
}

/// Not-equal comparison
#[no_mangle]
pub extern "C" fn rt_ne(left: Value, right: Value) -> Value {
    Value::from_bool(left != right)
}

/// Less-than comparison
///
/// Per LANG.txt §4.4:
/// Only Integer, Decimal, and String support comparison operators.
/// Comparing other types (List, Set, Dict, Function, LazySequence) produces RuntimeErr.
#[no_mangle]
pub extern "C-unwind" fn rt_lt(left: Value, right: Value) -> Value {
    // Integer comparison
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        return Value::from_bool(l < r);
    }

    // Decimal comparison
    if let (Some(l), Some(r)) = (left.as_decimal(), right.as_decimal()) {
        return Value::from_bool(l < r);
    }

    // Mixed Integer/Decimal comparison
    if let Some(l) = left.as_integer() {
        if let Some(r) = right.as_decimal() {
            return Value::from_bool((l as f64) < r);
        }
    }

    if let Some(l) = left.as_decimal() {
        if let Some(r) = right.as_integer() {
            return Value::from_bool(l < (r as f64));
        }
    }

    // String comparison (lexicographic)
    if let (Some(l), Some(r)) = (left.as_string(), right.as_string()) {
        return Value::from_bool(l < r);
    }

    // Per LANG.txt §4.4: Other types are not comparable
    runtime_error(&format!(
        "Cannot compare {} with {} using '<'",
        type_name(&left),
        type_name(&right)
    ))
}

/// Less-than-or-equal comparison
///
/// Per LANG.txt §4.4:
/// Only Integer, Decimal, and String support comparison operators.
#[no_mangle]
pub extern "C-unwind" fn rt_le(left: Value, right: Value) -> Value {
    // Integer comparison
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        return Value::from_bool(l <= r);
    }

    // Decimal comparison
    if let (Some(l), Some(r)) = (left.as_decimal(), right.as_decimal()) {
        return Value::from_bool(l <= r);
    }

    // Mixed Integer/Decimal comparison
    if let Some(l) = left.as_integer() {
        if let Some(r) = right.as_decimal() {
            return Value::from_bool((l as f64) <= r);
        }
    }

    if let Some(l) = left.as_decimal() {
        if let Some(r) = right.as_integer() {
            return Value::from_bool(l <= (r as f64));
        }
    }

    // String comparison
    if let (Some(l), Some(r)) = (left.as_string(), right.as_string()) {
        return Value::from_bool(l <= r);
    }

    // Per LANG.txt §4.4: Other types are not comparable
    runtime_error(&format!(
        "Cannot compare {} with {} using '<='",
        type_name(&left),
        type_name(&right)
    ))
}

/// Greater-than comparison
///
/// Per LANG.txt §4.4:
/// Only Integer, Decimal, and String support comparison operators.
#[no_mangle]
pub extern "C-unwind" fn rt_gt(left: Value, right: Value) -> Value {
    // Integer comparison
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        return Value::from_bool(l > r);
    }

    // Decimal comparison
    if let (Some(l), Some(r)) = (left.as_decimal(), right.as_decimal()) {
        return Value::from_bool(l > r);
    }

    // Mixed Integer/Decimal comparison
    if let Some(l) = left.as_integer() {
        if let Some(r) = right.as_decimal() {
            return Value::from_bool((l as f64) > r);
        }
    }

    if let Some(l) = left.as_decimal() {
        if let Some(r) = right.as_integer() {
            return Value::from_bool(l > (r as f64));
        }
    }

    // String comparison
    if let (Some(l), Some(r)) = (left.as_string(), right.as_string()) {
        return Value::from_bool(l > r);
    }

    // Per LANG.txt §4.4: Other types are not comparable
    runtime_error(&format!(
        "Cannot compare {} with {} using '>'",
        type_name(&left),
        type_name(&right)
    ))
}

/// Greater-than-or-equal comparison
///
/// Per LANG.txt §4.4:
/// Only Integer, Decimal, and String support comparison operators.
#[no_mangle]
pub extern "C-unwind" fn rt_ge(left: Value, right: Value) -> Value {
    // Integer comparison
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        return Value::from_bool(l >= r);
    }

    // Decimal comparison
    if let (Some(l), Some(r)) = (left.as_decimal(), right.as_decimal()) {
        return Value::from_bool(l >= r);
    }

    // Mixed Integer/Decimal comparison
    if let Some(l) = left.as_integer() {
        if let Some(r) = right.as_decimal() {
            return Value::from_bool((l as f64) >= r);
        }
    }

    if let Some(l) = left.as_decimal() {
        if let Some(r) = right.as_integer() {
            return Value::from_bool(l >= (r as f64));
        }
    }

    // String comparison
    if let (Some(l), Some(r)) = (left.as_string(), right.as_string()) {
        return Value::from_bool(l >= r);
    }

    // Per LANG.txt §4.4: Other types are not comparable
    runtime_error(&format!(
        "Cannot compare {} with {} using '>='",
        type_name(&left),
        type_name(&right)
    ))
}

/// Convert a Value to its string representation
/// Note: Uses the full format_value from builtins for collections
fn value_to_string(value: &Value) -> String {
    crate::builtins::format_value(value)
}

// ===== Closure Operations =====

use super::heap::ClosureObject;

/// Create a new closure with the given function pointer and captured values
///
/// Called from generated LLVM code to create closure objects.
///
/// # Safety
///
/// - `captures_ptr` must be a valid pointer to an array of `captures_count` Values,
///   or null if `captures_count` is 0
/// - The caller must ensure the captures array is valid for the duration of this call
///
/// Arguments:
/// - function_ptr: Pointer to the compiled function code
/// - arity: Number of parameters the function expects
/// - captures_ptr: Pointer to an array of captured values
/// - captures_count: Number of captured values
#[no_mangle]
pub unsafe extern "C" fn rt_make_closure(
    function_ptr: *const (),
    arity: u32,
    captures_ptr: *const Value,
    captures_count: usize,
) -> Value {
    // Collect captured values into a Vec
    let captures = if captures_count == 0 || captures_ptr.is_null() {
        Vec::new()
    } else {
        std::slice::from_raw_parts(captures_ptr, captures_count).to_vec()
    };

    let closure = ClosureObject::new(function_ptr, arity, captures);
    Value::from_closure(closure)
}

/// Call a closure with the given arguments
///
/// The closure's function expects the signature:
///   fn(env: *const ClosureObject, argc: u32, argv: *const Value) -> Value
///
/// This function also handles memoized closures by delegating to rt_call_memoized.
///
/// # Safety
/// The caller must ensure `argv` points to a valid array of `argc` Values.
#[no_mangle]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C-unwind" fn rt_call(callee: Value, argc: u32, argv: *const Value) -> Value {
    // Try regular closure first
    if let Some(closure) = callee.as_closure() {
        // Cast the function pointer to the expected signature
        let fn_ptr: extern "C" fn(*const ClosureObject, u32, *const Value) -> Value =
            unsafe { std::mem::transmute(closure.function_ptr) };

        // Call the function with the closure environment and arguments
        return fn_ptr(closure as *const ClosureObject, argc, argv);
    }

    // Try memoized closure
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
            let result = crate::builtins::call_closure(closure, &args);

            // Cache the result
            memoized.cache_result(args, result);

            return result;
        }

        // Inner value is not a closure - shouldn't happen with rt_memoize
        return Value::nil();
    }

    // Non-callable value - produce RuntimeErr
    runtime_error(&format!(
        "{} is not callable",
        type_name(&callee)
    ));
}

/// Get a captured value from a closure environment
///
/// Called from generated LLVM code to access captured values within a closure body.
///
/// # Safety
///
/// - `env_ptr` must be a valid pointer to a ClosureObject, or null
/// - The caller must ensure the closure object is valid for the duration of this call
#[no_mangle]
pub unsafe extern "C" fn rt_get_capture(env_ptr: *const ClosureObject, index: usize) -> Value {
    if env_ptr.is_null() {
        // No closure environment - shouldn't happen if codegen is correct
        return Value::nil();
    }

    let closure = &*env_ptr;
    closure.get_capture(index).unwrap_or_else(Value::nil)
}

// ===== Mutable Cell Operations =====
//
// Mutable cells are used to implement mutable variable capture in closures.
// When a mutable variable is captured by an inner closure, we wrap it in a cell
// so both the outer scope and the inner closure share the same mutable storage.

/// Create a new mutable cell containing the given value.
///
/// Allocates a heap object that can be shared between closures to enable
/// mutable captures (LANG.txt §8.3 counter pattern).
#[no_mangle]
pub extern "C" fn rt_cell_new(value: Value) -> Value {
    Value::from_cell(value)
}

/// Get the current value from a mutable cell.
///
/// # Safety
///
/// The `cell` argument must be a valid mutable cell Value, or this will panic.
#[no_mangle]
pub extern "C" fn rt_cell_get(cell: Value) -> Value {
    if let Some(cell_ptr) = cell.as_cell() {
        unsafe { (*cell_ptr).value }
    } else {
        runtime_error("rt_cell_get: expected a mutable cell")
    }
}

/// Set the value in a mutable cell.
///
/// # Safety
///
/// The `cell` argument must be a valid mutable cell Value, or this will panic.
/// This function mutates the cell in place - the old value is not decremented
/// (caller should handle reference counting if needed).
#[no_mangle]
pub extern "C" fn rt_cell_set(cell: Value, value: Value) -> Value {
    if let Some(cell_ptr) = cell.as_cell() {
        unsafe {
            (*cell_ptr).value = value;
        }
        value // Return the set value (assignment returns the assigned value)
    } else {
        runtime_error("rt_cell_set: expected a mutable cell")
    }
}
