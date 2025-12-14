use super::value::Value;

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

    // TODO: Handle List + List, Set + Set, Dict + Dict
    // For now, return nil for unsupported operations
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
pub extern "C" fn rt_div(left: Value, right: Value) -> Value {
    // Handle integers with floored division
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        if r == 0 {
            // TODO: Return RuntimeErr for division by zero
            return Value::nil();
        }
        return Value::from_integer(floored_div(l, r));
    }

    // Handle decimals (normal division)
    if let (Some(l), Some(r)) = (left.as_decimal(), right.as_decimal()) {
        if r == 0.0 {
            // TODO: Return RuntimeErr for division by zero
            return Value::nil();
        }
        return Value::from_decimal(l / r);
    }

    // Handle mixed Integer + Decimal (left type wins)
    if let Some(l) = left.as_integer() {
        if let Some(r) = right.as_decimal() {
            if r == 0.0 {
                return Value::nil();
            }
            return Value::from_integer((l as f64 / r) as i64);
        }
    }

    // Handle mixed Decimal + Integer (left type wins)
    if let Some(l) = left.as_decimal() {
        if let Some(r) = right.as_integer() {
            if r == 0 {
                return Value::nil();
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
pub extern "C" fn rt_mod(left: Value, right: Value) -> Value {
    // Handle integers with floored modulo
    if let (Some(l), Some(r)) = (left.as_integer(), right.as_integer()) {
        if r == 0 {
            // TODO: Return RuntimeErr for modulo by zero
            return Value::nil();
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
/// Per LANG.txt §4 and PLAN.md §8.5:
/// Only Integer, Decimal, and String support comparison
#[no_mangle]
pub extern "C" fn rt_lt(left: Value, right: Value) -> Value {
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

    // TODO: Return RuntimeErr for unsupported types (List, Set, Dict, etc.)
    // For now, return nil
    Value::nil()
}

/// Less-than-or-equal comparison
#[no_mangle]
pub extern "C" fn rt_le(left: Value, right: Value) -> Value {
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

    Value::nil()
}

/// Greater-than comparison
#[no_mangle]
pub extern "C" fn rt_gt(left: Value, right: Value) -> Value {
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

    Value::nil()
}

/// Greater-than-or-equal comparison
#[no_mangle]
pub extern "C" fn rt_ge(left: Value, right: Value) -> Value {
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

    Value::nil()
}

/// Convert a Value to its string representation
fn value_to_string(value: &Value) -> String {
    if let Some(i) = value.as_integer() {
        i.to_string()
    } else if let Some(d) = value.as_decimal() {
        d.to_string()
    } else if let Some(s) = value.as_string() {
        s.to_string()
    } else if let Some(b) = value.as_bool() {
        b.to_string()
    } else if value.is_nil() {
        "nil".to_string()
    } else {
        // TODO: Handle collection string representations
        "<?>".to_string()
    }
}
