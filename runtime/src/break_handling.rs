//! Break statement handling for iteration contexts.
//!
//! Uses thread-local storage to signal break from within closures to their
//! iteration context (fold, reduce, each, etc.).

use crate::operations::runtime_error;
use crate::value::Value;
use std::cell::RefCell;

thread_local! {
    /// Flag indicating whether a break has occurred
    static BREAK_OCCURRED: RefCell<bool> = const { RefCell::new(false) };
    /// The value to return when break occurs
    static BREAK_VALUE: RefCell<Option<Value>> = const { RefCell::new(None) };
    /// Depth counter for active iteration contexts
    static ITERATION_DEPTH: RefCell<u32> = const { RefCell::new(0) };
}

/// Signal a break with the given value.
/// Called from compiled code when a `break value` statement executes.
#[no_mangle]
pub extern "C" fn rt_break(value: Value) -> Value {
    if !in_iteration() {
        runtime_error("break outside iteration");
    }
    BREAK_OCCURRED.with(|flag| {
        *flag.borrow_mut() = true;
    });
    BREAK_VALUE.with(|val| {
        *val.borrow_mut() = Some(value);
    });
    // Return the value (caller should ignore this if break occurred)
    value
}

/// Check if a break has occurred.
/// Returns true if break was signaled since last reset.
pub fn break_occurred() -> bool {
    BREAK_OCCURRED.with(|flag| *flag.borrow())
}

/// Get the break value and reset the break state.
/// Returns Some(value) if break occurred, None otherwise.
/// Resets the break flag so subsequent iterations can run normally.
pub fn take_break_value() -> Option<Value> {
    let occurred = BREAK_OCCURRED.with(|flag| {
        let occurred = *flag.borrow();
        *flag.borrow_mut() = false;
        occurred
    });

    if occurred {
        BREAK_VALUE.with(|val| val.borrow_mut().take())
    } else {
        None
    }
}

/// Reset the break state without retrieving the value.
/// Used when entering a new iteration context.
pub fn reset_break_state() {
    BREAK_OCCURRED.with(|flag| {
        *flag.borrow_mut() = false;
    });
    BREAK_VALUE.with(|val| {
        *val.borrow_mut() = None;
    });
}

/// Enter an iteration context. Resets break state for this context.
pub fn enter_iteration() {
    ITERATION_DEPTH.with(|depth| {
        *depth.borrow_mut() += 1;
    });
    reset_break_state();
}

/// Exit an iteration context.
pub fn exit_iteration() {
    ITERATION_DEPTH.with(|depth| {
        let mut current = depth.borrow_mut();
        if *current > 0 {
            *current -= 1;
        }
    });
    reset_break_state();
}

fn in_iteration() -> bool {
    ITERATION_DEPTH.with(|depth| *depth.borrow() > 0)
}
