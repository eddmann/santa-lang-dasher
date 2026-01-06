//! Runtime library for santa-lang Dasher compiler.
//!
//! This crate provides the runtime support functions called by compiled santa-lang code.

// Allow unsafe operations in unsafe functions without explicit blocks (edition 2024 change)
#![allow(unsafe_op_in_unsafe_fn)]

pub mod break_handling;
pub mod builtin_registry;
pub mod builtins;
pub mod collections;
pub mod heap;
pub mod operations;
pub mod refcount;
pub mod string;
pub mod value;

// Re-export im crate for use in lang crate
pub use im;

#[cfg(test)]
mod tests;
