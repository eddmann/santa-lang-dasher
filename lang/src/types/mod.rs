mod ty;
mod infer;
mod builtins;
mod unify;

#[cfg(test)]
mod tests;

pub use ty::{Type, TypedExpr, TypedStmt, TypedProgram};
pub use infer::TypeInference;
pub use builtins::builtin_signatures;
