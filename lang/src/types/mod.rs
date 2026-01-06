mod builtins;
mod infer;
mod ty;
mod unify;

#[cfg(test)]
mod tests;

pub use builtins::{BuiltinSignature, ParamType, ReturnType, builtin_signatures, compute_return_type};
pub use infer::TypeInference;
pub use ty::{Type, TypedExpr, TypedProgram, TypedStmt};
