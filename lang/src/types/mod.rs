mod builtins;
mod infer;
mod ty;
mod unify;

#[cfg(test)]
mod tests;

pub use builtins::{builtin_signatures, compute_return_type, BuiltinSignature, ParamType, ReturnType};
pub use infer::TypeInference;
pub use ty::{Type, TypedExpr, TypedProgram, TypedStmt};
