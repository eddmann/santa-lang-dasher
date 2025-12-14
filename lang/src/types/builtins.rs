use std::collections::HashMap;
use crate::types::ty::Type;

/// Type signature for a built-in function
pub struct BuiltinSignature {
    pub name: &'static str,
    pub params: Vec<Type>,
    pub ret: Type,
}

/// Built-in signature database
pub fn builtin_signatures() -> HashMap<&'static str, BuiltinSignature> {
    // TODO: Implement all 65 built-in function signatures
    HashMap::new()
}
