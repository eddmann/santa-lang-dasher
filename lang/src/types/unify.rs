use crate::types::ty::Type;
use std::collections::HashMap;

/// Unification engine for type variables
pub struct Unifier {
    /// Substitutions from unification
    pub substitutions: HashMap<u32, Type>,
}

impl Unifier {
    pub fn new() -> Self {
        Self {
            substitutions: HashMap::new(),
        }
    }

    /// Attempt to unify two types, returning the more specific one
    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<Type, String> {
        match (a, b) {
            // Same concrete types unify
            (Type::Int, Type::Int) => Ok(Type::Int),
            (Type::Decimal, Type::Decimal) => Ok(Type::Decimal),
            (Type::String, Type::String) => Ok(Type::String),
            (Type::Bool, Type::Bool) => Ok(Type::Bool),
            (Type::Nil, Type::Nil) => Ok(Type::Nil),

            // TypeVar unifies with anything, records substitution
            (Type::TypeVar(id), other) | (other, Type::TypeVar(id)) => {
                self.substitutions.insert(*id, other.clone());
                Ok(other.clone())
            }

            // Unknown unifies with anything, result is Unknown
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(Type::Unknown),

            // Collection types unify element types
            (Type::List(a), Type::List(b)) => {
                let elem = self.unify(a, b)?;
                Ok(Type::List(Box::new(elem)))
            }
            (Type::Set(a), Type::Set(b)) => {
                let elem = self.unify(a, b)?;
                Ok(Type::Set(Box::new(elem)))
            }
            (Type::Dict(k1, v1), Type::Dict(k2, v2)) => {
                let key = self.unify(k1, k2)?;
                let value = self.unify(v1, v2)?;
                Ok(Type::Dict(Box::new(key), Box::new(value)))
            }
            (Type::LazySequence(a), Type::LazySequence(b)) => {
                let elem = self.unify(a, b)?;
                Ok(Type::LazySequence(Box::new(elem)))
            }

            // Incompatible types
            _ => Err(format!("Cannot unify {:?} and {:?}", a, b)),
        }
    }

    /// Apply substitutions to a type
    #[allow(dead_code)]
    pub fn apply_substitutions(&self, ty: &Type) -> Type {
        match ty {
            Type::TypeVar(id) => {
                if let Some(substitution) = self.substitutions.get(id) {
                    // Recursively apply substitutions
                    self.apply_substitutions(substitution)
                } else {
                    ty.clone()
                }
            }
            Type::List(elem) => Type::List(Box::new(self.apply_substitutions(elem))),
            Type::Set(elem) => Type::Set(Box::new(self.apply_substitutions(elem))),
            Type::Dict(k, v) => Type::Dict(
                Box::new(self.apply_substitutions(k)),
                Box::new(self.apply_substitutions(v)),
            ),
            Type::LazySequence(elem) => {
                Type::LazySequence(Box::new(self.apply_substitutions(elem)))
            }
            Type::Function { params, ret } => Type::Function {
                params: params.iter().map(|p| self.apply_substitutions(p)).collect(),
                ret: Box::new(self.apply_substitutions(ret)),
            },
            _ => ty.clone(),
        }
    }
}
