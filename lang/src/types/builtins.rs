use crate::runtime::builtin_registry::BUILTIN_SPECS;
use crate::types::ty::Type;
use std::collections::HashMap;

/// Type signature for a built-in function
///
/// For polymorphic functions, `ret` may contain Type::Unknown which means
/// the return type depends on the argument types and must be computed
/// at the call site.
#[derive(Clone)]
pub struct BuiltinSignature {
    pub name: &'static str,
    pub params: Vec<ParamType>,
    pub ret: ReturnType,
}

/// Parameter type specification
#[derive(Clone)]
pub enum ParamType {
    /// A specific concrete type
    Concrete(Type),
    /// Any type (will be Unknown)
    Any,
    /// Any collection type (List, Set, Dict, String, Range, LazySequence)
    Collection,
    /// A function type with given arity
    Function(usize),
}

/// Return type specification
#[derive(Clone)]
pub enum ReturnType {
    /// A specific concrete type
    Concrete(Type),
    /// Same as the element type of a collection argument (by index)
    ElementOf(usize),
    /// Same as a specific argument type (by index)
    SameAs(usize),
    /// List of element type from collection argument
    ListOf(usize),
    /// List of the return type of a function argument (for map-like operations)
    ListOfFunctionReturn(usize),
    /// The result depends on runtime values (Unknown)
    Dynamic,
}

impl BuiltinSignature {
    fn new(name: &'static str, params: Vec<ParamType>, ret: ReturnType) -> Self {
        Self { name, params, ret }
    }
}

/// Built-in signature database
///
/// This returns type signatures for all built-in functions in the registry.
/// The signatures are used to infer return types for function calls.
pub fn builtin_signatures() -> HashMap<&'static str, BuiltinSignature> {
    let mut sigs = HashMap::new();
    for spec in BUILTIN_SPECS {
        let sig = builtin_signature_for(spec.name);
        sigs.insert(spec.name, sig);
    }

    sigs
}

fn builtin_signature_for(name: &'static str) -> BuiltinSignature {
    macro_rules! sig {
        ($params:expr, $ret:expr) => {
            BuiltinSignature::new(name, $params, $ret)
        };
    }

    match name {
        // ===== 11.1 Type Conversion =====
        "int" => sig!(vec![ParamType::Any], ReturnType::Concrete(Type::Int)),
        "ints" => sig!(
            vec![ParamType::Concrete(Type::String)],
            ReturnType::Concrete(Type::List(Box::new(Type::Int)))
        ),
        "list" => sig!(vec![ParamType::Collection], ReturnType::Dynamic),
        "set" => sig!(vec![ParamType::Collection], ReturnType::Dynamic),
        "dict" => sig!(vec![ParamType::Any], ReturnType::Dynamic),

        // ===== 11.2 Collection Access =====
        "get" => sig!(vec![ParamType::Any, ParamType::Collection], ReturnType::Dynamic),
        "size" => sig!(vec![ParamType::Collection], ReturnType::Concrete(Type::Int)),
        "first" => sig!(vec![ParamType::Collection], ReturnType::ElementOf(0)),
        "second" => sig!(vec![ParamType::Collection], ReturnType::ElementOf(0)),
        "last" => sig!(vec![ParamType::Collection], ReturnType::ElementOf(0)),
        "rest" => sig!(vec![ParamType::Collection], ReturnType::SameAs(0)),
        "keys" => sig!(vec![ParamType::Any], ReturnType::Dynamic),
        "values" => sig!(vec![ParamType::Any], ReturnType::Dynamic),

        // ===== 11.3 Collection Modification =====
        "push" => sig!(vec![ParamType::Any, ParamType::Collection], ReturnType::SameAs(1)),
        "assoc" => sig!(
            vec![ParamType::Any, ParamType::Any, ParamType::Collection],
            ReturnType::SameAs(2)
        ),
        "update" => sig!(
            vec![ParamType::Any, ParamType::Function(1), ParamType::Collection],
            ReturnType::SameAs(2)
        ),
        "update_d" => sig!(
            vec![
                ParamType::Any,
                ParamType::Any,
                ParamType::Function(1),
                ParamType::Collection
            ],
            ReturnType::SameAs(3)
        ),

        // ===== 11.4 Transformation =====
        "map" => sig!(
            vec![ParamType::Function(1), ParamType::Collection],
            ReturnType::ListOfFunctionReturn(0)
        ),
        "filter" => sig!(
            vec![ParamType::Function(1), ParamType::Collection],
            ReturnType::SameAs(1)
        ),
        "flat_map" => sig!(vec![ParamType::Function(1), ParamType::Collection], ReturnType::Dynamic),
        "filter_map" => sig!(vec![ParamType::Function(1), ParamType::Collection], ReturnType::Dynamic),
        "find_map" => sig!(vec![ParamType::Function(1), ParamType::Collection], ReturnType::Dynamic),

        // ===== 11.5 Reduction =====
        "reduce" => sig!(
            vec![ParamType::Function(2), ParamType::Collection],
            ReturnType::ElementOf(1)
        ),
        "fold" => sig!(
            vec![ParamType::Any, ParamType::Function(2), ParamType::Collection],
            ReturnType::SameAs(0)
        ),
        "fold_s" => sig!(
            vec![ParamType::Any, ParamType::Function(2), ParamType::Collection],
            ReturnType::SameAs(0)
        ),
        "scan" => sig!(
            vec![ParamType::Any, ParamType::Function(2), ParamType::Collection],
            ReturnType::Dynamic
        ),

        // ===== 11.6 Iteration =====
        "each" => sig!(
            vec![ParamType::Function(1), ParamType::Collection],
            ReturnType::Concrete(Type::Nil)
        ),

        // ===== 11.7 Search =====
        "find" => sig!(
            vec![ParamType::Function(1), ParamType::Collection],
            ReturnType::ElementOf(1)
        ),
        "count" => sig!(
            vec![ParamType::Function(1), ParamType::Collection],
            ReturnType::Concrete(Type::Int)
        ),

        // ===== 11.8 Aggregation =====
        "sum" => sig!(vec![ParamType::Collection], ReturnType::Dynamic),
        "max" => sig!(vec![ParamType::Any], ReturnType::Dynamic),
        "min" => sig!(vec![ParamType::Any], ReturnType::Dynamic),

        // ===== 11.9 Slicing & Ordering =====
        "skip" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Collection],
            ReturnType::SameAs(1)
        ),
        "take" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Collection],
            ReturnType::ListOf(1)
        ),
        "sort" => sig!(
            vec![ParamType::Function(2), ParamType::Collection],
            ReturnType::ListOf(1)
        ),
        "reverse" => sig!(vec![ParamType::Collection], ReturnType::Dynamic),
        "rotate" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Collection],
            ReturnType::SameAs(1)
        ),
        "chunk" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Collection],
            ReturnType::Dynamic
        ),

        // ===== 11.10 Set Operations =====
        "union" => sig!(
            vec![ParamType::Collection, ParamType::Collection],
            ReturnType::SameAs(0)
        ),
        "intersection" => sig!(
            vec![ParamType::Collection, ParamType::Collection],
            ReturnType::SameAs(0)
        ),

        // ===== 11.11 Predicates =====
        "includes?" => sig!(
            vec![ParamType::Collection, ParamType::Any],
            ReturnType::Concrete(Type::Bool)
        ),
        "excludes?" => sig!(
            vec![ParamType::Collection, ParamType::Any],
            ReturnType::Concrete(Type::Bool)
        ),
        "any?" => sig!(
            vec![ParamType::Function(1), ParamType::Collection],
            ReturnType::Concrete(Type::Bool)
        ),
        "all?" => sig!(
            vec![ParamType::Function(1), ParamType::Collection],
            ReturnType::Concrete(Type::Bool)
        ),

        // ===== 11.12 Generators =====
        "zip" => sig!(vec![ParamType::Collection], ReturnType::Dynamic),
        "repeat" => sig!(
            vec![ParamType::Any],
            ReturnType::Concrete(Type::LazySequence(Box::new(Type::Unknown)))
        ),
        "cycle" => sig!(
            vec![ParamType::Collection],
            ReturnType::Concrete(Type::LazySequence(Box::new(Type::Unknown)))
        ),
        "iterate" => sig!(
            vec![ParamType::Function(1), ParamType::Any],
            ReturnType::Concrete(Type::LazySequence(Box::new(Type::Unknown)))
        ),
        "combinations" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Collection],
            ReturnType::Dynamic
        ),
        "range" => sig!(
            vec![
                ParamType::Concrete(Type::Int),
                ParamType::Concrete(Type::Int),
                ParamType::Concrete(Type::Int)
            ],
            ReturnType::Concrete(Type::LazySequence(Box::new(Type::Int)))
        ),

        // ===== 11.13 String Functions =====
        "lines" => sig!(
            vec![ParamType::Concrete(Type::String)],
            ReturnType::Concrete(Type::List(Box::new(Type::String)))
        ),
        "split" => sig!(
            vec![ParamType::Concrete(Type::String), ParamType::Concrete(Type::String)],
            ReturnType::Concrete(Type::List(Box::new(Type::String)))
        ),
        "regex_match" => sig!(
            vec![ParamType::Concrete(Type::String), ParamType::Concrete(Type::String)],
            ReturnType::Dynamic
        ),
        "regex_match_all" => sig!(
            vec![ParamType::Concrete(Type::String), ParamType::Concrete(Type::String)],
            ReturnType::Dynamic
        ),
        "md5" => sig!(
            vec![ParamType::Concrete(Type::String)],
            ReturnType::Concrete(Type::String)
        ),
        "upper" => sig!(
            vec![ParamType::Concrete(Type::String)],
            ReturnType::Concrete(Type::String)
        ),
        "lower" => sig!(
            vec![ParamType::Concrete(Type::String)],
            ReturnType::Concrete(Type::String)
        ),
        "replace" => sig!(
            vec![
                ParamType::Concrete(Type::String),
                ParamType::Concrete(Type::String),
                ParamType::Concrete(Type::String)
            ],
            ReturnType::Concrete(Type::String)
        ),
        "join" => sig!(
            vec![ParamType::Concrete(Type::String), ParamType::Collection],
            ReturnType::Concrete(Type::String)
        ),

        // ===== 11.14 Math Functions =====
        "abs" => sig!(vec![ParamType::Any], ReturnType::SameAs(0)),
        "signum" => sig!(vec![ParamType::Any], ReturnType::Concrete(Type::Int)),
        "vec_add" => sig!(
            vec![ParamType::Collection, ParamType::Collection],
            ReturnType::SameAs(0)
        ),

        // ===== 11.15 Bitwise Functions =====
        "bit_and" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)],
            ReturnType::Concrete(Type::Int)
        ),
        "bit_or" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)],
            ReturnType::Concrete(Type::Int)
        ),
        "bit_xor" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)],
            ReturnType::Concrete(Type::Int)
        ),
        "bit_not" => sig!(vec![ParamType::Concrete(Type::Int)], ReturnType::Concrete(Type::Int)),
        "bit_shift_left" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)],
            ReturnType::Concrete(Type::Int)
        ),
        "bit_shift_right" => sig!(
            vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)],
            ReturnType::Concrete(Type::Int)
        ),

        // ===== 11.16 Utility Functions =====
        "id" => sig!(vec![ParamType::Any], ReturnType::SameAs(0)),
        "type" => sig!(vec![ParamType::Any], ReturnType::Concrete(Type::String)),
        "memoize" => sig!(vec![ParamType::Function(1)], ReturnType::SameAs(0)),
        "or" => sig!(vec![ParamType::Any, ParamType::Any], ReturnType::Dynamic),
        "and" => sig!(vec![ParamType::Any, ParamType::Any], ReturnType::Dynamic),
        // ===== External Functions =====
        "puts" => sig!(vec![ParamType::Any], ReturnType::Concrete(Type::Nil)),
        "read" => sig!(
            vec![ParamType::Concrete(Type::String)],
            ReturnType::Concrete(Type::String)
        ),
        "env" => sig!(vec![], ReturnType::Concrete(Type::Nil)),

        _ => panic!("Missing signature for builtin: {}", name),
    }
}

/// Compute the concrete return type for a builtin call given argument types
pub fn compute_return_type(sig: &BuiltinSignature, arg_types: &[Type]) -> Type {
    match &sig.ret {
        ReturnType::Concrete(ty) => ty.clone(),
        ReturnType::SameAs(idx) => arg_types.get(*idx).cloned().unwrap_or(Type::Unknown),
        ReturnType::ElementOf(idx) => arg_types.get(*idx).map(element_type_of).unwrap_or(Type::Unknown),
        ReturnType::ListOf(idx) => {
            let elem_ty = arg_types.get(*idx).map(element_type_of).unwrap_or(Type::Unknown);
            Type::List(Box::new(elem_ty))
        }
        ReturnType::ListOfFunctionReturn(idx) => {
            // Get the function argument at the specified index and extract its return type
            let ret_ty = arg_types
                .get(*idx)
                .and_then(|ty| {
                    if let Type::Function { ret, .. } = ty {
                        Some((**ret).clone())
                    } else {
                        None
                    }
                })
                .unwrap_or(Type::Unknown);
            Type::List(Box::new(ret_ty))
        }
        ReturnType::Dynamic => Type::Unknown,
    }
}

/// Extract the element type from a collection type
pub fn element_type_of(ty: &Type) -> Type {
    match ty {
        Type::List(elem) | Type::Set(elem) | Type::LazySequence(elem) => (**elem).clone(),
        Type::Dict(_, val) => (**val).clone(), // For dicts, element is the value type
        Type::String => Type::String,          // String elements are strings
        _ => Type::Unknown,
    }
}

/// Compute expected parameter types for a lambda argument at the given position
/// in a builtin call. Returns None if the parameter at that position is not a function,
/// or if expected types cannot be determined.
///
/// This enables bidirectional type inference: we flow type information "backward"
/// from how a lambda is used to determine its parameter types.
pub fn compute_expected_lambda_type(sig: &BuiltinSignature, arg_idx: usize, arg_types: &[Type]) -> Option<Type> {
    // Check if this parameter position expects a function
    let param = sig.params.get(arg_idx)?;

    match param {
        ParamType::Function(arity) => {
            // Compute expected parameter types based on the function and other arguments
            let expected_params = compute_lambda_param_types(sig.name, *arity, arg_types);
            let expected_ret = compute_lambda_return_type(sig.name, arg_types);

            Some(Type::Function {
                params: expected_params,
                ret: Box::new(expected_ret),
            })
        }
        _ => None, // Not a function parameter
    }
}

/// Compute expected parameter types for a lambda based on the builtin it's passed to
fn compute_lambda_param_types(builtin_name: &str, arity: usize, arg_types: &[Type]) -> Vec<Type> {
    match builtin_name {
        // filter(pred, collection) - pred takes element, returns Bool
        // map(mapper, collection) - mapper takes element
        // flat_map(mapper, collection) - mapper takes element
        // filter_map(mapper, collection) - mapper takes element
        // find_map(mapper, collection) - mapper takes element
        // each(fn, collection) - fn takes element
        // find(pred, collection) - pred takes element
        // any?(pred, collection) - pred takes element
        // all?(pred, collection) - pred takes element
        "filter" | "map" | "flat_map" | "filter_map" | "find_map" | "each" | "find" | "count" | "any?" | "all?" => {
            // Lambda is first arg (idx 0), collection is second arg (idx 1)
            if let Some(collection_ty) = arg_types.get(1) {
                let elem_ty = element_type_of(collection_ty);
                vec![elem_ty]
            } else {
                vec![Type::Unknown; arity]
            }
        }

        // reduce(fn, collection) - fn takes (elem, elem) -> elem
        "reduce" => {
            if let Some(collection_ty) = arg_types.get(1) {
                let elem_ty = element_type_of(collection_ty);
                vec![elem_ty.clone(), elem_ty]
            } else {
                vec![Type::Unknown; arity]
            }
        }

        // fold(init, fn, collection) - fn takes (acc, elem) -> acc
        // fold_s(init, fn, collection) - fn takes (acc, elem) -> acc
        // scan(init, fn, collection) - fn takes (acc, elem) -> acc
        "fold" | "fold_s" | "scan" => {
            // init is idx 0, fn is idx 1, collection is idx 2
            let acc_ty = arg_types.first().cloned().unwrap_or(Type::Unknown);
            let elem_ty = arg_types.get(2).map(element_type_of).unwrap_or(Type::Unknown);
            vec![acc_ty, elem_ty]
        }

        // update(key, fn, collection) - fn takes old_value -> new_value
        // update_d(key, default, fn, collection) - fn takes old_value -> new_value
        "update" => {
            // fn is at idx 1, collection is at idx 2
            if let Some(collection_ty) = arg_types.get(2) {
                let elem_ty = element_type_of(collection_ty);
                vec![elem_ty]
            } else {
                vec![Type::Unknown]
            }
        }
        "update_d" => {
            // default is at idx 1, fn is at idx 2, collection is at idx 3
            if let Some(collection_ty) = arg_types.get(3) {
                let elem_ty = element_type_of(collection_ty);
                vec![elem_ty]
            } else {
                vec![Type::Unknown]
            }
        }

        // iterate(fn, initial) - fn takes current -> next (same type)
        "iterate" => {
            // fn is idx 0, initial is idx 1
            let init_ty = arg_types.get(1).cloned().unwrap_or(Type::Unknown);
            vec![init_ty]
        }

        // memoize(fn) - can't determine params without more info
        "memoize" => {
            vec![Type::Unknown; arity]
        }

        _ => vec![Type::Unknown; arity],
    }
}

/// Compute expected return type for a lambda based on the builtin it's passed to
fn compute_lambda_return_type(builtin_name: &str, arg_types: &[Type]) -> Type {
    match builtin_name {
        // Predicates always return Bool
        "filter" | "find" | "count" | "any?" | "all?" => Type::Bool,

        // fold/scan return same type as accumulator
        "fold" | "fold_s" | "scan" | "reduce" => {
            // For fold, return type should match initial value type
            // For reduce, return type matches element type
            if builtin_name == "reduce" {
                arg_types.get(1).map(element_type_of).unwrap_or(Type::Unknown)
            } else {
                arg_types.first().cloned().unwrap_or(Type::Unknown)
            }
        }

        // iterate returns same type as input
        "iterate" => arg_types.get(1).cloned().unwrap_or(Type::Unknown),

        // For map, flat_map, etc., we can't know the return type without analyzing the lambda body
        _ => Type::Unknown,
    }
}
