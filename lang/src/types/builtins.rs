use std::collections::HashMap;
use crate::types::ty::Type;

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
/// This returns type signatures for all 65 built-in functions (excluding `evaluate`).
/// The signatures are used to infer return types for function calls.
pub fn builtin_signatures() -> HashMap<&'static str, BuiltinSignature> {
    let mut sigs = HashMap::new();

    // Helper macro to insert signatures
    macro_rules! sig {
        ($name:expr, $params:expr, $ret:expr) => {
            sigs.insert($name, BuiltinSignature::new($name, $params, $ret));
        };
    }

    // ===== 11.1 Type Conversion =====
    sig!("int", vec![ParamType::Any], ReturnType::Concrete(Type::Int));
    sig!("ints", vec![ParamType::Concrete(Type::String)], ReturnType::Concrete(Type::List(Box::new(Type::Int))));
    sig!("list", vec![ParamType::Collection], ReturnType::Dynamic); // Returns List but element type varies
    sig!("set", vec![ParamType::Collection], ReturnType::Dynamic);
    sig!("dict", vec![ParamType::Any], ReturnType::Dynamic);

    // ===== 11.2 Collection Access =====
    sig!("get", vec![ParamType::Any, ParamType::Collection], ReturnType::Dynamic);
    sig!("size", vec![ParamType::Collection], ReturnType::Concrete(Type::Int));
    sig!("first", vec![ParamType::Collection], ReturnType::ElementOf(0));
    sig!("second", vec![ParamType::Collection], ReturnType::ElementOf(0));
    sig!("last", vec![ParamType::Collection], ReturnType::ElementOf(0));
    sig!("rest", vec![ParamType::Collection], ReturnType::SameAs(0));
    sig!("keys", vec![ParamType::Any], ReturnType::Dynamic); // Dict -> List of key types
    sig!("values", vec![ParamType::Any], ReturnType::Dynamic); // Dict -> List of value types

    // ===== 11.3 Collection Modification =====
    sig!("push", vec![ParamType::Any, ParamType::Collection], ReturnType::SameAs(1));
    sig!("assoc", vec![ParamType::Any, ParamType::Any, ParamType::Collection], ReturnType::SameAs(2));
    sig!("update", vec![ParamType::Any, ParamType::Function(1), ParamType::Collection], ReturnType::SameAs(2));
    sig!("update_d", vec![ParamType::Any, ParamType::Any, ParamType::Function(1), ParamType::Collection], ReturnType::SameAs(3));

    // ===== 11.4 Transformation =====
    sig!("map", vec![ParamType::Function(1), ParamType::Collection], ReturnType::ListOfFunctionReturn(0)); // List of mapper's return type
    sig!("filter", vec![ParamType::Function(1), ParamType::Collection], ReturnType::SameAs(1));
    sig!("flat_map", vec![ParamType::Function(1), ParamType::Collection], ReturnType::Dynamic);
    sig!("filter_map", vec![ParamType::Function(1), ParamType::Collection], ReturnType::Dynamic);
    sig!("find_map", vec![ParamType::Function(1), ParamType::Collection], ReturnType::Dynamic);

    // ===== 11.5 Reduction =====
    sig!("reduce", vec![ParamType::Function(2), ParamType::Collection], ReturnType::ElementOf(1));
    sig!("fold", vec![ParamType::Any, ParamType::Function(2), ParamType::Collection], ReturnType::SameAs(0));
    sig!("fold_s", vec![ParamType::Any, ParamType::Function(2), ParamType::Collection], ReturnType::SameAs(0));
    sig!("scan", vec![ParamType::Any, ParamType::Function(2), ParamType::Collection], ReturnType::Dynamic);

    // ===== 11.6 Iteration =====
    sig!("each", vec![ParamType::Function(1), ParamType::Collection], ReturnType::Concrete(Type::Nil));

    // ===== 11.7 Search =====
    sig!("find", vec![ParamType::Function(1), ParamType::Collection], ReturnType::ElementOf(1));
    sig!("count", vec![ParamType::Any, ParamType::Collection], ReturnType::Concrete(Type::Int));

    // ===== 11.8 Aggregation =====
    sig!("sum", vec![ParamType::Collection], ReturnType::Dynamic); // Int or Decimal depending on elements
    sig!("max", vec![ParamType::Any], ReturnType::Dynamic); // Varargs or collection
    sig!("min", vec![ParamType::Any], ReturnType::Dynamic);

    // ===== 11.9 Slicing & Ordering =====
    sig!("skip", vec![ParamType::Concrete(Type::Int), ParamType::Collection], ReturnType::SameAs(1));
    sig!("take", vec![ParamType::Concrete(Type::Int), ParamType::Collection], ReturnType::ListOf(1));
    sig!("sort", vec![ParamType::Collection], ReturnType::SameAs(0));
    sig!("reverse", vec![ParamType::Collection], ReturnType::SameAs(0));
    sig!("rotate", vec![ParamType::Concrete(Type::Int), ParamType::Collection], ReturnType::SameAs(1));
    sig!("chunk", vec![ParamType::Concrete(Type::Int), ParamType::Collection], ReturnType::Dynamic);

    // ===== 11.10 Set Operations =====
    sig!("union", vec![ParamType::Collection, ParamType::Collection], ReturnType::SameAs(0));
    sig!("intersection", vec![ParamType::Collection, ParamType::Collection], ReturnType::SameAs(0));

    // ===== 11.11 Predicates =====
    sig!("includes?", vec![ParamType::Any, ParamType::Collection], ReturnType::Concrete(Type::Bool));
    sig!("excludes?", vec![ParamType::Any, ParamType::Collection], ReturnType::Concrete(Type::Bool));
    sig!("any?", vec![ParamType::Function(1), ParamType::Collection], ReturnType::Concrete(Type::Bool));
    sig!("all?", vec![ParamType::Function(1), ParamType::Collection], ReturnType::Concrete(Type::Bool));

    // ===== 11.12 Generators =====
    sig!("zip", vec![ParamType::Collection], ReturnType::Dynamic); // Varargs collections
    sig!("repeat", vec![ParamType::Any], ReturnType::Concrete(Type::LazySequence(Box::new(Type::Unknown))));
    sig!("cycle", vec![ParamType::Collection], ReturnType::Concrete(Type::LazySequence(Box::new(Type::Unknown))));
    sig!("iterate", vec![ParamType::Function(1), ParamType::Any], ReturnType::Concrete(Type::LazySequence(Box::new(Type::Unknown))));
    sig!("combinations", vec![ParamType::Concrete(Type::Int), ParamType::Collection], ReturnType::Dynamic);
    sig!("range", vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)], ReturnType::Concrete(Type::LazySequence(Box::new(Type::Int))));

    // ===== 11.13 String Functions =====
    sig!("lines", vec![ParamType::Concrete(Type::String)], ReturnType::Concrete(Type::List(Box::new(Type::String))));
    sig!("split", vec![ParamType::Concrete(Type::String), ParamType::Concrete(Type::String)], ReturnType::Concrete(Type::List(Box::new(Type::String))));
    sig!("regex_match", vec![ParamType::Concrete(Type::String), ParamType::Concrete(Type::String)], ReturnType::Dynamic);
    sig!("regex_match_all", vec![ParamType::Concrete(Type::String), ParamType::Concrete(Type::String)], ReturnType::Dynamic);
    sig!("md5", vec![ParamType::Concrete(Type::String)], ReturnType::Concrete(Type::String));
    sig!("upper", vec![ParamType::Concrete(Type::String)], ReturnType::Concrete(Type::String));
    sig!("lower", vec![ParamType::Concrete(Type::String)], ReturnType::Concrete(Type::String));
    sig!("replace", vec![ParamType::Concrete(Type::String), ParamType::Concrete(Type::String), ParamType::Concrete(Type::String)], ReturnType::Concrete(Type::String));
    sig!("join", vec![ParamType::Concrete(Type::String), ParamType::Collection], ReturnType::Concrete(Type::String));

    // ===== 11.14 Math Functions =====
    sig!("abs", vec![ParamType::Any], ReturnType::SameAs(0)); // Preserves Int/Decimal
    sig!("signum", vec![ParamType::Any], ReturnType::Concrete(Type::Int));
    sig!("vec_add", vec![ParamType::Collection, ParamType::Collection], ReturnType::SameAs(0));

    // ===== 11.15 Bitwise Functions =====
    sig!("bit_and", vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)], ReturnType::Concrete(Type::Int));
    sig!("bit_or", vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)], ReturnType::Concrete(Type::Int));
    sig!("bit_xor", vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)], ReturnType::Concrete(Type::Int));
    sig!("bit_not", vec![ParamType::Concrete(Type::Int)], ReturnType::Concrete(Type::Int));
    sig!("bit_shift_left", vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)], ReturnType::Concrete(Type::Int));
    sig!("bit_shift_right", vec![ParamType::Concrete(Type::Int), ParamType::Concrete(Type::Int)], ReturnType::Concrete(Type::Int));

    // ===== 11.16 Utility Functions =====
    sig!("id", vec![ParamType::Any], ReturnType::SameAs(0));
    sig!("type", vec![ParamType::Any], ReturnType::Concrete(Type::String));
    sig!("memoize", vec![ParamType::Function(1)], ReturnType::SameAs(0));
    sig!("or", vec![ParamType::Any, ParamType::Any], ReturnType::Dynamic);
    sig!("and", vec![ParamType::Any, ParamType::Any], ReturnType::Dynamic);
    // Note: evaluate() is out of scope for Dasher (AOT limitation)

    // ===== External Functions =====
    sig!("puts", vec![ParamType::Any], ReturnType::Concrete(Type::Nil));
    sig!("read", vec![ParamType::Concrete(Type::String)], ReturnType::Concrete(Type::String));
    sig!("env", vec![], ReturnType::Concrete(Type::Nil));

    sigs
}

/// Compute the concrete return type for a builtin call given argument types
pub fn compute_return_type(sig: &BuiltinSignature, arg_types: &[Type]) -> Type {
    match &sig.ret {
        ReturnType::Concrete(ty) => ty.clone(),
        ReturnType::SameAs(idx) => {
            arg_types.get(*idx).cloned().unwrap_or(Type::Unknown)
        }
        ReturnType::ElementOf(idx) => {
            arg_types.get(*idx).map(element_type_of).unwrap_or(Type::Unknown)
        }
        ReturnType::ListOf(idx) => {
            let elem_ty = arg_types.get(*idx).map(element_type_of).unwrap_or(Type::Unknown);
            Type::List(Box::new(elem_ty))
        }
        ReturnType::ListOfFunctionReturn(idx) => {
            // Get the function argument at the specified index and extract its return type
            let ret_ty = arg_types.get(*idx)
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
        Type::String => Type::String, // String elements are strings
        _ => Type::Unknown,
    }
}

/// Compute expected parameter types for a lambda argument at the given position
/// in a builtin call. Returns None if the parameter at that position is not a function,
/// or if expected types cannot be determined.
///
/// This enables bidirectional type inference: we flow type information "backward"
/// from how a lambda is used to determine its parameter types.
pub fn compute_expected_lambda_type(
    sig: &BuiltinSignature,
    arg_idx: usize,
    arg_types: &[Type],
) -> Option<Type> {
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
        "filter" | "map" | "flat_map" | "filter_map" | "find_map" | "each" | "find" | "any?" | "all?" => {
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
        "filter" | "find" | "any?" | "all?" => Type::Bool,

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
        "iterate" => {
            arg_types.get(1).cloned().unwrap_or(Type::Unknown)
        }

        // For map, flat_map, etc., we can't know the return type without analyzing the lambda body
        _ => Type::Unknown,
    }
}
