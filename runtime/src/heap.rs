use im;
use crate::operations::runtime_error;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::AtomicU32;
use unicode_segmentation::UnicodeSegmentation;

/// Type tag for heap-allocated objects
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeTag {
    String,
    Decimal,      // Boxed decimal (for large values if needed)
    BoxedInteger, // For integers > 61 bits
    List,
    Set,
    Dict,
    Function,
    Closure,
    LazySequence,
    MutableCell,
    MemoizedClosure,    // Closure with memoization cache
    PartialApplication, // Closure with some args already applied
}

/// Header for all heap-allocated objects
#[repr(C)]
pub struct ObjectHeader {
    pub refcount: AtomicU32,
    pub type_tag: TypeTag,
}

impl Clone for ObjectHeader {
    fn clone(&self) -> Self {
        ObjectHeader {
            refcount: AtomicU32::new(self.refcount.load(std::sync::atomic::Ordering::Relaxed)),
            type_tag: self.type_tag,
        }
    }
}

impl ObjectHeader {
    pub fn new(type_tag: TypeTag) -> Self {
        ObjectHeader {
            refcount: AtomicU32::new(1), // Start with refcount of 1
            type_tag,
        }
    }
}

/// String heap object
/// Stores UTF-8 data with grapheme-cluster indexing support
#[repr(C)]
pub struct StringObject {
    pub header: ObjectHeader,
    pub data: String,
}

impl StringObject {
    pub fn new(s: impl Into<String>) -> Box<Self> {
        Box::new(StringObject {
            header: ObjectHeader::new(TypeTag::String),
            data: s.into(),
        })
    }

    pub fn as_str(&self) -> &str {
        &self.data
    }

    /// Get grapheme cluster at index (LANG.txt §3.3)
    pub fn grapheme_at(&self, index: usize) -> Option<&str> {
        self.data.graphemes(true).nth(index)
    }

    /// Number of grapheme clusters
    pub fn grapheme_len(&self) -> usize {
        self.data.graphemes(true).count()
    }

    /// Check if string is empty (for truthiness)
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

/// List heap object using persistent vector
#[repr(C)]
pub struct ListObject {
    pub header: ObjectHeader,
    pub data: im::Vector<super::value::Value>,
}

impl ListObject {
    pub fn new(elements: im::Vector<super::value::Value>) -> Box<Self> {
        Box::new(ListObject {
            header: ObjectHeader::new(TypeTag::List),
            data: elements,
        })
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

/// Set heap object using persistent hash set
#[repr(C)]
pub struct SetObject {
    pub header: ObjectHeader,
    pub data: im::HashSet<super::value::Value>,
}

impl SetObject {
    pub fn new(elements: im::HashSet<super::value::Value>) -> Box<Self> {
        Box::new(SetObject {
            header: ObjectHeader::new(TypeTag::Set),
            data: elements,
        })
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

/// Dict heap object using persistent hash map
#[repr(C)]
pub struct DictObject {
    pub header: ObjectHeader,
    pub data: im::HashMap<super::value::Value, super::value::Value>,
}

impl DictObject {
    pub fn new(entries: im::HashMap<super::value::Value, super::value::Value>) -> Box<Self> {
        Box::new(DictObject {
            header: ObjectHeader::new(TypeTag::Dict),
            data: entries,
        })
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

/// Mutable cell for captured variables (LANG.txt §8.3)
#[repr(C)]
pub struct MutableCellObject {
    pub header: ObjectHeader,
    pub value: super::value::Value,
}

impl MutableCellObject {
    pub fn new(value: super::value::Value) -> Box<Self> {
        Box::new(MutableCellObject {
            header: ObjectHeader::new(TypeTag::MutableCell),
            value,
        })
    }

    pub fn get(&self) -> super::value::Value {
        self.value
    }

    pub fn set(&mut self, value: super::value::Value) {
        self.value = value;
    }
}

/// Closure heap object (LANG.txt §8.3)
/// Closures store a function pointer and captured environment values.
///
/// The function signature for closure functions is:
///   fn(env: *const ClosureObject, argc: u32, argv: *const Value) -> Value
///
/// Where `env` points to this closure object, allowing access to captured values.
#[repr(C)]
pub struct ClosureObject {
    pub header: ObjectHeader,
    /// Pointer to the compiled function code
    pub function_ptr: *const (),
    /// Number of parameters the function expects (before rest param)
    pub arity: u32,
    /// Whether this function has a rest parameter (..args) - 0 or 1
    pub has_rest: u8,
    /// Captured environment values (flexible array)
    pub captures: Vec<super::value::Value>,
}

impl ClosureObject {
    pub fn new(
        function_ptr: *const (),
        arity: u32,
        has_rest: bool,
        captures: Vec<super::value::Value>,
    ) -> Box<Self> {
        Box::new(ClosureObject {
            header: ObjectHeader::new(TypeTag::Closure),
            function_ptr,
            arity,
            has_rest: if has_rest { 1 } else { 0 },
            captures,
        })
    }

    pub fn get_capture(&self, index: usize) -> Option<super::value::Value> {
        self.captures.get(index).copied()
    }
}

/// Memoized closure heap object (LANG.txt §8.10)
/// A closure wrapper that caches results based on arguments.
///
/// The cache uses a HashMap keyed by a vector of argument values.
/// Results are stored and returned on subsequent calls with the same arguments.
#[repr(C)]
pub struct MemoizedClosureObject {
    pub header: ObjectHeader,
    /// The original closure being memoized
    pub inner_closure: super::value::Value,
    /// Arity (same as inner closure)
    pub arity: u32,
    /// Cache: arguments -> result
    /// We use RefCell for interior mutability since the cache updates on each call
    pub cache: std::cell::RefCell<
        std::collections::HashMap<Vec<super::value::Value>, super::value::Value>,
    >,
}

impl MemoizedClosureObject {
    pub fn new(inner_closure: super::value::Value, arity: u32) -> Box<Self> {
        Box::new(MemoizedClosureObject {
            header: ObjectHeader::new(TypeTag::MemoizedClosure),
            inner_closure,
            arity,
            cache: std::cell::RefCell::new(std::collections::HashMap::new()),
        })
    }

    /// Look up a cached result for the given arguments
    pub fn get_cached(&self, args: &[super::value::Value]) -> Option<super::value::Value> {
        let cache = self.cache.borrow();
        cache.get(args).copied()
    }

    /// Store a result in the cache
    pub fn cache_result(&self, args: Vec<super::value::Value>, result: super::value::Value) {
        let mut cache = self.cache.borrow_mut();
        cache.insert(args, result);
    }
}

/// Partial application object - stores a closure with some arguments already applied
///
/// When a function is called with fewer arguments than its arity, a partial
/// application is created that captures the provided arguments. When called
/// with more arguments, the accumulated args are combined and the original
/// function is called.
#[repr(C)]
pub struct PartialApplicationObject {
    pub header: ObjectHeader,
    /// The original closure being partially applied
    pub closure: super::value::Value,
    /// Arguments already provided
    pub args: Vec<super::value::Value>,
    /// Remaining arity (original arity - args.len())
    pub remaining_arity: u32,
}

impl PartialApplicationObject {
    pub fn new(
        closure: super::value::Value,
        args: Vec<super::value::Value>,
        remaining_arity: u32,
    ) -> Box<Self> {
        Box::new(PartialApplicationObject {
            header: ObjectHeader::new(TypeTag::PartialApplication),
            closure,
            args,
            remaining_arity,
        })
    }
}

/// Lazy sequence variant types (LANG.txt §11.12-11.13)
///
/// Lazy sequences represent potentially infinite sequences that are
/// evaluated on demand. They support operations like take, first, skip.
#[derive(Clone)]
pub enum LazySeqKind {
    /// repeat(value) - infinite repetition of a single value
    Repeat { value: super::value::Value },

    /// cycle(collection) - infinite cycle through a collection
    Cycle {
        source: im::Vector<super::value::Value>,
        index: usize,
    },

    /// iterate(generator, initial) - generated sequence
    /// Uses Rc<RefCell<>> for mutable state that persists across clones,
    /// allowing efficient indexed access without recomputing from start.
    Iterate {
        generator: super::value::Value,                   // Closure
        current: Rc<RefCell<super::value::Value>>,        // Mutable current value
        index: Rc<RefCell<usize>>,                        // Current index (for caching)
    },

    /// Range-based lazy sequence (from .. syntax)
    Range {
        current: i64,
        end: Option<i64>,
        inclusive: bool,
        step: i64,
    },

    /// map(fn, lazy_seq) - lazy mapped sequence
    Map {
        source: Box<LazySequenceObject>,
        mapper: super::value::Value, // Closure
    },

    /// filter(fn, lazy_seq) - lazy filtered sequence
    Filter {
        source: Box<LazySequenceObject>,
        predicate: super::value::Value, // Closure
    },

    /// filter_map(fn, lazy_seq) - lazy map+filter sequence
    FilterMap {
        source: Box<LazySequenceObject>,
        mapper: super::value::Value, // Closure
    },

    /// skip(n, lazy_seq) - skip first n elements
    Skip {
        source: Box<LazySequenceObject>,
        remaining: usize,
    },

    /// combinations(size, collection) - all combinations of given size
    Combinations {
        source: Vec<super::value::Value>,
        size: usize,
        indices: Vec<usize>,
        done: bool,
    },

    /// zip(collections...) - zipped sequences
    Zip { sources: Vec<LazySequenceObject> },
}

/// Lazy sequence heap object (LANG.txt §11.12-11.13)
#[repr(C)]
#[derive(Clone)]
pub struct LazySequenceObject {
    pub header: ObjectHeader,
    pub kind: LazySeqKind,
}

impl LazySequenceObject {
    pub fn new(kind: LazySeqKind) -> Box<Self> {
        Box::new(LazySequenceObject {
            header: ObjectHeader::new(TypeTag::LazySequence),
            kind,
        })
    }

    /// Create a repeat sequence
    pub fn repeat(value: super::value::Value) -> Box<Self> {
        Self::new(LazySeqKind::Repeat { value })
    }

    /// Create a cycle sequence
    pub fn cycle(source: im::Vector<super::value::Value>) -> Box<Self> {
        Self::new(LazySeqKind::Cycle { source, index: 0 })
    }

    /// Create an iterate sequence
    pub fn iterate(generator: super::value::Value, initial: super::value::Value) -> Box<Self> {
        Self::new(LazySeqKind::Iterate {
            generator,
            current: Rc::new(RefCell::new(initial)),
            index: Rc::new(RefCell::new(0)),
        })
    }

    /// Create a range sequence
    pub fn range(start: i64, end: Option<i64>, inclusive: bool, step: i64) -> Box<Self> {
        if step == 0 {
            runtime_error("range requires non-zero step");
        }
        if let Some(end_val) = end {
            if start != end_val {
                if (end_val > start && step < 0) || (end_val < start && step > 0) {
                    runtime_error("range step direction does not match range");
                }
            }
        }
        Self::new(LazySeqKind::Range {
            current: start,
            end,
            inclusive,
            step,
        })
    }

    /// Get the next value from this lazy sequence, if any
    /// Returns (next_value, updated_sequence) or None if exhausted
    pub fn next(&self) -> Option<(super::value::Value, Box<LazySequenceObject>)> {
        match &self.kind {
            LazySeqKind::Repeat { value } => {
                // Repeat is infinite, always returns the same value
                Some((*value, Self::new(self.kind.clone())))
            }

            LazySeqKind::Cycle { source, index } => {
                if source.is_empty() {
                    return None;
                }
                let value = source[*index];
                let next_index = (*index + 1) % source.len();
                Some((
                    value,
                    Self::new(LazySeqKind::Cycle {
                        source: source.clone(),
                        index: next_index,
                    }),
                ))
            }

            LazySeqKind::Range {
                current,
                end,
                inclusive,
                step,
            } => {
                // Check if exhausted
                if let Some(end_val) = end {
                    let at_end = if *inclusive {
                        if *step > 0 {
                            *current > *end_val
                        } else {
                            *current < *end_val
                        }
                    } else if *step > 0 {
                        *current >= *end_val
                    } else {
                        *current <= *end_val
                    };
                    if at_end {
                        return None;
                    }
                }

                let value = super::value::Value::from_integer(*current);
                Some((
                    value,
                    Self::new(LazySeqKind::Range {
                        current: current + step,
                        end: *end,
                        inclusive: *inclusive,
                        step: *step,
                    }),
                ))
            }

            LazySeqKind::Iterate { .. } => {
                // Iterate requires closure evaluation which we can't do here.
                // Callers should use the mutable state directly via rt_get or
                // collect_bounded_lazy which handles closure calls.
                None
            }

            LazySeqKind::Skip { source, remaining } => {
                if *remaining == 0 {
                    // No more skipping, delegate to source
                    source.next().map(|(val, new_source)| {
                        (
                            val,
                            Self::new(LazySeqKind::Skip {
                                source: new_source,
                                remaining: 0,
                            }),
                        )
                    })
                } else {
                    // Skip this element, continue
                    source.next().and_then(|(_, new_source)| {
                        Self::new(LazySeqKind::Skip {
                            source: new_source,
                            remaining: remaining - 1,
                        })
                        .next()
                    })
                }
            }

            LazySeqKind::Combinations {
                source,
                size,
                indices,
                done,
            } => {
                if *done || source.is_empty() || *size == 0 || *size > source.len() {
                    return None;
                }

                // Get current combination
                let combination: im::Vector<super::value::Value> =
                    indices.iter().map(|&i| source[i]).collect();
                let value = super::value::Value::from_list(combination);

                // Advance to next combination
                let mut new_indices = indices.clone();
                let mut i = size - 1;
                let n = source.len();

                // Find the rightmost index that can be incremented
                while new_indices[i] == n - size + i {
                    if i == 0 {
                        // All combinations exhausted
                        return Some((
                            value,
                            Self::new(LazySeqKind::Combinations {
                                source: source.clone(),
                                size: *size,
                                indices: new_indices,
                                done: true,
                            }),
                        ));
                    }
                    i -= 1;
                }

                // Increment this index and reset all subsequent indices
                new_indices[i] += 1;
                for j in (i + 1)..*size {
                    new_indices[j] = new_indices[j - 1] + 1;
                }

                Some((
                    value,
                    Self::new(LazySeqKind::Combinations {
                        source: source.clone(),
                        size: *size,
                        indices: new_indices,
                        done: false,
                    }),
                ))
            }

            // Map/Filter/FilterMap/Zip need closures, handled by builtins
            LazySeqKind::Map { .. }
            | LazySeqKind::Filter { .. }
            | LazySeqKind::FilterMap { .. }
            | LazySeqKind::Zip { .. } => {
                // These require closure evaluation, handled elsewhere
                None
            }
        }
    }
}
