use std::sync::atomic::AtomicU32;
use im;
use unicode_segmentation::UnicodeSegmentation;

/// Type tag for heap-allocated objects
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeTag {
    String,
    Decimal,       // Boxed decimal (for large values if needed)
    BoxedInteger,  // For integers > 61 bits
    List,
    Set,
    Dict,
    Function,
    Closure,
    LazySequence,
    MutableCell,
}

/// Header for all heap-allocated objects
#[repr(C)]
pub struct ObjectHeader {
    pub refcount: AtomicU32,
    pub type_tag: TypeTag,
}

impl ObjectHeader {
    pub fn new(type_tag: TypeTag) -> Self {
        ObjectHeader {
            refcount: AtomicU32::new(1),  // Start with refcount of 1
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
    /// Number of parameters the function expects
    pub arity: u32,
    /// Captured environment values (flexible array)
    pub captures: Vec<super::value::Value>,
}

impl ClosureObject {
    pub fn new(
        function_ptr: *const (),
        arity: u32,
        captures: Vec<super::value::Value>,
    ) -> Box<Self> {
        Box::new(ClosureObject {
            header: ObjectHeader::new(TypeTag::Closure),
            function_ptr,
            arity,
            captures,
        })
    }

    pub fn get_capture(&self, index: usize) -> Option<super::value::Value> {
        self.captures.get(index).copied()
    }
}
