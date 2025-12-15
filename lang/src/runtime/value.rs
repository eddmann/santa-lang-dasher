use super::heap::{StringObject, ListObject, SetObject, DictObject, MutableCellObject, ClosureObject, ObjectHeader, TypeTag};

/// 64-bit NaN-boxed value representation
///
/// We use a simpler tagging scheme where the lower 3 bits are used for tags,
/// and integers are stored by shifting left 3 bits.
///
/// Tag scheme:
///   xxx...xxx001 = Integer (61-bit signed, shifted left 3)
///   xxx...xxx010 = Nil
///   xxx...xxx011 = Boolean (bit 3 = value)
///   000...xxx000 = Heap pointer (tag = 0, pointer aligned to 8 bytes)
///
/// Decimals are stored as actual f64 values (not tagged, identified by
/// not matching any of the above patterns and not being a valid heap pointer).
#[repr(transparent)]
#[derive(Copy, Clone, Debug)]
pub struct Value(u64);

// Implement PartialEq for Value with proper deep equality for strings
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        // Fast path: identical bits (including same heap pointer)
        if self.0 == other.0 {
            return true;
        }

        // Compare based on type
        match (self.heap_type_tag(), other.heap_type_tag()) {
            (Some(TypeTag::String), Some(TypeTag::String)) => {
                // Deep string comparison
                self.as_string() == other.as_string()
            }
            // TODO: Deep equality for collections (lists, sets, dicts)
            _ => false,
        }
    }
}

impl Eq for Value {}

// Implement Hash for Value with proper hashing for strings
impl std::hash::Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Hash based on type to ensure consistency with PartialEq
        if let Some(s) = self.as_string() {
            // Hash the string content
            std::hash::Hash::hash(&TypeTag::String, state);
            std::hash::Hash::hash(s, state);
        } else {
            // For non-strings, hash the raw bits
            // TODO: Deep hashing for collections
            std::hash::Hash::hash(&self.0, state);
        }
    }
}

// Tag constants
const TAG_INTEGER: u64 = 0b001;
const TAG_NIL: u64 = 0b010;
const TAG_BOOLEAN: u64 = 0b011;
const TAG_MASK: u64 = 0b111;  // Lower 3 bits

// 61-bit integers fit when shifted left by 3 (we lose 3 bits to the tag)
// This is 2^60 - 1 for positive, -2^60 for negative
#[allow(dead_code)]
const MAX_INLINE_INT: i64 = (1i64 << 60) - 1;
#[allow(dead_code)]
const MIN_INLINE_INT: i64 = -(1i64 << 60);

impl Value {
    // ===== Integer Operations =====

    pub fn from_integer(i: i64) -> Self {
        // Shift left by 3 bits and OR with tag
        Value(((i as u64) << 3) | TAG_INTEGER)
    }

    pub fn is_integer(&self) -> bool {
        // Check if lower 3 bits match TAG_INTEGER
        (self.0 & TAG_MASK) == TAG_INTEGER
    }

    pub fn as_integer(&self) -> Option<i64> {
        if self.is_integer() {
            // Arithmetic right shift by 3 to get the integer back (with sign extension)
            Some((self.0 as i64) >> 3)
        } else {
            None
        }
    }

    // ===== Nil Operations =====

    pub fn nil() -> Self {
        Value(TAG_NIL)
    }

    pub fn is_nil(&self) -> bool {
        // Nil is exactly TAG_NIL, not just lower 3 bits matching
        // This distinguishes nil from f64 values that happen to have 0b010 in lower bits
        self.0 == TAG_NIL
    }

    // ===== Boolean Operations =====

    pub fn from_bool(b: bool) -> Self {
        // Store boolean in bit 3, tag in lower 3 bits
        Value(TAG_BOOLEAN | if b { 1 << 3 } else { 0 })
    }

    pub fn is_boolean(&self) -> bool {
        // Booleans are exactly TAG_BOOLEAN (false) or TAG_BOOLEAN | (1 << 3) (true)
        // This distinguishes booleans from f64 values that happen to have 0b011 in lower bits
        self.0 == TAG_BOOLEAN || self.0 == (TAG_BOOLEAN | (1 << 3))
    }

    pub fn as_bool(&self) -> Option<bool> {
        if self.is_boolean() {
            Some((self.0 & (1 << 3)) != 0)
        } else {
            None
        }
    }

    // ===== Decimal Operations =====

    pub fn from_decimal(d: f64) -> Self {
        // Store as actual f64 (not NaN-tagged since we use the non-NaN range)
        Value(d.to_bits())
    }

    pub fn as_decimal(&self) -> Option<f64> {
        // Check if it's not one of our tagged types and not a heap pointer
        if !self.is_integer() && !self.is_nil() && !self.is_boolean() && !self.is_heap_object() {
            Some(f64::from_bits(self.0))
        } else {
            None
        }
    }

    // ===== Heap Pointer Operations =====

    pub fn from_heap_ptr<T>(ptr: *const T) -> Self {
        // Heap pointers have tag 0 (lower 3 bits are 000 due to 8-byte alignment)
        Value(ptr as u64)
    }

    pub fn is_heap_object(&self) -> bool {
        // A heap pointer has tag 0 (lower 3 bits are 000 due to 8-byte alignment)
        // and must have upper 16 bits as 0 (48-bit address space on x64)
        // This distinguishes pointers from f64 values which often have non-zero upper bits
        (self.0 & TAG_MASK) == 0 && self.0 != 0 && (self.0 >> 48) == 0
    }

    pub fn as_heap_ptr<T>(&self) -> Option<*const T> {
        if self.is_heap_object() {
            Some(self.0 as *const T)
        } else {
            None
        }
    }

    /// Get the type tag of a heap object, or None if not a heap object
    pub fn heap_type_tag(&self) -> Option<TypeTag> {
        if self.is_heap_object() {
            let header_ptr = self.0 as *const ObjectHeader;
            unsafe { Some((*header_ptr).type_tag) }
        } else {
            None
        }
    }

    // ===== String Operations =====

    pub fn from_string(s: impl Into<String>) -> Self {
        let obj = StringObject::new(s);
        let ptr = Box::into_raw(obj);
        Value::from_heap_ptr(ptr)
    }

    pub fn as_string(&self) -> Option<&str> {
        if self.heap_type_tag() == Some(TypeTag::String) {
            let ptr = self.0 as *const StringObject;
            unsafe { Some((*ptr).as_str()) }
        } else {
            None
        }
    }

    /// Get grapheme cluster at index (LANG.txt §3.3)
    pub fn grapheme_at(&self, index: usize) -> Option<&str> {
        if self.heap_type_tag() == Some(TypeTag::String) {
            let ptr = self.0 as *const StringObject;
            unsafe { (*ptr).grapheme_at(index) }
        } else {
            None
        }
    }

    /// Number of grapheme clusters in string
    pub fn grapheme_len(&self) -> usize {
        if self.heap_type_tag() == Some(TypeTag::String) {
            let ptr = self.0 as *const StringObject;
            unsafe { (*ptr).grapheme_len() }
        } else {
            0
        }
    }

    // ===== List Operations =====

    pub fn from_list(elements: im::Vector<Value>) -> Self {
        let obj = ListObject::new(elements);
        let ptr = Box::into_raw(obj);
        Value::from_heap_ptr(ptr)
    }

    pub fn as_list(&self) -> Option<&im::Vector<Value>> {
        if self.heap_type_tag() == Some(TypeTag::List) {
            let ptr = self.0 as *const ListObject;
            unsafe { Some(&(*ptr).data) }
        } else {
            None
        }
    }

    // ===== Set Operations =====

    pub fn from_set(elements: im::HashSet<Value>) -> Self {
        let obj = SetObject::new(elements);
        let ptr = Box::into_raw(obj);
        Value::from_heap_ptr(ptr)
    }

    pub fn as_set(&self) -> Option<&im::HashSet<Value>> {
        if self.heap_type_tag() == Some(TypeTag::Set) {
            let ptr = self.0 as *const SetObject;
            unsafe { Some(&(*ptr).data) }
        } else {
            None
        }
    }

    // ===== Dict Operations =====

    pub fn from_dict(entries: im::HashMap<Value, Value>) -> Self {
        let obj = DictObject::new(entries);
        let ptr = Box::into_raw(obj);
        Value::from_heap_ptr(ptr)
    }

    pub fn as_dict(&self) -> Option<&im::HashMap<Value, Value>> {
        if self.heap_type_tag() == Some(TypeTag::Dict) {
            let ptr = self.0 as *const DictObject;
            unsafe { Some(&(*ptr).data) }
        } else {
            None
        }
    }

    // ===== Mutable Cell Operations =====

    pub fn from_cell(value: Value) -> Self {
        let obj = MutableCellObject::new(value);
        let ptr = Box::into_raw(obj);
        Value::from_heap_ptr(ptr)
    }

    pub fn as_cell(&self) -> Option<*mut MutableCellObject> {
        if self.heap_type_tag() == Some(TypeTag::MutableCell) {
            Some(self.0 as *mut MutableCellObject)
        } else {
            None
        }
    }

    // ===== Closure Operations =====

    pub fn from_closure(closure: Box<ClosureObject>) -> Self {
        let ptr = Box::into_raw(closure);
        Value::from_heap_ptr(ptr)
    }

    pub fn as_closure(&self) -> Option<&ClosureObject> {
        if self.heap_type_tag() == Some(TypeTag::Closure) {
            let ptr = self.0 as *const ClosureObject;
            unsafe { Some(&*ptr) }
        } else {
            None
        }
    }

    pub fn is_closure(&self) -> bool {
        self.heap_type_tag() == Some(TypeTag::Closure)
    }

    // ===== Truthiness (LANG.txt §14.1) =====

    pub fn is_truthy(&self) -> bool {
        if let Some(b) = self.as_bool() {
            b
        } else if self.is_nil() {
            false
        } else if let Some(i) = self.as_integer() {
            i != 0
        } else if let Some(d) = self.as_decimal() {
            d != 0.0
        } else if let Some(s) = self.as_string() {
            !s.is_empty()
        } else if let Some(list) = self.as_list() {
            !list.is_empty()
        } else if let Some(set) = self.as_set() {
            !set.is_empty()
        } else if let Some(dict) = self.as_dict() {
            !dict.is_empty()
        } else {
            // Other heap objects (functions, closures, lazy sequences) are truthy
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tagging_constants() {
        // Verify our constants are correct
        assert_eq!(TAG_INTEGER, 0b001);
        assert_eq!(TAG_NIL, 0b010);
        assert_eq!(TAG_BOOLEAN, 0b011);
        assert_eq!(TAG_MASK, 0b111);
    }

    #[test]
    fn max_inline_integer_bounds() {
        // 61-bit integers can be stored inline (3 bits lost to tag)
        assert_eq!(MAX_INLINE_INT, (1i64 << 60) - 1);
        assert_eq!(MIN_INLINE_INT, -(1i64 << 60));
    }
}
