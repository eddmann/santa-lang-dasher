use crate::value::Value;
use std::os::raw::c_char;

/// Create a string Value from a C string pointer
/// This is called from generated LLVM code to create string literals
#[no_mangle]
pub extern "C" fn rt_string_from_cstr(ptr: *const c_char, len: usize) -> Value {
    unsafe {
        let bytes = std::slice::from_raw_parts(ptr as *const u8, len);
        let s = std::str::from_utf8_unchecked(bytes);
        Value::from_string(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    #[test]
    fn test_string_from_cstr() {
        let c_string = CString::new("hello").unwrap();
        let value = rt_string_from_cstr(c_string.as_ptr(), 5);

        assert!(value.as_string().is_some());
        assert_eq!(value.as_string().unwrap(), "hello");
    }
}
