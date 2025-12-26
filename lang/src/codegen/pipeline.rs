//! Compilation pipeline for AOT compilation of santa-lang programs.
//!
//! This module provides the full compilation pipeline:
//! 1. Parse source code
//! 2. Type inference
//! 3. Generate LLVM IR
//! 4. Emit object file
//! 5. Link with runtime library
//! 6. Produce executable

use flate2::read::GzDecoder;
use inkwell::context::Context;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;

use super::context::CodegenContext;
use crate::lexer::lex;
use crate::lexer::token::{Position, Span};
use crate::parser::ast::{Expr, Program, Stmt};
use crate::parser::Parser;
use crate::types::{Type, TypeInference, TypedExpr, TypedProgram};

/// Embedded runtime library (compressed with gzip)
/// This is populated by the build script if the runtime is available
#[cfg(feature = "embedded-runtime")]
static EMBEDDED_RUNTIME: &[u8] = include_bytes!(env!("RUNTIME_EMBEDDED_PATH"));

#[cfg(not(feature = "embedded-runtime"))]
static EMBEDDED_RUNTIME: &[u8] = &[];

/// Errors that can occur during compilation
#[derive(Debug)]
pub enum CompileError {
    LexError(String),
    ParseError(String),
    CodegenError(String),
    LinkError(String),
    IoError(std::io::Error),
}

impl From<std::io::Error> for CompileError {
    fn from(err: std::io::Error) -> Self {
        CompileError::IoError(err)
    }
}

/// The compilation pipeline
pub struct Compiler {
    /// Path to the runtime library (libsanta_lang.a)
    runtime_lib_path: Option<PathBuf>,
}

impl Compiler {
    /// Create a new compiler with default settings
    pub fn new() -> Self {
        Self {
            runtime_lib_path: None,
        }
    }

    /// Set the path to the runtime library
    pub fn with_runtime_lib(mut self, path: PathBuf) -> Self {
        self.runtime_lib_path = Some(path);
        self
    }

    /// Extract the embedded runtime library to a cache directory
    fn extract_embedded_runtime() -> Result<PathBuf, CompileError> {
        if EMBEDDED_RUNTIME.is_empty() {
            return Err(CompileError::LinkError(
                "No embedded runtime available".to_string(),
            ));
        }

        // Use a stable cache location
        let cache_dir = std::env::temp_dir().join("santa-lang-runtime");
        std::fs::create_dir_all(&cache_dir)?;

        let runtime_path = cache_dir.join("libsanta_lang_runtime.a");

        // Check if already extracted and matches current embedded version
        // We store the compressed size in a separate file to validate the cache
        let version_file = cache_dir.join("version");
        let expected_compressed_size = EMBEDDED_RUNTIME.len().to_string();

        if runtime_path.exists() {
            if let Ok(cached_size) = std::fs::read_to_string(&version_file) {
                if cached_size.trim() == expected_compressed_size {
                    return Ok(runtime_path);
                }
            }
        }

        // Decompress and write
        let mut decoder = GzDecoder::new(EMBEDDED_RUNTIME);
        let mut decompressed = Vec::new();
        decoder
            .read_to_end(&mut decompressed)
            .map_err(|e| CompileError::LinkError(format!("Failed to decompress runtime: {}", e)))?;

        std::fs::write(&runtime_path, &decompressed)?;
        std::fs::write(&version_file, &expected_compressed_size)?;

        Ok(runtime_path)
    }

    /// Find the runtime library
    fn find_runtime_lib(&self) -> Result<PathBuf, CompileError> {
        // If explicitly set, use that
        if let Some(ref path) = self.runtime_lib_path {
            if path.exists() {
                return Ok(path.clone());
            }
            return Err(CompileError::LinkError(format!(
                "Runtime library not found at: {:?}",
                path
            )));
        }

        // Try embedded runtime first
        if let Ok(path) = Self::extract_embedded_runtime() {
            return Ok(path);
        }

        // Fall back to searching for external runtime library
        // Try to find the project root from CARGO_MANIFEST_DIR
        let project_root = std::env::var("CARGO_MANIFEST_DIR")
            .map(PathBuf::from)
            .ok()
            .and_then(|p| p.parent().map(|p| p.to_path_buf()))
            .unwrap_or_else(|| PathBuf::from("."));

        // Try common locations for the runtime library
        let candidates = [
            // In release build directory (relative to project root)
            project_root.join("target/release/libsanta_lang_runtime.a"),
            // In debug build directory
            project_root.join("target/debug/libsanta_lang_runtime.a"),
            // Relative to current directory
            PathBuf::from("target/release/libsanta_lang_runtime.a"),
            PathBuf::from("target/debug/libsanta_lang_runtime.a"),
            PathBuf::from("libsanta_lang_runtime.a"),
        ];

        for candidate in &candidates {
            if candidate.exists() {
                return Ok(candidate.clone());
            }
        }

        Err(CompileError::LinkError(
            "Runtime library (libsanta_lang_runtime.a) not found. Run `cargo build --release` first.".to_string()
        ))
    }

    /// Compile source code to an executable
    pub fn compile_to_executable(
        &self,
        source: &str,
        output_path: &Path,
    ) -> Result<(), CompileError> {
        // Create temp directory for intermediate files with unique filename
        // Use atomic counter + timestamp + thread ID to ensure uniqueness across parallel tests
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);

        let temp_dir = std::env::temp_dir();
        let unique_id = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let thread_id = std::thread::current().id();
        let counter = COUNTER.fetch_add(1, Ordering::SeqCst);
        let obj_path = temp_dir.join(format!(
            "santa_program_{:?}_{}_{}.o",
            thread_id, unique_id, counter
        ));

        // Step 1: Compile to object file
        self.compile_to_object(source, &obj_path)?;

        // Step 2: Link with runtime
        self.link(&obj_path, output_path)?;

        // Clean up object file
        std::fs::remove_file(&obj_path).ok();

        Ok(())
    }

    /// Compile source code to an object file
    pub fn compile_to_object(&self, source: &str, output_path: &Path) -> Result<(), CompileError> {
        // Step 1: Lex
        let tokens = lex(source).map_err(|e| CompileError::LexError(format!("{:?}", e)))?;

        // Step 2: Parse
        let mut parser = Parser::new(tokens);
        let program = parser
            .parse_program()
            .map_err(|e| CompileError::ParseError(format!("{:?}", e)))?;

        // Step 3: Type inference
        let mut inference = TypeInference::new();
        let typed_program = inference
            .infer_program(&program)
            .map_err(|e| CompileError::CodegenError(format!("Type error: {}", e.message)))?;

        // Get the type environment for codegen to use
        let type_env = inference.into_type_env();

        // Step 4: Generate LLVM IR
        let context = Context::create();
        let mut codegen = CodegenContext::new(&context, "santa_program");

        // Pass the type environment to codegen for optimized subexpression inference
        codegen.set_type_env(type_env);

        // Create main function with typed program
        self.generate_main_typed(&mut codegen, &typed_program, &program)?;

        // Step 5: Emit object file
        codegen
            .write_object_file(output_path)
            .map_err(CompileError::CodegenError)?;

        Ok(())
    }

    /// Generate the main function from a program (legacy, uses simple type inference)
    #[allow(dead_code)]
    fn generate_main<'ctx>(
        &self,
        codegen: &mut CodegenContext<'ctx>,
        program: &Program,
    ) -> Result<(), CompileError> {
        let context = codegen.context;
        let i64_type = context.i64_type();

        // Create main function: int main()
        let fn_type = i64_type.fn_type(&[], false);
        let main_fn = codegen.module.add_function("main", fn_type, None);
        let entry = context.append_basic_block(main_fn, "entry");
        codegen.builder.position_at_end(entry);
        codegen.current_block = Some(entry);

        // Pre-analyze statements for self-referencing bindings and mutable captures
        codegen.pre_analyze_statements(&program.statements);

        // Compile each statement using compile_stmt (handles self-referential functions)
        let mut last_value = None;
        for stmt in &program.statements {
            match stmt {
                Stmt::Expr(expr) => {
                    let typed = self.type_expr(expr);
                    last_value = Some(
                        codegen
                            .compile_expr(&typed)
                            .map_err(|e| CompileError::CodegenError(format!("{:?}", e)))?,
                    );
                }
                Stmt::Let { .. } => {
                    // Use compile_stmt which properly handles self-referential functions
                    codegen
                        .compile_stmt(stmt)
                        .map_err(|e| CompileError::CodegenError(format!("{:?}", e)))?;
                }
                _ => {
                    // Skip other statements for now
                }
            }
        }

        // Return the last value, or 0
        // The value is NaN-boxed, so we need to unbox it to get the actual integer for exit code
        let return_val = match last_value {
            Some(v) => {
                // Unbox: (value >> 3) extracts the actual integer
                let int_val = v.into_int_value();
                codegen
                    .builder
                    .build_right_shift(int_val, i64_type.const_int(3, false), false, "unbox_return")
                    .unwrap()
            }
            None => i64_type.const_int(0, false),
        };
        codegen.builder.build_return(Some(&return_val)).unwrap();

        Ok(())
    }

    /// Generate the main function from a typed program (uses full type inference)
    ///
    /// This version uses pre-inferred types from the type inference pass,
    /// enabling better code generation through type specialization.
    fn generate_main_typed<'ctx>(
        &self,
        codegen: &mut CodegenContext<'ctx>,
        typed_program: &TypedProgram,
        program: &Program,
    ) -> Result<(), CompileError> {
        let context = codegen.context;
        let i64_type = context.i64_type();

        // Create main function: int main()
        let fn_type = i64_type.fn_type(&[], false);
        let main_fn = codegen.module.add_function("main", fn_type, None);
        let entry = context.append_basic_block(main_fn, "entry");
        codegen.builder.position_at_end(entry);
        codegen.current_block = Some(entry);

        // Pre-analyze statements for self-referencing bindings and mutable captures
        // This must happen before compiling so closures can properly capture cell variables
        codegen.pre_analyze_statements(&program.statements);

        // Compile each statement using the typed information
        let mut last_value = None;
        for (i, typed_stmt) in typed_program.statements.iter().enumerate() {
            match &typed_stmt.stmt {
                Stmt::Expr(expr) => {
                    // Create TypedExpr with the inferred type
                    let typed_expr = TypedExpr {
                        expr: expr.clone(),
                        ty: typed_stmt.ty.clone(),
                        span: typed_stmt.span,
                    };
                    last_value = Some(
                        codegen
                            .compile_expr(&typed_expr)
                            .map_err(|e| CompileError::CodegenError(format!("{:?}", e)))?,
                    );
                }
                Stmt::Let { .. } => {
                    // Use compile_stmt which properly handles self-referential functions
                    // Pass the original statement from program for compile_stmt
                    codegen
                        .compile_stmt(&program.statements[i])
                        .map_err(|e| CompileError::CodegenError(format!("{:?}", e)))?;
                }
                _ => {
                    // Skip other statements for now
                }
            }
        }

        // Return the last value, or 0
        // The value is NaN-boxed, so we need to unbox it to get the actual integer for exit code
        let return_val = match last_value {
            Some(v) => {
                // Unbox: (value >> 3) extracts the actual integer
                let int_val = v.into_int_value();
                codegen
                    .builder
                    .build_right_shift(int_val, i64_type.const_int(3, false), false, "unbox_return")
                    .unwrap()
            }
            None => i64_type.const_int(0, false),
        };
        codegen.builder.build_return(Some(&return_val)).unwrap();

        Ok(())
    }

    /// Simple type inference for an expression
    fn type_expr(&self, expr: &Expr) -> TypedExpr {
        let ty = match expr {
            Expr::Integer(_) => Type::Int,
            Expr::Decimal(_) => Type::Decimal,
            Expr::Boolean(_) => Type::Bool,
            Expr::String(_) => Type::String,
            Expr::Nil => Type::Nil,
            Expr::Infix { left, op: _, right } => {
                // For arithmetic ops between ints, result is int
                let left_ty = self.infer_type(left);
                let right_ty = self.infer_type(right);
                match (left_ty, right_ty) {
                    (Type::Int, Type::Int) => Type::Int,
                    (Type::Decimal, Type::Decimal) => Type::Decimal,
                    _ => Type::Unknown,
                }
            }
            _ => Type::Unknown,
        };

        TypedExpr {
            expr: expr.clone(),
            ty,
            span: Span::new(Position::new(0, 0), Position::new(0, 0)),
        }
    }

    /// Simple type inference helper
    fn infer_type(&self, expr: &Expr) -> Type {
        match expr {
            Expr::Integer(_) => Type::Int,
            Expr::Decimal(_) => Type::Decimal,
            Expr::Boolean(_) => Type::Bool,
            Expr::String(_) => Type::String,
            Expr::Nil => Type::Nil,
            _ => Type::Unknown,
        }
    }

    /// Link object file with runtime library to produce executable
    fn link(&self, obj_path: &Path, output_path: &Path) -> Result<(), CompileError> {
        let runtime_lib = self.find_runtime_lib()?;

        // Use clang to link
        let status = Command::new("clang")
            .arg("-o")
            .arg(output_path)
            .arg(obj_path)
            .arg(&runtime_lib)
            // Link system libraries needed by the runtime
            .arg("-lSystem")
            .arg("-lc")
            .arg("-lm")
            // Link frameworks required by native-tls on macOS
            .arg("-framework")
            .arg("Security")
            .arg("-framework")
            .arg("CoreFoundation")
            // Suppress duplicate library warnings (clang adds -lSystem automatically)
            .arg("-Wl,-no_warn_duplicate_libraries")
            // Strip debug symbols and dead code
            .arg("-Wl,-dead_strip")
            .arg("-Wl,-x")
            // Increase stack size to 32MB for deeply recursive programs
            .arg("-Wl,-stack_size,0x2000000")
            .status()?;

        if !status.success() {
            return Err(CompileError::LinkError(format!(
                "Linker failed with exit code: {:?}",
                status.code()
            )));
        }

        Ok(())
    }
}

impl Default for Compiler {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;

    /// Generate unique filename using thread ID and nanos
    fn unique_path(base: &str, ext: &str) -> PathBuf {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);

        let temp_dir = std::env::temp_dir();
        let unique_id = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let thread_id = std::thread::current().id();
        let counter = COUNTER.fetch_add(1, Ordering::SeqCst);
        temp_dir.join(format!(
            "{}_{:?}_{}_{}_.{}",
            base, thread_id, unique_id, counter, ext
        ))
    }

    #[test]
    fn compile_simple_integer_to_object() {
        let compiler = Compiler::new();
        let obj_path = unique_path("test_compile", "o");

        let result = compiler.compile_to_object("42", &obj_path);
        assert!(result.is_ok(), "Failed to compile: {:?}", result.err());

        // Verify object file exists
        assert!(obj_path.exists());

        // Clean up
        std::fs::remove_file(&obj_path).ok();
    }

    #[test]
    fn compile_arithmetic_to_object() {
        let compiler = Compiler::new();
        let obj_path = unique_path("test_arithmetic", "o");

        let result = compiler.compile_to_object("1 + 2 * 3", &obj_path);
        assert!(result.is_ok(), "Failed to compile: {:?}", result.err());

        assert!(obj_path.exists());
        std::fs::remove_file(&obj_path).ok();
    }

    #[test]
    fn compile_and_execute_simple_integer() {
        let compiler = Compiler::new();
        let exe_path = unique_path("test_exec_int", "exe");

        // Compile and link
        let result = compiler.compile_to_executable("42", &exe_path);
        assert!(result.is_ok(), "Failed to compile: {:?}", result.err());

        // Execute and get exit code
        let output = Command::new(&exe_path)
            .output()
            .expect("Failed to execute compiled program");

        // The return value is unboxed to the actual integer 42
        assert_eq!(output.status.code(), Some(42));

        // Clean up
        std::fs::remove_file(&exe_path).ok();
    }

    #[test]
    fn compile_and_execute_puts() {
        let compiler = Compiler::new();
        let exe_path = unique_path("test_puts_exec", "exe");

        // Compile puts(42) followed by 0 (for exit code)
        let result = compiler.compile_to_executable("puts(42)\n0", &exe_path);
        assert!(result.is_ok(), "Failed to compile puts: {:?}", result.err());

        // Execute and capture stdout
        let output = Command::new(&exe_path)
            .output()
            .expect("Failed to execute compiled program");

        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains("42"),
            "Output should contain '42', got: {}",
            stdout
        );

        // Clean up
        std::fs::remove_file(&exe_path).ok();
    }

    #[test]
    fn compile_and_execute_time_nanos() {
        let compiler = Compiler::new();
        let exe_path = unique_path("test_time_nanos_exec", "exe");

        // Compile __time_nanos() call and print it
        let result =
            compiler.compile_to_executable("let t = __time_nanos()\nputs(t)\n0", &exe_path);
        assert!(
            result.is_ok(),
            "Failed to compile __time_nanos: {:?}",
            result.err()
        );

        // Execute and capture stdout
        let output = Command::new(&exe_path)
            .output()
            .expect("Failed to execute compiled program");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let nanos_str = stdout.trim();
        let nanos: i64 = nanos_str.parse().expect("Should output a number");
        // Elapsed time since program start should be small and non-negative
        assert!(nanos >= 0, "Time should be non-negative, got: {}", nanos);
        assert!(
            nanos < 1_000_000_000,
            "Time should be less than 1 second, got: {}",
            nanos
        );

        // Clean up
        std::fs::remove_file(&exe_path).ok();
    }

    #[test]
    fn compile_and_execute_match_expression() {
        let compiler = Compiler::new();
        let exe_path = unique_path("test_match_exec", "exe");

        // Compile a match expression
        let source = r#"
            let r = match 2 { 1 { 100 } 2 { 200 } _ { 0 } };
            puts(r);
            0
        "#;
        let result = compiler.compile_to_executable(source, &exe_path);
        assert!(
            result.is_ok(),
            "Failed to compile match: {:?}",
            result.err()
        );

        // Execute and capture stdout
        let output = Command::new(&exe_path)
            .output()
            .expect("Failed to execute compiled program");

        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains("200"),
            "Output should contain '200', got: {}",
            stdout
        );

        // Clean up
        std::fs::remove_file(&exe_path).ok();
    }

    #[test]
    fn compile_and_execute_update_list() {
        let compiler = Compiler::new();
        let exe_path = unique_path("test_update_list_exec", "exe");

        // Test: update(0, |x| x + 1, [1, 2]) should produce [2, 2]
        let source = r#"
            let result = update(0, |x| x + 1, [1, 2]);
            puts(first(result));
            0
        "#;
        let result = compiler.compile_to_executable(source, &exe_path);
        assert!(
            result.is_ok(),
            "Failed to compile update: {:?}",
            result.err()
        );

        // Execute and capture stdout
        let output = Command::new(&exe_path)
            .output()
            .expect("Failed to execute compiled program");

        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains("2"),
            "Output should contain '2', got: {}",
            stdout
        );

        // Clean up
        std::fs::remove_file(&exe_path).ok();
    }

    #[test]
    fn compile_and_execute_update_d_list() {
        let compiler = Compiler::new();
        let exe_path = unique_path("test_update_d_list_exec", "exe");

        // Test: update_d(0, 10, |x| x + 1, [5, 2]) should produce [6, 2]
        // (existing value 5 is used, so 5 + 1 = 6)
        let source = r#"
            let result = update_d(0, 10, |x| x + 1, [5, 2]);
            puts(first(result));
            0
        "#;
        let result = compiler.compile_to_executable(source, &exe_path);
        assert!(
            result.is_ok(),
            "Failed to compile update_d: {:?}",
            result.err()
        );

        // Execute and capture stdout
        let output = Command::new(&exe_path)
            .output()
            .expect("Failed to execute compiled program");

        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains("6"),
            "Output should contain '6', got: {}",
            stdout
        );

        // Clean up
        std::fs::remove_file(&exe_path).ok();
    }
}
