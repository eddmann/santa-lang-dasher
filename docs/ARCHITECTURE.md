# Dasher Architecture

Dasher is the LLVM-based AOT (Ahead-of-Time) native compiler for santa-lang. It compiles santa-lang source code into standalone native executables through LLVM IR generation.

## Compilation Pipeline

```
Source Code
    │
    ▼
┌─────────┐
│  Lexer  │  Tokenizes source into token stream
└────┬────┘
     │
     ▼
┌─────────┐
│ Parser  │  Builds Abstract Syntax Tree (AST)
└────┬────┘
     │
     ▼
┌─────────────────┐
│ Type Inference  │  Infers types for specialization decisions
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│    Codegen      │  Emits LLVM IR with type-specialized ops
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│   LLVM (O2)     │  Optimizes and emits object file
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│     Linker      │  Links with runtime library
└────────┬────────┘
         │
         ▼
  Native Executable
```

The pipeline is orchestrated by `lang/src/codegen/pipeline.rs`, which coordinates all phases from source to executable.

## Project Structure

```
santa-lang-dasher/
├── lang/                    # Compiler crate
│   ├── src/
│   │   ├── lexer/           # Tokenizer
│   │   ├── parser/          # Parser and AST definitions
│   │   ├── types/           # Type inference system
│   │   │   ├── ty.rs        # Type definitions
│   │   │   ├── infer.rs     # Type inference engine
│   │   │   ├── unify.rs     # Type unification
│   │   │   └── builtins.rs  # Builtin function signatures
│   │   ├── codegen/         # LLVM code generation
│   │   │   ├── pipeline.rs  # Compilation orchestration
│   │   │   ├── context.rs   # Codegen state and helpers
│   │   │   └── compiler.rs  # Expression/statement compilation
│   │   └── runner/          # AoC runner DSL
│   └── build.rs             # Runtime embedding script
├── runtime/                 # Runtime library crate
│   └── src/
│       ├── value.rs         # NaN-boxed value representation
│       ├── heap.rs          # Heap object types
│       ├── operations.rs    # Runtime dispatch functions
│       ├── builtins.rs      # Built-in function implementations
│       └── collections.rs   # Collection operations
├── cli/                     # Command-line interface
└── benchmarks/              # Performance benchmarks
```

## Type Inference System

Dasher uses a flow-sensitive type inference system to determine types at compile time, enabling specialized code generation.

### Type Definitions (`lang/src/types/ty.rs`)

```rust
pub enum Type {
    // Primitive types - can be specialized
    Int,
    Decimal,
    String,
    Bool,
    Nil,

    // Collection types (parametric)
    List(Box<Type>),
    Set(Box<Type>),
    Dict(Box<Type>, Box<Type>),
    LazySequence(Box<Type>),

    // Function type
    Function { params: Vec<Type>, ret: Box<Type> },

    // Inference helpers
    Unknown,      // Cannot determine - triggers runtime dispatch
    TypeVar(u32), // Unification variable
    Never,        // Bottom type (return, break)
}
```

### Inference Engine (`lang/src/types/infer.rs`)

The `TypeInference` struct maintains:

- **Type Environment**: Maps variable names to their inferred types
- **Unifier**: Handles type variable substitution and unification
- **Function Definitions**: Stores user-defined functions for call-site re-inference
- **Inferring Set**: Tracks functions currently being inferred (prevents infinite recursion)

Key features:

1. **Bidirectional Inference**: For higher-order functions like `map`, the expected lambda type flows from the collection type to the lambda parameters.

2. **Call-site Re-inference**: User-defined functions are re-inferred at each call site with concrete argument types:

   ```
   let double = |x| x * 2;
   double(5)  // Re-infers body with x:Int → returns Int
   ```

3. **Pipeline Type Flow**: The pipeline operator `|>` propagates types through function chains.

### Unification (`lang/src/types/unify.rs`)

The unifier handles type compatibility:

- Same types unify to themselves
- `TypeVar` unifies with anything (records substitution)
- `Unknown` unifies with anything (result is `Unknown`)
- Collection types unify element types recursively

## Value Representation (NaN-Boxing)

All values are represented as 64-bit tagged values, defined in `runtime/src/value.rs`.

### Tag Scheme

```
Lower 3 bits determine value type:

xxx...xxx001  = Integer (61-bit signed, shifted left by 3)
xxx...xxx010  = Nil
xxx...xxx011  = Boolean (bit 3 holds the value)
000...xxx000  = Heap pointer (tag = 0, 8-byte aligned)

Decimals: Stored as raw f64 bit pattern (distinguished by elimination)
```

### Integer Encoding

Integers are stored inline with a 3-bit shift:

```rust
// Encode
let tagged = ((value as u64) << 3) | 0b001;

// Decode
let value = (tagged as i64) >> 3;  // Arithmetic right shift preserves sign
```

This provides 61-bit signed integers inline without heap allocation.

### Heap Objects

All heap objects share a common header:

```rust
#[repr(C)]
pub struct ObjectHeader {
    pub refcount: AtomicU32,
    pub type_tag: TypeTag,
}
```

Type tags: `String`, `Decimal`, `BoxedInteger`, `List`, `Set`, `Dict`, `Function`, `Closure`, `LazySequence`, `MutableCell`, `MemoizedClosure`, `PartialApplication`

### Collection Implementations

Collections use the `im` crate for persistent (immutable) data structures:

- **List**: `im::Vector<Value>` - O(log n) access, efficient append
- **Set**: `im::HashSet<Value>` - O(log n) insert/lookup
- **Dict**: `im::HashMap<Value, Value>` - O(log n) operations

## Native vs Runtime Dispatch

The compiler uses type information to choose between fast native code and runtime dispatch.

### Fast Path: Known Types

When types are known at compile time, the compiler emits direct LLVM instructions:

```rust
// Int + Int → native LLVM add
(Type::Int, InfixOp::Add, Type::Int) => {
    let l = self.unbox_int(left_val);
    let r = self.unbox_int(right_val);
    let result = self.builder.build_int_add(l, r, "add").unwrap();
    Ok(self.box_int(result))
}
```

Specialized operations include:

- **Integer arithmetic**: `add`, `sub`, `mul`, `div`, `mod` (Python-style floored)
- **Decimal arithmetic**: `fadd`, `fsub`, `fmul`, `fdiv`
- **Comparisons**: All comparison operators for Int, Decimal, Bool
- **Logical operations**: `not` for Bool, `neg` for Int/Decimal

### Slow Path: Runtime Dispatch

When types are unknown (`Type::Unknown`), the compiler emits FFI calls to runtime functions:

```rust
// Unknown types → runtime dispatch
_ => {
    let rt_fn = match op {
        InfixOp::Add => self.get_or_declare_rt_add(),
        InfixOp::Subtract => self.get_or_declare_rt_sub(),
        // ...
    };
    let call_result = self.builder
        .build_call(rt_fn, &[left_val.into(), right_val.into()], "rt_binop")
        .unwrap();
    Ok(call_result.try_as_basic_value().left().unwrap())
}
```

Runtime functions (`runtime/src/operations.rs`) handle:

- Type checking at runtime
- Mixed-type operations (Int + Decimal)
- Collection operations (List + List, Set - Set)
- String coercion (String + X)
- Error handling for invalid operations

### When Types Become Unknown

Types degrade to `Unknown` when:

- Variables are mutable (`let mut x = ...`) - type can change
- Pattern matching doesn't provide type information
- Higher-order function parameters without bidirectional inference
- External input or `read()` calls

## Closures and Functions

### Closure Object Structure

```rust
pub struct ClosureObject {
    pub header: ObjectHeader,
    pub function_ptr: *const (),  // Compiled function code
    pub arity: u32,               // Parameter count
    pub has_rest: u8,             // Has rest parameter (..args)
    pub captures: Vec<Value>,     // Captured values
}
```

### Function Compilation

Functions are compiled as separate LLVM functions with the signature:

```rust
extern "C" fn(env: *const ClosureObject, argc: u32, argv: *const Value) -> Value
```

- `env`: Pointer to closure object (for accessing captures)
- `argc`: Argument count
- `argv`: Pointer to argument array

### Capture Handling

Variables captured by closures:

1. **Immutable captures**: Value is copied into closure's capture array
2. **Mutable captures**: Wrapped in a `MutableCell` for shared mutation

```rust
// Detecting mutable captures in pre_analyze_statements
self.cell_variables.extend(
    self.find_mutable_captures_in_expr(expr, &mutable_vars, &bound_vars)
);
```

### Auto-Currying

When a function is called with fewer arguments than its arity, a `PartialApplicationObject` is created:

```rust
if argc < closure.arity {
    let remaining = closure.arity - argc;
    let partial = PartialApplicationObject::new(callee, args, remaining);
    return Value::from_partial_application(partial);
}
```

## Tail-Call Optimization (TCO)

Dasher implements TCO for self-recursive functions by converting tail calls to jumps.

### Detection

TCO is applied when:

1. The function calls itself in tail position
2. The call is the last expression (no operations after)

### Implementation

1. **Entry Block Setup**: Function starts with an entry block containing parameter allocas

2. **Tail Call Detection**: During compilation, self-recursive calls in tail position are identified:

   ```rust
   if let Some(ref tco) = self.tco_state {
       if let (Some(self_name), Expr::Identifier(name)) = (&tco.self_name, function.as_ref()) {
           if name == self_name && args.len() == tco.param_allocas.len() {
               return self.compile_tail_call(args);
           }
       }
   }
   ```

3. **Jump Instead of Call**: Arguments are evaluated to temporaries, then stored to parameter allocas, and a jump is emitted to the entry block:

   ```rust
   fn compile_tail_call(&mut self, args: &[Expr]) -> Result<BasicValueEnum<'ctx>, CompileError> {
       // Evaluate all arguments to temporaries first
       let mut arg_values = Vec::new();
       for arg in args { /* ... */ }

       // Update parameter allocas
       for (alloca, value) in tco.param_allocas.iter().zip(arg_values) {
           self.builder.build_store(*alloca, value).unwrap();
       }

       // Jump back to entry
       self.builder.build_unconditional_branch(tco.entry_block).unwrap();
   }
   ```

### TCO State

```rust
pub struct TcoState<'ctx> {
    pub self_name: Option<String>,        // Function name for self-call detection
    pub entry_block: BasicBlock<'ctx>,    // Target for tail jumps
    pub param_allocas: Vec<PointerValue<'ctx>>,  // Parameter storage
}
```

## Runtime Library Embedding

The runtime library is embedded into the compiler for single-binary distribution.

### Build Process (`lang/build.rs`)

1. **Locate Runtime**: Find `libruntime.a` in target directory
2. **Compress**: Use gzip for size reduction
3. **Embed**: Export path for `include_bytes!()` macro

```rust
// Compress using flate2/gzip
let mut encoder = GzEncoder::new(Vec::new(), Compression::best());
encoder.write_all(&data)?;
let compressed = encoder.finish()?;

// Write to OUT_DIR for include_bytes!()
fs::write(&dest_path, &compressed)?;
println!("cargo:rustc-env=RUNTIME_EMBEDDED_PATH={}", dest_path.display());
```

### Runtime Extraction (`lang/src/codegen/pipeline.rs`)

At link time, the compressed runtime is extracted to a temp directory:

```rust
fn extract_embedded_runtime() -> Result<PathBuf, CompileError> {
    let cache_dir = std::env::temp_dir().join("santa-lang-runtime");
    std::fs::create_dir_all(&cache_dir)?;

    // Hash-based cache validation
    let mut hasher = DefaultHasher::new();
    EMBEDDED_RUNTIME.hash(&mut hasher);
    let expected_hash = hasher.finish().to_string();

    // Check if already extracted and matches
    if runtime_path.exists() && cached_hash == expected_hash {
        return Ok(runtime_path);
    }

    // Decompress and write
    let mut decoder = GzDecoder::new(EMBEDDED_RUNTIME);
    let mut decompressed = Vec::new();
    decoder.read_to_end(&mut decompressed)?;
    fs::write(&runtime_path, &decompressed)?;

    Ok(runtime_path)
}
```

### Linking

The linker (clang) is invoked with platform-specific flags:

```rust
cmd.arg("-o").arg(output_path)
   .arg(obj_path)
   .arg(&runtime_lib)
   .arg("-lc").arg("-lm");

#[cfg(target_os = "macos")]
cmd.arg("-lSystem")
   .arg("-framework").arg("Security")
   .arg("-Wl,-dead_strip")
   .arg("-Wl,-stack_size,0x2000000");  // 32MB stack for recursion

#[cfg(target_os = "linux")]
cmd.arg("-lpthread").arg("-ldl")
   .arg("-lssl").arg("-lcrypto")
   .arg("-Wl,--gc-sections");
```

## LLVM Integration

Dasher uses LLVM 18 via the `inkwell` crate (v0.5).

### Optimization Level

Default optimization is O2 (Aggressive), configurable:

```rust
pub fn with_optimization(context: &'ctx Context, module_name: &str, opt_level: OptimizationLevel)
```

### Function Attributes

Runtime functions are marked with `nounwind` to enable better optimization:

```rust
fn add_runtime_function(&self, fn_name: &str, fn_type: FunctionType<'ctx>) -> FunctionValue<'ctx> {
    let func = self.module.add_function(fn_name, fn_type, None);
    let nounwind_kind = Attribute::get_named_enum_kind_id("nounwind");
    let nounwind_attr = self.context.create_enum_attribute(nounwind_kind, 0);
    func.add_attribute(AttributeLoc::Function, nounwind_attr);
    func
}
```

### Object File Generation

```rust
pub fn write_object_file(&self, path: &Path) -> Result<(), String> {
    let target_triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&target_triple)?;
    let target_machine = target.create_target_machine(
        &target_triple,
        "generic",
        "",
        self.opt_level,
        RelocMode::Default,
        CodeModel::Default,
    )?;
    target_machine.write_to_file(&self.module, FileType::Object, path)?;
    Ok(())
}
```

## Key Design Decisions

1. **Type-Specialized Dispatch**: The type inference system enables fast paths for common operations while maintaining dynamic language semantics.

2. **NaN-Boxing**: Efficient value representation with inline integers and heap pointer discrimination without separate type tags.

3. **Persistent Collections**: Using `im` crate provides immutable semantics with structural sharing, avoiding copies on updates.

4. **Embedded Runtime**: Single-binary distribution simplifies deployment and eliminates runtime dependencies.

5. **TCO via Jumps**: Self-recursive functions don't grow the stack, enabling functional programming patterns.

6. **Python-Style Division**: Floored division and modulo match language semantics rather than C/Rust defaults.

## Performance Characteristics

- **Fast Path Operations**: Native LLVM instructions for Int/Decimal/Bool operations
- **Closure Overhead**: Single indirection through function pointer + captured environment
- **Collection Updates**: O(log n) with structural sharing (no full copies)
- **String Indexing**: O(1) after first grapheme access (cached boundaries)
- **Memoization**: Hash-based cache in `MemoizedClosureObject`

## Dependencies

| Crate                  | Purpose                      |
| ---------------------- | ---------------------------- |
| `inkwell 0.5`          | LLVM 18 bindings             |
| `im`                   | Persistent collections       |
| `ordered-float`        | Hashable floating-point type |
| `unicode-segmentation` | Grapheme cluster handling    |
| `flate2`               | Runtime compression          |
| `regex`                | Pattern matching in builtins |
| `md-5`                 | MD5 hash builtin             |
| `ureq`                 | HTTP client (CLI only)       |
