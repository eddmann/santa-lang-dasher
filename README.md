# Dasher

An ahead-of-time (AOT) LLVM-based native compiler for the Santa programming language.

## Architecture Overview

```
Source → Lexer → Parser → Type Inference → Codegen → LLVM IR → Native Code
                                              ↓
                                    Runtime Library (FFI)
```

**Total codebase:** ~33,700 lines of Rust across 4 crates

## Project Structure

| Crate         | Purpose           | Description                                 |
| ------------- | ----------------- | ------------------------------------------- |
| `lang/`       | Compiler library  | Lexer, parser, type inference, LLVM codegen |
| `runtime/`    | FFI runtime       | Values, reference counting, 80+ builtins    |
| `cli/`        | CLI binary        | Command-line interface                      |
| `benchmarks/` | Performance tests | Benchmarking suite                          |

### Key Dependencies

- **inkwell 0.5** (LLVM 18.0): LLVM IR generation
- **im**: Persistent data structures (Vector, HashMap, HashSet)
- **ordered-float**: Ordered float comparisons
- **regex**: Pattern matching
- **expect-test**: Snapshot testing

## Compilation Pipeline

### 1. Lexer (`lang/src/lexer/`)

Single-pass character-by-character lexer that produces tokens with source positions.

**Handles:**

- Literals: integers, decimals, strings, booleans, nil
- Operators: arithmetic, comparison, logical, pipeline (`|>`), composition (`>>`)
- Keywords: `let`, `mut`, `if`, `else`, `match`, `return`, `break`
- Delimiters: `()`, `[]`, `{}`, `#{` (set literal)

### 2. Parser (`lang/src/parser/`)

**Pratt parsing** (top-down operator precedence) producing an AST.

```rust
Program {
    statements: Vec<Stmt>,    // Top-level bindings
    sections: Vec<Section>,   // AOC-specific sections
}
```

**Features:**

- Placeholder transformation: `_ + 1` becomes `|x| x + 1`
- AOC sections: `input:`, `part_one:`, `part_two:`, `test:`
- Pattern matching in `match` and `if let`

#### Solution File Compilation

Solution files (with `part_one:`/`part_two:` sections) undergo a **source transformation** before LLVM compilation:

```
┌─────────────────────────────────────────────────────────────┐
│  Solution File (.santa)                                     │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ input: read("aoc://2022/1")                          │   │
│  │ part_one: input |> lines |> map(int) |> sum          │   │
│  │ part_two: input |> lines |> max                      │   │
│  │ test: "5\n3\n8" part_one: 16 part_two: 8             │   │
│  └─────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼  Runner.generate_source()
┌─────────────────────────────────────────────────────────────┐
│  Generated Executable Source                                │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ let __args = __get_args();                           │   │
│  │ let __test_mode = first(__args) == "-t";             │   │
│  │                                                      │   │
│  │ if __test_mode {                                     │   │
│  │   // Run each @test section, compare results         │   │
│  │   let input = "5\n3\n8";                             │   │
│  │   __print_test_result("Part 1", actual, 16, time);   │   │
│  │ } else {                                             │   │
│  │   // Run solution with timing                        │   │
│  │   let input = read("aoc://2022/1");                  │   │
│  │   __print_result("Part 1", result, time);            │   │
│  │ }                                                    │   │
│  └─────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼  LLVM Codegen
┌─────────────────────────────────────────────────────────────┐
│  Native Executable                                          │
│  - Run normally: ./solution         → Part 1/2 results      │
│  - Run tests:    ./solution -t      → Test pass/fail        │
│  - With slow:    ./solution -t -s   → Include @slow tests   │
└─────────────────────────────────────────────────────────────┘
```

**Runtime intrinsics** used in generated code:

- `__get_args()` - Get command-line arguments
- `__time_nanos()` - High-precision timing
- `__print_result(label, value, time)` - Colored output
- `__print_test_result(label, actual, expected, time)` - Test output

### 3. Type Inference (`lang/src/types/`)

**Local, monomorphic type inference** enabling compile-time optimizations.

```rust
enum Type {
    Int, Decimal, String, Bool, Nil,
    List(Box<Type>),
    Set(Box<Type>),
    Dict(Box<Type>, Box<Type>),
    LazySequence(Box<Type>),
    Function { params: Vec<Type>, ret: Box<Type> },
    Unknown,      // Falls back to runtime dispatch
    TypeVar(u32), // Unification variable
    Never,        // Bottom type (return, break)
}
```

**Benefits:**

- Type specialization for native LLVM operations
- `Int + Int` compiles to native CPU add instruction
- Unknown types fall back to runtime dispatch

### 4. Code Generation (`lang/src/codegen/`)

Uses **inkwell** to generate LLVM IR with several optimizations:

- **Type specialization**: Known types use native LLVM operations
- **Tail-call optimization (TCO)**: Self-recursive functions don't grow stack
- **Closure objects**: Captured environments stored in heap-allocated objects
- **Optimization levels**: O0-O3 (default O2)

### 5. Object Emission & Linking

1. LLVM generates native object files (`.o`)
2. **Static linking** with `libsanta_lang_runtime.a` (runtime baked into executable)
3. Uses system `clang` for final linking

**Result:** Fully standalone native executables with no runtime dependencies.

## Value Representation: NaN-Boxing

All values encoded as **64-bit unsigned integers** with tag bits:

```
Tag (lower 3 bits):
  ...xxx001 = Integer (61-bit signed, shifted left 3)
  ...xxx010 = Nil
  ...xxx011 = Boolean (bit 3 = value)
  ...xxx000 = Heap pointer (naturally aligned)
```

**Benefits:**

- Single 64-bit type simplifies FFI
- Cheap type checking (mask & compare)
- Integers stored inline (no heap allocation)

## Runtime Library

### Heap Objects (`runtime/src/heap.rs`)

All heap objects share a common header:

```rust
struct ObjectHeader {
    refcount: AtomicU32,
    type_tag: TypeTag,
}
```

**Object types:** String, Decimal (boxed), BoxedInteger, List, Set, Dict, Function, Closure, LazySequence, MutableCell, MemoizedClosure, PartialApplication

### Reference Counting (`runtime/src/refcount.rs`)

- `rt_incref()` / `rt_decref()` - atomic operations
- Automatic recursive cleanup when refcount reaches 0
- Thread-safe with `Ordering::Relaxed` / `Ordering::Release`

### Collections (`runtime/src/collections.rs`)

Uses **persistent data structures** from the `im` crate:

| Type | Implementation              | Characteristics                   |
| ---- | --------------------------- | --------------------------------- |
| List | `im::Vector<Value>`         | O(1) push/pop, structural sharing |
| Set  | `im::HashSet<Value>`        | Immutable hash set                |
| Dict | `im::HashMap<Value, Value>` | Immutable hash map                |

### Built-in Functions (`runtime/src/builtins.rs`)

80+ functions organized by category:

**Collection Operations:**

- `map`, `filter`, `fold`, `reduce`, `scan`
- `first`, `last`, `rest`, `size`, `get`
- `push`, `assoc`, `update`
- `zip`, `flat_map`, `sort`, `reverse`

**Lazy Sequences:**

- `repeat`, `cycle`, `iterate`
- `range`, `combinations`
- `skip`, `take`, `take_while`

**String Operations:**

- `lines`, `split`, `join`
- `regex_match`, `regex_match_all`
- `trim`, `upper`, `lower`

**Utilities:**

- `memoize` - Function result caching
- `md5` - MD5 hashing
- `puts` - Print to stdout
- `read` - Read file or URL

### Type-Aware Operations (`runtime/src/operations.rs`)

Runtime dispatch for dynamically-typed operations:

```rust
// Integer + Integer → Integer
// Decimal + Decimal → Decimal
// Integer + Decimal → Integer (left type wins)
// String + X → String (coercion)
// List + List → List (concatenation)
// Set + Set → Set (union)
// Dict + Dict → Dict (merge)
```

### Lazy Sequences

Lazy evaluation with support for infinite sequences:

```rust
enum LazySeqKind {
    Repeat { value },               // Infinite repetition
    Cycle { source, index },        // Infinite cycling
    Iterate { generator, current }, // Function iteration
    Range { current, end, inclusive, step }, // Numeric range
    Map { source, mapper },         // Lazy map
    Filter { source, predicate },   // Lazy filter
    Skip { source, remaining },     // Skip first n elements
    Combinations { source, size, indices, done }, // All combinations
    Zip { sources },                // Zipped sequences
}
```

**Operations that force evaluation:** `list()`, `set()`, `sum()`, `size()`

## Key Design Patterns

| Pattern                        | Trade-off               | Benefit                              |
| ------------------------------ | ----------------------- | ------------------------------------ |
| **NaN-Boxing**                 | Type check cost         | FFI simplicity, cache efficiency     |
| **Persistent Data Structures** | Some copy overhead      | Immutability, functional semantics   |
| **Type Specialization**        | Code duplication        | Native ops for common types          |
| **Reference Counting**         | Per-allocation overhead | Deterministic cleanup, no GC pauses  |
| **Closure Convention**         | Extra env parameter     | Captured variables always accessible |

## Language Quirks

1. **Left type wins** in mixed arithmetic:

   ```
   5 + 3.0   // → 8 (Integer)
   3.0 + 5   // → 8.0 (Decimal)
   ```

2. **String concatenation** via `+`:

   ```
   "hello" + 42  // → "hello42"
   ```

3. **Infinite sequences** are supported:

   ```
   repeat(5) |> take(3)  // → [5, 5, 5]
   ```

4. **Grapheme-aware** string operations:

   ```
   "🎄" |> size  // → 1
   ```

5. **Placeholder sugar** for lambdas:
   ```
   _ * 2        // → |x| x * 2
   _ + _        // → |x, y| x + y
   ```

## Key Files Reference

| Component          | Key Files                                         |
| ------------------ | ------------------------------------------------- |
| Lexer              | `lang/src/lexer/{mod,token}.rs`                   |
| Parser             | `lang/src/parser/{mod,ast}.rs`                    |
| Type Inference     | `lang/src/types/{ty,infer,builtins}.rs`           |
| Code Generation    | `lang/src/codegen/{context,compiler,pipeline}.rs` |
| Solution Runner    | `lang/src/runner/mod.rs`                          |
| Values             | `runtime/src/{value,heap}.rs`                     |
| Reference Counting | `runtime/src/refcount.rs`                         |
| Operations         | `runtime/src/operations.rs`                       |
| Built-ins          | `runtime/src/builtins.rs`                         |

## Building

```bash
cargo build          # Build all crates
cargo build --release  # Build optimized release
cargo test           # Run all tests
cargo clippy         # Lint check
```

## Usage

```bash
# Run a solution (compile, run, delete executable)
./target/release/dasher examples/aoc2022/aoc2022_day01.santa

# Run tests
./target/release/dasher -t examples/basic_math.santa

# Include slow tests
./target/release/dasher -t -s examples/aoc2022/aoc2022_day01.santa

# Compile to executable (outputs alongside script)
./target/release/dasher -c examples/aoc2022/aoc2022_day01.santa
./examples/aoc2022/aoc2022_day01  # Run the compiled binary
```

## Development

See [CLAUDE.md](CLAUDE.md) for development guidelines including:

- TDD workflow requirements
- Architecture constraints
- Testing patterns
- Code style

## References

- **LANG.txt**: Authoritative language specification
- **PLAN.md**: Development roadmap and release gates
