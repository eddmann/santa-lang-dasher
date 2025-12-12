# Dasher: Santa-Lang LLVM Implementation Plan

An LLVM-backed native AOT compiler implementation of santa-lang.

**Note**: `evaluate()` is out of scope for Dasher due to the complexity of runtime code evaluation in an AOT-compiled system. This is a known limitation.

## Architecture (MANDATORY)

**This is a native LLVM compiler, NOT an interpreter or bytecode VM.**

```
Source → Lexer → Parser → Codegen → LLVM IR → Native Code
                              ↓
                    Runtime Library (FFI)
```

- **Codegen** produces LLVM IR using the `inkwell` crate
- **Runtime library** provides `extern "C"` FFI functions linked with compiled code
- **Final output** is AOT-compiled native machine code (executables)
- **Error handling** uses return value + flag pattern for graceful error propagation

### Forbidden Approaches
- ❌ Tree-walking interpreter (do NOT eval AST directly)
- ❌ Bytecode VM (do NOT compile to custom bytecode and interpret)
- ❌ Transpilation to another language

---

## Source of Truth

**LANG.txt** is the authoritative specification. All implementation decisions MUST conform to LANG.txt. Every phase includes:

- Specific LANG.txt section references
- Tests derived from LANG.txt examples
- Validation against LANG.txt-defined behaviors

## LANG.txt Coverage Checklist

| Section                  | Description                                 | Phase              |
| ------------------------ | ------------------------------------------- | ------------------ |
| §2 Lexical Structure     | Tokens, keywords, literals, comments        | Phase 1            |
| §3 Type System           | All 10 value types, hashability             | Phase 4            |
| §4 Operators             | Arithmetic, comparison, logical, precedence | Phases 2, 5, 7     |
| §5 Variables & Bindings  | let, mut, destructuring, shadowing          | Phases 3, 6        |
| §6 Expressions           | Literals, blocks, calls, infix, pipeline    | Phase 2            |
| §7 Control Flow          | if, if-let, match, return, break            | Phases 3, 6        |
| §8 Functions             | Lambdas, closures, partial, TCO, memoize    | Phases 2, 5, 8, 14 |
| §9 Pattern Matching      | All pattern types, guards                   | Phases 3, 15       |
| §10 Collections          | List, Set, Dict, Range, LazySeq             | Phases 4, 12       |
| §11 Built-in Functions   | All 66 functions                            | Phases 9-13        |
| §12 AOC Runner           | Sections, tests, script mode                | Phase 16           |
| §13 External Functions   | read, puts, env                             | Phase 18           |
| §14 Semantics            | Truthiness, precedence, scoping             | Phases 4, 7        |
| §15 Implementation Notes | Error handling, TCO requirements            | Phases 14, 17      |
| Appendix A               | Grammar (EBNF)                              | Phases 1-3         |
| Appendix B               | Built-in function reference                 | Phases 9-13        |
| Appendix C               | Operator precedence table                   | Phase 2            |
| Appendix D               | Example programs (integration tests)        | Phase 20           |

---

## TDD Methodology for Each Phase

**Every feature follows the RED→GREEN→REFACTOR cycle:**

1. **Identify behavior** from LANG.txt specification
2. **Write failing test** that describes the expected behavior
3. **Run test** - verify it fails for the right reason
4. **Write minimum code** to make the test pass
5. **Run test** - verify it passes
6. **Refactor** - improve code while keeping tests green
7. **Repeat** for next behavior

**Test file structure:**
- Each module has a `tests.rs` file
- Tests use `expect_test` for snapshot assertions
- Tests are integration-style (use real collaborators)

---

## Project Structure

```
/
├── Cargo.toml                 # Workspace root
├── lang/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── lexer/
│       │   ├── mod.rs
│       │   ├── token.rs
│       │   └── tests.rs
│       ├── parser/
│       │   ├── mod.rs
│       │   ├── ast.rs
│       │   └── tests.rs
│       ├── codegen/
│       │   ├── mod.rs
│       │   ├── context.rs     # LLVM context/module management
│       │   ├── compiler.rs    # AST to LLVM IR
│       │   ├── types.rs       # Value representation
│       │   └── tests.rs
│       ├── runtime/
│       │   ├── mod.rs
│       │   ├── value.rs       # Runtime value operations
│       │   ├── collections.rs # List, Set, Dict, Range
│       │   ├── builtins.rs    # Built-in function implementations
│       │   └── refcount.rs    # Reference counting
│       └── runner/
│           ├── mod.rs
│           └── tests.rs
├── runtime/
│   └── cli/
│       ├── Cargo.toml
│       └── src/
│           ├── main.rs
│           └── external.rs
├── examples/
│   ├── *.santa              # AOC solution files
│   └── run-tests.sh         # Test runner script
└── benchmarks/
    ├── Cargo.toml
    └── benches/
        └── compiler_benchmarks.rs
```

## Dependencies

```toml
# lang/Cargo.toml
[dependencies]
inkwell = { version = "0.5", features = ["llvm18-0"] }
im = { git = "ssh://git@github.com/eddmann/im-rs.git" }
ordered-float = "4.2"
unicode-segmentation = "1.10"
regex = "1.10"

[dev-dependencies]
expect-test = "1.5"
```

---

## Phase 1: Lexer

**Goal**: Tokenize santa-lang source into a stream of tokens.

**LANG.txt Reference**: §2 Lexical Structure, Appendix A (Grammar - lexical rules)

### 1.1 Token Types

Define all token types per LANG.txt §2:

- Keywords: `let`, `mut`, `if`, `else`, `match`, `return`, `break`, `nil`, `true`, `false`
- Literals: Integer, Decimal, String (with escape sequences)
- Identifiers: `[a-zA-Z][a-zA-Z0-9_?]*`
- Operators: `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`, `!`, `|>`, `>>`, `..`, `..=`
- Delimiters: `(`, `)`, `[`, `]`, `{`, `}`, `#{`, `,`, `:`, `;`, `|`, `` ` ``
- Comments: `// ...`
- Special: `_` (placeholder/wildcard)

### 1.2 Lexer Implementation

- UTF-8 source input
- Track line/column for error reporting
- Handle underscores in numeric literals (`1_000_000`)
- String escape sequences: `\n`, `\t`, `\r`, `\b`, `\f`, `\"`, `\\`
- Produce `Vec<Token>` with spans

### 1.3 Tests (expect_test snapshots)

```rust
#[test]
fn lex_integer_literals() { ... }
#[test]
fn lex_decimal_literals() { ... }
#[test]
fn lex_string_with_escapes() { ... }
#[test]
fn lex_operators() { ... }
#[test]
fn lex_keywords_vs_identifiers() { ... }
#[test]
fn lex_range_operators() { ... }
#[test]
fn lex_comments() { ... }
```

### Release Gate 1

- [ ] All token types from LANG.txt Section 2 are lexed correctly
- [ ] Error positions (line:column) are accurate
- [ ] All expect_test snapshots pass
- [ ] `cargo clippy` clean

---

## Phase 2: Parser - Expressions

**Goal**: Parse expressions into an AST using Pratt parsing.

**LANG.txt Reference**: §4 Operators, §6 Expressions, §8.1-8.7 Functions, §14.5 Operator Precedence, Appendix A & C

### 2.1 AST Node Types

```rust
pub enum Expr {
    // Literals
    Integer(i64),
    Decimal(f64),
    String(String),
    Boolean(bool),
    Nil,

    // Collections
    List(Vec<Expr>),
    Set(Vec<Expr>),
    Dict(Vec<(Expr, Expr)>),
    Range { start: Box<Expr>, end: Option<Box<Expr>>, inclusive: bool },

    // Identifiers & Placeholders
    Identifier(String),
    Placeholder,
    RestIdentifier(String),

    // Operations
    Prefix { op: PrefixOp, right: Box<Expr> },
    Infix { left: Box<Expr>, op: InfixOp, right: Box<Expr> },
    Index { collection: Box<Expr>, index: Box<Expr> },

    // Functions
    Function { params: Vec<Param>, body: Box<Expr> },
    Call { function: Box<Expr>, args: Vec<Expr> },
    InfixCall { function: String, left: Box<Expr>, right: Box<Expr> },

    // Control Flow
    If { condition: Box<Expr>, then_branch: Box<Expr>, else_branch: Option<Box<Expr>> },
    IfLet { pattern: Pattern, value: Box<Expr>, then_branch: Box<Expr>, else_branch: Option<Box<Expr>> },
    Match { subject: Box<Expr>, arms: Vec<MatchArm> },
    Block(Vec<Stmt>),

    // Spread
    Spread(Box<Expr>),
}
```

### 2.2 Operator Precedence (from santa-lang-rs reference implementation)

From highest to lowest:
1. `[]` - Index (highest)
2. `()` - Call
3. `!` `-` - Prefix
4. `*` `/` `%` `` ` `` - Multiplicative/Infix
5. `+` `-` - Additive
6. `>>` `|>` `..` `..=` - Composition/Pipeline/Range
7. `<` `<=` `>` `>=` - Comparison
8. `==` `!=` `=` - Equality/Assignment (same level)
9. `&&` `||` - Logical AND/OR (same level, lowest)

**Note**: This matches santa-lang-rs behavior where `&&` and `||` have the same precedence, and `=` groups with equality operators.

### 2.3 Trailing Lambda Syntax (Recognition)

The parser recognizes the pattern `expr identifier lambda`:

```santa
[1, 2, 3] map |x| x * 2
```

This is recognized as a trailing lambda call. The transformation to `map([1,2,3], |x| x*2)` happens in Phase 3 (see §3.7).

### 2.4 Tests

```rust
#[test]
fn parse_literals() { ... }
#[test]
fn parse_binary_operators() { ... }
#[test]
fn parse_operator_precedence() { ... }
#[test]
fn parse_function_expressions() { ... }
#[test]
fn parse_partial_application() { ... }
#[test]
fn parse_collections() { ... }
#[test]
fn parse_ranges() { ... }
#[test]
fn parse_index_expressions() { ... }
#[test]
fn parse_pipeline() { ... }
#[test]
fn parse_composition() { ... }
#[test]
fn parse_trailing_lambda_syntax() { ... }  // [1,2,3] map |x| x*2
```

### Release Gate 2

- [ ] All expression forms from LANG.txt parse correctly
- [ ] Operator precedence matches santa-lang-rs exactly
- [ ] Partial application (`_ + 1`) produces Function AST
- [ ] Trailing lambda syntax is recognized
- [ ] All expect_test snapshots pass
- [ ] `cargo clippy` clean

---

## Phase 3: Parser - Statements, Patterns & Sections

**Goal**: Complete the parser with statements, pattern matching, and AOC sections.

**LANG.txt Reference**: §5 Variables & Bindings, §7 Control Flow, §9 Pattern Matching, §12 AOC Runner, Appendix A

### 3.1 Statement Types

```rust
pub enum Stmt {
    Let { mutable: bool, pattern: Pattern, value: Expr },
    Return(Expr),
    Break(Expr),
    Expr(Expr),
}
```

### 3.2 Pattern Types

```rust
pub enum Pattern {
    Wildcard,                           // _
    Identifier(String),                 // x
    RestIdentifier(String),             // ..rest
    Literal(Literal),                   // 42, "hello", true
    List(Vec<Pattern>),                 // [a, b, ..rest]
    Range { start: i64, end: Option<i64>, inclusive: bool },
}
```

### 3.3 AOC Sections (Top-Level)

```rust
pub enum Section {
    Input(Expr),
    PartOne(Expr),
    PartTwo(Expr),
    Test { input: Expr, part_one: Option<Expr>, part_two: Option<Expr> },
}

pub struct Program {
    pub statements: Vec<Stmt>,
    pub sections: Vec<Section>,
}
```

### 3.4 Special Syntax Features

Per LANG.txt:

- **Trailing comma** (§10.2): `[1, 2, 3,]` is valid
- **Infix function calls** (§6.5): `` `includes?` `` backtick syntax

### 3.5 Empty Set vs Empty Block Disambiguation

The parser must distinguish `{}` based on context (LANG.txt §3.6):

```
Expression position → Empty Set:
  let x = {};              // Empty set
  fold({}, |acc, x| ...)   // Empty set as argument
  [1, {}, 3]               // Empty set in list

Statement position → Empty Block:
  if true { }              // Empty block
  let f = || { };          // Empty block (function body)
  match x { _ { } }        // Empty block (match arm)
```

**Parser Strategy**: Track whether we're parsing a "value expression" (RHS of let, function argument, collection element) or a "statement body" (if/else body, function body, match arm body). Default `{}` to Set in value context, Block in statement context.

### 3.6 Dict Shorthand Syntax

When parsing dictionary literals, bare identifiers become string-keyed entries (LANG.txt §3.7):

```rust
// #{name, age} transforms during parsing to:
// #{Expr::String("name"): Expr::Identifier("name"),
//   Expr::String("age"): Expr::Identifier("age")}

fn parse_dict_entry(&mut self) -> Result<(Expr, Expr), ParseError> {
    if self.current_is_identifier() && self.peek_is(Token::Comma | Token::RBrace) {
        // Shorthand: #{name} → #{"name": name}
        let name = self.consume_identifier()?;
        let key = Expr::String(name.clone());
        let value = Expr::Identifier(name);
        Ok((key, value))
    } else {
        // Explicit: key: value
        let key = self.parse_expression()?;
        self.expect(Token::Colon)?;
        let value = self.parse_expression()?;
        Ok((key, value))
    }
}
```

### 3.7 Trailing Lambda (Semantics)

When an expression is followed by an identifier and a lambda (without pipeline):

```santa
[1, 2, 3] map |x| x * 2
// Parses as: map([1, 2, 3], |x| x * 2)
```

The parser recognizes this pattern and transforms it during parsing. See Phase 2 for the syntax recognition.

### 3.8 Tests

```rust
#[test]
fn parse_let_binding() { ... }
#[test]
fn parse_let_destructuring() { ... }
#[test]
fn parse_mutable_binding() { ... }
#[test]
fn parse_match_expression() { ... }
#[test]
fn parse_match_with_guards() { ... }
#[test]
fn parse_aoc_sections() { ... }
#[test]
fn parse_test_sections() { ... }
#[test]
fn parse_trailing_lambda() { ... }
#[test]
fn parse_empty_set_in_expression_position() { ... }  // let x = {}
#[test]
fn parse_empty_block_in_statement_position() { ... } // if true { }
#[test]
fn parse_dict_shorthand() { ... }                    // #{name, age}
```

### Release Gate 3

- [ ] All statement forms parse correctly
- [ ] Destructuring patterns work (including nested, rest)
- [ ] Match expressions with guards parse correctly
- [ ] AOC sections (`input:`, `part_one:`, `part_two:`, `test:`) parse
- [ ] Trailing lambda syntax works
- [ ] **Empty `{}` disambiguates correctly** (Set vs Block)
- [ ] **Dict shorthand** parses correctly
- [ ] All expect_test snapshots pass
- [ ] `cargo clippy` clean

---

## Phase 4: LLVM Runtime Support Library

**Goal**: Build the FFI runtime library that LLVM-compiled code calls into.

**This is NOT an interpreter.** These are `extern "C"` functions that get linked with the compiled output.

**LANG.txt Reference**: §3 Type System (all types), §3.11 Hashability, §14.1 Truthy/Falsy Values

### 4.1 Value Representation (NaN-boxing)

NaN-boxing uses the unused bits in IEEE-754 NaN representations to encode values inline.

```rust
// 64-bit NaN-boxed value representation
//
// IEEE-754 doubles use bits 51-62 for exponent. When all 11 exponent bits are 1
// and the mantissa is non-zero, it's a NaN. We use this space for tagged values.
//
// Layout:
//   Heap pointer: 0x0000_XXXX_XXXX_XXXX (48-bit pointer, high bits 0)
//   NaN space:    0x7FF8_0000_0000_0000+ (quiet NaN, we use bits below)
//
// Tag scheme (in NaN payload):
//   0x7FF8 | 0001 = Integer (51-bit signed in lower bits)
//   0x7FF8 | 0002 = Nil
//   0x7FF8 | 0003 = Boolean (1 = true, 0 = false in lower bits)
//   Pointer       = High bits all zero, 48-bit aligned pointer

#[repr(C)]
pub struct Value(u64);

impl Value {
    pub fn is_integer(&self) -> bool;
    pub fn as_integer(&self) -> Option<i64>;  // 51-bit integers inline
    pub fn from_integer(i: i64) -> Value;     // Box if > 51 bits
    pub fn is_nil(&self) -> bool;
    pub fn is_heap_object(&self) -> bool;
    pub fn as_f64(&self) -> Option<f64>;      // Decimals stored as native f64
    // ... etc
}
```

**Note**: Integers larger than 51 bits must be boxed as heap objects. This is an implementation detail - the language semantics remain 64-bit integers.

### 4.2 Heap Objects

```rust
#[repr(C)]
pub struct HeapObject {
    pub header: ObjectHeader,
    // payload follows
}

#[repr(C)]
pub struct ObjectHeader {
    pub refcount: AtomicU32,
    pub type_tag: TypeTag,
}

#[repr(u8)]
pub enum TypeTag {
    String,
    Decimal,       // Boxed decimal (for large values)
    BoxedInteger,  // For integers > 51 bits
    List,
    Set,
    Dict,
    Function,
    Closure,
    LazySequence,  // Note: Ranges are represented as LazySequences
    MutableCell,   // For mutable captured variables (heap-boxed)
}
```

### 4.3 Reference Counting

```rust
// Called from generated code
#[no_mangle]
pub extern "C" fn rt_incref(value: Value) {
    if let Some(obj) = value.as_heap_object() {
        obj.header.refcount.fetch_add(1, Ordering::Relaxed);
    }
}

#[no_mangle]
pub extern "C" fn rt_decref(value: Value) {
    if let Some(obj) = value.as_heap_object() {
        if obj.header.refcount.fetch_sub(1, Ordering::Release) == 1 {
            std::sync::atomic::fence(Ordering::Acquire);
            rt_free(obj);
        }
    }
}
```

### 4.4 Collection Types (im-rs Persistent)

```rust
use im::{Vector, HashSet, HashMap};

pub struct ListObject {
    header: ObjectHeader,
    data: Vector<Value>,
}

pub struct SetObject {
    header: ObjectHeader,
    data: HashSet<Value>,
}

pub struct DictObject {
    header: ObjectHeader,
    data: HashMap<Value, Value>,
}
```

### 4.5 Mutable Captures (Heap-Boxed Cells)

Mutable variables captured by closures use heap-boxed cells to allow shared mutation:

```rust
pub struct MutableCellObject {
    header: ObjectHeader,
    value: Value,  // The current value
}

// When a mutable variable is captured:
// 1. Allocate MutableCell on heap
// 2. Both outer scope and closure reference the same cell
// 3. Reads/writes go through the cell

#[no_mangle]
pub extern "C" fn rt_cell_get(cell: Value) -> Value { ... }

#[no_mangle]
pub extern "C" fn rt_cell_set(cell: Value, value: Value) { ... }
```

This enables the counter pattern from LANG.txt §8.3 where inner closures can mutate variables from outer scopes.

### 4.6 String Handling (Grapheme Clusters)

Strings use grapheme-cluster indexing via `unicode-segmentation` crate:

```rust
use unicode_segmentation::UnicodeSegmentation;

pub struct StringObject {
    header: ObjectHeader,
    data: String,                    // UTF-8 data
    // Optional: cached grapheme indices for O(1) repeated access
}

// Indexing is O(n) - must iterate graphemes
// Consider caching grapheme boundaries for strings accessed multiple times
```

**Note**: `"👨‍👩‍👧‍👦"[0]` returns the whole family emoji as a single grapheme cluster.

### 4.8 Tests

```rust
#[test]
fn value_nan_boxing() { ... }
#[test]
fn value_large_integer_boxing() { ... }  // Integers > 51 bits
#[test]
fn value_equality() { ... }
#[test]
fn value_hashing() { ... }
#[test]
fn value_truthiness() { ... }
#[test]
fn refcount_increment_decrement() { ... }
#[test]
fn collection_operations() { ... }
#[test]
fn mutable_cell_operations() { ... }
#[test]
fn grapheme_string_indexing() { ... }
#[test]
fn unhashable_in_set_errors() { ... }  // {|x| x} and {#{a:1}} cause RuntimeErr
#[test]
fn unhashable_dict_key_errors() { ... }
```

### Release Gate 4

- [ ] NaN-boxing scheme works for inline integers and decimals
- [ ] Large integers (>51 bits) are boxed correctly
- [ ] Reference counting increments/decrements correctly
- [ ] Hashable values work correctly in Sets and Dict keys
- [ ] Non-hashable values (functions, dicts) produce RuntimeErr in Sets/Dict keys
- [ ] Truthiness matches LANG.txt Section 14.1
- [ ] Mutable cells work for captured variables
- [ ] Grapheme-cluster string indexing works (emoji test)
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 5: LLVM Codegen - Expressions

**Goal**: Generate LLVM IR for expressions.

**LANG.txt Reference**: §4 Operators, §4.7 Pipeline, §4.8 Composition, §8.4 Partial Application

### 5.1 LLVM Context Setup

```rust
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::builder::Builder;

pub struct CodegenContext<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,

    // Runtime function declarations
    rt_add: FunctionValue<'ctx>,
    rt_sub: FunctionValue<'ctx>,
    rt_mul: FunctionValue<'ctx>,
    rt_div: FunctionValue<'ctx>,
    rt_incref: FunctionValue<'ctx>,
    rt_decref: FunctionValue<'ctx>,
    // ... etc
}
```

### 5.2 Expression Compilation

```rust
impl<'ctx> CodegenContext<'ctx> {
    pub fn compile_expr(&mut self, expr: &Expr) -> Result<BasicValueEnum<'ctx>, CompileError> {
        match expr {
            Expr::Integer(n) => self.compile_integer(*n),
            Expr::Decimal(f) => self.compile_decimal(*f),
            Expr::String(s) => self.compile_string(s),
            Expr::Boolean(b) => self.compile_boolean(*b),
            Expr::Nil => self.compile_nil(),
            Expr::Infix { left, op, right } => self.compile_binary(left, op, right),
            Expr::Prefix { op, right } => self.compile_unary(op, right),
            Expr::Call { function, args } => self.compile_call(function, args),
            // ... etc
        }
    }

    fn compile_integer(&mut self, n: i64) -> BasicValueEnum<'ctx> {
        // Create tagged integer value
        let tagged = (n << 3) | 0b001;
        self.context.i64_type().const_int(tagged as u64, false).into()
    }

    fn compile_binary(&mut self, left: &Expr, op: &InfixOp, right: &Expr)
        -> Result<BasicValueEnum<'ctx>, CompileError>
    {
        let left_val = self.compile_expr(left)?;
        let right_val = self.compile_expr(right)?;

        // Call runtime helper for type-aware operation
        match op {
            InfixOp::Add => self.builder.build_call(self.rt_add, &[left_val, right_val], "add"),
            // ... etc
        }
    }
}
```

### 5.3 Runtime Helpers for Operations

```rust
// In runtime library (linked with generated code)
#[no_mangle]
pub extern "C" fn rt_add(left: Value, right: Value) -> Value {
    match (left.type_tag(), right.type_tag()) {
        (TypeTag::Integer, TypeTag::Integer) => {
            Value::from_integer(left.as_integer() + right.as_integer())
        }
        (TypeTag::String, _) => {
            // String concatenation with type coercion
            rt_string_concat(left, right)
        }
        (TypeTag::List, TypeTag::List) => rt_list_concat(left, right),
        (TypeTag::Set, TypeTag::Set) => rt_set_union(left, right),
        (TypeTag::Dict, TypeTag::Dict) => rt_dict_merge(left, right),
        _ => rt_type_error("add", left, right),
    }
}
```

### 5.4 Tests

```rust
#[test]
fn codegen_integer_literal() { ... }
#[test]
fn codegen_binary_expression() { ... }
#[test]
fn codegen_nested_expression() { ... }
#[test]
fn codegen_function() { ... }
#[test]
fn codegen_partial_application() { ... }
#[test]
fn codegen_pipeline() { ... }
```

### Release Gate 5

- [ ] All expression types compile to correct LLVM IR
- [ ] Partial application generates correct closure
- [ ] Pipeline operator compiles correctly
- [ ] Generated code links with runtime library
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 6: LLVM Codegen - Statements & Control Flow

**Goal**: Complete code generation with statements and control flow.

**LANG.txt Reference**: §5 Variables & Bindings, §7 Control Flow, §14.6 Scoping Rules

### 6.1 Variable Management

```rust
pub struct LocalVar<'ctx> {
    alloca: PointerValue<'ctx>,  // Stack slot
    mutable: bool,
}

impl<'ctx> CodegenContext<'ctx> {
    fn create_local(&mut self, name: &str, mutable: bool) -> LocalVar<'ctx> {
        let alloca = self.create_entry_block_alloca(name);
        LocalVar { alloca, mutable }
    }
}
```

### 6.2 Control Flow Compilation

```rust
fn compile_if(&mut self, cond: &Expr, then_br: &Expr, else_br: Option<&Expr>)
    -> Result<BasicValueEnum<'ctx>, CompileError>
{
    let cond_val = self.compile_expr(cond)?;
    let is_truthy = self.builder.build_call(self.rt_is_truthy, &[cond_val], "truthy");

    let then_bb = self.context.append_basic_block(self.current_fn, "then");
    let else_bb = self.context.append_basic_block(self.current_fn, "else");
    let merge_bb = self.context.append_basic_block(self.current_fn, "merge");

    self.builder.build_conditional_branch(is_truthy, then_bb, else_bb);

    // Compile then branch
    self.builder.position_at_end(then_bb);
    let then_val = self.compile_expr(then_br)?;
    self.builder.build_unconditional_branch(merge_bb);

    // Compile else branch
    self.builder.position_at_end(else_bb);
    let else_val = match else_br {
        Some(e) => self.compile_expr(e)?,
        None => self.compile_nil(),
    };
    self.builder.build_unconditional_branch(merge_bb);

    // Merge
    self.builder.position_at_end(merge_bb);
    let phi = self.builder.build_phi(self.value_type(), "if_result");
    phi.add_incoming(&[(&then_val, then_bb), (&else_val, else_bb)]);

    Ok(phi.as_basic_value())
}
```

### 6.3 Protected Built-in Names

Per LANG.txt §14.6, built-in function names cannot be shadowed:

```rust
// List of protected names (all 66 built-in functions)
const PROTECTED_NAMES: &[&str] = &[
    "int", "ints", "list", "set", "dict", "get", "size", "first", "second",
    "last", "rest", "keys", "values", "push", "assoc", "update", "update_d",
    "map", "filter", "flat_map", "filter_map", "find_map", "reduce", "fold",
    "fold_s", "scan", "each", "find", "count", "sum", "max", "min", "skip",
    "take", "sort", "reverse", "rotate", "chunk", "union", "intersection",
    "includes?", "excludes?", "any?", "all?", "zip", "repeat", "cycle",
    "iterate", "combinations", "range", "lines", "split", "regex_match",
    "regex_match_all", "md5", "upper", "lower", "replace", "join", "abs",
    "signum", "vec_add", "bit_and", "bit_or", "bit_xor", "bit_not",
    "bit_shift_left", "bit_shift_right", "id", "type", "memoize", "or", "and",
    // Note: "evaluate" excluded since it's out of scope for Dasher
];

fn check_protected_name(name: &str, source: Span) -> Result<(), CompileError> {
    if PROTECTED_NAMES.contains(&name) {
        Err(CompileError::ProtectedName { name: name.to_string(), source })
    } else {
        Ok(())
    }
}
```

### 6.4 Tests

```rust
#[test]
fn codegen_let_binding() { ... }
#[test]
fn codegen_destructuring() { ... }
#[test]
fn codegen_if_expression() { ... }
#[test]
fn codegen_match_expression() { ... }
#[test]
fn codegen_block_scoping() { ... }
#[test]
fn codegen_shadowing() { ... }
#[test]
fn codegen_protected_name_error() { ... }  // let sum = ... → CompileError
```

### Release Gate 6

- [ ] Variable scoping works correctly
- [ ] Shadowing behaves per LANG.txt
- [ ] **Protected built-in names cannot be shadowed**
- [ ] If expressions generate correct branch structure
- [ ] Match compilation handles all pattern types
- [ ] Guard clauses compile correctly
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 7: Runtime - Core Operations

**Goal**: Implement runtime operations called from generated code.

**LANG.txt Reference**: §4.1 Type Coercion Rules, §4 All Operators, §14.1 Truthy/Falsy

### 7.1 Arithmetic Operations

```rust
#[no_mangle]
pub extern "C" fn rt_add(left: Value, right: Value) -> Value { ... }

#[no_mangle]
pub extern "C" fn rt_sub(left: Value, right: Value) -> Value { ... }

#[no_mangle]
pub extern "C" fn rt_mul(left: Value, right: Value) -> Value { ... }

#[no_mangle]
pub extern "C" fn rt_div(left: Value, right: Value) -> Value { ... }

#[no_mangle]
pub extern "C" fn rt_mod(left: Value, right: Value) -> Value { ... }
```

### 7.2 Comparison Operations

```rust
#[no_mangle]
pub extern "C" fn rt_eq(left: Value, right: Value) -> Value { ... }

#[no_mangle]
pub extern "C" fn rt_lt(left: Value, right: Value) -> Value { ... }

#[no_mangle]
pub extern "C" fn rt_le(left: Value, right: Value) -> Value { ... }
```

### 7.3 Division and Modulo Semantics (IMPORTANT)

Santa uses **Python-style floored division**, NOT Rust's truncated division:

```rust
// Floored division (rounds toward negative infinity)
// -7 / 2 = -4  (NOT -3 like Rust's default)
// 7 / -2 = -4  (NOT -3)

pub fn floored_div(a: i64, b: i64) -> i64 {
    let q = a / b;
    let r = a % b;
    if (r != 0) && ((r < 0) != (b < 0)) { q - 1 } else { q }
}

// Floored modulo (result has same sign as divisor)
// -7 % 3 = 2   (NOT -1 like Rust)
// 7 % -3 = -2  (NOT 1)

pub fn floored_mod(a: i64, b: i64) -> i64 {
    ((a % b) + b) % b
}
```

### 7.4 Type Coercion Rules

Per LANG.txt §4.1:
- Integer + Decimal: left operand determines result type
- String + any: right operand coerced to string (when left is String)
- Integer + String: ERROR (not supported)

### 7.5 Comparison Restrictions

Only Integer, Decimal, and String support comparison operators (`<`, `>`, `<=`, `>=`).
Comparing other types (List, Set, Dict, Function, LazySequence) produces RuntimeErr.

### 7.7 Tests

```rust
#[test]
fn runtime_arithmetic() { ... }
#[test]
fn runtime_floored_division() { ... }     // -7/2=-4, 7/-2=-4
#[test]
fn runtime_floored_modulo() { ... }       // -7%3=2, 7%-3=-2
#[test]
fn runtime_comparison() { ... }
#[test]
fn runtime_comparison_type_errors() { ... } // [1,2] < [3,4] → RuntimeErr
#[test]
fn runtime_string_operations() { ... }
#[test]
fn runtime_collection_operations() { ... }
#[test]
fn runtime_type_coercion() { ... }
```

### Release Gate 7

- [ ] All arithmetic operations work correctly
- [ ] **Floored division semantics** match Python (-7/2=-4)
- [ ] **Floored modulo semantics** match Python (-7%3=2)
- [ ] Type coercion matches LANG.txt Section 4.1
- [ ] Comparison on non-comparable types produces RuntimeErr
- [ ] Division by zero produces RuntimeErr
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 8: Closures & Function Calls

**Goal**: Implement closures with captured variables.

**LANG.txt Reference**: §8.3 Closures (including mutable capture example)

### 8.1 Closure Representation

```rust
#[repr(C)]
pub struct ClosureObject {
    header: ObjectHeader,
    function_ptr: *const (),      // Pointer to compiled function
    env_size: u32,                // Number of captured values
    env: [Value; 0],              // Flexible array of captured values
}

impl ClosureObject {
    pub fn captures(&self) -> &[Value] {
        unsafe {
            std::slice::from_raw_parts(self.env.as_ptr(), self.env_size as usize)
        }
    }
}
```

### 8.2 Closure Compilation

```rust
impl<'ctx> CodegenContext<'ctx> {
    fn compile_closure(&mut self, params: &[Param], body: &Expr, captures: &[String])
        -> Result<BasicValueEnum<'ctx>, CompileError>
    {
        // Compile the function body
        let fn_ptr = self.compile_function_body(params, body, captures)?;

        // Create closure object with captured values
        let closure = self.builder.build_call(
            self.rt_make_closure,
            &[fn_ptr, capture_count, ...captured_values],
            "closure"
        );

        Ok(closure)
    }
}
```

### 8.3 Calling Convention

All functions receive:
1. Environment pointer (for closures, NULL for top-level)
2. Argument count
3. Arguments array

```rust
#[no_mangle]
pub extern "C" fn rt_call(callee: Value, argc: u32, argv: *const Value) -> Value {
    match callee.as_closure() {
        Some(closure) => {
            let fn_ptr: fn(*const ClosureObject, u32, *const Value) -> Value =
                unsafe { std::mem::transmute(closure.function_ptr) };
            fn_ptr(closure, argc, argv)
        }
        None => rt_type_error("call", callee),
    }
}
```

### 8.4 Tests

```rust
#[test]
fn closure_capture_local() { ... }
#[test]
fn closure_capture_upvalue() { ... }
#[test]
fn closure_mutable_capture() { ... }
#[test]
fn nested_closures() { ... }
```

### Release Gate 8

- [ ] Simple closures capture variables correctly
- [ ] Nested closures work
- [ ] Mutable captures update correctly
- [ ] Counter example from LANG.txt works correctly
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 9: Built-in Functions - Core

**Goal**: Implement core built-in functions.

**LANG.txt Reference**: §11.1 Type Conversion, §11.2 Collection Access, §11.3 Collection Modification, Appendix B

### 9.1 Type Conversion

- `int(value)` - parse to integer (round decimals half away from zero)
- `ints(string)` - extract all integers with regex
- `list(value)` - convert to list
- `set(value)` - convert to set
- `dict(value)` - convert to dictionary

### 9.2 Collection Access

- `get(index, collection)` - get element at index
- `size(collection)` - get size
- `first(collection)`, `second(collection)`, `rest(collection)`
- `keys(dict)`, `values(dict)`

### 9.3 Collection Modification

- `push(value, collection)` - add value
- `assoc(key, value, collection)` - associate key
- `update(key, fn, collection)` - update with function
- `update_d(key, default, fn, collection)` - update with default

### 9.4 Tests

```rust
#[test]
fn builtin_int_conversion() { ... }
#[test]
fn builtin_ints_extraction() { ... }
#[test]
fn builtin_collection_access() { ... }
#[test]
fn builtin_collection_modification() { ... }
```

### Release Gate 9

- [ ] All type conversion functions work per spec
- [ ] Collection access handles all types
- [ ] Collection modification is immutable (returns new)
- [ ] Edge cases return nil (not errors) where specified
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 10: Built-in Functions - Transformations

**Goal**: Implement higher-order transformation functions.

**LANG.txt Reference**: §11.4 Transformation, §11.5 Reduction, §11.6 Iteration, Appendix B

### 10.1 Transformation Functions

- `map(fn, collection)` - transform each element
- `filter(predicate, collection)` - keep matching
- `flat_map(fn, collection)` - map and flatten
- `filter_map(fn, collection)` - map and filter truthy
- `find_map(fn, collection)` - find first truthy mapped

**Dict Callback Arities**: When operating on Dictionaries, callbacks support two arities:
```santa
// Single-arg: receives value only
map(_ + 1, #{1: 2, 3: 4})           // #{1: 3, 3: 5}

// Two-arg: receives (value, key)
map(|v, k| k + v, #{1: 2, 3: 4})    // #{1: 3, 3: 7}
```

The runtime must detect callback arity and call appropriately.

### 10.2 Reduction Functions

- `reduce(fn, collection)` - reduce with first as initial
- `fold(initial, fn, collection)` - fold with initial
- `fold_s(initial, fn, collection)` - fold with state
- `scan(initial, fn, collection)` - intermediate results

### 10.3 Iteration

- `each(fn, collection)` - side effects, returns nil

### 10.4 Tests

```rust
#[test]
fn builtin_map() { ... }
#[test]
fn builtin_filter() { ... }
#[test]
fn builtin_reduce() { ... }
#[test]
fn builtin_fold() { ... }
#[test]
fn builtin_dict_single_arg_callback() { ... }  // map(_ + 1, dict)
#[test]
fn builtin_dict_two_arg_callback() { ... }     // map(|v, k| v + k, dict)
#[test]
fn builtin_reduce_empty_error() { ... }        // reduce(+, []) → RuntimeErr
#[test]
fn builtin_fold_empty_returns_initial() { ... }
```

### Release Gate 10

- [ ] All transformation functions work on all collection types
- [ ] Dict callbacks handle both (value) and (value, key) arities
- [ ] Reduce on empty collection throws RuntimeErr
- [ ] Fold on empty collection returns initial
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 11: Built-in Functions - Search & Aggregation

**Goal**: Complete search and aggregation functions.

**LANG.txt Reference**: §11.7-11.11, Appendix B

### 11.1 Functions

- `find`, `count`, `sum`, `max`, `min`
- `skip`, `take`, `sort`, `reverse`, `rotate`, `chunk`
- `union`, `intersection`
- `includes?`, `excludes?`, `any?`, `all?`

### Release Gate 11

- [ ] All search functions work correctly
- [ ] max/min handle varargs and single collection
- [ ] sort accepts both boolean and integer comparators
- [ ] Set operations work on mixed collection types
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 12: Lazy Sequences

**Goal**: Implement infinite lazy sequences.

**LANG.txt Reference**: §3.8 Lazy Sequence, §10.5, §11.12-11.13, §14.3

### 12.1 LazySequence Type

```rust
pub enum LazySeq {
    Range { current: i64, end: Option<i64>, inclusive: bool },
    Repeat { value: Value },
    Cycle { source: im::Vector<Value>, index: usize },
    Iterate { generator: Value, current: Value },
    Map { source: Box<LazySeq>, mapper: Value },
    Filter { source: Box<LazySeq>, predicate: Value },
    Skip { source: Box<LazySeq>, remaining: usize },
    Zip { sources: Vec<Box<LazySeq>> },
    Combinations { source: Vec<Value>, size: usize, indices: Vec<usize> },
}
```

### 12.2 Lazy Sequence Generators

- `repeat(value)`, `cycle(collection)`, `iterate(fn, initial)`
- `combinations(size, collection)`, `range(from, to, step)`
- `zip(..collections)`

### 12.3 Break from Iteration

Handle `break` in reduce/fold/each on infinite sequences.

### Release Gate 12

- [ ] Unbounded ranges work with take/find
- [ ] iterate generates correct sequences
- [ ] Lazy map/filter compose correctly
- [ ] break works in reduce/fold/each on infinite sequences
- [ ] combinations generates correct subsets
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 13: Built-in Functions - Remaining

**Goal**: Complete all remaining built-in functions.

**LANG.txt Reference**: §11.14-11.16, §4.5, Appendix B

### 13.1 String Functions

- `lines(string)`, `split(separator, string)`
- `regex_match(pattern, string)`, `regex_match_all(pattern, string)`
- `md5(string)`

### 13.2 Math Functions

- `abs(value)`, `signum(value)`, `vec_add(a, b)`

### 13.3 Bitwise Functions

- `bit_and`, `bit_or`, `bit_xor`, `bit_not`
- `bit_shift_left`, `bit_shift_right`

### 13.4 Utility Functions

- `id(value)`, `type(value)`, `memoize(fn)`
- `or(a, b)`, `and(a, b)`, `evaluate(string)`

### Release Gate 13

- [ ] All string functions work correctly
- [ ] Grapheme-cluster indexing for Unicode strings
- [ ] Regex functions handle errors gracefully
- [ ] All bitwise operations work on integers
- [ ] memoize caches results correctly
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 14: Tail-Call Optimization

**Goal**: Implement tail-call optimization for self-recursion.

**LANG.txt Reference**: §8.9 Recursion and TCO, §15 Implementation Notes

### 14.1 TCO Detection

Identify tail calls during compilation:
- Last expression in function body
- Self-recursive call (same function)
- No operations after the call

### 14.2 TCO Implementation

Convert tail calls to jumps:

```rust
fn compile_tail_call(&mut self, args: &[Expr]) -> Result<(), CompileError> {
    // Evaluate new arguments
    for (i, arg) in args.iter().enumerate() {
        let val = self.compile_expr(arg)?;
        // Store in parameter slots
        self.builder.build_store(self.param_slots[i], val);
    }

    // Jump to function entry
    self.builder.build_unconditional_branch(self.entry_block);
}
```

### 14.3 Tests

```rust
#[test]
fn tco_factorial() { ... }
#[test]
fn tco_deep_recursion() { ... }
#[test]
fn tco_not_applied_to_non_tail() { ... }
```

### Release Gate 14

- [ ] TCO applies to self-recursive tail calls
- [ ] Deep recursion (100k+) works without stack overflow
- [ ] Non-tail recursive calls work normally
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 15: Pattern Matching

**Goal**: Full pattern matching support.

**LANG.txt Reference**: §9 Pattern Matching

### 15.1 Pattern Types

- Wildcard `_`, Identifier, Literal
- List patterns with rest `..`
- Range patterns
- Guards

### 15.2 Compilation Strategy

Generate decision tree for efficient matching.

### Release Gate 15

- [ ] All pattern types match correctly
- [ ] Rest patterns work in any position
- [ ] Nested patterns work
- [ ] Guards evaluate correctly
- [ ] Match returns nil if no arm matches
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 16: AOC Runner

**Goal**: Implement the AOC solution runner.

**LANG.txt Reference**: §12 AOC Runner

### 16.1 Execution Flow

1. Evaluate top-level statements
2. Evaluate `input:` section
3. Run `part_one:` and `part_two:` with timing
4. For tests: create fresh environment, run with test input

### 16.2 Test Attributes

The `@slow` attribute marks tests that should be skipped by default:

```santa
@slow
test: {
  input: read("aoc://2022/1")
  part_one: 71300
  part_two: 209691
}
```

**Implementation**:
- Parser recognizes `@` followed by identifier before sections
- Runner tracks attribute on test sections
- Default: skip `@slow` tests
- CLI flag `-s` or `--slow` includes slow tests

### 16.3 Tests

```rust
#[test]
fn runner_solution_execution() { ... }
#[test]
fn runner_test_sections() { ... }
#[test]
fn runner_slow_test_attribute() { ... }
#[test]
fn runner_script_mode() { ... }
#[test]
fn runner_duplicate_section_error() { ... }
```

### Release Gate 16

- [ ] Solutions execute with input binding
- [ ] Tests run against expected values
- [ ] **@slow attribute** skips tests by default
- [ ] **-s/--slow flag** includes slow tests
- [ ] Timing information is collected
- [ ] Script mode works
- [ ] Duplicate sections produce errors
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 17: Error Handling & Reporting

**Goal**: Comprehensive error handling with source locations.

**LANG.txt Reference**: §15.5 Error Handling

### 17.1 Error Types

```rust
pub enum SantaError {
    LexError { message: String, line: u32, column: u32 },
    ParseError { message: String, span: Span },
    CompileError { message: String, span: Span },
    RuntimeError { message: String, trace: Vec<StackFrame> },
}
```

### Release Gate 17

- [ ] All error types have accurate source locations
- [ ] Stack traces show call chain
- [ ] Error messages are clear and helpful
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 18: CLI Runtime

**Goal**: Build the command-line interface.

**LANG.txt Reference**: §13 External Functions

### 18.1 Commands

```
dasher <SCRIPT>           Run solution file
dasher -t <SCRIPT>        Run tests (exclude @slow)
dasher -t -s <SCRIPT>     Run tests (include @slow)
```

**Note**: REPL is out of scope for AOT compiler. Use santa-lang-rs for REPL functionality.

### 18.2 External Functions

- `puts(..values)` - Print to stdout
- `read(path)` - Read file contents (supports file://, https://, aoc://)
- `env()` - Print environment (for debugging)

### 18.3 AOC Input Fetching

The `read("aoc://year/day")` scheme fetches puzzle input from adventofcode.com:

**Session Cookie**:
```
# Environment variable (preferred)
export AOC_SESSION=your_session_cookie

# Or config file
~/.config/dasher/session.txt
```

**Caching**:
- Inputs cached at `~/.cache/dasher/aoc/YEAR/DAY.txt`
- Cache checked before network request
- Cache never expires (puzzle inputs are immutable)

**Error Handling**:
- Missing session cookie → RuntimeErr with helpful message
- Network error → RuntimeErr
- 404 (future puzzle) → RuntimeErr
- Invalid year/day format → RuntimeErr

### 18.4 Exit Codes

- 0: Success
- 1: Argument error
- 2: Runtime error
- 3: Test failure

### 18.5 Tests

```rust
#[test]
fn cli_run_solution() { ... }
#[test]
fn cli_run_tests() { ... }
#[test]
fn cli_slow_flag() { ... }
#[test]
fn read_local_file() { ... }
#[test]
fn read_aoc_cached() { ... }
#[test]
fn read_missing_session_error() { ... }
```

### Release Gate 18

- [ ] All CLI commands work
- [ ] Output format matches other implementations
- [ ] **AoC input fetching** with session cookie
- [ ] **Input caching** works correctly
- [ ] **Missing session** produces helpful error
- [ ] Exit codes are correct
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 19: Benchmarks & Optimization

**Goal**: Performance validation and optimization.

**LANG.txt Reference**: §15.4 Performance Characteristics

### 19.1 LLVM Optimization Passes

Enable standard optimization passes:
- O2 for development
- O3 for release builds

### 19.2 Benchmark Categories

- Lexer, Parser, Codegen time
- Execution time vs Blitzen/Comet
- Memory usage

### Release Gate 19

- [ ] Performance meets or exceeds bytecode VM
- [ ] No performance regressions in CI
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 20: Integration & Polish

**Goal**: Final integration and verification.

**LANG.txt Reference**: Appendix D (Example Programs)

### 20.1 Incremental .santa Test Files

Throughout development, .santa test files are added incrementally to `examples/`:

- **Phases 1-3**: Basic syntax tests (literals, operators, patterns)
- **Phases 4-8**: Runtime tests (collections, closures, control flow)
- **Phases 9-13**: Built-in function tests
- **Phases 14-16**: Advanced features (TCO, pattern matching, AOC runner)

Each phase should add corresponding .santa files that exercise new functionality.

### 20.2 Integration Tests

Run all LANG.txt Appendix D examples:
- Fibonacci, AOC 2022 Day 1, Word Frequency, Prime Numbers, Recursive List Sum

### 20.3 Example Suite Validation

Run all .santa files from examples directory using run-tests.sh.

### 20.4 Final Verification

- [ ] LANG.txt compliance (except `evaluate()` which is out of scope)
- [ ] All 65 implemented built-in functions match Appendix B
- [ ] All integration tests pass
- [ ] All example suite tests pass
- [ ] Documentation complete
- [ ] Known limitations documented
- [ ] Ready for production use

---

## Summary

| Phase | Component            | Key Deliverable             |
| ----- | -------------------- | --------------------------- |
| 1     | Lexer                | Token stream from source    |
| 2     | Parser Expressions   | Expression AST              |
| 3     | Parser Complete      | Full AST with sections      |
| 4     | LLVM Runtime Library | FFI support for compiled code |
| 5     | LLVM Codegen Exprs   | Expression IR generation    |
| 6     | LLVM Codegen Stmts   | Full code generation        |
| 7     | Runtime Operations   | Arithmetic/comparison ops   |
| 8     | Closures             | Captured variables          |
| 9     | Builtins Core        | Type conversion & access    |
| 10    | Builtins Transform   | map/filter/reduce           |
| 11    | Builtins Search      | find/count/sort             |
| 12    | Lazy Sequences       | Infinite sequences          |
| 13    | Builtins Complete    | All remaining               |
| 14    | TCO                  | Tail-call optimization      |
| 15    | Pattern Matching     | Full pattern support        |
| 16    | AOC Runner           | Section execution           |
| 17    | Error Handling       | Rich error reporting        |
| 18    | CLI                  | Command-line interface      |
| 19    | Benchmarks           | Performance validation      |
| 20    | Integration          | Final polish & verification |

Each phase builds on previous phases. Release gates ensure quality before proceeding.
