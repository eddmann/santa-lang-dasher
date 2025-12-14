# Dasher: Santa-Lang LLVM Implementation Plan

An LLVM-backed native AOT compiler implementation of santa-lang.

**Note**: `evaluate()` is out of scope for Dasher due to the complexity of runtime code evaluation in an AOT-compiled system. This is a known limitation.

## Architecture (MANDATORY)

**This is a native LLVM compiler, NOT an interpreter or bytecode VM.**

```
Source → Lexer → Parser → Type Inference → Codegen → LLVM IR → Native Code
                                ↓               ↓
                         Typed AST      Runtime Library (FFI)
                                        (for Unknown types only)
```

- **Type Inference** analyzes AST and annotates expressions with inferred types
- **Codegen** produces LLVM IR using the `inkwell` crate
  - **Known types** → Native LLVM instructions (fast path)
  - **Unknown types** → Runtime library calls (dynamic fallback)
- **Runtime library** provides `extern "C"` FFI functions for dynamic dispatch
- **Final output** is AOT-compiled native machine code (executables)
- **Error handling** uses return value + flag pattern for graceful error propagation

### Performance Model

Type inference enables **specialization** - generating optimized native code when types are known at compile time:

| Operation | Unknown Types | Known Types (Int + Int) |
|-----------|---------------|------------------------|
| `a + b` | `call @rt_add` (type check + dispatch) | `add i64` (native CPU instruction) |
| `a < b` | `call @rt_lt` (type check + dispatch) | `icmp slt` (native comparison) |
| `list[i]` | `call @rt_index` | `call @rt_list_get_int` (skip type check) |

**Expected speedup**: 5-20x for numeric-heavy AOC code where types can be inferred.

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
| §3 Type System           | All 10 value types, hashability             | Phases 4, 5        |
| §4 Operators             | Arithmetic, comparison, logical, precedence | Phases 2, 6, 8     |
| §5 Variables & Bindings  | let, mut, destructuring, shadowing          | Phases 3, 7        |
| §6 Expressions           | Literals, blocks, calls, infix, pipeline    | Phase 2            |
| §7 Control Flow          | if, if-let, match, return, break            | Phases 3, 7        |
| §8 Functions             | Lambdas, closures, partial, TCO, memoize    | Phases 2, 6, 9, 15 |
| §9 Pattern Matching      | All pattern types, guards                   | Phases 3, 16       |
| §10 Collections          | List, Set, Dict, Range, LazySeq             | Phases 5, 13       |
| §11 Built-in Functions   | All 66 functions                            | Phases 10-14       |
| §12 AOC Runner           | Sections, tests, script mode                | Phase 17           |
| §13 External Functions   | read, puts, env                             | Phase 19           |
| §14 Semantics            | Truthiness, precedence, scoping             | Phases 5, 8        |
| §15 Implementation Notes | Error handling, TCO requirements            | Phases 15, 18      |
| Appendix A               | Grammar (EBNF)                              | Phases 1-3         |
| Appendix B               | Built-in function reference                 | Phases 10-14       |
| Appendix C               | Operator precedence table                   | Phase 2            |
| Appendix D               | Example programs (integration tests)        | Phase 21           |

**Note**: Phase 4 is the new Type System & Inference phase. All subsequent phases are renumbered (+1).

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
│       ├── types/                 # NEW: Type inference system
│       │   ├── mod.rs
│       │   ├── ty.rs              # Type representation
│       │   ├── infer.rs           # Inference algorithm
│       │   ├── builtins.rs        # Built-in function signatures
│       │   ├── unify.rs           # Type unification
│       │   └── tests.rs
│       ├── codegen/
│       │   ├── mod.rs
│       │   ├── context.rs         # LLVM context/module management
│       │   ├── compiler.rs        # Typed AST to LLVM IR
│       │   ├── specialize.rs      # Type-specialized code generation
│       │   └── tests.rs
│       ├── runtime/
│       │   ├── mod.rs
│       │   ├── value.rs           # Runtime value operations
│       │   ├── collections.rs     # List, Set, Dict, Range
│       │   ├── builtins.rs        # Built-in function implementations
│       │   └── refcount.rs        # Reference counting
│       └── runner/
│           ├── mod.rs
│           └── tests.rs
├── cli/
│   ├── Cargo.toml
│   └── src/
│       ├── main.rs
│       └── external.rs
├── examples/
│   ├── *.santa                # AOC solution files
│   └── run-tests.sh           # Test runner script
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

- [x] All token types from LANG.txt Section 2 are lexed correctly
- [x] Error positions (line:column) are accurate
- [x] All expect_test snapshots pass
- [x] `cargo clippy` clean

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

- [x] All expression forms from LANG.txt parse correctly
- [x] Operator precedence matches santa-lang-rs exactly
- [x] Partial application (`_ + 1`) parses Placeholder correctly
- [ ] Trailing lambda syntax is recognized (deferred to Phase 3)
- [x] All expect_test snapshots pass
- [x] `cargo clippy` clean

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

- [x] All statement forms parse correctly
- [x] Destructuring patterns work (including nested, rest)
- [x] Match expressions with guards parse correctly
- [x] AOC sections (`input:`, `part_one:`, `part_two:`, `test:`) parse
- [x] Trailing lambda syntax works
- [x] **Empty `{}` disambiguates correctly** (Set vs Block)
- [x] **Dict shorthand** parses correctly
- [x] All expect_test snapshots pass
- [x] `cargo clippy` clean

---

## Phase 4: Type System & Inference

**Goal**: Implement type inference to enable code specialization in later phases.

**LANG.txt Reference**: §3 Type System (inferring from values), §4 Operators (type rules), §11 Built-in Functions (signatures)

### 4.1 Type Representation

```rust
/// Compile-time type information for specialization
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    // Primitive types
    Int,
    Decimal,
    String,
    Bool,
    Nil,

    // Collection types (with element/key-value types)
    List(Box<Type>),
    Set(Box<Type>),
    Dict(Box<Type>, Box<Type>),  // key type, value type
    LazySequence(Box<Type>),     // element type

    // Function type
    Function {
        params: Vec<Type>,
        ret: Box<Type>,
    },

    // Inference helpers
    Unknown,           // Cannot determine - fall back to runtime dispatch
    TypeVar(u32),      // Unification variable (for polymorphic functions)
    Never,             // Bottom type (return, break - doesn't produce value)
}

impl Type {
    /// Check if this type is fully known (no Unknown or TypeVar)
    pub fn is_concrete(&self) -> bool { ... }

    /// Check if specialization is worthwhile for this type
    pub fn is_specializable(&self) -> bool {
        matches!(self, Type::Int | Type::Decimal | Type::Bool)
    }
}
```

### 4.2 Typed AST

The inference pass annotates the AST with types:

```rust
/// Expression with inferred type
#[derive(Debug)]
pub struct TypedExpr {
    pub expr: Expr,
    pub ty: Type,
    pub span: Span,
}

/// Statement with type information
#[derive(Debug)]
pub struct TypedStmt {
    pub stmt: Stmt,
    pub ty: Type,  // Type of expression statements, or Nil for let/return
    pub span: Span,
}

/// Typed program ready for codegen
#[derive(Debug)]
pub struct TypedProgram {
    pub statements: Vec<TypedStmt>,
    pub sections: Vec<TypedSection>,
}
```

### 4.3 Built-in Function Signatures

All 65 built-in functions have type signatures (excluding `evaluate`):

```rust
/// Type signature for a built-in function
pub struct BuiltinSignature {
    pub name: &'static str,
    pub params: Vec<ParamType>,
    pub ret: fn(&[Type]) -> Type,  // Return type may depend on input types
}

pub enum ParamType {
    Concrete(Type),
    Generic(u32),              // Type variable index
    Collection(u32),           // Any collection with element type var
    Predicate(u32),            // (T) -> Bool
    Mapper(u32, u32),          // (T) -> U
    Reducer(u32, u32),         // (T, U) -> T
}

/// Built-in signature database
pub fn builtin_signatures() -> HashMap<&'static str, BuiltinSignature> {
    hashmap! {
        // Type conversion - monomorphic
        "int" => sig!((Unknown) -> Int),
        "ints" => sig!((String) -> List<Int>),

        // Collection access - polymorphic
        "size" => sig!(<T>(Collection<T>) -> Int),
        "first" => sig!(<T>(Collection<T>) -> T),
        "rest" => sig!(<T>(Collection<T>) -> Collection<T>),
        "get" => sig!(<T>(Int, Collection<T>) -> T),

        // Transformations - higher-order polymorphic
        "map" => sig!(<T, U>((T) -> U, Collection<T>) -> Collection<U>),
        "filter" => sig!(<T>((T) -> Bool, Collection<T>) -> Collection<T>),
        "fold" => sig!(<T, U>(T, (T, U) -> T, Collection<U>) -> T),
        "reduce" => sig!(<T>((T, T) -> T, Collection<T>) -> T),

        // Numeric - monomorphic
        "abs" => sig!((Numeric) -> Numeric),  // Preserves Int/Decimal
        "sum" => sig!(<T: Numeric>(Collection<T>) -> T),

        // String
        "lines" => sig!((String) -> List<String>),
        "split" => sig!((String, String) -> List<String>),
        "md5" => sig!((String) -> String),

        // ... all 65 functions
    }
}
```

### 4.4 Type Inference Algorithm

Forward-propagating inference with local unification:

```rust
pub struct TypeInference {
    /// Type environment: variable name -> type
    env: HashMap<String, Type>,

    /// Current type variable counter
    next_type_var: u32,

    /// Substitutions from unification
    substitutions: HashMap<u32, Type>,
}

impl TypeInference {
    pub fn infer_program(&mut self, program: &Program) -> Result<TypedProgram, TypeError> {
        // 1. Collect top-level function definitions (for mutual recursion)
        // 2. Infer types for each statement
        // 3. Infer types for each section
    }

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<TypedExpr, TypeError> {
        let (typed_expr, ty) = match expr {
            // Literals have known types
            Expr::Integer(_) => (expr.clone(), Type::Int),
            Expr::Decimal(_) => (expr.clone(), Type::Decimal),
            Expr::String(_) => (expr.clone(), Type::String),
            Expr::Boolean(_) => (expr.clone(), Type::Bool),
            Expr::Nil => (expr.clone(), Type::Nil),

            // Variables look up the environment
            Expr::Identifier(name) => {
                let ty = self.env.get(name).cloned().unwrap_or(Type::Unknown);
                (expr.clone(), ty)
            }

            // Operators apply type rules
            Expr::Infix { left, op, right } => {
                let left_typed = self.infer_expr(left)?;
                let right_typed = self.infer_expr(right)?;
                let result_ty = self.infer_binary_op(op, &left_typed.ty, &right_typed.ty);
                // ...
            }

            // Function calls use signature database
            Expr::Call { function, args } => {
                self.infer_call(function, args)?
            }

            // Collections infer element types
            Expr::List(elements) => {
                let elem_ty = self.unify_all(elements)?;
                (expr.clone(), Type::List(Box::new(elem_ty)))
            }

            // If expressions unify branch types
            Expr::If { condition, then_branch, else_branch } => {
                let then_ty = self.infer_expr(then_branch)?.ty;
                let else_ty = else_branch
                    .map(|e| self.infer_expr(e))
                    .transpose()?
                    .map(|t| t.ty)
                    .unwrap_or(Type::Nil);
                let result_ty = self.unify(&then_ty, &else_ty)?;
                // ...
            }

            // Unknown falls back to runtime
            _ => (expr.clone(), Type::Unknown),
        };

        Ok(TypedExpr { expr: typed_expr, ty, span: expr.span })
    }
}
```

### 4.5 Binary Operation Type Rules

```rust
impl TypeInference {
    fn infer_binary_op(&self, op: &InfixOp, left: &Type, right: &Type) -> Type {
        match (op, left, right) {
            // Arithmetic: same-type operands
            (Add | Sub | Mul, Type::Int, Type::Int) => Type::Int,
            (Add | Sub | Mul, Type::Decimal, Type::Decimal) => Type::Decimal,
            (Div, Type::Int, Type::Int) => Type::Int,  // Integer division
            (Div, Type::Decimal, Type::Decimal) => Type::Decimal,
            (Mod, Type::Int, Type::Int) => Type::Int,

            // Mixed numeric: per LANG.txt §4.1, left operand determines type
            (Add | Sub | Mul | Div, Type::Int, Type::Decimal) => Type::Int,
            (Add | Sub | Mul | Div, Type::Decimal, Type::Int) => Type::Decimal,

            // String concatenation
            (Add, Type::String, _) => Type::String,

            // Comparison: returns Bool
            (Eq | NotEq | Lt | Le | Gt | Ge, _, _) => Type::Bool,

            // Logical: requires Bool, returns Bool
            (And | Or, Type::Bool, Type::Bool) => Type::Bool,

            // Collection operations
            (Add, Type::List(a), Type::List(b)) if a == b => Type::List(a.clone()),
            (Add, Type::Set(a), Type::Set(b)) if a == b => Type::Set(a.clone()),
            (Add, Type::Dict(k1, v1), Type::Dict(k2, v2)) if k1 == k2 && v1 == v2 =>
                Type::Dict(k1.clone(), v1.clone()),

            // Range operators
            (Range | RangeInclusive, Type::Int, Type::Int) => Type::LazySequence(Box::new(Type::Int)),

            // Unknown operands: fall back to runtime
            _ => Type::Unknown,
        }
    }
}
```

### 4.6 Unification

Simple unification for matching types:

```rust
impl TypeInference {
    /// Attempt to unify two types, returning the more specific one
    fn unify(&mut self, a: &Type, b: &Type) -> Result<Type, TypeError> {
        match (a, b) {
            // Same concrete types unify
            (Type::Int, Type::Int) => Ok(Type::Int),
            (Type::String, Type::String) => Ok(Type::String),
            // ...

            // TypeVar unifies with anything, records substitution
            (Type::TypeVar(id), other) | (other, Type::TypeVar(id)) => {
                self.substitutions.insert(*id, other.clone());
                Ok(other.clone())
            }

            // Unknown unifies with anything, result is Unknown
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(Type::Unknown),

            // Collection types unify element types
            (Type::List(a), Type::List(b)) => {
                let elem = self.unify(a, b)?;
                Ok(Type::List(Box::new(elem)))
            }

            // Incompatible types
            _ => Err(TypeError::Mismatch { expected: a.clone(), found: b.clone() }),
        }
    }

    /// Unify a list of expressions, returning common element type
    fn unify_all(&mut self, exprs: &[Expr]) -> Result<Type, TypeError> {
        if exprs.is_empty() {
            return Ok(Type::Unknown);  // Empty collection: unknown element type
        }

        let first = self.infer_expr(&exprs[0])?.ty;
        exprs[1..].iter().try_fold(first, |acc, e| {
            let ty = self.infer_expr(e)?.ty;
            self.unify(&acc, &ty)
        })
    }
}
```

### 4.7 Closure Type Inference

Closures infer parameter types from usage context:

```rust
impl TypeInference {
    fn infer_closure(&mut self, params: &[Param], body: &Expr, expected: Option<&Type>)
        -> Result<(Type, TypedExpr), TypeError>
    {
        // If we have an expected type (e.g., from map's signature), use it
        let param_types: Vec<Type> = if let Some(Type::Function { params: expected_params, .. }) = expected {
            expected_params.clone()
        } else {
            // Otherwise, create fresh type variables
            params.iter().map(|_| {
                let var = self.fresh_type_var();
                Type::TypeVar(var)
            }).collect()
        };

        // Bind parameters in environment
        let old_env = self.env.clone();
        for (param, ty) in params.iter().zip(&param_types) {
            self.env.insert(param.name.clone(), ty.clone());
        }

        // Infer body type
        let body_typed = self.infer_expr(body)?;

        // Restore environment
        self.env = old_env;

        // Apply substitutions to get final parameter types
        let final_params: Vec<Type> = param_types.iter()
            .map(|t| self.apply_substitutions(t))
            .collect();

        let fn_type = Type::Function {
            params: final_params,
            ret: Box::new(body_typed.ty.clone()),
        };

        Ok((fn_type, body_typed))
    }
}
```

### 4.8 Inference for Common AOC Patterns

Examples of what the inference system handles:

```santa
// EXAMPLE 1: Numeric pipeline - fully inferred
let input = "1\n2\n3";           // String
let nums = lines(input)          // List<String>
    |> map(int, _);              // List<Int>
let total = fold(0, +, nums);    // Int

// Type flow:
//   lines: (String) -> List<String>
//   map(int, _): int: (String) -> Int, so map produces List<Int>
//   fold(0, +, _): initial is Int, so result is Int

// EXAMPLE 2: Closure type propagation
let doubled = map(|x| x * 2, [1, 2, 3]);
// [1, 2, 3] is List<Int>
// map's signature: ((T) -> U, List<T>) -> List<U>
// So |x| has type (Int) -> ???
// x * 2: Int * Int = Int
// Therefore doubled: List<Int>

// EXAMPLE 3: Falls back to Unknown
let data = read("input.txt");    // String (from external)
let parsed = parse(data);        // Unknown (user-defined function)
let result = parsed + 1;         // Unknown (can't specialize)
```

### 4.9 Type Errors vs Runtime Fallback

The inference system distinguishes between:

1. **Type errors** (compile-time): Known-incompatible types
   ```santa
   1 + "hello"  // Error: Int + String not allowed (String + X is ok, not X + String)
   ```

2. **Unknown types** (runtime fallback): Can't determine, defer to runtime
   ```santa
   let x = get_value();  // Unknown
   x + 1                 // Generates: call @rt_add (runtime will check)
   ```

```rust
pub enum TypeError {
    Mismatch { expected: Type, found: Type, span: Span },
    ArityMismatch { expected: usize, found: usize, span: Span },
    NotCallable { ty: Type, span: Span },
    // Note: Unknown is NOT an error - it's a valid inference result
}
```

### 4.10 Tests

```rust
#[test]
fn infer_integer_literal() {
    assert_infers("42", Type::Int);
}

#[test]
fn infer_binary_arithmetic() {
    assert_infers("1 + 2", Type::Int);
    assert_infers("1.0 + 2.0", Type::Decimal);
    assert_infers("1 + 2.0", Type::Int);  // Left operand wins
}

#[test]
fn infer_list_literal() {
    assert_infers("[1, 2, 3]", Type::List(Box::new(Type::Int)));
    assert_infers("[]", Type::List(Box::new(Type::Unknown)));
}

#[test]
fn infer_builtin_call() {
    assert_infers("ints(\"1 2 3\")", Type::List(Box::new(Type::Int)));
    assert_infers("size([1, 2, 3])", Type::Int);
}

#[test]
fn infer_map_with_closure() {
    assert_infers("map(|x| x * 2, [1, 2, 3])", Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_fold() {
    assert_infers("fold(0, +, [1, 2, 3])", Type::Int);
}

#[test]
fn infer_pipeline() {
    let code = r#"
        "1\n2\n3"
        |> lines
        |> map(int, _)
        |> fold(0, +, _)
    "#;
    assert_infers(code, Type::Int);
}

#[test]
fn infer_unknown_fallback() {
    // User-defined function - can't know return type
    assert_infers("unknown_fn(42)", Type::Unknown);
}

#[test]
fn infer_if_unifies_branches() {
    assert_infers("if true { 1 } else { 2 }", Type::Int);
    // Mixed branches fall back to Unknown
    assert_infers("if cond { 1 } else { \"x\" }", Type::Unknown);
}

#[test]
fn type_error_incompatible() {
    // Int + String is an error (String + Int would coerce)
    assert_type_error("1 + \"hello\"", TypeError::Mismatch { .. });
}
```

### Release Gate 4

- [x] Type enum represents all santa-lang types
- [x] Literals infer correct concrete types
- [x] Binary operators follow LANG.txt §4.1 type rules
- [ ] Built-in function signatures are defined for all 65 functions (deferred to later phases)
- [x] Collection literals infer element types
- [ ] Closures infer parameter types from context (deferred to Phase 9)
- [ ] Pipeline/composition propagates types correctly (deferred to Phase 6)
- [x] Unknown falls back gracefully (no false errors)
- [x] Type errors caught for known-incompatible operations (via unification)
- [x] All tests pass (79 tests)
- [x] `cargo clippy` clean (one minor unused method warning)

---

## Phase 5: Runtime Support Library

**Goal**: Build the FFI runtime library that LLVM-compiled code calls into.

**This is NOT an interpreter.** These are `extern "C"` functions that get linked with the compiled output. With type inference, many operations bypass the runtime entirely - these functions are only called for `Unknown` typed expressions.

**LANG.txt Reference**: §3 Type System (all types), §3.11 Hashability, §14.1 Truthy/Falsy Values

### 5.1 Value Representation (NaN-boxing)

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

### 5.2 Heap Objects

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

### 5.3 Reference Counting

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

### 5.4 Collection Types (im-rs Persistent)

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

### 5.5 Mutable Captures (Heap-Boxed Cells)

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

### 5.6 String Handling (Grapheme Clusters)

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

### 5.7 Tests

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

### Release Gate 5

- [x] NaN-boxing scheme works for inline integers and decimals
- [ ] Large integers (>51 bits) are boxed correctly (deferred - wraps for now, acceptable for MVP)
- [x] Reference counting increments/decrements correctly
- [ ] Hashable values work correctly in Sets and Dict keys (basic infrastructure done, needs runtime ops in Phase 8)
- [ ] Non-hashable values (functions, dicts) produce RuntimeErr in Sets/Dict keys (deferred to Phase 8)
- [x] Truthiness matches LANG.txt Section 14.1
- [x] Mutable cells work for captured variables
- [x] Grapheme-cluster string indexing works (emoji test)
- [x] All tests pass (101 tests)
- [x] `cargo clippy` clean

---

## Phase 6: LLVM Codegen - Expressions

**Goal**: Generate LLVM IR for expressions, using type information to specialize code paths.

**LANG.txt Reference**: §4 Operators, §4.7 Pipeline, §4.8 Composition, §8.4 Partial Application

### 6.1 LLVM Context Setup

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

### 6.2 Type-Specialized Expression Compilation

The codegen accepts `TypedExpr` from the inference phase and uses type information to generate optimized code:

```rust
impl<'ctx> CodegenContext<'ctx> {
    /// Compile a typed expression, using specialization when types are known
    pub fn compile_expr(&mut self, expr: &TypedExpr) -> Result<BasicValueEnum<'ctx>, CompileError> {
        match &expr.expr {
            Expr::Integer(n) => self.compile_integer(*n),
            Expr::Decimal(f) => self.compile_decimal(*f),
            Expr::String(s) => self.compile_string(s),
            Expr::Boolean(b) => self.compile_boolean(*b),
            Expr::Nil => self.compile_nil(),
            Expr::Infix { left, op, right } => {
                self.compile_binary_typed(left, op, right, &expr.ty)
            }
            Expr::Prefix { op, right } => self.compile_unary(op, right),
            Expr::Call { function, args } => self.compile_call(function, args),
            // ... etc
        }
    }

    fn compile_integer(&mut self, n: i64) -> BasicValueEnum<'ctx> {
        // Create tagged integer value (NaN-boxed)
        let tagged = (n << 3) | 0b001;
        self.context.i64_type().const_int(tagged as u64, false).into()
    }

    /// Type-specialized binary operation compilation
    fn compile_binary_typed(
        &mut self,
        left: &TypedExpr,
        op: &InfixOp,
        right: &TypedExpr,
        result_ty: &Type,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let left_val = self.compile_expr(left)?;
        let right_val = self.compile_expr(right)?;

        // SPECIALIZATION: Use native LLVM ops when types are known
        match (&left.ty, op, &right.ty) {
            // Int + Int → native add (FAST PATH)
            (Type::Int, InfixOp::Add, Type::Int) => {
                let l = self.unbox_int(left_val);
                let r = self.unbox_int(right_val);
                let result = self.builder.build_int_add(l, r, "add");
                Ok(self.box_int(result))
            }

            // Int * Int → native mul (FAST PATH)
            (Type::Int, InfixOp::Mul, Type::Int) => {
                let l = self.unbox_int(left_val);
                let r = self.unbox_int(right_val);
                let result = self.builder.build_int_mul(l, r, "mul");
                Ok(self.box_int(result))
            }

            // Int < Int → native comparison (FAST PATH)
            (Type::Int, InfixOp::Lt, Type::Int) => {
                let l = self.unbox_int(left_val);
                let r = self.unbox_int(right_val);
                let cmp = self.builder.build_int_compare(IntPredicate::SLT, l, r, "lt");
                Ok(self.box_bool(cmp))
            }

            // Decimal + Decimal → native fadd (FAST PATH)
            (Type::Decimal, InfixOp::Add, Type::Decimal) => {
                let l = self.unbox_float(left_val);
                let r = self.unbox_float(right_val);
                let result = self.builder.build_float_add(l, r, "fadd");
                Ok(self.box_float(result))
            }

            // Unknown types → runtime dispatch (SLOW PATH)
            _ => {
                self.builder.build_call(self.rt_add, &[left_val, right_val], "add")
            }
        }
    }
}
```

### 6.3 Unboxing/Boxing Helpers

```rust
impl<'ctx> CodegenContext<'ctx> {
    /// Extract raw i64 from NaN-boxed integer (assumes type is known to be Int)
    fn unbox_int(&self, value: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        // Shift right to remove tag bits
        let val = value.into_int_value();
        self.builder.build_right_shift(val, self.const_i64(3), true, "unbox_int")
    }

    /// Box raw i64 into NaN-boxed integer
    fn box_int(&self, value: IntValue<'ctx>) -> BasicValueEnum<'ctx> {
        // Shift left and add tag
        let shifted = self.builder.build_left_shift(value, self.const_i64(3), "shift");
        let tagged = self.builder.build_or(shifted, self.const_i64(0b001), "tag");
        tagged.into()
    }

    /// Extract f64 from NaN-boxed decimal
    fn unbox_float(&self, value: BasicValueEnum<'ctx>) -> FloatValue<'ctx> {
        // Decimals are stored as actual f64 (non-NaN range)
        self.builder.build_bitcast(value, self.context.f64_type(), "unbox_float")
            .into_float_value()
    }

    /// Box f64 into NaN-boxed decimal
    fn box_float(&self, value: FloatValue<'ctx>) -> BasicValueEnum<'ctx> {
        self.builder.build_bitcast(value, self.context.i64_type(), "box_float")
    }
}
```

### 6.4 Runtime Helpers for Unknown Types

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

### 6.5 Tests

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
#[test]
fn codegen_specialized_int_add() { ... }  // Verify native add used
#[test]
fn codegen_fallback_unknown() { ... }     // Verify runtime called for Unknown
```

### Release Gate 6

- [ ] All expression types compile to correct LLVM IR
- [ ] **Type-specialized paths** generate native LLVM ops (Int+Int → add)
- [ ] **Unknown type paths** correctly call runtime functions
- [ ] Partial application generates correct closure
- [ ] Pipeline operator compiles correctly
- [ ] Generated code links with runtime library
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 7: LLVM Codegen - Statements & Control Flow

**Goal**: Complete code generation with statements and control flow.

**LANG.txt Reference**: §5 Variables & Bindings, §7 Control Flow, §14.6 Scoping Rules

### 7.1 Variable Management

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

### 7.2 Control Flow Compilation

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

### 7.3 Protected Built-in Names

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

### 7.4 Tests

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

### Release Gate 7

- [ ] Variable scoping works correctly
- [ ] Shadowing behaves per LANG.txt
- [ ] **Protected built-in names cannot be shadowed**
- [ ] If expressions generate correct branch structure
- [ ] Match compilation handles all pattern types
- [ ] Guard clauses compile correctly
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 8: Runtime - Core Operations

**Goal**: Implement runtime operations called from generated code.

**LANG.txt Reference**: §4.1 Type Coercion Rules, §4 All Operators, §14.1 Truthy/Falsy

### 8.1 Arithmetic Operations

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

### 8.2 Comparison Operations

```rust
#[no_mangle]
pub extern "C" fn rt_eq(left: Value, right: Value) -> Value { ... }

#[no_mangle]
pub extern "C" fn rt_lt(left: Value, right: Value) -> Value { ... }

#[no_mangle]
pub extern "C" fn rt_le(left: Value, right: Value) -> Value { ... }
```

### 8.3 Division and Modulo Semantics (IMPORTANT)

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

### 8.4 Type Coercion Rules

Per LANG.txt §4.1:
- Integer + Decimal: left operand determines result type
- String + any: right operand coerced to string (when left is String)
- Integer + String: ERROR (not supported)

### 8.5 Comparison Restrictions

Only Integer, Decimal, and String support comparison operators (`<`, `>`, `<=`, `>=`).
Comparing other types (List, Set, Dict, Function, LazySequence) produces RuntimeErr.

### 8.6 Tests

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

### Release Gate 8

- [x] All arithmetic operations work correctly
- [x] **Floored division semantics** match Python (-7/2=-4)
- [x] **Floored modulo semantics** match Python (-7%3=2)
- [x] Type coercion matches LANG.txt Section 4.1
- [ ] Comparison on non-comparable types produces RuntimeErr (deferred to Phase 18 - returns nil for now)
- [ ] Division by zero produces RuntimeErr (deferred to Phase 18 - returns nil for now)
- [x] All tests pass (137 tests)
- [x] `cargo clippy` clean

---

## Phase 9: Closures & Function Calls

**Goal**: Implement closures with captured variables.

**LANG.txt Reference**: §8.3 Closures (including mutable capture example)

### 9.1 Closure Representation

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

### 9.2 Closure Compilation

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

### 9.3 Calling Convention

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

### 9.4 Tests

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

### Release Gate 9

- [ ] Simple closures capture variables correctly
- [ ] Nested closures work
- [ ] Mutable captures update correctly
- [ ] Counter example from LANG.txt works correctly
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 10: Built-in Functions - Core

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

### Release Gate 10

- [ ] All type conversion functions work per spec
- [ ] Collection access handles all types
- [ ] Collection modification is immutable (returns new)
- [ ] Edge cases return nil (not errors) where specified
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 11: Built-in Functions - Transformations

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

### Release Gate 11

- [ ] All transformation functions work on all collection types
- [ ] Dict callbacks handle both (value) and (value, key) arities
- [ ] Reduce on empty collection throws RuntimeErr
- [ ] Fold on empty collection returns initial
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 12: Built-in Functions - Search & Aggregation

**Goal**: Complete search and aggregation functions.

**LANG.txt Reference**: §11.7-11.11, Appendix B

### 11.1 Functions

- `find`, `count`, `sum`, `max`, `min`
- `skip`, `take`, `sort`, `reverse`, `rotate`, `chunk`
- `union`, `intersection`
- `includes?`, `excludes?`, `any?`, `all?`

### Release Gate 12

- [ ] All search functions work correctly
- [ ] max/min handle varargs and single collection
- [ ] sort accepts both boolean and integer comparators
- [ ] Set operations work on mixed collection types
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 13: Lazy Sequences

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

### Release Gate 13

- [ ] Unbounded ranges work with take/find
- [ ] iterate generates correct sequences
- [ ] Lazy map/filter compose correctly
- [ ] break works in reduce/fold/each on infinite sequences
- [ ] combinations generates correct subsets
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 14: Built-in Functions - Remaining

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

### Release Gate 14

- [ ] All string functions work correctly
- [ ] Grapheme-cluster indexing for Unicode strings
- [ ] Regex functions handle errors gracefully
- [ ] All bitwise operations work on integers
- [ ] memoize caches results correctly
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 15: Tail-Call Optimization

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

### Release Gate 15

- [ ] TCO applies to self-recursive tail calls
- [ ] Deep recursion (100k+) works without stack overflow
- [ ] Non-tail recursive calls work normally
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 16: Pattern Matching

**Goal**: Full pattern matching support.

**LANG.txt Reference**: §9 Pattern Matching

### 15.1 Pattern Types

- Wildcard `_`, Identifier, Literal
- List patterns with rest `..`
- Range patterns
- Guards

### 15.2 Compilation Strategy

Generate decision tree for efficient matching.

### Release Gate 16

- [ ] All pattern types match correctly
- [ ] Rest patterns work in any position
- [ ] Nested patterns work
- [ ] Guards evaluate correctly
- [ ] Match returns nil if no arm matches
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 17: AOC Runner

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

### Release Gate 17

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

## Phase 18: Error Handling & Reporting

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

### Release Gate 18

- [ ] All error types have accurate source locations
- [ ] Stack traces show call chain
- [ ] Error messages are clear and helpful
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 19: CLI Runtime

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

### Release Gate 19

- [ ] All CLI commands work
- [ ] Output format matches other implementations
- [ ] **AoC input fetching** with session cookie
- [ ] **Input caching** works correctly
- [ ] **Missing session** produces helpful error
- [ ] Exit codes are correct
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 20: Benchmarks & Optimization

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

### Release Gate 20

- [ ] Performance meets or exceeds bytecode VM
- [ ] No performance regressions in CI
- [ ] All tests pass
- [ ] `cargo clippy` clean

---

## Phase 21: Integration & Polish

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

| Phase | Component            | Key Deliverable                           |
| ----- | -------------------- | ----------------------------------------- |
| 1     | Lexer                | Token stream from source                  |
| 2     | Parser Expressions   | Expression AST                            |
| 3     | Parser Complete      | Full AST with sections                    |
| 4     | **Type Inference**   | **Typed AST for specialization (NEW)**    |
| 5     | Runtime Library      | FFI support for compiled code             |
| 6     | Codegen Expressions  | Type-specialized expression IR            |
| 7     | Codegen Statements   | Full code generation                      |
| 8     | Runtime Operations   | Arithmetic/comparison ops                 |
| 9     | Closures             | Captured variables                        |
| 10    | Builtins Core        | Type conversion & access                  |
| 11    | Builtins Transform   | map/filter/reduce                         |
| 12    | Builtins Search      | find/count/sort                           |
| 13    | Lazy Sequences       | Infinite sequences                        |
| 14    | Builtins Complete    | All remaining                             |
| 15    | TCO                  | Tail-call optimization                    |
| 16    | Pattern Matching     | Full pattern support                      |
| 17    | AOC Runner           | Section execution                         |
| 18    | Error Handling       | Rich error reporting                      |
| 19    | CLI                  | Command-line interface                    |
| 20    | Benchmarks           | Performance validation                    |
| 21    | Integration          | Final polish & verification               |

Each phase builds on previous phases. Release gates ensure quality before proceeding.

### Key Architecture Decision: Type Inference for Specialization

Phase 4 (Type Inference) is the critical addition that enables **native code generation** for operations with known types:

```
Without Type Inference:          With Type Inference:
─────────────────────────        ─────────────────────────
let x = 1 + 2;                   let x = 1 + 2;
  ↓                                ↓
call @rt_add                     add i64 (native!)
  ↓                                ↓
Runtime type check               No runtime overhead
  ↓
Dispatch to int add

Expected: 5-20x speedup for numeric-heavy AOC code
```
