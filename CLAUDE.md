# Dasher Development Guidelines

## Architecture: LLVM Backend (MANDATORY)

**This is an LLVM-based native compiler. NOT a tree-walking interpreter. NOT a bytecode VM.**

```
Source → Lexer → Parser → Codegen → LLVM IR → Native Code
                              ↓
                    Runtime Library (FFI)
```

The architecture is:
1. **Lexer** → Token stream
2. **Parser** → AST
3. **Codegen** → LLVM IR (using `inkwell` crate)
4. **LLVM** → Native machine code (AOT compilation)
5. **Runtime library** → Support functions called from compiled code

### What "Runtime" Means Here

The `runtime/` module contains Rust functions that are **called from LLVM-compiled code** via FFI (`extern "C"`):
- Reference counting (`rt_incref`, `rt_decref`)
- Type-aware operations (`rt_add`, `rt_eq`, `rt_call`, etc.)
- Collection operations on persistent data structures (im-rs)

These are NOT an interpreter. They are support functions linked into the final executable.

### Forbidden Approaches
- ❌ Tree-walking interpreter (eval AST directly)
- ❌ Bytecode VM (compile to custom bytecode, interpret in a loop)
- ❌ Transpilation to another language

### Required Approach
- ✅ Generate LLVM IR using `inkwell`
- ✅ Use LLVM's optimization passes (O2/O3)
- ✅ AOT compile to native machine code (no JIT)

---

## Source of Truth

LANG.txt is the authoritative language specification. All implementation decisions MUST conform to LANG.txt.

## Test-Driven Development (TDD)

**We follow classical TDD (Detroit school) for all code.** This is non-negotiable.

### The TDD Cycle

1. **RED**: Write a failing test FIRST
   - Test describes expected behavior from LANG.txt
   - Run test, verify it fails for the right reason

2. **GREEN**: Write minimum code to pass
   - Only implement what's needed to pass the test
   - No premature optimization or generalization

3. **REFACTOR**: Clean up while green
   - Improve code structure
   - Remove duplication
   - Keep tests passing throughout

### Classical Testing School Principles

- **Test real collaborators**: Use actual Lexer, Parser, Runtime objects together
- **State-based verification**: Assert on outputs, not implementation details
- **Only mock at boundaries**: External I/O (files, network) - nothing else
- **No mocking internal components**: Don't mock Lexer to test Parser
- **Integration-style units**: A "unit" is a behavior, not a class

### Test Structure

```rust
#[test]
fn lexer_tokenizes_integer_literal() {
    // Arrange
    let source = "42";

    // Act
    let tokens = lex(source).unwrap();

    // Assert (state-based, not mocks)
    expect![[r#"[Integer(42)]"#]].assert_eq(&format!("{:?}", tokens));
}
```

### What NOT To Do

- Write code before tests
- Write multiple features before testing
- Mock internal components (Lexer, Parser, Runtime)
- Test implementation details
- Skip refactoring phase

### Testing Layers

1. **Unit tests**: Test individual functions/modules with real dependencies
2. **Integration tests**: Full lexer->parser->codegen->execution pipeline
3. **Example tests**: Run .santa files from examples directory

## Development Workflow

1. **Read PLAN.md** at the start of each session
2. **Identify current phase** from release gate checkboxes
3. **Work on ONE feature at a time** using TDD cycle
4. **Run tests frequently** - `cargo test` after each RED->GREEN->REFACTOR
5. **Update release gates** - check off items as they're completed
6. **Commit after each phase** - with message format: `feat(phase-N): description`

## Phase Completion Checklist

Before marking a phase complete:
- [ ] All features developed using TDD (test first!)
- [ ] All tests pass (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Release gates checked in PLAN.md
- [ ] Commit pushed

## Code Style

- Use `expect_test` for snapshot testing
- Keep functions small and focused
- Document non-obvious behavior with comments
- Follow Rust idioms (Result for errors, Option for optional values)

## Reference Implementation

The santa-lang-comet and santa-lang-blitzen repositories can be referenced for:
- Lexer/parser structure
- Builtin function signatures
- Test patterns
- LANG.txt behavior clarification

Do NOT copy code verbatim - implement from scratch based on LANG.txt.

## Commands

- `cargo build` - Build all crates
- `cargo test` - Run all tests (run frequently!)
- `cargo test -- --nocapture` - Run tests with output
- `cargo clippy` - Lint check
- `./examples/run-tests.sh` - Run example .santa files (after Phase 18)
