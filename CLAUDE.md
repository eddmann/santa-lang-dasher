# Dasher Development Guidelines

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

The santa-lang-rs and santa-lang-blitzen repositories can be referenced for:
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
