## santa-lang Implementation

This is **Dasher**, a santa-lang reindeer implementation. santa-lang is a functional programming language designed for solving Advent of Code puzzles. Multiple implementations exist to explore different execution models.

## Project Overview

- **Dasher**: LLVM-based AOT native compiler written in Rust
- Compiles to native executables via LLVM IR generation
- Batteries-included standard library for AoC patterns

## Setup

Requires Rust 1.85+ and **LLVM 18**:

```bash
# Linux
wget https://apt.llvm.org/llvm.sh && chmod +x llvm.sh && sudo ./llvm.sh 18
sudo apt-get install -y libpolly-18-dev
export LLVM_SYS_180_PREFIX=/usr/lib/llvm-18

# macOS
brew install llvm@18
export LLVM_SYS_180_PREFIX=$(brew --prefix llvm@18)

# Build
cargo build --release -p santa-cli
```

## Common Commands

```bash
make help               # Show all targets
make build              # Debug build
make release            # Release build
make fmt                # Format code
make lint               # rustfmt check + clippy -D warnings
make test               # Run all tests
make test/lang          # Lang crate only
make test/runtime       # Runtime crate only
make test/cli           # CLI crate only
make can-release        # Full CI: lint + test
make bench              # Criterion benchmarks
make run FILE=<path>    # Execute script
make test-examples      # Run example AoC solutions
```

## Code Conventions

- **Edition**: Rust 2021
- **Toolchain**: 1.85.0 (rust-toolchain.toml)
- **Formatting**: `max_width = 120` (rustfmt.toml)
- **Linting**: `clippy -D warnings`
- **Testing**: `expect_test` for snapshot testing
- **Structure**: `lang/` (compiler) + `runtime/` (FFI) + `cli/` + `benchmarks/`

## Tests & CI

```bash
cargo test              # All tests
cargo test -p santa-lang        # Lang crate
cargo test -p santa-lang-runtime # Runtime crate
cargo test -p santa-cli         # CLI crate
```

- **CI** (`test.yml`): Installs LLVM 18, runs `make can-release`
- **Build** (`build.yml`): linux-amd64, macos-amd64, macos-arm64, Docker
- Auto-updates `draft-release` branch after tests pass

## PR & Workflow Rules

- **Branches**: `main` for development, `draft-release` auto-updated
- **CI gates**: Must pass lint + test
- **Release**: release-drafter generates notes

## Security & Gotchas

- **LLVM 18 required**: Must set `LLVM_SYS_180_PREFIX` environment variable
- **Runtime embedding**: `lang/build.rs` compresses and embeds libsanta_lang_runtime.a
- **Build order**: Runtime must build before lang (workspace handles this)
- **Release profile**: `lto=true`, `codegen-units=1`, `opt-level=3`, `strip=true`
- **Example tests**: Require release build (`make test-examples` depends on `release`)

## Related Implementations

Other santa-lang reindeer (for cross-reference and consistency checks):

| Codename | Type | Language | Local Path | Repository |
|----------|------|----------|------------|------------|
| **Comet** | Tree-walking interpreter | Rust | `~/Projects/santa-lang-comet` | `github.com/eddmann/santa-lang-comet` |
| **Blitzen** | Bytecode VM | Rust | `~/Projects/santa-lang-blitzen` | `github.com/eddmann/santa-lang-blitzen` |
| **Dasher** | LLVM native compiler | Rust | `~/Projects/santa-lang-dasher` | `github.com/eddmann/santa-lang-dasher` |
| **Donner** | JVM bytecode compiler | Kotlin | `~/Projects/santa-lang-donner` | `github.com/eddmann/santa-lang-donner` |
| **Prancer** | Tree-walking interpreter | TypeScript | `~/Projects/santa-lang-prancer` | `github.com/eddmann/santa-lang-prancer` |

Language specification and documentation: `~/Projects/santa-lang` or `github.com/eddmann/santa-lang`
