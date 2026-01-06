<p align="center"><a href="https://eddmann.com/santa-lang/"><img src="./docs/logo.png" alt="santa-lang" width="400px" /></a></p>

# santa-lang Dasher

LLVM-based AOT native compiler implementation of [santa-lang](https://eddmann.com/santa-lang/), written in Rust.

## Overview

santa-lang is a functional, expression-oriented programming language designed for solving Advent of Code puzzles. This implementation compiles to native executables via LLVM, with type inference enabling specialization for native operations.

Key language features:

- First-class functions and closures with tail-call optimization
- Pipeline and composition operators for expressive data flow
- Persistent immutable data structures
- Lazy sequences and infinite ranges
- Pattern matching with guards
- [Rich built-in function library](https://eddmann.com/santa-lang/builtins/)
- AoC runner with automatic input fetching

## Architecture

```
Source Code → Lexer → Parser → Type Inference → Codegen → LLVM → Native Binary
                                                    ↓
                                          Runtime Library (FFI)
```

| Component          | Description                                             |
| ------------------ | ------------------------------------------------------- |
| **Lexer**          | Tokenizes source into keywords, operators, literals     |
| **Parser**         | Builds an Abstract Syntax Tree (AST) using Pratt parser |
| **Type Inference** | Infers and specializes types for native operations      |
| **Codegen**        | Generates LLVM IR using inkwell                         |
| **LLVM**           | Compiles IR to native machine code (AOT)                |
| **Runtime**        | FFI library for type-aware operations and collections   |

For detailed implementation internals, see [ARCHITECTURE.md](docs/ARCHITECTURE.md).

## Installation

### Docker

```bash
docker pull ghcr.io/eddmann/santa-lang-dasher:cli-latest
docker run --rm ghcr.io/eddmann/santa-lang-dasher:cli-latest --help
```

### Release Binaries

Download pre-built binaries from [GitHub Releases](https://github.com/eddmann/santa-lang-dasher/releases):

| Platform              | Artifact                                      |
| --------------------- | --------------------------------------------- |
| Linux (x86_64)        | `santa-lang-dasher-cli-{version}-linux-amd64` |
| Linux (ARM64)         | `santa-lang-dasher-cli-{version}-linux-arm64` |
| macOS (Intel)         | `santa-lang-dasher-cli-{version}-macos-amd64` |
| macOS (Apple Silicon) | `santa-lang-dasher-cli-{version}-macos-arm64` |

## Usage

```bash
# Run a solution
santa-cli solution.santa

# Run tests defined in a solution
santa-cli -t solution.santa

# Include slow tests (marked with @slow)
santa-cli -t -s solution.santa

# Evaluate inline code
santa-cli -e '1 + 2'

# Read from stdin
echo 'puts(42)' | santa-cli

# Compile to standalone executable
santa-cli -c solution.santa
./solution
```

## Example

Here's a complete Advent of Code solution (2015 Day 1):

```santa
input: read("aoc://2015/1")

part_one: {
  input |> fold(0) |floor, direction| {
    if direction == "(" { floor + 1 } else { floor - 1 };
  }
}

part_two: {
  zip(1.., input) |> fold(0) |floor, [index, direction]| {
    let next_floor = if direction == "(" { floor + 1 } else { floor - 1 };
    if next_floor < 0 { break index } else { next_floor };
  }
}

test: {
  input: "()())"
  part_one: -1
  part_two: 5
}
```

Key language features shown:

- **`input:`** / **`part_one:`** / **`part_two:`** - AoC runner sections
- **`|>`** - Pipeline operator (thread value through functions)
- **`fold`** - Reduce with early exit support via `break`
- **`test:`** - Inline test cases with expected values

## Building

Requires Rust 1.85+ and LLVM 18:

```bash
# Build CLI (debug)
make build

# Build CLI (release)
make release

# Run tests
make test

# Run linting
make lint
```

## Development

Run `make help` to see all available targets:

```bash
make help          # Show all targets
make can-release   # Run all CI checks (lint + test)
make lint          # Run rustfmt and clippy checks
make test          # Run all tests
make fmt           # Format code
make bench         # Run Criterion benchmarks
make install       # Install to ~/.cargo/bin
```

## Project Structure

```
├── lang/                  # Core compiler library
│   └── src/
│       ├── lexer/         # Tokenization
│       ├── parser/        # AST construction (Pratt parser)
│       ├── types/         # Type inference
│       ├── codegen/       # LLVM IR generation
│       └── runner/        # AoC solution runner
├── runtime/               # FFI runtime library
│   └── src/
│       ├── value.rs       # NaN-boxed value representation
│       ├── heap.rs        # Heap object types
│       ├── operations.rs  # Type-aware dispatch
│       └── builtins.rs    # 80+ built-in functions
├── cli/                   # Command-line interface
└── benchmarks/            # Performance benchmarks
```

## Other Reindeer

The language has been implemented multiple times to explore different execution models and technologies.

| Codename | Type | Language |
|----------|------|----------|
| [Comet](https://github.com/eddmann/santa-lang-comet) | Tree-walking interpreter | Rust |
| [Blitzen](https://github.com/eddmann/santa-lang-blitzen) | Bytecode VM | Rust |
| [Dasher](https://github.com/eddmann/santa-lang-dasher) | LLVM native compiler | Rust |
| [Donner](https://github.com/eddmann/santa-lang-donner) | JVM bytecode compiler | Kotlin |
| [Vixen](https://github.com/eddmann/santa-lang-vixen) | Embedded bytecode VM | C |
| [Prancer](https://github.com/eddmann/santa-lang-prancer) | Tree-walking interpreter | TypeScript |
