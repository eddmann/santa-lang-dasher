# Alignment Plan: santa-lang-dasher → santa-lang-blitzen/comet patterns

## Executive Summary

This plan aligns santa-lang-dasher with the established patterns from:
- **santa-lang-blitzen** (Bytecode VM in Rust)
- **santa-lang-rs** (Tree-walking interpreter in Rust, also known as "Comet")

Both reference projects share nearly identical infrastructure, so we'll consolidate to one consistent pattern.

---

## Current State Analysis

### santa-lang-dasher (Current)

| Aspect | Current State |
|--------|--------------|
| GitHub Workflows | **None** - No `.github/` directory |
| README.md | Detailed but different format |
| CLI Binary | `dasher` (uses clap) |
| CLI Flags | `-t`, `-s`, `-c` only |
| Makefile | **None** |
| Release Process | **None** - No tags, no versioning, no draft-release |
| Docker | **None** |
| rustfmt.toml | **None** |
| rust-toolchain.toml | **None** |
| LICENSE | **None** |

### santa-lang-blitzen/comet (Reference)

| Aspect | Reference Pattern |
|--------|------------------|
| GitHub Workflows | test.yml, build.yml, publish.yml, release-drafter.yml |
| README.md | Consistent format with logo, install options, usage, project structure |
| CLI Binary | `santa-cli` |
| CLI Flags | `-e`, `-t`, `-s`, `-r`, `-f`, `--fmt-write`, `--fmt-check`, `-p`, `-h`, `-v` |
| Makefile | Comprehensive with help, lint, test, bench targets |
| Release Process | draft-release branch, release-drafter, multi-platform builds |
| Docker | GHCR publishing with versioned tags |
| rustfmt.toml | `max_width = 120` (comet) or `edition = 2021` (blitzen) |
| rust-toolchain.toml | Pinned Rust version |
| LICENSE | MIT |

---

## Proposed Changes

### 1. GitHub Workflows (Priority: HIGH)

**Create `.github/` directory with:**

#### `.github/release-drafter.yml`
```yaml
name-template: $NEXT_PATCH_VERSION
tag-template: $NEXT_PATCH_VERSION
commitish: draft-release
template: |
  ## Changes

  $CHANGES
```

#### `.github/workflows/test.yml`
- Trigger on push (except draft-release) and PRs to main
- Run `make can-release` (lint + test)
- On main branch success, force-push to `draft-release` branch

#### `.github/workflows/build.yml`
- Trigger on push to `draft-release`
- Use release-drafter to create/update draft release
- Build CLI for 4 platforms:
  - linux-amd64 (x86_64-unknown-linux-gnu)
  - linux-arm64 (aarch64-unknown-linux-gnu)
  - macos-amd64 (x86_64-apple-darwin)
  - macos-arm64 (aarch64-apple-darwin)
- Build Docker image
- Upload artifacts to release

#### `.github/workflows/publish.yml`
- Trigger on release published
- Push Docker image to GHCR with version tag

**Files to create:**
- `.github/release-drafter.yml`
- `.github/workflows/test.yml`
- `.github/workflows/build.yml`
- `.github/workflows/publish.yml`

---

### 2. CLI API Alignment (Priority: HIGH)

**Current dasher CLI:**
```
dasher <SCRIPT>           Run solution
dasher -t <SCRIPT>        Test mode
dasher -s                 Include slow (with -t)
dasher -c <SCRIPT>        Compile to executable
```

**Aligned CLI (matching santa-cli):**
```
santa-cli <SCRIPT>        Run solution
santa-cli -e <CODE>       Evaluate inline script    [NEW]
santa-cli -t <SCRIPT>     Test mode
santa-cli -s              Include slow (with -t)
santa-cli -r              REPL mode                  [NEW]
santa-cli -p              Profile mode               [NEW - optional]
santa-cli -h              Help
santa-cli -v              Version
<stdin> | santa-cli       Read from stdin            [NEW]
```

**Changes to `cli/src/main.rs`:**
1. Rename binary from `dasher` to `santa-cli`
2. Add `-e/--eval` for inline script evaluation
3. Add `-r/--repl` for REPL mode (with rustyline)
4. Add `-h/--help` and `-v/--version` explicit handling
5. Add stdin support (when not a TTY)
6. Add `-p/--profile` as optional feature (like blitzen)
7. Version output: `"santa-lang Dasher {version}"`

**Changes to `cli/Cargo.toml`:**
```toml
[[bin]]
name = "santa-cli"  # Changed from "dasher"

[dependencies]
atty = "0.2.14"     # Detect TTY for stdin support
rustyline = "15.0"  # REPL support
pprof = { version = "0.14", features = ["flamegraph", "protobuf-codec"], optional = true }

[features]
profile = ["dep:pprof"]
```

---

### 3. Makefile (Priority: HIGH)

**Create `Makefile` with targets matching blitzen/comet:**

```makefile
IMAGE = rust:1.85.0-bullseye
DOCKER = docker run --rm -e CARGO_HOME=/app/.cargo -v $(PWD):/app -w /app

.DEFAULT_GOAL := help

.PHONY: help
help: ## Display this help message
	@awk 'BEGIN {FS = ":.*##"; ...}' $(MAKEFILE_LIST)

##@ Development

.PHONY: build
build: ## Build CLI (debug)
	cargo build -p santa-cli

.PHONY: release
release: ## Build CLI (release)
	cargo build --release -p santa-cli

.PHONY: repl
repl: ## Start interactive REPL
	cargo run -p santa-cli -- -r

.PHONY: run
run: ## Run a script (FILE=path/to/script.santa)
	cargo run -p santa-cli -- $(FILE)

.PHONY: run-test
run-test: ## Run script in test mode
	cargo run -p santa-cli -- -t $(FILE)

##@ Testing/Linting

.PHONY: can-release
can-release: lint test ## Run all CI checks

.PHONY: lint
lint: ## Run rustfmt and clippy
	cargo fmt -- --check
	cargo clippy -- -D warnings

.PHONY: fmt
fmt: ## Format code
	cargo fmt

.PHONY: test
test: ## Run all tests
	cargo test

.PHONY: test-examples
test-examples: ## Run example test suite
	./examples/run-tests.sh

##@ Benchmarking

.PHONY: bench
bench: ## Run Criterion benchmarks
	cargo bench -p santa-lang-benchmarks

##@ Installation

.PHONY: install
install: ## Install to ~/.cargo/bin
	cargo install --path cli

.PHONY: clean
clean: ## Clean build artifacts
	cargo clean
```

---

### 4. README.md Alignment (Priority: MEDIUM)

**Restructure to match blitzen/comet format:**

1. **Header with logo** (centered, link to docs site if exists)
2. **Project name**: "santa-lang Dasher"
3. **One-line description**: "LLVM-based AOT native compiler implementation of santa-lang, written in Rust"
4. **Overview section** with key features list
5. **Installation section**:
   - Docker: `ghcr.io/eddmann/santa-lang-dasher:cli-latest`
   - Release Binaries table (Linux x86_64, Linux ARM64, macOS Intel, macOS ARM)
6. **Usage section** with common commands
7. **Example** showing complete AoC solution
8. **Building section** with `cargo build --release`
9. **Development section** with `make help` reference
10. **Project Structure** diagram
11. **See Also** links to other implementations

---

### 5. Configuration Files (Priority: MEDIUM)

#### `rustfmt.toml` (create)
```toml
max_width = 120
```

#### `rust-toolchain.toml` (create)
```toml
[toolchain]
channel = "1.85.0"
```

#### `LICENSE` (create)
MIT License with copyright to Edd Mann

---

### 6. Cargo.toml Updates (Priority: MEDIUM)

**Root workspace:**
```toml
[workspace.package]
version = "0.1.0"
authors = ["Edd Mann <the@eddmann.com>"]
documentation = "https://eddmann.com/santa-lang/"  # Add if site exists
```

**cli/Cargo.toml:**
```toml
[package]
name = "santa-cli"  # Rename from dasher

[dependencies]
atty = "0.2.14"
rustyline = "15.0"
pprof = { version = "0.14", ..., optional = true }

[dev-dependencies]
assert_cmd = "2.0"
predicates = "3.1"
```

---

### 7. Docker Support (Priority: MEDIUM)

**Create `runtime/cli/build.Dockerfile`** (or `cli/build.Dockerfile`):
```dockerfile
FROM rust:1.85.0-bullseye AS builder
# Install LLVM 18 dependencies
RUN apt-get update && apt-get install -y llvm-18-dev libclang-18-dev
WORKDIR /app
COPY . .
RUN cargo build --release --bin santa-cli

FROM debian:bookworm-slim
COPY --from=builder /app/target/release/santa-cli /usr/local/bin/santa-cli
ENTRYPOINT ["santa-cli"]
```

**Note**: LLVM requirement makes Docker builds more complex than blitzen/comet. May need custom base image with LLVM 18 pre-installed.

---

### 8. Benchmark Infrastructure (Priority: LOW)

**Current state**: Uses Criterion, but less developed than blitzen

**Align with blitzen pattern:**
1. Create `benchmarks/Dockerfile` for reproducible benchmark environment
2. Add `make bench/run` for hyperfine benchmarks
3. Add `make bench/compare V1=ref V2=ref` for version comparison
4. Add benchmark fixtures directory with representative .santa files

---

## Implementation Phases

### Phase 1: Core Infrastructure (Immediate)
1. Create `.github/` directory with all workflows
2. Create `Makefile`
3. Create `rustfmt.toml`, `rust-toolchain.toml`, `LICENSE`

### Phase 2: CLI Alignment
1. Rename binary to `santa-cli`
2. Add `-e`, `-r`, stdin support
3. Add REPL implementation with rustyline
4. Add version output format

### Phase 3: Documentation
1. Restructure README.md
2. Update CLAUDE.md with Makefile commands

### Phase 4: Docker & Release
1. Create Dockerfile
2. Test release workflow locally
3. Push to GitHub and test workflows

---

## File Changes Summary

### Files to Create

| File | Priority | Description |
|------|----------|-------------|
| `.github/release-drafter.yml` | HIGH | Release drafter configuration |
| `.github/workflows/test.yml` | HIGH | CI test workflow |
| `.github/workflows/build.yml` | HIGH | Multi-platform build workflow |
| `.github/workflows/publish.yml` | HIGH | Docker publish workflow |
| `Makefile` | HIGH | Development automation |
| `rustfmt.toml` | MEDIUM | Code formatting config |
| `rust-toolchain.toml` | MEDIUM | Pinned Rust version |
| `LICENSE` | MEDIUM | MIT license |
| `cli/build.Dockerfile` | MEDIUM | Docker build |

### Files to Modify

| File | Priority | Changes |
|------|----------|---------|
| `cli/Cargo.toml` | HIGH | Rename binary, add deps |
| `cli/src/main.rs` | HIGH | Add -e, -r, stdin, REPL |
| `Cargo.toml` | MEDIUM | Add documentation URL |
| `README.md` | MEDIUM | Restructure to match pattern |
| `CLAUDE.md` | LOW | Add Makefile reference |

---

## Risks and Considerations

1. **LLVM Dependency**: Docker builds are more complex than blitzen/comet due to LLVM 18 requirement. May need pre-built LLVM base image or longer build times.

2. **Binary Size**: dasher produces 37MB binaries (embedded runtime). This is larger than blitzen but acceptable for LLVM-based compiler.

3. **Cross-compilation**: ARM64 Linux cross-compilation needs LLVM cross-compilation support, which is more complex than pure Rust projects.

4. **REPL Feasibility**: The LLVM compiler doesn't naturally support incremental compilation like an interpreter. REPL would need to:
   - Compile each line to a separate function
   - Execute via JIT or AOT to temp binary
   - May be complex to implement properly

5. **Format Command**: blitzen/comet have `-f/--fmt` for source formatting. This requires a formatter implementation in the lang crate. Could be deferred.

---

## Priority Recommendations

**Do First (Quick Wins):**
1. Create Makefile (easy, high value)
2. Create rustfmt.toml, rust-toolchain.toml, LICENSE (trivial)
3. Create basic GitHub workflows (test.yml at minimum)

**Do Second (CLI Alignment):**
1. Rename binary to santa-cli
2. Add -e, -h, -v, stdin support
3. REPL can be a placeholder that errors "not yet supported"

**Do Third (Full CI/CD):**
1. Complete build.yml with multi-platform
2. Add Docker support
3. Add publish.yml

**Defer:**
1. REPL implementation (complex for AOT compiler)
2. Format command (needs lang crate changes)
3. Benchmark infrastructure enhancements
