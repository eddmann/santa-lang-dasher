.DEFAULT_GOAL := help

.PHONY: help
help: ## Display this help message
	@awk 'BEGIN {FS = ":.*##"; printf "\nUsage:\n  make \033[36m<target>\033[0m\n"} /^[a-zA-Z\/_%-]+:.*?##/ { printf "  \033[36m%-20s\033[0m %s\n", $$1, $$2 } /^##@/ { printf "\n\033[1m%s\033[0m\n", substr($$0, 5) } ' $(MAKEFILE_LIST)

##@ Development

.PHONY: build
build: ## Build CLI (debug)
	cargo build -p cli

.PHONY: release
release: ## Build CLI (release)
	cargo build --release -p cli

.PHONY: run
run: ## Run a script (FILE=path/to/script.santa)
	cargo run -p cli -- $(FILE)

.PHONY: run-test
run-test: ## Run script in test mode (FILE=path/to/script.santa)
	cargo run -p cli -- -t $(FILE)

##@ Testing/Linting

.PHONY: can-release
can-release: lint test ## Run all CI checks (lint + test)

.PHONY: lint
lint: ## Run rustfmt and clippy checks
	cargo fmt -- --check
	cargo build -p runtime
	cargo clippy -- -D warnings

.PHONY: fmt
fmt: ## Format code
	cargo fmt

.PHONY: test
test: ## Run all tests
	cargo test

.PHONY: test/lang
test/lang: ## Test lang crate only
	cargo test -p lang

.PHONY: test/runtime
test/runtime: ## Test runtime crate only
	cargo test -p runtime

.PHONY: test/cli
test/cli: ## Test CLI only
	cargo test -p cli

##@ Benchmarking

.PHONY: bench
bench: ## Run Criterion benchmarks
	cargo bench -p lang-benchmarks