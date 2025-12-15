#!/bin/bash

# run-tests.sh - Test runner for all .santa example files
# Usage: ./run-tests.sh [-i pattern] [-e pattern] [-t timeout]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

# Settings
INCLUDE_PATTERN=""
TIMEOUT=60
declare -a EXCLUDE_PATTERNS=()

usage() {
    echo "Usage: $0 [OPTIONS]"
    echo ""
    echo "Options:"
    echo "  -i, --include PATTERN   Only run tests matching PATTERN"
    echo "  -e, --exclude PATTERN   Skip tests matching PATTERN"
    echo "  -t, --timeout SECONDS   Timeout per test (default: 60)"
    echo "  -h, --help              Show this help"
    echo ""
    echo "Examples:"
    echo "  $0                        # Run all tests"
    echo "  $0 -i 'aoc2022_*'         # Run only 2022 tests"
    echo "  $0 -e 'aoc2018_*'         # Skip 2018 tests"
    exit 0
}

while [[ $# -gt 0 ]]; do
    case $1 in
        -i|--include) INCLUDE_PATTERN="$2"; shift 2 ;;
        -e|--exclude) EXCLUDE_PATTERNS+=("$2"); shift 2 ;;
        -t|--timeout) TIMEOUT="$2"; shift 2 ;;
        -h|--help) usage ;;
        *) echo "Unknown: $1"; usage ;;
    esac
done

is_excluded() {
    local name="$1"
    for pattern in "${EXCLUDE_PATTERNS[@]}"; do
        [[ "$name" == $pattern ]] && return 0
    done
    return 1
}

# Results tracking
declare -a PASSED=() FAILED=() SKIPPED=() ERRORS=() TIMEOUTS=()

# Build CLI
echo -e "${BOLD}${CYAN}Building dasher...${NC}"
cargo build --release -p dasher --manifest-path "$PROJECT_ROOT/Cargo.toml" 2>/dev/null || {
    echo -e "${RED}Build failed${NC}"; exit 1
}

CLI="$PROJECT_ROOT/target/release/dasher"

# Check if CLI exists
if [ ! -f "$CLI" ]; then
    echo -e "${RED}CLI binary not found at $CLI${NC}"
    exit 1
fi

# Check if there are any .santa files
shopt -s nullglob
SANTA_FILES=("$SCRIPT_DIR"/*.santa)
shopt -u nullglob

if [ ${#SANTA_FILES[@]} -eq 0 ]; then
    echo -e "${YELLOW}No .santa files found in $SCRIPT_DIR${NC}"
    exit 0
fi

# Run tests
for file in "${SANTA_FILES[@]}"; do
    name=$(basename "$file" .santa)

    # Filter
    [[ -n "$INCLUDE_PATTERN" && "$name" != $INCLUDE_PATTERN ]] && continue
    is_excluded "$name" && { SKIPPED+=("$name"); continue; }

    printf "%-40s" "$name"

    # Run with timeout
    if timeout "$TIMEOUT" "$CLI" -t "$file" >/dev/null 2>&1; then
        echo -e "${GREEN}PASS${NC}"
        PASSED+=("$name")
    else
        code=$?
        case $code in
            124) echo -e "${YELLOW}TIMEOUT${NC}"; TIMEOUTS+=("$name") ;;
            3)   echo -e "${RED}FAIL${NC}"; FAILED+=("$name") ;;
            *)   echo -e "${RED}ERROR${NC}"; ERRORS+=("$name") ;;
        esac
    fi
done

# Summary
echo ""
echo -e "${BOLD}Results:${NC}"
echo -e "  ${GREEN}Passed:${NC}  ${#PASSED[@]}"
echo -e "  ${RED}Failed:${NC}  ${#FAILED[@]}"
echo -e "  ${YELLOW}Timeout:${NC} ${#TIMEOUTS[@]}"
echo -e "  ${RED}Errors:${NC}  ${#ERRORS[@]}"
echo -e "  Skipped: ${#SKIPPED[@]}"

# Show failures
if [ ${#FAILED[@]} -gt 0 ]; then
    echo ""
    echo -e "${RED}Failed tests:${NC}"
    for name in "${FAILED[@]}"; do
        echo "  - $name"
    done
fi

if [ ${#ERRORS[@]} -gt 0 ]; then
    echo ""
    echo -e "${RED}Error tests:${NC}"
    for name in "${ERRORS[@]}"; do
        echo "  - $name"
    done
fi

# Exit code
[[ ${#FAILED[@]} -eq 0 && ${#ERRORS[@]} -eq 0 && ${#TIMEOUTS[@]} -eq 0 ]] && exit 0 || exit 1
