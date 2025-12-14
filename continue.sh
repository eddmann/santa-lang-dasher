#!/bin/bash

# continue.sh - Resume Dasher development with Claude
# Usage: ./continue.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Colors
CYAN='\033[0;36m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

echo -e "${CYAN}=== Dasher Development Session ===${NC}"
echo ""

# Find current phase from PLAN.md
COMPLETED_GATES=$(grep -c "^- \[x\]" PLAN.md 2>/dev/null || echo "0")
TOTAL_GATES=$(grep -c "^- \[" PLAN.md 2>/dev/null || echo "0")

echo -e "${GREEN}Progress:${NC} $COMPLETED_GATES / $TOTAL_GATES release gates completed"
echo ""

# Run tests if cargo project exists
if [ -f "Cargo.toml" ]; then
    echo -e "${YELLOW}Running tests...${NC}"
    if cargo test --quiet 2>/dev/null; then
        echo -e "${GREEN}✓ All tests pass${NC}"
    else
        echo -e "${YELLOW}⚠ Some tests failing - Claude should address this first${NC}"
    fi
    echo ""
fi

# Build the prompt for Claude
PROMPT="Continue developing Dasher, an LLVM-backed native compiler for santa-lang.

## ARCHITECTURE (MANDATORY)
This is an LLVM COMPILER using inkwell - NOT an interpreter or VM!
- Codegen generates LLVM IR
- Runtime module provides FFI functions called from compiled code
- ❌ NO tree-walking interpreter (do not eval AST directly)
- ❌ NO bytecode VM

## CRITICAL REQUIREMENTS
1. **LLVM BACKEND** - Use inkwell to generate LLVM IR, not interpretation
2. **TDD IS MANDATORY** - Write failing test FIRST, then code to pass it
3. **Classical testing school** - Test real objects, state-based assertions, no mocking internals
4. **LANG.txt is source of truth** - All behavior must match the specification

## WORKFLOW
1. Read PLAN.md and CLAUDE.md to understand architecture and TDD requirements
2. Find current incomplete phase from release gate checkboxes
3. For each feature:
   - RED: Write a failing test first (based on LANG.txt)
   - GREEN: Write minimum code to pass
   - REFACTOR: Clean up while keeping tests green
4. Run \`cargo test\` frequently
5. Run \`cargo clippy\` before marking gates complete
6. Update PLAN.md release gates as you complete them
7. Commit after completing a phase

Current status: ~$COMPLETED_GATES/$TOTAL_GATES release gates completed.

Begin by reading PLAN.md and CLAUDE.md, then identify the next test to write."

echo -e "${CYAN}Starting Claude Code session...${NC}"
echo ""

# Start Claude with the prompt
claude --dangerously-skip-permissions "$PROMPT"
