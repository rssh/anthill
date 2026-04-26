#!/usr/bin/env bash
# discharge.sh — run every `proof <rule> by z3` block in safety.anthill
# through `anthill prove`. Z3 must be on $PATH; without it the prove
# driver reports each obligation as "skipped" rather than failed.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"

cd "$REPO_ROOT/rustland"

cargo run --quiet --bin anthill -- prove "$@" "$SCRIPT_DIR"
