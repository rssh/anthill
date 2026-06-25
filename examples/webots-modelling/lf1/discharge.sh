#!/usr/bin/env bash
# discharge.sh — run every `proof <rule> by z3` block in safety_*.anthill
# through `anthill prove`. Z3 must be on $PATH; without it the prove
# driver reports each obligation as "skipped" rather than failed.
#
# Extra args are forwarded to `anthill prove` (see the `"$@"` below), so the
# proof-cache flags (proposal 025.1 Phase 1) work here unchanged:
#
#   ./discharge.sh                 # normal run: cache miss → solve → write;
#                                  #   a warm second run reports "cache hit".
#   ./discharge.sh --show-cache    # list cached entries + verdicts, run nothing.
#   ./discharge.sh --stats         # print the cache hit/miss/written summary.
#   ./discharge.sh --refresh-cache # re-solve and overwrite (ignore existing hits).
#   ./discharge.sh --no-cache      # bypass the cache entirely (no lookup, no write).
#   ./discharge.sh --gc-cache 30   # drop entries older than 30 days, run nothing.
#   ./discharge.sh --cache-dir DIR # use DIR instead of the XDG default.
#
# Warm-cache CI pattern: commit nothing (the cache lives outside the repo under
# the XDG dir / --cache-dir), but persist that dir across CI runs (a cache key).
# First run populates it (each obligation solved once); subsequent runs are
# all-hits and finish in well under a second. To make staleness loud, run
# `./discharge.sh --refresh-cache` on a schedule (or when Z3 / the stdlib
# version bumps — both are part of the cache key, so a bump invalidates anyway).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"

cd "$REPO_ROOT/rustland"

cargo run --quiet --bin anthill -- prove "$@" "$SCRIPT_DIR"
