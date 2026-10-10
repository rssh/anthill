#!/usr/bin/env bash
# cargo test with live, monitorable progress.
#
# Cargo block-buffers stdout when not attached to a tty, which hides per-binary
# "Running .../target/debug/deps/foo-<hash>" progress until the run ends. This
# wrapper forks a pty (via `script`) so cargo line-buffers as if interactive,
# prefixes each line with elapsed seconds, and tees to a log under target/.
#
# Usage:
#   rustland/scripts/test.sh                       # everything, --no-fail-fast
#   rustland/scripts/test.sh -p anthill-core       # one crate
#   rustland/scripts/test.sh -p anthill-core --lib # unit tests only
#
# Watch from another shell or via Monitor:
#   tail -f rustland/target/test-run-latest.log
#
# A per-binary hang detector can be layered on top of the log:
#   the last "Running ..." line names the current binary; if no new line for
#   N minutes, that binary is hung.
#
# ── Parallelism: TWO TIERS, both derived from the CPU count ──────────────────
#
# libtest's default `--test-threads` is already `available_parallelism()`, so it
# does scale with the machine. That default is right for a COMPUTE-BOUND test
# and wrong for one that SPAWNS A SUBPROCESS: `anthill-cli` and `anthill-todo`
# tests exec the built CLI (123 `Command::new` sites between them), so N test
# threads means up to 2N runnable processes, and the child is doing the real
# work while its parent thread only waits. On a small box — a WSL VM with 2-4
# cores is the case that motivated this — that overcommit is what falls over.
#
# So the two crates that spawn run at HALF the CPU count and everything else
# runs at the full count. Override either with an env var; set both to 1 to
# serialize entirely.
#
#   ANTHILL_TEST_THREADS      compute-bound crates   (default: CPU count)
#   ANTHILL_CLI_TEST_THREADS  subprocess-spawning    (default: max(1, CPUs/2))
#
# The split costs one extra `cargo test` invocation. Passing an explicit
# selector (`-p`, `--workspace`, …) skips the split entirely and runs exactly
# what was asked, at the tier matching the named crates.
#
# ── Two builds: the gate's is optimized, the edit loop's is not ──────────────
#
# A test that loads the stdlib pays for the load, anthill-core's suites alone
# execute ~9 300 such loads, and the load is anthill-core code. MEASURED
# 2026-10-06 on a 6-core laptop (WI-20261006-ZVV24;
# docs/design/test-infrastructure.md §1.1, §2.5): one load is 2.1 s at
# opt-level 0 and 0.31 s with anthill-core at 2, and the full run went from over
# 3 hours to 16 min. Level 3 loads no faster once 12 threads share the box;
# level 1 gives up 2.5x of it. The two tree-sitter crates are the parse (their C
# sources are built at the package's opt-level): 0.20 s -> 0.07 s, paid once per
# test binary and on every spawn of the CLIs.
#
# The price is the REBUILD: with anthill-core optimized, an edit to most of its
# sources or to tests/common/mod.rs costs 1-2 min to rebuild where opt-level 0
# takes 8-16 s (kb/load.rs ~80 s, a one-line accessor in kb/term.rs ~130 s) —
# its own test binaries are optimized with it, a profile override being per
# package. That is why the setting is passed HERE, per run, and is not in
# Cargo.toml: a full run is worth it, an edit loop on a few tests is not.
#
#   ANTHILL_TEST_OPT=2   anthill-core at opt-level 2, the tree-sitter crates at 3
#   ANTHILL_TEST_OPT=0   the dev profile as the manifest has it
#
# Default: 2 for a full run (no arguments), 0 when a selection is given. Set it
# to 2 for a WIDE selection — `-p anthill-core` is 13 min optimized and over two
# hours not. Debug assertions and overflow checks are on in both. The two are
# separate builds in the same target/, each kept current by the runs that use it.
#
# ── Three load recipes: the shared base, one shot, or two steps ──────────────
#
#   neither set, or both 0         anthill-core's shared load helpers take a COPY of
#                                  the stdlib loaded once per test binary, sealed,
#                                  and `load_all(user)` into it — the gate (WI-059),
#                                  and the ORDER the product loads in
#                                  (`load::load_program`, WI-20261009-AN6CQ)
#   ANTHILL_TEST_FRESH_LOAD=1      one `load_all(stdlib ∪ user)` into a fresh KB,
#                                  for every load — how the library's own files
#                                  are loaded, and the recipe to bisect a
#                                  difference in the ORDER against
#   ANTHILL_TEST_TWO_STEP_LOAD=1   `load_all(stdlib)` and then `load_all(user)`
#                                  into a fresh KB
#
# The three must give every test the same verdict; the switches are how that is
# measured (WI-20261006-SZKV7, WI-059; `LoadRecipe` in
# anthill-core/tests/common/mod.rs). Setting both is refused. Run a control
# optimized, like any crate-wide selection:
#
#   ANTHILL_TEST_OPT=2 ANTHILL_TEST_FRESH_LOAD=1 scripts/test.sh -p anthill-core
#   ANTHILL_TEST_OPT=2 ANTHILL_TEST_TWO_STEP_LOAD=1 scripts/test.sh -p anthill-core
#
# Nothing is rebuilt: the test binaries read it at run time, so this script only
# validates it and writes into the log what was ASKED FOR. It reaches the loads
# that go through those helpers and nothing else: a test pinned to a recipe by
# name runs that one, and the library's unit tests, the other crates' harnesses
# and the binaries the CLI suites spawn load as the product does — the library,
# sealed, and then the program (`load::load_program`) — whatever is set here.
# So the log also carries what anthill-core's control test OBSERVED.
#
# ── Which carrier a declared type rides: a term, or a node ───────────────────
#
#   ANTHILL_TEST_NODE_CARRIER=1    every sort named where a type alias written bare
#                                  rides its occurrence node rides one too, standing
#                                  for itself
#
# The node changes no meaning, so every test must have the same verdict with the
# switch as without it: one that differs names a reader that does not read a type
# through the carrier-neutral view. The LOADER reads it (`node_carrier_control` in
# anthill-core/src/kb/load.rs), so unlike the load recipe it reaches every load of
# every crate, the spawned binaries included. Not a second gate — a control, run
# when a change touches how a type is carried or read:
#
#   ANTHILL_TEST_NODE_CARRIER=1 scripts/test.sh
#
# The log carries what was asked for and what anthill-core's control test OBSERVED.

set -euo pipefail
cd "$(dirname "$0")/.."

# CPU count: `nproc` on Linux/WSL, `sysctl` on macOS/BSD, 4 if neither answers.
cpus=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
half=$(( cpus / 2 )); [ "$half" -lt 1 ] && half=1
: "${ANTHILL_TEST_THREADS:=$cpus}"
: "${ANTHILL_CLI_TEST_THREADS:=$half}"

# Crates whose tests spawn the built binary — the throttled tier.
SPAWNING_CRATES=(anthill-cli anthill-todo)

mkdir -p target

# ── One run at a time ────────────────────────────────────────────────────────
#
# Two concurrent runs share one `target/` and fight over the cargo build lock,
# so the second sits blocked while both starve the machine — MEASURED, a second
# run started beside a live one produced 8 seconds of output and then nothing
# for 16 minutes, and the contention was enough to blow a 30s test timeout in an
# unrelated suite.
#
# The symlink is why this has to be a REFUSAL and not a warning. `test-run-
# latest.log` is claimed at STARTUP, so the second run takes it from the first
# and then dies holding it: `test-status.sh` reads `latest`, faithfully reports
# a dead 8-second run, and the live one becomes invisible. A stale pid file is
# not that hazard — it is a file whose process is gone, which `kill -0` settles.
#
# `--force` overrides, because the lock is advisory and a wedged run should not
# need a manual `rm`.
force=0
for a in "$@"; do [ "$a" = "--force" ] && force=1; done
if [ "$force" = 1 ]; then
  set -- "${@/--force/}"                     # drop it before cargo sees it
  # A lone `--force` leaves one empty arg, which cargo reads as an empty
  # selector; strip empties so `test.sh --force` means the same as `test.sh`.
  args=(); for a in "$@"; do [ -n "$a" ] && args+=("$a"); done
  set -- ${args+"${args[@]}"}
fi

pidfile="target/test-run.pid"
if [ "$force" = 0 ] && [ -e "$pidfile" ]; then
  read -r prev_pid prev_log < "$pidfile" || true
  if [ -n "${prev_pid:-}" ] && kill -0 "$prev_pid" 2>/dev/null; then
    prev_started=$(ps -o lstart= -p "$prev_pid" 2>/dev/null | sed 's/^ *//;s/ *$//')
    prev_age=$(ps -o etime= -p "$prev_pid" 2>/dev/null | tr -d ' ')
    {
      echo "test.sh: a run is already in flight"
      echo "  pid:  ${prev_pid}  (started ${prev_started:-?}, ${prev_age:-?} ago)"
      echo "  log:  rustland/${prev_log:-<unknown>}"
      echo "refusing to start a second run on the same target dir."
      echo "(pass --force to override)"
    } >&2
    exit 2
  fi
fi

# ── Which build (see the header) ─────────────────────────────────────────────
if [ "$#" -gt 0 ]; then default_opt=0; else default_opt=2; fi
: "${ANTHILL_TEST_OPT:=$default_opt}"
case "$ANTHILL_TEST_OPT" in
  2) opt_cfg=(--config 'profile.dev.package.anthill-core.opt-level=2'
              --config 'profile.dev.package.tree-sitter.opt-level=3'
              --config 'profile.dev.package.tree-sitter-anthill.opt-level=3')
     opt_note="anthill-core at opt-level 2" ;;
  0) opt_cfg=()
     opt_note="dev profile, opt-level 0" ;;
  *) echo "test.sh: ANTHILL_TEST_OPT=${ANTHILL_TEST_OPT}: expected 0 or 2" >&2; exit 2 ;;
esac

# ── Which load recipe (see the header) ───────────────────────────────────────
: "${ANTHILL_TEST_TWO_STEP_LOAD:=0}"
: "${ANTHILL_TEST_FRESH_LOAD:=0}"
case "${ANTHILL_TEST_FRESH_LOAD}${ANTHILL_TEST_TWO_STEP_LOAD}" in
  00) load_note="SHARED BASE in anthill-core's tests/common helpers, the library and then the program everywhere else" ;;
  10) load_note="ONE SHOT in anthill-core's tests/common helpers, the library and then the program everywhere else" ;;
  01) load_note="TWO-STEP in anthill-core's tests/common helpers, the library and then the program everywhere else" ;;
  11) echo "test.sh: ANTHILL_TEST_FRESH_LOAD=1 and ANTHILL_TEST_TWO_STEP_LOAD=1: each names a recipe, set one" >&2; exit 2 ;;
  *) echo "test.sh: ANTHILL_TEST_FRESH_LOAD=${ANTHILL_TEST_FRESH_LOAD} ANTHILL_TEST_TWO_STEP_LOAD=${ANTHILL_TEST_TWO_STEP_LOAD}: expected 0 or 1 for each" >&2; exit 2 ;;
esac
export ANTHILL_TEST_TWO_STEP_LOAD ANTHILL_TEST_FRESH_LOAD

# ── Which carrier a declared type rides (see the header) ─────────────────────
: "${ANTHILL_TEST_NODE_CARRIER:=0}"
case "${ANTHILL_TEST_NODE_CARRIER}" in
  0) carrier_note="terms, a node where a type alias is written" ;;
  1) carrier_note="A NODE for every sort named where an alias would ride one" ;;
  *) echo "test.sh: ANTHILL_TEST_NODE_CARRIER=${ANTHILL_TEST_NODE_CARRIER}: expected 0 or 1" >&2; exit 2 ;;
esac
export ANTHILL_TEST_NODE_CARRIER

# ── anthill-core must be ONE build, whatever is selected ─────────────────────
#
# Cargo unifies features across what one invocation builds. If another workspace
# crate turns on a feature of a dependency anthill-core also has, anthill-core
# becomes a different build per selection — and for the gate it is built
# optimized, ~110 s a time. MEASURED before this check existed
# (WI-20261006-ZVV24): four library builds in one gate, over `chrono` and
# `serde/derive`. Nothing else reports that drift — every selection still builds
# and passes — so it is refused here: what anthill-core's dependencies resolve to
# on their own must be what they resolve to in the whole workspace.
#
# It names `chrono` and `serde` on the manifests as they were before the fix, and
# nothing on them since. It sees the TARGET side only: a build-dependency's
# features (anthill-core is also built for the host, for anthill-stl's build
# script) are not on `-e normal` edges.
core_dep_features() {
  cargo tree "$@" -e normal -f '{p} [{f}]' --prefix none | sed 's/ (\*)//' | sort -u
}
alone=$(core_dep_features -p anthill-core)
whole=$(core_dep_features --workspace)
drift=$(comm -23 <(printf '%s\n' "$alone") <(printf '%s\n' "$whole"))
if [ -n "$drift" ]; then
  {
    echo "test.sh: anthill-core's dependencies resolve to DIFFERENT features alone and in the workspace:"
    printf '%s\n' "$drift" | sed 's/^/  alone: /'
    echo "another workspace crate enables a feature that anthill-core's own Cargo.toml line"
    echo "does not, so anthill-core would be built once per selection. See rustland/CLAUDE.md."
  } >&2
  exit 2
fi

ts=$(date +%Y%m%d-%H%M%S)
log="target/test-run-${ts}.log"
ln -sfn "test-run-${ts}.log" target/test-run-latest.log
printf '%s %s\n' "$$" "${log}" > "$pidfile"
# Removed however we leave — including the `set -e` paths and Ctrl-C — so the
# next run is never refused by a corpse.
trap 'rm -f "$pidfile"' EXIT

start=$(date +%s)
prefix_elapsed() {
  while IFS= read -r line; do
    printf '[%4ds] %s\n' "$(( $(date +%s) - start ))" "$line"
  done
}

# One `cargo test` under a pty, with RUST_TEST_THREADS set for that tier.
cargo_under_pty() {
  local threads="$1"; shift
  case "$(uname)" in
    # BSD `script`: command trails the logfile.
    Darwin)
      RUST_TEST_THREADS="$threads" \
        script -F -q /dev/null cargo test --no-fail-fast \
          ${opt_cfg[@]+"${opt_cfg[@]}"} "$@" 2>&1 ;;
    # util-linux `script`: command must be passed via -c "...". Build a
    # safely-quoted command string so args with spaces survive. `-e` returns
    # the CHILD's exit status rather than script's own — without it a failing
    # cargo is reported as success.
    *)
      local cmd="cargo test --no-fail-fast"
      for a in ${opt_cfg[@]+"${opt_cfg[@]}"} "$@"; do cmd+=" $(printf '%q' "$a")"; done
      RUST_TEST_THREADS="$threads" \
        script -efq -c "${cmd}" /dev/null 2>&1 ;;
  esac
}

# Run one tier, append to the log, and return cargo's own status. `set -e` is
# lifted around the pipeline so a failing tier does not abort the next one —
# that is what `--no-fail-fast` means across the split, and the caller folds the
# statuses so the script still exits non-zero if ANY tier failed.
run_tier() {
  local threads="$1"; shift
  set +e
  cargo_under_pty "$threads" "$@" | prefix_elapsed | tee -a "${log}"
  local st=${PIPESTATUS[0]}
  set -e
  return "$st"
}

echo "log:  rustland/${log}  (-> rustland/target/test-run-latest.log)"
echo "tail: tail -f rustland/target/test-run-latest.log"
echo "threads: ${ANTHILL_TEST_THREADS} (compute) / ${ANTHILL_CLI_TEST_THREADS} (spawning) on ${cpus} CPUs"
# What was MEASURED goes into the log too: the lines above say where to look, these
# three say what a reader of the log is looking at.
{
  echo "build:   ${opt_note} (ANTHILL_TEST_OPT=${ANTHILL_TEST_OPT})"
  echo "load:    ${load_note} (ANTHILL_TEST_FRESH_LOAD=${ANTHILL_TEST_FRESH_LOAD} ANTHILL_TEST_TWO_STEP_LOAD=${ANTHILL_TEST_TWO_STEP_LOAD})"
  echo "carrier: ${carrier_note} (ANTHILL_TEST_NODE_CARRIER=${ANTHILL_TEST_NODE_CARRIER})"
} | tee -a "${log}"
echo "---"

overall=0

if [ "$#" -gt 0 ]; then
  # Explicit selection: run exactly what was asked, once. Pick the tier by
  # whether the arguments name a spawning crate — a `-p anthill-todo` run
  # deserves the same throttle it gets inside a full run.
  tier="$ANTHILL_TEST_THREADS"
  for a in "$@"; do
    for c in "${SPAWNING_CRATES[@]}"; do
      [ "$a" = "$c" ] && tier="$ANTHILL_CLI_TEST_THREADS"
    done
  done
  run_tier "$tier" "$@" || overall=$?
else
  # Full run, split in two.
  excludes=(); for c in "${SPAWNING_CRATES[@]}"; do excludes+=(--exclude "$c"); done
  packages=(); for c in "${SPAWNING_CRATES[@]}"; do packages+=(-p "$c"); done

  run_tier "$ANTHILL_TEST_THREADS" --workspace "${excludes[@]}" || overall=$?
  run_tier "$ANTHILL_CLI_TEST_THREADS" "${packages[@]}" || overall=$?
fi

exit "$overall"
