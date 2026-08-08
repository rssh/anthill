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
        script -F -q /dev/null cargo test --no-fail-fast "$@" 2>&1 ;;
    # util-linux `script`: command must be passed via -c "...". Build a
    # safely-quoted command string so args with spaces survive. `-e` returns
    # the CHILD's exit status rather than script's own — without it a failing
    # cargo is reported as success.
    *)
      local cmd="cargo test --no-fail-fast"
      for a in "$@"; do cmd+=" $(printf '%q' "$a")"; done
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
