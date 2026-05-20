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

set -euo pipefail
cd "$(dirname "$0")/.."

ts=$(date +%Y%m%d-%H%M%S)
mkdir -p target
log="target/test-run-${ts}.log"
ln -sfn "test-run-${ts}.log" target/test-run-latest.log

start=$(date +%s)
prefix_elapsed() {
  while IFS= read -r line; do
    printf '[%4ds] %s\n' "$(( $(date +%s) - start ))" "$line"
  done
}

echo "log:  rustland/${log}  (-> rustland/target/test-run-latest.log)"
echo "tail: tail -f rustland/target/test-run-latest.log"
echo "---"

case "$(uname)" in
  # BSD `script`: command trails the logfile.
  Darwin) script -F -q /dev/null cargo test --no-fail-fast "$@" 2>&1 ;;
  # util-linux `script`: command must be passed via -c "...". Build a
  # safely-quoted command string so args with spaces survive.
  *)
    cmd="cargo test --no-fail-fast"
    for a in "$@"; do cmd+=" $(printf '%q' "$a")"; done
    script -fq -c "${cmd}" /dev/null 2>&1
    ;;
esac | prefix_elapsed | tee "${log}"
