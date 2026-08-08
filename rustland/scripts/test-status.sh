#!/bin/sh
# Report progress of an in-flight cargo test run started by scripts/test.sh.
# POSIX sh — survives `sh scripts/test-status.sh` (dash) as well as bash.
#
# Reads the latest log (or one passed as $1) and prints:
#   - the most recent "Running .../target/debug/deps/<name>-<hash>" line
#     (= which binary cargo is currently executing or last started)
#   - elapsed time since that line was written (rough hang signal)
#   - tail of the log
#
# Usage:
#   rustland/scripts/test-status.sh
#   rustland/scripts/test-status.sh path/to/test-run-XXXX.log

# No pipefail (not POSIX): the only pipeline below already masks failure
# with `|| true`.
set -eu
cd "$(dirname "$0")/.."

log="${1:-target/test-run-latest.log}"
if [ ! -e "${log}" ]; then
  echo "no log at: rustland/${log}" >&2
  echo "run scripts/test.sh first" >&2
  exit 1
fi

# Resolve symlink to real path so stat works portably.
real=$(readlink -f "${log}" 2>/dev/null || python3 -c 'import os,sys;print(os.path.realpath(sys.argv[1]))' "${log}")

echo "log: ${real}"

# Whether the run this log belongs to is still alive. `test.sh` writes
# "<pid> <log>" to target/test-run.pid and clears it on exit, so a live pid
# whose log is NOT this one means the caller is reading a finished run — the
# state that used to read as a hang, back when a second run could claim
# `latest` at startup and then die holding it.
if [ -e target/test-run.pid ]; then
  read -r live_pid live_log < target/test-run.pid || true
  if [ -n "${live_pid:-}" ] && kill -0 "${live_pid}" 2>/dev/null; then
    live_real=$(readlink -f "${live_log}" 2>/dev/null || echo "${live_log}")
    if [ "${live_real}" = "${real}" ]; then
      echo "     (live, pid ${live_pid})"
    else
      echo "     (NOT the live run — pid ${live_pid} is writing rustland/${live_log})"
    fi
  fi
fi
echo

last_running=$(grep -n "Running " "${real}" | tail -1 || true)
if [ -n "${last_running}" ]; then
  echo "current/last binary:"
  echo "  ${last_running}"
fi

# Mtime of the log = last write = roughly when the running test last produced output.
case "$(uname)" in
  Darwin) mtime=$(stat -f %m "${real}") ;;
  *)      mtime=$(stat -c %Y "${real}") ;;
esac
now=$(date +%s)
echo
echo "last log write: $(( now - mtime ))s ago"
echo "                (no new output for >120s often means a hang)"
echo
echo "--- tail -20 ---"
tail -20 "${real}"
