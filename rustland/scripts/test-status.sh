#!/usr/bin/env bash
# Report progress of an in-flight cargo test run started by scripts/test.sh.
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

set -euo pipefail
cd "$(dirname "$0")/.."

log="${1:-target/test-run-latest.log}"
if [[ ! -e "${log}" ]]; then
  echo "no log at: rustland/${log}" >&2
  echo "run scripts/test.sh first" >&2
  exit 1
fi

# Resolve symlink to real path so stat works portably.
real=$(readlink -f "${log}" 2>/dev/null || python3 -c 'import os,sys;print(os.path.realpath(sys.argv[1]))' "${log}")

echo "log: ${real}"
echo

last_running=$(grep -n "Running " "${real}" | tail -1 || true)
if [[ -n "${last_running}" ]]; then
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
