#!/usr/bin/env bash
# 060.1 §9 S1 (WI-20261127-DAPCN) — the probe's full-workspace runs, one per mode.
#
#   git apply docs/measurements/060.1-section9/s1-probe.patch      # the probe, on the tree
#   docs/measurements/060.1-section9/s1-runs.sh OUT [modes…]       # default modes: log load run
#   python3 -I docs/measurements/060.1-section9/s1-analyze.py OUT  # the counts
#   git checkout -- rustland && rm rustland/anthill-core/src/dapcn_s1.rs   # back out
#
# Each mode writes OUT/gate-<mode>.log (test.sh's log), OUT/hits-<mode>.log (the probe's hits:
# tag, stdlib|prog, the test, the site) and runs scripts/families.sh after the gate.
set -u
OUT=${1:?usage: s1-runs.sh OUT [modes…]}; shift
MODES=${*:-log load run}
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
cd "$(dirname "$0")/../../../rustland"
for mode in $MODES; do
  rm -f "$OUT/hits-$mode.log"
  echo "=== $mode start $(date -Is)" >> "$OUT/runs.status"
  ANTHILL_DAPCN_S1=$mode ANTHILL_DAPCN_S1_LOG="$OUT/hits-$mode.log" scripts/test.sh > "$OUT/gate-$mode.out" 2>&1
  echo "=== $mode gate exit $? $(date -Is)" >> "$OUT/runs.status"
  cp target/test-run-latest.log "$OUT/gate-$mode.log"
  ANTHILL_DAPCN_S1=$mode ANTHILL_DAPCN_S1_LOG="$OUT/hits-$mode-families.log" scripts/families.sh > "$OUT/families-$mode.out" 2>&1
  echo "=== $mode families exit $? $(date -Is)" >> "$OUT/runs.status"
done
