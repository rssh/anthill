#!/usr/bin/env bash
# The generated families — anthill-core/tests/families/ — every program of each, held
# to its properties: no crash, no verdict moved from the committed file, a program that
# loads runs, one verdict for two spellings of one program.
#
# NOT part of scripts/test.sh: the workspace run compiles the families and runs only
# their runner's own controls, which load no program. Run this when a change touches
# the typer, and commit the verdict files it moved with the change that moved them.
#
#   scripts/families.sh                    every family
#   scripts/families.sh a,c                the families whose names start so
#   scripts/families.sh bless [a,c]        write the verdict files from this tree, then judge
#   scripts/families.sh print <family> '<program name>'
#                                          one program, and what this tree says of it
#   scripts/families.sh dump <dir> [a,c]   every program as a file, <dir>/<family>/<name>.anthill
#
# A verdict file is anthill-core/tests/families/verdicts/<family>.tsv; a run leaves what
# it found beside the build, target/tmp/families/<family>.tsv, to diff against it.
#
# Built as the gate is — anthill-core at opt-level 2 — unless ANTHILL_TEST_OPT says
# otherwise, so a run after a gate links one binary and compiles nothing else.
#
#   ANTHILL_FAMILY_JOBS            child processes at a time   (default: CPU count)
#   ANTHILL_FAMILY_PATIENCE_SECS   silence before a child is killed and its program
#                                  called HUNG                 (default: 120)

set -euo pipefail
cd "$(dirname "$0")/.."

: "${ANTHILL_TEST_OPT:=2}"
export ANTHILL_TEST_OPT

run_test() {
  exec scripts/test.sh -p anthill-core --test wi_tests -- --ignored --exact "families::$1" --nocapture
}

case "${1:-}" in
  bless)
    export ANTHILL_FAMILIES_BLESS=1 ANTHILL_FAMILIES="${2:-}"
    run_test run ;;
  print)
    [ "$#" -eq 3 ] || { echo "usage: families.sh print <family> '<program name>'" >&2; exit 2; }
    export ANTHILL_FAMILIES_PRINT="$2:$3"
    run_test show ;;
  dump)
    [ "$#" -ge 2 ] || { echo "usage: families.sh dump <dir> [families]" >&2; exit 2; }
    mkdir -p "$2"
    export ANTHILL_FAMILIES_DUMP="$(cd "$2" && pwd)" ANTHILL_FAMILIES="${3:-}"
    run_test show ;;
  *)
    export ANTHILL_FAMILIES="${1:-}"
    run_test run ;;
esac
