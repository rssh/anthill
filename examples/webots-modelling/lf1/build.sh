#!/usr/bin/env bash
# build.sh — scaffold a runnable lf1 Webots project from this anthill spec.
#
# Runs `anthill codegen cpp-project` against the .anthill files in
# this directory, dropping a self-contained Webots project tree at
# `$OUT_DIR` (default `./build`). The result has:
#
#   build/
#     controllers/
#       LeaderController/    — generated header + main + Makefile + MavicBase
#       FollowerController/  — same shape
#     worlds/
#       multirotor_leader_follower1.wbt
#
# After this completes, the next step is `make` inside each
# controller folder (with $WEBOTS_HOME set) to produce the binaries
# Webots launches; then open `build/worlds/*.wbt` in Webots.
#
# Re-run this script whenever the .anthill specs change to refresh
# the generated headers.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"

OUT_DIR="${OUT_DIR:-$SCRIPT_DIR/build}"

cd "$REPO_ROOT/rustland"

cargo run --quiet --bin anthill -- codegen cpp-project \
    --namespace anthill.examples.lf1 \
    --cpp-sources "$SCRIPT_DIR/cpp" \
    --worlds-dir  "$SCRIPT_DIR/worlds" \
    --output-dir  "$OUT_DIR" \
    "$SCRIPT_DIR"

cat <<EOF

Scaffolded $OUT_DIR.

Next steps:
  export WEBOTS_HOME=/Applications/Webots.app/Contents          # macOS
  # or:  WEBOTS_HOME=/usr/local/webots                          # Linux

  (cd "$OUT_DIR/controllers/LeaderController"   && make)
  (cd "$OUT_DIR/controllers/FollowerController" && make)

Then open "$OUT_DIR/worlds/multirotor_leader_follower1.wbt" in Webots.
EOF
