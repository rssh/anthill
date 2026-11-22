#!/usr/bin/env bash
# The order-swap sweep of ../../spec-carrier-set.md's stage 2, tenth step: every program of two
# grids, each in both declaration orders of `Sp[A, B]`, and the pairs whose verdict differs.
# Usage: run.sh [path/to/anthill]   (default: rustland/target/debug/anthill). Writes the programs
# and their verdicts under rustland/target/spec-carrier-sweep (replaced at each run) and prints
# `VERDICT <program>: ab=… ba=…` for each pair that differs.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../../.." && pwd)"
A="${1:-$root/rustland/target/debug/anthill}"
work="$root/rustland/target/spec-carrier-sweep"
mkdir -p "$work"
for d in one two res-one res-two; do
  [ -d "$work/$d" ] && find "$work/$d" -maxdepth 1 -type f \( -name '*.anthill' -o -name '*.txt' \) -delete
done
python3 "$here/gen_one_provider.py" "$work/one" >/dev/null
python3 "$here/gen_two_providers.py" "$work/two" >/dev/null
for grid in one two; do
  mkdir -p "$work/res-$grid"
  ls "$work/$grid"/*.anthill | xargs -P 20 -I{} sh -c 'f={}; b=$(basename $f .anthill); "'"$A"'" run "$f" 2>&1 | head -1 > "'"$work/res-$grid"'/$b.txt"'
  for f in "$work/res-$grid"/*_ab.txt; do
    b=$(basename "$f" _ab.txt)
    kind() { grep -qE '^[0-9]+$' "$1" && echo "RUNS $(cat "$1")" || echo REFUSED; }
    ka=$(kind "$work/res-$grid/${b}_ab.txt"); kc=$(kind "$work/res-$grid/${b}_ba.txt")
    [ "$ka" != "$kc" ] && echo "VERDICT $grid/$b: ab=$ka ba=$kc"
  done
done
echo "sweep done: $(ls "$work"/one/*.anthill "$work"/two/*.anthill | wc -l) programs in $work"
