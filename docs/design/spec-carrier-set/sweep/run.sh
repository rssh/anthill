#!/usr/bin/env bash
# The order-swap sweep of ../../spec-carrier-set.md's stage 2, tenth step: every program of two
# grids, each in both declaration orders of `Sp[A, B]`, and the pairs whose verdict differs. A
# third grid (the P readers step): one provider's OWN two provisions at two applications, in both
# orders they can be written (`_is` / `_si`). A fourth (the former step): a function-typed carrier
# over `Ap[F, R]` in both declaration orders.
# Usage: run.sh [path/to/anthill]   (default: rustland/target/debug/anthill). Writes the programs
# and their verdicts under rustland/target/spec-carrier-sweep (replaced at each run) and prints
# `VERDICT <program>: ab=… ba=…` for each pair that differs.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../../.." && pwd)"
A="${1:-$root/rustland/target/debug/anthill}"
work="$root/rustland/target/spec-carrier-sweep"
mkdir -p "$work"
for d in one two own fm res-one res-two res-own res-fm; do
  [ -d "$work/$d" ] && find "$work/$d" -maxdepth 1 -type f \( -name '*.anthill' -o -name '*.txt' \) -delete
done
python3 "$here/gen_one_provider.py" "$work/one" >/dev/null
python3 "$here/gen_two_providers.py" "$work/two" >/dev/null
python3 "$here/gen_own_two.py" "$work/own" >/dev/null
python3 "$here/gen_former.py" "$work/fm" >/dev/null
for grid in one two own fm; do
  [ "$grid" = own ] && x=is y=si || x=ab y=ba
  mkdir -p "$work/res-$grid"
  ls "$work/$grid"/*.anthill | xargs -P 20 -I{} sh -c 'f={}; b=$(basename $f .anthill); "'"$A"'" run "$f" 2>&1 | head -1 > "'"$work/res-$grid"'/$b.txt"'
  for f in "$work/res-$grid"/*_$x.txt; do
    b=$(basename "$f" _$x.txt)
    kind() { grep -qE '^[0-9]+$' "$1" && echo "RUNS $(cat "$1")" || echo REFUSED; }
    ka=$(kind "$work/res-$grid/${b}_$x.txt"); kc=$(kind "$work/res-$grid/${b}_$y.txt")
    [ "$ka" != "$kc" ] && echo "VERDICT $grid/$b: $x=$ka $y=$kc"
  done
done
echo "sweep done: $(ls "$work"/one/*.anthill "$work"/two/*.anthill "$work"/own/*.anthill "$work"/fm/*.anthill | wc -l) programs in $work"
