#!/usr/bin/env bash
# Reproduce the measurements of ../spec-carrier-set.md.
# Usage: run.sh [path/to/anthill]   (default: rustland/target/debug/anthill)
set -u
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
A="${1:-$root/rustland/target/debug/anthill}"
cd "$here"

run() {    # a program with an entry: what it prints, or its refusal
  echo "=== $1"
  "$A" run "$1" 2>&1 | head -4 | cut -c1-300
}
rows() {   # the provision rows of a spec the program's own sorts write or are given
  echo "=== $1: SortProvidesInfo rows of $2 naming $3"
  "$A" query --path "$1" --max-results 100000 \
    'anthill.reflect.SortProvidesInfo(sort_ref: ?p, spec: ?s)' 2>&1 \
    | grep -E "SortView\($2\b" | grep -E "\b($3)\b"
}
carrier() { # which sort the reflect relation says a provision is at
  echo "=== $1: provision_carrier rows of $2 naming $3"
  "$A" query --path "$1" --max-results 100000 \
    'anthill.reflect.typing.provision_carrier(?p, ?s, ?c)' 2>&1 \
    | grep -E "\?s = $2\b" | grep -E "\b($3)\b"
}

echo "##### A. Selection: which instance a call gets"
for f in a1 a2 a3 a4 a5 a6 a7 a8; do run "$(ls $f-*.anthill)"; done

echo "##### B. The single carrier parameter, read two ways"
rows    b1-sortdomain-witness.anthill SortDomain 'Colour|W'
carrier b1-sortdomain-witness.anthill SortDomain 'Colour|W'
"$A" load b2-typevalue-witness.anthill 2>&1 | grep -i typevalue | head -2 | sed 's/^/=== b2: /'
carrier b3-order-T-first.anthill Bag2 MyBag
carrier b4-order-C-first.anthill Bag2 MyBag

echo "##### C. Not this question (controls for the record)"
for f in c1 c2 c3; do run "$(ls $f-*.anthill)"; done
