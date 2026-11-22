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

echo "##### A. Selection: which provision a call gets"
for f in a1 a2 a3 a4 a5 a6 a7; do run "$(ls $f-*.anthill)"; done

echo "##### B. The single carrier parameter, read two ways"
rows    b1-sortdomain-witness.anthill SortDomain 'Colour|W'
carrier b1-sortdomain-witness.anthill SortDomain 'Colour|W'
"$A" load b2-typevalue-witness.anthill 2>&1 | grep -i typevalue | head -2 | sed 's/^/=== b2: /'
carrier b3-order-T-first.anthill Bag2 MyBag
carrier b4-order-C-first.anthill Bag2 MyBag
for f in b5 b6 b7 b8; do run "$(ls $f-*.anthill)"; done

echo "##### C. Not decided here (kept apart)"
for f in c1 c2 c3 c4; do run "$(ls $f-*.anthill)"; done

echo "##### D. Decision 1: what a call fixes, for every provider"
for f in d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15; do run "$(ls $f-*.anthill)"; done

echo "##### E. Decision 4: a spec that takes Self and a type-var"
for f in e1 e2 e3 e4 e5; do
  run "$(ls $f-*.anthill)"
  carrier "$(ls $f-*.anthill)" Holder 'Holder'
done

echo "##### F. Decision 6: a provider named only at a result-only type-var"
run f1-provider-named-only-in-a-result.anthill
carrier f1-provider-named-only-in-a-result.anthill Coll 'Num'
echo "=== f1: self_provides rows of Coll"
"$A" query --path f1-provider-named-only-in-a-result.anthill --max-results 100000 \
  'anthill.reflect.typing.self_provides(?c, ?s)' 2>&1 | grep -E "\?s = Coll\b" || echo "  (none)"
echo "=== f2: Foo provides Dflt[T = Self], T result-only"
for q in 'self_provides(?c, ?s)' 'default_provider(?s, ?c, ?w)'; do
  "$A" query --path f2-only-type-var-is-result-only.anthill --max-results 100000 \
    "anthill.reflect.typing.$q" 2>&1 | grep -E "\?s = Dflt\b" | sed "s/^/  ${q%%(*}: /"
done

run f4-two-sorts-own-one-substituted-sort.anthill
echo "=== f4: default_provider rows of Coll"
"$A" query --path f4-two-sorts-own-one-substituted-sort.anthill --max-results 100000 \
  'anthill.reflect.typing.default_provider(?s, ?c, ?w)' 2>&1 | grep -E "\?s = Coll\b"

echo "##### G. Decision 5: the default rows of a self-representing spec"
"$A" load g1-two-defaults-overlap-refused.anthill 2>&1 | head -1 | cut -c1-300 | sed 's/^/=== g1: /'
run g2-self-representing-two-providers.anthill
echo "=== g2: default_provider rows of Src"
"$A" query --path g2-self-representing-two-providers.anthill --max-results 100000 \
  'anthill.reflect.typing.default_provider(?s, ?c, ?w)' 2>&1 | grep -E "\?s = Src\b"
run g3-self-returning-call-names-no-provider.anthill
run g4-self-returning-call-names-a-concrete-provider.anthill
run g5-provider-member-called-directly.anthill
run g6-self-result-expected-type.anthill
