#!/usr/bin/env bash
# Judge one program of the supplier matrix: print "<ns>\t<verdict>".
# A verdict is the program's printed answer, the query's answers, or the first error line.
set -u
dir=$1; ns=$2; mode=$3
bin=${ANTHILL_BIN:-rustland/target/debug/anthill}
f="$dir/$ns.anthill"
if [ "$mode" = run ]; then
  out=$(timeout 60 "$bin" run "$f" 2>&1); rc=$?
else
  out=$(timeout 60 "$bin" query -p "$f" -i "probe.$ns.*" 'rq(?r)' 2>&1); rc=$?
fi
if [ $rc -eq 124 ]; then v="TIMEOUT"
elif printf '%s' "$out" | grep -q '^error'; then
  v=$(printf '%s' "$out" | grep '^error' | sed -E "s#^error: [^ ]*\.anthill:[0-9]+:[0-9]+: ##; s#^error: ##" | cut -c1-160 | tr '\n' '|')
  v="ERR: $v"
elif [ "$mode" = query ]; then
  v=$(printf '%s' "$out" | grep -E '^\s*\?r = |solution\(s\)|no solution|warning' | tr '\n' ' ' | sed 's/  */ /g' | cut -c1-200)
else
  v=$(printf '%s' "$out" | tail -1 | cut -c1-200)
  [ $rc -ne 0 ] && v="EXIT $rc: $(printf '%s' "$out" | tr '\n' ' ' | cut -c1-200)"
fi
printf '%s\t%s\n' "$ns" "$v"
