#!/bin/bash
# usage: run.sh <binary> <label>; peak RSS per probe/n
B=$1; L=$2
cd "$(dirname "$0")"  # the probes sit beside this script
for spec in grow:chain control:chain cnt:cnt tgrow:chain tcnt:cnt; do
  f=${spec%%:*}; p=${spec##*:}
  for n in 1000 2000 4000; do
    out=$( { /usr/bin/time -f 'RSS %M KB wall %e s' $B query -p $f.anthill -i probe.$f.$p --max-depth 100000 "$p($n)" ; } 2>&1 | grep -E 'solution|RSS|rror' | tr '\n' ' ')
    echo "$L $f n=$n $out"
  done
done
