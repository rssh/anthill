#!/usr/bin/env python3
"""From a traced run (ANTHILL_LOAD_TIMING=1): how many runs of the provision check read every row, and why.
Counts the `[provider_requires]` lines `load_phase_inner` prints, grouped by their reason with the names taken out."""
import re, sys, collections
by = collections.Counter(); rows = collections.Counter(); ex = {}
narrowed_rows = []
n = 0
for l in open(sys.argv[1], errors='replace'):
    m = re.search(r"\[provider_requires\] read (\d+) rows from slot (\d+) of (\d+), (\d+) open goal\(s\): (.*)$", l)
    if not m: continue
    n += 1
    read, slot, total, open_, why = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)), m.group(5).strip()
    key = re.sub(r"'[^']*'", "'…'", why)
    key = ('NARROWED: ' if slot > 0 else 'EVERY ROW: ') + key + (' [open goals]' if open_ else '')
    by[key] += 1; rows[key] += read
    ex.setdefault(key, why)
    if slot > 0: narrowed_rows.append(read)
print('runs of the check:', n)
for k, c in by.most_common():
    print('%7d  %5.1f%%  rows/run %7.1f  %s' % (c, 100.0*c/n, rows[k]/c, k))
    if 'EVERY ROW' in k and "'" in ex[k]: print('                 e.g. ' + ex[k][:150])
if narrowed_rows:
    narrowed_rows.sort()
    print('narrowed runs: rows read  median %d  p90 %d  max %d' % (narrowed_rows[len(narrowed_rows)//2], narrowed_rows[int(len(narrowed_rows)*0.9)], narrowed_rows[-1]))
