#!/usr/bin/env python3
"""How many loads a test run EXECUTED, what each was, and where the thread-time went
(docs/design/test-infrastructure.md §2.4; the tables of load-count-2026-10-10.txt).

    cd rustland
    ANTHILL_LOAD_TIMING=1 RUST_TEST_THREADS=12 cargo test --no-fail-fast -p anthill-core \\
        --config <the gate's three opt lines, §10> -- --show-output > load-trace.log 2>&1
    python3 ../docs/measurements/test-infrastructure/load_trace_report.py load-trace.log [stdlib-files]

`stdlib-files` is how many files the stdlib is, when the log cannot say: the report takes
the commonest file count among the big loads, which is the stdlib's over a whole crate's
run and is NOT over one binary's (in `wi_tests` alone the commonest big load is the
stdlib and one user file, in one call). The first line printed says what was used.

`--show-output`, NOT `--nocapture`: libtest keeps capturing and prints each passed test's
output under `---- <test> stdout ----` once the binary's tests are done, so every trace
line belongs to ONE test and the lines of one load are contiguous — a load is split off at
its first mark (`scan_definitions`). Under `--nocapture` twelve threads' lines interleave
and a phase line cannot be given to a load.

A load is classified by the recipe line `tests/common` prints before it
(`recipe_load <recipe> user_files=<n>`) and by how many files it loaded. The copies of the
shared base are COUNTED from that line, and their TIME is read from the one
`shared_base_instance` prints for each (in the tree since WI-20261010-ANK4X; a temporary
timer for `load-count-2026-10-10.txt`):

    [load_timing] base_copy wait=<duration> copy=<duration>

`wait` from asking for a base to holding the lock of one of the pool's, `copy` the deep
copy made under it. A log taken before that line existed has none, and the `copy` and
`wait` columns are then 0 and the report says so.
"""
import re
import sys
from collections import Counter, defaultdict
from statistics import median

THREADS = 12
path = sys.argv[1]

DUR = re.compile(r'^([\d.]+)(ns|µs|ms|s)$')
UNIT = {'ns': 1e-9, 'µs': 1e-6, 'ms': 1e-3, 's': 1.0}


def secs(text):
    m = DUR.match(text.strip())
    if not m:
        raise ValueError(f'not a duration: {text!r}')
    return float(m.group(1)) * UNIT[m.group(2)]


class Load:
    __slots__ = ('files', 'phases', 'kind')

    def __init__(self):
        self.files = None
        self.phases = []      # (label, seconds), in order
        self.kind = None

    @property
    def total(self):
        return sum(s for _, s in self.phases)


class Test:
    def __init__(self, name):
        self.name = name
        self.loads = []
        self.copies = []      # (wait, copy) — only when the log has `base_copy` lines
        self.base_asks = 0    # `recipe_load SharedBase` lines: one copy of the base each
        self.recipes = []     # (recipe, user_files), in order
        self.events = []      # ('recipe', r, n) | ('copy',) | ('load', Load)


class Binary:
    def __init__(self, name):
        self.name = name
        self.tests = {}
        self.passed = self.failed = self.ignored = 0
        self.wall = 0.0
        self.ran = 0


binaries = []
cur_bin = None
cur_test = None
cur_load = None
lost = 0

RUNNING = re.compile(r'^\s*Running (unittests \S+|tests/\S+) \(')
DOCTEST = re.compile(r'^\s*Doc-tests (\S+)')
HEADER = re.compile(r'^---- (.+) (stdout|stderr) ----$')
RESULT = re.compile(r'^test result: \S+ (\d+) passed; (\d+) failed; (\d+) ignored; .* finished in ([\d.]+)s')
PHASE = re.compile(r'^\[load_timing\]   (.+): (\S+)$')
RECIPE = re.compile(r'^\[load_timing\] recipe_load (\w+) user_files=(\d+)$')
COPY = re.compile(r'^\[load_timing\] base_copy wait=(\S+) copy=(\S+)$')
VISITED = re.compile(r'^load_with_visited x (\d+)$')

with open(path, encoding='utf-8', errors='replace') as f:
    for raw in f:
        line = raw.rstrip('\n')
        m = RUNNING.match(line) or DOCTEST.match(line)
        if m:
            cur_bin = Binary(m.group(1))
            binaries.append(cur_bin)
            cur_test = cur_load = None
            continue
        if cur_bin is None:
            continue
        m = RESULT.match(line)
        if m:
            cur_bin.passed, cur_bin.failed, cur_bin.ignored = (int(m.group(i)) for i in (1, 2, 3))
            cur_bin.wall = float(m.group(4))
            cur_test = cur_load = None
            continue
        m = HEADER.match(line)
        if m:
            cur_test = cur_bin.tests.setdefault(m.group(1), Test(m.group(1)))
            cur_load = None
            continue
        if '[load_timing]' not in line:
            continue
        if cur_test is None:
            lost += 1
            continue
        m = RECIPE.match(line)
        if m:
            cur_test.recipes.append((m.group(1), int(m.group(2))))
            if m.group(1) == 'SharedBase':
                cur_test.base_asks += 1
            cur_test.events.append(('recipe', m.group(1), int(m.group(2))))
            continue
        m = COPY.match(line)
        if m:
            cur_test.copies.append((secs(m.group(1)), secs(m.group(2))))
            cur_test.events.append(('copy',))
            continue
        m = PHASE.match(line)
        if not m:
            lost += 1
            continue
        label, dur = m.group(1), secs(m.group(2))
        if label == 'scan_definitions' or cur_load is None:
            cur_load = Load()
            cur_test.loads.append(cur_load)
            cur_test.events.append(('load', cur_load))
        v = VISITED.match(label)
        if v:
            cur_load.files = int(v.group(1))
            label = 'load_with_visited x N'
        label = re.sub(r'\(\d+ sorts\)', '(N sorts)', label)
        cur_load.phases.append((label, dur))

# The stdlib's size: given, or the commonest file count among the big loads.
sizes = Counter(l.files for b in binaries for t in b.tests.values() for l in t.loads
                if l.files is not None and l.files >= 60)
GIVEN = len(sys.argv) > 2
STDLIB = int(sys.argv[2]) if GIVEN else sizes.most_common(1)[0][0]

# Classify each load from the recipe line that announced it.
KINDS = ['base-build', 'stdlib-alone', 'one-shot+user', 'on-base', 'two-step-2nd', 'later-other', 'unknown']
for b in binaries:
    for t in b.tests.values():
        pending = []
        for ev in t.events:
            if ev[0] == 'recipe':
                pending.append([ev[1], ev[2]])
            elif ev[0] == 'load':
                load = ev[1]
                n = load.files
                if n is None:
                    load.kind = 'unknown'
                elif n == STDLIB:
                    # the shared base's own build is announced `OneShot user_files=0`
                    # while a `SharedBase` line is still waiting for its load
                    waiting = any(p[0] == 'SharedBase' for p in pending)
                    hit = next((p for p in pending if p[0] == 'OneShot' and p[1] == 0), None)
                    if hit and waiting:
                        load.kind = 'base-build'
                        pending.remove(hit)
                    else:
                        load.kind = 'stdlib-alone'
                        if hit:
                            pending.remove(hit)
                elif n > STDLIB:
                    load.kind = 'one-shot+user'
                    hit = next((p for p in pending if p[0] == 'OneShot' and p[1] == n - STDLIB), None)
                    if hit:
                        pending.remove(hit)
                else:
                    hit = next((p for p in pending if p[0] == 'SharedBase' and p[1] == n), None)
                    if hit:
                        load.kind = 'on-base'
                        pending.remove(hit)
                    else:
                        hit = next((p for p in pending if p[0] == 'TwoStep' and p[1] == n), None)
                        if hit:
                            load.kind = 'two-step-2nd'
                            pending.remove(hit)
                        else:
                            load.kind = 'later-other'


def pct(a, b):
    return f'{100 * a / b:5.1f}%' if b else '    -'


print(f'# stdlib size {"given" if GIVEN else "detected"}: {STDLIB} files; trace lines outside any test block: {lost}')
print()
print('== 1. loads EXECUTED per binary, by what they are ==')
print('#   base-build     the shared base\'s own load of the stdlib, once per binary')
print('#   stdlib-alone   another call given the stdlib alone (a fresh recipe\'s first call, load_program\'s first)')
print('#   1shot+user     the stdlib and more in ONE call: a fresh load pinned by name, or one taken off the base')
print('#   on-base        the user\'s files loaded into a COPY of the base (`recipe_load SharedBase`, n > 0)')
print('#   later-other    a load of fewer files with no recipe line: load_program\'s second call, a bare load, one by hand')
print('#   copies         deep copies of the base taken (on-base loads, and load_stdlib_kb which loads nothing)')
hdr = f'{"binary":<32}{"tests":>6}{"wall s":>9}{"base-build":>11}{"stdlib-alone":>13}{"1shot+user":>11}{"on-base":>9}{"2step-2nd":>10}{"later-other":>12}{"copies":>8}'
print(hdr)
tot = Counter()
for b in binaries:
    c = Counter(l.kind for t in b.tests.values() for l in t.loads)
    copies = sum(t.base_asks for t in b.tests.values())
    ran = b.passed + b.failed
    print(f'{b.name:<32}{ran:>6}{b.wall:>9.1f}{c["base-build"]:>11}{c["stdlib-alone"]:>13}{c["one-shot+user"]:>11}'
          f'{c["on-base"]:>9}{c["two-step-2nd"]:>10}{c["later-other"] + c["unknown"]:>12}{copies:>8}')
    tot.update(c)
    tot['copies'] += copies
    tot['tests'] += ran
    tot['wall'] += b.wall
    tot['failed'] += b.failed
    tot['ignored'] += b.ignored
print(f'{"TOTAL":<32}{tot["tests"]:>6}{tot["wall"]:>9.1f}{tot["base-build"]:>11}{tot["stdlib-alone"]:>13}{tot["one-shot+user"]:>11}'
      f'{tot["on-base"]:>9}{tot["two-step-2nd"]:>10}{tot["later-other"] + tot["unknown"]:>12}{tot["copies"]:>8}')
print(f'# failed: {tot["failed"]}, ignored: {tot["ignored"]}')

print()
print('== 2. where the thread-time goes, per binary (thread-seconds; share of wall x 12) ==')
print('#   full loads   base-build + stdlib-alone + 1shot+user: a call that loads the stdlib')
print('#   later loads  every other call')
print('#   copy         inside deep_clone;   wait   from asking for a base to holding the lock of one of the pool\'s')
print(f'{"binary":<32}{"wall x12":>9}{"full loads":>12}{"later loads":>12}{"copy":>8}{"wait":>8}{"all of it":>11}{"share":>8}{"   the rest":>11}')
gt = Counter()
for b in binaries:
    full = sum(l.total for t in b.tests.values() for l in t.loads if l.kind in ('base-build', 'stdlib-alone', 'one-shot+user'))
    later = sum(l.total for t in b.tests.values() for l in t.loads if l.kind not in ('base-build', 'stdlib-alone', 'one-shot+user'))
    wait = sum(w for t in b.tests.values() for w, _ in t.copies)
    copy = sum(c for t in b.tests.values() for _, c in t.copies)
    tt = b.wall * THREADS
    allof = full + later + wait + copy
    print(f'{b.name:<32}{tt:>9.0f}{full:>12.1f}{later:>12.1f}{copy:>8.1f}{wait:>8.1f}{allof:>11.1f}{pct(allof, tt):>8}{tt - allof:>11.0f}')
    for k, v in (('tt', tt), ('full', full), ('later', later), ('wait', wait), ('copy', copy)):
        gt[k] += v
allof = gt['full'] + gt['later'] + gt['wait'] + gt['copy']
print(f'{"TOTAL":<32}{gt["tt"]:>9.0f}{gt["full"]:>12.1f}{gt["later"]:>12.1f}{gt["copy"]:>8.1f}{gt["wait"]:>8.1f}{allof:>11.1f}{pct(allof, gt["tt"]):>8}{gt["tt"] - allof:>11.0f}')


def stats(xs):
    xs = sorted(xs)
    if not xs:
        return 'n=0'
    q = lambda p: xs[min(len(xs) - 1, int(p * len(xs)))]
    return (f'n={len(xs):>6}  mean={1000 * sum(xs) / len(xs):8.2f} ms  median={1000 * median(xs):8.2f}  '
            f'p90={1000 * q(0.9):8.2f}  p99={1000 * q(0.99):8.2f}  max={1000 * xs[-1]:8.2f}')


print()
print('== 3. one load, and one copy, as a test thread pays them (12 threads at once) ==')
by_kind = defaultdict(list)
for b in binaries:
    for t in b.tests.values():
        for l in t.loads:
            by_kind[l.kind].append(l.total)
for k in KINDS:
    if by_kind[k]:
        print(f'  load, {k:<14} {stats(by_kind[k])}')
waits = [w for b in binaries for t in b.tests.values() for w, _ in t.copies]
copies = [c for b in binaries for t in b.tests.values() for _, c in t.copies]
wi = next((b for b in binaries if 'wi_tests' in b.name), None)
if copies:
    print(f'  copy of the base     {stats(copies)}')
    print(f'  wait for a base      {stats(waits)}')
else:
    print('  copy of the base     NOT TRACED: no `base_copy` line in this log (columns `copy` and `wait` above are 0)')
if wi and wi.wall:
    n = sum(t.base_asks for t in wi.tests.values())
    cs = [c for t in wi.tests.values() for _, c in t.copies]
    said = f'{n} copies in {wi.wall:.0f} s = {n / wi.wall:.1f} a second asked'
    if cs:
        said += f'; one lock gives {1 / (sum(cs) / len(cs)):.0f} a second at the mean copy'
    print(f'  wi_tests: {said}')


def phase_table(title, loads):
    acc = Counter()
    for l in loads:
        for label, s in l.phases:
            acc[label] += s
    total = sum(acc.values())
    print()
    print(f'== {title}: {len(loads)} loads, {total:.1f} thread-s, {1000 * total / max(1, len(loads)):.1f} ms a load ==')
    shown = 0
    rest = 0.0
    for label, s in acc.most_common():
        if shown < 22:
            print(f'  {pct(s, total)}  {s:9.1f} s  {1000 * s / max(1, len(loads)):7.2f} ms/load  {label}')
            shown += 1
        else:
            rest += s
    if rest:
        print(f'  {pct(rest, total)}  {rest:9.1f} s  {1000 * rest / max(1, len(loads)):7.2f} ms/load  the other {len(acc) - shown} phases')


every = [l for b in binaries for t in b.tests.values() for l in t.loads]
phase_table('4a. phases of a load ON THE BASE (the user\'s files into a copy)', [l for l in every if l.kind == 'on-base'])
phase_table('4b. phases of a load that carries the stdlib', [l for l in every if l.kind in ('base-build', 'stdlib-alone', 'one-shot+user')])
phase_table('4c. phases of the other later loads', [l for l in every if l.kind in ('later-other', 'two-step-2nd', 'unknown')])

print()
print('== 5. loads per test (integration binaries; a test with no trace line has none) ==')
for b in binaries:
    ran = b.passed + b.failed
    if not ran:
        continue
    with_loads = [t for t in b.tests.values() if t.loads or t.base_asks]
    d = Counter(min(len(t.loads), 4) for t in with_loads)
    none = ran - len(with_loads)
    loads = sum(len(t.loads) for t in b.tests.values())
    print(f'  {b.name:<32} tests {ran:>5}: no load or copy {none:>5}; copy only {d[0]:>4}; 1 load {d[1]:>5}; 2 {d[2]:>4}; 3 {d[3]:>4}; 4+ {d[4]:>4}'
          f'   loads/test {loads / ran:.2f}')

print()
print('== 6. the loads that still carry the stdlib, by test file (module), most thread-time first ==')
mods = defaultdict(lambda: [0, 0.0, Counter()])
for b in binaries:
    for t in b.tests.values():
        parts = t.name.split('::')
        short = b.name.replace('tests/', '').replace('.rs', '')
        # a binary that aggregates include files names a test `<file>::<test>`
        key = f'{short}::{parts[0]}' if len(parts) > 1 else short
        for l in t.loads:
            if l.kind in ('stdlib-alone', 'one-shot+user'):
                mods[key][0] += 1
                mods[key][1] += l.total
                mods[key][2][l.kind] += 1
rows = sorted(mods.items(), key=lambda kv: -kv[1][1])
tot_n = sum(v[0] for _, v in rows)
tot_s = sum(v[1] for _, v in rows)
print(f'  {tot_n} such loads in {len(rows)} test files, {tot_s:.1f} thread-s (the base builds are not among them)')
for key, (n, s, kinds) in rows[:40]:
    print(f'  {s:8.1f} s  {n:>5} loads  ({kinds["stdlib-alone"]} alone, {kinds["one-shot+user"]} with a user file)  {key}')
if len(rows) > 40:
    n = sum(v[0] for _, v in rows[40:])
    s = sum(v[1] for _, v in rows[40:])
    print(f'  {s:8.1f} s  {n:>5} loads  in the other {len(rows) - 40} files')

print()
print('== 7. the 25 tests with the most traced load time ==')
tests = []
for b in binaries:
    for t in b.tests.values():
        s = sum(l.total for l in t.loads) + sum(w + c for w, c in t.copies)
        if s:
            tests.append((s, len(t.loads), Counter(l.kind for l in t.loads), b.name, t.name))
tests.sort(reverse=True)
for s, n, kinds, bname, tname in tests[:25]:
    k = ', '.join(f'{v} {k}' for k, v in kinds.most_common())
    print(f'  {s:7.2f} s  {n:>4} loads ({k})  {tname}')
