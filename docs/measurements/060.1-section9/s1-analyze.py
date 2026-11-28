#!/usr/bin/env python3
"""060.1 §9 S1 (WI-20261127-DAPCN) — counts from s1-runs.sh OUT: rows per mode, failures by probe tag.

Usage: python3 -I s1-analyze.py OUT   (writes OUT/failed-<mode>.txt: binary, test, tags)"""
import collections
import re
import sys

S = sys.argv[1] if len(sys.argv) > 1 else "."
ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]|\x1b\(B")


def tests(path):
    """{(binary, test): verdict} from a test.sh log."""
    out = {}
    binary = "?"
    try:
        lines = open(path, errors="replace").read().splitlines()
    except FileNotFoundError:
        return None
    for ln in lines:
        ln = ANSI.sub("", ln)
        m = re.search(r"Running (\S+) \(([^)]+)\)", ln)
        if m:
            binary = m.group(2).split("/")[-1].rsplit("-", 1)[0] + ":" + m.group(1)
            continue
        m = re.search(r"\] test (\S+) \.\.\. (ok|FAILED|ignored)", ln)
        if m:
            out[(binary, m.group(1))] = m.group(2)
    return out


def hits(path):
    rows = []
    try:
        for ln in open(path, errors="replace"):
            parts = ln.rstrip("\n").split("\t")
            if len(parts) >= 4:
                rows.append(tuple(parts[:4]))
    except FileNotFoundError:
        pass
    return rows


def summary(mode):
    t = tests(f"{S}/gate-{mode}.log")
    h = hits(f"{S}/hits-{mode}.log")
    print(f"\n######## mode {mode}")
    if t is None:
        print("  (no gate log)")
        return None, h
    c = collections.Counter(t.values())
    totals = [0, 0, 0]
    for ln in open(f"{S}/gate-{mode}.log", errors="replace"):
        m = re.search(r"test result: \w+\. (\d+) passed; (\d+) failed; (\d+) ignored", ANSI.sub("", ln))
        if m:
            totals = [a + int(b) for a, b in zip(totals, m.groups())]
    print(f"  gate: {totals[0]} passed / {totals[1]} failed / {totals[2]} ignored"
          f"  (rows parsed one by one: {dict(c)} — interleaved output drops some `ok` lines)")
    return t, h


def per_tag(h):
    by_tag = collections.defaultdict(lambda: {"tests": set(), "sites": set(), "cli": set()})
    for tag, scope, who, detail in h:
        key = (tag, scope)
        site = re.sub(r"\s+cited@.*$", "", detail)
        if who.startswith("main:"):
            by_tag[key]["cli"].add(who.split(":")[1])
        else:
            by_tag[key]["tests"].add(who)
        by_tag[key]["sites"].add(site)
    return by_tag


def print_tags(h, title):
    print(f"  -- {title}: tag / scope / tests reaching / CLI processes / distinct sites")
    for (tag, scope), v in sorted(per_tag(h).items()):
        print(f"    {tag:40s} {scope:7s} {len(v['tests']):6d} {len(v['cli']):6d} {len(v['sites']):6d}")


base, hlog = summary("log")
if hlog:
    print_tags(hlog, "reach (log mode, nothing refused)")

for mode, prefix in (("load", "L"), ("run", "R")):
    t, h = summary(mode)
    if t is None:
        continue
    failed = sorted(k for k, v in t.items() if v == "FAILED")
    newly = [k for k in failed if base is None or base.get(k) != "FAILED"]
    print(f"  failed: {len(failed)}  (not failing in log mode: {len(newly)})")
    # attribute: which refusing tags did each failed test reach
    reach = collections.defaultdict(set)
    for tag, scope, who, detail in h:
        if tag.startswith(prefix):
            reach[who].add(tag)
    attributed = collections.Counter()
    unattributed = []
    for b, name in newly:
        tags = reach.get(name)
        if tags:
            for tg in tags:
                attributed[tg] += 1
        else:
            unattributed.append((b, name))
    print("  failed tests by the probe tags they reached (a test may count under several):")
    for tg, n in attributed.most_common():
        print(f"    {tg:40s} {n:6d}")
    print(f"  failed with no in-process hit (CLI-spawned, or a fixture in another thread): {len(unattributed)}")
    by_bin = collections.Counter(b for b, _ in unattributed)
    for b, n in by_bin.most_common(12):
        print(f"    {b:70s} {n}")
    by_file = collections.Counter(n.split("::")[0] for _, n in newly)
    print("  failed tests by test module (top 40):")
    for f, n in by_file.most_common(40):
        print(f"    {f:70s} {n}")
    with open(f"{S}/failed-{mode}.txt", "w") as fh:
        for b, n in newly:
            fh.write(f"{b}\t{n}\t{','.join(sorted(reach.get(n, [])))}\n")
