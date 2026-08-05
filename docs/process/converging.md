# Converging — does the base stabilize?

Notes on the ticket-generation dynamics of this project, and the open questions they raise.
Measured 2026-08-02 over `anthill-todo/workitems.anthill` git history. Numbers rot; the method (§5) does not.

## 1. The policy this measures

Work is not started on a parked front (scaland resync, Cell runtime, staging brackets, effect rows)
until the base is stable. 42 pre-June work items sit Open under that rule — deliberately parked, not neglected.

The rule is only safe while the base actually converges. If base work generates work faster than it
retires it, the gate never opens and the parked fronts wait forever. **The branching factor is what
decides that**, and it is the metric this document exists to track.

## 2. Branching factor — the definition

> **b** = tickets *filed in a closing commit* ÷ tickets *closed*, over the same window.

b is a Galton–Watson offspring mean over the spinoff process. Each closed ticket is a parent; the
follow-ups filed alongside its delivery are its children.

- **b < 1** — subcritical. The spinoff tree is finite: one ticket generates **1/(1−b)** descendants
  in total, then the line dies out. The base converges; the gate has a date.
- **b ≥ 1** — critical or supercritical. The tree does not terminate. The base never stabilizes and
  the parking rule becomes self-defeating.

b counts only *co-filed* work. Tickets filed in a commit that closes nothing are **injected** — new
fronts, user filings, review output — and are a choice, not a dynamic. This is why b (0.63 lifetime)
is smaller than raw creation/closure (1.07, §3).

## 3. Measurements (2026-08-02)

### 3.1 b is drifting toward 1

| block | closed | spinoffs | **b** | descendants per ticket, 1/(1−b) |
|---|---|---|---|---|
| W20–W23 | 163 | 73 | **0.45** | 1.8 |
| W24–W27 | 284 | 146 | **0.51** | 2.0 |
| W28–W31 | 281 | 196 | **0.70** | 3.3 |
| W31 alone | 74 | 77 | **1.04** | does not converge |

Lifetime: 861 close events, 539 co-filed → **b = 0.63**.

### 3.2 The multiplier lives in a minority of deliveries

Over 743 commits that closed at least one item:

| spinoffs filed | events |
|---|---|
| 0 | **467 (63%)** |
| ≤1 | 187 |
| 1–2 | 54 |
| 2–4 | 23 |
| >4 | 12 |

Nearly two thirds of deliveries file nothing. The impression of "each closed ticket creates a few"
comes from the 35 high-fanout events, which also write the memorable commit subjects
(`WI-857 delivered; file its follow-ups (WI-864..868)`).

### 3.3 The open count is not a health metric

Open oscillated 126 (Jun 15) → 63 (Jul 15) → 123 (Aug 2) **straight through** the drift from b=0.45
to b=1.04. It reported nothing. Current: 131 Open, 16 PreOpened, 4 Claimed, 781 closed
(743 Delivered + 38 Verified), 3 Rejected, 3 Stale — 938 total.

Creation vs closure W20–W31: 782 created, 728 closed — ratio **1.07**.

### 3.4 Spinoffs are absorbed, not accumulated

Completion by birth cohort — 82–94% of everything filed reaches Delivered/Verified:

```
2026-03  born  38  done  32  (84%)
2026-04  born 110  done  90  (82%)
2026-05  born 203  done 172  (85%)
2026-06  born 247  done 231  (94%)
2026-07  born 310  done 237  (76%)   still in flight
```

Spinoffs are real work that gets done. The backlog is not a leak.

### 3.5 The drift is one subsystem

Of the 114 tickets born W31, description keywords concentrate hard:

```
resolve 40 · carrier 19 · requirement 14 · simp 13 · host 12 · provision 11 · dispatch 11
```

Resolution/dispatch/carrier/requirement is being discovered one delivery at a time. This matches the
recorded failure mode across the WI-8xx/9xx feedback: *the ticket's consumer list missed 2*,
*2 of 4 producers found only by DRIVING*, *the caller list was STALE*. Each delivery measures the
blast radius and finds neighbours the ticket did not know about. At b≈1 that subsystem has enough
unmeasured surface that each measurement finds one more than it retires.

### 3.6 The parked set is five chains with ready heads

42 pre-June Open: **8** blocked by an open dep, **14** with all declared deps closed, **20** with no
`depends_on` at all.

```
WI-020 → WI-021           guard analysis → fast-path pre-checks   (WI-024 tests both)
WI-156 → WI-157 → WI-158  scaland resync: eval → CLI/prove → codegen   [umbrella WI-151]
WI-188 → WI-189 → WI-190  .copy → staging brackets → quasi-quote patterns
WI-207 → WI-208           acyclic_cell typer rule → data-flow discharge
WI-329 → WI-330           handler discharge → migrate typing_pass_spec onto row unification
```

Every head is ready — nothing outside the parked set blocks any chain. What holds them is the
policy in §1, not a dependency.

Four gates are stated in prose only, invisible to the tracker:

| item | prose gate | status |
|---|---|---|
| WI-294 | "gated behind the scaland `Term->Value` resolver migration (mirror of rustland WI-246)" | real prerequisite, no edge |
| WI-128 | "DEFERRED: requires resolver instrumentation to capture a derivation tree" | prerequisite with no ticket |
| WI-266 | "DEFERRED until a concrete driver appears" | **not** a prerequisite — a trigger |
| WI-177 | "after WI-009" | WI-009 is Delivered — stale gate, now free |

## 4. Questions for review

1. **What is "the base", named?** The parking rule in §1 gates on a condition that exists only in our
   heads. Should the base be an explicit ticket set (a tag / umbrella) so b can be measured *within it*
   rather than globally? §3.5 says the global b is currently dominated by one cluster anyway.

2. **Is b < 1 the right gate, and at what value?** b=0.7 converges in principle but implies 3.3
   descendants per ticket. Is the opening condition "b < 1", "b < 0.5", or "b < X sustained for N weeks"?
   Without an answer the gate has no date and the parking rule is unfalsifiable.

3. **Is b actionable, or only diagnostic?** The claim in §3.5 is that a design pass which settles the
   carrier/spec-op keying and requirement-dictionary questions *ahead* of discovery would retire a whole
   generation at once and drop b. Untested. The rival hypothesis is that a design pass only relabels the
   discovery — the same facts get found, in a document instead of a ticket. **How would we tell the
   difference?** A pre-registered prediction (e.g. "b for the resolve cluster falls below 0.4 in the two
   weeks after the pass") is the cheapest test.

4. **Is W31 signal or noise?** One week, 74 closes. The 4-week blocks (0.45 → 0.51 → 0.70) are the robust
   part; b=1.04 is one point. Re-measure before acting on it. Note the last window is also biased low on
   closes — W31-filed tickets that close in W32 are not yet counted.

5. **Encode the four prose gates?** (§3.6) Adding the WI-294 and WI-128 edges makes `next` and the Open
   count honest — they currently report those as ready. Cost is near zero. Objection: WI-128's
   prerequisite has no ticket, so encoding it means filing one, which itself raises the count.

6. **Does the tracker need a "waiting for a trigger" state?** WI-266 is not blocked by anything — it is
   waiting for a *driver* to appear. That is a third state alongside Open and PreOpened, and it is the
   honest label for a good part of the parked set. Or is PreOpened already that, used loosely?

7. **Should b be measured per cluster?** A global b averages a converging subsystem with a diverging one
   and reports neither. §3.5 suggests the interesting b is per-area. Requires an area tag on tickets.

8. **Does the reopen rate matter?** 70 items were closed and later reopened (861 close events vs 779
   closed items). That is a second convergence signal — work that did not stay done — and it is not
   currently in b at all.

## 5. Method (reproduce)

Both series come from ID-set diffs between consecutive commits touching the tracker file, so a status
rewrite is never miscounted as a creation.

```sh
# id -> status, format-agnostic (the file's fact layout changed ~W24;
# take the LAST status token per record, since descriptions quote "status: Open")
cat > /tmp/closed.pl <<'PL'
local $/; my $t = <STDIN>;
for my $r (split /fact WorkItem\(/, $t) {
  next unless $r =~ /id:\s*"(WI-\d+)"/; my $id = $1;
  my @s = ($r =~ /status:\s*(Open|Claimed|Delivered|Verified|Rejected|Stale|PreOpened)/g);
  next unless @s;
  print "$id\n" if $s[-1] eq 'Delivered' or $s[-1] eq 'Verified';
}
PL

# per-commit: ids newly created, ids newly closed
: > /tmp/p1; : > /tmp/p2
git log --format='%H|%ad' --date=short --reverse -- anthill-todo/workitems.anthill |
while IFS='|' read sha date; do
  git show $sha:anthill-todo/workitems.anthill > /tmp/f
  grep -oE 'id: "WI-[0-9]+"' /tmp/f | sort -u > /tmp/a
  perl /tmp/closed.pl < /tmp/f | sort -u > /tmp/b
  echo "$date created=$(comm -13 /tmp/p1 /tmp/a | wc -l) closed=$(comm -13 /tmp/p2 /tmp/b | wc -l)"
  mv /tmp/a /tmp/p1; mv /tmp/b /tmp/p2
done
```

**Caveats, each verified rather than assumed.**

- **b is a proxy.** It attributes every ticket filed in a closing commit to that closure. A follow-up
  filed one commit later reads as injected, not as a spinoff — so b is a lower bound on true fanout.
- **The denominator counts close *events*, not items.** 861 events vs 781 currently-closed items;
  the gap is 70 distinct items that were closed and later reopened, some more than once (measured,
  §4 q8). Re-closures inflate the denominator, which makes b a slight **under**estimate.
- **Do not count `status:` occurrences with grep.** Descriptions quote status values in prose
  (WI-187's text contains `status: Open)` while the item is Delivered), which inflates Open by ~5%.
  Use the last-token-per-record extractor above, or `anthill-todo list --status X`.
- **`anthill-todo list` output embeds WI references in descriptions.** Anchor on the
  `^  WI-NNN [Status]` line prefix, not a bare `WI-[0-9]+` match, or the count roughly triples.
- **Known data defect:** `WI-169` names two unrelated items (`workitems.anthill:1069` scaland
  forward-mapping spec; `:3298` synth-rule lifetime). Both Delivered, so nothing is broken today.
  ID collisions from parallel branches are a recurring failure mode — cf.
  `renumber the remote's colliding WI-754 follow-up to WI-863`.
