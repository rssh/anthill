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

#### Re-measured 2026-08-06 — the rise is real, the breach was not a step

§4 q4 asked whether W31's 1.04 was signal or noise. It was signal, but not a level shift: W32
comes in **below 1 and above every prior block**. The trend line, not the breach, is the finding.

| block | closed | spinoffs | **b** | 1/(1−b) |
|---|---|---|---|---|
| W20–W23 | 163 | 73 | 0.45 | 1.8 |
| W24–W27 | 284 | 146 | 0.51 | 2.0 |
| W28–W31 | 281 | 196 | 0.70 | 3.3 |
| W31 alone | 74 | 77 | 1.04 | — |
| **W32 (Aug 3–6, partial)** | **60** | **53** | **0.88** | **8.3** |

Lifetime now: 921 close events, 592 co-filed → **b = 0.643** (was 0.63).

The four blocks above W32 reproduce the 2026-08-02 figures exactly, so the series is comparable and
the re-run is a continuation rather than a second method. Per day, W32 is noisy around a high mean —
Aug 3 **1.12**, Aug 4 0.65, Aug 5 **1.00**, Aug 6 0.71 — which is what a process sitting near
criticality looks like: individual days breach, the window does not. At b=0.88 each ticket implies
**8.3** descendants, against 3.3 one block earlier. The gate in §1 is further away than it was, and
the marginal cost of the drift is now steep: b=0.90 gives 10, b=0.95 gives 20.

**b DOES NOT DISTINGUISH A SPINOFF FIXED THE SAME HOUR FROM ONE PARKED FOR A MONTH**, and that gap
matters more as b rises. It counts filings against closures in a window; a follow-up filed and
delivered in the same session still lands in the numerator, exactly like one that joins the parked
set. A delivery that finds three neighbours and *fixes* them scores b=3.0 for that commit if the
three are filed first, and b=0 if they are simply fixed — same work, same day, same code. So b as
defined measures **filing behaviour**, not accumulating debt; §3.4's 82–94% absorption is what says
the debt is not accumulating. Pairing b with a median time-to-close for spinoffs would separate the
two, and is the cheaper half of §4 q3's "how would we tell the difference".

**A worked example, from the delivery that prompted this re-measurement (WI-1028, 2026-08-06).**
Converting the loader's scope spine to `ScopeId` required reading every scope-carrying site. That
reading surfaced three defects — a predicate reading a constructor flag through a term encoding, an
ambiguous `requires` base standing the absolute rung up as if the ambiguity were a miss, and a
per-member symbol re-derivation. **None was created by the ticket; all three were already true, and
the delivery only made them visible.** That is §3.5's mechanism seen from the inside: discovery
scales with how much of the subsystem a change has to read, not with how much it breaks.

The filings, though, were not forced by that. Two of the three fixes were 6 and ~8 lines; the third
turned out to be **no fix at all** (below). Each ticket *description* was longer than its diff. That
suggests a threshold cheaper than judgement:

> **If the ticket text would be longer than the diff, the ticket is the wrong container — fix it.**

It would have caught all three. Note the economics run against the intuition: a ticket good enough
to action later must explain itself to a stranger, so for small items filing costs *more* than
fixing. Two forces push the other way and are worth naming because both are fixable — review is a
**pump** (four agents over one diff returned ~30 findings; whatever is not applied wants somewhere
to go, and "apply" and "file" are not held to the same size test), and for an agent, filing is
defence against losing the finding at end-of-session, which argues for fixing *now* since code is
the durable form. All three closed the same day.

**And the third closed by being MEASURED, which is the outcome a ticket makes least likely.** It was
filed as a perf item: ~750 `format!` + string-keyed `resolve_symbol` per stdlib load, hoistable, and
the reviewer's note said it "dwarfs" everything else in the diff. True and irrelevant — it dwarfed a
smaller negligible thing. Measured in release at n=25: median 0.0411s with the hoist against 0.0397s
without, indistinguishable, and the arithmetic agrees at ~0.4% of a 40ms load. The hoist was written,
measured, and reverted; what landed is a doc comment at the site recording the numbers so the next
reader does not re-derive it from an operation count. A relative comparison between two negligible
costs reads as significance — **"dwarfs X" is only a finding once X is known to matter.** Had this
sat as an open ticket it would have read as pending work indefinitely, since the operation count is
persuasive and nobody re-measures a backlog item.

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

4. ~~**Is W31 signal or noise?**~~ **ANSWERED 2026-08-06 (§3.1).** Signal, but not a level shift: W32
   is 0.88 — below 1, above every prior block. The series is 0.45 → 0.51 → 0.70 → 0.88 and the
   question is no longer "was the breach real" but "what bends the trend". Successor question:
   **should the gate be on b at all, or on b paired with spinoff time-to-close?** b cannot tell a
   follow-up fixed the same hour from one parked for a month (§3.1), and as b rises that is most of
   what one wants to know. Caveat carried forward: W32 is 4 days and partial.

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
- **Fixed data defect (was: `WI-169` names two unrelated items).** The scaland forward-mapping
  spec has been renumbered to `WI-1101`; `WI-169` is now the synth-rule lifetime item alone, which
  is what `kb/execute.rs`, `kb/mod.rs`, `eval_q3_test.rs` and WI-678 all mean by the id. The note
  here used to read "Both Delivered, so nothing is broken today" — the opposite was true, and
  both-Delivered was the thing that broke it: two records in ONE status group collapse to one in
  `chrono_topo`'s id-keyed emit walk, so a listing printed 1088 rows under a `1089 item(s)` footer
  and `show WI-169` answered only the scaland record. `anthill-todo` now refuses any command on a
  store with a duplicate id (`duplicate_item_id`, main.anthill), so this cannot recur silently.
  ID collisions from parallel branches remain a recurring failure mode — cf.
  `renumber the remote's colliding WI-754 follow-up to WI-863` — but they now fail loudly.
