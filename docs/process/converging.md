# Converging — does the base stabilize?

Notes on the ticket-generation dynamics of this project, and the open questions they raise.
A running series, measured 2026-08-02 and re-measured 2026-08-06 and 2026-09-02 over the
`anthill-todo` tracker's git history. Each sitting appends rather than overwrites, so the drift is
readable. Numbers rot — and so did the method: the tracker changed layout on 2026-08-17, §5 has been
rewritten to span both regimes, and the 2026-08-02 recipe now produces a wrong answer *silently*.

## 1. The policy this measures

Work is not started on a parked front (scaland resync, Cell runtime, staging brackets, effect rows)
until the base is stable. 42 pre-June work items sat Open under that rule on 2026-08-02 — deliberately
parked, not neglected — and 47 do on 2026-09-02 (§3.6 for why those two are on different definitions).

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
fronts, user filings, review output — and are a choice, not a dynamic. This is why b (0.64 lifetime)
is smaller than raw creation/closure (1.07, §3 — a ratio that has not moved across the whole series).

## 3. Measurements (2026-08-02, re-measured 2026-08-06 and 2026-09-02)

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

#### Re-measured 2026-09-02 — the trend bent, and b stopped being the interesting number

§4 q4's successor asked what bends the trend. It bent. The four-week block **fell for the first time
in the series**, to a value it has not held since W24–W27.

| block | closed | spinoffs | **b** | 1/(1−b) |
|---|---|---|---|---|
| W20–W23 | 163 | 73 | 0.45 | 1.8 |
| W24–W27 | 284 | 146 | 0.51 | 2.0 |
| W28–W31 | 281 | 196 | 0.70 | 3.3 |
| W31 alone | 74 | 77 | 1.04 | — |
| W32 | 115 | 87 | 0.76 | 4.1 |
| W33 | 109 | 48 | 0.44 | 1.8 |
| W34 | 87 | 38 | 0.44 | 1.8 |
| W35 | 82 | 79 | 0.96 | 27 |
| W36 (Aug 31–Sep 2, 3 days) | 20 | 23 | 1.15 | — |
| **W32–W35 (four full weeks)** | **393** | **252** | **0.64** | **2.8** |

Lifetime now: 1275 close events, 815 co-filed → **b = 0.639** (0.643 on Aug 6, 0.63 on Aug 2). The new
month came in almost exactly at the lifetime average, so the lifetime figure barely moved; the *block*
series is where the change is.

The series is one series across three sittings and one tracker-format change: W20–W31 reproduce to the
digit, and both prior lifetime checkpoints reproduce to within a commit-day — 862/540 at Aug 2 against
the recorded 861/539, and 933/598 at Aug 6 against 921/592, that one having been taken mid-day. The
W32 row moved only because it is now a *full* week: Aug 3–6 alone is 71/58, and 60/53 was recorded from
a partial snapshot. Neither reading is 0.88; the week closed at 0.76.

**Time-to-close moved sharply. The threshold rule does not get the credit.** §3.1 proposed on Aug 6:
*if the ticket text would be longer than the diff, the ticket is the wrong container — fix it.* b
cannot see that rule at all — a same-hour fix, filed first, still lands in the numerator — which is
exactly the blindness recorded above in capitals. Pairing b with a spinoff time-to-close was named
there as the cheaper half of §4 q3's test. Measured, with injected tickets carried alongside as the
control, since the rule is about *spinoffs* and should move them and not the others:

| born | spinoff n / closed | same-day | ≤7d | injected n / closed | same-day | ≤7d |
|---|---|---|---|---|---|---|
| through Jun | 292 / 255 | 60% | 78% | 306 / 275 | 35% | 69% |
| Jul | 183 / 163 | 60% | 88% | 127 / 109 | 45% | 87% |
| Aug 1–6 | 83 / 74 | 69% | 92% | 34 / 28 | 64% | 86% |
| **Aug 7–31** | **144 / 113** | **72%** | **100%** | **107 / 69** | **58%** | **99%** |
| Sep 1–2 | 20 / 10 | 80% | 100% | 3 / 1 | 100% | 100% |

Every spinoff born after the rule was written that has closed at all closed **inside a week**, against
78% over the project's first four months. That is the largest single movement anywhere in this
document, and b reports none of it.

**But the control refutes the attribution.** Against their own baselines, injected tickets moved
*further* than spinoffs on both measures and in every cohort — same-day +23pp against +11pp, ≤7d
+29pp against +22pp — and the injected acceleration starts in **July, a month before the rule was
written**. If the rule were doing the work, the population it names would have moved more than the
population it does not name, and the move would begin in August. Neither holds. Something broader
changed how fast anything filed gets closed, and this measurement cannot say what; the honest reading
is that the rule is confounded with it, not that the rule did nothing.

**What survives is the instrument, and the gate.** b has swung between 0.44 and 1.15 week to week all
summer while the thing it stands in for — whether follow-ups accumulate — went from "most within a
week" to "all within a week". Whatever the cause, the follow-up set is not accumulating, and §1's gate
is about accumulation. The honest gate is a pair, and it is the second element that moved.

Two things weaken even that. The ≤7d figures are over *closers only*: 22% of the Aug 7–31 spinoff
cohort is still open, and every one of them will land outside a week, so 100% will fall — though the
earlier rows are the ones at 78% and 88% and they have had their tails. And a project whose sessions
close what they file within a day will show this pattern whether or not debt is accumulating
elsewhere; the parked set (§3.6) is exactly where it would hide, and it did not move either.

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

**2026-09-02.** The table above does not reproduce under the current pathspec: its total (743 closing
events) does, but its buckets do not, because the 2026-08-02 recipe followed only
`anthill-todo/workitems.anthill` while this one follows `anthill-todo/`. The deltas below are
therefore stated against a **recomputation of the same baseline window with the same method**, not
against the table above.

| spinoffs filed | through Aug 2 | Aug 3 – Sep 2 |
|---|---|---|
| 0 | 466 (62.7%) | 191 (55.8%) |
| 1 | 177 (23.8%) | 85 (24.9%) |
| 2 | 51 (6.9%) | 35 (10.2%) |
| 3–4 | 28 (3.8%) | 24 (7.0%) |
| >4 | 21 (2.8%) | 7 (2.0%) |
| **closing events** | **743** | **342** |

Zero-fanout deliveries 62.7% → **55.8%**; three-or-more 6.6% → **9.1%**; but the extreme tail shrank,
`>4` spinoffs 2.8% → **2.0%**. More deliveries file something; fewer file a pile. Set beside §3.1's
time-to-close, what changed is not whether a follow-up gets written down but how long it stays
written down.

### 3.3 The open count is not a health metric

Open oscillated 126 (Jun 15) → 63 (Jul 15) → 123 (Aug 2) **straight through** the drift from b=0.45
to b=1.04. It reported nothing. Current: 131 Open, 16 PreOpened, 4 Claimed, 781 closed
(743 Delivered + 38 Verified), 3 Rejected, 3 Stale — 938 total.

Creation vs closure W20–W31: 782 created, 728 closed — ratio **1.07**.

**2026-09-02.** Open 123 → **164**, PreOpened 16 → **22**, closed 781 → **1097** (1059 Delivered +
38 Verified), plus 8 Rejected, 2 ProposalRejected, 3 Stale, 2 Claimed — **1298** total. Open rose 33%
across the very month in which b *fell*. That is the same non-signal as before, with the sign flipped,
which is stronger evidence than the original observation: the count now moves against b, not merely
independently of it.

Creation vs closure W32–W36: 440 created, 413 closed — ratio **1.07**, identical to W20–W31's 1.07 to
two digits. That ratio has not moved all summer and is not a gate either.

Both sides of that ratio are **event** counts, not distinct items, and the two are far apart on the
creation side: the 440 creation events in that window are **361 distinct tickets**, because a branchy
history lets an id leave and re-enter the id set (111 ids across the whole series are "born" more than
once). The ratio is still meaningful — it compares events with events — but the number must not be
reused as a ticket population. §3.5 uses 361.

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

**2026-09-02**, by git-observed birth month (not the backfilled `created:` field — see §5):

```
2026-03  born  38  done  32  (84%)
2026-04  born 110  done  90  (82%)
2026-05  born 203  done 175  (86%)
2026-06  born 247  done 233  (94%)
2026-07  born 310  done 272  (88%)   was 76% a month ago
2026-08  born 368  done 284  (77%)   still in flight
2026-09  born  23  done  11  (48%)   two days old
```

July went 76% → 88% in the month, landing where June sat one measurement ago. The absorption claim
survives a second look on a cohort that has now had time to fail: nothing is leaking.

The born column sums to 1299 against the 1298 of §3.3 and §5. The extra one is **WI-647**, created
during the proposal-053 equality/ordering split and later removed from the tracker: it was born in
git, so the birth-keyed series counts it, and it is not in any status directory today, so the status
census does not. Distinct births, not creation events — see §3.3.

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

**2026-09-02 — the cluster did not retire, but two of its questions did.** Share of ticket
*descriptions* mentioning each term, over **distinct** births: W31 (n=114 — the same 114 the block
above counts) against Aug 3 – Sep 2 (n=361). Creation events would give 123 and 440 and would
double-count 9 and 79 tickets respectively; see §3.3.

| term | W31 | Aug 3–Sep 2 | shift |
|---|---|---|---|
| scope | 44.7% | 42.1% | −2.6 |
| carrier | 36.0% | 32.4% | −3.6 |
| resolve | 22.8% | 27.4% | +4.6 |
| dispatch | 21.1% | 20.8% | −0.3 |
| requirement | 10.5% | 10.0% | −0.6 |
| **simp** | **17.5%** | **6.4%** | **−11.2** |
| **host** | **23.7%** | **15.5%** | **−8.2** |
| effect | 7.0% | 18.3% | +11.3 |
| typer | 13.2% | 23.5% | +10.4 |
| label | 4.4% | 11.6% | +7.2 |
| proof | 1.8% | 7.8% | +6.0 |
| arrow | 2.6% | 7.2% | +4.6 |
| tuple | 2.6% | 6.6% | +4.0 |

Carrier, scope, dispatch and requirement are **flat within a few points** — four weeks and 413
closures did not measurably shrink their share of new work, and `resolve` actually rose. What fell is
`simp`, by two thirds once WI-881/884/888 settled what `[simp]` admits and what makes a defining
equation fire, and `host`, by a third. Against them a new front — effect rows, the typer, proof
passes, and the label/arrow/tuple group — rose by more than the two gave up.

**This is the natural experiment §4 q3 asked for, and it splits the answer.** Settling a question
*does* retire its generation: `simp` was one ticket in six and is now one in sixteen, with no delivery
campaign aimed at the backlog — answering the question retired the tickets rather than closing them.
`host`'s fall is a second, weaker instance with no single settling commit to point at.
But global b did not fall in response, because the freed capacity went straight into the next front.
A design pass is therefore actionable **per cluster** and invisible **globally**, which promotes §4 q7
from a suggestion to a finding: a global b averages a retiring subsystem with an opening one and
reports neither.

The caution is that this is one observation, not a controlled test, and the direction of causation is
assumed rather than shown — `simp` work might have run out for reasons unrelated to the settlement.
The pre-registered prediction §4 q3 asks for is still unmade; the next front (effects/typer/proofs) is
the place to make it, *before* the pass rather than after.

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

**2026-09-02.** On a definition the whole series can share — git-observed birth before June, status
Open or PreOpened — the parked set was **50** on Aug 2 and is **47** today. Three retired in a month.
The policy in §1 is holding it roughly steady, as intended. (The "42" above used the tracker's own
status listing and is not comparable; the old single-file format carried no birth date at all, so the
only age the whole series can agree on is the git-observed one. See §5.)

**One** of the four prose gates resolved itself without the tracker's help:

- **WI-266** — "DEFERRED until a concrete driver appears" — **Delivered 2026-08-15.** A driver
  appeared. This was the one item the tracker structurally could not schedule, and it closed anyway,
  which weakens rather than strengthens the case for a "waiting for a trigger" state (§4 q6).
- **WI-294** and **WI-128** are still Open with their prerequisites still stated in prose only.

Separately, in the *tracked* chains above — a different population, the one the prose gates are
contrasted with — **WI-329** (handler discharge) is Delivered, so **WI-330** is a free head and that
chain shortened by one instead of moving.
- **WI-177** still carries no `depends_on`, so its stale "after WI-009" gate is still invisible and
  still stale. §4 q5 has now been open across two re-measurements at "cost is near zero", which is
  itself the finding: a near-zero-cost fix that does not get done is not being priced correctly.

### 3.7 Code size — the tickets are producing prose faster than code

Added 2026-09-02, from the question *is code size changing, given that no new functionality is meant
to be going in beyond one example written for an article?* It is changing, substantially, and the
composition of the change is the answer.

`rustland` Rust by line kind. Test lines are test *files* plus brace-matched `#[cfg(test)]` blocks —
matching on the first `#[cfg(test)]` and running to EOF gets this badly wrong, because `typing.rs`
declares `#[cfg(test)] mod tests;` on line 31 and would charge its whole 69k-line body to tests.

| | Jun 7 | Jul 5 | Aug 2 | Aug 16 | Sep 2 |
|---|---|---|---|---|---|
| production code | 46,924 | 60,215 | 75,795 | 98,032 | **115,506** |
| production doc-comment | 10,231 | 16,430 | 29,492 | 41,792 | **53,607** |
| production `//` comment | 6,586 | 11,934 | 19,593 | 26,334 | **34,694** |
| test code | 40,540 | 66,177 | 104,238 | 147,195 | **185,964** |
| test doc + comment | 7,247 | 14,016 | 29,442 | 47,701 | **72,047** |
| blank (both) | 9,672 | 12,997 | 18,370 | 21,609 | **26,230** |
| **all rustland Rust** | 121,200 | 181,769 | 276,930 | 382,663 | **488,048** |

Deleted lines run at **7.8%–27.0%** of added lines across all Rust, week by week since June, median
15.1% — one earlier week (May 11–17, the first measured) reaches 40.1%. The work is **additive, not
rework**: there is no week in which the tree shrank, and no week in which deletions reach a third of
additions, so "not adding functionality" is not a description of what the diffs do. Separated by path
below, production files alone sit at 20–27% and test files at 3–15%.

Normalized against the thing that is supposed to be driving it:

| window | closes | prod code /ticket | prod prose /ticket | test code /ticket |
|---|---|---|---|---|
| Jun 7 → Jul 5 | 284 | 47 | 41 | 90 |
| Jul 5 → Aug 2 | 281 | 55 | 74 | 135 |
| Aug 2 → Aug 16 | 224 | **99** | 85 | 192 |
| Aug 16 → Sep 2 | 189 | **92** | **107** | 205 |

Production *code* per closed ticket roughly doubled between July and August and has now flattened
(99 → 92) for the first time in the series. Production *prose* per closed ticket has not flattened; at
107 lines per ticket it now **exceeds the code**, and it is the fastest-growing category in the tree.
Of the 80,476 production lines added Aug 2 → Sep 2, **49% are comments and doc-comments**, and prose
is 42% of all production lines against 37% a month ago.

That is the localized-invariant discipline showing up as mass — CLAUDE.md's "each stated in
`docs/kernel-language.md` and enforced by a doc-commented site". It is not new functionality; it is
recorded reasoning *about* existing functionality. But it is growing faster than the functionality,
which is a claim worth holding to account: prose that outgrows its subject is either the reason the
spinoff time-to-close collapsed (§3.1) or the next thing that will need retiring.

**The article example is visible in the numbers, and it was not free.** `examples/guardians` did not
exist on Aug 2 and is 5,803 lines on Sep 2, all of it since Aug 22. Its first commit subject reads
`guardians: an agent the kernel checks before it runs, and the result-binder fix that writing it
needed` — so writing an example *in* the language changed the kernel. **5,803 of the +5,887 in
`examples/` is guardians**; the remaining 84 lines are small edits to two existing examples
(`github-todo` 2,078→2,108, `webots-modelling` 3,112→3,166) and two that did not move at all
(`classic-mini` 403→403, `sql-store` 226→226). "It uses the
language, not something new" is the intent; the measurement says that using it found a defect, which
is §3.5's mechanism — discovery scales with how much of the subsystem a change has to read — applied
to an example instead of a delivery.

**Is the new code addition or rework?** Asked directly, since a project whose tickets are mostly
corrections should be rewriting more and appending less. It is not. Deleted lines against added lines,
`rustland` Rust, by path (test-path files against everything else — inline `#[cfg(test)]` blocks count
on the src side here, which biases the src column *toward* looking like rework):

| window | src added | src deleted | del/add | test added | test deleted | del/add |
|---|---|---|---|---|---|---|
| Jun | 41,177 | 9,470 | 23.0% | 34,324 | 2,098 | 6.1% |
| Jul | 60,887 | 16,371 | 26.9% | 55,403 | 1,608 | 2.9% |
| Aug 1–16 | 64,806 | 14,748 | 22.8% | 73,759 | 11,222 | 15.2% |
| Aug 16 – Sep 2 | 46,445 | 9,537 | **20.5%** | 71,266 | 2,789 | 3.9% |

**The ratio is flat and if anything falling** — 23% → 27% → 23% → 20.5%. Four to five lines are added
for every one replaced, and that has not changed in four months. Over Aug 2 → Sep 2 the deletions
amount to **13.1%** of the src-path tree that existed on Aug 2 (19,453 against 148,640), in a month
when that tree grew **57%** to 233,560.

Those stock figures are counted with the *same* path classifier as the churn above, and the net
reconciles exactly — 148,640 + 84,920 = 233,560, and 128,290 + 126,198 = 254,488 on the test side.
That check matters: the natural mistake here is to divide src-*path* churn by §3.7's production-line
stock, which excludes inline `#[cfg(test)]` blocks that the path classifier keeps. The two
denominators differ by ~18,000 lines and give 14.8% / 65% instead of 13.1% / 57%.

Split another way over the same month: 11 new src files contributed 9,601 lines of pure addition,
while 82 existing files took +94,772/−19,085. So the growth is mostly *inside* existing files, but it
is growth, not replacement. Per closed ticket: **253 src lines added, 47 deleted, 339 test lines
added, 33 deleted.**

The conclusion is uncomfortable and worth stating plainly: tickets that read as corrections are
producing net-new production code at a steady 4:1 ratio.

**Control-flow surface, to tell "uncovering missing behaviour" from "accreting alternatives".** Lines
are a weak proxy; declarations and branches are not. Counted in production code only — test files and
brace-matched `#[cfg(test)]` blocks excluded, comment and blank lines excluded, so the `code` column
reconciles exactly with §3.7's production-code row:

| | Jun 7 | Jul 5 | Aug 2 | Sep 2 | Aug 2 → Sep 2 |
|---|---|---|---|---|---|
| code lines | 46,924 | 60,215 | 75,795 | 115,506 | **+52.4%** |
| `fn` | 2,222 | 2,791 | 3,522 | 4,614 | +31.0% |
| `pub fn` | 692 | 846 | 1,087 | 1,385 | +27.4% |
| match arms (`=>`) | 4,732 | 5,980 | 6,999 | 8,605 | +22.9% |
| `if` / `else if` | 2,212 | 3,021 | 3,633 | 4,782 | +31.6% |
| `struct` / `enum` decls | 329 | 369 | 476 | 642 | +34.9% |
| **lines per `fn`** | 21.1 | 21.6 | 21.5 | **25.0** | +16% |
| **lines per match arm** | 9.9 | 10.1 | 10.8 | **13.4** | +24% |

Both readings are partly right, and the split is legible. **The implementation is still growing real
surface** — 1,092 new functions, 298 new public functions and 166 new type declarations in a single
month is not what a codebase in correction mode does. But surface grew at 23–35% against 52% for
lines, and lines-per-`fn` broke a two-month flat line (21.1 → 21.6 → 21.5 → 25.0). So the *last month
specifically* added more length per decision point than any earlier window: the marginal line is
increasingly not a new branch.

That is the shape of a system whose behaviour is roughly settled and whose *explanation* is not —
consistent with §3.7's prose finding and with §3.5, where the settled question (`simp`) retired its
tickets while the unsettled ones (carrier, scope, resolve, dispatch) did not move at all. **"The
language is specified" is defensible; "the implementation has stopped growing" is not.**

### 3.8 Test execution time on this machine

Local, machine-specific, and not in git: `rustland/scripts/test.sh` prefixes every line with elapsed
seconds and keeps a log per run under `rustland/target/`. There are **9,050 dated runs from 2026-05-16
to 2026-09-02** sitting there, which is a wall-clock series nobody had read. Machine: WSL2, Intel Core
Ultra 9 275HX, 24 cores, 15 GB. `test.sh` runs compute-bound crates at 24 threads and the two
subprocess-spawning crates (`anthill-cli`, `anthill-todo`) at 12.

Per day, the fullest run of that day — the one with the most tests passed:

| date | tests | wall clock | ms/test | test binaries |
|---|---|---|---|---|
| 2026-05-20 | 1,163 | 0:24 | 21 | 46 |
| 2026-05-31 | 1,369 | 0:35 | 26 | 46 |
| 2026-06-07 | 1,556 | 0:42 | 27 | 48 |
| 2026-06-14 | 1,798 | 2:05 | 70 | 54 |
| 2026-06-21 | 2,211 | 2:21 | 64 | 61 |
| 2026-07-05 | 2,535 | 2:58 | 70 | 67 |
| 2026-07-19 | 3,139 | 2:54 | 55 | 84 |
| 2026-08-02 | 4,065 | 4:01 | 59 | 95 |
| 2026-08-09 | 4,458 | 3:50 | 52 | **35** |
| 2026-08-16 | 4,976 | 6:06 | 74 | 35 |
| 2026-08-23 | 5,645 | 7:41 | 82 | 36 |
| 2026-08-30 | 6,209 | 9:46 | 94 | 36 |
| **2026-09-02** | **6,339** | **10:13** | **97** | 36 |

**Tests grew 5.5×; wall clock grew 25×.** Cost per test went 21 ms → 97 ms, a 4.7× rise, so the suite
is not merely bigger — each test is slower. The stdlib every test loads grew from 3,457 to 8,619 lines
over the same window, which is a candidate explanation and is **not** established here; §3.1's
measured 40 ms stdlib load is the number to re-take.

Fitted over the last eight weeks the wall clock **doubles every 32 days**. Extrapolating the current
rate: 20 minutes in about a month, 30 minutes in seven weeks, an hour by late November. Nothing in
the series so far has bent that curve — note the binary-count drop from 95 to 35 around Aug 5–6, when
tests were consolidated into shared `tests/include/` binaries: it removed 60 link steps and saved no
measurable wall clock, so link time was not the cost.

This matters to §1 directly. Every measurement in this document is taken by someone who ran the suite,
and the local convention is to run it before every commit. At 413 closes a month and ten minutes a
run, the suite is now a material fraction of the working day, and it is the one series here with a
clean exponential fit and no sign of bending.

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

   **PARTLY ANSWERED 2026-09-02 (§3.5).** Actionable per cluster, invisible globally. `simp` fell from
   16.3% to 6.1% of new ticket descriptions after WI-881/884/888 settled what `[simp]` admits — no
   delivery campaign, the answer retired the tickets — while the global b did not respond, because the
   freed capacity moved into effects/typer/proofs. The rival hypothesis is not excluded: this is one
   uncontrolled observation and `simp` work may simply have run out. **The pre-registered prediction is
   still unmade, and the effects/typer/proof front is the place to make it, before the pass.**

4. ~~**Is W31 signal or noise?**~~ **ANSWERED 2026-08-06 (§3.1).** Signal, but not a level shift: W32
   is 0.88 — below 1, above every prior block. The series is 0.45 → 0.51 → 0.70 → 0.88 and the
   question is no longer "was the breach real" but "what bends the trend". Successor question:
   **should the gate be on b at all, or on b paired with spinoff time-to-close?** b cannot tell a
   follow-up fixed the same hour from one parked for a month (§3.1), and as b rises that is most of
   what one wants to know. Caveat carried forward: W32 is 4 days and partial.

   **SUCCESSOR ANSWERED 2026-09-02 (§3.1).** The gate should not be on b alone. b bent down (0.70 →
   0.64 over four full weeks) but has swung 0.44–1.15 week to week, while the paired metric moved
   monotonically and far: spinoffs closing within 7 days went 78% → 88% → 92% → **100%** across the
   four birth cohorts. b measured filing behaviour, as §3.1 said it did; time-to-close measures the
   thing the gate is actually about. Two successors, and the second is the sharper one:

   (a) **What is the closing condition on the pair, and does §1's parking rule open on it today?** A
   defensible reading is "b < 1 sustained over four weeks AND ≥90% of spinoffs closing within 7 days",
   which the last four weeks satisfy. If that is the gate, it is open, and the parked fronts in §3.6
   need a start date rather than a fourth measurement.

   (b) **What actually accelerated closure?** The control failed: injected tickets moved *further*
   than spinoffs and started moving in July, before the threshold rule existed (§3.1). So the pair's
   second element improved for a reason this document has not identified, and a gate opened on an
   unexplained improvement is a gate that can close again without warning. This is the cheapest thing
   left to measure and the most load-bearing.

5. **Encode the four prose gates?** (§3.6) Adding the WI-294 and WI-128 edges makes `next` and the Open
   count honest — they currently report those as ready. Cost is near zero. Objection: WI-128's
   prerequisite has no ticket, so encoding it means filing one, which itself raises the count.

   **STILL OPEN across two re-measurements 2026-09-02 (§3.6).** WI-294, WI-128 and WI-177 are all
   unchanged; WI-177's gate names a Delivered item and has been stale for a month with `depends_on`
   still empty. A near-zero-cost fix that survives two measurement cycles is not being priced right —
   either the cost is not near zero, or the honesty of `next` is not actually wanted.

6. **Does the tracker need a "waiting for a trigger" state?** WI-266 is not blocked by anything — it is
   waiting for a *driver* to appear. That is a third state alongside Open and PreOpened, and it is the
   honest label for a good part of the parked set. Or is PreOpened already that, used loosely?

   **WEAKENED 2026-09-02 (§3.6).** WI-266 was Delivered on 2026-08-15 — the driver appeared. The one
   item that motivated the state closed without it, so the state would have bought nothing here.

7. **Should b be measured per cluster?** A global b averages a converging subsystem with a diverging one
   and reports neither. §3.5 suggests the interesting b is per-area. Requires an area tag on tickets.

   **PROMOTED TO A FINDING 2026-09-02 (§3.5).** No longer a suggestion: over Aug 3 – Sep 2 the global b
   was flat *while* one cluster retired by two thirds and another grew by the same amount. The global
   number averaged them and reported neither. The blocker is unchanged — it needs an area tag.

8. **Does the reopen rate matter?** 70 items were closed and later reopened (861 close events vs 779
   closed items). That is a second convergence signal — work that did not stay done — and it is not
   currently in b at all.

   **THE INSTRUMENT CANNOT ANSWER THIS 2026-09-02.** Now 1275 close events against 1098 distinct
   items ever closed: 126 items with more than one close, 177 excess events, apparently up from 9.5%
   to 13.9% of all closes. But the measurement is an id-set diff over a branchy history, and the
   closed set *shrank* on 5% of commits in the new window against 2% before — tracking a rise in merge
   density (5.5% of commits against 3.8%), not necessarily work undone. A branch merged out of order
   looks exactly like a reopen. **Answering q8 needs a status-transition log the tracker does not
   keep**, which is a concrete, small feature request rather than another measurement.

9. **Is prose outgrowing code a convergence signal or the next debt?** (§3.7, new.) Production prose is
   now 107 lines per closed ticket against 92 lines of code, and 42% of all production lines. The
   optimistic reading is that it is why spinoff time-to-close collapsed — the invariants are written
   where the next reader trips over them. The pessimistic reading is that it is unmeasured, unversioned
   duplication of `docs/kernel-language.md` that will need its own retirement pass. Nothing here
   distinguishes them. What would: whether a doc-commented site is *cited* by a later ticket.

10. **Should code size be a tracked series at all?** It is now (§3.7), and it immediately contradicted
    a working assumption — 80,476 production lines added in a month under a "no new functionality"
    intent, with deletions at 8–15% of additions every week. The number worth watching is probably not
    total size but production code per closed ticket, which flattened this month for the first time.

11. ~~**Are the corrections adding behaviour or replacing it?**~~ **ANSWERED 2026-09-02 (§3.7).**
    Adding. The delete/add ratio in production files is flat at 20–27% across four months, and the
    month added 1,092 functions and 166 type declarations. But control-flow surface grew at 23–35%
    against 52% for lines, and lines per `fn` broke a two-month flat line — so the growth is
    increasingly *length per decision*, not new decisions. Successor: **which subsystem is the
    lines-per-`fn` rise in?** If it is the four unsettled clusters of §3.5, it is the cost of
    working around an unanswered question, and settling the question is the cheaper fix — that is
    exactly what `simp` demonstrated.

12. **What bends the test-suite curve, and when is it worth bending?** (§3.8.) Wall clock doubles
    every 32 days with a clean fit and no inflection, currently 10:13 for 6,339 tests, and cost per
    test has risen 4.7× — so this is not solved by running fewer tests. The first thing to establish
    is whether the per-test rise is stdlib load, since every test pays it; §3.1 measured that load at
    40 ms in a window where the stdlib has since grown 2.5×. **This is the only series in this
    document that is unambiguously diverging**, and unlike b it has a hard limit: attention.

## 5. Method (reproduce)

Both series come from ID-set diffs between consecutive commits touching the tracker, so a status
rewrite is never miscounted as a creation.

**The tracker changed layout on 2026-08-17 (WI-1118) and the id scheme changed on 2026-08-18.** The
recipe below handles both; the one published on 2026-08-02 does not, and running it across the
boundary produces a spectacular artifact rather than an error — see the caveats.

- Before 2026-08-17: one file, `anthill-todo/workitems.anthill`, status a fact field.
- 2026-08-17 only: one file per item, `anthill-todo/<status>/WI-<id>.anthill`.
- After: `anthill-todo/<status>/WI-<id>.anthill.md`. **Status is the directory**, so no parsing.
- ids are `WI-<num>` *and*, since 2026-08-18, `WI-<yyyymmdd>-<rand>` (175 of 1298 at Sep 2).

```bash
# bash, not sh: brace expansion below. Run from the repo root.
cat > /tmp/cl.pl <<'PL'
local $/; my $t = <STDIN>;
for my $r (split /fact WorkItem\(/, $t) {
  next unless $r =~ /id:\s*"(WI-[A-Za-z0-9_-]+)"/; my $id = $1;
  my @s = ($r =~ /status:\s*(Open|Claimed|Delivered|Verified|Rejected|Stale|PreOpened|ProposalRejected)/g);
  next unless @s;
  print "$id\n" if $s[-1] eq 'Delivered' or $s[-1] eq 'Verified';
}
PL

git log --format='%H|%ad' --date=short --reverse -- anthill-todo/ > /tmp/commits
: > /tmp/p_ids; : > /tmp/p_cl
while IFS='|' read -r sha date <&3; do
  git ls-tree -r --name-only "$sha" -- anthill-todo/ </dev/null > /tmp/tree
  if grep -qx 'anthill-todo/workitems.anthill' /tmp/tree; then
    git show "$sha:anthill-todo/workitems.anthill" </dev/null > /tmp/f
    grep -oE 'id: "WI-[A-Za-z0-9_-]+"' /tmp/f | grep -oE 'WI-[A-Za-z0-9_-]+' | sort -u > /tmp/c_ids
    perl /tmp/cl.pl < /tmp/f | sort -u > /tmp/c_cl
  else
    X='s#^anthill-todo/[a-z_]+/(WI-[A-Za-z0-9_-]+)\.anthill(\.md)?$#\1#'
    grep -E '^anthill-todo/[a-z_]+/WI-[A-Za-z0-9_-]+\.anthill(\.md)?$'             /tmp/tree | sed -E "$X" | sort -u > /tmp/c_ids
    grep -E '^anthill-todo/(delivered|verified)/WI-[A-Za-z0-9_-]+\.anthill(\.md)?$' /tmp/tree | sed -E "$X" | sort -u > /tmp/c_cl
  fi
  # per commit: the two DELTAS, then the two TOTALS. The totals are what the
  # sanity checks below read; without them a pattern miss is undetectable.
  printf '%s created=%s closed=%s n=%s k=%s\n' "$date" \
    "$(comm -13 /tmp/p_ids /tmp/c_ids | wc -l)" "$(comm -13 /tmp/p_cl /tmp/c_cl | wc -l)" \
    "$(wc -l < /tmp/c_ids)" "$(wc -l < /tmp/c_cl)"
  cp /tmp/c_ids /tmp/p_ids; cp /tmp/c_cl /tmp/p_cl
done 3< /tmp/commits > /tmp/out
```

Two checks on that output, both on the `n=`/`k=` totals rather than the deltas:

```bash
#   1. no row may show n=0 -- an empty id set means the filename pattern missed an era
awk '$4=="n=0"' /tmp/out            # must print nothing
#   2. the LAST row must agree with the working tree
ls anthill-todo/*/*.anthill.md | wc -l                       # 1298 at 2026-09-02  -> n=
ls anthill-todo/{delivered,verified}/*.anthill.md | wc -l    # 1097 at 2026-09-02  -> k=
```

Note the `/*.anthill.md` in both: `ls anthill-todo/{delivered,verified} | wc -l` counts the two
`dir:` headers and a blank separator as well, and answers 1100.

**Test-time series (§3.8).** Machine-local; `target/` is gitignored, so this exists only where the
runs happened and cannot be reconstructed elsewhere.

```sh
# per log: result-line count, final elapsed seconds, total tests passed
find rustland/target -maxdepth 1 -name 'test-run-*.log' -print0 | xargs -0 gawk '
  /test result:/ { res[FILENAME]++; if (match($0, /\. ([0-9]+) passed/, m)) pass[FILENAME]+=m[1] }
  { if (match($0, /^\[ *([0-9]+)s\]/, e)) last[FILENAME]=e[1] }
  END { for (f in last) printf "%s\t%d\t%d\t%d\n", f, res[f]+0, last[f]+0, pass[f]+0 }'
```

Take the run with the most tests passed per day; that is the fullest run and the only one comparable
across days. Do **not** filter on binary count — it fell from 95 to 35 on 2026-08-06 when tests moved
into shared `tests/include/` binaries, and a fixed threshold silently drops one era or the other.

**Caveats, each verified rather than assumed.**

- **b is a proxy.** It attributes every ticket filed in a closing commit to that closure. A follow-up
  filed one commit later reads as injected, not as a spinoff — so b is a lower bound on true fanout.
- **The denominator counts close *events*, not items.** 1275 events against 1098 items ever closed;
  the gap is 126 items closed more than once. Re-closures inflate the denominator, which makes b a
  slight **under**estimate — and see §4 q8 on why that gap is not a clean reopen count.
- **A too-narrow filename pattern is silent, and enormous.** Matching only `*.anthill.md` misses the
  2026-08-17 commits that used `*.anthill`. Those commits then have an *empty* id set, so the next
  commit re-creates every item: the first run of this measurement reported W34 at 2000 closed / 2270
  spinoffs and a lifetime b of 0.96 instead of 87 / 38 and 0.639. It produced a plausible number, not
  an error. The `no row may show 0` check above exists because of this.
- **`created:` was backfilled by the migration.** The single-file format had no birth date; every
  `created:` timestamp predating 2026-08-17 was reconstructed. It agrees with the git-observed birth
  everywhere it can be checked, but it is not independent evidence and the pre-migration series cannot
  use it. Age is measured from the commit an id first appears in.
- **`run_in_background` on a long walk can be killed at the tool timeout and still report success.**
  Two runs stopped at 744 and 1032 of 1879 commits with exit 0 and an empty log, each truncating the
  series at a different date. Always print and check a processed count.
- **Do not count `status:` occurrences with grep.** Descriptions quote status values in prose
  (WI-187's text contains `status: Open)` while the item is Delivered), which inflates Open by ~5%.
  Use the last-token-per-record extractor above, or the status directory, or `anthill-todo list --status X`.
- **`anthill-todo list` output embeds WI references in descriptions.** Anchor on the
  `^  WI-NNN [Status]` line prefix, not a bare `WI-[0-9]+` match, or the count roughly triples.
- **`#[cfg(test)]`-to-EOF is not a test-code split** (§3.7). `typing.rs` declares
  `#[cfg(test)] mod tests;` on line 31; the naive split charged 69,442 production lines to tests and
  reported production Rust *shrinking* by 33k lines over a month in which it grew by 80k. Brace-match
  the block, and treat a `mod name;` form as two lines, not a file.
- **`created` is an event count too, and the gap is large.** The same branch interleaving that
  inflates the closed side inflates the created side: 1,442 creation events over the series against
  **1,299 distinct ids**, with 111 ids "born" more than once. Deltas may be compared with deltas
  (§3.3's 1.07 ratio is events over events, and sound), but a creation count must never be reused as
  a ticket population — doing so put n=440 and n=123 into §3.5's first draft where the distinct
  populations are 361 and 114, double-counting 79 and 9 tickets and shifting every percentage in the
  table. Anything keyed on *tickets* takes the id set, not the delta.
- **A partial test log is indistinguishable from a fast one.** `test-run-latest.log` is a symlink
  claimed at startup and the log is written live, so a killed or in-flight run has a smaller final
  elapsed value and fewer result lines than a complete one. Taking the per-day *maximum by tests
  passed* is what makes the series honest; taking the latest run would have reported 2026-06-30 as a
  5-second suite (it was one aborted run of 2 tests).
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
