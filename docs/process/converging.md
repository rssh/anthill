# Converging — does the base stabilize?

Notes on the ticket-generation dynamics of this project, and the open questions they raise.
A running series, measured 2026-08-02 and re-measured 2026-08-06, 2026-09-02 and 2026-10-05 over the
`anthill-todo` tracker's git history. Each sitting appends rather than overwrites, so the drift is
readable. Numbers rot — and so did the method: the tracker changed layout on 2026-08-17, §5 has been
rewritten to span both regimes, and the 2026-08-02 recipe now produces a wrong answer *silently*.
On 2026-10-05 the same thing was found one level down: a third of the events the recipe counted in
its newest window never happened, so §5 carries a second recipe and §3.1 reports both. §3.9 is that
sitting's reading of the whole.

## 1. The policy this measures

Work is not started on a parked front (scaland resync, Cell runtime, staging brackets, effect rows)
until the base is stable. 42 pre-June work items sat Open under that rule on 2026-08-02 — deliberately
parked, not neglected — and 47 do on 2026-09-02 (§3.6 for why those two are on different definitions).
45 do on 2026-10-05.

The rule is only safe while the base actually converges. If base work generates work faster than it
retires it, the gate never opens and the parked fronts wait forever. **The branching factor is what
decides that**, and it is the metric this document exists to track.

**2026-10-05.** Two things this section did not know. The gate has had a ticket since 2026-08-17 —
WI-1126, *0.1.0 base interpreter feature freeze* — which states the opening condition as a
deliverable (every proposal carries a verdict; the spec's base sections have no undecided hole), not
as a rate; §3.6 reports where it stands. And the metric named above has stopped measuring what it was
chosen for: §3.1 shows b at its lowest four-week value in the series (0.34) inside the five weeks in
which the open set grew by 29%.

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

**2026-10-05 — the premise of that paragraph no longer holds.** "Injected … are a choice, not a
dynamic" was true while a follow-up was filed in the commit that delivered its parent. Three rules in
`CLAUDE.md` have since moved the filing: *if the change is smaller than the ticket text, make it
inline* (2026-08-06), *implement review changes immediately instead of firing follow-ups*
(2026-08-07), and *never open a ticket without discussion* (2026-09-05). A follow-up is now either
fixed inside its parent, where no ticket records it, or filed afterwards in a `todo:` commit of its
own, which closes nothing. b counts neither. The definition is unchanged; what it catches is the
residue, and §3.1 brackets what it misses.

## 3. Measurements (2026-08-02, re-measured 2026-08-06, 2026-09-02 and 2026-10-05)

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

#### Re-measured 2026-10-05 — b fell, and the fall belongs to the instrument

Five more weeks on the recipe as published. Every earlier row reproduces to the digit — the
2026-09-02 walk is exactly the first 1,879 commits of today's 2,245 — and the partial W36 row
(20 / 23) is the same row, now a full week.

| block | closed | spinoffs | **b** | 1/(1−b) |
|---|---|---|---|---|
| W32–W35 | 393 | 252 | 0.64 | 2.8 |
| W36 (full) | 46 | 72 | 1.57 | — |
| W37 | 50 | 30 | 0.60 | 2.5 |
| W38 | 27 | 5 | 0.19 | 1.2 |
| W39 | 77 | 55 | 0.71 | 3.5 |
| W40 | 33 | 9 | 0.27 | 1.4 |
| W41 (Oct 5 only) | 2 | 0 | — | — |
| **W36–W39 (four full weeks)** | **200** | **162** | **0.81** | **5.3** |

Lifetime now: 1490 close events, 963 co-filed → **b = 0.646** (0.639 on Sep 2).

**A THIRD OF THE EVENTS IN THAT TABLE NEVER HAPPENED.** The recipe diffs each commit against the
*previous commit in `git log` order*. On a linear history that is its parent. On a branchy one it is
often a commit on another branch, which lacks the tickets this branch filed and the closures it made
— so they vanish at that step and are "created" and "closed" a second time at the next. §4 q8 met
the symptom on 2026-09-02 ("a branch merged out of order looks exactly like a reopen") and stopped
there. Diffing each commit against **its own parents** (§5, second recipe) removes it:

| | log order | against own parents | never happened |
|---|---|---|---|
| close events, through Aug 2 | 862 | 782 | 9% |
| close events, Aug 3 – Sep 2 | 414 | 322 | 22% |
| close events, Sep 3 – Oct 5 | 214 | 142 | **34%** |
| creation events, Sep 3 – Oct 5 | 298 | 185 | **38%** |
| lifetime close events / distinct items ever closed | 1,490 / 1,241 | 1,246 / 1,241 | |

One day shows the scale. In log order 2026-09-05 closes 7 items and co-files 27 — b = 3.86, the
worst day in the series and more than a third of W36's spinoffs. Against their own parents that
day's commits closed **1** item and filed **6**, none of them alongside a close. The contamination
was about a tenth of all close events through early August and has been between a fifth and a half
every week since W33, as more of the work arrived by merge (merges are 3.5% of all commits through
Aug 2, 4.9% of the month to Sep 2, 7.4% since); in W39 it is 49%.

The series again, each commit against its own parents:

| block | closed | spinoffs | **b** | created | filed in a commit that closes nothing |
|---|---|---|---|---|---|
| W20–W23 | 151 | 66 | 0.44 | 201 | 135 (67%) |
| W24–W27 | 250 | 122 | 0.49 | 226 | 104 (46%) |
| W28–W31 | 249 | 167 | 0.67 | 308 | 141 (46%) |
| W31 alone | 66 | 66 | 1.00 | 114 | 48 (42%) |
| W32–W35 | 301 | 180 | 0.60 | 344 | 164 (48%) |
| **W36–W39** | **135** | **65** | **0.48** | **175** | **110 (63%)** |
| W37–W40 | 125 | 42 | 0.34 | 157 | 115 (73%) |

Lifetime 1,246 closes, 734 co-filed → b = 0.59. Week by week since W32, closes run 104, 72, 62, 63,
then 36, 39, 21, 39, 26; b runs 0.75, 0.29, 0.40, 0.89, then 0.89, 0.41, 0.10, 0.38, 0.35.

**What survives the correction.** The summer's shape does — 0.44 → 0.49 → 0.67 → 0.60, with W31 at
exactly 1.00 — so every earlier finding stands, a few points lower. The Aug 6 alarm (0.88, "8.3
descendants") was a partial week read through a contaminated instrument; W32 closed at 0.75.

**What the corrected series says about this window is three things, and only the first is good.**
Co-filing has nearly stopped: 180 → 65 → 42 per four weeks, b = 0.34 over W37–W40, and four
deliveries in five now file nothing (§3.2). Closures fell by more than half, 301 → 135 — the rate of
W20–W23, in May. And the tickets did not stop being written, they moved: the share filed in a commit
that closes nothing went 48% → 63% → 73%.

**Those are not "injected" in §2's sense.** Since Sep 3, 80 commits that close nothing filed 134
tickets. The four largest are 10 (Oct 2), 9 (Oct 3), 9 (Sep 29) and 5 (Sep 26): three read
`todo: file N follow-ups found by WI-…'s /code-review`, and the fourth files the work sequence of a
proposal just reviewed. By subject line alone 54 of the 134 are follow-ups or review output; of the
rest, most still are (`found delivering SNJPR`, `what N3W68 found outside its thirteen items`,
`measured by HXGXF`) and a handful are the planned steps of a proposal. That gives a bracket where
there used to be a number:

| | Aug 3 – Sep 2 | Sep 3 – Oct 5 |
|---|---|---|
| closed (own parents) | 322 | 142 |
| co-filed only — b as defined | 203 → **0.63** | 51 → **0.36** |
| + tickets whose filing commit calls them follow-ups | 258 → 0.80 | 105 → 0.74 |
| every ticket filed | 377 → 1.17 | 185 → **1.30** |

The measured b fell by almost half while the bracket holding the real fan-out went from
[0.63, 1.17] to [0.36, 1.30] — wider at both ends and still straddling 1. **b can no longer say which
side of 1 the process is on.** It could while filing and delivering shared a commit, and that is the
practice the three rules of §2 ended. Nor can it be recovered from what the tracker records: an item
has no field for where it came from, the subject-line count above is the best available stand-in,
and a pattern over descriptions finds a named parent in under a quarter of them. §4 q13.

**A worked example — the lineage that dominates the window.** WI-20260929-WBHTM (a spec-operation
call over a value-in-type argument) was filed and delivered on Sep 29; its `/code-review` filed nine
follow-ups. One of the nine, WI-20260929-0RP29 (a type projection nested in a return type), was
marked Delivered the next morning and reached its **tenth** fix pass on Oct 3. Its reviews filed 21
more tickets (2 + 10 + 9, on Sep 30, Oct 2 and Oct 3). One of the 21 was a redesign out of the
seventh review — WI-20261001-80ZV8, proposal 070 — which took 15 commits and 36 recorded notes and
filed three of its own. Three generations below one ticket, 33 descendants, six days. **b saw two of
the 33** — the pair filed in the commit that closed 80ZV8. The other 31 were filed in commits that
closed nothing.

**And inside that ticket the process did not converge.** WI-20261002-E1WN0, filed out of the same
work, records the measurement: *eight `/code-review` passes each reported the cap of 15 findings; of
the eighth's fifteen, fourteen were regressions of the two passes it read, and about a third were
one program judged two ways by two spellings or two readers.* A pass that finds fifteen and whose
fixes plant fourteen for the next is a branching factor of about 1 **inside one ticket**, where no
tracker metric looks. This is "fix it, do not file it" doing what it was written to do, with a cost
the rule did not price: the spinoff tree that used to be visible as tickets now grows as review
rounds, and what bounds it is not the queue but the reviewer's cap of 15. E1WN0's own answer is a
change of method rather than an eleventh pass — a generated family of programs per typer rule (1,152
from one template; 104 of them crashed the loader, which 434 hand-written rows had not), each held
to stated properties. It is Open.

**Time-to-close, and the 100% that was a denominator.** On the own-parents series — a ticket is born
in the commit that added it and closed in the commit that closed it:

| born | spinoff n / closed | same-day | ≤7d | injected n / closed | same-day | ≤7d | **all born: closed ≤7d** |
|---|---|---|---|---|---|---|---|
| through Jun | 282 / 247 | 62% | 80% | 317 / 286 | 36% | 71% | 67% |
| Jul | 171 / 157 | 54% | 85% | 139 / 128 | 43% | 83% | 77% |
| Aug 1–6 | 73 / 67 | 64% | 91% | 44 / 40 | 52% | 78% | 79% |
| Aug 7–31 | 118 / 100 | 64% | 92% | 132 / 99 | 52% | 89% | 72% |
| **Sep** | **68 / 43** | **53%** | **93%** | **118 / 68** | **46%** | **90%** | **58%** |
| Oct 1–5 | 3 / 1 | — | — | 22 / 3 | — | — | — |

The first six columns are the 2026-09-02 table's, over closers only. The last is new: of **every**
ticket of the cohort that is at least seven days old, the share closed within seven days of its
birth — a ticket that never closed stays in the denominator. (For September that is the 168 born
Sep 1–28.)

*The prediction made on Sep 2 held.* The Aug 7–31 cohort read 100% / 99% within a week then, with a
quarter of it still open; it reads 92% / 89% now.

*The "largest single movement anywhere in this document" was mostly that denominator.* A young
cohort measured over closers only can contain nothing but tickets that closed quickly — the slow
ones are still open and are not counted. On the all-born column the same cohorts read 67% → 77% →
79% → 72%: one real step, in July, which is exactly where the Sep 2 control put it ("the injected
acceleration starts in July, a month before the rule was written"), and nothing after it. §4 q4(b)
asked what accelerated closure in August. Nothing did.

*September is below the spring baseline, and the shortfall is one fortnight.* Born Sep 1–14 (101
tickets): 49% closed within a week, 42 not delivered today. Born Sep 15–28 (67 tickets): 73% — the
August rate again. The first fortnight's residue is not a plan waiting its turn: 3 of the 42 carry a
`depends_on`; the rest are defects found in passing (`MEASURED BY ME (found by /code-review during
…)`), five scaland items, and open design questions. The Oct 1–5 cohort — 25 born, 21 open, 19 of
the 25 from the two review batches above — is where the next sitting sees whether that fortnight was
an episode or the level.

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

**2026-10-05.** On the published recipe the new window reads 168 closing events: no spinoff 114
(67.9%), one 25 (14.9%), two 13 (7.7%), 3–4 7 (4.2%), `>4` 9 (5.4%). The zero bucket is the highest
in the series and the `>4` tail has nearly tripled. **The tail is §3.1's artefact.** Each commit
against its own parents:

| spinoffs filed | through Aug 2 | Aug 3 – Sep 2 | Sep 3 – Oct 5 |
|---|---|---|---|
| 0 | 445 (63.9%) | 177 (58.6%) | **107 (78.7%)** |
| 1 | 163 (23.4%) | 77 (25.5%) | 18 (13.2%) |
| 2 | 44 (6.3%) | 28 (9.3%) | 5 (3.7%) |
| 3–4 | 25 (3.6%) | 18 (6.0%) | 5 (3.7%) |
| >4 | 19 (2.7%) | 2 (0.7%) | 1 (0.7%) |
| **closing commits** | **696** | **302** | **136** |

Eight of the nine high-fan-out "deliveries" were a branch re-entering the walk with tickets it had
filed days earlier. What is left is the sharpest regime change in the document: **nearly four
deliveries in five file nothing**, and the piles are filed on their own — 10, 9, 9 and 5 tickets in
four commits that close nothing (§3.1). This section's title has become wrong in an instructive way:
the multiplier no longer lives in a minority of deliveries. It lives outside deliveries.

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

**2026-10-05.** Open 164 → **201**, PreOpened 22 → **24**, Claimed 2 → **5**, closed 1097 → **1239**
(1200 Delivered + 39 Verified), plus 11 Rejected, 2 ProposalRejected, 3 Stale — **1485** total.
`anthill-todo list --status open --unblocked` answers 163.

The count was dismissed above because it oscillated straight through a drift in b. With b unable to
see filing (§3.1) it deserves a second look, as a series rather than a reading — Open + PreOpened +
Claimed on main at each week's end:

```
Jun 14  130    Jul 12   83    Aug  9  166    Sep  6  203    Oct  4  231
Jun 21   92    Jul 19  104    Aug 16  146    Sep 13  210
Jun 28   98    Jul 26  103    Aug 23  152    Sep 20  206
Jul  5  102    Aug  2  152    Aug 30  179    Sep 27  215
```

Flat near 100 for six weeks, one step in W31 (+49, the week b touched 1.00), a plateau, and from
Aug 23 a climb of 79 in six weeks. It has more than doubled since late July. As a count it still
says little. As **weeks of work at the current closing rate** it is the quantity §1's gate is about,
and with the parked set (§3.6) left out it reads: late July, 53 open against 62 closes a week —
under one week. End of August, 132 against 75 — under two. Today **185 against 32 — almost six.**

All of that growth is in Open: since late July Open went 84 → 201 while PreOpened went 15 → 24. By
the practice §3.6 records, PreOpened is where work outside the base is filed, so what is
accumulating is base work, not parked ideas.

Creation against closure, each commit against its own parents: W20–W31 735 created / 650 closed,
**1.13**; W32–W35 344 / 301, **1.14**; W36–W40 218 / 161, **1.35**. The ratio that "has not moved all
summer" had not. It has now. (On the published recipe the three read 1.07, 1.04 and 1.42 — the last
inflated on both sides by re-entering branches.)

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

**2026-10-05**, same keying (the born counts of the six earlier months are unchanged, as they must be):

```
2026-03  born  38  done  32  (84%)
2026-04  born 110  done  90  (82%)
2026-05  born 203  done 176  (87%)
2026-06  born 247  done 234  (95%)
2026-07  born 310  done 285  (92%)   was 88% a month ago, 76% two months ago
2026-08  born 368  done 307  (83%)   was 77% a month ago
2026-09  born 186  done 111  (60%)
2026-10  born  25  done   4  (16%)   five days old
```

July has reached June. August is following more slowly: 77% → 83% in its second month, where July
gained twelve points in its own. **September is the first cohort to arrive behind**: 60% at its
first full reading, against 76% for July on Aug 2 and 77% for August on Sep 2, and its reading is
taken five days after the month ended where theirs were taken two days after. "Nothing is leaking"
still holds for everything through July. For August and September it is no longer shown, and their
residue is where the open set's growth sits: of the 201 Open today, 50 were born in August, 70 in
September and 20 in October, against 8 from June and 17 from July.

The born column sums to 1487 against 1485 in the tracker. The second extra is **WI-874**, closed on
2026-09-16 by deleting its file rather than moving it: born in git, in no status directory today.

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
`simp`, by two thirds once WI-881/884/888 settled what `@[simp]` admits and what makes a defining
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

**2026-10-05 — the old questions are retiring, and one cluster has taken over.** Same method, which
this sitting had to recover (§5): a whole-word, case-insensitive match over each ticket's
`## Description` chapter. It reproduces the W31 column exactly and eleven of the thirteen Aug rows
(`host` 54 against 56, `tuple` 22 against 24). New window: the 185 distinct births of Sep 3 – Oct 5,
and its two halves (92 born through Sep 20, 93 after).

| term | W31 | Aug 3–Sep 2 | **Sep 3–Oct 5** | shift | through Sep 20 | after |
|---|---|---|---|---|---|---|
| **carrier** | 36.0% | 32.4% | **49.2%** | **+16.8** | 51.1% | 47.3% |
| **requirement** | 10.5% | 10.0% | **24.3%** | **+14.3** | 25.0% | 23.7% |
| dispatch | 21.1% | 20.8% | 28.1% | +7.3 | 22.8% | 33.3% |
| arrow | 2.6% | 7.2% | 10.8% | +3.6 | 13.0% | 8.6% |
| simp | 17.5% | 6.4% | 9.7% | +3.3 | 13.0% | 6.5% |
| typer | 13.2% | 23.5% | 26.5% | +3.0 | 23.9% | 29.0% |
| tuple | 2.6% | 6.6% | 8.6% | +2.0 | 10.9% | 6.5% |
| effect | 7.0% | 18.3% | 18.4% | +0.1 | 19.6% | 17.2% |
| label | 4.4% | 11.6% | 8.6% | −3.0 | 12.0% | 5.4% |
| host | 23.7% | 15.5% | 11.9% | −3.6 | 14.1% | 9.7% |
| proof | 1.8% | 7.8% | 3.2% | −4.6 | 5.4% | 1.1% |
| **resolve** | 22.8% | 27.4% | **20.5%** | **−6.9** | 28.3% | 12.9% |
| **scope** | 44.7% | 42.1% | **32.4%** | **−9.7** | 46.7% | 18.3% |

Two movements, opposite in sign. `scope`, flat through August's 413 closures, and `resolve`, which
rose through them, both fell — and fell inside the window, 47% → 18% and 28% → 13% between its
halves. `host` kept falling (24% → 16% → 12%), `proof` and `label` gave back most of their August
rise, and `simp` ends the window where August left it (6.5% in the later half). The resolver, the
scoping rules and the host boundary are producing a shrinking share of new work with no campaign
aimed at any of them. That is this section's "settling a question retires its generation", on four
more terms.

Against them `carrier` is now in **one new ticket in two** and `requirement` in one in four, with
`dispatch` at a third in the later half. The words that rose with them say what the front is — share
of descriptions, Aug 3–Sep 2 → Sep 3–Oct 5: `parameter` 25% → 51%, `slot` 18% → 37%, `bound` 14% →
34%, `dictionary` 7% → 27%, `provider` 8% → 22%, `witness` 6% → 19%, `rigid` 3% → 15%. It is the
typer's requirement machinery: which dictionary a `requires` means, what a sort parameter's slot
holds, how a provider's own parameters reach a member.

**What is being discovered there is the design.** Six numbered proposals were first committed in
this window, each a change to the type system or to how a typed call is resolved: 065 (a rigid type
is a value only where a requirement says so), 066 (provision blocks), 067 (`Fillable`), 068 (an
operation application in a rule body is a computation), 069 (declaration-site defaults), 070
(`Self`; a bare sort is fresh everywhere). This sitting first read them as a front being *written*
— surface added by choice. **That reading was wrong, and their author corrected it the same day:
every proposal after 060 is the repair of a defect in the base's design, and work outside the base
is not proposed at all but filed PreOpened** (§3.6; fifteen tickets have been born PreOpened since
June, two of them in this window). The proposals' own openings agree wherever they were checked: 061
— "a predicate is the only name in the language with no declaration"; 066 — a conditional
provision's condition applied to every body its carrier owns; 069 — §4.4 of the spec contradicting
§8.1; 070 — "one text means two things, depending on where it is written".

So ten design repairs have landed in six weeks (061–064 on Aug 21–25, 065–068 on Sep 19–26, 069–070
on Oct 3), `docs/kernel-language.md` went from 2,819 lines on Aug 2 to 5,618 on Sep 2 and 6,862
today, and the sentence this section opened with — *resolution/dispatch/carrier/requirement is being
discovered one delivery at a time* — is right again, one level up. The resolution half is
converging. In the requirement half what a delivery now finds is not a missed caller or a stale list
but a hole in the design, and the fix is a proposal: larger than a patch, cutting across typer,
loader, generators and spec, and able to move the ground under another repair before either is built
(070 rewrote §2 of 069 the day after both were drafted). Each repair then meets everything already
there: the open tickets read as pairs and triples (*a spec-operation call over a carrier whose
effect row is the caller's row parameter*; *an operation-level `requires` over a two-hop σ chain*;
*a dependent return type at a call*). A table of interactions grows with the square of the number of
features and is being filled in one reviewed example at a time — which is the mechanism E1WN0 (§3.1)
names, and the reason a review pass over it does not converge.

The prediction §4 q3 has asked for since Aug 2 is registered there, at this sitting.

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

**2026-10-05.** Parked set, same definition: 50 → 47 → **45**. Two left it — WI-263 Delivered,
WI-177 Rejected.

The five chains, with the edges as the tracker holds them:

| head | waits on | since |
|---|---|---|
| WI-020 (guard analysis) | WI-556, PreOpened — an example that would *use* the optimisation | before Aug 2 |
| WI-156 (scaland resync) | **WI-1126** (the freeze gate), WI-069, WI-070 — all Open | added between Aug 2 and Sep 2 |
| WI-188 (`.copy` → staging brackets) | **WI-20261003-QV5W5**, implement proposal 069 — Open | Oct 3 |
| WI-207 (acyclic_cell) | nothing — WI-205 is Delivered | ready |
| WI-330 (row-unification migration) | nothing — all three dependencies Delivered | ready |

"Every head is ready … what holds them is the policy, not a dependency" is true of two chains in
five, and was never true of WI-020. For the scaland chain the policy **has been written down as the
dependency** — WI-156 waits on WI-1126 — which is what §4 q1 and q5 asked for; this document did not
notice when it happened. The staging chain went the other way: its head carried no dependency
through September and now waits on a proposal two days old. A parked chain acquired a prerequisite
from the newest proposal (whether that is the rule failing or the rule working is §4 q15).

**WI-1126 is the gate, and it has not started.** Filed 2026-08-17: *"GATE — 0.1.0 BASE INTERPRETER
FEATURE FREEZE … it ships a SETTLED BASE and a TRIAGED proposal backlog"*, with an acceptance that
can be checked — every file under `docs/proposals` carries a verdict, the spec's base sections hold no
undecided hole, both suites green. WI-010, WI-156 and WI-165 depend on it. Seven weeks on, it has no
recorded note and nothing filed against it; `docs/proposals/rejected/` holds its README and nothing
else; and the population it has to triage has grown from 66 numbered files to 77 (061–070 and
027.4). Its premise —
*"The base type system is written"* — was stated when `kb/typing` held 28,450 lines of production
code. It holds 47,139 today (§3.7).

**The tracker's own parked state is PreOpened** — in the tool's words *captured idea / future
direction; not yet committed to the active queue (cannot be claimed until promoted to Open)* — and
since 2026-10-05 this document knows that it is where work outside the base is meant to be filed.
24 items are there: 13 born PreOpened, the first on 2026-06-24, and 11 demoted from Open between May
and August. None of the five chains above is among them. They are Open, as they were before the
practice began, which is why this section needed a birth date to find its parked set.

The prose gates, closed out:

- **WI-294 was never a prose gate.** Its row above — "real prerequisite, no edge" — was wrong on
  Aug 2 and repeated on Sep 2. WI-674 *is* the scaland `Term->Value` migration, and
  `depends_on: WI-288, WI-674` is in the Aug 2 tree. The prose was read; the field was not.
- **WI-177** was Rejected on 2026-09-24 as moot — the path it optimises was never built. The stale
  gate that survived two sittings at "cost is near zero" was settled by reading the ticket, not by
  adding the edge.
- **WI-266** is Delivered (above). **WI-128** is the one left: Open, its prerequisite still without
  a ticket.

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

#### 2026-10-05 — a correction first: the lines-per-`fn` break was `cargo fmt`

The two tables this section rests on reproduce — all thirty cells of the line-kind table and all
twenty-four of the control-flow table — once the classifier's rules are recovered (§5; they were not
written down). Reproducing them located the "two-month flat line" breaking: not across a month, but
inside one commit. **`10191d6a Format Rust workspace` (2026-08-10)** touched 606 files,
+44,523 / −17,209:

| | commit before | `10191d6a` | Aug 16 |
|---|---|---|---|
| production code | 80,096 | 91,648 | 98,032 |
| test code | 116,140 | 132,100 | 147,195 |
| `fn` | 3,771 | 3,771 | 3,989 |
| lines per `fn` | 21.2 | **24.3** | 24.6 |
| lines per match arm | 11.0 | **12.5** | 12.8 |

Eleven and a half thousand lines of production code and sixteen thousand of test code arrived with
no function, branch or behaviour: long lines were wrapped. Three conclusions drawn on Sep 2 rest on
it and do not stand:

- *"Production code per closed ticket roughly doubled between July and August"* (55 → 99). Net of
  the reformat the Aug 2 → Aug 16 row is **48**, not 99 — and so the series did not then "flatten
  (99 → 92)". It reads 47, 55, 48, 92: flat through mid-August and doubling in the second half.
- *"Surface grew at 23–35% against 52% for lines … the marginal line is increasingly not a new
  branch."* Net of the reformat, lines grew **33%** over Aug 2 → Sep 2 against 23–35% for surface.
  In step. "The shape of a system whose behaviour is roughly settled and whose *explanation* is not"
  was a description of rustfmt's line width.
- §4 q11's successor — *which subsystem is the lines-per-`fn` rise in?* — has no subsystem for an
  answer. It rose in `anthill-cpp-gen` (21.2 → 24.9, on four new functions) as it did in the typer
  (26.3 → 29.8).

The add-and-delete table's `Aug 1–16` row holds the same commit (+22,589 / −8,730 in src files,
+21,934 / −8,479 in test files), which is the whole of its odd 15.2% beside 3–6% for tests in every
other row. Taken out, that row is near +42 thousand / −6 thousand in src: about 14%, not 22.8%.

What does stand: the 4:1 add-to-delete finding, the prose finding (untouched — the reformat moved no
comment), and "still growing real surface". On the wrapped basis lines per `fn` reads 24.3 → 24.6 →
25.0 → 25.3 → 25.3: a slow rise that has stopped.

#### 2026-10-05 — the state

| | Sep 2 | Sep 20 | **Oct 5** | Sep 2 → Oct 5 |
|---|---|---|---|---|
| production code | 115,506 | 126,061 | **141,510** | +22.5% |
| production doc-comment | 53,607 | 62,419 | **69,479** | +29.6% |
| production `//` comment | 34,694 | 42,156 | **44,754** | +29.0% |
| test code | 185,964 | 211,182 | **243,681** | +31.0% |
| test doc + comment | 72,047 | 87,682 | **100,751** | +39.8% |
| blank (both) | 26,230 | 29,107 | **32,733** | |
| **all rustland Rust** | 488,048 | 558,607 | **632,908** | +29.7% |

145 thousand lines in 33 days. Prose is 44.7% of non-blank production lines — 43.3% on Sep 2 and
39.3% on Aug 2 by the same division; the "42%" and "37%" above do not reproduce from the table they
sit under — and it is half of the production lines added: 25,932 against 26,004 of code.

**Per closed item, on closes that happened** (§3.1 — the table above this addendum divides by
log-order close events, which overstate the denominator by a tenth to a third):

| window | items closed | prod code / item | prod prose / item | test code / item |
|---|---|---|---|---|
| Jun 7 → Jul 5 | 250 | 53 | 46 | 103 |
| Jul 5 → Aug 2 | 249 | 63 | 83 | 153 |
| Aug 2 → Aug 16 | 176 | 61 † | 108 | 153 † |
| Aug 16 → Sep 2 | 146 | 120 | 138 | 266 |
| Sep 2 → Sep 20 | 75 | 141 | 217 | 336 |
| **Sep 20 → Oct 5** | **67** | **231** | **144** | **485** |

† net of the reformat (126 and 244 with it). Rows below it are in the wrapped style, which spends
about 14% more lines on the same code; that explains 120 against 105, not 120 against 61.

**A closed item now carries about four times the code it did in June — production and test alike,
after the 14% is taken off** — and its weight has roughly doubled twice since mid-August. This is
where the halved closure count of §3.1 went: production code grew by 7.2 thousand lines a week over
the last fortnight, exactly the rate of Aug 16 → Sep 2, on half the closes. (On the old denominators
the two new rows read 102 / 158 / 245 and 138 / 86 / 290 — the same direction, understated.)

**Where it went — one subsystem.** Production code lines:

| | Aug 2 | Sep 2 | **Oct 5** | share of Sep 2 → Oct 5 growth | prose per line of code |
|---|---|---|---|---|---|
| `kb/typing` | 20,409 | 33,783 | **47,139** | **51%** | 1.00 |
| `kb/load` | 10,246 | 16,762 | 21,272 | 17% | 0.81 |
| `kb/resolve` | 3,958 | 4,843 | 7,463 | 10% | 1.01 |
| `eval` | 7,234 | 9,789 | 11,584 | 7% | 0.80 |
| everything else | 33,948 | 50,329 | 54,052 | 14% | |

The typer was 17% of production code on Jun 7, 27% on Aug 2 and is **33%** now. It took half of the
month's growth, and it is accelerating again: 240 lines a day over Sep 2 → Sep 20, **569 a day** over
Sep 20 → Oct 5 (net of 501 lines of module boilerplate the split below added) — level with its
previous peak, 574 a day in the first half of August. In the typer and the resolver there is now a
line of prose for every line of code. This is §3.5's cluster measured in a different unit, and it
agrees.

**Control-flow surface, in step with lines.**

| | Sep 2 | **Oct 5** | Sep 2 → Oct 5 |
|---|---|---|---|
| code lines | 115,506 | 141,510 | +22.5% |
| `fn` | 4,614 | 5,586 | +21.1% |
| `pub fn` | 1,385 | 2,393 | +72.8% |
| match arms (`=>`) | 8,605 | 10,108 | +17.5% |
| `if` / `else if` | 4,782 | 5,842 | +22.2% |
| `struct` / `enum` decls | 642 | 786 | +22.4% |
| lines per `fn` | 25.0 | 25.3 | |
| lines per match arm | 13.4 | 14.0 | |

972 new functions and 144 new type declarations in 33 days — 29 functions a day against 35 a day
the month before. Neither the corrected August nor this window shows length growing faster than
decisions. **The implementation is still growing real surface, at four fifths of August's pace, on
well under half of August's closures.** (`pub fn` is the typer split, below: 758 functions gained a
visibility in one week because their callers moved to another file.)

**Addition or rework — the first sign of the second.** Snapshot to snapshot, as above:

| window | src added | src deleted | del/add | test added | test deleted | del/add |
|---|---|---|---|---|---|---|
| Sep 2 → Sep 20 | 33,944 | 5,851 | 17.2% | 46,074 | 3,608 | 7.8% |
| Sep 20 → Oct 5 | 112,598 | 86,524 | **76.8%** | 51,227 | 3,000 | 5.9% |

The second row is mostly one move: `7706ae6c` (2026-09-23) split `kb/typing.rs`, 80,388 lines, into
51 files under `kb/typing/`. A tree diff cannot tell a moved line from a rewritten one, so here is
the same comparison as a **multiset difference of non-blank lines** — a line that only changed place
counts as nothing — recomputed for every window so the rows are comparable:

| window | src added | src deleted | del/add |
|---|---|---|---|
| Jun 7 → Jul 5 | 34,347 | 5,643 | 16.4% |
| Jul 5 → Aug 2 | 46,332 | 6,562 | 14.2% |
| Aug 2 → Aug 16 (holds the reformat) | 58,037 | 10,829 | 18.7% |
| Aug 16 → Sep 2 | 42,988 | 6,950 | 16.2% |
| Sep 2 → Sep 20 | 32,174 | 4,579 | 14.2% |
| **Sep 20 → Oct 5** | **36,683** | **11,415** | **31.1%** |

Four months inside 14–19%, then double. The split commit's own edits — visibilities and imports,
1,213 lines — are in that row; cut out, it is 30.1%. W39 alone is 36% (33% cut out), the first week
to reach the "third of additions" the section above could not find. And what was deleted has names:
runtime dispatch (WI-20260922-0DK3H), the frame type-argument channel (WI-20260921-28TAT), the
rule-body round trip and its per-atom tables (WI-753), the implicit self-sort tie
(WI-20261001-80ZV8). **Four mechanisms retired in fifteen days.** "Tickets that read as corrections
are producing net-new production code at a steady 4:1" is no longer the whole description.

**Examples.** `guardians` 5,803 → 7,053; `classic-mini` 403 → 734; the other three within 30 lines.

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

**2026-10-05 — it bent a little, and the early record is gone.** `rustland/target/` holds no log
older than 2026-09-24: the 9,050 the table above was read from no longer exist, and nothing exists
for Sep 3 – Sep 23. What follows is 778 logs over nine days.

| date | tests | wall clock | ms/test | full runs that day | hours in test runs |
|---|---|---|---|---|---|
| 2026-09-24 | 7,583 | 13:56 | 110 | 11 | 4.9 |
| 2026-09-25 | 7,667 | 13:34 | 106 | 13 | 3.8 |
| 2026-09-26 | 7,711 | 13:48 | 107 | 12 | 3.1 |
| 2026-09-29 | 7,817 | 13:50 | 106 | 5 | 1.3 |
| 2026-09-30 | 7,917 | 14:26 | 109 | 9 | 2.9 |
| 2026-10-01 | 8,036 | 14:40 | 110 | 6 | 2.4 |
| 2026-10-02 | 8,173 | 15:43 | 115 | 3 | 2.7 |
| 2026-10-03 | 8,386 | 16:06 | 115 | **20** | 6.4 |
| **2026-10-04** | **8,507** | **16:36** | **117** | **20** | **7.0** |

Wall clock here is the **median of the day's full runs**, not the fullest run: on Oct 2 the run with
the most tests passed took 57:50 beside two others at 15:29 and 15:43, so the rule above picked a
stall (§5). On Oct 4 both rules give the same run.

Against Sep 2: tests 6,339 → 8,507 (+34%), wall clock 10:13 → 16:36 (+62%), cost per test 97 → 117
ms. The projection made then — *20 minutes in about a month* — is scored today, 32 days on: 16:36.
The curve is still exponential but its doubling time is **46 days, not 32**. On the new rate: 20
minutes in mid-October, 30 in mid-November, an hour at the turn of the year. Nothing identifies what
bent it. The stdlib grew 12% (8,619 → 9,676 lines) while cost per test grew 21%, so stdlib load is
at most part of the per-test rise, and §4 q12's first measurement is still not taken.

**What it costs.** Over the nine days, 99 full runs took 25.8 hours and all runs 34.5, against 33
items closed on those days: three full runs and 47 minutes of full-suite wall clock per closed item.
On Oct 3 and Oct 4 the suite ran in full twenty times a day. (And that is this machine. `CLAUDE.md`
has recorded since 2026-09-27 that a full workspace run takes over an hour in a cloud session, with
a rule beside it — measure a back-out on a small temporary binary first — which is the first
countermeasure this series has drawn.)

**Is the suite what halved the closures? It is tempting, and the time budget says no.** Closes per
week times suite minutes is between 400 and 620 for each of the six weeks since W32 that has a suite
reading, while each factor moved fourfold — 104 closes at under 4 minutes, 26 at over 16. Two
monotone series will do that. The logs give the direct test: on Oct 3 a full run started every 46
minutes of the working span and on Oct 4 every 69, and a run takes 16. With the suite of Aug 2
(4:01) those cycles would be 34 and 57 minutes — a fifth to a third more of them, not twice as many.
**Between two thirds and three quarters of a cycle is not the suite.** The suite is a tax on every
cycle, it is growing, and it is not where the factor of two went. That is in §3.7 — four times the
code per closed item — and in §3.1's ten passes.

### 3.9 What the 2026-10-05 sitting adds up to

Kept apart from the sections above because it is reading, not measurement, and is meant to be argued
with.

**1. The instruments say "converging" and the stock says "accumulating". The instruments are wrong,
each for a stated reason.** b is at its lowest sustained value since spring because filing left the
closing commit (§2, §3.1), and what is still counted is a third merge artefact. "Every spinoff closes
within a week" was a closers-only denominator (§3.1). Lines per `fn` was a formatter (§3.7).
Meanwhile the open set outside the parked chains went from under a week of work to almost six
(§3.3), September is the first cohort to arrive behind its predecessors (§3.4), and creation over
closure moved for the first time, 1.14 → 1.35. On the pair §4 q4(a) proposed — b < 1 over four weeks
and at least 90% of spinoffs closed inside one — the gate reads **open** today, on either recipe.
That is the strongest evidence here that the pair is not the gate.

**2. The work did not shrink. The ticket did.** Closures are back at May's rate while code grows at
August's. A closed item carries about four times what it did in June (§3.7); commit subjects name
117 tickets where the month before named 260, on three quarters as many commits; and one ticket took
ten passes (§3.1). The rules that stopped follow-ups being filed did not stop them existing — they
are review rounds inside the parent now. For a six-line fix that is the right trade, and it is the
case the rule was written from (§3.1, 2026-08-06). For a defect in how two type-system features meet
it is a different trade: the eighth pass found fourteen regressions.

**3. "The base" is two things doing opposite things.** The resolver, the scoping rules and the host
boundary are settling: their share of new tickets fell with nothing aimed at them (§3.5), which is
what convergence looks like in this tracker. The type system's requirement machinery is not: ten
proposals in six weeks have changed it, it is a third of the production code, and it took half of
the month's growth (§3.5, §3.7).

This sitting first took those proposals for new design and asked whether they were base or a front
that was never parked (§4 q15). The answer given the same day settles both halves: **they are base,
and they are not new design. Each repairs a defect in the design the base already had; what is
outside the base is filed PreOpened.** So §1's rule is being applied as written, and the parked
chains wait where they should: the scaland chain through WI-1126, which has not started, and the
staging chain, since Oct 3, on proposal 069 (§3.6).

That puts this document's original question back in force, one level above where it has been asked.
*Does base work generate work faster than it retires it* was measured over tickets, and for the
settled half the answer is no. For the requirement half the unit that matters is the design repair,
and there the evidence so far is that repairs keep arriving — four in late August, four in late
September, two in the first days of October — and that one can reopen another before either is
built. Whether that series closes is what "does the base stabilize" now means. It is counted in
proposals, not tickets (§4 q15 starts the count), and the triage it needs is already written down as
WI-1126, which says the base type system "is written" and under which the typer has grown by two
thirds. The author's own summary on the day was shorter: there is no date, because much of the base
is still underspecified. §4 q15 turns that into two lists.

**4. Three things turned the right way, and none of them is b.** Deletion: four mechanisms retired
in a fortnight, the first window in which deleting is not a rounding of adding (§3.7). The suite:
doubling every 46 days instead of 32, with the first rule written against it (§3.8). And method:
E1WN0 is the first ticket here to answer "the examples do not converge" with something other than
more examples (§3.1).

**Three readings fit these facts, and they recommend different things.**

- *Deepening.* The easy defects are gone; what is left is defects in the type system's design, in
  bigger units, closing slower. They run out. → Watch repair proposals per month and typer lines per
  day; both should fall without intervention.
- *Critical inside the typer.* Each repair changes the ground under features already built and under
  other repairs, and review regresses about as fast as it fixes. It does not settle by this method.
  → Change the method (E1WN0) before the next repair is built, and triage which design defects
  0.1.0 must repair (WI-1126). WI-20261003-QV5W5, the implementation of 069, is the next one, and
  four tickets already wait on it.
- *Capacity.* The dynamics are what they were and the cycle got longer. → Shorten the cycle.

§3.8's time budget bounds the suite's part of *capacity* at a factor of 1.2 to 1.35 in a fall that is
more than twofold; the other part — how many design decisions a day can be taken — cannot be read
from a repository. Between the first two readings nothing here decides. §4 q3 registers what would.

## 4. Questions for review

1. **What is "the base", named?** The parking rule in §1 gates on a condition that exists only in our
   heads. Should the base be an explicit ticket set (a tag / umbrella) so b can be measured *within it*
   rather than globally? §3.5 says the global b is currently dominated by one cluster anyway.

   **ANSWERED BY THE TRACKER ON 2026-08-17; NOTICED HERE 2026-10-05 (§3.6).** WI-1126 names it:
   *sorts, rules, operations, the four kernel constructs, unification, the eq family, effect rows*
   are base, and the ticket's fourth part is to say which extensions may still move. It is a gate
   ticket rather than a tag, so b still cannot be measured within it — and after §3.1 that matters
   less than it did. What it leaves open is q15.

   **AND THE BOUNDARY HAS AN OPERATIONAL FORM, stated 2026-10-05 (§3.6):** what is outside the base
   is filed PreOpened. Between 0% and 4% of each month's tickets are born there, so every series in
   this document is, to that tolerance, already measured within the base.

2. **Is b < 1 the right gate, and at what value?** b=0.7 converges in principle but implies 3.3
   descendants per ticket. Is the opening condition "b < 1", "b < 0.5", or "b < X sustained for N weeks"?
   Without an answer the gate has no date and the parking rule is unfalsifiable.

   **2026-10-05.** Not on b at any value: b can no longer be read off this tracker (§3.1). The gate
   WI-1126 states is of another kind — no proposal without a verdict, no undecided hole in the
   spec's base sections — and it has the property this question asked for. It is falsifiable today,
   and today it is false. Successor: q14.

3. **Is b actionable, or only diagnostic?** The claim in §3.5 is that a design pass which settles the
   carrier/spec-op keying and requirement-dictionary questions *ahead* of discovery would retire a whole
   generation at once and drop b. Untested. The rival hypothesis is that a design pass only relabels the
   discovery — the same facts get found, in a document instead of a ticket. **How would we tell the
   difference?** A pre-registered prediction (e.g. "b for the resolve cluster falls below 0.4 in the two
   weeks after the pass") is the cheapest test.

   **PARTLY ANSWERED 2026-09-02 (§3.5).** Actionable per cluster, invisible globally. `simp` fell from
   16.3% to 6.1% of new ticket descriptions after WI-881/884/888 settled what `@[simp]` admits — no
   delivery campaign, the answer retired the tickets — while the global b did not respond, because the
   freed capacity moved into effects/typer/proofs. The rival hypothesis is not excluded: this is one
   uncontrolled observation and `simp` work may simply have run out. **The pre-registered prediction is
   still unmade, and the effects/typer/proof front is the place to make it, before the pass.**

   **REGISTERED 2026-10-05**, to be scored at the next sitting (about 2026-11-05) on the methods of
   §5. Each is this sitting's reading extrapolated, and each names what refutes it.

   1. *The settled half stays settled.* `scope` under 30% and `resolve` under 20% of new ticket
      descriptions (32% and 21% now; 18% and 13% in the later half). Either one back at its August
      level (42%, 27%) refutes "settling retires its generation" for that term.
   2. *Design defects keep surfacing in the requirement half.* At least three more numbered
      proposals that repair the base's design are first committed by then (ten in the last six
      weeks), and `carrier` stays at 40% or above of new descriptions. One or none, with `carrier`
      under 35%, would be the first evidence in this series that the base's design is closing.
      (Rewritten the day it was registered, when §3.5's first reading was corrected; as first
      written it tested "written, not discovered", which no longer needs testing.)
   3. *The stock keeps climbing.* Open + PreOpened + Claimed between 255 and 290 (230 now; +7 to +13
      a week since late August). Under 240 refutes accumulation.
   4. *September does not catch up.* Its cohort is under 75% done (60% now; July and August gained
      12 and 6 points over their second month). 80% or more means absorption was delayed, not
      reduced.
   5. *The suite stays on its curve.* A full run takes between 24 and 28 minutes (16:36 now; 27 at a
      46-day doubling). Under 22 means something bent it, and the 2026-09-27 rule is the candidate.
   6. *The typer experiment — the test this question has wanted since Aug 2.* If E1WN0 lands for a
      rule family before the next ticket in that family, that ticket takes three review passes or
      fewer and no pass is mostly regressions. If it does not land first, the next projection or
      dictionary ticket of 0RP29's size repeats 0RP29's shape: more than five passes. A change of
      method ahead of discovery, with the outcome named in advance, on the one cluster that is not
      converging.
   7. *The author's, given the same day.* The next repairs come in control effects — "a few
      proposals" — because no real program uses the Suspension effect yet (q15: no example file,
      one test file). Scored by where the next numbered proposals land, and by whether the first
      real Suspension program is followed by one.

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

   **BOTH ANSWERED 2026-10-05 (§3.1, §3.9).** (b) Nothing accelerated closure in August. Over all
   tickets born rather than over closers only, the share closed inside a week is 67% → 77% → 79% →
   72% → 58%: one step, in July, and a fall since. The 100% was a young cohort measured without its
   open members. (a) The pair is satisfied today — b = 0.48, or 0.81 on the published recipe; 93% of
   September's closed spinoffs inside a week — in the window where every direct measure of
   accumulation worsened. A gate that reads open under those conditions is measuring something else.
   The pair is withdrawn; q14 replaces it.

5. **Encode the four prose gates?** (§3.6) Adding the WI-294 and WI-128 edges makes `next` and the Open
   count honest — they currently report those as ready. Cost is near zero. Objection: WI-128's
   prerequisite has no ticket, so encoding it means filing one, which itself raises the count.

   **STILL OPEN across two re-measurements 2026-09-02 (§3.6).** WI-294, WI-128 and WI-177 are all
   unchanged; WI-177's gate names a Delivered item and has been stale for a month with `depends_on`
   still empty. A near-zero-cost fix that survives two measurement cycles is not being priced right —
   either the cost is not near zero, or the honesty of `next` is not actually wanted.

   **CLOSED 2026-10-05 (§3.6), and not by encoding anything.** WI-294's edge had been in the tracker
   since before the first sitting — this question was partly about a gap that did not exist. WI-177
   was Rejected as moot on 2026-09-24. Only WI-128 is left, and its prerequisite still has no
   ticket. The lesson is not about pricing: one of the four "prose gates" was mis-recorded *here*,
   twice, by reading a description and not the field beside it.

6. **Does the tracker need a "waiting for a trigger" state?** WI-266 is not blocked by anything — it is
   waiting for a *driver* to appear. That is a third state alongside Open and PreOpened, and it is the
   honest label for a good part of the parked set. Or is PreOpened already that, used loosely?

   **WEAKENED 2026-09-02 (§3.6).** WI-266 was Delivered on 2026-08-15 — the driver appeared. The one
   item that motivated the state closed without it, so the state would have bought nothing here.

   **2026-10-05.** The last sentence of the question is the answer. PreOpened is that state, by
   stated practice and by the tool's own definition (§3.6), and it is used sparingly rather than
   loosely: 24 items, two added in the last five weeks.

7. **Should b be measured per cluster?** A global b averages a converging subsystem with a diverging one
   and reports neither. §3.5 suggests the interesting b is per-area. Requires an area tag on tickets.

   **PROMOTED TO A FINDING 2026-09-02 (§3.5).** No longer a suggestion: over Aug 3 – Sep 2 the global b
   was flat *while* one cluster retired by two thirds and another grew by the same amount. The global
   number averaged them and reported neither. The blocker is unchanged — it needs an area tag.

   **2026-10-05.** Still no area tag. §3.5's term shares stand in for it, and they now disagree with
   the global figure in exactly the way this question predicted: the global b halved while one
   cluster's share of new tickets rose by half and two others' fell by a quarter.

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

   **ANSWERED 2026-10-05 (§3.1) — it does not matter, because there is almost none.** It needed no
   transition log, only a different diff. Each commit against its own parents, the whole history
   holds 1,246 close events over 1,241 items: **five** items were ever closed twice (WI-019, WI-088,
   WI-644, WI-880, WI-20260829-ARQ5X). The "70 items closed and later reopened" of Aug 2, the 126 of
   Sep 2 and the 171 the published recipe reports today are branches re-entering the walk. Work in
   this tracker stays done. What does not stay still is the instrument: the same artefact is in
   every "closed" column above, at 9% through Aug 2 and 34% since Sep 2.

9. **Is prose outgrowing code a convergence signal or the next debt?** (§3.7, new.) Production prose is
   now 107 lines per closed ticket against 92 lines of code, and 42% of all production lines. The
   optimistic reading is that it is why spinoff time-to-close collapsed — the invariants are written
   where the next reader trips over them. The pessimistic reading is that it is unmeasured, unversioned
   duplication of `docs/kernel-language.md` that will need its own retirement pass. Nothing here
   distinguishes them. What would: whether a doc-commented site is *cited* by a later ticket.

   **2026-10-05 (§3.7).** Prose is 44.7% of production lines and at parity with code exactly where
   the design is still moving — 1.00 lines of prose per line of code in the typer, 1.01 in the
   resolver, against 0.3–0.56 in the generators, the parser and the tools. Prose concentrating where
   the code changes most is the pessimistic reading's shape, and one commit shows what a reversal
   costs outside the code: when proposal 070 changed what a bare sort name means, `f8b69009` rewrote
   52 references in 14 documents and 349 in 84 test files.
   The optimistic reading lost its one piece of evidence with §3.1 — time-to-close did not collapse.
   The citation test is still unmade.

10. **Should code size be a tracked series at all?** It is now (§3.7), and it immediately contradicted
    a working assumption — 80,476 production lines added in a month under a "no new functionality"
    intent, with deletions at 8–15% of additions every week. The number worth watching is probably not
    total size but production code per closed ticket, which flattened this month for the first time.

    **2026-10-05 (§3.7).** It is the number worth watching, and it had not flattened: the "99" it
    flattened from was a reformat. Net of that, per close event: 47, 55, 48, 92, 102, 138. Per item
    actually closed: 53, 63, 61, 120, 141, **231**. Doubling in the second half of August and again
    since — the plainest single statement of what changed in this window.

11. ~~**Are the corrections adding behaviour or replacing it?**~~ **ANSWERED 2026-09-02 (§3.7).**
    Adding. The delete/add ratio in production files is flat at 20–27% across four months, and the
    month added 1,092 functions and 166 type declarations. But control-flow surface grew at 23–35%
    against 52% for lines, and lines per `fn` broke a two-month flat line — so the growth is
    increasingly *length per decision*, not new decisions. Successor: **which subsystem is the
    lines-per-`fn` rise in?** If it is the four unsettled clusters of §3.5, it is the cost of
    working around an unanswered question, and settling the question is the cheaper fix — that is
    exactly what `simp` demonstrated.

    **THE SECOND HALF IS WITHDRAWN 2026-10-05 (§3.7).** "Adding" stands. "Increasingly length per
    decision" does not: lines per `fn` went 21.2 → 24.3 inside one commit, `10191d6a Format Rust
    workspace`, and net of it lines and surface grew in step in August (33% against 23–35%) and
    again this month (22.5% against 17.5–22.4%). The successor question has no subsystem for an
    answer. Its replacement is q17.

12. **What bends the test-suite curve, and when is it worth bending?** (§3.8.) Wall clock doubles
    every 32 days with a clean fit and no inflection, currently 10:13 for 6,339 tests, and cost per
    test has risen 4.7× — so this is not solved by running fewer tests. The first thing to establish
    is whether the per-test rise is stdlib load, since every test pays it; §3.1 measured that load at
    40 ms in a window where the stdlib has since grown 2.5×. **This is the only series in this
    document that is unambiguously diverging**, and unlike b it has a hard limit: attention.

    **2026-10-05 (§3.8).** It bent to a 46-day doubling and nothing here says why; the logs that
    could have dated the bend no longer exist. The stdlib-load measurement is still not
    taken, and the stdlib (+12%) cannot be all of the per-test rise (+21%). "When is it worth
    bending" has a first number: a full run is a quarter to a third of a validation cycle, three of
    them go into each closed item, and a suite as fast as August's would buy a fifth to a third more
    cycles. Worth doing; not the factor of two.

13. **Should a ticket record where it came from?** (§3.1, new.) Fan-out was readable off the
    history while a follow-up was filed in its parent's closing commit. It no longer is: the
    bracket is [0.36, 1.30]. An optional `origin: WI-…` attribute, written when a ticket is filed
    out of work on another, would make b exact and independent of how commits are cut — the same
    shape of request as q8's transition log, which turned out not to be needed. This one is.

14. **What is the gate now?** (§3.9; successor to q2 and q4a.) Three candidates can be read today,
    and none is a branching factor: WI-1126's own acceptance (false: no proposal has a verdict); the
    unparked backlog in weeks of closing (5.8; it was under 2 through August); and whether a cohort
    arrives behind its predecessor (September did). The first is the only one that says what to
    *do*. With q15 answered there is a fourth, and it is the one closest to §1's own words: **a
    month in which no new proposal has to repair the base's design.** There has not been one since
    the repairs began in August.

15. **Are proposals 059–070 the base, or a front?** (§3.5, §3.9.) If the base, it is by
    construction not stable until they stop, and §1 is waiting on a decision rather than a
    measurement. If a front, it is the one front that was never parked, and it is the one producing
    the tickets. Either answer gives the parked chains a date. Having neither is what leaves them
    without one — and WI-188 shows the cost running the other way, a parked head acquiring a
    prerequisite from the newest proposal.

    **ANSWERED 2026-10-05: base — and repairs to it, not additions.** Put at the end of the sitting
    and answered the same day by the author of the proposals, in three statements. *Every proposal
    after 060 is the fix of a design defect.* *What is outside the base is filed PreOpened.* *There
    is no date, because much of the base is still underspecified — and more repairs are expected,
    next in control effects, where no real program yet uses the Suspension effect.*

    What follows. §3.5's first reading — "written, not discovered" — was wrong, and is corrected
    there and in §3.9. §1 is being applied consistently: WI-188 waiting on 069 is a parked head
    waiting on base work. And "the base is stable" means *its design defects have stopped
    surfacing*, which is a rate after all, counted in repairs:

    ```
    001 – 060   Feb – Aug 7     the design   58 main-sequence proposals
    061 – 064   Aug 21 – 25     repairs       4
    065 – 068   Sep 19 – 26     repairs       4
    069 – 070   Oct 3           repairs       2
    ```

    Two measurements say where the remaining ones are, and both can be repeated at every sitting.

    *What the spec itself says is open.* `docs/kernel-language.md` cites work items by id, and the
    ones still Open, Claimed or PreOpened mark sentences the spec knows it cannot finish yet:

    | | spec lines | tickets cited | of them still open |
    |---|---|---|---|
    | Aug 2 | 2,819 | 89 | 8 |
    | Sep 2 | 5,618 | 255 | 17 |
    | Oct 5 | 6,862 | 338 | **21** |

    Seven of the 21 are cited under §5.3 (rules), three each under §5.2 (sorts) and §8.1 (the type
    system), and two under §12.1 — WI-069 and WI-070, the Suspension and Branch effects, Open since
    April.

    *What no real program has exercised.* Files that name each effect the standard library declares,
    as example files / test files: `Error` 35 / 152, `External` 31 / 14, `Permission` 23 / 4, `Modify`
    11 / 72, `Branch` 3 / 13, `Suspension` **0 / 1**. `Error`, the most exercised, got its repair
    once its programs existed (027.4, Sep 9). `Permission` arrived with the program that needed it
    (064, the guardians example). `Suspension` has no program and no repair yet, and it is where the
    author expects the next ones. That is §3.7's guardians observation — writing a program in the
    language is what finds the hole — turned into a forecast: **the base's design closes area by
    area as each area gets a real program, and an area with none is a reservoir of repairs not yet
    counted.**

    So the gate has no date, and the reason is no longer that a rate is unmeasured. It is that the
    list is unwritten: the 21 above, plus every base construct no real program has used. That list
    is WI-1126's first part. Written, it turns §1's "until the base is stable" into a count that
    goes down.

16. **Can the inside of a ticket be measured?** (§3.1.) Passes per ticket and regressions per pass
    are now where the branching is, and the only record is prose in ticket notes — 0RP29's "eight
    passes, fourteen of fifteen" survives because someone wrote the sentence. E1WN0's committed
    verdict files would turn the second into a diff. Until then this document cannot see the
    process it was written to watch.

17. **Is the last fortnight's deletion the start of consolidation, or four coincidences?** (§3.7.)
    Deleted-to-added on moved-line-proof counts ran 14–19% for four months and is 30% since Sep 20,
    with four named mechanisms removed. If it holds above 25% next sitting while the typer's
    lines-per-day falls, the code has started retiring alternatives instead of accreting them —
    which is what §3.7 was set up to detect and is the first thing in this series that would look
    like the base stabilizing from the inside.

## 5. Method (reproduce)

Both series come from ID-set diffs between consecutive commits touching the tracker, so a status
rewrite is never miscounted as a creation.

**"Consecutive" is the flaw (2026-10-05).** The recipe below diffs each commit against the previous
one *in `git log` order*, which on a branchy history is frequently not its parent. It is kept
because every number before this sitting was produced by it and must stay reproducible; the second
recipe, further down, diffs each commit against its own parents and is the one to trust from here
on. §3.1 has both series side by side.

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
#   2. the LAST row must agree with the tree the recipe actually walked
git ls-files 'anthill-todo/*/*.anthill.md' | wc -l           # 1298 at 2026-09-02  -> n=
git ls-files 'anthill-todo/delivered/*.anthill.md' \
             'anthill-todo/verified/*.anthill.md'  | wc -l   # 1097 at 2026-09-02  -> k=
```

`git ls-files`, not `ls`, and that is the whole point of check 2: the recipe walks
`git ls-tree` over COMMITS, so comparing it against the working tree makes it fail for a
reason that has nothing to do with the recipe the moment anyone has an unstaged ticket.
Measured while writing this section — one untracked work item and `ls` answers 1299
against the recipe's 1298, in a check whose job is to catch a silent miss. (The id-scheme
count above, 175 of 1298, is on the tracked set for the same reason.)

Note the `/*.anthill.md` glob too: `ls anthill-todo/{delivered,verified} | wc -l` counts the
two `dir:` headers and a blank separator as well, and answers 1100.

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

**2026-10-05: the fullest run is not always a clean one.** On 2026-10-02 the run with the most tests
passed took 57:50 while the two other full runs that day took 15:29 and 15:43 — a stall, chosen by
the rule because it happened to pass 94 more tests. From this sitting the wall clock is the *median*
over the day's full runs, a full run being one whose tests run (passed plus failed) come within 3%
of the day's largest passed count; the run count and the summed elapsed time per day come from the
same pass over the logs. No binary-count filter is involved, and adding one changes nothing.

**Second recipe (2026-10-05): each commit against its own parents.** With a pathspec, `--parents`
rewrites every listed commit's parents to its nearest ancestors that also touch the tracker, so the
diff below is between a commit and what it was actually built on. A merge is diffed against the
union of its parents and normally contributes nothing.

```python
#!/usr/bin/env python3
# Run from the repo root. One row per ISO week, then the lifetime totals.
import datetime as dt, re, subprocess
from collections import defaultdict

def git(*args):
    return subprocess.run(["git", *args], capture_output=True, check=True).stdout.decode("utf-8", "replace")

FILE = re.compile(r"^anthill-todo/([a-z_]+)/(WI-[A-Za-z0-9_-]+)\.anthill(\.md)?$")
REC_ID = re.compile(r'id:\s*"(WI-[A-Za-z0-9_-]+)"')
STATUS = re.compile(r"status:\s*(Open|Claimed|Delivered|Verified|Rejected|Stale|PreOpened|ProposalRejected)")

def sets(sha):
    """(every id in the tracker at this commit, the ids that are closed)."""
    tree = git("ls-tree", "-r", "--name-only", sha, "--", "anthill-todo/").splitlines()
    if "anthill-todo/workitems.anthill" in tree:                 # before 2026-08-17
        text = git("show", f"{sha}:anthill-todo/workitems.anthill")
        closed = set()
        for record in text.split("fact WorkItem("):
            name, statuses = REC_ID.search(record), STATUS.findall(record)
            # ANY record of an id being closed closes it: an id carried by two
            # records must not be decided by whichever came last.
            if name and statuses and statuses[-1] in ("Delivered", "Verified"):
                closed.add(name.group(1))
        return set(re.findall(r'id: "(WI-[A-Za-z0-9_-]+)"', text)), closed
    hits = [m for m in map(FILE.match, tree) if m]               # status is the directory
    return {m.group(2) for m in hits}, {m.group(2) for m in hits if m.group(1) in ("delivered", "verified")}

# --topo-order --reverse yields every parent before its children.
log = [line.split() for line in git("log", "--parents", "--topo-order", "--reverse", "--date=short",
                                    "--format=%H %ad %P", "--", "anthill-todo/").splitlines()]
state, weeks = {}, defaultdict(lambda: [0, 0, 0])
for sha, date, *parents in log:
    ids, closed = state[sha] = sets(sha)
    assert ids, f"empty id set at {sha}: the filename pattern missed an era"
    created = ids - set().union(*(state[p][0] for p in parents))
    newly_closed = closed - set().union(*(state[p][1] for p in parents))
    row = weeks[tuple(dt.date.fromisoformat(date).isocalendar()[:2])]
    row[0] += len(newly_closed)
    row[1] += len(created) if newly_closed else 0                # co-filed: the commit also closes
    row[2] += len(created)

total = [sum(r[i] for r in weeks.values()) for i in range(3)]
for (year, week), (closed, spinoffs, created) in sorted(weeks.items()):
    print(f"{year}-W{week:02d} closed={closed:4d} spinoffs={spinoffs:4d} created={created:4d}")
print(f"commits={len(log)} closed={total[0]} spinoffs={total[1]} created={total[2]} b={total[1] / total[0]:.3f}")
```

It takes about a minute, and its last line on 2026-10-05 is
`commits=2245 closed=1246 spinoffs=734 created=1517 b=0.589`. Its own check is the pair on that line
against the tracker: 1,246 close events must sit just above the number of items ever closed (1,241
— five were closed twice), where the first recipe's 1,490 sits 249 above it. **The gap between the
two recipes' totals is the artefact, and it should be printed at every sitting**: 16% of close events
lifetime, 34% in the newest window.

A ticket's birth, on this recipe, is the earliest commit that creates it and its close the earliest
commit that closes it; the cohort tables of §3.1 and §3.4 use those, and a "spinoff" is a ticket
whose birth commit also closes something.

**Definitions the 2026-09-02 sitting used and did not write down.** Recovered on 2026-10-05 by
matching its recorded numbers, each to the digit unless it says otherwise. They are here so that the
next sitting spends its time measuring.

- *Cohorts in the first recipe* (§3.4, and the n / closed columns of §3.1's Sep 2 table): a ticket's
  birth is its **last** creation event in log order, not its first as the caveat below says, and it
  is a spinoff if that event's commit closes something. "First" moves one id from August to May.
  The percentage columns of that table do not reproduce under any of twenty date and timestamp
  definitions tried — same-day lands within 5 points and within-7-days within 2 — which is why
  §3.1's 2026-10-05 table restates every row instead of extending it.
- *§3.5's terms*: a whole-word, case-insensitive match (`\bterm\b`) over the `## Description`
  chapter only — not the `## Changes` notes — of each distinct birth in the window. A substring
  match more than triples `simp` and doubles `resolve`. Descriptions are edited after filing, so an
  old window re-read on today's tree drifts by a ticket or two; the 2026-09-02 columns were matched
  on the tree of `e0cc3692`, the W31 column exactly and eleven of the thirteen Aug rows (§3.5).
- *§3.7's line kinds*: a file is a test file when its path contains `test` (that takes in
  `…/tests/…`, `kb/typing/tests.rs` and `kb/test_support.rs`). Elsewhere, a test block is a
  `#[cfg(test)]` attribute **on a `mod`**, brace-matched, or two lines for `mod name;`. A
  `#[cfg(test)]` on a field, a `fn` or a `use` is production: brace-matching from a struct field
  runs on to the next unrelated `{` and took 732 lines of `kb/mod.rs` with it on the first attempt.
  A line is blank, doc (`///`, `//!`), comment (any other `//`, or inside `/* */`) or code.
- *§3.7's surface*, over production code lines only: `fn` is `^\s*(pub(\([^)]*\))?\s+)?fn\s+\w`
  (so not `const fn`, and not `fn $name` in a macro); `pub fn` is `^\s*pub(\([^)]*\))?\s+fn\s`;
  a match arm is a line containing `=>`; `if` / `else if` is `^\s*(\}\s*)?(else\s+)?if\b`, which
  also takes a guard continued after a multi-line pattern (`} if …`, 61 of them on Sep 2);
  `struct` / `enum` is `^\s*(pub(\([^)]*\))?\s+)?(struct|enum)\s+\w`.
- *§3.7's added and deleted lines*: a tree-to-tree `git diff --numstat` between two snapshot
  commits, by the same path rule — **not** a sum over the commits in between, which counts a line
  written and rewritten twice and gives +52,440 / −15,543 where the table says +46,445 / −9,537.
  The four recorded rows are bounded by the last commits of May 31, Jun 30, Jul 31 and Aug 16 and
  by the Sep 2 sitting, and all four reproduce.
- *Snapshots*: the last commit of the day, UTC — `fba8c613` Jun 7, `0767d834` Jul 5, `699f198c`
  Aug 2, `c09f3f58` Aug 16, `7ae08e01` Sep 20 — except the two sitting days, which are read at the
  sitting: `c752fff3` Sep 2 (the day's last commit holds 1,112 lines more) and `cc948805` Oct 5.

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
  use it. Age is measured from the commit an id first appears in. (2026-10-05: on the first recipe
  the recorded cohorts were in fact keyed on the commit an id *last* appears in — see the recovered
  definitions above. The second recipe uses the first, as this sentence always said.)
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

Added 2026-10-05:

- **A recipe that reproduces is the same instrument, not a correct one.** The first recipe gave back
  every recorded number to the digit at this sitting, and a third of its newest events never
  happened (§3.1). What caught it was not a re-run but a conservation check: close events cannot
  exceed the items ever closed by more than the handful genuinely closed twice, and 1,490 against
  1,241 does. Every event series here now gets that check.
- **A map keyed by id is not the first recipe.** In the single-file era 1,494 commits carry some id
  on two records. The recipe prints an id for *every* record whose last status is closed and then
  `sort -u`s, so an id is closed when any of its records is. Porting it to one process with a map
  from id to status lets the last record win and reports 1,277 / 818 where the recipe says
  1,275 / 815 — two phantom closes, one in W28–W31 and one in W32. Small, silent, and found only
  because the old rows are checked to the digit before a new one is trusted.
- **Closers-only favours whatever is young.** A cohort a few days old, measured over the tickets
  that have closed, contains only tickets that closed in a few days. §3.1's "100% within a week"
  was that. Divide by every ticket born at least as long ago as the window being claimed.
- **A reformat is growth to a line counter, and a file split is a rewrite to a diff.** `10191d6a`
  (`cargo fmt`, 606 files) added 27,314 lines and no behaviour and was read on Sep 2 as functions
  growing longer; `7706ae6c` (one file into 51) reads as 80 thousand lines deleted. Before trusting
  any per-line or per-function trend, list the commits that touch a hundred `.rs` files or more —
  there are nine in this history — and for churn use the multiset difference of non-blank lines
  between two trees, which no move can inflate.
- **`target/` is not an archive.** The 9,050 test logs behind §3.8's first table were gone within
  three weeks of its writing. What a sitting wants to keep from a build directory has to be in this
  file when the sitting ends.
- **Read the field before the prose.** §3.6 carried "real prerequisite, no edge" for WI-294 across
  two sittings while `depends_on` held the edge. A statement here about what the tracker does *not*
  record must be checked against the attribute, not the description.
