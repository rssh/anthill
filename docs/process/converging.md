# Converging — does the base stabilize?

Notes on the ticket-generation dynamics of this project, and the open questions they raise: a
running series over the `anthill-todo` tracker's git history, measured at sittings on 2026-08-02,
08-06, 09-02, 10-05, 10-25 and 11-23.

This file holds the latest sitting — the state table, each series' latest reading (§3), the reading
of the whole (§3.11), the questions still open (§4) and the method (§5). Every earlier sitting's
measurements and readings, and the history of each question, are in
[`converging-history.md`](converging-history.md) under the same section and question numbers, so a
§ reference resolves in whichever file holds it. At each sitting the reading it replaces moves
there, and the state table is replaced.

Numbers rot, and so does the method. The tracker changed layout on 2026-08-17; on 2026-10-05 a third
of the newest window's events turned out never to have happened, which is why §5 carries a second
recipe; on 2026-10-25 a term's share of new tickets turned out to move with their length. §5
records each, so that a sitting checks the last one's numbers before trusting its own.

## State at the latest sitting (2026-11-23)

| series | 2026-10-05 | 2026-10-25 | **2026-11-23** | § |
|---|---|---|---|---|
| items closed per day (own parents) | 4.3 | 6.5 | **5.0** | 3.1 |
| tickets filed per day | 5.6 | 8.6 | **4.9** | 3.1 |
| b, co-filed only | 0.36 | 0.35 | **0.16** | 3.1 |
| every ticket filed ÷ closed | 1.30 | 1.32 | **0.99** (0.77, then 1.31) | 3.1 |
| Open + PreOpened + Claimed | 231 | 267 | **261** | 3.3 |
| the same outside the parked set, in weeks of closing | 5.8 | 5.1 | **6.2** | 3.3 |
| September cohort delivered | 60% | 70% | **83%** | 3.4 |
| `carrier` in new ticket descriptions | 49% | 26% | **28%** | 3.5 |
| `dictionary`, per 1,000 words of new descriptions | 1.19 | 0.91 | **2.98** | 3.5 |
| parked set | 45 | 42 | **42** | 3.6 |
| production code lines added per day | 788 | 1,584 | **1,270** | 3.7 |
| typer share of production code | 33% | 38% | **42%** | 3.7 |
| src lines deleted ÷ added, moves excluded | 20% | 21% | **28%** (39%, then 19%) | 3.7 |
| full test run on this machine | 16:36 | 2:49 | **5:38** | 3.8 |
| numbered proposals that repair the base, since Aug 21 | 10 | 13 | **16** | 4 q15 |
| WI-1126, the freeze gate | no note | no note | **one verdict, no note** | 3.6 |

Rates in the Oct 5 column are over Sep 3 – Oct 5, in the Oct 25 column over the twenty days since
that sitting's commit, `cc948805`, and in the Nov 23 column over the 29 days since the Oct 25
sitting's tracker commit, `d6a28558`; counts are as of each sitting. Where a cell carries two
numbers in brackets they are the window's two fortnights, split at `e3f98bcd` (Nov 8).

## 1. The policy this measures

Work is not started on a parked front (scaland resync, Cell runtime, staging brackets, effect rows)
until the base is stable; 42 items born before June wait under that rule (§3.6). The rule is only
safe while the base actually converges. If base work generates work faster than it retires it, the
gate never opens and the parked fronts wait forever — that is what this document measures.

The gate has a ticket, WI-1126 (*0.1.0 base interpreter feature freeze*, filed 2026-08-17). It
states the opening condition as a deliverable — every proposal carries a verdict, the spec's base
sections hold no undecided hole — not as a rate (§3.6, §4 q14). What is outside the base is filed
PreOpened (§4 q1). The metric this document was first written for, the branching factor b (§2),
stopped measuring fan-out when follow-ups stopped being filed in their parent's closing commit (§2,
§3.1); the state table carries the series that took its place. The earlier counts are in the
history file's §1.

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

## 3. The series, at the latest sitting (2026-11-23)

Each subsection says what its series measures and gives the latest reading. Every earlier reading
is under the same number in the history file, with the caveats that came with it.

### 3.1 Closing, filing and b

Close and creation events per ISO week, each commit diffed against its own parents (§5, second
recipe); b — tickets filed in a commit that also closes something, over items closed (§2) — and the
bracket that holds the real fan-out since filing left the closing commit; time-to-close by birth
cohort. The first recipe's series, and every earlier window, are in the history file's §3.1.

#### Re-measured 2026-11-23 — filing fell to closing, for one fortnight

29 days, on the second recipe. Every week through W42 reproduces to the digit on both recipes. W43
moved from 43 / 9 / 41 to 45 / 10 / 46 because the Oct 25 sitting read it at `d6a28558`, on the
morning of its last day; the first recipe's W43 moved from 83 to 87 the same way. The window is
`git rev-list d6a28558..234cbe83` (§5), and the same cut over `cc948805..d6a28558` gives back the
Oct 25 window's 130 / 46 / 171 and §3.2's buckets exactly.

| week | closed | spinoffs | **b** | created | log order: closed |
|---|---|---|---|---|---|
| W43 (Oct 19–25, full) | 45 | 10 | 0.22 | 46 | 87 |
| W44 (Oct 26 – Nov 1) | 43 | 0 | 0.00 | **14** | 46 |
| W45 (Nov 2–8) | 43 | 11 | 0.26 | 49 | 73 |
| W46 (Nov 9–15) | 24 | 1 | 0.04 | 33 | 27 |
| W47 (Nov 16–22) | 31 | 11 | 0.35 | 42 | 54 |
| W48 (Nov 23 only) | 3 | 0 | — | 1 | 3 |
| **W44–W47** | **141** | **23** | **0.16** | **138** | **200** |

Lifetime 1,522 close events over 1,517 items ever closed — the Oct 25 total and this window's 146,
and still the same five closed twice — and b = 0.528. The first recipe reports 1,913: **29% of its close events in this
window never happened** (207 against 146), down from 39%, as merges fell from 14.3% of commits to
8.7% (37 of 424).

| | Sep 3 – Oct 5 | Oct 5 – Oct 25 | **since the Oct 25 sitting** |
|---|---|---|---|
| closed | 142 (4.3 a day) | 130 (6.5 a day) | **146 (5.0 a day)** |
| co-filed only — b as defined | 51 → 0.36 | 46 → 0.35 | **24 → 0.16** |
| + tickets whose filing commit is not a planned stage | (105 → 0.74) | 148 → 1.14 | **113 → 0.77** |
| every ticket filed | 185 → 1.30 | 171 → 1.32 | **144 → 0.99** |

The middle row is cut as on Oct 25. 69 commits that close nothing filed 120 tickets. 31 are planned
work by their commit's subject: proposal 074's stages (10), 073's (4), 051's second phase (4),
010.1's sequence (3), the correction sequences of 002 and 004 (2 each), library proposal 001-map's
phases (2), the two question maps' tickets (2), 060.1's (1) and the second stage of
`docs/design/spec-carrier-set.md` (1). Eight were filed on Nov 22–23 **for anthill-traces**, a
program outside this repository that uses `anthill-core` as a library — a public builder, contract
clauses as written, a resolution budget on `KB.execute`, a build as a cargo git dependency. Six were
found **writing a program in the language** — an e-commerce shop's state modelled as a value
(Nov 15) and what its specification then needed (Nov 21). The other 75 say they were found in
other work, as before.

**Every ticket filed ÷ closed reached 0.99, the first window in the series at or under 1** (1.13
over W20–W31, 1.14 over W32–W35, 1.30 to 1.35 in every window since). It is one fortnight. Split at `e3f98bcd` (Nov 8): Oct 25 → Nov 8
closed 88 and filed 68, **0.77**; Nov 8 → Nov 23 closed 58 and filed 76, **1.31** — the level of
the three windows before. W44 alone closed 43 and filed 14. Seven deliveries in eight now file
nothing in their own commit (§3.2).

Time-to-close, all cohorts on today's tree:

| born | spinoff n / closed | same-day | ≤7d | injected n / closed | same-day | ≤7d | **all born: closed ≤7d** |
|---|---|---|---|---|---|---|---|
| through Jun | 283 / 249 | 62% | 80% | 316 / 286 | 36% | 71% | 67% |
| Jul | 171 / 163 | 52% | 82% | 139 / 129 | 43% | 82% | 77% |
| Aug 1–6 | 73 / 68 | 63% | 90% | 44 / 41 | 51% | 76% | 79% |
| Aug 7–31 | 120 / 115 | 57% | 82% | 130 / 106 | 46% | 81% | 72% |
| Sep | 68 / 58 | 40% | 71% | 118 / 97 | 33% | 67% | 57% |
| Oct 1–5 | 3 / 2 | — | — | 28 / 23 | 9% | 22% | 23% |
| Oct 6–18 | 37 / 25 | 40% | 72% | 87 / 62 | 34% | 69% | 49% |
| Oct 19–31 | 10 / 4 | — | — | 49 / 31 | 26% | 81% | **49%** |
| Nov 1–15 | 12 / 3 | — | — | 71 / 36 | 33% | 86% | **41%** |

The closers-only columns of the September and October rows went on falling as their slow members
closed (Sep's spinoffs within a week: 93% on Oct 5, 84% on Oct 25, 71% now), the 2026-10-05 caveat
at work. The last column is the one that holds: **the share of new tickets closed within a week has
not come back** — 67, 77, 79, 72, 57, then 23, 49, 49, 41. The stock fell in W44 (§3.3) while the
tickets born around it closed no faster.

### 3.2 Spinoffs per delivery

Closing commits by how many tickets they file in the same commit, each commit against its own
parents. Through August about three deliveries in five filed nothing; since September four in five
or more (history §3.2).

**2026-11-23.** Same cut, 136 closing commits since the Oct 25 sitting: no spinoff 119 (87.5%), one
13 (9.6%), two 2 (1.5%), 3–4 2 (1.5%), `>4` none. The Oct 25 row reproduces exactly. Seven
deliveries in eight file nothing, and none filed more than four.

### 3.3 The open stock

Open + PreOpened + Claimed on `main` at each week's end (Sunday); the same outside the parked set in
weeks of work at the window's closing rate; the status census; creation over closure. The weekly
series from June is in the history file's §3.3.

**2026-11-23.** Open 240 → **230**, PreOpened 26 → **30**, Claimed **1**, closed 1369 → **1515**
(1476 Delivered + 39 Verified), plus 16 Rejected, 2 ProposalRejected, 4 Stale — **1,798** total.
`anthill-todo list --status open --unblocked` answers **190** (189).

```
Oct 25  267    Nov  1  240    Nov  8  245    Nov 15  250    Nov 22  263
```

(Oct 25 is the sitting's reading at `d6a28558`; the day ended at 270.) **The first fall across a
sitting window: 267 → 261.** It is one week — −30 in W44, which closed 43 and filed 14 — and then
+5, +5, +13, the climb of every week since late August. §3.10 named the falsifier of its reading
as "the Open stock turning down at the current way of working", and recorded that since Aug 16 no
reading had been lower than the one two weeks before it. Nov 1 (240) is lower than Oct 18 (271).
What the way of working was that week is §3.7's: the fortnight that deleted the most.

In weeks of work the unparked set reads **219 against 35 closes a week (W44–W47) — 6.2**, up from
5.1 because the divisor fell. Creation against closure, each commit against its own parents: W44–W47
138 / 141, **0.98** (1.30 for W41–W43; 1.02 on the published recipe).

By birth month, what is Open today: 62 born in November, 61 in October, 28 in September, 26 in
August, 19 in June and July, 34 before June. 109 of the 230 carry a tag: 59 `typing`, 10
`proposal-068` (18), 6 `proposal-074`, 5 `proposal-037`, 4 `guardians`, 4 `library-001-map`, 3
`proposal-050.1`. 31 carry a `proposal-…` stage tag, against 40.

### 3.4 Absorption, by birth month

The share of each month's births Delivered or Verified today, birth keyed on the second recipe
(§5). A cohort is compared with its predecessors at the same age.

**2026-11-23**, same keying; every born count through September is unchanged:

```
2026-03  born  38  done  32  (84%)
2026-04  born 110  done  91  (83%)
2026-05  born 204  done 178  (87%)
2026-06  born 247  done 234  (95%)
2026-07  born 310  done 291  (94%)
2026-08  born 367  done 330  (90%)
2026-09  born 186  done 154  (83%)   60% → 70% → 77% (Nov 5) → 83%
2026-10  born 214  done 147  (69%)   twenty-three days after its end
2026-11  born 126  done  58  (46%)   twenty-three days old
```

**September caught up.** At 83% eight weeks after its end it stands three points under August at
the same age (86% on Oct 25), and October, at 69% twenty-three days after its end, is where
September was at twenty-five (70%). Absorption was delayed, not reduced — the alternative §4 q3's
fourth prediction named. The born column sums to 1,802: the tracker's 1,798, WI-647, WI-874, and two
deleted on Nov 13, WI-20261113-XD6HP (filed from a mistyped witness, its rule withdrawn) and
WI-20261113-26390.

### 3.5 What new tickets are about

Whole-word, case-insensitive matches in the `## Description` chapter of each ticket born in the
window (§5): the share of descriptions naming a term, and its occurrences per thousand words. A term
has retired where both fall; a share that falls alone may only be shorter descriptions.

**2026-11-23 — two fronts retired, and the requirement cluster came back under another word.** Same
method; the Oct 5 – Oct 25 column reproduces on today's tree in all twelve rows, both measures. New
window: the 144 births since the Oct 25 sitting, 142 with a description today (two were deleted).
Median description 322 words (357).

| term | Oct 5 – 25 | **since Oct 25** | per 1,000 words, Oct 5 – 25 | **per 1,000 words, since** |
|---|---|---|---|---|
| carrier | 26.3% | 28.2% | 1.73 | 1.84 |
| requirement | 18.1% | 22.5% | 1.37 | 1.11 |
| dispatch | 13.5% | 13.4% | 0.45 | 0.56 |
| **dictionary** | 11.1% | **26.8%** | 0.91 | **2.98** |
| **provider** | 18.7% | **24.6%** | 1.06 | **2.35** |
| witness | 8.2% | 7.0% | 0.42 | 0.76 |
| rigid | 4.1% | 6.3% | 0.29 | 0.33 |
| typer | 23.4% | 16.2% | 0.88 | 0.73 |
| effect | 14.0% | 12.0% | 0.57 | 0.89 |
| label | 12.3% | 4.9% | 0.69 | 0.87 |
| **proof** | 12.9% | **5.6%** | 1.31 | **0.67** |
| resolve | 8.8% | 15.5% | 0.22 | 0.49 |
| **scope** | 28.1% | **10.6%** | 1.69 | **0.38** |

`scope` fell on both measures, to a quarter of its density, once the scope of an operation's own
names was settled (GJVVW, TGAAD, Oct 23–25) — settling a question retiring its tickets again, on
the new scope questions that had doubled its density on Oct 25. `proof` halved on both, the SMT-lowering chains of mid-October done. `carrier` and
`dispatch`, which halved on Oct 25, did not go on falling; they are flat.

**`dictionary` tripled per word and `provider` doubled** — in the second fortnight `dictionary` is
in 28% of new descriptions at 3.39 per thousand words, the densest any term has been in this
table. These are the words that rose with `carrier` on Oct 5 ("the typer's requirement machinery":
`parameter`, `slot`, `dictionary`, `provider`, `witness`), and the window's three repairs are all
there: 060.1 (a rule takes a dictionary only where it writes one), 073 (a value of an abstract type
is an instance of its sort, and no carrier or provider is chosen at run time) and 074 (a typeclass
instance is a dictionary, and is written as one). So §3.10's "the cluster that was not converging
is retiring its tickets" read a change of vocabulary as a retirement. The question moved from *who
answers this call* (`carrier`, `dispatch`) to *what a value carries* (`dictionary`, `provider`),
and it is the same cluster. `docs/design/spec-carrier-set.md` (Nov 22) gives its size in the
implementation's own terms: one carrier parameter computed per spec by an inference the spec calls
"the rule as implemented", read by about 120 sites.

`resolve` went the other way, 0.22 → 0.49 per thousand words and 18.9% of descriptions in the
second fortnight: the resolver read by new consumers — a resolution budget and a depth that counts
nesting (0WT09), a failing search that re-enters choice points, the proof of a goal (075).
`acceptance` is back in 82% of descriptions, from 55%.

### 3.6 The parked set and the gate

Items born before June and still Open or PreOpened — the fronts §1 parks — the chains they form,
and the gate ticket WI-1126.

**2026-11-23.** Parked set **42**, the same 42 items: none left, none joined, in 29 days.

| head | waits on |
|---|---|
| WI-020 (guard analysis) | WI-556, PreOpened |
| WI-156 (scaland resync) | WI-1126, WI-069, WI-070, WI-294 (WI-152 and WI-153 closed; WI-294 added in the dependency review of Nov 2) |
| WI-188 (`.copy` → staging brackets) | proposal 069's stage 4, WI-20261023-FHT5Z (stage 3, CX743, Delivered Oct 24) |
| WI-207 (acyclic_cell) | nothing — ready |

**WI-1126 has its first verdict and still no note.** On 2026-10-30 `27a060a9` rejected proposal 005
(`extends` and sort inheritance) under it — every case 005 names is an existing clause, `requires`
or a spec's provision — and `docs/proposals/rejected/` holds it beside its README. It is the one
verdict in fourteen weeks; the ticket's own file has not changed since 2026-08-19. The population
to triage is 85 numbered files (060.1, 073, 074, 010.1 and 075 added, 005 decided), and the typer
under its premise "the base type system is written" holds 87,597 lines of production code (§3.7).
PreOpened 26 → 30, four born there: 074's stage 7, 010.1's documentation stage, a rule body with no
shadowing (WI-20261121-9WMZ1, which the spec cites as open), and a status of its own for
`type_value` (WI-20261103-WEHYP, "in future").

### 3.7 Code size

`rustland` Rust by line kind with §5's classifier; per item closed; by subsystem; control-flow
surface; and churn as the multiset difference of non-blank lines between two trees, which no move
or split can inflate.

#### 2026-11-23 — a fifth slower, and the first fortnight that deleted two lines for every five

The classifier gives back the Oct 25 column to the digit at `d6a28558`, the sitting's tracker
commit, which is therefore the snapshot both windows here start from.

| | Oct 25 | Nov 8 | **Nov 23** | Oct 25 → Nov 23 |
|---|---|---|---|---|
| production code | 173,196 | 189,824 | **210,425** | +21.5% |
| production doc-comment | 79,646 | 82,527 | **86,581** | +8.7% |
| production `//` comment | 47,608 | 46,874 | **48,188** | +1.2% |
| test code | 305,424 | 331,297 | **353,565** | +15.8% |
| test doc + comment | 121,692 | 128,470 | **136,515** | +12.2% |
| blank (both) | 39,298 | 41,855 | **44,432** | |
| **all rustland Rust** | 766,864 | 820,847 | **879,706** | +14.7% |

113 thousand lines in 29 days, against 134 thousand in the twenty before: **production code 1,270
lines a day (1,584), test code 1,642 (3,087)**. Prose fell again: 17% of the production lines added
(29%, and half before that), 39.0% of all non-blank production lines (42.4%), and the `//` comments
of the first fortnight shrank. One commit touches more than a hundred `.rs` files, `d068e45a`
(457 files, +611 / −547 src and +2,497 / −1,847 test: WI-20261113-S4D63 removing the bare host call
form); it is neither a reformat nor a move.

**Per item closed:**

| window | items closed | prod code / item | prod prose / item | test code / item |
|---|---|---|---|---|
| Oct 5 → Oct 25 | 130 | 244 | 100 | 475 |
| Oct 25 → Nov 8 | 88 | 189 | 24 | 294 |
| Nov 8 → Nov 23 | 58 | 355 | 93 | 384 |
| **Oct 25 → Nov 23** | **146** | **255** | **51** | **330** |

Production code per item held at about 250; test code per item fell by 30%, prose by half. The
fortnights differ by a factor of two: the second closed fewer and heavier items — WI-20261105-CBRD2
(proposal 073's stage 4: 89 commits, 78 notes) and WI-20261122-CXR5B (fifteen steps) closed in it.

**Where.** Production code lines:

| | Oct 25 | **Nov 23** | share of the growth | prose per line of code |
|---|---|---|---|---|
| `kb/typing` | 65,404 | **87,597** | **60%** | 0.67 |
| `kb/load` | 27,230 | 31,795 | 12% | 0.65 |
| `kb/resolve` | 7,998 | 10,726 | 7% | 0.78 |
| `eval` | 12,205 | 14,584 | 6% | 0.68 |
| everything else | 60,359 | 65,723 | 14% | |

The typer is **42%** of production code (17% on Jun 7, 27% Aug 2, 33% Oct 5, 38% Oct 25) and took
60% of the growth, at **757 lines a day** — 719 to Nov 8 and 794 after — against 913 in the window
before: the first fall of its rate since September. The resolver grew by 2,728 lines, five times its
535 of the window before (§3.5's `resolve`). Prose per line of code fell in every core subsystem.

**Surface, in step:** `fn` 6,875 → 8,250 (+20%), `pub fn` 2,941 → 3,583, match arms 12,033 → 14,266
(+19%), `if` / `else if` 7,242 → 8,863 (+22%), `struct` / `enum` 973 → 1,171 (+20%); lines per `fn`
25.5, per arm 14.7. 1,375 functions in 29 days, 47 a day (64).

**Addition or rework — the highest fortnight in the series.** Multiset difference of non-blank
lines, by the path rule:

| window | src added | src deleted | del/add | test added | test deleted | del/add |
|---|---|---|---|---|---|---|
| Oct 5 → Oct 25 | 59,035 | 12,352 | 20.9% | 88,570 | 7,862 | 8.9% |
| **Oct 25 → Nov 8** | **30,600** | **11,934** | **39.0%** | 39,067 | 6,307 | 16.1% |
| Nov 8 → Nov 23 | 32,896 | 6,277 | 19.1% | 35,146 | 5,483 | 15.6% |
| Oct 25 → Nov 23 | 62,486 | 17,201 | **27.5%** | 73,196 | 10,773 | 14.7% |

Over the window, above the 25% that §4 q17 set as its test while the typer's lines a day fell. By
fortnight, 39% — above the 31% of Sep 20 → Oct 5, the previous high — and then 19%. What the first
fortnight deleted has names, and every one is a mechanism that answered a question a second way:
proposal 060.1 §5 (Nov 4) withdrew the inference of a rule body's requirements —
`kb/typing/anchor.rs` (*rewriting `find_dictionary` goals and anchor grounding*, 1,184 lines)
deleted whole, `kb/typing/rule_requirements.rs` −903; 073's stages 1 and 2 (C6GK8, 89J6K) decided at
load the calls the interpreter chose at run time and stopped filling an operation's own slots from
its argument values; 068 D1b (DEY66) retired the per-consumer reductions and `reduce_op_value`'s
call-by-name fold. In the second fortnight CBRD2 retired the equality index's run-time readers and
the unpinned-goal counter, at a third of the rate.

**Tests.** 199 test files added and **3 removed**, the first removals in the series — each a test of
a retired mechanism (`wi236_call_with_requirements_test`, `wi867_host_dictionary_constructor_test`,
`rule_goal_sort_bracket_refused_test`). Files named by a work item (`/wi[_0-9]` in the path; the
rule behind Oct 25's "812" was not written down): 862 of 1,059 on Oct 25, 1,045 of 1,255 now.

**Examples** +42 / −29 lines in six files; no new example program — the shop model of Nov 15 is not
in this repository. `scaland` 39,144 → 40,767 lines of Scala, 28 commits.

### 3.8 Test execution time on this machine

Wall clock of a full `rustland/scripts/test.sh` run on this machine (WSL2, Intel Core Ultra 9
275HX, 24 cores, 15 GB): the median of each day's full runs, read from the logs under
`rustland/target/` (§5). The logs are not kept, so a reading the history file does not hold is
lost.

**2026-11-23 — it doubled in four weeks, and the logs that would say why are gone again.**
`rustland/target/` holds 903 logs, the oldest of 2026-11-19 10:31; it is 82 GB, against 123 GB on
Oct 25. Nothing is left of Oct 26 – Nov 18. The day table, by the same rules:

| date | tests | wall clock | ms/test | full runs | hours in full runs |
|---|---|---|---|---|---|
| 2026-10-25 (last sitting) | 10,926 | 2:49 | 15 | 11 | 0.5 |
| 2026-11-19 | 12,386 | 5:01 | 24 | 29 | 2.5 |
| 2026-11-20 | 12,434 | 4:58 | 24 | 29 | 2.4 |
| 2026-11-21 | 12,500 | 5:26 | 26 | 12 | 1.1 |
| **2026-11-22** | **12,602** | **5:38** | **27** | 23 | 2.2 |
| 2026-11-23 (to 15:40) | 12,636 | 6:16 | 30 | 7 | 6.9 † |

† One of the seven ran 6 h 21 min, a stall; the other six sum to 0.6 h.

Against Oct 25: tests +15%, wall clock **×2.0**, cost per test 15 → 27 ms. That is a doubling in 28
days, against the 46-day slope that held from August through October, and the projection made on
Oct 25 — four minutes in mid-November, five at the end of it — was passed by Nov 19.
`rustland/scripts/test.sh` and `rustland/Cargo.toml` did not change in the window and the stdlib
grew 4% (9,813 → 10,197 lines), so neither the build setting that bent the curve in October nor the
stdlib load is a candidate; with the logs gone nothing more can be said. A first split, for the next
sitting to compare with: in a full run of Nov 19–22 the first test binary starts at a median 74–86
seconds, so about a quarter of the wall clock is building and three quarters running.

### 3.11 What the 2026-11-23 sitting adds up to

Reading, not measurement. §3.9 and §3.10, the readings of 2026-10-05 and 2026-10-25, are in
the history file.

**1. For one fortnight the stock went down, and it was the fortnight that deleted the most.** Oct 25
→ Nov 8 closed 88 items and filed 68 (§3.1), the Open stock fell by 30 in its first week, the
largest weekly fall since June (§3.3), and its source tree deleted two lines for every five it
added, the series' high (§3.7). The work was consolidation decided in proposals: 060.1 withdrew a rule
body's inferred requirements, 073 moved the interpreter's run-time choice of a carrier to the load,
068 D1b retired the per-consumer reductions. In the second fortnight deleted over added went back
to 19%, filing to 1.31 per close, and the stock climbed by 23. §3.10's falsifier — "the Open stock
turning down at the current way of working" — happened once, at a way of working §3.10 had
proposed. Two weeks are one observation, and the other way round reads as well: a fortnight spent
retiring mechanisms is a fortnight in which little new is built, and little new found.

**2. The cluster that was "retiring" changed its word.** `carrier` and `dispatch` stayed down;
`dictionary` tripled per word and `provider` doubled (§3.5). All three numbered repairs of the
window — 060.1, 073, 074 — are in the requirement machinery, and the reorganization's third
question map, `spec-carrier-set.md`, found the implementation computing one carrier parameter per
spec where the model has a set, read by about 120 sites. That is base design repaired, by §4 q15's
standard, sixteen times since Aug 21: three in these 29 days, three in the twenty before, seven a
month before that. The rate fell; it is not zero, and it is all one subsystem.

**3. Inside a ticket the process now converges, and the ticket has become a project.** CBRD2 took 89
commits and 78 notes over fifteen days, with at least twelve recorded `/code-review` passes of three
to eight findings each; CXR5B went in fifteen steps, each reviewed, two to six findings a pass, each
step with its measured back-outs. No pass of either reached the cap of fifteen that 0RP29 and
9WVT7 hit on every recorded pass, and neither filed a pile behind it. The method — measure first, step, back out, review
the step — bounds the review. But the unit a ticket now names is a proposal stage, a few hundred
lines to several thousand, and every count of tickets in this file measures it less well than it did
in the summer.

**4. New work is arriving from outside the base.** Eight tickets for anthill-traces, a program
outside this repository built on `anthill-core`, in two days; six from a shop model written in the
language; proposal 075, the proof of a goal, the first numbered proposal since August that repairs
nothing — it adds a capability a specification asked for — and 010.1, which settles what was left of
a brainstorm. They are filed Open, in the base's queue, while §1's parked fronts wait (§3.6, the same
42). §4 q19.

**5. What nothing in the window aimed at drifted.** The suite doubled in four weeks with no change
to its build, and its logs were cleaned away before the cause could be read (§3.8). WI-1126 took one
verdict in fourteen weeks (§3.6). The share of new tickets closed within a week is 41% for the first
half of November, under every cohort but the review batch of early October (§3.1).

**What would show this reading wrong.** If consolidation is what lowered the stock, the fortnights
with deleted over added above 25% are the fortnights in which the Open stock falls, and the others
are not. §4 q3 registers that, with four other predictions, for the next sitting.

## 4. Questions for review

Closed questions are one line each here, with their date; their full text, and the superseded
notes on the open ones, are in the history file under the same numbers.

1. **What is "the base", named?** — Answered: WI-1126 names it (filed 2026-08-17, noticed here
   2026-10-05); what is outside it is filed PreOpened (2026-10-05).

2. **Is b < 1 the right gate, and at what value?** — No value of b: b can no longer be read off the
   tracker (2026-10-05). Successor: q14.

3. **Is b actionable, or only diagnostic?** The claim in §3.5 is that a design pass which settles the
   carrier/spec-op keying and requirement-dictionary questions *ahead* of discovery would retire a whole
   generation at once and drop b. Untested. The rival hypothesis is that a design pass only relabels the
   discovery — the same facts get found, in a document instead of a ticket. **How would we tell the
   difference?** A pre-registered prediction (e.g. "b for the resolve cluster falls below 0.4 in the two
   weeks after the pass") is the cheapest test.

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

   **FINAL SCORE 2026-11-23**, eighteen days after it was due. Each is read on the Nov 5 tree
   (`7379c5fd`, births and stock over Oct 5 → Nov 5) where the series allows, and today beside it.

   1. *Holds.* `scope` 23.9%, `resolve` 9.4% of the month's new descriptions. Since then `scope`
      fell further (10.6%, and per word to a quarter) and `resolve` rose to 15.5%, under its line
      (§3.5).
   2. *Neither branch.* Five numbered repairs in the month (050.1, 071, 072, 060.1, 073), more than
      three; `carrier` at 27.4%, under 35%. The repairs kept coming and left the word: their word
      now is `dictionary` (§3.5).
   3. *Neither.* 248 on Nov 5: under the band of 255–290, over the 240 that refutes; Nov 1 read
      exactly 240. 261 today (§3.3).
   4. *Neither on Nov 5* (77%, between 75% and 80%). 83% today: absorption was delayed, not
      reduced (§3.4).
   5. *Refuted* (interim): a build setting.
   6. *The first leg borne out (interim); the second not tested as written.* No ticket outside a
      family recorded passes at the cap after 9WVT7, which closed on Oct 27 with four leftovers
      filed. The largest ticket in the series, CBRD2, recorded at least twelve passes of three to
      eight findings — more passes than predicted, none of 0RP29's shape (§3.11).
   7. *Refuted for the month.* The three repairs after Oct 25 are all in the requirement
      machinery; none is in control effects, and `Suspension` still has no program — 0 example
      files, 1 test file.

   Of seven, one held, two were refuted and four landed between the band and its refutation. The
   bands were drawn without the series' week-to-week spread, and the next ones are drawn wider.

   **REGISTERED 2026-11-23**, to be scored at the next sitting (about 2026-12-21) on §5's methods.

   1. *Consolidation lowers the stock.* For each fortnight of the window, deleted over added above
      25% goes with a fall in Open + PreOpened + Claimed, and below 20% with a rise. A fortnight
      above 25% with a rise, or one under 20% with a fall, refutes it for that fortnight.
   2. *The requirement cluster settles with 074.* Once 074's open stages are delivered, `dictionary`
      falls under 1.5 per thousand words of new descriptions (2.98 now). At 2.5 or more with the
      stages delivered, the cluster did not settle; with stages still open, nothing is scored.
   3. *Repairs slow.* At most two numbered proposals that repair the base are first committed in
      the four weeks (three in each of the last two windows). Four or more refutes "slowing".
   4. *The suite stays on its new slope.* A full run takes 8 to 14 minutes (5:38 now; 11 at a
      28-day doubling). Under 7 means the November rise was an episode; over 14, a steeper one.
   5. *Outside requests become a stream.* At least eight more tickets are filed for programs outside
      this repository (anthill-traces, the shop model and their kind). Fewer than four means the
      eight of Nov 22–23 were a burst.

4. **Is W31 signal or noise — and should the gate be on b paired with time-to-close?** — Signal,
   not a level shift (2026-08-06). The pair was withdrawn on 2026-10-05: its "100% of spinoffs
   within a week" was a closers-only denominator.

5. **Encode the four prose gates?** — Closed 2026-10-05: one edge was in the tracker all along, one
   gate was moot (WI-177 Rejected), one closed on its own (WI-266). WI-128 is left, its
   prerequisite without a ticket.

6. **Does the tracker need a "waiting for a trigger" state?** — PreOpened is that state
   (2026-10-05).

7. **Should b be measured per cluster?** — The area tag exists since October; b itself can no
   longer be measured (2026-10-25). §3.5's term counts stand in for a per-cluster reading.

8. **Does the reopen rate matter?** — No: five items were ever closed twice; the rest was the
   first recipe's merge artefact (2026-10-05).

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

    **2026-11-23 (§3.7).** Prose fell for the second sitting running: 17% of the production lines
    added (29%, and half before that), 39.0% of non-blank production lines (42.4%), 0.67 lines of
    prose per line of code in the typer (0.82, then 1.00). The citation test is still unmade.

10. **Should code size be a tracked series at all?** — Yes (§3.7, since 2026-09-02); production
    code per item closed is its plainest number.

11. **Are the corrections adding behaviour or replacing it?** — Adding; the lines-per-`fn` rise
    was `cargo fmt` (2026-10-05). Successor: q17.

12. **What bends the test-suite curve, and when is it worth bending?** (§3.8.) Wall clock doubles
    every 32 days with a clean fit and no inflection, currently 10:13 for 6,339 tests, and cost per
    test has risen 4.7× — so this is not solved by running fewer tests. The first thing to establish
    is whether the per-test rise is stdlib load, since every test pays it; §3.1 measured that load at
    40 ms in a window where the stdlib has since grown 2.5×. **This is the only series in this
    document that is unambiguously diverging**, and unlike b it has a hard limit: attention.

    **ANSWERED 2026-10-25 (§3.8).** A build setting bent it: anthill-core at opt-level 2 in the gate,
    filed and delivered on Oct 6 (WI-20261006-ZVV24), 16:14 → 3:09 overnight, and 2:17 by Oct 11 (WI-059's shared
    stdlib copy is in that span, its share not separated). The per-test cost was never measured; it was compiled faster. The
    slope is unchanged at a 46-day doubling from a sixth of the height, and closing rose by the share
    the cycle arithmetic allowed — the question's "worth doing; not the factor of two", confirmed.

    **2026-11-23 (§3.8) — the curve is back.** 2:49 → 5:38 in 28 days with tests +15%, no change to
    `test.sh` or the build and the stdlib +4%. The logs that would date it were cleaned away on
    Nov 19. The first new number is a split: about a quarter of a full run is building.

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

    **2026-11-23.** WI-1126: one verdict, 005 rejected. 6.2 weeks. September caught up (83%), so the
    third candidate reads "no" for the first time. Three repairs in 29 days. The fourth candidate —
    a month with no repair — is as far as it was.

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

    So "the base is stable" means *its design defects have stopped surfacing*, a rate counted in
    repairs. The series to date (each sitting's additions are in the history file):

    ```
    001 – 060   Feb – Aug 7     the design    58 main-sequence proposals
    061 – 064   Aug 21 – 25     repairs        4
    065 – 068   Sep 19 – 26     repairs        4
    069 – 070   Oct 3           repairs        2
    050.1       Oct 15          repair         memory through a `let`: a write the binder drops
    071         Oct 16          repair         Error's boundary evidence (`ErrorTag` → `TypePattern`)
    072         Oct 17          repair         constructor contracts, asked for while 037 was revised
    005         Oct 30          rejected       `extends` and sort inheritance — WI-1126's first verdict
    060.1       Nov 4           repair         a rule takes a dictionary only where it writes one
    073         Nov 5           repair         a value of an abstract type is an instance of its sort;
                                               no carrier or provider is chosen at run time
    074         Nov 13          repair         a typeclass instance is a dictionary, written as one
                                               (073 part 2's defect: one written form, two meanings)
    010.1       Nov 15          supersedes     010's brainstorm: typed and untyped queries
    075         Nov 22          new            the proof of a goal, `SLDProof` — asked for by a
                                               specification that could not say why a goal fails
    ```

    Sixteen repairs since Aug 21: ten in the six weeks to Oct 5, three in each window since. 075 is
    the first numbered proposal since August that repairs nothing, and 005 the first rejected.

    Two measurements say where the remaining repairs are, repeated at every sitting.

    *What the spec itself says is open.* `docs/kernel-language.md` cites work items by id, and the
    ones still Open, Claimed or PreOpened mark sentences the spec knows it cannot finish yet:

    | | spec lines | tickets cited | of them still open |
    |---|---|---|---|
    | Aug 2 | 2,819 | 89 | 8 |
    | Sep 2 | 5,618 | 255 | 17 |
    | Oct 5 | 6,862 | 338 | 21 |
    | Oct 25 | 7,566 | 351 | 17 |
    | **Nov 23** | **8,024** | **364** | **16** |

    WI-069 and WI-070, the Suspension and Branch effects, Open since April, are two of the 16.

    *What no real program has exercised.* Files that name each effect the standard library declares,
    as example files (`examples/*.anthill`) / test files, on 2026-11-23: `Error` 35 / 283, `External`
    31 / 15, `Permission` 23 / 5, `Modify` 12 / 115, `Branch` 3 / 13, `Suspension` **0 / 1**. The
    test column grows where the repairs are; the example column has not moved since Oct 25.
    `Error` got its repair once its programs existed (027.4, Sep 9) and `Permission` arrived with the
    program that needed it (064, guardians) — **the base's design closes area by area as each area
    gets a real program, and an area with none is a reservoir of repairs not yet counted.** None of
    the six repairs since Oct 5 is in an area without a program: two are in `Error` and `Modify`,
    four in the type system — 072's constructor contracts and the requirement machinery of 060.1,
    073 and 074.

    So the gate has no date because the list is unwritten: the 16 above, plus every base construct
    no real program has used. That list is WI-1126's first part, and it has one verdict.

16. **Can the inside of a ticket be measured?** (§3.1.) Passes per ticket and regressions per pass
    are now where the branching is, and the only record is prose in ticket notes — 0RP29's "eight
    passes, fourteen of fifteen" survives because someone wrote the sentence. E1WN0's committed
    verdict files would turn the second into a diff. Until then this document cannot see the
    process it was written to watch.

    **2026-11-23.** The notes have converged on a form a pattern can read: CXR5B writes each pass as
    `/code-review (high): N findings`, thirteen of them, 2 to 6 findings; CBRD2 writes
    `/code-review: N findings, K fixed`, at least twelve, 3 to 8. Passes per ticket and findings per
    pass can now be counted from the tracker, which is half of what this question asked for. What
    a finding regressed is still prose.

17. **Is the last fortnight's deletion the start of consolidation, or four coincidences?** (§3.7.)
    Deleted-to-added on moved-line-proof counts ran 14–19% for four months and is 30% since Sep 20,
    with four named mechanisms removed. If it holds above 25% next sitting while the typer's
    lines-per-day falls, the code has started retiring alternatives instead of accreting them —
    which is what §3.7 was set up to detect and is the first thing in this series that would look
    like the base stabilizing from the inside.

    **2026-11-23 (§3.7): met over the window, by one fortnight.** Deleted over added 27.5% while the
    typer's lines a day fell, 913 → 757. Split, it is 39.0% — the series' high — and then 19.1%.
    The first fortnight is the consolidation of 060.1, 073 and 068 D1b; the second is CBRD2's and
    CXR5B's. Whether that is the start of a level or a second episode is §4 q3's first prediction
    of this sitting, scored per fortnight.

18. **Should time be spent reorganizing instead of repairing?** (Asked by the user, 2026-10-25;
    §3.10.) The capacity reading was tested and spent (§3.8): a sixth of the suite bought half as
    many closes again and the same 1.3 filings per close. Two levers have been seen to change the
    series — a settled question retires a cluster's tickets, and a generated family bounds the review
    passes of its rules — and neither has been applied to the whole. §3.10's reading: the list
    first (WI-1126's verdicts and the 0.1.0 sort of the Open set), then one answer per question
    under families — 068 for the rule body, the pairs outside it such as ZAWX9's — and tests by
    subject where that touches them. Scored by the series already here: the Open
    stock turning down; deleted over added above 25% with the typer's lines per day falling; review
    passes per ticket in the consolidated rules at three or fewer.

    **2026-11-23 — what four weeks of it did.** The second map's two tickets are Open:
    WI-20261025-053QV (last touched Nov 13, by 073's stage 3) and WI-20261025-27050 (Nov 2, a
    dependency review). Of the third question, *what a name refers to*, 1Y96B is Delivered (Nov 1)
    and FTV0Q Open, with no map written. No family was added after the two of Oct 25; there are
    seven. A third map came out of the work rather than the list: `docs/design/spec-carrier-set.md` (Nov 22), *which
    of a spec's parameters a provision binds* — one carrier parameter computed per spec where the
    model has a set, about 120 readers — whose stages 1 and 2 were delivered on Nov 22–23 (JE2MT,
    CXR5B in fifteen steps, with DBR8V's composite witnesses beside them). The proposals did the
    rest of the consolidating: 060.1, 073 and 074 each retire a second way of answering one
    question; the first two landed in the fortnight that §3.7 and §3.3 read as the best of the
    series, 074 in the one after. The list — WI-1126's verdicts and the 0.1.0 sort of the Open set — has one verdict.

19. **Where do requests from outside the base go?** (§3.11, new.) In this window the base's queue
    took eight tickets for anthill-traces, a program outside this repository built on
    `anthill-core`, six from a shop model written in the language, and proposal 075, a new
    capability a specification asked for — all filed Open, while the PreOpened convention (q1)
    says work outside the base is filed PreOpened and §1 keeps the parked fronts waiting. If a
    consumer's request is base, the base has a source of work that is not repair and does not run
    out as the design settles, and the gate needs a boundary for it; if it is not, it belongs in
    PreOpened, and the Open stock and every series here that reads it are overstated by it. Either
    way, a tag on such tickets would let each series be read with them and without.

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

Added 2026-10-25:

- **A share-of-descriptions count moves with description length.** Median descriptions went from
  505 words to 357 in this window, and every word's share fell with it — `acceptance` from 93% to
  55%. §3.5 now prints occurrences per thousand words of description beside the share; a term has
  retired only where both fall.
- **A ticket created on two branches has two births, and the topological order picks one.** 30 ids
  are created in two parallel commits (a ticket filed on two branches), and for 15 of them one
  commit also closes something and the other does not. `--topo-order` can order two parallel
  commits differently once later merges join them, so a cohort's spinoff and injected counts can
  trade a ticket or two between sittings with nothing in the tracker changed: through June 282 / 317
  became 283 / 316, Aug 7–31 118 / 132 became 120 / 130. The cohort totals do not move.
- **The id key is the file's stem, slug included.** A renamed slug would be a deletion and a
  creation. None has happened: 1,658 stems over 1,657 ids, the one pair being two items, WI-052 and
  WI-052b.
- **The scheme of §3.7 reproduces to the digit as written.** The classifier below was written from
  the definitions above on this sitting and gave back every cell of the Sep 2 and Oct 5 tables,
  subsystems included, on its first run.

Added 2026-11-23:

- **A window is a commit range between two sittings' tracker commits**, `git rev-list A..B`, with
  each event taken from the second recipe. Over `cc948805..d6a28558` that gives back the
  2026-10-25 window exactly — 130 closed, 46 co-filed, 171 filed, 64 commits filing 125 tickets
  without a close, §3.2's buckets. The Oct 25 sitting's tracker commit is **`d6a28558`**, found as
  the commit whose status census is the one recorded (1,656; 240 Open); §3.7's Oct 25 column
  reproduces there as well. This sitting's is **`234cbe83`**. Write the commit into the state
  table's footnote at each sitting.
- **`target/` is not an archive, again.** Its logs before 2026-11-19 were cleaned, so §3.8 has no
  reading between Oct 25 and Nov 19 and cannot date the doubling. Copying a sitting's day table
  into this file is not enough when the series moves between sittings; the per-day row would have
  to be kept somewhere tracked as the runs happen.
- **A stall sits inside "full runs".** On Nov 23 one full run took 6 h 21 min. The median is
  untouched by it; the summed hours are not, and the day table marks it.
- **The term counts**, as run: births in the window keyed on the second recipe, the
  `## Description` chapter of each on today's tree, `\bterm\b` case-insensitive; share is the
  fraction of descriptions with a match, density the matches per thousand whitespace-separated
  words of all the window's descriptions together. Both columns of 2026-10-25 reproduce exactly.
- **Named test files**: the rule behind 2026-10-25's "812 of the 1,059" was not written down;
  `/wi[_0-9]` in the path gives 862 there. Use that from here.
- **The id-keyed map fails in the directory era too.** The 2026-10-05 caveat above found it in the
  single-file era. This sitting's first port of the second recipe kept one status per id in a
  dict and read "closed" off it — and `9607478e` (2026-08-18, converting the items that arrived
  during the layout change) holds WI-1131 in `delivered/` and in `open/` at once. The dict kept the
  last directory, so WI-1131 was dropped from the closed set there and closed a second time in the
  next commit: 1,523 lifetime events, six items closed twice, W34 at 63 against the recorded 62.
  The recipe as printed derives "closed" from every path, and any path in `delivered/` or
  `verified/` closes an id. Keep a status map for censuses only. It was caught by the conservation
  check, a sixth item closed twice with nothing in the tracker changed.

```python
#!/usr/bin/env python3
# §3.7 line kinds, surface and subsystems over one commit's rustland/*.rs. Run from the repo root:
#   python3 lines.py <commit>
import collections, re, subprocess, sys
sha = sys.argv[1]
git = lambda *a, inp=None: subprocess.run(["git", *a], input=inp, capture_output=True, check=True).stdout
files = [(m.split()[2], p) for m, p in (l.split("\t") for l in git("ls-tree", "-r", sha, "--", "rustland/").decode().splitlines())
         if p.endswith(".rs")]
out, i, blobs = git("cat-file", "--batch", inp="".join(f"{b}\n" for b, _ in files).encode()), 0, []
for _ in files:
    nl = out.index(b"\n", i); n = int(out[i:nl].split()[2])
    blobs.append(out[nl + 1:nl + 1 + n].decode("utf-8", "replace")); i = nl + 2 + n
FN = re.compile(r"^\s*(pub(\([^)]*\))?\s+)?fn\s+\w"); PUBFN = re.compile(r"^\s*pub(\([^)]*\))?\s+fn\s")
IF = re.compile(r"^\s*(\}\s*)?(else\s+)?if\b"); SE = re.compile(r"^\s*(pub(\([^)]*\))?\s+)?(struct|enum)\s+\w")
MOD = re.compile(r"^\s*(pub(\([^)]*\))?\s+)?mod\s+\w+\s*(;|\{)")
SUB = re.compile(r"rustland/anthill-core/src/(kb/typing|kb/load|kb/resolve|eval)(/|\.rs|_)")
def kind(lines):
    ks, block = [], False
    for ln in lines:
        s = ln.strip()
        if block: ks.append("comment"); block = "*/" not in s
        elif not s: ks.append("blank")
        elif s.startswith(("///", "//!")): ks.append("doc")
        elif s.startswith("//"): ks.append("comment")
        elif s.startswith("/*"): ks.append("comment"); block = "*/" not in s[2:]
        else: ks.append("code")
    return ks
def test_lines(lines):                     # #[cfg(test)] on a mod: brace-matched, or two lines for `mod x;`
    mask, j = [False] * len(lines), 0
    while j < len(lines):
        if lines[j].strip().startswith("#[cfg(test)]"):
            k = j + 1
            while k < len(lines) and (lines[k].strip().startswith("#[") or not lines[k].strip()): k += 1
            m = MOD.match(lines[k]) if k < len(lines) else None
            if m and m.group(3) == ";": mask[j] = mask[k] = True; j = k + 1; continue
            if m:
                depth, e = 0, k
                while e < len(lines):
                    depth += lines[e].count("{") - lines[e].count("}")
                    if depth <= 0 and e > k: break
                    e += 1
                for x in range(j, min(e, len(lines) - 1) + 1): mask[x] = True
                j = e + 1; continue
        j += 1
    return mask
tot, surf, sub, blank = collections.Counter(), collections.Counter(), collections.Counter(), 0
for (_, path), text in zip(files, blobs):
    lines = text.split("\n")[:-1] if text.endswith("\n") else text.split("\n")
    mask = [True] * len(lines) if "test" in path else test_lines(lines)
    m = SUB.match(path); area = m.group(1) if m else "other"
    for ln, k, t in zip(lines, kind(lines), mask):
        if k == "blank": blank += 1; continue
        side = "test" if t else "prod"; tot[side, k] += 1
        if side == "prod": sub[area, k] += 1
        if side == "prod" and k == "code":
            surf.update(x for x, r in (("fn", FN), ("pub fn", PUBFN), ("if", IF), ("struct/enum", SE)) if r.match(ln))
            surf["=>"] += "=>" in ln
print(sha[:8], {f"{s} {k}": n for (s, k), n in sorted(tot.items())}, "blank", blank)
print("surface", dict(surf), "code", tot["prod", "code"])
for a in ("kb/typing", "kb/load", "kb/resolve", "eval", "other"):
    print(f"  {a:10} code={sub[a, 'code']} prose/code={(sub[a, 'doc'] + sub[a, 'comment']) / sub[a, 'code']:.2f}")
```

The add-and-delete table's move-proof rows are `Counter` differences over the stripped non-blank
lines of the same blobs, split by `"test" in path`: `sum((new - old).values())` added,
`sum((old - new).values())` deleted.

- **The suite's day table** (§3.8), as the 2026-10-05 rule states it: strip `ESC[…m` and `ESC(B`
  first, sum `N passed; M failed` over the `test result:` lines of each log, take the last
  `[ Ns]` prefix as its wall clock; a full run is one whose passed plus failed reach 97% of the
  day's largest passed count; report the median of the full runs, their number, and the summed
  elapsed of all runs. It reproduces the nine-row table of 2026-10-05 exactly. `rustland/target/`
  is 123 GB on this machine today and still holds every log since 2026-09-24.
