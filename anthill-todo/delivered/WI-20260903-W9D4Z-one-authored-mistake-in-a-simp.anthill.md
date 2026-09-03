## Attributes

- id: WI-20260903-W9D4Z-one-authored-mistake-in-a-simp
- created: 2026-09-03T09:30:17Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-03T12:33:11Z

- acceptance: cargo-test, scaland-sbt-test

## Description

ONE AUTHORED MISTAKE IN A `[simp]` RHS IS REPORTED ONCE PER FIRING SITE, BYTE-IDENTICAL IN TEXT AND LOCATION.

MEASURED on the WI-20260903-FCZ3N tree, in `zzd` with `operation sink(r: Int64) -> Int64 = r`:

| program | errors |
|---|---|
| `rule bad(?x) <=> sink("nope") [simp]` + `operation c(n) = bad(n)`          | 1 — `4:20: … sink.r (op-arg): expected Int64, got String` |
| the same rule + `operation c(n) = bad(n) + bad(n)`                          | **2, byte-identical**, both `4:20` |
| CONTROL: `operation c2(n) = sink("nope") + sink("nope")` (written twice)   | 2, at `4:37` and `4:52` — two places, two messages |

The control is what says the duplication is not the ordinary two-mistakes case: the author wrote ONE `sink("nope")`, and it is reported N times with nothing to tell the copies apart.

WHY IT LOOKS LIKE THIS NOW. WI-20260903-FCZ3N made a fired `[simp]` RHS keep the span the AUTHOR wrote, which is the whole point of that ticket — before it, the N copies carried their N REDEXES' distinct spans, so they were distinguishable and every one of them pointed at a line where the mistake is not written. So this is not a regression to undo: the location is now right and the COUNT is the residue. Raised by `/code-review` on FCZ3N, which is also where the wi873 `nth_at_span` fixture had to be re-sited for the same collision (`one_rule_fired_at_two_redexes_collides_on_one_span`).

THE QUESTION IS WHOSE. Collapsing identical `(span, message)` load errors is a change to the whole diagnostic channel, not to `[simp]`: every pass feeds it, several suites assert error COUNTS, and "two errors that happen to render alike" would have to be shown impossible rather than assumed. That is why it is not folded into FCZ3N.

ACCEPTANCE. The two-firing-site program above reports the mistake ONCE, at `4:20`; the two-written-copies control still reports TWICE, at its two spans. Census the corpus for existing identical-`(span, message)` pairs FIRST — if the dedup collapses any of them, each one is either a second instance of this same shape or a suite whose count assertion is now measuring the dedup, and both have to be named before the change lands. Say which rows fail when it is backed out.

NOTE: do NOT pin the current 2 with a fixture in the meantime — a row asserting the duplication would go red on this ticket's own fix.

Split out of WI-20260903-FCZ3N, which measured it and does not own it.

## Changes

### 2026-09-03T12:33:06Z — feedback — claude

DELIVERED.

THE ANSWER TO "THE QUESTION IS WHOSE" IS: THE CHANNEL. `load_phase_inner` now ends BOTH of
its exits — the full one and the `run_typer: false` partial one — with
`dedup_rendered_load_errors`, keyed on what the reader actually sees: the SOURCE's
identity plus the error's rendering (`path:line:col: message`, or the bare `Display` for
an unstamped one).

THE CENSUS SAID WHERE IT HAD TO GO, and that is why it is not a producer's. Run FIRST, as
the ticket required: a probe at both exits recording every batch containing two errors
with the same `(file, rendering)`, over the whole workspace (36 binaries, 6 358 tests).
SEVEN GROUPS, ALL n = 2, IN FOUR FILES — and every one is a second instance of this same
shape, none a suite measuring the duplication:

  * 5 groups — `Cell[W = Int64]` / `… is over-applied` on `is_modifiable(…)`
    (`wi709_type_arg_validation_test`, `wi710_rule_body_type_arg_test`,
    `wi839_call_bracket_channel_test`). The two copies are the per-file LOADER's and
    `type_check_sorts`'s. The per-file `dedup_load_errors` runs before the typer exists,
    so it CANNOT pair them.
  * 2 groups — `type mismatch in div.effects (op-effects): … undeclared effect: …`
    (`wi_vt8cf_division_tower_test`). Both from `type_check_sorts`, in ONE pass, so no
    cross-pass key would catch them either. Span-LESS, which is the other arm of the key.

None of the four asserts a count (`errs.iter().any(…)`, `!errs.is_empty()`), which the
36-binary run after the change confirms: 0 failures, 6 364 passed (6 358 + this file's 6…
now 7).

THE CLAIM IS INDISTINGUISHABILITY, NOT IMPOSSIBILITY. The ticket asked for "two errors
that happen to render alike" to be shown impossible rather than assumed. They are NOT
impossible — one `[simp]` rule fired at two redexes is two genuine findings — and the
change does not pretend otherwise. What it asserts is that printing the second tells the
reader NOTHING: same sentence, same `path:line:col`, nothing to tell the copies apart.
What is refused is collapsing a pair the reader COULD separate, which is what the two
halves of the key are for and what two of the three back-out axes measure.

ACCEPTANCE, MET, in `zzd` with `operation sink(r: Int64) -> Int64 = r`:

  | program                                                     | before | after |
  |---|---|---|
  | `rule bad(?x) <=> sink("nope") [simp]` + `c(n) = bad(n)`     | 1 @ 4:20 | 1 @ 4:20 |
  | the same rule + `c(n) = bad(n) + bad(n)`                     | 2 @ 4:20 | **1 @ 4:20** |
  | the same rule + `c(n) = bad(n) + bad(n) + bad(n)`            | 3 @ 4:20 | **1 @ 4:20** |
  | CONTROL: `c2(n) = sink("nope") + sink("nope")` (written 2x)  | 2 @ 4:37, 4:52 | 2 @ 4:37, 4:52 |

THREE BACK-OUT AXES, and the two KEY axes are the interesting ones because most of what
they fail is not mine:

 1. THE DEDUP ITSELF (`dedup_rendered_load_errors` returns its input) — EXACTLY 3 ROWS of
    4 072 in `wi_tests`, all in this file, one per producer pairing. Nothing outside can
    fail: that back-out restores the tree the census was taken on, whose 36-binary run was
    green.
 2. FILE IDENTITY IN THE KEY (key on the rendering ALONE) — 2 rows, and only ONE is mine.
    The other is `wi835_use_site_requires_scope_test::one_refusal_per_site_including_across_files_at_equal_offsets`,
    written against the IDENTICAL hazard at a producer key ("a site key that carried only
    the offsets, and not the `SourceId`, collapsed these two into one and silently dropped
    the second file's diagnostic"). An existing row catching this is the evidence that the
    file half is load-bearing.
 3. THE RENDERING IN THE KEY (key on `(file, span)`) — 12 rows, and TEN are pre-existing,
    in EIGHT files this change never touches: `wi347` (`one_misspelling_in_both_clause_lists_is_reported_twice`),
    `wi792` (2), `wi1100`, `wi994`, `wi749`, `wi_7x7nk`, `wi_w6jh0` (3). §8.5's standing
    rule that "a diagnostic list is never silently truncated" (WI-20260830-JM7A8) is the
    same promise stated in the spec.

GREEN UNDER ALL THREE BY DESIGN — the controls: `two_written_copies_are_two_diagnoses`
(two spans; the row a message-only key fails) and `distinct_mistakes_are_all_still_reported`.

A CORRECTION FELL OUT OF AXIS 2. `LoadError::TypedPatternNotEnforced`'s doc recorded a
"pre-existing limit": that ACROSS files, two unlabeled rules at equal byte offsets "still
collapse" under `dedup_key`. MEASURED FALSE — 2 refusals, with AND without this change.
`dedup_load_errors` is reached only through `stamped_file_errors`, which is handed ONE
file's errors at a time, so two files' diagnostics were never in one call for it to
collapse. The hazard is NEW with a batch-wide key, which is exactly why that key carries
the source's address. Doc corrected at the variant, and my own doc no longer cites a limit
that did not exist.

TWO PRODUCER-SIDE COMMENTS RETIRED THEIR CLAIM, NOT THEIR CODE. `check_rule_body_goals`
and `NonEqKeyRequiresLawfulEq`'s rendering both said the producer "is the only place that
can collapse them". That sentence is what a channel rule retires. Both keys STAY — they
are `SourceSpan`-based, so they hold however a message renders — and both comments now say
so, with this as the backstop. `wi1034`'s test-side copy of the same sentence too.

WHAT IS NOT COVERED, NAMED RATHER THAN SKIPPED: `anthill-cli`'s `scan_query_source`, which
reports a query source's declaration scan directly. Deliberately left alone — it is ONE
pass over ONE file, so it has no two producers to pair, and no duplicate from it appears
in the census. Recorded at `dedup_rendered_load_errors`.

NO SCALAND MIRROR, and for a stronger reason than FCZ3N's. scaland's `loadAll` has no
dedup at any level (not even the per-file one), no typer and no `simp_rewrite` — so
neither the producing shape (a fired `[simp]` RHS re-checked per redex) nor the second
producer (a whole-KB pass beside the loader) exists there to duplicate. `sbt test` re-run
green (`[success]`, 0 failures) to satisfy the acceptance field.

── THE REVIEW, AND WHAT ITS FOUR FINDINGS MEASURED TO ──────────────────────

`/code-review` reviewed this change AND the committed WI-20260903-FCZ3N diff beside
it, and raised 4. Every one was re-measured here rather than taken at face value; two
were right, one was right about a stale doc and wrong about its severity, and one did
not reproduce.

 1. `reparent_spliced` does not reparent a PATTERN node (it reparents only the
    `as_expr()` branch), so a spliced pattern keeps the RULE's owner while its `Expr`
    siblings get the REDEX's. CORRECT, and a behaviour change FCZ3N introduced. NOT
    DRIVABLE TODAY, measured: a probe on both non-`Expr` branches over the whole
    `wi_tests` binary (4 073 tests) records ZERO hits, because the lambda defect
    WI-20260903-FC2X4 owns is what stops a `NodeKind::Pattern` ever reaching a fired
    RHS. Recorded as feedback ON FC2X4, whose fix is what makes it reachable — a
    branch nothing can drive is not a branch to "fix" blind.

 2. The `fact` spelling of a `[simp]` equation loses the unbound-RHS-variable verdict.
    CORRECT AND LIVE. Measured: `rule fu(?x) <=> sink(?y) [simp]` + consumer is
    refused (1 error), `fact fu(?x) <=> sink(?y) [simp]` + the same consumer LOADS
    CLEAN (0) — and the `fact` spelling genuinely fires (`fact dbl(?x) <=> ?x + ?x
    [simp]` gives `drive(5) = 10`), so it is a live site accepting a malformed rule.
    `assert_fact` sets `globals: Vec::new()`, so `open_equation` hands
    `bottom_out_unbound` an empty frame. NOT inline-sized — the repair reaches
    `with_fresh_vars`' arity-0 routing (WI-624/635) or moves the verdict to load time,
    which FCZ3N decided against on purpose. FILED as WI-20260903-2M5XR.

 3. `nth_at_span`'s doc argument at `kb/mod.rs` and `req_insertion.rs` is stale.
    RIGHT ABOUT THE MECHANISM, WRONG ABOUT THE SEVERITY. Both docs justified the field
    with "`substitute_to_occurrence` builds every node of a `[simp]` RHS from the
    single redex occurrence", which FCZ3N replaced — the collision class MOVED, from
    two calls in one RHS to one written call spliced at N redexes. But the claim that
    the population "grew by orders of magnitude" does not hold: RE-MEASURED, the stamp
    is `0` for every call in stdlib / `github-todo`, `0` across `anthill-todo` (488
    loads), and over the whole `wi_tests` corpus (5 551 loads) exactly ONE entry is
    non-zero — `one_rule_fired_at_two_redexes_collides_on_one_span`, the fixture
    written to drive it. FIXED HERE, in both docs, with the measured numbers, since
    FCZ3N updated the test file and left the two doc-commented enforcement sites
    behind.

 4. "The RHS occurrence is built for every bodyless equation, tagged or not, so an
    inert one pays a second error-emitting read, and only the new dedup keeps a
    duplicated diagnostic out of the list." THE HARM DOES NOT REPRODUCE. Measured on
    three shapes — `rule inert(?x) <=> sink("nope")`, the same with an unresolvable
    name, and `fact tau() <=> sink("nope")` — each reports **0 errors**, not two and
    not one: an untagged equation is inert and its RHS is never type-checked, so there
    is no diagnostic for the dedup to be masking. What remains is that the build runs
    for equations that can never fire (90 written RHSs, of which 21 are tagged), which
    is a load-path cost in FCZ3N's own territory and not a correctness question. Not
    filed: the claim as stated was measured false, and the residue has no measured
    harm to name.

TESTS: `rustland/anthill-core/tests/include/wi_w9d4z_one_mistake_one_diagnosis_test.rs`
(7 rows). Also corrected `nth_at_span`'s doc at `kb/mod.rs` and `req_insertion.rs`
(review finding 3). Full workspace suite green: 36 binaries, 0 compile errors,
0 failures.

