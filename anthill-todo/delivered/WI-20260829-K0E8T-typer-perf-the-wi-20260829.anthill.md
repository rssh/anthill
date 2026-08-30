## Attributes

- id: WI-20260829-K0E8T-typer-perf-the-wi-20260829
- created: 2026-08-29T19:27:33Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-30T06:20:18Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER/PERF: the WI-20260829-N01PY witness leg runs an UNMEASURED walk on `types_compatible`'s FAILURE path — the hot one — and allocates a carrier term before its own gate.

Found by /code-review on the N01PY commit (a6dc7061). NOT DRIVEN TO A NUMBER by that review
or by this ticket: no measurement is quoted anywhere for the gate, which is the point.

TWO PARTS, same call path, so one ticket:

(1) THE GATE IS NOT AS CHEAP AS ITS DOC SAYS. For every FAILED compare whose expected side
is a spec with any provisions, `provisions_of_spec` allocates a `Vec<RuleId>` and then
decodes EVERY provision fact — `fact_head_named_args`, two `get_named_arg`,
`sort_ref_functor`, `unwrap_spec_view` (allocates a `SmallVec`), then
`provision_carrier_binding` (which allocates a `named_keys` `Vec` on the short-name
fallback) — and the survivors are `.collect()`ed into another `Vec`. `types_compatible`
returning `false` IS the common case in dispatch candidate filtering, so this sits squarely
on the hot path. WORSE BEFORE `build_provides_index` EXISTS: `provides_rids_by_spec` ->
`rids_or_scan` returns EVERY `SortProvidesInfo` fact in the KB (its own doc says so), so
each failed compare in the pre-`type_check_sorts` loader passes walks all provisions.

(2) THE CARRIER TERM IS BUILT BEFORE THE GATE. `bare_sort_compatible` (typing.rs ~52727)
runs `let actual_term = kb.make_sort_ref(a);` UNCONDITIONALLY, ahead of the "cheap gate"
the design doc says comes first, on the failure path of every bare<->bare compatibility
check. `TermStore::alloc` (kb/term.rs:339) hashes a whole `Term` and bumps a refcount that
nothing on this path ever decrements. Candidate repairs: build it only after the provision
gate has found a witness row, or key the gate on SYMBOLS and mint the term lazily.

WHY THIS IS A TICKET AND NOT AN INLINE FIX: (2) looks like a one-line hoist, but its value
depends entirely on (1)'s cost, and `make_sort_ref` may be the cheap half. Fixing (2) alone
would be a repair with no measurement — and this repo's own history says a widened
`types_compatible` reaches machinery it was never on.

HOW TO MEASURE (repo rule): PAIRED, IN-PROCESS, MIN-OF-K. Shell sampling has been measured
to span 34x on ONE binary here and CONTENTION dwarfed the code 4x, so a wall-clock `time`
around `cargo test` will not answer this. Count the work instead of timing it if that is
cleaner: a counter on `provisions_of_spec` entries and on `make_sort_ref` calls from this
path, over a full stdlib load, with the leg present vs. its first statement returning false.

ACCEPTANCE: a number for how often the gate runs and what it costs on a full stdlib load
plus the anthill-core suite, quoted AT THE SITE; the repair (if any) justified by that
number and re-measured after; the `build_provides_index`-absent case measured separately,
since it is the pathological one. If the answer is 'it is already cheap', say so at the site
with the number and close this — a measured non-problem is a result.

## Changes

### 2026-08-30T06:19:46Z — feedback — user

MEASURED FIRST, then repaired — and the count decides part (1)'s premise against it.
`types_compatible` is NOT hot: 2797 calls in a whole `stdlib/` load, ~19 per millisecond
of 145 ms. 1238 reach `bare_sort_compatible`, 1214 fall through to the N01PY leg, so the
gate runs 1267 times (1214 bare + 53 parameterized) — but its `by_spec_base` bucket is
EMPTY at 1263 of those, so across the entire load it looks at 4 provision rids and matches
none. The leg is 87% of every provision-walk call in the load (1267 of 1457) and 0.2% of
the rids they decode (4 of 1924).

PRICED per compare (200k in-process iterations, min-of-9, release), against the whole
bare<->bare compare it rides on: 562 ns with the leg vs 395 ns backed out for the common
shape — the gate 167 ns, 42% of the failed compare. Against a spec that HAS provisions it
is 1204 ns (`Stream`, 6) to 2706 ns (`FiniteCollection`, 6), 3-7x the rest of the check.
Times the population that is ~0.22 ms of a 145 ms load — 0.15% — which a paired
in-process min-of-11 whole-load A/B cannot resolve (143.5 / 143.9 / 139.8 ms for leg-on /
lazy-mint / backed-out, three completely overlapping distributions). So: cheap at THIS
population, and the population is a fact about `stdlib/`, not about the code. Both
readings are written at the site, because the ticket asked for both.

Part (2)'s `make_sort_ref` IS the cheap half — 39 ns of the 167, 47 us per load. Hoisted
anyway, for the reason the ticket only half-names: `alloc` bumps a refcount on a hash-cons
HIT and nothing on this path decrements it, so every refused compare left `Ref(actual)`
permanently one reference heavier. `WitnessActual::{Term,Bare}` makes the eager mint
UNSPELLABLE rather than discouraged. Same size, same call path: the gate now does ONE
`canonical_sort_sym` (an FQN string hash) where it did three, and returns on an empty
bucket before entering the decoder — `provisions_of_spec` split into fetch +
`provisions_from_rids`.

RE-MEASURED, all five arms PAIRED IN ONE PROCESS: 574.1 / 537.0 / 500.9 / 463.6 / 410.1 ns
for old-gate+eager (HEAD) / old-gate+lazy / new-gate+eager / new-gate+lazy (SHIPPED) /
leg-off (control). The gate: 164.0 -> 53.5 ns, 3.1x, and 40% of the failed compare -> 13%.
AND WHERE IT BUYS NOTHING, which is half the result: against `FiniteCollection` it moves
2674 -> 2597 ns (3%) because the per-fact DECODE dominates, and with `provides_index`
absent all four arms sit at ~17.6 us because the scan returns all 96 facts so the
emptiness check cannot fire. The whole-load A/B still cannot see any of it.

THE PATHOLOGICAL CASE IS PRICED AND ALL BUT UNREACHABLE — but NOT unreachable, which is
the correction the census bought. With `provides_index` absent the same common compare
costs 17505 ns against 7638 ns; the gate alone 9867 ns, 59x its indexed cost. The BASELINE
moves too (395 -> 7638 ns) because `sort_provides_admissibly` reads the same index: a
missing index is expensive for the whole relation, not for this leg. Population: 0 of the
1267 stdlib-load entries, and 2 of 30,726,442 across the whole `anthill-core` suite
(13 binaries, 5303 tests, 4381 threads) — 6.5e-8. Neither repair helps there, by
construction, and the doc says so.

NOT DONE, with the number: a per-spec memo of witness carriers would collapse the gate to
one HashMap lookup. At 0.15% it buys nothing measurable and costs a new index with its own
invalidation surface (WI-954's stale-index-answers-EMPTY). Stated at the site with what to
re-take first.

TEST: `k0e8t_witness_gate_test`, two rows, DRIVING — the observable is the refcount of
`Ref(Int64)` across one failed compare, not `TermStore::len` (the term is long since
interned, which is why the defect was invisible). Row 1 is the empty-bucket shape; row 2
(`FiniteCollection`, 6 provisions, none witnessed on Int64) makes the gate do real work,
so a repair that minted after the emptiness check but before the provision walk would pass
row 1 and fail row 2. CONTROL RUN: with `WitnessActual::Term(kb.make_sort_ref(a))` restored
both rows fail by exactly +1 (458 -> 459). The `assert!(!types_compatible(..))` verdicts
pass either way by design — the hoist changes no answer.

Files: rustland/anthill-core/src/kb/typing.rs (+243/-20, one file).

### 2026-08-30T06:20:10Z — feedback — user

/code-review (high) raised THREE, all correct, all fixed — and one of them says the first cut of this ticket was half a repair.

(1) THE HOIST NARROWED THE LEAK, IT DID NOT END IT. Moving the mint past the gate leaves
every REFUSED compare allocating nothing — but an ACCEPTED one still ran `make_sort_ref`,
i.e. `TermStore::alloc`, which increfs on a hash-cons HIT with nothing on this path ever
decrementing. A program type-checking the same witnessed pair repeatedly adds one
reference per compare, without bound. Fixed with WI-849's read-only half: a new
`KnowledgeBase::find_sort_ref` (beside `make_sort_ref`, so the WI-361 `Ref(S)` canon stays
in one place) is tried first and `alloc` is the fallback — bounded by DISTINCT carriers,
once each, not by compares. Not increffing is sound and the site says why: the id is the
re-entrancy key (removed on every exit) plus one `goal_bindings` value handed to
`spec_resolves_at_bindings`, which answers a bool and retains nothing, and type-checking
retracts nothing so the slot cannot be freed underneath it.

(2) MY DOC OVERCLAIMED. It said the carrier makes the eager mint 'UNSPELLABLE'; the
reviewer wrote `WitnessActual::Term(kb.make_sort_ref(a))` at the bare arm, compiled it,
and reproduced the defect exactly. Reworded: the type is a nudge, the tests are the guard.

(3) A stray trailing blank line at EOF, edit residue from the instrumentation strip.

TEST GREW A THIRD ROW, because rows 1 and 2 both REFUSE and are therefore satisfied by the
hoist alone — they could not see (1) at all. Row 3 (`Plain` <: `Cap` over a bare witnessed
carrier, the N01PY shape) ACCEPTS, ten compares, so the assertion is about GROWTH. The two
back-outs now separate cleanly, both measured: back out the hoist and rows 1+2 fail by +1
(458 -> 459); back out `find_sort_ref` alone and only row 3 fails, by exactly +10 for its
ten compares (8 -> 18).

AND THE DOC-TESTS CAUGHT A FOURTH, which no reading would have: the re-measure table was
indented five spaces inside the `///` block, so rustdoc took it for a Rust code block and
tried to COMPILE it ('unknown start of token: U+2014'). Re-indented to three, matching the
file's other tables; doc-tests back to their original 4 and green. Worth remembering — a
comment-only edit broke the build.

FINAL GREEN: 12 test binaries, 5302 passed / 0 failed (lib 570, incl. the three new rows),
plus 4 doc-tests. Files: rustland/anthill-core/src/kb/typing.rs and
rustland/anthill-core/src/kb/mod.rs — TWO files, correcting the previous note's 'one file'.

