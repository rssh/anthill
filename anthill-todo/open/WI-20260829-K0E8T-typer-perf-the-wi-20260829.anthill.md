## Attributes

- id: WI-20260829-K0E8T-typer-perf-the-wi-20260829
- created: 2026-08-29T19:27:33Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T19:27:33Z

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

