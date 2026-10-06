## Attributes

- id: WI-20261006-SZKV7-two-step-load-as-a-switch-in
- created: 2026-10-06T04:53:49Z

- status: Open
- status_agent: user
- status_at: 2026-10-06T04:53:49Z

- acceptance: cargo-test

- depends_on: WI-20261006-ZVV24-build-the-tests-optimized

- tags: test-infra

## Description

TWO-STEP LOAD AS A SWITCH IN THE ONE TEST RECIPE — the control that the frontier-driven passes (docs/design/test-infrastructure.md §4 A3) and the cached base KB (§5, WI-059) both rest on, built before either.

WHAT. In `try_load_kb_named_prepared_with` (`anthill-core/tests/common/mod.rs`, the one recipe every stdlib-loading helper ends in), an environment switch — `ANTHILL_TEST_TWO_STEP_LOAD=1` — changes `load_all(stdlib ∪ user)` into a fresh KB to `load_all(stdlib)` and then `load_all(user)` into that same fresh KB. No `Clone`, no `Send`, no shared base: each test still builds its own KB, `prepare` still runs before the first load, and the `LoadOptions` are the same for both calls. With the switch off the recipe is today's.

WHY NOW. (1) §4 A3 names the equivalence `load_all(S ∪ U)` ≡ `load_all(S); load_all(U)` — same observable KB facts, same diagnostics for the same `U` — as the control for making a pass frontier-driven, where a skipped item fails SILENTLY and the suite stays green. The oracle has to exist, and be known green, before the first pass is changed, or a difference found later cannot be attributed. (2) Nobody knows how many of the 7 039 tests already differ under a two-step load. Every one that does differs for a reason lever B would hit, so the list is B's real cost, available without building B.

RUN the whole `anthill-core` suite under the switch and CLASSIFY every test that differs:

- the test asserts something that legitimately depends on the recipe (`Symbol` numbering, `LoadResult.defined_sorts`, the order of diagnostics): fix the assertion, or pin the test to the one-shot recipe BY NAME with the reason at its site;
- the two-step load builds a different KB, or reports different diagnostics, for the same `U`: a loader finding. Report it — it is either a bug or a constraint on A3 and B — and do not adjust the test around it. Ask before filing anything from the list.

Things §5.3 already expects to differ and that must be checked, not assumed: `Symbol` numbering, `LoadResult.defined_sorts` (the user's only, on the second call), diagnostics for a refused `U`, `fact_dedup` and discrimination-tree state for a `U` that re-asserts a stdlib fact.

CONTROL. A switch that is silently ignored would report "suite green under two-step" having measured nothing. One row asserts it took effect: under the switch the user load's `LoadResult.defined_sorts` holds the user's sorts and no stdlib sort; without it, both. Say at the row that it fails when the switch is backed out.

COST. Under the switch a load is the stdlib load plus the incremental one — 4.46 s + 2.89 s in debug against 4.85 s (§2.3) — so the suite run is about 1.5× today's `wi_tests` block. That is why this item waits for the profile change.

DONE WHEN: the switch is in the recipe; the control row is in; the full `anthill-core` run under the switch is recorded, with the classified list in the doc's §5.3 and every pinned test saying why at its site.

