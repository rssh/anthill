## Attributes

- id: WI-20261006-SZKV7-two-step-load-as-a-switch-in
- created: 2026-10-06T04:53:49Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-08T06:24:12Z

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

## Changes

### 2026-10-08T06:24:09Z — feedback — claude

DELIVERED — the switch, its control, the classified run, and the first of the two loader findings fixed inline (user, 2026-10-08).

THE SWITCH. `ANTHILL_TEST_TWO_STEP_LOAD=1` makes the one recipe (`tests/common/mod.rs`, `LoadRecipe` / `recipe_load`) call `load_all(stdlib)` and then `load_all(user)` into the same fresh KB. `scripts/test.sh` validates it and writes the recipe ASKED FOR into the log; `wi_szkv7_two_step_load_test` is the control and writes the recipe it OBSERVED. Back-outs measured: the helpers ignoring the switch, the constant renamed, and the two-step arm making a one-shot call each fail the row that should catch them.

THE RUN (docs/design/test-infrastructure.md §5.3; raw: docs/measurements/test-infrastructure/two-step-run-2026-10-07.txt). 2 of 7 873 tests differed, neither an assertion on the recipe, so nothing was pinned or adjusted: wi830 `a_role_that_is_not_a_role_is_refused_at_load` and wi228 `pin_now_threads_conditional_tree_into_nested_dictionary_nodes`. The switch reached 8 222 of 9 695 stdlib loads executed (85 %); 1 028 more are made by ~175 test files that carry their own copy of the load, 79 by the library's unit tests (§2.4).

FINDING 1, FIXED. The typer reached a clause only through a sort THE CALL defined, so a later load's clause under an earlier load's sort was never checked — `fact box(n: "seven")` over a base `box(n: Int64)`, the same clause spelled `rule … :- true`, and a rule with contradictory variable types or outside the pattern fragment written into the base's sort; `KB.loaded` accepted them. The loader now hands the typer what the call added as one value (`typing::Loaded`: the sorts it defined and the range of rule slots it filled before its typer), and `type_check_sorts` takes nothing else. `wi_szkv7_clause_frontier_test`: 13 rows, nine back-outs measured.

FINDING 2, OPEN — the user's call on the semantics. Derived equality is not taken back: with a user witness sort providing `Eq[T = List[T = A]]`, a one-call load derives no equality rows for `List`; loaded after the stdlib, the rows the stdlib call derived stay beside the written ones (§4 A3). Under the switch the suite has this one red row (7 885 passed, 1 failed).

GATE: 8 766 passed, 0 failed, 14 ignored (one shot, 2026-10-08). NOT DONE HERE, not filed: routing the ~175 own-load test files through the recipe (§8.6 c).

### 2026-10-08T12:45:30Z — feedback — claude

FINDING 2 SETTLED, 2026-10-08 (user: refuse) — a composite's equality is closed by the load that defines it. What decides it is who supplies its `eq` and which provisions of `PartialEq` / `Eq` / `NonEq` are about it; a load derives the equality from what it finds and reads both through negations, which are sound within a load and false across loads. A later load that changes either for a composite an earlier load defined is now a load error (`LoadError::EqualityOfEarlierSort`; kernel-language.md §8.3), one load of both sources being unchanged. Measured before it: `reading(v: Float)` loaded and then a witness `eq … = true` for it answered `eq(reading(1.5), reading(2.5))` false where one load answers true.

DECIDED BY COMPARING STATES (`eq_derive::EqualitySignature`, recorded at every exit of a load, recomputed at the next): three cuts that read what a load DID were each wrong somewhere, by /code-review. NOT COVERED, and said so in the spec: sorts that are no composite; what a supplier computes or what shape the sort has (a redeclaration).

`wi_szkv7_later_equality_test`: 25 rows, eleven back-outs measured. `wi228`'s fixture supplies an `eq` for the stdlib's `List` and is pinned to one load by name — the one test the rule touches. Under the switch the suite is now GREEN: 7 923 passed, 0 failed, 6 ignored. Gate: 8 803 passed, 0 failed, 14 ignored.

