## Attributes

- id: WI-20260925-YNCY3-cleanup-and-efficiency-from
- created: 2026-09-25T22:22:57Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-26T09:13:48Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

CLEANUP AND EFFICIENCY FROM THE REVIEWS OF WI-20260925-P7VP4 / WI-20260925-SHED7 — verified items the /code-review rounds of 2026-09-25 cut by their report cap. No wrong answers here; each is duplication, dead code, a misleading test record, or wasted work, named with the owner or the cheaper form.

DUPLICATION / DEAD CODE:
 1. `weave_covered_call`'s widened `requirements: &[…]` parameter and its P7VP4 doc paragraph are vestigial (one caller, one element; P7VP4 weaves with `weave_calls`) — see the WI-1040 nested-weave item in the pre-existing-defects ticket, whose fix retires it.
 2. `call_op_bridged` builds a callee frame three ways (`requirements_from_supplied`, `resolve_bridge_requirements_except`, `override_supplied_slots`): a partly supplied call to an operation whose chain is all op-scoped gets no `__req_self` where the all-supplied and uncited calls do; `override_supplied_slots`' replace arm is dead; `.ok()?` swallows `stand_in_requirement`'s error. One constructor.
 3. The condition-argument reader is written three times — `fill_derive::type_arg` (TermId), `domain_evidence_of_type` and `sort_domain_route` (Value) — and `condition_param_sym` re-derives, by short name on every read, the declared parameter symbol the loader had and dropped (load.rs `domain_params` pushes `(key, var)`). Store the declared symbol in `SortDomainEntry.params`; one `TermView`-generic reader. Its positional half is unreachable (the loader stores type arguments NAMED) — make a positional there a debug assertion.
 4. relation.rs carries the route's resolve-and-emit tail three times (`route_requirement_read`, `op_slot_route`, `sort_domain_route`) — one `resolve_route`; the `#[allow(clippy::too_many_arguments)]` on the 7-parameter `sort_domain_route` suppresses nothing.
 5. Hand-written walks beside their owners: `term_mentions_var`, `open_term_placeholders`, `fill_derive::mentions_sort` (vs `term_any_subterm` / `rewrite_term_leaves`); `dealias_type`'s leaf match and `is_unrouted_read` (vs `ref_or_nullary_name` / `KnowledgeBase::value_symbol`); `woven_call_takes_slots` (= `spec_op_call_parent(..).is_none()`, and the load-side `inferred_slot_demand` spells it a third time); `step_init`'s `bool_view_head` duplicates the arity+1 hook's `woven_head`; `supplied_dictionary` duplicates `dictionary_dispatch_target`'s BindValue→Dictionary read.
 6. `fill_derive::PRIMITIVE_SORTS` re-lists `load::PRELUDE_SORTS` (a primitive added there silently gets no `fill`); `evidence_term`'s `Dict` arm re-spells `build_dictionary_term`.
 7. `builtin_apply_domain`'s error arms are dead (it runs only after `lower_apply_domain` answered NotYet) and it re-runs `domain_evidence` per rotation just to delay — reduce it to `delay()`. `DomainEvidence::NotYet` / `Unpinned` are handled identically except at one arm (`NotYet(Option<VarId>)`?). `pin_bound_from_value` / `pin_bound_from_value_open` are line-for-line twins except for the type read.
 8. `inferred_read` re-aligns a demand's arguments (a spec-op demand is aligned ~5 times) and `unreachable!`s if that fails — carry the aligned arguments in the demand.
 9. `NoDomain` (a KB that never loaded `anthill.realization.runtime.Dictionary`) is taken as conformance by the typed-head arms of `lower_apply_domain` and a silent Failure by `read_dictionary_into` — make it the loud error the 2-ary form already raises.

TEST RECORDS:
 10. `wi_shed7_fillable_test::a_domain_relation_is_no_row_of_the_operation_table` reads `sort_ops_for_impl` names instead of calling `Dictionary.ops` (an exact proxy today — reword or drive it); `wi_5g28a_sort_domain_test::a_bound_that_names_its_sort_enumerates_as_before` is labelled CONTROL but answers to no axis — name its back-out; `a_call_nested_in_a_woven_call_is_woven_too` asserts a count only.
 11. Test helpers duplicated across `wi_p7vp4…` and `wi_shed7…` (`only_int` / `one_definite_int`, the Node/Term → TermPrinter row renderer) — move to `crate::common`.

EFFICIENCY:
 12. `fill_goal` wraps each parametric fill step in a citation marker, so every clause opening recomputes `requirement_read_counts` (a qualified-name round trip, Vec allocations) for a layout fixed at derivation; `fill_goal` also re-finds the SortDomain entry through `fill_relations` though `lower_apply_domain` holds it.
 13. Slot reads run as body goals on every invocation and do nothing (a citation binds their `out` at clause opening) — drop them from the OPENED body after `bind_citation_reads`.
 14. `domain_evidence` rebuilds the whole parent dictionary to evaluate one `__domain_sub` and re-copies a routed dictionary every fill step.
 15. The typed-head `find_dictionary(SortDomain…)` read after `apply_domain` builds, when nothing routed it, a dictionary no later goal reads.
 16. `builtin_find_dictionary` scans `named_keys` twice (`slot`, `out`); `builtin_type_domain` allocates `named_keys` per firing to find `early`; `is_unrouted_read` does a string-keyed `symbols.lookup` per marker slot — cache the symbols.
 17. `reduce_op_value` re-classifies a woven callee (slot vs dispatch) on every reduction and retry — stamp the kind at weave time.
 18. `carrier_provided_by_witness` now runs on the run-time DontFire path (the shared guard core): it walks every provision row of the spec per call — check the witness bucket first (as `witness_provides_admissibly` does).

ACCEPTANCE: behaviour unchanged — full workspace green via rustland/scripts/test.sh (same counts) and scaland testFull; each deleted duplicate replaced by a call to its owner; measured timings for 12–18 (`ANTHILL_LOAD_TIMING` / a query loop) before and after.

## Changes

### 2026-09-26T08:39:52Z — feedback — user

DELIVERED, NOT COMMITTED (claude, 2026-09-26). Per item:
1. WI-1040 weaves through P7VP4's one-pass `weave_calls` (identity in the original tree, a `reached` flag per target); `weave_covered_call` and its widened `requirements` parameter are gone, and a covered call is its occurrence alone (the functor rode along unused). This IS WI-20260925-PRVA2 (a): `a_covered_call_nested_in_another_covered_call_is_woven_with_it` (wi1040) PANICKED the load on the call-by-call weave (measured at HEAD 35e115c6) and passes now. Its outer body is FOLDED (`= n`) — a bridged call reduces no argument but a host operation's, so a nested call answers only through a fold.
2. `call_op_bridged` builds every frame through `frame_requirements_from_trees`: the derivation places each supplied dictionary in its own slot (`BridgeSlot::Supplied`, `resolve_bridge_requirements_supplied`, nothing derived when every slot is supplied). A partly supplied, all-op-scoped chain gets its `__req_self` as the other two routes do; a stand-in failure is the ordinary `NoDictionarySort` suspend, not swallowed; supplied slots with no parent frame, or at a count the chain disagrees with, are refused (`Unresolvable`), never dropped (/code-review); `requirements_from_supplied` and `override_supplied_slots` (with its dead replace arm) are gone. Backing the supplied-slot use out reddens EIGHT P7VP4 rows, not the one its header claimed — corrected there.
3. `DomainParam { key, decl, var }` travels from the loader (`collect_domain_job`) through `DomainJob`, `SortDomainEntry` and the KB's `domain_params`. `condition_param_sym`, `condition_arg_position` and `type_arg` are gone: ONE reader, `fill_derive::condition_arg` (any `TermView`, over `named_field`), serves the fill derivation, the typed-head sweep, the resolver and the citation route, with a debug assertion for a positional application (it never fired over the workspace), and provision conditions read `decl`.
4. relation.rs's three resolve-and-emit tails are `resolve_route`; `sort_domain_route`'s no-op clippy allow is gone.
5. `term_mentions_var`, `mentions_sort` -> `term_any_subterm` (now pub(crate)); `open_term_placeholders` -> `rewrite_term_leaves`; `dealias_type`'s leaf match -> `ref_or_nullary_name`; `is_unrouted_read` -> `value_symbol`; the slot/dispatch split -> `spec_op_call_parent` on both sides (its doc records the woven split as a reader); `step_init`'s two woven-head readers -> `goal_call_head`; the BindValue->Dictionary read -> `dictionary_of_binding`.
6. `PRIMITIVE_SORTS` is gone — the fill derivation iterates `load::PRELUDE_SORTS` (`prelude_sort_qn` / `is_prelude_sort_qn`); `evidence_term`'s Dict arm and `build_dictionary_term` share `dictionary_term`.
7. `builtin_apply_domain` is the dispatch arm's `delay()` (reached only on the lowering's NotYet fall-through, same step, same σ); `NotYet(Option<VarId>)` replaces NotYet / Unpinned; the two pin readings are one `pin_bound`.
8. The inference's demands carry their aligned arguments (`DemandCall`, `SpecDemand`, `SlotDemand`), aligned once by the predicate that admits the call; `inferred_read` neither re-aligns nor `unreachable!`s; the carrier reads take arguments already in parameter order (`aligned_carrier_outcome`, `aligned_carrier_args`).
9. `NoDomain` is a fault in the typed-head arms of `lower_apply_domain` and in the SortDomain read (`read_dictionary_into`). New row `a_typed_head_evidence_that_names_no_domain_is_a_fault` (wi_shed7): FAILS with the typed-head arms reading NoDomain as NoDomainType again — exactly it, measured.
10. `a_domain_relation_is_no_row_of_the_operation_table` calls `Dictionary.ops`; `a_bound_that_names_its_sort_enumerates_as_before` names its back-out (the ground bound's FILL: 17 rows red with it; routed through `apply_domain(Colour, ?x)` instead of the static call: 0 — both measured); `a_call_nested_in_a_woven_call_is_woven_too` asserts the structure (`common::body_calls`), not a count.
11. `common::one_definite_int`, `show_value`, `shown_rows`, `body_calls`.
12. `fill_goal` takes the provider entry's kind and read flag from `lower_apply_domain`; a per-query `read_layout_cache` computes a cited relation's read layout once (`bind_citation_reads` takes the layout).
13 + 15. A ROUTING-ONLY read — a slot read, or a typed head's SortDomain read (recognised by provenance) — is dropped from the OPENED body after the citation binding and both pre-checks (`is_routing_only_read`, a per-query `routing_read_cache`); both stay in the stored body the layout and the routes read.
14. `__domain_sub(?self, k)` reads slot k alone (`domain_sub_evidence`); a dictionary a read already built — no sub an expression or a variable — passes through `domain_evidence` uncopied.
16. `builtin_find_dictionary` scans its labels once; `is_unrouted_read` compares a cached interned symbol (`KnowledgeBase::unrouted_read_sym`, MONOTONE for layers). `builtin_type_domain`'s `early` scan was gone already with round 3's `__domain_guard`.
17. NOT STAMPED, by measurement: `woven_call_takes_slots` costs 1.3 µs a reduction — 0.04% of a woven query, 0.2% of an interpreter call — and a stamp is a new field on `Expr::ApplyWithin` that FDPJ8's one-shape rule would push into the reflect `apply_within` entity. Left for the user's decision.
18. `carrier_provided_by_witness` memoizes each spec's witness carriers inside `ProvidesIndex`, filled lazily per spec asked (the scan's own population — WI-954), dropped with the index: 15 µs -> 0.35 µs a DontFire call.

MEASURED (debug; a scratch query-loop harness over the SHED7 / P7VP4 fixtures, not committed; min of 7, before -> after): typed el(colours) x40 37.40 -> 34.41 ms; el(ints) x40 35.13 -> 32.61; same q x40 48.26 -> 40.49; DontFire noOrd x200 14.65 -> 11.59; value face letters x5 42.62 -> 41.11; load, fill colourLists, cited dom, woven cmpOne, slot viaOpOne, ruleDesc, slotDesc and plain unchanged within noise. Per-site probes: SortDomain read builds 40-240 a workload -> 0; slot reads run 200 -> 0; witness scan 3.05 -> 0.07 ms; bind_citation_reads 1.04 -> 0.48 ms; domain_evidence (value face) 1.67 -> 0.72 ms.

FOUND, NOT IN SCOPE (not ticketed): through `kb.resolve` a woven query's first dictionary derivation costs ~2.9 ms (`fetch_dictionary`) and a bridged call ~3 ms, against ~0.16 ms through an interpreter — every `query_unary` mutates the KB (interns a variable and a term), which looks like a cold start of the typing caches per query.

/code-review (high): 7 findings, 4 fixed (above), 3 skipped — no driving row for the partial-supply `__req_self` (no program found that reads the stand-in there), the second per-opening cache probe beside `cut_cache` (unmeasurable), and dropping routing-only reads at the source (the stored body IS the citation layout).

TESTS: full workspace 7674 passed, 0 failed (7672 + the two new rows); scaland testFull 578 + 35 passed (1 skipped).

### 2026-09-26T08:49:14Z — feedback — user

CORRECTION to the FOUND, NOT IN SCOPE note above: not a cold cache. Re-resolving the same goal with no KB mutation costs the same; the time is `resolve_with_rung` re-deriving the provider tree (`WeakOrd[T = Int64]`, 5 nodes, ~2.9 ms) on every uncited call, uncached. Filed with the user's agreement as WI-20260926-QPC89.

