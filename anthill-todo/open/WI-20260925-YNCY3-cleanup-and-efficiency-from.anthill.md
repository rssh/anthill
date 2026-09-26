## Attributes

- id: WI-20260925-YNCY3-cleanup-and-efficiency-from
- created: 2026-09-25T22:22:57Z

- status: Open
- status_agent: user
- status_at: 2026-09-25T22:22:57Z

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

