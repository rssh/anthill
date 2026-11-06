## Attributes

- id: WI-20261015-ZPETZ-the-bridge-s-host-entry-and
- created: 2026-10-15T17:59:38Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T17:59:38Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

THE BRIDGE'S HOST ENTRY AND THE IN-BODY DISPATCH ARE TWO FACES OF ONE CALL, and each special case has to be taught to both by hand.

A rule-body application reaches the evaluator through `invoke_op_with_requirements` (the bridge's `call_op_bridged*`); an operation body's call goes through `dispatch_call_with_requirements_inner` / `dispatch_resolved_operation`. Each keeps its own list of routes: a body, a builtin, value-directed dispatch to a supplier, the `eq` bridge, the `Error.reify` boundary. Twice a route existed on one face only and a rule body could not reach what an operation body did: WI-1057 copied value-directed dispatch to the host entry after a rule body could not reach a fact-route supplier, and WI-20260908-9WVT7 (2026-10-15) taught the host entry the `Error.reify` boundary after `rule direct(?r) :- Error.reify(lambda () -> f(), ?r)` answered nothing. Proposal 068 §1 says a rule-body application is evaluated by the evaluator that runs operation bodies, with the same dispatch; two lists make that a promise kept by copying.

THE CHANGE: the host entry hands a call to the in-body dispatch itself (one frame pushed for the call, then `dispatch_resolved_operation`), so a route added there is a route of both, and the host entry's own copies go: the WI-1057 value-directed arm, the `Error.reify` interception (`Interpreter::invoke_reify_boundary`).

THE CONSTRAINT: this path is the bridge's eval↔SLD crossing, whose native stack per crossing is a measured budget (`BRIDGE_REENTRY_CAP`; its canary is `wi625…::eval_undecidable_instance_fact_eq_is_loud_not_false` under `RUST_MIN_STACK`). The change must not add a native frame per crossing, in an unoptimized build either.

RELATED: WI-20260926-DSEXA (068 §8 steps 3–4, the per-consumer reductions retired).

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): one dispatch serves both entries; the two copies above are deleted, and `wi_9wvt7_reify_rule_body_test` and the WI-1057 rows still pass; the canary re-measured; full workspace green.

## Changes

### 2026-11-06T06:22:33Z — feedback — claude

MEASURED 2026-11-06 against proposal 073 (docs/proposals/073-abstract-values-are-instances.md), decided with the user. The WI-1057 arm this ticket deletes from the host entry is the host-entry copy of `dispatch_resolved_operation` step 3b, which 073 stage 3 (WI-20261105-P0QGF) removes from both faces. Its own reason is gone: over `operation otherDescribe(x: Leaf) -> Int64 = 9` and `namespace Leaf provides Desc[T = Leaf, describe = otherDescribe] end` with no other supplier, `operation probe() -> Int64 = Desc.describe(leaf())` read through `rule rOp(?r) :- unify(?r, probe())` and `rule answer(?r) :- Desc.describe(leaf(), ?r)` both answer 9 on b219d492, and with the value-direction census trace on neither face reaches a value-directed step: the typer decides the call at load. The header of tests/include/wi1043_bodyless_rule_body_test.rs ("Row 3 has no pin", WI-1057's back-out table) is stale and is corrected when the arm goes. In the census over the full workspace (62882ef0, source unchanged since) the arm is reached by 14 tests, all of them 073's cases: `Stream.splitFirst` -> `List.splitFirst` in Stream's default bodies (wi_shed7_reads_wait_test::the_split_first_solver_finishes); `WeakOrd.compare` -> `Int64.compare` (wi_5g28a_rule_dictionary_test: a_rule_citation_passes_the_callers_dictionary, an_operation_passes_its_dictionary_to_an_operation, a_returned_relation_keeps_the_callers_dictionary, a_caller_without_a_dictionary_answers_as_before; wi_shed7_reads_wait_test::every_read_waits; wi_k4jgc_evaluation_strategy_test::a_body_less_spec_operation_dispatches_in_a_value_slot; wi_p7vp4_rule_body_requirements_test::a_call_at_a_concrete_carrier_keeps_its_own_route; wi_0rrqp_clause_typed_through_constructor_test: the_slot_is_read_wherever_the_clause_states_its_requirement, a_slot_the_clause_writes_is_not_read_off_the_argument); `IndexedSeq.length` -> `List.length` (wi_8rjk8_guarded_equation_fires_test::stdlib_indexed_seq_out_of_bounds_law_fires_to_a_value); `Llm.complete` -> `FakeLlm.complete` (guardians: a_fake_model_answers_from_its_own_value_and_sends_nothing, one_round_of_the_generation_loop_answers_the_same_verdict, a_refused_round_feeds_the_next_prompt). DECIDED: this ticket comes before 073 stage 3, which depends on it, so stage 3 removes value-direction from one dispatch and a rule body cannot answer differently from an operation body while it is under way. Here the WI-1057 arm is deleted because the in-body dispatch covers it; its route then goes with stage 3. What is this ticket's alone: one dispatch for both entries, and the `Error.reify` copy.

