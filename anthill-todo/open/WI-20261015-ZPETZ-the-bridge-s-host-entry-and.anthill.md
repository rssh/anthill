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

