## Attributes

- id: WI-20261017-JTA3E-a-rule-body-never-checks-an
- created: 2026-10-17T05:24:26Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T05:24:26Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

A RULE BODY NEVER CHECKS AN OPERATION CALL'S ARGUMENTS AGAINST ITS SIGNATURE — `?x <=> needs_int("s")` loads and answers a String from an operation declared `-> Int64`. Measured 2026-10-17 on ce868fe4.

THE FINDING. Over `operation needs_int(n: Int64) -> Int64 = n` and `operation inc(n: Int64) -> Int64 = n + 1`:
  rule passThrough(?x) :- ?x <=> needs_int("s")     LOADS; query answers ?x = "s" — a WRONG ANSWER, the declared `-> Int64` handed out a String
  rule arith(?x) :- ?x <=> inc("s")                 LOADS; query is a conditional answer with a warning ("could not be evaluated by the resolver: type mismatch: expected Int64, got Node and Int64")
  rule r(?x) :- ?x <=> needs_int(str_op())          LOADS (`str_op() -> String`): a call-shaped argument is not checked either
  rule r(?x) :- needs_int_b("s")                    LOADS (`needs_int_b(n: Int64) -> Bool`): nor is a goal-position call
  rule r(?x) :- ?x <=> needs_int(1 + "s")           REFUSED — by `add`'s own check, a spec op; not by `needs_int`'s
  operation viaOp() -> Int64 = needs_int("s")       REFUSED: "type mismatch in needs_int.n (op-arg): expected Int64, got String"
So one call gets two verdicts by the body it is written in. NOT a proposal-055 question — the String literal is the control.

WHY. The rule-body typer is a DISPATCH walk (`kb/typing/rule_dispatch.rs`, `dispatch_calls_in_occ` / `call_dispatch_shape`). Only spec-op calls (`=`, arithmetic) reach `type_check_node`. In a VALUE position any other `Expr::Apply` is `CallDispatch::DataTerm`, name-checked only (`data_functor_error`); in a GOAL position a plain operation falls to `Subgoal`, shape-checked against clauses only — although `call_dispatch_shape`'s own doc says "an OPERATION named as a goal has a signature; both stay `Call`", which the code does not do. The WI-20260904-50B2K `declared` check fires only on a child the walk dispatches, so a leaf argument in a declared slot is never compared.

`data_functor_error` records three measured reasons a data slot is not type-checked. Reason 1 — "it loses the EXPECTATION": a sort name read as a type only where a `Type` was expected — is RETIRED by WI-20260824-JM6ZW (both bodies' walks record type values themselves), so that doc is stale and is corrected here. Reason 2 (scope under a binder) is what `CallDispatch::BinderForm` already answers by handing the binder form over whole. Reason 3 (storing the redex-free node changes what the rule means) is answered by CHECKING without STORING: the 50B2K tail already returns `walked` for `Call`. The summary "a rule body's data slot holds a TERM" is true of a relation goal's argument, which is matched; it is not true of a `<=>` operand, which is EVALUATED as a call, so the call's contract applies to it.

WHAT. Check an operation call's arguments against its declared parameters in a rule body as `check_apply_iter` checks them in an operation body — at least where the call is evaluated (a `<=>` operand, an operation named as a goal), without storing the typer's rewritten node. Decide and state whether a call in a relation goal's DATA slot (a term the clause matches, never evaluated) is in or out. Correct `data_functor_error`'s reason 1 and the goal-ladder doc of `call_dispatch_shape`.

CONTROL. One fixture per row above, each in both bodies; say at the test site which rows fail with the change backed out. Keep green: `wi1058_rule_body_position_test`, `wi884_sibling_backing_test` (reason 3), `wi620_paren_lambda_param_test` (reason 2), `wi_50b2k_binder_inference_test`, `wi1056` (one report, not two, for a slot whose descendant already reported). Families (`scripts/families.sh`): commit any verdict that moves.

DONE WHEN: the six rows above give the operation body's verdict in a rule body (the String passthrough refused at load); the gate is green.

