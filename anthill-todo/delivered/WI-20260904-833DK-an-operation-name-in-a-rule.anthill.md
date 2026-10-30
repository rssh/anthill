## Attributes

- id: WI-20260904-833DK-an-operation-name-in-a-rule
- created: 2026-09-04T16:45:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-30T19:34:50Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN OPERATION NAME IN A RULE-BODY FUNCTION SLOT IS NOT CALLABLE. It arrives as a
`Value::Node(Ref(op))` and the apply path — which knows `Value::Closure` and
`Value::OpRef` — dies with the CALLEE'S OWN PARAMETER read as an operation name.

MEASURED 2026-09-04 on the WI-20260904-QQPQ2 tree (rustland):

  operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)
  operation inc1(n: Int64) -> Int64 = n + 1
  rule value(?r) :- ?r <=> apply1(inc1, 2)
    -> LOADS CLEAN. One solution, FLOUNDERED, `?r` unbound.
       The bridge reports `UnknownOperation { name: "<ns>.apply1.f" }` and
       residualizes (`bridge_op_to_eval`'s "any other eval error residualizes",
       kb/resolve.rs).

  operation v() -> Int64 = apply1(inc1, 2)          the CONTROL
  rule value(?r) :- ?r <=> v()                       -> 3, definite.

WHERE IT SITS. `bridge_op_to_eval` hands each operand ON THE CARRIER THE RESOLVER
PROVED IT ON, so a bare operation NAME written in a rule-body data slot arrives as a
`Value::Node` occurrence. In an OPERATION body the same name is eta-expanded by
`reduce_var` into a `Value::OpRef` and is callable. Nothing performs that expansion for
a bridged operand, so the callee's `f(n)` looks up local `f`, finds a value the apply
path does not classify as callable, and falls through to dispatch — which reads `f` as
an operation name qualified under its caller.

WI-784'S RULE IS WHAT MAKES IT A DEFECT AND NOT A MISSING FEATURE: a lambda and an
operation are INTERCHANGEABLE as function values. The lambda spelling of the identical
program answers (WI-20260904-50B2K's row, and QQPQ2's for the multi-binder case); the
operation spelling does not.

NOT A TUPLE / ARITY QUESTION — measured, and this is what separated it from QQPQ2 rather
than a scope judgement. The failure is raised BEFORE any argument is destructured:
`spread_eta_args` (the tuple reader QQPQ2 repaired) is NEVER ENTERED, and the row above
is at ONE parameter, where no tuple exists anywhere in the program. The two-parameter
spelling `apply2(sum2op, (a: 1, b: 2))` fails identically and for this reason, not for
the carrier one.

PINNED, so this does not have to be rediscovered:
`rustland/anthill-core/tests/include/wi_qqpq2_tuple_carrier_test.rs::an_eta_d_operation_name_is_a_known_gap`
asserts the CURRENT behaviour — the single solution is a RESIDUAL, not definite. When it
becomes definite the gap is closed; delete that row and say which change closed it.

WHERE THE REPAIR GOES, not investigated beyond the diagnosis above: the callee
classification in the apply path (`eval/eval.rs`), which must recognize a value that
VIEWS as a nullary functor naming an operation and mint the `OpRef` `reduce_var` would
have. Its own controls are needed — that area carries WI-577's builtin-backed OpRef
fallback and WI-801's `classify_application`, and widening what counts as callable is
exactly the kind of change that must name the rows a back-out fails.

## Changes

### 2026-10-30T19:34:51Z — feedback — claude

Delivered in 4903165d with WI-20261023-Y6QW2, whose operation-reference half is this ticket: the apply path recognizes a value that views as a nullary functor naming an operation and mints the OpRef reduce_var would (the same eta_op_ref, extracted), with the typer's dictionary, operation slots and spread labels. ?r <=> apply1(inc1, 2) answers 3, definite, and the two-parameter apply2(sum2op, (a: 1, b: 2)) answers 3 through spread_eta_args. The pinned row wi_qqpq2…::an_eta_d_operation_name_is_a_known_gap answered 3 and is deleted as it asks; its programs are wi_y6qw2_function_value_from_a_rule_test::an_operation_name_in_a_function_slot_is_applied, failing with the conversion backed out. Controls named by the ticket: the builtin-backed OpRef path is untouched (an OpRef dispatches through dispatch_resolved_operation as before); full workspace 11,232 passed. Scaland has no evaluator, nothing to port; its sbt suite was not run for this change (no scaland file changed).

