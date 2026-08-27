## Attributes

- id: WI-20260827-XBHX3-a-host-call-nested-inside-the
- created: 2026-08-27T05:51:57Z

- status: Open
- status_agent: claude
- status_at: 2026-08-27T05:51:57Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A HOST CALL NESTED INSIDE THE `OTHER` OPERAND IS COMPARED STRUCTURALLY BY THE WI-580 UNFOLD -- the safety gate reads BODIED op-calls only, and the naive widening costs completeness.

RAISED BY /code-review ON THE WI-20260826-VPEWK DIFF, both the hazard and the cost of the obvious fix are MEASURED below. Pre-existing: VPEWK did not introduce it, it made it the shape that is left over.

THE GATE. `unfold_eq_operand` (rustland/anthill-core/src/kb/resolve.rs) case-splits an unground op-call operand into one continuation per `match` arm of the callee body, and each arm asserts `unify(result_i, OTHER)`. Before it does, it asks `value_has_bodied_op_call(&other)` and DECLINES if true. That gate own comment states the reason: "OTHER must be finite DATA: the per-arm `unify(result, OTHER)` compares structurally, so an unevaluated bodied op-call inside OTHER would wrongly FAIL (dropping real solutions -- unsound under NAF)."

THE HOLE. The gate reads `HeadCheck::BodiedOpCall`, i.e. `builtins.get(f).is_none() && op_body_node(f).is_some()`. A HOST-IMPLEMENTED op has no body node, so a host call inside OTHER is INVISIBLE to it -- and a host call is a computation, not data, so it is exactly what the gate exists to refuse. At TOP level this does not bite (VPEWK made `reduce_operand` reduce a host call before the compare); NESTED inside OTHER nothing reduces it, and the structural compare then drops real solutions. Unsound under NAF for the same reason the bodied case is.

NOT DRIVEN: I did not build a fixture with a host call nested inside a data structure in OTHER while the other operand case-splits. Reported as a code-path reading. Constructing that fixture is the first step of this ticket, and if it turns out UNREACHABLE say so and close -- the gate comment would then need to say why.

THE OBVIOUS FIX IS WRONG, MEASURED. Widening the head check to `op_body_node(f).is_some() || is_interpreter_mapped_op(f)` was tried on the VPEWK tree. It is SOUND -- the gate only ever DECLINES more, and a decline falls back to the builtin, which delays -- but it costs completeness on a query that works today:

  rule bodiedFirst(?c) :- Colour.isRed(?c) = String.contains("abc", "b")
      body-only gate (today):  1 solution, DEFINITE
      widened gate:            1 solution, CONDITIONAL (residual eq(isRed(?_), contains(...)))

`Colour.isRed` is a bodied `match` op, `String.contains` is host-mapped. The split is legitimate and the widened gate abandons it, because OTHER holds a host call that `reduce_operand` WOULD have reduced before any structural compare ever happened. Backed out for that reason; the regression is not worth an undriven hazard.

WHAT THE GATE ACTUALLY NEEDS, and this is the ticket. It cannot currently distinguish "un-reduced and will STAY un-reduced" (the hazard -- nested, nothing will reduce it) from "not yet reduced but reducible at this position" (the top-level host call, which `reduce_operand` handles). Both present as the same `Expr::Apply`. Candidate directions, none chosen: (a) REDUCE `other` before gating rather than gating on its un-reduced form, and measure what that costs the hot path; (b) make the gate DEPTH-AWARE -- a top-level host call is fine, a nested one is not; (c) leave the top-level case to `reduce_operand` and widen the gate only below depth 0.

ACCEPTANCE: a driven fixture with a host call nested inside OTHER, showing the dropped solution and its NAF polarity (or a demonstration that the shape is unreachable, with the reason written at the gate); the chosen direction implemented; `bodiedFirst` above still 1 DEFINITE, asserted as a control with its measurement stated; and the note now at `HeadCheck::BodiedOpCall` replaced by whatever this ticket concludes. Full workspace green via rustland/scripts/test.sh.

