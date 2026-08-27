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

## Changes

### 2026-08-27T08:33:47Z — feedback — user

A DRIVEN FIXTURE FOR THIS TICKET'S FIRST STEP EXISTS NOW, on a neighbouring path — WI-20260827-P83AR, filed 2026-08-27 while finishing WI-880's reflect migration.

THIS TICKET SAYS 'NOT DRIVEN -- I did not build a fixture with a host call nested inside a data structure in OTHER... Constructing that fixture is the first step of this ticket, and if it turns out UNREACHABLE say so and close.' A nested host call IS reachable and IS unsound, though by a different route than the gate this ticket names, so the 'unreachable, close it' branch is not the one to take.

MEASURED (P83AR's fixture, three operations of MY OWN, all non-generic, all host-mapped):
  operation mk(n: Int64) -> Term               mapped "as_term"
  operation tsq(t: Term) -> Option[T = Int64]  mapped "term_as_int"
  operation sq(a: Int64) -> Int64              mapped "int_abs"
  rule termNest(1) :- tsq(mk(7)) = some(7)  -> total 0, DECIDED FALSE  (eval answers some(7))
  rule intNest(1)  :- sq(sq(7)) = 7         -> total 1, suspends, sound
That is `reduce_op_value` / `is_unreduced_op_call`, not `unfold_eq_operand` — no case-split is involved and the failure is a WRONG answer rather than a dropped one. Separate ticket for that reason.

WHY IT IS STILL YOURS TO READ: the separator is the DECLARED TYPE and nothing else — the two rows above differ only in `Term` versus `Int64`. That is this ticket's own open question made concrete. This ticket says the gate 'cannot currently distinguish un-reduced-and-will-STAY-un-reduced from not-yet-reduced-but-reducible-at-this-position. Both present as the same `Expr::Apply`.' Where the parameter is `Term`, they also present as the same THING: an un-reduced call IS a term, so 'is this data?' has a legitimate yes, and any depth- or reducibility-aware rule chosen here (directions a/b/c) has to answer that case too or it will fix one path and leave the other.

NOT A MERGE PROPOSAL — two mechanisms, two acceptances. A cross-link so neither is worked in isolation, and so this ticket's first step does not start from scratch.

### 2026-08-27T09:04:29Z — feedback — user

UPDATE — the neighbour this ticket was cross-linked to (WI-20260827-P83AR) is DELIVERED, and the fix changes the ground under one of this ticket's own measurements. Re-measure before starting.

WHAT CHANGED. `reduce_op_value` (kb/resolve.rs) now REDUCES a HOST callee's arguments before bridging, rather than only sigma-walking them. So a host call nested in a host call's ARGUMENT now reduces to a value instead of residualizing — WI-20260826-VPEWK's documented remainder is closed (`:- Bool.and(Bool.not(false), true) = true` went 0-with-a-residual to 1 DEFINITE).

THIS TICKET'S GATE IS UNTOUCHED. `unfold_eq_operand`'s `value_has_bodied_op_call` still reads `HeadCheck::BodiedOpCall`, so a host call inside OTHER is still invisible to it. The hazard as WRITTEN stands; what changed is the neighbourhood it sits in.

RE-MEASURE THE `bodiedFirst` ROW BEFORE RELYING ON IT. This ticket records `rule bodiedFirst(?c) :- Colour.isRed(?c) = String.contains(\"abc\", \"b\")` as '1 solution, DEFINITE' today and '1 CONDITIONAL' under the widened gate, and uses that delta to refute the obvious fix. On the CURRENT tree I measure it as 1 CONDITIONAL already — with the argument-reduction change and with it backed out, i.e. my change does not move it. So either the row moved earlier (WI-880's arithmetic or reflect migration both landed since), or my fixture differs from yours in `Colour`'s spelling (mine is `entity red` / `entity blue`, no parentheses). Either way the refutation this ticket rests on needs re-running against the tree as it now is; if the row is conditional anyway, the widened gate costs nothing there and direction (a)/(b)/(c) reopens.

ALSO: the driven fixture this ticket asked for as its first step is in P83AR and now lives as a regression guard in `wi880_reflect_mapping_test::a_nested_host_call_reduces` — three host-mapped operations (`mk`/`tsq`/`sq`) that separate a `Term`-typed parameter from an `Int64`-typed one, plus the `Set.insert(Set.empty(), 1)` row that any widening of reducibility must not break.

