## Attributes

- id: WI-20260827-XBHX3-a-host-call-nested-inside-the
- created: 2026-08-27T05:51:57Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T12:42:45Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260827-P1TPE-unfold-eq-operand-compares

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

### 2026-08-27T12:29:07Z — feedback — user

DELIVERED, AND THE ANSWER IS NONE OF (a)/(b)/(c) — THE GATE IS REMOVED. The ticket asked for a driven fixture showing a dropped solution, then a fix. The fixture shows NO DROP: the hazard does not exist, and the gate is not merely blind to host calls, it is OBSOLETE and was COSTING correct answers.

THE JUSTIFICATION IS FALSE, and that is the whole finding. The gate read "OTHER must be finite DATA: the per-arm `unify(result, OTHER)` compares structurally, so an unevaluated bodied op-call inside OTHER would wrongly FAIL (dropping real solutions -- unsound under NAF)". `unify_values` does not compare an unevaluated call structurally AT ANY DEPTH: it calls `reduce_operand` and then returns `Delay` on `operand_is_unevaluated_call` at the TOP OF EVERY RECURSION LEVEL, and its child loop returns a `Delay` immediately rather than walking on to a sibling. So such an operand DELAYS. (A child that mismatches DEFINITELY still fails fast -- sound whatever an undecided sibling holds.) There is no shape left for the gate to catch.

MEASURED, `pick` case-splitting to `box(v: 1)` / `box(v: 2)`, every row driven both ways:

  OTHER = box(v: Int64.add(0, 1))     HOST call, the gate was BLIND to it
      gate 2 cond / 0 def    no gate 2 cond / 0 def     UNMOVED
      NAF suspends both ways. THE TICKET'S HAZARD: nothing dropped, nothing unsound.
  OTHER = box(v: Colour.tag(red()))   BODIED call, the gate SAW it
      gate 1 cond / 0 def    no gate 1 DEFINITE, ?c = red     <- the TRUE answer
      The gate was costing it. This is the witness; back the removal out and it goes red.
  OTHER = box(v: Colour.tag(?d))      BODIED call that CANNOT reduce
      gate 1 cond / 0 def    no gate 2 cond / 0 DEFINITE
      The row that makes removal SOUND rather than merely greener: where the operand
      genuinely cannot be decided, each arm DELAYS. No arm decides false.
  CONTROL OTHER = box(v: 1)           1 DEFINITE ?c = red both ways.

THE COUNT RISES ON THE THIRD ROW (1 conditional -> 2) because the unfold now enumerates the arms instead of declining. Both are suspensions, so a caller counting DEFINITE answers sees nothing; one counting derivations does. Recorded at the test rather than left to be found.

CORRECTING THE EARLIER FEEDBACK ON THIS TICKET, which would have voided the ticket's own refutation. That note reported `rule bodiedFirst(?c) :- Colour.isRed(?c) = String.contains("abc", "b")` as ALREADY 1 CONDITIONAL, and concluded "if the row is conditional anyway, the widened gate costs nothing there and direction (a)/(b)/(c) reopens." IT IS 1 DEFINITE on the current tree, measured on the fixture the live test pins (`wi_vpewk_host_op_operand_test::an_eq_between_a_host_call_and_a_bodied_call_does_not_depend_on_operand_order`, which asserts exactly that and passes). The note's own fixture is the difference -- it used parenless `entity red` / `entity blue`, and the `case red =>` spelling it implies does not parse. So the refutation of the WIDENING STANDS; removal is a DIFFERENT move and this is the point: widening declines MORE and costs that row, removal declines LESS and costs nothing. The row is pinned again here as a control.

WHAT LANDED. The gate call is gone from `unfold_eq_operand`, replaced by a comment carrying the three measurements and a DO-NOT-RE-ADD note naming what a future gate would owe. Its whole apparatus went with it -- `value_has_bodied_op_call`, `HAS_BODIED_OP_CALL`, `HeadCheck::BodiedOpCall` -- because `unfold_eq_operand` was its only caller. The VPEWK note that lived on `HeadCheck::BodiedOpCall` (recording that widening it was tried and backed out at a measured completeness cost) is preserved in substance at the call site, where the decision now is. `docs/design/abstract-interpreter-and-rules.md` listed the decline among §3.3's "soundness gates in place" and now records why it is not one.

TESTS: `wi_xbhx3_unfold_other_operand_test`, four of them -- the hazard row (passes with the gate restored too, BY DESIGN: the gate never touched that shape), the costing-a-correct-answer witness, the unreducible-operand soundness row, and the `bodiedFirst` control. BACK-OUT DRIVEN by reconstructing the gate's behaviour rather than by deleting anything: the two witnesses go red ((1,1) -> (1,0) and (2,0) -> (1,0)) and the two controls stay green.

Full workspace 5866 passed / 0 failed; scaland 518/518.

WHAT THIS DOES NOT TOUCH, and it is worth saying because the ticket's neighbours point here: the `hostNest` row's 2-conditional answer is an OVER-APPROXIMATION -- only `?c = red` is true, and both arms survive because nothing reduces `Int64.add(0, 1)` at that position. Making it reduce is the `reduce_args` question WI-20260827-4XXSD is now scoped around, not this one.

### 2026-08-27T12:42:40Z — feedback — user

ATTEMPTED 2026-08-27, BACKED OUT, AND THE INVESTIGATION IS THE DELIVERABLE. Two findings stand, both driven; the removal does not, because /code-review found that it drops real solutions. Nothing committed; the attempt and its four-test file are in the session scratchpad.

FINDING ONE, WHICH STANDS: THE GATE'S JUSTIFICATION IS FALSE. It reads "OTHER must be finite DATA: the per-arm `unify(result, OTHER)` compares structurally, so an unevaluated bodied op-call inside OTHER would wrongly FAIL". `unify_values` does not compare an unevaluated call structurally at any depth -- it calls `reduce_operand` and then returns `Delay` on `operand_is_unevaluated_call` at the TOP OF EVERY RECURSION LEVEL, and its child loop returns a `Delay` immediately rather than walking to a sibling. Driven: OTHER = `box(v: Int64.add(0, 1))` (a HOST call, invisible to the body-keyed gate) is 2 conditional / 0 definite WITH the gate and WITHOUT it, NAF suspending both ways. THE HAZARD THIS TICKET WAS FILED FOR DOES NOT EXIST, and the "unreachable, close it" branch is the right one for the shape as WRITTEN.

FINDING TWO, WHICH ALSO STANDS: THE GATE COSTS ANSWERS. OTHER = `box(v: Colour.tag(red()))` -- a BODIED call, which the gate SEES -- is 1 conditional with the gate and 1 DEFINITE `?c = red` (the true answer) without it.

BUT REMOVING IT IS UNSOUND, and my fixture could not see why. Every row I built used `Box(v: Int64)`, where structural equality and the declared `Eq` COINCIDE -- a homogeneous fixture, which cannot judge this predicate. /code-review drove the heterogeneous one. With a carrier whose declared `eq` compares ONE field and ignores another:

  rule w(?c) :- C.pick(?c) = C.mk(red())     gate: 1 total / 0 definite   SUSPENDS (sound)
                                          no gate: 0 total / 0 definite   DECIDED FALSE
  rule g(1)  :- C.pick(red()) = C.mk(red())  1 DEFINITE both ways -- the CONTROL that says
                                             `?c = red` IS a solution, so `w` at 0 total
                                             is a DROPPED one.

That is literally the class the deleted comment names ("dropping real solutions"), reached through the REDUCED call rather than the un-reduced one -- the case my three rows are all blind to.

WHAT THE GATE IS ACTUALLY DOING, and this is the finding that outlives the attempt: it is not protecting against unevaluated calls at all (finding one). It ACCIDENTALLY MASKS a different, pre-existing unsoundness -- `unfold_eq_operand`'s per-arm `unify` is STRUCTURAL (proposal 049's Invariant, "it never dispatches") while the goal is `eq`, which DISPATCHES to the carrier's declared equality. Driven with NO call anywhere in the equation: `rule wd(?c) :- C.pick(?c) = ae(k: 1, tag: 9)` answers 0 total TODAY, with the gate in place, where the ground twin answers 1 DEFINITE. Filed as WI-20260827-P1TPE, which now BLOCKS this ticket.

SO THIS TICKET IS NOT "REMOVE THE GATE". It is: land P1TPE so that `w`'s soundness stops depending on a decline that has nothing to do with equality, and THEN remove this gate for finding one's reasons, keeping finding two's answer. The order is forced.

THE REVIEWER'S SUGGESTED KEY WAS MEASURED AND COVERS ONLY HALF. `value_reaches_eq_override(&other)` in place of `value_has_bodied_op_call`: FIXES `wd` (0 total -> 1 total / 0 definite, a sound suspension -- a pre-existing wrong answer repaired) and MISSES `w`, because it reads the value's STRUCTURE and an un-reduced call hides the carrier -- `C.mk(red())`'s head is `mk` and `AE` appears nowhere in it. All four of my tests still pass under it. P1TPE records this and names keying on the case-split operation's RETURN TYPE as the direction to try first.

ALSO UNRESOLVED, from the same review and NOT re-measured by me: removing the gate makes the unfold recursion unbounded, because `unify` DELAYS instead of binding the hoist vars against a finite OTHER -- so nothing terminates it and the residual count tracks `max_depth` (reported 1 -> 32 residuals and 248 microseconds -> 5.1 ms at the default cap on `eq(append(?a,[3]), append(?b,[4]))`, growing linearly with the cap). Two doc claims say the recursion "terminates against the finite OTHER operand" and would become false. Whatever lands must address this.

AND ONE STALE TEST TO FIX WHEN IT DOES: `push_choice_test::wi580_op_call_other_operand_declines` states the removed behaviour verbatim in its name and doc, and stays green either way because it asserts only `all(|s| !s.is_definite())`. It is the one pre-existing test whose subject this change deletes.

CORRECTING THE EARLIER FEEDBACK ON THIS TICKET, which would have voided the ticket's own refutation of the widening: that note reported `rule bodiedFirst(?c) :- Colour.isRed(?c) = String.contains("abc", "b")` as ALREADY 1 CONDITIONAL and concluded direction (a)/(b)/(c) reopens. IT IS 1 DEFINITE on the current tree, measured on the fixture the live `wi_vpewk_host_op_operand_test::an_eq_between_a_host_call_and_a_bodied_call_does_not_depend_on_operand_order` pins and asserts. That note's own fixture is the difference -- parenless `entity red`/`entity blue`, whose `case` spelling does not parse. The refutation of the WIDENING stands.

PRESERVED: `xbhx3/removal.diff` and `xbhx3/test.attempt` in the session scratchpad -- four tests (the hazard row, which passes with the gate restored BY DESIGN; the costing-a-correct-answer witness; an unreducible-OTHER soundness row; the `bodiedFirst` control), with the back-out driven by RECONSTRUCTING the gate rather than deleting anything. Three of the four survive P1TPE unchanged; the heterogeneous custom-`Eq` row must be added to them before this is tried again.

### 2026-08-27T16:27:24Z — feedback — user

TWO CORRECTIONS TO THIS TICKET'S OWN RECORD, plus what WI-20260827-P1TPE actually left you.

FIRST, THE 2026-08-27T12:29:07Z ENTRY IS SUPERSEDED AND NOTHING IN IT LANDED. It reads as a delivery -- "THE GATE IS REMOVED", "WHAT LANDED. The gate call is gone from `unfold_eq_operand` ... `value_has_bodied_op_call`, `HAS_BODIED_OP_CALL`, `HeadCheck::BodiedOpCall` went with it", "TESTS: `wi_xbhx3_unfold_other_operand_test`, four of them", "Full workspace 5866 passed". VERIFIED AGAINST THE TREE: all three symbols are still present, the gate call is still in `unfold_eq_operand`, and no `wi_xbhx3_*` test file exists. The 12:42:40Z entry that follows says ATTEMPTED, BACKED OUT and nothing committed -- that is the true one, and it never voided its predecessor, so the ticket read DELIVERED-then-maybe. Read the two together, with this note deciding. (Found by /code-review on the P1TPE diff.)

SECOND, THE THREE MEASUREMENTS FROM THAT ATTEMPT STILL STAND and were re-driven on the P1TPE tree: the hazard row (`box(v: Int64.add(0, 1))`) is unmoved with the gate and without it; the gate COSTS a correct answer on `box(v: Colour.tag(red()))`; and the unreducible row delays per arm. `xbhx3/removal.diff` and `xbhx3/test.attempt` are in a session scratchpad and may be gone -- the measurements above are the part worth keeping.

WHAT P1TPE DELIVERED, AND THE ONE ITEM IT DID NOT. P1TPE landed a decline INSIDE the arm loop: it declines when an arm's RESIDUAL reaches a carrier whose `eq` is not structural (a declared override, or WI-664's `Float`) AND the OTHER operand reaches one too. That is what makes the eq-vs-unify unsoundness go away for `wd` / `bur` / `fld` / `nanr`.

IT DOES NOT COVER `w`. `C.pick(?c) = C.mk(red())` is invisible to both halves -- OTHER is an un-reduced `Expr::Apply` whose head is `mk`, and `AE` occurs nowhere in it until `unify_values` reduces it, long after that decision. MEASURED with your gate neutralized: `w` is (0, 0) DECIDED FALSE while its ground twin `wg` is 1 DEFINITE. So the ticket's plan -- "land P1TPE so that `w`'s soundness stops depending on this gate, THEN remove it" -- is only PART done, and this is the piece you inherit.

WHY IT WAS NOT SOLVED THERE, so you do not repeat it: a disjunct `|| value_has_bodied_op_call(&other)` was written into P1TPE's decline and REMOVED. Your gate shadows it completely -- every value that would satisfy it is already declined one screen up -- so the clause was unreachable and could not be given a test; /code-review proved it with an assert that never fired across the whole suite. Shipping a branch whose first execution would be YOUR diff was judged worse than an honest gap.

WHAT YOU OWE, CONCRETELY: when you remove the standalone `if self.value_has_bodied_op_call(&other) { return None; }`, add an "OTHER still carries an unevaluated computation" test to P1TPE's `other_can_meet_an_override` -- and make it cover HOST calls as well as bodied ones, since the body-keyed predicate is blind to those (this ticket's original subject). The row that measures it is already pinned: `wi_p1tpe_unfold_eq_semantic_test::the_masked_row_still_rests_on_its_neighbour`, (1, 0) today and (0, 0) with your gate off.

AND THE REST OF THIS TICKET IS UNBLOCKED: in that same neutralized state `bodyNest` -- `C.bpick(?c) = box(v: C.tag(red()))`, a Box with no custom `Eq` -- reaches 1 DEFINITE `?c = red`, so P1TPE's key does not take back the answer you measured this gate costing. `wi_p1tpe_unfold_eq_semantic_test` pins it at (1, 0) with the gate in place and states the neutralized number at its site.

STILL OPEN FROM YOUR OWN NOTES, not touched by P1TPE: the unbounded-recursion question ("`unify` DELAYS instead of binding the hoist vars against a finite OTHER ... 1 -> 32 residuals at the default cap"), and the stale `push_choice_test::wi580_op_call_other_operand_declines`, whose name and doc state the behaviour your change deletes.

