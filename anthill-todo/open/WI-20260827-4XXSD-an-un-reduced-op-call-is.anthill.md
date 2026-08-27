## Attributes

- id: WI-20260827-4XXSD-an-un-reduced-op-call-is
- created: 2026-08-27T11:16:05Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T11:57:02Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260827-XBHX3-a-host-call-nested-inside-the

## Description

AN UN-REDUCED OP CALL IS HANDED TO A HOST FUNCTION AS DATA, and the only thing stopping it is the ground gate — which stops it BY ACCIDENT. Split out of WI-20260827-1ZG70's analysis; it is that ticket's PREREQUISITE and a wrong answer on its own today.

THE MECHANISM. `reduce_op_value` reduces a host callee's arguments (WI-880) and falls back with `.unwrap_or(v)` — so an argument whose own reduction FAILS comes back as the un-reduced CALL. `bridge_op_to_eval` then ground-gates that argument, and a call whose arguments are ground IS deeply ground. The gate passes, the host function runs on `Fn(inner, [...])`, and it commits.

MEASURED 2026-08-27 on the tree at b09aa9f1, driven through `term_field` (whose carrier refusal is the neighbour ticket, and is only the CAUSE — any un-reducible inner call does this):

  rule f1(?t) :- term_field(as_term(some(7)), "value") <=> ?t
      SUSPENDS (definite=false) — this is the inner call failing
  rule f2(?n) :- term_functor_name(term_field(as_term(some(7)), "value")) <=> ?n
      -> some("term_field")   1 DEFINITE.  The CALL's functor, not the term's.
  rule f4(?s) :- term_to_string(term_field(as_term(some(7)), "value")) <=> ?s
      -> "term_field(as_term(some(value: 7)), \"value\")"   1 DEFINITE.
      The printed text of the un-reduced CALL. Nothing is more explicit than this row.

EVERY ARGUMENT ABOVE IS GROUND. No logic variable is involved anywhere — this is not a groundness problem and does not wait on 1ZG70.

TWO ROWS ARE BLIND and are recorded so they are not mistaken for witnesses: `term_as_int(term_field(...))` answers `none()` BOTH before and after (before, from reading the call; after, because the argument is the `Option` wrapper, which is not a `Const` int) — same value, opposite reasons. `term_as_int(term_field(...)) = some(7)` is 0/0 both ways for the same reason. The discriminating rows are f1/f2/f4.

THE REPAIR, driven: `bridge_op_to_eval` refuses an argument for which `is_unreduced_op_call` answers true, on its own line, BEFORE the ground check. That predicate ALREADY owns exactly this question at the `eq` operand position (WI-20260826-VPEWK's host leg, and its doc argues the case); this is the same question one position over, at a host ARGUMENT.

MEASURED across the repair: f2 and f4 go from a definite WRONG value to a sound SUSPENSION; f1 is unmoved (it is the cause, not the symptom); `term_as_int(term_field(...))` loses its accidentally-right `none()` and suspends too, which is a small completeness cost paid back by the neighbour ticket. WI-880's own guards are UNMOVED: `term_as_int(as_term(7)) = some(7)` stays 1 DEFINITE and `= none()` stays 0.

WHY THE GROUND GATE CANNOT KEEP DOING THIS JOB, and why this must land BEFORE 1ZG70. The gate refuses an un-reduced call only when the call happens to contain a VARIABLE. WI-880 already paid for this coordinate once (`term_as_int(as_term(7)) = none()` went 0 -> 1 DEFINITE because a GROUND call passed the gate) and repaired it by REDUCING a host callee's arguments — which covers the case where the inner call CAN reduce, and not the case where it FAILS to, which is this ticket. WI-20260827-1ZG70 then wants to RELAX the ground gate for the reflect family; the moment it does, every un-reducible inner call becomes readable data at every exempt slot. Splitting the two questions is what makes 1ZG70 safe to land at all.

THE CORPUS DOES NOT REACH THIS. Full workspace is 5863 passed / 0 failed WITH the repair and 5863 / 0 WITHOUT it — identical. Green is not the evidence here; f1/f2/f4 are. A test must be written that fails when the refusal is backed out.

ACCEPTANCE: f2 and f4 above suspend rather than answering a definite value read off the un-reduced call, driven, with the back-out measurement stated at the test site; WI-880's `term_as_int(as_term(7)) = some(7)` stays 1 and `= none()` stays 0, both driven in the same file; the two blind rows are recorded AS blind rather than asserted as witnesses; the split between "is this ground" and "is this an un-reduced call" is stated at `bridge_op_to_eval`'s soundness-gates doc, which today lists only the first; full workspace green via rustland/scripts/test.sh.

REFERENCE: `bridge_op_to_eval` / `reduce_op_value` / `is_unreduced_op_call` (rustland/anthill-core/src/kb/resolve.rs), docs/kernel-language.md §5.2. A driven prototype of the refusal exists and measured green.

## Changes

### 2026-08-27T11:56:58Z — feedback — user

ATTEMPTED 2026-08-27 AND BACKED OUT. The three-line repair this ticket describes — refuse an unevaluated-call argument at `bridge_op_to_eval`, ahead of the ground check — IS WRONG IN TWO DIRECTIONS, both measured, and the correct repair is a different and larger change. Nothing was committed; the attempt and its diff are preserved.

WHAT WAS BUILT AND WHAT IT MEASURED. The gate went in, the two witnesses in the ticket flipped to sound suspensions, WI-880's guards held, full workspace 5864 passed / 0 failed, scaland 518/518. /code-review then returned fifteen findings and the two that matter were driven against baseline.

DEFECT ONE — THE GATE IS TOP-LEVEL AND THE DEFECT IS NOT. `bridge_op_to_eval` inspects the argument's HEAD; `value_deep_ground` beside it RECURSES. So a call ONE CONSTRUCTOR DEEP walks through untouched. Measured, identical WITH and WITHOUT the gate:

  term_to_string(as_term(some(term_field(as_term(some(7)), "value"))))
      -> "some(value: term_field(as_term(some(value: 7)), \"value\"))"   1 DEFINITE
  term_to_string(as_term(some(Int64.add(1, 2))))  -> "some(value: add(1, 2))"   1 DEFINITE
  term_to_string(as_term([Int64.add(1, 2)]))      -> "[add(1, 2)]"              1 DEFINITE
  control: term_to_string(as_term(some(7)))       -> "some(value: 7)"           correct

The first row is THIS TICKET'S OWN "least deniable witness" with one `some(...)` wrapper added. The repair fixed the row the ticket quoted and left the class it named.

DEFECT TWO — THE GATE DELETES CORRECT ANSWERS, and this one is a regression the attempt introduced. `bridge_op_to_eval` is shared by FOUR call sites and only ONE of them reduces its arguments: `reduce_args = host_op_reducible_at_a_value(op)`. At the `needs_dict`, body-less and complex-body sites the arguments were NEVER reduction candidates, so refusing an unevaluated one refuses a call the interpreter could decide. Measured across the back-out:

  operation pick(x: Int64) -> Int64 = if Int64.gt(1, 0) then 42 else x   -- never reads x
  operation g() -> Int64 = 7
  rule p3(?r) :- pick(g()) <=> ?r
      baseline   1 DEFINITE, 42
      with gate  0 definite / 1 total, SUSPENDS
  controls: pick(1) and pick(h()) (h body-less unmapped) answer 42 both ways.

/code-review reports the same shape as an UNSOUNDNESS at two of those sites (a hard failure rather than a delay, with `not(...)` answering 1 DEFINITE) — filed below as unverified, because it flagged them not back-out-verified itself.

THE ROOT, AND WHY IT IS NOT A PLACEMENT TWEAK. The ticket's mechanism paragraph says "an argument whose OWN reduction failed comes back as the call". That premise holds ONLY at the host site. Moving the gate into `reduce_op_value`'s host arm fixes defect two — but defect one then needs a DEEP walk, and a deep refusal needs to tell "un-reduced and will STAY un-reduced" from "not yet reduced, and reducible here". THAT DISTINCTION IS ALREADY KNOWN NOT TO EXIST. `HeadCheck::BodiedOpCall`'s own comment records the identical widening being TRIED AND BACKED OUT on the neighbouring gate for the identical reason, at a measured completeness cost (`Colour.isRed(?c) = String.contains("abc","b")` 1 DEFINITE -> suspension), and hands the open question to WI-20260827-XBHX3 in those words. This ticket walked into it from the other side.

THE REPAIR THAT WOULD ACTUALLY WORK, and it is the completeness-preserving one rather than a wider refusal: make the host arm's argument reduction RECURSE INTO CONSTRUCTORS. Today `reduce_args` reduces only the top-level argument and bails at the first constructor, so `as_term(some(Int64.add(1, 2)))` is never given the chance to become `some(3)` — it is not that reduction FAILED, it is that reduction was never attempted. Recursing makes those rows ANSWER rather than suspend, and only what still cannot reduce needs refusing. Then the refusal is small, deep, and scoped to the host arm.

SO THIS TICKET IS REALLY: (1) recurse the host arm's argument reduction through constructors and list literals; (2) refuse, deeply and at that arm only, what still holds an unevaluated call; (3) leave the other three bridge sites alone. Its acceptance should be rewritten around the `some(...)`-wrapped rows above, since the flat ones it currently names are satisfied by a repair that fixes almost nothing.

DEPENDENCY: add WI-20260827-XBHX3, or at least read it first — step (2) is its open question and a decision there decides the shape here.

PRESERVED, not lost: the attempt's diff and its four-test file (two witnesses, one per predicate leg; a WI-880 control; a boundary row) are in the session scratchpad as `4xxsd-attempt.diff` and `wi_4xxsd_test.attempt`. The builtin leg they drive is real and worth keeping whatever shape the repair takes — with the narrow `is_unreduced_op_call`, `term_functor_name(as_term(Int64.add(1,2)))` answers `some("add")`, `term_as_int` of it answers `none()` where the truth is `some(3)`, and `term_to_string(as_term(box(7).v))` answers the desugared `field_access(box(v: 7), "v", type_arg: [...])` internal form in a user-visible String.

TWO MORE /code-review FINDINGS WORTH KEEPING, NEITHER VERIFIED HERE:
  * a residual `if`/`match` argument reaches `occurrence_to_term`'s `debug_assert!(false, "unexpected non-goal Expr")` — panics in debug, becomes `Term::Bottom` in release. Reported as driven by the reviewer; NOT re-measured here, and NOT established as new.
  * `DEEP_GROUND.opaque = true`, so an opaque-headed residual holding an UNBOUND variable reads as deeply ground — which undercuts the "ground gate" half of the story this ticket and WI-20260827-1ZG70 both lean on. Structural, not driven.

AND ONE ABOUT THE CONTROL FIXTURE, which was right: the attempt blessed `term_functor_name(myop(7)) -> some("myop")` as an intended boundary, citing the `Set.insert` symbolic-algebra exemption. `myop` is declared-but-unimplemented with NO rules over it, which is not the exempt shape that exemption is argued from — a body-less SPEC op the membership RULES resolve over. Build that control from the exempt shape, or key it on `body_less_dispatchable` rather than on "has no body".

