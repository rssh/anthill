## Attributes

- id: WI-20260827-P1TPE-unfold-eq-operand-compares
- created: 2026-08-27T12:41:52Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-27T16:26:51Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`unfold_eq_operand` COMPARES STRUCTURALLY WHERE THE GOAL IS SEMANTIC, so a case-split over a carrier with a declared `Eq` DROPS REAL SOLUTIONS. Pre-existing, driven, and reachable with NO op-call anywhere in the equation. Found while investigating WI-20260827-XBHX3, which is a DIFFERENT question about the same site.

THE MECHANISM. `unfold_eq_operand` expands a `SemEq` goal whose operand is an unground bodied op-call into one continuation per `match` arm, and each arm asserts `unify(result_i, OTHER)`. `unify` is STRUCTURAL by construction -- proposal 049's Invariant, stated at `builtin_unify`: "Carrier-agnostic and structural-only -- it never dispatches". But the goal being expanded is `eq`, which DOES dispatch to the carrier's declared equality (kernel-language.md 8.3). Where the two disagree, the arms decide by the wrong relation.

MEASURED 2026-08-27 on the tree at b09aa9f1, and the second row has no call in it at all:

  sort AE
    entity ae(k: Int64, tag: Int64)
    operation aeq(a: AE, b: AE) -> Bool = a.k = b.k
    provides PartialEq[T = AE, eq = aeq]
    provides Eq[T = AE]
  end
  sort C
    entity red   entity green
    operation pick(c: C) -> AE =
      match c  case red() -> ae(k: 1, tag: 8)   case green() -> ae(k: 2, tag: 0)
  end

  rule wd(?c) :- C.pick(?c) = ae(k: 1, tag: 9)      -> 0 total, 0 definite  DECIDED FALSE
  rule g(1)   :- C.pick(red()) = ae(k: 1, tag: 9)   -> 1 DEFINITE           the CONTROL

`g` is the whole argument: GROUND, the same equation, and it answers 1 -- because the ground path takes the declared `Eq` and `aeq` compares only `k`. So `?c = red` IS a solution of `wd`, and the unfold answers that there is none. A dropped solution, and a definite refutation rather than a suspension, so NAF over it can conclude.

WHY THE `tag` FIELD IS THE POINT: the two values agree on `k` (declared-equal) and differ on `tag` (structurally unequal). A fixture whose values agree structurally measures NOTHING here -- the two relations coincide and every arm answers the same either way. Any test for this must vary the field the declared `eq` IGNORES.

IT IS MASKED, TODAY, ON PART OF ITS DOMAIN, which is why nothing has found it. `unfold_eq_operand` declines whenever OTHER carries a bodied op-call (`value_has_bodied_op_call`). So the sibling row

  rule w(?c) :- C.pick(?c) = C.mk(red())            -> 1 total, 0 definite  SUSPENDS

is sound only by accident: the decline has nothing to do with equality, it is about un-reduced calls. Remove that gate for its own (good) reasons -- WI-20260827-XBHX3 -- and `w` joins `wd` at 0 total. THAT IS THE COUPLING between the two tickets, and it is why XBHX3 cannot land first.

WHAT THE FIX IS NOT. Two obvious keys were prototyped and MEASURED, and each covers exactly half:
  * gate on `value_has_bodied_op_call(other)` (today's): catches `w`, MISSES `wd`.
  * gate on `value_reaches_eq_override(other)`: FIXES `wd` (0 total -> 1 total, 0 definite, a
    sound suspension), MISSES `w` -- because it reads the value's STRUCTURE and an un-reduced
    call hides the carrier: `C.mk(red())`'s head is `mk`, and `AE` appears nowhere in it.
Their union would cover both and would cost the answer XBHX3 measured the first gate costing (`box(v: Colour.tag(red()))`, a Box with no custom `Eq`, 1 conditional where the true `?c = red` is available as 1 DEFINITE). So the union is not free either.

DIRECTIONS, none chosen. (a) Key the decline on the case-split OPERATION'S RETURN TYPE reaching an eq override, which is the type the comparison is actually AT and which an un-reduced OTHER cannot hide -- narrowest of the three and the one I would try first. (b) Make the per-arm goal semantic where the carrier demands it, which collides with the unfold NEEDING to bind (`append(?a, [3]) = [1,3]` solves `?a = [1]`, and `eq` never binds -- so it would have to be a hybrid, unify to bind then `eq` to decide). (c) Decline the unfold entirely for a carrier with a declared `Eq`, which is (a) without the type read and gives up the relational cases over such carriers.

ACCEPTANCE: `wd` above answers 1 DEFINITE `?c = red`, or SUSPENDS -- either is sound, deciding FALSE is not -- with `g` asserted beside it as the control that says the answer exists; the fixture varies the field the declared `eq` ignores, and says at its site that a structurally-agreeing fixture would measure nothing; `w`'s soundness no longer depends on the `value_has_bodied_op_call` decline, so XBHX3 can proceed; the `box(v: Colour.tag(red()))` row (no custom `Eq`) is NOT collateral -- it must still be reachable as 1 DEFINITE by whatever key is chosen, or the cost is stated; `wi616_semantic_eq_test`'s five and `wi_vpewk_host_op_operand_test`'s `bodiedFirst` (1 DEFINITE) unmoved; full workspace green via rustland/scripts/test.sh.

REFERENCE: `unfold_eq_operand` / `builtin_unify` / `value_reaches_eq_override` / `REACHES_EQ_OVERRIDE` (rustland/anthill-core/src/kb/resolve.rs), docs/design/abstract-interpreter-and-rules.md 3.3, docs/kernel-language.md 8.3 (`=` dispatches, `<=>` binds). BLOCKS WI-20260827-XBHX3.

## Changes

### 2026-08-27T16:26:47Z — feedback — user

DELIVERED, AND THE KEY IS NONE OF (a)/(b)/(c) -- it is the ARM'S RESIDUAL, paired with the OTHER operand, and it took three /code-review rounds to get there. Direction (a) was tried first, as the ticket asked, and it LEFT THE DEFECT LIVE in two shapes.

WHAT LANDED: one decline inside `unfold_eq_operand`'s arm loop (rustland/anthill-core/src/kb/resolve.rs). The unfold declines when an arm's RESIDUAL reaches a carrier whose `eq` is not structural AND the OTHER operand reaches one too -- the SAME two predicates `sem_eq_values` consults before it will commit to a structural verdict: `value_reaches_eq_override` (a declared override) and `value_reaches_partial_carrier` (WI-664's unshielded `Float`). No new index, no new gate spec; the OTHER-side halves are hoisted above the loop and the override half is prefixed with `has_eq_dispatch_entries()`, mirroring `sem_eq_values` outcome 3.

WHY THE RESIDUAL AND NOT THE RETURN TYPE. Direction (a) was implemented and MEASURED, and it misses two shapes because a declared type has no children beyond its own bindings:
  `operation fpick(c: C) -> Wrap` where `entity wrap(v: AE)`   -> 0 total DECIDED FALSE
  `operation gopt[A](c: C, x: A) -> Option[T = A]` at A = AE   -> 0 total DECIDED FALSE
The first is the override one NOMINAL FIELD down; the second's return type is a bare parameter. It also DECLINED MORE than it had to, costing a correct answer (`cpick`, whose arm residuals ANF-hoist to bare vars and are already compared semantically). The residual is exactly what `unify` will compare, so nothing it will compare can be missing from it -- and reading structure is sound on THAT side, unlike on OTHER's, because `anf_flatten` has already hoisted every op-call out of it into its own semantic `eq` goal and `unify_values` delays on any un-reduced call it still meets.

THE OTHER HALF IS NOT CONSERVATISM. `unify` can only wrongly REFUTE where BOTH sides are concrete; against a flex operand it BINDS. A residual-only key took the GENERATOR shape from 2 DEFINITE to a suspension -- `C.pick(?c) = ?v` and `C.fpick(?c) = wrap(v: ?v)` -- and /code-review caught it.

THE FLOAT LEG FAILS THE OTHER WAY, and /code-review found it too. `unify` reads two `nan`s as equal (`OrderedFloat` is reflexive), IEEE `eq` does not, so
  rule nanrg(1) :- C.fnan(red()) = p(f: nan)   -> 0 total, correctly REFUTED
  rule nanr(?c) :- C.fnan(?c)    = p(f: nan)   -> 1 DEFINITE `?c = red`   WRONG
That is a PROOF of a false equation, not a dropped solution -- worse than the defect this ticket was filed for, in the same site and the same class.

MEASURED, four gate states, this site's decline against the neighbouring `value_has_bodied_op_call` gate (WI-20260827-XBHX3's subject):

                   nb ON            nb ON           nb OFF           nb OFF
                   this OFF         this ON         this ON          this OFF
                   (before)         (DELIVERED)     (after XBHX3)    (XBHX3 alone)
  wd               (0, 0) WRONG     (1, 0)          (1, 0)           (0, 0) WRONG
  wd0 wd0Naf       (0,0) (1,1) W    (1,0) (1,0)     (1,0) (1,0)      (0,0) (1,1) W
  bur              (0, 0) WRONG     (1, 0)          (1, 0)           (0, 0) WRONG
  fld              (0, 0) WRONG     (1, 0)          (1, 0)           (0, 0) WRONG
  nanr             (1, 1) WRONG     (1, 0)          (1, 0)           (1, 1) WRONG
  w                (1, 0)           (1, 0)          (0, 0) WRONG     (0, 0) WRONG
  bodyNest         (1, 0)           (1, 0)          (1, 1) ?c = red  (1, 1) ?c = red
  genp             (1, 1)           (1, 0)          (1, 0)           (1, 1)
  fok              (1, 1)           (1, 0)          (1, 0)           (1, 1)
  gen genw genb fgen  (2, 2) each   -- unmoved in all four
  cost costg g wg burg fldg plain tagr nanrg fokg  -- unmoved in all four

TWO COSTS, BOTH DRIVEN AND BOTH STATED AT THEIR TESTS. `genp` (`C.pick(?c) = ae(k: ?k, tag: 8)`) was 1 DEFINITE and is now a suspension -- and that answer set was 1 OF 2: `?c = green, ?k = 2` holds under `aeq` and the structural `unify` dropped it on `tag`, so the trade is a silently incomplete DEFINITE set for a suspension that omits nothing (both ground twins asserted). `fok` is the Float leg's carrier-level over-approximation: a Float compare where structural and IEEE happen to AGREE is declined too. That is the same over-approximation `sem_eq_values` already makes, taken deliberately so the two readers of one equation cannot disagree about which values need the semantic path.

THE ACCEPTANCE ITEM I DID NOT DELIVER, said plainly. "`w`'s soundness no longer depends on the `value_has_bodied_op_call` decline" is NOT met. `C.pick(?c) = C.mk(red())` is invisible to BOTH halves -- OTHER is an un-reduced `Expr::Apply` whose head is `mk`, and `AE` occurs nowhere in it until `unify_values` reduces it, long after this decision. A disjunct `|| value_has_bodied_op_call(&other)` WAS written here and REMOVED: the standalone gate shadows it completely, so the clause was unreachable and untestable, and /code-review proved it with an assert that never fired across the suite. An untestable branch whose first execution is someone else's diff is worse than an honest gap. WHAT XBHX3 OWES: when it removes that gate, add an "OTHER still carries an unevaluated computation" test to `other_can_meet_an_override`, covering HOST calls as well as bodied ones. The row that measures it is pinned at `the_masked_row_still_rests_on_its_neighbour` -- (1, 0) today, (0, 0) with the gate neutralized. The rest of XBHX3 is unblocked: `bodyNest` reaches 1 DEFINITE `?c = red` in the neutralized state, so this key does not take back the answer XBHX3 measured that gate costing.

TESTS: `wi_p1tpe_unfold_eq_semantic_test`, ten of them. Back-out DRIVEN by neutralizing both hoisted flags (NOT by editing the `if` -- `false && A || B` leaves the second leg live and silently measured only half the change, which is how the first back-out table came out wrong): `wd`/`wd0`/`wd0Naf`/`bur`/`fld`/`nanr` go red, and the six control tests stay green BY DESIGN and say so at their sites.

ALSO FILED FROM THIS WORK, each with an isolated driven fixture: WI-20260827-T2470 (a POSITIONAL constructor argument in an operation body builds a value that compares unequal to the same constructor written anywhere else -- equality-independent, refutes even the ground call, and the stdlib's own `Option.optionPure` is that spelling); WI-20260827-EJ5F5 (a bare nullary-entity name in a `case` pattern silently binds as a variable, so `pick(green())` returns the `red` arm's value); WI-20260827-APXSS (three spellings that slip past WI-1001's condition (2), reported by /code-review with repros).

Full workspace 5872 passed / 0 failed via rustland/scripts/test.sh; scaland 518/518 (the WI-580 unfold is not ported there, so no Scala change was needed).

