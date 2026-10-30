## Attributes

- id: WI-20261030-H3PC8-a-hypothesis-holding-a-closure
- created: 2026-10-30T16:58:53Z

- status: Open
- status_agent: claude
- status_at: 2026-10-30T16:58:53Z

- acceptance: cargo-test

- tags: resolver

## Description

A HYPOTHESIS HOLDING A CLOSURE PANICS THE PROCESS — the one-pattern matcher puts the hypothesis in a discrimination tree, which refuses a closure. Filed by the user's decision, 2026-10-30, found delivering WI-20261030-BXMPK.

MEASURED (cf906e65, and the same on 9f69fd45 before BXMPK): over `operation pureThunk() -> () -> String = lambda () -> "x"`, `rule hyp(?x, ?f) :- eq(1, 2)`, `rule direct(?f) :- (forall(?x), hyp(?x, ?f) -: hyp(?x, ?g))`, the query `viaDirect(?r)` over `rule viaDirect(1) :- pureThunk(?f), direct(?f)` panics: "discrim insert: opaque head carries no discrimination key — value-fact keying is unimplemented (WI-348 Phase B/C)" (kb/discrim.rs `insert_walk`). The same through `ho_apply`: `rule holdsFor(?p, ?f) :- (forall(?x), ?p(?x, ?f) -: hyp(?x, ?g))` with `pureThunk(?f), holdsFor(hyp, ?f)`. The twin handed a lambda occurrence (`direct(lambda () -> "x")`) answers 1, and so does one handed a number.

THE MECHANISM (READ): `KnowledgeBase::match_view_value_pattern` (kb/mod.rs) matches ONE pattern against a target by building a one-pattern `SubstTree` and inserting the pattern; the insert panics on a `ViewHead::Opaque` stored head, a guard written for the KB's own index, where no fact holds a closure. Its callers, each handing it a pattern that can now hold one: the frame's `forall` hypotheses (`hypothesis_candidates`, kb/resolve.rs — the measured site); an extent row matched with the GOAL as the pattern (`pump_extent_row`) — a goal carries a closure since WI-20261023-W2JP7 and WI-20261030-BXMPK, not measured with a mounted extent; and an occurrence pattern (`match_occ_pattern`, the reflect `occurrence_term` path).

THE CHANGE: a one-pattern match reads both sides through the view and unifies them, so a closure in the pattern binds a variable at that position or meets the target's value there, and no index is built for one pattern. What a closure equals is `Value::opaque_carrier_eq`'s answer (false, even against itself) and is not this ticket's to change. The resolution semantics the tree gives today (a goal's flex variable binds to the pattern's structure, `unify_rebind = false`) are kept or the difference is stated and measured.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): `viaDirect` and the `ho_apply` twin answer 1, definite, with no panic, each failing with the tree put back; a row for the extent path if a program reaches it, else the measurement at the site; the lambda and number twins as controls.

