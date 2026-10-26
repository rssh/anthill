## Attributes

- id: WI-20261025-TSYS6-a-carrier-s-own-eq-and-a
- created: 2026-10-25T19:59:50Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-26T07:13:03Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CARRIER'S OWN `eq` AND A PROVISION'S BINDING OF IT ANSWER ONE CALL TWO WAYS — the own member is pinned at load and runs, the binding is left to the semantic-equality builtin, which answers reflexivity first and stops a circular `eq` at its re-entry cap. MEASURED on 56059e50 (the same on 5b7dc522, before WI-20261025-7K84M): `sort Loop { entity lp(v: Int64)  operation eq(x: Loop, y: Loop) -> Bool = false  provides PartialEq[T = Loop] }` answers `PartialEq.eq(lp(v: 1), lp(v: 1))` with 0 (the member ran); the same `false` written as `operation neverEq(x: Loop, y: Loop) -> Bool = false` beside `namespace Loop provides PartialEq[T = Loop, eq = neverEq] end` answers 1 (reflexivity, the binding never called). With the CIRCULAR body `eq(x, y) = PartialEq.eq(x, y)`: the own member runs until the global step budget, `evaluation exceeded the step budget of 100000000` after about 9 s, by name, through `=`, the dot, and a `requires PartialEq[T = T]` dictionary alike, and on a reflexive call too; the binding twin answers 1 on the reflexive call and is refused in 0.3 s on `lp(v: 1), lp(v: 2)` — `instance-fact eq over loopEq could not be decided` (the bridge's re-entry cap, wi625_eval_semantic_eq_test::eval_undecidable_instance_fact_eq_is_loud_not_false). MECHANISM, as read: `resolve_at_goal` answers semantic equality by the provider's table row (WI-20261025-7K84M kept that, its equality clause), and the row is the carrier's own member where it has one — so the call is pinned to the member (`classify_pin_or_apply_within`) and never reaches `sem_eq_core`'s cascade (Float pair, reflexivity, the equality index's dispatch, buried override, structure); a binding is no table row, so the call stays `PartialEq.eq` and the builtin answers. §8.7's rule that a written implementation answers whichever route writes it does not hold for equality. QUESTION FOR THE USER FIRST: which answer is the language's — §8.3's 'structurally identical operands are equal by reflexivity' for every carrier (then a carrier's own `eq` is not called on identical operands, as the binding is not, and a circular own `eq` meets the bridge's cap), or 'the carrier's own `eq` is called' (then the binding is too, and reflexivity is `Eq`'s law `eq_refl`, not `PartialEq`'s — §8.3 also says `PartialEq` has no reflexivity law, and `Float`'s `nan = nan` is false by a special case in the cascade). WHAT, after the answer: one answer for both texts at every route (by name, `=`, the dot, a dictionary, a rule body), and a circular `eq` refused as the binding's is, by its own message. ACCEPTANCE: rows for the four programs above and their dictionary spelling, each with the answer the user gives, both texts alike; the full gate green.

## Changes

### 2026-10-25T23:06:46Z — feedback — user

Decided by the user (2026-10-25): the type's own `eq` decides `=`, written as its member or as a provision's binding alike, and is called on identical operands too — reflexivity is `Eq`'s law (`eq_refl`), not `PartialEq`'s. A type that provides `Eq` keeps the reflexivity answer for identical operands (licensed by `eq_refl`; how identical `Set`s are decided today). So for a `PartialEq`-only `Loop`: `eq = false` answers 0 on `PartialEq.eq(lp(v: 1), lp(v: 1))` for both texts, and a circular `eq` is refused the same way for both, by the bridge's 'could not be decided'. Every stdlib type with an own `eq` (Set, Map, Pair, SortedSet, TotalFloat) also provides `Eq`, so no stdlib answer is meant to move.

### 2026-10-26T07:13:02Z — feedback — claude

Delivered (93e6ad2c). Routes kept (the user's choice after the measurement: routing the member through the builtin's bridge cost about 90x per call, 1.9 vs 173 us debug): the member is pinned and runs, the binding goes through the builtin; the builtin's reflexivity step and the WI-664 field-wise compare stand aside for an operand headed by a type with its own eq and no Eq (eq_dispatch_is_partial, both halves); an open such operand is refused as undecided in eval. Answers for the four programs: eq = false 0 as member and as binding; circular binding refused at the cap on identical operands too; circular member still runs to the step budget (the routes' difference, pinned by a row). NOT COVERED: such a type buried in one with no eq of its own (some(lp(v: 1)) against itself) keeps reflexivity at the top — WI-625's documented buried-override gap. Gate 10890 passed, 0 failed; rows wi_tsys6_own_eq_decides_test (8); kernel-language §8.3 reworded (approved). Also noted on WI-20261020-NNQ1S: a type with its own eq and no provision now has that eq decide identical operands (1 -> 0).

