## Attributes

- id: WI-20260828-8Q0Q5-typer-an-arrow-typed-entity
- created: 2026-08-28T15:18:29Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T15:35:26Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

typer: an ARROW-typed ENTITY FIELD fed a bare operation name does not bind the arrow's EFFECT ROW, so the row leaks as an undeclared `?_` at the constructing operation. MINIMAL REPRO (no stdlib combinators, 8 lines): `sort C10 { effects R = ?; entity c10(f: (Int64) -> Int64 @ {R}); operation run(c: C10) -> Int64 effects R = match c case c10(f) -> f(1) }` with `operation probe() -> Int64 = C10.run(c10(inc))` reports 'undeclared effect ?_'. MEASURED DISCRIMINATORS, all in one probe: the SAME eta-lifted op into an OPERATION PARAMETER arrow slot with the same row param is CLEAN, so the defect is the FIELD path and not eta-lift itself; an inline `lambda x -> x + 1` in the same FIELD slot is CLEAN, so it is the bare-NAME reading and not the arrow; routing the construction through an op whose declared RETURN pins the row is CLEAN, which is the workaround in use. ROOT CAUSE, located: the constructor-argument hint push-down (typing.rs, the `Expr::Apply`/constructor arm that builds `pos_hints`/`named_hints`) looks `entity_field_types` up only when some argument is a CALL, a TUPLE, a SORT NAME or a CONSTRUCTOR APPLICATION (`has_call_field || has_tuple_field || has_sort_field || has_ctor_field`). A bare operation name is none of those, so no hint is computed, the argument is typed with NO expected type, and `check_bare_ref` has no arrow to eta-lift against — the op's declared row never meets the field's row parameter. The hint becomes the child's `expected` (`push_visit(work, arg, env, hint, fuel)`), which is exactly what makes the operation-parameter path work. FIX DIRECTION: a fifth hint kind beside the existing four — gated on the argument being a bare name of kind Operation AND the field type being callable by head (`type_head_is_callable`, immutable) — returning the declared field type. Pre-existing and INDEPENDENT of WI-590: the repro fixture uses only Int64/Function/EffectsRuntime. Surfaced while probing why `mapped(xs, inc)` in a free operation does not type-check; WI-590's own note misattributed it to the SOURCE access row, which D4/D5 refute (source field fully abstract + concrete arrow row is CLEAN; concrete source + abstract arrow row LEAKS).

## Changes

### 2026-08-28T15:35:33Z — feedback — user

DELIVERED. `arrow_slot_arg_hint` — the fifth constructor-argument hint kind, gated on the argument being a bare name of kind Operation AND the field being callable by head (`type_head_is_callable`), returning the declared field type so the name eta-lifts against the declared arrow and its row binds. Wired into both the positional and named hint chains, and `has_op_name_field` added to the `field_types` gate.

CONTROL MEASURED: with the gate neutralised (`|| (false && has_op_name_field)`), `entity_field_binds_the_ops_row` goes red with the ticket's own error and the other three rows stay green — they are the operation-parameter slot, the inline lambda, and the declared-return workaround, each changing exactly one thing and each already green, which is what makes the defect row an experiment about the FIELD path rather than about eta-lift or about arrows.

CONTAINMENT, argued and measured. Widening the gate means more builds compute `entity_field_types`, so the four older hints could in principle newly fire. They cannot: each one's first statement is a gate on the ARGUMENT's shape (a call, a sort name, a constructor application — `variant_field_expected_from_ctor` included), and a bare name is none of those. With the gate neutralised the only verdict that changes in the whole workspace is the defect row's.

TWO THINGS THIS DID NOT FIX, both filed rather than folded in. WI-20260828-2TMB5: a bare operation name against a NON-callable field loads clean, measured identically with this change and with it backed out. WI-20260828-BH1JZ: the stdlib shape `FiniteCollection.collect(mapped(xs, inc))` still fails, and the bare-name axis is NOT why — it fails with an inline lambda too; the cause is that an inline construction's sort params are grounded by nothing when the only consumer is a spec-op call.

Tests: rustland/scripts/test.sh green — 36 binaries, 5969 passed, 0 failures. scaland sbt test green — 544 passed, 0 failures.

