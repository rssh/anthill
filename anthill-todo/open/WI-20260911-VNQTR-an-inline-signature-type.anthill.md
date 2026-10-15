## Attributes

- id: WI-20260911-VNQTR-an-inline-signature-type
- created: 2026-09-11T06:26:50Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T06:26:50Z

- acceptance: cargo-test

- tags: effects

## Description

AN INLINE SIGNATURE TYPE VARIABLE DOES NOT RIDE THE TYPE-ARGUMENT CHANNEL, so a callee's
type argument resolved to one arrives at run time as a dangling skolem — the WI-708
regression shape, reached through the one type-parameter family the channel does not carry.

WI-1FKR2 SAYS THE TWO FAMILIES ARE THE SAME THING. An inline `?t` written in a signature
(`via(b: Box[?t]) -> Box[?t]`) is quantified by §5.4 exactly as a declared `[A]` binder is,
and `check_operation_bodies` treats them as one list: `op_own_params = rec.type_params.clone();
op_own_params.extend(inline_type_params)` (typing.rs), both skolemized together into
`param_rigids[sort_rigid_len..]`.

THE CHANNEL CARRIES ONLY HALF OF IT, and the join is a local variable:
 * `set_resolved_type_args` is gated on the CALLEE's `op.type_params` — the declared
   brackets. An operation whose only type parameter is an inline `?t` has an EMPTY
   `type_params`, so the write is skipped entirely and it gets no channel as a callee.
 * `op_own_params` is LOCAL to `check_operation_bodies` and never stored back on the
   record, so nothing downstream can recover the inline half.
 * Consequently a CALLER whose only type parameter is inline has an empty frame channel,
   and `collect_closed_type_args` returns at its `caller.type_args.is_empty()` guard.

WHY `op_own_param_ref_rewrite` CANNOT SIMPLY BE EXTENDED. That rewrite (landed with the
channel closure) turns a skolem standing for the enclosing operation's own parameter into
the `Ref(<op-scoped symbol>)` a body reference carries, so eval can ground it by symbol
identity. Doing that for an inline `?t` would mint a reference NOTHING BINDS — the caller's
channel has no entry for it — which is strictly worse than leaving the skolem: a dangling
`Var(Rigid ?t)` is visibly wrong, a `Ref(?t)` reads as a nominal sort. That is the same
"confidently wrong beats visibly wrong" hazard /code-review drove against the first shape
of the channel join, and it is why this is filed rather than patched in place.

MEASURED: `operation viaInline(b: List[T = ?t]) -> Type = tyOf(b)` loads clean beside its
bracketed twin `operation viaBracket[U](b: List[T = U]) -> Type = tyOf(b)`, over
`operation tyOf[T](x: T) -> Type = Cell[V = T]`.

WHAT CLOSING IT NEEDS: the inline family reaching the channel at all — either
`OperationInfo` carrying it so `set_resolved_type_args` can write entries for it, or the
write site recomputing `inline_signature_type_params` the way `check_operation_bodies`
does. Then `op_own_param_ref_rewrite` extends to it for free.

ACCEPTANCE: `viaInline`, called with a concrete list, grounds `tyOf`'s `T` — the body read
`Cell[V = T]` answers `Cell[V = Int64]`, not `Cell[V = Var(Rigid ?t)]` — with the bracketed
`viaBracket[U]` row as the control that already passes (it is `wi708_body_type_arg_read_test`'s
`a_type_argument_passed_through_a_generic_caller_is_ground`).

## Changes

### 2026-10-15T15:17:01Z — feedback — claude

RE-MEASURED 2026-10-15 on ee3696eb: the channel this ticket describes is gone. WI-20260921-28TAT removed `Frame.type_args`, `set_resolved_type_args` and `op_own_param_ref_rewrite`; a type parameter's run-time value is now read through a `TypeValue` requirement (proposal 065). In today's language the program is

  operation tyOf[T](x: T) -> Type requires TypeValue[T = T] = Cell[V = T]
  operation viaInline(b: List[T = ?t]) -> Type requires TypeValue[T = ?t] = tyOf(b)

and `viaInline(cons(1, nil))` answers `Cell(V: List(T: Int64))`, as the bracketed `viaBracket[U]` does. With the clause written, the inline family carries the requirement like a bracket, so the acceptance as written holds.

WHAT IS LEFT IS A DIFFERENT GAP, and the inline family is only half of it. The refusal of forwarding a rigid into an operation that reads it (kernel-language.md, 065: `mid[U](y: U) = tyOf(y)` is refused at the call, naming the clause to add) misses two shapes. Both load and then fail at run time with `DeferToRequirement: requirement param __req_typevalue not bound in caller frame`, a panic through the rule-body bridge in a debug build:
 * an inline rigid: `midInline(y: ?t) -> Type = tyOf(y)`;
 * a rigid nested in a type argument: `midNested[U](y: List[T = U]) -> Type = tyOf(y)`, where the derived `TypeValue` for `List[T = U]` is conditioned on `TypeValue[T = U]`, which the caller does not hold. The same with an inline `?t` in place of `U` loads too.
`mid[U](y: U) -> Type = tyOf(y)` is refused at load, as the spec says.

PROPOSED, not done: rescope this ticket to that refusal, with the acceptance that both shapes are refused at load naming the clause to add, and that each, with the clause written, answers at run time.

### 2026-10-15T17:18:54Z — feedback — claude

CORRECTION to the entry above (2026-10-15, found by the /code-review sweep): the run-time failure it describes is not caused by the missing refusal.

Through an anthill caller the unrefused shapes return the right Type: `midX(y: ?t) -> Type = tyOf(y)` gives `midX(5) === tyOf(5)` true (the control against `tyOf("s")` false), and `midX[U](y: List[T = U])` behaves the same, behind a generic caller too. The panic was measured through a rule body (`rule rc(?r) :- c(?r)`), and through a rule body even the clause-written twins and the spec's own repair, `mid[U](y: U) requires TypeValue[T = U] = tyOf(y)`, panic "frame binds []", while `let r = tyOf(y)` then `r` answers. That is WI-20261012-EZJXH's mechanism, a whole-body call reached from a rule body, here with the type fixed by an argument rather than a bracket.

What stands: the load-time refusal of a forward misses the inline shape and the nested one. The proposed acceptance's "answers at run time" holds through an anthill caller; through a rule body it waits on EZJXH.

