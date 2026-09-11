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

