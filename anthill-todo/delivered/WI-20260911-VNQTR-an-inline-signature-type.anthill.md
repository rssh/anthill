## Attributes

- id: WI-20260911-VNQTR-an-inline-signature-type
- created: 2026-09-11T06:26:50Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-20T14:15:53Z

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

### 2026-10-20T13:51:28Z — feedback — claude

RESCOPED AND DELIVERED 2026-10-20 on 15a12b17, uncommitted (user: "lets look on … a type-argument channel is removed", then "fix inline").

RE-MEASURED FIRST. The description's acceptance holds in the present language (`viaInline(b: List[T = ?t]) -> Type requires TypeValue[T = ?t] = tyOf(b)` answers `Cell(V: List(T: Int64))`, as `viaBracket[U]` does), and the 2026-10-15 note's nested bracketed shape has been refused since 9WVT7's review fixes (d4f93591, b437fdbb). What was left is the ticket's own thesis one layer down: an inline signature variable is the same parameter as a bracket's (§5.4, WI-1FKR2), and the operation's RECORD listed only the brackets and the member-sugar parameters, so every reader of "the operation's own type parameters" gave the two spellings of one signature two verdicts.

THE RECORD (load.rs `mint_inline_type_params`; `KnowledgeBase::minted_param`, one registry for the member sugar's names, the inline variables and an unwritten slot's unknown). A variable written in a parameter type is minted before the signature is converted, under a name of its own that reads as written, and listed on the record after the member parameters; a call's bracket cannot bind it (`op_info::bracket_type_params`), and the bracket refusal says so. Moved to the bracket's verdict: the forward refusal (§5.2) names `?t` and prints `requires TypeValue[T = ?t]`; arguments binding one variable are joined; an override's variable is bound at a dispatched call; a lambda is typed through a sibling binding its variable; a handler's inline row tail takes the body's residue; a list literal at an inline variable is one type; an unconstrained inline variable is refused advising no bracket; a provider widening a spec operation's inline row is refused; a body `?t` read as a value is read through its `TypeValue` slot; a member restates the spec operation's clause over its variable; the diagnostics print `?t`; the C++ generator makes `?U` a template parameter of the operation's own beside a bracket `[U]` or the sort's `T`, named apart from a value parameter.

MEMBER PAIRING (signature.rs `paired_type_params`). A member's declared parameters are the spec operation's by position where the two declare as many; a variable written in a parameter type by where it stands in the two signatures, read as types (an application's arguments by key). Paired by position across the record, a strengthening `requires` read as a restatement and the member answered at another parameter's type; and two sides writing different numbers of variables paired nothing, so providers that ran were refused (both found by the round-2 review). Restatements in another spelling now load. Restating requirements in another ORDER stays refused, the decided rule `spec_op_requirement_at_member_test` pins.

FOUND ON THE WAY AND FIXED (user: "fix inline"):
 * TRANSITIVE COVER (dep_projection.rs Strategy 2c, behind the construction a provision answers): a caller's clause covers a forward through its chain to any depth; `scope_chain_cover` reads a node met before only once where its sort is on no cycle (a diamond lattice cost +77% of a load).
 * TWO SLOT PATHS ARE TWO TYPES (carrier.rs `dispatch_values_match`): a requirement at `xs.T` covered a call at `ys.T` — wrong values at depth 0-1 before this ticket, at any depth through 2c.
 * UNWRITTEN SLOT FORWARD (dict.rs `caller_part`, `binding_is_pinned`): a slot at the top of a parameter's type — written `?`, left out, or left open by an alias (read in the body by its path) — is named by its path (`xs.T`) wherever it stands in what a call passes, and `requires TypeValue[T = xs.T]` repairs it; a nested slot (`Box.V`) is refused advising a variable for it; a spec part keeps its "no TypeValue whatever the caller supplies" verdict.
 * FUNCTION VALUES (eta.rs): an operation used as a value parks a forward of the caller's parameter and a carrier no provision answers at; an element still open at the reference that its parameters carry is read where the value is applied (the review measured programs that ran refused otherwise), and one only the result names is pinned by the expected arrow's result.
 * CONSTRUCTION FIELD HINT (arg_hints.rs, visit.rs): a lambda or an operation name in a construction's field is typed at the instance the construction states, by position as by name.
 * A PROVIDER MEMBER'S FORWARD is advised on the spec operation it backs and restated on the member (a slot: a variable on both).
 * `@[simp]` (node_occurrence.rs `TYPE_VALUE_READ_PASS`): a type parameter's read a rewrite moves into a type position denotes the parameter there, a bracket's `K` and a signature's `?k` alike.

ROWS: wi_vnqtr_inline_param_forward_test, wi_vnqtr_inline_family_record_test, wi_vnqtr_transitive_cover_test, wi_vnqtr_unwritten_slot_forward_test, wi_vnqtr_function_value_forward_test, wi_vnqtr_member_pairing_test, wi_vnqtr_projection_paths_test, wi_vnqtr_simp_type_param_read_test; anthill-cpp-gen generic_sort_test `an_inline_variable_is_a_template_parameter_of_its_own`. Every mechanism's back-out measured over the whole wi_tests binary (7552 rows, green without a switch), each turning red only its own rows (counts in each file's header). Full workspace 10189 passed / 0 failed / 17 ignored; families unmoved, and unmoved under the node carrier; anthill-core under the node carrier 9164 passed / 0 failed / 9 ignored.

LEFT FOR THE USER (pre-existing unless said): a self-recursive call that swaps the operation's own type parameters is answered by the caller's clause through the swap (wrong value, both spellings); a construction mixing a positional and a named argument types the positional by slot; a function value in a construction passed straight to a call gets no instance from the call (`apply(h(f: lambda…))`); construction-site refusals do not use the forward refusal's account; the deep cover is not read for a rule body's `require[…]` (068); an alias's tie is not joined at a call; the SMT generator keys a parameter's sort by its name (not driven); spec text for the record, the member pairing and the slot verdicts awaits sign-off.

