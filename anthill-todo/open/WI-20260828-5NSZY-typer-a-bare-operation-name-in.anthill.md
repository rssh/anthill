## Attributes

- id: WI-20260828-5NSZY-typer-a-bare-operation-name-in
- created: 2026-08-28T22:12:39Z

- status: Open
- status_agent: user
- status_at: 2026-08-28T22:12:39Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

typer: a BARE OPERATION NAME in a POLYMORPHIC slot cannot reach the arrow that would let it lift, so it is REFUSED where it could be accepted. MEASURED: `operation apply_it(o: Option[T = Function[A = Int64, B = Int64]], v: Int64)` fed `apply_it(some(inc), 41)` is a load error at the reference — `some(value: T)` is not callable by head, so no constructor-argument hint is computed, the name reaches `check_bare_ref` with `expected = None`, and WI-20260828-2TMB5 refuses a lift with no arrow to lift against. THE REFUSAL IS CORRECT AS IT STANDS and must not simply be relaxed: with no arrow, `attach_eta_dispatch_dict` pins neither the requirement dictionary nor the argument-spread labels, and the first cut of 2TMB5 — which lifted anyway against the operation's own arrow — made `via_option(some(sub2))` return -7 where its arrow-slot twin returned 7. The fix is to make the ARROW REACH THE REFERENCE, not to lift without one. WHERE TO LOOK, and what has already been REFUTED: `ctor_field_expected` (typing.rs) already walks a declared field type through the constructor's own `expected`, and a hint built on it (gated `type_head_is_callable` on the WALKED type, the exact peer of `variant_field_expected_from_ctor`) was written and MEASURED NOT TO FIRE — because the constructor itself has `expected = None`. The chain breaks ONE LEVEL UP: `one_arg_hint` pushes an operation's declared parameter type into a CONSTRUCTOR-APPLICATION argument only when `variant_slot_arg_hint` accepts it, i.e. when the parameter type names an ENTITY; `Option[T = ...]` / `List[T = ...]` name a SORT, so nothing is pushed. A second probe that pushed the parameter type down whenever the constructor argument carried a bare operation name ALSO did not suffice on its own. So this needs BOTH halves: the param type reaching the constructor, and the walk from there to the field. CONTAINMENT IS THE RISK, not the mechanism — pushing an expected type into constructor arguments that took none changes the WI-20260826-JSFHG classification decision (`expected_names_an_entity`) and the expected-seed for every such build, so it needs its own census of what newly receives a hint. ACCEPTANCE: `apply_it(some(inc), 41)` evaluates to 42, DRIVEN; a 2-parameter operation through the same polymorphic slot spreads BY LABEL (the `via_option(some(sub2))` / `direct(sub2)` pair in wi_2tmb5_bare_op_name_zero_arg_reading_test must BOTH return 7); a `requires`-carrying operation through that slot mints a dictionary rather than dying in a foreign apply frame; and every row of wi_2tmb5_bare_op_name_zero_arg_reading_test that is about a NON-callable slot stays refused.

