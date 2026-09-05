## Attributes

- id: WI-20260904-34J8Z-a-binder-list-lambda-s-arrow
- created: 2026-09-04T21:44:06Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T21:44:06Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a binder-list lambda's arrow param is a variable where its arity says named_tuple

FOUND BY /code-review ON WI-20260904-50B2K's `?pat` SPLIT, as two findings that turn out
to be one repair. Neither is a regression — both shapes behave identically on the tree
before that change — and the assert half is fixed there; this is the part that is not a
one-line edit.

THE DISAGREEMENT. A lambda's arrow is built with `arity` = the WRITTEN binder count
(`lambda_written_arity`) and `param` = whatever the three-rung type ladder supplied. At
rung 3 that is a VARIABLE, so an un-annotated `lambda (a, b) -> …` mints
`arrow(param: ?param, arity: 2)`. `arrow_positional_param_slots` reads arity 2 as "the
param IS the parameter list, a `named_tuple` of exactly 2 fields" and finds a variable.

    let g = lambda (a, b) -> a  g((a: 1, b: 2))

aborted a debug build on that assert, and — the control that says the MINT is not what
decides it — the ANNOTATED twin `lambda (a: Int64, b: Int64)` aborted identically, since
per-binder annotations are read one level down and the arrow's param is a variable either
way. In release the assert is absent and the same shape silently returns `None`, standing
the whole argument check down.

FIXED THERE, NARROWLY: the assert now excepts an UNDETERMINED param
(`arrow_param_is_undetermined` — `TypeVar` or `FlexVar`, deliberately not `Skolem`), and
`None` is read as the withholding the rest of the file gives for an undetermined type
rather than as a malformed term. Both programs now load and answer 1, pinned by
`wi_50b2k_binder_inference_test::a_direct_application_of_a_multi_binder_lambda_no_longer_aborts_the_typer`
(back-out: drop the disjunct, and that one row of 4126 fails).

WHAT IS LEFT, AND IT IS THE SAME REPAIR TWICE.

  (1) THE PARAMETER LIST IS NEVER LEARNED. The withholding is correct but permanent: no
      later evidence turns `?param` into a `named_tuple`, so a direct application of a
      multi-binder lambda is never slot-checked at all.

  (2) A TUPLE BINDER'S COMPONENTS ARE INDEPENDENT VARIABLES. 50B2K's `?pat` split mints
      one fresh variable per component with NOTHING tying it to the parent's, so unifying
      the parent at a use site (`?p := (a: Int64, b: Int64)`) does not solve `?a` / `?b`.
      Inference therefore reaches a tuple binder only through its own BODY. Recorded at
      the tuple arm of `bind_and_label_pattern`.

BOTH ARE ANSWERED BY MINTING THE PARAM AS A `named_tuple` OVER THE COMPONENT VARIABLES —
`arity` and `param` then agree by construction, and ONE unification at a use site solves
every component at once.

BUILT AND MEASURED 2026-09-04 — TWO OBSTACLES, AND NEITHER IS THE ONE THIS TICKET FIRST
GUESSED. The first draft argued the blocker was the LABELS (a `named_tuple` needs field
names, and WI-803 takes them from the expected type while 50B2K's own text refuses the
binder names). So the mint was written with WI-790's `_1.._n` positional labels and the
whole binary run: **4124 passed, 2 FAILED**, and the labels were not what broke either of
them. The attempt is reverted; the two failures are what this ticket is now about.

  (1) A SYNTHESIZED CONTEXT SILENTLY DISPLACES THE USER'S ANNOTATIONS.
      `wi517_typed_lambda_binder_test::typed_tuple_binders_pin_elements_without_expected_context`
      — `let f = lambda (a: A, b: B) -> add(a, b)` — failed with "expected `requires
      Additive[…]` covering abstract type parameter". WI-517's rule is that the CONTEXT
      type beats the binder's own annotation, and its justification is that a context is
      what the value ACTUALLY IS. A minted tuple is not that: it is a hole wearing a
      context's clothes, so `bind_and_label_pattern`'s Var arm hands each binder a fresh
      `_i` variable and DISCARDS the written `: A` / `: B`. One name, two questions — the
      defect class this repo names most often, and it is the real blocker.
      Telling a SYNTHESIZED context from a DECLARED one at that arm is prerequisite work.

  (2) THE ARITY READING FLIPS THE APPLICATION INTO AN ARITY ERROR.
      `let g = lambda (a, b) -> a  g((a: 1, b: 2))` became "type mismatch in g.arity
      (op-arg): expected 2 arguments — the parameter list this function value declares,
      got 1 argument". Once the param IS a real two-field list, the call that passes ONE
      tuple is read as one argument against two slots. That runs straight into WI-775's
      settled rule that `f(3, 10)` and `f((3, 10))` are BOTH legal at a `Function` slot,
      so the fix must say which reading a MINTED list gets — a question the declared case
      never had to answer, because a declaration says which one the author meant.

THE LABELS ARE STILL A QUESTION, just not the blocking one: tuple LABELS ARE IDENTITY
(`docs/kernel-language.md` §4.5), so whether `(_1: ?v, _2: ?w)` may meet `(a: Int64,
b: Int64)` has to be decided. The measurement above says it is decided AFTER the two
above, not before.

DRIVEN AND ASSERTED AT ITS WRONG VALUE, so this ticket has an acceptance rather than a
description: `let g = lambda (a, b) -> a  g((b: 2, a: 1))` answers **2**, where every
other spelling of the same program answers 1. The permuted argument binds BY SLOT because
`bind_and_label_pattern` has no labels to bind by — kernel-language.md §6.7's documented
fallback, reached here because nothing declares this lambda's parameter type. That row
lives in
`wi_50b2k_binder_inference_test::a_direct_application_of_a_multi_binder_lambda_no_longer_aborts_the_typer`
as its third arm; FLIPPING IT TO 1 IS THIS TICKET'S ACCEPTANCE.

CONTROLS THIS OWES, all green today and all must stay green:
  * `wi_50b2k_binder_inference_test::part_b_a_permuted_named_tuple_binds_a_rule_body_lambdas_binders_by_name`
    — a permuted tuple bound BY NAME when a declaration IS present (answers -1). The
    invented labels must not displace a declared one; rung 2 must keep beating rung 3.
  * `arity_mismatch_still_refuses_to_match` — `lambda (p, q)` against a 3-component tuple
    must LOAD clean and fail at the MATCH. A by-label read that ignores the extra
    component would turn a loud arity failure into an accepted program.
  * `wi_50b2k_binder_inference_test::the_tuple_binders_operation_body_twin_drives_and_is_unmoved`
    and `pat_a_tuple_binders_component_is_inferred_when_the_parent_type_is_a_hole`.
