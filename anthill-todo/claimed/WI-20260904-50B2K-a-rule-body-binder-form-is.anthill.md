## Attributes

- id: WI-20260904-50B2K-a-rule-body-binder-form-is
- created: 2026-09-04T09:31:41Z

- status: Claimed
- status_agent: claude
- status_at: 2026-09-04T12:17:52Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN UN-ANNOTATED LAMBDA BINDER IS GIVEN THE FORM THAT MEANS "I COULD NOT NAME THIS TYPE",
when the question it asks is "this type is TO BE INFERRED". The two want opposite
behaviour — the first must not commit, the second must — and they share one
representation.

DECIDED 2026-09-04 (user): an un-annotated binder HAS a type of its own, to be inferred.
It is not merely whatever an expectation hands it. "It should be inferred; if it can't be
inferred it's polytype." That rule has two halves and both are work below: (b) infers it
where the information exists, (c) generalizes what is genuinely unconstrained.

MEASURED on the WI-20260903-FC2X4 tree, with
`operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)` in scope:

  rule value(?r) :- ?r <=> apply1(lambda x -> x + 1, 2)
    -> ambiguous dispatch of `anthill.prelude.Additive.add`: 3 instances provide
       `anthill.prelude.Additive` … and the call selects none

WHERE THE TYPE COMES FROM. `type_check_node`'s lambda arm has a three-rung priority
ladder for the binder type (`kb/typing.rs`, the `param_type` let):

  1. the ANNOTATION — `lambda (x: T)`, WI-517's `typed_binder`
  2. `expected`'s arrow param slot — commented "Checking direction: the expected
     arrow's param slot, as-is"
  3. FALLBACK — `kb.make_type_var(kb.intern("?param"))`

Rung 2 is `None` in a rule body (the enclosing `apply1(…)` is a
`CallDispatch::DataTerm`, which WI-1058 deliberately does not type-check). So rung 3
fires.

RUNG 3'S FORM IS DELIBERATE, DOCUMENTED, AND RIGHT FOR WHAT IT WAS BUILT FOR — do not
"fix" `type_var` itself. `KnowledgeBase::make_type_var`'s doc states the design:
`type_var` "carries a name and NO identity, where a variable carries an `id` that is its
identity. Three forms, three questions." It is INERT on purpose —
"compatible-with-anything in the unify/subtype dispatch WITHOUT committing (the M6
flounder posture)", "so an imprecise type never wrong-FIRES a guard" — and the
hash-consing is argued there too ("~7 literals … nominal identity"), against a
`Var::Global` that "would carry a distinct `VarId` per site". WI-963 drives all three
facts as tests and records that the question "was asked twice about this code" (this is
the third time; the answer keeps not covering the case below).

TYPE PARAMETERS ARE ALREADY VARIABLES, and that is not in tension: a parameter is a
`Var::Rigid` extracting as `Skolem` ("a parameter rigidified for the duration of a body
check", WI-392 / WI-1059). `TypeVar` is NOT a type parameter — WI-963's row calls it "a
type the extractor could not name, minted for an un-annotated lambda binder, while a
logic variable is the ENGINE's".

`TypeVar` AND `FlexVar` ARE NOT TWO FLAVOURS OF VARIABLE — they are not the same KIND of
thing, and `kb/load.rs`'s TypeExtractor pre-registration block states the rule:
"`SortRef` / `Parameterized` / `Error` are COMPUTED-ONLY … never built by the engine …
only the `extract` builtin mints them, post-load".

    ENGINE-BUILT (pre-registered; used as STORED term functors):
      Arrow, TypeVar, NamedTuple, Nothing, Denoted, ExprCarried, PolyType, EffectsRows
    COMPUTED-ONLY (`extract` mints post-load; no term of their own):
      SortRef, Parameterized, Error, FlexVar, Skolem

`FlexVar` / `Skolem` appear NOWHERE in `load.rs` — verified. They are VIEWS: the thing
itself is `Term::Var(Var::Global(id))` / `Term::Var(Var::Rigid(id))`, which `extract`
renders (WI-1079; before it, both reported `Error`). `TypeVar` is a STORED TYPE FORM,
sibling to `Arrow` and `Denoted`. So this ticket's defect, said in that vocabulary: a
lambda binder is on a stored structural form when it belongs on an actual variable.

THE REMOVAL CRITERION, for whoever asks "then delete `TypeVar`". If the engine stops
building it, it does NOT fall back to computed-only — `extract` already covers variables
via `FlexVar` / `Skolem` — it becomes DEAD VOCABULARY and is removable. What holds it is
ONE site: the requirement-supply path at `typing.rs:23328` feeds a derived value type
into `unify_types` against a declared param type, where compatible-with-anything leaves
the slot UNDER-DETERMINED instead of binding wrongly (WI-20260830-NX4FD's "a recorded
absence"). The other two runtime readers convert to `None` via `sort_functor_of_view`
before any comparison, so for them it is a totality SENTINEL an `Option` would say
better. Removal is not this ticket; the criterion is recorded so it is not re-derived.

THE DEFECT IS THE PAIRING, NOT THE FORM. WI-963's justification is the M6 flounder
posture — do not commit when you genuinely do not know — and it is attached to
`fresh_type_var`, the `?_` site. It was applied to every site. An un-annotated lambda
binder is not a type nobody could name; it is a type to be inferred, and inference is
precisely what must commit.

THE CENSUS — eleven `make_type_var` call sites, split by the question each name says it
asks. BY NAME, WHICH IS A HYPOTHESIS AND NOT A MEASUREMENT: redo it site by site.

    "no type available AT RUN TIME" — keep inert, this is `type_var`'s real owner:
      ?_            typing.rs 59725, 59731, `fresh_type_var` 59923
                    ALL EIGHT `fresh_type_var` call sites are inside `value_type_term`'s
                    region (`seq_literal_value_type`, `var_type_term`,
                    `child_types_pos`/`_named`, `value_type_term`, `value_type_term_d`)
                    — WI-578, the CARRIED TYPE OF A RUNTIME VALUE. Proposal 060's staging
                    invariant is that run time "performs no typing operations" and only
                    reads that carried type, so an under-determined one MUST NOT commit:
                    a flex var here would bind during a runtime comparison and commit to
                    what typing never decided. That is what the M6 flounder posture
                    protects, and it is why `type_var` does not go away.
      ?ungrounded   typing.rs 3398   ("a typer bug here … so we don't panic in release")
                    NEITHER COLUMN, really — a defensive path. By this repo's "prefer a
                    loud error over a silent skip" it wants a DIAGNOSTIC, not an inert
                    type. Its own question; not this ticket's.

    "to be inferred" — must commit:
      ?param        RUNG 3 — DONE (this ticket)
      ?pat          `scrutinee_type.or_else(annotation).unwrap_or_else(…)` — the SAME
                    three-rung ladder as rung 3, one level down (a sub-pattern of a
                    tuple-destructuring binder). The direct sibling; take it first.
      ?T  x2        an EMPTY list/set literal's element type (`element_type` is `None`
                    because there are no elements). The consumer pins it —
                    `let xs: List[T = Int64] = []`.
      ?logical_var  a free `?x` with no binding — "declared signatures resolve it on the
                    consumer side" (its own doc). Genuine, and the LARGEST blast radius:
                    every rule body. Take it last.

    RE-CENSUSED SITE BY SITE 2026-09-04, and ONE ROW MOVED COLUMNS — which is why the
    ticket said the by-name list was a hypothesis:
      ?result       NOT an inference hole. It fires only when the lambda BODY RESULT IS
                    AN `Err` — error recovery, with a diagnostic already being reported.
                    An inert value is right there: it stops the failure cascading into a
                    second, derived complaint. Belongs beside `?ungrounded`.

MEASURED 2026-09-04 BY DOING (a) — `type_var` HAS A THIRD JOB, AND IT IS GROUNDNESS.
Rung 3 was flipped to `Term::Var(Var::Global(fresh))` and the whole suite run against a
6403/0 baseline. Result: 6398 passed, 8 FAILED. The eight split in two OPPOSITE
directions, and the second is the finding:

  GROUP A — NEVER SOLVED (5 rows). The variable reaches a conformance check unbound:
  "expected Int64, got ??param".
    eval_test::m2_lambda_identity
    eval_test::m2_closure_arena_reclaims_on_drop
    typing_test::type_check_op_lambda_let_inferred        `let g = lambda q -> q  g(x)`
    wi620_paren_lambda_param_test::paren_binders_bind_and_apply
    parse_test::wi342_env_dataflow_let_bound_lambda_carries_modify_effect
  The first four are solvable BY THE APPLICATION: `Path 2` (a call through an
  arrow-typed variable) builds a `subst` from its argument check and DISCARDS it — the
  site's own comment says why, on a premise this change invalidates ("an arrow VALUE's
  type is already whatever the environment resolved it to"). `wi342` is different: the
  lambda is RETURNED, not applied, so the only evidence is the declared return type and
  the solve would have to happen at the CONFORMANCE site, which compares without binding.

  GROUP B — FAIL-OPEN (3 rows). A program that must be refused now LOADS:
    wi_2tmb5_bare_op_name_zero_arg_reading_test::the_inline_lambda_twin_was_always_refused
    typer_capability_matrix_test::a_lambda_inside_a_list_literal
    typer_capability_matrix_test::the_row_remainders
  Driven: `operation probe() -> Plain = plain(lambda x -> x)` with `entity plain(v: Int64)`
  returns NO errors, where it was refused "expected Int64, got …".

THE MECHANISM, and it is the answer to "why is `type_var` needed" that neither of this
ticket's earlier answers had. `validate_arg_against_param` gates on groundness —
"Everything above this line treats 'not ground' as 'not mine to decide'".

    arrow(type_var, type_var)   a functor term with a `Ref` child: STRUCTURALLY GROUND
                                -> the whole-type check RUNS -> arrow vs Int64 -> refused
    arrow(?v, ?v)               contains a real variable: NOT DETERMINED
                                -> the check is WITHHELD -> the program loads

So `type_var` is not merely "inert"; it is UNKNOWN BUT STILL CHECKABLE. That is why it is
a functor term and not a variable, and it is a THIRD question beside the two this ticket
already separated. A bare logic variable is "unknown, and therefore not checked".

WHICH REFRAMES THE FIX. Rung 3 cannot simply become a logic variable. Either

  (i) the binder's variable keeps GROUNDNESS while gaining bindability — a CONSTRAINED
      logical variable, which is where this ticket's discussion had independently arrived
      before the measurement gave it a reason; or
  (ii) the solving happens BEFORE the check (Path 2 `subst` propagation + a conformance
      site that binds), and the groundness gate learns that a head-kind mismatch (arrow vs
      a determined nominal sort) is decidable even when a type is non-ground.

(ii) is two edits in a heavily-measured area: the gate carries WI-836 / WI-469 / WI-1059 /
WI-1085 / WI-RKMD4 measurements, and a refusal placed in its non-ground branch would
pre-empt the WI-408 some-coercion that legitimately admits a lambda into an
`Option[T = Function[…]]` slot. Neither candidate is a small edit; NEITHER IS DONE.

THE WORK STANDS AT: rung 3 flipped, `wi_50b2k_binder_inference_test` added (3 rows, the
back-out matrix below measured), 8 pre-existing rows red. Not deliverable as it stands.

WHERE THE REPAIR STANDS — 6403/0 baseline -> 6398/8 -> 6404/2. THREE EDITS, and the ONE
ROOT CAUSE they share is that `validate_arg_against_param`'s groundness gate treats
"contains a variable" as "not mine to decide", which BOTH withholds the refusal AND
prevents the unification that would decide it:

  1. RUNG 3 mints `Term::Var(Var::Global(fresh))` (`type_check_node`'s `Expr::Lambda` arm).
  2. PATH 2 (a call through an arrow-typed variable) now UNIFIES each argument against its
     slot — Path 1's own idiom, boolean discarded — and resolves `ret_ty` through the
     resulting σ. It previously did NEITHER: the site's comment stated as its premise that
     "an arrow VALUE's type is already whatever the environment resolved it to", which held
     only while an un-annotated binder was inert. Fixed 4 rows.
  3. A CALLABLE-KIND VERDICT in the gate's non-ground branch — a function where the
     declared type contains no function anywhere is decided, whatever the variables inside
     turn out to be. The KIND sibling of WI-RKMD4's `nominal_head_mismatch`, and narrower:
     that one withholds at a callable head entirely, because WI-836 measured a nested
     `Function[A = ?X, B = Int64]` against `Int64` in a program that must load — a pairing
     that reaches this gate with `List` on both sides, so this verdict declines there.
     Fixed 2 rows.

     ITS FIRST CUT WAS SYMMETRIC AND THAT WAS WRONG, measured: the REVERSE pairing has
     legitimate coercions (an eta-lift, a zero-arg thunk), and
     `wi_cbrsw_permission_effect_test::a_denial_of_a_sub_capability_does_not_forbid_the_
     super_capability` newly reported "expected () -> Unit, got Unit" on a program that
     must load clean. One direction only.

FOURTH EDIT — THE CALLABLE-KIND VERDICT IS ONE OWNER, ASKED AT TWO SITES.
`callable_against_callable_free` is now a named function called BOTH from the gate's
non-ground branch (the whole argument against the whole declared type — a lambda in an
`Int64` field) and from inside `nominal_head_mismatch` (the per-binding descent — a lambda
inside a `List[T = Int64]`). It is placed ABOVE that function's WI-836 withholding, which
is SYMMETRIC where its evidence is one-directional: WI-836's program
(`take[X](l: List[T = Function[A = X, B = Int64]], w: X)` given `cons(1, nil())`) descends
to actual `Int64` against declared `Function[A = ?X, B = Int64]` — the REVERSE pairing, and
its own assertion says "a NON-ARROW argument passes". Still withheld. Fixed 1 row, 6405/1.

ONE ROW REMAINS RED. Its shape is narrow and MEASURED to the token:

  parse_test::wi342_env_dataflow_let_bound_lambda_carries_modify_effect
    `let f = lambda v -> set_cell(s, v)` then `f` RETURNED. Both neighbours LOAD CLEAN,
    driven:
      DIRECT     `= lambda v -> set_cell(s, v)` in the return position   -> rung 2 works
      ANNOTATED  `= let f = lambda (v: Int64) -> set_cell(s, v)  f`      -> rung 1 works
    So the gap is exactly LET + UN-ANNOTATED BINDER: the let's expectation belongs to its
    BODY, not to its value (correctly), and nothing carries the body's own evidence back.
    `set_cell` declares `v: Int64` and that call is Path 1, whose argument unification
    binds `?v` into the CALLEE-INSTANTIATION σ and drops it with the call.

    FIXED BY THE FIFTH EDIT — SOLVE, THEN COMPARE THE SOLVED TYPE. The op-return check now
    unifies the body type against the declared return and hands `types_compatible` the
    RESOLVED value (and the error carries it too, so the message names the solved type).

    BOTH HALVES ARE LOAD-BEARING, and the first cut had only the unify — measured, it
    changed NOTHING and I wrote it off as "the unify does not bind on this pair". THAT
    CONCLUSION WAS WRONG, and an eprintln settled it in one run: `unify=true`,
    `actual_after=Int64 -> Cell[V = Int64]`. The binding was landing in σ all along;
    `types_compatible` was simply handed the UNRESOLVED `result.ty` and never read it.
    Recorded because the failed first cut looked like evidence about UNIFICATION and was
    evidence about the CALLER — a negative result named the wrong half.

    THE EFFECTS ROW IS NOT INVOLVED, measured before the fix: the effect-free twin
    (`operation outer() -> (Int64) -> Int64 = let f = lambda v -> twice(v)  f`) failed with
    the identical shape.

SUPERSEDED — the two rows below were the state before the fourth edit; one is now green:

  parse_test::wi342_env_dataflow_let_bound_lambda_carries_modify_effect
    `let f = lambda v -> set_cell(s, v)` then `f` RETURNED. The body DOES pin `v` —
    `set_cell` declares `v: Int64` — but that call is Path 1, whose argument unification
    binds `?v` into the CALLEE-INSTANTIATION σ and discards it with the call. There is no
    substitution threaded through an operation BODY, so a binding made in one call cannot
    be seen by the lambda that owns the variable. Either that thread is built (real
    inference state), or the op-return conformance must UNIFY rather than only compare
    (narrow, but it would let any un-determined body type be bound from the declaration —
    measure before believing it safe).

  typer_capability_matrix_test::a_lambda_inside_a_list_literal
    `takes_list([lambda x -> 7])` — expects "expected List[T = Int64], got
    List[T = ??param -> Int64]". Heads AGREE (`List` vs `List`) and the disagreement is in
    the BINDING, so no head-level verdict reaches it; it needs the non-ground path to
    descend. Note the recorded message already contains `??param`, so the row was written
    against a type-var-named binder and its TEXT survives the change — it is the VERDICT
    that flipped.

ITEM 1 OF THE CENSUS ATTEMPTED AND BACKED OUT — `?pat`, measured 2026-09-04.
Flipping the sub-pattern's rung 3 to the engine's own variable FAILED FOUR ROWS, all one
error: "type mismatch in match.rule (rule): expected Int64, got ??pat".

  eval_test::m2_set_literal_as_entity
  wi1094_named_slot_inference_test::two_inferred_sets_agree_and_merge
  wi1094_named_slot_inference_test::inference_does_not_override_a_dictionary_the_caller_supplies
  wi844_sorted_set_driver_test::omitting_the_ordering_is_resolved_and_runs

THE SHAPE IS `match s case SetLiteral(a, _, _) -> a` over a `Set[T = Int64]`. `SetLiteral`
is a PARSE-LEVEL MARKER with no declared field types, so its sub-patterns arrive with no
context type and NOTHING CAN EVER PIN THEM. That is a type nobody can NAME, not one to be
INFERRED — and the SAME site also serves a tuple binder's component (`lambda (a, b) -> …`
with no annotation), which IS an inference hole. One mint, two questions: the very
conflation this ticket separates one level up, found one level down.

So `?pat` cannot be flipped wholesale. It must be SPLIT first — a sub-pattern of a binder
whose parent type is a variable is an inference hole; a sub-pattern of a constructor that
declares no field types is not. Reverted, with the measurement recorded at the mint.

WHAT THE ATTEMPT DID DELIVER, kept: the rule-body/operation-body ASYMMETRY exists at the
tuple level too (`?r <=> apply2(lambda (a, b) -> a + b, (a: 1, b: 2))` was refused with the
`Additive` ambiguity while its operation-body twin loaded), and a SEPARATE pre-existing
defect was measured out of it — a MULTI-BINDER lambda in a rule body loads and is NEVER
APPLIED. Its annotated twin answers nothing either, while `sum2((a: 1, b: 2))` in the same
position answers 3, so it is an application gap and not a typing one. Filed as
WI-20260904-QQPQ2 and pinned by
`wi_50b2k_binder_inference_test::the_tuple_binders_operation_body_twin_drives_and_is_unmoved`.

/CODE-REVIEW (high) — EIGHT FINDINGS, all addressed. Two are worth carrying forward:

  * THE ONE REAL REGRESSION was mine and was MEASURED by the reviewer, not read:
    `callable_against_callable_free` sat ABOVE the reflect-`Term` escape, so
    `term_to_string(lambda x -> x)` flipped from LOADS CLEAN to "expected Term, got
    ??param -> ??param" — while its ANNOTATED twin kept loading, because a ground pair
    never reaches the non-ground branch. The escape now lives INSIDE the verdict, so one
    owner covers both call sites. Pinned by
    `a_lambda_in_a_reflect_term_slot_is_still_accepted`, whose FIRST CUT MEASURED NOTHING:
    it wrapped the lambda in `as_term(..)`, routing it through a GENERIC `E` slot instead
    of a `Term` one, and stayed green under the back-out. Driven directly, it fails.

  * ONE FINDING'S FIX DOES NOT EXIST HERE. The reviewer was right that
    `type_param_var_term` interns a fresh variable that nothing releases, against
    CLAUDE.md's transient-terms rule — but the proposed `Value::Var` carrier is rejected in
    a type position (`value_to_type_child`: "A scalar/`Var`/`Entity` is a typer bug here"),
    measured as `WI-342: non-type Value in a TypeChild slot` on every row.
    `TypeChild::Ground` holds a `TermId`, so a variable in TYPE position is interned BY
    CONSTRUCTION. The cost stands, bounded by (binders x passes); removing it is a
    representation change.

  The other six: the reflect ordering (above), the `walk_type_deep_value`-vs-grounding
  spelling at the op-return, Path 2's unresolved effect row, `abstracting_return_error`
  reading the unsolved body type, the unify running on the `WrapSome` arm (now `Ok`-only),
  and a pinned row for the gap the solve opens
  (`known_gap_the_declaration_may_solve_a_binder_the_body_contradicts` — measured as
  loading with the solve BACKED OUT too, so not a regression).

WHAT TO DO — three parts, measured separately. (a) IS DONE for the `?param` site; see the
measured record above, including that its prediction "(a) alone does not fix the measured
program" was FALSIFIED — the body's own `Int64` literal pins the binder through
`Additive.add`'s signature.

  (a) RUNG 3 MINTS THE ENGINE'S OWN VARIABLE. `Term::Var(Var::Global(fresh))`, which
      extracts as `FlexVar(name, id)`. Freshening the SYMBOL alone is not the fix:
      `TypeVar` has no `id` field, so two differently-named identity-less variables
      still cannot be told apart by a consumer following WI-1079's rule to compare `id`.

      TWO HAZARDS, BOTH NAMED BY WI-963'S OWN DOC. (1) A `Var::Global` is read by the
      DISCRIMINATION TREE as "a wildcard edge matching any subterm" — this changes a TYPE
      position, not an indexed term, but that must be SHOWN, not assumed. STILL NOT SHOWN
      as of the delivery below. And the risk is SCOPE, not semantics: wildcard is CORRECT
      for a flex var. What would be wrong is an inference variable — scoped to one
      type-check pass — escaping into an INDEXED term that outlives it, where the wildcard
      makes the leak SILENT. Note the direction: the inert `type_var` it replaces is a
      functor term, so the same leak would key CONCRETELY — wrong but visible. This change
      may have moved a potential leak from loud to quiet.

      MEASURED 2026-09-04 AND UNREALIZED: a probe in `DiscrimTree::insert_walk` watching
      for a `Var::Global` named `?param` / `?pat` fired ZERO times across 1485 tests. A
      LOWER BOUND, not a proof — the corpus is not the population. The hazard cannot be
      CHECKED structurally because an inference variable and a resolution variable are the
      same type (`Var::Global`); that is WI-20260904-5NM85. And it is not fixed by any
      carrier choice, so WI-20260904-02ERR does not owe it. (2) Structural
      equality of undetermined types goes away: today two are the same term, after the
      change each site allocates a fresh var. WI-963 states that as the cost of the
      alternative; here it is the POINT, but anything relying on the old equality moves.

      THE END STATE IS NOT "REMOVE `type_var`" — it is `type_var` meaning exactly ONE
      thing: no type available at run time, which is what its own doc already claims.
      Removing the stdlib ENTITY is a further step again (declared reflect vocabulary,
      `extract` must stay total, `persistence/print.rs` reads it) and nothing here needs
      it.

      SCOPE IT TO RUNG 3 FIRST, then take the rest of the "to be inferred" column one at
      a time. `type_var` keeps a LIVE consumer that must go on working:
      `type_term_mentions_type_var` gates WI-427's downward hint on it, to keep an
      operation's OWN type parameter out of scope as a top-down hint for a different call.

  (b) IS AN ARGUMENT'S SYNTHESIZED TYPE UNIFIED AGAINST THE CALLEE'S DECLARED PARAM TYPE
      IN A RULE-BODY DATA SLOT? This is the "should be inferred" half. With (a) alone the
      binder has a real variable and still nothing solves it: WI-1058 does not type-check
      the `DataTerm` parent AT ALL, so the lambda's `?T -> ?R` is never compared with
      `apply1`'s declared `Function[A = Int64, B = Int64]`. This is ONE unification, not
      a type-check of the parent — WI-1058's three reasons at `data_functor_error` are
      about CHECKING that node; this asks only whether its declared signature constrains
      a child that is checked anyway. THE INFORMATION IS PRESENT; inferring beats
      generalizing wherever it is.

  (c) GENERALIZE WHAT IS GENUINELY UNCONSTRAINED — the "if it can't be inferred it's
      polytype" half. A binder nothing pins should generalize, and a deferred requirement
      should ride the result: `∀T. Additive[T] => T -> T`, with the USE discharging
      `Additive`. Today that cannot be expressed: `PolyType(binders, body)` has no context
      field and `generalize_eta_arrow` — the sole PolyType producer (WI-1083) — has no
      constraint slot. `signature_bound_vars` is documented as "the one owner" of the
      binder set, so a lambda's unsolved binder extends THAT, not a parallel path. Lands
      in proposal 060's requirement channel. LARGEST of the three; do it last, and only
      for binders (b) leaves open.

CONTROLS.

  THE OBSERVED ERROR IS THE MECHANISM'S SIGNATURE. A type that could not be compared at
  all would leave NO candidate instance. One that compares against everything and commits
  to nothing leaves ALL of them — exactly "3 instances provide … and the call selects
  none". Any repair that produces "no instance" has changed the mechanism, not fixed it.

  A FIXTURE I DESIGNED AND THEN DISCARDED, recorded so it is not re-invented: "two
  un-annotated lambdas needing DIFFERENT binder types in one program, which share a
  TermId today". It MEASURES NOTHING. Sharing a term can only leak through a BINDING, and
  `type_var` is never bound — that is the whole of its inertness. So the two lambdas
  cannot interfere and the fixture passes both ways. The defect is not collision; it is
  that nothing is EVER pinned.

  THE DRIVE TEST IS THE MEASURED PROGRAM ITSELF: `?r <=> apply1(lambda x -> x + 1, 2)`
  must go from refused to ANSWERING 3 — the value, not "it loads". Its back-out is rung 3
  restored to `make_type_var`, which must put it back to "3 instances … selects none".

  MUST STAY GREEN: wi620's `all_match(?xs, lambda (x) -> is_pos(x))` — an un-annotated
  binder already pinned by its own body, because `is_pos` declares `n: Int64`. It is the
  shape that works today and (a) must not move it.

  Nothing pins the measured program, deliberately — it goes green on (a)+(b).

SPLIT OFF, AND NOT A TICKET. The second program this ticket originally carried —
`?y <=> (lambda t -> (t -> t))` — is a different question, and it was a DESIGN decision,
not a defect. It now lives in proposal 055 §2 ("A COMPUTED arrow is `->` itself",
decided 2026-09-04): `->` in value position gets the signature
`arrow(param: Type, result: Type) -> Type` at arity 1, and NOTHING DECLARES `t` — its
type is a temporary logical variable that the BODY solves, because `->`'s operands are
`Type`. The lambda is `Type -> Type` as a RESULT of inference, not as a written
annotation. That is why 055's rule waits on part (a) below: the variable to solve is
exactly what (a) supplies. No ∀, no PolyType, no type-level binder — a bare `->` in expression position is
never a lambda (WI-605 `ArrowTermInExprPosition`), so `(t -> t)` in a lambda body can
only be an arrow TYPE and its binder can only be an ordinary value.

055's work list records that it DEPENDS ON PART (a) of this ticket: until an
un-annotated binder gets a real inference variable, that body cannot pin `t : Type`. It
does NOT depend on (b) — the pinning is from its own body, the same shape as wi620's
`all_match(?xs, lambda (x) -> is_pos(x))` control, differing only in whether the pinning
callee has a declaration (`is_pos` declares `n: Int64`; `arrow` declared nothing).

PART (b) NOW HAS A DRIVEN CONSEQUENCE, MEASURED 2026-09-04 WHILE DELIVERING QQPQ2, and
it is a WRONG VALUE rather than a withheld one. A rule-body lambda's BINDER LIST
destructures a PERMUTED named tuple BY SLOT where every other spelling of the same
program binds BY NAME:

  rule  apply2(lambda (a: Int64, b: Int64) -> a - b, (b: 2, a: 1))   ->  1   (2 - 1)
  op    apply2(lambda (a: Int64, b: Int64) -> a - b, (b: 2, a: 1))   -> -1   (1 - 2)
  rule  named_sub((b: 2, a: 1))   -- a `match` pattern, same carrier                -> -1

THE CAUSE IS THE SAME `None` PART (b) IS ABOUT, one layer over. A tuple pattern takes
its labels from the EXPECTED type (`bind_and_label_pattern`, WI-803); a lambda written
in a rule-body DATA slot receives no expectation, so `labels` is EMPTY and
`match_tuple_pattern` falls to its source-order zip — and the value's source order is
the LITERAL's, not the binders'. The `match` and `let` spellings are unaffected because
their labels come from the operation's DECLARED parameter type, which is present. So
(b) buys the LABELS as well as the binder TYPE, and that is a second reason to do it.

The binder NAMES are not a substitute, and the temptation is worth naming: in the row
above they happen to be `a` and `b`, matching the type's component names. A binder name
is the author's local name and a component name is the type's — one name, two questions.

VISIBLE ONLY SINCE QQPQ2: before the tuple-carrier repair that program had NO answer at
all. Pinned as
`wi_qqpq2_tuple_carrier_test::known_gap_a_rule_body_lambdas_binders_zip_by_slot`, which
asserts the CURRENT value with a message naming this ticket's part (b) as its owner.

NOTE ON THIS TICKET'S OWN HISTORY. Three drafts diagnosed this wrongly before reading
`make_type_var`'s doc: "no expected type reached the binder", then "a type that cannot
unify", then "a wildcard, not a variable". The first two were led by
`prelude/sort.anthill`'s "A PLACEHOLDER, not a logical variable" — an operational claim
in logical vocabulary, which reads as a contradiction since a logical variable IS a
placeholder. That sentence is reworded at its site by this ticket.

