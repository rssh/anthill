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

    "to be inferred" — must commit. THE THREE ROWS BELOW THAT ARE NOT `?param` ARE STILL
    THIS TICKET'S: a spin-off was written and DELETED as a verbatim copy of this section
    (user, 2026-09-04) — restating a census in a second file adds a queue entry and no
    information, and the ticket's own ordering rule already says "scope it to rung 3
    first, then take the rest of the column one at a time":
      ?param        RUNG 3 — DONE (this ticket)
      ?pat          DONE (this ticket) — SPLIT, not flipped. See "ITEM 1 OF THE CENSUS"
                    below: the site serves BOTH questions and only one of them may
                    commit.
      ?T  x3        ANSWERED (this ticket) — and the answer is DO NOT FLIP IT, plus a
                    correction to this row. It is `x3`, not `x2`: the two sites named
                    here are the `ListLit` / `SetLit` build frames, and the third,
                    `check_seq_literal_constructor`, was missed. Probed: the two named
                    fire ZERO times across the whole binary and the unnamed one fires
                    EIGHT — the census named the dead sites and missed the live one.
                    THE COLUMN WAS ALSO WRONG. An EMPTY literal has no element to infer
                    FROM, so this is part (c)'s question and not (b)'s. Flipped anyway
                    and measured: 4127/0, byte-identical diagnostics on every shape that
                    could tell the two forms apart. Both accept the same programs for
                    OPPOSITE reasons — inert is compatible-with-anything, a variable is
                    NON-GROUND so the check is withheld — and a shape mismatch is refused
                    under both, since the `List`/`Set` head is concrete and
                    `nominal_head_mismatch` decides on the head. A change with no witness
                    is not a fix; recorded at all three mints instead.
      ?logical_var  ANSWERED (this ticket) — DO NOT FLIP IT, and the reason is
                    STRUCTURAL rather than a thin corpus. 22,798 reaches across the
                    binary, the most driven of the five, and the flip changed NOTHING:
                    4127/0, byte-identical diagnostics on a free `?x` at two INCOMPATIBLE
                    slots, at one slot, as a dot receiver, and in an entity field.

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

THE SPLIT IS DONE 2026-09-04, and it is exactly that sentence in code. `UnpinnedBinder`
(`Unnameable` / `ToBeInferred`) is threaded into `bind_and_label_pattern` and read ONLY by
the `Pattern::Var` fallback; each recursing arm answers it afresh for its own children:

    CONSTRUCTOR arm   always `Unnameable`, and deliberately NOT computed from the
                      scrutinee: what is missing is the ENTITY's declaration, which no
                      parent type can supply. A `SetLiteral` under an unsolved scrutinee
                      is no more solvable than one under a concrete `Set[T = Int64]`.
    TUPLE arm         `ToBeInferred` when the parent type IS an unsolved variable
                      (`parent_type_is_inference_hole`), else `Unnameable`; INHERITS when
                      it has no type of its own, so a tuple nested in an undeclared
                      constructor field stays unnameable.
    the three outer   seed `Unnameable`. Never read at the lambda and match sites (a type
    call sites        is always present there), and at the `let` site it holds the
                      `bound_ty == None` case unchanged — that evidence would come from
                      the bound VALUE's expression, a different channel, unmeasured here.

`Var::Global` ONLY. A `Var::Rigid` is a parameter rigidified for a body check — named,
just abstract — and its components are no more solvable than an undeclared field's. Both
CARRIERS are read (`Value::Term` wrapping a `Term::Var`, and WI-109's `Value::Var`), since
a type value is carrier-neutral here and reading one would answer `false` for a hole
depending on which side built it.

WHAT IT BUYS, MEASURED, AND THE FIRST TWO WITNESSES MEASURED NOTHING — recorded so they
are not re-invented. `let g = lambda (a, b) -> a + b  apply2(g, (a: 1, b: 2))` is refused
BOTH ways: two unpinned operands leave `Additive` no evidence wherever the mint comes
from, and its single-binder twin `let g = lambda x -> x + x  g(2)` is refused at rung 3's
already-fixed `?param` for the same reason. That is the (c) residue, not a `?pat` gap, and
it is pinned as `known_gap_a_binder_with_no_evidence_in_its_body_is_still_ambiguous`.
`lambda (a, b) -> takes_int(a)` also loads both ways — the callee's declaration pins the
component through Path 1 whatever the mint is.

THE WITNESS IS ONE PINNED OPERAND AND ONE UNPINNED: `lambda (a, b) -> a + 1`, refused with
the ambiguity that is the inertness' own signature and now answering 2. Three arms, all
driven, and the second and third are the SYMMETRY:

    let g = lambda (a, b) -> a + 1   in an operation body, applied through apply2
    holder2(f: lambda (a, b) -> a + 1)   in a RULE body      (entity field: no hint)
    holder2(f: lambda (a, b) -> a + 1)   in an OPERATION body (entity field: no hint)

The two entity-field spellings move TOGETHER — refused before, 2 after — which is the
same shape part (a)'s isolating row uses and for the same reason: an entity field takes no
lambda hint in either body, so both sat on the fallback. A fix that moved only one of them
would have put back the asymmetry this ticket removes. The ANNOTATED twin of each answers
2 under both cells (rung 1 wins, never reaching the mint).

THE BACK-OUT IS EXACT, one per HALF of the split, because a single-cell reading would
credit the wrong one:

    `parent_type_is_inference_hole` forced false   1 of 4124 rows in `wi_tests`:
      `pat_a_tuple_binders_component_is_inferred_when_the_parent_type_is_a_hole`
      (all three arms are in that one row), and nothing else.
    the `match unpinned` dropped for an              5 rows in anthill-core, 5608/5:
    unconditional variable                             eval_test::m2_set_literal_as_entity
                                                       wi1094::two_inferred_sets_agree_and_merge
                                                       wi1094::inference_does_not_override_a_dictionary_the_caller_supplies
                                                       wi844::omitting_the_ordering_is_resolved_and_runs
                                                       control_an_undeclared_constructors_field_stays_unnameable

Both halves are load-bearing and each is measured on its own; a single cell would have
credited the other. Workspace 6425/0 before, 6428/0 after (three new rows).

THE DISCRIMINATION-TREE HAZARD PART (a) LEFT "STILL NOT SHOWN" IS NOW SHOWN, and this
change is what made re-running it necessary rather than optional: (a)'s probe watched for
a `Var::Global` named `?param` OR `?pat`, and at that time `?pat` could not mint one — so
that half of the probe was VACUOUS and its zero said nothing about this site. Re-run with
`?pat` live, over the whole `wi_tests` binary (4124 rows, 0 failed), writing `O_APPEND`
from `DiscrimTree::insert_walk`:

    ?pat   / ?param  reaching an indexed term      0
    any other `Var::Global` var-edge insertion     2,974,466      (the positive control)

So an inference variable minted for a binder does not escape into a term that outlives its
pass, on this corpus. A LOWER BOUND — the corpus is not the population — and the hazard
still cannot be CHECKED structurally, because an inference variable and a resolution
variable are the same type (WI-20260904-5NM85).

A STALE SPEC SENTENCE FIXED, left by part (a) and found here: kernel-language.md §
("How the opened slot is REPRESENTED") named "an un-annotated lambda binder" as the
example of a `TypeVar`. It has not been one since (a). The sentence now says what a
`TypeVar` is for — a runtime carried type, and a sub-pattern of a constructor that
declares no field types — and states the rule as this ticket found it: the distinction is
by REASON FOR THE ABSENCE, not by position.

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

      DONE 2026-09-04, AND IT IS AN EXPECTATION, NOT A POST-HOC UNIFICATION — which the
      ticket's own second reading ("the same `None`", one layer over, at the tuple LABELS)
      already implied and the first ("one unification") did not. A unification run AFTER
      the child is typed is too late for BOTH consumers: the lambda's body is checked at
      the moment the binder is bound, and `bind_and_label_pattern` takes the tuple labels
      at that same moment. So `dispatch_calls_in_occ` now carries an `expected` down, and
      `data_slot_arg_hints` computes one per slot from the callee's cached signature.

      THROUGH `apply_arg_hints`, THE OPERATION BODY'S OWN HINT CHAIN, so the two spellings
      cannot come to hint differently — the asymmetry this ticket exists to remove. It is
      narrow for free: only a lambda / bare reference in a callable slot, a call in a
      ground slot, a sort name in a `Type` slot, a constructor application in a variant
      slot get anything; every other child still gets `None`.

      WHAT IT BUYS, MEASURED, and the first witness written for it MEASURED NOTHING —
      recorded so it is not re-invented. `apply1(lambda x -> x + x, 2)` answers 4 WITH the
      hint and WITHOUT it: after (a) the binder is a real inference variable, so the
      `Additive` dispatch DEFERS instead of tying and the runtime picks `Int64` off the
      actual argument. An un-pinned binder is observable only where the body's use
      CONTRADICTS the declaration, or where LABELS are read:

        FAIL-OPEN -> REFUSAL.  `?r <=> apply1(lambda x -> takes_str(x), 2)` LOADED CLEAN
          and ANSWERED 7, running an `Int64` through a `String` parameter. It now reports
          "type mismatch in takes_str.s (op-arg): expected String, got Int64" — the SAME
          message, to the token, that its operation-body twin and its annotated twin
          already reported, which is what makes this an agreement rather than a new
          refusal the rule-body spelling invented.
        WRONG VALUE -> RIGHT VALUE.  `apply2(lambda (a, b) -> a - b, (b: 2, a: 1))`
          answered 1 (zipped BY SLOT against the literal's written order) and now answers
          -1 (BY NAME, from the callee's declared tuple). QQPQ2's
          `known_gap_a_rule_body_lambdas_binders_zip_by_slot` is DELETED — its own
          instruction — and replaced by
          `wi_50b2k_binder_inference_test::part_b_a_permuted_named_tuple_binds_a_rule_body_lambdas_binders_by_name`.

      THE BACK-OUT IS EXACT: `data_slot_arg_hints` returning `unhinted` unconditionally
      fails TWO rows of 4118 in `wi_tests` — the two above — and nothing else. Baseline
      6420/0 workspace-wide before the change, 6423/0 after (four new rows, one deleted).

      AND (b) ABSORBED (a)'S ONLY WITNESS — found by driving the (a) back-out again after
      (b) landed, not predicted. `?r <=> apply1(lambda x -> x + 1, 2)` fell on the (a)
      back-out when (a) shipped; (b) now reaches that same slot with `apply1`'s declared
      type, so the binder is typed at RUNG 2 and rung 3 is never asked — the row passes
      with (a) backed out and measures "at least one of the two halves". A row that
      isolates (a) had to be built from a slot (b) does not hint, and the entity field is
      that slot: `runit(holder(f: lambda x -> x + 1), 2)` answers 3 with (a) and is
      REFUSED without it, in both (b) states, and its OPERATION-BODY twin moves with it
      (an entity field takes no lambda hint in either body). Filed in the test file as the
      three-cell matrix, all cells driven:

        (a) out    1 row   part_a_a_binder_no_declaration_reaches_is_still_inferred_…
        (b) out    2 rows  the two part_b_ rows
        both out   4 rows  those three plus the row the ticket was opened on

      SCOPED TO AN OPERATION'S PARAMETERS, DELIBERATELY, NOT AN ENTITY'S FIELDS: the two
      have DIFFERENT hint chains and the constructor chain has no lambda arm at all
      (`arrow_slot_arg_hint` reads a bare operation NAME). Hinting an entity field here
      would make the rule-body spelling of a build behave differently from its
      operation-body twin — this ticket's own asymmetry pointing the other way. Measured
      and pinned as `known_gap_an_entity_field_lambda_is_unhinted_in_both_bodies`, which
      asserts the SYMMETRY: both spellings load the same ill-typed program today.

      A SEPARATE DEFECT MEASURED OUT OF THIS WORK AND FILED AS WI-20260904-EMVCB, not
      fixed here: a rule-body lambda whose RESULT IS ITS ARGUMENT answers the argument's
      `Value::Node`, where the operation-body twin answers `Value::Int` —
      `apply1(lambda x -> x, 2)` and `apply1(lambda x -> takes_int(x), 2)`, both unmoved
      by (b) in either direction, while `x + x` and `0 - x` in the same position answer
      scalars. It is an evaluation question (QQPQ2's carrier boundary, the RESULT side)
      and not a typing one.

  (c) NOT DONE. TWO OTHER TICKETS NOW DEPEND ON WHETHER IT HAPPENS — WI-816 and WI-817,
      noted on both 2026-09-05. WI-817 concluded that `lambda_within` is needed by NO
      writable program, on the ground that "a closure arrow type is MONOMORPHIC, so every
      writable lambda is created at a FIXED instantiation"; WI-816's delete-vs-implement
      decision rests on that. Part (c) is exactly what makes it false — `∀T. Additive[T] =>
      T -> T` is created once and invoked at many types. So WI-816 must NOT be closed as
      (a) DELETE while (c) is intended, and (c) is a second re-measure trigger for WI-817
      beside the Rule A one it already names.

      — and still this ticket's, for the same reason the census rows are: a
      spin-off was written and deleted as a re-typing of the three bullets below.
      GENERALIZE WHAT IS GENUINELY UNCONSTRAINED — the "if it can't be inferred it's
      polytype" half. A binder nothing pins should generalize, and a deferred requirement
      should ride the result: `∀T. Additive[T] => T -> T`, with the USE discharging
      `Additive`. Today that cannot be expressed: `PolyType(binders, body)` has no context
      field and `generalize_eta_arrow` — the sole PolyType producer (WI-1083) — has no
      constraint slot. `signature_bound_vars` is documented as "the one owner" of the
      binder set, so a lambda's unsolved binder extends THAT, not a parallel path. Lands
      in proposal 060's requirement channel. LARGEST of the three; do it last, and only
      for binders (b) leaves open.

      WHAT (a) + (b) LEAVE FOR IT, measured 2026-09-04 and stated so the population is not
      re-derived by guess: after (a) an un-pinned binder no longer TIES a dispatch — the
      variable defers and the runtime picks the carrier off the actual argument, so
      `?r <=> apply1(lambda x -> x + x, 2)` answers 4 with (b) and without it. So the
      residue is NOT the ambiguity this ticket opened on; it is that such a lambda has no
      TYPE to state, and therefore nothing can be said about it at a second use site or in
      a signature. A fixture for (c) must make that observable — a row that merely answers
      is green already and measures nothing.

      CONTROLS (c) OWES, both green today and both must stay green: wi620's
      `all_match(?xs, lambda (x) -> is_pos(x))`, a binder pinned by its own body through a
      callee's declaration; and
      `part_b_a_binder_typed_from_the_declaration_refuses_a_body_that_contradicts_it`,
      which must keep REFUSING — a generalization that admits it has replaced a type error
      with a ∀. And `known_gap_the_declaration_may_solve_a_binder_the_body_contradicts` is
      (c)'s to DECIDE, not to inherit: its own text says flipping it to a refusal is the
      question of whether a lambda binder's uses constrain it.

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
all. It was pinned as
`wi_qqpq2_tuple_carrier_test::known_gap_a_rule_body_lambdas_binders_zip_by_slot`, which
asserted the wrong value with a message naming this ticket's part (b) as its owner. PART
(b) IS DONE and that row is deleted; the same program is now asserted at -1 by
`wi_50b2k_binder_inference_test::part_b_a_permuted_named_tuple_binds_a_rule_body_lambdas_binders_by_name`.

A SECOND /CODE-REVIEW PASS (high, run 2026-09-04 on the QQPQ2 tree) FOUND FOUR MORE ON
THIS TICKET'S SHIPPED CODE. Three fixed, one filed:

  * THE CALLABLE-KIND VERDICT WAS ASKED TWICE AND THE SECOND CALL COULD NEVER BE TRUE.
    `nominal_head_mismatch`'s FIRST statement is `callable_against_callable_free(actual,
    declared)`; the gate calls that predicate on the SAME two values, in straight-line
    order, right after calling `nominal_head_mismatch` on them. So the "FOURTH EDIT" above
    did not add a second reach — it MOVED the verdict, and the comment defending the
    outer call ("the two reach different pairs: this one sees the whole argument, that one
    the per-binding descent") described where the verdict was first placed, not where it
    ended up. MEASURED before removing it: neutralized, anthill-core is 5605/0, unchanged.
    Removed; the surviving site's comment now says it serves BOTH pairs.

  * THE NEW `debug_assert` IN `types_compatible_view_structural` WOULD ABORT ON A PAIR
    THE DESIGN SAYS TO REFUSE. `type_dispatch_name_view` NAMES `PolyType` precisely so a ∀
    reaching the structural arms is a MISMATCH no arm accepts, and there is no `poly_type`
    arm — so `(poly_type, poly_type)` is a DELIBERATE `false`, and the assert's predicate
    ("same form name ⇒ an omission") is exactly wrong for it. Excepted. Still not driven
    either way: `check_bare_ref` instantiates a ∀ at the reference, so no corpus program
    reaches this dispatch with two of them; the exception is written from the decision
    5000 lines away rather than from a red row.

  * THE ASSERT MESSAGE CARRIED TWO BAKED-IN 22-SPACE RUNS — a lost `\` line continuation,
    the same footgun this repo has been bitten by before. Repaired, with the whole
    expression kept INSIDE the macro so a release build still evaluates none of it (the
    first repair hoisted a `let` and would have paid for two `type_dispatch_name_view`
    calls on every fall-through).

  * WHAT A FAILED `unify_types` LEAVES IN σ IS NOW READ, and is NOT repaired here. Edits 2
    and 5 made the argument check's σ live — `ret_ty`, the effect row, and the op-return's
    compared value all resolve through it — while `unify_types` binds as it descends and
    does not roll back, so a pair that conforms by SUBTYPING but not EQUALITY keeps
    whatever it bound before the mismatch. NOT an inline fix at these two sites: the
    discarded-boolean idiom is the FILE's, ~10 call sites share it, and repairing two
    would leave eight and two rules. Filed as WI-20260904-60143 with the census it owes,
    and pointed at from both sites.

NOTE ON THIS TICKET'S OWN HISTORY. Three drafts diagnosed this wrongly before reading
`make_type_var`'s doc: "no expected type reached the binder", then "a type that cannot
unify", then "a wildcard, not a variable". The first two were led by
`prelude/sort.anthill`'s "A PLACEHOLDER, not a logical variable" — an operational claim
in logical vocabulary, which reads as a contradiction since a logical variable IS a
placeholder. That sentence is reworded at its site by this ticket.

A /CODE-REVIEW (high) PASS ON THE PART-(b) TREE FOUND THREE, and it also reviewed the
two commits before it. All three addressed; the first was a live wrong-value defect in
SHIPPED code and is the one worth carrying forward.

  * A USER-WRITTEN `_1` LABEL WAS PROMOTED AND THE COMPONENTS SILENTLY REORDERED —
    WI-20260904-QQPQ2's `tuple_components_from_view`, found and DRIVEN by the reviewer
    against a comment at the site that called the shape UNDRIVABLE. The synthetic-`_N`
    promotion asked WI-790's owner about the FILTERED subsequence of `_N` labels, which
    RENUMBERS them: a `_1` written at slot 1 becomes index 0 of that subsequence, passes
    "is this the synthetic name for its own index", and is promoted into `pos` — so
    `iter()` yields it FIRST. `(x: 1, _1: 2)` destructured `2 - 1` on the occurrence
    carrier and `1 - 2` on the native one: ONE PROGRAM, TWO ANSWERS, which is the exact
    disagreement that function exists to remove.

    THE UNDRIVABLE NOTE WAS ABOUT A DIFFERENT SHAPE. It excused a MIXED positional/named
    literal, which parse refuses; it said nothing about an ALL-NAMED literal one of whose
    labels happens to spell `_N`, and that is ordinary text. `_1` at slot 1 is a USER
    label by CLAUDE.md's own rule.

    FIXED by promoting the LEADING RUN of `_N` labels, indexed where they actually stand.
    A `_N` after the run is a user label at the wrong index and stays named, which leaves
    source order intact because `iter()` is `pos ++ named`. Pinned by
    `wi_qqpq2_tuple_carrier_test::a_user_written_underscore_label_is_not_promoted_and_both_carriers_agree`,
    whose CONTROL is the same program with the label renamed to `y` — green under the
    back-out too, so the `_N` spelling is the cause and not the fixture.

  * A DIRECTED VERDICT UNDER A POSITION WHOSE DOC SAID ONLY SYMMETRIC ONES MAY BE CLAIMED.
    `HeadPosition::Nested` read "the parameter's declared VARIANCE is not read, so only a
    verdict both directions agree on may be claimed" — true while every verdict there was
    symmetric, and false since this ticket's FOURTH EDIT put the one-directional
    `callable_against_callable_free` at `nominal_head_mismatch`'s top. The arrow-parameter
    caller's own comment carried the now-VOID reason "a callable component needs no guard
    at this call: the predicate withholds at a callable HEAD itself" — the verdict was
    moved above that withholding by this ticket.

    THE REVIEWER'S DIRECTION CLAIM DID NOT HOLD, checked before acting: that caller SWAPS
    its operands because the parameter position is contravariant, so the directed question
    it asks is `d_param <: a_param` — the sound direction. The reverse pairing, the one
    with the eta-lift and the zero-arg thunk, is excluded by the predicate's own first
    conjunct. What was real is the two stale sentences, and they are repaired: the
    convention is now stated once ("every caller hands (subtype-candidate,
    supertype-candidate); the contravariant caller reaches it by swapping"), and the
    exposure that REMAINS is named — the per-binding descent pairs bindings at the same
    label, a COVARIANT reading, so a verdict claimed there is wrong for a parameter
    declared contravariant.

    MEASURED rather than argued: with the verdict computed beside the arrow-parameter call
    and reported, it fires ZERO times across the WHOLE `wi_tests` binary (4121 rows, 0
    failed) while the SAME probe at the per-binding descent fires ONCE — a positive
    control, so the zero is an unwitnessed reach and not a probe that cannot fire. A lower
    bound; the corpus is not the population.

    THE PROBE'S OWN MECHANISM COST AN HOUR AND IS RECORDED SO IT IS NOT REPEATED. An
    `eprintln!` marker can be TORN by the default test parallelism, and with a control
    that fires exactly ONCE a single lost line flips the verdict — so the first pass was
    run `--test-threads=1`, which serializes 4121 tests to buy write atomicity and was
    heading for ~75 minutes. Appending to a file opened `O_APPEND` is atomic for a short
    write whatever the thread count: same rigor, full parallelism, 356s. The run also went
    through `scripts/test.sh` the second time, so `test-status.sh` could see it — a raw
    `cargo test` writes neither the pid file nor the log symlink that script reads (user,
    2026-09-04).

  * THE HINT/CHILD ALIGNMENT WAS GUARDED ONLY IN DEBUG. `data_slot_arg_hints`' length
    guarantee was a `debug_assert_eq!`, and the caller zips three lists — a `zip`
    TRUNCATES, so a short list would silently drop the tail children from the walk and a
    long one would panic out of bounds inside `ChildCursor::take` with nothing naming the
    site. Promoted to `assert_eq!`: two `usize`s, once per data term.

A /CODE-REVIEW (high) PASS ON THE `?pat` TREE FOUND SIX. One fixed here, one declined with
its reason, three given owners, one folded into an existing ticket.

  * A DIRECT APPLICATION OF A MULTI-BINDER LAMBDA ABORTED THE TYPER — FIXED HERE.
    `let g = lambda (a, b) -> a  g((a: 1, b: 2))` hit
    `arrow_positional_param_slots`' `debug_assert!` ("an `arrow` of arity != 1 must carry
    its parameter list as a `named_tuple`"), because a lambda's arity is its WRITTEN
    binder count while its param comes from the type ladder, whose bottom rung is a
    variable. THE TWO COMMENTS CONTRADICTED EACH OTHER: `lambda_written_arity`'s own text
    says "`param_type` cannot supply it — an unannotated lambda's is a fresh type var".
    The assert was the wrong half, and now excepts an UNDETERMINED param
    (`arrow_param_is_undetermined`: `TypeVar` or `FlexVar`, deliberately not `Skolem` — a
    rigidified parameter is decided, just opaque).

    I DROVE THE ANNOTATED TWIN AND IT ABORTED IDENTICALLY, which is the finding the
    reviewer's own report did not have: `lambda (a: Int64, b: Int64)` aborts the same way,
    because per-binder annotations are read one level down. So the MINT is not what
    decides this and a row driving only the un-annotated spelling would have credited this
    ticket with a pre-existing defect. Both arms now answer 1. Back-out: drop the
    disjunct, 1 row of 4126 fails.

    IN RELEASE THE SHAPE WAS ALREADY `None` — the whole argument check stood down
    silently. The fix makes the debug build agree with that, and the site now says WHY
    `None` is right here: an undetermined param is the withholding `validate_arg_against_
    param`'s groundness gate performs everywhere else, not a malformed term.

  * THE DEEPER REPAIR IS ONE THING ANSWERING TWO FINDINGS — WI-20260904-34J8Z, THE ONE
    FOLLOW-UP THAT SURVIVED BEING ATTEMPTED. The reviewer's second finding is that a tuple
    binder's components are INDEPENDENT variables with nothing tying them to the parent's,
    so solving the parent at a use site solves neither; minting the param as a
    `named_tuple` OVER those variables answers that and the arity disagreement at once.

    BUILT AND MEASURED RATHER THAN ARGUED, and the ticket's first draft named the wrong
    obstacle. It said the blocker was the LABELS. The mint was written with `_1.._n` and
    the whole binary run: 4124 passed, 2 FAILED, and neither failure was about labels.
    (1) `wi517_typed_lambda_binder_test::typed_tuple_binders_pin_elements_without_expected_context`
    — a MINTED context is not a context, but `bind_and_label_pattern` cannot tell, and
    WI-517's rule that the context beats the annotation then DISCARDS the user's written
    `: A` / `: B`. (2) The application flips into an arity error, "expected 2 arguments …
    got 1 argument", which runs into WI-775's settled rule that `f(3, 10)` and `f((3, 10))`
    are both legal at a `Function` slot. Reverted; the ticket now carries both.

  * A RULE-BODY DATA SLOT HINTED AND DID NOT CHECK — FIXED HERE, after being written up
    as a ticket and then attempted. `apply1(lambda x -> "no", 2)` loaded in a rule body and
    answered a `String` from a call declared `-> Int64`; its operation-body twin was
    refused. It now reports "expected Function[A = Int64, B = Int64], got Int64 -> String"
    in both. `dispatch_calls_in_occ` compares the child's synthesized type back against
    the same declared type part (b) handed down.

    THE REASON I FILED IT INSTEAD OF DOING IT WAS WRONG, AND MEASURING SETTLED IT IN ONE
    RUN. The objection was that the comparison needs a σ binding the callee's type
    parameters, so a FRESH σ would pass concrete signatures and FAIL OPEN on generic ones.
    It does not: `validate_arg_against_param` GATES ON GROUNDNESS, so a declared param that
    is the callee's own type parameter reaches that gate unresolved and is WITHHELD. The
    fresh σ answers exactly the subset it can answer, and the gate that makes that true was
    already there. Driven: `pick[X](f: Function[A = X, B = X], v: X)` still loads.

    THAT FUNCTION AND NOT A BARE `types_compatible`, so the reflect-`Term` escape, WI-408's
    some-coercion and the provider-admissible carrier apply here exactly as at an operation
    body's argument — a narrower comparison would refuse programs the op-body spelling
    accepts, inventing the asymmetry this ticket removes.

    BACK-OUT: 1 row of 4126,
    `part_b_a_rule_body_data_slot_checks_its_children_against_the_declaration`, whose four
    arms are the rule spelling (refused), the op twin (refused, the AGREEMENT), a
    conforming lambda (still answers 3, so the check refuses a contradiction and not the
    channel) and the generic callee (still loads).

    WHAT IT DOES NOT DO: the context names the RULE (`value.body (rule)`) where the op-body
    twin names the SLOT (`apply1.f (op-arg)`). Pairing each hint with its param symbol
    means threading `apply_arg_hints`' positional-to-field ranking out through this
    channel; recorded at the site, not done.

  * THE CONTRAVARIANCE EXPOSURE IS CLOSED, not ticketed — and the ticket I wrote for it
    first was WRONG ON ITS FACTS. It claimed "variance is not plumbed to that descent at
    all, so there is nothing to gate on yet". Variance has been plumbed since WI-293:
    [`declared_variance`] reads the `Covariant` / `Contravariant` facts, and
    `Function`'s `A` is DECLARED contravariant — so the exposure was live-reachable, not
    hypothetical. `nominal_head_mismatch`'s descent simply never called it. It does now,
    on all four arms, read for a DECIDED-MISMATCH predicate rather than a compatibility
    one: covariant asks the pair as written, contravariant SWAPPED, invariant must hold
    both ways so either direction deciding is a mismatch, bivariant accepts either so
    neither can decide.

    MEASURED, AND NO VERDICT MOVES ON THIS CORPUS — 4126/0 with the change. A probe
    reporting the arm and both directions at every reach:

        Invariant       145,858 reaches      Contravariant   0
        Covariant        50,480 reaches      Bivariant       0

    so `Contravariant` at this descent is an UNWITNESSED reach with ~196k reaches as the
    positive control. What says the change is not vacuous is that the two DIRECTIONS
    disagree where they are consulted: of the decided reaches, two are `cov=false,
    con=true` — direction matters at this site, and the corpus simply contains no
    contravariant parameter to witness the wrong one.

  * THE INTERNING COST ALREADY HAD AN OWNER — WI-20260904-02ERR, updated rather than
    re-filed. Two things it did not have: the `?pat` split adds a SECOND producer, and the
    site's "bounded by (binders x passes)" reads as a constant of the program when nothing
    releases the refcount — a process that loads repeatedly accumulates without bound.

  * THE `debug_assert` IN `types_compatible_view_structural` IS KEPT — declined, with the
    reason at the site. The reviewer read it as "a user program hitting an unwired pair
    crashes a debug build"; the condition is not one a PROGRAM can create. Both dispatch
    tables are compiled in, so they can only disagree because someone edited one and not
    the other, and the reader it fires for is that developer. A release build gets the
    safe `false` either way. What WOULD change the answer is the census the site already
    says is undone.

THREE FOLLOW-UPS WERE WRITTEN AND TWO WERE DELETED — user, 2026-09-04 ("why you wrote new
tickets?"), and they were right. This repo's own rule is "if the size of code in change is
less than the ticket description, do not open a new ticket, make it inline". Each
description ran 60-80 lines and I had ATTEMPTED NONE of the three. Attempting them took one
measurement each and changed the answer twice:

    0DGXR  contravariance   3 lines. The ticket's premise ("variance is not plumbed")
                            was false — it has been since WI-293. DELETED.
    0ZB9N  the slot check   ~15 lines. The ticket's objection (a fresh σ fails open on a
                            generic callee) was false — the groundness gate withholds.
                            DELETED.
    34J8Z  the named_tuple  survives, and is a BETTER ticket for having been built: the
           param            obstacle it named was wrong and the two real ones are measured.

It is the same failure as the FFYAM spin-off in a different shape — that one re-typed work
that already had an owner; this one wrote a description in place of the attempt. THE TEST
IS CHEAP AND IT IS THE ONLY ONE THAT WORKS: build it, run it, and let the failures decide
whether it is a ticket.

THE `?T` CENSUS ROW, AND WHAT PROBING IT TURNED UP — 2026-09-04.

The row is answered by a MEASUREMENT rather than a change (see the census entry above),
and the probe that answered it surfaced a live asymmetry that the part-(b) slot check did
not cover:

    rule value(?r) :- ?r <=> addI([], 1)      LOADED
    operation w() -> Int64 = addI([], 1)      type mismatch in addI.a (op-arg):
                                              expected Int64, got List[T = ??T]

THE CAUSE IS THAT THE CHECK WAS GATED ON THE HINT. `data_slot_arg_hints` supplies a type
only where imposing one top-down is CORRECT — a lambda in a callable slot, a call in a
ground slot, a sort name in a `Type` slot, a constructor application in a variant slot —
and a collection literal is deliberately none of those. Its DECLARED slot type is
nonetheless exactly what the operation-body spelling compares against.

FIXED BY SPLITTING THE TWO CHANNELS. `data_slot_declared_types` is the sibling of
`data_slot_arg_hints`: same cached signature, same slot mapping, but it answers "what did
the callee DECLARE here" for EVERY slot rather than "what should I impose". The hint still
types the child; the check now reads the declaration.

THE WITNESS IS A LAMBDA IN A NON-CALLABLE SLOT, not the list literal —
`addI(lambda x -> x, 1)` is refused in a rule body now and was refused in an operation
body all along, so the row measures the two spellings COMING INTO AGREEMENT. Pinned by
`a_lambda_in_a_non_callable_slot_is_refused_in_both_bodies`; back-out (the check reading
`expected` instead of `declared`) fails exactly that 1 row of 4127.

AND THE REFLECT-`Term` CONTROL NOW SAYS MORE THAN IT DID: `term_to_string(lambda x -> x)`
in a rule body still LOADS, because the check runs through `validate_arg_against_param`,
which carries the reflect-`Term` escape. A bare `types_compatible` would refuse it. That
is the measurement saying reusing the operation body's own argument checker was
load-bearing and not a convenience.

WHAT IS STILL NOT CHECKED, MEASURED AND NOT FIXED — the list literal itself. A child with
NO dispatch shape (a collection literal) returns before the type check, and one that is a
`DataTerm` returns at `checked_not_typed`, so neither reaches the comparison:

    rule  addI([], 1)          loads     (no dispatch shape -> returns early)
    rule  addI(box(v: 1), 1)   loads     (a DataTerm -> `checked_not_typed` returns early)
    rule  addI(strOp(), 1)     loads

ATTEMPTED: checking un-dispatched children too, by typing them before the shape gate. It
FAILS TWO ROWS and both are real. (1) `wi1056::the_rule_body_and_the_operation_body_report_
the_same_error` — the rule body reports TWO errors where the operation body reports one, and
an `errors.len() == mark` gate does not suppress it. (2)
`wi_qqpq2_tuple_carrier_test::a_positional_tuple_meeting_a_name_keyed_pattern_reads_by_slot`
— a program that must load is refused, "expected (a: Int64, b: Int64), got (_1: Int64,
_2: Int64)": the child's SYNTHESIZED type carries `_N` labels where the operation-body path
compares the argument AS REWRITTEN (WI-803's relabelling). Reverted. Both are the WI-1058
boundary — typing a node the rule-body walk deliberately does not type — and neither is a
small edit.

A /CODE-REVIEW (high) PASS ON THE `?T` TREE FOUND NINE. The two that mattered were both
MINE and both real; one change was REVERTED on its own evidence.

  * THE SLOT CHECK CREATED THE ASYMMETRY IT CLOSES — HIGH, and the reviewer's own fixture
    did not reproduce it. `data_slot_declared_types` mapped positional arguments by RAW
    INDEX, but a named argument CONSUMES a parameter: in `f3(lambda x -> x, a: 1)` over
    `f3(a: Int64, b: Function[…])` the lambda is parameter `b`, and reading `params[0]`
    compared it against `a: Int64`. Driven — rule REFUSED, operation body LOADED. The
    named lookup was the same defect quieter: `Symbol` equality where the tree's rule is
    `same_label`, so a use-site label against a qualified parameter found nothing and
    SKIPPED the check. Both now go through the CALL PATH'S OWN owners,
    `positional_param_indices` (WI-20260827-1F0QP) and `match_named_arg_param`. The
    finding named a program that loads either way; building a DISCRIMINATOR (a slot whose
    two candidate parameters have different types) is what drove it.

  * THE NEW DOC STOLE ITS NEIGHBOUR'S — the footgun this repo has hit before, and it was
    in memory when I did it. Inserting `data_slot_declared_types`' doc directly above
    `fn data_slot_arg_hints` moved that function's ~50-line doc onto the new one and left
    the old with none. Both re-attached, and the two functions are now ONE, returning both
    lists from one signature read — which also makes them structurally unable to disagree
    about the slot mapping, the property the two findings above are about.

  * THE VARIANCE CHANGE IS REVERTED, on the reviewer's evidence plus my own. Finding: the
    `Invariant` arm — the DEFAULT for every sort with no variance fact — asked the SWAPPED
    direction, where the predicates under this descent are one-directional by construction.
    Driven: WI-836's program over a user sort `Holder[T = Function[A = X, B = Int64]]` given
    `holder(v: 1)` went from LOADING to "expected Holder[T = Function[A = ?X, B = Int64]],
    got Holder[T = Int64]", while the identical program over `List` (covariant) loads —
    WI-836's own row. Correcting `Invariant` to the un-swapped direction then left
    `Contravariant` as the only arm that could change an answer, and
    `Contravariant(sort: Function, param: A)` is the STDLIB'S ONLY such fact: zero reaches
    across the binary against ~196k as the positive control, and two hand-built programs
    did not reach it either. A four-arm match whose live arms are the current behaviour and
    whose other two cannot be driven READS as "variance is handled here" while nothing
    exercises it. The exposure keeps its prose at `HeadPosition::Nested`, now carrying the
    measurement. SAME RULE AS `?T`, APPLIED TO MY OWN CHANGE.

  * FOUR SMALLER ONES FIXED: two stale comments at the check (one still said the check is
    gated on the HINT, which is exactly what the change stopped being true; the
    report-once conjunct had no rationale where every neighbour has one), `WrapSome` made
    an EXPLICIT arm saying the ACCEPT is shared with the operation body but the some-INSERTION
    is not (that rewrite is `check_apply_iter`'s, the pass a data term does not get), and
    the stdlib `TypeExtractor.TypeVar` declaration — the AUTHORITY for its own API — which
    still said an un-annotated lambda binder is one. It now states the rule this ticket
    arrived at: the form is decided by the REASON FOR THE ABSENCE, not the position.

  * ONE DECLINED, with the reason at its site: the `types_compatible_view_structural`
    `debug_assert`. Both dispatch tables are compiled in, so they can only disagree because
    someone edited one and not the other.

Workspace 6430/0 -> 6431/0. scaland 539/0.

THE CENSUS IS CLOSED, AND THE COLUMN'S PREDICATE WAS WRONG FROM THE START — 2026-09-05.

All five "to be inferred" rows are now driven, and the two that moved and the three that
did not have ONE explanation. It is not the one the column was named for.

    ?param        FLIPPED     rung 3 of the lambda ladder
    ?pat          SPLIT       a tuple component whose parent type is a hole
    ?T   x3       INERT       an empty list/set literal's element type
    ?logical_var  INERT       a free `?x` with no binding

NEITHER FORM CAN EVER REFUSE. An inert `type_var` is compatible-with-anything, so a check
that RUNS on it accepts. A flex variable is NON-GROUND, so the check is WITHHELD. Both
accept everything, and a mint's choice of form is therefore invisible ON ITS OWN.

THE FLIP CHANGES AN ANSWER EXACTLY WHEN SOMETHING BINDS THE VARIABLE AND A LATER READER
SEES THE BINDING — which needs a σ or an env SHARED between the mint and that reader. That
single predicate explains all four measurements, including the two that failed:

    ?param        the binder's type goes into the LAMBDA BODY'S ENV and the body reads it
                  in the same pass, so `Additive.add`'s signature pins it. THE POINT.
    ?pat, binder  the same env, one level down. THE POINT.
    ?pat, undecl  the same env — which is why flipping it wholesale FAILED FOUR ROWS
                  rather than doing nothing. The variable IS shared, gets bound by
                  nothing, and reaches the op-return conformance UNBOUND: a fail-open.
                  Hence the split rather than a flip.
    ?T            no shared reader. The literal's type is handed to whoever consumes it
                  and read once.
    ?logical_var  no shared reader. `validate_arg_against_param`'s σ is the CALLEE
                  INSTANTIATION and is discarded with the call, so a binding made at one
                  use is not visible at the next — measured directly with `?x` at two
                  incompatible slots, which loads under both forms.

SO THE QUESTION TO ASK AT A MINT IS NOT "is this type to be inferred" — every one of the
five is, in the ordinary sense — BUT "does a later reader in the same pass see what this
mint produced". Only two sites do. Flipping the other three needs the inference-state
thread this ticket's wi342 discussion names ("Either that thread is built (real inference
state), or …"), which is part (c)'s ground.

THE TICKET'S OWN WARNING WAS RIGHT AND SHOULD BE READ TWICE: "BY NAME, WHICH IS A
HYPOTHESIS AND NOT A MEASUREMENT: redo it site by site." Site by site moved `?result` out
of the column before any code changed, corrected `?T` from two sites to three (naming the
two that fire ZERO times and missing the one that fires eight), and has now retired the
column's predicate entirely.

A /CODE-REVIEW (high) PASS ON THE `?logical_var` TREE FOUND SIX, and the one that mattered
was a defect this ticket's own DESIGN had been keeping invisible.

  * A POSITIONAL ARGUMENT BESIDE A NAMED ONE WAS HINTED FROM THE WRONG SLOT — and the
    defect was in `apply_arg_hints`, the SHARED chain, not in this ticket's new channel.
    That loop mapped a positional argument with `params[i]`; a named argument CONSUMES a
    parameter, so the two read different slots than the CHECK, which has always used
    `positional_param_indices` (WI-20260827-1F0QP). Driven, and it is a WELL-TYPED PROGRAM
    REFUSED rather than a missed hint:

        operation f4(a: Function[A = String, B = String],
                     b: Function[A = Int64,  B = Int64]) -> Int64
        f4(lambda x -> x + 1, a: g)
          -> "type mismatch in add.b (op-arg): expected String, got Int64"

    The lambda is parameter `b` and was hinted with `a`'s `String`, so its body was checked
    at the wrong type. Fixed at the shared owner, so both spellings move together.

    WHY IT SURVIVED IS THIS TICKET'S OWN DESIGN POINT, TURNED AROUND. Part (b) hints a rule
    body through the operation body's OWN chain precisely so the two cannot come to hint
    differently — which is exactly what kept a SHARED defect SYMMETRIC, and therefore
    invisible to every rule-vs-op comparison in this file. Both spellings reported it
    identically. It surfaced only because `data_slot_arg_hints`' sibling list had been
    corrected to the right owner and left this one disagreeing INSIDE ONE FUNCTION.
    AGREEMENT BETWEEN TWO SPELLINGS IS NOT CORRECTNESS OF EITHER — the rule-vs-op control
    this ticket leans on cannot see anything the shared chain does to both.

  * MY FORMATTING CHECK WAS UNSOUND, and it let three collapsed lines ship. To avoid the
    "`cargo fmt` rewrites the whole crate" footgun I had been running standalone `rustfmt`
    on a COPY and comparing counts; that proxy disagrees with `cargo fmt -p anthill-core --
    --check`, which flagged all three `?T` sites where a comment insert had swallowed the
    newline. `--check` rewrites nothing, so the proxy was never needed. Now compared HEAD
    vs working with the real command (via `git stash`): 7 hunks in my files against 8 on
    HEAD — one fewer, none new.

  * THE `_N` ALL-SYNTHETIC CARRIER DIVERGENCE DID NOT REPRODUCE. The reviewer predicted
    that an entirely `_N`-spelled list promotes on the occurrence carrier and not on the
    native one, so `match_tuple_pattern`'s `is_name_keyed` gate would take different arms.
    Driven: `(_2: Int64, _1: Int64)` declared against `(_1: 1, _2: 2)`, in-order, and a
    user-labelled control all answer -1 on BOTH carriers — the declared labels are not
    `labels_are_positional`, so both take the positional path. The reviewer was right that
    the CONTROL was missing, so it is now
    `an_all_synthetic_named_tuple_destructures_alike_on_both_carriers`, stated as measured
    rather than as proof (it drives the ANSWER, not the predicate).

  * THE INTERNING NOTE SHARPENED AT ITS SITE: this caller is exactly the case
    `type_param_var_term`'s own doc excludes ("not a case any caller here is expected to
    hit"), because `kb.fresh_var` never produces an existing variable, so the `alloc`
    fallback is taken EVERY time. And "bounded by (binders x passes)" reads as a constant
    of the program and is not one — nothing decrements the refcount. WI-20260904-02ERR owns
    the repair.

  * ONE ALREADY OWNED (the discarded-boolean σ residue, WI-20260904-60143) and ONE LEFT
    WHERE IT IS: the op-return solve gap, pinned by
    `known_gap_the_declaration_may_solve_a_binder_the_body_contradicts`. Measured as not a
    regression, and its own text says part (c) must DECIDE it — so it stays (c)'s rather
    than becoming a separate item.

Workspace 6431/0 -> 6433/0. scaland 539/0.

PART (c) — THE GROUND TRUTH, MEASURED 2026-09-05 BEFORE ANY OF IT IS BUILT.

THE USER'S FORMULATION, which is the one to build to: "create N vars, fill them by solving
typing; if we have unfilled after typing, make it PolyType" — i.e. generalization is a
READ-OFF of the residue, not a detection of failure. Free after solving -> the binders;
constraints mentioning them but not determining them -> the context. "If not inferred"
MEANS "the constraints left the type free". And: for `let g = lambda x -> x + x` we should
infer `Additive[T]` and ADD A `requires` TO THE LAMBDA.

THAT MAPS ONTO EXISTING SHAPES, which is the good news. `PolyType(binders: List[Term],
body: Term)` already IS "the leftover variables" — `binders` is a list of VARIABLES, not
names, each extracting as a `FlexVar` whose `id` links it to its occurrences in `body`
(WI-1079's rule, argued at the declaration). And a `requires`-carrying function value
already works end to end: `wi_5nszy…::a_requires_carrying_operation_mints_its_dictionary_
through_the_nesting` runs `operation same[T](a: T, b: T) -> Bool requires PartialEq[T]`
eta'd into an `Option[Function[…]]` slot and answers.

WHAT IS GENUINELY NEW is that a LAMBDA's dictionary CANNOT BE RESOLVED AT THE MINT. In that
passing row the slot is concrete, so `PartialEq[Int64]` resolves where the value is made.
A generalized lambda has nothing to resolve against until it is APPLIED, so the constraint
must ride UNRESOLVED and be filled at the USE. That is the one thing the existing mechanism
cannot do — and it is exactly `lambda_within`'s purpose (WI-816 / WI-817, noted there).

AND THE BLOCKER UNDER ALL OF IT, now MEASURED rather than inferred:

    (i)   THERE IS NO CHANNEL FOR A SOLVED BINDER. `TypeResult` carries `ty`, `env`,
          `effects`, `node` — NO substitution. `check_apply_iter` takes `env` IMMUTABLY,
          and `bind_var` is called at binder-binding sites only (`bind_and_label_pattern`,
          op-param setup), so a call cannot write a solved type back. `check_operation_
          bodies`' per-body `rigidify` is a READ-ONLY type-param→rigid map, not an
          inference σ. So at the `LambdaBody` frame the arrow is built from the ORIGINAL
          `param_type` and every binder looks unfilled.

    (ii)  BUT THE BINDING DOES HAPPEN, which is what says the design is viable rather than
          misconceived. Probed at `check_apply_iter`'s argument unification, reporting
          every variable a unification newly bound, on
          `operation outer() -> Function[A = Int64, B = Int64] = let f = lambda v ->
          twice(v)  f`:

              _ 109    R 23    EffP 5    Acc 4    T 3    Eff 2    Dst 2    A 2    ?param 1

          `?param` IS bound — once — to `Int64` by the body's own `twice(v)` call, into the
          per-call σ that is then DISCARDED. The evidence exists and has nowhere to go.

    (iii) SO NAIVE GENERALIZATION OVER-GENERALIZES, and wi620's control is what would
          break: `lambda x -> is_pos(x)` would become `∀T. T -> Bool` where it is
          `Int64 -> Bool`.

THE ORDER IS THEREFORE FORCED, and it is not the order this ticket's (c) bullet implies:

    1. THREAD THE σ — a pass-level substitution the work loop carries, into which
       `check_apply_iter` binds CALLER-OWNED variables (not the callee's own instantiation
       vars, which is the distinction the per-call σ exists to keep). Until this, "unfilled"
       is not answerable. THE BULK OF THE WORK, and no design for it exists anywhere.
    2. AN UNSOLVED-RECEIVER DISPATCH RECORDS the requirement instead of raising. Today it
       raises `Ambiguous` on the spot — the constraint is not LEFT free, it is SPENT AS AN
       ERROR. `DispatchOutcome::Deferred` is NOT this channel: its own doc scopes it to a
       spec reached through the enclosing sort's `requires` chain, i.e. a constraint already
       declared, and it carries no payload.
    3. the leftover vars become `PolyType` binders — the existing shape, no change.
    4. the constraint rides as an OPEN dictionary, filled at the use rather than the mint.

Steps 3 and 4 have machinery. Steps 1 and 2 do not.

PART (c), FIRST SLICE — DELIVERED 2026-09-05, AFTER BEING BUILT, BACKED OUT, AND REBUILT
ON A WATERMARK THE USER NAMED.

WHAT IT DOES. `report_call_solutions` copies a finished call's bindings into the walk's
`Substitution`; the `LambdaBody` frame resolves the arrow through it. An un-annotated
binder's arrow now reflects what its BODY pinned rather than the variable minted before the
body ran: `let f = lambda v -> twice(v)` is `Int64 -> Int64`, not `??param -> Int64`.

THE FIRST CUT WAS BACKED OUT BECAUSE ITS SAFETY ARGUMENT WAS FALSE, and the record is kept
because the failure mode is the reusable part. It rested on "`VarId`s are unique, so a
callee's variable can never be mistaken for a caller's — the WRITER needs no scoping rule
and the READER filters". /code-review falsified it and three rounds of driving found THREE
populations:

  1. `record_type_param_var` publishes ONE canonical `Var::Global` per type-parameter
     SYMBOL, so a callee's `T` is the SAME variable at every call site — measured in one
     walk as `var 1372 kept=String dropped=Int64`. WI-374's own note says the per-call σ is
     what kept that sound, and this copied out of it.
  2. The filter constrained the σ's DOMAIN, not its RANGE: `?param := ?T_callee` put a
     callee variable INTO the arrow (measured, an arrow leaving the walk reading `?_`).
  3. A call's σ is NOT type-only. With both gates added, a ground-disagreement assert still
     fired on 19 ROWS OF 19, colliding on `Name` bound to `"x"` / `"y"` / `"z"` — dispatch's
     value-level bindings, riding as `Value::Term` so a carrier filter missed them too.

THREE POPULATIONS IN THREE PATCHES SAID THE METHOD WAS WRONG, NOT THE PATCHES. Enumerating
what to exclude is guessing at a set nobody has enumerated.

THE FIX IS PROVENANCE BY ALLOCATION ORDER (user, 2026-09-05: "env should also contain idx
of var, to have each new var with new index"). The index ALREADY EXISTED and nothing read
it: `VarId` carries a `u32` and `fresh_var` is a monotonic counter. `var_watermark()` reads
it, the walk takes one at its start, and a binding is reported only when the VARIABLE and
every variable inside its VALUE satisfy `raw() >= watermark`. None of (1)-(3) is minted
during the walk — a type parameter's canonical variable and a fact pattern's variables come
from LOAD — so one question retires the list.

    MEASURED: with the gate, a consistency check over the whole `wi_tests` binary sees NO
    variable bound twice to disagreeing values (4131 rows). Ungated: 19 of 19 in one file.

A SECOND /code-review FINDING, ALSO REAL AND ALSO A WRONG ACCEPT: resolving only the
arrow's DOMAIN splits a binder occurring in both halves. `lambda v -> (a: twice(v), b: v)`
against a declared `B = (a: Int64, b: String)` LOADED — the domain read `Int64`, the
codomain's raw `??param` no longer conflicted, and the op-return's declaration-solve bound
it to `String`. Both halves AND the effects now resolve together, which is the invariant
the frame's own comment states and the rule Path 1 already follows. Pinned by
`both_halves_of_a_solved_arrow_resolve_together`.

ROWS: two known gaps flipped to positive, each carrying the instruction to write its
replacement —
  * `the_body_use_binds_a_let_bound_lambdas_binder_before_the_declaration_can` (the WRONG
    VALUE: `?v` committed to `String` while the body handed it to an `Int64` parameter),
    with the AGREEING twin as control;
  * `an_entity_field_lambda_is_refused_in_both_bodies_once_its_body_pins_the_binder`, which
    EARNED ITS KEEP mid-change: with only the arrow fix,
    `runit(holder(f: lambda x -> takes_str(x)), 2)` was refused in an operation body and
    still LOADED in a rule body. Extending the CHECK to an entity's FIELDS closed it; the
    HINT still reads operations only, or the mirror asymmetry returns.

BACK-OUTS, ALL DRIVEN: the `LambdaBody` resolve dropped -> 2 rows; the entity-field
fallback dropped -> 1 row (the asymmetry, restored); the `body_ty` / `body_effects`
resolutions dropped -> the desync row.

TWO NAMED GAPS RATHER THAN SILENT ONES, both at the site: there is NO ROLLBACK — a report
happens when an argument's unification finishes, which is before the call is known to type
(the discarded-boolean idiom WI-20260904-60143 owns), so a speculative binding from a
failing call could outrank a later one; and THE PROJECTION-DEFERRED PATH DOES NOT REPORT.

THE CONTAINER IS STILL WALK-LIFETIME, which is what makes the watermark NECESSARY rather
than merely correct. Solutions travelling WITH the result would scope to the body that
produced them and both gaps above would go with it — `check_apply_iter` already returns
`env: env.clone()` at FIFTEEN of its return points, so the channel exists and is inert, and
`LambdaBody` discarding `body_r.env` is the one thing in the way. That is the next step,
and it is WI-502's `σ → (σ, residual C)` shape, which (c)'s constraint half needs anyway.

Workspace 6433/0 -> 6434/0. scaland 539/0.

A SECOND /code-review PASS ON THE REBUILT SLICE FOUND SEVEN, all addressed. The HIGH is the
one worth carrying, and it is a lesson about GATES rather than about this ticket.

  * THE GATE READ A BLIND COLLECTOR, so its range half was VACUOUS for exactly the leak it
    exists to stop. `collect_value_type` has arms for `Value::Term`, `Value::Node` and
    `Value::Entity` / `Value::Tuple`, then `_ => {}` — there is NO `Value::Var` arm. A
    binding `?param := Value::Var(T_canonical)` (the shape `unify_types`' var arm mints when
    it binds one variable to another's walked value) therefore collected ZERO variables, and
    `vars.iter().all(..)` answered `true` on an empty list. A gate that asks an
    under-collecting reader answers `true`, not `false`.

    FIXED AT THE CALLER AND DELIBERATELY NOT IN THE COLLECTOR. `collect_value_type` feeds
    `signature_bound_vars`, the ONE OWNER of a signature's binder set (WI-1083), so widening
    it changes which variables a `∀` quantifies. MEASURED BOTH WAYS: adding the arm there is
    green (4130/0), and the shape occurs ZERO times on this corpus — so the wider fix has no
    witness, and by the rule this ticket has been applying all along it does not ship. The
    under-collection is real, is NOT this ticket's, and is recorded at the site: its map twin
    `map_value_type` misses the arm too, and WI-1078's reader inherits it.

  * THE OCCURS-CHECK THE DOC CLAIMED DOES NOT EXIST. `Substitution::bind_value` compares
    structurally when the variable is already bound and RAW-INSERTS otherwise, and the
    report is filtered to the unbound case, so it always takes the insert path. Two calls
    contributing `?a := f(?b)` and `?b := g(?a)` — each acyclic and walk-local alone — would
    leave `body_solutions` CYCLIC for `resolve_type_deep_value` to walk. The check is now
    performed here, by `value_mentions_var`.

  * THE DOC-STEAL, THIRD TIME THIS SESSION: `var_watermark` was inserted under `fresh_var`'s
    doc line and took it. Restored.

  * A `TEMP REVIEW PROBE` TEST WAS LEFT IN THE TREE by the reviewing pass —
    `zz_probe_canonical_type_param_leak`, a `#[test]` that only prints and asserts NOTHING,
    which would have committed as permanent zero-signal coverage for the very leak above.
    Removed. (The first pass's probes reached my saved patch the same way, and had to be
    stripped out of it before it could be reapplied.)

  * TWO DOC SITES STILL ASSERTED THE FALSIFIED "no scoping rule needed" RATIONALE — at the
    DECLARATION and at the ONLY CONSUMER, so a maintainer reading either would have removed
    the watermark gate as redundant. Both now say what was measured.

  * THE OP-RETURN UNIFY PROBES ON A CLONE AND COMMITS ONLY ON SUCCESS. `unify_types` binds
    as it descends without rolling back, and this σ is read TWO LINES DOWN by the
    `walk_type_deep_value` whose result `conformance_error` RENDERS — so on the refusal path
    this ticket's own new row exercises, the "got …" half of the user-visible message was
    built from a half-applied substitution. `hint_instantiation_subst` is the file's pattern
    for this and an `imbl` clone is O(1) (WI-569). The file-wide census of the ~10 sites
    sharing the discarded-boolean idiom stays WI-20260904-60143's; this is the one whose σ a
    DIAGNOSTIC reads.

  * A duplicated-and-truncated comment block from my own edit, repaired.

THE LESSON THAT GENERALIZES: A GATE IS ONLY AS EXHAUSTIVE AS THE READER IT ASKS. Both the
first cut's failure (enumerating populations) and this one's (asking a collector with a
`_ => {}` arm) are the same shape — the gate was written against an idea of the input
rather than against what the reader actually returns for every carrier.