## Attributes

- id: WI-20260904-60143-a-discarded-boolean-unify
- created: 2026-09-04T17:21:39Z

- status: Delivered
- status_agent: user
- status_at: 2026-09-06T14:45:05Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DISCARDED-BOOLEAN `unify_types` LEAVES ITS PARTIAL BINDINGS IN σ, AND SINCE
WI-20260904-50B2K THAT σ IS READ.

RAISED BY /CODE-REVIEW on the 50B2K tree, 2026-09-04. `unify_types` has no
snapshot/rollback: it binds into `subst` as it descends and returns `false` at the FIRST
mismatch, keeping everything it bound before that point. Ten call sites in `kb/typing.rs`
discard the boolean deliberately — the idiom's stated reason is that unify is EQUALITY
while the surrounding check is SUBTYPING plus three conversions, so a unify-false must
not reject:

  typing.rs  9262 14741 15839 15887 15943 16517 18862 18980 23402 44764 44774 44899
             60252 60257 65231   (grep `unify_types(kb, &mut subst`; not all discard)

THE IDIOM WAS HARMLESS WHILE NOBODY READ THE σ AFTERWARDS. 50B2K's edits 2 and 5 changed
that: the arrow-call path now resolves `ret_ty` AND the effect row through the same
`subst` (typing.rs ~19099), and the op-return check hands `types_compatible` the RESOLVED
value (~65231). So an argument that conforms by subtyping can now leave a return type
that depends on HOW FAR unification got before giving up.

THE REVIEWER'S SCENARIO, not yet driven: an arrow slot `Pair[L = Animal, R = ?v]` given
`Pair[L = Dog, R = Int64]`. Unify descends, `Dog` vs `Animal` is a mismatch under
EQUALITY, and whether `?v` was bound to `Int64` first depends on named-arg iteration
order. In the losing order the caller reports a spurious "expected …, got `??param`".

WHY THIS IS NOT AN INLINE FIX AT THE TWO 50B2K SITES. The question is the FILE'S idiom,
not those sites': repairing 2 of ~10 is the "a SHARED CALLEE is the wrong place for a
CALLER's guard" shape in reverse — the other eight keep the behaviour and the next reader
finds two rules. The census is the work.

THE CANDIDATE REPAIR IS CHEAP IF THE CENSUS SAYS SO. `Substitution.bindings` is an
`imbl::HashMap` (WI-569), so `Clone` is O(1) structural sharing — a snapshot is
`let before = subst.clone()` and a rollback is `subst = before`. CHECK BEFORE BELIEVING
IT: `Substitution` also carries `parent: Option<Box<Substitution>>`, whose `Clone` is a
DEEP copy of the chain, plus `contradiction_details` and the constraint store. Measure the
clone at a hot site rather than assuming the map's O(1) covers the struct.

WHAT THE TICKET OWES:
  1. WHICH of the ~15 sites discard the boolean, and for each, whether anything READS the
     σ afterwards. The two 50B2K sites do; the others are the population to establish, not
     to assume.
  2. A DRIVING program for the wrong-value case — a subtyping-conformant argument whose
     partial bindings change a reported type. Without one, a rollback is an unmeasured
     behaviour change and must not ship: some row may DEPEND on a partial binding, which
     is itself worth knowing.
  3. Then either the rollback at every reading site, or a stated rule at
     `unify_types` saying what a caller may assume about σ on `false` — the two-lists
     failure this file has been bitten by is exactly what an unstated one produces.

Pointed at from `validate_arg_against_param`'s Path-2 argument loop (the `ArgValidation::
Ok` arm), so the next reader of that site meets this ticket rather than re-deriving it.


### Census

Every `unify_types(` call in `kb/typing.rs`, classified. The ticket estimated "~10 sites
discard the boolean"; the discarding population is **16**, and the ticket's own line list
named 15 candidate positions of which several were internal recursion rather than callers.

#### A — the relation's own descent (7)

`unify_parameterized_view` base + bindings, `unify_arrow_view` params/result/effects,
`unify_arrow_function_view` param/result/effects, `unify_named_tuple_as` slots,
`unify_arrow_params`, the shape re-dispatch. These are the mechanism, not callers: σ is the
caller's and the verdict propagates. Both carriers reach them through ONE implementation
(`unify_term_dispatch` routes to the same `*_view` fns), so an edit here cannot desync the
hash-consed path from the `Value` path.

#### B — already atomic: probe or snapshot (6)

`hint_instantiation_subst` (clone, commit on success) · the contradiction-replay `scratch` ·
`pair_present_labels` and `cover_present_labels` (snapshot, restore per candidate — a
BACKTRACK, not a verdict rollback) · the `lacks`-conflict probe (never commits) · the
operation-return check (clone, commit on success — added on WI-20260904-50B2K after review).
The file had ALREADY hand-rolled this pattern six times and stated the reason at each. The
ticket said "four".

#### C — boolean used as the verdict (4)

`variant_slot_arg_hint` (`return None`, σ local) · the projection-return check (renders a
diagnostic FROM the polluted σ, then `Err`) · `constrain_vid` and `constrain_literal_arg`
(set `subst.contradiction` conditionally; the rule's σ keeps the partial bindings either way).

#### D — boolean DISCARDED and σ read afterwards — the population (16)

`thread_expected_tuple_fields` (reads on the NEXT line) · the eta pin from an expected arrow
(feeds the dictionary build) · `concrete_self_receiver_override` · Path 1's positional and
named argument loops · the projection-elimination loop · the expected-return seed · Path 2's
positional and named argument loops · the bridge-requirements loop · the slot-binding loop ·
the constructor's named-field, positional-field and expected-type unifies · the value-typer's
two constructor-field unifies.

**The census result that decided the fix.** At four of these — Path 1's and Path 2's argument
loops — the SAME σ in the SAME call is read BOTH as evidence (the groundness-gated refusals
read it through `validate_arg_against_param`) and as the answer (`resolved_ret` / `ret_ty`).
So item 3's first branch, "the rollback at every reading site", is not available at the sites
that matter: there is no reading site to roll back at without also removing the evidence.

### Item 2 — the driving program

`sort Pair[A, B]`, and one disagreement written two ways:

| slot order | before | with the ticket's rollback | delivered |
|---|---|---|---|
| `take[X](p: Pair[A = Int64, B = X])` given `Pair[A = String, B = Int64]` | `expected Pair[A = Int64, B = ?X]` | `expected Pair[A = Int64, B = ?X]` | `expected Pair[A = Int64, B = Int64]` |
| `take2[X](p: Pair[A = X, B = Int64])` given `Pair[A = Int64, B = String]` | `expected Pair[A = Int64, B = Int64]` | `expected Pair[A = ?X, B = Int64]` | `expected Pair[A = Int64, B = Int64]` |

A raw inference variable in a refusal message — the ticket's predicted symptom, reached
without any conversion, purely by which slot was written first.

### Item 3 — the rollback is FALSIFIED, twice

Built (snapshot at entry, restore on `false`) and run: **6481 pass, 4 fail.**

| fails with a rollback inside `unify_types` |
|---|
| `kb::typing::tests::wi1084_arrow_function_unify_tests::the_two_spellings_of_one_slot_answer_alike` |
| `wi1078_unbound_return_var_test::the_tie_survives_the_opening` |
| `wi1082_self_return_tie_test::a_bodyless_member_cannot_launder_either` |
| `wi1083_polytype_test::a_result_type_disagreement_is_refused` |

All four are groundness-gated: the variable pinned by the AGREEING component is what makes
the disagreeing one read GROUND and therefore comparable. This is the ticket's own warning
("some row may DEPEND on a partial binding") realised — and `unify_arrow_function_view`'s doc
had already said so in the file: "answered false having bound nothing was a defect".

And the second falsification: the rollback does not even fix the order-dependence. It LEVELS
DOWN — the middle column above shows it making the order that worked report `?X` too.

### Delivered

The rule is not "roll back" and not "descend totally" — it is **no authorial order may decide
which bindings survive a `false`.**

- **A list whose slot order is the AUTHOR'S** — a parameterized type's bindings, a tuple's
  fields, an arrow's parameter list — unifies every slot and returns the conjunction.
  `unify_parameterized_view` and `unify_named_tuple_as`, one back-out each.
- **An arrow's `param`/`result`/`effects` keep the short-circuit**: their order is fixed by
  the form, so stopping at the first disagreeing part is already a function of the two types.
  Making them total too was built and measured UNSOUND — it fills unwritten carrier params
  from a failed unify and turns
  `wi_mdwew…::ambient_requires_compound_clause_value_is_not_bound_verbatim` from a refusal
  into a clean load ("grant a licence and bind a wrong rigid together", the shape that test
  exists to forbid). Kept in step across BOTH spellings (`arrow` and `Function[A, B, E]`).
- **The rule is STATED at `unify_types`** — what survives a `false`, why it is deliberate,
  which four rows depend on it, and the probe-commit a caller takes when it reads σ as an
  answer.
- **Two comments that made FALSE claims about this are corrected**: the receiver-override
  said a failed unify "leaves them free" and the expected-return seed said it binds "nothing".
  Both bind every component that agreed.

Tests: `wi_60143_total_unify_descent_test`, 6 rows — 2 controls, 2 loops driven by their own
back-out, and the tuple back-out turns a REFUSAL into a clean load (a refusal that did not
previously happen: nothing pinned `X`, so the slot read non-ground and the gate deferred).

