## Attributes

- id: WI-20260902-2SZ88-make-the-dot-chain-provenance
- created: 2026-09-02T18:40:24Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-02T20:32:05Z

- acceptance: cargo-test, scaland-sbt-test

## Description

MAKE THE DOT-CHAIN PROVENANCE ANSWER EXACT: ASK THE PARSE NODE, NOT A HASH-CONSED KEY.

`Loader::parse_dot_chain_table` answers 'is this node a dot the author wrote' from a `HashSet<TermId>` keyed by the HASH-CONSED KB term. That key is MANY-TO-ONE and cannot answer the question: a minted `ns.rel` and a hand-written `anthill.reflect.field_access(ns, rel)` convert to the SAME term — that identity is the entire premise of WI-20260901-92VA4, which is why the bit exists rather than a shape test.

The first cut stamped both, and the written call was silently ACCEPTED and typed as the relation it does not spell. MEASURED, one entity with two Int64 fields, varying ONLY structural identity:

  `boxedc(v: <written call>, w: 1)`                  -> refused (control)
  `boxedc(v: <written call>, w: zz4n.inner.other)`   -> refused (control, distinct TermId)
  `boxedc(v: <written call>, w: zz4n.inner.rel)`     -> **ACCEPTED, typed Relation**

The shipped repair is a SET DIFFERENCE: a kb id is stamped only if EVERY parse node in the atom mapping to it is a citation. That is conservative in the safe direction — never a wrong acceptance — but it is a real weakening: on a collision the bit is WITHHELD where the exact answer is true, so a citation that shares a term with a written call beside it falls back to the per-leaf 'unresolved name' cascade WI-20260902-4NEKZ removed. A user who writes both spellings in one atom gets the worse diagnostic back, silently.

THE EXACT FIX is to carry the PARSE `TermId` beside the KB one through the materializer — `WorkOp::Visit` currently carries only the term id — so `visit_term` can ask `dotted_citation_name` of the node itself instead of looking up a lossy key. Then the bit is exact, the set difference goes away, and `new_expr_dot_chain`'s doc can go back to claiming the safety property it used to claim.

WORTH DOING WITH WI-20260902-2NXAC, NOT BEFORE IT: that ticket lists three MORE readings the same early return drops (CZJ2N's nullary-operation call, proposal-035 form-(3) receiver types, and `substitute_occurrence`'s `Expr::Apply` arm), and threading the parse id is the one change that answers all of them at once. Doing this alone buys back one diagnostic; doing it as the shared substrate fixes four things.

ACCEPTANCE. `a_citation_beside_a_written_field_access_call_does_not_launder_it` keeps passing on all three rows, AND a new row shows the citation in row three getting the ONE true diagnosis rather than the three-segment cascade — that row fails today by design and is the measurement this ticket exists for.

Found by /code-review on the WI-20260902-4NEKZ follow-up, 2026-09-02.

## Changes

### 2026-09-02T20:01:55Z — feedback — user

DELIVERED AS "DELETE THE ROUND-TRIP", NOT AS "THREAD THE PARSE TermId".

The ticket proposed carrying the parse `TermId` beside the KB one through `WorkOp::Visit`.
Measured against the call sites, that is the wrong shape: `materialize_from_handle` has
FOURTEEN production callers (4 in eval/eval.rs, 4 in kb/resolve.rs, one each in
eval/mod.rs, kb/execute.rs, kb/mod.rs, kb/typing.rs, 2 in kb/load.rs) against TWO
`_spanned` ones, and the fourteen start from a runtime-substituted or resolved term with
no parse node at all. A parse id there is `Option` at 14 of 16 readers — a fallback at
every one, which the repo's own rules forbid — and it gives `node_occurrence.rs` a
dependency on the parse IR that its own doc flags at the same site.

WHAT SHIPPED INSTEAD. `Loader::entity_ctor_expr` builds an entity constructor's occurrence
from its PARSE NODE. There is then no key to be many-to-one, because the builder is
standing at the node: every child recurses through `build_body_atom_occurrence`, which
takes its span from the parse term and its `dot_chain` from `dotted_citation_name` of its
own node — the same exactness the un-nested path always had.

CENSUSED FIRST, not assumed. The early return was instrumented and the whole workspace
suite run: 127 097 nodes took it. 126 813 — 99.78% — are plain entity constructors and now
take the native arm. 284 are reflect-keyed (`ListLiteral` 192, `dot_apply` 49, `if_expr` 9,
the rest in ones and twos) and ONE was not an entity at all. So the round-trip is, in
practice, this path.

THE ONE THING THE PARSE NODE CANNOT ANSWER, and the failure it caused. `convert_term` does
not only resolve names, it LOWERS — WI-433 assigns positionals to declared fields, `some(x)`
is coerced to `some(value: x)`, and `fill_entity_named_args` fills omitted fields with a
fresh var or WI-716's `none()`. Those fills must not be re-minted or the occurrence and the
term hold different variables for one field. A new `Loader::entity_slot_origin`, keyed by
the PARSE id and written at the single site that decides the assignment, says which parse
child produced each slot; a slot with no origin is invented and is materialized from the
term.

AND THE LOWERING ALSO WRAPS WRITTEN SLOTS, which the first cut missed:
`wrap_bare_option_value` turns a bare value at an `Option[..]` field into `some(…)`, so the
lowered child is one node LARGER than the conversion of the parse child. MEASURED — five
`github_todo_test` rows fell, `wi717_omitted_optionals_stay_claimable` among them, because
the occurrence held the bare payload while the term held `some(payload)`. The repair is an
IDENTITY CHECK against `term_map` rather than a list of the transforms that exist: a list
would be a producer census (WI-805) and would go stale in silence the day a second
transform is added.

MEASURED EFFECT — TWO ROWS FLIP, 0 -> 1. This is WI-20260902-2NXAC's finding (1), on the
half this change reaches. Definite answers:

  seven <=> 7                              1 -> 1  control
  seven() <=> 7                            1 -> 1  control
  plus1(6) <=> 7                           1 -> 1  control
  boxedva(x: plus1(6)) <=> boxedva(x: 7)   1 -> 1  the control that says nesting is fine
  boxedva(x: seven) <=> boxedva(x: 7)      0 -> 1
  boxedva(x: seven()) <=> boxedva(x: 7)    0 -> 1
  [seven] <=> [7]                          0 -> 0  the reflect half, still 2NXAC's
  [seven()] <=> [7]                        0 -> 0  ditto
  [plus1(6)] <=> [7]                       1 -> 1  control

AND THE DOT-CHAIN ANSWER IS NOW TABLE-FREE FOR THIS PATH, measured on two axes.
With `parse_dot_chain_table` made to return an EMPTY set, per row, baseline -> after:

  zz4n.inner.rel = 7               1 typed Relation -> 1 typed Relation   control, never took the return
  [zz4n.inner.rel] = 7             3, none typed    -> 3, none typed      reflect half, still reads it
  {zz4n.inner.rel} = 7             3, none typed    -> 3, none typed      ditto
  (zz4n.inner.rel, 1) = 7          3, none typed    -> 3, none typed      ditto
  boxed4n(v: zz4n.inner.rel) = 7   3, none typed    -> 1 typed Relation   <- the only row that moves

Second axis: with the change in, commenting out `cited.retain(|k| !plain.contains(k))`
leaves `wi_4nekz_dotted_equation_operand_test` 8 of 8 GREEN, where on the baseline the same
back-out reddens `a_citation_beside_a_written_field_access_call_does_not_launder_it`. The
set difference stays only because the reflect half still keys on the same table.

THE ACCEPTANCE ROW THIS TICKET ASKED FOR CANNOT BE WRITTEN, and that is a finding rather
than an omission. The ticket asks for a row showing "the citation in row three getting the
ONE true diagnosis rather than the three-segment cascade". MEASURED, in BOTH field orders
and on BOTH trees:

  boxedc(v: zz4n.inner.rel, w: 1)                  1 error, 1 naming Relation[   control
  boxedc(v: <written call>, w: 1)                  3 errors, 0 naming Relation[  control
  boxedc(v: <written call>, w: zz4n.inner.rel)     3 errors, 0
  boxedc(v: zz4n.inner.rel, w: <written call>)     3 errors, 0

Two unrelated behaviours mask it: the typer reports ONE entity-field mismatch per atom
(`boxedc(v: <citation>, w: <citation>)` reports one, not two), and a written `field_access`
call's three per-leaf errors suppress the field diagnosis of every sibling — row four is
the proof, where the citation is FIRST and still says nothing. Row two against row three is
the decisive control: an atom with NO citation reports exactly what the collision reports,
so the bit's value changes no output in this shape. The figures are identical before and
after. Recorded in the new test file's header so the next reader does not re-derive it.

TESTS. New `wi_2sz88_entity_ctor_native_occurrence_test.rs` (registered in `wi_tests.rs`):
`a_nullary_op_in_an_entity_constructor_argument_is_a_call` DRIVES the capability and is the
one row that reddens when `entity_ctor_expr` is made to return `None`;
`the_reflect_half_still_needs_the_table` pins the residue and says in its own failure
message that it is the test to delete when 2NXAC lands. Stated at the site: the second is
green under the back-out BY DESIGN, and the dot-chain claim has no row because it needs the
change and the table varied together.

NOT DRIVEN, and said rather than implied: the effect-row-aux guard in the named loop
mirrors the generic arm's verbatim and I could not construct its shape (an effect-row
binding in an entity constructor's named argument in a rule body); it stays because the
alternative is a panic, not a wrong answer.

Workspace suite: 6343 passed, 0 failed over 36 binaries (baseline 6341 + the 2 new rows),
zero debug-assert firings.

### 2026-09-02T20:31:53Z — feedback — user

/code-review (high) FOUND FIVE; THREE WERE REAL REGRESSIONS I HAD SHIPPED. Each was
re-measured against the back-out before it was touched, and each now has its own test and
its own back-out axis.

(1) A POSITIONAL EFFECT-ROW AUX PANICKED THE LOADER. I put the `lower_effect_row_aux_occ`
guard on the NAMED loop only. A positional `ParseAux` under an entity head then reached
`unreachable!("Term::ParseAux reached build_body_atom_occurrence")`. MEASURED on
`rule rr(1) :- holds(Outer[k = Bx[{}]])`: baseline reports 2 located load errors, the first
cut PANICKED. Repair: one `Loader::lowered_child_occurrence` that BOTH loops go through, so
they cannot drift apart again — which is the actual lesson, since the asymmetry existed
only because I wrote the rule twice.

Worth recording against my own note on the previous pass: I had written at that site that I
could not drive the guard's shape. That was true of the NAMED loop and I generalised it to
the arm. The reviewer drove it — positionally.

(2) A BARE VALUE AT AN `Option` FIELD LOST ITS SPAN — WI-1035/1039's `1:1` back again. The
retain dropped every `wrap_bare_option_value`-transformed slot, and the reader then
materialized it with the TABLE-LESS `materialize_from_handle`. So the wrap was correct and
everything UNDER it was mislocated. MEASURED, same call at an Option field and a plain one:

  bo(v: fx("a")),  v: Option[T = Int64]    11:22 baseline -> 1:1 first cut -> 11:22 now
  bo2(v: fx("a")), v: Int64      control    7:23           ->  7:23        ->  7:23

Repair: keep every written origin (the retain is gone) and ROUTE at the reader — pass
through, or materialize the transformed child with ITS OWN subtree's span and dot-chain
tables. The identity check against `term_map` stays; it moved from a filter to a
three-way branch, which is where the decision is used.

(3) AN INLINE DESCRIPTION UNDER AN ENTITY HEAD WAS EMITTED TWICE. `entity_ctor_expr` calls
`convert_term` on the subtree (which emits `DescriptionInfo` for every described var) and
then recurses into the same children, whose `Var::Global` arm emits them again — that arm's
own comment says it exists only because generic atoms never call `convert_term`, and that
"entity / reflect-form atoms still emit via the `convert_term` call". `emit_desc_fact`
indexes per target, so the second run makes a DISTINCT fact. MEASURED: 2 with the change, 1
on the baseline, and the generic-atom control 1 either way. Repair: a saved/restored
`descs_emitted_by_convert` flag over the child walk.

(4) STALE DOC — `build_body_atom_occurrence`'s own header still said entity functors FALL
BACK "because a native rebuild would mint different [vars]". Rewritten: it now says
entities are native, why the fills are still read from the term, and that the 284 reflect
nodes are the remaining fallback.

(5) NOT FIXED, RECORDED AS A HOLE. The `Term::Ref` arm (a 0-field constructor folded by
`nullary_canon`) returns before the `Expr::Apply` tail, so it never calls
`build_recv_type` — a form-(3) receiver on a ZERO-FIELD constructor is still unconsumed and
still refused. An `Expr::Ref` has no slot to put one in, so this is not a one-line fix. Not
a regression (the round-trip consumed nothing either); noted at the site and handed to
WI-20260902-2NXAC, whose finding (2) owns the same channel.

TESTS ADDED for (1)(2)(3), each with a control that stays green: D
`a_positional_effect_row_under_an_entity_head_does_not_panic`, E
`a_bare_value_at_an_option_field_keeps_its_span` (plain-field control), F
`an_inline_description_under_an_entity_head_is_emitted_once` (generic-atom control).

FOUR BACK-OUT AXES, each run separately AND all three defects reintroduced together: with
2+3+4 in at once, exactly D, E and F fail and A and C pass — so no row is standing in for
another's defect. Recorded in the file header.

FINAL: workspace suite 6346 passed, 0 failed over 36 binaries (baseline 6341 + 5 new rows),
zero panics, zero debug-assert firings. `tests/include` registration invariant checked.

### 2026-09-03T07:07:07Z — feedback — user

REGRESSION IN THE DELIVERED WORK, FOUND AND FIXED AFTER THE FACT — AND IT WAS A SILENT
ACCEPTANCE, THE DIRECTION THIS TICKET FAMILY EXISTS TO PREVENT.

`entity_ctor_expr` called `self.build_recv_type(parse_id)`. I read the round-trip's silence
about `recv_type` as one of the three readings WI-20260902-2NXAC said that `return` drops,
and repaired it. FOR AN ENTITY HEAD THE SILENCE WAS THE REFUSAL WORKING.

A proposal-035 form-(3) companion receiver types the result of an OPERATION CALL. On an
entity constructor it is meaningless, and `check_unconsumed_recv_types` says exactly that —
"form (3) applies to an operation call, not to an entity constructor or a fact / rule
head". That sweep refuses every bracket nobody CONSUMED, so consuming one deletes the
refusal. MEASURED:

  rule cc(1) :- ?v <=> Bx[T = Int64].bx(k: 1)
     baseline            -> REFUSED, with that message
     2SZ88 as shipped    -> LOADS CLEAN
     fixed               -> REFUSED

WHY BOTH /code-review PASSES AND I MISSED IT: every fixture I built for this channel put
the bracket on an OPERATION (`Map[K = String].empty()`), where consuming it is right. The
constructor case is the same channel read at a different head, and nothing tested it. The
user asked what a form-(3) receiver actually IS; building the answer is what produced the
fixture that fails.

THE FIX is `recv_type: None` in `entity_ctor_expr`, with the reasoning at the site. The
NESTED case is unaffected and is a genuinely different node: `boxm(m: Map[…].empty())` puts
the bracket on `empty`, whose occurrence the child walk builds through the generic arm.
`a_form_three_receiver_type_under_a_literal_is_not_refused` covers that,
`a_form_three_receiver_on_a_constructor_is_refused` covers this, and the two disagree ON
PURPOSE — reading them as one channel is what produced the acceptance. Each has its own
control and each was backed out: the constructor row fails with `build_recv_type` restored,
the nested row stays green.

NOT FIXED, and now correctly classified: a form-(3) bracket on a ZERO-FIELD constructor
(`Bx[T = Int64].nada`) loads clean on EVERY tree INCLUDING the baseline — the bare name
never carries the bracket to the sweep. I had recorded this as a hole 2SZ88 left; it is
PRE-EXISTING and not this ticket's, and the earlier note saying `Expr::Ref` has no
`recv_type` slot described the wrong mechanism.

Workspace suite after the fix: 6350 passed, 0 failed.

