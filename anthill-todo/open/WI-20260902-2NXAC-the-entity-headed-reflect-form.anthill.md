## Attributes

- id: WI-20260902-2NXAC-the-entity-headed-reflect-form
- created: 2026-09-02T18:39:48Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T18:39:48Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE ENTITY-HEADED / REFLECT-FORM EARLY RETURN IN `build_body_atom_occurrence` LOSES THREE MORE READINGS, NOT JUST THE DOT-CHAIN BIT.

WI-20260902-4NEKZ's follow-up repaired ONE thing that arm drops (`dot_chain`, via `Loader::parse_dot_chain_table`). `/code-review` found three more losses at the SAME `return`, all pre-existing and none repaired. They share one root: the arm hands off to `materialize_from_handle_spanned`, which walks the KB TERM and so sees nothing the PARSE tree knew.

(1) WI-20260902-CZJ2N'S NULLARY-OPERATION CALL. `nullary_canon` folds `Fn{f,[],[]}` to `Term::Ref(f)`, and `visit_term`'s `Term::Ref` arm builds a plain `Expr::Ref` that `reduce_op_value` hands straight back un-reduced. MEASURED, definite answers:

  `rule c(1) :- seven <=> 7`                     -> 1
  `rule c(1) :- seven() <=> 7`                   -> 1
  `rule c(1) :- plus1(6) <=> 7`                  -> 1
  `rule c(1) :- [plus1(6)] <=> [7]`              -> 1
  `rule c(1) :- [seven] <=> [7]`                 -> **0**
  `rule c(1) :- [seven()] <=> [7]`               -> **0**
  `rule c(1) :- boxedva(x: seven) <=> boxedva(x: 7)` -> **0**

The tightest pair varies only nesting: `seven() <=> 7` answers 1, `[seven()] <=> [7]` answers 0, and `[plus1(6)]` proves nesting per se is fine. So the PARENTHESISED spelling is lost too, which means CZJ2N's "the census said zero, the population is new code only" understates its reach.

(2) PROPOSAL-035 FORM-(3) RECEIVER TYPES ARE FALSELY REFUSED. The native arm sets `recv_type: self.build_recv_type(parse_id)` and that call is what marks the parse node consumed. The early return calls neither it nor `consumed_recv_types.insert`, and `build_recv_type` has no call site reachable from inside a materialized subtree. So `rule r(1) :- ?v <=> [Map[K = String].empty()]` takes the early return (`ListLiteral` is in `is_reflect_form_functor`), the inner OPERATION call's `recv_type` is never consumed, and `check_unconsumed_recv_types` raises `InvalidTypeArgument` asserting the callee 'is not a call whose result it can type', about a callee that IS an operation call. Same for a form-(3) call in an entity-constructor argument in a rule body. PLAUSIBLE, not driven end to end; the shape is identical to the `dot_chain` loss just repaired at the same `return`.

(3) `substitute_occurrence` DROPS `dot_chain` ON `Expr::Apply` — the one variant that carries a chain. Its explicit arms (node_occurrence.rs 4967, 4989, 5009, 5025, 5054) rebuild with `new_expr` (hardcoded false), while the same function's `_` fall-through routes to `simp_rewrite::reassemble` -> `rebuilt_expr`, which DOES carry it. `rebuilt_expr`'s own doc names this population verbatim: 'A rebuild (De Bruijn open/close, SUBSTITUTION, `[simp]` reassembly) is the same node with new children; dropping the bit here would make a rule body's dot chain stop reading as one the first time the resolver opened it.' The trailing comment at 5083 enumerates the carried stamps and does not mention `dot_chain`, so the omission reads as decided when it is not.

RELATED, SAME CLASS, MEASURED SEPARATELY: a `[simp]` rule's RHS is spliced through `NodeOccurrence::synthesized_expr`, which also hardcodes `dot_chain: false`, so a citation in a simp RHS gets the per-leaf cascade AND reports it at the redex's span rather than the name's. `rule trig(?x) <=> sink(zzsimp.inner.rel) [simp]` with `operation consumer() -> Int64 = trig(5)` reports THREE errors all at the `trig(5)` call site, where the name does not appear. Controls: the same expression written directly in an op body reports ONE correct error; in a rule body ONE; the simp rule with NO consumer reports 0 (so all three come from the FIRE); a ONE-SEGMENT citation in the same fire reports ONE (so the fire does not lose name resolution in general).

SCOPE. Decide whether the fix is per-loss (three more tables threaded through the same walk) or structural — carry the PARSE `TermId` beside the term one through `WorkOp::Visit` so the materializer can ask the parse tree anything, which is also what WI-20260902-2SZ88-make-the-dot-chain-provenance needs to make the dot-chain answer exact rather than conservative. The structural option subsumes both and is the reason this is one ticket and not four.

Found by /code-review on the WI-20260902-4NEKZ follow-up, 2026-09-02. Every measurement above was run in this repo.

## Changes

### 2026-09-02T20:02:42Z — feedback — user

THE ENTITY HALF IS DONE (WI-20260902-2SZ88). WHAT IS LEFT IS THE REFLECT HALF, AND IT IS
0.22% OF THE POPULATION.

2SZ88 shipped `Loader::entity_ctor_expr`: a plain entity constructor's occurrence is now
built from its PARSE NODE, so it never reaches `materialize_from_handle_spanned` and
nothing about it has to be shipped in a `TermId`-keyed side table. The early return now
fires only for `is_reflect_form_functor`.

CENSUSED, whole workspace suite, the early return instrumented: 127 097 nodes took it.
126 813 (99.78%) were plain entity constructors and are now native. The RESIDUE this
ticket still owns is 284 nodes:

  ListLiteral   192
  dot_apply      49
  int_lit        10
  if_expr         9
  string_lit      2
  match_expr      2
  lambda_expr     2
  constructor     2
  apply           2
  var_ref, let_expr, float_lit, bool_lit   1 each

and ONE node that was not an entity at all (a `dot_apply`). SetLiteral and TupleLiteral do
not appear in the corpus at this position but are in `is_reflect_form_functor` and are
reached by `wi_4nekz_dotted_equation_operand_test`'s own rows.

PER-FINDING STATE.

(1) CZJ2N'S NULLARY CALL — HALF FIXED, MEASURED. The two ENTITY rows flip 0 -> 1:
`boxedva(x: seven) <=> boxedva(x: 7)` and its parenthesised spelling. The two LIST rows are
UNCHANGED at 0 (`[seven] <=> [7]`, `[seven()] <=> [7]`), with `[plus1(6)] <=> [7]` still 1
as the control that says nesting per se is fine. Those two rows are pinned by
`wi_2sz88_entity_ctor_native_occurrence_test::the_reflect_half_still_needs_the_table`,
whose failure message names THIS ticket and says it is the test to delete when this lands.

(2) FORM-(3) RECEIVER TYPES — HALF FIXED, NOT DRIVEN. `entity_ctor_expr` calls
`self.build_recv_type(parse_id)` exactly as the generic arm does, so an entity
constructor's receiver type is consumed and `check_unconsumed_recv_types` no longer
refuses it. The ticket's own example (`?v <=> [Map[K = String].empty()]`) is a LIST literal
and is untouched. Neither half has a driving test — the finding was PLAUSIBLE, not driven,
in the ticket, and it is still plausible-not-driven for the reflect half; the entity half
is now covered only by the suite staying green.

(3) `substitute_occurrence` DROPS `dot_chain` — UNTOUCHED. 2SZ88 changed nothing in
`node_occurrence.rs`'s substitution arms. Still five explicit arms (4967, 4989, 5009, 5025,
5054) rebuilding with `new_expr`, still a trailing comment at 5083 that enumerates the
carried stamps without mentioning this one. This is independent of the round-trip and can
be fixed on its own.

RELATED (the `[simp]` RHS through `synthesized_expr`) — UNTOUCHED, same reason.

SCOPE DECISION, ANSWERED. The ticket asked whether the fix is per-loss or structural.
Structural, and the structural move is NOT the parse-`TermId`-through-`WorkOp::Visit` both
tickets proposed: `materialize_from_handle` has 14 production callers that start from a
term with no parse node, so a parse id there is an `Option` at 14 of 16 readers. The move
that worked was to stop round-tripping at all — build the occurrence where the parse node
is. Doing the same for the reflect forms means giving `build_body_atom_occurrence_inner`
the arms `visit_fn` has for `ListLiteral` / `SetLiteral` / `TupleLiteral` and the
control-flow forms, reading invented structure (the WI-1096 cons/nil spine) from the
memoized `convert_term` the way `entity_ctor_expr` reads the entity fill. Start with the
three collection literals: they are 192 of the 284 and they carry every row 4NEKZ and this
ticket measure.

WATCH FOR: the lowering WRAPS written children as well as inventing whole ones
(`wrap_bare_option_value` at an `Option` field). 2SZ88's first cut missed that and felled
five `github_todo_test` rows. The repair there is an identity check against `term_map`, not
an enumeration of transforms; the same guard will be needed here.

