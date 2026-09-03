## Attributes

- id: WI-20260902-2NXAC-the-entity-headed-reflect-form
- created: 2026-09-02T18:39:48Z

- status: Claimed
- status_agent: claude
- status_at: 2026-09-02T20:53:38Z

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

### 2026-09-02T22:16:50Z — feedback — user

DELIVERED: FINDING (1) FOR THE COLLECTION LITERALS. FINDINGS (2), (3) AND THE `[simp]`-RHS
RELATIVE REMAIN — SEE BELOW, THEY ARE NOT THE SAME KIND OF WORK.

WHAT SHIPPED. `Loader::collection_literal_expr` (+ `cons_spine_expr`) builds `[a, b]`,
`{a, b}` and `(a, b)` from their PARSE nodes, the way WI-20260902-2SZ88 did for entity
constructors. Those are 192 of the 284 reflect-keyed nodes that still took the early
return, and they carry every row this ticket and WI-20260902-4NEKZ measure.

Each surface pairs its lowered slots with its written children by its own rule — index for
a list or set, LABEL for a tuple (a tuple's labels are its identity, so the lowered order
may differ from the written one) — and every pair goes through
`Loader::lowered_child_occurrence`, the shared three-way rule 2SZ88 introduced. `[a, b]` is
the hard one: WI-1096 lowers it to a `cons`/`nil` spine, so the KB tree has MORE NODES than
the parse tree. `cons_spine_expr` walks spine and elements together; the cells and the
terminating `nil` are the lowering's own and are rebuilt, each `head` is a written element.

THE STRUCTURE IS UNCHANGED AND THAT WAS CHECKED, not assumed. A lowered list rebuilds as
`Expr::Apply` under `cons` with named head/tail — what `visit_fn`'s `_` arm produces — and
NOT the `Expr::Constructor` that `build_occurrence_cons_list` builds for the bare-`nil`
pattern convention. Those two shapes coexist deliberately and picking the wrong one would
silently change how a rule body's list matches. Verified by dumping the whole occurrence
tree for all three surfaces before and after: byte-identical except the one node this
ticket is about, `Expr::Ref(seven)` -> `Expr::Apply { seven }`.

MEASURED — EIGHT ROWS FLIP 0 -> 1, definite answers:

  seven <=> 7 / seven() <=> 7 / plus1(6) <=> 7     1 -> 1   controls
  boxedva(x: seven) <=> boxedva(x: 7)              1 -> 1   2SZ88's, still 1
  [plus1(6)] <=> [7]                               1 -> 1   control, the SPINE surface
  {plus1(6)} <=> {7}                               1 -> 1   control, the SET surface
  (plus1(6), 1) <=> (7, 1)                         1 -> 1   control, the TUPLE surface
  [seven] <=> [7]                                  0 -> 1
  [seven()] <=> [7]                                0 -> 1
  {seven} <=> {7}                                  0 -> 1
  {seven()} <=> {7}                                0 -> 1
  (seven, 1) <=> (7, 1)                            0 -> 1
  [[seven]] <=> [[7]]                              0 -> 1
  [boxedva(x: seven)] <=> [boxedva(x: 7)]          0 -> 1
  [seven, plus1(6)] <=> [7, 7]                     0 -> 1

THREE CONTROLS, ONE PER SURFACE, deliberately: the three take three different code paths
here, so one control would have covered one of them. The last three rows are the
recursion — a literal in a literal, an ENTITY in a literal (the two natives compose), and
a bare element BESIDE a written one, which is the row that fails if the spine walk pairs
by the wrong index.

AND THE DOT-CHAIN ROWS. With `parse_dot_chain_table` emptied, per row, before 2SZ88 ->
after 2SZ88 -> after this:

  zz4n.inner.rel = 7                 1 typed -> 1 typed -> 1 typed   control, never took the return
  boxed4n(v: zz4n.inner.rel) = 7     3, none -> 1 typed -> 1 typed
  [zz4n.inner.rel] = 7               3, none -> 3, none -> 1 typed
  {zz4n.inner.rel} = 7               3, none -> 3, none -> 1 typed
  (zz4n.inner.rel, 1) = 7            3, none -> 3, none -> 1 typed

── THE TABLE'S STATE, IN THREE PARTS ────────────────────────────────────────

I first wrote "the table has no reader the suite can reach", which was true and useless —
it does not distinguish a live guard with no coverage from inert code, and those want
opposite decisions. The user asked directly. Instrumented and measured:

  * STILL CALLED: 108 times over `wi_tests` — `dot_apply` 76, `int_lit` 12, `if_expr` 8,
    `lambda_expr` 4, the rest in ones and twos.
  * ALWAYS EMPTY: 0 of those 108 returned a non-empty set. NOT structurally dead though —
    a hand-written `?b.take(zz4n.inner.rel)` in a rule body (a citation as a `dot_apply`
    ARGUMENT) makes it `cited = 2`.
  * AND ITS RESULT CHANGES NOTHING REACHABLE: emptying it leaves the whole `wi_tests`
    binary green AND gives byte-identical diagnostics on that `cited = 2` program.

KEPT ON AN ASYMMETRY, NOT ON EVIDENCE OF USE, and the doc now says so: a lost diagnostic is
recoverable, a written `field_access` laundered into a name it does not spell is
WI-20260901-92VA4's silent acceptance and is not. The numbers and what to re-run before
deleting it are at `parse_dot_chain_table`.

── WHAT I COULD NOT DRIVE, SAID RATHER THAN GLOSSED ─────────────────────────

The other ~92 reflect-keyed nodes are not covered, and I could not build a fixture that
separates their behaviour from an unrelated one. `let` does not PARSE in a rule body. `if`
there answers 0 for EVERY variant — bare nullary, applied operation, plain integer literal
alike — so its 0 is another defect and a fixture on it would credit this ticket for a
repair it did not make. A `dot_apply` fixture I tried failed identically on all three rows
(the receiver read as a name), so it judged nothing. The rest reach a rule body only as
reflection PATTERNS, where a nullary-CALL reading is not the question. So the collection
literals MAY be the whole reachable residue of finding (1) — "may be" is the claim.

── /code-review FOUND A REGRESSION I HAD JUST INTRODUCED ────────────────────

INLINE DESCRIPTIONS EMITTED TWICE inside `[…]`, `{…}` and `(…)`. This is the SAME ROOT
CAUSE 2SZ88 hit and fixed for entity constructors: two walks over one subtree, and
`emit_desc_fact` indexes per target so the second makes a distinct fact. I added a second
two-walk function and did not set `descs_emitted_by_convert`. MEASURED: 2 for all three
literals, generic-atom control 1.

The repair is not just setting the flag. BOTH save/restores now wrap a SPLIT-OUT function
(`collection_literal_children`, `entity_ctor_children`) rather than a loop body, so a later
`return` inside cannot skip the restore — the structural version of the fix I should have
written the first time. New row
`an_inline_description_inside_a_literal_is_emitted_once`, and it reddens on its own axis.

ALSO FROM THE REVIEW, and taken further than reported: a `return None` in the pairing loop
fired AFTER the positional children were already built, so a bail would leave emitted
descriptions, consumed `recv_type`s and pushed diagnostics behind for the caller's
round-trip to repeat. Not drivable, so made STRUCTURAL instead of left unreachable — every
pairing is resolved before any child is built. The reviewer noted `entity_ctor_children`
has the mirror shape; I fixed that one too rather than only the site flagged.

NOT CHANGED, third finding: `lowered_child_occurrence` rebuilds the two tables per
transformed child where the round-trip built them once per atom. Perf only, invisible at
corpus size, noted here rather than at the site because it is a property of the shared
helper and not of this ticket.

── STILL OPEN ON THIS TICKET ────────────────────────────────────────────────

(2) FORM-(3) RECEIVER TYPES. The entity half is consumed (2SZ88's `build_recv_type` call);
the reflect half is not, and neither half has a driving test — the finding was PLAUSIBLE,
not driven, when filed and it still is. Plus 2SZ88's own hole: the `Term::Ref` arm (a
0-field constructor folded by `nullary_canon`) has no `recv_type` slot to put one in.

(3) `substitute_occurrence` DROPS `dot_chain` on five explicit arms. Untouched. NOTE FOR
WHOEVER TAKES IT: those arms use `NodeOccurrence::new_expr`, which also resets the
SYNTHESIZED ORIGIN — `occ.rebuilt_expr(expr)` carries both plus the typer stamps and is a
five-line change. But the only consumer of the bit is `typing.rs`'s
`loader_chain_dotted_name` guard, and every `substitute_occurrence` caller is in
`kb/mod.rs` / `kb/resolve.rs` — i.e. AFTER typing. So check drivability before assuming it
is observable.

RELATED, THE `[simp]` RHS. Its measurement REPRODUCES EXACTLY: `rule trig(?x) <=>
sink(zzsimp.inner.rel) [simp]` with a consumer reports THREE errors all at one offset; no
consumer reports 0 (so all three come from the FIRE); the same expression in an op body
reports 1, in a rule body 1, and a ONE-SEGMENT citation in the same fire 1. TRACED: the
cause is `simp_rewrite::subst_visit`, which resolves the RHS from a TERM
(`kb.walk_view(term, subst)`) and rebuilds occurrences with `synthesized_expr` — A THIRD
TERM->OCCURRENCE ROUND-TRIP, the same defect class as 2SZ88 and this ticket, in a different
walk. `synthesized_expr` hardcodes `dot_chain: false` DELIBERATELY (a synthesis is not the
author's dot), so the fix is not to change that constructor: it is for the simp rule to
keep its RHS OCCURRENCE instead of re-deriving it from the term. That is its own ticket's
worth of work.

Workspace suite: 6348 passed, 0 failed over 36 binaries.

### 2026-09-03T04:27:27Z — feedback — user

FINDING (3) CHECKED. IT IS CORRECT AS CODE-READING AND WAS INERT IN FACT — AND THE SAME
FIVE ARMS HELD A DIFFERENT, LIVE DEFECT THE TICKET DOES NOT NAME.

THE TICKET'S CLAIM, MEASURED. Instrumented `substitute_occurrence` and ran `wi_tests`:

  chain-bearing nodes reaching the five explicit arms      16
  of those, ACTUALLY rebuilt (i.e. the bit really lost)     0

And the 0 is STRUCTURAL, not luck. A citation node is `field_access(Ref(ns), Ident(rel))` —
`loader_chain_dotted_name` requires both children to be names — and `push_unknown_fn`
builds it with `type_args: []` and `recv_type: None`. `substitute_occurrence` rewrites only
`Expr::Var(Global)` leaves, so none of `c1..c4` can be true for such a node; `rebuilt` is
always `None` and `unwrap_or_else(|| Rc::clone(occ))` returns the ORIGINAL, bit intact.

So the ticket is right that the arm WOULD drop it and wrong that anything reaches it in a
state where that matters. Filing it was still correct — "the omission reads as decided when
it is not" was the point, and it was not decided.

THE LIVE DEFECT BESIDE IT. Those arms build with `NodeOccurrence::new_expr`, which also
resets a `Synthesized` ORIGIN to `Source`. That has NO equivalent protection — a synthesized
node can freely have a child that changes. MEASURED, same run:

  nodes actually rebuilt by the five arms                  20
  of those, `Synthesized` (i.e. provenance chain reset)    20  — all of them

The readers of that chain are `simp_rewrite`'s two `OccurrenceOrigin::Synthesized` matches
and `source_head_name`'s walk (WI-20260820-5R2XT, "the name the AUTHOR wrote at this call
site, when a MACRO lowered it into a call to something else").

ONE CHANGE COVERS BOTH: the five arms now build with `occ.rebuilt_expr(expr)`, which carries
the origin, the `dot_chain` bit and the typer stamps. That let the function's tail lose its
separate `carry_typer_stamps_from` pass entirely — it is a plain
`rebuilt.unwrap_or_else(|| Rc::clone(occ))` now, and the `_` arm's `reassemble` (which
always carried all three) no longer needs special-casing beside it.

NEITHER IS DRIVABLE, AND THAT IS STATED RATHER THAN GLOSSED. With the switch in, the
workspace suite is 6348 passed / 0 failed — byte-identical to without it. NO TEST WAS
ADDED, because a test that passes both ways measures nothing (and would be the exact
mistake this ticket's own file warns about). The change is made correct BY CONSTRUCTION and
the two numbers are recorded at the site, replacing a comment that asserted the arms only
needed their stamps carried.

WHY NOT LEAVE IT ALONE, since neither loss is observable: the dot_chain half is safe by an
invariant that would die the moment a chain could contain a variable or carry a type
argument, and the ORIGIN half is a live loss today whose reader simply is not exercised.
`rebuilt_expr` costs nothing over `new_expr` and removes both, so the cheaper option is the
one that does not need the invariant to keep holding.

WHAT REMAINS ON THIS TICKET AFTER THIS: finding (2) only, plus the `[simp]`-RHS relative.

### 2026-09-03T05:21:27Z — feedback — user

FINDING (2) WAS ALREADY FIXED — BY BOTH NATIVE ARMS, NEITHER AIMED AT IT — AND IS NOW
DRIVEN. The ticket filed it as PLAUSIBLE, NOT DRIVEN END TO END. I nearly shipped it the
same way; the user asking "what is finding 2" is what got it measured.

THE MECHANISM. Proposal 035 form (3) writes a companion receiver's type on an operation
call (`Map[K = String, V = Int64].empty()`). `build_recv_type` reads the bracket AND marks
the parse node consumed; `check_unconsumed_recv_types` then sweeps every node still
carrying an unread one and refuses it. The round-trip called neither — the sweep therefore
refused a form-(3) call nested in a literal or an entity argument, asserting the callee "is
not a call whose result it can type" about a callee that IS an operation call.

Both native arms repair it as a side effect: every child now goes through
`build_body_atom_occurrence`, whose generic-application arm reads `build_recv_type`.

MEASURED — load errors matching "not read here", baseline -> with both arms:

  ?v <=> Map[…].empty()                  0 -> 0   control, never took the early return
  ?v <=> [Map[…].empty()]                1 -> 0   the ticket's own example
  ?v <=> {Map[…].empty()}                1 -> 0
  ?v <=> (Map[…].empty(), 1)             1 -> 0
  ?v <=> boxm(m: Map[…].empty())         1 -> 0   the ENTITY arm, WI-20260902-2SZ88's half

`a_form_three_receiver_type_under_a_literal_is_not_refused` covers all five and reddens on
four when either arm is backed out, so ONE test covers both tickets' halves. The bare row
is green either way by design.

STILL OPEN on this finding, and stated in the test rather than left to look total: a
form-(3) receiver on a ZERO-FIELD constructor. `entity_ctor_expr`'s `Term::Ref` arm (the
`nullary_canon` fold) returns before the `Expr::Apply` tail and an `Expr::Ref` has no
`recv_type` slot, so that one shape is still unconsumed. Not driven; recorded at the arm.

── /code-review (2nd pass) FOUND NO CORRECTNESS BUG ─────────────────────────

It independently drove the two `entity_slot_origin` write sites my tests do NOT cover — the
`some(x)` positional coercion and WI-433's `PositionalPlan::Assign` — and both report at
the written column, no `1:1`. It also confirmed duplicate tuple labels are refused at PARSE
time, so `collection_literal_children`'s first-match pairing cannot mis-pair.

FOUR LOW FINDINGS, ALL ADDRESSED:

1. `collection_literal_expr` allocated a `String` for the form key BEFORE testing it. That
   arm is the `else` of the entity gate, so it runs for every non-entity `Term::Fn` in
   every rule body — 127 097 nodes over one workspace load — and nearly all fail the test.
   Now tested on the borrowed slice, owned only on a hit.

2. The `-} +} else {` restructure left the ~100-line generic-application arm at its old
   indentation, which is the one hunk where control flow actually changed. NOT fixed with
   `cargo fmt`, which the finding suggested: `load.rs` is not rustfmt-clean and formatting
   it emits a 6 556-line unrelated diff. Re-indented the 101 lines of the block instead.

3. `cons_spine_expr`'s `cells: Vec<(TermId, TermId)>` never read its second element, and
   the `cells.is_empty()` half of its guard is unreachable (an empty spine is the bare
   `nil`, which the caller returns on). Dropped to `Vec<TermId>`, and the unreachability is
   STATED rather than guarded — a guard that cannot fire reads as a case someone handled.

4. THE ONE WORTH THE MOST. `entity_slot_origin` is WRITTEN gated on `entity_field_names` of
   the UN-ROUTED functor and READ gated on the same predicate applied to the ROUTED one, so
   the two sites ask about two different symbols and the reader's `debug_assert!(false, …)`
   PANICS every debug build if they disagree. They cannot today — routing maps only
   `POSITION_DIRECTED_BOOLEANS` (`Bool.not`/`or`/`and`), none with a field schema — but that
   coupling was written nowhere. It is now, at both ends, naming what a future entry in that
   table would break.

Workspace suite: 6349 passed, 0 failed over 36 binaries.

── WHAT REMAINS ─────────────────────────────────────────────────────────────

Findings (1), (2) and (3) are done as far as anything reachable goes. What is left is the
`[simp]`-RHS relative, and it is a DIFFERENT ticket's shape: `simp_rewrite::subst_visit`
resolves a fired rule's RHS from a TERM (`kb.walk_view`) and rebuilds occurrences with
`synthesized_expr` — A THIRD TERM->OCCURRENCE ROUND-TRIP. Its measurement reproduces
exactly (3 errors at one offset, 0 with no consumer, 1 for each direct spelling, 1 for a
one-segment citation in the same fire). `synthesized_expr` hardcodes `dot_chain: false`
DELIBERATELY — a synthesis is not the author's dot — so the fix is not that constructor: it
is for a `[simp]` rule to keep its RHS OCCURRENCE instead of re-deriving it from the term.

