## Attributes

- id: WI-20261011-12VZB-a-constructor-written-with-all
- created: 2026-10-11T09:25:34Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-11T12:14:14Z

- acceptance: cargo-test

- tags: typing

## Description

A CONSTRUCTOR WRITTEN WITH ALL ITS ARGUMENTS NAMED, OUT OF DECLARATION ORDER, IN AN OPERATION BODY IS READ AS A DIFFERENT TERM FROM THE SAME VALUE WRITTEN IN ORDER. Measured 2026-10-11 on 8c535707 with the WI-20261011-CR6GD change in the tree; found while delivering it.

THE PROGRAM. `sort Pair` with `entity pair(a: Int64, b: Int64)`, `operation first(p: Pair) -> Int64`, `rule first(pair(a: ?a, b: ?b)) <=> ?a @[simp]`, `rule big(pair(a: ?a, b: ?b)) :- ?a > 3`, and `operation need(p: Pair) -> Int64 requires Pair.big(p) = p.a`. `Pair.first(Pair.pair(a: 7, b: 2))` runs to 7, and `need(Pair.pair(a: 7, b: 2))` loads and runs to 7. `Pair.first(Pair.pair(b: 2, a: 7))` loads clean and dies `OperationBodyMissing` — the equation did not fire — and `need(Pair.pair(b: 2, a: 7))` is a load error, "expected precondition `big(pair(b: 2, a: 7))` provable at the call site". One level down it is the same: with `sort Outer { entity wrap(p: Pair, n: Int64) }` and `rule inner(wrap(p: pair(a: ?a, b: ?b), n: ?n)) <=> ?b @[simp]`, `Outer.inner(Outer.wrap(n: 9, p: Pair.pair(7, 2)))` does not fire. The positional and mixed spellings (`pair(7, 2)`, `pair(7, b: 2)`, `pair(2, a: 7)`) were the same defect and are fixed with CR6GD.

MECHANISM. The canonical entity form is every argument named, in declaration order (docs/design/entity-term-mapping.md §2). The loader builds it for a rule text and the evaluator for a value (`finish_constructor`). An operation body keeps its node as written, and two readers take that node as a term before it is evaluated: the `@[simp]` matcher through its view (kb/term_view.rs `occ_head` / `occ_pos_child` / `occ_named_child` / `occ_named_keys`), and a call-site precondition through its term twin (`try_occurrence_to_term`). The discrimination tree descends named keys in the order the view gives them, so `pair(b:, a:)` and `pair(a:, b:)` are two shapes. CR6GD made view and twin canonical for a node that has a POSITIONAL argument (`node_occurrence::canonical_positional_ctor_args`), which is told off the node for nothing. An all-named node cannot be told from a canonical one without its field list.

WHAT, with the choice measured rather than assumed. (a) The same canonical reading for every `Expr::Constructor` with two or more named arguments: one `entity_field_names` lookup, a std `HashMap` probe, at every read of every such node — the `cons(head:, tail:)` cells a resolver goal holds included, which are canonical already and would pay for nothing. Measure a list-heavy resolution before choosing it. (b) A fact on the node, set where the node is built, that its named arguments are in declaration order: nothing at read, and the evaluator still runs the arguments in the order written. Every site that builds an `Expr::Constructor` owes it. (c) Reorder the node where the operation body is built: nothing at read, but the evaluator then runs the arguments in declaration order, and kernel-language.md states no order of argument evaluation — a spec question first. Whichever is taken, view and twin move together (WI-425).

NOT THIS TICKET. A constructor of no field written bare (`Color.code(red)` under `rule code(red) <=> 1 @[simp]`) is not matched either, though its precondition is proved: the node is a `var_ref` whose twin is the name and whose view is not, a difference kept on purpose at the lowering boundary (WI-592, WI-756). And an OPERATION application has no canonical spelling at all — `rule scale(?v, 1) <=> ?v @[simp]` fires on `scale(5, 1)` and not on `scale(v: 5, by: 1)` — which the spec calls structural matching.

CONTROL. The two programs above run to 7 and the nested one to 2, each failing on the tree before. The in-order named rows and the positional rows of `wi_cr6gd_clause_defined_call_test` pass either way, and so does a named tuple, whose written order is its identity. `term_view` `a_positional_constructor_reads_as_its_canonical_entity_and_as_its_twin` gains the out-of-order spelling. Neighbours: WI-20260827-T2470 (the evaluator half of the canonical form), WI-20260827-XFB56 (an under-applied constructor, another axis), WI-20260827-1F0QP (a mixed constructor PATTERN).

## Changes

### 2026-10-11T12:14:13Z — feedback — claude

DELIVERED 2026-10-11 — A CONSTRUCTOR WRITTEN ALL NAMED, OUT OF DECLARATION ORDER, IS READ IN THE CANONICAL ENTITY FORM (commit 5c7657a0). The two programs of the description run to 7 and the nested one to 2.

THE CHOICE, MEASURED AS THE TICKET ASKED: (a), the declaration order asked where the order is read, with nothing kept on the node. The cost the ticket feared is not there. The order reaches two readers only, the key list (occ_named_keys) and the term twin (try_occurrence_to_term): the head counts and a child is found by name. Counted with a temporary counter in the CLI: the key reader meets a constructor node of two or more named arguments 44 times in a load of the standard library and 188 times with anthill-todo's sources, and not once more under a resolution over thirty-element lists — a rule body's cons(head:, tail:) is the loader's canonical application, not an Expr::Constructor. (b), a fact on the node, would be owed by each of the twenty-odd sites that build one and wrong in silence at the one that forgets. (c) would run the arguments in declaration order. docs/design/entity-term-mapping.md §2 has the table.

WHAT CHANGED. node_occurrence::canonical_ctor_args (renamed from canonical_positional_ctor_args) answers for an all-named node too, gated by KnowledgeBase::named_out_of_declared_order (kb/resolve.rs): two or more named arguments, a field schema, not already in declaration order. A functor with no schema is left as written, as the load leaves a rule's text; a named tuple keeps its written order. The node is not touched: its arguments are evaluated in the order written.

CONTROLS, each measured by back-out; the header of wi_12vzb_constructor_named_out_of_order_test has the lists. The gate answering false: nine rows fail (seven dying OperationBodyMissing, two on the precondition) and the sealed row; five pass either way by design. The view's key order alone as written: the seven equation rows. The twin alone: the two precondition rows. term_view's unit row (renamed a_constructor_reads_as_its_canonical_entity_and_as_its_twin) gains the spelling and fails on its key order. No operation body in the standard library, the examples or anthill-todo writes such a constructor, counted where the node is built (0 of 15, 27 and 75 with two or more named arguments).

WHAT ELSE IT MOVED: behind a seal a later load's @[simp] rule headed by a constructor is refused where a sealed body writes that construction out of order (wi_9bkz4_sealed_bodies_test, one new row).

FOUND ON THE WAY, on the row that runs the call at every site an operation body writes one. (1) FIXED, in its own commit (a2ab1619): a match arm's GUARD was typed and the written one put back into the stored body. An equation fired in a guard in no spelling (case mk(v: n) | dbl(n) > 3 loaded clean and died OperationBodyMissing), and a dot call in a guard was a load error, 'no such member (dot dispatch)', about an operation the sort declares. The typed guard is stored now (typing/build.rs); the arm still assumes the guard as written. Rows: wi_12vzb_match_guard_stored_as_typed_test, and two more in wi_9bkz4_sealed_bodies_test. (2) NOT CHANGED, asked of the user and not filed: a const's VALUE is checked with no equation applied (typing/sorts.rs check_constant_bodies, 'without simp write-back'), so const c: Int64 = dbl(4) loads clean and dies at first use, in every spelling; kernel-language.md §5.3 does not list a const among the firing sites. (3) OBSERVED, not investigated: if Box.isBig(b) then need(b) else 0 is refused where need requires Box.isBig(b) and isBig is a bodied Bool operation, before this change and after.

SPEC. Not edited. §8's table of constructor arguments shows the positional, named and mixed spellings and does not say that named arguments may be written in any order; a row for it was proposed to the user.

RUNS. Full workspace at each commit: 36 binaries, 9178 passed at 5c7657a0 and 9188 at a2ab1619, 0 failed. anthill-core under ANTHILL_TYPER_ORACLE=1, ANTHILL_TEST_TWO_STEP_LOAD=1 and ANTHILL_TEST_FRESH_LOAD=1: 8290 passed, 0 failed, each. /code-review run: nine findings, seven fixed, two needing no change.

