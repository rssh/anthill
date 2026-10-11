## Attributes

- id: WI-20261011-12VZB-a-constructor-written-with-all
- created: 2026-10-11T09:25:34Z

- status: Open
- status_agent: claude
- status_at: 2026-10-11T09:25:34Z

- acceptance: cargo-test

- tags: typing

## Description

A CONSTRUCTOR WRITTEN WITH ALL ITS ARGUMENTS NAMED, OUT OF DECLARATION ORDER, IN AN OPERATION BODY IS READ AS A DIFFERENT TERM FROM THE SAME VALUE WRITTEN IN ORDER. Measured 2026-10-11 on 8c535707 with the WI-20261011-CR6GD change in the tree; found while delivering it.

THE PROGRAM. `sort Pair` with `entity pair(a: Int64, b: Int64)`, `operation first(p: Pair) -> Int64`, `rule first(pair(a: ?a, b: ?b)) <=> ?a @[simp]`, `rule big(pair(a: ?a, b: ?b)) :- ?a > 3`, and `operation need(p: Pair) -> Int64 requires Pair.big(p) = p.a`. `Pair.first(Pair.pair(a: 7, b: 2))` runs to 7, and `need(Pair.pair(a: 7, b: 2))` loads and runs to 7. `Pair.first(Pair.pair(b: 2, a: 7))` loads clean and dies `OperationBodyMissing` — the equation did not fire — and `need(Pair.pair(b: 2, a: 7))` is a load error, "expected precondition `big(pair(b: 2, a: 7))` provable at the call site". One level down it is the same: with `sort Outer { entity wrap(p: Pair, n: Int64) }` and `rule inner(wrap(p: pair(a: ?a, b: ?b), n: ?n)) <=> ?b @[simp]`, `Outer.inner(Outer.wrap(n: 9, p: Pair.pair(7, 2)))` does not fire. The positional and mixed spellings (`pair(7, 2)`, `pair(7, b: 2)`, `pair(2, a: 7)`) were the same defect and are fixed with CR6GD.

MECHANISM. The canonical entity form is every argument named, in declaration order (docs/design/entity-term-mapping.md §2). The loader builds it for a rule text and the evaluator for a value (`finish_constructor`). An operation body keeps its node as written, and two readers take that node as a term before it is evaluated: the `@[simp]` matcher through its view (kb/term_view.rs `occ_head` / `occ_pos_child` / `occ_named_child` / `occ_named_keys`), and a call-site precondition through its term twin (`try_occurrence_to_term`). The discrimination tree descends named keys in the order the view gives them, so `pair(b:, a:)` and `pair(a:, b:)` are two shapes. CR6GD made view and twin canonical for a node that has a POSITIONAL argument (`node_occurrence::canonical_positional_ctor_args`), which is told off the node for nothing. An all-named node cannot be told from a canonical one without its field list.

WHAT, with the choice measured rather than assumed. (a) The same canonical reading for every `Expr::Constructor` with two or more named arguments: one `entity_field_names` lookup, a std `HashMap` probe, at every read of every such node — the `cons(head:, tail:)` cells a resolver goal holds included, which are canonical already and would pay for nothing. Measure a list-heavy resolution before choosing it. (b) A fact on the node, set where the node is built, that its named arguments are in declaration order: nothing at read, and the evaluator still runs the arguments in the order written. Every site that builds an `Expr::Constructor` owes it. (c) Reorder the node where the operation body is built: nothing at read, but the evaluator then runs the arguments in declaration order, and kernel-language.md states no order of argument evaluation — a spec question first. Whichever is taken, view and twin move together (WI-425).

NOT THIS TICKET. A constructor of no field written bare (`Color.code(red)` under `rule code(red) <=> 1 @[simp]`) is not matched either, though its precondition is proved: the node is a `var_ref` whose twin is the name and whose view is not, a difference kept on purpose at the lowering boundary (WI-592, WI-756). And an OPERATION application has no canonical spelling at all — `rule scale(?v, 1) <=> ?v @[simp]` fires on `scale(5, 1)` and not on `scale(v: 5, by: 1)` — which the spec calls structural matching.

CONTROL. The two programs above run to 7 and the nested one to 2, each failing on the tree before. The in-order named rows and the positional rows of `wi_cr6gd_clause_defined_call_test` pass either way, and so does a named tuple, whose written order is its identity. `term_view` `a_positional_constructor_reads_as_its_canonical_entity_and_as_its_twin` gains the out-of-order spelling. Neighbours: WI-20260827-T2470 (the evaluator half of the canonical form), WI-20260827-XFB56 (an under-applied constructor, another axis), WI-20260827-1F0QP (a mixed constructor PATTERN).

