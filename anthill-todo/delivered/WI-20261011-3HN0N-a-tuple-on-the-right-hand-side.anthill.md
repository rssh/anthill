## Attributes

- id: WI-20261011-3HN0N-a-tuple-on-the-right-hand-side
- created: 2026-10-11T06:33:38Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-11T17:53:38Z

- acceptance: cargo-test

- tags: typing

## Description

A TUPLE ON THE RIGHT-HAND SIDE OF A `@[simp]` EQUATION LOADS CLEAN AND DIES IN EVAL WITH AN INTERNAL ERROR. Measured 2026-10-11 on fb862725; found while delivering WI-20261011-RM247.

THE PROGRAM. In one namespace: `operation both(a: Int64) -> (Int64, Int64)`, `rule both(?a) <=> (?a, ?a) @[simp]`, `operation fstof(p: (Int64, Int64)) -> Int64 = p._1`, `operation go() -> Int64 = fstof(both(4))`. It loads with no diagnostic and `go()` fails 'internal evaluator error: unhandled Expr variant in eval: Discriminant(13)'. The same with a named tuple (`-> (x: Int64, y: Int64)`, `<=> (x: ?a, y: ?a)`, read with `p.x`) and with the tuple under a constructor (`-> Option[T = (Int64, Int64)]`, `<=> some((?a, ?a))`). The twin with the tuple written in the operation's own body, `operation both(a: Int64) -> (Int64, Int64) = (a, a)`, runs to 4.

MECHANISM, as far as read. A tuple written in an operation body is lowered by the loader to a constructor node over `anthill.reflect.TupleLiteral`, which eval constructs. A rule's text keeps it as the tuple node (`Expr::TupleLit`), and that node is what a fired equation splices into the operation body (`simp_rewrite::build_rhs_template`). The typer types it; eval lists `TupleLit` among the variants it has no reading for (eval/eval.rs, beside `ListLit`, `SetLit`, `DotApply`). fb862725 closed the same gap for a constructor applied on a right-hand side — an application node headed by a constructor, which eval now constructs — and did not reach this one: a tuple's positional order is its identity (`finish_constructor`'s note on the literal forms), so what the node becomes has to agree with what the loader builds for the same text.

WHAT. One reading of a tuple for an operation body, whichever text it came from: either the splice hands an operation body the node the loader would have built, which also covers every other reader of rewritten bodies (the C++ and Rust generators read them and were not driven on one), or eval reads the tuple node. A list literal on a right-hand side already runs (`<=> [?a, ?a]`, length 2); a set literal was not measured.

CONTROL. The three programs as rows asserting 4: each fails on the tree before, dying in eval. The body-written twin passes either way. A value built through a rewritten tuple compares equal to the one the body-written twin builds.

## Changes

### 2026-10-11T17:53:34Z — feedback — user

DELIVERED in f9654e00. THE TYPER READS A COLLECTION LITERAL OF A RULE'S TEXT AS THE CONSTRUCTOR AN OPERATION BODY WRITES, and the typed body keeps it (`typing::literal_as_constructor`, a guarded first arm of `visit_type`). The three programs of the ticket run to 4, and each value compares equal to the one the body-written twin builds.

WHY THE TYPER, AND NOT THE SPLICE OR EVAL. Measured before choosing. (1) A tuple reaches an operation body by two routes, not one: as the equation's own right-hand side, and as the value its guard bound a variable to (`rule bg: both(?a) = ?p :- pairof(?a, ?p) @[simp]` over `pairof(4, (4, 5))`, and `:- ?p <=> (?a, 5)`). The second arrives through the binding, after the template is built, so a lowering of the template in `build_rhs_template` does not see it. (2) Typing differs between the two nodes, so a reading in eval alone leaves a refusal: `rule both(?a) <=> () @[simp]` under `-> Unit` was refused at load, 'expected Unit, got ()' — the literal's frame types an empty tuple as a tuple of no components and takes no expected type, where the constructor's check gives `Unit` and threads the expected components. (3) The set and the flat list die the same way: `<=> {?a, 5}`, `<=> ListLiteral(?a, 5)`, and `<=> H.holder([?a, 5])` where the field is a `Stream` (a position that declares another collection, so the loader does not lower it to the spine). All three nodes are read.

WHICH TEXT. The reading is made where the text is written as an operation body is: an operation's body, a const's value, and what stands under a compound expression of a rule body (lambda, if, let, match, in-body proof) — the loader builds the three with one walk and writes constructors there. A lambda in a rule body that called such an operation killed the query (panic in `bridge_op_to_eval`), and one returning the `Unit` an equation leaves was refused at load ('expected Function[A = Int64, B = Unit], got Int64 -> ()'); both answer. `TypingEnv.rule_body_dispatch` is now `Option<RuleText>` (Term / Expression) and `TypingEnv::under` is asked at both descents into a rule body's node: the typer's visit, and the rule-body walk's recursion, which enters an `if` itself. No row drives the second — said at the line: an `if` written in a rule body is not evaluated. A rule body's own term is untouched.

CONTROLS, wi_3hn0n_tuple_on_rhs_test, 37 rows. With the reading backed out 31 fail: 26 load clean and die in eval on the literal's node, 2 are refused at load for `Unit`, 3 die in the resolver's bridge. 6 pass either way by design (the body-written twin, a `[…]` lowered to its spine, a tuple a rule body writes as an argument, a lambda a rule body writes, a tuple in a goal matched against facts, a rule body's own `()`). With the reading made everywhere the typer meets the node, the whole workspace passes but two: a_rule_bodys_own_empty_tuple_is_typed_as_before (the goal loads, its `()` typed `Unit`) and wi285_unrec_test::collection_literal_frames_assemble_types, restated here to type the three nodes as a rule body's own term, with a second row for the same nodes in an operation body.

GENERATORS. The C++ generator lowered the literal's node as it lowers the constructor: its header for a sort calling `both` is the same text before and after (`return {4, 4};`), and `mk{4}` for a rewritten constructor application. Not a row. The Rust generator does not lower bodies.

GATE on f9654e00: rustland/scripts/test.sh, full: 36 binaries, 9314 passed, 0 failed. /code-review run at xhigh: 11 findings, 8 fixed, 3 not applied (the first of FOUND below; a third site that mints a literal's constructor; rule text made runnable at two layers, eval for a constructor application and the typer for a literal). No spec text changed; scaland has no typer and nothing mirrors this.

FOUND ON THE WAY, each measured before and after this change with the same answer, NOT FIXED, no ticket filed. (a) `()` IS `Unit` ONLY WHERE IT IS WRITTEN AS AN OPERATION BODY IS. `fact U.u(v: (), n: 4)` over `entity u(v: Unit, n: Int64)` is refused 'expected Unit, got TupleLiteral'; the goal `U.u(v: (), n: ?r)` is refused 'expected Unit, got ()'; and `rule value(?r) :- ?r <=> takes(Box.mk(4).nothing(), 4)` with `rule nothing(?b) <=> () @[simp]` is refused the same way where its operation-body twin now runs — the slot check reads the argument's type through the structural value-type reader, which also says `()`. (b) AN `if` WRITTEN AS AN ARGUMENT IN A RULE BODY IS NOT EVALUATED: `rule value(?r) :- ?r <=> fstof((if 1 = 1 then (4, 5) else (6, 7)))` panics in `bridge_op_to_eval`, 'field_access: entity has no field _1'; no equation involved. (c) A RULE BODY CALLING AN EQUATION-DEFINED OPERATION OF A SORT WITH NO PARAMETER LEAVES A RESIDUAL where the parametric sort answers: with `operation open(b: Box) -> Int64`, `rule open(?b) <=> peek(?b) @[simp]`, `rule value(?x) :- ?x <=> Box.open(Box.mk(4))` answers '?x = ?_, residual unify(?_, open(mk(v: 4)))'; the same with `sort V = ?` answers 4 (wi_rm247's a_rule_body_reaches_it). (d) THE C++ GENERATOR EMITS `p._1` FOR A FIELD READ OFF A TUPLE, over `std::tuple<int64_t, int64_t>`: `operation fstof(p: (Int64, Int64)) -> Int64 = p._1` becomes `return p._1;`. (e) LOAD ERRORS OF OPERATIONS AT NAMESPACE LEVEL COME IN NO FIXED ORDER: two runs of one load printed the same two errors in two orders (`op_bodies_iter` is a hash map's order). (f) THE PRINTER WRITES A TUPLE OF AN OPERATION BODY BY ITS ENTITY'S NAME, `TupleLiteral(_1: a, _2: b)`, and a rule's own as `(_1: a, _2: b)`. (g) READ, NOT DRIVEN: `body_specialize` answers a definite non-match for a tuple pattern against a scrutinee that is the tuple's constructor node (`occ_head_ctor` is `Some` for it), which is what an operation body writes.

