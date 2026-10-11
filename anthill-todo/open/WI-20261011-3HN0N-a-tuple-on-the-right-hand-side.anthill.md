## Attributes

- id: WI-20261011-3HN0N-a-tuple-on-the-right-hand-side
- created: 2026-10-11T06:33:38Z

- status: Open
- status_agent: claude
- status_at: 2026-10-11T06:33:38Z

- acceptance: cargo-test

- tags: typing

## Description

A TUPLE ON THE RIGHT-HAND SIDE OF A `@[simp]` EQUATION LOADS CLEAN AND DIES IN EVAL WITH AN INTERNAL ERROR. Measured 2026-10-11 on fb862725; found while delivering WI-20261011-RM247.

THE PROGRAM. In one namespace: `operation both(a: Int64) -> (Int64, Int64)`, `rule both(?a) <=> (?a, ?a) @[simp]`, `operation fstof(p: (Int64, Int64)) -> Int64 = p._1`, `operation go() -> Int64 = fstof(both(4))`. It loads with no diagnostic and `go()` fails 'internal evaluator error: unhandled Expr variant in eval: Discriminant(13)'. The same with a named tuple (`-> (x: Int64, y: Int64)`, `<=> (x: ?a, y: ?a)`, read with `p.x`) and with the tuple under a constructor (`-> Option[T = (Int64, Int64)]`, `<=> some((?a, ?a))`). The twin with the tuple written in the operation's own body, `operation both(a: Int64) -> (Int64, Int64) = (a, a)`, runs to 4.

MECHANISM, as far as read. A tuple written in an operation body is lowered by the loader to a constructor node over `anthill.reflect.TupleLiteral`, which eval constructs. A rule's text keeps it as the tuple node (`Expr::TupleLit`), and that node is what a fired equation splices into the operation body (`simp_rewrite::build_rhs_template`). The typer types it; eval lists `TupleLit` among the variants it has no reading for (eval/eval.rs, beside `ListLit`, `SetLit`, `DotApply`). fb862725 closed the same gap for a constructor applied on a right-hand side — an application node headed by a constructor, which eval now constructs — and did not reach this one: a tuple's positional order is its identity (`finish_constructor`'s note on the literal forms), so what the node becomes has to agree with what the loader builds for the same text.

WHAT. One reading of a tuple for an operation body, whichever text it came from: either the splice hands an operation body the node the loader would have built, which also covers every other reader of rewritten bodies (the C++ and Rust generators read them and were not driven on one), or eval reads the tuple node. A list literal on a right-hand side already runs (`<=> [?a, ?a]`, length 2); a set literal was not measured.

CONTROL. The three programs as rows asserting 4: each fails on the tree before, dying in eval. The body-written twin passes either way. A value built through a rewritten tuple compares equal to the one the body-written twin builds.

