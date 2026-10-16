## Attributes

- id: WI-20261016-HE2J6-a-call-s-result-is-not-a-fresh
- created: 2026-10-16T12:47:13Z

- status: Open
- status_agent: user
- status_at: 2026-10-16T12:47:13Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A call's result is not a fresh region: a write to a value an ordinary call or a callback returned is dropped as a write to a fresh local, though the value may be (part of) an input, or a cell a closure holds.

MEASURED 2026-10-16 — each loads typed PURE while writing a cell its caller holds:
(1) the typer's local masking (WI-314, region::external_effects): operation h4(l: List[T = Cell[V = Int64]], d: Cell[V = Int64]) -> Unit = (let x = first(l, d); Cell.set(x, 1)), where `first` returns an element of `l` or `d` itself.
(2) the flow analysis's `fresh_output` provenance (proposal 046, stdlib/anthill/reflect/feed.anthill): via(l, g, f) = match l case cons(h, _) -> f(g(h)), called with g = lambda x -> x, writes an element of `l`; use_fresh(d, mk, f) = (let c = mk(); f(c); d), called with mk = lambda () -> d, writes `d`; a fold step (a, t) -> t makes the accumulator an element of `xs`, which the WI-353 answer {Modify[z], Modify[result]} omits.

EXPECTED: such a write is kept — re-keyed onto the inputs the value may come from (at least every modifiable input, as the boundary already does for a callback place the flow pass did not trace), and refused where nothing of the operation can name it (a cell only a closure holds).

WHERE TO LOOK: region::external_effects (the let/match-bound local drop); region::op_boundary_effects with feed.keep_modify's two fresh_output rules; flow_derive::apply_callback (a callback's value is its result place). wi341_callback_modify_test::a_thunks_output_that_stays_local_drops_while_it_counts_as_fresh pins today's verdict and flips with this. Design: docs/design/modify-effect-derive.md §"A drop needs evidence" (its last paragraph).

