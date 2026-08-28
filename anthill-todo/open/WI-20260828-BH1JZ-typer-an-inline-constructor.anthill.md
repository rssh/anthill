## Attributes

- id: WI-20260828-BH1JZ-typer-an-inline-constructor
- created: 2026-08-28T15:35:04Z

- status: Open
- status_agent: user
- status_at: 2026-08-28T15:35:04Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

typer: an INLINE constructor application whose only consumer is a SPEC-OP CALL does not ground its own sort params. MEASURED MATRIX, stdlib carriers, four rows that bracket it exactly: (1) `operation probe(xs: List[T = Int64]) -> MappedStream[Source = List[T = Int64], Src = Int64, T = Int64, ES = {}, EF = {}] = mapped(xs, inc)` — CLEAN, the declared return pins every param; (2) the same construction consumed by `Stream.splitFirst(mapped(xs, inc))` — REFUSED with `Stream.splitFirst.dispatch: expected matching impl for per-call bindings, got no impl matches`; (3) consumed by `FiniteCollection.collect(mapped(xs, inc))` — REFUSED with `undeclared effect ??_`; (4) the SAME witness consumer fed an ALREADY-TYPED carrier (`operation probe(m: MappedStream[Source = List[T = Int64], …]) = FiniteCollection.collect(m)`) — CLEAN. So neither the construction nor the witness is broken on its own; what is missing is grounding the construction's params when the only thing downstream is a spec-op call, which cannot pin them the way a declared type does. NOT the shapes already ruled out, each by its own measurement: not the arrow/transform row (WI-20260828-8Q0Q5 fixed that, and row 3 still fails with an inline `lambda` in place of `inc`); not transitive provision (a hand-written carrier providing the spec through an intermediate is CLEAN in the same shape); not a missing provision reader for a concrete carrier into a spec-typed field (the hand-written analogue of exactly that shape is CLEAN). LOW IMPACT, stated so it is not over-prioritised: the stdlib never writes the failing spelling — `xs.map(f)` resolves `FiniteCollection.map`, whose declared return pins every param, which is row 1. It bites a USER writing the combinator by hand. Surfaced by WI-590, whose test file documents the bracket at wi590_conditional_finiteness_test's header and works around it by naming the carrier in the probe's signature.

