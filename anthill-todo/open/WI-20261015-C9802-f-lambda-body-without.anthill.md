## Attributes

- id: WI-20261015-C9802-f-lambda-body-without
- created: 2026-10-15T20:50:56Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T20:50:56Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

`?f <=> lambda () -> body` WITHOUT PARENTHESES PARSES AS A FUNCTION TYPE, and the body is evaluated where it stands.

MEASURED 2026-10-15 on cc3d1a7d, and the same before WI-20260908-9WVT7 (found by its review), over `operation plus1(n: Int64) -> Int64 = n + 1` and `operation applyThunk(f: () -> Int64) -> Int64 = f()`: `rule bareOnly(?f) :- ?f <=> lambda () -> plus1(1)` answers `?f = arrow(lambda, 2)`; `rule bare(?r) :- ?f <=> lambda () -> plus1(1), applyThunk(?f, ?r)` faults ("unknown operation: probe.h.applyThunk.f") and leaves `applyThunk(arrow(lambda, 2), ?_)`; parenthesised, `?f <=> (lambda () -> plus1(1))`, it answers 2. So `lambda () -> e` on the right of `<=>` is read as the arrow type `lambda -> e`, and `e` is reduced as an operand.

TO DECIDE: the precedence of `lambda` against the arrow type in a term position (tree-sitter-anthill/grammar.js; scaland's fastparse follows), or a load refusal of a bare `lambda` as an arrow's domain.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; tree-sitter corpus): `bareOnly` answers a closure, or the program is refused naming the parenthesis; `bare` answers 2.

