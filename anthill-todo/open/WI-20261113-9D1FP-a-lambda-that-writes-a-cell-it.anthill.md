## Attributes

- id: WI-20261113-9D1FP-a-lambda-that-writes-a-cell-it
- created: 2026-11-13T11:42:06Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T11:42:06Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A lambda that writes a cell it allocates itself is charged a write: at a pure callback slot it is refused, though the same body as an operation is pure.

MEASURED 2026-11-13 (tree over d7ac9630 and on d7ac9630 itself, so not caused by WI-20261002-DNDZF):

  operation hof(f: (u: Unit) -> Unit) -> Unit = f(())
  operation own() -> Unit =
    let d: Cell[V = Int64] = Cell.new(0)
    Cell.set(d, 7)
  operation go() -> Int64 =
    let _ = hof(lambda (u: Unit) ->
      let d: Cell[V = Int64] = Cell.new(0)
      Cell.set(d, 7))
    1
  operation go2() -> Int64 =
    let _ = hof(lambda (u: Unit) -> own())
    2

go is refused: 'type mismatch in hof.f (op-arg): expected callback effects admitted by parameter f of hof (a closed row), got the lambda argument declares Modify[T = result], which the closed row does not admit'. go2, the same body behind an operation, loads: the operation boundary drops the write to its own fresh local, the lambda's row does not, and names the write by the arrow's result place.

EXPECTED: a write to a cell the lambda allocates inside its own body, and which does not leave it, is no part of the lambda's row, as at an operation's boundary; go loads and runs as go2. A cell that leaves the lambda (returned, stored in a captured cell) keeps the write, under whatever HE2J6 decides for a result.

WHERE TO LOOK: how a lambda's row is derived from its body (the label lands on the result place: the fresh_output / local provenance in kb/flow_derive.rs and stdlib/anthill/reflect/feed.anthill) against region::op_boundary_effects (kb/region.rs), which masks an operation's own locals. Related, opposite direction: WI-20261016-HE2J6 (a call's result is not fresh).

