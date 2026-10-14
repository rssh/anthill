## Attributes

- id: WI-20261014-6T5C6-an-entity-field-s-arrow-type
- created: 2026-10-14T08:25:03Z

- status: Open
- status_agent: user
- status_at: 2026-10-14T08:25:03Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

An entity field's arrow type cannot name its own parameter in its effect row.

PROGRAM (measured 2026-10-14, plain and ANTHILL_TEST_NODE_CARRIER=1 alike):

  sort Box
    effects EB = ?
    entity box(g: (k: Cell[V = Int64]) -> Int64 @ {Modify[k], EB})
  end

is a load error: "unresolved name 'k' in scope 'Box'", at the k of Modify[k]. The same arrow written as an operation's parameter type loads and runs (run[EffP](p: Cell[V = Int64], g: (k: Cell[V = Int64]) -> Int64 @ {Modify[k], EffP}) -> Int64 effects {Modify[p], EffP} = g(p), called run(r, lambda (k: Cell[V = Int64]) -> put(k, 5)), is 55), and the field without the label (@ {EB}) loads. So a field's arrow cannot say that its callback writes the cell it is handed, which an operation's slot can.

EXPECTED: the field loads; a construction box(g: lambda (k: Cell[V = Int64]) -> put(k, 5)) is admitted at it, and the write is to the cell the field's function is later applied to.

WHERE TO LOOK: found during 1TJQH. A guess, not measured: the name k is resolved in the entity's scope when the field type is lowered, where an operation's arrow is lowered with its binders in scope.

## Changes

### 2026-10-14T08:35:08Z — feedback — user

WIDENED (user, 2026-10-14), found by the family e-applied-arrow: an arrow type names its own parameter in its row only in an operation's PARAMETER LIST. Refused the same way ('unresolved name z') in a let annotation (let w: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]} = lambda (z: Cell[V = Int64]) -> put(z, 5)) and in an operation's result type (operation mk() -> (z: Cell[V = Int64]) -> Int64 @ {Modify[z]} = …), as well as in an entity field. EXPECTED: all three load, the row naming the arrow's own parameter as it does in a parameter list.

