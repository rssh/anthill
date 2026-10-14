## Attributes

- id: WI-20261014-N2YEK-an-entity-field-whose-row
- created: 2026-10-14T08:47:41Z

- status: Open
- status_agent: user
- status_at: 2026-10-14T08:47:41Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

An entity field whose row parameter is bound to nothing admits a lambda that writes its own parameter, and applying the field's function then writes with nothing declared.

PROGRAM (measured 2026-10-14, plain and ANTHILL_TEST_NODE_CARRIER=1 alike, and on the tree before 1TJQH as well):

  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  sort Box
    effects EB = ?
    entity box(g: (z: Cell[V = Int64]) -> Int64 @ {EB})
  end
  operation use(q: Cell[V = Int64]) -> Int64 =
    let b: Box[EB = {}] = box(g: lambda (z: Cell[V = Int64]) -> put(z, 5))
    let w = b.g
    w(q)

use declares no effects, and RUNS, writing q (called over a cell holding 1, use(c) * 10 + Cell.get(c) is 55). The construction alone loads (let b: Box[EB = {}] = box(g: lambda (z: Cell[V = Int64]) -> put(z, 5)), then 0). The field's row says the function does nothing; the lambda writes the cell it is handed. A lambda writing a cell in scope at the same field is refused, correctly: put(q, 5) gives "expected Box[EB = {}], got Box[EB = Modify[T = q]]" (since 1TJQH; admitted before it).

EXPECTED: the construction is refused — a callback writing its own parameter is no label the field's row parameter takes, as at an operation's slot @ {EffP} — and so use never runs. 1TJQH's delivery said this of a constructor's field; no row drove it, the family c-callback-row's field naming the parameter in its row (@ {Modify[k], EB}), which 6T5C6 refuses.

THE FAMILY e-applied-arrow lists the programs typed=field,row=open,does=writes-own,declares=none (applied=call, alias, slot) as P3 exceptions naming this ticket: UNSOUND runs 552. When the fix lands they excuse nothing and the run says so.

