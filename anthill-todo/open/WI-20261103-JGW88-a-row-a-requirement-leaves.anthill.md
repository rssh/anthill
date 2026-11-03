## Attributes

- id: WI-20261103-JGW88-a-row-a-requirement-leaves
- created: 2026-11-03T22:43:53Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T22:43:53Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A ROW A REQUIREMENT LEAVES UNWRITTEN IS NOT THE ROW ITS PROJECTION NAMES. Over `sort Strm { sort C = ?  effects E = ?  operation step(s: C) -> Int64 effects {E} }`, a body under `requires Strm[C = P]` that declares `effects {P.E}` and calls `Strm.step(x)` (`x: P`) is refused "expected declared: [P.E], got undeclared effect: Strm[C = P].E" — for an operation's clause (`g[P](x: P) -> Int64 effects {P.E} requires Strm[C = P] = Strm.step(x)`) and, since WI-20261020-DNX0E, for a sort's (`sort Sp { sort P = ?  requires Strm[C = P]  operation g(x: P) -> Int64 effects {P.E} = Strm.step(x) }`). MEASURED on 89500f50 (the operation's refused so, the sort's printing the undeclared row as `?_`) and on the DNX0E tree. DNX0E made a member a clause leaves unwritten (GVGSQ's instance unknown, `scope_clause_at_carrier`) the projection the signature writes for it — `-> P.Val = Storage.get(x, k)` loads — by `MintedParam::Member`'s `at` and the ζ arm (`projection_is_instance_member`), but excludes an effect row (`declared_carrier_param`): a row is compared by the row algebra, not by ζ, and `P.E` in a row is an atom the row decomposition reads, which nothing ties to the minted row member. EXPECTED: `effects {P.E}` covers what the instance's `E` raises, both clause kinds; a body declaring `effects {}` is still refused naming `P.E` (or the instance's row) as undeclared; two carriers' rows stay apart (`effects {P.E}` does not cover `Strm.step(y)` at `y: Q`). ACCEPTANCE: the three as rows, sort and operation spelling each; back-outs measured; full gate green.

