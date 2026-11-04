## Attributes

- id: WI-20261104-G36KK-a-provision-binding-a-member
- created: 2026-11-04T06:52:24Z

- status: Open
- status_agent: user
- status_at: 2026-11-04T06:52:24Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PROVISION BINDING A MEMBER TO THE PROVIDER'S OWN PARAMETER IS NOT READ AT THE ARGUMENT'S TYPE. `sort Wrap { sort T = ?  entity wrap(v: T)  provides Storage[C = Wrap, Val = T]  operation get(s: Self) -> T = s.v }` with `mkw() -> Wrap[T = Int64] = wrap(v: 1)`: `g(mkw())` over `g[P](x: P) -> P.Val requires Storage[C = P] = Storage.get(x)` in `main() -> Int64` is refused "type mismatch in main.return (op-return): expected Int64, got P.Val"; the row twin (`effects R = ?`, `provides Strm[C = Wrap, E = R]`, `mkw() -> Wrap[T = Int64, R = {Error}]`, `g` declaring `effects {P.E}`) is refused "undeclared effect: P.E" under `effects {Error}`. MEASURED on 0eaa2e86 (found by WI-20261103-JGW88's /code-review). The projection stays unground — the refusal names `P.Val`. `ground_rigid_projection_if_concrete` reads the carrier by its sort and the provision's binding as written, and nothing there reads a binding that is the provider's own parameter at the argument's type arguments; not traced further. EXPECTED: `P.Val` at `Wrap[T = Int64]` is `Int64` and `main` runs to 1; at `R = {Error}` the call incurs `Error`; where the argument leaves the parameter open (a bare `Wrap`) the member does not read, refused as `UnreadProjection` refuses. ACCEPTANCE: rows, both kinds; back-outs measured; full gate green.

