## Attributes

- id: WI-20261103-JGW88-a-row-a-requirement-leaves
- created: 2026-11-03T22:43:53Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-04T06:50:24Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A ROW A REQUIREMENT LEAVES UNWRITTEN IS NOT THE ROW ITS PROJECTION NAMES. Over `sort Strm { sort C = ?  effects E = ?  operation step(s: C) -> Int64 effects {E} }`, a body under `requires Strm[C = P]` that declares `effects {P.E}` and calls `Strm.step(x)` (`x: P`) is refused "expected declared: [P.E], got undeclared effect: Strm[C = P].E" — for an operation's clause (`g[P](x: P) -> Int64 effects {P.E} requires Strm[C = P] = Strm.step(x)`) and, since WI-20261020-DNX0E, for a sort's (`sort Sp { sort P = ?  requires Strm[C = P]  operation g(x: P) -> Int64 effects {P.E} = Strm.step(x) }`). MEASURED on 89500f50 (the operation's refused so, the sort's printing the undeclared row as `?_`) and on the DNX0E tree. DNX0E made a member a clause leaves unwritten (GVGSQ's instance unknown, `scope_clause_at_carrier`) the projection the signature writes for it — `-> P.Val = Storage.get(x, k)` loads — by `MintedParam::Member`'s `at` and the ζ arm (`projection_is_instance_member`), but excludes an effect row (`declared_carrier_param`): a row is compared by the row algebra, not by ζ, and `P.E` in a row is an atom the row decomposition reads, which nothing ties to the minted row member. EXPECTED: `effects {P.E}` covers what the instance's `E` raises, both clause kinds; a body declaring `effects {}` is still refused naming `P.E` (or the instance's row) as undeclared; two carriers' rows stay apart (`effects {P.E}` does not cover `Strm.step(y)` at `y: Q`). ACCEPTANCE: the three as rows, sort and operation spelling each; back-outs measured; full gate green.

## Changes

### 2026-11-04T06:50:21Z — feedback — user

Delivered. A row a requirement leaves unwritten is the row its projection names: in the body (the row member minted with its at, declared_carrier_param; the coverage check asking the ζ identity of an atom, atom_is_projected_instance_member), against an arrow's row (relate_effect_rows, cancel_instance_member_tails), and at a caller (the call's row read off the carrier's provision, resolve_type_deep_value in check_apply_iter; a carrier whose provision does not read it refused naming the requirement, UnreadProjection). Measured on 29c0191f and the delivered tree: g[P](x: P) -> Int64 effects {P.E} requires Strm[C = P] = Strm.step(x) and its sort spelling, refused "expected declared: [P.E], got undeclared effect: Strm[C = P].E", now run — g(mem) to 7 under effects {Error}, g(pure) to 5 under no row — and g(mem) under no row is refused naming Error; effects {} and P.E over Q's row are refused as before. /code-review found that the identity checked the parameter and the member's name alone — with A requiring B[C = C], effects {P.E} requires A[C = P] = B.op(x) covered B's Error while callers read A's {}, and -> P.Val requires A[C = P] = B.get(x) returned B's Int64 as A's String (the type half since DNX0E) — so a member gets its at only where its clause's spec is the one P.member is read through (rigid_projection_lender), for types and rows alike. Rows: wi_jgw88 (7), six back-outs in its header. Not here, refused as their type twins are: a caller forwarding through its own parameter, g as a function value, a parametric provider binding the row to its own parameter; and check_override_refinement reading no P.E at a provision.

