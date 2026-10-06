## Attributes

- id: WI-20261006-728RW-a-spec-member-written-through
- created: 2026-10-06T09:03:27Z

- status: Open
- status_agent: claude
- status_at: 2026-10-06T09:03:27Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SPEC MEMBER WRITTEN THROUGH A DOTTED HEAD IS NOT READ AS THE TWO-SEGMENT ONE IS. The member sugar is taken for `Spec.Member` — two segments — only (`Loader::try_expr_carried_projection_segments`: "Two-segment only; anything else stays on the `remap_name` path"), so one text has three readings by what its head is. MEASURED on the tree that delivers WI-20261006-XQGEW (the user's questions, 2026-10-06). (1) A NESTED SORT, the member open — `sort X2 { sort C = ?  effects E = ?  operation go(self: C) -> Int64 effects {E}  sort SX { sort C = ?  effects E = ?  operation inner(self: C) -> Int64 effects {E} } }`, `PX` providing both: `operation f(b: X2.SX.C) -> Int64 = 1` LOADS and `f(5)` answers 1 — the position takes any value and no requirement is owed — and `f(b: X2.SX.C) -> X2.SX.C = b` returns the 5; with a body that uses it (`= X2.SX.inner(b)`) the operation is refused "expected declared: [], got undeclared effect: ?_" and "expected `requires SX[…]` covering abstract type parameter", neither saying why. The same member through an import (`import ….X2.{SX}`, `b: SX.C`) is the sugar: `f(5)` is refused "`…X2.SX[C = Int64]` cannot be supplied", and `two(a: X2.C, b: SX.C) -> Int64 effects {X2.E, SX.E} = X2.go(a) + SX.inner(b)` runs (11). (2) A NAMESPACE-QUALIFIED SPEC — `f(b: probe.ns.Y2.C) -> Int64 = 1`: as (1), `f(5)` loads. (3) A NESTED ALIAS, the member open — `sort SX1 { sort C = ?  operation inner(self: C) -> Int64 }`, `sort X2 { sort SX = SX1 }`: `f(b: X2.SX.C)` is a load error, "unresolved type name 'X2.SX.C' … not a resolvable qualified sort reference", where `SX.C` (the alias imported) and `SX1.C` are the sugar and run. (4) A NESTED ALIAS, the member fixed — `sort SX1 { sort C = Int64 }`, `sort X2 { sort SX = SX1 }` (the user's example): `f(b: X2.SX.C) -> Int64 = b` is RIGHT today, `f(5)` answering 5 and `f("s")` refused, as `SX.C` and `SX1.C` are. Printed, the dotted members of (1) are their bare names: `two(a: X3.Y.C, b: X3.Z.C) -> Int64 effects {X3.Y.E, X3.Z.E} = fails()` reports "expected declared: [E, E]". EXPECTED: a dotted head is read as the head it resolves to — the member sugar where the member is open, (1)–(3), and the type it is fixed to where it is not, (4), unchanged — and its parameter is printed as written (`X2.SX.C`; WI-20261006-XQGEW's record holds one head name, the two-segment spelling's). ACCEPTANCE: in (1)–(3) `f(5)` is refused for want of a provision and `f(px())` runs through the provider's; (4) answers as today; `two` over `X3.Y` and `X3.Z` is refused naming `[X3.Y.E, X3.Z.E]`; a qualified name that is no spec's member (`Enum.Entity`, `ns.Sort`, `Outer.Inner`) resolves as before; the standard library and the examples load; full workspace green via rustland/scripts/test.sh. REFERENCE: kernel-language §5.4; `Loader::try_rigid_type_projection` and `Loader::alias_type_member` (rustland/anthill-core/src/kb/load.rs); WI-20260924-SNJPR (the member through an alias); WI-20261006-XQGEW.

