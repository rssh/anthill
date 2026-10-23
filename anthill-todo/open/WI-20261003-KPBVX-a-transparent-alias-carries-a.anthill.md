## Attributes

- id: WI-20261003-KPBVX-a-transparent-alias-carries-a
- created: 2026-10-03T16:54:18Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T16:54:18Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261003-QV5W5-implement-proposal-069

- tags: proposal-069

## Description

A TRANSPARENT ALIAS CARRIES A DECLARATION DEFAULT EXACTLY AS THE DIRECT APPLICATION DOES (proposal 069 §2, *A type default is context-free*). Under 069, `Function` declares `effects E = ? default {}`, so `Function[A, B]` is pure wherever it is written. A transparent alias `sort F = Function[A, B]` must denote that same pure type in every position — the review (1376b717) made the default context-free precisely so an alias cannot change whether a default applies. TO DRIVE, each against the direct spelling, both ways: (1) a PARAMETER `f: F` refuses an effectful argument, as `f: Function[A, B]` does; (2) a RETURN `-> F` is pure — a body returning an effectful function is refused; (3) a RULE logical position — under `sort Box[T = Int64]` and `sort B = Box`, a goal over `B` matches `Box[Int64]` only, as `Box` does, while `Box[?]` / an alias of `Box[?]` ranges over every element type; (4) a WRITTEN BOUND `?f: F` on a rule column is pure, as `?f: Function[A, B]` is; (5) a DEPENDENT default through an alias (`sort AsymmetricPair[T1, T2 = T1]`, `sort P = AsymmetricPair[Int64]`) gives `T2 = Int64`. Also an alias that WRITES the slot (`sort G = Function[A, B, ?]`) stays open, and one that writes `{IO}` keeps `{IO}`. CONTROL: each row must fail if the alias is expanded before default installation is marked (the alias losing the default) — say at each row which back-out reddens it. Acceptance: cargo-test via rustland/scripts/test.sh; scaland testFull.

## Changes

### 2026-10-23T06:41:37Z — feedback — claude

MEASURED WITH QV5W5'S STAGE 1 (2026-10-23): the loader records every parameter default in the alias rounds (`declare_type_aliases`), a defaulted sort pending until its defaults are, so an alias's definition is lowered with the defaults filled whichever file declares the sort. Rows (1) and (5) already hold: `sort F = Function[A = Int64, B = Int64]` refuses an effectful `useF(boom)` at `f` ("declares `Error`, which the closed row does not admit"), `sort G = Function[…, E = ?]` takes it, `sort B = Box` under `sort Box[T = Int64]` refuses a `String` box ("expected B (Box[T = Int64])"), `sort PI = P[Int64]` under `sort P[T1, T2 = T1]` refuses `pp(a: 1, b: "s")` ("expected PI (P[T1 = Int64, T2 = Int64])"). Rows (2)–(4) are not driven yet. A GAP FOUND, for this ticket: the carrier rule (`check_sort_parameter_carriers`) reads a slot an alias's definition LEFT OUT and a default filled as WRITTEN — `sort Box[T = Int64]  sort MyBox = Box  operation get(b: MyBox) -> T` is not refused for want of a carrier, where `get(b: Box) -> T` is. The direct spelling carries a `TypeNode::Defaulted` mark on the slot; the alias's recorded type (`alias_types`, `alias_targets`, the `SortAlias` fact) is a hash-consed term, which cannot. The repair is the alias record holding its type as a value with its readers (memory: no written twin beside a term), then `applications_of`' alias arm reads the mark. Add that row, with its control.

