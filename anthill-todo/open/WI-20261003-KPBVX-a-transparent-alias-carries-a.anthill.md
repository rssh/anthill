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

