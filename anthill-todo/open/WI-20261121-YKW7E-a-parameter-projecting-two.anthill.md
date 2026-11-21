## Attributes

- id: WI-20261121-YKW7E-a-parameter-projecting-two
- created: 2026-11-21T08:43:18Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T08:43:18Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PARAMETER PROJECTING TWO HOPS OFF A SIBLING IS REFUSED WHEN THE SIBLING'S ARGUMENT IS A CONSTRUCTED VALUE: over `sort State { sort P = ?; requires DataProvider[P = P]; entity state(provider: P) }` and `sort Wrap0 { entity wrap0(st: State) }`, `operation op2(a: Wrap0, k: a.st.provider.K) -> Int64 = check(a.st, k)` called as `op2(wrap0(st: u), ju)` inside `fwd(u: State, ju: u.provider.K)` is refused "type mismatch in op2.return (op-return): expected a well-formed type projection, got no `requires` bound on 'State' whose carrier is this abstract type parameter declares a member 'K'; cannot project 'K'" — measured on f7ed45c6 with the debug CLI, 2026-11-21 (found by WI-20261121-204T6's review; an operation, so no change of that ticket's); the lambda `lambda (a: Wrap0, k: a.st.provider.K) -> check(a.st, k)` applied to the same arguments likewise. The argument is no path, so the call opens `a.st` to an unknown of its own (`Receivers::Call`, `field_type_at_path`), whose `provider`'s `P` then carries no `requires` and `K` reads nothing. WHAT: measure whether a field of a constructed argument should be read at the constructor's own arguments (`wrap0(st: u)`'s `st` is `u`, so `a.st.provider.K` is `u.provider.K`), or the opened unknown keep the bound its declaring sort's `requires` gives it. ACCEPTANCE: `op2(wrap0(st: u), ju)` runs to 42 (`check` returning 42); `op2(wrap0(st: u), jw)` for another state's key is refused at the call; the let-bound `let a0 = wrap0(st: u); op2(a0, ju)` is decided as the language says (measure it first); full workspace green via rustland/scripts/test.sh.

