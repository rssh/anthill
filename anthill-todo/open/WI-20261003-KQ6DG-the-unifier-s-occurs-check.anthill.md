## Attributes

- id: WI-20261003-KQ6DG-the-unifier-s-occurs-check
- created: 2026-10-03T12:31:34Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T12:31:34Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE UNIFIER'S OCCURS CHECK READS A BINDING AS WRITTEN, SO A CALL BINDS A VARIABLE INSIDE ITSELF AND THE LOADER OVERFLOWS ITS STACK. `operation two[A, B](f: (x: A) -> B, g: (y: B) -> A) -> Int64 = 1`, `operation go() -> Int64 = two(lambda (x) -> [x], lambda (y) -> [y])`, with a `requires anthill.cli.Main` app whose `main` calls `go()`: the loader aborts "thread 'main' has overflowed its stack" (exit 134) on every build — the tree before WI-20260929-0RP29 and the trees its eighth, ninth and tenth reviews saw (MEASURED). The same with an option parameter beside the pair (`two[A, B](k: Option[T = A], f: (x: A) -> B, g: (y: B) -> A)` called `two(none, lambda (x) -> [x], lambda (y) -> [y])`, which the `binds_a_cycle` guard in `projection_receivers` was meant to cover), and with a body applying the pair (`-> A = g(f(g(f(1))))`). The first lambda binds `B ↦ List[T = A]`, the second `A ↦ List[T = B]`: `bind_resolved` (typing/unify.rs) admits it because its `occurs_in` reads `List[T = B]` as written — `B` is no `A` — not through σ, where `B` is `List[T = A]`; `Substitution::bind_value` checks nothing. σ then holds a cycle, and every deep reader (`walk_type_deep`, `resolve_type_deep_value`) recurses through it without end. The typer patches readers one at a time: 13 `binds_a_cycle` scans after the fact (12 in typing/signature.rs, 1 in typing/carrier.rs `projection_receivers`), each guarding one reader. FIX: the occurs check follows σ where a variable is bound — `bind_resolved` and the `bind_value` route — with a visited set, so the binding that would close a cycle fails at the argument making it ("no finite type"), and the `binds_a_cycle` scans become debug assertions or go. ACCEPTANCE: the three programs refused at load naming the argument that closes the cycle, no stack overflow; a chained but acyclic call — `two[A, B](f: (x: A) -> B, g: (y: Int64) -> A) -> B = f(g(41))`, matched `case cons(h, t) -> h` over `two(lambda (x) -> [x], lambda (y) -> y + 1)` — still runs to 42 (MEASURED: runs on today's tree); the rows those guards cover pass (`wi_0rp29_review9_regressions_test` part 98, the declaration rule's rows in `wi_0rp29_member_rule_test`); the suite's wall time not materially slower, measured before and after (every binding pays the walk); full workspace green via rustland/scripts/test.sh.

