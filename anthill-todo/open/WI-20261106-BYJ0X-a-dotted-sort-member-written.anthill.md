## Attributes

- id: WI-20261106-BYJ0X-a-dotted-sort-member-written
- created: 2026-11-06T09:25:19Z

- status: Open
- status_agent: user
- status_at: 2026-11-06T09:25:19Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a dotted sort member written without parentheses in a `@[simp]` right-hand side (`f(?a) <=> K.seven @[simp]` over a const, `K.one` over a nullary operation) dies in the typer where the rewrite fires with an internal-defect message; `K.one()` runs

## Changes

### 2026-11-06T09:25:49Z — feedback — user

FOUND BESIDE WI-20260825-6RRVA (bd8eebdf) while looking for a positive row. MEASURED on bd8eebdf, each with `operation f(a: Int64) -> Int64`, `rule r: f(?a) <=> RHS @[simp]` and `operation g(x: Int64) -> Int64 = f(x)`, over `sort K { const seven: Int64 = 7; operation one() -> Int64 = 1; entity box(v: Int64) }`: RHS `K.seven` and `K.one` refuse at g's splice with "type mismatch in p6r.pos.K.reference: expected a type value recorded where the sort is written (proposal 055 §1), got a plain reference to the sort — a defect in the walk that built this occurrence, not an error in the program" plus "seven.name / one.name: expected resolved name, got unresolved"; `K.one()` loads and runs; the same with `K.mk.v` (a field read off a nullary op). LIKELY CAUSE, not verified: an equation head converts with ConstFold::Off, so the data-slot const fold and the dotted rungs leave the replacement's chain as `field_access(Ref(K), seven)`, and the spliced replacement reaches the typer as a field access whose receiver is a plain sort Ref with no recorded type value. Loud today (load error), so not silent — but the message blames the loader's walk, and the spelling is one §5.3 now tells authors is a path.

