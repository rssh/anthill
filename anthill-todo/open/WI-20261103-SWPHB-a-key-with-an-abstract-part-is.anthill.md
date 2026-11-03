## Attributes

- id: WI-20261103-SWPHB-a-key-with-an-abstract-part-is
- created: 2026-11-03T05:08:30Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T05:08:30Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A KEY WITH AN ABSTRACT PART IS SKIPPED WHOLE, so an unlawful part beside it loads: `operation k[F](s: Set[T = (a: F, b: Float)]) -> Int64 = 1` loads, as do `Set[T = Pair[A = F, B = Float]]` and `sort H { sort F = ?  entity h(s: Set[T = (a: F, b: Float)]) }` (measured 2026-11-03), where `Set[T = (a: Int64, b: Float)]` is refused. Since WI-20261102-7AB56 a neutral projection is abstract the same way: `k(x: Leaf[E = Float], y: Leaf, s: Set[T = (a: x.E, b: y.E)])` loads (found by its /code-review; before it every projection key was refused). MECHANISM: `check_use_site_requires_eq` (typing/coherence.rs) skips a binding `type_is_ground` answers false for, and `read_projection_key` answers a key that keeps a neutral as abstract; `eq_holds_at` is asked of a ground key only. WHAT: judge the concrete part of a partly abstract key, with `Eq` assumed at each abstract leaf (a type parameter, a variable, a neutral projection) as the requirement of the code that binds it. The resolver's assumption channel (`available_requires`) covers a goal coarsely — `Eq[T = ?F]` covers `Eq[Float]` — so it is not that assumption as it stands. ACCEPTANCE: the four keys above refused, naming the unlawful part; `Set[T = (a: F, b: Int64)]`, `Set[T = Pair[A = F, B = Int64]]` and `Set[T = (a: x.E, b: y.E)]` over an open `E` load; full workspace green via rustland/scripts/test.sh.

