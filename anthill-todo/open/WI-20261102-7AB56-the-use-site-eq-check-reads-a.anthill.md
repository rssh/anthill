## Attributes

- id: WI-20261102-7AB56-the-use-site-eq-check-reads-a
- created: 2026-11-02T20:05:11Z

- status: Open
- status_agent: user
- status_at: 2026-11-02T20:05:11Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE USE-SITE Eq CHECK READS A PROJECTION KEY AS GROUND, so `Set[T = x.E]` is refused whatever `x` is. Over `sort Leaf { sort E = ?  entity leaf(e: E) }`, `operation k(x: Leaf, s: Set[T = x.E]) -> Int64 = 1` is refused "`T = x.E` binds a type that does not provide `Eq`", where its generic twin `k[E](x: Leaf[E = E], s: Set[T = E])` loads; since WI-20260929-TJ3G4 the same holds of `requires Holder[C = Set[T = x.E]]` in an operation's own `requires`. Over `x: Leaf[E = Float]` the refusal is right, by accident: nothing provides `Eq` at a projection at all. Measured 2026-11-02. MECHANISM: `check_use_site_requires_eq` (typing/coherence.rs) gates on `type_is_ground`, which counts the projection's path as closed, and `eq_holds_at` then asks `Eq` of `x.E` itself. Skipping every projection (`value_contains_projection`) was measured and declined (user, 2026-11-02): it fixes the open case and loads `x: Leaf[E = Float]` with `Set[T = x.E]` in silence. WHAT: ground a projection key through the receiver's declared type where that fixes the member, and defer it as abstract where it does not — the site has no link to the operation whose parameter the receiver is, so the check, or the site, needs one. ACCEPTANCE: the open-`E` key loads at a parameter and in an operation's `requires`; `x: Leaf[E = Float]` is refused there and `x: Leaf[E = Int64]` loads; a rigid projection (`P.Key`) likewise; full workspace green via rustland/scripts/test.sh.

