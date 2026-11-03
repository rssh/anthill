## Attributes

- id: WI-20261103-G5FK3-a-projection-off-a-value-whose
- created: 2026-11-03T09:10:08Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T09:10:08Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PROJECTION OFF A VALUE WHOSE TYPE IS A TYPE PARAMETER BOUNDED BY A `requires` IS REFUSED WHERE THE RIGID SPELLING LOADS: `operation k[P](x: P, s: x.Key) -> Bool requires Storage[C = P] = true` is refused "type mismatch in k.s (op-arg): expected a well-formed type projection, got cannot project 'Key' off an abstract receiver with no concrete sort", and with `Storage[C = P, Key = Int64]` too, while `s: P.Key` loads; the same in a sort (`sort H { sort P = ?; requires Storage[C = P]; operation g(p: P, k: p.Key) -> Bool = true }` refused, `k: P.Key` loads), in a `let` annotation (`let z: Option[T = x.Key] = none` refused, `P.Key` loads) and, since WI-20261103-SG16K, a typed lambda binder (`lambda (s: x.Key) -> true`, which loaded unread before it) — measured 2026-11-03, `Storage` a spec `{ sort C = ?; sort Key = ? }`. The bound says `P` is a `Storage` carrier, and that spec declares `Key`, so `x.Key` is `P.Key`. The abstract-receiver arm of `project_type_member` forms a neutral only through `recv_decl_sort`, the sort declaring a FIELD the receiver path reads (`s.provider.K`, WI-430); a parameter typed by a type parameter has none, so neither the operation's nor the enclosing sort's `requires` is asked. WHAT: read a projection off a receiver typed by a type parameter through the `requires` clauses that bound that parameter — the operation's own and the enclosing sort's — as the rigid `P.Key` is read (carrier-precise, as WI-430: only a bound whose carrier IS the parameter lends its members); open, a neutral; fixed by the bound, its binding. ACCEPTANCE: the four programs above load; under `Key = Int64` a body `s + 1` with `s: x.Key` types and runs, and under `Key = String` it is refused; a member no bound declares (`x.Nope`) stays refused naming it; full workspace green via rustland/scripts/test.sh.

