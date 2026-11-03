## Attributes

- id: WI-20261103-95S43-a-projection-off-a-spec-s-own
- created: 2026-11-03T09:28:49Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T09:28:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PROJECTION OFF A SPEC'S OWN CARRIER IS REFUSED IN THE SPEC'S BODIES: in `sort Coll { sort C = ?; sort Elem = ?; operation first(c: C) -> Elem; … }` a default body's `let e: c.Elem = first(c)` is refused "cannot project 'Elem' off an abstract receiver with no concrete sort", as are a typed lambda binder `lambda (e: c.Elem) -> …` (since WI-20261103-SG16K; it loaded before, unread) and the return `operation pick(c: C) -> c.Elem = first(c)` (at `pick.return`), and the `Eq` key check refuses `lambda (s: Set[T = c.Elem])` there as not judged ("type 'Coll.C' has no member 'Elem'"). A body-less `has(c: C, e: c.Elem) -> Bool` loads, and a SIBLING CALL reads its callee's `c.Element` as this instance's (`this_instance_member`, WI-20261001-80ZV8) — measured 2026-11-03. Reading a body's annotations through `this_instance_member` was tried in SG16K and backed out on its second /code-review: the function has no gate for a projection an author writes off any receiver. `spec_carrier_param` names an element for a data sort, so `let y: x.T = x` in `sort Box { sort T = ?; entity box(v: T); operation put(x: T) -> Box[T = T] = … }` and `let y: a.B = b` over `entity p2(a: A, b: B)` loaded, and under `requires Storage[C = S, Key = Int64]` `s.Key` read as the sort's own `Key` ("expected ?Key, got Int64"). WHAT: a projection off a receiver typed by the carrier of the spec a body is written in reads as this instance's member at every reader of that body — `read_written_annotation` (a `let`, a lambda, a pattern binder), the body's check of its own signature, the `Eq` key check (`read_projection_key`) — gated so it answers a genuine carrier only: not a data sort's element, not the member that is the carrier itself, not a carrier that a `requires` bounds with that member (that reading is WI-20261103-G5FK3's). ACCEPTANCE: the four spellings above load in a spec's default body and run at a provider; a lambda `(e: c.Elem)` applied to `1` is refused against `c.Elem`; the Box, Pair2 and Storage-bounded programs above stay refused; full workspace green via rustland/scripts/test.sh.

