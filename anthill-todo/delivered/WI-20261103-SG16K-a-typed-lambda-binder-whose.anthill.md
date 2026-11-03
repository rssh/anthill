## Attributes

- id: WI-20261103-SG16K-a-typed-lambda-binder-whose
- created: 2026-11-03T05:08:35Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-03T10:17:05Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A TYPED LAMBDA BINDER WHOSE ANNOTATION PROJECTS A MANIFEST PARAMETER IS REFUSED: `operation k(x: Leaf[E = Int64]) -> Bool =` / `let h = lambda (s: List[T = x.E]) -> true` / `true` is refused "type mismatch in <binder>.s (binder-annotation): expected List[T = x.E], got List[T = Int64]" — no key involved; the same with `Set[T = x.E]`, and over an open `E` it loads (measured 2026-11-03, found while measuring WI-20261102-7AB56). The annotation as written, its projection unread, is compared with a type in which it is read. WHAT: read the annotation's projections where the binder-annotation check compares it, as a `let` annotation's are (`read_denoted_projections`); measure first which side carries which reading. ACCEPTANCE: the program loads, and the lambda applied to a `List[T = String]` is refused; full workspace green via rustland/scripts/test.sh.

