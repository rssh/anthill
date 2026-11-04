## Attributes

- id: WI-20261104-16J8G-an-inferred-key-is-never
- created: 2026-11-04T08:20:20Z

- status: Open
- status_agent: claude
- status_at: 2026-11-04T08:20:20Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN INFERRED KEY IS NEVER JUDGED FOR A LAWFUL Eq: the use-site check reads only types a program WRITES, so a Set or Map whose key type the typer infers loads with a key that does not provide Eq. Measured 2026-11-04 on 3dcbd560: 'let s = {1.5}', 'let s = {(a: 1.5, b: 1)}', 'size({1.5, 2.5})' and 'size[F = Float]({1.5})' over 'operation size[F](s: Set[T = F]) -> Int64 = 1', and 'let m = Map.empty[K = Float, V = Int64]()' (an operation's type arguments, not a written type) each load, where 'let s: Set[T = Float] = {1.5}' and 'operation size(s: Set[T = Float])' are refused 'binds a type that does not provide Eq'. Found by WI-20261103-SWPHB, whose key check assumes Eq at a type parameter as the best case and so leaves what a call binds the parameter to unjudged. MECHANISM: check_use_site_requires_eq (typing/coherence.rs) reads the sites the type LOWERINGS record (ParameterizedSite); an inferred type has no lowering, and the check's non-scope (3) says so ('the declared signature it flows into or out of is what carries the refusal' — not so where that signature names a type parameter). DECIDE FIRST: kernel-language.md's = paragraph says 'Map[K = Float] / Set[T = Float] are refused wherever the type is written'; whether a key the typer infers is held to it too, and where — at a set or map literal's element type, at an operation's written type arguments (Map.empty[K = Float]), at each call's instantiated argument and result types, or as a requirement a signature's key at a parameter implies for its callers (which a generic caller forwarding the parameter then owes as well). ACCEPTANCE: each program above refused naming the key or loaded by the decided rule, with its lawful twin (Int64) loading and running; the spec sentence worded with the user; full workspace green via rustland/scripts/test.sh.

