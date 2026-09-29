## Attributes

- id: WI-20260929-TJ3G4-the-use-site-eq-check-skips-a
- created: 2026-09-29T16:03:58Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T16:03:58Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE USE-SITE Eq CHECK SKIPS A KEY THAT HOLDS A VALUE-IN-TYPE: `Map[K = Buf[T = Float], V = Int64]` is refused (Float has no lawful Eq) but `Map[K = Buf[T = Float, N = 3], V = Int64]` loads clean; likewise `Set[T = …]` and a key `P[A = Float, B = Buf[…, N = 3]]` — in operation parameters, `requires` and `provides` alike, and identically on the Sep 20 build. FOUND by WI-20260924-F3FYJ's review (V18), PRE-EXISTING. MECHANISM: `check_use_site_requires_eq` (typing/coherence.rs ~1004) keeps only `Value::Term` site bindings on the premise that "a denoted binding names no carrier" — true of a bare `N = 3`, false of a TYPE holding one, which rides `Value::Node`; the dropped key leaves the goal `Eq[T = K]` non-ground and it is deferred as abstract (coherence.rs ~1041) with no diagnostic. The same premise is written at `ParameterizedSite::bindings` (kb/mod.rs ~698). FIX: judge a type holding a value-in-type — lower it with `node_occurrence::value_to_term`, or make `noneq_holds_at` / `spec_resolves_at_bindings` carrier-agnostic — and keep a bare denoted skipped. ACCEPTANCE: the valued keys refused like their ground twins, a lawful valued key (`A = Int64`) loading as the control; full workspace green via rustland/scripts/test.sh.

