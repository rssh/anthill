## Attributes

- id: WI-20260929-TJ3G4-the-use-site-eq-check-skips-a
- created: 2026-09-29T16:03:58Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-02T21:22:27Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE USE-SITE Eq CHECK SKIPS A KEY THAT HOLDS A VALUE-IN-TYPE: `Map[K = Buf[T = Float], V = Int64]` is refused (Float has no lawful Eq) but `Map[K = Buf[T = Float, N = 3], V = Int64]` loads clean; likewise `Set[T = …]` and a key `P[A = Float, B = Buf[…, N = 3]]` — in operation parameters, `requires` and `provides` alike, and identically on the Sep 20 build. FOUND by WI-20260924-F3FYJ's review (V18), PRE-EXISTING. MECHANISM: `check_use_site_requires_eq` (typing/coherence.rs ~1004) keeps only `Value::Term` site bindings on the premise that "a denoted binding names no carrier" — true of a bare `N = 3`, false of a TYPE holding one, which rides `Value::Node`; the dropped key leaves the goal `Eq[T = K]` non-ground and it is deferred as abstract (coherence.rs ~1041) with no diagnostic. The same premise is written at `ParameterizedSite::bindings` (kb/mod.rs ~698). FIX: judge a type holding a value-in-type — lower it with `node_occurrence::value_to_term`, or make `noneq_holds_at` / `spec_resolves_at_bindings` carrier-agnostic — and keep a bare denoted skipped. ACCEPTANCE: the valued keys refused like their ground twins, a lawful valued key (`A = Int64`) loading as the control; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-02T21:22:24Z — feedback — user

Delivered 2026-11-02. THE TICKET'S OWN MECHANISM WAS ALREADY GONE: WI-20260829-2NMXA replaced the Value::Term-only filter in check_use_site_requires_eq by one that drops a binding that IS a value at its root, so every key the description names is refused now (measured through the CLI: operation parameter, entity field, a sort's requires, provides, Set, the P[A = Float, B = Buf[..., N = 3]] key), and the lawful control loads. Rows pin the positions 2NMXA did not (wi_tj3g4_valued_key_positions_test), and the stale premise at ParameterizedSite::bindings is corrected. FOUND WHILE MEASURING and fixed here (user: inline): an OPERATION's own requires recorded no use site at all — requires Holder[C = Map[K = Float, V = Int64]] loaded, its ground key included. A bracket written there as a type argument of a bracket is recorded by convert_term at its own span, its bindings read through the aliases they name; a requirement (the goal, or one under not(...)) is no use; a bracket whose arguments were refused is not judged again; the written-row check is handed the type lowerings' sites alone (WrittenTypeSites), so a row there is judged once. A projection key (Set[T = x.E]) is refused there as in a signature (user's choice); grounding it is WI-20261102-7AB56. NOT JUDGED, documented in the check's non-scope (4): a key in an ensures clause, a fact's bracket, a rule body. Three /code-review passes, findings applied; nine back-outs measured (test header). Full workspace 11,540 passed, 0 failed, 17 ignored; families green, no verdict moved. No Scala or grammar file changed; scaland not run.

