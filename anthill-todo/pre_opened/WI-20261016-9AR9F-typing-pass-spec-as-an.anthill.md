## Attributes

- id: WI-20261016-9AR9F-typing-pass-spec-as-an
- created: 2026-10-16T10:10:31Z

- status: PreOpened
- status_agent: user
- status_at: 2026-10-16T10:10:38Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-1126, WI-010

- tags: typing

## Description

typing_pass_spec as an executable alternative implementation: rewrite docs/proposals/typing_pass_spec.anthill in the type model the engine has, so PART I runs by SLD as the conformance oracle its header says it is, and the Rust typer is checked against it.

WHY. The file claims two roles: PART I (synth / check / wf_type) is "what Rust and Scala must COMPLY with" and "can be run as a conformance ORACLE via SLD"; PART II (type_check) is the reference algorithm they reimplement. Neither role is exercised today. Its only reader is `typing_pass_spec_parses_and_loads` (rustland/anthill-core/tests/include/typing_test.rs:1673), which TOLERATES every load error and asserts only that `TypingEnv`, `type_check` and `assert_compatible` are defined. Nothing resolves a `synth` goal, so a rule that says the wrong thing stays green.

WHAT IS STALE (measured 2026-10-16).
  * Type notation: since WI-361 the deep constructors the file is written in (`sort_ref`, `parameterized`, `arrow`, `type_var`, `named_tuple`, `nothing`, `TypeField`) resolve to nothing; a type is term-backed (`Ref(S)`, `Fn{S, named}`, structural forms via `TypeExtractor`). The note at lines 39-50 says so.
  * Effects: still `List[Type]` with `union_effects` and an `actual ⊆ declared` check (`check_effects`). The typer works on `EffectExpression` rows (`present` / `guarded` / `absent` / `open` / `merge` / `empty_row`) with row unification and subtyping, lacks constraints and handler discharge (WI-307/326/328/329, proposal 048; rustland/anthill-core/src/kb/typing/effects.rs). This ABSORBS WI-330, whose pieces (a)-(d) are this item restricted to effects.
  * Helpers: `check_named_args`, `synth_branches`, `check_branches`, `extend_ctx_from_pattern`, `lub`, `union_effects` exist only as a "deferred" comment; `type_compatible`, imported from anthill.reflect.typing, is not declared there (only `is_entity_of` is).

WHY AFTER WI-1126. The oracle encodes the base type model. Written before the freeze settles that model it is rewritten with every change; after it, the oracle is what pins the model down. WI-010 (subtype / assignable / unify_type as anthill rules) is gated the same way and supplies what PART I's SUB rule needs.

TARGET STATE.
  (1) The file loads with ZERO load errors, and the smoke test asserts that instead of tolerating them.
  (2) PART I in term-backed notation, effects as rows: synth / check carry an EffectExpression row; union is `merge`; SUB uses row subtyping; LAM puts the body row on the arrow; APP instantiates the callee's declared row with guard discharge; handler discharge removes what a handler covers.
  (3) The deferred helper relations are written, or the language fragment they cover is listed as out of scope, by name, in one place.
  (4) A conformance test DRIVES the oracle: for a corpus of operation bodies it resolves `synth(Γ, body, ?T, ?E)` by SLD and compares type and row with what the Rust typer records. Control: a mutated spec rule, and a deliberately wrong typer answer, each fail it.

OPEN, to decide at promotion: does PART II (type_check) also run as a third typer whose results are compared, or is it kept as reference prose aligned with PART I; is scaland checked against the oracle too, or Rust only.

