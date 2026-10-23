## Attributes

- id: WI-20261023-GBH5F-proposal-069-stage-2-operation
- created: 2026-10-23T05:45:40Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T05:45:40Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261003-QV5W5-implement-proposal-069

- tags: proposal-069

## Description

PROPOSAL 069 STAGE 2 — OPERATION TYPE-PARAMETER DEFAULTS (§1.3), replacing WI-850's refusal. `operation decode[T = String](bytes: Bytes) -> T` declares a default; at a call the parameter is settled by (1) an explicit call-site binding, (2) inference from arguments, requirements, receiver and expected result, (3) the declaration default, (4) the unconstrained-type-parameter error — the default is installed once, in declaration order, where that error is raised today, and solving resumes before validation (§2 steps 4–6). A default may name earlier type parameters and the enclosing scope; a forward reference and a wrong-kind default are load errors at the default. Work: tree-sitter keeps the parsed `default` field as language; Rust and Scala IR carry it on TypeParam; OperationInfo records it; reflect exposes it; codegen and persistence keep it. Spec: kernel-language §5.4 TypeParam production and the WI-850 paragraph, proposal 042 OQ3. ACCEPTANCE driven by value: `identity[T = String](x: Option[T] = none()) -> T` style rows — inference wins over the default (`identity[T = String](42)` is Int64), the default answers when nothing binds T, an explicit call-site binding overrides it; a dependent default `[T, U = List[T]]` expands after T; forward reference and kind mismatch refused. WI-850's refusal tests (Rust and scaland ParseTest / DiagnosticLocationTest) are replaced by driven calls with a control that fails when default installation is backed out. WI-951 (raw CST text in the refusal) becomes moot with the refusal. Acceptance: rustland/scripts/test.sh, scaland sbt testFull, npx tree-sitter test.

## Changes

### 2026-10-23T05:45:55Z — feedback — claude

The 069 §8 row `identity[T = String](x: Option[T] = none()) -> T` carries a VALUE default, which is stage 3. Here it is driven without one: `identity[T = String](x: Option[T]) -> T` called as `identity(none())` takes the default, `identity(some(42))` infers Int64, `identity[T = Bool](none())` overrides. Stage 3 adds the `= none()` form of the same row.

