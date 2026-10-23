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

### 2026-10-23T06:19:05Z — feedback — claude

MOVED HERE FROM STAGE 1 (2026-10-23, while implementing QV5W5): a CONSTRUCTOR call's sort parameter that inference leaves unbound takes its default (069 §2 steps 4–5; a constructor is a call, kernel-language §5.4). It shares this stage's machinery and its obstacle. MEASURED: installing the default inside `check_constructor_iter` (after the fields, the sort's requires and the expected type) refused `wantS(tag(n: 1))` over `sort Tag[T = Int64]  entity tag(n: Int64)` and `wantS(x: Tag[T = String])` — `expected Tag[T = String], got Tag[T = Int64]` — because an argument is typed before the call meets its parameter type (WI-379's args-before-expected order; `hof_arg_hint` gives a constructor argument no hint), so the default came before the call's own evidence, the order §2 forbids. The default has to go in where the call's inference has finished, as an operation type parameter's does at the unconstrained-parameter check. Rows: `wantS(tag(n: 1))` loads (the parameter binds T); `let t = tag(n: 1)` then `wantI(t)` loads and `wantS(t)` is refused (no evidence at the let, so the default — or, if the boundary is the body, say which and why); `ap(first: 1)` under `sort AP[T1, T2 = T1]` is `AP[T1 = Int64, T2 = Int64]`. In a rule body the construction is a pattern and the parameter stays the clause's variable (decided on QV5W5, reading (b)).

