## Attributes

- id: WI-20261101-C580V-a-call-s-type-argument-is-not
- created: 2026-11-01T06:09:41Z

- status: Open
- status_agent: claude
- status_at: 2026-11-01T06:09:41Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CALL'S TYPE ARGUMENT IS NOT INFERRED THROUGH A REQUIRES CLAUSE. Over `sort Wide { sort W = ? }`, `sort Narrow { requires Wide[W = Int64]; entity narrow }`, `sort Narrow2 { sort Q = ?; requires Wide[W = Q] }` and `operation takeAt[Y](x: Wide[W = Y]) -> Int64 = 4`, each of `takeAt(narrow())`, `takeAt(m)` with `m: Narrow2[Q = String]`, and `takeAt(n)` in `g[X](n: Narrow2[Q = X])` is refused with "expected a type for 'Y', got unconstrained" (measured 2026-11-01 on a5720275, and on its parent). The bracketed calls load: `takeAt[Int64](narrow())` loads, and `takeAt[String](narrow())` is refused since WI-20261020-G37HS, which made the typer's subsumption (`types_compatible`) read the instances a refining sort's clauses give it (`instances_through_requires`, shared with `type_admits`). Inference does not: `unify_types` (typing/unify.rs) has no refinement leg, so Y is never bound from the clause. EXPECTED: the three unbracketed calls infer Y (Int64, String, X) and load; `takeAt` over a sort whose clause names no argument (`requires Wide`) keeps its refusal; a sort with two clauses giving two instances of Wide is an explicit decision (refused as ambiguous, or the first), not a silent pick. Related: WI-20261025-27050 C6 (provision lookup does not climb a refinement with written arguments).

