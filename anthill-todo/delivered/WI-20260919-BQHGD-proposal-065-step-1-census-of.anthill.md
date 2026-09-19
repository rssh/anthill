## Attributes

- id: WI-20260919-BQHGD-proposal-065-step-1-census-of
- created: 2026-09-19T15:19:28Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-19T15:39:22Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

PROPOSAL 065 STEP 1 — CENSUS OF RIGID VALUE READS, AND THE OVERRIDE-SUBSET PROBE. Measurement only; changes no behaviour. Everything after it in 065's order of work is sized by it.

(1) THE CENSUS. Run 065's rule — "a rigid type parameter read in VALUE position with no `requires TypeValue[T = B]` in scope" — in the TYPER as a COUNT, not a refusal, over the stdlib and every test fixture. Report each site as its operation, its line and column, the parameter it reads, and the parameter's kind: an operation bracket, a sort parameter, or an inline signature variable. Include `Type`-slot ARGUMENTS (`facts_of(kb, T)`, `is_modifiable(T)`) — they are value reads too. Grep says the stdlib has no operation returning `Type` and ten test files contain one; that is only the WRITTEN `-> Type` population and is not the census. NOT the evaluator: R541X's `refuse_unbound_type_param` marks the same two read shapes but counts only what a test happens to execute.

(2) THE §3 PROBE. 065 §3 says an implementation's OPERATION-level `requires` must be a subset of its spec operation's, and guesses that `check_override_refinement`'s precondition leg already refuses an added clause. The basis for the guess is that the implementation's `requires` list is shared by logical preconditions and spec-requirement clauses — the loader injects `EffectsRuntime[…]` into it. DRIVE it: a spec `f[B](x: B) -> Int64` with an override `f[B](x: B) -> Int64 requires Eq[T = B]`. Report which of three it is: refused with the strengthened-precondition message, refused some other way, or LOADED. Also report the direct-call spelling, the provider's member called with its carrier pinned, which 065 says must be refused too.

DELIVERABLE: the census table and the probe verdict, recorded on this ticket and in 065 §6. If (2) loads, say so; the leg is then step 3's to add. ACCEPTANCE: measurement, with no code change kept. The probe fixtures are kept as tests of the CURRENT behaviour, each saying which step will change it.

## Changes

### 2026-09-19T15:39:17Z — feedback — user

DELIVERED. Census (full workspace, typer-side count): 19 unique sites, all in five test files, ZERO in stdlib/anthill-stl/examples; every site the resolved TypeValue form. One site (h054k dq[K]) is a simp argument that inlining places in a TYPE position, so step 3 must judge reads after @[simp] expansion. Probe: an ADDED op-level clause is already refused; a clause RESTATED over the op's own type parameter is OVER-refused (type params not aligned), a ground restatement loads, a spec-only clause loads, a provider-sort clause over its own param loads. Recorded in 065 §6 and on N31XX; rows pinned in wi_bqhgd_override_requires_subset_probe_test. The temporary census hook is removed.

