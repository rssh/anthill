## Attributes

- id: WI-20260830-A0MBV-should-checker-check-take-no
- created: 2026-08-30T20:28:15Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-08T14:10:07Z

- acceptance: cargo-test, scaland-sbt-test

- tags: guardians

## Description

SHOULD `Checker.check` TAKE NO `self`? A denial covers ACQUISITION, not POSSESSION, so `-Permission[Llm]` does not make a checker model-free -- and rejected/steering_checker.anthill is the proof, carrying `entity mk(oracle: Llm)` and calling `self.oracle.complete(p)` with the denial in its row. Its own comment states the rule: 'Being handed a model is permitted; `check` denies only acquisition.' What refuses it is `Permission[Reveal]` on `LlmOutput.text_of` -- it may ask, and may not read the answer.

THE PROPOSAL. Declare `operation check(src: Source, spec: Symbol) -> CheckResult` with no carrier parameter. With no `self` there is no field to hold a model in, so `-Permission[Llm]` would become total over the checker BY CONSTRUCTION rather than by a further row.

THE COST, AND IT IS THE REASON THIS IS A QUESTION RATHER THAN A CHANGE. steering_checker.anthill is THE ONLY FIXTURE IN THE EXAMPLE THAT MENTIONS `Reveal` (measured: `grep -rl Reveal fixtures lib` returns it, lib/harness.anthill, lib/llm.anthill, lib/spec.anthill). Drop `self` and the steering attack becomes INEXPRESSIBLE rather than refused, so nothing measures `Permission[Reveal]` any more -- prevention by construction bought at the price of the control for the mechanism that does the preventing today. A stateless checker also cannot carry configuration (a target base, a budget, a timeout), which a real one needs.

WHERE THIS CAME FROM: writing the ICTERI-2026 article. The paper said '`check` declares `-Permission[Llm]`: the component ... may not acquire a model, SO IT CANNOT BE STEERED BY ONE'. The 'so' is false, and steering_checker.anthill is the counterexample shipped in the distribution. The article is fixed (it now names `Permission[Reveal]` as what stops steering); the design question is this ticket.

ACCEPTANCE: a decision recorded either way. If self is dropped, a replacement control for `Permission[Reveal]` must exist before the fixture goes, and the configuration question answered.

## Changes

### 2026-09-08T14:06:21Z — feedback — user

SUPERSEDED BY WI-20260908-K5HVE. The question is answered YES — `check` should take no carrier parameter — and BOTH premises this ticket argues from turn out false, so the reasoning is recorded here rather than carried forward.

THE STATED COST EXPIRED. This ticket weighs dropping `self` against losing the only fixture that mentions `Reveal`. WI-20260829-MCKTE deleted `Permission[Reveal]`, the `LlmOutput` wrapper and `steering_checker.anthill` outright; the seal on `Text`'s `raw` projection (§8.6 `internal`, constructor + projection + match) does that work generally now, and `rejected/reads_text.anthill` is its successor. There is no `Reveal` control left to protect.

THE SECURITY ARGUMENT DOES NOT HOLD EITHER, and this is the half worth keeping. A candidate provides `Triage` into a DISCARDABLE LAYER (`KB.loaded`, WI-SPGBP) and never selects the base pipeline's carriers, so a hostile `provides Checker` is not in the threat model — 'who guards the guard' does not apply to a sort only the deployment writes. Making `check` carrier-free is therefore an INTERFACE argument, not a containment one.

AND THE PREMISE UNDER BOTH: `-Permission[Llm]` on `check` constrains nothing today. `LoadChecker.check` is host-bound, so the row bounds its DECLARED row while its body sits outside the row's reach — the boundary `harness.anthill` already admits for the `Source` seal. Measured: `guardians_check` is registered at arity 3 and never reads `args[0]`. The denial's whole measured content is that a candidate declaring the row and violating it is refused, shown on seven counterfactual programs the pipeline never asks a model to write. Binding the real checker means writing `check` in anthill, which needs WI-20260908-9WVT7 (047's `Error` layer).

MEASURED WHILE DECIDING THIS, and carried into K5HVE: deleting `provides Checker[C = MintingChecker]` leaves that fixture's refusal byte-identical (controls: lib alone loads at 3154 facts; `checker.anthill` sans `provides` loads at 3163). So the `Checker` spec does no measurement work at all, and the change K5HVE describes is larger than this ticket's description — this project's own test for when a follow-up gets its own ticket.

