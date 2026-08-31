## Attributes

- id: WI-20260830-A0MBV-should-checker-check-take-no
- created: 2026-08-30T20:28:15Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T20:28:15Z

- acceptance: cargo-test, scaland-sbt-test

- tags: guardians

## Description

SHOULD `Checker.check` TAKE NO `self`? A denial covers ACQUISITION, not POSSESSION, so `-Permission[Llm]` does not make a checker model-free -- and rejected/steering_checker.anthill is the proof, carrying `entity mk(oracle: Llm)` and calling `self.oracle.complete(p)` with the denial in its row. Its own comment states the rule: 'Being handed a model is permitted; `check` denies only acquisition.' What refuses it is `Permission[Reveal]` on `LlmOutput.text_of` -- it may ask, and may not read the answer.

THE PROPOSAL. Declare `operation check(src: Source, spec: Symbol) -> CheckResult` with no carrier parameter. With no `self` there is no field to hold a model in, so `-Permission[Llm]` would become total over the checker BY CONSTRUCTION rather than by a further row.

THE COST, AND IT IS THE REASON THIS IS A QUESTION RATHER THAN A CHANGE. steering_checker.anthill is THE ONLY FIXTURE IN THE EXAMPLE THAT MENTIONS `Reveal` (measured: `grep -rl Reveal fixtures lib` returns it, lib/harness.anthill, lib/llm.anthill, lib/spec.anthill). Drop `self` and the steering attack becomes INEXPRESSIBLE rather than refused, so nothing measures `Permission[Reveal]` any more -- prevention by construction bought at the price of the control for the mechanism that does the preventing today. A stateless checker also cannot carry configuration (a target base, a budget, a timeout), which a real one needs.

WHERE THIS CAME FROM: writing the ICTERI-2026 article. The paper said '`check` declares `-Permission[Llm]`: the component ... may not acquire a model, SO IT CANNOT BE STEERED BY ONE'. The 'so' is false, and steering_checker.anthill is the counterexample shipped in the distribution. The article is fixed (it now names `Permission[Reveal]` as what stops steering); the design question is this ticket.

ACCEPTANCE: a decision recorded either way. If self is dropped, a replacement control for `Permission[Reveal]` must exist before the fixture goes, and the configuration question answered.

