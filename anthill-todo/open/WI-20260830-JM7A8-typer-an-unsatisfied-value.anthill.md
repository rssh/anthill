## Attributes

- id: WI-20260830-JM7A8-typer-an-unsatisfied-value
- created: 2026-08-30T11:56:12Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T11:56:12Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER: AN UNSATISFIED VALUE PRECONDITION SUPPRESSES THE SAME CALL'S EFFECT ATTRIBUTION, SO AN INDEPENDENT ROW VIOLATION AT THAT CALL GOES UNREPORTED.

MEASURED on `examples/guardians`. Give `Email.send` a value precondition naming its FIRST argument -- `send(to: Address, body: Text[Public]) requires deliverable(to)` -- beside the guarded effect it already carries, `(Permission[Outbox] :- external_addr(to))`. Then `fixtures/agent/rejected/computed_recipient.anthill` and `.../letbound_recipient.anthill` report ONLY:

    type mismatch in guardians.Email.send.requires: expected precondition
      `deliverable(who)` provable at the call site, got unsatisfied precondition

and the line those two fixtures exist for --

    type mismatch in run.effects (op-effects): expected declared:
      [External, llm.E, Error], got undeclared effect: Permission[T = Outbox]

-- is GONE from both. The two failures are INDEPENDENT: the precondition is a proof obligation over the KB, the effect is a row the body incurs. Reporting one and dropping the other is the loud-over-silent rule failing in the direction that matters, because the surviving diagnostic looks complete.

ISOLATED. The DECLARED-row comparison still fires -- a variant of `computed_recipient` that also declares `Filesystem` still reports "effects must not widen" beside the precondition error -- so the suppression is not a global bail-out on the operation. It is the CALL's inferred effects that are not attributed once its precondition fails.

WHY IT IS NOT MERELY COSMETIC. A test asserting the second diagnostic goes red, and the natural repair -- update the expected substring -- silently changes what the test measures. In guardians that would have retired the only two rows that measure §5.5's conservative direction on an undecided guard, which no other fixture in the suite exercises. The general shape: a contract added to an operation can DELETE coverage elsewhere without deleting a test.

SCOPE. Decide and implement the intended rule. Two candidates: (a) attribute the call's declared effects even when its precondition is unsatisfied, so both diagnostics surface -- the call's effects are read off the DECLARATION and do not depend on the precondition holding; (b) keep the suppression and say so, in which case the loader should state at the site that further checks on this call were skipped, so a reader knows the error list is truncated. (a) looks right and cheap; (b) is the fallback if effect attribution genuinely needs the precondition's bindings.

ACCEPTANCE: a call whose precondition is unsatisfied AND whose effect the caller has not declared reports BOTH, in one load. CONTROL: a call whose precondition is unsatisfied and whose effects ARE covered still reports exactly one error. Regression: nothing in the workspace suite changes verdict.

RECORDED AS: examples/guardians/docs/design/measured.md C2a, which is also why `Email.send`'s shipped precondition is on `body` rather than on `to`.

