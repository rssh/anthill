## Attributes

- id: WI-20260831-PYNS2-a-written-row-type-argument-on
- created: 2026-08-31T15:45:33Z

- status: Open
- status_agent: user
- status_at: 2026-08-31T15:45:33Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A WRITTEN ROW TYPE-ARGUMENT ON A PARAMETER NEVER REACHES THE CALL'S EFFECT INSTANTIATION, so an operation that projects it is refused `got undeclared effect: ?_` — with the DECLARED side resolving correctly, which is what makes the message unreadable.

MEASURED (found while censusing routes for WI-20260831-RSRP5, whose gates the `?_` swallows):

```
sort Spec
  sort C = ?
  effects E = ?
  operation go(self: C, p: String) -> Out effects {E, Error} = out(v: p)
end

operation ask(s: Spec[E = {Error}], p: String) -> Out
  effects {s.E, Error} = Spec.go(s, p)
```

  -> type mismatch in ask.effects (op-effects): expected declared: [Error, Error],
     got undeclared effect: ?_

THE TWO HALVES DISAGREE ABOUT THE SAME SLOT. `s.E` on the DECLARED side eliminates correctly — `expected declared: [Error, Error]` proves the written `E = {Error}` was read. The BODY's call to `Spec.go(s, p)` incurs the spec op's `{E, Error}` with `E` UNBOUND, so an unresolved row var surfaces as an incurred effect. Same parameter, same written binding, read on one side and not the other.

CONTROLS, both measured, which is what says this is not about the label:
  * `E = {}` gives the identical `got undeclared effect: ?_`.
  * The same shape with the receiver typed at a CARRIER (guardians' `h.generate(llm, p)` with `llm: LiveLlm`) works — WI-20260830-APWM3's acceptance test drives it. So the defect is specific to a row bound by a WRITTEN TYPE ARGUMENT rather than by a `provides` binding.

WHY IT MATTERS BEYOND THE MESSAGE. This is the third of three routes by which a concrete row can reach a projection (the others: a `provides` binding, and a sort's bound alias — both delivered under RSRP5). It is the only one where the row is written AT THE USE SITE, which is exactly where a caller would write it to say "I take a pure model" or "I take one that touches the world". Today that spelling cannot be used at all.

NOT DIAGNOSED. The declared-side elimination runs in `check_operation_bodies` against `param_map`; the call-side instantiation is `check_apply`'s. Which of the two loses the binding is not established here — start by asserting what `Spec.go(s, p)`'s incurred row IS, not by assuming the elimination is at fault.

ACCEPTANCE: `operation ask(s: Spec[E = {Error}], …) effects {s.E, Error} = Spec.go(s, p)` LOADS, with a control at `E = {}` that must ALSO load, and one at `E = {External}` under a declared row that omits `External` which must still be REFUSED (naming `External`, not `?_`) — otherwise the fix has merely silenced the row rather than bound it.

