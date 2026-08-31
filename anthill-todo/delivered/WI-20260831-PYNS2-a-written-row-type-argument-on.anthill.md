## Attributes

- id: WI-20260831-PYNS2-a-written-row-type-argument-on
- created: 2026-08-31T15:45:33Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-31T17:24:32Z

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

## Changes

### 2026-08-31T17:23:11Z — feedback — user

DELIVERY RECORD. Rust 6232 passed / 0 failed (36 result lines); scaland 524 / 0, untouched — it has no typing module at all (`core/src/main/scala/anthill/` is codegen, discrim, intern, kb, load, parse, resolve, span, subst, term), so there is nothing to mirror.

THE CENSUS CORRECTED THE TICKET, and that is the main result. "Today that spelling cannot be used at all" is measured FALSE. WHICH RECEIVER SHAPE the called operation has decides it, and only one of three was broken:

    self-receiver spec op (`go(self: Spec, …)`)          WORKS   unchanged
    carrier-param (`go(self: C, …)`), spec HAS a carrier  WORKS   unchanged
    carrier-param, NO carrier provides the spec YET       `?_`    WORKS

The self-receiver shape needed nothing — `self: Spec` unifies with the argument's `Spec[E = {Error}]`, and ordinary argument unification binds `Spec.E`. And the ticket's own motivating spelling, guardians' `ask(m: Llm[E = {}], p) effects {m.E, Error} = Llm.complete(m, p)`, ALREADY LOADED: `Llm` has two carriers. What was broken is a spec nothing implements yet — which is the state a program is in while it is being written, and why the minimal fixture hit it and guardians did not.

THE TICKET SAID "NOT DIAGNOSED — assert what the incurred row IS, do not assume the elimination is at fault". That was the right instruction and it held: the declared side was never at fault. The incurred `?_` is the spec's row parameter `E`, which binds through WI-609's REFLEXIVE arm of `carrier_param_receiver` (the receiver's carrier IS the op's own spec, so the receiver's type-args ARE the spec's params). INSTRUMENTED, that arm declined on exactly one leg: `spec=Spec carrier=Spec has_ctors=false has_providers=false`.

THE FIX is to ask the reflexive question ABOVE `carrier_is_abstract_spec`, whose PROVIDER leg this case has already answered — the carrier IS the sort declaring the operation, so spec-hood is settled by construction and the census of who implements it says nothing about it. The `!sort_has_constructors` leg is kept.

BACKED OUT (the arm returned to under the predicate): the two coverage tests red, the four controls stay green.

A WIDENING BUILT, MEASURED AND DECLINED: dropping `!sort_has_constructors` too makes a constructor-bearing sort's shape load and leaves the suite green (6227 / 0). Declined on what the flag it sets MEANS — an empty view marked `transitive` makes the call defer to eval, returning above `dispatch_spec_op_cached`, `MissingRequiresForSpecOp` and WI-1027's supplier-tie refusal, which every neighbour reserves for a value with no representation of its own. The hazard I first wrote down for it (a `Box[T = Box[T = Int64]]` whose `Box.wrap(x: T)` receiver is an ELEMENT, not a carrier) was BUILT AND DID NOT FIRE — recorded as not-driven rather than as the reason.

/code-review RAISED FOUR FINDINGS.

  1 (high) DISSOLVED ON MEASUREMENT, and it was right to raise. Backing out gives TWO errors and the fix gives none, so the second — `missing 'requires Spec5[E = …]' … covering ABSTRACT TYPE PARAMETER` — looked deleted. It is a CONSEQUENCE of the first: `E` was unpinned, and writing `E = {Error}` is exactly what stops it being an abstract parameter. THE SEPARATOR is the SELF-RECEIVER twin (same body-less op, same unimplemented spec, same written row), which loads clean — AND DOES SO ON THE BACKED-OUT TREE, so it is not my change producing it. The carrier-param shape now answers as its sibling always did. I built a repair first (the reflexive arm's `transitive` asking WI-325's witness question) and REMOVED it: it changed no row, because a spec with no providers has no candidate to be refused over. A branch that fires nowhere.
  2 (medium) VALID. Every fixture had a DEFAULT body, which takes the runnable-body early return and never reaches dispatch — so the half where finding 1 lives was untested. Added `a_bodyless_op_on_an_unimplemented_spec_agrees_with_its_self_receiver_twin`, with the self-receiver control.
  3 (low, latent) VALID AND FIXED. `statically_pinned_carrier` filtered with `!carrier_is_abstract_spec`, using the PROVIDER leg as its stand-in for "is this an abstract spec value?". Once the reflexive arm stopped needing a provider, a spec nothing provides reached that filter, answered "concrete", and was reported as a statically pinned CARRIER — the exact mis-pin its own WI-608 leg exists to prevent, in that leg's own words. It takes the spec symbol now and excludes a reflexive carrier outright. Measured benign either way (that population has no competing supplier to mis-pin TO), so no test reds on it; changed anyway so the invariant is asked rather than argued.
  4 (low) FIXED — RSRP5's route-C table row still said "unchanged".

ROUTE C IS JUDGED BY NOTHING, filed as WI-20260831-V25N3 rather than fixed here. `operation ask(s: Spec[E = {Beep}], …)` and `… [E = {Modify[Thing]}]` both LOAD CLEAN, at labels the RSRP5 gates refuse in a `provides` binding — so §5.5's "a row element is judged once, at its origin" is false for THIS origin. PRE-EXISTING, measured rather than assumed: the same hole is drivable on guardians' `Llm` (`E = {Error, LlmOutput}` loads clean), which has carriers, so the route was reachable there before this ticket. Not inline because the work is the CENSUS of every type position a row can be written in (parameter types, return type, entity field, sort type-param binding, `requires` clause), not the gate — whose judging half is already built and shared.

SPEC: §5.5's route-C paragraph said the spelling "does not work today at all". Rewritten to what it does, with the one shape still outside it, plus a paragraph pointing the judged-at-its-origin claim at V25N3. RSRP5's test header updated in three places — its route-C row, its "covers the projection route ENTIRELY" claim (that origin, not every origin), and its "NOT MEASURABLE" note.
