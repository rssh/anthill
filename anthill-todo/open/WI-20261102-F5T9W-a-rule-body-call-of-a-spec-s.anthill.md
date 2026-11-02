## Attributes

- id: WI-20261102-F5T9W-a-rule-body-call-of-a-spec-s
- created: 2026-11-02T06:53:06Z

- status: Open
- status_agent: claude
- status_at: 2026-11-02T06:53:06Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261102-Y9HSG-a-rule-body-call-woven-with

- tags: proposal-068

## Description

A RULE-BODY CALL OF A SPEC'S DEFAULT BODY IS ASKED FOR THE SPEC'S OWN `requires` AT THE CALL SITE, read at the spec's own parameters, instead of taking it with the dictionary the enclosing sort's requirement hands in. Found on WI-20260925-SHED7 step 3 (proposal 067; docs/brainstorms/fillable-collection-landscape.md §4.1, `fromList`; its §4.4: "C's dictionary … carries the element's as its sub-dictionary").

MEASURED on 5476eece: the program of WI-20261102-Y9HSG (the woven default body, which this depends on), with `Pc2` declaring `requires Iterable[C = C, Element = Element, E = {}]` (as `PersistentCollection` requires `Iterable`), is refused at load: "requirement `Iterable[C = Pc2.C, Element = Bit, E = {}]` of `Pc2` cannot be supplied for call to `Pc2.fromL`: element `C = Pc2.C` is unconstrained at this call site; this is a RULE-body goal, and nothing in the clause determines which `Iterable` instance it means". The element named is the spec's own `C`, not `Sat`'s, where `Sat`'s `requires Pc2[C = C, Element = Bit]` supplies the provider's dictionary, and the provision's own chain with it. With the stdlib's `E = Effect` the element named is `E = Pc2.Effect`, whatever the call's bracket or `Sat`'s requirement writes for `Effect` (both spellings measured, `Effect = {}` included); the stdlib's `PersistentCollection` with a `fromList` default body is refused the same (measured on a prototype, reverted).

CONTROL: `fromL` declared without a body and written by each provider, the same `requires` kept, answers 2 models.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): the program loads and answers 2 models (driven once WI-20261102-Y9HSG runs the body); a default body that reads the spec's requirement (an `Iterable` member over its carrier) answers through the provider's chain; the body-less control unchanged.

