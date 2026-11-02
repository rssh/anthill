## Attributes

- id: WI-20261102-Q5X28-a-rule-body-call-reached
- created: 2026-11-02T06:53:07Z

- status: Open
- status_agent: claude
- status_at: 2026-11-02T06:53:07Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

A RULE-BODY CALL REACHED THROUGH THE ENCLOSING SORT'S REQUIREMENT READS THE SPEC'S EFFECT ROW AS OPEN, so a pure call is never run, even where every provision and the requirement write `Effect = {}`. Found on WI-20260925-SHED7 step 3 (proposal 067; the stdlib's `PersistentCollection` declares `effects Effect = ?`, `insert … effects Effect`, and `List` / `SortedSet` provide it without writing `Effect`).

MEASURED on 5476eece: `Pc2` as in WI-20261102-Y9HSG, with `effects Effect = ?`, `ins` and `fromL` declared `effects Effect`, and `fromL` without a body, written by each provider (`Bag`'s through a helper); `Bag provides Pc2[C = Bag[T = T], Element = T, Effect = {}]`, a second provider the same, `Sat requires Pc2[C = C, Element = Bit, Effect = {}]`. `Sat[C = Bag[T = Bit]].model.takeN(100).length()` loads and raises `relation_floundered(goals: [unify(?, fromL(cons(t, cons(t, cons…))))])`: the call is ground and never run. With `Effect` unwritten everywhere, the same.

CONTROL: the program with no effect row answers 2 models.

TO DECIDE with the user: what an unwritten `Effect` reads as at such a call — the provision's (`List`'s `insert` is pure), or open, and then refused at load as a possibly effectful rule-body call (R1W5A's rule) — never a silent flounder.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): the program with `Effect = {}` written answers 2 models; the unwritten case answers as decided; the no-row control unchanged.

