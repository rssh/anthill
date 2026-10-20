## Attributes

- id: WI-20261017-DYX5E-variance-aware-dispatch
- created: 2026-10-17T16:47:20Z

- status: PreOpened
- status_agent: claude
- status_at: 2026-10-17T16:47:25Z

- acceptance: cargo-test, scaland-sbt-test

## Description

VARIANCE-AWARE DISPATCH THROUGH THE SUBTYPE RELATION (user, 2026-10-17, from WI-20260908-9WVT7's sixth and seventh reviews). Which provision answers a call, and whether a requires in scope covers it, is decided by meeting the provision's head, or the requirement, with the call's type through the subtype relation. Today the whole head is read covariantly, with one exception: an arrow's parameter is met as itself and its result through the subtype relation (spec §8.7). The question is to read each position of the head by its declared variance: a covariant position (a result, a covariant parameter) through the subtype relation; a contravariant one (an arrow's parameter) through the supertype relation, so a provision at (Dog) -> Int64 answers a call at (Animal) -> Int64 (a function taking any animal is a function taking dogs), which is refused today; an invariant position (an invariant sort parameter, a mutable place) exactly. The same for a requires in scope covering a call's requirement: one direction only. Measure first what the current rule does at an invariant parameter (a provision at Cell[V = Animal] and a call at Cell[V = Dog]). Spec: §8.7 'Which one a call gets'; §5.2, two arrow requirements are one binding only where their results are the same.

