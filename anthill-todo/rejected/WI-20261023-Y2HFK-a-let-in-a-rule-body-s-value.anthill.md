## Attributes

- id: WI-20261023-Y2HFK-a-let-in-a-rule-body-s-value
- created: 2026-10-23T17:13:15Z

- status: Rejected
- status_agent: claude
- status_at: 2026-10-26T12:52:15Z

- acceptance: cargo-test

- tags: proposal-068

## Description

A `let` in a rule body's value slot is bound as written, not evaluated, also in a call's argument. MEASURED 2026-10-23 (38a260a6): over `operation idI(x: Int64) -> Int64 = x`, `rule letPure(?v) :- ?v <=> (let x = 3  x + 1)` answers `?v = let x = 3 in add(x, 1)` (the term), and `rule letInArg(?v) :- ?v <=> idI(let x = 3  x + 1)` the same; WI-20261013-R1W5A's typing of the clause masks a `let`'s own cell (`?v <=> (let c = Cell.new(3)  Cell.get(c))` loads) but the value is never computed. 068 §1.1 evaluates a rule-body application by the operation-body evaluator; a binder form in a value slot is not reached by it (the `if` in a rule body is noted in `dispatch_calls_in_occ` as "bound as it is written and is not evaluated"). ACCEPTANCE: `letPure(?v)` and `letInArg(?v)` answer 4, definite; the cell twin answers 3.

## Reason

Superseded by WI-20261011-2S5FP (user, 2026-10-26): a `let` in a rule body's value slot is one of the compound expressions that ticket evaluates. Its three rows (letPure, letInArg, the cell twin) are carried to 2S5FP, and WI-20261013-R1W5A depends on 2S5FP in its place.

