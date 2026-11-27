## Attributes

- id: WI-20261127-ZMT3F-a-bare-not-x-in-a-rule-body
- created: 2026-11-27T08:34:30Z

- status: Open
- status_agent: user
- status_at: 2026-11-27T08:34:30Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A bare `not(x)` in a rule-body VALUE position never evaluates and is never refused: `rule a1 :- not(true) = false` answers one CONDITIONAL row, residual `eq(not(true), false)`, with every argument ground (found 2026-11-27 writing WI-20260911-5TK6B's tiny-sat over `Bool`).

MEASURED on the CLI of 2026-11-27 (f0fd9367c plus 5TK6B's change, which does not touch this path):
  1 `rule a1 :- not(true) = false` — conditional, residual `eq(not(true), false)`. The same with `import anthill.prelude.Bool.{not}` and without it.
  2 `rule a3(?r) :- ?r <=> not(true)` — `?r` unbound, residual `unify(?_, not(true))`.
  3 `rule a4 :- not(true) === false` — conditional, residual `struct_eq(not(true), false)`.
  4 Nested, the case that found it: `or(not(?p), not(?r)) = true` after `?p`, `?r` are bound stays a residual, so tiny-sat written with `not` answers every assignment conditionally instead of its two models.
CONTROLS: `anthill.prelude.Bool.not(true) = false` answers true; an operation body's `not(true)` evaluates (`operation o1() -> Bool = not(true)`, `?r <=> o1()` gives `false`); `or(true, false) = true` and `and(true, false) = false` answer true in a rule body.

LIKELY CAUSE, to verify: a bare `not` in a rule body resolves to the negation connective (the reified goal `not`, answered by a one-shot NAF search), and in a VALUE slot that functor has no value reading — the term is carried as data, neither evaluated nor refused. Silent: the answer is conditional, and under a negation or a quantified constraint a residual reads as undecided.

DECIDE at the work (spec first): in a value position, does an imported `Bool.not` win, so `not(true)` is `false` — or is a goal connective in a value slot refused at load, naming `Bool.not` as the spelling? Either way not silent.

ACCEPTANCE (every row driven): rows 1–4 answer definitely (or are refused at load with the sentence the decision picks); the controls unchanged; a back-out reddens rows 1–4.

