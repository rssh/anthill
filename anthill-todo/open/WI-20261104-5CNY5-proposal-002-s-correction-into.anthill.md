## Attributes

- id: WI-20261104-5CNY5-proposal-002-s-correction-into
- created: 2026-11-04T06:52:36Z

- status: Open
- status_agent: user
- status_at: 2026-11-04T06:52:36Z

- acceptance: review

- tags: proposal-002, typing

## Description

PROPOSAL 002'S CORRECTION INTO THE SPEC: kernel-language §4.4 still says an arrow records its parameter arity (WI-791) and that a call of a function value passes exactly that many arguments (WI-792), where proposal 002 §"Correction (2026-11-03)" (decided with the user 2026-11-03 and 2026-11-04) says every arrow is a `Function`. The rule there: `(p1: T1, ..., pn: Tn) -> R` is `Function[A = (p1: T1, ..., pn: Tn), B = R]` with no parameter count; two matches relate tuples, the tuple match (a value of one tuple type against an expected one, by name with width and permutation, §4.5, unchanged) and the application match (an application's arguments against the tuple of the function applied: a positional argument to the component at its position, a named one to the component with its label); `f((x, y))` is `f(x, y)`, and one tuple is always the argument list, for a call through a value and a call of an operation by its name alike; a callable meets a function type by label when the two tuples carry the same labels, and by a mapping of labels by position otherwise; a callable's own parameter count is checked where it becomes a value (WI-801). WHAT: rewrite §4.4's "Parameter lists correspond slot by slot", "An arrow records its parameter ARITY", "Applying a function value checks its arguments" and the `Function` note ("The equivalence is not exact ... `Function` states no arity"); the lambda paragraphs ("Applying a lambda", and the binder-annotation paragraph's "a conflict surfaces through the body's use of the binder", stale since WI-794); and §8's "the parameters of a lambda of several binders, which take their types from the type around it". Define both matches where first used, state the rule with one example each, no history. Show the text to the user before committing. ACCEPTANCE: the spec states 002's correction and 002's status line says so; documentation only.

