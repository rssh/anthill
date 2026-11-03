## Attributes

- id: WI-20261103-WEHYP-should-typevalue-type-value
- created: 2026-11-03T12:15:33Z

- status: PreOpened
- status_agent: claude
- status_at: 2026-11-03T12:15:41Z

- acceptance: cargo-test

- tags: typing

## Description

SHOULD `TypeValue.type_value` AND `TypePattern.admits` HAVE A SPECIAL STATUS WHERE A TERM IS NOT RUN — a fact, a rule-body goal, a precondition, a sort's goal? (user, 2026-11-03: "maybe we should think about special status of type_value (and type_pattern), but in future. Now — let Public[]"). Raised by WI-20261103-7FFQP part 3, which settled that a type-level variable holds a type and the facts it is checked against write the type as data, `Public[]` (kernel-language §4.4, §5.2). The user's first spelling for that type was `type_value(Public)`. Measured on 4828b593 over `import anthill.reflect.{TypeValue, TypePattern}` and `enum Level { entity Public; entity Untrusted }`:

- `fact flows_to(TypeValue.type_value[T = Public](), Public[])` — refused: "call-site type arguments `TypeValue.type_value[…](…)` are not supported here — … a rule-body goal, a `fact` head, a `constraint` and a `requires` / `ensures` contract expression have no channel for it". A call written in a fact is a pattern and is not run (proposal 068 §5).
- `operation send(body: Text[L = ?l]) -> Unit requires flows_to(?l, TypeValue.type_value[T = Public]()) = ()` — the same refusal, and the precondition then reads `flows_to(Public[], type_value)`.
- `rule r(1) :- TypePattern.admits[T = Level](Public[])` — the same refusal; `operation q() -> Bool = TypePattern.admits[T = Level](Public[])` loads.
- A sort goal `requires TypePattern.admits[T = Level](L)` is a syntax error: the goal form is a call by a plain name (grammar `_requires_goal_call`).

WHAT A SPECIAL STATUS COULD BUY, not decided: `TypeValue.type_value[T = X]()` written in a term would be the type `X` written as data, the same term as `X[]`; and `TypePattern.admits[T = X](t)` would be a goal wherever goals are written, so a sort could bound a parameter by subtyping — `requires TypePattern.admits[T = TrustLevel](Trust)` — where `is_entity_of(Trust, TrustLevel)` asks for an entity and admits the sort itself (proposal 062 §History rejected `sort Trust <: TrustLevel` as the wrong relation; this would be the relation `TypePattern` already defines). Questions before any work: does either take the bracket channel a rule body lacks, or is it a builtin form of its own; is `type_value[T = X]()` in a fact folded to `X[]` at load or kept as a call; and does a sort goal's grammar take a bracketed callee. PreOpened: future work, not on any current path.

