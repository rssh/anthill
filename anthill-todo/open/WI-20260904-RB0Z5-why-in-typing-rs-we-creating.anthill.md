## Attributes

- id: WI-20260904-RB0Z5-why-in-typing-rs-we-creating
- created: 2026-09-04T14:10:03Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T14:10:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

why in typing.rs we creating value with term with type_var:
Value::term(type_param_var_term(kb, Var::Global(vid))), at line 11667, we can't create Var
in value itself ?

ANSWERED 2026-09-04 — NO, NOT TODAY, AND THE REASON IS THE SLOT, NOT THE VALUE.
`Value::Var(Var::Global(vid))` is perfectly constructible; what refuses it is where the
type goes. A type value reaching a `TypeChild` slot must be a `Term` or a `Node`
(`value_to_type_child`: "A scalar / `Var` / `Entity` is a typer bug here"), and
`TypeChild::Interned` holds a `TermId` — so a variable in TYPE position is interned BY
CONSTRUCTION.

MEASURED, not read: swapping the mint to `Value::Var(..)` failed EVERY row of
`wi_50b2k_binder_inference_test` with "WI-342: non-type Value in a TypeChild slot:
Var(Global(VarId { .. }))".

AND THE OBJECTION BEHIND THE QUESTION IS CORRECT. `/code-review` raised the same thing
independently: `type_param_var_term` reaches its `alloc` fallback unconditionally for a
brand-new `VarId` — its own doc calls that "not a case any caller here is expected to
hit" — so every un-annotated binder leaves a refcounted `Term::Var` in the store that
nothing releases, against CLAUDE.md's rule that transient terms are not interned. The cost
is bounded by (binders x type-check passes), not unbounded, so it was recorded at the mint
rather than treated as a blocker.

THE SHARPER ANSWER, 2026-09-04 — WI-1079 HALF-LANDED, and the contradiction is inside ONE
file. Two sites disagree about the same question:

  `type_head` (WI-1079)          "A BARE LOGICAL VARIABLE IS A TYPE, and before this arm
                                  it was the one form that reached `Error` while being
                                  perfectly well-formed."
  `value_to_type_child` (WI-342) "A scalar/`Var`/`Entity` is a typer bug here (types are
                                  `Term`/`Node`)."

Both are about a variable in TYPE POSITION. WI-1079 admitted it at the READING end — the
`type_head` arm, and the `FlexVar` / `Skolem` reflect forms `extract` had been reporting as
`Error` — and the occurrence-BUILDING path never got the matching arm. So this ticket's
`Value::term(type_param_var_term(..))` is not "the slot's shape" as first answered here; it
is a WORKAROUND for a half-delivered rule: the variable is laundered through the term store
to get past a slot WI-1079 should have taught to accept it.

WHICH RE-FRAMES THE FIX. The third carrier is not a new idea, it is FINISHING WI-1079 AT
THE BUILDING END — and that is the argument that says it is a correction rather than a
feature. Whoever takes it should read WI-1079 first and check whether any OTHER builder
was left behind by the same half-landing; `value_to_type_child` was found by driving this
one mint, so it is a LOWER BOUND on that population, not a census.

THE FIX IS A THIRD `TypeChild` CARRIER, and it is written up in the sibling
WI-20260904-DTY3B ("why TypeChild accepts a hash-consed TermId"), which asks the same
question from the slot's side: keep `Interned` for shared persistent structure and `Node`
for the denoted spine, and add `Var(VarId)` for a transient inference variable. Then this
mint is `TypeChild::Var(kb.fresh_var(fresh))` with nothing interned. See DTY3B for what
must be measured first — the `_ =>` arms, where a new variant goes wrong silently.

