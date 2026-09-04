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

THE FIX IS A THIRD `TypeChild` CARRIER, and it is written up in the sibling
WI-20260904-DTY3B ("why TypeChild accepts a hash-consed TermId"), which asks the same
question from the slot's side: keep `Interned` for shared persistent structure and `Node`
for the denoted spine, and add `Var(VarId)` for a transient inference variable. Then this
mint is `TypeChild::Var(kb.fresh_var(fresh))` with nothing interned. See DTY3B for what
must be measured first — the `_ =>` arms, where a new variant goes wrong silently.

