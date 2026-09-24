## Attributes

- id: WI-20260924-F8PYZ-a-provision-spelled-through-a
- created: 2026-09-24T07:50:43Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T07:50:43Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PROVISION SPELLED THROUGH A SPEC ALIAS LOADS CLEAN AND PROVIDES NOTHING. With `sort StoreAlias = Store`, `sort FileStore provides StoreAlias[State = WIS] … end` loads with no diagnostic, but FileStore is not a `Store` provider: `Store.peek(wis(n: 9))` dies at run time 'operation has no body: Store.peek', while the control `provides Store[State = WIS]` returns 9. FOUND by WI-20260923-ZBWMC's review sweep; PRE-EXISTING, the same on the 09-20 binary. A silent skip, which the development principles forbid: the clause reads as a provision and records none that dispatch can use. Decide which is meant and make it so: either an alias names its target spec in a provision (resolve it when the clause is recorded, so the relation's spec base, `provided_spec_symbol`, the member-fit and operation-coverage checks and dispatch all see `Store`), or a provision must name the spec itself (refuse the clause loudly, naming the spec the alias stands for). ACCEPTANCE: a test that drives dispatch through an alias-spelled provision (or pins its refusal), with the direct spelling as the control; full workspace green via rustland/scripts/test.sh.

