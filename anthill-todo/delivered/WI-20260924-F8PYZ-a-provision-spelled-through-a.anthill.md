## Attributes

- id: WI-20260924-F8PYZ-a-provision-spelled-through-a
- created: 2026-09-24T07:50:43Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-24T14:49:51Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PROVISION SPELLED THROUGH A SPEC ALIAS LOADS CLEAN AND PROVIDES NOTHING. With `sort StoreAlias = Store`, `sort FileStore provides StoreAlias[State = WIS] … end` loads with no diagnostic, but FileStore is not a `Store` provider: `Store.peek(wis(n: 9))` dies at run time 'operation has no body: Store.peek', while the control `provides Store[State = WIS]` returns 9. FOUND by WI-20260923-ZBWMC's review sweep; PRE-EXISTING, the same on the 09-20 binary. A silent skip, which the development principles forbid: the clause reads as a provision and records none that dispatch can use. Decide which is meant and make it so: either an alias names its target spec in a provision (resolve it when the clause is recorded, so the relation's spec base, `provided_spec_symbol`, the member-fit and operation-coverage checks and dispatch all see `Store`), or a provision must name the spec itself (refuse the clause loudly, naming the spec the alias stands for). ACCEPTANCE: a test that drives dispatch through an alias-spelled provision (or pins its refusal), with the direct spelling as the control; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-24T14:49:50Z — feedback — user

DELIVERED in 57bd3659. A spec clause reads a type alias as the spec it stands for (user decision: read through, not refuse) — every alias of a spec, bare or carrying bindings, in a provision (its `where` block and `default` mark with it), its `:- …` conditions, a sort's and an operation's `requires`. A positional binds the parameter the alias left open: over `sort S2A = Spec2[A = WIS]`, `S2A[B = NoSp]` and `S2A[NoSp]` are `Spec2[A = WIS, B = NoSp]`. What a clause cannot read an alias as is refused at load, naming why (`SpecAliasRefused`): an alias of no sort, a cyclic chain, a clause re-binding what its alias fixes, a name that is an alias AND owns members. A qualified spec name is resolved WHOLE (`provided_spec_symbol`, the `where`-block reader). Tests: wi_f8pyz_spec_clause_alias_test, 48 rows; twelve back-outs measured, ledger in its module doc. Spec: kernel-language §5.1. cargo-test: full workspace green via rustland/scripts/test.sh, 7535 passed, 0 failed. scaland-sbt-test: NOT re-run — nothing under scaland/ changed, and scaland records no provisions. Not read through yet, each loud: member access, the bare-spec sugar, a requires's scope, imports, binding blocks, type positions → WI-20260924-SNJPR. Filed from its review: SNJPR, R97NK (a public alias of an internal sort), EBAQA (duplicate aliases, rule R1), FS8M3 (a provision at an alias's address).

