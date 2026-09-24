## Attributes

- id: WI-20260924-FS8M3-a-provision-written-at-an
- created: 2026-09-24T14:36:28Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T14:36:28Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, provisions

## Description

A PROVISION WRITTEN AT AN ALIAS'S ADDRESS IS FILED UNDER THE ALIAS, AND DISPATCH NEVER FINDS IT. `sort FileStore … end`, `sort FSAlias = FileStore`, then `namespace FSAlias  provides Store[State = WIS]  … end`: the clause's PROVIDER is `FSAlias` (a `provides` clause names its provider by where it is written), the provision is filed under a sort with no operations, and `Store.peek(wis(n: 9))` dies at run time "operation has no body" — the same program with `namespace FileStore` returns 9. PRE-EXISTING (the same before F8PYZ, which covers the SPEC slot only; F8PYZ does refuse such a name when a spec clause NAMES it, since it then owns members of its own). Kernel-language §5.1 measures a `namespace` at an alias's address as a secondary entry, and 059 §Definitions leaves open whether an alias is a main entry at all. DECIDE: the entry is the alias TARGET's (read through, as a spec clause now reads its spec), or a `namespace` at an alias's address is refused, naming the target. ACCEPTANCE: dispatch driven through the chosen behaviour, with `namespace FileStore` as the control; full workspace green.

