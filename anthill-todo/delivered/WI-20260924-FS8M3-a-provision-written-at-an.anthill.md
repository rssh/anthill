## Attributes

- id: WI-20260924-FS8M3-a-provision-written-at-an
- created: 2026-09-24T14:36:28Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-27T20:12:32Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, provisions

## Description

A PROVISION WRITTEN AT AN ALIAS'S ADDRESS IS FILED UNDER THE ALIAS, AND DISPATCH NEVER FINDS IT. `sort FileStore … end`, `sort FSAlias = FileStore`, then `namespace FSAlias  provides Store[State = WIS]  … end`: the clause's PROVIDER is `FSAlias` (a `provides` clause names its provider by where it is written), the provision is filed under a sort with no operations, and `Store.peek(wis(n: 9))` dies at run time "operation has no body" — the same program with `namespace FileStore` returns 9. PRE-EXISTING (the same before F8PYZ, which covers the SPEC slot only; F8PYZ does refuse such a name when a spec clause NAMES it, since it then owns members of its own). Kernel-language §5.1 measures a `namespace` at an alias's address as a secondary entry, and 059 §Definitions leaves open whether an alias is a main entry at all. DECIDE: the entry is the alias TARGET's (read through, as a spec clause now reads its spec), or a `namespace` at an alias's address is refused, naming the target. ACCEPTANCE: dispatch driven through the chosen behaviour, with `namespace FileStore` as the control; full workspace green.

## Changes

### 2026-09-27T20:12:17Z — feedback — user

DELIVERED. A `provides` clause in a `namespace` at a type alias's address is a load error (LoadError::ProvidesAtAliasAddress, load_provides_clause), naming what the alias stands for and where to write it instead; for an alias that APPLIES its target the repair also says a clause at the head speaks for every instantiation. The clause is refused, not read through (user decision 2026-09-27); the entry's other members stay (§5.1). Spec: kernel-language.md secondary-entry table. Exact-vs-applied is read off the SCAN (alias_chain_applies over alias_heads/aliases_applying), after /code-review suspected the first cut's reading of the per-declaration load record (alias_targets) was load-order dependent — MEASURED not reproducible today (entry above the alias in one file and in an earlier file both pass under that reading, since every alias declaration is recorded before any provides clause loads), kept for order-independence by construction and a 20-line walk replaced by one existing call. Tests: wi_fs8m3_provides_at_alias_address_test, 6 rows; back-outs measured and recorded in its header (alias arm removed: the 4 refusal rows fail; first-link-only exactness: 3 fail; load-record reading: all pass, documented at that row; the 2 controls pass under every back-out). Full Rust workspace green except cmd_claim_test::claim_on_readonly_dir_raises_clean_error_not_panic, which fails only because this container runs as root (0o555 does not stop root); scaland sbt testFull 578/578.

