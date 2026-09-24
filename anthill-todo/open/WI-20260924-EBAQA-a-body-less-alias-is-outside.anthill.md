## Attributes

- id: WI-20260924-EBAQA-a-body-less-alias-is-outside
- created: 2026-09-24T14:36:27Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T14:36:27Z

- acceptance: cargo-test, scaland-sbt-test

- tags: declarations, loader

## Description

A BODY-LESS ALIAS IS OUTSIDE RULE R1: TWO DECLARATIONS OF ONE NAME LOAD, AND THE FIRST ONE WINS. `sort SA = StoreA` and `sort SA = StoreB` in one namespace load clean; the loader keeps the FIRST (the `sort_alias_exists` dedup, and insert-if-absent in both alias maps), so swapping the two lines flips a program between running and "operation has no body" — in type positions as well as, since F8PYZ, in spec clauses. `sort Code { entity mk(…) }` beside `sort Code = Int64` also loads (kernel-language §5.2: "A body-less type ALIAS is outside the rule — stated as a limit, not covered"); F8PYZ refuses such a name in a SPEC CLAUSE (two readings), but type positions still pick one. DECIDE: extend R1 so a body-less alias is a declaration it counts — refuse alias+alias and alias+body at the declaration, naming both spans — or record why an alias is not a main entry (059 §Definitions leaves it open). ACCEPTANCE: both orders of each pair driven by a test; full workspace green.

