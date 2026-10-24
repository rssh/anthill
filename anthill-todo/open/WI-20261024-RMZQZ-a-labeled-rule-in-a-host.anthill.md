## Attributes

- id: WI-20261024-RMZQZ-a-labeled-rule-in-a-host
- created: 2026-10-24T11:49:53Z

- status: Open
- status_agent: user
- status_at: 2026-10-24T11:49:53Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A LABELED RULE IN A HOST `provides … language … end` BLOCK DOES NOT LOAD — "unresolved name 'law'" — one head or several. Found during WI-20260908-NE0E4 (2026-10-24); MEASURED in rustland with a one-head and a two-head labeled rule.

WHY: pass 1 defines a rule's LABEL in the scope the rule is written in (rustland `scan_rule`, load.rs; scaland `DefinePass.defineRuleLabel`, Loader.scala), and neither pass 1 walks a host block's items — rustland's define walk has arms for `Item::Rule` and `Item::RuleBlock` only, scaland's for `RuleItem` / `RuleBlockItem` (its host blocks are deferred). So a host block's rule label is defined nowhere, and the loader's reference to it resolves to nothing.

WHERE IT BELONGS: the block's CLAUSES resolve in the TARGET sort's scope (§10.2; WI-20260821-TTHRK puts their heads' names there too), so the label belongs there as well. That scope is known only once the block's target resolves — after imports (pass 2) — which is why pass 1 cannot simply define it where it defines every other label.

TO DO: measure scaland first (expected the same, from the code). Define a host block's rule labels at the carrier's scope once the target resolves, in both implementations.

ACCEPTANCE (driven, not "it loads"): a labeled single-head and a labeled multi-head rule in a host block load; `using` / `rules_by_label` on the label reaches exactly the clauses stored under the carrier's predicates; two carriers' blocks writing one label do not collide; and `wi_ne0e4_multi_head_introduction_test` (whose header records this gap) gets its host-block multi-head row. Back-outs at each row's site.

