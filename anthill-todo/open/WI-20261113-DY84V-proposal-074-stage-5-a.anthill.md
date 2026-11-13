## Attributes

- id: WI-20261113-DY84V-proposal-074-stage-5-a
- created: 2026-11-13T23:01:44Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:01:44Z

- acceptance: cargo-test

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 5 — A `REQUIRES` NAMING A SORT WITH CONSTRUCTORS IS REFUSED (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§2, "A sort with constructors is closed"). First, the count: every such `requires` in the test fixtures, by a traced run of the full gate (the standard library and the examples write none). Each is rewritten, its sort without constructors or the refinement removed, or deleted where it tests only that refinement. Rows: `X1 requires X` refused, naming both sorts; a data sort requiring a spec (`requires Eq[T = K]`) and a spec refining a spec (`Classical requires Constructive`) load and run as today. Spec: §8.2's refinement paragraph ("A sort that refines another is a subtype …") and §5.1's data-sort rule, which today names `provides` only. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

