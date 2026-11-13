## Attributes

- id: WI-20261113-0FTHQ-proposal-074-stage-9-a-call
- created: 2026-11-13T23:22:34Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:22:34Z

- acceptance: cargo-test

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 9 — A CALL USES THE DICTIONARY ITS OPERATION IS HANDED (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§2, "Which dictionary a call uses"; T13; split from stage 1 after the third review). `viaParam` and `viaMember`, handed `Alt`'s dictionary, answer 2; a bracket naming `Leaf` outranks the handed dictionary; a call two handed dictionaries answer is refused at load. What a handed dictionary covers: `f(d: Additive[T = Meters], …) = sum2(a, b)` handed `ProjAdditive`'s dictionary (or any second provider at a type) answers through it; `o: Ord[T = Int64]` handed answers `WeakOrd.compare(1, 2)` through its chain; `o` beside `w: WeakOrd[T = Int64]`, and a lambda binder beside the operation's dictionary at one spec and type, refused at load. Until stage 1 lands, the rows hand a dictionary as the tree does today (`viaParam(Tag[T = Leaf])`), and stage 1 rewrites them with 073's rows. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

