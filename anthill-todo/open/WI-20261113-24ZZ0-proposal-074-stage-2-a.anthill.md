## Attributes

- id: WI-20261113-24ZZ0-proposal-074-stage-2-a
- created: 2026-11-13T23:01:18Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:01:18Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 2 — A CONSTANT HOLDS A DICTIONARY (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§2; T12). `const ints: Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()` is folded at load, and `add2(ints, 2, 3)` answers 5. Today: "const has a non-foldable body". A constant at an application stage 1 refuses is refused as there. Its value in a data slot is not part of the stage (§2, "In a rule body"). Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

