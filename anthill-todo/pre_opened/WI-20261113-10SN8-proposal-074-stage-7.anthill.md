## Attributes

- id: WI-20261113-10SN8-proposal-074-stage-7
- created: 2026-11-13T23:02:10Z

- status: PreOpened
- status_agent: claude
- status_at: 2026-11-13T23:02:24Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1, WI-20261113-64272-proposal-074-stage-8-specs

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 7 — DICTIONARIES IN THE C++ AND RUST GENERATORS (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§1.4; parked, filed PreOpened). Group one, a dictionary built at load, emitted as a constant; group two passed where a template cannot unroll it (polymorphic recursion, T8); group three, a value with its dictionary (T9), as the host's own form of a value beside its table. Rows: T2, T4, T7, T8 and T9 generated, compiled and run in each. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

