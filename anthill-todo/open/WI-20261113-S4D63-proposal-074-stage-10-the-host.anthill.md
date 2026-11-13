## Attributes

- id: WI-20261113-S4D63-proposal-074-stage-10-the-host
- created: 2026-11-13T23:22:43Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:22:43Z

- acceptance: cargo-test

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 10 — THE HOST BOUNDARY (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§1.4, "A host call and the code generators"; split from stage 1 after the third review). `zeroOf()` from the host refused at the boundary naming `X`, `add2(7, 2, 3)` naming `x`; `sum2(2, 3)` 5 and `add2(intInstance(), 2, 3)` 5 as today. The Scala emitter measured on a dictionary parameter, and refusing it loudly if it emits anything else. Until stage 1 lands, `intInstance` is written as the tree writes it today, and stage 1 rewrites it. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

