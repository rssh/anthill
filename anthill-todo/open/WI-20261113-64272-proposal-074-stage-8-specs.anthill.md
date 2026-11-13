## Attributes

- id: WI-20261113-64272-proposal-074-stage-8-specs
- created: 2026-11-13T23:02:01Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:02:01Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1, WI-20261113-FCMJA-proposal-074-stage-6-x-t-read

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 8 — SPECS OVER A TYPE CONSTRUCTOR (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§6; H1–H5, G1–G3). An operation's higher-kinded parameter, `lift[F[T]]` (H2), fixed by a call's bracket, an argument or the expected type; a sort filling a constructor slot by its unwritten parameters in order (H4), `provides Monad[M = Box]` loading; a requirement's constructor read through it (`requires Monad[M = F]` making `M[T = A]` read `F[T = A]`, refused today); `m.M[Int64]` off a dictionary parameter (H1); §5.4's member spelling at a higher-kinded member (H3, which loads and dies today); a constructor's dictionary a sub-dictionary of a provider over it (H4's `OptionTMonad`); `TypeValue` at a sort with unwritten parameters (H5, with stage 6's value read); a row parameter by use (G1–G3). Depends on stages 1 and 6. Rows: H1–H5 and G1–G3 driven to their answers. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

