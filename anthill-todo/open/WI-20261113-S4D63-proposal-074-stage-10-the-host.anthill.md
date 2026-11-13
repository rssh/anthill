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

## Changes

### 2026-11-13T23:42:21Z — feedback — claude

Rows moved here from WI-20261105-CBRD2 (073 §6.1) with the user 2026-11-13, 074 §1.4 superseding 073's host entry: over sort Desc { sort T = ?  operation describe(x: T) -> Int64 }, Leaf providing Desc[T = Leaf] at 7, and gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x), interp.call("gen", &[leaf]) answers 7 — leaf fixes A = Leaf at the boundary and Desc[T = Leaf] is built there (measured on bf311200: 7; Desc.describe(leaf) 7; sum2(2, 3) 5; sum2(1.5, 2.5) 4.0; zeroOf() dies Internal 'requirement param __req_additive not bound'). has(s, "a") without s.O is refused naming s.O, the MySet value not holding its O: WI-20260923-DK0QJ's half (a) (its fixture landmines are in that ticket; the nested slot ranked by resolve_inner on the host route is the defect to drive). The three entries (call, call_with_witnesses, call_with_requirements) become one: a witness named by its sort is that sort's dictionary, and an operation's own requires — which call_with_requirements has no spelling for today (WI-822) — is passed the same way.

