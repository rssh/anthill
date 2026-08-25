## Attributes

- id: WI-20260824-5XBBQ-guardians-the-namespace-gate
- created: 2026-08-24T09:06:49Z

- status: Open
- status_agent: claude
- status_at: 2026-08-24T09:06:49Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260823-SPGBP-wire-the-reflect-kb

- tags: anthill-side-check

## Description

guardians: the namespace gate is a TEXT SCAN and two spellings walk through it. `namespace_violations` (rustland/anthill-core/tests/guardians_test.rs) scans `src.lines()` for the prefixes `namespace ` / `sort ` / `enum ` and refuses a name in the trusted namespace that is not under `guardians.agent.`. Anthill lets a declaration name its namespace by DOTTED PREFIX, and that spelling has none of those keywords in front of it — so a candidate can assert into the trusted namespace while every line the scan looks at is legal. MEASURED, both land `guardians.Checked` (the very fact `agent_is_safe` cites ABOUT the candidate), both queried back: (a) `sort guardians.agent.PoliteTriage … fact guardians.Checked(carrier: \"…\", spec: \"…\") … end` — the sort line is allowed because it starts with `guardians.agent.`, and the `fact` line carries no scanned keyword; (b) `namespace guardians.agent.forge … fact guardians.Checked(…) … end` — same, one namespace deeper. `harness_rejects_a_candidate_that_reopens_a_trusted_namespace` catches only the bare `namespace guardians` spelling it was written against. NOTE the gate refuses `namespace guardians.agent` itself by accident (`!name.starts_with(\"guardians.agent.\")` — the trailing dot), which is the kind of thing a text scan gets right and wrong for unrelated reasons. FIX: ask the question of DECLARATIONS, not of lines. The gate is a rule over the names a candidate declares, which is what the user's ask (\"rust should provide technical binding, the essence of the check should be in the example\") means here — the policy moves into `examples/guardians/lib/`, and rust supplies only what the source declares. DEPENDS on provenance: in a base built from [trusted…, candidate] nothing distinguishes the candidate's declarations from the library's, and `anthill.reflect.SourceUnit` — declared at reflect.anthill:164, documented 'Emitted by the loader after processing each file' — is emitted NOWHERE (grep across rustland returns zero hits), and lacks a `sorts` field besides. So: emit SourceUnit (with sorts), then write the gate as a rule joining it to SortInfo. A LAYERED kb does not close this on its own — a layer stops the candidate RETARGETING a trusted symbol, but a clause asserted under that symbol is still seen by a trusted goal, which is exactly the forgery above. ACCEPTANCE: both spellings above are refused, with the refusal naming the declaration; `agent/good.anthill` and a candidate declaring only under `guardians.agent.` still pass (the control that keeps this from degrading into refuse-everything); the gate is expressed in `lib/`, not in the test. Full workspace green via rustland/scripts/test.sh.

