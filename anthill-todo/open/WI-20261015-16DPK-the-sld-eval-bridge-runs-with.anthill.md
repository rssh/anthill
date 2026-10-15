## Attributes

- id: WI-20261015-16DPK-the-sld-eval-bridge-runs-with
- created: 2026-10-15T20:50:55Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T20:50:55Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

THE SLD→EVAL BRIDGE RUNS WITH NO STEP CAP, so a rule-body call that does not terminate hangs resolution.

MEASURED 2026-10-15 on cc3d1a7d, and the same before WI-20260908-9WVT7 (found by its review): `operation loop(n: Int64) -> Int64 = if n < 0 then 0 else loop(n + 1)` with `rule loopD(?r) :- loop(0, ?r)` — the query does not return (killed at the timeout). A rule-body `Error.reify` of a looping thunk hangs the same way. The bridge's interpreter is `EvalConfig { bridge_mode: true, ..EvalConfig::default() }` (`run_in_bridge_interp`), whose `step_cap` is `None`; the CLI's backstop `CLI_STEP_CAP` is installed by `register_runtime` on the top-level interpreter only, so a bridged call is uncapped under `anthill run` too. `BRIDGE_REENTRY_CAP` bounds eval↔SLD re-entry, not steps.

kernel-language.md says the kernel uses stratification and loop detection to ensure rule evaluation terminates, and `EvalError::bridge_disposition` already reads `StepsExhausted` as a fault — which the bridge can never produce.

TO DECIDE: whether a bridged call is capped and at what — the CLI's cap, one `ResolveConfig` carries, or one derived from the search's remaining budget — and what an exhausted one answers (a fault, the search incomplete).

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): `loopD(?r)` returns, with the search marked incomplete and a message naming the cap; a long terminating bridged call still answers.

