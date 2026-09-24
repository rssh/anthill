## Attributes

- id: WI-20260823-ZW6N5-lf1-s-codegen-track-cannot
- created: 2026-08-23T09:43:54Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-24T19:57:25Z

- acceptance: cargo-test

## Description

LF1'S CODEGEN TRACK CANNOT SCAFFOLD A SPEC THAT WAS SPLIT BY CONTROLLER. `examples/webots-modelling/lf1/build.sh` runs `anthill codegen cpp-project --namespace anthill.examples.lf1` and exits 1 with WI-761's required-header refusal: "no entities, sum sorts, sort-with-operations, or constants to emit directly under namespace 'anthill.examples.lf1'". The diagnosis is a DIVERGENCE, not a regression in either half. `run_codegen_cpp_project` (anthill-cli/src/main.rs) reads `Generated` facts by PREFIX — so the two controllers resolve fine — but emits exactly ONE namespace header, from `--namespace` ITSELF, named after its last segment (`lf1.hpp`). That design assumes the umbrella namespace holds the shared types. It did: the stale `build/controllers/*/lf1.hpp` on disk carries `Pose`, `Controls`, `Waypoint`, `WaypointSequence`, `FollowerState` under `namespace anthill::examples::lf1`. Commit 1490af99 (2026-04-26, 'lf1: split spec by controller and sensor') then moved every declaration into sub-namespaces — `anthill.examples.lf1.leader`, `.follower_gps`, `.follower_transponder`, `.safety.*`, `.webots.*` — and nothing is declared directly under `anthill.examples.lf1` any more. build.sh, written the same day (1de91351), still names the umbrella. So the scaffold has been dead since April; only the PROOF track (discharge.sh) is exercised by CI, via `prove_tactic_test::legacy_lf1_proofs_unchanged`, and it passes 14/14 unsat. TWO CANDIDATE FIXES, and the choice is a design call, not a typo repair. (a) SPEC REORG — move the shared entities back to `anthill.examples.lf1` and leave only per-controller operations in the sub-namespaces; touches leader/follower_gps/follower_transponder plus every safety_* import. (b) CODEGEN — teach cpp-project to emit a header per sub-namespace under the prefix (or aggregate them into the primary one), and have each controller include what it needs; this changes the tool's one-header contract and needs the include-wiring in the generated `*_main.cpp` shims to follow. FOUND WHILE DELIVERING WI-897, which is unrelated: cpp-gen does not depend on smt-gen, and the same failure reproduces with WI-897's spec edit reverted. ACCEPTANCE: `./build.sh` exits 0 and the scaffolded tree compiles under `clang++ -std=c++17 -fsyntax-only -Wall -Wextra` as the README claims; a test drives the scaffold so it cannot rot silently again — the absence of one is why this went four months unnoticed.

## Changes

### 2026-09-24T19:57:37Z — feedback — user

DELIVERED in 69949a6c as candidate (b), and (a) alone could not have worked: the controllers' traits classes live in the sub-namespaces, so an umbrella header would never contain them. cpp-project now roots each controller's HEADER CLOSURE (emit_namespace_header_closure) at the namespace declaring it; --namespace only selects Generated targets. A second defect sat behind the first: the primary header was written under its LAST segment (lf1.hpp) while every generated include spells the full path. Measured 2026-09-24: build.sh exits 0; every shim and generated header passes clang++ -std=c++20 -fsyntax-only -Wall -Wextra; real Webots make links Leader/Follower (macOS needs WEBOTS_HOME=/Applications/Webots.app plus WEBOTS_HOME_PATH=.../Contents, docs fixed); discharge.sh still 14/14. LEFT OPEN BY DECISION (user, 2026-09-24): TransponderFollowerController's Generated fact is PARKED (commented, realization.anthill) because it has no _main.cpp shim, which needs the leader-pose radio no controller has wired; cpp-project now REFUSES a controller with no entry point instead of scaffolding a folder that fails at link. Restore the fact together with that shim. Guard: anthill-cli wi_zw6n5_lf1_scaffold_test.

