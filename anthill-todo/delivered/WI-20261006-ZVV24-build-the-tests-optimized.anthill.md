## Attributes

- id: WI-20261006-ZVV24-build-the-tests-optimized
- created: 2026-10-06T04:53:11Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-06T11:38:11Z

- acceptance: cargo-test

- tags: test-infra

## Description

BUILD THE TESTS OPTIMIZED — measure, choose the level, land `[profile.test]` (lever A1 of docs/design/test-infrastructure.md §4, with its step 0 and the cheap experiments of §4 A5 / §6 C3 pulled into the same measuring session).

WHY. One gate on the 6-core laptop is 3 h 27 min (2026-10-05, §1), and one number explains it: a test that loads the stdlib pays ~4.85 s for the load in the debug profile, and `rustland/Cargo.toml` has no `[profile]` section, so the tests run at `opt-level = 0`. The same load built `--release` is 0.62 s — 7.9× (§2.5), uniform across parse / full / pre-typer / incremental, so it is the code generation and not one pass. Nothing else in the doc is this cheap, and every later lever is sized from the table this item produces.

MEASURE, on an idle machine (check the load average first — the 2026-10-05 numbers were taken with a gate in flight and say so):

1. Re-take §2.1's four numbers at the dev profile with `docs/measurements/test-infrastructure/bench_load.rs` (recipe in §10).
2. Fill §2.5's empty rows — `[profile.test] opt-level = 1`, `2` and `3`, with `debug-assertions` and `overflow-checks` ON: the four bench numbers; the rebuild of `anthill-core` + `wi_tests` after a one-line edit to `kb/load.rs` (`cargo test --no-run`); the cold build. Also `debug = "line-tables-only"` as a compile-side variant, and `[profile.dev.package."*"] opt-level = 3` once to confirm §4 A1's guess that it is near-useless here, then drop it.
3. Close the gap in the model before anything is sized from it. §2.4's fit — 3 100 load call sites × 4.85 s = 15 000 s of thread-time against 7 801 s of `wi_tests` wall — implies an effective parallelism of about 2 on a 6-core box, while §2.5's projection ("~5 min of `wi_tests`") divides by 6; scaling the measured wall by the measured ratio gives ~16 min instead. Two measurements say which: (a) a counter of EXECUTED loads in the one recipe (`try_load_kb_named_prepared_with`, `anthill-core/tests/common/mod.rs`) — 3 100 is a count of call SITES, and a helper called by twenty tests is one site; (b) the bench at 1 / 6 / 12 concurrent threads — do loads scale, or do the allocator and memory bandwidth cap them. If (b) scales badly: `mimalloc` as `#[global_allocator]` in the `wi_tests` aggregator, and `ANTHILL_TEST_THREADS=6` against 12, in the same session.
4. One full `rustland/scripts/test.sh` run at the chosen level; §1's per-binary table re-taken in the same format.

DECIDE (the user's, §8.1): the level — §4 A1's rule is the highest one at which the one-line-edit rebuild stays tolerable in the edit loop, given the gate saving at that level.

WATCH FOR. `cargo build` and `cargo test` stop sharing the `anthill-core` artifact (one more library compile per profile, not per run). A test whose verdict depends on the profile — stack depth, timing, a debug-only check — is a finding to report, not to adjust around. The spawned CLI binaries (`CARGO_BIN_EXE_anthill-todo`, the `anthill` one) are built by the same `cargo test` under the same profile, so `cmd_tests` (46 min) and `cli_tests` (7 min) should shrink with the load; the table confirms or refutes it.

DONE WHEN: the gate is green at the chosen level; §1, §2.1 and §2.5 carry the new numbers with date, machine and raw files under `docs/measurements/test-infrastructure/`; `rustland/CLAUDE.md` says what profile the tests run at and why. The re-taken table is what decides the follow-ons — a re-profile for hashing (A2, whose 22 % share is partly un-inlined SipHash at opt-level 0), the frontier-driven passes (A3), `KnowledgeBase: Clone + Send`, WI-059, the in-process CLI entry (§5.4 a). None of them is filed, on purpose.

## Changes

### 2026-10-06T11:37:52Z — feedback — claude

DELIVERED — as a per-run setting in `rustland/scripts/test.sh`, NOT as `[profile.test]` in the manifest. A full run builds `anthill-core` at opt-level 2 and the two tree-sitter crates at 3 (three `--config` lines); a selected run stays on the plain dev profile; `ANTHILL_TEST_OPT=0|2` overrides either. DECIDED by the user, 2026-10-06: first "always on", reversed to "gate only" once the per-module rebuild costs were measured.

MEASURED (docs/design/test-infrastructure.md §1.1, §2.4, §2.5, §4 A1, §7; raw files `docs/measurements/test-infrastructure/*2026-10-06*`): one stdlib load 2.11 s -> 0.31 s on a quiet machine (level 3 no faster under 12 threads, level 1 gives up 2.5x); the gate 3 h 12-27 min -> 15 min 45 s warm, 19-31 min with rebuilds; 8560 / 0 / 14 in four of five optimized runs. Loads scale across threads (six give 4.0-4.5x), so neither the allocator nor the thread count is a lever. The suites EXECUTE ~9 300 stdlib loads for 7 676 tests — three times the call-site count lever B was sized from — and loading is still 87 % of the suite's time.

THE PRICE, which is why it is per run: optimized, the rebuild after an edit costs 1-2 min where opt-level 0 takes 8-16 s, for most of anthill-core's sources and for tests/common/mod.rs (`kb/load.rs` 78-85 s, a one-line accessor in `kb/term.rs` 116-147 s) — a package override optimizes the crate's own test binaries with it. This entry's first claim, "only a very large module", was wrong and /code-review caught it.

FOUND AND FIXED on the way: anthill-core was built FOUR times a gate, because `chrono` (anthill-todo, anthill-version) and `serde` (anthill-smt-gen's `derive` feature, now `serde_derive` directly) resolved different features per selection. A gate's second cargo invocation now compiles for 4 s after a core edit, not 98-115 s, and `test.sh` refuses to run on such drift (it names `chrono` and `serde` on the manifests as they were).

RECORDED, NOT FIXED: (1) the eval/SLD stack canary needs (1.0, 1.5] MiB at opt-level 0 and (384, 512] KiB at 2, so the optimized gate does not guard the unoptimized budget — documented at `BRIDGE_REENTRY_CAP` (user: leave documented). (2) ONE run lost `wi_tests` to SIGABRT — "pointer being freed was not allocated" while a test's thread dropped its KnowledgeBase, one line after an unrelated test FAILED in another thread. Not reproduced on the binary that aborted (ten re-runs of the segment, four under MallocScribble); the next full run was green; 1 abort in 6 optimized executions; cause unknown. The stack and the attempts are in `full-run-2026-10-06-core-opt2.txt`.

/code-review ran on the always-on form (14 findings, all taken); the ~15 lines of mode logic in `test.sh` that replaced it were checked by hand only.

