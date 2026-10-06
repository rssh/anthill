## Attributes

- id: WI-20261006-ZVV24-build-the-tests-optimized
- created: 2026-10-06T04:53:11Z

- status: Open
- status_agent: user
- status_at: 2026-10-06T04:53:11Z

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

