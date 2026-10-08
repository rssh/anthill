## Attributes

- id: WI-20261008-RAH0Z-route-every-test-s-stdlib-load
- created: 2026-10-08T06:26:34Z

- status: Open
- status_agent: user
- status_at: 2026-10-08T06:26:34Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261006-SZKV7-two-step-load-as-a-switch-in

- tags: test-infra

## Description

ROUTE EVERY TEST'S STDLIB LOAD THROUGH THE ONE RECIPE — the test files that build their own KB, collect the stdlib and call `load_all` themselves, moved onto `tests/common`, so the two-step control (WI-20261006-SZKV7) and later the base KB (WI-059) reach them.

WHAT. 172 files under `anthill-core/tests/include`, and `classic_mini_test.rs` and `github_todo_test.rs`, carry a local copy of the load: `KnowledgeBase::new()`, `collect_stdlib_and_rust_bindings`, `load::load_all`. Up to 1 557 of the suite's tests live in them. Replace each copy with a call into the one recipe (`recipe_load` and the helpers that end in it).

WHY. (1) `ANTHILL_TEST_TWO_STEP_LOAD=1` reaches a test only through the recipe. Counted 2026-10-07 (docs/design/test-infrastructure.md §2.4; raw: docs/measurements/test-infrastructure/two-step-run-2026-10-07.txt): of the 9 591 stdlib loads the integration binaries execute, 1 028 are one-shot loads the switch did not reach — 885 in `wi_tests`, 25 in `parse_tests`, 118 in the other nine — so 'green under two-step' says nothing about those tests. (2) Lever B reaches a test the same way, so they would stay on a full load each. (3) A copy re-reads and re-parses the 87 stdlib files at every load; the recipe parses them once per binary (`STDLIB_PARSED`).

HOW, suggested. (a) Give `tests/common` what the copies want and it lacks — that is why about thirty of them exist: SWITCH-HONOURING entries that return the loader's own `Vec<LoadError>` and the `LoadResult`. `recipe_load` returns both but takes its recipe as an argument, and naming a recipe there takes a test OUT of the switch's reach; the entry the copies move to must read the switch. (b) Replace by helper shape — 54 `load_errors`, 22 `load_with`, 12 `try_load`, 12 `load_result`, 12 `load_capturing_errors`, 9 `load_kb`, 6 `load_errs`, 4 `load_with_stdlib`, and the stdlib-alone copies (7 `load_stdlib_kb`, 5 `stdlib_kb`, 3 `load_stdlib`), which become `common::load_stdlib_kb` — itself moved onto `STDLIB_PARSED`. (c) Two shapes need a decision, not a replacement: `load_capturing_errors` hands back the KB of a load that FAILED together with its errors (e.g. `wi210_dispatch_test`), which the recipe does not; and five files load another directory beside the stdlib (examples, testcases).

PINNED BY NAME. A test whose subject IS the number of calls — `incremental_load_test`, `wi1103_derived_provision_reload_test`, the re-type suites — names its recipe (`recipe_load(.., LoadRecipe::…)`) and says why at its site. That is the only way a test stays outside the switch.

NOT IN SCOPE. The library's own unit tests: 79 one-shot loads through `kb/test_support.rs`. `src/` cannot use `tests/common`.

EXPECT FINDINGS. About a thousand more loads come under the switch, so the two-step run after the move may differ in more than the one test it differs in today. Classify as SZKV7 did: an assertion on the recipe is fixed or pinned by name; a different KB or different diagnostics for the same file is a loader finding — report it, do not adjust the test around it, ask before filing.

CONTROL. The count (§10): the suite traced under the switch, where a `load_with_visited x N` with N above the stdlib's file count is a one-shot load that is not the recipe's. 1 028 before. After: the loads of the tests pinned by name and no others, each listed with its reason.

DONE WHEN: no file outside `tests/common` collects the stdlib and calls `load_all` except those pinned by name; the gate is green; one `anthill-core` run under the switch is recorded with its differences classified; §2.4's table is re-taken.

