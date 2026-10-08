## Attributes

- id: WI-20261008-RAH0Z-route-every-test-s-stdlib-load
- created: 2026-10-08T06:26:34Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-08T19:47:30Z

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

## Changes

### 2026-10-08T08:41:40Z — feedback — claude

TWO FILES THAT WILL NEED A PIN, known in advance (2026-10-08). `wi224_sld_resolution_test` and `typing_test` each carry a fixture that supplies an `eq` for the stdlib's `List` (`provides PartialEq[T = List[T = A]]` / `provides Eq[T = List[T = A]]`), and both load the stdlib themselves today, so they run in one call. Since the second finding of WI-20261006-SZKV7 was settled, loading such a file AFTER the stdlib is a load error (`EqualityOfEarlierSort`; kernel-language.md §8.3): a composite's equality is closed by the load that defines it. Moved onto the recipe those fixtures must name `LoadRecipe::OneShot` and say why at the site, as `wi228_tree_threaded_dispatch_test` does. Four other files supply an equality for `Map` or `Set`, which have no constructors and so are no composites — the rule's domain; it does not touch them. A fixture supplying one for a composite the stdlib defines (`Pair`, `Option`, `SortedSet`, …) is in the rule's reach and needs the same pin.

### 2026-10-08T19:47:27Z — feedback — claude

DELIVERED. No file outside `tests/common` collects the stdlib and calls `load_all` but the ones pinned by name. 196 local load helpers in 174 files (172 under `tests/include`, `classic_mini_test.rs`, `github_todo_test.rs`) now load through the one recipe: 139 were the recipe verbatim and were replaced by script, 57 by hand; the 117 that were left forwarding one call are aliases (`use crate::common::load_errors_of as load_errors`), a function being where the next copy starts. `common::load_stdlib_kb` reads `STDLIB_PARSED`.

WHAT `tests/common` GAINED, each following the switch through ONE read of it (`run_switched_recipe`): `LoadOutcome` — the loader's `LoadError` values, a clean load's warnings, the KB a REFUSED load left; `UserFile` — a file read from disk beside the stdlib; `load_stdlib_kb_prepared`; and for a test that keeps its own `load_all`, `stdlib_parsed()` and `present_all_again`. `collect_stdlib_and_rust_bindings` is private.

THE TWO SHAPES "that need a decision" were settled by giving the recipe the capability, and are the user's to reverse: (1) it hands back the KB of a load that failed; (2) it takes paths, so the examples, the testcases and anthill-todo's store bundle are under the switch.

THE COUNT (docs/design/test-infrastructure.md §2.4, §5.3; raw: docs/measurements/test-infrastructure/one-recipe-run-2026-10-08.txt): one-shot loads the switch does not reach in the integration binaries, 1 028 -> 66; through the recipe in two calls, 8 222 of 9 591 -> 9 329 of 9 726. Every one of the 66 is a test pinned by name and listed with its reason. The library's 79 are as they were, out of scope.

THE RUN UNDER THE SWITCH: 7 943 passed, 0 failed, 6 ignored, OBSERVED TWO-STEP — no test differs, so "expect findings" found none in the loader. The two files the note of 2026-10-08 said would need a pin did NOT: `wi224_sld_resolution_test` supplies its `Eq` for a local container, not for `List`, since WI-20260918-CKD4J, and `typing_test`'s `List` fixture already went through a `common` helper and asserts a refusal that holds under both recipes.

NOT IN THE TICKET, ADDED: a guard, `wi_rah0z_one_recipe_test`. A test file that takes the stdlib's files, names a `LoadRecipe`, or calls a helper that names one is in its `PINNED` list with a reason and a line count, or the suite fails; a second row is the control that `LoadOutcome`'s entries follow the switch. Six back-outs measured, in its module doc and the raw file. Three test files that were pinned to two calls for no stated reason (`wi_1wbzt`, `wimh90f`, `wi284`) follow the switch now.

FOUND ON THE WAY, FIXED HERE: `wi210_dispatch_test` loaded anthill-todo's store bundle without `domain` and `version`; the load was REFUSED with 35 errors, the helper discarded the verdict, and three tests read what the loader had recorded by then. The bundle is one list in `common` (five loaders spelled it out) and loads clean; `wi210`, `wi221` and `github_todo_test` load strictly; no accessor of `LoadOutcome` hands out the KB without the verdict.

/code-review ran on the move (12 findings, all taken). One was a regression the move made: `wi_acg10_census_test` (ignored, a measurement) files rules by source PATH and the recipe's stdlib has none, so its stdlib group counted 0 rules in silence — it loads by path again, by name, and refuses a zero (re-run: 434 rules). What was changed in answer to the review — `LoadOutcome`'s private halves, the aliases, the guard's counts, the bundle helper — was checked by hand and by the runs, not by a second review.

RECORDED, NOT DONE: the stdlib's parsed files carry no path (a diagnostic located in one renders `<file N>`); stamping them would have fixed the census at its root and changes what every test's KB reports as a source name, so it was left. `wi925` and `wi926` reach the stdlib through a `FileSourceResolver`, which the guard does not see and says so.

Gate, on main as merged (08f70bf8 plus this): rustland 8 823 / 0 / 14, scaland 630.

