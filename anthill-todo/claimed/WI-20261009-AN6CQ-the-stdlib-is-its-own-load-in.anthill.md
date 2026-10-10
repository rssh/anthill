## Attributes

- id: WI-20261009-AN6CQ-the-stdlib-is-its-own-load-in
- created: 2026-10-09T18:53:27Z

- status: Claimed
- status_agent: claude
- status_at: 2026-10-09T18:53:43Z

- acceptance: cargo-test

- depends_on: WI-20261009-4ZRTG-the-library-is-sealed-a

## Description

THE STDLIB IS ITS OWN LOAD IN THE PRODUCT — the CLI, anthill-todo and the generated Rust bundle hand the loader the standard library (with its host bindings) FIRST and the program in a later `load_all`, where today they hand it both in one call. Decided 2026-10-09 (user): "in principle it is logical to have stdlib in own layer"; a precompiled stdlib comes later and needs this shape.

WHY. (1) Since WI-059 the test helpers of anthill-core load a test's files as a LATER load than the stdlib's (a copy of one loaded stdlib), and the product loads them in ONE call — so the gate's ~9 000 helper loads no longer exercise the shape users run (docs/design/test-infrastructure.md §8.7). Making the product load as the tests do removes the question instead of answering it with a second tier of the gate. (2) The two shapes are NOT the same language today, in one place: a file that changes the equality of a composite the stdlib defines — `provides Eq[T = List[T = A]]` with its own `eq` — loads in one call and is `EqualityOfEarlierSort` as a later load (kernel-language.md §8.3, WI-20261006-SZKV7). A rule that holds for `KB.loaded` and for every test, and not for a file passed to `anthill check`, is two rules. (3) A stdlib loaded once and kept — in a test binary now, in a snapshot later — is only the product's stdlib if the product loads it apart.

WHAT CHANGES FOR A USER. One kind of program becomes a load error: one that supplies the equality of a stdlib sort that has constructors (`List`, `Option`, `Pair`, …), or adds or removes a `PartialEq` / `Eq` / `NonEq` provision about it. `Map` and `Set` have no constructors and are not in the rule's reach. The repair is the one `wi224_sld_resolution_test` already made: a sort of the program's own holding the list. Measured 2026-10-09 over anthill-core's suites under all three load recipes: of 7 951 tests, ONE fixture is such a program (`wi228_tree_threaded_dispatch_test`); the examples, the testcases and anthill-todo's store bundle get the same verdict either way. NOT MEASURED: `cli_tests` and `cmd_tests`, which spawn the real binary and have never run with the stdlib as a separate load — expect findings, and classify them as SZKV7 did (an assertion on the load's shape is fixed; a different verdict for the same program is reported, not adjusted around; ask before filing).

WHERE. Five sites build a KB from the stdlib and a program in one call: `anthill-cli/src/main.rs` (stdlib, embedded host bindings, user files), `anthill-cli/src/run.rs` (`build_kb`), `anthill-todo/src/main.rs` twice (one through `load_all_per_file`, whose per-file results seed the store — check what it does with the stdlib's), and the Rust bundle `anthill-rust-gen` generates (`bundle.rs`, a template). One helper, not five copies: the first load is the stdlib AND its host bindings (a stdlib without its binding layer is refused), the second is everything else. Both loads' warnings are reported; a stdlib that does not load is the build-level error it is today.

SPEC (kernel-language.md §8.3 and wherever a "program" is said to be loaded): the standard library is loaded before a program, and a program is a later load. Say what that closes — a stdlib composite's equality — and that the loader's API still takes any list of files in one call, which is how the stdlib's own files are loaded together.

TESTS. `wi228`'s fixture is no longer a legal PROGRAM; it stays pinned to one load only if what it tests is the stdlib's own load, and says so, else it wraps the list. `wi_rah0z_one_recipe_test`'s equality fixture and the three recipes' docs (`rustland/CLAUDE.md`, `scripts/test.sh`) call one shot "what the CLI does" — after this it is not. A control that DRIVES it: a program supplying an `eq` for `List`, run through the real `anthill` binary, is refused, and the same file with the list wrapped loads — say which fails when a site is backed out to one call.

COST, to be measured and written down: a CLI start pays a second-call load until the frontier-driven passes (§4 A3) or a precompiled stdlib — 0.18 s on 0.30 s in the gate's build by §5.1's bench — so `cmd_tests` (~10 spawns a test) and `cli_tests` get slower. Estimated 1 to 1.5 min of gate.

NOT IN SCOPE: scaland, which has no equality-closure rule at all (its own ticket); the precompiled stdlib; making the second call cheap.

DONE WHEN: no product path loads the stdlib and a program in one call; the spec says so; the control is in with its back-out measured; the gate is green; the cost is measured beside the old one.

## Changes

### 2026-10-09T20:34:57Z — feedback — user

PARKED 2026-10-09 behind WI-20261009-4ZRTG (the library is sealed), on the local branch `wi-an6cq-stdlib-first` (one WIP commit, 18216c02; not pushed, not for main).

WHAT IS ON THE BRANCH, all of it green when it was parked: `load::load_program` (the library in one `load_all`, the program in a later one) used by the CLI's two sites, anthill-todo and the generated Rust bundle; the §8.3 bullet; rows that drive the rule through the real `anthill` and `anthill-todo` binaries, three back-outs measured (one per site, each failing only its own row); the other crates' test loaders and the core's unit-test loader moved to the same order. No fixture of ANY suite is refused by the new order (cli_tests 198, cmd_tests 295, core lib 671, cpp-gen 207, smt-gen, stl). Cost measured with the real binary, the gate's build: `anthill load` of a six-line file 480-520 ms -> 660-720 ms, about +0.2 s a start.

WHY PARKED. /code-review (14 findings) reproduced, and I reproduced after it: with the library loaded first a program can REDECLARE A LIBRARY OPERATION and REOPEN A LIBRARY TYPE in silence — one call refuses both — and `anthill check` lists 15 pending proof records for the library's own derived provisions. The ticket's claim that one kind of program is judged differently by the two orders was wrong: it was what the suites assert, and no fixture redeclares a library name. The census and the cause are in WI-20261009-4ZRTG.

ALSO FROM THAT REVIEW, to take when this resumes: `wi966_loader_verdict_test`'s list of loader entry points does not know `load_program(`; `scripts/test.sh`'s `load:` line and rustland/CLAUDE.md say every other crate runs one shot, which the moved harnesses make false, and no switch reaches them; `ProgramLoad::warnings()` would report a library advisory twice (the program's load re-runs the whole-KB lint); `load_program` with both slices empty does not bootstrap, and an empty program yields an invented `LoadResult`; `lf1_real_spec_test` still loads in one call; `--no-stdlib` with the on-disk library is one call, so the CLI still gives one program two verdicts, now in both directions; the bundle's row reads the emitted text and the compile check is `#[ignore]`; two stale comments and an unused `mut`.

