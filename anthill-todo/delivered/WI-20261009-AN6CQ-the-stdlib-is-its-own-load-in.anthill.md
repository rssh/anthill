## Attributes

- id: WI-20261009-AN6CQ-the-stdlib-is-its-own-load-in
- created: 2026-10-09T18:53:27Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-10T15:56:23Z

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

### 2026-10-10T15:27:35Z — feedback — user

RESUMED 2026-10-10 after WI-20261009-4ZRTG and WI-20261010-9BKZ4 landed; main merged into `wi-an6cq-stdlib-first` (dc379f4d). READY ON THE BRANCH, GATED, NOT COMMITTED — two things are the user's before it lands: the wording of the §8.3 bullet (the ticket's SPEC clause asked for it; it now says the library's load is SEALED and three rules bind every program), and `--no-stdlib` (below).

WHAT IS BUILT. `load::load_program` loads the library, SEALS that load (`seal_declarations`), and loads the program in a later one — so a program is held to all three rules a test's file already was: a library composite's equality (SZKV7), a library name declared again (4ZRTG), a library body reached into (9BKZ4). It bootstraps for itself; an empty library is one load and no seal; an empty program is no second load, reported as none (`program: Option<ProgramFiles>`, one field where the first cut had two that had to agree). The CLI's two sites, anthill-todo and the generated Rust bundle call it; so do the core's unit-test loader and the harnesses of anthill-cpp-gen, anthill-smt-gen and anthill-stl.

THE PARKED REVIEW'S LEFTOVERS, each taken: `wi966_loader_verdict_test` knows `load_program(`; `scripts/test.sh`'s `load:` line and rustland/CLAUDE.md say that everything outside anthill-core's helpers loads the library and then the program, whatever the switches; `ProgramLoad::warnings()` gives a library advisory once (the requires-shadow lint reads the whole KB at every load — `LoadWarning::is_raised_again_by_a_later_load`, an exhaustive match); both slices empty still bootstraps and an empty program invents no result; `lf1_real_spec_test` loads through `load_program`; the bundle's row pins the template's wiring and `emitted_bundle_compiles` was RUN by hand and passes; the stale comments and the unused `mut` are gone. `--no-stdlib` with a library named on the command line STAYS ONE LOAD, on purpose and not asked: it is the only way the CLI has to load a library's own files, so a program named beside them is part of that library's load and judged as part of it — said in the flag's help and in §8.3, pinned by a row. The alternative is a flag that names an on-disk library AS the library.

CONTROLS, each back-out MEASURED in one build with env-switched back-outs, since removed: `wi_an6cq_load_program_test` (anthill-core, 6 rows over a small library of its own) — no seal: 2 rows fail; no bootstrap: 1; the advisory not deduplicated: 1. `wi_an6cq_stdlib_first_test` (anthill-cli, 10 rows through the built binary) — no seal: the operation, the type, the `@[simp]` rule and the on-disk library beside the embedded one all load; main.rs at one call: the `eq` for `List` and the `@[simp]` rule load; run.rs at one call: the `run` row; 4ZRTG's skip of derived provisions backed out: `check` lists 142 records for 127. The same file in anthill-todo (3 rows) — no seal: the operation; one call: the equality. The measurements were taken before /code-review's reshaping of `ProgramLoad`, which moved fields and no logic.

/code-review ran once on the resumed diff (8 findings, no correctness bug in `load_program`): 7 taken — the one `Option`; a `Library` enum in the CLI in place of a flag and a list that could say 'bindings and no stdlib'; the `check` row pairs its absent names with a present one of the same spelling (`Float`'s written `NonEq` against `Option`'s and `List`'s derived); anthill-cpp-gen's lenient helper panics on a refusal that is the ORDER's; anthill-smt-gen's three loaders are one and a file on disk knows its path; the comments; the bundle row. NOT taken, said at the site: making the requires-shadow lint skip what a seal holds — a frontier-driven pass with its own question (a later load can write an operation or a `requires` into a sealed sort, or a provision that withdraws the advisory), and this ticket's scope excludes making the second call cheap.

NOT DRIVEN: that a generated bundle refuses what the CLI refuses. Nothing in the tree runs one; it rests on the one function all three sites call.

COST (docs/measurements/test-infrastructure/stdlib-first-cost-2026-10-10.txt), the gate's build, beside a JVM job: `anthill load` of a six-line file 450-470 ms -> 550-556 ms by the minima, about +0.1 s a start, where the unsealed branch measured +0.2 s on 2026-10-09.

GATE on the tree as it stands: 9 038 passed, 0 failed, 14 ignored, observed SHARED BASE; cli_tests 36 s, cmd_tests 163 s, wi_tests 236 s. scaland not touched — it has neither this order nor a seal (WI-20261009-S723J covers the order and the equality rule, not the seal).

### 2026-10-10T15:56:19Z — feedback — user

DELIVERED 2026-10-10. The entry above left two things to the user — the wording of the §8.3 bullet, and `--no-stdlib` over a library named on the command line staying one load; the answer to it was 'let deliver ticket, commit and push', and neither was changed. The Scala half is WI-20261009-S723J's, extended the same day (user) to the seal and to what a sealed body is protected from, with a list of what scaland has to be checked for first. Gate on the sources as delivered: 9 038 passed, 0 failed, 14 ignored, observed SHARED BASE; the design doc, the measurement file, this tracker and one status line of the spec changed after it. Landed on main as ONE commit: the branch's first commit was a WIP marked not for main.

