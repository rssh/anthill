# Test infrastructure — making the gate fast

**Status.** Brainstorm with measurements, 2026-10-05. **Lever A1 landed 2026-10-06, for
the gate** — a full `scripts/test.sh` run builds `anthill-core` optimized, a selected run
does not (WI-20261006-ZVV24: §1.1, §2.5, §4 A1), and that day's re-measurement on a quiet machine
corrected several of the first day's numbers — each correction is dated where it stands.
**The two-step load switch landed 2026-10-07** (WI-20261006-SZKV7: §5.3) and found the
equivalence levers A3 and B rest on broken in two places (§4 A3). Both were settled the
next day — the first fixed, the second made a load error — and the suite is green under
the switch. **The tests that built their own stdlib load were moved onto the one recipe
the same day** (WI-20261008-RAH0Z: §2.4, §5.3), so the switch reaches every such load
but those of the tests pinned to a recipe by name: 66, where it was 1 028.
**A knowledge base can be deep-copied since 2026-10-09** (WI-20261009-D0SD4: §5.2), which
is the half of lever B that §5.2 had wrong: a KB cannot be made `Send`, so the base is
copied instead, and one copy is 7.3 ms beside a 300 ms load (§5.1).
**Lever B landed the same day** (WI-059: §5.3): the test helpers start from a copy of one
stdlib per test binary, the suite is green under it and under the fresh recipe, and
`wi_tests` ran in 412–491 s where the fresh recipe took 625–763 s that day.
Nothing else here is decided; §8 lists
the decisions that are the user's, and §9 the sequence this doc recommends. Numbers rot:
every one below is dated, says what machine it came from, and has its raw material under
`docs/measurements/test-infrastructure/` so it can be re-taken.

**The problem.** Every work item is gated on a full workspace run (`rustland/scripts/test.sh`).
On 2026-10-05 the tracker took 18–31 commits a day; one gate on the 6-core laptop that
measured this doc is **3 h 27 min** of wall clock (§1), a few hours on a slow box, and
10–20 min on the fast one. The gate is the loop's clock, and the loop is the project's.

**The short version.** One number explains almost all of it: a test that loads the
standard library pays **~4.8 s** for that load (debug profile, §2), and the `anthill-core`
suites do it at **~3 100 call sites** across 7 039 tests. The CLI suites pay the same load
once per spawned process. (Re-measured 2026-10-06: 2.1 s on a quiet machine, 5.2 s with
twelve threads loading at once, and ~9 300 stdlib loads EXECUTED — §2.1, §2.4, §2.5.)
Three levers, in the order they should be pulled:

| lever | what it attacks | expected gain | cost |
|---|---|---|---|
| A1. build `anthill-core` optimized (§4 A1) — **DONE 2026-10-06** | the 4.8 s | measured: the load 6.8× faster with every check still on, the gate **3 h 27 min → 15 min 45 s** warm, 30 min 40 s cold (§1.1) | three `--config` lines in `test.sh`, for a full run only: optimized, a rebuild after most edits costs 1–2 min more (§2.5), so the edit loop is left at opt-level 0 |
| A2–A4. hashing, frontier-driven passes, hot spots (§4) | the load (0.31 s since A1), and the "incremental" load (0.15 s since A1) | tens of % each; A3 is what makes B pay | hours to days each |
| B. load the stdlib once per process, clone per test (§5) — **DONE 2026-10-09, before A3** | the ×3 100 | measured, beside another job: `wi_tests` 625–763 s → 412–491 s over three runs of each, the gate 1 329 s → 1 151 s (§5.3). A3 is what takes the rest: a test still pays its second-call load | days |
| C. run less per gate, or on more machines (§6) | the policy | whatever the policy allows | a decision |

The ordering is not free: B without A3 wins at most ~1.7×, because today loading a
four-line file into an already-loaded KB still costs **2.4–2.9 s** (§2.3) — the load
pipeline has whole-KB passes that run regardless of what was added. A1, by contrast, is
independent of everything else and shrinks every term at once.

---

## 1. Where a full run spends its time

Full run, 2026-10-05 12:48, this checkout's sibling at `~/work/oss/anthill`, debug
profile, 12 test threads on an Intel i7-9750H (6 physical cores / 12 threads, 64 GiB,
macOS 25.6), with other work on the machine (load average ~20 during the run). Raw table:
`docs/measurements/test-infrastructure/full-run-2026-10-05.txt`.

| binary | tests | wall | share |
|---|---:|---:|---:|
| `anthill-core` · `wi_tests` | 6 043 | 7 801 s (2 h 10 min) | 63 % |
| `anthill-todo` · `cmd_tests` (spawns the CLI) | 295 | 2 786 s (46 min) | 22 % |
| `anthill-cli` · `cli_tests` (spawns the CLI) | 198 | 445 s | 4 % |
| `anthill-core` · the other 10 integration binaries | 923 | 810 s | 7 % |
| `anthill-core` · lib unit tests | 656 | 104 s | 1 % |
| `anthill-cpp-gen`, `anthill-smt-gen`, `anthill-stl`, rest | 395 | ~374 s | 3 % |
| compile + link before the first binary runs | | 23 s (incremental; 127 s and 180 s on two other runs today) | <2 % |
| **total** | **8 510** | **12 448 s = 3 h 27 min** | |

Two readings of the `wi_tests` block (completions per 10-minute bucket, from the same log):
throughput sat between 0.5 and 1.1 tests/s for the whole two hours and the last bucket was
not a few stragglers but the same rate on a thinning queue. So it is **throughput-bound,
not tail-bound**: scheduling tricks (reordering, retries, a smarter runner) will not move
it; only fewer or cheaper loads will.

At 12 threads on 6 physical cores, 1.1 tests/s means ~11 s of thread-time per test — about
two of the single-threaded loads measured in §2, which is what hyper-threading on a
hash-and-allocate workload plus the odd double-loading test predicts.

**The subprocess suites.** `cmd_tests` averages 9.4 s wall per test at 6 threads, i.e. ~56 s
of thread-time per test. Each spawn of `anthill-todo` parses the stdlib embedded in the
binary and loads it from scratch (`stdlib::parse_embedded`, then `load_all`) before doing
anything — the same ~4.8 s — and a todo test runs a project through several commands.
`setup_project` has 161 call sites and `Command::new(ANTHILL_TODO_BIN)` 51 in the include
files, plus per-file helpers; the per-test cost says roughly ten spawns per test.

**History that still matters.** The macOS first-launch assessment (35–92 s per fresh test
binary, verdict cached by content) is why the suites were consolidated into 21 binaries
(`rustland/CLAUDE.md`, "Where a new test file goes"). That tax is paid and the layout is
right; nothing below undoes it. The second thing already done is `STDLIB_PARSED`: the
parsed stdlib is a `LazyLock` per test binary, so the **parse** is shared and only the
**load** is repeated. §2.1 shows the parse would have been ~0.5 s of the 4.8 s.

### 1.1 The same run with `anthill-core` optimized (WI-20261006-ZVV24)

Full run, 2026-10-06 09:17, this checkout, the same machine with no other gate in flight,
`anthill-core` at opt-level 2 and the dependencies at 3 (§4 A1; narrowed to the two
tree-sitter crates from the third run on), 12 test threads. **8 560
passed, 0 failed, 14 ignored** — the totals of the last gated commit. Raw table:
`full-run-2026-10-06-core-opt2.txt`. The opt-level 0 column is §1's run.

| binary | tests | opt-level 0 (§1) | optimized | ratio |
|---|---:|---:|---:|---:|
| `anthill-core` · `wi_tests` | 6 093 | 7 801 s | **659 s** | 11.8× |
| `anthill-todo` · `cmd_tests` (spawns the CLI) | 295 | 2 786 s | **240 s** | 11.6× |
| `anthill-cli` · `cli_tests` (spawns the CLI) | 198 | 445 s | 57 s | 7.8× |
| `anthill-core` · the other 10 integration binaries | 922 | 810 s | 74 s | 10.9× |
| `anthill-core` · lib unit tests | 661 | 104 s | 10 s | 10× |
| `anthill-cpp-gen`, `anthill-smt-gen`, `anthill-stl`, rest | 391 | ~374 s | 35 s | ~11× |
| compile, both cargo invocations | | 23 s (incremental) | 762 s (**cold**, see below) | |
| **total** | **8 560** | **12 448 s = 3 h 27 min** | **1 840 s = 30 min 40 s** | **6.8×** |
| the same, second run: the feature fixes in, warm builds | 8 560 | | **945 s = 15 min 45 s** | 13× |
| the same, third run: as reviewed, everything rebuilt (444 s of compile) | 8 560 | | 1 476 s = 24 min 36 s | 8.4× |
| fourth run: through `test.sh`'s full-run mode | | | **`wi_tests` ABORTED** — see below | |
| fifth run: the same tree, unchanged, warm | 8 560 | | 1 136 s = 18 min 56 s | 11× |

§1's run had other work on the machine. The quietest opt-level 0 gate of that day (22:53,
read from its log before the directory was removed) took 11 519 s = 3 h 12 min, with
`wi_tests` 7 518 s, `cmd_tests` 2 143 s and `cli_tests` 351 s — against it the total is 6.3×.

The second run is what a gate costs when nothing in `anthill-core` was edited: 23 s of
compile, then `wi_tests` 602 s, `cmd_tests` 162 s, `cli_tests` 33 s. After an edit to a
large `anthill-core` module add 4–5 min of compile (§7).

The tests themselves went from about 3 h 25 min to **18 min** in the first run and
**15 min** in the second. `wi_tests` beat the bench's
7.4× (12-thread load throughput, §2.5). Two candidate reasons, not separated: the test
bodies — resolution, eval — are `anthill-core` code too and shrink with the loads, and a
laptop that throttles over a two-hour all-core run does not over an eleven-minute one.

**One run aborted, and the cause is not known.** The fourth run lost `wi_tests` 40 s in:
`SIGABRT` from the allocator ("pointer being freed was not allocated") while one test's
thread was dropping its `KnowledgeBase` — the inner table of `sort_ops` — one line after an
unrelated test in another thread had FAILED. Two threads going wrong in the same second
reads as heap corruption, and `anthill-core` has no `unsafe` outside one unit-test helper,
so the write would be a dependency's or the tree-sitter C code's. It did not reproduce on
the binary that aborted (the failed test alone, its file, and the first 235 tests at 12
threads ten times over, four of them with the allocator scribbling freed memory), and the
fifth run of the unchanged tree is green: **1 abort in 6 full optimized executions of
`wi_tests`** that day. Not known: whether it also happens, rarely, at opt-level 0; whether
optimization exposes something latent; whether it was a machine that had spent the morning
at a load average over 100. The stack and the attempts are in the raw file. AddressSanitizer
is the tool that would say, and needs a nightly toolchain.

The compile row is not a like-for-like: this checkout had never built the workspace's
tests, so 762 s is a cold build of everything. It is also where the run found something:
`anthill-core`'s library was built **four times** — a target and a host flavour (it is a
build-dependency of `anthill-stl`, and `tree-sitter`'s build script turns on
`serde_json/preserve_order` for host builds only), each once per cargo invocation, because
`test.sh` runs the gate as two (`--workspace --exclude` the spawning crates, then `-p` them)
and the two selections resolved different features for two of `anthill-core`'s
dependencies: `chrono`, and `serde` through `anthill-smt-gen`'s use of its `derive`
feature. At opt-level 0 a redundant build of the library cost 35 s cold and went unnoticed;
optimized it is 110 s. Both are fixed in the manifests, and the second run's second
invocation compiled for 1.8 s (§7 has the mechanism and the rule it leaves).

## 2. The unit of cost: one stdlib load

All numbers in this section: 2026-10-05, this machine, **debug profile** (what `cargo test`
builds), **with the user's gate run in flight** (load average 10–20), so absolute values are
inflated — roughly 1.5× is a fair guess — while ratios hold. Re-take on an idle machine
before quoting them anywhere else. Recipe: `docs/measurements/test-infrastructure/bench_load.rs`
(a throwaway `anthill-core` example; copy it into `anthill-core/examples/` to run, do not
commit it there, `cargo test` builds examples). Per-phase trace:
`docs/measurements/test-infrastructure/load-phases-debug-2026-10-05.txt`, taken with the
loader's own `ANTHILL_LOAD_TIMING=1` switch (`load_phase_inner`'s `mark!`).

**Re-taken 2026-10-06 with no gate in flight** (load average 2–3, the desktop's own): the
inflation was **2.3×**, not 1.5×. §2.1 and §2.5 carry the quiet numbers; §2.2's and §2.3's
per-phase times were not re-taken and are to be read as SHARES. Raw:
`bench-matrix-2026-10-06.txt`, `compile-cost-2026-10-06.txt`.

### 2.1 Four numbers

| measurement | 2026-10-05, gate in flight | 2026-10-06, quiet | what it is |
|---|---:|---:|---|
| `parse` | 0.52 s | 0.22 s | read + tree-sitter parse of the 87 files (73 `stdlib/anthill`, 14 `anthill-stl/anthill`) |
| `full` | 4.85 s | **2.11 s** | fresh `KnowledgeBase::new()` + `load_all(stdlib ∪ bindings ∪ one 4-line user file)` — **what every `load_kb_with` pays** |
| `pre_typer` | 2.25 s | 1.03 s | the same with `LoadOptions { run_typer: false }` — everything before the typer |
| `incr` | 2.40 s | **1.18 s** | `load_all(one 4-line user file)` into a KB that already holds the stdlib — **what a cached-KB design would pay today** |

Medians of 5, debug profile. A test thread does not see the quiet number: with 12 loads
running at once on this 6-core box one load takes **5.2 s** (§2.5's scaling rows), which is
what a `wi_tests` thread actually pays.

### 2.2 Where the 4.8 s goes (full load, `ANTHILL_LOAD_TIMING`)

| phase | time | share |
|---|---:|---:|
| `type_check_sorts` (206 sorts) | 1.73–1.81 s | 37 % |
| `load_with_visited` × 88 files (the per-item loader) | 0.87–1.17 s | 21 % |
| `eq_derive::classify + derive_total_eq + derive_conditional_eq` | 0.54–0.60 s | 12 % |
| `check_provider_requires` | 0.45 s | 9 % |
| `type_value_derive::run` | 0.18–0.26 s | 5 % |
| `sort_domain_derive::run` | 0.16–0.22 s | 4 % |
| everything else (≈45 phases) | ~0.35 s | 8 % |

Inside the two biggest, from a 12-second sampling profile (`sample`, call tree, 8 596 samples
on the load loop):

- `type_check_sorts` → `check_operation_bodies` is 33 % of the whole load, almost all of it
  `typing::expr::type_check_node_gated_in_gamma` (25 %) and `region::region_sorts` (6 %, which
  the pass's own comment says is "computed ONCE by the caller" — worth a look at why it still
  shows under the per-op loop).
- `derive_conditional_eq` is `eq_derive::field_conditions` (8 %).
- `check_provider_requires` is `synth::resolve_within_provider` (7 %).
- `type_value_derive::run` is `projection::any_requirement_names_spec` (6 %);
  `sort_domain_derive::run` is `projection::any_requirement_names_one_of` (4.5 %).

Self time, across everything: **hashing**. `HashMap::get` + SipHash frames are the top of
the leaf list (**22 %** of leaf samples between `hash_one`, `sip::*` — whose `write`,
`c_rounds`, `d_rounds`, `rotate_left` are each a separate un-inlined call at opt-level 0 —
`RawTable::find`, `hashbrown::get`), then `memmove`/`memcmp` (7 %), the debug-only
`precondition_check`s (4 %), and `malloc`. A visible slice of the hashing hashes
**strings**: `canonical_sym` builds the
qualified name of a symbol and looks it up in `by_qualified_name` (a `&str`-keyed map) —
called from the typer's hot loops. Then `SymbolTable::resolve_in_scope_recursive*`,
`SmallVec` traffic, `copy_nonoverlapping` precondition checks (debug-only), `TermStore::alloc`.

### 2.3 The incremental load is not incremental

Loading the four-line file into an already-loaded KB:

| phase | full load | incremental load | depends on the new file? |
|---|---:|---:|---|
| `type_check_sorts` | 1.73 s (206 sorts) | **1.21 s (0 sorts)** | no — whole-KB sweep |
| `eq_derive::classify + derive_*` | 0.59 s | **0.92 s** | no — and larger, the KB is now bigger |
| `check_provider_requires` | 0.45 s | **0.44 s** | no |
| `check_override_refinement`, `eq_derive::run`, `register_specialization_witnesses` | 56 + 60 + 17 ms | 56 + 55 + 41 ms | no |
| `load_with_visited` | 0.87 s × 88 files | 1.8 ms × 1 file | yes — proportional |
| everything else | ~0.3 s | ~0.1 s | mostly yes |
| **total** | **4.46 s** | **2.89 s** | |

So ~2.75 s of the 2.9 s is work whose input did not change. The loader was built for a
one-shot load of a closed file set (and `anthill-todo`'s per-file cold start, which is also
one-shot); nothing in it was ever asked to be cheap on a second call. This is the fact
that orders the levers: **a cached base KB saves ~40 % until these passes are made
frontier-driven, and ~98 % after**.

### 2.4 How many loads a gate does

Call sites in `anthill-core/tests` that end in a stdlib load (one recipe,
`try_load_kb_named_prepared_with`, "ONE function, so a change to the load pipeline cannot
reach the ~683 ordinary call sites while leaving …" — WI-966/-967):

| helper | sites |
|---|---:|
| `load_kb_with` | 1 995 |
| `try_load_kb_with` | 959 |
| `load_stdlib_kb` | 137 |
| `load_kb_bare` (no stdlib) | 19 |
| `try_load_kb_prepared` (host fn mounted before load) | 5 |
| `load_stdlib_kb_with_source`, `try_load_kb_untyped_with` | 4 + 4 |

≈ 3 100 loads for 7 039 tests; a test may load more than once (a control load, a refusal
load and a clean load). 3 100 × 4.85 s ≈ 4.2 h of thread-time, which on 6 cores with
hyper-threading is the 2 h 10 min measured. **The model fits; there is nothing hidden.**

**Corrected 2026-10-06 — the fit was two errors cancelling.** 3 100 is a count of call
SITES, not of loads executed: a helper that twenty tests call is one site. And the helpers
are not the only way in — **346 direct `load::load_all*` calls in 194 files** under
`anthill-core/tests` never pass through `common/`, so "the one recipe" is the recipe of the
tests that use it, not of the suite. On the other side, 4.85 s was a bench number inflated
2.3× by the gate it was measured beside (§2.1). The honest inputs are the contended load
time — 5.2 s with 12 threads loading, §2.5 — and the number of loads a gate EXECUTES,
which needs no new code to count: `ANTHILL_LOAD_TIMING=1` with `--nocapture` prints one
trace per load, direct calls included, and each trace says how many files it loaded.

**Counted 2026-10-06** (`load-count-2026-10-06.txt`), `anthill-core`'s twelve test
binaries, 12 threads, optimized:

| binary | tests | loads executed | of them stdlib-sized (≥ 80 files) | load time as a share of the binary's thread-time |
|---|---:|---:|---:|---:|
| `wi_tests` | 6 093 | 8 602 | 8 441 | 89 % |
| `parse_tests` | 460 | 461 | 243 | 77 % |
| the other nine integration binaries | 462 | 521 | 484 | 23–85 % |
| lib unit tests | 661 | 127 | 103 | 79 % |
| **all twelve** | **7 676** | **9 711** | **9 271** | **87 %** |

So the suite runs **1.2 stdlib loads per test** (1.4 in `wi_tests`), three times the
call-site count — and **optimizing the load did not change what the suite is made of**:
at 0.3 s a load instead of 2.1 s, loading is still 87 % of the time. Lever B's case is
intact, on an 11-minute `wi_tests` instead of a 2-hour one. The split of that load time
by phase is also what §2.2 measured at opt-level 0, to within a point or two:
`type_check_sorts` 38 %, `load_with_visited` 21 %, `eq_derive`'s classify and derive 10 %,
`check_provider_requires` 8 %, `type_value_derive` 4 %, `sort_domain_derive` 4 %.

**Counted 2026-10-07 — how many of them go through the recipe**
(`two-step-run-2026-10-07.txt`; WI-20261006-SZKV7). The same trace with the two-step
switch on separates them: a call given the stdlib AND another file at once is a one-shot
load the switch did not reach. (The "through the recipe" column needed one more line in
the trace, printed by the recipe for this run and not kept; §10's recipe gives the other
two columns' sum without it.)

| | stdlib loads executed | through the recipe | one-shot, not reached | the stdlib alone, by other means |
|---|---:|---:|---:|---:|
| `wi_tests` | 8 860 | 7 847 (89 %) | 885 | 128 |
| `parse_tests` | 247 | 18 | 25 | 204 |
| the other nine integration binaries | 484 | 357 | 118 | 9 |
| lib unit tests (their own loader, `kb/test_support.rs`) | 104 | 0 | 79 | 25 |
| **all twelve** | **9 695** | **8 222 (85 %)** | **1 107** | **366** |

Outside the library's own 79, the 1 028 are the copies: **172 files under
`tests/include`** (by grep), and `classic_mini_test.rs` and `github_todo_test.rs`, build a
KB, collect the stdlib and call `load_all` themselves.
Most are the recipe verbatim (of their local helpers, 55 return `Vec<String>`, 29 a
`KnowledgeBase`, 12 a `Result<(), Vec<String>>` — all of which a `common` helper returns
already); about thirty want what the recipe did not expose until this item, the loader's
`LoadError`s or its `LoadResult`. They are outside the two-step control (§5.3) and would
be outside lever B: neither reaches a test except through the recipe. The library's 79
are a different change — `src/` cannot use `tests/common` at all.

**Re-taken 2026-10-08 — the copies moved onto the recipe**
(`one-recipe-run-2026-10-08.txt`; WI-20261008-RAH0Z). The same traced run, the gate's
build, 12 threads; the "through the recipe" column is read off a line the recipe prints
under `ANTHILL_LOAD_TIMING=1`, which is in the tree now (§10).

| | stdlib loads executed | through the recipe, in two calls | one-shot, not reached | the stdlib alone |
|---|---:|---:|---:|---:|
| `wi_tests` | 8 995 | 8 815 (98 %) | 62 | 118 |
| `parse_tests` | 247 | 42 | 0 | 205 |
| the other nine integration binaries | 484 | 472 | 4 | 8 |
| lib unit tests (their own loader, `kb/test_support.rs`) | 104 | 0 | 79 | 25 |
| **all twelve** | **9 830** | **9 329 (95 %)** | **145** | **356** |

In the integration binaries the one-shot loads the switch does not reach went from
**1 028 to 66**, and every one of the 66 is made by a test pinned BY NAME, with the
reason at its site: 15 are the recipe itself with `LoadRecipe::OneShot` written out (the
switch's own controls, `incremental_load_test`'s comparison of the two recipes, and
`wi228`'s fixture, which the language's rule puts in the stdlib's load), and 51 are made
by hand, over `common::stdlib_parsed()` or the stdlib's paths — a project file ordered
BEFORE the stdlib, a load through `load_all_per_file`, the batches of a test about which
batch judges a clause, every loaded file presented to the KB again, a corpus audited by
path. The list
is in the tree as `wi_rah0z_one_recipe_test::PINNED`, which is also the guard: a test
file that takes the stdlib's files, names a `LoadRecipe`, or calls a helper that names
one is on that list with its reason and its count, or the suite fails. Of the stdlib
loaded alone, 325 of 331 go through `common::load_stdlib_kb`, which parses nothing —
it re-read all 87 files at each call before.

What the copies were FOR, now that they are gone: 139 of the 196 local helpers were the
recipe verbatim. The rest wanted something `common` did not hand out — the loader's
`LoadError` values, a clean load's warnings, the KB a refused load left, a file read
from disk beside the stdlib — and it does now (`LoadOutcome`, `UserFile`), through one
read of the switch. The two shapes the ticket set aside as decisions were both settled
by giving the recipe the capability: it returns the KB whatever the verdict, and it
takes paths. The library's 79 stay as they were.

### 2.5 The optimized-build numbers

`rustland/Cargo.toml` has no `[profile]` section, and until WI-20261006-ZVV24 nothing
overrode it: everything ran at `opt-level = 0`. The first day's release-against-dev pair, taken beside a running gate
(4.85 s against 0.62 s, the "7.9×" this doc opened with), is in `bench-debug-2026-10-05.txt`
and `bench-release-2026-10-05.txt`. Measured 2026-10-06 on a quiet machine: the same bench with ONE thing
changed from the dev profile at a time. Debug assertions, overflow checks, full debug info
and incremental compilation stay on in every row but the last. Raw:
`bench-matrix-2026-10-06.txt`.

| build | `parse` | `full` | `pre_typer` | `incr` | `full` ratio | loads/s on 1 thread | 6 threads | 12 threads |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| dev (opt-level 0) | 0.22 s | 2.11 s | 1.03 s | 1.18 s | 1× | 0.44 | 1.82 | 2.24 |
| `anthill-core` at opt-level 1 | 0.20 s | 0.79 s | 0.41 s | 0.45 s | 2.7× | 1.21 | 4.89 | 5.75 |
| `anthill-core` at opt-level 2 | 0.20 s | **0.31 s** | 0.14 s | 0.15 s | **6.8×** | 3.48 | 15.6 | **16.5** |
| `anthill-core` at opt-level 3 | 0.18 s | 0.26 s | 0.13 s | 0.15 s | 8.2× | 3.51 | 15.8 | 16.3 |
| `anthill-core` at 2, ALL dependencies at 3 † | **0.085 s** | 0.31 s | 0.15 s | 0.17 s | 6.8× | | | 17.4 † |
| `anthill-core` at 2, the two tree-sitter crates at 3 — **the gate's build** ‡ | **0.072 s** | 0.27 s | | | | | | 17.9 ‡ |
| release (opt-level 3, assertions off) | 0.08 s | 0.22 s | 0.12 s | 0.13 s | 9.6× | 4.25 | 18.5 | 17.9 |

† second session (08:56), where `anthill-core` at 2 alone gave 16.7 and release 20.9.
‡ third session (11:55), where `anthill-core` at 2 alone gave 0.185 s / 0.27 s / 18.7, all
dependencies at 3 gave 0.072 s / 0.27 s / 18.3, and release 0.071 s / 0.22 s / 21.2.
**Compare within a session, not across**: the same binary's 12-thread figure moved up to
18 % between the three (release: 17.9, 20.9, 21.2), with the machine's background load.

The thread columns are `full` on N threads at once, each thread building its own KB on a
default-size stack as a libtest thread does (`THREADS=<n>` in the bench).

Three readings:

- **Level 2 takes nearly all of it.** It is within 1.4× of a release build with every check
  still on. Level 3 is 17 % faster on one thread and indistinguishable once 12 share the box
  (16.3 against 16.5 loads/s, same session — inside the noise). Level 1 leaves 2.5× on the
  table to save 16 s of cold compile.
- **Loads scale across threads.** Six threads give 4.0–4.5× one thread's throughput, and
  twelve change it by −3 % (release) to +23 % (opt-level 0) — an ordinary curve for six
  physical cores. There is no
  allocator or lock contention to hunt (§4 A5), and the thread count is not a lever
  (§6 C3). What a test thread pays is the contended number: 5.2 s a load at opt-level 0
  with 12 running, 0.60 s at level 2.
- **Two dependencies matter, for the parse.** §4 A1 guessed a dependencies-only override
  near-useless on the grounds that the tree-sitter C parser "is compiled by `cc` at its own
  `-O`". It is not: `cc` takes the PACKAGE's opt-level, so in the dev profile `parser.c`
  is built `-O0`. With dependencies at 3 the stdlib parse falls from 0.20 s to 0.085 s —
  the release figure — and the two crates the parse runs in, `tree-sitter` and
  `tree-sitter-anthill`, give all of it on their own (0.072 s against 0.072 s, third
  session). A test binary pays the parse once (`STDLIB_PARSED`); a spawned CLI
  process pays it every time, so this one is for `cmd_tests` and `cli_tests`.

**What it costs to compile.** Raw: `compile-cost-2026-10-06.txt`. Wall seconds, CPU seconds
in brackets where they say something.

| the `anthill-core` library | opt-level 0 | at 1 | at 2 | at 3 |
|---|---:|---:|---:|---:|
| cold compile | 35 s (66) | 92 s (570) | 108 s (728) | 111 s (737) |
| rebuild after a new line in `kb/load.rs` (40 519 lines; everything after it moves) | 8–15 s | 66–69 s (473–486) | 69–78 s (551–587) | |
| rebuild after the same statement on an EXISTING line there (nothing moves) | 7 s | | 48 s (250) | |
| rebuild after a new line in `fs_util.rs` (118 lines) | 6.5 s | | 6.7 s | |

**The rebuild cost is set by what the edit INVALIDATES, not by the level** — and not by the
size of the file, which is what this paragraph first claimed from the three rows above
(/code-review, 2026-10-06, asked for the rows below). Under incremental compilation an
optimized unit is re-optimized whole, and a unit is invalidated by a change to anything
inlined into it. So `kb/load.rs`, 40k lines in one module, costs most of a cold build for
one line; a leaf module costs what it did; and a one-line accessor in a 518-line file that
everything uses costs MORE than `load.rs`, the test binary included.

The loop a work item actually runs, `cargo test -p anthill-core --test wi_tests --no-run`,
after one new line in a function body (`compile-cost-2026-10-06.txt` §3, §6):

| edit in | opt-level 0 (a selected run) | optimized (the gate's build) |
|---|---:|---:|
| one `tests/include` file (a new item at its end) | 8 s | 10–11 s |
| `kb/typing/expr.rs` (1 223 lines, a typer module) | 13 s | 26–27 s |
| `tests/common/mod.rs` (the helpers all 669 test files use) | 8 s | 62–69 s |
| `kb/load.rs` (40 519 lines) | 15–16 s | 78–85 s |
| `eval/value.rs` (1 150 lines) | 13 s | 77–82 s |
| `intern.rs` (3 129 lines; a one-line accessor) | 14 s | 127–134 s |
| `kb/term.rs` (518 lines; a one-line accessor) | 14.5 s | 116–147 s |
| cold — `wi_tests` never built against this library | 39 s (62 CPU) | 99 s (601 CPU) |

At opt-level 0 every row is 8–16 s. Optimized, an edit to most of `anthill-core`'s sources
or to the shared test helpers costs one to two minutes more, and only an edit confined to
one test file, or to a module little else inlines from, stays near what it was. This is the
price of the setting — the reason it is applied to the gate and not to the edit loop (§4
A1) — and the only number in this section that moving the tests out of the package, or
splitting the big modules, would change.

**A profile override is per PACKAGE, not per target.** `[profile.dev.package.anthill-core]`
optimizes the library and every other target of that package: `wi_tests` and the other ten
integration binaries, the unit-test harness, the examples. Cargo has no way to say "the
library only" short of moving the tests into a package of their own. That is the 601 s of
CPU in the cold row above — `wi_tests` itself, 267k lines, at opt-level 2 (its binary is
35 MB against 63 MB) — and it is why an edit to `tests/common/mod.rs` costs a minute: the
test binary is re-optimized too. The other crates' tests and binaries stay at 0.

An override on the `dev` profile is inherited by `test` (checked with a two-crate probe:
the overridden library and its harness get `-C opt-level=2`, a dependent crate's binary and
tests do not). `[profile.test] opt-level = N`, this doc's first proposal, would compile
every test crate in the workspace optimized. And a profile given with `--config` outranks
the manifest's (same probe), which is what lets one script run both builds.

## 3. The cost model, and what it rules out

```
gate_wall ≈ Σ_tests (loads × T_load + T_test_body) / effective_cores  +  T_compile  +  T_subprocess_suites
```

- `T_load` is lever A. `loads` is lever B. `effective_cores` and the Σ are lever C.
- `T_test_body` (resolution, eval) is small next to the load for almost every test; the
  throughput curve in §1 says there is no class of slow tests to hunt. Not a lever today.
- `T_compile` is 2 % of the gate. Not a lever today — but it is the term that lever A1
  (opt-level) can make worse, so it is measured alongside. **2026-10-06: it did.** With
  `anthill-core` optimized a gate compiles for 23 s when the crate was not edited and for
  229–306 s after an edit to one of its large modules — a fifth to a quarter of a ~20 min
  gate (§1.1, §7). It is a lever now; §7 says what is left in it.
- Reordering binaries, a different test runner, retries, fail-fast: none change any term.
  `cargo-nextest` in particular runs **one process per test**, which is exactly the shape
  lever B cannot live in (§5.4); it would also not help, since the launch-assessment tax is
  per binary content and already paid once.

## 4. Lever A — make one load cheaper

This is the user's question of 2026-10-05, "can we speed up load", and it pays everywhere:
every test, every `anthill-todo` cold start, every `anthill check`.

### A1. Build profile

Debug `opt-level = 0` on a workload that is hash maps, small vectors and symbol resolution
costs **6.8× on the load** at the level taken (§2.5), and the first full run with it changed
went from 3 h 27 min to 30 min 40 s (§1.1). This was the single cheapest thing to do and
the first step of §9. What was proposed here on 2026-10-05, and what the measurements of
2026-10-06 made of each (WI-20261006-ZVV24):

1. `[profile.test] opt-level = 1` (or 2). **Not this spelling.** It optimizes every test
   crate in the workspace, and `cargo build` and `cargo test` stop sharing the `anthill-core`
   artifact. The load is `anthill-core` code, so the override names that package and sits on
   `dev`, which `test` inherits — given per run, as `--config` (see the decision below):

   ```
   --config profile.dev.package.anthill-core.opt-level=2
   --config profile.dev.package.tree-sitter.opt-level=3          # the parse: see 2
   --config profile.dev.package.tree-sitter-anthill.opt-level=3
   ```

   Debug assertions, overflow checks, debug info and incremental compilation are untouched —
   this codebase leans on the first two (`debug_assert!`, the precondition checks).
   **Level 2**: level 3 loads no faster under 12 threads, level 1 gives up 2.5× of the load
   for 16 s of cold compile and rebuilds no faster after an edit (§2.5).
2. `[profile.dev.package."*"] opt-level = 3` — dependencies only. Guessed near-useless;
   **measured otherwise for the parse**: the tree-sitter C parser is built at the package's
   opt-level, so it was `-O0`, and the stdlib parse falls 0.20 s → 0.085 s. It does nothing
   for the load itself, as predicted (the hashers are monomorphized inside `anthill-core`).
   Taken for the CLI suites, which parse on every spawn — but NARROWED to the two crates
   the parse runs in, which give the whole gain. `package."*"` outranks `build-override`,
   so it would also optimize every proc-macro crate and third-party build script on a cold
   build (and `syn`, `quote` and `proc-macro2` resolve different features under the gate's
   two invocations, so twice), for nothing at test time. The first two full runs of §1.1
   were taken with `"*"`; the third, and what `test.sh` passes, with the two names.
3. `debug = "line-tables-only"` for the optimized crate. **Measured, not taken**: a tenth of
   the compile's CPU and next to nothing of its wall (cold 105 s against 108 s; a `load.rs`
   edit 67–72 s against 69–78 s), paid for with the debugger's view of locals.

**What it costs, and where.** One to two minutes more per rebuild after an edit to most of
`anthill-core`'s sources or to `tests/common/mod.rs` — `kb/load.rs` 78–85 s, `kb/term.rs`
116–147 s, the test helpers 62–69 s, where opt-level 0 took 8–16 s for each; 26 s for a
typer module; next to nothing for an edit confined to one test file (§2.5 has the table).
And a gate after an edit to the crate compiles for 4–5 min, the library being built three
times (§7). In CPU rather than this 12-thread laptop's wall clock: about 590 s for one
`load.rs` edit, 2 150–2 230 s for a gate's compile after a core edit, ~1 450 s for the
library's two flavours on any cold build — on a 4-core box, minutes where the above says
seconds. The native-stack budget of the eval/SLD crossing also moves with the level, and
the optimized gate does not guard the unoptimized one (`BRIDGE_REENTRY_CAP` in
`kb/resolve.rs` records both measurements).

Two ways to hold the setting. **Decided 2026-10-06 (user): gate only** — the second. The
first was chosen earlier the same day, on this doc's then claim that only a very large
module rebuilds slowly; §2.5's per-module table, taken after /code-review questioned the
claim, reversed it.

- **Always on, in `rustland/Cargo.toml`.** One artifact set; what the edit loop runs is
  what the gate runs; every test invocation loads fast, the filtered ones included. But
  every rebuild after an edit to `anthill-core` or to the test helpers costs 1–2 min more,
  and a work item is many rebuilds: ten of them give back more than the fast loads of the
  filtered runs save.
- **Gate only** — the manifest untouched, `scripts/test.sh` passing the three `--config`
  lines. A full run (no arguments) is optimized; a selected run is the plain dev profile;
  `ANTHILL_TEST_OPT=2` or `=0` overrides either default, and a WIDE selection wants `=2`
  (`-p anthill-core`: 13 min against over two hours). The edit loop keeps its 8–16 s
  rebuilds; the gate compiles what it needs, 4–5 min after an edit to the crate. Costs: a
  second artifact set and incremental cache in `target/` (the gate checkout's had reached
  131 GB on 2026-10-06 and filled the disk — two sets get there sooner), a selected run
  keeps 2 s loads, and the gate does not test the build the edit loop iterated on — which
  cuts both ways: both builds are now exercised.

### A2. Hashing

- `FxHash`/`ahash` for maps keyed by `Symbol`, `TermId`, `u32` and tuples of them. SipHash
  is DoS-resistant and slow; nothing here is adversarial. `rustc-hash` is one dependency and
  a type alias; the change is mechanical and measurable in isolation.
- `canonical_sym` (and through it `canonical_sort_sym`) hashes a **string** on every call:
  `qualified_name_of(sym)` then `by_qualified_name.get(&str)`. A `Vec<Symbol>` (or
  `HashMap<Symbol, Symbol>` under A2's hasher) that caches the canonical symbol per symbol,
  invalidated where `by_qualified_name` is written, makes it an index. The profile shows
  ~4 % self + its hashing children; the typer's hot loops call it per node.
- `SymbolTable::resolve_in_scope_recursive_with_mode` (5 % self): check what it hashes and
  whether the scope walk re-hashes the same name per level.

Expected: 10–25 % of the load, no semantic risk, back-out is the bench.

### A3. Frontier-driven passes — the enabler for lever B

Make the passes in §2.3 do work proportional to **what the call added**, with the base
sealed:

- `type_check_sorts` is already given `all_sorts` (the sorts this call defined) but spends
  1.2 s when that list is empty — `check_operation_bodies` and `type_rule_bodies` sweep every
  op and rule in the KB (the "free-op sweep" the re-type tests exercise on purpose). The
  frontier exists: `KnowledgeBase.loaded_rule_frontier`, and `LoadResult.defined_sorts`;
  what is missing is the same for ops and rules, and a rule for which old items a new one
  can invalidate (a new provider for an old spec; a new override of an old op). The design
  question per pass is "which items can this call have changed the verdict of", and the
  honest answer for each is a short set — provider/requirer edges, override edges, eq
  derivation over fields that mention the new sorts.
- `eq_derive::classify + derive_total_eq + derive_conditional_eq` and `eq_derive::run`:
  derive for the new sorts and for old sorts whose fields mention them.
- `check_provider_requires`: check the new provisions, and old provisions whose spec the
  new file touched.

**The trap this must not fall into** is the one the repo's principles name: a pass that
skips an item it should have checked fails *silently*, and the suite stays green. The
control is cheap and must be stated at the site: the one-shot full load stays exactly as it
is (it is still what the CLI does), and the equivalence `load_all(S ∪ U)` ≡
`load_all(S); load_all(U)` — same KB observable facts, same diagnostics for the same `U` —
is asserted by running the entire `anthill-core` suite under both recipes (§5.3 has the
switch) and by a focused test per pass whose fixture is a `U` that invalidates an old item.

Expected: `incr` from 2.9 s to under 0.1 s. Note this does **not** make the one-shot full
load faster; it makes the second call cheap. Its value is lever B.

**Measured 2026-10-07 — the equivalence does not hold today, in two places**
(WI-20261006-SZKV7; §5.3 has the run). Both were found by the two-step switch before any
pass was touched, which is what it was built first for, and each is a statement about a
pass this section proposes to change:

- **The sort loop had the wrong frontier already — FIXED 2026-10-08.** The typer's
  loop over `sort_names` (`kb/typing/sorts.rs`) reaches a fact through its constructor's
  SORT and a rule through its domain SORT, and a load hands it the sorts that load
  defined. A clause THIS call asserted under a sort an EARLIER call defined is under no
  sort in the list and was never checked. One-shot the two sets coincide, which is why
  nothing noticed. Three shapes, each refused in one call and loading clean in two until
  the fix: `fact box(n: "seven")` over a base `box(n: Int64)`; its other spelling
  `rule box(n: "seven") :- true`; and a rule with contradictory variable types, or
  outside the pattern fragment, written into the base's sort through a second `namespace`
  entry. The two-step run found the first; /code-review of its fix found the other two,
  which the fix had left open by taking its work list from `LoadResult.fact_rule_ids` —
  a list one producer feeds. The typer is now handed what the call ADDED as one value
  (`typing::Loaded`, from `LoadResult::loaded`): the sorts it defined and the RANGE OF
  RULE SLOTS it filled before its typer ran, which no producer can be left off. It is
  the typer's only argument — a list of sorts alone no longer compiles — so a hand-driven
  call and the pipeline's own are given the same thing. It is the first pass with a
  frontier of items rather than of sorts, and the shape the others need: what the call
  added, not what the KB holds. Measured in one call over the stdlib it checks nothing
  (4 600 slots walked in 3 ms). Two things it does NOT settle, both stated at the site:
  the two recipes give the same diagnostics but not always in the same ORDER, and a
  fact a later load merely RESTATES is the earlier load's, not re-checked.
- **Equality derivation is not monotone in what has been loaded — REFUSED 2026-10-08
  (user).** A written `provides Eq[T = List[T = A]]` loaded TOGETHER with the stdlib
  leaves `List` with no derived `PartialEq` / `Eq` / `NonEq` provision; loaded AFTER it,
  the rows the stdlib's own call derived were still there beside the written ones. The
  derivation reads what decides a composite's equality through NEGATIONS — it
  classifies a composite only if nothing supplies its `eq` (`eq_derive::classify`, the
  boundary test) and derives for it only if nothing already speaks for it — and those
  are sound within a load and false across loads, both sets growing after the rows are
  written. With the rows stay the derived rows of every sort HOLDING the first, every
  call the earlier typer resolved against them, and for a sort that reaches a `Float`
  its own derived `NonEq`, which the next classification reads back as a hand-written
  leaf: `reading(v: Float)` and then a witness `eq … = true` for it answered
  `eq(reading(1.5), reading(2.5))` FALSE where one load answers TRUE. Taking the rows
  back was weighed and not done: it means re-deriving every dependent and re-resolving
  every call that read them, and it makes an earlier load's facts something a later one
  can change — which is what every frontier-driven pass of this section would then have
  to allow for. So a load may change NOTHING about the equality of a composite an
  earlier load defined — who supplies its `eq`, which provisions of the three specs name
  it, under what conditions — and doing so is a LOAD ERROR (`EqualityOfEarlierSort`),
  one load of both being unchanged; `kernel-language.md` §8.3 has the rule. It is
  decided by comparing STATES: each composite's equality signature is recorded when a
  load ends, and recomputed by the same function at the next. Three cuts that read
  what a load DID instead were each wrong somewhere (/code-review): a record of the
  sorts derived for refused a later load it had no business refusing; the rows in the
  load's rule slots miss a row that repeats an earlier one; the operations it declared
  include every source presented again. Not covered by it, and said so at the site and
  in the spec: sorts that are no composite; what the load's own later passes add to an
  earlier composite; and what a supplier computes or what shape the sort has, an
  operation or a sort declared again being a redeclaration. **The base is sealed** as
  far as who decides equality goes, which is the premise the rest of this section
  assumed.

Neither is a hypothetical for the tests alone: `KB.loaded` (`eval/builtins.rs`,
`kb_loaded`) calls `load_all` on the live KB, which is the second call of a two-step load.
Until the fix above it accepted `fact box(n: "seven")` over a base `box(n: Int64)`, and
until the refusal it accepted a candidate that replaced a base sort's equality.

### A4. Hot spots inside the passes

For when A1–A3 are in and the profile is re-taken (the ranking will shift):

- `typing::expr::type_check_node_gated_in_gamma` — 25 % of the load today. A per-node typer
  that is a quarter of a whole load over 206 sorts deserves a look at what it recomputes
  per node (environment construction? projection elimination? the `canonical_sym` calls?).
- `region::region_sorts` under the per-op loop (6 %) — the comment says computed once.
- `eq_derive::field_conditions` (8 %), `synth::resolve_within_provider` (7 %),
  `projection::any_requirement_names_spec` / `_one_of` (~10 % together) — each a single
  function; each probably a quadratic walk that a precomputed index flattens.

### A5. Allocator

A debug build on the system allocator with this many small `Vec`/`SmallVec`/`HashMap`
allocations: `mimalloc` as the global allocator in the **test binaries only** (a
`#[global_allocator]` in each aggregator) is a one-line experiment. Typical: 5–15 %.

**2026-10-06: not tried, and the reason to try it first is gone.** The case for an allocator
experiment was the suspicion that twelve allocating threads contend. They do not: six
threads give 4.0–4.5× one thread's load throughput (§2.5), an ordinary curve for six
cores. What is left is the single-thread 5–15 %, unmeasured, and a step-6 item as before.

### A6. A loaded-KB snapshot on disk

Serialize the loaded stdlib KB once (at build time or on first use), deserialize per
process. Would also fix the product's cold start (`anthill-todo`, `anthill`). But the KB is
a dozen hash maps, a hash-consed term store, a discrimination tree and `Rc` caches;
deserializing and re-linking that is not obviously faster than a clone, and the snapshot
must be keyed on the stdlib content *and* the binary (every `anthill-core` change
invalidates it). **Not now.** Lever B gets the same per-test win in-process with none of
the machinery; revisit for the product cold start when §5.2 b is on the table.

## 5. Lever B — load the stdlib once per process

### 5.1 The shape

```
static BASE: LazyLock<Mutex<KnowledgeBase>>  — stdlib ∪ rust bindings, loaded once per test binary
per test:   let mut kb = BASE.lock().clone();  load_all(&mut kb, &[user files]);  …
```

Per-test cost becomes `T_clone + T_incr`. `T_incr` is 2.9 s today and ~0.1 s after A3.
(2026-10-06, optimized: `T_incr` is 0.15–0.17 s on a quiet machine, against a full load of
0.31 s — the same "B without A3 wins at most ~1.7×", on numbers a tenth the size.)
`T_clone` is unmeasured (there is no `Clone` yet); a KB of this size is a few MB of hash
maps and vectors, so tens of milliseconds in debug is the expectation. With 12 threads
cloning under one mutex that is still far below one load; a pool of N bases is the fallback
if contention shows.

**Measured 2026-10-09** (WI-20261009-D0SD4; raw: `clone-cost-2026-10-09.txt`), one thread,
the same machine with no gate in flight:

| | `full` | `incr` | `clone` | `clone + incr` | `full / (clone + incr)` |
|---|---:|---:|---:|---:|---:|
| dev (opt-level 0), the first cut | 2.55 s | 1.51 s | 124 ms | 1.55 s | 1.64× |
| the gate's build, the first cut | 320 ms | 183 ms | 23.5 ms | 219 ms | 1.46× |
| the gate's build, **as landed** (two runs) | 302 / 313 ms | 184 / 180 ms | **7.3 ms** | 201 / 194 ms | **1.5–1.6×** |

So the base KB buys a load about 1.5× today — below the 1.7× read off `incr` alone, the
second call being still 60 % of a load. With A3 in, a test pays the copy and little
else: a fortieth of a load.

The first cut copied the discrimination tree node by node, and that one field was three
quarters of the copy (28.6 ms of 38: a `HashMap` a node). /code-review pointed out that
the tree holds nothing bound to a thread; its children are `Arc` now, so it passes the
copy as any plain field does and its subtrees are SHARED between a copy and its
original, each side path-copying what it writes. `full` and `incr` did not move with
the atomic counts. What is left of the copy is mostly the term store, the clauses with
their body trees, and the symbol table — 3.9, 2.7 and 1.5 ms in the first cut's
breakdown, which was taken with timers in and ran a fifth slower than the copy alone.

And twelve threads copying under one mutex is no longer "far below one load" once A3
lands: at ~15 ms a test, twelve threads ask for ~800 copies a second and one lock gives
~135. The pool of bases is then a requirement, not a fallback — WI-059's to size.

### 5.2 What has to be true of `KnowledgeBase`

- **`Clone`.** No `impl Clone` exists. The struct (`kb/mod.rs`, lines 919–2275) is
  `HashMap`/`Vec`/`HashSet`/`Option` fields, a `TermStore`, a `SymbolTable`, a `SubstTree`,
  a `Cell<Option<Symbol>>`, `HashMap<Symbol, Rc<NodeOccurrence>>` (`const_bodies`) and seven
  `RefCell<HashMap<_, Rc<Vec<_>>>>` typer caches. All of it derives, once `TermStore`,
  `SymbolTable` and `SubstTree` derive (none does today; nothing in them looks like it
  can't). The `Rc`s are shared-immutable, so a clone that shares them is correct.
- **`Send`.** A `static` needs it, and `Rc` forbids it. Two ways: `Rc → Arc` in the eight
  fields (an atomic increment per cache hit — negligible, and these caches are
  `RefCell`-guarded already so single-threaded access is a given), or keep the base in a
  thread-local. **Thread-local does not work here**: libtest spawns a fresh OS thread per
  test, so a `thread_local!` base would be loaded per test and nothing is saved. `Rc → Arc`
  it is, with a compile-time `Send` assertion next to the struct (a `const _` that
  instantiates `fn needs_send<T: Send>()` at `KnowledgeBase` — no crate needed) so a
  future `Rc` field is a compile error, not a silent regression of this design.

  **Corrected 2026-10-06 — it is not eight fields.** `Rc<NodeOccurrence>` is the body
  representation of operations, rules and consts (1 072 mentions in 58 files), and
  `NodeKind` carries `Value`s whose tuple and entity payloads are `Rc<[Value]>` — so the
  change reaches the interpreter's hot path, where every `Value` clone becomes an atomic
  increment, and that cost has to be measured rather than called negligible. About 1 740
  `Rc` uses in 68 files of `anthill-core`, 79 more in `anthill-stl` / `-cpp-gen` /
  `-smt-gen`; `HostFnImpl::Dynamic` is an `Arc<dyn Fn>` with no `Send + Sync` bound.
  Suggested shape: a `Shared<T>` alias first (mechanical, no behaviour change), so the
  flip to `Arc` is one line and is measured against a one-line back-out.
  **Corrected 2026-10-09 — it is not `Rc → Arc` at all** (WI-20261009-D0SD4). Asked a
  field at a time, the compiler says 25 of `KnowledgeBase`'s 116 fields hold something
  that is not `Send`, and two of the reasons no `Arc` removes. `Value` carries the
  interpreter's five arenas (`Rc<RefCell<CellArena | MapArena | StreamArena |
  ClosureArena | SubstArena>>`) and the layer arena, so a `Send` `Value` is a lock on
  each. And every expression node has four `RefCell` slots the typer writes in place
  (`classification`, `op_dicts`, `inferred_type`, `lowered_receiver`), and an `Arc` of a
  type holding a `RefCell` is not `Send` either. The count above is also low: 2 030 `Rc`
  uses in 72 files of `anthill-core/src`.

  The first bullet is wrong for the same slots: **the `Rc`s of a body tree are not
  shared-immutable.** A second `load_all` re-types every operation body already in the
  KB (the free-op sweep, `typing/sorts.rs`) and writes its verdicts into the nodes, so
  two KBs sharing a tree would each stamp what the other reads. The layer snapshot
  (`kb/layer.rs`) clones `op_records` and `const_bodies` by `Rc` and so has this shape;
  whether `KB.loaded` can leave a base call site carrying a discarded layer's verdict
  is NOT TESTED.

  **What was built instead (user, 2026-10-09).** `KnowledgeBase::deep_clone`
  (`kb/deep_clone.rs`), safe code: a copy that shares NO `Rc` with its original — a new
  allocation for every body tree and value payload, the sharing WITHIN the copy kept by
  a memo. (The discrimination tree is the one large thing shared with the original, and
  through an `Arc`: §5.1.) It is a struct literal over every field with
  no `..`; a field with no `Rc` in it goes through one helper bounded `Clone + Send`,
  which is the compiler's own proof that it holds none, and the 25 others through
  copiers that are exhaustive matches for the same reason. It REFUSES what it could
  neither duplicate nor leave out: a closure host function, a mounted backend or a
  record of one, an interpreter-arena handle, an applied layer, a live import audit, a
  KB caught mid-load or mid-search, a receiver twin the KB does not own, and a body
  nested deeper than a megabyte of stack — the copiers recurse, and a refusal is better
  than an abort. The memo caches whose rows hold an `Rc` start empty in the copy. Then `common::SendableKb`
  (`tests/common/mod.rs`) wraps such a copy and carries the ONE `unsafe impl Send` of
  the change, in test support and not in the library: sending is sound because nothing
  outside the wrapper holds an `Rc` into it, which is exactly what the deep copy
  establishes. `Send` is decided from a type's fields, never from a value, so no amount
  of copying makes the compiler see it; the only safe alternative is a second,
  `Rc`-free type to freeze the base into and thaw a KB out of — about twenty mirror
  types and a conversion each way, not taken. The claim is checked where it is made:
  five rows in `kb/deep_clone.rs` (the original is dropped and every occurrence and
  payload it held is freed; every payload a `Value` can carry is made anew; the typer's
  stamps come across and are then independent; the refusals; the stack budget), fifteen
  back-outs measured against them and tabled there with the two copiers no row covers,
  and three more rows from outside the crate, one of which takes copies on eight
  threads at once.
- **Not `Sync`** is fine: the `Mutex` provides exclusive access for the clone.
- `Interpreter::new(kb)` takes the KB by value (81 sites) — a clone is exactly what it wants.

### 5.3 Where the switch lives, and the control

The one recipe, in `anthill-core/tests/common/mod.rs` — `run_recipe` since
WI-20261008-RAH0Z, which every helper reaches through the one read of the switch,
`run_switched_recipe`; it was `try_load_kb_named_prepared_with` when this was written.
Today it builds `STDLIB_PARSED ∪ user` and loads into `KnowledgeBase::new()`. The change
is in that one function: clone the base, load `user`. Because it is the one function:

- the whole suite flips at once, which is the **control**: the full `anthill-core` run must
  pass under both recipes, and an env switch (`ANTHILL_TEST_FRESH_LOAD=1`) keeps the
  one-shot recipe runnable forever, for bisecting a difference and for the equivalence
  claim of A3;
- the sites that **cannot** use the base stay explicit: `try_load_kb_prepared` (5 sites)
  mounts a host fn *before* load and `register_host_fn` refuses a late entry — those keep
  the fresh load; `load_kb_bare` (19) has no stdlib; `load_stdlib_kb` (137) wants the base
  itself — a clone, no second load; the `*_untyped` variants (4 + 4) stop before the typer
  and need the fresh path or a base loaded untyped.

Things that can differ between the recipes and must be checked, not assumed: `Symbol`
numbering (interning order shifts — a test comparing symbols by id rather than name would
flip; by the conventions it should not exist), `LoadResult.defined_sorts` (now only the
user's — which is what the re-type tests want anyway), diagnostics for a refused `U` (the
whole-KB passes re-report nothing for the base, since the base loads clean — but A3 must
keep it so), and `fact_dedup` / discrimination-tree state for a `U` that re-asserts a
stdlib fact.

**The run, 2026-10-07 (WI-20261006-SZKV7).** The recipe now takes a `LoadRecipe`, and
`ANTHILL_TEST_TWO_STEP_LOAD=1` makes every helper load `load_all(stdlib)` and then
`load_all(user)` into the same fresh KB. There is no `Clone` and no shared base, so the
number of `load_all` calls is the only thing that varies. `wi_szkv7_two_step_load_test`
is the control that a switched run measured what it says — the user call's
`LoadResult.defined_sorts` holds the user's sorts and no stdlib one. `test.sh` writes the
recipe it was ASKED for into the run's log and the control writes the one it OBSERVED,
so a log carries both. One `anthill-core` run under the switch, the gate's build,
12 threads: **7 871 passed, 2 failed, 6 ignored**, against 7 873 / 0 / 6 for the same
thirteen binaries in that night's one-shot gate; both failures pass one-shot on the same
binary and failed again in a second switched run. Raw: `two-step-run-2026-10-07.txt`.

| test | class | what differs |
|---|---|---|
| `wi830_extent_binding_test::a_role_that_is_not_a_role_is_refused_at_load` | loader finding, **fixed 2026-10-08** | a fact over the stdlib's `ExtentBinding` with a `role` that is no `ExtentRole` was refused one-shot and LOADED CLEAN two-step: the typer reaches a clause through the sorts the call defined, and the fact's entity was defined by the earlier call (§4 A3). `wi_szkv7_clause_frontier_test` drives it, and the rule-shaped siblings no test in the suite had, without the switch |
| `wi228_tree_threaded_dispatch_test::pin_now_threads_conditional_tree_into_nested_dictionary_nodes` | loader finding, **refused since 2026-10-08**; the test is PINNED to one load by name | a user sort providing `Eq[T = List[T = A]]`: one-shot, `List` gets no derived equality rows and the call `eq(x, y)` at `List[Int64]` is pinned to the user's `eq`; two-step, the stdlib call's derived `List → PartialEq / Eq / NonEq` rows stayed beside the written ones and the call carried no `CallClass` (§4 A3). Here the program's value was the same under both; with a `Float` field it was not. Loading it after the stdlib is now a load error, so the fixture has to be in the stdlib's load, and says so at its site |

Neither test was adjusted to fit the two-step recipe; under the switch the suite had
these two red rows, and one of them has since been pinned to one load BY NAME, for the
reason its row above gives. The first was not the tests' alone — `KB.loaded` is a
second `load_all` on a live KB, and it accepted a source whose `fact box(n: "seven")`
over the base's `box(n: Int64)` a one-shot load refuses (probed; the raw file has it).
**With the first fixed, 2026-10-08, the same run was 7 885 passed, 1 failed, 6 ignored**
— the second row alone. **With the second refused the same day, and the one test it
touches pinned to one load by name, the run is 7 923 passed, 0 failed, 6 ignored** — the
first green run under the switch, and the evidence that the rule refuses no later load
it should not: every one of the suite's two-step loads passes through its check. Of seven test files that
supply an equality for a prelude container, it is the only one the rule touches: four
supply it for `Map` or `Set`, which have no constructors and so are no composites — the
rule's domain — and two loaded the stdlib themselves and were not reached by the switch.
WI-20261008-RAH0Z moved both onto the recipe the same day and NEITHER needed the pin:
`wi224_sld_resolution_test` has supplied its `Eq` for a local container, not for `List`,
since WI-20260918-CKD4J, and `typing_test`'s `List` fixture already went through a
`common` helper and asserts a refusal that holds under both recipes.

**The run after the copies moved, 2026-10-08 (WI-20261008-RAH0Z).** One `anthill-core`
run under the switch, traced, the gate's build: **7 943 passed, 0 failed, 6 ignored** —
no test differs, with 1 107 more stdlib loads under the switch than the run above had
(9 329 through the recipe in two calls, against 8 222; §2.4). So the ticket's "expect
findings" found none in the loader. It found one in the TESTS, and not by the switch:
`wi210_dispatch_test` had been loading anthill-todo's store bundle without `domain` and
`version`, the load was refused with 35 errors, its helper discarded the verdict, and
three tests read what the loader had recorded by then. The recipe's new entries hand
out no KB without the verdict, which is how it showed; the bundle is one list in
`common` now and loads clean. Raw: `one-recipe-run-2026-10-08.txt`.

**No test differs for a reason that is the recipe's own.** Nothing within the switch's
reach reads `Symbol` numbering, the order of diagnostics, or `fact_dedup` state in a way
the second call changes; the files that read `LoadResult.defined_sorts` (the control
aside) already load in two calls by hand and never pass through the recipe. That is a
statement about what the
suite ASSERTS, in two ways narrower than "the recipes are equivalent":

- **The oracle is the assertions.** A KB that differs where no test looks is invisible to
  it — the second finding was caught by ONE test that reads a `CallClass`, while every
  test that only ran such a program saw the same value.
- **The switch reaches 85 % of the stdlib loads the suites execute** — 8 222 of 9 695,
  counted (§2.4). Another 1 107 ran one-shot whatever the switch said: 1 028 made by test
  files that carry their own copy of the load, 79 by the library's own unit tests.
  **Since WI-20261008-RAH0Z, 2026-10-08: 95 %** — 9 329 of 9 830; 145 run one-shot
  whatever it says, 66 made by tests pinned to a recipe by name and the library's 79.

**The shared base, 2026-10-09 (WI-059).** The recipe has a third way to load,
`LoadRecipe::SharedBase`, and it is the default: a test's KB is a deep copy of the
stdlib loaded once per test binary (`common::SendableKb`, §5.2), and the test's own
files are loaded into the copy. `ANTHILL_TEST_FRESH_LOAD=1` selects the one-shot recipe
for every load and `ANTHILL_TEST_TWO_STEP_LOAD=1` the two-step one; `test.sh` validates
both and refuses the two together. `load_stdlib_kb` is a copy and no load at all. The
one read of the switch (`run_switched_recipe`) is also the one place a load is taken OFF
the base for what it asks: a hook to run before the stdlib's load, or options other than
the default — the two things the base, being loaded already and loaded one way, cannot
give. Those helpers say so at their definitions; `load_outcome_files` lost its hook
parameter to a `_prepared` twin so that the common case has none to pass.

The control is the two-step switch's, extended: it tells the three recipes apart by which
call defined the stdlib's sorts and by whether the test's own thread loaded the stdlib at
all, and writes what it OBSERVED into the log. Two back-outs fail it — the switch never
choosing the base, and `load_stdlib_kb` loading for itself.

One full gate on the base: **8 831 passed, 0 failed, 14 ignored**, observed SHARED BASE.
`anthill-core` under `ANTHILL_TEST_FRESH_LOAD=1`: **7 951 passed, 0 failed, 6 ignored**,
observed one shot. No test differs, which the two-step runs above predicted: the base is
the two-step recipe with its first call made once for everybody. One row of the guard
had to change, and it is the rule's own consequence rather than a finding — under the
default a test's files are now a LATER load than the stdlib's, so
`wi_rah0z_one_recipe_test`'s fixture that supplies an `eq` for the stdlib's `List` is
refused by default and loads clean only under the fresh recipe.

**What /code-review of it found** (13 findings, all taken but the one that is a decision,
§8.7). The one that mattered: `wi1075`'s census counts loader events in a THREAD-LOCAL,
and on the shared base the stdlib is no longer loaded on the test's own thread, so the
census had stopped seeing the stdlib and stayed green. It loads one-shot by name now. The
same reasoning made every helper that takes a hook a way OUT of the default recipe in the
guard's eyes (`wi_rah0z_one_recipe_test`): the recipe cannot tell a closure that does
nothing from one that mounts a host function, so a no-op hook would take a test off the
base in silence — one test did — and nine test files are listed with the reason they
load fresh. The rest: the base's build cannot panic and poison its `LazyLock` (a load
that panics is kept as the error every test then reports); the control also reads a
SECOND thread, which a per-thread base fails and the first reading does not; the shared
base is not a `LoadRecipe` a test can name, so "the base, with a hook" cannot be written;
`load_stdlib_kb_with_source` starts from the base like its untyped twin.

What it bought (raw: `shared-base-run-2026-10-09.txt`):

| | one shot | shared base |
|---|---:|---:|
| `wi_tests`, three runs of each over the morning | 625, 724, 763 s | **412, 419, 491 s** |
| `parse_tests`, two full gates an hour apart | 23.9 s | 13.9 s |
| the whole gate, the same two | 1 329 s | 1 151 s |

**No ratio here is clean.** Another job was running on the machine through the morning
— JVM processes, taken for idle servers until `top` showed one at 116 % CPU and
`wi_tests` at 65 % of its 1 200 %. So the two sets of runs do not overlap, and that is
what can be said: somewhere between the 1.27× of the two gates and the 1.74× of one
back-to-back triple, with §5.1's 1.5–1.6× for one load on one quiet thread the number to
plan from. The load average that the first write-up of these runs called unexplained
(85–97 after a shared-base run, 29 after a fresh one) was that job's, not the recipe's:
a five-second sample of `wi_tests` on the base shows its threads hashing, comparing and
allocating, and waiting on the base's lock nowhere near the top of any stack. §2.4's
count of loads by route was not re-taken, and the table wants re-taking on a quiet
machine.

### 5.4 The subprocess suites

`cmd_tests` (46 min) and `cli_tests` (7 min) do not benefit from an in-process base: every
spawn is a fresh process. (2026-10-06, optimized: 162–240 s and 33–57 s — option (c) below,
taken. What (a) would still buy is to be re-estimated from those, not from 46 min.) Options:

- **(a) An in-process entry point.** `anthill-todo` and `anthill` get a library function —
  `run(argv, cwd, env) -> (status, stdout, stderr)` — that `main` is a one-line wrapper
  around, and the tests call it directly, sharing a base KB as in §5.1. The isolation the
  subprocess gave (cwd, env) becomes explicit arguments, which the `cmd_tests.rs` header
  already demands of every test (every spawn must pass `-d` or `current_dir`). A handful of
  tests that assert process-level facts (exit codes on a signal, the real `main`'s argument
  stripping, project discovery from a cwd) keep spawning, and say so at the site.
  Expected: `cmd_tests` from 46 min to a few minutes.
- **(b) Snapshot in the binary** (§4 A6) — fixes the product cold start too. Larger; later.
- **(c) Nothing but A1** — an optimized `anthill-core` makes each spawn's load cheaper by
  whatever §2.5 says. Free once A1 is decided.

### 5.5 What lever B does not change

The one-shot load path, the CLI, the `anthill-todo` cold start, and every test that asserts
on the *act* of loading the stdlib (`incremental_load_test`, `stdlib_drift_test`, the
re-type suites). Those stay on the fresh recipe by name, and the count of such sites is a
number the doc can carry (today: 5 + 19 + 8, §5.3).

## 6. Lever C — run less per gate, or on more machines

These are policy, not engineering, and the repo rule today is explicit: before a
non-documentation commit, all tests pass. The doc lists the options so the decision is
informed; it does not recommend changing the rule until A and B have been measured.

- **C1. Tiered gate.** Local, per WI: the crate the WI touched, `--lib`, and the WI's own
  include file (`-p anthill-core --test wi_tests -- wi_xxxx`), minutes. Full workspace:
  before the commit, as now — but on the fast box or in the cloud (>60 min there today,
  which A+B would also cut). The risk is the one the principles name: a regression in a
  binary the local tier skipped. It is bounded by the full tier still existing; what changes
  is *when* it runs relative to the edit loop.
- **C2. Sharding.** `cargo test` cannot split a binary across machines; `cargo-nextest`'s
  `--partition` can, but nextest's one-process-per-test runs against lever B (every test
  would load its own base). A shard **by binary** is possible with plain cargo (`test.sh`
  already runs tiers) and is coarse: `wi_tests` is 63 % of the run by itself. A finer split
  of `wi_tests` into N aggregators by hash of the file name is one `#[path]` list edit per
  file and gives N independently-launchable binaries — at the cost of N launch-assessment
  taxes on macOS, paid once per build.
- **C3. Thread count.** 12 threads on 6 physical cores. On a hash-and-allocate workload the
  second hyper-thread buys little and each thread holds a full KB (memory bandwidth, cache).
  Measure `ANTHILL_TEST_THREADS=6` against 12 on an idle machine once; it may be a free 10 %
  either way. **Measured 2026-10-06 (§2.5, load throughput):** 12 threads against 6 is +23 %
  at opt-level 0, and with `anthill-core` at 2 it is +6 % — inside that table's noise, so
  "no difference". The default stays; not a lever.
- **C4. Fewer loads per test.** Some tests load three times for a control, a refusal and a
  clean run. With lever B each is cheap, so this stops mattering. Without it, it is an audit
  of 3 100 sites for a few percent — not worth it.

## 7. Compile-time side (small on 2026-10-05; a fifth of the gate since A1)

- Incremental rebuild of the library and all 21 test binaries after an edit: 23 s, 127 s and
  180 s on three runs on 2026-10-05, at opt-level 0. `wi_tests` alone is 669 include files,
  267 k lines (the 298 k first written here is all 714 files under `tests/include`); it is
  one compilation unit, so any `anthill-core` API change recompiles it whole. Not a lever at
  2 % of the gate, but A1 raises this term and §2.5 measures both sides.
- A cold `cargo build -p anthill-cli` on this machine: 125 s wall (395 s CPU).
- **`anthill-core` was built several times a gate, and now is not** (2026-10-06,
  WI-20261006-ZVV24; raw: `compile-cost-2026-10-06.txt` §4). Cargo unifies features across
  what ONE invocation builds, so a dependency of `anthill-core` that resolves different
  features under different selections makes `anthill-core` a different build per selection.
  Two did: `chrono` (`anthill-todo` asked for the default features, `anthill-core` for
  `clock` alone — and `anthill-todo` is in the gate's second invocation only) and `serde`
  (`anthill-smt-gen` turned on `derive`, which hangs `serde_derive` — and through it `syn`,
  whose features follow clap's derive — under `anthill-core`'s own `serde`). Measured
  before: four library builds in one gate, and a rebuild whenever a `-p anthill-core` run
  was followed by a wider one. After giving `anthill-todo` the `chrono` features
  `anthill-core` has and moving `anthill-smt-gen` to `serde_derive` directly, the gate's
  second cargo invocation compiles for **4 s** after a core edit, down from 98–115 s.
  `anthill-version`'s `chrono` — a BUILD-dependency, so the host side — was aligned with
  them; it was not a cause of the gate's rebuild (both invocations include that crate), it
  keeps the host build of `anthill-core` the same for a selection that leaves the crate out.
  The rule this leaves: **no workspace crate enables, on a dependency `anthill-core` also
  has, a feature that `anthill-core`'s own line does not.** A subset is harmless
  (`smallvec = "1"` beside `anthill-core`'s `const_generics`). `test.sh` now refuses to run
  when the rule is broken on the target side — it compares what `anthill-core`'s
  dependencies resolve to alone and in the whole workspace — because nothing else reports
  it: every selection still builds and passes. The host side it cannot see.
- What a gate still compiles after a one-line edit to `kb/load.rs`, optimized: **229–306 s**
  (2 150–2 230 s of CPU) in the first invocation — the library three times at once: the
  target build, the host build (`anthill-core` is a build-dependency of `anthill-stl`, and
  the host side resolves `serde_json/preserve_order` through `tree-sitter`'s build script,
  so it is a second flavour), and the unit-test harness. The host build need not be
  optimized — it runs one load in `anthill-stl`'s build script — but a NAMED package
  override outranks `build-override`, so it is. The way out is the inverted spelling
  (`[profile.dev] opt-level = 2`, every other workspace crate pinned to 0 by name), which
  leaves host builds to `build-override`; not taken, because it makes "optimized" the
  default a new crate gets in silence. Unmeasured; ~70 s a gate by the numbers above.
- **Fresh-clone trap, reproduced today.** `tree-sitter-anthill/build.rs` regenerates
  `src/parser.c` when `grammar.js` is *newer by mtime*. A clone or a pull sets `grammar.js`'s
  mtime to now while `src/parser.c` is gitignored and keeps its old one, so the build script
  runs `npx tree-sitter generate` — which fails on a machine without `npm install` in that
  directory (`npm error could not determine executable to run`). The fix is small: compare a
  content hash of `grammar.js` recorded next to `parser.c`, or regenerate only when `parser.c`
  is absent and leave explicit regeneration to `npx tree-sitter generate`. Worth a ticket
  only if the user agrees it bites; it bit this session's measurement.

## 8. Decisions that are the user's

1. **Profile. DECIDED 2026-10-06 (user): for the gate only** — `scripts/test.sh` passes
   `anthill-core` at opt-level 2 and the two tree-sitter crates at 3 on a full run, and
   `rustland/Cargo.toml` carries no override (§4 A1). "Always on, in the manifest" was the
   first choice and was reversed once the per-module rebuild costs were measured. With it:
   the native-stack budget of the eval/SLD crossing differs between the two builds and the
   optimized gate does not guard the unoptimized one — left DOCUMENTED, at
   `BRIDGE_REENTRY_CAP` in `kb/resolve.rs`, rather than guarded (user, same day).
2. **Order of A3 and B.** The doc's recommendation (§9) is A3 first because B is capped at
   ~1.7× without it; the alternative is B first at the capped gain, which still halves
   `wi_tests`, and A3 after. **B first, 2026-10-09 (user)** — done; A3 is next, one
   ticket a pass.
3. **`anthill-todo` in-process entry point** (§5.4 a): a change to the product's structure
   (a library crate with `main` as a wrapper), not only to tests. Both CLI crates are
   bin-only today and `anthill-todo/src/main.rs` writes through 129 `println!`/`eprintln!`
   sites with no writer threaded, so it is a larger change than §5.4 reads — and
   `cmd_tests` is 240 s now, not 46 min.
4. **Gate policy** (§6 C1): untouched until A and B are measured, unless the user wants the
   tiered gate now.
5. **Tickets.** Filed 2026-10-06 under the tag `test-infra`: WI-20261006-ZVV24 (A1, this
   change), WI-20261006-SZKV7 (the two-step load switch — the control A3 and B rest on,
   which §9 did not have as a step of its own), and WI-059 rewritten as B. A3 goes one
   ticket per pass, filed one at a time (user, 2026-10-06). Not filed: A2, `Clone + Send`,
   §5.4 a, the §7 fresh-clone trap. **`Clone + Send` filed 2026-10-09** (user) as
   WI-20261009-D0SD4, a deep copy and a wrapper rather than what the name says (§5.2);
   WI-059 depends on it.
6. **What the two-step run found** (2026-10-07; §4 A3, §5.3, §2.4) — three things.
   (a) The sort loop's frontier — facts, and as review of the fix showed, rules:
   a bug by any reading, and `KB.loaded` had it — fixed inline, 2026-10-08 (user).
   (b) Equality derivation that a later written provider does not take back: decided
   2026-10-08 (user) — a rule, refused at load, and implemented inline: a non-monotone
   update is refused because other facts depend on what it would change. (c) The test
   files that carry their own copy of the load: routing them through the recipe is what
   puts them under the two-step control and, later, on the base KB — filed 2026-10-08 as
   WI-20261008-RAH0Z (user), and delivered the same day (§2.4). With (a) and (b) settled
   the control A3 rests on is green for every test it reaches, and since (c) that is
   every test but the ones pinned to a recipe by name.

7. **Should a gate also run the fresh recipe?** (2026-10-09, /code-review of WI-059; NOT
   decided.) With the shared base the default, the ~9 000 helper loads of `anthill-core`
   no longer hand the loader the stdlib and a user file in ONE call — the shape the CLI
   uses. What still does: the library's own unit tests (their loader), the tests pinned
   to one shot by name, every load with a hook, and every other crate, the two CLI
   suites among them. So a loader change that misbehaves only when stdlib and user items
   share a batch has those to get past, and not `wi_tests`. And one class of legal
   program now gets a different verdict from `load_kb_with` than from `anthill`: a file
   that supplies an equality for a stdlib sort loads in one call and is refused as a
   later one (§4 A3). The options: leave it to whoever runs
   `ANTHILL_TEST_FRESH_LOAD=1` (the ticket's design); run `anthill-core` under it as a
   second tier of the gate (13–18 min more); or on a schedule rather than per commit.

## 9. Recommended sequence, with the measurement at each step

| step | what | measured by | expected / outcome |
|---|---|---|---|
| 0 | re-take §2 on a quiet machine; the opt-level rows and the compile deltas | the bench + `cargo test --no-run` after a one-line edit | **done 2026-10-06** — level 2 (§2.5) |
| 1 | A1: `anthill-core` at 2 and the tree-sitter crates at 3, for the gate | one full run, same log format as §1 | **done 2026-10-06** — 3 h 27 min → 30 min 40 s cold, 15 min 45 s warm (§1.1) |
| 2 | the two-step load switch in the one recipe (WI-20261006-SZKV7) | the `anthill-core` suite under the switch | **done 2026-10-07** — 2 tests of 7 873 differed, both loader findings (§5.3); both settled 2026-10-08 and the suite is green under the switch (7 923 / 0); the switch reaches only the loads that go through the recipe (§2.4) |
| 2a | every test's stdlib load through the one recipe (WI-20261008-RAH0Z) | the traced run's one-shot count under the switch (§10) | **done 2026-10-08** — 1 028 → 66 in the integration binaries, each of the 66 a test pinned by name and listed (§2.4); the suite is green under the switch (7 943 / 0), and step 5's base KB reaches the same loads |
| 3 | A2 hashing + `canonical_sym` cache | a profile RE-TAKEN at level 2 first, then the bench, `full` | unknown until re-profiled: §2.2's 22 % was SipHash as un-inlined calls at opt-level 0 |
| 4 | A3 frontier-driven `type_check_sorts`, `eq_derive`, `check_provider_requires` — one ticket a pass | the bench, `incr`; the full suite under both recipes | `incr` 0.15 s → ~0.01 s (optimized) |
| 5a | a deep copy of a KB, and a `Send` wrapper for the test base (WI-20261009-D0SD4) | the bench's `clone` rows; the copy's own controls | **done 2026-10-09** — 7.3 ms a copy, `full / (clone + incr)` 1.5–1.6× (§5.1); real `Send` is not available (§5.2) |
| 5 | B: base-in-recipe (WI-059) | one full run; `ANTHILL_TEST_FRESH_LOAD=1` run as control | **done 2026-10-09, before step 4** — green under all three recipes; `wi_tests` 625–763 s → 412–491 s, taken beside another job and to be re-taken quiet (§5.3). With step 4: a fortieth of a load a test, and a pool of bases (§5.1) |
| 6 | §5.4 a in-process `anthill-todo` entry | one full run | unmeasured: each spawn is a parse and a load (~0.4 s) plus the command; weigh against §8.3 |
| 7 | A4 hot spots as a level-2 profile ranks them; A5 allocator | the bench, one full run | single-digit % each. C3 thread count is measured and is not a lever (§6) |

Step 1 did what the model said in kind and less than it said in degree: the doc projected
"~5 min of `wi_tests`" and a gate under 20 min, and got 10–11 min and 16–31 min — the
projection divided by six cores where §2.4's own fit implied two, and counted call sites
where loads are executed. After it the gate is roughly **15–18 min of tests plus compile**
(4–5 min after an edit to a large `anthill-core` module, §7), and of the tests,
10–11 min are `wi_tests` and 3–4 are `cmd_tests`. Step 5 is still where the gate changes shape
rather than scale: a test stops paying for the stdlib at all, and what is left is the
tests' own bodies.

## 10. Appendix — how to re-take the numbers

```bash
# one stdlib load, four ways (debug); copy the example in first, remove it after
cp docs/measurements/test-infrastructure/bench_load.rs rustland/anthill-core/examples/
cd rustland && ITERS=5 cargo run -q --example bench_load -p anthill-core
ITERS=5 cargo run -q --release --example bench_load -p anthill-core

# per-phase trace of each load the bench does (the loader's own switch)
ANTHILL_LOAD_TIMING=1 ITERS=1 ./target/debug/examples/bench_load 2>&1 | grep load_timing

# sampling profile of the load loop (macOS); the call tree lands in the file
LOOP=1 ITERS=1 ./target/debug/examples/bench_load & sample $! 12 -mayDie -file /tmp/load-profile.txt; kill $!

# per-binary wall from a test.sh log (the table in §1)
grep -E 'Running|test result' target/test-run-latest.log

# the same bench at another setting, without touching the manifest (§2.5's rows).
# Plain `cargo run` is the "dev (opt-level 0)" row. This is the gate's build; drop the two
# tree-sitter lines for the "`anthill-core` at N" rows:
cargo run -q --example bench_load -p anthill-core \
  --config 'profile.dev.package.anthill-core.opt-level=2' \
  --config 'profile.dev.package.tree-sitter.opt-level=3' \
  --config 'profile.dev.package.tree-sitter-anthill.opt-level=3'

# the bench also prints `clone` — KnowledgeBase::deep_clone of the loaded stdlib — and
# `clone+incr`, the copy and then the user file loaded into it (§5.1's table)

# do loads scale across threads? N threads, ITERS loads each (§2.5's thread columns)
THREADS=12 ITERS=3 ./target/debug/examples/bench_load

# how many loads a suite EXECUTES, and what share of its time they are (§2.4).
# Raw cargo on purpose: this prints ~500k lines, and test.sh forks a process per line.
# (plain cargo is the unoptimized build; add the three --config lines above for the gate's)
ANTHILL_LOAD_TIMING=1 RUST_TEST_THREADS=12 cargo test --no-fail-fast -p anthill-core -- --nocapture > load-trace.log 2>&1
grep -c 'load_with_visited x' load-trace.log

# the suite under each of the other two recipes (§5.3); the default is the shared base.
# The log says which recipe was asked for (its `load:` line) and which one the control
# observed (`load recipe OBSERVED`).
ANTHILL_TEST_OPT=2 ANTHILL_TEST_FRESH_LOAD=1 scripts/test.sh -p anthill-core
ANTHILL_TEST_OPT=2 ANTHILL_TEST_TWO_STEP_LOAD=1 scripts/test.sh -p anthill-core

# how many of the stdlib loads the switch does NOT reach (§2.4): the trace above with the
# switch on. A `load_with_visited x N` with N ABOVE the stdlib's file count (87 today) is
# the stdlib and another file in ONE call — a one-shot load that is not the recipe's.
# N equal to it is a call given the stdlib alone: the recipe's first, or `load_stdlib_kb`.
# Under the same switch the recipe prints a line of its own for each load it makes
# (`tests/common`, `run_recipe`): `recipe_load <OneShot|TwoStep> user_files=<n>`.
#   TwoStep, n > 0   a load that followed the switch, or one pinned to two calls by name
#   OneShot, n > 0   a load pinned to ONE call by name (`LoadRecipe::OneShot`)
#   OneShot, n = 0   the stdlib alone, through `load_stdlib_kb`
# An N > 87 load with no `OneShot, n > 0` line is one a test made by hand.
ANTHILL_LOAD_TIMING=1 ANTHILL_TEST_TWO_STEP_LOAD=1 RUST_TEST_THREADS=12 \
  cargo test --no-fail-fast -p anthill-core -- --nocapture 2>&1 \
  | grep -a -E 'load_with_visited x|recipe_load|Running |Doc-tests|test result' > load-trace.log
```

Everything in §1 came from `rustland/scripts/test.sh`'s own log: its elapsed-seconds
prefix on every line is what makes the per-binary table and the throughput curve free.
