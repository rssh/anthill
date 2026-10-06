# Test infrastructure — making the gate fast

**Status.** Brainstorm with measurements, 2026-10-05. Nothing here is decided; §8 lists
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
once per spawned process. Three levers, in the order they should be pulled:

| lever | what it attacks | expected gain | cost |
|---|---|---|---|
| A1. build the tests optimized (§4 A1) | the 4.8 s | **the same load is 7.9× faster at opt-level 3** (§2.5); opt-level 1/2 with assertions still to measure | one `[profile.test]` line + a compile-time measurement |
| A2–A4. hashing, frontier-driven passes, hot spots (§4) | the 4.8 s, and the 2.9 s "incremental" load | tens of % each; A3 is what makes B pay | hours to days each |
| B. load the stdlib once per process, clone per test (§5) | the ×3 100 | wi_tests from hours to minutes — **but only after A3**, which is a prerequisite | days |
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

## 2. The unit of cost: one stdlib load

All numbers in this section: 2026-10-05, this machine, **debug profile** (what `cargo test`
builds), **with the user's gate run in flight** (load average 10–20), so absolute values are
inflated — roughly 1.5× is a fair guess — while ratios hold. Re-take on an idle machine
before quoting them anywhere else. Recipe: `docs/measurements/test-infrastructure/bench_load.rs`
(a throwaway `anthill-core` example; copy it into `anthill-core/examples/` to run, do not
commit it there, `cargo test` builds examples). Per-phase trace:
`docs/measurements/test-infrastructure/load-phases-debug-2026-10-05.txt`, taken with the
loader's own `ANTHILL_LOAD_TIMING=1` switch (`load_phase_inner`'s `mark!`).

### 2.1 Four numbers

| measurement | median of 5 | what it is |
|---|---:|---|
| `parse` | 0.52 s | read + tree-sitter parse of the 87 files (73 `stdlib/anthill`, 14 `anthill-stl/anthill`) |
| `full` | **4.85 s** | fresh `KnowledgeBase::new()` + `load_all(stdlib ∪ bindings ∪ one 4-line user file)` — **what every `load_kb_with` pays** |
| `pre_typer` | 2.25 s | the same with `LoadOptions { run_typer: false }` — everything before the typer |
| `incr` | **2.40 s** | `load_all(one 4-line user file)` into a KB that already holds the stdlib — **what a cached-KB design would pay today** |

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

### 2.5 The optimized-build numbers

`rustland/Cargo.toml` has no `[profile]` section: tests run at `opt-level = 0`. The same
bench built `--release` (`nice -n 19`, `-j 3`, during the user's run — so if anything this
row is *pessimistic*; raw output in `bench-release-2026-10-05.txt`):

| profile | `parse` | `full` | `pre_typer` | `incr` | `full` ratio |
|---|---:|---:|---:|---:|---:|
| dev (opt-level 0, debug-assertions on) | 0.52 s | 4.85 s | 2.25 s | 2.40 s | 1× |
| release (opt-level 3, debug-assertions off) | 0.19 s | **0.62 s** | 0.30 s | 0.36 s | **7.9×** |
| `[profile.test] opt-level = 1` (assertions on) | _to measure_ | | | | |
| `[profile.test] opt-level = 2` (assertions on) | _to measure_ | | | | |

The ratio is uniform across the four measurements (6.7–7.9×), so it is the code generation,
not one pass: un-inlined SipHash rounds, un-inlined `SmallVec`/iterator adaptors, and the
debug-only precondition checks (§2.2) are what opt-level 0 costs on this workload.

Plugging it into §2.4's model: 3 100 loads × 0.62 s ≈ 32 min of thread-time, which on this
box is **~5 min of `wi_tests`** instead of 130, and the test bodies shrink by the same
factor. That is the whole gate under ~20 min on the laptop **before any code changes**,
to be confirmed by one full run at the chosen level.

What decides the level: **load speed × loads per gate** against **compile time × edits per
WI**. The release build above cost ~790 s of CPU for `anthill-core` + the bench (at `-j 3`,
niced) against ~395 s for the whole debug CLI build — roughly 2× at opt-level 3; opt-level 1
is known to be much cheaper to compile than 3. Still to measure, on an idle machine: the
incremental rebuild of `anthill-core` + `wi_tests` after a one-line edit at levels 1, 2 and
3 (today, opt-level 0: 23–180 s, §1), and the load at 1 and 2 with assertions on.

## 3. The cost model, and what it rules out

```
gate_wall ≈ Σ_tests (loads × T_load + T_test_body) / effective_cores  +  T_compile  +  T_subprocess_suites
```

- `T_load` is lever A. `loads` is lever B. `effective_cores` and the Σ are lever C.
- `T_test_body` (resolution, eval) is small next to the load for almost every test; the
  throughput curve in §1 says there is no class of slow tests to hunt. Not a lever today.
- `T_compile` is 2 % of the gate. Not a lever today — but it is the term that lever A1
  (opt-level) can make worse, so it is measured alongside.
- Reordering binaries, a different test runner, retries, fail-fast: none change any term.
  `cargo-nextest` in particular runs **one process per test**, which is exactly the shape
  lever B cannot live in (§5.4); it would also not help, since the launch-assessment tax is
  per binary content and already paid once.

## 4. Lever A — make one load cheaper

This is the user's question of 2026-10-05, "can we speed up load", and it pays everywhere:
every test, every `anthill-todo` cold start, every `anthill check`.

### A1. Build profile

Debug `opt-level = 0` on a workload that is hash maps, small vectors and symbol resolution
costs **7.9× on the load** (§2.5, measured). This is the single cheapest thing to do and the
first step of §9. The options, in order of blast radius:

1. `[profile.test] opt-level = 1` (or 2), keeping `debug-assertions = true` and `overflow-checks`.
   Applies to everything `cargo test` builds, so `cargo build` and `cargo test` stop sharing
   the `anthill-core` artifact — one extra compile of the library per profile, not per run.
   Keeps the assertions, which this codebase leans on (`debug_assert!`, precondition checks
   — the `copy_nonoverlapping::precondition_check` frames in the profile are those).
2. `[profile.dev.package."*"] opt-level = 3` — dependencies only. **Likely near-useless
   here**: `HashMap`, `SmallVec` and the hashers are generic and get monomorphized inside
   `anthill-core`, so they compile at `anthill-core`'s level, not the dependency's. The
   tree-sitter C parser is compiled by `cc` at its own `-O` already. Measure once to
   confirm, then drop.
3. `debug = 1` (line tables only) instead of full debug info: cuts link time and binary size,
   no run-time effect. A compile-side win only.

Decision rule: pick the highest level at which the incremental rebuild after a one-line
edit to `kb/load.rs` stays under what the user tolerates in the edit loop (the doc's
guess: ~60 s), given the gate saving at that level. Both halves get measured in §2.5.

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
`T_clone` is unmeasured (there is no `Clone` yet); a KB of this size is a few MB of hash
maps and vectors, so tens of milliseconds in debug is the expectation. With 12 threads
cloning under one mutex that is still far below one load; a pool of N bases is the fallback
if contention shows.

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
- **Not `Sync`** is fine: the `Mutex` provides exclusive access for the clone.
- `Interpreter::new(kb)` takes the KB by value (81 sites) — a clone is exactly what it wants.

### 5.3 Where the switch lives, and the control

The one recipe, `try_load_kb_named_prepared_with` in `anthill-core/tests/common/mod.rs`.
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

### 5.4 The subprocess suites

`cmd_tests` (46 min) and `cli_tests` (7 min) do not benefit from an in-process base: every
spawn is a fresh process. Options:

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
  either way.
- **C4. Fewer loads per test.** Some tests load three times for a control, a refusal and a
  clean run. With lever B each is cheap, so this stops mattering. Without it, it is an audit
  of 3 100 sites for a few percent — not worth it.

## 7. Compile-time side (small today, watch it)

- Incremental rebuild of the library and all 21 test binaries after an edit: 23 s, 127 s and
  180 s on three runs today. `wi_tests` alone is 669 include files, 298 k lines; it is one
  compilation unit, so any `anthill-core` API change recompiles it whole. Not a lever at 2 %
  of the gate, but A1 raises this term and §2.5 measures both sides.
- A cold `cargo build -p anthill-cli` on this machine: 125 s wall (395 s CPU).
- **Fresh-clone trap, reproduced today.** `tree-sitter-anthill/build.rs` regenerates
  `src/parser.c` when `grammar.js` is *newer by mtime*. A clone or a pull sets `grammar.js`'s
  mtime to now while `src/parser.c` is gitignored and keeps its old one, so the build script
  runs `npx tree-sitter generate` — which fails on a machine without `npm install` in that
  directory (`npm error could not determine executable to run`). The fix is small: compare a
  content hash of `grammar.js` recorded next to `parser.c`, or regenerate only when `parser.c`
  is absent and leave explicit regeneration to `npx tree-sitter generate`. Worth a ticket
  only if the user agrees it bites; it bit this session's measurement.

## 8. Decisions that are the user's

1. **Profile.** Whether `cargo test` may run optimized (§4 A1), and at what level, once §2.5
   has both the load and the compile numbers.
2. **Order of A3 and B.** The doc's recommendation (§9) is A3 first because B is capped at
   ~1.7× without it; the alternative is B first at the capped gain, which still halves
   `wi_tests`, and A3 after.
3. **`anthill-todo` in-process entry point** (§5.4 a): a change to the product's structure
   (a library crate with `main` as a wrapper), not only to tests.
4. **Gate policy** (§6 C1): untouched until A and B are measured, unless the user wants the
   tiered gate now.
5. **Tickets.** None filed from this doc; the repo rule is to ask first. Candidates:
   A1 (measure + decide), A2, A3 (one per pass, or one with three parts), B (§5.1–5.3),
   §5.4 a, the §7 fresh-clone trap.

## 9. Recommended sequence, with the measurement at each step

| step | what | measured by | expected |
|---|---|---|---|
| 0 | re-take §2 on an idle machine; fill §2.5's opt-level 1 and 2 rows and the compile deltas | the bench + `time cargo test --no-run` after a one-line edit | the A1 level |
| 1 | A1 `[profile.test]` change | one full run, same log format as §1 | up to 7.9× on every load (§2.5); the model says a gate under ~20 min on the laptop |
| 2 | A2 hashing + `canonical_sym` cache | the bench, `full` | −10–25 % per load |
| 3 | A3 frontier-driven `type_check_sorts`, `eq_derive`, `check_provider_requires` | the bench, `incr`; the full suite under both recipes | `incr` 2.9 s → <0.1 s |
| 4 | B `Clone` + `Send` + base-in-recipe | one full run; `ANTHILL_TEST_FRESH_LOAD=1` run as control | `wi_tests` 130 min → <10 min on this box |
| 5 | §5.4 a in-process `anthill-todo` entry | one full run | `cmd_tests` 46 min → minutes |
| 6 | C3 thread count; A5 allocator; A4 hot spots as the profile then ranks them | the bench, one full run | single-digit % each |

Steps 1 and 2 are independent of each other and of 3–5. Step 1 alone, if a full run
confirms the model, takes this laptop's gate from 3.5 h to the 10–20 min the fast box gets
today, and the fast box to a few minutes. Step 4 is where the gate changes shape rather than
scale: a test stops paying for the stdlib at all, and the gate's cost becomes the tests'
own bodies — which is the number that makes the current policy (full run per WI)
comfortable rather than a question.

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
```

Everything in §1 came from `rustland/scripts/test.sh`'s own log: its elapsed-seconds
prefix on every line is what makes the per-binary table and the throughput curve free.
