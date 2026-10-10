# CLAUDE.md — Rust Implementation

## Build & Test

All commands from `rustland/`:

```bash
cargo build                                         # build all crates
cargo build -p anthill-todo                         # build todo CLI
```

**Always run tests via `scripts/test.sh`** — it forks a pty so `Running …`
lines aren't buffered, logs to `target/test-run-latest.log`, and gives
live per-binary progress. Plain `cargo test` buffers under
`| tail` and shows nothing until cargo exits, which makes hangs
indistinguishable from slow compiles.

```bash
scripts/test.sh                                     # full workspace (the gate), live progress
scripts/test.sh -p anthill-core                     # one crate
ANTHILL_TEST_OPT=2 scripts/test.sh -p anthill-core  # ...optimized: 13 min, not 2 h (see below)
scripts/test.sh -p anthill-core --lib               # unit tests only
scripts/test.sh -p anthill-core --test github_todo  # one integration binary
scripts/test.sh -p anthill-core -- debruijn_multi   # filter by test name
scripts/test.sh -p anthill-core -- --nocapture      # show eprintln output

scripts/test-status.sh                              # report current/last binary + last log write age
```

Reach for raw `cargo test` only when you specifically need a behavior
`test.sh` doesn't provide (e.g. doc-tests, `--exact`, custom test
runners).

**Two builds: the gate's is optimized, the edit loop's is not.** A full run
(`scripts/test.sh`, no arguments) builds `anthill-core` at opt-level 2 and the two
tree-sitter crates at 3; a SELECTED run uses the plain dev profile. `ANTHILL_TEST_OPT=2`
or `=0` overrides either default. Debug assertions and overflow checks are on in both.
The setting is passed by the script and is NOT in `Cargo.toml` — its header says why, in
full; the short of it (WI-20261006-ZVV24; `docs/design/test-infrastructure.md` §1.1, §2.5):

- Optimized, a stdlib load is 0.3 s instead of 2.1 s, and the suites execute ~9 300 of
  them: the gate went from over 3 hours to ~16 min, ~20–25 after an edit to `anthill-core`.
- Optimized, the REBUILD after an edit costs 1–2 min where opt-level 0 takes 8–16 s — for
  most of `anthill-core`'s sources and for `tests/common/mod.rs` (`kb/load.rs` ~80 s, a
  one-line accessor in `kb/term.rs` ~130 s, a typer module ~26 s, one test file ~10 s).
  It follows how widely the edited code is used, not the size of the file.

So: iterate on a few tests with a selected run, set `ANTHILL_TEST_OPT=2` for a WIDE
selection (a whole crate), and let the full run be the gate. The two builds live side by
side in `target/`; raw `cargo test` / `cargo build` are the unoptimized one.

**Three load recipes; the gate runs the shared base.** `anthill-core`'s shared load
helpers (`tests/common/mod.rs`, `LoadRecipe`) give a test a COPY of the stdlib loaded
ONCE per test binary and `load_all` the test's own files into it (WI-059;
`KnowledgeBase::deep_clone`, WI-20261009-D0SD4). The stdlib is 0.3 s to load and 7 ms to
copy. Two switches select the other recipes, for every such load of the run:

```bash
ANTHILL_TEST_OPT=2 ANTHILL_TEST_FRESH_LOAD=1    scripts/test.sh -p anthill-core   # one `load_all(stdlib ∪ user)`, fresh KB
ANTHILL_TEST_OPT=2 ANTHILL_TEST_TWO_STEP_LOAD=1 scripts/test.sh -p anthill-core   # stdlib, then user, fresh KB
```

They are controls, not more gates: the three must give every test the same verdict. Reach
for `ANTHILL_TEST_FRESH_LOAD=1` FIRST when a test fails in a way that looks like the
load's — it is what the CLI does. A test that differs is an assertion on the recipe, a
loader finding, or a fixture that by the language's own rule belongs in the stdlib's
load: under the shared base and under two steps a test's files are a LATER load than the
stdlib's, and a later load may not add to the equality of a stdlib sort, declare one of
its names again, or reach into its bodies — a `@[simp]` rule that rewrites one, a
provision of a stdlib spec at stdlib types that changes who answers a dispatch
(`kernel-language.md` §8.3). That last kind is pinned to one load BY NAME, with the
reason at its site (WI-20261006-SZKV7; the list of every test outside the switch is
`PINNED` in `wi_rah0z_one_recipe_test`, and `docs/design/test-infrastructure.md` §5.3 has
the runs).

The log carries the recipe the script was asked for (`load:`) and the one the control
test observed (`load recipe OBSERVED`). A load is OFF the shared base, and gets a fresh
KB, when it asks for something the base cannot give: a hook run before the stdlib's load
(`try_load_kb_prepared*`, `load_outcome_files_prepared`, `load_stdlib_kb_prepared` — a
closure that does nothing still counts, the recipe cannot see inside one), load options
other than the default (the `*_untyped` helpers), or a recipe named at the call. The
tests pinned by name, the library's unit tests and every other crate run one-shot
whatever the switches say.

**A sealed load's bodies are typed once** (WI-20261010-9BKZ4). Every recipe SEALS the
stdlib's load (`load::seal_declarations*`, WI-20261009-4ZRTG), and the typer's two
whole-KB sweeps — the free-operation sweep, the rule-body sweep — skip what a seal holds;
what a later load could have changed in a sealed body is a load error instead
(`kb/typing/sealed.rs`, `LoadError::ChangesSealedCode`) — raised by the TYPER, so a run
made by hand (`type_check_sorts(&mut kb, result.loaded())`) raises it as the pipeline's
does, and read off the KB, so a load made after a refused one is refused again. Nothing sealed, nothing skipped:
a plain sequence of `load_all` calls, and `KB.loaded` over one, types every body at every
load as before. A new whole-KB sweep in the typer owes the same question — is this body a
sealed load's — and a new way for a later load to change how an earlier body is READ owes
a refusal there. The control that nothing was skipped that should have been typed:

```bash
ANTHILL_TYPER_ORACLE=1 ANTHILL_TEST_OPT=2 scripts/test.sh -p anthill-core   # types sealed bodies too, and fails a load that changes one
```

It is slow (about twice the run) and is for a change to the typer's sweeps or to what a
seal holds, not for the gate. `typing::bodies_typed_by_this_thread` counts what a load
typed, for a test that a body was NOT.

**A third control: which carrier a declared type rides.** A type is read through the
carrier-neutral view (`TermView`, `extract_type`), and a reader that matches the carrier
instead — a `Value::Term` gate, a `_ => false` for "a carrier this cannot read" — answers
for a term and not for the same type on an occurrence. `ANTHILL_TEST_NODE_CARRIER=1` makes
the loader put every sort named in an operation's parameter or result type, in an
entity's field type, in a const's type, in the type arguments a call writes, in an
annotation or in a rule head's bound on the occurrence a type alias written there rides
(`TypeNode::Aliased`), standing for itself:

```bash
ANTHILL_TEST_NODE_CARRIER=1 scripts/test.sh          # the whole workspace, every load
```

The node changes no meaning, so every test must have the verdict it has without the
switch; one that differs names a reader that bypasses the view. Run it when a change
touches how a type is carried or read. The loader reads the switch
(`node_carrier_control`), so it reaches every load of every crate, the spawned binaries
too. The log carries what was asked for (`carrier:`) and what
`alias_written_name_test` observed (`node carrier OBSERVED`). To find the reader behind a
difference, print each `unify_types` / `types_compatible` pair in both modes and diff:
reading the code does not find it. The fix is then proved without the switch — a type that
holds a value (`Foo[T = Int64, N = 3]`) rides an occurrence on its own
(`value_holding_type_readers_test`).

The native-stack budget of the eval↔SLD crossing differs between the two builds, and the
optimized gate does not guard the unoptimized one — see `BRIDGE_REENTRY_CAP` in
`kb/resolve.rs` before changing anything on that path.

**No workspace crate may enable, on a dependency `anthill-core` also has, a feature
that `anthill-core`'s own `Cargo.toml` line does not.** Cargo unifies features across
what one invocation builds, so one extra feature makes `anthill-core` a different build
per selection — it was compiled four times a gate, over `chrono` and `serde/derive`,
before that was found, and each build is ~110 s when optimized. A subset is harmless
(`smallvec = "1"` beside `anthill-core`'s `const_generics`). `scripts/test.sh` refuses to
run when the rule is broken and names the dependency; for derive macros, depend on
`serde_derive` directly, as `anthill-smt-gen` does.

## Crate Structure

- `anthill-core` — parser, KB, resolution, codegen (the core library)
- `anthill-cli` — CLI binary: `anthill load/query/check/codegen`
- `anthill-stl` — standard library Rust-side support
- `anthill-todo` — work-item management CLI

## Module Map (`anthill-core/src/`)

| Module | Role |
|--------|------|
| `intern.rs` | `SymbolTable`: string interning (`Symbol(u32)`), scope-aware resolution. Also the sole owner of the `_N` positional-field-label convention — `positional_label` / `positional_label_index` / `is_positional_label_at` (WI-790) |
| `parse/convert.rs` | Tree-sitter CST → typed IR (`ParsedFile`) |
| `parse/ir.rs` | Parse IR types: `Item`, `ParsedFile`, `SimpleTermStore` |
| `kb/term.rs` | `Term`, `TermId`, `TermStore` (hash-consed), `Var` enum |
| `kb/mod.rs` | `KnowledgeBase`: indexes, `assert_fact`, `assert_rule_debruijn_with_nodes`, `with_fresh_vars` |
| `kb/load.rs` | Load ParsedFile → KB: `scan_definitions`, symbol remapping |
| `kb/resolve.rs` | SLD resolution: `SearchStream`, builtins, NAF, delay |
| `kb/discrim.rs` | `SubstTree`: discrimination tree for structural matching |
| `kb/subst.rs` | `Substitution` with `bind_compressed` (path compression) |
| `kb/typing.rs` + `kb/typing/` | The typer: one module split by topic into ~50 files that share one namespace (`use super::*`, glob re-exports). `typing.rs`'s module doc maps where things live |
| `codegen/rust.rs` | Generate Rust trait/struct/enum from anthill specs |
| `persistence/print.rs` | `TermPrinter`: render terms as `.anthill` text |

## De Bruijn Variables

Rules in the KB use `Var::DeBruijn(u32)`. The resolver opens them via `with_fresh_vars()`:
1. Allocate N fresh `Global(VarId)` for arity N
2. The occurrence body opens DeBruijn → Global through `open_debruijn_node` (its `TermId`-typed type channels still go through the interning `term_from_debruijn`); the head is never opened as a term — the match is fully encoded in `tree_subst`
3. `body_rename` substitutes concrete values from the head match directly into body terms
4. Only query-var linkages go into `answer_links` (not synthetic fresh→concrete bindings, to avoid O(n²) `bind_compressed`); each link is resolved through `body_rename` first so a nonlinear head's concrete match reaches the answer, occurs-checked — a cyclic link flags the match contradictory and the candidate is dropped (WI-624). A link is TRANSIENT (WI-20260905-N20EZ): built off the hash-consed store by `substitute_vars_transient` as a `Value::Var` (fresh leaf), a `Value::Entity` (rebuilt spine), or the shared `Value::Term` (untouched subterm) — a fresh `VarId` made every interned var term new, so the store grew per clause opened for ever. Every σ read chases through `chase_var`, which follows all three carriers; there is no `TermId`-only `walk` any more
5. A bodyless rule with arity > 0 also opens through `with_fresh_vars` — only *ground* arity-0 candidates take the resolver's raw-bind fact fast-path (WI-624). A legacy Global-var arity-0 head (the loader's omitted-field fresh fills) is non-ground despite arity 0, so it too opens through `with_fresh_vars`' arity-0 legacy path — freshening its head var per match — gated by the cached `RuleEntry.head_has_vars` flag so the routing stays an O(1) read, not a per-match head walk (WI-635)

## Where a new test file goes

**A file directly under `<crate>/tests/` is its own test binary.** Cargo compiles,
links and launches one process per such file. Add a new integration test to
`tests/include/` and register it in the crate's aggregator instead:

```rust
#[path = "include/wi1234_thing_test.rs"]
mod wi1234_thing_test;
```

Only *direct children* of `tests/` are auto-discovered, so a file under
`tests/include/` runs **only** if an aggregator names it. An unregistered file
compiles never and runs never, in silence — nothing warns. The invariant is that
every file in `tests/include/` is registered **exactly once** across the crate's
aggregators; this reports any drift:

```bash
cd anthill-core/tests && diff \
  <(grep -h -o '^#\[path = "include/[^"]*"' *.rs | sed 's|.*include/||;s|"||' | sort) \
  <(ls include/*.rs | sed 's|include/||' | sort)
```

| Crate | Where to register |
|---|---|
| `anthill-core` | `wi_tests.rs` — the default for a per-WI test. Topic binaries `algebra_tests.rs`, `builtin_tests.rs`, `eval_tests.rs`, `induction_tests.rs`, `parse_tests.rs`, `resolve_tests.rs` also aggregate; pick one, not both |
| `anthill-cli` | `cli_tests.rs` |
| `anthill-todo` | `cmd_tests.rs` |
| `anthill-cpp-gen`, `anthill-rust-gen`, `anthill-smt-gen` | `autotests = false` + an explicit `[[test]]` block in `Cargo.toml` — same goal, different mechanism |

Inside an aggregated file, `common` is the *crate root's* module: write
`crate::common::…` and do NOT declare `mod common;` — the aggregator owns that,
and a second declaration is a compile error.

This is not tidiness. Each extra binary costs a link and a process launch, and on
macOS the FIRST execution of a freshly built binary stalls in an out-of-process
launch assessment — measured 35–92 s with zero in-process CPU, verdict cached by
content, no path exclusion available. Consolidating `anthill-cli` and
`anthill-todo` cut their wall-clock from ~2940 s and ~2520 s to 24 s and 424 s;
folding `anthill-core`'s stragglers in took the workspace from 42 integration
test targets to 21.

A test that genuinely needs its own process — its own `fn main()`, a custom
harness, or process-global state (env vars, cwd) that would leak across a shared
binary — stays a direct child of `tests/`, and says at its site why.

## Test Patterns

Integration tests in `anthill-core/tests/` follow:
1. Load through a `tests/common` helper — THE ONE RECIPE. Do not collect the stdlib and
   call `load_all` yourself: 174 files once did (WI-20261008-RAH0Z), each re-reading
   and re-parsing the stdlib at every load, and each outside the recipe's switches
   above — and, now, off the shared base. Pick by what the test reads:

   | the test wants | helper |
   |---|---|
   | a KB; a load error fails the test | `load_kb_with(src)`; files on disk: `load_kb_with_user_files(&user_paths(&files))` |
   | the errors, rendered | `load_errors_of(src)`, `load_errors_of_files(&[..])`; `try_load_kb_with*` for a `Result` |
   | the loader's `LoadError` values | `unrendered_load_errors_of(src)` |
   | a clean load's warnings, or the KB a REFUSED load left beside its errors | `load_outcome(src)`, `load_outcome_files(&[UserFile::..])` — a `LoadOutcome`; `load_outcome_files_prepared(.., hook)` when something must be mounted BEFORE the load (a fresh KB, off the shared base) |
   | the stdlib alone | `load_stdlib_kb()` — a copy of the shared base, no load; `load_stdlib_kb_prepared(hook)` for its `LoadResult` or a hook before the load (a fresh load) |
   | anthill-todo's store bundle under a driver | `load_anthill_todo_store_bundle(&[driver])` |
   | the user file's own `LoadResult` (a re-type test) | `load_stdlib_kb_with_source(src)` — two calls, by name |

   A local helper that only forwards is an alias — `use crate::common::load_errors_of
   as load_errors;` — not a `fn`: a function is where the next copy starts.

   A test whose SUBJECT is the load's shape — how many calls, in what order, through
   which entry point or with which options — makes its own `load_all` over
   `common::stdlib_parsed()`, or names its `LoadRecipe`, and says why at the site
   (`NOT THE RECIPE, BY NAME`). `wi_rah0z_one_recipe_test` enforces it: a test file
   that names a way out of the recipe is in that file's `PINNED` list, with its reason
   and its count, or the guard fails.
2. `load_all` BOOTSTRAPS. Do not call `register_prelude` or the
   builtin-tag pass first; every load entry point owns that, and the
   pre-registering "house sequence" was deleted from 172 files (WI-967).
   `register_prelude` is for a hand-built KB that never loads; the KB method
   `register_builtin_tags` is `pub(crate)` and has exactly one caller.
   `eval::builtins::register_standard_builtins` is a DIFFERENT function — it binds
   host fns on an `Interpreter`, and you DO call it per fresh interpreter (WI-968).
3. Need the file in the KB *without* the checks? `load_all_with(.., LoadOptions {
   run_typer: false, .. })` — it stops immediately before the typer, so everything the
   typer reads is built. Then drive the typer with `type_check_sorts(&mut kb,
   result.loaded())` — the load's own work list, the sorts it defined AND the clauses it
   asserted — and it cannot disagree with the pipeline's own call, which is given
   exactly that. The typer takes nothing else: a list of sorts alone used to be accepted
   and missed every fact and rule a file wrote under a sort an EARLIER load defined
   (WI-20261006-SZKV7). `Loaded::nothing()` re-runs the whole-KB passes (the free-op
   sweep) over a KB nothing was added to.
   There is no separate single-file `load` any more (WI-20260901-Q68AK);
   it was a second copy of the prologue and its earlier stop point is what let a shipped
   test assert a refusal the real pipeline never makes (WI-20260901-7ZZ1Z).
4. READ the loader's verdict — never `let _ = load_all(..)`. A discarded `Err` is
   not a worse message, it is no guard: the test then asserts over a KB that never
   finished loading, and stays green. `common::expect_loaded` to fail on it,
   `common::expect_load_errors` to PIN it when the fixture is dirty on purpose, or
   a named `*_lenient` helper. `load_kb_with` panics on load errors in all three
   test crates. Enforced by `wi966_loader_verdict_test` (WI-966).
5. Build query term, call `kb.resolve(&[query], &config)`
6. Assert on `solutions.len()`, `subst.resolve_with_term(var)`, `kb.reify(var, &subst)`

## Conventions

- `SmallVec<[T; N]>` for term args. Use `from_elem` for single, `from_slice` for multiple (requires `Copy`).
- Named args canonicalized for stable hash-consing/discrim matching — by DECLARED
  field order when the functor has a schema, else interning order
  (`canonicalize_record_named_args`). Not alphabetical. Exempt: an ORDERED
  PRODUCT (named tuple), whose source order is its identity.
- Positional field labels are `_1`, `_2`, … (ONE-based, spec §4.5). Never spell
  them with a local `format!` or `strip_prefix('_')` — mint via
  `intern::positional_label(i)` and read via `positional_label_index` /
  `is_positional_label_at` (WI-790). Anything else `_`-prefixed (`_0`, `_01`,
  `_b`) is a USER label, reachable only by name and never re-slotted positionally.
- A scope is a `ScopeId`, never a raw and never a term. Mint it with
  `SymbolTable::scope_id(owner_symbol)` and read its owner with `ScopeId::owner()`.
  Never carry the scope's TERM and project back: the owner projection is total off
  the symbol and was not off the term (WI-984), and carrying the term let a value
  that named no scope reach 22 readers before anything noticed (WI-1028).
  A site that must PUT the scope where a term goes derives one there
  (`make_name_term_from_sym(scope.owner())`) — but must not then match on its SHAPE:
  that derivation applies the WI-511 canon (`Ref` for a constructor owner, `Fn`
  otherwise), so a `Term::Fn` test on the result is an unnamed `is_constructor_symbol`
  read. To ask a question ABOUT the scope, ask the owner — `load::is_sort_scope` was
  the last predicate doing it the other way and WI-1029 retired it. The same canon
  read from the other side is at `KnowledgeBase::resolve_qualified_name_term`.
- `assert_rule_debruijn_with_nodes` for rules (converts vars; term bodies first go through `term_body_to_nodes`), `assert_fact` for ground facts (arity 0).
- `FnArg` is `Copy` (both `TermId` and `Symbol` are `Copy`).
- `KnowledgeBase::deep_clone` (`kb/deep_clone.rs`, WI-20261009-D0SD4) returns a copy that
  shares NO `Rc` with its original, and the test suites' `common::SendableKb` hands such
  a copy to another thread on that promise — its `unsafe impl Send` is sound only while
  the promise holds. So the copy is a struct literal with no `..`, and a field passes
  either `plain` (bounded `Clone + Send`: the compiler's proof that it holds no `Rc`) or
  a hand-written copier. When a new field, or an `Rc` added to an old type, stops that
  file compiling: WRITE THE COPIER (new `Rc`, every leaf through `plain`) or refuse the
  state with a `DeepCloneError`. Never loosen the bound and never `clone()` an
  `Rc`-bearing value there — that compiles, passes most runs, and corrupts a count.
