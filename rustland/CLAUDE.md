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
scripts/test.sh                                     # full workspace, live progress
scripts/test.sh -p anthill-core                     # one crate
scripts/test.sh -p anthill-core --lib               # unit tests only
scripts/test.sh -p anthill-core --test github_todo  # one integration binary
scripts/test.sh -p anthill-core -- debruijn_multi   # filter by test name
scripts/test.sh -p anthill-core -- --nocapture      # show eprintln output

scripts/test-status.sh                              # report current/last binary + last log write age
```

Reach for raw `cargo test` only when you specifically need a behavior
`test.sh` doesn't provide (e.g. doc-tests, `--exact`, custom test
runners).

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
| `codegen/rust.rs` | Generate Rust trait/struct/enum from anthill specs |
| `persistence/print.rs` | `TermPrinter`: render terms as `.anthill` text |

## De Bruijn Variables

Rules in the KB use `Var::DeBruijn(u32)`. The resolver opens them via `with_fresh_vars()`:
1. Allocate N fresh `Global(VarId)` for arity N
2. `term_from_debruijn` replaces DeBruijn → Global in head+body
3. `body_rename` substitutes concrete values from the head match directly into body terms
4. Only query-var linkages go into `answer_links` (not synthetic fresh→concrete bindings, to avoid O(n²) `bind_compressed`); each link is resolved through `body_rename` first so a nonlinear head's concrete match reaches the answer, occurs-checked — a cyclic link flags the match contradictory and the candidate is dropped (WI-624)
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
1. Load stdlib via `common::collect_anthill_files(&common::stdlib_dir())`
2. Parse + `load_all` — which BOOTSTRAPS. Do not call `register_prelude` or the
   builtin-tag pass first; every load entry point owns that, and the
   pre-registering "house sequence" was deleted from 172 files (WI-967).
   `register_prelude` is for a hand-built KB that never loads; the KB method
   `register_builtin_tags` is `pub(crate)` and has exactly one caller.
   `eval::builtins::register_standard_builtins` is a DIFFERENT function — it binds
   host fns on an `Interpreter`, and you DO call it per fresh interpreter (WI-968).
3. READ the loader's verdict — never `let _ = load_all(..)`. A discarded `Err` is
   not a worse message, it is no guard: the test then asserts over a KB that never
   finished loading, and stays green. `common::expect_loaded` to fail on it,
   `common::expect_load_errors` to PIN it when the fixture is dirty on purpose, or
   a named `*_lenient` helper. `load_kb_with` panics on load errors in all three
   test crates. Enforced by `wi966_loader_verdict_test` (WI-966).
4. Build query term, call `kb.resolve(&[query], &config)`
5. Assert on `solutions.len()`, `subst.resolve_with_term(var)`, `kb.reify(var, &subst)`

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
