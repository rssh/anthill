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
| `intern.rs` | `SymbolTable`: string interning (`Symbol(u32)`), scope-aware resolution |
| `parse/convert.rs` | Tree-sitter CST → typed IR (`ParsedFile`) |
| `parse/ir.rs` | Parse IR types: `Item`, `ParsedFile`, `SimpleTermStore` |
| `kb/term.rs` | `Term`, `TermId`, `TermStore` (hash-consed), `Var` enum |
| `kb/mod.rs` | `KnowledgeBase`: indexes, `assert_fact`, `assert_rule_debruijn`, `with_fresh_vars` |
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
4. Only query-var linkages go into `answer_links` (not synthetic fresh→concrete bindings, to avoid O(n²) `bind_compressed`)

## Test Patterns

Integration tests in `anthill-core/tests/` follow:
1. Load stdlib via `common::collect_anthill_files(&common::stdlib_dir())`
2. Parse + `register_prelude` + `register_standard_builtins` + `load_all`
3. Build query term, call `kb.resolve(&[query], &config)`
4. Assert on `solutions.len()`, `subst.resolve_with_term(var)`, `kb.reify(var, &subst)`

## Conventions

- `SmallVec<[T; N]>` for term args. Use `from_elem` for single, `from_slice` for multiple (requires `Copy`).
- Named args always sorted by field name for canonical ordering.
- `assert_rule_debruijn` for rules (converts vars), `assert_fact` for ground facts (arity 0).
- `FnArg` is `Copy` (both `TermId` and `Symbol` are `Copy`).
