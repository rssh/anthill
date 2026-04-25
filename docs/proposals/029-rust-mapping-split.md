# 029: Split Rust mapper by direction-of-truth

## Status: Draft

## Depends on: `docs/rust-forward-mapping.md` (the mapping specification)

## Relates to: kernel spec §8.5, §8.7 (`Implementation` facts); WI tickets for full-mapper and backward-recognizer work

## Motivation

The current Rust mapper (`rustland/anthill-core/src/codegen/rust.rs`) walks the parse IR (`ParsedFile`) and emits Rust skeletons syntactically. It exists to bootstrap the kernel — generating the Rust bindings the stdlib needs so the kernel can build itself. It is deliberately KB-free.

As the language matures, three distinct use-cases pull in different directions:

1. **anthill is source of truth, generate Rust.** Writing a spec in anthill and emitting a Rust trait/impl (skeleton or full implementation translation). Needs `TermId`-level resolution and fact-driven decisions: `Implementation` / `NamespaceMapping` / `CarrierBinding` (kernel spec §8.5, §8.7) determine crate paths, carriers, profiles, derive macros.
2. **Rust is source of truth, generate anthill.** Lifting an existing Rust trait (with proof annotations carried as Rust attributes) into an anthill sort, so proofs can be discharged against the anthill KB. The anthill side is *derived*; the Rust attributes stay where they are.
3. **Bidirectional integration.** Some modules are anthill-authored, others Rust-authored, both meet at an integration boundary. This is not a third tool — it is the *workflow* of running (1) and (2) over a shared KB and resolving the seam with `Implementation` / `NamespaceMapping` facts.

A single mapper cannot serve (1) and (2): they have different inputs, different outputs, and different sources of authority. They also need to be separable from the bootstrap mapper, which has a fourth, narrower use-case:

4. **Bootstrap.** Generate Rust bindings for the stdlib so the kernel can build. Runs without a KB. This is a self-build concern, not a user-facing tool.

Non-goals: defining new mapping rules, changing `docs/rust-forward-mapping.md`, supporting other host languages (Scala, SMT-LIB have their own mappings).

## Architecture

Three crates, by direction-of-truth, plus the existing bootstrap path inside `anthill-core`.

### Shared specification

`docs/rust-forward-mapping.md` is the single source of truth for what anthill ↔ Rust looks like. All implementations conform to subsets of these rules. The document describes the input/output relation, not how rules are executed.

### Bootstrap path (existing, stays in `anthill-core`)

- **Use-case**: (4) — generate Rust bindings for stdlib during the kernel's own build.
- **Input**: `ParsedFile` (parse IR), no KB.
- **Implementation**: direct `match` over parse nodes. Syntactic rules only.
- **Location**: stays in `anthill-core`. Current `rustland/anthill-core/src/codegen/rust.rs` is the implementation; may be reorganized into a submodule (`codegen/rust/bootstrap.rs`) but no new crate is created for it. Keeping it inside `anthill-core` avoids a build cycle and reflects the truth that bootstrap is part of the kernel's self-build.
- **Surface**: exposed as the `bootstrap-codegen` subcommand of the `anthill-core`-owned CLI binary (the same binary that drives kernel self-build). Library API stays as well, for callers that need it programmatically.
- **Dependencies**: `anthill-core` only. No `anthill-stl`, no loaded KB.
- **Scope**: the subset of anthill whose Rust mapping is determined by syntax alone — exactly what is needed to generate stdlib bindings. Not a general-purpose tool. No `Implementation`/`NamespaceMapping` consumption. No macro-aware output.
- **Frozen**: changes only when the stdlib needs a new construct. Not a place to add features.

### `anthill-rust-gen` (new crate) — anthill → rust

- **Use-case**: (1) — anthill is source of truth, generate Rust (interface, implementation, or full translation).
- **Input**: loaded `KnowledgeBase`.
- **Implementation**: walks KB entries, resolves `TermId`s, queries fact indexes. Uses `Implementation` / `NamespaceMapping` / `CarrierBinding` to pick crate paths, carriers, and profiles. Can emit macro-using Rust (e.g. `#[derive(...)]` driven by `fact Eq{T = ...}`).
- **Location**: new crate `rustland/anthill-rust-gen/`.
- **Dependencies**: `anthill-core` (KB types, term store, symbol table) and `anthill-stl` (for the stdlib sorts it must recognize: `Implementation`, `NamespaceMapping`, `CarrierBinding`, `Eq`, `Ordered`, persistence and reflect sorts). `anthill-core` stays free of stdlib-specific knowledge; that knowledge lives here.
- **Scope**: full `docs/rust-forward-mapping.md`.

### `rust-anthill-gen` (new crate workspace) — rust → anthill

- **Use-case**: (2) — Rust is source of truth, generate anthill.
- **Model**: inventory-based, modeled on `lantr-io/rustus`. The user annotates Rust items with proc-macro attributes; macros expand into `inventory::submit!` calls that register builder closures. At runtime, the user's binary calls an emitter that iterates the inventory, runs the builders in passes, and produces `.anthill` text. **No external Rust-source parser, no `cargo expand`, no `syn`-driven extraction tool.** The user's normal Rust compile is what reads the annotations.
- **Workspace layout** (mirrors rustus's `rustus-macros` / `rustus-core` / `rustus-prelude` split):
  - `rustland/anthill-rust-derive/` — proc-macro crate. Defines:
    - `#[anthill::sort]` on traits / structs / enums
    - `#[anthill::operation]` on trait methods or free functions
    - `#[anthill::effect(Modify, Error, ...)]` on operations
    - `#[anthill::impl_of("qualified.anthill.Sort")]` linking a Rust impl to an existing anthill sort
    - `#[anthill::law("name")]` on test/property functions, lifted into anthill `rule` proof obligations
    - `#[anthill(name = "qualified.anthill.name")]` overrides for explicit naming
    - Each macro expands into an `inventory::submit! { AnthillEntry { ... } }` registration plus any helper trait impls needed at runtime (analog of rustus's `sir_eq` / `sir_data_decl` methods).
  - `rustland/anthill-rust-export/` — runtime crate. Defines `AnthillEntry`, `inventory::collect!`, `AnthillBuildContext`, and a `build_anthill_files(crate_name) -> Vec<AnthillFile>` / `dump_to(path)` API. Two passes: declare sorts/entities, then emit operations and `Implementation` facts.
  - `rustland/anthill-rust-prelude/` — pre-registered mappings for primitives and stdlib traits: `i64` → `Int`, `String` → `String`, `Vec<T>` → `List[T = ...]`, `PartialEq` → `anthill.prelude.Eq`, `PartialOrd` → `anthill.prelude.Ordered`, etc. Users do not re-annotate these.
  - `rustland/rust-anthill-gen/` — facade crate that re-exports the three above (parallel to the top-level `rustus` crate). `use rust_anthill_gen::prelude::*;` brings the macros and runtime in.
- **Dependencies**: `anthill-core` and `anthill-stl` are *optional* runtime deps used only by the validator pass below. The minimum-viable export pipeline runs with just `inventory` and a small string-emitter — no KB needed.
- **KB validation (optional)**: a separate validator routine, called explicitly, loads a KB from `anthill-stl` and checks every `impl_of` annotation against the loaded KB (right sort exists, signature matches, effects compatible). Failures surface as build-time errors when the user wires the validator into their `build.rs` or test suite. Without the validator, the export proceeds optimistically and emits `Implementation` facts that may later fail to validate when loaded into a KB.
- **Naming convention**: `<source>-<target>-gen`. Source of truth comes first. Scales to other targets: `anthill-scala-gen`, `scala-anthill-gen`, `anthill-smt-gen`.

### Bidirectional workflow (not a crate)

Use-case (3) is a *workflow*, not a separate tool. The anthill-authored modules are emitted as Rust by `anthill-rust-gen`; the Rust-authored modules carry `anthill-rust-derive` annotations and are exported as `.anthill` by `anthill-rust-export`. Both halves populate a shared KB; `Implementation` and `NamespaceMapping` facts at the seam wire them together. The annotation conventions in `anthill-rust-derive` (qualified names via `#[anthill(name = "...")]`, sort linking via `#[anthill::impl_of(...)]`) make a single Rust crate self-describing in both directions: it can be the target of forward codegen and the source of backward export simultaneously, with annotations naming the same anthill identifiers in both roles. The "tool" for orchestration is composition, not new logic — a CLI subcommand may eventually wrap it.

## Naming summary

| Crate                                   | Direction         | Source of truth | KB needed?                |
|-----------------------------------------|-------------------|-----------------|---------------------------|
| `anthill-core` (bootstrap)              | anthill → rust    | anthill stdlib  | no                        |
| `anthill-rust-gen`                      | anthill → rust    | anthill         | yes                       |
| `rust-anthill-gen` (facade)             | rust → anthill    | rust            | optional (validator only) |
| ↳ `anthill-rust-derive` (proc macros)   | rust → anthill    | rust            | no                        |
| ↳ `anthill-rust-export` (runtime)       | rust → anthill    | rust            | no                        |
| ↳ `anthill-rust-prelude` (mappings)     | rust → anthill    | rust            | no                        |

## What changes, concretely

1. Keep bootstrap codegen in `anthill-core`. Optionally rename `anthill-core/src/codegen/rust.rs` → `anthill-core/src/codegen/rust/bootstrap.rs` for clarity; public re-exports stay so existing callers do not change.
2. Expose bootstrap codegen as a `bootstrap-codegen` subcommand of the `anthill-core`-owned CLI. Library entry point remains for in-process callers.
3. Create new crate `rustland/anthill-rust-gen/` for use-case (1). Depends on `anthill-core` and `anthill-stl`.
4. Create the rust → anthill workspace (use-case (2)) modeled on `lantr-io/rustus`:
   - `rustland/anthill-rust-derive/` — proc-macro crate (`#[anthill::sort]`, `#[anthill::operation]`, `#[anthill::impl_of(...)]`, etc.).
   - `rustland/anthill-rust-export/` — runtime crate with `inventory`-based registry and `dump_to(path)` API.
   - `rustland/anthill-rust-prelude/` — pre-registered mappings for Rust primitives and stdlib traits.
   - `rustland/rust-anthill-gen/` — facade crate re-exporting the above.
   None of these depend on a Rust-source parser. They depend on `inventory`. `anthill-core` / `anthill-stl` enter only via the optional validator pass.
5. No conformance test between bootstrap and `anthill-rust-gen`. They serve different use-cases (stdlib bindings vs. general codegen) and need not produce identical output. If a narrower cross-check is wanted later — e.g. that `anthill-rust-gen` on the stdlib produces output equivalent to bootstrap modulo KB-required additions — that can be added once both exist; not required by this proposal.

## Migration

- Bootstrap remains the only mapper used by the kernel's own build. No consumer change.
- `anthill-rust-gen` is built incrementally; new use-cases (agent workflows, user-invoked codegen) target it from day one rather than extending bootstrap.
- `rust-anthill-gen` is started after `anthill-rust-gen` is far enough along to define what "a recognized Rust item" looks like — a follow-up proposal will fix its API.

## Open questions

- The full annotation surface for `anthill-rust-derive`. Starting set: `#[anthill::sort]`, `#[anthill::operation]`, `#[anthill::effect(...)]`, `#[anthill::impl_of(...)]`, `#[anthill::law(...)]`, `#[anthill(name = "...")]`. Whether operation-level annotations are required vs. derived from the surrounding `#[anthill::sort]` trait — needs design work alongside the first real use-case.
- Whether the validator pass runs by default (e.g. emitted `.anthill` files always include a `// validated against KB <hash>` header) or strictly opt-in. Default-on is safer; default-off keeps the export pipeline KB-free for users who only ever consume the emitted files later.
- Should `anthill-rust-gen` emit a structured IR (e.g. `syn::File`) that is then pretty-printed, or emit strings directly as bootstrap does? An IR is attractive for round-tripping with `anthill-rust-export` (compare both directions in the same IR) but is not required for forward codegen.
- How are profiles (`no_std` vs `std`, etc.) selected at the CLI level? Deferred to whichever proposal wires `anthill-rust-gen` into `anthill` CLI subcommands.
