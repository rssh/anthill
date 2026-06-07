# 034: Split Scala mapper by direction-of-truth

## Status: Draft

## Depends on: `docs/scala-forward-mapping.md` (the mapping specification — written alongside this proposal)

## Mirrors: [029-rust-mapping-split.md](029-rust-mapping-split.md)

## Relates to: kernel spec §8.5, §8.7 (`Implementation` facts); WI tickets for the scaland resync stack

## Motivation

Same shape as 029: as scaland matures, four distinct use-cases pull a mapper in different directions, and a single tool cannot serve them all. Recap:

1. **anthill is source of truth, generate Scala.** Spec → Scala traits / case classes / methods. Needs KB-level resolution and fact-driven decisions.
2. **Scala is source of truth, generate anthill.** Lift an existing Scala trait (with proof annotations) into an anthill sort.
3. **Bidirectional integration.** Workflow over a shared KB; not a separate tool.
4. **Bootstrap.** Generate Scala bindings for the stdlib so scaland can build itself. Runs without a KB.

This proposal adapts 029's three-crate split to the Scala / sbt ecosystem.

Non-goals: defining new mapping rules (those live in `docs/scala-forward-mapping.md`), supporting other host languages (Rust / SMT-LIB / C++ have their own).

## Architecture

Three sbt subprojects, by direction-of-truth, plus the existing bootstrap path inside `scaland/core`.

### Shared specification

`docs/scala-forward-mapping.md` is the single source of truth for what anthill ↔ Scala looks like. All implementations conform to subsets of these rules.

### Bootstrap path (existing-or-future, stays in `scaland/core`)

- **Use-case**: (4) — generate Scala bindings for stdlib during scaland's own build.
- **Input**: `ParsedFile` (parse IR), no KB.
- **Implementation**: direct `match` over parse nodes. Syntactic rules only.
- **Location**: `scaland/core/src/main/scala/anthill/codegen/scala/bootstrap.scala` (mirrors `rustland/anthill-core/src/codegen/rust/bootstrap.rs`). Currently does not exist — scaland is parser+loader+lightweight-resolver only; bootstrap codegen lands when scaland needs to emit Scala bindings (i.e. when there's a real consumer).
- **Surface**: subcommand of the `scaland`-owned CLI (when one exists).
- **Dependencies**: `scaland-core` only. No loaded KB.
- **Scope**: subset of anthill whose Scala mapping is determined by syntax alone.
- **Frozen**: changes only when stdlib gains a new construct.

### `anthill-scala-gen` (new subproject) — anthill → scala

- **Use-case**: (1) — anthill is source of truth, generate Scala (interface, implementation, or full translation).
- **Input**: loaded `KnowledgeBase`.
- **Implementation**: walks KB entries, resolves `TermId`s, queries fact indexes. Uses `Implementation` / `NamespaceMapping` / `CarrierBinding` from the loaded KB plus `LanguageMapping(language: "scala", profile: ...)` from `stdlib/anthill/realization/scala_std.anthill`.
- **Location**: new sbt subproject `scaland/anthill-scala-gen/`.
- **Dependencies**: `scaland-core` + `scaland-stl` (parallel to rustland's `anthill-stl` — currently does not exist on the Scala side; created if/when needed).
- **Scope**: full `docs/scala-forward-mapping.md`.

### `scala-anthill-gen` (new sbt-workspace) — scala → anthill

- **Use-case**: (2) — Scala is source of truth, generate anthill.
- **Model**: Scala 3 `inline` macros + a runtime registry, parallel to rustland's `inventory`-based approach. The user annotates Scala items with type-class-derived markers; an `inline` macro records each in a global registry; an emitter walks the registry and produces `.anthill` text.
  - Scala has no exact analog of Rust's `inventory` crate (linker-section-based static registration). Equivalent approaches:
    - **Macro-derived registration**: each `@anthillSort` annotation triggers an `inline def` that registers via a typeclass instance into a `Registry` companion object. Registration is at class-load time (not link time). This is the v1 approach.
    - **scala-meta `Mirror` introspection** as a fallback for derivable cases (e.g. `case class` field discovery without explicit annotation).
- **Workspace layout** (parallel to `rustland/{anthill-rust-derive, anthill-rust-export, anthill-rust-prelude, rust-anthill-gen}`):
  - `scaland/anthill-scala-derive/` — Scala 3 macro subproject. Defines:
    - `@anthillSort` annotation on `trait` / `case class` / `enum`
    - `@anthillOperation` on methods or top-level functions
    - `@anthillEffect("Modify", "Error", ...)` on operations
    - `@anthillImplOf("qualified.anthill.Sort")` linking a Scala impl to an existing anthill sort
    - `@anthillLaw("name")` on test/property functions, lifted into anthill `rule` proof obligations
    - `@anthillName("qualified.anthill.name")` overrides for explicit naming
    - Each macro expands to a registry `submit` call.
  - `scaland/anthill-scala-export/` — runtime subproject. Defines `AnthillEntry`, `Registry`, `AnthillBuildContext`, and a `buildAnthillFiles(crateName: String): Seq[AnthillFile]` / `dumpTo(path: Path)` API. Two passes: declare sorts/entities, then emit operations and `Implementation` facts.
  - `scaland/anthill-scala-prelude/` — pre-registered mappings for primitives and Scala stdlib types: `Int64` → `Int64`, `String` → `String`, `List[T]` → `List[T = ...]`, `cats.Eq` → `anthill.prelude.Eq` (if cats is available; otherwise just `Object.equals`), `Ordering` → `anthill.prelude.Ordered`, etc. Users do not re-annotate these.
  - `scaland/scala-anthill-gen/` — facade subproject re-exporting the above.
- **Dependencies**: `scaland-core` + `scaland-stl` are *optional* runtime deps used only by the validator pass. The minimum-viable export pipeline runs with just the macro + a small string-emitter.
- **KB validation (optional)**: a separate validator routine, called explicitly, loads a KB and checks every `@anthillImplOf` annotation against the loaded KB (sort exists, signature matches, effects compatible). Failures surface as build-time errors when the user wires the validator into their `Test/test`. Without the validator, export proceeds optimistically.

### Bidirectional workflow (not a subproject)

Same as 029: use-case (3) is a workflow, not a separate tool. Anthill-authored modules emitted as Scala by `anthill-scala-gen`; Scala-authored modules carrying `anthill-scala-derive` annotations exported as `.anthill` by `anthill-scala-export`. Both halves populate a shared KB; `Implementation` and `NamespaceMapping` facts at the seam wire them together.

## Naming summary

| sbt subproject                                  | Direction         | Source of truth | KB needed?                |
|-------------------------------------------------|-------------------|-----------------|---------------------------|
| `scaland-core` (bootstrap)                      | anthill → scala   | anthill stdlib  | no                        |
| `anthill-scala-gen`                             | anthill → scala   | anthill         | yes                       |
| `scala-anthill-gen` (facade)                    | scala → anthill   | scala           | optional (validator only) |
| ↳ `anthill-scala-derive` (macros)               | scala → anthill   | scala           | no                        |
| ↳ `anthill-scala-export` (runtime)              | scala → anthill   | scala           | no                        |
| ↳ `anthill-scala-prelude` (mappings)            | scala → anthill   | scala           | no                        |

## What changes, concretely

1. Author `docs/scala-forward-mapping.md` (the mapping spec; landed alongside this proposal).
2. Author `stdlib/anthill/realization/scala_std.anthill` (the `LanguageMapping` facts; landed alongside this proposal).
3. Bootstrap codegen lands in `scaland/core/src/main/scala/anthill/codegen/scala/bootstrap.scala` when first needed. Not part of this proposal — gated on a real consumer.
4. Create new sbt subproject `scaland/anthill-scala-gen/` for use-case (1) when WI-156 (eval) lands and a real consumer surfaces.
5. Create the scala → anthill workspace (use-case (2)) modeled on `lantr-io/rustus`: `scaland/{anthill-scala-derive, anthill-scala-export, anthill-scala-prelude, scala-anthill-gen}/`. Started after `anthill-scala-gen` is far enough along to define what "a recognized Scala item" looks like — a follow-up proposal will fix its API.
6. No conformance test between bootstrap and `anthill-scala-gen` (same rationale as 029 §5).

## Migration

- Scaland today is parser+loader+lightweight-resolver only — no codegen. The bootstrap path can be added incrementally; no consumer to break.
- `anthill-scala-gen` and `scala-anthill-gen` are gated on real use-cases. Filing them as proposals up-front locks in the architecture so any future codegen work fits the same shape rustland adopted in 029.

## Open questions

- The full annotation surface for `anthill-scala-derive`. Starting set mirrors 029. Whether operation-level annotations are required vs. derived from the surrounding `@anthillSort` trait — needs design work alongside the first real use-case.
- Whether `inline` macro registration runs at compile time or class-load time. Compile-time is preferred (catches errors earlier) but requires a `using` context per registration; class-load time is simpler.
- Whether `anthill-scala-gen` emits a structured IR (e.g. `scala.meta.Tree`) that is then pretty-printed, or emits strings directly as bootstrap does. An IR is attractive for round-tripping with `anthill-scala-export`.
- How are profiles (`scala_std` vs `scala_zio` vs `scala_cats_effect`, etc.) selected at the CLI level? The Scala ecosystem has more "effect runtime" profiles than rust does — likely deferred to whichever proposal wires `anthill-scala-gen` into a CLI.
- Effect-system mapping for `Modify` and `Error`: Scala has more idiomatic choices than Rust (immutable update returning `(state, R)`, `Either[E, R]`, `cats.effect.IO`, `zio.ZIO`). The default `scala_std` profile picks one set; alternative profiles (`scala_cats_effect`, `scala_zio`) extend.
