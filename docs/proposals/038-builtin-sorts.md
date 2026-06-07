# Proposal 038 — Builtin sorts: spec satisfaction without namespace shadowing

## Status

Draft. Driver is WI-210 phase 3 (spec/impl call-site dispatch); the issue surfaced when stdlib's namespace-level `fact Numeric[Int64]` failed deterministic candidate matching.

## Problem

Anthill has five primitive sorts — `Int64`, `Float`, `String`, `Bool`, `BigInt` — registered as global builtin symbols (`PRELUDE_SORTS` in `rustland/anthill-core/src/kb/load.rs:853`):

```rust
pub const PRELUDE_SORTS: &[&str] = &["Int64", "BigInt", "Float", "String", "Bool"];
```

These sorts have:
- A `Symbol(...)` with `SymbolKind::Sort` registered at global scope.
- A runtime carrier (Rust's `i64`, `f64`, `String`, `bool`, etc.).
- **No declarative body**. There is no place inside the language where one can say "Int64 satisfies Eq" and have it land "on the sort `Int64`."

### How stdlib works around it today

Stdlib parks satisfaction declarations in a *namespace* whose name shadows the builtin sort:

```anthill
namespace anthill.prelude.Int64       -- a Namespace, NOT the sort
  ...
  fact Eq[Int64]                      -- intent: "Int64 satisfies Eq"
  fact Ordered[Int64]
  fact Numeric[Int64]
end
```

Two semantic problems flow from this:

1. **Sort body is missing.** Operations declared inside the namespace (`abs`, `neg`, …) belong to the namespace, not to the sort `Int64`. Tools that walk a sort's operations (codegen, reflection, dispatch) can't find them via `Int64` and have to know about the parallel namespace.

2. **Name resolution shadowing.** Inside `namespace anthill.prelude.Int64`, the bare identifier `Int64` resolves to the *namespace* symbol (`anthill.prelude.Int64`), not to the *builtin sort* symbol (`Int64`). So `fact Eq[Int64]` records the binding value as the namespace, not as the sort. Anything matching that fact against the actual builtin `Int64` symbol — including WI-210's dispatch, proof-record specialization, codegen carrier resolution — sees a mismatch:

   ```
   per-call binding:    Int64                           (the builtin sort)
   candidate binding:   anthill.prelude.Int64           (the namespace)
                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                        same short name, different Symbol value
   ```

WI-210 phase 3's deterministic dispatch surfaces this directly: `add(x, x)` for `x : Int64` fails to find an `Int64 → Numeric` impl candidate because the candidate's binding value is `anthill.prelude.Int64`, not `Int64`.

### Why it matters beyond WI-210

The shadowing problem is local to primitive sorts today, but the same shape recurs anywhere a sort has no place to host its own satisfaction declarations. Future "external sorts" — sorts whose carrier is a foreign-language object (Rust struct, C++ class, file handle) — have the identical issue: they need a body where facts can live, not a namespace doppelgänger.

## Design constraint: no new keywords

The design below stays within the existing kernel-language vocabulary (`sort`, `entity`, `fact`, `provides`, `import`, `meta`, …). No new syntactic primitives.

## Design

Anthill already has a cross-language realization mechanism (`stdlib/anthill/realization/realization.anthill` defines `Implementation`, `CarrierBinding`, `NamespaceMapping`). Use it to bind anthill-level sort declarations to host artifacts — but **split the declaration across files** so the language-agnostic spec lives separately from each host's binding.

### Layered file structure

```
stdlib/anthill/prelude/int.anthill            -- language-agnostic spec
    sort Int64 = ?                              -- pure abstract declaration
    operation abs(a: Int64) -> Int64              -- abstract ops; no body
    operation minValue() -> Int64
    operation maxValue() -> Int64
    -- ... etc

rustland/anthill-stl/anthill/int.anthill      -- Rust host binding
    provides Int64 language rust
      artifact "rustland/anthill-stl/src/prelude/int.rs"
      carrier Int64 = "i64"
      fact Eq[T = Int64]
      fact Ordered[T = Int64]
      fact Numeric[T = Int64]
    end

scaland/anthill-stl/anthill/int.anthill       -- Scala host binding
    provides Int64 language scala
      artifact "scaland/.../scala/Int64.scala"
      carrier Int64 = "scala.Long"
      fact Eq[T = Int64]
      fact Ordered[T = Int64]
      fact Numeric[T = Int64]
    end

cppland/.../anthill/int.anthill               -- C++ host binding (future)
    provides Int64 language cpp
      carrier Int64 = "int64_t"
      fact Eq[T = Int64]
      ...
    end
```

### Why split across files

This separation is **not optional** — anthill has multiple languages with their own interpreters (rustland's eval, scaland's eval, a future C++ runtime). Each interpreter is a distinct host with its own:
- runtime carrier (`i64` / `scala.Long` / `int64_t`),
- builtin registry (the actual code that runs `add(Int64, Int64)` at execution time),
- type-system mapping (codegen renders `Int64` as the host carrier).

Co-locating Rust's `i64` binding inside `stdlib/anthill/prelude/int.anthill` would force every implementation to take a stdlib dependency on Rust-specific bindings (and vice-versa for Scala). The natural boundary is: **stdlib owns the spec, each implementation owns its binding file.** The build system (cargo/sbt) loads stdlib + the implementation's binding files; the interpreter sees one consistent picture per host.

### Semantics

- **Pure-anthill spec** (`stdlib/`): `sort Int64 = ?` is an abstract sort. The KB knows the name, the type parameters (none for primitives), and any abstract operation declarations. No bodies, no carrier.
- **Host binding** (per-implementation): the `provides Int64 language rust { … }` block (the existing `provides_block` form for `language ≠ anthill`) emits an `Implementation` fact recording the carrier (`i64`), artifact path, and the satisfaction facts that hold for the carrier. The same block is consumed by:
  - Codegen — renders `Int64` as `i64` when emitting Rust source.
  - The interpreter — at startup, walks `Implementation` facts for its own language tag, registers carrier handlers and builtin tags.
  - WI-210 dispatch — sees the `SortProvidesInfo` records emitted from the satisfaction facts inside the block, keyed on the `Int64` sort symbol (the abstract sort, not a namespace doppelgänger).
- **Multi-host coexistence**: a project that targets multiple languages loads multiple binding files; each contributes its own `Implementation` fact tagged with its `language`. The interpreter at runtime selects only its own language's facts (via a `language: "rust"` filter on the Project fact, or an equivalent runtime-time selector).

### Loader changes

`load_provides_block` (load.rs:4943) currently has an early return for non-`anthill` languages:

```rust
fn load_provides_block(&mut self, pb: &ProvidesBlock, domain: TermId) {
    if self.parsed.symbols.name(pb.language) != "anthill" { return; }   // <— stubs out everything else
    for item in &pb.items {
        match item { … }   // recurses for anthill only
    }
}
```

Two concrete steps:

1. **Remove the early return; recurse into items for any language.** Items inside the block (`Fact`, `Rule`, `Proof`, `RuleBlock`) are loaded the same way they would be at namespace level. A `fact Eq[T = Int64]` inside `provides Int64 language rust { … }` emits the regular fact AND triggers Phase 1's `SortProvidesInfo` auto-emit (sort-body path: `current_scope` during the recursion is the binding's spec sort, derived from the block's outer name). "Int64 satisfies Eq" is a true anthill-spec-level statement regardless of host; only the carrier differs.

2. **Emit one `Implementation` fact per block** (host-binding metadata). The block's `carrier`, `artifact`, `profile` clauses populate the `Implementation` entity (already defined in `stdlib/anthill/realization/realization.anthill`):

   ```anthill
   fact Implementation(
     target      : "anthill.prelude.Int64",
     artifact    : "rustland/anthill-stl/src/prelude/int.rs",
     language    : "rust",
     profile     : some("std"),
     description : none,
     carrier     : [CarrierBinding(sort_name: "Int64", host_type: "i64")],
     namespace_map : []
   )
   ```

   Codegen/interpreter consume `Implementation` by `(language, profile)` filter; WI-210 dispatch consumes the host-agnostic `SortProvidesInfo` records emitted in step 1.

The `provides_block` already supports `Artifact`, `Carrier`, `NamespaceMap` items (`ProvidesItem::Artifact`, etc.) — they currently feed into nothing for non-anthill blocks. The proposal also wires those through to the Implementation fact's fields.

### Open questions

- **Implementation entity**: has `carrier: List[CarrierBinding]`, `target: String`, `artifact: String`, `profile: Option[T = String]` — we lean on this for the type→host-type mapping. The satisfaction facts emitted inside the block are *additional* SortProvidesInfo records, not new fields on Implementation.
- **Interpreter selection (via profile)**: each runtime — rustland's eval, scaland's eval, future C++/Lua interpreters — has different needs from the same host language. A standalone-codegen build wants the production carrier and `[std]` profile; an embedded interpreter loaded into a hosting application wants smaller dependencies and possibly different carriers; a bootstrap stage may strip everything else.

  Use the existing `profile: Option[T = String]` field on `Implementation` (and `LanguageMapping`) for this. Conventional profile names:
  - `"embedded-interpreter"` — bindings for use when the host language is hosting the anthill interpreter.
  - `"bootstrap-interpreter"` — minimal initial set for stage0 / bootstrap.
  - `"std"` (default) — standard production codegen / runtime.

  ```anthill
  -- rustland/anthill-stl/anthill/int.anthill
  provides Int64 language rust
    profile "std"
    carrier Int64 = "i64"
    fact Eq[T = Int64]
    fact Ordered[T = Int64]
    fact Numeric[T = Int64]
  end

  provides Int64 language rust
    profile "embedded-interpreter"
    carrier Int64 = "i64"
    -- typically same carrier; embedded-interpreter profile may
    -- elide some provider-side helpers or pull a different builtin
    -- registration set.
    fact Eq[T = Int64]
    fact Ordered[T = Int64]
    fact Numeric[T = Int64]
  end
  ```

  Each interpreter at startup filters `Implementation` facts by `language = <its host>` AND `profile = <its mode>` (e.g., rustland's eval consumes `language = "rust", profile = "embedded-interpreter"`). The Project fact's `language`/`profile` fields select the production-vs-embedded mode at build time.

- **Pure-anthill bindings**: for sorts where the runtime is anthill itself (no host), the spec stays in stdlib without a `provides … language rust` companion. Spec satisfaction facts go directly inside the sort body (Phase 1 sort-body path), as proposal 036 does for `WorkItemStore`/`FileBasedWorkitemStore`.

### Migration scope

~5 stdlib files (`Int64`, `Float`, `String`, `Bool`, `BigInt`) get stripped down to pure-anthill specs (`sort Int64 = ?` plus abstract operation declarations). Each implementation directory (`rustland/`, `scaland/`, future `cppland/`) gets ~5 new files in `<lang>land/anthill-stl/anthill/` carrying the per-language `provides Int64 language X { … }` blocks. Plus wiring in the loader's `provides_block` path to consume non-anthill bodies (today they're stubbed for `language ≠ anthill`).

## Out of scope

- Plugin-supplied sorts (third-party FFI carriers). Same shape; land after stdlib migration.
- Variance annotations on type parameters (separate proposal).
- Renaming `anthill.prelude.Int64` namespace to avoid shadowing (mechanically falls out once the sort declaration is hoisted to its proper home).

## Acceptance

When this proposal lands:

1. Builtin sorts (`Int64`, `Float`, `String`, `Bool`, `BigInt`) have pure-anthill specs in stdlib and per-language binding files in each implementation directory; satisfaction facts inside those binding blocks emit `SortProvidesInfo` with `sort_ref` resolving to the builtin sort symbol (not a namespace doppelgänger).
2. WI-210 phase 3 dispatch hook is re-wired in `kb/typing.rs::check_apply`; the parked dispatch tests (`Unique` / `NoMatch` / `Ambiguous`) pass.
3. `add(x, x)` for `x : Int64` type-checks via Int64's spec satisfaction (no `WI-210 dispatch failed: no impl of anthill.prelude.Numeric.add` error).
4. `cargo test` green across `anthill-core`, `anthill-todo`.
5. Codegen continues to render `Int64` as `i64` (carrier table unchanged in observable output).
