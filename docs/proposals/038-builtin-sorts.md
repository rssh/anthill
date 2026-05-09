# Proposal 038 — Builtin sorts: spec satisfaction without namespace shadowing

## Status

Draft. Filed alongside WI-213. Driver is WI-210 phase 3 (spec/impl call-site dispatch); the issue surfaced when stdlib's namespace-level `fact Numeric[Int]` failed deterministic candidate matching.

## Problem

Anthill has five primitive sorts — `Int`, `Float`, `String`, `Bool`, `BigInt` — registered as global builtin symbols (`PRELUDE_SORTS` in `rustland/anthill-core/src/kb/load.rs:853`):

```rust
pub const PRELUDE_SORTS: &[&str] = &["Int", "BigInt", "Float", "String", "Bool"];
```

These sorts have:
- A `Symbol(...)` with `SymbolKind::Sort` registered at global scope.
- A runtime carrier (Rust's `i64`, `f64`, `String`, `bool`, etc.).
- **No declarative body**. There is no place inside the language where one can say "Int satisfies Eq" and have it land "on the sort `Int`."

### How stdlib works around it today

Stdlib parks satisfaction declarations in a *namespace* whose name shadows the builtin sort:

```anthill
namespace anthill.prelude.Int       -- a Namespace, NOT the sort
  ...
  fact Eq[Int]                      -- intent: "Int satisfies Eq"
  fact Ordered[Int]
  fact Numeric[Int]
end
```

Two semantic problems flow from this:

1. **Sort body is missing.** Operations declared inside the namespace (`abs`, `neg`, …) belong to the namespace, not to the sort `Int`. Tools that walk a sort's operations (codegen, reflection, dispatch) can't find them via `Int` and have to know about the parallel namespace.

2. **Name resolution shadowing.** Inside `namespace anthill.prelude.Int`, the bare identifier `Int` resolves to the *namespace* symbol (`anthill.prelude.Int`), not to the *builtin sort* symbol (`Int`). So `fact Eq[Int]` records the binding value as the namespace, not as the sort. Anything matching that fact against the actual builtin `Int` symbol — including WI-210's dispatch, proof-record specialization, codegen carrier resolution — sees a mismatch:

   ```
   per-call binding:    Int                           (the builtin sort)
   candidate binding:   anthill.prelude.Int           (the namespace)
                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                        same short name, different Symbol value
   ```

WI-210 phase 3's deterministic dispatch surfaces this directly: `add(x, x)` for `x : Int` fails to find an `Int → Numeric` impl candidate because the candidate's binding value is `anthill.prelude.Int`, not `Int`.

### Why it matters beyond WI-210

The shadowing problem is local to primitive sorts today, but the same shape recurs anywhere a sort has no place to host its own satisfaction declarations. Future "external sorts" — sorts whose carrier is a foreign-language object (Rust struct, C++ class, file handle) — have the identical issue: they need a body where facts can live, not a namespace doppelgänger.

## Design constraint: no new keywords

The design below stays within the existing kernel-language vocabulary (`sort`, `entity`, `fact`, `provides`, `import`, `meta`, …). No new syntactic primitives.

## Design

Anthill already has a cross-language realization mechanism (`stdlib/anthill/realization/realization.anthill` defines `Implementation`, `CarrierBinding`, `NamespaceMapping`). Use it to bind anthill-level sort declarations to host artifacts — but **split the declaration across files** so the language-agnostic spec lives separately from each host's binding.

### Layered file structure

```
stdlib/anthill/prelude/int.anthill            -- language-agnostic spec
    sort Int = ?                              -- pure abstract declaration
    operation abs(a: Int) -> Int              -- abstract ops; no body
    operation minValue() -> Int
    operation maxValue() -> Int
    -- ... etc

rustland/anthill-stl/anthill/int.anthill      -- Rust host binding
    provides Int language rust
      artifact "rustland/anthill-stl/src/prelude/int.rs"
      carrier Int = "i64"
      fact Eq[T = Int]
      fact Ordered[T = Int]
      fact Numeric[T = Int]
    end

scaland/anthill-stl/anthill/int.anthill       -- Scala host binding
    provides Int language scala
      artifact "scaland/.../scala/Int.scala"
      carrier Int = "scala.Long"
      fact Eq[T = Int]
      fact Ordered[T = Int]
      fact Numeric[T = Int]
    end

cppland/.../anthill/int.anthill               -- C++ host binding (future)
    provides Int language cpp
      carrier Int = "int64_t"
      fact Eq[T = Int]
      ...
    end
```

### Why split across files

This separation is **not optional** — anthill has multiple languages with their own interpreters (rustland's eval, scaland's eval, a future C++ runtime). Each interpreter is a distinct host with its own:
- runtime carrier (`i64` / `scala.Long` / `int64_t`),
- builtin registry (the actual code that runs `add(Int, Int)` at execution time),
- type-system mapping (codegen renders `Int` as the host carrier).

Co-locating Rust's `i64` binding inside `stdlib/anthill/prelude/int.anthill` would force every implementation to take a stdlib dependency on Rust-specific bindings (and vice-versa for Scala). The natural boundary is: **stdlib owns the spec, each implementation owns its binding file.** The build system (cargo/sbt) loads stdlib + the implementation's binding files; the interpreter sees one consistent picture per host.

### Semantics

- **Pure-anthill spec** (`stdlib/`): `sort Int = ?` is an abstract sort. The KB knows the name, the type parameters (none for primitives), and any abstract operation declarations. No bodies, no carrier.
- **Host binding** (per-implementation): the `provides Int language rust { … }` block (the existing `provides_block` form for `language ≠ anthill`) emits an `Implementation` fact recording the carrier (`i64`), artifact path, and the satisfaction facts that hold for the carrier. The same block is consumed by:
  - Codegen — renders `Int` as `i64` when emitting Rust source.
  - The interpreter — at startup, walks `Implementation` facts for its own language tag, registers carrier handlers and builtin tags.
  - WI-210 dispatch — sees the `SortProvidesInfo` records emitted from the satisfaction facts inside the block, keyed on the `Int` sort symbol (the abstract sort, not a namespace doppelgänger).
- **Multi-host coexistence**: a project that targets multiple languages loads multiple binding files; each contributes its own `Implementation` fact tagged with its `language`. The interpreter at runtime selects only its own language's facts (via a `language: "rust"` filter on the Project fact, or an equivalent runtime-time selector).

### Open questions

- **Loader change**: `load_provides_block` (load.rs:4943) currently only recurses into inner items for `language anthill`; for other languages it stubs out. Step 1 is to wire up satisfaction-fact emission inside non-anthill `provides` blocks — items inside should emit `SortProvidesInfo` tied to the spec sort, regardless of the host language.
- **Implementation entity**: has `carrier: List[CarrierBinding]`, `target: String`, `artifact: String` — we lean on this for the type→host-type mapping. The satisfaction facts emitted inside the block are *additional* SortProvidesInfo records, not new fields on Implementation.
- **Interpreter selection**: the runtime (rustland's eval) needs to know which language tag's `Implementation` facts to consume. Conventionally `language: "rust"` for rustland; configurable via the Project fact's `language` field (already present in `anthill-todo/project.anthill`).
- **Pure-anthill bindings**: for sorts where the runtime is anthill itself (no host), the spec stays in stdlib without a `provides … language rust` companion. Spec satisfaction facts go directly inside the sort body (Phase 1 sort-body path), as proposal 036 does for `WorkItemStore`/`FileBasedWorkitemStore`.

### Migration scope

~5 stdlib files (`Int`, `Float`, `String`, `Bool`, `BigInt`) get stripped down to pure-anthill specs (`sort Int = ?` plus abstract operation declarations). Each implementation directory (`rustland/`, `scaland/`, future `cppland/`) gets ~5 new files in `<lang>land/anthill-stl/anthill/` carrying the per-language `provides Int language X { … }` blocks. Plus wiring in the loader's `provides_block` path to consume non-anthill bodies (today they're stubbed for `language ≠ anthill`).

## Out of scope

- Plugin-supplied sorts (third-party FFI carriers). Same shape; land after stdlib migration.
- Variance annotations on type parameters (separate proposal).
- Renaming `anthill.prelude.Int` namespace to avoid shadowing (mechanically falls out once the sort declaration is hoisted to its proper home).

## Acceptance

When this proposal lands:

1. Builtin sorts (`Int`, `Float`, `String`, `Bool`, `BigInt`) have pure-anthill specs in stdlib and per-language binding files in each implementation directory; satisfaction facts inside those binding blocks emit `SortProvidesInfo` with `sort_ref` resolving to the builtin sort symbol (not a namespace doppelgänger).
2. WI-210 phase 3 dispatch hook is re-wired in `kb/typing.rs::check_apply`; the parked dispatch tests (`Unique` / `NoMatch` / `Ambiguous`) pass.
3. `add(x, x)` for `x : Int` type-checks via Int's spec satisfaction (no `WI-210 dispatch failed: no impl of anthill.prelude.Numeric.add` error).
4. `cargo test` green across `anthill-core`, `anthill-todo`.
5. Codegen continues to render `Int` as `i64` (carrier table unchanged in observable output).
