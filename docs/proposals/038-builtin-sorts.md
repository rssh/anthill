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

The proposals below stay within the existing kernel-language vocabulary (`sort`, `entity`, `fact`, `provides`, `import`, `meta`, …). No new syntactic primitives.

## Two design directions

### (A) Meta annotation: `[builtin]` on a regular sort declaration

The `meta_block` syntax already lets users annotate any declaration with `[key: value, …]`. Use it to mark a sort as having a runtime-supplied carrier:

```anthill
namespace anthill.prelude
  sort Int [builtin]
    fact Eq[T = Int]
    fact Ordered[T = Int]
    fact Numeric[T = Int]

    operation minValue() -> Int
    operation maxValue() -> Int
    operation abs(a: Int) -> Int
    -- … etc
  end
end
```

Semantics:

- **Declarative form**: regular `sort Int { … }` block. Body holds the satisfaction facts and any operations whose runtime is supplied by the host. WI-210's Phase 1 auto-emit fires inside the body — `SortProvidesInfo(sort_ref = Int, spec = SortView(Eq, T = Int))` is recorded with `sort_ref = Int` (the builtin), which is exactly the symbol that dispatch matches against.
- **`[builtin]` meta**: tells the loader "this sort has no constructor entities; values come from the runtime." The loader skips checks that require constructors (induction rule emission, exhaustive-match validation, …) for sorts carrying this meta.
- **Backwards-compatible**: `PRELUDE_SORTS` registration is retained (so the sort exists at scan time before stdlib loads). Loading the `sort Int [builtin] { … }` block reuses the existing symbol (the loader already does this — load.rs:422 "Reuse existing sort symbol if already defined"), attaching the body items to it.
- **Namespace migration**: the existing `namespace anthill.prelude.Int { … }` becomes a `sort Int { … }` block (probably hoisted to the parent namespace `anthill.prelude` to avoid the same-name shadowing). Imports change from `import anthill.prelude.Int.{abs, neg}` to `import anthill.prelude.Int.{abs, neg}` (qualified-name resolution lands on the sort instead of the namespace — same surface syntax).

Open questions (A):

- Should the `[builtin]` meta also be available on *operation* declarations whose body is supplied by the host (today many operations have no body and are linked at codegen time — same idea, different scope)?
- Are there existing `[…]` meta keys whose semantics conflict with `[builtin]` (e.g. `[infix: "+"]` on operations)? The two should compose orthogonally.

### (B) Implementation clause: declare in stdlib, bind to host via `provides … language rust`

Anthill already has a cross-language realization mechanism (`stdlib/anthill/realization/realization.anthill` defines `Implementation`, `CarrierBinding`, `NamespaceMapping`). Use it to bind anthill-level sort declarations to host artifacts:

```anthill
namespace anthill.prelude
  -- Fully declared in anthill: signature is the spec, body is empty.
  sort Int = ?

  provides Int language rust
    artifact "rustland/anthill-stl/src/prelude/int_carrier.rs"
    carrier Int = "i64"
    fact Eq[T = Int]
    fact Ordered[T = Int]
    fact Numeric[T = Int]
    operation minValue() -> Int   -- body-less; codegen wires to Rust impl
    operation abs(a: Int) -> Int
  end
end
```

Semantics:

- **Pure-anthill spec**: `sort Int = ?` is an abstract sort. The KB knows nothing more than its name.
- **Host binding**: the `provides Int language rust { … }` block (the existing `provides_block` form for `language ≠ anthill`) emits an `Implementation` fact recording the carrier (`i64`), artifact path, and the satisfaction facts that hold for the carrier. Codegen consumes this to render `Int` as `i64` in Rust code; the runtime uses `i64` for values.
- **Satisfaction facts inside the provides block**: live inside the language-specific `provides` body, alongside the carrier binding. They emit `SortProvidesInfo` keyed on the `Int` sort symbol (the abstract sort, not a namespace) — same as (A) for dispatch matching.
- **No special-case `[builtin]` meta**: the only "builtin"-ness is the `language rust` (or `language cpp`, `scala`, …) tag on the `provides` block, which already exists for cross-language realization.

Open questions (B):

- The current `load_provides_block` (load.rs:4943) only recurses into inner items for `language anthill`; for other languages it stubs out. Step 1 of (B) is to wire up satisfaction-fact emission inside non-anthill `provides` blocks — items inside should still emit `SortProvidesInfo` tied to the spec sort.
- The `Implementation` reflect entity has `carrier: List[CarrierBinding]` — we'd lean on this for the type→host-type mapping.
- Hosts other than rust (cpp/scala/python/lua/proto): each language gets its own `provides Int language X { … }` block with its own carrier. Multiple language bindings can coexist for the same anthill sort.

### Comparison

| | (A) `[builtin]` meta | (B) `provides … language rust` |
|---|---|---|
| Sort declaration | Concrete (with body) | Abstract (`sort Int = ?`) |
| Carrier mapping | Implicit (host knows how to handle `[builtin]`) | Explicit (`carrier Int = "i64"`) inside the provides block |
| Satisfaction facts live in… | The sort body (regular `fact` lines) | The provides block (regular `fact` lines) |
| Multi-language support | Each language ships its own `[builtin]`-marked sort decl, OR re-uses one decl with per-language host binding elsewhere | Natural — multiple `provides Int language X` blocks per language |
| Reuses existing infrastructure | Meta blocks; sort body parsing | `provides_block`; Implementation entity; codegen Carrier table |
| Affects kernel-language §11.6 (entity-of-sort)? | Yes — `[builtin]` sorts have no entities; rules about constructor enumeration must skip them | No — abstract sort, no special rule |
| Migration scope (stdlib) | ~5 files (int, float, string, bool, bigint): wrap in `sort Name [builtin] { … }`, hoist out of namespace shadowing | ~5 files + add `provides Name language rust { … }` block(s); operations migrate to inside the provides block |

### Recommendation

**(B), with phased migration.** Reasoning:

- (B) reuses the existing `Implementation`/`provides_block` infrastructure. (A) introduces new semantics for an existing meta (`[builtin]`) — soft expansion of meta semantics is OK, but having explicit `provides … language rust` is more transparent about what's actually happening (a host-language binding).
- (B) generalizes naturally to "external sorts" — sorts whose carrier is a foreign-language object that isn't a primitive. This is a future concern (FFI, plugin-supplied types) and the shape is identical.
- (B) keeps the `sort Int = ?` declaration simple and pure-anthill. The complexity of "this binds to i64 in Rust" lives in the cross-language layer where it belongs.

The migration is ~5 stdlib files plus wiring in the loader's `provides_block` path to actually consume non-anthill bodies (today they're stubbed).

## Out of scope

- Plugin-supplied sorts (third-party FFI carriers). Same shape as (B); land after stdlib migration.
- Variance annotations on type parameters (separate proposal).
- Renaming `anthill.prelude.Int` namespace to avoid shadowing (mechanically falls out of either (A) or (B) once the sort declaration is hoisted to its proper home).

## Acceptance

When this proposal lands:

1. Builtin sorts (`Int`, `Float`, `String`, `Bool`, `BigInt`) are declared with bodies (under chosen direction); satisfaction facts inside those bodies emit `SortProvidesInfo` with `sort_ref` resolving to the builtin sort symbol (not a namespace doppelgänger).
2. WI-210 phase 3 dispatch hook is re-wired in `kb/typing.rs::check_apply`; the parked dispatch tests (`Unique` / `NoMatch` / `Ambiguous`) pass.
3. `add(x, x)` for `x : Int` type-checks via Int's spec satisfaction (no `WI-210 dispatch failed: no impl of anthill.prelude.Numeric.add` error).
4. `cargo test` green across `anthill-core`, `anthill-todo`.
5. Codegen continues to render `Int` as `i64` (carrier table unchanged in observable output).
