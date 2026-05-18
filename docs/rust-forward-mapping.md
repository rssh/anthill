# Rust Forward Mapping

This document defines how anthill kernel constructs map to Rust code — the **forward direction**: from specification to skeleton. The inverse direction (linking existing Rust code back to specs) is handled by `Implementation` facts (kernel spec §8.5, §8.7).

## 1. Overview

An anthill namespace declares an **algebra**: abstract sorts, operations with contracts, and laws. The forward mapping generates Rust **skeletons** — traits, structs, enums, and function signatures — from these declarations. The generated code is compilable but incomplete: operation bodies are left as `todo!()`, to be filled in by a developer or agent.

The mapping is deterministic: given the same anthill source, the same Rust code is produced. The generated code serves as a starting point; once an implementation exists, an `Implementation` fact (§8) links the code back to the spec for verification.

**Codegen correctness requirement**: The generated Rust code must be directly implementable — filling in `todo!()` bodies with real logic, without changing function signatures, types, or module structure. If a generated signature cannot be implemented as-is, the fix belongs in the codegen rules or the anthill spec, not in post-hoc edits to the generated output.

## 2. Mapping Rules

### Summary Table

| Anthill construct | Rust construct |
|---|---|
| `namespace N` | `mod n` |
| Sort with operations (no constructors) `sort S { operation ... }` | `trait S` |
| Sort with constructors `sort S { entity C₁(...), entity C₂(...) }` | `enum S { C1 { fields }, C2 { fields } }` |
| Standalone `entity E(fields)` | `struct E { fields }` |
| `operation op(a: S, ...) -> R` (first arg is enclosing sort) | `fn op(&self, ...) -> R` on the trait or impl |
| `operation op(a: S, ...) -> ...S...` (return contains S) | `fn op(self, ...) -> ...Self...` by-value (§9) |
| `operation op(x: A, y: B) -> R` (no self-arg) | method on `{Namespace}Ops` module trait |
| `effects (Modify X)` | `&mut self` |
| No effects | `&self` (if method), no `Result` wrapping |
| `effects (Error)` or `effects (Error E)` | `Result<R, Error>` or `Result<R, E>` return |
| `effects (Requires Cap)` | generic bound or runtime check (future) |
| `sort T` (abstract sub-sort = type parameter) | generic `<T>` |
| `requires Eq[T]` | trait bound: `where T: Eq` or supertrait |
| `fact SortName` or `fact SortName[bindings]` (inside sort body) | supertrait: `trait S: SortName` |
| `fact SortName` or `fact SortName[bindings]` (in entity's namespace) | `impl SortName for Entity` |
| `List[T = X]` | `Vec<X>` |
| `Option[T = X]` | `Option<X>` |
| `rule` (law) | `#[cfg(test)]` property-based test stub |
| `Quoted("rust", source)` | verbatim Rust code inserted as-is |
| `constraint` (denial) | `debug_assert!` or test-time check |
| `import N.{A, B}` | `use n::{A, B};` |

### 2.1 Namespace → Module

A `namespace` maps to a Rust `mod`. Nested namespaces become nested modules. The namespace name is lowercased and hyphens become underscores (following Rust module naming conventions):

```
namespace banking           →  pub mod banking { ... }
namespace anthill.prelude    →  pub mod anthill { pub mod prelude { ... } }
```

Exports control visibility: `export`-prefixed items become `pub`, `internal` items have no `pub`.

### 2.2 Sort with Operations (No Constructors) → Trait

A sort whose body contains operations but no entity constructors maps to a Rust trait. The operations become trait methods. Abstract sorts (no body) exist only as type parameters inside sort bodies (see §2.6) — they do not appear at namespace level.

```
sort Store {                               pub trait Store {
  operation persist(              →              fn persist(&mut self, ...) -> ...;
    store: Store, ...) -> FactId                 ...
  ...                                      }
}

sort Eq {                                  pub trait Eq {
  sort T                        →              fn eq(&self, other: &Self) -> bool;
  operation eq(a: T,                           fn neq(&self, other: &Self) -> bool;
    b: T) -> Bool                          }
  operation neq(a: T,
    b: T) -> Bool
}
```

When the sort has a type parameter (`sort T` inside the body), the parameter becomes a Rust generic or `Self` depending on usage (see §2.6).

**Self substitution.** Inside trait method signatures, the enclosing sort name is always replaced with `Self` — both in parameter types and return types. For single-type-parameter traits, the type parameter is also collapsed to `Self` and removed from the trait's generic list (see §4). For multi-parameter traits, only the sort name itself becomes `Self`:

```
sort Stream {                              trait Stream<T, E> {
  sort T                        →              fn split_first(self) -> Option<Pair<T, Self>>;
  sort E                                       fn tail(self) -> Self;
  operation split_first(                       fn is_empty(&self) -> bool;
    s: Stream) -> Option{...}              }
  operation tail(s: Stream)
    -> Stream
  operation isEmpty(s: Stream)
    -> Bool
}
```

Note: `split_first` and `tail` take `self` by value (not `&self`) because the Rust/std profile's `returns_same_type` receiver rule detects that the return type contains `Self` — see §9. `is_empty` returns `Bool`, not `Stream`, so it stays as `&self`.

### 2.3 Sort with Constructors → Enum

A sort with entity constructors maps to a Rust enum. Each constructor becomes a variant:

```
sort WorkStatus {                          pub enum WorkStatus {
  entity Draft                      →          Draft,
  entity Open                                  Open,
  entity Claimed(agent: String,                Claimed {
    since: String)                                 agent: String,
  entity Verified(at: String)                      since: String,
                                               },
                                               Verified {
}                                                  at: String,
                                               },
                                           }
```

Nullary constructors (no fields) become unit variants. Constructors with fields become struct variants.

**Self substitution in enum impl blocks.** When an enum sort also has operations, the sort name in parameter types and return types is replaced with `Self`. However, type parameters are NOT collapsed to `Self` for enums — they remain as generic parameters:

```
sort LogicalStream {                       enum LogicalStream<T> {
  sort T                                       Empty,
  entity Empty                   →         }
  operation pure(x: T)                     impl<T> LogicalStream<T> {
    -> LogicalStream                           fn pure(x: T) -> Self;
  operation mplus(                             fn mplus(&self, b: Self) -> Self;
    a: LogicalStream,                      }
    b: LogicalStream)
    -> LogicalStream
}
```

Note that `pure(x: T)` does NOT get `&self` — type parameter `T` is not treated as the sort itself in enum context. Only the sort name `LogicalStream` matches for the self-arg heuristic.

### 2.4 Standalone Entity → Struct

A standalone `entity` (sugar for a single-constructor sort) maps to a Rust struct:

```
entity Account(                            pub struct Account {
  id: AccountId,                →              pub id: AccountId,
  balance: Money                               pub balance: Money,
)                                          }
```

### 2.5 Operation → Function or Method

Operations map to either trait methods or free functions, depending on the self-arg heuristic (§4):

```
-- Method (first arg is enclosing sort):
operation balance(a: Account) -> Money
→  fn balance(&self) -> Money;

-- Free function (no clear self):
operation route(fact: Term) -> Store
→  pub fn route(fact: Term) -> Store { todo!() }
```

### 2.6 Type Parameters → Generics

An abstract `sort T` declared inside a sort body is a type parameter. It maps to a Rust generic:

```
sort List {                                pub enum List<T> {
  sort T                        →              Nil,
  entity nil                                   Cons { head: T, tail: Box<List<T>> },
  entity cons(head: T,                     }
    tail: List)
}
```

### 2.7 Requires → Trait Bounds

A `requires` declaration maps to a trait bound — either as a supertrait (on a trait definition) or a `where` clause (on a generic struct or function):

```
sort Ordered {                             pub trait Ordered: Eq {
  sort T                        →              fn gt(&self, other: &Self) -> bool;
  requires Eq[T]                               ...
  operation gt(a: T,                       }
    b: T) -> Bool
}
```

When the requires binds a specific type, it becomes a where clause:

```
sort Container {                           pub trait Container<T>
  sort T                        →              where T: Numeric {
  requires Numeric[T]                          ...
  ...                                      }
}
```

### 2.8 Parametric Instantiation → Generic Application

Inline type expressions `Name[T = X]` map to generic type application in Rust:

```
List[T = Int]                   →  Vec<i32>        (prelude type)
Option[T = Account]             →  Option<Account>  (prelude type)
List[T = ContextRef]            →  Vec<ContextRef>  (prelude type)
```

Prelude types have special mappings (§2.9). Non-prelude parametric sorts map directly: `MyContainer[T = Foo]` → `MyContainer<Foo>`.

### 2.9 Prelude Type Mappings

Anthill prelude sorts map to idiomatic Rust types. These mappings are defined in the `LanguageMapping` profile (§9) as `TypeMapping` facts, not hardcoded in the codegen. The default Rust/std profile (`stdlib/anthill/realization/rust_std.anthill`) declares:

| Anthill type | Rust type |
|---|---|
| `Int` | `i64` |
| `Float` | `f64` |
| `Bool` | `bool` |
| `String` | `String` |
| `List[T = X]` | `Vec<X>` |
| `Option[T = X]` | `Option<X>` |
| `Duration` | `std::time::Duration` |
| `Timestamp` | `String` |

A different profile (e.g. Rust/no_std) could override these — `List` → `heapless::Vec`, `String` → `heapless::String`, etc.

### 2.10 Rules → Test Stubs

Rules expressing laws generate property-based test stubs:

```
rule add_comm: add(?a, ?b) = add(?b, ?a)

→  #[cfg(test)]
   mod tests {
       use super::*;
       // Law: add_comm
       // add(a, b) = add(b, a)
       #[test]
       fn prop_add_comm() {
           todo!("property: add(a, b) == add(b, a)")
       }
   }
```

### 2.11 Quoted Terms → Verbatim Code

`Quoted("rust", source)` terms are inserted as-is into the generated Rust code:

```
Quoted("rust", "use serde::{Serialize, Deserialize};")
→  use serde::{Serialize, Deserialize};
```

Quoted terms in other languages (e.g., `Quoted("sql", ...)`) are ignored during Rust code generation.

### 2.12 Constraints → Debug Assertions

Constraints (denials) generate debug assertion helpers or test-time checks:

```
constraint non_negative: gte(balance(?a), zero-val)

→  // Invariant: non_negative — balance(a) >= 0
   fn check_non_negative(a: &Account) -> bool {
       a.balance >= 0
   }
```

These are generated in a separate `invariants` submodule for test-time checking.

### 2.13 Fact as Spec Satisfaction Declaration → Supertrait or Impl

A `fact SortName` or `fact SortName[bindings]` declares a spec satisfaction (refinement) relationship. The bindings (if any) are used by the kernel for constraint checking but are ignored by the codegen — only the sort name matters for the Rust mapping. It maps differently depending on context:

**Inside a sort body** — becomes a supertrait:

```
sort QueryableStore {                      pub trait QueryableStore: Store {
  fact Store                      →            fn retrieve(&self, ...) -> ...;
  operation retrieve(                      }
    store: QueryableStore,
    pattern: Term) -> List[T = Term]
}

sort Stream {                              trait Stream<T, E>: Streamable {
  sort T                          →            ...
  sort E                                   }
  fact Streamable[T = T]
  ...
}
```

`fact Store` inside `sort QueryableStore` means "every QueryableStore is-a Store". `fact Streamable[T = T]` inside `sort Stream` means "every Stream is-a Streamable" — the bindings are stripped, only the sort name `Streamable` becomes a supertrait.

**In an entity's namespace** — becomes a trait implementation:

```
-- In namespace anthill.persistence.sql:
entity SqlStore(                           pub struct SqlStore { ... }
  connection: String, ...)        →
fact QueryableStore                        impl QueryableStore for SqlStore { ... }
```

`fact QueryableStore` in the namespace where `SqlStore` is defined means "SqlStore is-a QueryableStore", which maps to implementing the trait.

## 3. Generation Boundary

Not every sort in the KB should be generated. The codegen must decide: for each sort/namespace, generate a skeleton or treat it as an external dependency?

### 3.1 The Rule: Implementation Facts Define the Boundary

The codegen queries the KB for `Implementation` facts with `language: "rust"`. Any sort or namespace that already has a Rust implementation is **excluded** from generation — it is an external dependency. Everything else in scope is a candidate for generation.

```
-- A is implemented in another project:
fact Implementation("graphics.Renderer",
  artifact: "renderer/src/lib.rs", language: "rust",
  carrier: { Pixel: "u32" })

-- B depends on A, has no Implementation fact:
namespace scene
  import graphics.Renderer
  entity Scene(renderer: Renderer, objects: List[T = SceneObject])
  operation render(s: Scene) -> Frame
end
```

Running `anthill codegen rust scene`:
- **Renderer** — has a Rust `Implementation` fact → **skip**, emit `use renderer::Renderer;`
- **Scene** — no `Implementation` fact → **generate** struct and method stubs

### 3.2 Resolution of External Types

When a generated sort B references an external sort A (one with an `Implementation` fact), the codegen resolves A's Rust type from the Implementation fact's carrier bindings and artifact path:

| Information | Source |
|---|---|
| Rust type name | `carrier` bindings in the `Implementation` fact |
| Import path | `artifact` field → derive crate/module path |

For example, if A's Implementation declares `carrier: { Pixel: "u32" }`, then anywhere B's anthill spec references `Pixel`, the generated Rust uses `u32`.

If A's Implementation declares `artifact: "renderer/src/lib.rs"` and the carrier maps `Renderer` to the sort itself, the generated code emits `use renderer::Renderer;` (the exact import path derivation is convention-based — see §3.4).

### 3.3 Three Categories

Every sort encountered during codegen falls into one of three categories:

| Category | Condition | Codegen action |
|---|---|---|
| **Prelude** | Sort is in `anthill.prelude` | Use Rust type from profile (§2.9, §9): `List` → `Vec`, `Option` → `Option`, etc. |
| **Implemented** | Has `Implementation` fact with `language: "rust"` | Skip generation, emit `use` import with types from carrier bindings |
| **Unimplemented** | No matching `Implementation` fact | Generate skeleton |

### 3.4 Import Path Derivation

The `artifact` field in an `Implementation` fact is a file path (e.g., `"src/renderer.rs"`). The codegen derives a Rust `use` path from it:

1. Strip the source root prefix (e.g., `src/`) and file extension (`.rs`)
2. Replace `/` with `::`
3. Prepend the crate name if the artifact is in a different crate

```
artifact: "src/renderer.rs"     →  use crate::renderer::Renderer;
artifact: "renderer/src/lib.rs" →  use renderer::Renderer;  // external crate
```

When the derivation is ambiguous (e.g., the artifact path doesn't follow conventions), the codegen emits a `// TODO: use ???::TypeName;` comment and continues.

### 3.5 Staleness Detection via Timestamps

Both sort definitions and `Implementation` facts carry a `last-modified` timestamp in their metadata. The codegen compares these to **automatically detect** when an implementation is stale:

```
-- Sort definition, last changed 2026-02-20:
sort Store {
  operation persist(store: Store, fact: Term, meta: Meta) -> FactId
    effects (Modify{store}, Error)
  ...
}
[last-modified: "2026-02-20T14:00:00Z"]

-- Implementation fact, created 2026-02-10:
fact Implementation("anthill.persistence.Store",
  artifact: "src/persistence.rs", language: "rust",
  carrier: { ... })
  [last-modified: "2026-02-10T09:00:00Z"]
```

The sort's `last-modified` (`02-20`) is newer than the Implementation's (`02-10`), so the codegen knows the implementation is **stale**. It automatically regenerates the skeleton for that sort, even though an Implementation fact exists.

**Staleness rule:**

| Condition | Codegen action |
|---|---|
| No `Implementation` fact | Generate (unimplemented) |
| `Implementation` exists, `impl.last-modified >= sort.last-modified` | Skip (up to date) |
| `Implementation` exists, `impl.last-modified < sort.last-modified` | Regenerate (stale) |
| `Implementation` exists, no timestamps on either | Skip (assume up to date) |

This makes `--include-implemented` rarely needed — staleness is detected automatically. The flag remains available to force regeneration regardless of timestamps.

After updating the code to match the new spec, the developer supersedes the old Implementation fact:

```
fact Implementation("anthill.persistence.Store",
  artifact: "src/persistence.rs", language: "rust",
  carrier: { ... })
  [trust: proposed, last-modified: "2026-02-21T10:00:00Z",
   supersedes: old_impl_fact]
```

Now `impl.last-modified >= sort.last-modified`, so the codegen considers it up to date again.

For **external dependencies** (sort A implemented in another project), if A's spec changes, the codegen will emit the new type signatures from A's (updated) carrier bindings. Compilation errors in B's code reveal what needs manual fixing.

### 3.6 CLI Control

```
anthill codegen rust                          -- default: generate unimplemented + stale sorts
anthill codegen rust --include-implemented    -- force regenerate all, ignoring timestamps
anthill codegen rust --exclude graphics       -- skip a namespace even if unimplemented
anthill codegen rust --dry-run               -- show what would be generated (and why: unimplemented/stale)
```

`--dry-run` reports the staleness status of each namespace, showing which sorts would be regenerated and why:

```
$ anthill codegen rust --dry-run
  banking.Account          — unimplemented, will generate
  persistence.Store        — stale (sort: 2026-02-20, impl: 2026-02-10), will regenerate
  graphics.Renderer        — up to date, skipping
  anthill.prelude.List     — prelude, using Vec<T>
```

## 4. Self-Arg Heuristic

When mapping operations to Rust methods vs. free functions, the codegen must decide which (if any) argument becomes `self`. The heuristic:

1. **Enclosing sort rule.** If the operation is declared inside a sort body `sort S { operation op(x: S, ...) -> R }`, and the first argument's type matches `S` (the enclosing sort name), then `x` becomes `self`. For **single-type-parameter trait sorts** (where "self-collapse" is active), the type parameter also matches — `op(x: T, ...) → fn op(&self, ...)`. For **enum sorts** and **multi-parameter trait sorts**, only the sort name itself matches.

2. **Namespace entity rule.** If the operation is declared at namespace level, and its first argument type matches an entity or defined sort declared in the same namespace, it becomes a method in an `impl` block for that type.

3. **No-self rule.** If neither rule applies, the operation is collected into a **module trait** named `{Namespace}Ops` with `&self` added as receiver. This makes them enforceable interfaces — implementations provide a unit struct with the trait impl.

**Examples:**

```
-- Rule 1a: Single-param trait — type param T matches as self
sort Eq {
  sort T
  operation eq(a: T, b: T) -> Bool        →  fn eq(&self, other: &Self) -> bool;
}

-- Rule 1b: Multi-param trait — sort name matches as self, type params do not
sort Stream {
  sort T
  sort E
  operation tail(s: Stream) -> Stream      →  fn tail(self) -> Self;
  operation isEmpty(s: Stream) -> Bool     →  fn is_empty(&self) -> bool;
}
-- Note: tail gets `self` (by-value) because the receiver_map
-- "returns_same_type" rule matches (return is Self). isEmpty
-- returns Bool, not Stream, so it stays as &self.

-- Rule 1c: Enum — sort name matches as self, type params do NOT
sort LogicalStream {
  sort T
  entity Empty
  operation mplus(a: LogicalStream,        →  fn mplus(self, b: Self) -> Self;
    b: LogicalStream) -> LogicalStream
  operation pure(x: T) -> LogicalStream    →  fn pure(x: T) -> Self;   -- T ≠ self
}
-- mplus returns LogicalStream → returns_same_type → self by value.
-- pure: first param is T, not LogicalStream — no self at all.

-- Rule 1d: Sort name match in enum
sort List {
  operation length(l: List) -> Int         →  fn length(&self) -> i64;
}

-- Rule 2: In namespace config, first arg is Settings (an entity in config)
namespace config {
  entity Settings(path: String, verbose: Bool)
  operation load(s: Settings) -> Settings  →  impl Settings { fn load(self) -> Self { todo!() } }
}
-- load returns Settings → returns_same_type → self by value.

-- Rule 3: No matching sort/entity → module trait
namespace persistence {
  operation route(fact: Term) -> Store     →  pub trait PersistenceOps {
}                                                fn route(&self, fact: Term) -> impl Store;
                                             }
```

**Self-reference style.** The receiver is determined by evaluating the `LanguageMapping` profile (§9) rules in order. The default Rust/std profile produces:

| Condition | Rust receiver | Source |
|---|---|---|
| `Modify{...}` on the sort itself | `&mut self` | effect_map |
| Return type contains `Self` | `self` (by value) | receiver_map `returns_same_type` |
| No effects / default | `&self` | — |

Effect rules are checked first (they are semantic). Receiver rules are checked second (they are Rust-specific ownership optimizations). See §9 for details.

## 5. Effects → Rust Idioms

The kernel's effect declarations (kernel spec §5.5) map to Rust idioms. These mappings are defined as data in the `LanguageMapping` profile (§9), not hardcoded in the codegen. The rules below describe the default Rust/std profile (`stdlib/anthill/realization/rust_std.anthill`):

### 5.1 Modify (Access Pattern)

`effects (Modify X)` indicates the operation mutates state. This affects only the **receiver form**:
- `&mut self` if X is the enclosing sort
- `&mut x: X` parameter if X is a different argument

Modify does **not** imply fallibility — it only declares the access pattern. If the operation can fail, declare `Error` explicitly:

```
operation persist(store: Store, fact: Term, meta: Meta) -> FactId
  effects (Modify{store}, Error)

→  fn persist(&mut self, fact: Term, meta: Meta) -> Result<FactId, Error>;
```

Without `Error`, the return is unwrapped:

```
operation increment(counter: Counter) -> Int
  effects (Modify{counter})

→  fn increment(&mut self) -> i64;
```

### 5.2 Read — Not an Effect on Parameters

Reading a parameter is not a side effect — it's what operations do. Declaring `effects (Read{store})` when `store` is already a parameter is redundant and should be avoided.

`Read` is reserved for future use in **capture tracking** — declaring that a returned closure or value captures a read reference to an external resource not in the parameter list. This is analogous to Scala 3's capture checking.

For now, the receiver form (`&self` vs `&mut self`) is determined by:
- `Modify{x}` on a parameter → `&mut self`
- Default → `&self`

An operation that takes the enclosing sort as its first parameter gets `&self` automatically — no effect declaration needed:

```
operation sorts(kb: KB, namespace: Option[T = String]) -> List[T = SortInfo]

→  fn sorts(&self, namespace: Option<String>) -> Vec<SortInfo>;
```

### 5.3 Error (Fallibility)

`effects (Error)` or `effects (Error E)` declares that the operation can fail. This is orthogonal to access patterns — a pure function, a read, or a mutation can each independently be fallible.

Bare `Error` wraps in `Result<R, Error>`:

```
operation execute(kb: KB, query: LogicalQuery) -> Stream[T = Substitution]
  effects (Error)

→  fn execute(&self, query: LogicalQuery) -> Result<impl Stream<Substitution>, Error>;
```

Typed `Error E` uses the specific error type:

```
operation withdraw(a: Account, m: Money) -> Account
  effects (Error InsufficientFunds)

→  fn withdraw(&self, m: Money) -> Result<Account, InsufficientFunds>;
```

When `Modify` and `Error` are both present, they compose independently — `Modify` determines the receiver, `Error` determines the return wrapping:

```
operation transfer(from: Account, to: Account, m: Money) -> Account
  effects (Modify[Ledger], Error TransferError)

→  fn transfer(
       &mut self,
       to: &Account,
       m: Money,
   ) -> Result<Account, TransferError>;
```

### 5.4 Pure Operations

Operations with no effects are pure functions. They use `&self` (if a method) and return the result directly — no `Result` wrapping:

```
operation balance(a: Account) -> Money

→  fn balance(&self) -> Money;
```

### 5.5 Effect Parameters on Sorts (E on Stream)

Sorts may declare abstract effect parameters — e.g. `sort E = ?` on `Stream`. These represent what can happen when *consuming* elements, not when creating the stream. The interpretation of `E` depends on which concrete effects are bound at the use site.

**Resolution rule**: For each concrete project, the set of effects is known. The LanguageMapping profile defines how each effect maps to a host-language construct. The effect parameter `E` is resolved by the same rules:

| Binding | Rust interpretation |
|---|---|
| `E = Error` | Iterator yields `Result<T, ErrorType>` — iteration can fail |
| `E` unbound (`= ?`) | Items are plain `T` — pure iteration |
| `E = Suspend` (future) | `async fn next()` / `Future<Output = Option<T>>` |

**Example: KB.execute**

```
operation execute(kb: KB, query: LogicalQuery)
  -> Stream[T = Substitution, E = Error]
  effects (Error)
```

This has two independent error points:
- `effects (Error)` — **creation** can fail (invalid query). Maps to `Result<..., Error>` on the return.
- `E = Error` on Stream — **iteration** can fail (residual errors, depth limits). Maps to items being `Result<Substitution, Error>`.

Generated Rust:
```rust
fn execute(&self, query: LogicalQuery) -> Result<impl Stream<Substitution, Error>, Error>;
```

The outer `Result` is from `effects (Error)`. The `Error` type parameter on `Stream` is structural — the `Stream` trait's implementation decides how `E` affects item types. A concrete implementation (e.g. file-backed) would produce `Result<Substitution, Error>` items; a pure in-memory one might leave `E` unbound.

**General principle**: With the current Rust/std profile, the only implemented effect is `Error`, which maps to `Result`. So `E` in practice resolves to "is there an error type or not." When more effects are implemented (Suspend → `async`, etc.), the LanguageMapping's `effect_map` determines the interpretation — no codegen changes needed, only profile updates.

**MonadStack for non-direct languages**: In languages with monadic effect encoding (Scala/cats, Haskell), `E` resolves to a monad that encapsulates all bound effects. The `LanguageMapping` profile defines the monad stack composition order. For Rust, this is unnecessary — each effect has a direct encoding (`Result`, `&mut`, `async`), and they compose structurally rather than via monad transformers.

### 5.6 Modify[result] — fresh-target allocation (per proposal 027.1)

When `effects (Modify[result])` appears on a return (proposal 027.1), the operation allocates a fresh value of its return type. The Rust shape depends on the active profile:

| Anthill                                                        | Rust mapping by profile                                          |
|---                                                             |---                                                               |
| `op f() -> Cell[V] effects Modify[result]` (std)               | `fn f() -> Cell<V>` (owned return)                               |
| `op f() -> Cell[V] effects Modify[result]` (no_std)            | `fn f() -> Box<Cell<V>>` (heap-allocated)                        |
| `op f() -> Cell[V] effects Modify[result]` (arena)             | `fn f<'arena>(a: &'arena Arena) -> &'arena mut Cell<V>`          |

Carrier and allocation strategy are profile-driven (§9), not hardcoded — the same mechanism as other effect mappings in this section.

Other 027.1 allocator-shape rules apply uniformly:
- `Map.empty() -> Map[K, V] effects Modify[result]` → `fn empty() -> HashMap<K, V>` (std) / `Box<HashMap<...>>` (no_std) / arena equivalent
- `Substitution.empty() -> Substitution effects Modify[result]` → analogous

### 5.7 Discharge analysis ↔ stack allocation

027.1 defines a *discharge rule*: a value carrying `Modify[result]` bound to a local that doesn't escape the operation's body has its effect discharged at the function boundary and doesn't propagate to the inferred row. Rust codegen mirrors this directly:

| Anthill body                                                                 | Rust translation                                                                  |
|---                                                                           |---                                                                                |
| `let c = Cell.new(0); ...; Cell.get(c)` (c discharged — local use only)      | `let mut c = Cell::new(0); ...; c.get()` (local; dropped at scope end)            |
| `let c = Cell.new(0); ...; c` (c propagates as `Modify[result]`)             | `let mut c = Cell::new(0); ...; c` (returned by value)                            |
| `let c = Cell.new(0); something(c)` (depends on `something`'s sig)           | `let mut c = Cell::new(0); something(&mut c)` (borrow) or `something(c)` (move)   |

Conceptually, anthill's discharge analysis is structurally the same computation Rust's borrow checker performs for lifetimes — escape detection on effect targets rather than on references. Knowing this connection helps Rust users build accurate intuition for the effect system: a tight discharge analysis yields fewer heap allocations and more stack-resident values in idiomatic generated Rust. **027.1 Phase 1 is therefore load-bearing for Rust codegen quality, not only for effect-system correctness.**

(Note: `Read[c]` cell-precise tracking discussed in 027.1's §"Standard effect catalog" is not yet a Rust mapping concern — §5.2 above keeps the current convention that read access on a parameter is implicit. If cell-precise `Read[c]` lands per a future driver, this section should be revisited: disjoint `&` borrows would license dedup/parallelization that the current "parameter implies read" convention cannot express.)

### 5.8 Receiver Rules (Ownership)

Beyond effects, the Rust profile defines **receiver rules** — host-language-specific conventions for how `self` is passed. These are not semantic properties of the operation; they are Rust ownership optimizations.

The default Rust/std profile has one receiver rule:

**`returns_same_type` → `ByValue`.** When the return type of a method contains the enclosing sort (i.e. `Self`), take `self` by value instead of `&self`. This avoids cloning: the caller gives up the old value and receives a new one.

This rule applies to operations like `splitFirst`, `tail`, `collect` on `Stream` — all of which return (or contain) `Stream` in their output. Operations like `head` and `isEmpty` return `Option[T]` and `Bool` respectively (no `Stream`), so they stay as `&self`.

```
-- Stream operations are pure (no effects):
operation splitFirst(s: Stream) -> Option[T = Pair[A = T, B = Stream]]
operation isEmpty(s: Stream) -> Bool

-- Rust/std profile produces:
fn split_first(self) -> Option<(T, Self)>;   -- returns_same_type → by value
fn is_empty(&self) -> bool;                  -- no match → &self
```

**Why not `Modify{s}`?** Stream is semantically immutable — `splitFirst` is a pure function. In Scala, it returns a new value without mutation. The by-value receiver (`self` instead of `&self`) is a Rust-specific optimization (ownership avoids cloning), driven by the `returns_same_type` receiver rule, not by any effect.

Receiver rules are evaluated after effect rules. If an effect already determines the receiver (e.g. `Modify → &mut self`), receiver rules do not override it.

## 6. Concrete Examples

### 6.1 Persistence Store Hierarchy

The persistence layer uses a three-sort hierarchy: `Store` (base), `QueryableStore` (pattern-based retrieval), and `BulkStore` (load-all-into-memory). The sort hierarchy replaces runtime capability tags.

```
-- Anthill:
namespace anthill.persistence

  sort Store                                  -- base: all backends

  operation route(fact: Term) -> Store
  operation persist(store: Store, fact: Term, meta: Meta) -> FactId
    effects (Modify{store}, Error)
  operation retract(store: Store, id: FactId) -> Bool
    effects (Modify{store}, Error)
  operation flush(store: Store, delta: List[T = Term]) -> Bool
    effects (Modify{store}, Error)

  sort QueryableStore
    fact Store                                -- QueryableStore is-a Store

  operation retrieve(store: QueryableStore, pattern: Term) -> List[T = Term]
    effects (Error)

  sort BulkStore
    fact Store                                -- BulkStore is-a Store

  operation pull(store: BulkStore) -> List[T = Term]
    effects (Error)

end

-- In namespace anthill.persistence.sql:
entity SqlStore(connection: String, schema: String, dialect: SqlDialect)
fact QueryableStore                           -- SqlStore is-a QueryableStore

-- In namespace anthill.persistence.filesystem:
entity FileStore(root: String, convention: FileConvention)
fact BulkStore                                -- FileStore is-a BulkStore
```

Generated Rust:

```rust
pub mod persistence {
    pub trait Store {
        fn persist(&mut self, fact: Term, meta: Meta) -> Result<FactId, Error>;
        fn retract(&mut self, id: FactId) -> Result<bool, Error>;
        fn flush(&mut self, delta: Vec<Term>) -> Result<bool, Error>;
    }

    pub trait QueryableStore: Store {
        fn retrieve(&self, pattern: Term) -> Result<Vec<Term>, Error>;
    }

    pub trait BulkStore: Store {
        fn pull(&self) -> Result<Vec<Term>, Error>;
    }

    pub fn route(fact: Term) -> impl Store { todo!() }
}

pub mod sql {
    use super::persistence::*;

    pub struct SqlStore {
        pub connection: String,
        pub schema: String,
        pub dialect: SqlDialect,
    }

    impl Store for SqlStore { /* ... */ }
    impl QueryableStore for SqlStore { /* ... */ }
}

pub mod filesystem {
    use super::persistence::*;

    pub struct FileStore {
        pub root: String,
        pub convention: FileConvention,
    }

    impl Store for FileStore { /* ... */ }
    impl BulkStore for FileStore { /* ... */ }
}
```

Note: `fact Store` inside `sort QueryableStore` becomes supertrait `QueryableStore: Store`. `fact QueryableStore` in the SqlStore namespace becomes `impl QueryableStore for SqlStore` (which implies `impl Store for SqlStore` since `QueryableStore: Store`).

### 6.2 Prelude List

```
-- Anthill:
sort anthill.prelude.List
  sort T
  entity nil
  entity cons(head: T, tail: List)
  operation length(l: List) -> Int
  rule length(nil) = 0
  rule length(cons(?x, ?xs)) = add(1, length(?xs))
end
```

Generated Rust:

```rust
pub enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> },
}

impl<T> List<T> {
    pub fn length(&self) -> i64 {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Law: length(nil) = 0
    #[test]
    fn prop_length_nil() {
        todo!("property: List::Nil.length() == 0")
    }

    // Law: length(cons(x, xs)) = 1 + length(xs)
    #[test]
    fn prop_length_cons() {
        todo!("property: Cons { head, tail }.length() == 1 + tail.length()")
    }
}
```

### 6.3 Prelude Trait Hierarchy (Eq / Ordered / Numeric)

```
-- Anthill:
sort anthill.prelude.Eq
  sort T
  operation eq(a: T, b: T) -> Bool
  operation neq(a: T, b: T) -> Bool
  rule neq(?a, ?b) = not(eq(?a, ?b))
end

sort anthill.prelude.Ordered
  sort T
  requires Eq[T]
  operation gt(a: T, b: T) -> Bool
  ...
end

sort anthill.prelude.Numeric
  sort T
  requires Ordered[T]
  operation add(a: T, b: T) -> T
  operation sub(a: T, b: T) -> T
  operation mul(a: T, b: T) -> T
  operation zero-val() -> T
  ...
end
```

Generated Rust:

```rust
pub trait Eq {
    fn eq(&self, other: &Self) -> bool;

    fn neq(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

pub trait Ordered: Eq {
    fn gt(&self, other: &Self) -> bool;
    fn gte(&self, other: &Self) -> bool;
    fn lt(&self, other: &Self) -> bool;
    fn lte(&self, other: &Self) -> bool;
}

pub trait Numeric: Ordered {
    fn add(&self, other: &Self) -> Self;
    fn sub(&self, other: &Self) -> Self;
    fn mul(&self, other: &Self) -> Self;
    fn zero_val() -> Self;
}
```

Note: `requires Eq[T]` on `Ordered` becomes a supertrait `: Eq`. `requires Ordered[T]` on `Numeric` becomes `: Ordered`. The `rule neq(?a, ?b) = not(eq(?a, ?b))` generates a default method implementation.

### 6.4 Stage 0 WorkStatus

```
-- Anthill:
sort WorkStatus {
  entity Draft
  entity Open
  entity Claimed(agent: String, since: String)
  entity Delivered(agent: String, at: String)
  entity Verified(at: String)
  entity Rejected(reason: String, at: String)
  entity ProposalRejected(reason: String, at: String)
  entity Stale(reason: String, since: String)
}
```

Generated Rust:

```rust
pub enum WorkStatus {
    Draft,
    Open,
    Claimed {
        agent: String,
        since: String,
    },
    Delivered {
        agent: String,
        at: String,
    },
    Verified {
        at: String,
    },
    Rejected {
        reason: String,
        at: String,
    },
    ProposalRejected {
        reason: String,
        at: String,
    },
    Stale {
        reason: String,
        since: String,
    },
}
```

### 6.5 Banking Algebra

Banking is parametric over `Money` (abstract sub-sort), so it is a `sort`, not a `namespace`. The codegen produces a trait with `Money` as an associated type:

```
-- Anthill:
sort banking
  import anthill.prelude.Numeric.{Numeric, add, sub, gt, gte, zero-val}

  sort Money                                         -- type parameter (abstract)
  requires Numeric[T = Money]

  entity Account(id: AccountId, balance: Money)

  operation deposit(a: Account, m: Money) -> Account
    requires gt(m, zero-val)
    ensures eq(balance(result), add(balance(a), m))
  operation withdraw(a: Account, m: Money) -> Account
    requires gt(m, zero-val)
    requires gte(balance(a), m)
    ensures eq(balance(result), sub(balance(a), m))
  operation balance(a: Account) -> Money

  constraint non_negative: gte(balance(?a), zero-val)
end
```

Generated Rust:

```rust
pub trait Banking {
    type Money: Numeric;

    fn deposit(a: &Account<Self::Money>, m: Self::Money) -> Account<Self::Money> {
        todo!()
    }

    fn withdraw(a: &Account<Self::Money>, m: Self::Money) -> Account<Self::Money> {
        todo!()
    }

    fn balance(a: &Account<Self::Money>) -> Self::Money {
        todo!()
    }
}

pub struct Account<Money> {
    pub id: AccountId,
    pub balance: Money,
}

#[cfg(test)]
mod tests {
    use super::*;

    // Invariant: non_negative — balance(a) >= 0
    #[test]
    fn check_non_negative() {
        todo!("invariant: account.balance() >= 0")
    }
}
```

### 6.6 Stage 0 WorkItem (Entity with Parametric Fields)

```
-- Anthill:
entity WorkItem(
  id          : String,
  description : Option[T = Term],
  context     : Option[T = List[T = ContextRef]],
  acceptance  : List[T = AcceptanceCriterion],
  depends_on  : Option[T = List[T = String]],
  status      : WorkStatus
)
```

Generated Rust:

```rust
pub struct WorkItem {
    pub id: String,
    pub description: Option<Term>,
    pub context: Option<Vec<ContextRef>>,
    pub acceptance: Vec<AcceptanceCriterion>,
    pub depends_on: Option<Vec<String>>,
    pub status: WorkStatus,
}
```

## 7. What Is NOT Generated

The forward mapping produces **skeletons**, not complete implementations. The following are deliberately excluded:

### 7.1 Rule Bodies

Rules that express operational semantics (e.g., `rule length(cons(?x, ?xs)) = succ(length(?xs))`) become test stubs, not executable code. The anthill kernel does not yet have execution semantics for sequential composition — generating runnable Rust from declarative rules requires a separate compilation step that is out of scope.

Exception: simple equational rules like `neq(?a, ?b) = not(eq(?a, ?b))` MAY generate default method implementations when the mapping is unambiguous.

### 7.2 Unspecified Terms

`Unspecified(text, hints, id)` terms cannot be formalized into Rust code. They are emitted as comments:

```
<"human-readable description of the business logic">
→  // TODO: human-readable description of the business logic
```

### 7.3 Implementation Facts

`Implementation` facts (kernel spec §8.5) are the **reverse** direction — they link existing code to specs. They are not consumed by the forward mapping; they are what you create AFTER generating (or hand-writing) the Rust code, to close the verification loop.

### 7.4 Metadata

`Meta(trust: ..., agent: ..., ...)` annotations are provenance information for the KB, not structural information for code generation. They are not reflected in the generated Rust code.

### 7.5 Routing Rules and Store Configuration

Persistence routing rules (`rule route(X) = Store(...)`) are runtime configuration, not type structure. They do not generate Rust code.

## 8. Relationship to Implementation Facts

The forward mapping and `Implementation` facts are two halves of a round-trip:

```
                    Forward Mapping
    Anthill Spec  ─────────────────────→  Rust Skeleton
         │                                      │
         │                                      │ (developer fills in bodies)
         │                                      ↓
         │                                Rust Implementation
         │                                      │
         └──────────────────────────────────────┘
                   Implementation Fact
              (links code back to spec)
```

1. **Forward mapping** (this document): `anthill codegen rust` generates Rust skeletons from algebra specs.

2. **Development**: A developer or agent fills in the `todo!()` bodies, making the code functional.

3. **Implementation fact** (kernel spec §8.5): An `Implementation` fact is asserted, linking the Rust code back to the anthill spec:

```
fact Implementation("banking",
  artifact: "src/banking.rs", language: "rust",
  profile: "std",
  carrier: { Money: "i64", AccountId: "u64" })
  [trust: proposed]
```

4. **Verification**: The kernel generates proof obligations from operation contracts (`requires`/`ensures`). Agents discharge these obligations via testing, formal verification, or manual review, progressively upgrading the trust level.

The forward mapping is optional — hand-written code that matches the spec works equally well. The `Implementation` fact is what matters for verification: it declares "this code intends to implement that spec." The forward mapping merely automates the boilerplate.

## 9. LanguageMapping: Data-Driven Codegen

The codegen rules described in §4 (self-arg heuristic), §5 (effects → Rust idioms), and §2.9 (type mappings) are not hardcoded. They are defined as `LanguageMapping` facts in the KB, declared in `anthill.realization`. The codegen reads the active profile and applies its rules.

### 9.1 Architecture

```
┌─────────────────────────────────────┐
│  Kernel effects (language-agnostic) │   Modify, Error
│  — what happens semantically        │
├─────────────────────────────────────┤
│  LanguageMapping profile            │   "rust/std", "rust/no_std", "scala/cats"
│  — how effects map to host syntax   │
├─────────────────────────────────────┤
│  Codegen                            │   reads profile, emits code
└─────────────────────────────────────┘
```

The kernel spec says **what** happens (e.g. `Modify(store)` — this operation mutates the store). The profile says **how** to express that in the host language (e.g. `&mut self` in Rust, mutable state monad in Scala). This separation means:

- The same anthill spec generates idiomatic Rust **and** idiomatic Scala
- Rust-specific concerns (ownership, borrowing) don't pollute the spec
- Changing codegen behavior is a profile change, not a code change

### 9.2 LanguageMapping Entity

Defined in `stdlib/anthill/realization/realization.anthill`:

```anthill
entity LanguageMapping(
  language      : String,                    -- "rust", "scala", "python"
  profile       : Option[T = String],        -- "std", "no_std", etc.
  effect_map    : List[T = EffectMapping],   -- effect → host syntax
  receiver_map  : List[T = ReceiverRule],    -- ownership rules (host-specific)
  type_map      : List[T = TypeMapping]      -- prelude type → host type
)
```

Three kinds of rules:

**`effect_map`** — semantic: how kernel effects map to host syntax.

```anthill
entity EffectMapping(
  effect    : String,        -- "Modify", "Error"
  receiver  : ReceiverForm   -- SharedRef, MutRef, ByValue, ResultWrap
)
```

**`receiver_map`** — host-language-specific: how to pass `self` based on signature patterns. Not tied to any effect. Evaluated in order; first match wins.

```anthill
entity ReceiverRule(
  condition : String,        -- "returns_same_type"
  receiver  : ReceiverForm   -- ByValue, SharedRef, etc.
)
```

**`type_map`** — prelude type mappings.

```anthill
entity TypeMapping(
  anthill_type : String,     -- "Int", "List", "Option"
  host_type    : String      -- "i64", "Vec", "Option"
)
```

### 9.3 ReceiverForm

The host-language forms available:

```anthill
sort ReceiverForm
  entity SharedRef                    -- &self / shared borrow
  entity MutRef                       -- &mut self / exclusive borrow
  entity ByValue                      -- self / move (consuming)
  entity ResultWrap                   -- wrap return in Result<R, Error>
  entity ResultTyped(error: String)   -- wrap return in Result<R, E>
end
```

### 9.4 Default Rust/std Profile

The default profile is declared in `stdlib/anthill/realization/rust_std.anthill`:

```anthill
fact LanguageMapping(
  language: "rust",
  profile: some("std"),

  effect_map: [
    EffectMapping(effect: "Modify", receiver: MutRef),

    EffectMapping(effect: "Error",  receiver: ResultWrap),

  ],

  receiver_map: [
    ReceiverRule(condition: "returns_same_type", receiver: ByValue)
  ],

  type_map: [
    TypeMapping(anthill_type: "Int",       host_type: "i64"),
    TypeMapping(anthill_type: "Float",     host_type: "f64"),
    TypeMapping(anthill_type: "Bool",      host_type: "bool"),
    TypeMapping(anthill_type: "String",    host_type: "String"),
    TypeMapping(anthill_type: "Duration",  host_type: "std::time::Duration"),
    TypeMapping(anthill_type: "Timestamp", host_type: "String"),
    TypeMapping(anthill_type: "List",      host_type: "Vec"),
    TypeMapping(anthill_type: "Option",    host_type: "Option")
  ]
)
```

### 9.5 Evaluation Order

For a given operation, the codegen determines the receiver form as follows:

1. **Effect rules** (from `effect_map`): if the operation has `Modify{x}` where x is the self parameter, use `MutRef` (`&mut self`).

2. **Receiver rules** (from `receiver_map`): if no effect determined the receiver, evaluate receiver rules in order. For `returns_same_type`: check whether the enclosing sort name appears in the return type. If so, use `ByValue`.

3. **Default**: `SharedRef` (`&self`).

Effect rules take priority because they are semantic — `Modify` genuinely means mutation. Receiver rules are optimizations that apply when no semantic effect constrains the choice.

**Example: Stream operations**

```
splitFirst(s: Stream) -> Option[Pair[T, Stream]]
  1. No Modify → default receiver
  2. receiver_map: Stream appears in return → ByValue
  Result: fn split_first(self) -> Option<(T, Self)>

isEmpty(s: Stream) -> Bool
  1. No Modify
  2. receiver_map: Stream does NOT appear in return (Bool)
  3. Default: SharedRef
  Result: fn is_empty(&self) -> bool

persist(store: Store, fact: Term) -> FactId  effects (Modify{store}, Error)
  1. Modify{store} → MutRef
  2. Error → ResultWrap
  Result: fn persist(&mut self, fact: Term) -> Result<FactId, Error>
```

### 9.6 Alternative Profiles

A Rust/no_std profile might differ:

```anthill
fact LanguageMapping(
  language: "rust", profile: some("no_std"),
  effect_map: [
    EffectMapping(effect: "Modify", receiver: MutRef),
    EffectMapping(effect: "Error",  receiver: ResultWrap),
  ],
  receiver_map: [
    ReceiverRule(condition: "returns_same_type", receiver: ByValue)
  ],
  type_map: [
    TypeMapping(anthill_type: "Int",    host_type: "i32"),
    TypeMapping(anthill_type: "List",   host_type: "heapless::Vec"),
    TypeMapping(anthill_type: "String", host_type: "heapless::String"),
    ...
  ]
)
```

A Scala profile would have an empty `receiver_map` — no ownership concerns:

```anthill
fact LanguageMapping(
  language: "scala", profile: some("cats"),
  effect_map: [
    EffectMapping(effect: "Modify", receiver: SharedRef),  -- immutable values, state monad

    EffectMapping(effect: "Error",  receiver: ResultWrap),

  ],
  receiver_map: [],
  type_map: [
    TypeMapping(anthill_type: "Int",    host_type: "Int"),
    TypeMapping(anthill_type: "List",   host_type: "List"),
    TypeMapping(anthill_type: "Option", host_type: "Option"),
    ...
  ]
)
```

Here `splitFirst(s: Stream) -> ...Stream...` stays as a regular method call — no by-value, no consumption. The JVM GC handles the old reference.
