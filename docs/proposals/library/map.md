# Library: Map — Split into MapReadable, PersistentMap, MutableMap

## Status

Draft 2026-05-28. First proposal under `docs/proposals/library/` — the directory holds stdlib-library design proposals as distinct from kernel-language proposals in the parent directory.

## Motivation

Today's `stdlib/anthill/prelude/map.anthill` declares one sort `anthill.prelude.Map` with:

- `empty() -> Map` (no `effects` clause)
- `put(m: Map, key: K, value: V) -> Map` (functional-update shape — no effects)
- `remove(m: Map, key: K) -> Map`
- read-only ops: `get`, `contains`, `keys`, `values`, `entries`, `size`
- algebraic rules: `get(put(?m, ?k, ?v), ?k) = some(?v)`, etc.

Reading this as a user, you read **persistent / functional** Map. The rules confirm it — `put` returns a new map without disturbing `?m`.

But the runtime (`Value::Map(handle)`) is an arena handle — mutable in implementation, hidden behind a functional spec. Proposal 037 §327 flags this as a known TODO ("Operations declare `Modify[their_value]` (TODO — currently silent for Map/Substitution; pure for Stream)"). Proposal 027.1 wants `empty` to carry `Modify[result]` for fresh-allocation tracking. The current file is mid-migration: neither fully persistent (lacks 027.1's allocator effect on `empty`) nor unified-with-mutable (no effect polymorphism).

If the project goal includes a mutable variant — a HashMap-style sort whose operations modify in place — then trying to share `Map` between both semantics forces:

| Aspect | PersistentMap | MutableMap |
|---|---|---|
| `put` return | `-> Map` | `-> Unit` |
| `put` effect | `()` | `Modify[m]` |
| Equality | by structure (`put(empty, k, v) = put(empty, k, v)`) | by handle (each `new` distinct) |
| Aliasing | value semantics | reference semantics |
| Time-travel ready (per 037 §330) | yes | no |

These are four real semantic differences, not an effect-row detail. Effect polymorphism (`empty() -> Map effects ?E`) can paper over the `empty` signature, but the `put` return-type difference cannot be hidden, and the equational laws can't be unified — `put(empty, k, v) = put(empty, k, v)` is true in column 1 and undefined in column 2.

The clean solution is **separate sorts with non-colliding operation names**, sharing only the read-only operations through a `MapReadable` abstraction. Each call site reads unambiguously: `with(m, k, v)` is functional, `set(m, k, v)` is mutating.

## Design

Three sorts. `MapReadable` carries the operations that are pure and identical in both variants. `PersistentMap` and `MutableMap` each `requires MapReadable` and add their own update operations with names that don't collide.

### Read-only abstraction

```anthill
sort anthill.prelude.MapReadable
  import anthill.prelude.{Option, Stream, Pair, Bool, Int, Eq}

  sort K = ?
  sort V = ?
  effects E = ?                       -- iteration effect row; bound by concrete sort (proposal 045 / WI-320 syntax)
  requires Eq[K]

  operation get(m: MapReadable, key: K) -> Option[V]
  operation contains(m: MapReadable, key: K) -> Bool
  operation size(m: MapReadable) -> Int
  operation keys(m: MapReadable) -> Stream[K, E]
  operation values(m: MapReadable) -> Stream[V, E]
  operation entries(m: MapReadable) -> Stream[Pair[K, V], E]

  rule contains(?m, ?k) = neq(get(?m, ?k), none)
end
```

Returns are `Stream` (the abstract lazy-sequence sort from `anthill.prelude.Stream`), not `List` — iteration over a map shouldn't force the whole element set into a materialised list. `Stream` is itself abstract: its internal representation is implementation-defined, so the concrete iteration shape (arena snapshot, lazy unfold, cursor over the underlying hash table) is hidden behind the Stream interface. The `E` parameter carries the iteration effect — pure (`()`) for snapshot or value-semantics iteration, or some concrete effect like `Error` for fallible streams.

Generic code parameterised over `MapReadable` accepts either concrete sort. Omitting `E` from the requires-binding leaves it as an anonymous logical variable, which makes the operation polymorphic over the iteration effect — `population_count` works on any map without committing to a particular effect:

```anthill
operation population_count(m: MapReadable, threshold: Int) -> Int
  requires MapReadable[K, Int]    -- E left implicit; polymorphic over iteration effect
  = …
```

If the generic operation actually consumes the stream returned by `keys`/`values`/`entries`, it inherits the iteration effect through its own row — proposal 045 covers the row-polymorphism mechanism. Generic code that only consults `get`/`contains`/`size` is unaffected.

### Persistent (functional) variant

```anthill
sort anthill.prelude.PersistentMap
  import anthill.prelude.{MapReadable, Eq}

  sort K = ?
  sort V = ?
  requires Eq[K]
  requires MapReadable[K, V, ()]              -- iteration over a persistent map is pure

  -- Construction
  operation empty() -> PersistentMap

  -- Functional update — no effects, returns a new map
  operation with(m: PersistentMap, key: K, value: V) -> PersistentMap
  operation without(m: PersistentMap, key: K) -> PersistentMap

  -- Laws
  rule get(empty, ?) = none
  rule get(with(?m, ?k, ?v), ?k) = some(?v)
  rule get(with(?m, ?k2, ?v), ?k) = get(?m, ?k)
    :- neq(?k, ?k2)
  rule without(empty, ?) = empty
  rule get(without(?m, ?k), ?k) = none
  rule size(empty) = 0
end
```

`empty` declares no effects — two `empty()` results denote the same persistent map by structural equality. This is value-level referential transparency, which makes `PersistentMap.empty` bare-callable after proposal 039 Phase 2 and admissible as a `const` body under the same proposal (though `empty()` at the use site is usually just as readable; the const buys a name, nothing more).

The runtime may still allocate fresh arena slots per `empty()` call as an implementation detail — but the spec demands those slots compare structurally equal, so the implementation is bound to the persistent semantics rather than free to expose handle identity.

### Mutable variant

```anthill
sort anthill.prelude.MutableMap
  import anthill.prelude.{MapReadable, Eq, Unit}

  sort K = ?
  sort V = ?
  effects E = ?                               -- iteration effect row; concrete impl picks snapshot vs live
  requires Eq[K]
  requires MapReadable[K, V, E]

  -- Construction (allocator — per 027.1)
  operation new() -> MutableMap
    effects Modify[result]

  -- In-place mutation
  operation set(m: MutableMap, key: K, value: V) -> Unit
    effects Modify[m]
  operation delete(m: MutableMap, key: K) -> Unit
    effects Modify[m]
  operation clear(m: MutableMap) -> Unit
    effects Modify[m]
end
```

The mutating operations return `Unit`; their effect on `m` is described by post-conditions over `get(m, k)` rather than equational rewrites:

```anthill
ensures get(m, key) = some(value)            -- on set(m, key, value)
ensures get(m, key) = none                   -- on delete(m, key)
```

(Hoare-style spec language for stateful resources is its own design question; see 037 and 045.)

## Naming rationale

`with` / `without` for PersistentMap mirror Clojure's `assoc` / `dissoc` and Scala's `+` / `-` (immutable.Map). The verbs read as functional: "the map *with* k → v," "the map *without* k." Alternatives considered:

- `put` / `remove` — match Java's `Map`, but `put` is the canonical mutating verb in most languages; using it for the functional variant invites the wrong mental model.
- `updated` / `removed` (Scala) — explicit past participles, but wordier.
- `insert` / `delete` — read as imperative.

`new` / `set` / `delete` for MutableMap mirror Rust (`HashMap::new`, `insert`) and Java (`put`, `remove`) — though MutableMap's `set` deliberately picks a name distinct from Java's `put` to avoid any cross-contamination with PersistentMap signatures.

The cross-sort name table:

| Action | PersistentMap | MutableMap |
|---|---|---|
| construct empty | `empty() -> PersistentMap` | `new() -> MutableMap effects Modify[result]` |
| add a binding | `with(m, k, v) -> PersistentMap` | `set(m, k, v) -> Unit effects Modify[m]` |
| drop a binding | `without(m, k) -> PersistentMap` | `delete(m, k) -> Unit effects Modify[m]` |
| empty out | use `empty()` | `clear(m) -> Unit effects Modify[m]` |

No name appears in both columns; readers never need to consult the type to know which shape they're reading.

## Migration of existing `Map` users

Today's `anthill.prelude.Map` is the persistent shape, so the rename is straightforward but wide-blast-radius. Audit (from the current stdlib + examples):

- `stdlib/anthill/persistence/` — uses `Map` in store-related operations.
- `stdlib/anthill/realization/` — uses `NamespaceMapping` which carries `Map`.
- `stdlib/anthill/reflect/` — uses `Map` in some query operations.
- `examples/github-todo/`, `examples/webots-modelling/lf1/` — uses `Map`.
- `rustland/anthill-core/src/` — references `Map` symbols for builtin dispatch.

Two migration shapes:

1. **Rename `Map` → `PersistentMap` everywhere, rename `put` → `with`, `remove` → `without`.** Mechanical pass; every user touched. The rename of `put` is the more disruptive piece because the verb is in common use.

2. **Keep `Map` as a deprecated alias to `PersistentMap` for one release, but still rename `put` → `with` and `remove` → `without`.** Reduces blast radius on the sort name; the verb rename is unavoidable.

Recommendation: option 1. The verb rename is required either way; doing both renames at once produces a clean stdlib state and avoids leaving deprecated aliases lying around. Coordinate with a single PR.

## Interaction with other proposals

- **027.1 (allocator effects via `Modify[result]`)** — `MutableMap.new()` declares `Modify[result]` directly; `PersistentMap.empty()` has empty row. The 027.1 migration TODO at 037 §327 resolves cleanly to "split first, then `empty` lands on PersistentMap with no effects clause."
- **037 (anthill state model)** — MutableMap is a state-bearing arena resource (§Map[K, V] / Substitution / Stream in 037). PersistentMap is value-shaped. Each maps unambiguously to one of 037's resource categories.
- **039 (term-level constants)** — `const EMPTY_MAP: PersistentMap[Int, String] = empty()` is admissible (empty declared row, foldable body) once 039 Phase 3 lands. `const M: MutableMap[Int, String] = new()` is rejected by the §Validator (`new` has `effects Modify[result]`). Both outcomes are correct.
- **043 (simp-rewrite)** — PersistentMap's algebraic laws become rewrite rules under the simp framework. MutableMap has no rewrite-friendly laws (its semantics are over execution traces, not value equality).
- **045 (effect sets and expressions)** — MutableMap's `Modify[m]` effects participate in 045's row machinery; the `Modify[result]` discharge rule from 027.1 fires for `new`.
- **046 (region tracking and effect derive)** — MutableMap is the canonical region-aware resource. PersistentMap is not.

## Open questions

1. **Bridge operations between the variants?** A `freeze(m: MutableMap) -> PersistentMap effects Modify[m]` and `thaw(m: PersistentMap) -> MutableMap effects Modify[result]` pair is the standard "build mutably, then freeze for sharing" pattern (Haskell's `runST` over `STRef`, Rust's `Vec` → `Box<[T]>`, Clojure's transient/persistent split). Worth doing — defer to a follow-up once a concrete use case lands.

2. **`requires MapReadable` — sub-sort relation or algebraic dependence?** Today's `requires` in a sort body declares an algebraic dependence (the sort depends on another sort's algebra). For `MapReadable`'s read-only operations to be callable on a `PersistentMap` or `MutableMap` value, the resolver needs Implementation facts pairing each writable sort to `MapReadable`'s spec. Standard mechanism; just need to write the facts. Confirm this is the intended pattern rather than introducing a new sub-sort relation.

3. **Naming — `MapReadable` vs alternatives.** Considered: `MapView` (Java-flavoured, but `View` usually implies "non-owning reference into another container"), `ReadOnlyMap` (clear but ugly), `MapQuery` (signals read-only but conflicts with proposal 010's query language). `MapReadable` reads as "any map you can read from" — a capability adjective applied to the noun. Pick the one that reads best.

4. **Scope — only Map, or List/Set/Vector too?** The same split applies in principle:
   - `ListReadable` / `PersistentList` / `MutableList`
   - `SetReadable` / `PersistentSet` / `MutableSet`
   - `VectorReadable` / `PersistentVector` / `MutableVector` (or use `MutableList` for both)
   
   Recommend doing only Map in this proposal; List/Set/Vector follow the same template once Map lands and the pattern is validated.

5. **Should the runtime really back PersistentMap differently from today's arena?** Today's arena gives a fresh handle per `empty()`, identical handles for identical contents only if explicit interning runs. For PersistentMap's spec to hold (`empty = empty`), either the arena must intern empties (cheap — one shared empty handle) or the runtime equality has to look through handles to structural content. Both work; pick one. The Haskell-style "share the empty constructor" route is simplest.

6. **Promote to associated iter carriers (Level 2)?** This proposal returns `Stream[K, E]` from `keys`/`values`/`entries`. The concrete iteration shape (arena snapshot, lazy unfold, hash-table cursor) hides behind Stream's abstract sort — sufficient hiding for the common case. A more abstract design declares iterator carriers as sort parameters of MapReadable itself (`sort KeysIter = ?`, `requires Iteration[KeysIter, K, E]`, `keys -> KeysIter`), letting each concrete sort pick a carrier that doesn't have to satisfy Stream — useful for parallel/chunked/disk-backed iterators whose natural shape doesn't fit the sequential `Option[(T, Stream)]` contract. The promotion is backward-incompatible at the spec boundary but only affects the typeclass declaration; concrete map sorts gain a few `requires` lines and client code over MapReadable keeps compiling. Defer until a real driver appears (concurrent or paged map).

## Phasing

Each phase lands independently with its own tests.

**Phase 1 — `MapReadable`.** Add `stdlib/anthill/prelude/map_readable.anthill` with the read-only operations and the `contains` law. No Implementation facts yet. Test: file loads, exports resolve.

**Phase 2 — `PersistentMap`.** Add `stdlib/anthill/prelude/persistent_map.anthill` with `empty` / `with` / `without` and the algebraic rules. Implementation fact pairs it to `MapReadable`. Test: existing Map functional-update tests, ported with the new names.

**Phase 3 — rename of existing `Map` users.** Mechanical pass over `stdlib/anthill/persistence/`, `stdlib/anthill/realization/`, `stdlib/anthill/reflect/`, examples, and any Rust builtin dispatch. Remove the original `stdlib/anthill/prelude/map.anthill` once all callers are updated.

**Phase 4 — `MutableMap`.** Add `stdlib/anthill/prelude/mutable_map.anthill` with allocator + mutating operations. Implementation fact pairs to `MapReadable`. Wire up the arena machinery for the new `MutableMap` carrier in the Rust runtime. Test: full mutable lifecycle (new → set → get → delete → clear) under effect tracking.

**Phase 5 (deferred).** Bridge operations (`freeze`, `thaw`) when the first concrete need appears.
