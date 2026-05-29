# Library: Iteration / Collection — read, persistent-build, mutable-build split

## Status

Draft 2026-05-29. Second proposal under `docs/proposals/library/`. Surfaced by [`001-map.md`](001-map.md): Map's `MapReadable` / `PersistentMap` / `MutableMap` is the *keyed* instance of a split the sequence/collection traits should also carry.

## Motivation

Today `stdlib/anthill/prelude/` has two collection traits:

- **`Iteration`** — `split(i: Iterator) -> Option[(Element, Iterator)] effects Effect`. The carrier is its own iterator: splitting yields the head element and the rest-of-same-type.
- **`Collection`** — `requires Iteration[Iterator = Collection, …]` plus `insert(c, elem) -> Collection effects Effect` and `empty() -> Collection`.

`List` provides both (`fact Collection[…]`, `fact Iteration[…]`, with `insert = cons`, `empty = nil`, `split` by pattern match).

Two gaps:

1. **`Collection`'s build is functional.** `insert -> Collection` returns a *new* collection, leaving the input untouched. So `Collection` is really the *persistent* builder — but its name doesn't say so, and there is **no trait for an in-place builder**, even though `MutableMap` ([001-map](001-map.md)) already needs exactly that shape: `new` (allocator), in-place `insert`/`set`, `setMany`.
2. **The names don't line up with `001-map`'s `…Readable` / `Persistent…` / `Mutable…` scheme**, so the parallel between maps and sequences is invisible — a reader who learns the map split learns nothing transferable about collections.

This proposal makes the collection hierarchy the same three-layer split as Map.

## Design

| layer | trait | carrier is its own iterator? | map analog ([001-map](001-map.md)) |
|---|---|---|---|
| read / iterate | `Iteration` (the "CollectionRead" layer) | — (it *is* the iterator) | `MapReadable` |
| persistent build | `PersistentCollection` *(rename of `Collection`)* | yes — as `List` is | `PersistentMap` |
| mutable build | `MutableCollection` *(new)* | no — see below | `MutableMap` |

As with Map, the relationship between a concrete sort and these traits is **provides** (a satisfaction `fact` + operation bodies), never `requires`; `requires` is reserved for genuine dependencies and for the superclass constraint *inside* a trait declaration (`PersistentCollection requires Iteration`). See [001-map §Alignment](001-map.md) and its Open Q 2.

There is **no umbrella `Collection` supertrait** — `Iteration` is the shared read layer, exactly as `MapReadable` is for maps (where no umbrella `Map` exists).

### Read layer — `Iteration` (unchanged)

`Iteration` stays as it is: the iterator capability. `split` decomposes a carrier into element + rest-of-same-type; a carrier *provides* it via `fact Iteration[Iterator = C, Element = …]` + a `split` body. `List` and `Stream` are iterators.

This is the read layer the user calls "CollectionRead." Whether it is renamed `CollectionReadable` for surface symmetry with `MapReadable` is Open Q 1; the capability is the same either way.

### Persistent builder — `PersistentCollection`

Today's `Collection`, renamed, with the carrier parameter renamed `Collection → C` to match `IndexedSeq`/the new trait. Functional build; `requires Iteration` over itself — a persistent collection can cheaply produce its rest, so it *is* its own iterator:

```anthill
sort anthill.prelude.PersistentCollection
  import anthill.prelude.Iteration

  sort C = ?
  sort Element = ?
  effects Effect = ?
  requires Iteration[Iterator = C, Element, Effect]   -- persistent ⇒ may be its own iterator

  operation insert(c: C, elem: Element) -> C    effects Effect
  operation empty() -> C
end
```

`List` provides it: `fact PersistentCollection[C = List[T], Element = T]`, `insert = cons`, `empty = nil`. `PersistentMap` provides it with `Element = Pair[K, V]` (`insert(m, pair(k, v)) = with(m, k, v)`).

### Mutable builder — `MutableCollection` (new)

In-place build. The allocator `new` carries `Modify[result]` (proposal 027.1); `insert`/`clear` mutate in place and return `Unit`:

```anthill
sort anthill.prelude.MutableCollection
  import anthill.prelude.{Unit, Stream}

  sort C = ?
  sort Element = ?
  effects E = ?                       -- read/access effect (snapshot vs live cursor)

  operation new() -> C                         effects Modify[result]
  operation insert(c: C, elem: Element) -> Unit   effects Modify[c]
  operation clear(c: C) -> Unit                effects Modify[c]

  -- read side: a mutable collection is *iterable* (produces a Stream),
  -- not its own iterator — see below
  operation stream(c: C) -> Stream[Element, E]
end
```

Why `MutableCollection` does **not** `requires Iteration[Iterator = C]`: `Iteration.split` returns the rest-of-same-type — it *consumes* the carrier. For a mutable collection, "splitting consumes the collection" is the wrong semantics (iterating would empty the container). So a mutable collection is *iterable*: it produces a `Stream` (a snapshot or a cursor) via `stream`, and the **`Stream`** is the `Iteration` witness. This is the Rust `IntoIterator` vs `Iterator` distinction, and the same call [001-map](001-map.md) made for `MutableMap` (which reads via `entries -> Stream`, not by self-splitting).

## Relationship to `Stream` and `IndexedSeq`

- **`Stream`** is itself an `Iteration` (`splitFirst` *is* `split`). It is the iterable bridge for any carrier that should not self-consume — the return type of `MutableCollection.stream` and of `MapReadable.entries`/`keys`/`values`.
- **`IndexedSeq`** (`length` + `nth`) is a *read refinement* — random access by position — orthogonal to the build axis. Both a persistent and a mutable carrier may additionally provide `IndexedSeq`; it neither requires nor is required by the build traits.

## Migration

Small blast radius: only `collection.anthill` (defines the trait) and `list.anthill` (provides it) mention these today.

1. **Rename** `sort Collection → PersistentCollection` in `collection.anthill`; rename the carrier parameter `Collection → C`.
2. **Update `list.anthill`**: `fact Collection[Collection = List[T], Element = T]` → `fact PersistentCollection[C = List[T], Element = T]`; update the `import` and the `Collection.insert`/`Collection.empty` comments.
3. **Add `mutable_collection.anthill`** with `MutableCollection`.
4. **Retarget [001-map](001-map.md)**: `PersistentMap`'s `fact Collection[…]` becomes `fact PersistentCollection[…]`, and `MutableMap` gains `fact MutableCollection[…]` once a mutable carrier lands.

The `Collection → PersistentCollection` rename of the trait name is the wide-feeling but mechanically tiny part; do it in one PR.

## Interaction with other proposals

- **[001-map](001-map.md)** — the keyed instance. `PersistentMap` provides `PersistentCollection`; `MutableMap` provides `MutableCollection`; both provide `MapReadable` (the keyed read layer, richer than `Iteration` because maps have key lookup).
- **027.1 (allocator effects)** — `MutableCollection.new()` declares `Modify[result]`; the discharge rule fires the same as for `MutableMap.new`.
- **045 / WI-320 (effect rows)** — `Effect`/`E` are effect-row parameters; the pure binding `{}` follows `List`'s **WI-301** caveat (`Effect = {}` not yet expressible as a type argument, so it is omitted, leaving the row unbound = pure).
- **037 (state model)** — `MutableCollection` carriers are state-bearing arena resources; `PersistentCollection` carriers are value-shaped.
- **`IndexedSeq` (existing)** — orthogonal read refinement, unaffected.

## Open questions

1. **Read-layer name — keep `Iteration`, or `CollectionReadable`?** `Iteration` is the *iterator* concept (self-consuming `split`). `MapReadable` is a *readable container* (random access + produces iterators) — strictly richer. For un-keyed sequences "readable ≈ iterable," so `Iteration` may suffice. *Recommend keeping `Iteration`* and not minting `CollectionReadable` unless a sequence read-capability beyond iteration (e.g. `size`/`contains` as primitives rather than folds) earns its own trait.

2. **A shared `Iterable` bridge?** `MutableCollection.stream(c) -> Stream` produces an iterator without consuming. Should that be its own shared trait — `Iterable`/`Streamable` with `stream(c) -> Stream[Element, E]` — that *both* persistent and mutable carriers provide (the `IntoIterator` analog), rather than an ad-hoc op on `MutableCollection`? This would also give persistent collections one uniform iteration path (Q 3).

3. **Does `PersistentCollection` need self-`Iteration` at all?** It currently `requires Iteration[Iterator = C]` (self-split), matching `List`. If the `Iterable` bridge (Q 2) exists, persistent collections could iterate through it too, giving a single iteration path across both builders. Keeping self-split is cheap for persistent carriers; uniformity argues against it. Decide together with Q 2.

4. **`MutableCollection.insert` return value.** It returns `Unit`. The keyed analog `setMany` returns the count newly inserted ([001-map](001-map.md) Open Q 10) and `deleteMany` the count removed; for consistency a `MutableCollection` might return `Bool` ("was new") from `insert`. Defer with the same reasoning as 001-map Open Q 9/10 — keep `Unit` until a caller wants the witness.

5. **No umbrella.** Confirmed mirror of Map: no `Collection` supertrait over the persistent/mutable builders; `Iteration` (or the Q 2 `Iterable`) is the only shared layer. Flag here only so the absence is deliberate, not an oversight.

## Phasing

Each phase lands independently with its own tests.

**Phase 1 — rename.** `Collection → PersistentCollection` (+ carrier `Collection → C`) in `collection.anthill`; update `list.anthill`'s `fact`/imports. Test: `list.anthill` loads, the `PersistentCollection` fact resolves, existing List tests pass.

**Phase 2 — `MutableCollection`.** Add `mutable_collection.anthill`. No carriers yet. Test: file loads, exports resolve.

**Phase 3 — first mutable carrier.** A concrete mutable sequence (a `MutableList`, or `MutableMap` from 001-map with `Element = Pair[K, V]`) provides `MutableCollection`; wire the arena. Test: full mutable lifecycle under effect tracking.

**Phase 4 (optional) — `Iterable` bridge.** If Open Q 2 resolves yes, introduce the shared `stream`-producing trait and route both builders through it.
