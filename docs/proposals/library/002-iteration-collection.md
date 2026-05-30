# Library: Iteration / Collection — read, persistent-build, mutable-build split

## Status

Draft 2026-05-29. Second proposal under `docs/proposals/library/`. Surfaced by [`001-map.md`](001-map.md): Map's `MapReadable` / `PersistentMap` / `MutableMap` is the *keyed* instance of a split the sequence/collection traits should also carry. Open questions were settled in design discussion: read layer keeps the name `Iteration` (Q 1); shared `Iterable` bridge whose `iterator` returns a `Stream` (Q 2); persistent collections provide rather than self-iterate (Q 3); `insert` returns `Bool` "was new" (Q 4); no umbrella supertrait (Q 5).

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

Four traits in two pairs — a read pair (consume / produce) and a build pair (persistent / mutable):

| role | trait | what it is | map analog ([001-map](001-map.md)) |
|---|---|---|---|
| iterator (consume) | `Iteration` | a thing you `split` into element + rest | (`Stream`) |
| **iterable (produce)** | **`Iterable`** *(new)* | `iterator(c) -> Stream` — the shared "can be walked" layer | `MapReadable` (via `entries`) |
| persistent build | `PersistentCollection` *(rename of `Collection`)* | functional `empty` / `insert` | `PersistentMap` |
| mutable build | `MutableCollection` *(new)* | in-place `new` / `insert` | `MutableMap` |

As with Map, the relationship between a concrete sort and these traits is **provides** (a satisfaction `fact` + operation bodies), never `requires`; `requires` is reserved for genuine dependencies and for the superclass constraint *inside* a trait declaration. See [001-map §Alignment](001-map.md) and its Open Q 2.

`Iterable` is the shared read layer both builders sit on — the analog of `MapReadable` for maps. There is **no umbrella `Collection` supertrait**: `Iterable` is the only thing the two builders have in common.

### Iterator vs iterable — `Iteration` and `Iterable`

`Iteration` is the low-level **iterator**: `split(i) -> Option[(Element, Iterator)]`, the carrier consuming itself one element at a time. `Stream` provides it (`splitFirst` *is* `split`); so does `List`.

`Iterable` is the new shared **"can be walked"** capability — it *produces* an iterator rather than *being* one:

```anthill
sort anthill.prelude.Iterable
  import anthill.prelude.Stream

  sort C = ?                          -- carrier (the collection)
  sort Element = ?
  effects E = ?                       -- iteration/access effect (rides on the produced Stream)

  operation iterator(c: C) -> Stream[Element, E]
end
```

`iterator` returns a `Stream`. Because `Stream` is abstract, the concrete shape is the carrier's to pick — a persistent list returns a stream that is a bare pointer into itself; a mutable collection returns a snapshot or a live cursor; the host pays no boxing it doesn't need. The `iterator` call carries no effect of its own (like `MapReadable.entries`); the access effect `E` lives on the returned `Stream` and is paid on consumption.

This split is the Rust `IntoIterator` (produce) vs `Iterator` (consume) distinction. It is what lets a **mutable** collection be walked without "splitting consumes the container": a mutable carrier never self-`split`s — it hands out a `Stream` and the `Stream` is the `Iteration` witness.

### Persistent builder — `PersistentCollection`

Today's `Collection`, renamed, with the carrier parameter renamed `Collection → C`. Functional build, and it `requires Iterable` (not self-`Iteration`) — every collection can be walked through the one shared interface:

```anthill
sort anthill.prelude.PersistentCollection
  import anthill.prelude.Iterable

  sort C = ?
  sort Element = ?
  effects Effect = ?
  requires Iterable[C = C, Element, E = Effect]   -- a built collection can be walked

  operation insert(c: C, elem: Element) -> C    effects Effect
  operation empty() -> C
end
```

`List` provides it: `fact PersistentCollection[C = List[T], Element = T]`, `insert = cons`, `empty = nil`, and `fact Iterable[C = List[T], Element = T]` with `iterator(l)` a stream over `l`. `PersistentMap` provides it with `Element = Pair[K, V]` (`insert(m, pair(k, v)) = with(m, k, v)`).

### Mutable builder — `MutableCollection` (new)

In-place build, and it too `requires Iterable`. The allocator `new` carries `Modify[result]` (proposal 027.1); `insert`/`clear` mutate in place and return `Unit`:

```anthill
sort anthill.prelude.MutableCollection
  import anthill.prelude.{Unit, Bool, Iterable}

  sort C = ?
  sort Element = ?
  effects E = ?
  requires Iterable[C = C, Element, E]   -- reads go through the shared Iterable.iterator -> Stream

  operation new() -> C                         effects Modify[result]
  operation insert(c: C, elem: Element) -> Bool   effects Modify[c]   -- true if newly added (collection changed)
  operation clear(c: C) -> Unit                effects Modify[c]
end
```

Both builders `requires Iterable` rather than `Iteration`: a mutable collection must not be its own self-consuming iterator (`split` returning the rest-of-same-type would mean "walking empties the container"), and routing the persistent side through the same `Iterable` gives one uniform iteration path instead of two trait shapes (Open Q 3, resolved: persistent collections *provide* `Iterable`, they are not required to self-`Iterate`).

## Relationship to `Stream` and `IndexedSeq`

- **`Stream`** is itself an `Iteration` (`splitFirst` *is* `split`), and it is what `Iterable.iterator` returns — the bridge for any carrier that should not self-consume, the same type `MapReadable.entries`/`keys`/`values` already return. (`Stream` trivially provides `Iterable` too: `iterator(s) = s`.)
- **`IndexedSeq`** (`length` + `nth`) is a *read refinement* — random access by position — orthogonal to the build axis. Both a persistent and a mutable carrier may additionally provide `IndexedSeq`; it neither requires nor is required by the build traits.

## Migration

Small blast radius: only `collection.anthill` (defines the trait) and `list.anthill` (provides it) mention these today.

1. **Add `iterable.anthill`** with the `Iterable` trait. Have `Stream` provide it (`iterator(s) = s`).
2. **Rename** `sort Collection → PersistentCollection` in `collection.anthill`; rename the carrier parameter `Collection → C`; change `requires Iteration[Iterator = C, …]` → `requires Iterable[C = C, …]`.
3. **Update `list.anthill`**: `fact Collection[Collection = List[T], Element = T]` → `fact PersistentCollection[C = List[T], Element = T]`; add `fact Iterable[C = List[T], Element = T]` with an `iterator` body (a stream over the list — `List`'s existing `split` can back it). Update imports.
4. **Add `mutable_collection.anthill`** with `MutableCollection`.
5. **Retarget [001-map](001-map.md)**: `PersistentMap`'s `fact Collection[…]` becomes `fact PersistentCollection[…]`; `MapReadable` already returns `Stream` from `entries`, so a map provides `Iterable` (`iterator(m) = entries(m)`) for free; `MutableMap` gains `fact MutableCollection[…]` once a mutable carrier lands.

The `Collection → PersistentCollection` rename of the trait name is the wide-feeling but mechanically tiny part; do it in one PR.

**Build gotcha:** new prelude files must be registered in the two embedded-stdlib lists (`rustland/anthill-cli/src/stdlib_embedded.rs` and `rustland/anthill-todo/src/stdlib_embedded.rs`) — the `include_str!` bundles the CLIs ship, distinct from the dir-scan the `anthill-core` tests use. A file present on disk but absent from those lists loads fine under test yet fails to resolve in the CLI bundle.

**Status (2026-05-30):** steps 1–4 *declarations* + the rename have landed (`iterable.anthill`, `mutable_collection.anthill`, `collection.anthill`, `list.anthill`, both embedded lists). **WI-344** (provider admissibility in `type_compatible`) has also landed (on `main`) — the typer now admits a value where a spec it *provides* is expected, the enabler for every provider here. Remaining to land: carriers actually *providing* `Iterable` (`Stream` and `List` via the `iterator` body; the map provision in [001-map](001-map.md)), plus the soundness gate below.

A `List` *is* a `Stream` — it can declare `fact Stream[List]` (its `split` is `splitFirst`), so `iterator(xs) = xs` is the right body. The typer used to reject this: `types_compatible(List, Stream)` returned false (`expected Stream, got List`) because it matched types only nominally + the `requires`-chain and never consulted the `fact Stream[List]` provision. **WI-344** fixed exactly that — admitting a value where a spec it *provides* is expected, the same demand→search that discharges a `requires`, run at the value position — so the providers now typecheck.

What remains is **soundness**, not typing. Today `List` provides `PersistentCollection` (which `requires Iterable`) without providing `Iterable`, and that unmet requirement loads silently because a spec-level `requires` with no provider is not diagnosed (**WI-343**, open). Adding the `Iterable` provision closes that instance, but the `fact Stream[List]` it leans on is itself trusted-not-checked: `Stream`'s `takeN`/`collect` have no derived rules, so a carrier can claim `Stream` without backing the full op set. WI-343 + op-provision completeness are the companion track that makes the facts the typer trusts actually *true*.

**Implementation surface.** The read/persistent half is **stdlib-only**: the `fact`/`operation` provisions need no compiler or interpreter change, because WI-344 (the one required typer change) has landed. The soundness gate (WI-343) is a small loader/typer diagnostic. Only **Phase 4** (the first mutable carrier) needs real compiler + interpreter work — `Modify[result]`/`Modify[c]` effect tracking and arena resources (027.1, 037); and running a walk end-to-end (rather than just loading/typechecking it) additionally needs the runtime side of provider dispatch (WI-281).

## Interaction with other proposals

- **[001-map](001-map.md)** — the keyed instance. `PersistentMap` provides `PersistentCollection`; `MutableMap` provides `MutableCollection`; both provide `MapReadable` (the keyed read layer, richer than `Iteration` because maps have key lookup).
- **027.1 (allocator effects)** — `MutableCollection.new()` declares `Modify[result]`; the discharge rule fires the same as for `MutableMap.new`.
- **045 / WI-320 (effect rows)** — `Effect`/`E` are effect-row parameters; the pure binding `{}` follows `List`'s **WI-301** caveat (`Effect = {}` not yet expressible as a type argument, so it is omitted, leaving the row unbound = pure).
- **037 (state model)** — `MutableCollection` carriers are state-bearing arena resources; `PersistentCollection` carriers are value-shaped.
- **`IndexedSeq` (existing)** — orthogonal read refinement, unaffected.

## Open questions

1. *(Resolved — keep `Iteration`)* **Read-layer name.** `Iteration` is the *iterator* concept (self-consuming `split`); `Iterable` already supplies the "readable/walkable" verb on top of it. No `CollectionReadable` is minted — it would only be warranted if a sequence read-capability beyond iteration (e.g. `size`/`contains` as primitives rather than folds) earned its own trait, which nothing yet needs.

2. *(Resolved)* **Shared iteration interface — yes, `Iterable`.** Both builders `requires Iterable`, and `iterator(c) -> Stream[Element, E]` — every carrier produces a `Stream`. `Stream` is the iterator type; that is the whole shared read interface.

3. *(Resolved)* **`PersistentCollection` does not self-`Iterate`.** It `requires Iterable` like the mutable builder; one uniform iteration path. A persistent carrier *may* still be its own `Iteration` as an internal convenience (cheap `split`), but that is an implementation detail behind its `iterator`, not a hierarchy requirement.

4. *(Resolved — `Bool`)* **`MutableCollection.insert` return value.** Returns `Bool` = "was the element new" (the collection changed) — Java `Collection.add` / Rust `HashSet::insert`: `false` when a set-like carrier already held it, vacuously `true` for a list/bag. This is the singular shadow of `setMany`'s "count newly inserted": singular ops return the witness, batched ops return the count. **Consequence for [001-map](001-map.md):** when `MutableMap` provides `MutableCollection` (`insert(m, pair(k, v))`), the "was new" bit must come from somewhere. The native `set` already knows whether it overwrote; recomputing it with a separate `contains` before `set` costs an extra read — fatal on a DB carrier. So `MutableMap.set` should likewise return `Bool` ("was the key new"), and by symmetry `delete -> Bool` ("was present") — i.e. 001-map Open Q 9 resolves *yes*. That alignment is 001-map's to make.

5. *(Resolved — no umbrella)* **`Iterable` is the only shared layer.** No `Collection` supertrait over the persistent/mutable builders; `Iterable` is the single thing they share, mirroring `MapReadable` for maps. Deliberate, not an oversight.

## Phasing

Each phase lands independently with its own tests.

**Phase 1 — `Iterable`.** Add `iterable.anthill` (`iterator(c) -> Stream[Element, E]`); have `Stream` provide it. Test: file loads, exports resolve.

**Phase 2 — rename + reparent.** `Collection → PersistentCollection` (+ carrier `Collection → C`), and `requires Iteration` → `requires Iterable`, in `collection.anthill`; update `list.anthill` (`fact PersistentCollection`, add `fact Iterable`, imports). Test: `list.anthill` loads, both facts resolve, existing List tests pass.

**Phase 3 — `MutableCollection`.** Add `mutable_collection.anthill` (`requires Iterable`). No carriers yet. Test: file loads, exports resolve.

**Phase 4 — first mutable carrier.** A concrete mutable sequence (a `MutableList`, or `MutableMap` from 001-map with `Element = Pair[K, V]`) provides `MutableCollection` + `Iterable`; wire the arena. Test: full mutable lifecycle under effect tracking.
