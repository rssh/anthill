# Library: Finiteness as a type — `FiniteCollection` and `FiniteStream`

## Status

Draft 2026-06-29. Third proposal under `docs/proposals/library/`. Extends
[`002-iteration-collection.md`](002-iteration-collection.md). Surfaced by
**WI-585**: the eager consumers `count` / `foldRight` on `Stream` and
`size` / `foldRight` on `Iterable` *walk to the end of the carrier*, so they
diverge on an infinite stream — yet a `Stream` provides `Iterable`, so an
`Iterable` may be infinite. They do not belong on a maybe-infinite carrier.

Design discussion settled the shape: **finiteness is a TYPE**, not a
caller-asserted runtime obligation. A new abstract spec `FiniteCollection`
owns the eager consumers; a new carrier `FiniteStream` is a `Stream` that
additionally guarantees termination, so a *lazy* pipeline over a finite source
stays consumable.

## Motivation

Three eager operations consume a carrier *to its end*:

- **count / size** — walk every element, return how many.
- **collect** — walk every element, materialize them into a `List`.
- **foldLeft / foldRight** — walk every element, reduce to a value.

All of them **diverge on an infinite stream**. Today they live on `Stream`
(`count`, `foldLeft`, `foldRight`, `collect`) and on `Iterable`
(`size = count(iterator(c))`, `foldLeft`, `foldRight`). Both are wrong homes:
`Stream` is explicitly the *lazy, maybe-infinite* sequence, and `Iterable` is
satisfied by `Stream` (`Stream provides Iterable`), so neither can promise the
walk terminates.

The naïve fix — "move them to a `FiniteCollection` sort that carriers opt into"
— has a sharp edge that drove this proposal. `Iterable.map` / `Iterable.filter`
return a **lazy `Stream`** (a `MappedStream` / `FilteredStream` carrier — see
[`combinators.anthill`]). If the eager consumers live *only* on
`FiniteCollection`, then a mapped stream can no longer be collected, folded, or
sized, because a `MappedStream` provides `Stream`, not `FiniteCollection` —
mapping an infinite stream stays infinite. So `xs.map(f).size()` (the point of
`wi492`) and `collect(map([1,2,3], inc))` (`eval_test` wi064) stop type-checking.

The deeper cause: the static type *after* `map` is `Stream[Dst]`, which **erases
the source's finiteness**. Even though *this* mapped stream came from a finite
list, the type no longer says so, so a later consumer only sees a bare `Stream`.

The fix is to keep finiteness *in the type*: a finiteness-preserving `map` must
**return a finite type**, so the obligation is discharged structurally rather
than re-derived after the fact.

## Design

Three layers, mirroring the `Iterable` (capability) / `Stream` (carrier) split
that [002](002-iteration-collection.md) already established:

| role | spec / sort | what it is | analog |
|---|---|---|---|
| walk, maybe-infinite | `Stream` *(existing, trimmed)* | lazy sequence; `splitFirst` core only | — |
| **consume, finite** | **`FiniteCollection`** *(new)* | abstract spec: `collect` / `size` / `foldLeft` / `foldRight` | `Iterable` is to walking what this is to consuming |
| **lazy-but-finite carrier** | **`FiniteStream`** *(new)* | a `Stream` that also `provides FiniteCollection`; its **tail is a `FiniteStream`** | `Stream` is to `Iterable` what `FiniteStream` is to `FiniteCollection` |

`FiniteCollection` is the *capability* ("can be fully consumed"); `FiniteStream`
is a *carrier* that provides it lazily. Both are needed: `Map` is finite-and-
consumable but is **not** a stream, so the consumers must live on an abstract
spec (`FiniteCollection`) that both `Map` and the finite streams provide.

### The load-bearing invariant: a finite stream's tail is finite

This single fact is what makes the drain recursion well-typed again. `Stream`'s
`collect` recurses on a tail typed `Stream`:

```anthill
operation collect(s: Stream) -> List[T = s.T] =
  match splitFirst(s)
    case none() -> nil
    case some(pair(h, rest)) -> cons(head: h, tail: collect(rest))   -- rest : Stream
```

If `collect` lives on `FiniteCollection`, that recursive `collect(rest)` is
ill-typed — `rest` is a `Stream`, not a `FiniteCollection`. `FiniteStream` fixes
exactly this: its `splitFirst` returns a `FiniteStream` tail, so the recursion
type-checks:

```anthill
sort anthill.prelude.FiniteStream
  import anthill.prelude.{Stream, FiniteCollection, Option, Pair, List, Int64}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.List.{nil, cons}

  sort T = ?
  effects E = ?

  provides Stream[T, E]                                       -- IS a Stream (lazy core)
  provides FiniteCollection[C = FiniteStream, Element = T, E = E]   -- CAN be consumed

  -- The finiteness primitive: like Stream.splitFirst, but the tail is FINITE.
  operation splitFirst(s: FiniteStream) -> Option[Pair[A = s.T, B = FiniteStream[T = s.T, E = s.E]]] effects s.E

  -- collect is now a WELL-FOUNDED recursion — `rest` is itself a FiniteStream.
  operation collect(s: FiniteStream) -> List[T = s.T] effects s.E =
    match splitFirst(s)
      case none() -> nil
      case some(pair(h, rest)) -> cons(head: h, tail: collect(rest))   -- rest : FiniteStream ✓
end
```

A `FiniteStream` provides `Stream` by *weakening* its `splitFirst` (a finite
tail is still a `Stream` tail). That is a **covariant-return provision** — see
[Kernel dependencies](#kernel-dependencies).

### `collect` is the finiteness primitive

`FiniteCollection`'s defining operation is `collect` (body-less). A carrier
*proves* it is finite by supplying a terminating `collect`. `size` and the folds
derive from `collect` once, via `List`'s concrete operations:

```anthill
sort anthill.prelude.FiniteCollection
  import anthill.prelude.{Iterable, List, Int64}

  sort C = ?
  sort Element = ?
  effects E = ?
  requires Iterable[C = C, Element = Element, E = E]   -- a finite collection can still be walked

  -- The finiteness PRIMITIVE: materialize the whole collection into a List.
  -- Body-less; each carrier provides it. (You can only honor this if iteration
  -- terminates — that IS the finiteness guarantee.)
  operation collect(c: C) -> List[T = Element] effects E

  -- Derived eager consumers, over List's concrete ops on the materialized list.
  operation size(c: C) -> Int64 effects E = List.length(collect(c))
  operation foldLeft[Acc, EffP](c: C, init: Acc, f: (acc: Acc, x: Element) -> Acc @ {EffP}) -> Acc effects {E, EffP} =
    List.foldLeft(collect(c), init, f)
  operation foldRight[Acc, EffP](c: C, init: Acc, f: (x: Element, acc: Acc) -> Acc @ {EffP}) -> Acc effects {E, EffP} =
    List.foldRight(collect(c), init, f)
end
```

`size = count` from `Stream`, renamed: on a *guaranteed-finite* carrier the
property name `size` is finally appropriate — the very reason `Stream`'s comment
gave for *not* calling it `size` ("a property name would mislead… diverges on an
infinite stream") no longer applies.

### Carriers

- **`List`** `provides FiniteStream` (a list's tail is a list → finite). It thus
  provides `FiniteCollection` and `Stream` transitively. `List` keeps its own
  `length`, and gains concrete `foldLeft` / `foldRight` (recursion over `cons`),
  which the `FiniteCollection` default bodies call. `List.collect` is the
  identity (a list already *is* the materialized form).
- **`Map`** `provides FiniteCollection` directly (it is finite but not a stream):
  `collect(m) = entries(m)`. `Map` keeps its own O(1) `size` (overrides the
  default walk — the WI-444 carrier override).
- **Finite combinators** — `FiniteCollection.map` / `filter` return a
  **`FiniteStream`**, so a pipeline over a finite source stays lazy *and*
  consumable. `Stream.map` / `filter` keep returning a bare `Stream` for
  maybe-infinite sources. See next section.

### Finite-preserving `map` / `filter`

To make `xs.map(f).size()` type-check, the finite `map` must *return* a finite
type:

```anthill
operation map[Dst, EffP](c: FiniteCollection, f: (x: Element) -> Dst @ {EffP, -Modify[x]})
  -> FiniteStream[T = Dst, E = {E, EffP}]
```

The body produces a lazy mapped carrier whose **source field is itself a
`FiniteStream`**, so it *unconditionally* provides `FiniteStream` — the finiteness
is captured structurally in the field type, no conditional instance required:

```anthill
sort anthill.prelude.FiniteMappedStream
  entity fmapped(source: FiniteStream[Src, ES], fn: (Src) -> T @ {EF})   -- field is FiniteStream
  provides FiniteStream[T, {ES, EF}]                                     -- UNCONDITIONAL
  operation splitFirst(m: FiniteMappedStream) -> Option[Pair[A = T, B = FiniteMappedStream]] effects {ES, EF} = …
end
```

This is the **separate-finite-carrier** realization (recommended for the first
implementation). It duplicates the `MappedStream` / `FilteredStream`
`splitFirst` logic, but the duplication is honest: the finite carrier's field
type *is* the proof. The alternative — reusing the one `mapped` carrier with a
**conditional provision** ("a mapped stream is finite when its source is") — is
discussed under [Conditional provisions](#conditional-provisions); it needs more
machinery and is left as a future consolidation.

### What moves, what stays

| op | from | to |
|---|---|---|
| `count` → `size` | `Stream`, `Iterable` | `FiniteCollection` |
| `collect` | `Stream` | `FiniteCollection` (primitive) + `FiniteStream` (impl) |
| `foldLeft` | `Stream`, `Iterable` | `FiniteCollection` |
| `foldRight` | `Stream`, `Iterable` | `FiniteCollection` |
| `splitFirst`, `head`, `headOption`, `tail`, `takeN`, `find`, `isEmpty`, `iterator` | `Stream` | **stay** (lazy core) |
| `map`, `filter` (→ `Stream`) | `Iterable` / `Stream` | **stay** (lazy, maybe-infinite) |

`takeN` (bounded), `find` (short-circuits), `isEmpty` (one step) stay on
`Stream`: none requires reaching the end.

### Dispatch coherence

After the move, `xs.map(f)` on a `List` has two applicable providers: the lazy
`Iterable.map` (→ `Stream`) and the finite `FiniteCollection.map`
(→ `FiniteStream`). We want the finite one to win on a finite carrier, the lazy
one on a value that only provides `Stream` (a genuinely infinite stream, where
the result is correctly *not* consumable).

**The kernel's actual rule (verified) is provision-graph distance, NOT a
`requires`/sub-spec ranking.** When a carrier provides several specs that define
the same short name, `find_spec_op_for_provided_sort`
(`rustland/anthill-core/src/kb/typing.rs:2942-2993`) builds a BFS list of the
provided specs — *directly*-provided specs at the front, *transitively*-provided
behind — and takes the **first** that defines the name. (`requires` is never
consulted for ordering; the only "most-specific" *count* in the typer,
`pick_most_specific` at `typing.rs:8912`, ranks competing impls of the **same**
spec by number of ground bindings, which is a different question.)

This *plausibly* gives the right answer for free: if `List provides FiniteStream`
directly, then `FiniteCollection` is reached at BFS depth 1 (via `FiniteStream`)
while `Iterable` is at depth 2 (`FiniteStream → Stream → Iterable`), and `Stream`
itself defines no `map` — so `FiniteCollection.map` is found before
`Iterable.map`. But this is a **graph-shaping outcome to verify in Phase B**, not
a guarantee: if both `map`s ever land at equal BFS distance the lookup is
order-dependent, and the sibling impl-selection path raises an *ambiguity error*
on a tie. Phase B's job is to shape the `provides` graph so the finite op is
strictly closer (and add a test pinning it), or to give finite `map`/`filter` a
distinct resolution path. See [kernel dependency 2](#kernel-dependencies).

## Kernel dependencies

This proposal is *mostly* stdlib, but it leans on two typer/dispatch
capabilities that must be confirmed or built — discovering them up front is why
the design was written before the code:

1. **Covariant-return provision.** `FiniteStream` provides `Stream.splitFirst`
   via its own `splitFirst` with a *more specific* tail
   (`FiniteStream` ⊑ `Stream`). The provider-admissibility check
   (`type_compatible`, WI-344) must accept a refined return type, akin to
   operation-override refinement (proposal §8.7 / WI-347).
2. **Provider selection when two specs share an op name.** *Verified:* the kernel
   resolves this by **provision-graph distance** — `find_spec_op_for_provided_sort`
   (`typing.rs:2942-2993`) takes the first match in a BFS list with directly-
   provided specs ahead of transitively-provided ones. There is **no `requires`/
   sub-spec specificity ranking** (the `pick_most_specific` count at
   `typing.rs:8912` ranks impls of the *same* spec by ground-binding count — a
   different mechanism). So Phase B does **not** get to "FiniteCollection is more
   specific, it wins"; it must *shape the graph* so `FiniteCollection.map` is
   strictly closer than `Iterable.map` (depth 1 via `FiniteStream` vs depth 2 via
   `Stream → Iterable`), and pin it with a test, because equal distance is
   order-dependent / an ambiguity error. **Doc gap:** `kernel-language.md` §8.7
   documents coherence + override but is *silent* on this two-different-specs case
   — worth documenting once Phase B settles the rule.

## Conditional provisions

A tidier realization of finite `map`/`filter` would reuse the single `mapped`
carrier and declare *a mapped stream is finite exactly when its source is* —
Haskell's `instance Finite s => Finite (Mapped s)`.

Anthill does **not** support a rule-bodied `fact S[…] :- …` (the grammar, IR,
loader, and typer all handle only ground provider facts;
`collect_provides_candidates` skips any rule with a body and looks providers up
by functor index, never through SLD). It **does** support conditional instances
via the **witness-sort + `requires`** pattern, with a working precedent in
`wi224_sld_resolution_test`:

```anthill
sort EqList                 -- "List[A] is Eq WHEN A is Eq"
  sort A = ?
  requires Eq[T = A]
  fact Eq[T = List[T = A]]
end
```

The catch: the witness keys on a *type parameter*, but `mapped`'s `source` field
is typed `Stream` (not a parameter that preserves the source's finiteness), so a
constructed `mapped(…)` value erases the source finiteness exactly as `map`'s
return type does. Reusing one carrier therefore additionally requires
parameterizing it over its source *sort* — more machinery than the separate
finite carrier. Hence: **separate carriers first, conditional-instance
consolidation later.**

> **Doc-fix (separate WI):** `docs/design/operation-call-model.md:551` claims
> `fact Eq[T = List[?A]] :- Eq[?A]` "already works via Horn-clause facts; SLD
> resolution handles it natively." That is **inaccurate** against the
> implementation and should be corrected to the witness-sort pattern.

## Migration

The move must land in **both** the spec and the Rust host. The `Stream` trait is
generated from `stream.anthill` (WI-553, `anthill-stl/build.rs` →
`OUT_DIR/stream.rs`); removing `count`/`foldLeft`/`foldRight`/`collect` from the
spec regenerates a trimmed trait, so the matching impls in
`SearchStreamAdapter` (`anthill-stl/src/reflect/bridge.rs`: `count`,
`fold_right`, and `collect` — `fold_left` goes too) must be removed in the same
change, and the `fold_solutions` helper retired if nothing else uses it.

Callers to rewire: `map.anthill`, `iterable.anthill`, `stream.anthill`,
`list.anthill`, `combinators.anthill`; tests `wi424_iterable_members_test`,
`eval_test` (wi064), `wi492_transitive_provision_test`. New prelude files
(`finite_collection.anthill`, `finite_stream.anthill`, finite combinators) must
be added to the two embedded-stdlib lists
(`rustland/anthill-cli/src/stdlib_embedded.rs`,
`rustland/anthill-todo/src/stdlib_embedded.rs`) — a file on disk but absent from
those lists loads under test yet fails in the CLI bundle (the 002 gotcha).

## Phasing

Ordered so **every phase keeps the suite green** — additive first, removal last.

**Phase A — add the sorts (WI-585, re-scoped).** Add `FiniteCollection`
(`collect` primitive + `size`/`foldLeft`/`foldRight` defaults) and `FiniteStream`
(provides `Stream` + `FiniteCollection`). `List provides FiniteStream`; `Map
provides FiniteCollection`; `List` gains concrete `foldLeft`/`foldRight`.
**Nothing is removed** — `Stream`/`Iterable` keep their consumers, so all
existing tests still pass. Test: stdlib loads; `FiniteCollection.size`/folds and
`collect` eval on a `List` and a `Map`. Depends on the covariant-return
provision (kernel dep 1) for `FiniteStream provides Stream`.

**Phase B — finite combinators + coherence.** Add `FiniteCollection.map`/`filter`
returning `FiniteStream`, with the finite mapped/filtered carriers. Resolve
most-specific-provider dispatch (kernel dep 2). Rewire `wi492` to the finite
path (`xs.map(inc).size()` now goes List → FiniteStream → size). Test: finite
pipelines type-check and eval; an infinite-stream consume is rejected.

**Phase C — remove the unsound homes.** Delete `count`/`foldLeft`/`foldRight`/
`collect` from `Stream` and `size`/`foldLeft`/`foldRight` from `Iterable`;
regenerate the `Stream` trait; drop the `bridge.rs` adapter impls. Rewire
`eval_test` wi064 and `wi424_iterable_members_test` to the `FiniteCollection`
ops. Test: full suite green; the removed ops are gone from the generated trait.

**Phase D — consolidation (optional).** Replace the separate finite carriers
with the conditional-provision reuse, once source-sort-parameterized carriers
land. Pure cleanup; no capability change.

## Interaction with other proposals

- **[002-iteration-collection](002-iteration-collection.md)** — this is its
  consume-layer completion: `Iterable` is the *walk* capability,
  `FiniteCollection` is the *consume* capability; `Stream` is to `Iterable` what
  `FiniteStream` is to `FiniteCollection`.
- **[001-map](001-map.md)** — `Map` provides `FiniteCollection`
  (`collect = entries`); its own `size` overrides the default walk.
- **045 / WI-320 (effect rows)** — `E` / `EffP` are effect-row parameters; the
  pure binding `{}` follows `List`'s existing convention.
- **§8.7 / WI-347 (override & coherence)** — supplies most-specific dispatch and
  covariant-return refinement (the two kernel deps).
- **WI-553 (generated `Stream` trait)** — removing ops regenerates the trait;
  the `bridge.rs` adapter impls track it.

## Open questions

1. *(Leaning: both)* **Do we need both `FiniteCollection` and `FiniteStream`?**
   `Map` (finite, not a stream) forces an abstract consume spec, and the
   map-then-consume case forces a lazy finite carrier. Both earn their place.
2. *(Leaning: lazy via `FiniteStream`)* **Eager vs lazy finite `map`.** An eager
   `FiniteCollection.map -> List` is simpler (no `FiniteStream`, no coherence
   work) but materializes immediately. The `FiniteStream` return keeps laziness;
   chosen because it generalizes (`filter`, chained combinators) and matches the
   existing lazy `mapped`/`filtered` design.
3. **`collect` primitive vs `splitFirst`-drain primitive.** `collect` (→ `List`)
   is the chosen `FiniteCollection` primitive; an alternative is a finite
   `splitFirst` with the drain derived. `collect` is simpler for non-stream
   carriers (`Map.collect = entries`); the stream carriers derive `collect` from
   their finite `splitFirst` anyway.
4. **Separate finite carriers vs conditional-instance reuse** — resolved
   *separate first* (Phase A–C), reuse as Phase D cleanup.
