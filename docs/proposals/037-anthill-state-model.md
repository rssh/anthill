# 037: The Modify Effect Framework

## Status: Draft

## Tracks: foundations for WI-192, WI-200, time-travel

## Relates to: 027 (effect handlers and standard effects — establishes the handler model; this proposal supersedes 027 §Suspension "twin operations" pattern and 027 §"Modify[T]" — see 027's See-also for the cross-link), 007 (persistence layer — first non-cell consumer), 030 (proof cache; KB epoch), 035 (parameterized sorts), 036 (domain store sorts — concrete consumer)

## Goal

Specify `Modify[T]` as a *framework* that any stateful resource in anthill plugs into uniformly. Not a description of "what currently exists"; a prescription of "how mutation is named, dispatched, and composed."

The framework decides:
1. What `Modify[T]` means at the type level.
2. How a resource type plugs in — identity, available operations, state location.
3. How dispatch routes from a user-level operation to the actual mutation.
4. How `Modify[T]` composes with Branch (transactional), with itself (nested mutations), with time-travel (forward-compat).
5. How multi-instance state is handled.

Anything that mutates user-visible state in anthill — KB, persistence stores, in-memory cells, Map/Substitution/Stream arenas, future domain stores — plugs into the framework or is documented as an exception.

## Definition

The framework has three orthogonal concerns:

### 1. `Modify[T]` — the effect kind

```anthill
sort Modify
  sort T = ?
  -- (no operations on Modify itself)
end
fact Effect[T = Modify[?]]
```

`Modify[T]` is purely an *effect annotation*. It announces "an operation may mutate a resource of type T." It owns no operations — it's a label, used in effect rows.

### 2. `Cell[V]` — the standard small-state sort

```anthill
sort Cell
  sort V = ?
  operation new(initial: V) -> Cell[V]                        -- construct; allocation-only
  operation get(c: Cell[V]) -> V                              -- read; type-pure
  operation set(c: Cell[V], value: V) -> Unit
    effects Modify[c]
end
```

Three operations: `new` (construct), `get` (read), `set` (write). `Cell.new(initial)` allocates a fresh Cell with identity, initialized to `initial`. The constructor name avoids duplicating the sort name (`Cell.cell` would be awkward) and mirrors the host-language allocation convention (`Cell::new` in Rust, `Cell.apply` in Scala, `cell_new` in C). `new` is not a reserved word in anthill, so the import lands cleanly. Construction is **allocation, not mutation** — it doesn't modify any existing Cell, so it doesn't carry `Modify[anything]`. This matches how arena-allocated values are constructed elsewhere in the stdlib (`Map.empty()`, `Substitution.empty()`, `List.nil()` are all effect-pure even though each call yields a fresh handle).

**`Modify[T]` has one semantics: the operation mutates the named resource.** It carries no rollback flag and no scope flag. Whether the mutation survives backtracking is **not** a property of the operation or of the handler — it is the **resource's branch-interaction contract**, declared as part of the resource type itself.

The reason: a Modify whose mutation simply persisted across logical branches would be unsound. If `set(c, 5)` in alt A persisted into alt B, then B's observation of `c` would depend on whether A ran first — execution order, not logical content. Logical branches must be logically independent. The contract has to live somewhere, and "with the resource type" is the only place that keeps it consistent under arbitrary handler installations.

How `set(c, v)` reads:

- The call always means "write `v` to the active state of `c`."
- "The active state of `c`" depends on the surrounding scope:
    - Outside any Branch (or other snapshot-establishing scope), there is one state for `c`. The write goes there. There's no rollback because there is nothing to roll back from.
    - Inside Branch, the resource's branch-interaction contract dictates state lifetime. A `Cell` whose contract says **branch-local snapshot** is snapshotted at branch entry; `set` writes to the active snapshot; abandoning the branch reclaims it.
- The Modify handler does not pick rollback policy. It picks state representation — a host-language structure (associative table, arena, version graph, test fixture, audit-wrapped delegate, …) keyed by whatever the handler chooses (interned identifier, memory address, integer handle, structural composite). Two handlers for the same resource differ in *where state lives and how it's represented*, not in *when mutations roll back*.

Branch's contribution is **runtime-level**: when entering a branch, the runtime walks resources whose contracts declare branch-local-snapshot and snapshots them; abandoning a sibling reverts. The Modify handler is unchanged — it always writes to the active state, and "active" is determined by the surrounding scope, not by handler swapping.

Adding Branch to a region doesn't require an effect-row marker on `set` itself. The composition is clean.

The same logic applies to resource-specific operations (`KB.assert`, `Store.persist`, `WorkItemStore.commit`). Each has one mutation per operation; rollback under Branch is the resource's contract:

- **KB**: contract is branch-local-snapshot — `KB.assert` inside Branch writes to a per-branch fact set (the `register_undo` mechanism).
- **Cell**: contract is branch-local-snapshot — `Cell.set` inside Branch writes to a per-branch slot.
- **Store** (filesystem-backed): contract is *sticky-by-physics* — the filesystem can't roll back atomically. Either a buffered handler absorbs writes for the branch's duration and flushes on commit, or the type system rejects `Modify[store]` calls inside Branch (analogous to the Branch+Consumes constraint from 027).
- **Console.print** / other irreversible side effects: also sticky-by-physics; same two resolutions.

There are no `assert_local` / `persist_local` / `commit_local` variants — every mutation is one operation, and the contract handles the scope axis.

**Effect-row convention**: `Modify[parameter_name]` — refers to the specific parameter the operation receives, not the type. This identifies *which* resource is mutated, not just "some resource of this type." Matches the existing `Modify[store]` usage on `Store.persist` and `Modify[s]` planned for `WorkItemStore.commit`. Multi-instance distinction (WI-200) and future path-based effects (`Modify[s.backend]`) build on parameter-name references.

The exception is proposal 027's `operation set(target: T, ...) effects Modify[T]` — there `T` is both the Modify sort's type parameter and the type of `target`, so the type form is also the parameter form within the Modify sort body. Outside Modify's body, all derived operations use parameter names (`Modify[c]`, `Modify[store]`, `Modify[s]`).

`Cell[V]` is a concrete sort: "a typed mutable cell holding a V." It exposes the standard get/set protocol — one read, one write. Branch-interaction is part of Cell's contract, not the operation's signature.

Resources that fit "small typed state you read and overwrite" declare themselves as `Cell[V]` and inherit the protocol. A counter is `Cell[Int]`. A flag is `Cell[Bool]`. A small record is `Cell[MyRecord]`.

Resources that DON'T fit the Cell protocol — KB, Store, WorkItemStore, Map, Substitution, Stream — declare their own sorts with their own operations. They still carry `Modify[their_sort]` on mutating ops; they just don't use Cell's get/set protocol.

### 3. Type-specific Modify handlers — the dispatch story

The framework requires a **bidirectional correspondence**:
- An operation may declare `Modify[T]` only if T has a registered handler.
- A registered handler exists only for types T that anticipate `Modify[T]` operations.

Bare value types (Int, Bool, String) do **not** admit Modify — they have no handler. Mutable cells wrapping them (`Cell[Int]`) do, because Cell has a handler. Following ML's `Int` vs `IORef Int` and Haskell's `Int` vs `IORef Int` / `STRef Int`. Mutability is a property of the *wrapper*, not the wrapped value.

For every resource type T whose operations mutate, there's at least one Modify handler installed at startup. Operations on T raise `Modify[T]` effect; the dispatcher routes to T's currently-active handler. The handler implements T's specific operations against T's state.

**Handlers vary in state representation, not in rollback policy.** A type can have multiple handlers — selected by interpreter context — but two handlers for the same resource differ in *where state lives and how it's represented*, never in *when mutations roll back*. Rollback is the resource's branch-interaction contract (§"Resource type plug-in"), enforced at the runtime level (§"Composition with Branch"); it is orthogonal to handler choice.

Concrete handler variants:
- **Direct handler**: the default; state lives in a host-language structure (associative table, arena, slot pool — whatever the host realizes efficiently). The keying is the handler's choice: interned identifier, memory address, integer handle, structural composite. None of this is part of the contract Modify exposes.
- **Time-travel handler**: state is a version graph instead of a single value; `get` returns the current head, `set` extends the graph. `get_at` (under a separate `TimeTravel[s]` effect) navigates history. Same operation surface, richer state.
- **Audit handler**: wraps another handler; logs every operation before delegating.
- **Test handler**: substitutes a controlled fixture for the resource's state.
- **Read-only handler**: implements `get` from a pre-populated map; raises Error on `set`.

What is *not* a handler:
- ~~Branch-aware handler~~. Branch interaction is **not** a handler concern — it's the resource's contract enforced by the runtime. The runtime snapshots resources at branch entry per their contract; the same Modify handler writes to whatever state is "active" without knowing whether it's a snapshot or the parent state.

The handler-stack model from proposal 027 §"with_handler" picks the topmost handler matching the effect; switching handlers is the language-level mechanism for time-travel mode, audit mode, test mode, etc. — *all* dimensions that are about state representation, never about rollback semantics.

```
                        ┌─────────────────────────────────┐
   anthill code         │   Cell[Int].set(counter, 5)     │
                        │   KB.assert(kb, fact, sort)     │
                        │   Store.persist(store, fact, m) │
                        │   WIS.commit(wis, work_item)    │
                        └────────────────┬────────────────┘
                                         │ raises Modify[T]
                                         ▼
                        ┌─────────────────────────────────┐
   effect dispatcher    │  match T:                       │
                        │    Cell[V]    → cell_handler    │
                        │    KB         → kb_handler      │
                        │    Store      → store_handler   │
                        │    WIS        → wis_handler     │
                        └─────────────────────────────────┘
                                         │
                        ┌────────────────┼────────────────┐
                        ▼                ▼                ▼
                 host-side structure  host-side fact   host-side store
                 (assoc table /       indexes          registry
                  arena / version     (sort / functor  (per-instance
                  graph / fixture     / discrim tree)  backend value
                  — handler's choice)                   + pending writes)
```

The structures shown are illustrative — they describe what each handler happens to use in the current Rust realization, not what the framework requires. A different host (Scala, C) can pick whatever native structure is efficient; a different handler within the same host can also choose differently. The framework specifies only the dispatch architecture and the contract; everything below the dispatcher is realization.

This brings the existing zoo of state mechanisms (Modify cell, KB indexes, store registry, arenas, source map) under one architecture: each is **a specific handler for a specific resource-type's Modify effect**. The Modify-cell associative table is Cell[V]'s handler. The store registry is Store's handler. KB's internal indexes are KB's handler. Etc.

The framework's invariant: **every mutation declares `Modify[T]`**; **every resource type has a handler** that implements its operations. The resource-specific operation surface varies per type; the dispatch architecture is uniform.

## Resource type plug-in

A *resource type* is any anthill sort whose values can be mutated through `Modify[T]`. To plug T into the framework, the resource MUST declare its **interpreter contract**: a per-resource specification covering identity, exposed operations, state location, dispatch path, lifecycle, branch interaction, and time-travel readiness. Each resource has its own contract; the framework doesn't impose a uniform shape — only that all seven concerns below are answered.

The interpreter contract for each resource type covers:

### 1. Identity scheme

How are two values of T distinguished as "different resources"? **Identity is a property of the *handler*, not of the resource sort.** The resource sort exposes the user-facing API (`new` / `get` / `set` for Cell, `assert` / `retract` for KB, etc.) and stays free of identity-related declarations. The Modify handler is parameterized by the keying scheme it uses internally:

```anthill
-- Conceptual sketch (handlers live in the realization layer; the
-- type parameters describe the contract at the framework level):
sort ModifyHandler
  sort Resource    = ?     -- the resource type this handler covers
  sort IdentityKey = ?     -- how this handler distinguishes instances
end
```

The handler internally maps `Resource → IdentityKey`, then keys its state by `IdentityKey`. User code never sees `IdentityKey` — it interacts with `Resource` values through the resource sort's operations. Different handlers for the same Resource may pick different IdentityKey types (one might use opaque handles, another might use a structural key), but this is a state-representation choice, not a semantic one.

Three concrete identity schemes (matching what handlers will plug in for, per WI-200):

- **Functor-only**: the handler keys all instances of the Resource sort to a single slot. `IdentityKey = Unit`. One instance per Resource type. Suitable for singletons (KB, a process-wide config cell).

  ```anthill
  Cell.new(0)   -- keyed to the single `Cell` slot
  Cell.new(1)   -- ALSO keyed to that slot — collides; overwrites the first
  ```

- **Identity-by-key**: the handler computes an `IdentityKey` from the resource value. `IdentityKey` is a framework-provided opaque type (the runtime may choose interned strings, packed ints, or opaque handles depending on what's efficient). Two resource values land in the same slot iff the handler computes the same key for both.

  Why a framework-provided opaque type rather than bare `String`? Because `String` is weakly typed (any string can be passed) and loses the "this is a resource key" signal. And **not** `Symbol` — Symbols are hash-consed, meant for syntactic identifiers like sort and operation names; using them for dynamic resource keys would pollute the global intern table monotonically.

  Example resource (where the handler keys by the entity's `name` field):

  ```anthill
  sort Config
    entity Config(name: String)                    -- structural form
    operation new(name: String, initial: ConfigData) -> Config
    operation get(c: Config) -> ConfigData
    operation set(c: Config, v: ConfigData) -> Unit
      effects Modify[c]
  end
  -- Handler: ModifyHandler with Resource = Config, IdentityKey = (the
  -- name-derived key). Internally: key(Config(name: "db")) →
  -- IdentityKey.fromString("db").
  ```

  Useful when the resource has a natural domain key the user will reuse (project name, session id, file path, named-config slot). `WorkItemStore(project: "anthill")` and `WorkItemStore(project: "rustland")` denote two distinct stores under an identity-by-key handler — the entity term is what the handler uses to derive the key.

- **Opaque handle**: the handler allocates a fresh internal slot per construction call; `IdentityKey` is whatever the handler uses to address slots (typically an `Int` uid, hidden from user code). Two calls to `Cell.new(0)` produce two distinct cells even with identical initial values. Identity is allocation-time, not value-time. The current arena machinery for `Map` / `Substitution` / `Stream` uses this scheme — and `Cell[V]` belongs in this category: cells in Rust (`Cell::new`), OCaml (`ref`), Haskell (`newIORef`) all get identity from allocation, not from a domain key the user supplies.

  ```anthill
  sort Cell
    sort V = ?
    operation new(initial: V) -> Cell[V]    -- fresh handle every call
    operation get(c: Cell[V]) -> V
    operation set(c: Cell[V], v: V) -> Unit
      effects Modify[c]
  end
  ```

  ```anthill
  let c1 = Cell.new(0)   -- handle uid=1
  let c2 = Cell.new(0)   -- handle uid=2 (distinct, even with same V)
  ```

The resource sort says nothing about identity; the handler's type parameters say everything. Default for an un-parameterized handler is functor-only (`IdentityKey = Unit`), which keeps backward compatibility.

### 2. Operations exposed

T's operations are what the resource type provides. They:
- Use the resource handle (a value of type T) as their first argument.
- Carry `Modify[T]` in the effect set if they mutate.
- Read-only operations (lookups, queries) DO NOT carry Modify[T]. Reading is observation, not mutation; consistent with `get` being type-pure today.

A resource type can expose any operations that suit its purpose. KB exposes `assert/retract/execute/by_functor/...`. Store exposes `persist/flush/retract`. WorkItemStore exposes `commit/lookup/next_id/by_status`. The framework doesn't constrain the surface.

### 3. State location

Where does the actual mutable state live? The framework abstracts over location; the handler picks whatever the host language supports efficiently. Common categories (described in framework-neutral terms; the Rust realization examples are illustrative, not normative):

- **Value-tree associative table**: a host-side associative structure keyed by the handler's identity scheme; values are anthill `Value`s. Suitable when the state can be expressed as a Value tree.
- **Per-instance backend registry**: an associative structure mapping the instance key to a host-language object that carries non-Value internal state (file handles, network connections, large data structures). Useful when the resource's state spills outside the Value model. (Rust realization today: `store_registry` for FileStore — the values are `Box<dyn Store>`; in another host this would be whatever object/struct/closure the language offers.)
- **Resource-internal structures**: the handler treats the resource itself as the substrate. KB falls here — its rules and indexes ARE the state, not a value-tree representation of state. The handler's "operations" are direct method calls on the substrate.
- **Arena**: refcounted, handle-keyed, garbage-collected. Map / Substitution / Stream use this (each value is a handle into a per-resource arena allocated on demand).

Location is a realization detail. The user-level operations on T are the same regardless — both `Cell.set(c, v)` and `Store.persist(store, fact, meta)` are operations carrying `Modify[their_resource]`; the user can't tell (and shouldn't have to know) where the state physically lives or what the handler keys it by.

### 4. Dispatch path

How does an operation call reach the state?

- **Handler-dispatched**: operation raises an effect → effect handler intercepts → handler accesses state. Today's path for Cell's get/set.
- **Direct builtin**: operation maps to a Rust function that directly accesses state. Today's path for Store.persist, KB.assert, Map.put.

The framework PERMITS both. Handler-dispatched is more flexible; direct is faster. A resource may start direct and migrate to handler-dispatched without changing the type-level surface. **The effect annotation is the same regardless of dispatch path.**

### 5. Lifecycle

When does the resource come into existence and when does it go away? The framework's default is **garbage-collected / refcounted** — the resource lives as long as something references it; when no references remain, the runtime reclaims its state. This is the conventional behavior; deviations should be justified.

- **Refcounted (the default)**: created by a `new` / construction op; the runtime tracks references via the arena machinery (refcount, slot pool); state is reclaimed when refcount drops to zero. Today's behavior for arena values (Map, Substitution, Stream); the target behavior for `Cell[V]` under the opaque-handle scheme. No "process lifetime" — if the program drops the resource, it's gone.

- **Pinned by runtime root**: a runtime-internal root holds a strong reference for the program's duration. KB is the canonical example — the interpreter always retains the KB it queries against, so even if no anthill-level reference exists, the KB stays alive. The bundle's `WorkItemStore` lives this way today only because the host process installs it at startup and keeps a host-side reference; this is a host choice, not a property of the resource type.

  This is not a special lifecycle *category* — it's just refcounting where one of the references is held outside anthill code. From the program's perspective, the resource is reachable; from the runtime's perspective, ordinary GC rules apply, and the runtime root is part of the reachability graph.

- **Lexically-scoped**: a `with_handler(...)` / `with_resource(...)` construct (proposal 027 future direction) installs the resource for the dynamic extent of a scope. Entry creates state; exit reclaims it. A *region-based* refinement of refcounting where the lifetime is statically known.

The resource sort doesn't need a separate "lifecycle declaration" if it follows the default. Sorts whose lifetime is constrained (scoped, pinned) are the ones that need a contract entry. The interpreter manages instantiation and disposal via the runtime's standard arena/refcount machinery.

### 6. Branch interaction

How does the resource behave when execution enters a `Branch` choice point? Three options — and the framework treats sticky-under-Branch as a soundness hazard, not a normal mode (per §"Cell[V]"):

- **Branch-local snapshot** (the canonical sound option): the resource is *cloned* at branch entry; each branch sees its own copy; abandoning a branch discards its copy. The runtime mechanism is `register_undo` per snapshot. This is the model for any resource whose state is value-shaped enough to clone (Cell, KB facts, value-only Maps).
- **Frozen**: the resource is read-only inside the branch. Mutations under Branch are a type error. Use this when mutation under branch is genuinely meaningless (Console output that shouldn't double-print, sensors that read external state).
- **Sticky-by-physics** (escape hatch, not a normal mode): the resource cannot be rolled back atomically because its state lives in an external system that doesn't support cheap undo (filesystem, network, hardware). Two acceptable resolutions:
    1. Provide a *buffered handler* that accumulates writes in memory and only flushes on commit. The buffer is snapshot-able; the resource effectively becomes branch-local-snapshot at the framework level.
    2. Add a *static constraint* that prevents this resource from being used inside `Branch` (analogous to 027's Branch+Consumes constraint). The compiler rejects the program if a `Modify[r]` op for such a resource appears inside Branch.

  Plain sticky-under-Branch — the resource silently leaks writes across alternatives — is **not** an accepted contract. Sibling branches would observe an unspecified value (depends on which branch ran first), which violates the logical-independence-of-branches invariant. Today's implementations of Cell / KB / Store *behave* sticky-under-Branch only because the snapshot machinery (or the constraint) hasn't landed yet — that is a soundness gap, not a design choice. The proposal flags this gap rather than blessing it.

The resource type declares which model applies. The runtime consults this when entering `Branch`. **Each resource type's contract must specify what happens at branch entry/exit — silence is a bug.**

For example: a `Cell[V]` declared "branch-local snapshot" gets cloned into a per-branch slot at branch entry; the (unchanged) Modify handler writes to the active snapshot; abandoning the branch drops the slot. A `Console` declared "frozen" rejects `print` calls inside Branch at compile time.

### 7. Time-travel readiness

Is the resource designed to support a future time-travel handler? If yes, the resource type's operations follow the five forward-compat invariants (§"With time-travel" below). If no, the resource is opaque to time-travel — version graph queries don't apply.

Resources that hold non-Value internal state (FileStore's pending writes, KB's discrim trees) are typically *not* time-travel-ready out of the box; their handler implementations would need to grow versioned variants. Resources whose state is a Value (Cell[V], WorkItemStore's wis(...)) are naturally time-travel-ready — a versioned handler swaps in transparently.

## Per-resource interpreter contracts

Each resource type needs its own contract spelled out. The framework requires this section in any proposal introducing a new state type. Below: the contracts for the resource types that exist (or will exist for WI-192).

### Cell[V]

| | |
|---|---|
| Identity scheme | **Opaque handle**: `Cell.new` returns a fresh handle per call (Rust `Cell::new`, OCaml `ref`, Haskell `IORef` flavor). The Rust realization today uses a transitional functor-keyed scheme that collapses all `Cell.new(...)` calls to one slot; WI-200 replaces it with the opaque-handle scheme that matches the contract. |
| Operations exposed | `new(initial) -> Cell[V]` (construct), `get(c) -> V` (read), `set(c, v) -> Unit` (write). No `key` operation — Cell's identity is allocation-time. One write op with one semantics (mutate); branch interaction is the contract below. |
| State location | A host-language structure private to the Cell handler. The structure shape and the keying primitive are realization details, not part of the framework — alternative handlers (time-travel, test fixture, audit-wrapped delegate) carry different state representations for the same operation surface. |
| Dispatch path | Handler-dispatched via the existing Modify effect machinery. |
| Lifecycle | **Refcounted** (the default): born at `Cell.new(initial)`; reclaimed when no references remain. Optional lexical scoping via `with_resource`. While the transitional functor-keyed Rust scheme is in place, Cell state is effectively pinned for the process duration (single slot per V, no GC) — a side-effect of the functor-only identity scheme, not a lifecycle decision. Refcounted GC follows automatically once WI-200 lifts Cell to opaque-handle. |
| Branch interaction | **Branch-local snapshot** (per the contract). Today's implementation behaves sticky-under-Branch only because the snapshot machinery isn't wired yet — that is a soundness gap, not the contract. The fix is the runtime `register_undo` + per-branch state cloning (Open Decision 3). |
| Time-travel readiness | Yes — state is a Value; a versioned handler can layer in transparently. |

### KB

| | |
|---|---|
| Identity scheme | Singleton (one KB per Interpreter). Multi-KB scenarios use explicit kb-handle threading. |
| Operations exposed | `assert(kb, term, sort) -> Option[FactId]`, `retract(kb, id) -> Bool`, `execute(kb, query) -> Stream`, `by_functor`, `by_sort`, etc. |
| State location | KB's internal substrate (the rules, fact indexes, discrimination tree, etc.) — not a value-tree representation; the handler operates on the substrate directly. The Rust realization uses native data structures (e.g. an indexed rule list, a functor → fact map, a discrim tree); other hosts pick equivalent native shapes. |
| Dispatch path | Direct builtin today (`kb.assert_fact(...)`); handler-dispatched in principle for substitution. |
| Lifecycle | **Pinned by runtime root**: the interpreter always holds a strong reference to the KB it queries against, so KB stays alive for the process duration. Not a special lifecycle category — just refcounting where the runtime root is one of the references. |
| Branch interaction | **Branch-local snapshot** (per the contract). Today's KB *behaves* sticky-under-Branch because the snapshot machinery isn't fully wired yet — that is a soundness gap. The fix is `register_undo` on KB-level mutations; `KB.assume` from prior drafts disappears once `assert` itself becomes branch-local under Branch. |
| Time-travel readiness | Partial — proposal 030 wires `state_hash` for proof cache; full time-travel needs versioned indexes. WI-201 (candidate). |

**Open per Rule 1**: KB.assert / retract / assume should declare `Modify[kb]` effects (currently silent). `execute` stays effect-`Error` only (queries don't mutate).

### Store (FileStore, IndexedFileStore)

| | |
|---|---|
| Identity scheme | **Identity-by-key** (`String`): the canonical-form string of `(functor, field-values)` is the key. Two `Store(...)` values with the same field values denote the same backing store; this is the existing `store_registry` lookup. Implemented today via the registry; consistent with the framework's identity-by-key scheme. |
| Operations exposed | `persist(store, fact, meta) -> FactId`, `flush(store, delta) -> Bool`, `retract(store, id) -> Bool`, `pull` (BulkStore). |
| State location | A per-instance backend registry: an associative structure mapping the instance key to a host-language object carrying the backend internals (pending writes, source map, indexes, file handles). The Rust realization uses `HashMap<String, Box<dyn Store>>`; other hosts pick equivalent shapes (e.g., a Scala `Map[String, Store]` with a sealed trait, a C struct of function pointers + per-instance void pointer). |
| Dispatch path | Direct builtin today. Operations declare `Modify[store]` for effect-row honesty. |
| Lifecycle | **Pinned by runtime root**: the host process registers store instances at startup and retains host-side references for the duration. Not a property of Store-as-a-type — a Store the program drops with no host-side root would be reclaimed under refcounted rules. |
| Branch interaction | **Sticky-by-physics** (the filesystem can't roll back atomically). Two acceptable resolutions per the framework: (a) a buffered Store handler that accumulates writes in memory, snapshot-able like Cell, and only flushes on commit; or (b) a static constraint that prevents `Modify[store]` ops inside Branch. Today neither is in place — `persist` writes leak across alternatives, which is a soundness gap until one of (a)/(b) lands. |
| Time-travel readiness | No — the backend object's internals aren't versioned. A future versioned variant would maintain its own history. |

### Map[K, V] / Substitution / Stream (arena values)

| | |
|---|---|
| Identity scheme | Opaque arena handle (allocated per construction). Multi-instance native; refcounted. |
| Operations exposed | `Map.put/get/contains/remove/...`; `Substitution.lookup/apply/compose`; `Stream.splitFirst`. |
| State location | A per-resource arena (slot pool with refcounting) — host-realized as native arena structures (e.g., the Rust realization names them `map_arena`, `subst_arena`, `stream_arena`). |
| Dispatch path | Direct builtin. Operations declare `Modify[their_value]` (TODO — currently silent for Map/Substitution; pure for Stream). |
| Lifecycle | **Refcounted** (the default): refcount drops to zero → slot reclaimed. The canonical implementation of the framework's default lifecycle. |
| Branch interaction | **Branch-local snapshot** (per the contract — value-shaped state can be cloned). Today's arenas behave sticky-under-Branch because the runtime snapshot hooks aren't wired in yet — soundness gap, fixable transparently when the runtime grows the hooks. |
| Time-travel readiness | Yes for Map (Value-shaped); Substitution and Stream have non-Value internals so partial. |

### WorkItemStore (anthill-todo, WI-192)

| | |
|---|---|
| Identity scheme | Functor-only for v0.1 (single bundle invocation = single store). WI-200 may lift later. |
| Operations exposed | `next_id(s) -> String`, `lookup(s, id) -> Option[WorkItem]`, `by_status(s, st) -> List[WorkItem]`, `commit(s, w) -> Unit`, `forget(s, id) -> Unit`. |
| State location | The Modify cell, holding a `wis(backend, by_id, by_status, id_counter)` Value. Reuses Cell[V] machinery. |
| Dispatch path | Handler-dispatched via Modify (Cell's handler covers it). |
| Lifecycle | **Pinned by runtime root** (host-side): the bundle's host installs `wis(...)` at startup and retains a host reference for the CLI's duration. Not a property of `WorkItemStore`-as-a-type — under refcounted rules a dropped store would be reclaimed; the host just doesn't drop it during a single CLI invocation. |
| Branch interaction | **Branch-local snapshot** (inherits Cell's contract). Bundle's CLI doesn't use Branch, so the soundness gap above isn't load-bearing for v0.1 — but the contract is still snapshot, not sticky. |
| Time-travel readiness | Yes — wis(...) is Value-shaped; a future versioned-Cell handler covers it transparently. |

The framework requires this contract for every new resource type. A resource without an interpreter contract is incomplete.

## Composition rules

### With Branch (resource contract drives snapshot)

Modify has one semantics: mutate the named resource. Whether the mutation rolls back when the surrounding execution backtracks is the **resource's branch-interaction contract**, enforced at the runtime level. The Modify handler is not involved — it always writes to whatever the runtime presents as the active state of the resource.

When execution enters a `Branch`:

1. The runtime walks the resource types touched by the branch body.
2. For each resource whose contract is **branch-local snapshot**, the runtime clones (or otherwise snapshots) the resource's state into a per-branch slot, and registers an undo callback (`register_undo`) so abandoning a sibling restores the parent state.
3. For resources whose contract is **frozen**, the type system has already rejected any `Modify[r]` op inside the branch body at compile time.
4. For resources whose contract is **sticky-by-physics**, either (a) a buffered handler has been installed that absorbs the writes into a snapshot-able buffer, or (b) the same compile-time constraint as Frozen applies. Plain leaky-sticky is not an accepted contract.

The Modify handler is unchanged across these cases. It always writes to the active state of the resource; what "active state" means is whatever the runtime presents as current (parent state, branch snapshot, or buffer).

Effect rows stay clean: just `Modify[c]`, never `Modify[c], Branch`. Adding Branch to a region doesn't perturb the effect row of a `set` call site, because Branch's interaction with state is a runtime mechanism, not a typing-level concern.

No source-level `_local` / `_atomic` / `_transactional` operations exist or are needed.

### With other Modify effects

Operations can declare multiple `Modify[X]` effects, one per resource they touch:

```anthill
operation commit(s: WorkItemStore, w: WorkItem) -> Unit
  effects {Modify[s], Modify[backend], Error}    -- modifies both s and s.backend
```

The framework treats these independently — handlers for Modify[s] and Modify[backend] are separate. There's no automatic transitivity (Modify[s] does NOT imply Modify[anything reachable from s]).

If transitivity is desired (path-based effects), the operation declares it explicitly. Future proposal could add path syntax (`Modify[s.backend]` resolves at type-check time).

### With Error

`Modify[T]` operations that can fail also declare `Error`. The framework doesn't tie them: a `set` that raises Error before reaching the handler leaves state untouched; a `set` that completes its mutation and *then* signals an error has already mutated. The atomicity of `set` itself is the handler's responsibility (the handler should not partially-write); rollback under failure is the resource's branch-interaction contract (under `try` / `bracket` constructs that establish a snapshot scope, the runtime restores state on Error the same way it does on branch abandon).

### With time-travel (forward-compat invariants)

Five invariants the framework holds for any T, so a future time-travel handler can substitute a versioned representation without breaking existing code:

1. `set(target, v)` — observable contract is "next get returns v." Handler implementation hidden.
2. `get(target)` returns the current head. Time-travel adds `get_at` under a separate `TimeTravel[s]` effect.
3. `Modify[T]` surface doesn't expose handler-internal structure (no version IDs, snapshot handles, dirty bits in operation signatures).
4. `set` returns `Unit` (not the prior value) — capturing the prior value would force every handler to materialize it.
5. Operation signatures don't encode rollback policy. Whether mutations roll back is the resource's branch-interaction contract; a time-travel handler swaps in (changing state representation, not rollback policy) without renaming or re-typing the operation.

These hold for resource-specific ops too (commit, persist, assert) — none of them return the prior value or expose handler internals.

## Multi-instance support

Single-instance-per-functor is the simplest identity scheme; the framework permits all three (functor-only, identity-by-key, opaque-handle). The handler picks one per resource. WI-200 tracks the runtime work to make multi-instance schemes available — until then, the Rust realization uses a single type-independent associative table that effectively forces functor-only on every Modify-using resource.

Until WI-200 lands, all stateful resources are functor-keyed (one instance per type). This is OK for KB (one per Interpreter), config cells (singleton), the bundle's WorkItemStore (one per CLI invocation). It's NOT OK for arena-allocated values (Map, Substitution, Stream) — those use opaque handles via separate machinery (`Value::Map(handle)`, etc.) and don't go through the Modify cell.

Bringing arena resources into the framework is part of WI-200 — an opaque-handle identity scheme makes this uniform.

## Read operations

Read-only operations DO NOT declare `Modify[T]`. The framework treats reading as observation; `get(target)` is type-pure even though it reads mutable state. This matches Haskell `IORef.read` (typed `IO`) loosely — the static contract distinguishes "may mutate" from "may observe."

Resource-specific read ops (KB.execute, Store.pull, Map.get, WorkItemStore.lookup) follow the same rule — no Modify in the effect set. They MAY declare `Error` if they can fail; otherwise pure-typed.

(Discussion: a future Read[T] effect for tracking observation explicitly is mentioned in 027 §"Read[T]" but isn't required for v1. The framework leaves room.)

## What this proposal makes binding

Once accepted, the following are rules for any new state design:

### Rule 1: Every mutation declares Modify[X]

If an operation modifies any resource visible at the type level, it MUST declare `Modify[X]` (where X is the resource it touches) in its effect set. Silence is a bug.

This applies to KB.assert (currently silent — fix to `Modify[kb]`), to all future stateful sorts, to all resource-specific operations.

### Rule 2: Modify[T] is uniform across resources

The effect kind is `Modify` for any mutation of any resource. We don't introduce per-domain effect kinds (`KbWrite`, `MapWrite`, etc.) — that would fragment API analysis. The resource parameter is what distinguishes.

### Rule 3: Read is silent

Read-only operations don't declare Modify. Observation is type-pure.

### Rule 4: Handler protocol is dispatch-independent

The operations on a resource (their signatures, effect rows, semantics) are the same whether dispatch is handler-mediated or direct. Migration between dispatch paths doesn't change user-visible types.

### Rule 5: One operation per mutation; rollback is the resource's contract

Operations have ONE source-level form per mutation, with ONE semantics: mutate the named resource. Whether the mutation rolls back is the **resource's branch-interaction contract**, enforced at the runtime level — not a property of the operation, the handler, or any contextual flag.

Resources whose physics prevent atomic rollback (filesystem, external service) declare **sticky-by-physics** in their contract, which forces one of two resolutions: a buffered handler that absorbs writes for the branch's duration, or a static constraint that rejects the resource's use under Branch (analogous to the Branch+Consumes constraint from 027). A resource that silently leaks writes across branch alternatives is not an accepted contract — sibling alts would observe an unspecified value (depends on which alt ran first), which breaks logical-independence-of-branches.

`set_local` / `assert_local` / `commit_local` and equivalent paired operations are not introduced, since the contract handles the rollback axis.

### Rule 6: Multi-instance via declared identity

A resource that supports multiple instances declares its identity scheme (functor / by-field / opaque). The default is functor-only (single instance) until the resource opts into multi-instance.

### Rule 7: Forward compatibility with time-travel (the five invariants from §"Composition with time-travel")

Operations on resources observe these invariants so a future time-travel handler can layer in.

### Rule 8: Modify[T] and handler are bidirectionally required

`Modify[T]` may appear in an effect row only if T has a registered handler (so the runtime knows where to dispatch). A handler for T is meaningful only if at least one operation declares `Modify[T]` (otherwise it can never fire). Bare value types without a wrapper sort (Int, Bool, String, raw functor terms) cannot carry Modify because they have no handler and no place for one to attach. Mutability is a property of the resource type, declared by introducing a sort that owns operations carrying `Modify[T]`.

## Open decisions before WI-192 implements

The framework above leaves these open; they need answers before WI-192's WorkItemStore lands:

1. **KB.assert effect declaration**: change reflect.anthill to add `Modify[kb]` on assert/retract. Mechanical change; needed for honesty per Rule 1. *Recommendation: yes, do it as part of this proposal's acceptance.*

2. **WorkItemStore identity scheme**: functor-only (single instance) or one of the WI-200 schemes? *Recommendation: functor-only for v0.1; revisit when multi-instance need arises.*

3. **Branch snapshot machinery timeline**: when does the runtime grow the snapshot/`register_undo` hooks that enforce branch-local-snapshot contracts? Today's runtime doesn't have these (Branch's eval-side wiring is partial). Until they land, every resource whose contract says "branch-local snapshot" actually *behaves* sticky-under-Branch — a soundness gap, not a contract feature. *Recommendation: defer the implementation; bundle is a one-shot CLI without Branch use, so the gap isn't load-bearing for v0.1. When Branch lands as a usable feature, the snapshot machinery is a hard prerequisite, not optional.*

4. **`Modify.get` on resources without get/set protocol**: KB / Store / WorkItemStore don't expose `get(s) -> S` because their state isn't a single value. Is this OK? *Recommendation: yes — `get`/`set` are the standard ops on Modify but resources can omit them when they don't fit. The framework allows.*

## Acceptance

Design-level proposal. Acceptance is:
1. Rules 1–8 accepted as binding for new state designs.
2. KB.assert / retract effect annotations updated (per open decision 1).
3. Proposals 027, 035, 036 reference this framework where they touch state semantics.
4. Future proposals introducing new state cite this framework or document why they diverge.

Once accepted, WI-192 implementation proceeds under the framework without re-litigating fundamentals.
