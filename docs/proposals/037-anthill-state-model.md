# 037: The Modify Effect Framework

## Status: Draft

## Tracks: foundations for WI-192, WI-200, time-travel

## Relates to: 027 (effect handlers and standard effects — establishes Modify), 007 (persistence layer — first non-cell consumer), 030 (proof cache; KB epoch), 035 (parameterized sorts), 036 (domain store sorts — concrete consumer)

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
  operation get(c: Cell[V]) -> V                              -- read; type-pure
  operation set(c: Cell[V], value: V) -> Unit
    effects Modify[c]
end
```

**One write operation, not two.** Proposal 037 supersedes 027 §4's split between `set` (sticky) and `set_local` (transactional, requires Branch). The split was unnecessarily duplicating the API surface for what's a handler concern, not an operation concern.

In algebraic effects, **operations are stable; handlers determine semantics**. Inside Branch, the runtime installs a *compatible Modify handler* that intercepts every `set` and registers undo on the current snapshot — making the operation transactional without changing its source form. Outside Branch, the default sticky handler is in scope, and `set` writes through as a normal mutation. Same source-level call, different runtime semantics, depending on the active handler.

The handler is the substitution point:
- **Default handler**: sticky writes through to the cell's state.
- **Branch-installed handler**: sticky writes plus `register_undo` on the current snapshot, so abandoning a sibling alt reverts.
- **Lexically-scoped handler** (`with_resource`, `with_handler`): writes through to the scoped state; reverted on scope exit.
- **Audit handler**: writes through plus logs each operation.
- **Test handler**: substitutes a controlled state for the duration of a test.

Branch's contribution is to install its compatible handler at branch entry; it doesn't require an effect-row marker on `set` itself. Composition is clean — adding Branch to a region doesn't force every `set` call site to declare `Branch` in its effect row.

The same logic applies to resource-specific operations (KB.assert, Store.persist, WorkItemStore.commit). Each has one mutation-flavor per operation; the handler determines whether it's sticky / transactional / audited / time-travelled. We don't need `assert_local`, `persist_local`, `commit_local` variants — Branch (and other scope-establishing constructs) install handlers that make the existing operations transactional.

**Effect-row convention**: `Modify[parameter_name]` — refers to the specific parameter the operation receives, not the type. This identifies *which* resource is mutated, not just "some resource of this type." Matches the existing `Modify[store]` usage on `Store.persist` and `Modify[s]` planned for `WorkItemStore.commit`. Multi-instance distinction (WI-200) and future path-based effects (`Modify[s.backend]`) build on parameter-name references.

The exception is proposal 027's `operation set(target: T, ...) effects Modify[T]` — there `T` is both the Modify sort's type parameter and the type of `target`, so the type form is also the parameter form within the Modify sort body. Outside Modify's body, all derived operations use parameter names (`Modify[c]`, `Modify[store]`, `Modify[s]`).

`Cell[V]` is a concrete sort: "a typed mutable cell holding a V." It exposes the standard get/set protocol — one read, one write. Sticky vs transactional behavior is provided by the active handler, not by separate operations.

Resources that fit "small typed state you read and overwrite" declare themselves as `Cell[V]` and inherit the protocol. A counter is `Cell[Int]`. A flag is `Cell[Bool]`. A small record is `Cell[MyRecord]`.

Resources that DON'T fit the Cell protocol — KB, Store, WorkItemStore, Map, Substitution, Stream — declare their own sorts with their own operations. They still carry `Modify[their_sort]` on mutating ops; they just don't use Cell's get/set protocol.

### 3. Type-specific Modify handlers — the dispatch story

The framework requires a **bidirectional correspondence**:
- An operation may declare `Modify[T]` only if T has a registered handler.
- A registered handler exists only for types T that anticipate `Modify[T]` operations.

Bare value types (Int, Bool, String) do **not** admit Modify — they have no handler. Mutable cells wrapping them (`Cell[Int]`) do, because Cell has a handler. Following ML's `Int` vs `IORef Int` and Haskell's `Int` vs `IORef Int` / `STRef Int`. Mutability is a property of the *wrapper*, not the wrapped value.

For every resource type T whose operations mutate, there's at least one Modify handler installed at startup. Operations on T raise `Modify[T]` effect; the dispatcher routes to T's currently-active handler. The handler implements T's specific operations.

A type can have **multiple handlers** — selected by interpreter context:
- **Direct handler**: the default; fast path with simple state.
- **Time-travel handler**: maintains a version graph; same operation surface, richer state.
- **Branch-aware handler**: intercepts `set` calls and registers `register_undo` on the current snapshot, making the same write transactional without source-level changes.
- **Audit handler**: logs every operation before delegating to a wrapped handler.
- **Test handler**: substitutes a mock for the resource's state.

The handler-stack model from proposal 027 §"with_handler" picks the topmost handler matching the effect; switching handlers is the language-level mechanism for time-travel mode, audit mode, test mode, etc.

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
                  HashMap<Sym, V>   KB indexes     store_registry
                  (or whatever      (assert_fact   (Box<dyn Store>
                   the handler      / retract /    / pending writes /
                   chooses)         by_functor)    source_map)
```

This brings the existing zoo of state mechanisms (Modify cell, KB, store_registry, arenas, source_map) under one architecture: each is **a specific handler for a specific resource-type's Modify effect**. The Modify-cell HashMap is Cell[V]'s handler. The store_registry is Store's handler. KB's internal indexes are KB's handler. Etc.

The framework's invariant: **every mutation declares `Modify[T]`**; **every resource type has a handler** that implements its operations. The resource-specific operation surface varies per type; the dispatch architecture is uniform.

## Resource type plug-in

A *resource type* is any anthill sort whose values can be mutated through `Modify[T]`. To plug T into the framework, the resource MUST declare its **interpreter contract**: a per-resource specification covering identity, exposed operations, state location, dispatch path, lifecycle, branch interaction, and time-travel readiness. Each resource has its own contract; the framework doesn't impose a uniform shape — only that all seven concerns below are answered.

The interpreter contract for each resource type covers:

### 1. Identity scheme

How are two values of T distinguished as "different resources"? Three options (per WI-200):

- **Functor-only**: same sort → same identity. One instance per type. Today's default Modify handler. Suitable for singletons (KB, a process-wide config cell).
- **Identity-by-field**: the sort designates one or more fields as identity. Cells key by `(functor, identity_value)`. Instances coexist as long as identity values differ.
- **Opaque handle**: a fresh `Value::Resource(uid)` per construction. Maximum isolation; no field shape needed.

Resources that can have multiple instances declare which scheme they use; the runtime keys cells accordingly. Default is functor-only (single instance) for backward compatibility.

### 2. Operations exposed

T's operations are what the resource type provides. They:
- Use the resource handle (a value of type T) as their first argument.
- Carry `Modify[T]` in the effect set if they mutate.
- Read-only operations (lookups, queries) DO NOT carry Modify[T]. Reading is observation, not mutation; consistent with `get` being type-pure today.

A resource type can expose any operations that suit its purpose. KB exposes `assert/retract/execute/by_functor/...`. Store exposes `persist/flush/retract`. WorkItemStore exposes `commit/lookup/next_id/by_status`. The framework doesn't constrain the surface.

### 3. State location

Where does the actual mutable state live? The framework abstracts over location; an implementation chooses:

- **Modify cell** (`default_modify_handler`): a HashMap keyed by the identity scheme; values are anthill `Value`s. Suitable when the state can be expressed as a Value tree.
- **Resource registry**: a Rust-side `HashMap<Key, Box<dyn ResourceImpl>>` where ResourceImpl carries non-Value internal state (file handles, network connections, large data structures). Today's `store_registry` for FileStore.
- **KB's own indexes**: KB rules and indexes are the state. Special case — KB IS the substrate, not a value-shaped resource.
- **Arena**: refcounted, handle-keyed, garbage-collected. Map / Substitution / Stream.

The location is an implementation detail. The user-level operations on T are the same regardless of location — both `Modify.set(target, v)` and `Store.persist(store, fact, meta)` are operations carrying `Modify[their_resource]`; the user can't tell where the state physically lives.

### 4. Dispatch path

How does an operation call reach the state?

- **Handler-dispatched**: operation raises an effect → effect handler intercepts → handler accesses state. Today's path for Cell's get/set.
- **Direct builtin**: operation maps to a Rust function that directly accesses state. Today's path for Store.persist, KB.assert, Map.put.

The framework PERMITS both. Handler-dispatched is more flexible; direct is faster. A resource may start direct and migrate to handler-dispatched without changing the type-level surface. **The effect annotation is the same regardless of dispatch path.**

### 5. Lifecycle

When does the resource come into existence and when does it go away?

- **Process-lifetime**: KB, the bundle's WorkItemStore, a process-wide config cell. Created once at startup; persists until process exit.
- **Construction-bounded**: arena values (Map, Substitution, Stream). Created by an op call; refcount-managed; dropped when no references remain.
- **Lexically-scoped**: cells introduced under a `with_handler(...)` or `with_resource(...)` construct (proposal 027 future direction). Born at scope entry; die at scope exit.

The resource type declares which lifecycle category it falls into. The interpreter manages instantiation and disposal accordingly.

### 6. Branch interaction

How does the resource behave when execution enters a `Branch` choice point?

- **Sticky**: state persists across branch alternatives. Modifications in alt A are observable in alt B. (Today's default for Cell, KB, Store.)
- **Branch-local snapshot**: the resource is *cloned* at branch entry; each branch sees its own copy; abandoning a branch discards its copy. The Branch-installed Modify handler intercepts each `set` call and registers `register_undo`, so the same operation that's sticky outside Branch becomes transactional inside it. The interpreter installs the compatible handler at branch entry; resources that opt in update the per-branch snapshot instead of the parent state.
- **Frozen**: the resource is read-only inside the branch. Mutations would be a type error. Useful for resources whose mutation under branch is genuinely meaningless (e.g., a Console output that shouldn't double-print).

The resource type declares which model applies. The interpreter consults this when entering `Branch`. **Each resource type's contract must specify what happens at branch entry/exit — silence is a bug.**

For example: a `Cell[V]` declared "branch-local snapshot" gets cloned into a per-branch slot at branch entry; its handler updates the per-branch slot; abandoning the branch drops the slot. A `Cell[V]` declared "sticky" updates the parent state directly.

### 7. Time-travel readiness

Is the resource designed to support a future time-travel handler? If yes, the resource type's operations follow the five forward-compat invariants (§"With time-travel" below). If no, the resource is opaque to time-travel — version graph queries don't apply.

Resources that hold non-Value internal state (FileStore's pending writes, KB's discrim trees) are typically *not* time-travel-ready out of the box; their handler implementations would need to grow versioned variants. Resources whose state is a Value (Cell[V], WorkItemStore's wis(...)) are naturally time-travel-ready — a versioned handler swaps in transparently.

## Per-resource interpreter contracts

Each resource type needs its own contract spelled out. The framework requires this section in any proposal introducing a new state type. Below: the contracts for the resource types that exist (or will exist for WI-192).

### Cell[V]

| | |
|---|---|
| Identity scheme | Functor-only today (default Modify handler keys by `Cell` symbol — single instance per V). WI-200 to lift this. |
| Operations exposed | `get(c) -> V`, `set(c, v) -> Unit`. One write op; sticky vs transactional via active handler. |
| State location | `default_modify_handler`'s `HashMap<Symbol, Value>`. |
| Dispatch path | Handler-dispatched via the existing Modify effect machinery. |
| Lifecycle | Process-lifetime by default; lexically-scoped via future `with_resource`. |
| Branch interaction | Default handler is sticky; Branch installs a compatible handler that makes `set` transactional via `register_undo`. |
| Time-travel readiness | Yes — state is a Value; a versioned handler can layer in transparently. |

### KB

| | |
|---|---|
| Identity scheme | Singleton (one KB per Interpreter). Multi-KB scenarios use explicit kb-handle threading. |
| Operations exposed | `assert(kb, term, sort) -> Option[FactId]`, `retract(kb, id) -> Bool`, `execute(kb, query) -> Stream`, `by_functor`, `by_sort`, etc. |
| State location | KB's internal Rust structures: `rules: Vec<RuleEntry>`, `by_functor: HashMap<...>`, discrimination tree. Not value-shaped. |
| Dispatch path | Direct builtin today (`kb.assert_fact(...)`); handler-dispatched in principle for substitution. |
| Lifecycle | Process-lifetime; created with the Interpreter. |
| Branch interaction | Sticky today. `KB.assume` (designed; partially implemented) provides branch-local snapshot via `register_undo`. |
| Time-travel readiness | Partial — proposal 030 wires `state_hash` for proof cache; full time-travel needs versioned indexes. WI-201 (candidate). |

**Open per Rule 1**: KB.assert / retract / assume should declare `Modify[kb]` effects (currently silent). `execute` stays effect-`Error` only (queries don't mutate).

### Store (FileStore, IndexedFileStore)

| | |
|---|---|
| Identity scheme | Canonical-form String (functor + field values). Multi-instance native. |
| Operations exposed | `persist(store, fact, meta) -> FactId`, `flush(store, delta) -> Bool`, `retract(store, id) -> Bool`, `pull` (BulkStore). |
| State location | `store_registry: HashMap<String, Box<dyn Store>>`. The Box holds non-Value internals (pending writes, source map, indexes). |
| Dispatch path | Direct builtin today. Operations declare `Modify[store]` for effect-row honesty. |
| Lifecycle | Process-lifetime; instances registered at startup. |
| Branch interaction | Sticky today. No Branch-aware Store handler installed yet, so `persist` writes leak across alternatives — caller's responsibility. The framework permits a future compatible handler that buffers per-branch writes and flushes on commit. |
| Time-travel readiness | No — `Box<dyn Store>` internals aren't versioned. A future versioned variant would maintain its own history. |

### Map[K, V] / Substitution / Stream (arena values)

| | |
|---|---|
| Identity scheme | Opaque arena handle (allocated per construction). Multi-instance native; refcounted. |
| Operations exposed | `Map.put/get/contains/remove/...`; `Substitution.lookup/apply/compose`; `Stream.splitFirst`. |
| State location | Per-resource arena (`map_arena`, `subst_arena`, `stream_arena`) — refcount + slot pool. |
| Dispatch path | Direct builtin. Operations declare `Modify[their_value]` (TODO — currently silent for Map/Substitution; pure for Stream). |
| Lifecycle | Construction-bounded; refcount drops to zero → slot reclaimed. |
| Branch interaction | Sticky today. Could be branch-local-snapshot for Map (clone at branch entry) without changing user code. |
| Time-travel readiness | Yes for Map (Value-shaped); Substitution and Stream have non-Value internals so partial. |

### WorkItemStore (anthill-todo, WI-192)

| | |
|---|---|
| Identity scheme | Functor-only for v0.1 (single bundle invocation = single store). WI-200 may lift later. |
| Operations exposed | `next_id(s) -> String`, `lookup(s, id) -> Option[WorkItem]`, `by_status(s, st) -> List[WorkItem]`, `commit(s, w) -> Unit`, `forget(s, id) -> Unit`. |
| State location | The Modify cell, holding a `wis(backend, by_id, by_status, id_counter)` Value. Reuses Cell[V] machinery. |
| Dispatch path | Handler-dispatched via Modify (Cell's handler covers it). |
| Lifecycle | Process-lifetime; host instantiates wis(...) at startup, calls `Modify.set` once before `Main.main`. |
| Branch interaction | Sticky (matches the bundle's CLI semantics; no branch use). |
| Time-travel readiness | Yes — wis(...) is Value-shaped; a future versioned-Cell handler covers it transparently. |

The framework requires this contract for every new resource type. A resource without an interpreter contract is incomplete.

## Composition rules

### With Branch (handler swaps determine sticky vs transactional)

Proposal 037 supersedes 027 §4's `set` / `set_local` split. Each operation has one source-level form; sticky vs transactional is a HANDLER concern, not an OPERATION concern.

- Default handler: writes through; sticky. Outside Branch, calls to `set` mutate persistently.
- Branch-installed compatible handler: same write, plus `register_undo` registers a callback that reverts the cell's value on snapshot abandon. Inside Branch, the same `set` call is transactional.
- Lexical-scope handlers (`with_resource`, `atomic`): same shape — the scope's handler intercepts and provides its rollback semantics.

The framework requires: when entering Branch, the runtime installs a compatible Modify handler for any resource type that opts into branch-local snapshot semantics (per the resource's interpreter contract). Resources that opt into "sticky always" don't get a compatible handler installed — their ops behave the same in or out of Branch.

No source-level `_local` operations needed. Effect rows stay clean (just `Modify[c]`, never `Modify[c], Branch`).

### With other Modify effects

Operations can declare multiple `Modify[X]` effects, one per resource they touch:

```anthill
operation commit(s: WorkItemStore, w: WorkItem) -> Unit
  effects {Modify[s], Modify[backend], Error}    -- modifies both s and s.backend
```

The framework treats these independently — handlers for Modify[s] and Modify[backend] are separate. There's no automatic transitivity (Modify[s] does NOT imply Modify[anything reachable from s]).

If transitivity is desired (path-based effects), the operation declares it explicitly. Future proposal could add path syntax (`Modify[s.backend]` resolves at type-check time).

### With Error

`Modify[T]` operations that can fail also declare `Error`. The framework doesn't tie them: under the default (sticky) handler, a `set` that fails leaves state pre-mutation (the handler doesn't write); under a Branch-aware (transactional) handler, the same `set` rolls back via the snapshot mechanism. Error is orthogonal to which handler is active.

### With time-travel (forward-compat invariants)

Five invariants the framework holds for any T, so a future time-travel handler can substitute a versioned representation without breaking existing code:

1. `set(target, v)` — observable contract is "next get returns v under the active handler." Handler implementation hidden.
2. `get(target)` returns the current head under the active handler. Time-travel adds `get_at` under a separate `TimeTravel[s]` effect.
3. `Modify[T]` surface doesn't expose handler-internal structure (no version IDs, snapshot handles, dirty bits in operation signatures).
4. `set` returns `Unit` (not the prior value) — capturing the prior value would force every handler to materialize it.
5. Operation signatures don't encode sticky vs transactional. The active handler picks the semantics; a time-travel handler swaps in without renaming or re-typing the operation.

These hold for resource-specific ops too (commit, persist, assert) — none of them return the prior value or expose handler internals.

## Multi-instance support

Single-instance-per-functor (today's default) is the simplest case. Multi-instance support requires picking an identity scheme (per §"Resource type plug-in"). WI-200 tracks the design — the framework permits any of the three schemes; a sort declares which it uses.

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

### Rule 5: One operation per mutation; handler determines semantics

Operations have ONE source-level form per mutation. Sticky vs transactional is determined by the active handler, not by separate operations. The runtime installs a compatible Branch-aware handler at Branch entry; the same `set` / `assert` / `commit` operation behaves transactionally there. Resources MUST NOT expose `set_local` / `assert_local` / `commit_local` variants — that duplicates the API surface for a concern that belongs to handlers.

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

3. **Branch-aware Modify handler timeline**: when does the runtime install the compatible Modify handler at Branch entry? Today's runtime doesn't (Branch's eval-side wiring is partial). Until it does, `set` calls inside Branch are sticky regardless. *Recommendation: defer the implementation; bundle is a one-shot CLI without Branch use.*

4. **`Modify.get` on resources without get/set protocol**: KB / Store / WorkItemStore don't expose `get(s) -> S` because their state isn't a single value. Is this OK? *Recommendation: yes — `get`/`set` are the standard ops on Modify but resources can omit them when they don't fit. The framework allows.*

## Acceptance

Design-level proposal. Acceptance is:
1. Rules 1–8 accepted as binding for new state designs.
2. KB.assert / retract effect annotations updated (per open decision 1).
3. Proposals 027, 035, 036 reference this framework where they touch state semantics.
4. Future proposals introducing new state cite this framework or document why they diverge.

Once accepted, WI-192 implementation proceeds under the framework without re-litigating fundamentals.
