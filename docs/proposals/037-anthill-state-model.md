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
  operation set(c: Cell[V], value: V) -> Unit                  -- sticky write
    effects Modify[Cell[V]]
  operation set_local(c: Cell[V], value: V) -> Unit            -- transactional write
    effects Modify[Cell[V]], Branch
end
```

`Cell[V]` is a concrete sort: "a typed mutable cell holding a V." It exposes the standard get/set/set_local protocol of proposal 027 — the State monad encoding via effect handlers.

Resources that fit "small typed state you read and overwrite" declare themselves as `Cell[V]` and inherit the protocol. A counter is `Cell[Int]`. A flag is `Cell[Bool]`. A small record is `Cell[MyRecord]`.

Resources that DON'T fit the Cell protocol — KB, Store, WorkItemStore, Map, Substitution, Stream — declare their own sorts with their own operations. They still carry `Modify[their_sort]` on mutating ops; they just don't use Cell's get/set protocol.

### 3. Type-specific Modify handlers — the dispatch story

For every resource type T whose operations mutate, there's a Modify handler installed at startup. Operations on T raise `Modify[T]` effect; the dispatcher routes to T's handler. The handler implements T's specific operations.

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

A *resource type* is any anthill sort whose values can be mutated through `Modify[T]`. To plug T into the framework, the resource declares:

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

- **Handler-dispatched**: operation raises an effect → effect handler intercepts → handler accesses state. Today's path for `Modify.set` / `Modify.get` / `Modify.set_local` (the standard ops on Modify).
- **Direct builtin**: operation maps to a Rust function that directly accesses state. Today's path for everything else (Store.persist, KB.assert, Map.put).

The framework PERMITS both. Handler-dispatched is more flexible (substitute test handlers, audit handlers); direct is faster. A resource may start direct and migrate to handler-dispatched later without changing the type-level surface.

The crucial invariant: **the effect annotation is the same regardless of dispatch path.** `Modify[T]` is stable across implementation choices.

## Composition rules

### With Branch (sticky vs transactional)

Per proposal 027 §4:

- `set(target, v)` — sticky. Mutation persists across `Branch` backtrack. Default for irreversible writes (committed state).
- `set_local(target, v)` — transactional. Mutation rolled back via `register_undo` on snapshot abandon. Required when in a Branch context and you want speculative writes.
- The same protocol applies to resource-specific ops: a resource may expose `commit_local` / `assume` / etc. as transactional variants of its sticky operations.

The framework requires: if a resource exposes a sticky operation, it MAY also expose a transactional variant; if it does, the variant carries `Modify[T] + Branch` and uses `register_undo` for rollback.

### With other Modify effects

Operations can declare multiple `Modify[X]` effects, one per resource they touch:

```anthill
operation commit(s: WorkItemStore, w: WorkItem) -> Unit
  effects {Modify[s], Modify[backend], Error}    -- modifies both s and s.backend
```

The framework treats these independently — handlers for Modify[s] and Modify[backend] are separate. There's no automatic transitivity (Modify[s] does NOT imply Modify[anything reachable from s]).

If transitivity is desired (path-based effects), the operation declares it explicitly. Future proposal could add path syntax (`Modify[s.backend]` resolves at type-check time).

### With Error

`Modify[T]` operations that can fail also declare `Error`. The framework doesn't tie them: a sticky `set` that fails leaves the state pre-mutation (the handler simply doesn't write); a transactional `set_local` rolls back via the existing snapshot mechanism. Error is orthogonal to sticky/transactional.

### With time-travel (forward-compat invariants)

Five invariants the framework holds for any T, so a future time-travel handler can substitute a versioned representation without breaking existing code:

1. `set(target, v)` — observable contract is "next get returns v." Handler implementation hidden.
2. `get(target)` returns the current head. Time-travel adds `get_at` under a separate `TimeTravel[s]` effect.
3. `Modify[T]` surface doesn't expose handler-internal structure.
4. `set` returns `Unit` (not the prior value).
5. Sticky vs transactional encoded in the operation, not the handler.

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

### Rule 5: Sticky default; transactional opt-in via `_local` suffix

`set` is sticky; `set_local` is transactional and requires Branch. Resources following the same pattern (e.g., `commit` / `commit_local`) match this convention.

### Rule 6: Multi-instance via declared identity

A resource that supports multiple instances declares its identity scheme (functor / by-field / opaque). The default is functor-only (single instance) until the resource opts into multi-instance.

### Rule 7: Forward compatibility with time-travel (the five invariants from §"Composition with time-travel")

Operations on resources observe these invariants so a future time-travel handler can layer in.

## Open decisions before WI-192 implements

The framework above leaves these open; they need answers before WI-192's WorkItemStore lands:

1. **KB.assert effect declaration**: change reflect.anthill to add `Modify[kb]` on assert/retract. Mechanical change; needed for honesty per Rule 1. *Recommendation: yes, do it as part of this proposal's acceptance.*

2. **WorkItemStore identity scheme**: functor-only (single instance) or one of the WI-200 schemes? *Recommendation: functor-only for v0.1; revisit when multi-instance need arises.*

3. **`set_local` implementation timeline**: implement now to support transactional retract+persist, or defer (and document that bundle commands aren't atomic on Error)? *Recommendation: defer; bundle is a one-shot CLI where atomicity gain is small.*

4. **`Modify.get` on resources without get/set protocol**: KB / Store / WorkItemStore don't expose `get(s) -> S` because their state isn't a single value. Is this OK? *Recommendation: yes — `get`/`set` are the standard ops on Modify but resources can omit them when they don't fit. The framework allows.*

## Acceptance

Design-level proposal. Acceptance is:
1. Rules 1–7 accepted as binding for new state designs.
2. KB.assert / retract effect annotations updated (per open decision 1).
3. Proposals 027, 035, 036 reference this framework where they touch state semantics.
4. Future proposals introducing new state cite this framework or document why they diverge.

Once accepted, WI-192 implementation proceeds under the framework without re-litigating fundamentals.
