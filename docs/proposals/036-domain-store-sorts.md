# 036: Domain Store Sorts

## Status: Draft

## Tracks: WI-192

## Relates to: 037 (Modify framework — canonical state model; this proposal is a concrete consumer), WI-188 (entity copy), WI-189 (reify/reflect operators), WI-190 (quasi-quote patterns), WI-194 (commit), WI-195 (Error effect wired), WI-187 (IndexedFileStore — already landed), WI-200 (multi-instance Modify state — resolves the single-instance limitation noted below)

## Motivation

The `anthill-todo` bundle's read-side commands (status / show / list / graph / next) and mutating commands (add / feedback / claim / deliver / verify / delete / update / add-dependency / remove-dependency) all start with the same idiom:

```anthill
let raw_rows = rows_of(facts_of(kb(), "WorkItem"))
let row_map = build_row_map(raw_rows)
let dep_map = build_dep_map(raw_rows)
let fb_set = feedback_set()
```

That's ~120 lines of glue (build_row_map, build_dep_map_acc, register_dependents, feedback_set, collect_feedback_set, max_id_in, id_suffix_of, parse_wi_suffix, parse_int_or_zero, parse_int_acc, digit_value, pad3, status_for_m, direct_dependents_m, append_string, plus the cmd_X-side calls). Each command rebuilds the indexes; each Map value type is hand-rolled; the WorkItem-specific schema (id format, status partition, feedback membership) is scattered across helpers.

The pattern is "fact set + a few indexes + domain operations." That's a *sort* in anthill's existing vocabulary — algebra over data — refined for the `WorkItem` domain.

## What the surface looks like

`WorkItemStore` is the **anthill-todo subproject's** domain store — declared in the project's anthill source, alongside `WorkItem` itself. It does not live in the stdlib. Other projects that want a "store with custom indexes" declare their own (`UserStore`, `ProjectStore`, `RuleAuditStore`) using the same machinery.

The pluggable-backend story (file-system today, GitHub issues and remote API later — see `examples/github-todo/docs/pluggable-backend.md`) is handled at the **backend** level: WorkItemStore's `backend` field is typed as the abstract `Store` sort. Concrete Stores (FileStore, IndexedFileStore, future GitHubStore, future RemoteApiStore) all satisfy `Store` and plug in interchangeably. WorkItemStore itself is concrete — one piece of code, one set of operations — written once over the abstract Store interface.

```anthill
-- ─── Data shape: backend is abstract Store ─────────────────────────
-- The backend field is typed at the abstract `Store` sort (declared
-- in stdlib/anthill/persistence/store.anthill). Any value satisfying
-- `Store` can be plugged in: IndexedFileStore today; GitHubStore /
-- RemoteApiStore later. The WorkItemStore code is the same.
enum WIS
  entity wis(
    backend: Store,                       -- abstract; multiple impls
    by_id: Map[String, WorkItem],
    by_status: Map[WorkStatus, List[WorkItem]],
    id_counter: Int)
end

-- WorkItemStore = a mutable cell holding the WIS data. Cell's
-- protocol (Modify[s], get(s), set(s, v)) applies directly.
sort WorkItemStore = Cell[WIS]

-- Operations: one set, written once. Each takes s: WorkItemStore
-- (= Cell[WIS]) and uses Cell.get / Cell.set on it. Inside commit,
-- `persist(backend, ...)` dispatches via the Store spec — the
-- concrete backend (FileStore, GitHubStore, ...) determines what
-- runs there.
operation commit(s: WorkItemStore, w: WorkItem) -> Unit
  effects {Modify[s], Error}
=
  match Cell.get(s)
    case wis(backend, by_id, by_status, counter) ->
      let _ = persist(backend, w, Meta(entries: nil()))    -- Store spec dispatch
      let _ = flush(backend, nil())                         -- Store spec dispatch
      let updated = wis(backend, Map.put(by_id, w.id, w),
                        add_to_status(by_status, w.status, w),
                        counter + 1)
      Cell.set(s, updated)

operation lookup(s: WorkItemStore, id: String) -> Option[WorkItem]
=
  match Cell.get(s)
    case wis(_, by_id, _, _) -> Map.get(by_id, id)

-- (next_id, by_status_of, forget elided — same shape.)
```

The polymorphism is in the **backend**, not in WorkItemStore. Switching from local files to GitHub is a host-side decision: build `wis(github_store, ...)` instead of `wis(file_store, ...)`. The WorkItemStore code doesn't change; the Store dispatch carries the backend-specific semantics. This matches `pluggable-backend.md`'s framing — the *type of data sources* is configurable per project, but the WorkItem domain logic is the same.

Bundle's `cmd_add` collapses to:
```anthill
-- The bundle's commands take s: WorkItemStore (= Cell[WIS]). The
-- concrete backend behind s.backend is whatever the host plugged
-- in (IndexedFileStore today; GitHubStore / RemoteApiStore later)
-- — selected at startup, dispatched at every persist/flush call.
operation cmd_add(a: AddArgs, s: WorkItemStore) -> Int
  effects {ConsoleOutput, Modify[s], Error}
=
  let id = next_id(s)
  let wi = WorkItem(
    id: id, description: a.description,
    acceptance: a.acceptance, depends_on: a.depends,
    status: Open())
  let _ = commit(s, wi)
  let _ = println(console(),
                  concat("added: ", concat(id, concat(" — ", a.description))))
  0
```

No `Pair[Int, WorkItemStore]` return, no threading — `commit` mutates through `Modify[s]` (Cell's effect); the next `next_id(s)` (or any other read on `s`) sees the updated state. The Cell handle is stable across the call; the wrapped `wis(...)` value shifts.

`cmd_claim` collapses similarly:
```anthill
operation cmd_claim(a: ClaimArgs, s: WorkItemStore) -> Int
  effects {ConsoleOutput, ConsoleError, Modify[s], Error}
=
  match lookup(s, a.id)
    case none() -> ...error...
    case some(wi) ->
      let updated = wi.copy(status = Claimed(agent: a.agent, since: now()))
      let _ = commit(s, updated)
      0
```

The `wi.copy(...)` is WI-188 (entity copy form). Without it, we need an explicit re-construction or `replace_named_arg`.

## What language features the surface needs

Walking the surface above, here's what anthill must provide for it to actually work:

### 1. Entity-typed values flowing out of `facts_of` *(blocker)*

`Map[String, WorkItem]` says "values are typed at the WorkItem entity." Today `facts_of(kb(), "WorkItem")` returns `List[Term]` — opaque term handles. To put a typed WorkItem in the map, we need a coercion `Term → WorkItem` that the typer accepts.

This is **WI-189** (reify/reflect operators): `let wi: WorkItem = ↓term`.

**Without WI-189**, we can fall back to `Map[String, Term]`. The map carries Term values; `lookup` returns `Option[Term]`; field access still goes through `term_field` / `term_as_string`. That's a partial win — consolidates the indexes but keeps the reflection surface in command bodies.

### 2. Mutating commit through the Modify framework *(not a blocker — already exists)*

Defining `WorkItemStore = Cell[WIS]` resolves the "how does Modify[s] apply to an entity?" question structurally: the bundle's `s: WorkItemStore` IS a Cell handle (via the type alias). Cell's protocol — `Modify[c]`, `get(c)`, `set(c, v)` — applies straight from the framework. No new state-bearing sort to design; no muddled handle-vs-value question.

What commit does, end-to-end:

| Step | What runs | Effect |
|---|---|---|
| 1 | `match Cell.get(s)` | Reads s's cell slot. Returns the current `wis(b, m1, m2, c1)`. |
| 2 | `case wis(backend, by_id, by_status, counter)` | Destructures the returned value, binding `backend`, `by_id`, etc. locally. |
| 3 | `persist(backend, w, ...)` | Goes through Store's handler keyed by `backend`. Mutates the store's slot (writes the file, calls the API, etc., depending on the concrete Store impl). `backend` handle unchanged. |
| 4 | `let updated = wis(backend, Map.put(by_id, ...), ..., counter + 1)` | Constructs a fresh wis term. Pure. |
| 5 | `Cell.set(s, updated)` | Goes through Cell's handler keyed by `s`. Overwrites the cell's slot with `updated`. `s` handle unchanged. |
| 6 | (later) `Cell.get(s)` from any other operation | Returns `updated`. |

Two distinct mutations: Store's slot in step 3, Cell's slot in step 5. They go through two separate handlers (Store's, Cell's), each keyed by its own resource. The `Modify[s]` declaration on commit's signature covers both transitively (per 037's transitivity rule — `s.backend` is reachable from `s`).

The host's startup work: build the initial `wis(...)` value (walks `facts_of("WorkItem")`, fills the maps, scans `id_counter`), allocate a `Cell[WIS]`, seed it with `Cell.set(handle, initial)`, pass the handle into `Main.main`.

#### `Modify[s]` covers the backend reach

A reader might expect `commit` to declare `Modify[backend]` separately since the body calls `persist(backend, ...) effects {Modify[store], Error}`. It doesn't need to: per 037's transitivity rule, `Modify[s]` covers any component reachable through s — including the backend reachable via `Cell.get(s).backend`. The declaration `effects {Modify[s], Error}` is the conservative bound: "anything reachable from s may change," which includes the disk write.

Handler dispatch at the call site stays per-resource: `persist(backend, ...)` goes through the Store handler keyed by `backend`, while `Cell.set(s, ...)` goes through Cell's handler keyed by `s`. Transitivity is a typing/effect-row concern, not a runtime-dispatch one.

#### Branch-interaction propagates through `s`'s components

The Branch-interaction reasoning has to follow reachability the same way. `Cell[WIS]`'s state is value-tree, so it could in principle be branch-local-snapshot. But the wis value's `backend` field is a `Store`, which 037 declares **sticky-by-physics** for filesystem-backed impls — the filesystem can't roll back atomically. Since `commit` transitively mutates whatever the backend mutates, the cell's effective contract under Branch is the *intersection* of its components, dominated by the most-restrictive component (the backend). For a file-backed Store, that's sticky-by-physics overall; for a hypothetical purely-in-memory mock backend, branch-local-snapshot would be admissible. Until the framework grows path effects + per-component contract reasoning (or a buffered Store handler absorbs disk writes for the branch's duration, or a static constraint rejects `commit` inside Branch — analogous to the Branch+Consumes constraint from 027), `commit` cannot be called soundly inside `Branch` against a sticky-by-physics backend. For the bundle's v0.1 (one-shot CLI, no Branch use), this is not load-bearing — the gap is documented at the framework level (037 §"Store" contract row).

A switch to a different backend (GitHub issues, remote API) plugs in via the abstract `Store` field. The cell's effective Branch behavior is dictated by whichever concrete Store the host wires in; the WorkItemStore code doesn't change.

#### Forward compatibility with time-travel

A future time-travel handler (versioned state, audit trails, history queries) should coexist with `Modify` without breaking changes. WorkItemStore's design satisfies the five forward-compat invariants of 037 §"With time-travel":

1. `set(s, v)`'s observable contract is "next `get(s)` returns `v`."
2. `get(s)` returns the current head; `get_at` (if added later) lives under a separate `TimeTravel[s]` effect.
3. `Modify[s]` doesn't expose handler-internal structure.
4. `set` returns `Unit`, not the prior value.
5. Operation signatures don't encode rollback policy — that's the resource's contract.

WorkItemStore's design satisfies all five — `commit` calls `set` returning `Unit`; `lookup` calls `get`; only `Modify[s]` is declared. A future time-travel handler could substitute a versioned representation of the `wis(...)` Value without changing any user-visible code.

#### Single-instance-per-functor limitation

Today's transitional Rust scheme (the type-independent `default_modify_handler`) keys cells by **functor symbol only** — `wis(...)` regardless of field values shares a single cell. Two `wis(backend_a, ..., counter: 5)` and `wis(backend_b, ..., counter: 10)` collide. This is fine for the bundle's WI-192 use case (one CLI invocation = one project = one WorkItemStore) but breaks for multi-instance scenarios:

- Tests that exercise `cmd_X` against multiple isolated stores in the same process.
- A future `anthill-todo-server` managing N project workspaces.
- Composition where two operations independently want isolated state of the same sort type.

Per 037, identity is a property of the *handler* (`ModifyHandler[Resource, IdentityKey]`), not the resource sort. The framework permits three identity schemes for the handler to pick:

- **Functor-only** (`IdentityKey = Unit`) — current scheme; one slot per Resource type.
- **Identity-by-key** (`IdentityKey = String / Int / IdentityKey` opaque type, computed via a sort-declared `key` operation) — multi-instance via a domain key the user supplies (project name, workspace id).
- **Opaque-handle** (`IdentityKey = ` allocation-time uid) — multi-instance via fresh handles per construction.

WI-200 tracks the runtime work to wire per-resource handlers under these schemes. Until WI-200 lands, every Modify-using resource is functor-keyed. WI-192 v0.1 ships under this limitation and uses functor-only on purpose (single-store bundle). Documented here so the limitation is visible at design-review time, not surprise at multi-tenant time.

So a WorkItemStore.commit body looks like:

```anthill
operation commit(s: WorkItemStore, w: WorkItem) -> Unit
  effects {Modify[s], Modify[backend], Error}
=
  match get(s)
    case wis(backend, by_id, by_status, counter) ->
      let _ = persist(backend, w, Meta(entries: nil()))
      let _ = flush(backend, nil())
      let updated = wis(backend, Map.put(by_id, w.id, w),
                        add_to_status(by_status, w.status, w),
                        counter + 1)
      set(s, updated)
```

`s` at every call site is just the resource handle. Inside the body, `get(s)` reads the current `wis(...)` value, `set(s, new)` writes the next one — these are Cell's standard operations dispatched via the Modify effect machinery (per 037's per-resource interpreter contract for WorkItemStore). Identity of `s` is stable across calls; the state behind it shifts.

Under v0.1's transitional handler scheme (functor-only identity), the field values inside `s` don't participate in state lookup — the runtime keys all `wis(...)` calls to one slot. That matches the bundle's single-store usage. When WI-200 lands and Cell migrates to opaque-handle identity, `s`'s allocation-time uid will become the keying scheme — multi-store usage falls out without changing user-visible code.

The only runtime work needed at startup: the host calls `Modify.set(wis_handle, initial_wis)` once, seeding the cell. That's a single effect dispatch through machinery that already works.

Earlier drafts considered three other options (functional threading; a new Cell value variant; a separate registry pattern duplicating what Modify already does). All inferior to using the framework as-is. Discarded.

#### Note: registries and state are the same idea

This is the framework's central observation, spelled out in 037 §3 "Type-specific Modify handlers": the Modify cell, the host store registry, KB indexes, arenas, source maps are all *handlers for resource-specific Modify effects*. They differ in state representation; they are uniform in dispatch. WorkItemStore's state happens to be value-shaped, so it plugs into the Cell-style handler with no new machinery. Resources whose state spills outside the Value model (e.g. FileStore's per-instance backend objects) get a different state-representation choice but the same dispatch architecture.

Cross-reference 037 for the full framework; WI-192 is its first end-to-end consumer.

### 3. Map keys at sort `WorkStatus` *(may be blocker)*

`Map[WorkStatus, ...]` — `WorkStatus` is an enum (`Open` / `Claimed` / `Delivered` / `Verified` / `Rejected` / ...). `Map.put` / `Map.get` use `MapKey::try_from_value`. Today MapKey supports Int / Bool / Str / Term. An enum-entity value is `Value::Entity` — does the existing builtin handle that?

Probably not directly. We'd need either:
- Extend `MapKey` to handle `Value::Entity` (keying by canonical form, like `store_canonical_key`).
- Use `String` keys instead (`Map[String, ...]`, status name as the key).

The String workaround is fine for the bundle's use case but is a paper cut. **Filing as WI-197 candidate**: extend Map keys to entity values via canonical-form hashing.

### 4. Construction at host (Rust) side *(implementation, not language)*

The host needs to build the initial `wis(...)` entity. That requires:
- Reading facts via `facts_of`.
- Building `Map<MapKey, Value>` Rust-side (the runtime representation).
- Constructing the `Value::Entity { functor: wis_sym, named: [...] }` with Map-typed values.
- Registering it for the bundle's `Main.main` call.

No language feature. Just plumbing in `run_anthill_bundle`.

### 5. Bundle ports its commands *(implementation, not language)*

Mechanical: each command body rewrites to use `next_id` / `lookup` / `by_status_of` / `commit` / `forget`. About 120 lines retire from main.anthill.

### 6. Optional: Sort refinement / `requires Store` *(nice-to-have, not blocking)*

The original framing said `sort WorkItemStore { requires Store; ... }` — declaring that WorkItemStore IS-A Store. That'd let WorkItemStore be passed to generic `persist` / `flush`. But the bundle doesn't NEED that — it only needs domain ops. Drop the `requires Store` clause; `WorkItemStore` is a fresh sort that *uses* a Store via the `backend` field.

(If we ever want WorkItemStore to be polymorphic over backend type — `IndexedFileStore`, `IndexedSqlStore`, etc. — `requires Store` becomes meaningful. Out of scope for v0.1.)

### 7. Optional: `entity wis with backend, ...` syntax *(nice-to-have, depends on WI-188)*

Constructing a new wis with one field changed (e.g., during commit) is `wis.copy(by_id = ...)` if WI-188 lands. Without it, manual reconstruction:
```anthill
match s
  case wis(b, _, by_status, c) -> wis(b, new_by_id, by_status, c)
```

Mechanical and ugly. Functional path costs more lines without WI-188.

## Implementation strategies

Given the language facilities, two landings are reasonable:

### Strategy A: minimal v0.1, Modify state, today

- WorkItemStore uses `Map[String, Term]` (not WorkItem) — sidesteps WI-189.
- by_status keyed by status name `String` — sidesteps Map-key-at-entity-value gap (the existing `MapKey` only handles Int/Bool/Str/Term, not enum-Entity values).
- `commit` mutates via `Modify[s]` state semantics (already wired via `default_modify_handler`). Threading is *not* needed.
- Bundle commands take `(s: WorkItemStore, ...)` and return `Int` (no threading); commit fires `set(s, new)` internally.
- Construction at host: build initial `wis(...)` Value at startup, fire `Modify.set(wis_handle, initial)` once before `Main.main`.

**Cost to land:** ~1-2 days. ~30 lines of new sort declaration + ~30 lines of host plumbing + ~150-line refactor of bundle commands. No language changes.

**What's lost vs the ideal:** type-safe field access (commands still use `term_field` / `term_as_string` to read individual WorkItem fields); status-key strings instead of WorkStatus enum values.

**What's gained:** the indexes are centralized in one place; the ~120 lines of glue retire; commands are linear (no threading, no `Pair[Int, S]` return); the abstraction shape matches the ideal end-state.

### Strategy B: land alongside WI-188 + WI-189

- WI-188 enables `wi.copy(status = ...)` for in-place field updates.
- WI-189 lets `Map.get(by_id, id)` return `Option[WorkItem]` with native field access (`wi.id`, `wi.status`).
- Map values typed `WorkItem`; lookup typed too; commands stop calling `term_field`.

**Cost to land:** 1-2 weeks (WI-188 + WI-189 as prerequisites, then ~1 day to retype WorkItemStore over `WorkItem` instead of `Term`).

**What's lost vs the ideal:** still status keyed by name string. Closes when WI-197 (entity-values-as-Map-keys) lands.

## Recommendation

**Land Strategy A first**, file the gap-closing WIs (WI-188 / WI-189 / WI-197) as follow-ups for Strategy B.

Rationale:
- Strategy A demonstrates the abstraction with zero language changes. The bundle's structure improves immediately, no threading verbosity.
- The follow-up WIs each have independent value beyond the bundle.
- Strategy A's two paper cuts (Term values in maps, name-keyed status) are localized to ~5 places and shrink to nothing as the gap-closers land. No throwaway work.

## Decomposition

`WorkItemStore` is project-side: it lives in `anthill-todo/`'s anthill source alongside `domain.anthill` and `rules.anthill`. The bundle's binary embeds it via the existing `BulkStore::pull` path (any `.anthill` file in the project's anthill-todo/ directory is loaded at startup). No bundle-side declaration; the project owns its store sort.

Files affected:
- `stdlib/anthill/persistence/filesystem.anthill` — declare `entity IndexedFileStore(root: String, convention: FileConvention)`. Today only `FileStore` is declared even though the bundle's host already wires an `IndexedFileStore` Rust impl behind a `FileStore` Value::Entity (canonical-key shape coincides). Adding the entity makes the Value-side type honest. Both entities can coexist (FileStore for projects that don't need source-span retract; IndexedFileStore for those that do).
- `anthill-todo/store.anthill` — **new project-side file** declaring `sort WorkItemStore`, the `wis` entity, and the `next_id` / `lookup` / `by_status_of` / `commit` / `forget` operations. Operation bodies in anthill (no Rust builtins for v0.1). Loaded at runtime via the project's BulkStore::pull, just like domain.anthill and rules.anthill today.
- `rustland/anthill-todo/src/main.rs` (`run_anthill_bundle`) — switch the constructed Value::Entity functor from `FileStore` to `IndexedFileStore`; construct the initial `wis(...)` value at startup (walk facts_of("WorkItem"), build the maps, scan id_counter); fire `Modify.set(wis_handle, initial_wis)` once before `Main.main` runs. Pass `wis_handle` to `Main.main` as a 4th arg.
- `rustland/anthill-todo/anthill/main.anthill` — `main` / `dispatch` thread the WorkItemStore handle (no contents — just a handle for Modify state to key against); each command body uses store ops; the ~120 lines of build_row_map / build_dep_map / feedback_set / next_workitem_id / max_id_in / pad3 / etc. retire.

Other projects that adopt this pattern (UserStore, ProjectStore, RuleAuditStore) follow the same shape: declare in their own project, host wires the initial state, command bodies use store ops. The pattern is *not* anthill-todo-specific — what's anthill-todo-specific is the WorkItem domain.

## Out of scope

- WI-189 (reify/reflect operators) — see Strategy A vs B.
- WI-188 (entity copy form) — same.
- WI-194 (commit / transactions) — Strategy A uses Modify-state commit (already wired), no separate commit op needed. WI-194 (transactional batches: persist + retract atomically with rollback on Error) becomes useful for cmd_claim/deliver/verify's retract+persist pair but is independent of WI-192.
- WI-197 candidate (Map keys at entity values) — sidestepped via String keys.
- IndexedFileStore vs other Store backends — WorkItemStore is composed over an IndexedFileStore today; trait-driven backend swap is out of scope.

## Acceptance

- `rustland/anthill-todo/anthill/main.anthill` drops the ~120 lines of map-building / id-parsing / format glue listed above.
- `cargo test` green; existing cmd_X integration tests still pass.
- Live `anthill-todo --anthill list` / `graph` perf parity or better with WI-183 (the indexes are still O(1) lookups, just shifted from per-command rebuild to one-shot at startup).
