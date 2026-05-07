# 036: Domain Store Sorts

## Status: Draft

## Tracks: WI-192

## Relates to: WI-188 (entity copy), WI-189 (reify/reflect operators), WI-190 (quasi-quote patterns), WI-194 (commit), WI-195 (Error effect wired), WI-187 (IndexedFileStore — already landed)

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

`WorkItemStore` is the **anthill-todo subproject's** domain store sort — declared in the project's anthill source, alongside `WorkItem` itself. It does not live in the stdlib. Other projects that want a "store with custom indexes" declare their own (`UserStore`, `ProjectStore`, `RuleAuditStore`) using the same machinery.

The general pattern — *declare a sort that wraps a Store with project-specific indexes and operations* — is what's important. anthill-todo uses it for WorkItem; the example below is what that project files declare.

```anthill
sort WorkItemStore
  -- A WorkItemStore instance carries the file-backed store plus
  -- precomputed indexes for the queries the bundle needs. The
  -- indexes are entity-fields, not a new "index" keyword — anthill's
  -- existing entity machinery is enough.
  entity wis(
    backend: IndexedFileStore,
    by_id: Map[String, WorkItem],
    by_status: Map[WorkStatus, List[WorkItem]],
    id_counter: Int)

  -- Construction. Walks the backend's facts once; builds the maps
  -- and the id counter. Called once at startup by the host.
  operation from_backend(backend: FileStore) -> WorkItemStore

  -- Domain queries. O(1) Map.get over the precomputed indexes.
  -- `next_id` mutates: it increments the counter and returns the
  -- resulting id, so two calls produce distinct ids. `lookup` and
  -- `by_status_of` are pure reads.
  operation next_id(s: WorkItemStore) -> String
    effects Modify[s]
  operation lookup(s: WorkItemStore, id: String) -> Option[WorkItem]
  operation by_status_of(s: WorkItemStore, st: WorkStatus)
    -> List[WorkItem]

  -- Mutation. Persists the work item to the backend, updates each
  -- index, increments the counter. The Modify[s] effect dispatches
  -- through the existing default_modify_handler — get(s) reads the
  -- current state, set(s, new) writes the next one. Identity of s
  -- is stable across calls; the state behind it shifts.
  operation commit(s: WorkItemStore, w: WorkItem) -> Unit
    effects {Modify[s], Modify[backend], Error}

  operation forget(s: WorkItemStore, id: String) -> Unit
    effects {Modify[s], Modify[backend], Error}
end
```

Bundle's `cmd_add` collapses to:
```anthill
operation cmd_add(a: AddArgs, s: WorkItemStore) -> Int
  effects {ConsoleOutput, Modify[s], Modify[backend], Error}
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

No `Pair[Int, WorkItemStore]` return, no threading — `commit` mutates through the Modify[s] effect; the next `next_id(s)` (or any other read on `s`) sees the updated state. Identity of `s` is stable across the call; contents shift behind it.

`cmd_claim` collapses similarly:
```anthill
operation cmd_claim(a: ClaimArgs, s: WorkItemStore) -> Int
  effects {ConsoleOutput, ConsoleError, Modify[s], Modify[backend], Error}
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

### 2. Mutating commit through state semantics *(not a blocker — already exists)*

`commit` updates `backend`, `by_id`, `by_status`, `id_counter` together. Looking at what anthill already has:

`stdlib/anthill/prelude/effects.anthill` declares `Modify[T]` with `get(target: T) -> T` and `set(target: T, value: T) -> Unit effects Modify[T]`. That's the State monad. `eval/effects.rs::default_modify_handler` implements it as a `HashMap<Symbol, Value>` keyed by resource functor — the functor symbol of the target value identifies the cell; the stored Value is whatever was last `set`.

Per proposal 027 §4, `Modify` has two write ops: sticky `set` and transactional `set_local`. `set` mutations persist across `Branch` backtracks; `set_local` rolls back via the `register_undo` snapshot mechanism. WorkItemStore's `commit` uses sticky `set` — once a WorkItem is persisted to disk and the indexes updated, that state is irreversible; a search-branch backtrack must not roll the maps back into a state that contradicts what's on disk. (Today `set_local` isn't wired; v0.1 lands with `set` only, which is what `commit` needs anyway.)

#### Forward compatibility with time-travel

A future time-travel effect (versioned resources, audit trails, history queries) should coexist with `Modify` without breaking changes. Five design invariants preserve that compatibility:

1. **`set(target, v)` is "advance the head."** The observable contract is "next `get(target)` returns `v`." Whether the handler overwrites a single cell or appends to a version graph is hidden behind that contract. The same `set` works under both default and time-travel handlers.

2. **`get(target)` returns the current head.** Always. Time-travel adds `get_at(target, version)` as a *new operation* under a *separate* effect (`TimeTravel[s]`), not as a refinement of `get`.

3. **`Modify[s]` doesn't expose handler-internal structure.** The user-facing surface is `get` / `set` / `set_local`. The handler may store cells as single values or version graphs; the effect's surface doesn't observe the difference.

4. **`set` returns `Unit`, not the prior value.** Returning the displaced value would force the handler to materialize old state even when no history is kept. Callers that need the prior value `get` first.

5. **Sticky vs transactional is encoded in the *operation*, not the handler.** `set` is sticky; `set_local` is transactional. Different ops, same handler. (Today's design.)

WorkItemStore's design satisfies all five invariants — `commit` calls `set` returning `Unit`; `lookup` calls `get`; only `Modify[s]` is declared; no `set_versioned` / `get_at` is mixed in. A future time-travel handler could substitute a versioned representation without changing any user-visible code.

#### Single-instance-per-functor limitation

The default Modify handler keys cells by **functor symbol only** (`eval/effects.rs::resource_key`). Two `wis(backend_a, ..., counter: 5)` and `wis(backend_b, ..., counter: 10)` share a single cell — setting one is observable to the other. This is fine for the bundle's WI-192 use case (one CLI invocation = one project = one WorkItemStore) but breaks for multi-instance scenarios:

- Tests that exercise `cmd_X` against multiple isolated stores in the same process.
- A future `anthill-todo-server` managing N project workspaces.
- Composition where two operations independently want isolated state of the same sort type.

Three design directions for future multi-instance support — each a candidate WI:

- **Identity-by-field**: sort declares which entity field carries instance identity; cells key by `(functor, identity_value)`.
- **Opaque resource handles**: new `Value::Resource(uid)` variant; cells key by uid; mkResource allocates a fresh uid per construction.
- **Per-instance handler scope**: `with_handler(Modify, instance_handler) { ... }` lexically introduces a scoped handler owning one instance's state.

WI-192 v0.1 ships with the single-instance limitation. Multi-instance is a separate proposal — likely a generalization of `resource_key` paired with one of the three options above. Documented here so the limitation is visible at design-review time, not surprise at multi-tenant time.

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

`s` at every call site is just the resource handle — its field values don't matter because the Modify handler keys by functor symbol (`wis`). Inside, `get(s)` reads the current state, `set(s, new)` writes the next one. Identity of `s` is stable across calls; the state behind it shifts.

The only runtime work needed: at startup, the host calls `Modify.set(wis_handle, initial_wis)` once — seeding the cell. That's a single effect dispatch through machinery that already works.

Earlier drafts of this doc considered three other options (functional threading; a new Cell value variant; a separate registry pattern duplicating what Modify already does). All inferior to using existing state semantics. Discarded.

#### Note: registries and state are the same idea

The runtime today has multiple state stores: the Modify cell, `store_registry`, `IndexedFileStore.source_map`, map_arena, subst_arena, stream_arena, the KB indexes themselves. They differ in (key shape, value shape, access surface), but conceptually they're all instances of the same primitive — *mutable state keyed by identity*. The split between "Modify cell" and "host registry" is forced when the state can't be expressed as an anthill `Value` (FileStore's `Box<dyn Store>` internals, for example). When the state IS expressible as Values — as with WorkItemStore's `(backend, by_id, by_status, id_counter)` — the Modify cell suffices and no new registry is needed.

A future "first-class resources" proposal could unify these into one abstraction, but it's not on WI-192's path. WI-192 uses the Modify cell as-is; a later refactor could rewire all the registries under a single mechanism without changing user-visible code.

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
