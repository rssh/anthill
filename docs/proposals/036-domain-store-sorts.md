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

A new sort, declared in the project (or in the bundle when shipping rust+anthill):

```anthill
sort WorkItemStore
  -- A WorkItemStore instance carries the file-backed store plus
  -- precomputed indexes for the queries the bundle needs. The
  -- indexes are entity-fields, not a new "index" keyword — anthill's
  -- existing entity machinery is enough.
  entity wis(
    backend: FileStore,
    by_id: Map[K = String, V = WorkItem],
    by_status: Map[K = WorkStatus, V = List[T = WorkItem]],
    id_counter: Int)

  -- Construction. Walks the backend's facts once; builds the maps
  -- and the id counter. Called once at startup by the host.
  operation from_backend(backend: FileStore) -> WorkItemStore

  -- Domain queries. O(1) Map.get over the precomputed indexes.
  operation next_id(s: WorkItemStore) -> String
  operation lookup(s: WorkItemStore, id: String) -> Option[T = WorkItem]
  operation by_status_of(s: WorkItemStore, st: WorkStatus)
    -> List[T = WorkItem]

  -- Mutation. Persists the work item to the backend, updates each
  -- index, increments the counter. The Modify[s] effect carries
  -- "this operation may write to s" through to the typer; the
  -- Error effect propagates underlying-store failures (WI-195).
  operation commit(s: WorkItemStore, w: WorkItem) -> WorkItemStore
    effects {Modify[s], Error}

  operation forget(s: WorkItemStore, id: String) -> WorkItemStore
    effects {Modify[s], Error}
end
```

Bundle's `cmd_add` collapses to:
```anthill
operation cmd_add(a: AddArgs, s: WorkItemStore) -> Pair[Int, WorkItemStore] =
  let id = next_id(s)
  let wi = WorkItem(
    id: id, description: a.description,
    acceptance: a.acceptance, depends_on: a.depends,
    status: Open())
  let s2 = commit(s, wi)
  let _ = println(console(),
                  concat("added: ", concat(id, concat(" — ", a.description))))
  pair(0, s2)
```

`cmd_claim` collapses similarly:
```anthill
operation cmd_claim(a: ClaimArgs, s: WorkItemStore) -> Pair[Int, WorkItemStore] =
  match lookup(s, a.id)
    case none() -> ...error...
    case some(wi) ->
      let updated = ... wi with status = Claimed(agent, since) ...
      pair(0, commit(s, updated))
```

The `... wi with ...` is WI-188 (entity copy form). Without it, we need an explicit re-construction or `replace_named_arg`.

## What language features the surface needs

Walking the surface above, here's what anthill must provide for it to actually work:

### 1. Entity-typed values flowing out of `facts_of` *(blocker)*

`Map[K = String, V = WorkItem]` says "values are typed at the WorkItem entity." Today `facts_of(kb(), "WorkItem")` returns `List[Term]` — opaque term handles. To put a typed WorkItem in the map, we need a coercion `Term → WorkItem` that the typer accepts.

This is **WI-189** (reify/reflect operators): `let wi: WorkItem = ↓term`.

**Without WI-189**, we can fall back to `Map[K = String, V = Term]`. The map carries Term values; `lookup` returns `Option[Term]`; field access still goes through `term_field` / `term_as_string`. That's a partial win — consolidates the indexes but keeps the reflection surface in command bodies.

### 2. Either functional commit (return new store) or real Modify effect *(blocker)*

`commit` updates `backend`, `by_id`, `by_status`, `id_counter` together. Three options:

- **(A) Functional**: `commit` returns a `WorkItemStore`. Caller threads. Pure, composes well, but every command's signature gains the threading and dispatch-level returns become `Pair[Int, WorkItemStore]` (or similar). Verbose at call sites.

- **(B) Cell semantics** *(heavier than I first thought; probably not the right path)*: `WorkItemStore` becomes a first-class mutable cell — a new Value variant with arena-managed contents that `Modify[s]` writes through. Requires a new value kind, typer rules for cell coercion, effect-dispatch wiring. Conceptually clean but adds a significant new runtime concept.

- **(C) Registry pattern**: The `FileStore` pattern, scaled up. `wis(backend)` is a *passive handle* — its only field is the backend reference, which (combined with the sort) forms a canonical key. The actual maps + counter live in interpreter-side Rust state keyed by that canonical string. Operations (`next_id` / `lookup` / `commit`) are Rust builtins that look up the state by key and mutate. `Modify[s]` is annotation; real mutation is the registry's job. Same machinery as today's `FileStore` / `IndexedFileStore`, just one more registry. ~1 week of plumbing.

(C) is the right path for the maximalist landing. (A) is doable today with no runtime support. (B) is overkill — we don't need a general cell construct to solve this specific problem.

### 3. Map keys at sort `WorkStatus` *(may be blocker)*

`Map[K = WorkStatus, V = ...]` — `WorkStatus` is an enum (`Open` / `Claimed` / `Delivered` / `Verified` / `Rejected` / ...). `Map.put` / `Map.get` use `MapKey::try_from_value`. Today MapKey supports Int / Bool / Str / Term. An enum-entity value is `Value::Entity` — does the existing builtin handle that?

Probably not directly. We'd need either:
- Extend `MapKey` to handle `Value::Entity` (keying by canonical form, like `store_canonical_key`).
- Use `String` keys instead (`Map[K = String, V = ...]`, status name as the key).

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

Given the language gaps above, three landings are possible:

### Strategy A: minimal v0.1, no language extensions

- Use `Map[K = String, V = Term]` (not WorkItem) — sidesteps WI-189.
- Use `Map[K = String, V = ...]` for by_status keyed by status name string — sidesteps the enum-key gap.
- Functional `commit` — caller threads — sidesteps the Modify mutability gap.
- Bundle commands take `(s: WorkItemStore, ...)` and return `Pair[Int, WorkItemStore]` where they mutate.

**Cost to land:** ~1-2 days. ~30 lines of new sort declaration + ~50 lines of host plumbing + ~150-line refactor of bundle commands.

**What's lost vs the ideal:** type-safe field access (still uses term_field/term_as_string in commands); threading verbosity at call sites; status-key strings instead of WorkStatus values.

**What's gained:** the indexes are centralized in one place; the ~120 lines of glue retire; the bundle's structure mirrors the design even if surface ergonomics aren't ideal.

### Strategy B: land alongside WI-188 + WI-189

- Wait for entity copy (`wi.copy(status = ...)`) — eliminates manual reconstruction.
- Wait for `↓Term : WorkItem` — type-safe field access via `wi.id`, `wi.status` etc.
- Map values are typed `WorkItem`; lookup returns `Option[WorkItem]` with native field access.
- Functional `commit` still threads but is one-line per call site.

**Cost to land:** 1-2 weeks (WI-188 + WI-189 as prerequisites, then 1-2 days for WI-192).

**What's lost:** still functional threading; still status keyed by name (or wait for entity-as-key).

### Strategy C: land alongside WI-188 + WI-189 + registry-pattern commit (WI-194 maximalist)

- Same as B plus: `commit` mutates the registry-side `WorkItemStoreState` via a Rust builtin (the same pattern `FileStore::persist` uses today, just with a richer state struct).
- Bundle commands take `s: WorkItemStore`, never return one. Threading retires entirely. Modify[s] is annotation; real mutation is the registry's job.

**Cost to land:** ~2 weeks (1 week for WI-188+189, ~1 week for the registry pattern + builtins + bundle ports).

**What's gained:** the ideal shape from the WI-191/192/194 brainstorm. Command bodies are linear, no threading, Error propagates to top-level handler.

## Recommendation

**Land Strategy A first, file the gap-closing WIs as follow-ups.**

Rationale:
- Strategy A demonstrates the abstraction with zero language changes. The bundle's structure improves immediately.
- The follow-up WIs (188 / 189 / 194 / 197) each have independent value beyond the bundle, so they'll land when there's broader motivation.
- Strategy A's "ugly" parts (Term values in maps, name-keyed status, threading) are localized to ~5 places — they shrink to nothing as the gap-closers land. No throwaway work.

## Decomposition

Files affected:
- `rustland/anthill-todo/anthill/store.anthill` — new file declaring `sort WorkItemStore`, the `wis` entity, and the `from_backend` / `next_id` / `lookup` / `by_status_of` / `commit` / `forget` operations. Operation bodies in anthill (no Rust builtins for v0.1).
- `rustland/anthill-todo/src/anthill_bundle.rs` — embed the new file.
- `rustland/anthill-todo/src/main.rs` (`run_anthill_bundle`) — construct the initial `wis(...)` value at startup; pass to `Main.main` as a 4th arg.
- `rustland/anthill-todo/anthill/main.anthill` — `main` / `dispatch` thread `WorkItemStore`; each command body uses store ops; the ~120 lines of build_row_map / build_dep_map / feedback_set / next_workitem_id / max_id_in / pad3 / etc. retire.

## Out of scope

- WI-189 (reify/reflect operators) — see Strategy A vs B.
- WI-188 (entity copy form) — same.
- WI-194 (commit / transactions) — Strategy A uses functional commit; cell semantics is C.
- WI-197 candidate (Map keys at entity values) — sidestepped via String keys.
- IndexedFileStore vs other Store backends — WorkItemStore is composed over an IndexedFileStore today; trait-driven backend swap is out of scope.

## Acceptance

- `rustland/anthill-todo/anthill/main.anthill` drops the ~120 lines of map-building / id-parsing / format glue listed above.
- `cargo test` green; existing cmd_X integration tests still pass.
- Live `anthill-todo --anthill list` / `graph` perf parity or better with WI-183 (the indexes are still O(1) lookups, just shifted from per-command rebuild to one-shot at startup).
