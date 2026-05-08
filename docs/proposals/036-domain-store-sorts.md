# 036: Domain Store Sorts

## Status: Draft

## Tracks: WI-192

## Relates to: 037 (Modify framework — canonical state model; this proposal is a concrete consumer), WI-202 (phase 1 prerequisite — IndexedFileStore + QueryableStore foundation: stdlib entity, fact, retrieve builtin), WI-188 (entity copy), WI-189 (reify/reflect operators), WI-190 (quasi-quote patterns), WI-194 (commit), WI-195 (Error effect wired), WI-187 (IndexedFileStore Rust impl — already landed; underpins WI-202), WI-200 (multi-instance Modify state — resolves the single-instance limitation noted below), WI-201 (`Spec.AssociatedType` syntax — would let polymorphic bundle commands drop the explicit `?S where WorkItemStore[?S]` noise)

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

`WorkItemStore` is the **anthill-todo subproject's** domain spec — declared in the project's anthill source, alongside `WorkItem` itself. It does not live in the stdlib. Other projects that want a "store with custom indexes" declare their own (`UserStore`, `ProjectStore`, `RuleAuditStore`) using the same machinery.

To match the pluggable-backend direction (`examples/github-todo/docs/pluggable-backend.md` — local files today; GitHub issues and remote API later) and the reality that **different backends have different capabilities** (GitHub search vs in-memory Map indexing; rate limits; eventual consistency), `WorkItemStore` is shaped as a spec parameterized by `State`. Each backend supplies its own `State` value-shape and its own bodies for the spec's operations. WI-192 ships the file-backed implementation; GitHub and API are separate work items, each adding a new impl sort with `fact WorkItemStore[<its-WIS>]` plus bodies, without touching the spec.

```anthill
-- ─── 1. Spec — operations declared ONCE, over Cell[State] ─────────
-- The spec lives over Cell[State] so the Cell protocol (Modify[s],
-- Cell.get, Cell.set) applies uniformly. State is the data-shape;
-- each impl picks its own.
sort WorkItemStore
  sort State = ?

  -- Mutating operations: Modify[s] covers everything reachable from
  -- s (per 037's transitivity rule).
  operation next_id(s: Cell[State]) -> String
    effects Modify[s]
  operation commit(s: Cell[State], w: WorkItem) -> Unit
    effects {Modify[s], Error}
  operation forget(s: Cell[State], id: String) -> Unit
    effects {Modify[s], Error}

  -- Read-only operations. No Modify; observation is type-pure.
  operation lookup(s: Cell[State], id: String) -> Option[WorkItem]
  operation by_status_of(s: Cell[State], st: WorkStatus)
    -> List[WorkItem]
end

-- ─── 2. File-backed impl: a sort that binds State and provides bodies ─
sort FileBasedWorkitemStore
  -- The data shape this impl operates over. NO in-memory by_id /
  -- by_status caches: the backend already satisfies QueryableStore
  -- (stdlib `store.anthill` — `retrieve(store, pattern) -> Stream[Term, Error]`),
  -- so every lookup delegates to backend queries. The Rust
  -- IndexedFileStore impl maintains its own internal cache to make
  -- retrieve fast — that's a backend concern, transparent here.
  -- id_counter is the only domain-store state: a fresh-id counter.
  enum WIS
    entity wis(
      backend: IndexedFileStore,
      id_counter: Int)
  end

  -- This sort satisfies the spec with State bound to WIS, AND
  -- declares the backend is queryable.
  fact WorkItemStore[WIS]
  fact QueryableStore[IndexedFileStore]

  -- Bodies. Signatures are inherited from the spec; queries route
  -- through the backend's retrieve, so the WorkItemStore code is a
  -- thin domain layer over QueryableStore semantics.
  operation commit(s, w) =
    match Cell.get(s)
      case wis(backend, counter) ->
        let _ = persist(backend, w, Meta(entries: nil()))
        let _ = flush(backend, nil())
        Cell.set(s, wis(backend, counter + 1))

  operation lookup(s, id) =
    match Cell.get(s)
      case wis(backend, _) ->
        Stream.first(retrieve(backend, WorkItem(id: id)))
        -- (Stream returns Term values; WI-189 reflects each into
        -- a typed WorkItem so the result is Option[WorkItem].)

  operation by_status_of(s, st) =
    match Cell.get(s)
      case wis(backend, _) ->
        Stream.collect(retrieve(backend, WorkItem(status: st)))

  -- (next_id reads/bumps id_counter; forget calls retract on backend.)

  -- Bundle commands live inside the impl sort. State is bound, so
  -- s: Cell[WIS] is concrete; no polymorphism overhead. cmd_add
  -- calls the spec-op bodies above (resolved through the same
  -- fact). Different impls write their own cmd_* — fitting, since
  -- backends with different capabilities (GitHub search, API
  -- batches) typically need different command logic anyway.
  operation cmd_add(a: AddArgs, s: Cell[WIS]) -> Int
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

  -- (cmd_claim, cmd_deliver, cmd_verify, cmd_delete, cmd_status,
  -- cmd_show, cmd_list, cmd_graph, cmd_next, cmd_feedback,
  -- cmd_update, cmd_add_dep, cmd_remove_dep elided — same shape.)
end

-- ─── 3. Future backends — same shape, separate impl sorts ──────────
-- sort GitHubBasedWorkitemStore
--   enum WIS entity wis(token, repo, ...) end
--   fact WorkItemStore[WIS]
--   operation commit(s, w) = ... -- suited to GitHub's capabilities
-- end
--
-- sort RemoteApiBasedWorkitemStore
--   enum WIS entity wis(endpoint, session, ...) end
--   fact WorkItemStore[WIS]
--   operation commit(s, w) = ... -- suited to remote API
-- end
```

This is a typeclass-like layering — and that's appropriate here. Each backend's bodies exploit its own capabilities (FileBasedWorkitemStore materializes everything in memory; GitHubBased would defer to GH search; RemoteApiBased would batch over a session). The spec captures the contract; the impls capture the variability — including the bundle commands, which live inside each impl sort with a concrete `Cell[WIS]` parameter.

`cmd_claim` shape (also inside `FileBasedWorkitemStore`):

```anthill
operation cmd_claim(a: ClaimArgs, s: Cell[WIS]) -> Int
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

No `Pair[Int, S]` return, no threading — `commit` mutates through `Modify[s]` (Cell's effect); the next `next_id(s)` or `lookup(s, ...)` sees the updated state. The Cell handle is stable across the call; the wrapped `wis(...)` value shifts.

## What language features the surface needs

Walking the surface above, here's what anthill must provide for it to actually work:

### 1. Term → WorkItem reflection on retrieve results *(blocker for typed surface)*

`retrieve(backend, WorkItem(id: id))` returns `Stream[Term, Error]` — the elements are opaque term handles, not typed WorkItem values. To get back a typed `Option[WorkItem]` from `lookup`, we need a coercion that the typer accepts.

This is **WI-189** (reify/reflect operators): `let wi: WorkItem = ↓term`.

**Without WI-189**, we work with `Term` values and use `term_field` / `term_as_string` for field access. The structural shape is the same; only the surface is less typed.

### 2. Mutating commit through the Modify framework *(not a blocker — already exists)*

`s: Cell[WIS]` is plainly a Cell handle. Cell's protocol — `Modify[c]`, `get(c)`, `set(c, v)` — applies straight from the framework. No new state-bearing sort to design.

What commit does end-to-end (file-backed impl):

| Step | What runs | Effect |
|---|---|---|
| 1 | `match Cell.get(s)` | Reads s's cell slot. Returns `wis(backend, counter)`. |
| 2 | `case wis(backend, counter)` | Destructures, binding `backend` and `counter` locally. |
| 3 | `persist(backend, w, ...)` | Routes to Store's handler keyed by `backend`. Writes the file. |
| 4 | `flush(backend, nil())` | Routes to Store's handler. Flushes pending writes. |
| 5 | `Cell.set(s, wis(backend, counter + 1))` | Routes to Cell's handler keyed by `s`. Overwrites slot — only id_counter advances. |
| 6 | (later) `lookup(s, id)` from any other op | Reads `wis(backend, _)` from cell, calls `retrieve(backend, ...)` on the queryable backend. |

Two distinct mutations: Store's slot in steps 3-4 (the file), Cell's slot in step 5 (id_counter). They route to two separate handlers. The `Modify[s]` declaration on commit's signature covers both transitively (per 037's transitivity rule — `s.backend` is reachable from `s`).

The host's startup work: allocate a `Cell[WIS]` initialized to `wis(backend, scan_max_id(backend) + 1)` — one scan to seed the counter; subsequent lookups go through `retrieve` directly.

#### `Modify[s]` covers the backend reach

A reader might expect `commit` to declare `Modify[backend]` separately since the body calls `persist(backend, ...) effects {Modify[store], Error}`. It doesn't need to: per 037's transitivity rule, `Modify[s]` covers any component reachable through s — including the backend reachable via `Cell.get(s).backend`. The declaration `effects {Modify[s], Error}` is the conservative bound: "anything reachable from s may change," which includes the disk write.

Handler dispatch at the call site stays per-resource: `persist(backend, ...)` goes through the Store handler keyed by `backend`, while `Cell.set(s, ...)` goes through Cell's handler keyed by `s`. Transitivity is a typing/effect-row concern, not a runtime-dispatch one.

#### Branch-interaction propagates through `s`'s components

The Branch-interaction reasoning has to follow reachability the same way. `Cell[WIS]`'s state is value-tree, so it could in principle be branch-local-snapshot. But the wis value's `backend` field is a `Store`, which 037 declares **sticky-by-physics** for filesystem-backed impls — the filesystem can't roll back atomically. Since `commit` transitively mutates whatever the backend mutates, the cell's effective contract under Branch is the *intersection* of its components, dominated by the most-restrictive component (the backend). For a file-backed Store, that's sticky-by-physics overall; for a hypothetical purely-in-memory mock backend, branch-local-snapshot would be admissible. Until the framework grows path effects + per-component contract reasoning (or a buffered Store handler absorbs disk writes for the branch's duration, or a static constraint rejects `commit` inside Branch — analogous to the Branch+Consumes constraint from 027), `commit` cannot be called soundly inside `Branch` against a sticky-by-physics backend. For the bundle's v0.1 (one-shot CLI, no Branch use), this is not load-bearing — the gap is documented at the framework level (037 §"Store" contract row).

A switch to a different backend (GitHub issues, remote API) brings its own State type and bodies. The cell's effective Branch behavior is dictated by whichever components the impl's State value reaches; e.g. a hypothetical purely-in-memory mock backend would be branch-local-snapshot admissible.

#### Forward compatibility with time-travel

A future time-travel handler (versioned state, audit trails, history queries) should coexist with `Modify` without breaking changes. WorkItemStore's design satisfies the five forward-compat invariants of 037 §"With time-travel":

1. `set(s, v)`'s observable contract is "next `get(s)` returns `v`."
2. `get(s)` returns the current head; `get_at` (if added later) lives under a separate `TimeTravel[s]` effect.
3. `Modify[s]` doesn't expose handler-internal structure.
4. `set` returns `Unit`, not the prior value.
5. Operation signatures don't encode rollback policy — that's the resource's contract.

The spec satisfies all five — `commit` calls `Cell.set` returning `Unit`; `lookup` calls `Cell.get`; only `Modify[s]` is declared in the spec's effect rows. A future time-travel handler could substitute a versioned representation of the State `Cell` without changing any user-visible code.

#### Single-instance-per-functor limitation

Today's transitional Rust scheme (the type-independent `default_modify_handler`) keys cells by **functor symbol only** — `file_wis(...)` regardless of field values shares a single cell. Two `file_wis(backend_a, ..., counter: 5)` and `file_wis(backend_b, ..., counter: 10)` would collide. This is fine for the bundle's WI-192 use case (one CLI invocation = one project = one WorkItemStore) but breaks for multi-instance scenarios:

- Tests that exercise `cmd_X` against multiple isolated stores in the same process.
- A future `anthill-todo-server` managing N project workspaces.
- Composition where two operations independently want isolated state of the same sort type.

Per 037, identity is a property of the *handler* (`ModifyHandler[Resource, IdentityKey]`), not the resource sort. The framework permits three identity schemes for the handler to pick:

- **Functor-only** (`IdentityKey = Unit`) — current scheme; one slot per Resource type.
- **Identity-by-key** (`IdentityKey = String / Int / IdentityKey` opaque type, computed via a sort-declared `key` operation) — multi-instance via a domain key the user supplies (project name, workspace id).
- **Opaque-handle** (`IdentityKey = ` allocation-time uid) — multi-instance via fresh handles per construction.

WI-200 tracks the runtime work to wire per-resource handlers under these schemes. Until WI-200 lands, every Modify-using resource is functor-keyed. WI-192 v0.1 ships under this limitation and uses functor-only on purpose (single-store bundle). Documented here so the limitation is visible at design-review time, not surprise at multi-tenant time.

Under v0.1's transitional handler scheme (functor-only identity), the field values inside `s` don't participate in state lookup — the runtime keys all `file_wis(...)` calls to one slot. That matches the bundle's single-store usage. When WI-200 lands and Cell migrates to opaque-handle identity, `s`'s allocation-time uid will become the keying scheme; multi-store usage follows without changing user-visible code.

Earlier drafts considered three other options (functional threading; a new Cell value variant; a separate registry pattern duplicating what Modify already does). All inferior to using the framework as-is. Discarded.

#### Note: registries and state are the same idea

This is the framework's central observation, spelled out in 037 §3 "Type-specific Modify handlers": the Modify cell, the host store registry, KB indexes, arenas, source maps are all *handlers for resource-specific Modify effects*. They differ in state representation; they are uniform in dispatch. The WorkItemStore spec's state happens to be value-shaped (a `Cell[X]` for some X), so it plugs into the Cell-style handler with no new machinery. Resources whose state spills outside the Value model (e.g. backend objects with non-Value internals) get a different state-representation choice but the same dispatch architecture.

Cross-reference 037 for the full framework; WI-192 is its first end-to-end consumer.

### 3. IndexedFileStore satisfies QueryableStore *(blocker)*

The design relies on `retrieve(backend, pattern) -> Stream[Term, Error]` from stdlib's `QueryableStore` spec. IndexedFileStore today is `BulkStore` (load-all only); it must additionally satisfy `QueryableStore` for `lookup` / `by_status_of` to work.

Required:
- Declare `fact QueryableStore[IndexedFileStore]` in stdlib (or in the project's `store.anthill`).
- Implement the `retrieve` Rust-side: pattern-matching against the IndexedFileStore's existing source-span-indexed term cache (already in memory after `pull`). O(N) scan per query is fine at CLI scale.

This subsumes what the in-memory `by_id` / `by_status` maps were doing in earlier drafts — instead of materializing in the WorkItemStore layer, the backend does the materialization once (transparent to the WorkItemStore).

### 4. Construction at host (Rust) side *(implementation, not language)*

The host needs to build the initial `wis(...)` entity. With the simplified state, that's just:
- Construct the IndexedFileStore (existing pattern).
- Scan its facts for the max existing WorkItem id → seed `id_counter`.
- Build `Value::Entity { functor: wis_sym, named: [(backend, ...), (id_counter, ...)] }`.
- Allocate a `Cell[WIS]` and seed via `Cell.set` once before `Main.main`.

No language feature. ~20 lines of plumbing in `run_anthill_bundle`.

### 5. Bundle ports its commands *(implementation, not language)*

Mechanical: each command body rewrites to use `next_id` / `lookup` / `by_status_of` / `commit` / `forget`. About 120 lines retire from main.anthill (the index-rebuilding glue).

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

### Strategy A: minimal v0.1 — Term-typed retrieve results

- IndexedFileStore declared as satisfying `QueryableStore`; `retrieve` Rust impl walks its in-memory cache (already populated post-pull).
- WorkItemStore spec + FileBasedWorkitemStore impl as in §"What the surface looks like" — `wis(backend, id_counter)`, no in-memory caches.
- `lookup` / `by_status_of` work on `Term` values from the retrieve stream (use `term_field` / `term_as_string` to read fields).
- `commit` mutates via `Modify[s]` (Cell's effect on the wis cell, transitively reaching the backend). Already wired.
- Bundle commands inside the impl sort, taking `s: Cell[WIS]`.

**Cost to land:** ~1-2 days. ~20 lines of new sort declarations (spec + impl) + ~20 lines of host plumbing + Rust-side `retrieve` for IndexedFileStore + ~150-line refactor of bundle commands. No language changes.

**What's lost vs the ideal:** type-safe field access (commands still use `term_field` / `term_as_string` on retrieve results); pattern-matching against `WorkItem(...)` term shapes by hand.

**What's gained:** the indexes don't exist anymore; the ~120 lines of glue retire; commands are linear (no threading, no `Pair[Int, S]` return); single source of truth (the backend); the abstraction shape matches the ideal end-state.

### Strategy B: land alongside WI-188 + WI-189

- WI-189 enables `↓term : WorkItem` — `Stream.first(retrieve(...))` |> typed `Option[WorkItem]`.
- WI-188 enables `wi.copy(status = ...)` for in-place field updates inside `cmd_claim` / `cmd_deliver`.
- Bundle command bodies stop calling `term_field`.

**Cost to land:** 1-2 weeks (WI-188 + WI-189 as prerequisites, then ~1 day to retype the bundle bodies over `WorkItem` instead of `Term`).

## Recommendation

**Land Strategy A first**, file the gap-closing WIs (WI-188 / WI-189) as follow-ups for Strategy B.

Rationale:
- Strategy A demonstrates the abstraction with zero language changes. The bundle's structure improves immediately, no threading verbosity, no in-memory index machinery.
- The follow-up WIs each have independent value beyond the bundle.
- Strategy A's paper cut (Term-typed retrieve results) is localized to ~5 places and shrinks to nothing as WI-189 lands. No throwaway work.

## Decomposition

The `WorkItemStore` spec and `FileBasedWorkitemStore` impl are project-side: they live in `anthill-todo/`'s anthill source alongside `domain.anthill` and `rules.anthill`. The bundle's binary embeds them via the existing `BulkStore::pull` path. No bundle-side declaration; the project owns its store layout.

Files affected:
- `stdlib/anthill/persistence/filesystem.anthill` — declare `entity IndexedFileStore(root: String, convention: FileConvention)` plus `fact QueryableStore[IndexedFileStore]`. Today only `FileStore` is declared even though the bundle's host already wires an `IndexedFileStore` Rust impl. Adding the entity makes the Value-side type honest; the QueryableStore fact unlocks `retrieve` for downstream consumers.
- `rustland/anthill-stl/...` — implement `retrieve(IndexedFileStore, pattern) -> Stream[Term, Error]` as a builtin. The IndexedFileStore Rust impl already keeps the pulled facts in memory; `retrieve` walks them, unifying each against the pattern, yielding matches as a Stream.
- `anthill-todo/store.anthill` — **new project-side file** declaring `sort WorkItemStore` (spec, with `sort State = ?` and operations over `Cell[State]`) and `sort FileBasedWorkitemStore` (impl, with the WIS enum, `fact WorkItemStore[WIS]`, and operation bodies). Operation bodies in anthill (no Rust builtins for v0.1).
- `rustland/anthill-todo/src/main.rs` (`run_anthill_bundle`) — construct the initial `wis(backend, id_counter_seed)` value at startup (scan `facts_of("WorkItem")` for max id → seed counter); allocate `Cell[WIS]` and seed via `Cell.set` once before `Main.main`. Pass the cell handle to `Main.main`.
- `rustland/anthill-todo/anthill/main.anthill` — `main` / `dispatch` thread the `Cell[WIS]` handle; each command body uses the FileBasedWorkitemStore operations (lookup / commit / next_id / by_status_of / forget); the ~120 lines of build_row_map / build_dep_map / feedback_set / next_workitem_id / max_id_in / pad3 / etc. retire.

Other projects that adopt this pattern (UserStore, ProjectStore, RuleAuditStore) follow the same shape: declare a domain spec + per-backend impl in their own project, require the backend to satisfy QueryableStore, command bodies use spec ops. What's anthill-todo-specific is the WorkItem domain and the file-backed impl.

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
