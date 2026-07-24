# Proposal 007: Pluggable Persistence Layer

**Status:** Draft — **partly superseded** by the extent-sources work (see the status update below)
**Depends on:** Kernel Language Specification (§4.2 Quoted Terms, §5.4 Operations, §5.5 Effects, §8.3 Rule Evaluation)
**Affects:** CLI Design (§3 Architecture), Stage 0 Metasystem Design (§9.7 Storage)

> **Status update (2026-07-21) — partly superseded.** The read / routing / retrieval design below predates the extent-sources work and is revised by it. Current direction:
>
> - **[057 — Extent Seam](057-extent-seam.md)** (implementable) and **[the extent-sources vision](future/extent-sources.md)** (full model) replace the **read side**. §3's routing becomes single-owner **extent ownership** — a functor is *mounted* at its discrim node, not selected by precedence `route` rules; §5's store-aware backward chaining and §11's `RouteHandler` value-integration seam collapse into **one** `ExtentSource::lookup` reached through the mount (no retrieve-beside-unification, one tagged-candidate path); and the eager Rust `retrieve -> Vec<TermId>` is retired for the declared streaming cursor.
> - **[053 — Fact Mutability](053-fact-mutability.md)** owns the write-policy ladder; `monotonicity` here is that query.
> - **WI-780 (write seam)** retires the **`FactId` identity** of §4: `persist` returns the content / domain key and `retract` is content-keyed, so `FactId = Handle(RuleId)` is dropped.
>
> **What still stands:** §1 (persistence as a kernel algebra), §2's *declared* trait contract (`Store` / `NonMonotonicStore` / `QueryableStore` / `BulkStore` — 057 *conforms* to it rather than replacing it), and the **filesystem** backend (§6 — the one backend actually implemented). §7's SQL store is an **illustrative example, not a requirement** (`sql.anthill` is a sketch; no such backend is built), and its `retrieve`-based read design predates 057 — a SQL store is an `ExtentSource` *owner* under the extent model, not a retrieve-beside-unification `QueryableStore`. Read the superseded sections for motivation; take the mechanism from 057 and the vision.

## Motivation

The kernel language specifies a rich knowledge base with metadata, trust levels, provenance, and evolving facts — but the current architecture is purely in-memory. The CLI design states:

> Both modes operate on an **in-memory KB**. The console accumulates state across commands; one-shot mode loads, executes, and exits.

This creates a gap between the language's capabilities and what can be realized:

1. **Trust progression** — a fact starts `proposed`, gets `tested(47)`, eventually `verified`. That lifecycle spans sessions, but there's no durable store for trust upgrades.

2. **Provenance and iterations** — `supersedes`, `iteration`, `timestamp` metadata imply a timeline of fact versions. Without persistence, there's no timeline.

3. **Proof results** — `ProofResult` captures solver output, duration, counterexamples. These are expensive to produce and must survive restarts.

4. **Agent collaboration** — the stigmergic model requires a persistent substrate for agents to leave traces on. Stage 0 already assumes this: `anthill/` files in a git repo, shared by multiple tools.

5. **Scale** — a project may have millions of facts (audit records, metrics, logs). Loading everything into memory is not viable. Some facts must remain in an external store and be queried on demand.

The Stage 0 design ([stage0-metasystem-design.md §9.7](../stage0/stage0-metasystem-design.md#97-storage)) already has a concrete file-based persistence model. But other backends are natural: PostgreSQL for large-scale queryable data, SQLite for single-file portability. The persistence model should be **pluggable**, and the configuration should be expressible in anthill itself.

## Proposal

### 1. Persistence as a Kernel-Level Algebra

Persistence is defined as an abstract algebra in the `anthill.persistence` namespace — sorts, operations, and laws expressed in the kernel language. Concrete backends (filesystem, PostgreSQL, SQLite) are implementations that provide carrier bindings.

### 2. Store and its capability traits

Every backend is a `Store`: it can append facts, flush, and report the write
policy of the functors it owns. Anything beyond that — retracting, native query,
bulk load — is a **capability**, and a capability is a **trait** (a sort that
carries the operation), not a marker value. A backend gains a capability by
*providing* its trait (`fact <Trait>[Backend]`); a backend that does not provide
a trait does not have its operation at all.

```anthill
namespace anthill.persistence
  import anthill.reflect.{Term, FactId, Symbol, Monotonicity}
  import anthill.prelude.{List, Stream}
  import anthill.prelude.Meta.{Meta}
  export Store, NonMonotonicStore, QueryableStore, BulkStore,
         route, persist, retract, retrieve, pull, flush, monotonicity

  -- Base: append a fact, flush, and report a functor's write policy. Nothing
  -- here mutates or reads back — those are the traits below.
  sort Store {
    operation persist(store: Store, fact: Term, meta: Meta) -> FactId
      effects {Modify[store], Error}
    operation flush(store: Store, delta: List[T = Term]) -> Bool
      effects {Modify[store], Error}
    -- Write POLICY (proposal 053) of a functor this store owns: which write
    -- operations are permitted for it — constant (none), monotone (persist
    -- only), non_monotone (persist + retract). A QUERY: the system reads it to
    -- plan, never by attempting a write and catching the failure.
    operation monotonicity(store: Store, functor: Symbol) -> Monotonicity
  }

  -- Mutation is a capability: only a NonMonotonicStore carries `retract`.
  sort NonMonotonicStore {
    fact Store
    operation retract(store: NonMonotonicStore, id: FactId) -> Bool
      effects {Modify[store], Error}
  }

  -- Native pattern retrieval (backward chaining delegates to the backend).
  sort QueryableStore {
    fact Store
    operation retrieve(store: QueryableStore, pattern: Term) -> Stream[Term, Error]
      effects Error
  }

  -- Load all facts into the KB (backward chaining then works in memory).
  sort BulkStore {
    fact Store
    operation pull(store: BulkStore) -> List[T = Term]
      effects Error
  }
end
```

**Two kinds of capability, two mechanisms.**

- **Provision — a trait.** `retract`, `retrieve`, `pull` are not on every store,
  so "can mutate / query / bulk-load" is *having the operation* = providing the
  trait (`fact NonMonotonicStore[SqlStore]`, `fact QueryableStore[SqlStore]`,
  `fact BulkStore[FileStore]`). An append-only backend simply does not provide
  `NonMonotonicStore`, and so cannot be asked to `retract` at all.
- **Policy — a predicate.** `persist` is on *every* `Store`, but whether it (and
  `retract`) is *permitted* for a given functor is that functor's
  **monotonicity** (053), answered by `monotonicity(store, functor)`. It governs
  universal operations per predicate and adds no operation, so it is a
  value/predicate, not a trait.

Provision and policy stay consistent by construction: a store that does not
provide `NonMonotonicStore` has no `retract`, so `monotonicity` for its functors
can only be `monotone` or `constant` — `non_monotone` *implies* the trait. (The
earlier `caps` / `StoreCaps` value tried to make provision a marker, which is why
it never fit the operation-bearing capabilities and was never built. It is
dropped.)

`monotonicity` answers "can I add / remove predicate `P` here?" *without* a write
attempt: `persist` is available for `P` ⟺ `monotonicity(P) ≠ constant`, and
`retract` ⟺ `monotonicity(P) = non_monotone`. The runtime guard (053) that
refuses a disallowed write is only the backstop for code that skips the query.

The `retrieve` / `pull` distinction determines how the backward chaining engine
(kernel spec §8.3) interacts with the store — see §5 below.

### 3. Routing: 1-to-1 Mapping from Fact Sort to Store

> **Superseded by [057](057-extent-seam.md) §Model / the vision.** Single ownership is now *structural*: the discrim **mount** occupies the functor position, bound at **registration**, not chosen by precedence `route` rules. The specific-before-default precedence and the catch-all `rule route(?)` below are gone — content-based sharding lives *inside* one composite source, never as competing owners of one functor. The 1-to-1 principle stated here survives; the rule-precedence *mechanism* does not.

Each fact sort is owned by exactly one store. No fact lives in two places. Routing is an operation — the kernel dispatches facts to the right store:

```
namespace anthill.persistence

  -- Given a fact, which store owns it?
  operation route(fact: Term) -> Store

end
```

Routing rules are expressed as ordinary rules with precedence — specific patterns match before the catch-all default:

```
-- WorkItems go to the file store
rule route(WorkItem(?))  = FileStore("anthill", stage0)
rule route(Project(?))   = FileStore("anthill", stage0)
rule route(Feedback(?))  = FileStore("anthill", stage0)

-- Everything else goes to the database
rule route(?)            = SqlStore("postgresql://localhost/myproject", "anthill", Postgresql)
```

Because routing rules are facts in the KB, they are queryable (`query by_sort Rule` filtered by `route`) and self-documenting.

### 4. Core Operations

The operations are declared on the sorts of §2 — `persist` / `flush` /
`monotonicity` on `Store`, `retract` on `NonMonotonicStore`, `retrieve` on
`QueryableStore`, `pull` on `BulkStore`. Their semantics:

- **`persist(store, fact, meta) -> FactId`** — append a fact to its backing
  store. Permitted iff `monotonicity(fact's functor) ≠ constant`.
- **`retract(store, id) -> Bool`** (`NonMonotonicStore`) — remove a fact.
  Permitted iff `monotonicity(functor) = non_monotone`. Absent entirely on a
  store that does not provide `NonMonotonicStore`.
- **`retrieve(store, pattern) -> Stream[Term, Error]`** (`QueryableStore`) —
  translate the pattern to a native query and stream the matches.
- **`pull(store) -> List[Term]`** (`BulkStore`) — load all of the store's facts
  into the KB (retrieval then runs in memory).
- **`flush(store, delta) -> Bool`** — write buffered changes back to the store.
- **`monotonicity(store, functor) -> Monotonicity`** — the write-policy query
  (§2; proposal 053), read *before* a write rather than discovered by attempting
  one.

### 5. Backward Chaining Integration

> **Superseded by [057](057-extent-seam.md).** There is no retrieve-*beside*-unification: a store-owned functor is **mounted** at its discrim node, and retrieval reaching the mount delegates to `ExtentSource::lookup`, yielding tagged `Resident(RuleId)` / `Row(Value)` candidates on the *one* seam. The queryable-vs-bulk dichotomy below becomes owner-role (`lookup` through the mount) vs mirror-role (`pull` rehydrates into resident) — a registration choice, not two engine paths. The "external oracle" framing survives only as the vision's *oracle archetype* (deferred).

This is the key architectural point. The reasoning engine's backward chaining (kernel spec §8.3) is extended to be **store-aware**.

When the engine encounters a goal during backward chaining:

```
?- AuditEntry(account: "alice", action: "withdraw", ?amount, ?at)
```

It checks: is the sort `AuditEntry` routed to a queryable store?

- **If queryable** (e.g., PostgreSQL): the engine calls `retrieve(store, pattern)`. The store translates the pattern to a native query (SQL), executes it, and returns matching facts. These enter the KB as working copies with provenance indicating external retrieval.

- **If bulk** (e.g., filesystem): facts were already loaded into the KB at startup via `pull`. Normal in-KB unification proceeds.

A queryable store acts as an **external oracle** in the reasoning engine — a well-known pattern in logic programming (Datalog with external data sources, Prolog foreign predicates). The reasoning engine is store-agnostic: it sees facts, some from memory, some fetched on demand.

### 6. Concrete Backend: Filesystem

The filesystem backend stores facts as `.anthill` files. It is always `bulk` — all files are loaded into memory at startup.

```
namespace anthill.persistence.filesystem
  import anthill.persistence

  entity FileStore(root: String, convention: FileConvention)

  -- FileStore is bulk (load all files, work in memory) and mutable
  fact BulkStore[FileStore]
  fact NonMonotonicStore[FileStore]

  -- ================================================================
  -- File conventions: how facts map to files
  -- ================================================================

  sort FileConvention {
    entity stage0                             -- Stage 0 layout:
                                              --   workitems/ dir, project.anthill, etc.
    entity by_namespace                       -- one directory per namespace
    entity flat                               -- all files in root directory
  }

  -- Stage 0 convention routing:
  -- WorkItem(id: "WI-001", status: Draft, ...)
  --   → anthill/workitems/WI-001.anthill.draft
  -- Project(...)
  --   → anthill/project.anthill
  -- Feedback(workitem: "WI-001", ...)
  --   → anthill/workitems/WI-001.feedback.anthill

  operation file_path(fact: Term, meta: Meta, conv: FileConvention) -> String

  -- Status-dependent renaming (stage0 convention):
  -- Draft    → .anthill.draft
  -- Rejected → .anthill.rejected
  -- other    → .anthill
  operation suffix(status: Term, conv: FileConvention) -> String
end
```

The filesystem backend is the **bootstrap store** — it is always available and always loaded first (see §8).

### 7. Concrete Backend: SQL (with Dialect)

> **Illustrative example, not a requirement.** No SQL backend is implemented — `sql.anthill` is an anthill-level *sketch* of what a queryable store could declare, kept for the dialect / marshalling ideas. Its `queryable` / `retrieve` read design predates [057](057-extent-seam.md): under the extent model a SQL store is an `ExtentSource` **owner** — mounted at its functor node, answering `lookup` with `LookupQuery.bound` pushed down to a WHERE clause — not a retrieve-beside-unification `QueryableStore`. Read this for the dialect layering, not as a read-path spec.

The SQL backend stores facts as table rows. It is `queryable` — backward chaining translates KB patterns to SQL queries. PostgreSQL, MySQL, SQLite, DuckDB etc. are **dialects** of a single `SqlStore`, not separate store types.

> **Canonical source:** `stdlib/anthill/persistence/sql.anthill`

```
namespace anthill.persistence.sql
  import anthill.persistence.{Store, QueryableStore, NonMonotonicStore}

  sort SqlDialect {
    entity Postgresql
    entity Mysql
    entity Sqlite
    entity Duckdb
  }

  entity SqlStore(connection: String, schema: String, dialect: SqlDialect)

  -- All SQL stores are queryable (chaining delegates to SQL) and mutable
  fact QueryableStore[SqlStore]
  fact NonMonotonicStore[SqlStore]

  -- ================================================================
  -- Query bindings: how to translate patterns to SQL
  -- ================================================================

  -- A QueryBinding maps a fact sort to a table with explicit SQL.
  -- The SQL uses Quoted terms (kernel spec §4.2) — formal in SQL,
  -- embedded in the anthill.
  --
  -- SQL is written manually per-binding for now. Dialect-aware
  -- generation from columns + dialect can be added later.
  entity QueryBinding(
    sort_pattern : Term,                      -- which facts this binding handles
    table        : String,
    columns      : List[T = ColumnDef],
    retrieve_sql : Term,                      -- Quoted("sql", "...") pattern → SELECT
    persist_sql  : Term,                      -- Quoted("sql", "...") fact → INSERT/UPSERT
    retract_sql  : Term                       -- Quoted("sql", "...") id → DELETE
  )

  entity ColumnDef(name: String, field: String, sql_type: String)
end
```

**Example: 1M audit records in PostgreSQL.**

```
-- Declare the store
fact audit_db(SqlStore(
  connection: "postgresql://localhost/myproject",
  schema: "anthill",
  dialect: Postgresql
))

-- Route AuditEntry facts to postgres
rule route(AuditEntry(?)) = SqlStore(
  "postgresql://localhost/myproject", "anthill", Postgresql
)

-- Bind the query translation
fact QueryBinding(
  sort_pattern: AuditEntry(?account, ?action, ?amount, ?at),
  table:        "audit_entries",
  columns: [
    ColumnDef("account", "account", "text"),
    ColumnDef("action",  "action",  "text"),
    ColumnDef("amount",  "amount",  "numeric"),
    ColumnDef("at",      "at",      "timestamptz")
  ],
  retrieve_sql: Quoted("sql",
    "SELECT account, action, amount, at FROM audit_entries
     WHERE ($1 IS NULL OR account = $1)
       AND ($2 IS NULL OR action = $2)"),
  persist_sql: Quoted("sql",
    "INSERT INTO audit_entries (account, action, amount, at)
     VALUES ($1, $2, $3, $4)"),
  retract_sql: Quoted("sql",
    "DELETE FROM audit_entries WHERE account = $1 AND at = $4")
)
```

Now this backward chaining query:

```
?- AuditEntry(account: "alice", action: "withdraw", ?amount, ?at)
```

becomes:

```sql
SELECT account, action, amount, at FROM audit_entries
WHERE account = 'alice' AND action = 'withdraw'
```

The reasoning engine does not know it is hitting PostgreSQL. It sees facts.

### 8. Project-Level Configuration and Bootstrap

#### The bootstrap problem

If storage configuration is in the KB, and you need storage to load the KB, there is a chicken-and-egg problem. The solution: there is always a **bootstrap store** — a file-based store at a well-known location that is loaded first.

#### Startup sequence

```
1. Read anthill/project.anthill from disk (hardcoded filesystem path)
   → Parse project configuration, store declarations, routing rules

2. For each declared bulk store:
   → pull(store): load all facts into KB

3. For each declared queryable store:
   → Register as external oracle in the reasoning engine
   → No data loaded yet — facts will be retrieved on demand

4. KB is ready:
   - In-memory facts from bulk stores (filesystem, SQLite, ...)
   - External oracles registered for queryable stores (PostgreSQL, ...)
   - Reasoning engine can backward-chain across both
```

#### Project configuration example

```
namespace my-project
  import anthill.persistence
  import anthill.persistence.filesystem
  import anthill.persistence.sql.*

  -- Bootstrap store: always filesystem, always loaded first
  fact bootstrap(FileStore(root: "anthill", convention: stage0))

  -- Secondary store: queryable, for large-scale data
  fact project_db(SqlStore(
    connection: "postgresql://localhost/myproject",
    schema: "anthill",
    dialect: Postgresql
  ))

  -- Routing with precedence:
  -- Stage 0 artifacts go to files (git-friendly, human-readable)
  rule route(WorkItem(?))    = FileStore("anthill", stage0)
  rule route(Project(?))     = FileStore("anthill", stage0)
  rule route(Feedback(?))    = FileStore("anthill", stage0)
  rule route(ToolDef(?))     = FileStore("anthill", stage0)

  -- Large-scale operational data goes to postgres (queryable)
  rule route(AuditEntry(?))  = SqlStore("postgresql://localhost/myproject", "anthill", Postgresql)
  rule route(Metric(?))      = SqlStore("postgresql://localhost/myproject", "anthill", Postgresql)

  -- Default: everything else goes to files
  rule route(?)              = FileStore("anthill", stage0)
end
```

### 9. Interaction with Existing Kernel Concepts

#### Effects (§5.5–5.7)

Persistence operations use the kernel's effect system. `persist` has `effects (Modifies store)`, `retrieve` has `effects (Reads store)`. This composes with the existing effect semantics — the kernel tracks which operations touch which backends.

#### Metadata (§7)

Every persisted fact carries its `Meta` — trust, agent, timestamp, iteration, supersedes. The persistence layer preserves metadata across store/load cycles. For queryable stores, metadata fields may be stored as additional columns and participate in query translation.

#### Quoted Terms (§4.2)

SQL queries in `QueryBinding` are `Quoted("sql", ...)` terms — formal in SQL, embedded in the anthill. This is exactly the use case `Quoted` was designed for: host-language fragments that are opaque to the kernel but meaningful to an external executor.

#### Implementation Facts (§8.5)

Concrete store backends (FileStore, SqlStore) are implementations of the abstract `Store` algebra. When an `Implementation` fact links host-language code to the `persist`/`retrieve`/`retract` operations, the kernel can generate proof obligations for the effect-env condition (§5.6): the implementation must only modify declared resources.

### 10. Scope and Non-Goals

**In scope:**
- Abstract persistence algebra (`Store`, `route`, `persist`, `retrieve`, `retract`)
- Store capabilities (`queryable` vs `bulk`) and backward chaining integration
- Filesystem backend with pluggable file conventions
- PostgreSQL backend with SQL query bindings
- Bootstrap sequence from file-based root
- 1-to-1 routing with precedence rules

**Not in scope (deferred):**
- Schema migration — when `QueryBinding` changes, queries are rewritten manually
- Multi-store replication — a fact lives in exactly one store
- Conflict resolution across stores — 1-to-1 routing prevents conflicts by design
- Transaction semantics across stores — each store has its own consistency guarantees
- Caching / invalidation for queryable stores — retrieved facts are working copies, not cached

### 11. Value integration and ingestion contract (post-026.1)

> **Superseded by [057](057-extent-seam.md) (retirement stage R2).** The `RouteHandler` read seam this section motivates retires into `ExtentSource::lookup`; the single-mount read path *is* the reconciled implementation contract, with rows entering σ as carrier-neutral `Value`s and the lookup contract (values-first, ground-equality pushdown, superset soundness) pinning the `Store`↔resolver boundary 026.1 left open.

This proposal predates [026.1 Value-integrated KB queries](026.1-value-integrated-kb-queries.md). The abstract algebra (sections 1–10) holds, but the **implementation contract** between a `Store` and the resolver needs to align with 026.1's `Value` / `TermView` boundary. WI-168 records this reconciliation.

#### Two ingestion paths

A fact entering the KB from a store flows through one of two paths, depending on the store's capabilities:

1. **Bulk pull → `assert_fact` (TermId path).** For `bulk` stores: at startup, `pull(store)` returns all facts. They are parsed (for filesystem stores) or row-converted (for in-memory stores), promoted to `TermId` via `TermStore::alloc`, and asserted as KB facts. This is the path the current Rust implementation uses for `FileStore`. Memory cost: O(KB-resident fact count). Query cost: structural indexing in the discrim tree, all bindings produced by `bind_term` end up as `Value::Term(tid)` in σ.

2. **Queryable retrieve → `bind_value` (Value path, [026.1 Q4](026.1-value-integrated-kb-queries.md#implementation-milestones)).** For `queryable` stores at scale: when the resolver hits a goal whose sort is routed to a queryable store, `retrieve(store, pattern)` returns a `Stream[Value::Entity]` from the native query. Each row binds to σ via `bind_value` — **no `TermStore` allocation per row**. The resolver consumes these bindings via `TermView` (026.1 §"TermView abstraction"), which generalises matching/unification over both `Value::Term` and `Value::Entity`. Memory cost: O(active substitution size during query); the main `TermStore` does not grow with row count.

The split mirrors 026.1's "one input boundary, one output boundary": KB-resident facts stay TermId-keyed for hash-consed structural-equality fast paths; external rows enter as Values without paying that cost.

#### Parser as a Value producer

The canonical implementation of a "row → Value" mapping is the **anthill parser**, applied at row-fragment granularity. Backends that ingest anthill source text (the existing `FileStore`; future `GitHubStore` reading issue bodies; future `ApiStore` consuming response payloads) parse each row into a `ParsedFile`-style IR and convert to `Value::Entity` via the same path that `alloc_from_value` reverses.

This makes the ingestion contract **uniform across backends**: every store's `retrieve` produces Values, regardless of whether the row came from the filesystem, a SQL cursor, an HTTP API, or an issue tracker. The 026.1 Q4 `StreamSource::External` variant is the resolver-side wrapper that surfaces these Values to the search loop.

The parser-based path is what `examples/github-todo/docs/pluggable-backend.md` anticipates for its `local | github | api` backend taxonomy: each backend produces anthill-formatted rows; the parser is the shared converter; the resolver consumes them via TermView.

#### `retrieve` return type — `Term` at the spec level, `TermView` at the carrier

The abstract `retrieve` operation (§4) returns `List[Term]`. The `Term` here is the public abstract sort from `anthill.reflect` — that is the only level at which anthill code holds a result.

The implementation-side contract is sharper: what the resolver actually consumes from a `retrieve` result is a `TermView` — the Rust trait introduced by [026.1 Q2](026.1-value-integrated-kb-queries.md) that abstracts over the row's *carrier representation*. Two carriers satisfy `TermView`:

- `TermId` — when the backend hash-conses every row into the main `TermStore` (path 1 above).
- `Value::Entity` (or another non-`Value::Term` variant) — when the backend yields rows via Q4's `StreamSource::External` (path 2 above).

`TermView` is deliberately *not* exposed as a sort in `anthill.reflect`. That would leak Rust-side representation polymorphism into the kernel language for no gain — anthill code can only observe a `Term`, and which carrier backs it is a residency decision the runtime owns. The sort surface stays minimal; the carrier choice lives in the implementation contract and is documented per backend (§9 *Implementation Facts*). This is the same lineage-preservation principle 026.1 enforces for `Substitution` bindings.

#### Q4 status: required for queryable backends at scale

026.1 Q4 was filed as "optional, profile-driven". The reconciliation here elevates it: **Q4 is the required path for any queryable backend whose row-set may exceed the KB's residency budget** (typical SQL stores, future GitHub/API backends). The "required threshold" is workload-dependent:

- < ~10K rows total in the queried table: bulk pull is acceptable; pay the hash-cons once and avoid Q4 plumbing.
- ≥ ~10K rows or unbounded streams: Q4 is required to keep `TermStore` size bounded.

The threshold is a design hint, not a hard contract. Workloads that recursively query an external source (proposal 026.1 §"Pathological case: deep recursion over external streams") may exhibit substitution-clone pressure even at lower row counts; the escape valves listed there (query-scoped arena, prefix memoization, projection pushdown) compose with Q4.

#### Q4 implementation contract (landed)

WI-052 (substrate) and WI-052b (resolver-side wiring) together land the implementation:

- `eval::stream::ExternalStream` — Rust trait with `next() -> Option<Value>` and a `description()` identity hook. Every row source (filesystem, SQL cursor, HTTP API, GitHub issues) implements this.
- `eval::stream::StreamSource::External(Box<dyn ExternalStream>)` — the variant the resolver pumps; yielded rows surface as `Value::Entity` and reach σ via `bind_value`, never `TermStore::alloc`.
- `kb::route::{RouteHandler, RouteRegistry}` + `KnowledgeBase::register_route_handler` — per-functor backend registry. When the resolver hits a goal whose head functor has a registered handler, `step_init` drains the handler's `ExternalStream` and produces `Candidate::ExternalRow(subst)` entries alongside the discrim-tree results.
- Acceptance: (a) 10K-row scan via `splitFirst` leaves `KnowledgeBase::term_store_len()` unchanged from its pre-scan baseline (`anthill-core/tests/eval_q4_test.rs`); (b) a query against a routed functor yields one solution per matching row, with `Value::Str` / `Value::Entity` bindings reaching σ unchanged (`anthill-core/tests/route_dispatch_test.rs`).

A backend's `retrieve` is therefore a function `(store, pattern) -> impl ExternalStream`. The path from a goal in the resolver to a row in σ is: registered handler constructs an `ExternalStream` for the goal pattern → resolver pumps the stream → each row binds via `TermView` + `bind_value`. None of these steps allocate in the main `TermStore`.

**Caveats** (separate follow-up items):

- The Stage B path is **eager-drain**: every matching row materializes a `Candidate` before the choice point is built. Correct, and `TermStore`-bounded, but memory grows with the matching-row count. Lazy per-iteration pumping is a follow-up that wraps the stream into a `FrameState` rather than a `Vec<Candidate>`.
- The current registry is keyed by **head functor symbol directly** — the anthill-level `rule route(GoalSort(?))=Store` declarations from §3 are *not yet consulted at resolution time*. Concrete backends (`FileStore`, `SqlStore`, `GitHubStore`) drive that wiring; until one ships, the route-rule path is forward-compatible documentation.
- The Stage B unification skips `is_duplicate_projection` when σ has any non-`Value::Term` binding. `kb::reify` walks bindings via `resolve_with_term`, which only sees `Value::Term` entries — so external-row substitutions would all reify to the same TermId (the goal with unbound vars) and the dedup would collapse genuinely distinct rows. Hash-consing a Value-tree to make `reify` Value-aware would defeat Q4's no-`TermStore`-growth guarantee, so the dedup is structurally skipped instead.

#### What this means for proposal 033

Proposal 033 §Open questions §5 records the same gap from the disjunction-substrate side. With this section, that question is resolved: the goal queue stays `Vec<TermId>` (matching `Frame.goals`), the substitution carries `Value` (per Q1), and `bind_value` is the single entry point that lifts non-`Term` row data into σ. No 033 implementation depends on Q4 landing first; 033's `Continuation` variant is forward-compatible with whatever the backend produces.

#### Out of scope for this section

- Concrete `GitHubStore` / `ApiStore` schema or routing logic (deferred to a future proposal that supersedes the relevant parts of `examples/github-todo/docs/pluggable-backend.md`).
- Implementation milestones for Q4 itself — those live in 026.1.
- Migration plan for pre-Value SQL bindings (the existing `QueryBinding` schema in §7 uses `Quoted("sql", ...)` terms which are unchanged; only the row-decoding path on the way back is new).

## Design Rationale

### Why persistence configuration in anthill syntax?

The persistence conventions are themselves knowledge about the project. Expressing them as anthill facts means they are:
- **Queryable** — `query by_sort Binding` shows where facts live
- **Self-documenting** — the project configuration describes its own storage topology
- **Versionable** — routing rules evolve with the project (committed to git)
- **Composable** — different namespaces can declare different storage strategies

### Why 1-to-1 routing?

Simplicity. No conflict resolution, no sync between stores, no consistency protocols. A fact has exactly one home. If you need the same data in two places, that's an application-level concern (ETL, replication), not a kernel concern.

### Why queryable vs bulk (not a spectrum)?

Two modes cover the practical cases cleanly:
- **Bulk** = small enough to fit in memory, or must be fully loaded for reasoning (typical: project metadata, work items, rules, specifications). All filesystem stores are bulk.
- **Queryable** = too large for memory, or lives in an external system that already handles querying (typical: operational databases, log stores, metrics). Pattern translation is the key capability.

A store that can do both is just `queryable` — the engine queries on demand, which subsumes loading everything.

### Why bootstrap from filesystem?

The bootstrap store must be available without configuration — you can't read config from a database before you know the database connection string. The filesystem is universally available. `anthill/project.anthill` at a well-known path is the seed from which the full storage topology is loaded.

This mirrors how every database-backed application works: the connection string lives in a config file on disk.
