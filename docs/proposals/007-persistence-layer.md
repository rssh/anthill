# Proposal 007: Pluggable Persistence Layer

**Status:** Draft
**Depends on:** Kernel Language Specification (§4.2 Quoted Terms, §5.4 Operations, §5.5 Effects, §8.3 Rule Evaluation)
**Affects:** CLI Design (§3 Architecture), Stage 0 Metasystem Design (§9.7 Storage)

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

### 2. Store: The Abstract Backend

```
namespace anthill.persistence
  export Store, StoreCaps, Binding, route, retrieve, persist, retract, pull, flush

  -- ================================================================
  -- Store: abstract storage backend
  -- ================================================================

  sort Store                                  -- abstract: filesystem, postgres, sqlite, ...

  -- What the store can do natively
  sort StoreCaps {
    entity queryable                          -- supports pattern-based retrieval;
                                              --   backward chaining delegates to store
    entity bulk                               -- must load all facts into memory;
                                              --   backward chaining works in-KB
  }

  operation caps(store: Store) -> StoreCaps
end
```

A `queryable` store can translate KB query patterns into native queries (SQL, glob patterns, API calls). A `bulk` store loads all its facts into the KB at startup; retrieval is handled by the in-memory reasoning engine.

This distinction determines how the backward chaining engine (kernel spec §8.3) interacts with the store — see §5 below.

### 3. Routing: 1-to-1 Mapping from Fact Sort to Store

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

```
namespace anthill.persistence

  -- ================================================================
  -- Core operations on any store
  -- ================================================================

  -- Persist a fact to its backing store
  operation persist(store: Store, fact: Term, meta: Meta) -> FactId
    effects (Modifies store)

  -- Retrieve facts matching a pattern
  -- For queryable stores: translates pattern to native query
  -- For bulk stores: no-op (facts already in KB from pull)
  operation retrieve(store: Store, pattern: Term) -> List[T = Term]
    effects (Reads store)

  -- Remove a fact from its backing store
  operation retract(store: Store, id: FactId) -> Bool
    effects (Modifies store)

  -- ================================================================
  -- Bulk loading and flushing
  -- ================================================================

  -- Pull all facts from a bulk store into the KB
  operation pull(store: Store) -> List[T = Term]
    effects (Reads store)

  -- Flush KB delta (new/changed/retracted facts) back to store
  operation flush(store: Store, delta: List[T = Term])
    effects (Modifies store)

end
```

### 5. Backward Chaining Integration

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

  -- FileStore is always bulk: load all files, work in memory
  rule caps(FileStore(?)) = bulk

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

The SQL backend stores facts as table rows. It is `queryable` — backward chaining translates KB patterns to SQL queries. PostgreSQL, MySQL, SQLite, DuckDB etc. are **dialects** of a single `SqlStore`, not separate store types.

> **Canonical source:** `stdlib/anthill/persistence/sql.anthill`

```
namespace anthill.persistence.sql
  import anthill.persistence.{Store, StoreCaps}

  sort SqlDialect {
    entity Postgresql
    entity Mysql
    entity Sqlite
    entity Duckdb
  }

  entity SqlStore(connection: String, schema: String, dialect: SqlDialect)

  -- All SQL stores are queryable: backward chaining delegates to SQL
  rule caps(SqlStore(?_)) = queryable

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
