# Anthill CLI / Console Design

The anthill CLI provides two modes of interaction with the knowledge base:

- **One-shot commands** — for CI, scripting, and quick checks
- **Interactive console** — for exploration, testing, and debugging

Both modes operate on an **in-memory KB backed by persistent stores**. At startup, the CLI loads project configuration from the bootstrap store (`.anthill/project.anthill`), pulls facts from bulk stores into memory, and registers queryable stores as external oracles for backward chaining. The console accumulates state across commands and flushes changes back to stores; one-shot mode loads, executes, and exits.

For the persistence layer design, see [Proposal 007: Pluggable Persistence Layer](proposals/007-persistence-layer.md).

## 1. One-Shot Commands

### 1.1 Project-Aware Mode (default)

When run inside a directory with `.anthill/project.anthill`, the CLI operates in **project mode** — it reads the project configuration, initializes all declared stores, and works against the full persistent KB:

```
anthill check                              -- load project, run constraints, report violations
anthill query "by_sort Operation"          -- load project, query, print results
anthill query "by_functor deposit"         -- queries reach both in-memory and queryable stores
anthill flush                              -- write pending KB changes back to stores
anthill codegen rust                       -- generate Rust skeletons for unimplemented namespaces
anthill codegen rust banking               -- generate for a specific namespace
anthill codegen rust --output src/generated/  -- specify output directory
anthill codegen rust --dry-run             -- preview without writing files
anthill codegen rust --include-implemented -- regenerate even if Implementation fact exists
anthill codegen rust --exclude graphics    -- skip a namespace
```

### 1.2 Expression Evaluation

Evaluate an expression against the KB. Queries and expressions are unified — both are terms evaluated against the KB:

```
anthill eval "<expression>"                   -- evaluate in project mode
anthill eval --load <dir> "<expression>"      -- evaluate with explicit files
```

What comes back depends on the expression:

```
-- Ground expression → value
anthill eval "1 + 2"
3

-- Expression with ?variables → bindings (query mode)
anthill eval "?x :- Ring{?x}"
?x = Int

-- Equation → true/false (proof check)
anthill eval "add(?a, zero) = ?a"
true (discharged by KB resolution)

-- Expression using loaded definitions
anthill eval --load stdlib/ --load my_project/ "length(cons(1, cons(2, nil)))"
2
```

This subsumes the existing `query` command — `query` is just `eval` with `?variables`.

### 1.3 Explicit File Mode

For ad-hoc use without a project (or in CI on specific files), pass files explicitly. An ephemeral in-memory KB is used with no persistence:

```
anthill load <files...>                    -- parse + load, report errors
anthill check <files...>                   -- load + run constraints, report violations
anthill query <query> <files...>           -- load + query, print results
anthill eval <expression> <files...>       -- load + evaluate expression
```

### 1.4 Common Options

Exit code: 0 = success, 1 = errors/violations. Output is human-readable by default, `--json` for machine consumption.

Examples:

```
-- Project mode (inside a project directory):
anthill check
anthill query "by_sort WorkItem"
anthill query "AuditEntry(account: \"alice\", ?action, ?amount, ?at)"

-- Code generation:
anthill codegen rust
anthill codegen rust banking --output src/generated/
anthill codegen rust --dry-run

-- Explicit file mode:
anthill load banking.anthill prelude.anthill
anthill check banking.anthill
anthill query "by_sort Operation" banking.anthill
```

## 2. Interactive Console

```
anthill console
```

Enters a REPL with a mutable in-memory KB backed by persistent stores. If run inside a project directory, the console initializes from the project configuration (bootstrap store → bulk stores → queryable oracle registration). State persists across commands within the session and can be flushed back to stores.

### 2.1 Startup and Loading

In project mode, the console initializes automatically:

```
anthill console
loading project from .anthill/project.anthill
  bootstrap: FileStore(".anthill", stage0) — 3 sorts, 5 operations, 12 facts
  bulk pull: FileStore(".anthill", stage0) — 8 workitems, 3 feedback
  oracle:    SqlStore("postgresql://localhost/myproject") — queryable (audit_entries, metrics)
ready. 9 sorts, 20 operations, 23 facts in memory; 2 queryable stores registered.

anthill>
```

Additional files can be loaded explicitly — `load` is additive:

```
anthill> load banking.anthill
loaded: 3 sorts, 5 operations, 2 constraints, 12 facts

anthill> load prelude.anthill
loaded: 6 sorts, 15 operations, 8 rules (cumulative: 9 sorts, 20 operations, ...)
```

### 2.2 Asserting and Retracting

Assert facts using anthill surface syntax:

```
anthill> assert fact parent("alice", "bob")
fact #42 asserted [store: FileStore(".anthill")]

anthill> assert fact parent("bob", "charlie")
fact #43 asserted [store: FileStore(".anthill")]

anthill> assert rule ancestor(?X, ?Z) :- parent(?X, ?Y), ancestor(?Y, ?Z)
fact #44 asserted

anthill> retract #42
retracted fact #42
```

Assert parses the input as anthill source and loads it into the KB. The routing rules determine which store owns the fact. This means any valid declaration works:

```
anthill> assert sort Color { entity red; entity green; entity blue }
sort Color registered (Defined, 3 constructors)

anthill> assert entity Point(x: Int, y: Int)
sort Point registered

anthill> assert operation distance(a: Point, b: Point) -> Int
fact #51 asserted
```

Changes are held in the in-memory KB and marked as pending. Use `flush` to write them to the backing stores (see §2.8).

### 2.3 Expression Evaluation

The console can evaluate expressions directly. Since expressions are terms, and the KB handles both evaluation and queries, the same command handles values, queries, and proof checks:

```
anthill> 1 + 2
3

anthill> length(cons(1, cons(2, nil)))
2

anthill> ?x :- Ring{?x}
?x = Int

anthill> fact Ring{Float}
OK

anthill> ?x :- Ring{?x}
?x = Int
?x = Float

anthill> add(?a, zero) = ?a
true
```

Typing an expression evaluates it. Typing a declaration (`fact`, `sort`, `rule`, etc.) asserts it. The REPL unifies expression evaluation and KB interaction.

### 2.4 Querying

Queries work across all stores transparently. For facts in bulk stores, the query runs against the in-memory KB. For facts in queryable stores, the query is translated to a native query (e.g., SQL) and executed on demand:

```
anthill> query by_sort Operation
deposit(a: Account, m: Money) -> Account  [domain: Account]
withdraw(a: Account, m: Money) -> Account [domain: Account]
balance(a: Account) -> Money              [domain: Account]

anthill> query by_sort Requirement
Requires(Numeric{T = Money})  [domain: banking]

anthill> query by_functor parent
parent("alice", "bob")    [#42, sort: Fact, domain: _global]
parent("bob", "charlie")  [#43, sort: Fact, domain: _global]

anthill> query by_domain Account
  Sort: Account (Defined)
  Members: checking (Constructor), savings (Constructor), deposit (Operation), withdraw (Operation)
  Requirements: none
  Facts: 5

-- Pattern query — reaches queryable stores via backward chaining:
anthill> query AuditEntry(account: "alice", ?action, ?amount, ?at)
AuditEntry("alice", "deposit",  500, "2026-01-15T10:00:00Z")  [store: SqlStore, table: audit_entries]
AuditEntry("alice", "withdraw", 200, "2026-02-01T14:30:00Z")  [store: SqlStore, table: audit_entries]
(2 results from queryable store)
```

### 2.5 Inspecting

```
anthill> sorts
Namespace  (Abstract)
Money      (Abstract)
Account    (Defined: checking, savings)
Color      (Defined: red, green, blue)

anthill> members Account
  checking  (Constructor)
  savings   (Constructor)
  deposit   (Operation)
  withdraw  (Operation)

anthill> requirements Ordered
  Eq{T}  [domain: Ordered]

anthill> stats
  sorts: 9  facts: 51  active: 50  retracted: 1
  stores: 2 (1 bulk, 1 queryable)  pending: 3 (2 asserted, 1 retracted)
```

### 2.6 Checking Constraints

```
anthill> check
OK: 0 constraint violations

anthill> assert fact balance(account1, -100)
fact #52 asserted

anthill> check
VIOLATION: non_negative
  balance(?a) >= 0
  bindings: ?a = account1, balance = -100
```

### 2.7 Session Management

```
anthill> reset                  -- clear the KB, start fresh
anthill> reload                 -- re-load all previously loaded files + re-pull bulk stores
anthill> history                -- show command history
anthill> help                   -- show available commands
```

### 2.8 Persistence

```
anthill> stores
  FileStore(".anthill", stage0)                         bulk     12 facts loaded
  SqlStore("postgresql://localhost/myproject", "anthill") queryable  (audit_entries, metrics)

anthill> routes
  WorkItem(?)   → FileStore(".anthill", stage0)
  Project(?)    → FileStore(".anthill", stage0)
  Feedback(?)   → FileStore(".anthill", stage0)
  AuditEntry(?) → SqlStore("postgresql://localhost/myproject", "anthill")
  ?             → FileStore(".anthill", stage0)    [default]

anthill> pending
  asserted: fact #52 parent("alice", "bob")      → FileStore(".anthill")
  asserted: fact #53 parent("bob", "charlie")    → FileStore(".anthill")
  retracted: fact #42                            → FileStore(".anthill")

anthill> flush
  FileStore(".anthill"): 2 persisted, 1 retracted
  SqlStore("postgresql://..."): 0 changes
flushed.

anthill> flush --dry-run
  (no pending changes)

anthill> pull
  FileStore(".anthill"): 0 new facts (up to date)
  (queryable stores are not pulled — queried on demand)
pulled.
```

`flush` writes pending changes (asserts, retractions, trust updates) back to the backing stores via the routing rules. `pull` re-loads facts from bulk stores, picking up external changes (e.g., another agent committed new `.anthill` files to git). Queryable stores are never pulled — they are always queried on demand.

## 3. Architecture

The CLI is a thin layer over `anthill-core` and the persistence layer:

```
                         CLI / Console
                      (REPL, formatting,
                       command dispatch)
                              │
                    ──────────┴──────────
                        KnowledgeBase
                     (terms, facts, indexes,
                      backward chaining)
                              │
                    ──────────┴──────────
                     Persistence Layer
                   (route, persist, retrieve,
                    flush, pull)
                     ╱        │        ╲
              FileStore    SqlStore    (other stores)
              (bulk)       (queryable)
```

### 3.1 Command Mapping

| Console command | Core function |
|----------------|---------------|
| `load` | `parse::parse()` + `kb::load::load()` |
| `eval` / expression | `parse::parse()` + `kb::resolve()` / `Runtime.evaluate()` |
| `assert` | `parse::parse()` + `kb::load::load()` + `persistence::route()` |
| `retract` | `kb.retract(fact_id)` + mark pending in store |
| `query by_sort` | `kb.by_sort(sort_term)` — may trigger queryable store |
| `query by_functor` | `kb.by_functor(sym)` — may trigger queryable store |
| `query <pattern>` | backward chaining — delegates to queryable stores |
| `query by_domain` | `kb.by_domain(domain_term)` |
| `sorts` | iterate `kb` sort registry |
| `members` | `kb.by_sort(member_sort)` filtered by domain |
| `check` | evaluate constraints (denials) against KB state |
| `stores` | list configured stores and their capabilities |
| `routes` | list routing rules (which sorts → which stores) |
| `pending` | list uncommitted changes awaiting flush |
| `flush` | `persistence::flush()` — write delta to backing stores |
| `pull` | `persistence::pull()` — reload from bulk stores |
| `codegen rust` | `codegen::rust::generate()` — forward-map namespaces to Rust skeletons ([docs](rust-forward-mapping.md)) |

### 3.2 Bootstrap and Startup

By default, the CLI looks for `.anthill/project.anthill` in the current directory (walking up to the repo root). A different bootstrap config can be specified with `--config`:

```
anthill console                              -- default: .anthill/project.anthill
anthill console --config path/to/my.anthill  -- custom bootstrap config
anthill check --config /etc/anthill/prod.anthill  -- e.g., production store config
```

This allows the same project to have multiple storage topologies — e.g., a local development config (filesystem only) and a production config (filesystem + PostgreSQL), or a CI config pointing at a test database.

The startup sequence (see [Proposal 007 §8](proposals/007-persistence-layer.md#8-project-level-configuration-and-bootstrap)):

1. Read bootstrap config (default `.anthill/project.anthill`, or `--config` path)
2. Parse project configuration: store declarations, routing rules
3. For each bulk store: `pull(store)` — load all facts into KB
4. For each queryable store: register as external oracle in the reasoning engine
5. KB is ready — in-memory facts + queryable oracles

## 4. Relationship to Stage 0

The console is **plumbing**; stage0 commands are **porcelain**:

```
                    Stage 0 porcelain
                (decompose, claim, verify, status)
                           │
                    ───────┴────────
                    anthill console
                  (load, assert, query, flush,
                   pull, inspect, check)
                           │
                    ───────┴────────
                     KnowledgeBase
                  (terms, facts, indexes)
                           │
                    ───────┴────────
                   Persistence Layer
                 (FileStore, SqlStore, ...)
```

Stage 0 workflow commands build on the same KB and persistence layer. They could be added as console commands later (`status`, `verify WI-001`), but the console is useful without them.
