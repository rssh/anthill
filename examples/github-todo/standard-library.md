# Stage 0 Standard Library

> **Example**: For a runnable example using these types, see [`examples/github-todo/`](./).

This document defines the `anthill.stage0` standard domain — entity types for projects, tools, and work items — and the syntactic sugar that makes them convenient to author.

This is the **standard library layer** of the three-layer architecture:

1. **Kernel language** ([kernel-language.md](../../docs/kernel-language.md)) — `domain`, `sort`, `rule`, `operation` — the formal foundation
2. **Syntactic sugar** ([kernel-language.md §6](../../docs/kernel-language.md#6-syntactic-sugar)) — `entity` (single-constructor sort), `fact` (bodyless rule), `constraint` (headless rule)
3. **Standard library** (this document) — entity types in the `anthill.stage0` domain, with additional sugar for `.anthill` files

Stage 0 does not introduce a separate language. It uses `entity` and `fact` from the kernel language to define its types and instances. What looks like "Stage 0 syntax" (`project`, `tool`, `workitem` blocks) is sugar that desugars to `fact` assertions in the `anthill.stage0` domain.

For design rationale and growth path, see [design.md](design.md).

## 1. Design Principle: Everything Is a Fact

In the full anthill, the KB stores knowledge as facts — instances of entities within domains. Stage 0 follows the same principle:

- A **project configuration** is a fact: `Project("cps2", "scala", "sbt")`
- A **tool definition** is a fact: `ToolDef("sbt-test", "sbt", ["test"], ...)`
- A **work item** is a fact: `WorkItem("WI-001", "Add match support", ...)`
- A **work item status change** is a fact: `StatusChange("WI-001", Open, Claimed("agent-1", ...))`

The acceptance runner, CLI, and MCP server don't need special constructs — they query the KB for facts of known entity types. The "language" for Stage 0 is just the core language's `entity`, `fact`, and `domain` constructs, applied to a specific domain.

## 2. The Standard Domain: `anthill.stage0`

This domain is shipped with anthill. It defines all types needed for structured work decomposition — record types via `entity` sugar, and ADTs/enums via defined `sort`.

```
domain anthill.stage0
  import anthill.prelude.List
  import anthill.prelude.Option
  import anthill.prelude.Duration.{Duration}
  export Project, Module, ToolDef, ToolPack, WorkItem, Feedback
  export SourceRoot, SourceScope, ContextRef, AcceptanceCriterion
  export SuccessCriterion, WorkStatus, Capability

  -- =================================================================
  -- Project structure
  -- =================================================================

  entity Project(
    name       : String,
    language   : Option{T = String},       -- primary language (simple projects)
    build      : Option{T = String},       -- build system (auto-imports std.<build> tools)
    modules    : Option{T = List{T = Name}}, -- module names (composite projects)
    sources    : Option{T = List{T = SourceRoot}}, -- override convention-based roots
    tools      : List{T = Name},           -- tool names available in this project
    domains    : Option{T = List{T = Name}} -- KB domains managed by this project
  )

  entity Module(
    name       : String,
    root       : String,                   -- path relative to project root
    language   : String,
    build      : Option{T = String},
    sources    : Option{T = List{T = SourceRoot}}
  )

  entity SourceRoot(
    path       : String,                   -- relative to module/project root
    language   : Option{T = String},       -- override module/project language
    scope      : SourceScope
  )

  sort SourceScope {                     -- enum: all nullary constructors
    entity Main
    entity Test
    entity Generated
    entity Docs
  }

  -- =================================================================
  -- Tool definitions and packs
  -- =================================================================

  entity ToolDef(
    name       : String,
    command    : String,                   -- executable name or path
    args       : Option{T = List{T = String}}, -- may contain $param placeholders
    working_dir: Option{T = String},       -- relative to project/module root
    timeout    : Option{T = Duration},     -- default: 5m
    success    : SuccessCriterion
  )

  sort SuccessCriterion {                -- ADT: success criterion for tool execution
    entity ExitZero
    entity ExitCode(code: Int64)
    entity OutputMatches(pattern: String)
    entity Custom(term: Term)
  }

  entity ToolPack(
    name       : String,                   -- e.g. "std.sbt", "team.ci-tools"
    tools      : List{T = Name}            -- tool names provided by this pack
  )

  -- =================================================================
  -- Work items
  -- =================================================================

  entity WorkItem(
    id          : String,
    description : Option{T = Term},        -- String, Unspecified, or FileRef(path)
    context     : Option{T = List{T = ContextRef}},
    acceptance  : List{T = AcceptanceCriterion},
    depends_on  : Option{T = List{T = String}}, -- WorkItem ids
    generates   : Option{T = List{T = Term}},   -- facts produced when Verified
    requires_capability : Option{T = List{T = Capability}}, -- what the task needs
    status      : WorkStatus
  )

  sort ContextRef {                      -- ADT: what a work item references
    entity FileRef(path: String, lines: Option{T = String})
    entity FactRef(domain: String, pattern: Term)
    entity WorkItemRef(id: String)
  }

  sort AcceptanceCriterion {             -- ADT: how to verify a work item
    entity ToolPasses(tool: String, params: Option{T = Term})
    entity FactHolds(domain: String, pattern: Term)
    entity Compiles(source: SourceRoot)
    entity Constraint(term: Term)
  }

  sort WorkStatus {                      -- ADT: work item lifecycle
    entity Draft                           -- proposed by decomposer, awaiting review
    entity Open                            -- accepted, available for agents to claim
    entity Claimed(agent: String, since: String)
    entity Delivered(agent: String, at: String)
    entity Verified(at: String)
    entity Rejected(reason: String, at: String)          -- delivery rejected (acceptance failed)
    entity ProposalRejected(reason: String, at: String)  -- decomposition rejected
    entity Stale(reason: String, since: String)
  }

  -- =================================================================
  -- Agent capabilities
  -- =================================================================

  sort Capability {                      -- ADT: what an agent can do
    entity Code(languages: List{T = String})  -- write/modify code
    entity Test                               -- run acceptance tools
    entity Refine                             -- provide feedback, request changes
    entity Review                             -- accept/reject (gate decisions)
    entity Decompose                          -- break tasks into WorkItems
    entity Architect                          -- make design decisions
    entity HumanJudgment                      -- non-automatable decisions
  }

  -- =================================================================
  -- Feedback (refinement comments on work items)
  -- =================================================================

  entity Feedback(
    workitem : String,                     -- WorkItem id
    author   : String,                     -- agent id
    content  : Term,                       -- String or FileRef(path)
    at       : String                      -- timestamp
  )

end anthill.stage0
```

All `.anthill` files are **facts in this domain**. When you write a project declaration, tool definition, or work item, you are asserting a fact of the corresponding entity type.

## 3. Syntactic Sugar

Writing raw entity facts is verbose. The `.anthill` file format provides **sugar** that desugars to `anthill.stage0` facts. The sugar and its desugaring are defined below.

### 3.1 Lexical Conventions

Source files are UTF-8. Comments: `-- single line` and `{- multi-line -}`. All keywords are **context-dependent** (soft), following the Scala 3 approach — a word is a keyword only in a syntactic position where it is expected; elsewhere it is an ordinary identifier. Only `true` and `false` are reserved.

Identifiers: `Letter (Letter | Digit | '-' | '_')*` or quoted `"..."`. Names: dot-separated identifiers (`cps2.transforms`). Literals: strings (`"..."`), integers, floats, booleans, durations (`5m`, `30s`).

### 3.2 Block Delimiters

All declarations support braces or end-markers:

```
Body[F] ::= '{' F '}'    -- brace-delimited
           | F 'end'      -- end-delimited
```

### 3.3 Project Sugar

```
project cps2 {
  language: scala
  build: sbt
  import tools: std.scalafmt
  tools: sbt-compile, sbt-test, scalafmt-check
}
```

**Desugars to:**

```
fact Project("cps2", language: "scala", build: "sbt",
             tools: ["sbt-compile", "sbt-test", "scalafmt-check"])
  [trust: axiom, agent: "author"]
```

Plus the tool import triggers: all `ToolDef` facts from `std.sbt` and `std.scalafmt` are loaded into the project's KB.

#### Composite project (modules)

```
project domains-gradsoft {
  modules:
    module backend {
      root: "backend"
      language: scala
      build: sbt
    }
    module frontend {
      root: "frontend"
      language: typescript
      build: npm
    }
  import tools: std.flyway
  tools: sbt-compile, sbt-test, npm-build, npm-test, flyway-migrate
}
```

**Desugars to:**

```
fact Project("domains-gradsoft",
             modules: ["backend", "frontend"],
             tools: ["sbt-compile", "sbt-test", "npm-build", "npm-test", "flyway-migrate"])
  [trust: axiom, agent: "author"]

fact Module("backend", root: "backend", language: "scala", build: "sbt")
  [trust: axiom, agent: "author"]

fact Module("frontend", root: "frontend", language: "typescript", build: "npm")
  [trust: axiom, agent: "author"]
```

Plus auto-imports of `std.sbt`, `std.npm`, and `std.flyway` tool packs.

### 3.4 Tool Sugar

```
tool sbt-test-only {
  command: "sbt"
  args: ["cps2/testOnly", "$testClass"]
  timeout: 10m
  success: ExitZero
}
```

**Desugars to:**

```
fact ToolDef("sbt-test-only", command: "sbt",
             args: ["cps2/testOnly", "$testClass"],
             timeout: 10m, success: ExitZero)
  [trust: axiom, agent: "author"]
```

#### Standard packs and auto-import

Standard tool packs (`std.sbt`, `std.npm`, `std.python`, etc.) are just collections of `ToolDef` facts shipped with anthill. Declaring `build: sbt` auto-imports the `std.sbt` pack. Explicit `import tools: std.flyway` imports additional packs.

A local `tool` declaration with the same name **overrides** an imported `ToolDef` fact (the local fact has higher priority).

| Pack | Tools provided |
|---|---|
| `std.sbt` | `sbt-compile`, `sbt-test`, `sbt-test-only`, `sbt-publish`, `sbt-clean` |
| `std.maven` | `mvn-compile`, `mvn-test`, `mvn-package`, `mvn-clean` |
| `std.gradle` | `gradle-build`, `gradle-test`, `gradle-clean` |
| `std.npm` | `npm-build`, `npm-test`, `npm-lint` |
| `std.cargo` | `cargo-build`, `cargo-test`, `cargo-clippy`, `cargo-fmt` |
| `std.python` | `pytest`, `pytest-module`, `mypy-check`, `ruff-check` |
| `std.flyway` | `flyway-migrate`, `flyway-validate`, `flyway-info` |
| `std.docker` | `docker-build`, `docker-compose-up`, `docker-compose-down` |
| `std.scalafmt` | `scalafmt-check`, `scalafmt-format` |

### 3.5 WorkItem Sugar

```
workitem WI-CPS2-MATCH-002 {
  description: "Implement CPS transform logic for simple match"
  context:
    WorkItemRef(WI-CPS2-MATCH-001)
    FileRef("compiler-plugin/src/main/scala/cps/plugin/MatchTransform.scala")
  acceptance:
    Compiles({ path: "compiler-plugin/src/main/scala", scope: Main })
    ToolPasses(sbt-test-only, { testClass: "cps.plugin.MatchSimpleTest" })
  depends_on: [WI-CPS2-MATCH-001]
  status: Open
  [trust: proposed, agent: "architect"]
}
```

**Desugars to:**

```
fact WorkItem("WI-CPS2-MATCH-002",
  description: "Implement CPS transform logic for simple match",
  context: [WorkItemRef("WI-CPS2-MATCH-001"),
            FileRef("compiler-plugin/src/main/scala/cps/plugin/MatchTransform.scala")],
  acceptance: [Compiles(SourceRoot("compiler-plugin/src/main/scala", scope: Main)),
               ToolPasses("sbt-test-only", { testClass: "cps.plugin.MatchSimpleTest" })],
  depends_on: ["WI-CPS2-MATCH-001"],
  status: Open)
  [trust: proposed, agent: "architect"]
```

### 3.6 Feedback Sugar

```
feedback {
  workitem: WI-CPS2-MATCH-003
  author: "rssh"
  content: "merge with WI-MATCH-004, they touch the same file"
  at: "2027-03-15T10:30:00Z"
}
```

**Desugars to:**

```
fact Feedback("WI-CPS2-MATCH-003",
  author: "rssh",
  content: "merge with WI-MATCH-004, they touch the same file",
  at: "2027-03-15T10:30:00Z")
  [trust: axiom, agent: "rssh"]
```

Feedback can reference a file for longer reviews:

```
feedback {
  workitem: WI-CPS2-MATCH-002
  author: "rssh"
  content: FileRef("docs/reviews/match-002-review.md")
  at: "2027-03-15T11:00:00Z"
}
```

Feedback facts accumulate — they are not superseded. The WorkItem itself is revised (new fact via `meta.supersedes`) in response to feedback. The feedback history shows why the design evolved.

### 3.7 Metadata

Metadata blocks `[trust: ..., agent: ..., iteration: ...]` are sugar for `Meta(...)` Fn terms (see [kernel-language.md §7](../../docs/kernel-language.md#7-metadata)). `Meta` is an entity in `anthill.prelude.Meta` with **open keys** — any `Name : Term` pair is accepted. Well-known keys (`trust`, `agent`, `timestamp`, `iteration`, `source`, `supersedes`) have semantic meaning to the kernel; additional keys are project-defined and pass through.

```
-- Sugar:
fact X [trust: axiom, agent: "author"]
-- Desugars to:
rule X  meta: Meta(trust: axiom, agent: "author")

-- Trust constructors:
--   proved | verified | tested(N) | empirical | proposed | stale | axiom | decision
-- Surface sugar: tested-47 → tested(47)
```

## 4. Semantics

Since everything is a fact, semantics are defined by **queries over facts** rather than special rules.

### 4.1 Project and Module Semantics

The acceptance runner loads the project by querying:
- `Project(?name, ...)` — exactly one result expected
- `Module(?name, ...)` — zero or more, referenced by `Project.modules`
- `ToolDef(?name, ...)` — all tools, from imports and local declarations

**Source root inference**: when a `Module` (or simple `Project`) has `build` but no `sources`, the system infers source roots from build conventions (sbt → `src/main/scala` + `src/test/scala`, etc.). When `build` is absent, it detects from root markers (`build.sbt`, `package.json`, etc.).

### 4.2 Tool Execution

A `ToolDef` fact is an executable specification. When invoked:
1. Resolve `command` via PATH
2. Substitute `$param` placeholders in `args` from the provided Bindings
3. Execute as subprocess in `working_dir` (relative to project/module root)
4. Evaluate `success` criterion against the result

### 4.3 WorkItem Lifecycle

WorkItem status transitions are themselves **facts** — each transition produces a new `WorkItem` fact that supersedes the previous one (via `meta.supersedes`). The current status of a WorkItem is its most recent fact.

```
                    feedback           accept          claim         deliver          verify
  Draft ◀──────────────────▶ Draft ──────▶ Open ─────────▶ Claimed ──────▶ Delivered ──────▶ Verified
    │        (revise)                        ▲                │               │  ▲
    │   reject                   release     │                │  feedback     │  │  feedback
    │                            └───────────┘                └──(rework)────▶│  └──(rework)──┘
    ▼                                                                         │
  ProposalRejected                                                            └──────▶ Rejected

  Any status ──(environment change)──▶ Stale
```

**Refinement loops**: `Feedback` facts (see §3.6) drive iterative revision. An agent with `Refine` capability provides feedback; the responsible agent revises and produces a new WorkItem fact (via `meta.supersedes`). This cycle can repeat N times before acceptance or rejection.

**Capability matching**: a WorkItem with `requires_capability` can only be claimed by an agent whose capabilities match. At Stage 0, capability matching is enforced by the skill/CLI/spawner, not by the KB itself.

**Dependency enforcement**: a WorkItem with `depends_on: ["X", "Y"]` cannot transition to `Claimed` unless the most recent facts for X and Y both have `status: Verified`.

**Acceptance verification**: all criteria in `acceptance` are checked. Each criterion queries facts:
- `ToolPasses(tool, params)` — find `ToolDef` fact, execute, check success
- `Compiles(source)` or `Compiles(module: name)` — find appropriate compiler tool, execute
- `FactHolds(domain, pattern)` — query KB for matching fact
- `Constraint(term)` — evaluate term

**Fact generation**: when status becomes `Verified`, each term in `generates` is asserted as a new fact with `trust: tested-N`.

### 4.4 No Special Query Language

Since work items, tools, and projects are facts, the standard KB query protocol works:

```
-- Find all open work items
query WorkItem(?id, status: Open)

-- Find work items requiring Scala coding
query WorkItem(?id, requires_capability: ?caps) where contains(?caps, Code(["scala"]))

-- Find work items blocked on WI-001
query WorkItem(?id, depends_on: ?deps) where contains(?deps, "WI-001")

-- Find all feedback on a work item
query Feedback(workitem: "WI-CPS2-MATCH-002", ?author, ?content, ?at)

-- Find all tools for the project
query ToolDef(?name, ?command, ...)

-- Check if a fact was generated
query FactHolds("cps2.transforms", matchSupported)
```

At Stage 0, these queries are simple pattern matches over facts — no unification, no rule resolution. As the project grows into later stages, the same queries gain access to reasoning.

## 5. Complete Examples

### 5.1 Simple Project (brace style)

```
-- anthill/project.anthill

project cps-async-connect {
  language: scala
  build: sbt                               -- auto-imports std.sbt tools
  tools: sbt-compile, sbt-test
}

-- All of the above is sugar for:
--   fact Project("cps-async-connect", language: "scala", build: "sbt",
--                tools: ["sbt-compile", "sbt-test"]) [trust: axiom]
-- Plus ToolDef facts loaded from std.sbt pack.
```

```
-- anthill/workitems/connection-pool.anthill

workitem WI-POOL-001 {
  description: "Define ConnectionPool trait with acquire/release semantics"
  context:
    FileRef("src/main/scala/cps/async/connect/Connection.scala")
  acceptance:
    Compiles({ path: "src/main/scala", scope: Main })
  depends_on: []
  status: Open
  [trust: proposed, agent: "architect"]
}

workitem WI-POOL-002 {
  description: "Implement bounded connection pool with timeout"
  context:
    WorkItemRef(WI-POOL-001)
    FileRef("src/main/scala/cps/async/connect/BoundedPool.scala")
  acceptance:
    Compiles({ path: "src/main/scala", scope: Main })
    ToolPasses(sbt-test)
  depends_on: [WI-POOL-001]
  status: Open
  [trust: proposed, agent: "architect"]
}

workitem WI-POOL-003 {
  description: "Add connection pool integration tests"
  context: WorkItemRef(WI-POOL-002)
  acceptance: ToolPasses(sbt-test)
  depends_on: [WI-POOL-002]
  generates:
    [fact("cps-async-connect.pool", "connection-pooling-works")]
  status: Open
  [trust: proposed, agent: "architect"]
}
```

### 5.2 Composite Project (end-marker style)

```
-- anthill/project.anthill

project inventory-app
  modules:
    module backend
      root: "backend"
      language: python
      build: poetry                        -- auto-imports std.python, std.poetry
    end
    module frontend
      root: "frontend"
      language: typescript
      build: npm                           -- auto-imports std.npm
    end
    module db
      root: "db"
      language: sql
    end
  import tools: std.flyway                 -- for db module
  tools: pytest, mypy-check, npm-build, npm-test, flyway-migrate, lint-all
end

-- Only project-specific tool needs definition
tool lint-all
  command: "make"
  args: ["lint"]
  timeout: 3m
  success: ExitZero
end
```

```
-- anthill/workitems/batch-import.anthill

workitem WI-BATCH-001
  description: "DB migration: create import_jobs table with status tracking"
  context:
    FileRef("db/migrations/")
    FileRef("backend/src/models/inventory.py")
  acceptance:
    ToolPasses(flyway-migrate, { dbUrl: "jdbc:postgresql://localhost:5432/inventory_test" })
  depends_on: []
  status: Open
  [trust: proposed, agent: "product-owner"]
end

workitem WI-BATCH-002
  description: "Backend: CSV parser with validation for inventory items"
  acceptance:
    ToolPasses(pytest-module, { module: "tests/test_csv_parser.py" })
    ToolPasses(mypy-check)
  depends_on: []
  status: Open
  [trust: proposed, agent: "product-owner"]
end

workitem WI-BATCH-003
  description: "Backend: batch import API endpoint with progress tracking"
  context:
    WorkItemRef(WI-BATCH-001)
    WorkItemRef(WI-BATCH-002)
  acceptance:
    ToolPasses(pytest-module, { module: "tests/test_import_api.py" })
    ToolPasses(mypy-check)
  depends_on: [WI-BATCH-001, WI-BATCH-002]
  status: Open
  [trust: proposed, agent: "product-owner"]
end

workitem WI-BATCH-004
  description: "Frontend: drag-and-drop CSV upload with progress bar"
  acceptance:
    ToolPasses(npm-build)
    ToolPasses(npm-test)
  depends_on: []
  status: Open
  [trust: proposed, agent: "product-owner"]
end

workitem WI-BATCH-005
  description: "Integration: end-to-end batch import with error reporting"
  context:
    WorkItemRef(WI-BATCH-003)
    WorkItemRef(WI-BATCH-004)
  acceptance:
    ToolPasses(pytest)
    ToolPasses(npm-test)
    ToolPasses(lint-all)
  depends_on: [WI-BATCH-003, WI-BATCH-004]
  generates:
    [fact("inventory-app.features", "batch-import-operational")]
  status: Open
  [trust: proposed, agent: "product-owner"]
end
```

### 5.3 WorkItem Lifecycle as Fact Supersession

Each status change produces a new fact that supersedes the previous one:

```
-- Iteration 1: created
fact WorkItem("WI-POOL-002", description: "Implement bounded connection pool",
  acceptance: [Compiles(...), ToolPasses(sbt-test)],
  depends_on: ["WI-POOL-001"], status: Open)
  [trust: proposed, agent: "architect", iteration: 1]

-- Iteration 2: claimed
fact WorkItem("WI-POOL-002", ..., status: Claimed("llm-coder-v3", "2027-03-15T10:30:00Z"))
  [trust: proposed, agent: "architect", iteration: 2, supersedes: WI-POOL-002-v1]

-- Iteration 3: delivered
fact WorkItem("WI-POOL-002", ..., status: Delivered("llm-coder-v3", "2027-03-15T11:15:00Z"))
  [trust: proposed, agent: "architect", iteration: 3, supersedes: WI-POOL-002-v2]

-- Iteration 4: verified (all acceptance criteria passed)
fact WorkItem("WI-POOL-002", ..., status: Verified("2027-03-15T11:20:00Z"))
  [trust: tested-47, agent: "architect", iteration: 4, supersedes: WI-POOL-002-v3]
```

### 5.4 File-Referenced Descriptions

WorkItem descriptions can reference a markdown file instead of inline text. This is useful for rich descriptions with examples, diagrams, and code snippets:

```
workitem WI-CPS2-MATCH-001 {
  description: FileRef("docs/workitems/match-support.md")
  context:
    FileRef("compiler-plugin/src/main/scala/cps/plugin/CpsTransformPhase.scala")
  acceptance:
    Compiles({ path: "compiler-plugin/src/main/scala", scope: Main })
  status: Open
  [trust: proposed, agent: "architect"]
}
```

The skill/CLI reads the `.md` file when presenting the WorkItem to a user. Agents read it directly as context. The file is version-controlled alongside the WorkItem.

### 5.5 Unspecified Descriptions

```
-- Rough initial decomposition
workitem WI-PERF-001 {
  description: <"Improve API response time for /search">
  acceptance: ToolPasses(pytest)
  status: Open
  [trust: proposed, agent: "tech-lead"]
}

-- Refined after investigation (new fact supersedes)
workitem WI-PERF-001 {
  description: "Add database index on inventory.sku column.
                Target: p95 < 200ms for /search."
  context:
    FileRef("backend/src/api/search_routes.py")
    FileRef("db/migrations/")
  acceptance:
    ToolPasses(flyway-migrate, { dbUrl: "jdbc:postgresql://localhost:5432/inventory_test" })
    ToolPasses(pytest-module, { module: "tests/test_search_perf.py" })
  status: Open
  [trust: proposed, agent: "tech-lead", supersedes: WI-PERF-001-v1]
}
```

### 5.5 Custom Tool with OutputMatches

```
tool api-health {
  command: "curl"
  args: ["-sf", "http://localhost:8080/health"]
  timeout: 30s
  success: OutputMatches("\"status\"\\s*:\\s*\"ok\"")
}

workitem WI-DEPLOY-001 {
  description: "Verify deployment: API healthy and database accessible"
  acceptance:
    ToolPasses(api-health)
  status: Open
  [trust: proposed, agent: "ops"]
}
```

## 6. File Organization

### 6.1 Directory Structure

```
my-project/
  anthill/
    project.anthill                       -- Project fact (required, exactly one)
    tools/
      custom-tools.anthill                -- Project-specific ToolDef facts (if any)
    workitems/
      feature-auth.anthill                -- accepted WorkItems (Open/Claimed/Verified/...)
      feature-batch-import.anthill
      feature-search.anthill.draft        -- proposed WorkItems (status: Draft)
      feature-search.feedback.anthill     -- Feedback facts for the feature under review
      feature-old.anthill.rejected        -- rejected proposals (status: ProposalRejected)
    facts/
      verified.anthill                    -- Auto-generated: facts from Verified WorkItems
  src/
  tests/
  ...
```

### 6.2 File Suffixes as Status Representation

File suffixes mirror the WorkItem status inside the file:

| Suffix | WorkItem status | Loaded into KB? |
|---|---|---|
| `.anthill` | `Open`, `Claimed`, `Delivered`, `Verified`, etc. | Yes |
| `.anthill.draft` | `Draft` | Yes |
| `.anthill.rejected` | `ProposalRejected(...)` | Yes |

The suffix is a **representation** of the status — it makes the lifecycle visible at the filesystem level (`ls` shows which features are draft/accepted/rejected). The semantic truth is the `status` field inside the WorkItem.

When `anthill accept <feature>` runs, it transitions all `Draft` items to `Open` AND renames `.anthill.draft` → `.anthill`. When `anthill reject <feature>` runs, it transitions to `ProposalRejected` AND renames to `.anthill.rejected`.

Inconsistency between suffix and content (e.g., `.anthill.rejected` containing `status: Open`) produces a parse-time warning.

### 6.3 Parsing

The system reads all `.anthill`, `.anthill.draft`, and `.anthill.rejected` files, desugars them into facts, and loads them into the `anthill.stage0` domain. All WorkItems are loaded regardless of status — `Draft` items are visible but not claimable, `ProposalRejected` items serve as context for future decomposition. Order doesn't matter — facts are identified by their entity type and key fields, not by file position.

### 6.4 Version Control

All `anthill/` files are checked into git, including `.draft` and `.rejected` files. The `facts/verified.anthill` file is auto-generated but also committed — it records the persistent knowledge produced by verified work items.

## 7. Relationship to the Kernel Language

The kernel language (see [kernel-language.md](../../docs/kernel-language.md)) defines 4 constructs plus syntactic sugar. Stage 0 uses a subset:

| Layer | Construct | Used at Stage 0? | How |
|---|---|---|---|
| **Kernel** | `domain` | Yes — `anthill.stage0` standard domain | Defines entity types |
| **Sugar** | `entity` | Yes — `Project`, `Module`, `ToolDef`, `WorkItem`, `Feedback`, etc. | Desugars to single-constructor `sort` |
| **Kernel** | `sort` | Yes — `SourceScope`, `WorkStatus`, `Capability`, etc. | Abstract and defined (ADT) types |
| **Kernel** | `rule` | No | No reasoning yet |
| **Kernel** | `operation` | No | No contracts yet |
| **Sugar** | `fact` (bodyless rule) | Yes — every project/tool/workitem is a fact | The fundamental unit |
| **Sugar** | `constraint` (headless rule) | No | Tools check invariants instead |
| **Sugar** | `operation { }` / `rule { }` (blocks) | No | No operations/rules yet |
| **Std lib** | `Obligation` (anthill.verification) | No | No proofs yet |
| **Std lib** | `Implementation` (anthill.verification) | No | No host-language linking yet |
| **Std lib** | `Requirement` (anthill.governance) | No — `WorkItem` is the precursor | Grows into `Requirement` at Stage 1 |
| **Std lib** | `Decision` (anthill.governance) | No | Deferred to later stages |
| **Terms** | `Const`, `Fn`, `Ref`, `Unspecified` | Yes | Descriptions, generates |
| **Terms** | `Var` (unification) | No | No unification |
| **Terms** | `Quoted` (host-language fragment) | No | No host-language embedding |

The key insight: Stage 0 doesn't avoid the kernel language — it uses it, with a specific domain. The sugar (`project`, `tool`, `workitem` blocks) is a convenience layer over facts, not a replacement for them. As a project grows, it adds more kernel constructs — `rule` for reasoning, `operation` for contracts — and more standard domains (`anthill.governance` for Requirements, `anthill.verification` for Obligations) using the same mechanism.

## 8. Grammar of the Sugar

The sugar grammar is minimal — it provides a readable way to assert facts in the `anthill.stage0` domain:

```
-- =================================================================
-- Stage 0 Sugar Grammar
-- =================================================================
-- All keywords are context-dependent (soft) except true/false.
-- Each declaration desugars to one or more facts in anthill.stage0.
-- =================================================================

File           ::= (ProjectDecl | ImportDecl | ToolDecl | WorkItemDecl | FeedbackDecl)*

Body[F]        ::= '{' F '}'  |  F 'end'

-- Project → desugars to Project(...) fact + Module(...) facts
ProjectDecl    ::= 'project' Name Body[ProjectFields]
ProjectFields  ::= ( 'language' ':' Identifier
                     ['build' ':' Identifier]
                     ['sources' ':' SourceRoot (',' SourceRoot)*]
                   | 'modules' ':' ModuleDecl+
                   )
                   [ImportDecl]*
                   'tools' ':' Name (',' Name)*
                   ['domains' ':' Name (',' Name)*]
                   [MetaBlock]

ModuleDecl     ::= 'module' Name Body[ModuleFields]
ModuleFields   ::= 'root' ':' StringLit
                   'language' ':' Identifier
                   ['build' ':' Identifier]
                   ['sources' ':' SourceRoot (',' SourceRoot)*]
                   [MetaBlock]

SourceRoot     ::= '{' 'path' ':' StringLit ','
                       ['language' ':' Identifier ',']
                       'scope' ':' SourceScope '}'
SourceScope    ::= 'Main' | 'Test' | 'Generated' | 'Docs'     -- constructors of sort SourceScope

-- Tool import → loads ToolDef facts from a pack
ImportDecl     ::= 'import' 'tools' ':' Name (',' Name)*

-- Tool → desugars to ToolDef(...) fact
ToolDecl       ::= 'tool' Name Body[ToolFields]
ToolFields     ::= 'command' ':' StringLit
                   ['args' ':' '[' StringLit (',' StringLit)* ']']
                   ['working_dir' ':' StringLit]
                   ['timeout' ':' DurationLit]
                   'success' ':' SuccessCriterion
                   [MetaBlock]

SuccessCriterion ::= 'ExitZero'                              -- constructors of sort SuccessCriterion
                   | 'ExitCode' '(' IntLit ')'
                   | 'OutputMatches' '(' StringLit ')'
                   | 'Custom' '(' Term ')'

-- WorkItem → desugars to WorkItem(...) fact
WorkItemDecl   ::= 'workitem' Id Body[WorkItemFields]
WorkItemFields ::= ['description' ':' Term]
                   ['context' ':' ContextRef (',' ContextRef)*]
                   'acceptance' ':' AcceptanceCriterion (',' AcceptanceCriterion)*
                   ['depends_on' ':' '[' Id (',' Id)* ']']
                   ['generates' ':' '[' Term (',' Term)* ']']
                   ['requires_capability' ':' Capability (',' Capability)*]
                   'status' ':' WorkStatus
                   [MetaBlock]

ContextRef     ::= 'FileRef' '(' StringLit [',' 'lines' ':' IntLit '..' IntLit] ')'  -- constructors of sort ContextRef
                 | 'FactRef' '(' Name ',' Term ')'
                 | 'WorkItemRef' '(' Id ')'

AcceptanceCriterion ::= 'ToolPasses' '(' Name [',' Bindings] ')'  -- constructors of sort AcceptanceCriterion
                      | 'FactHolds' '(' Name ',' Term ')'
                      | 'Compiles' '(' (SourceRoot | 'module' ':' Name) ')'
                      | 'Constraint' '(' Term ')'

WorkStatus     ::= 'Draft'                                   -- constructors of sort WorkStatus
                 | 'Open'
                 | 'Claimed' '(' 'agent' ':' StringLit ',' 'since' ':' StringLit ')'
                 | 'Delivered' '(' 'agent' ':' StringLit ',' 'at' ':' StringLit ')'
                 | 'Verified' '(' 'at' ':' StringLit ')'
                 | 'Rejected' '(' 'reason' ':' StringLit ',' 'at' ':' StringLit ')'
                 | 'ProposalRejected' '(' 'reason' ':' StringLit ',' 'at' ':' StringLit ')'
                 | 'Stale' '(' 'reason' ':' StringLit ',' 'since' ':' StringLit ')'

Capability     ::= 'Code' '(' 'languages' ':' '[' StringLit (',' StringLit)* ']' ')'
                 | 'Test'
                 | 'Refine'
                 | 'Review'
                 | 'Decompose'
                 | 'Architect'
                 | 'HumanJudgment'

-- Feedback → desugars to Feedback(...) fact
FeedbackDecl   ::= 'feedback' Body[FeedbackFields]
FeedbackFields ::= 'workitem' ':' Id
                   'author' ':' StringLit
                   'content' ':' Term
                   'at' ':' StringLit
                   [MetaBlock]

-- Metadata → sugar for Meta(...) Fn term (see kernel-language.md §7)
-- Meta is open-keyed: any Name : Term pair is accepted.
MetaBlock      ::= '[' MetaEntry (',' MetaEntry)* ']'
MetaEntry      ::= Name ':' Term                   -- any key-value pair
                 -- Well-known keys: trust, agent, timestamp, iteration, source, supersedes
                 -- Additional keys are project-defined and pass through.

Trust          ::= 'axiom' | 'decision' | 'proposed'
                 | 'tested' '(' IntLit ')' | 'verified' | 'stale'
                 | 'proved' | 'empirical'
                 -- Surface sugar: tested-47 → tested(47)

Bindings       ::= '{' Identifier ':' Term (',' Identifier ':' Term)* '}'

-- Terms (core language subset)
Term           ::= StringLit | IntLit | FloatLit | BoolLit
                 | 'Ref' '(' Name ')'
                 | Name '(' Term (',' Term)* ')'
                 | '<"' [^"]* '">'                       -- Unspecified (simple)
                 | '<"' [^"]* '"' ',' 'hints' ':' '[' Term (',' Term)* ']' '>'  -- Unspecified with hints

-- Lexical (same as core language)
Id             ::= Name
Name           ::= Identifier ('.' Identifier)*
Identifier     ::= Letter (Letter | Digit | '-' | '_')*
                 | '"' [^"]+ '"'
StringLit      ::= '"' [^"]* '"'
IntLit         ::= '-'? Digit+
FloatLit       ::= '-'? Digit+ '.' Digit+
BoolLit        ::= 'true' | 'false'
DurationLit    ::= IntLit ('ms' | 's' | 'm' | 'h' | 'd')
```
