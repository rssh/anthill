# Example: GitHub-Style TODO Tracking

This example demonstrates using anthill as a structured TODO / work-item tracker for a software project. It shows how anthill's knowledge base and fact-based approach naturally supports project management — work items, tools, dependencies, and status tracking are all just facts in the KB.

## Overview

Anthill's kernel language (`sort`, `entity`, `fact`, `rule`) provides the foundation. The stage0 syntactic sugar (`project`, `tool`, `workitem`, `feedback`) makes it convenient to express project management concepts without writing raw entity facts.

Everything is a fact:
- A **project** is a fact: `Project("my-app", language: "rust", ...)`
- A **tool** is a fact: `ToolDef("cargo-test", command: "cargo", args: ["test"], ...)`
- A **work item** is a fact: `WorkItem("WI-001", description: "Add auth", status: Open)`
- **Status changes** are new facts that supersede previous ones

## Files

| File | Description |
|------|-------------|
| `project.anthill` | Project configuration: language, build system, tools |
| `workitems.anthill` | Work items with dependencies, acceptance criteria, status |
| `tools.anthill` | Custom tool definitions (project-specific) |
| `feedback.anthill` | Review feedback on work items |
| `domain.anthill` | The `anthill.stage0` domain definition (entity types used above) |

## How It Works

### 1. Define your project

```anthill
project my-github-app {
  language: rust
  build: cargo
  tools: cargo-build, cargo-test, cargo-clippy
}
```

This desugars to a `Project(...)` fact in the KB. Declaring `build: cargo` auto-imports standard cargo tools.

### 2. Decompose work into items

```anthill
workitem WI-AUTH-001 {
  description: "Add JWT authentication middleware"
  context:
    FileRef("src/middleware/auth.rs")
  acceptance:
    Compiles({ path: "src", scope: Main })
    ToolPasses(cargo-test)
  status: Open
}
```

Each work item is a fact with:
- **context**: files, other work items, or KB facts it relates to
- **acceptance**: how to verify it's done (tool passes, compiles, fact holds)
- **depends_on**: other work items that must be `Verified` first
- **status**: lifecycle state (`Draft → Open → Claimed → Delivered → Verified`)

### 3. Query the KB

Since work items are facts, standard KB queries work:

```
-- Find all open work items
query WorkItem(?id, status: Open)

-- Find items blocked on WI-AUTH-001
query WorkItem(?id, depends_on: ?deps) where contains(?deps, "WI-AUTH-001")

-- Find all feedback on a work item
query Feedback(workitem: "WI-AUTH-002", ?author, ?content, ?at)
```

### 4. Track status via fact supersession

Status changes produce new facts:

```anthill
-- Initially:
workitem WI-AUTH-001 { status: Open }

-- Agent claims it:
workitem WI-AUTH-001 { status: Claimed("agent-1", "2027-03-15") }
  [supersedes: WI-AUTH-001-v1]

-- Agent delivers:
workitem WI-AUTH-001 { status: Delivered("agent-1", "2027-03-16") }
  [supersedes: WI-AUTH-001-v2]
```

The current status is always the most recent (non-superseded) fact.

## WorkItem Lifecycle

```
                feedback           accept          claim         deliver          verify
Draft ◀──────────────────▶ Draft ──────▶ Open ─────────▶ Claimed ──────▶ Delivered ──────▶ Verified
  │        (revise)                        ▲                │               │  ▲
  │   reject                   release     │                │  feedback     │  │  feedback
  │                            └───────────┘                └──(rework)────▶│  └──(rework)──┘
  ▼                                                                         │
ProposalRejected                                                            └──────▶ Rejected
```

## Design Principle

This example uses anthill's core insight: **domain knowledge as facts in a knowledge base**. There is no separate task-tracking language — `project`, `tool`, `workitem` are syntactic sugar that desugar to standard `entity` and `fact` declarations. As a project grows, the same KB gains rules, constraints, and reasoning without changing the data model.

See [domain.anthill](domain.anthill) for the full entity type definitions.
