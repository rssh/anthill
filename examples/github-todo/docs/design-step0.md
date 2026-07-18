# Stage 0: Structured Work Decomposition

> Structured tasks with machine-checkable acceptance, dependency tracking, and parallel execution by humans and AI agents.

## 1. User Stories

### Developer working with an AI agent

> I describe what I want. The agent breaks it into tasks with clear "done" criteria. I review. The agent works through tasks, verifying each one. I see progress and can intervene when needed.

```
Me:     "Add authentication to the API"
Agent:  → proposes 4 tasks with acceptance criteria (Draft)
Me:     "merge tasks 2 and 3, add lint check"
Agent:  → revises (Draft, iteration 2)
Me:     "accept"
Agent:  → Draft → Open, starts working
        → claims WI-001, implements, delivers
        → verifies: compiles? yes. tests pass? yes. → Verified
        → claims WI-002 (deps met), continues...
Me:     "status"
        → 2 verified, 1 in progress, 1 blocked
```

### Team with multiple AI agents

> We decompose a cross-layer feature. Independent tasks go to different agents working in parallel — backend, frontend, database. Each agent works in its own git worktree. Verified branches merge back.

```
WI-001: DB migration          → agent A (worktree A)
WI-002: Backend endpoint      → agent B (worktree B), waits for WI-001
WI-003: Frontend form         → agent C (worktree C), independent
WI-004: Integration test      → waits for WI-002 + WI-003
```

Agents A and C work simultaneously. No orchestrator — the dependency DAG IS the coordination.

### CI / automation

> On every PR, verify that all delivered tasks pass their acceptance criteria. Block merge if any check fails.

```
anthill verify --all-delivered    # run in CI
anthill validate                  # check consistency (deps exist, no cycles)
```

### Developer inspecting state

> I want to see what's done, what's in progress, what's blocked — at a glance. The state is in version-controlled files alongside the code.

```
anthill status
anthill list --open
anthill graph
```

## 2. Actions

The developer interacts through **commands**, not by editing files. The tool reads and writes the files.

| Action | What it does |
|--------|-------------|
| `decompose "desc"` | Break a description into Draft tasks |
| `accept` | Review and accept Draft → Open |
| `reject "reason"` | Reject Draft → ProposalRejected |
| `list [--status X]` | Show tasks, optionally filtered by status |
| `status` | Summary: N open, N claimed, N verified, N blocked |
| `next` | Show the next claimable task (Open, all deps Verified) |
| `claim <id>` | Take a task → Claimed |
| `deliver <id>` | Mark work as done → Delivered |
| `verify [<id>]` | Run acceptance criteria → Verified or Rejected |
| `feedback <id> "text"` | Attach a comment to a task |
| `graph` | Show the dependency DAG |
| `validate` | Check consistency (deps exist, no cycles, refs valid) |

These actions are the same whether invoked from the CLI, the Claude Code skill, or an MCP tool call.

## 3. Core Concepts

**Three entities:**

| Entity | What it is | Key fields |
|--------|-----------|------------|
| **Task** | A unit of work with verifiable acceptance | id, description, acceptance, depends_on, status |
| **Tool** | An external command that checks something | name, command, args, success criterion |
| **Project** | Binds a codebase to the anthill | language, build, sources, tools |

**One state machine:**

```
         accept        claim         deliver        verify
Draft ──────────▶ Open ──────▶ Claimed ──────▶ Delivered ──────▶ Verified
                    ▲              │                │
                    └──────────────┘                └────────▶ Rejected
                        release                    (acceptance fails)
```

Draft tasks can go through feedback/revision cycles before acceptance.
Any task can become Stale when its environment changes.

**One coordination mechanism:** the dependency DAG.

A task is **claimable** when: status is Open AND all dependencies are Verified.
Independent tasks (no mutual dependencies) can be worked in parallel.

## 4. Data and Logic

Two kinds of content, two formats:

| What | Format | Who writes it | Purpose |
|------|--------|--------------|---------|
| **Entity data** (tasks, config, tools) | TOML/JSON — standard term serialization | The tool | Structured data, machine-managed |
| **Logic** (rules, queries, constraints) | `.anthill` — the anthill language | Humans | Workflow logic, reasoning |
| **Content** (descriptions, specs, code) | `.md`, source files | Humans and agents | The actual work product |

Tasks **reference** markdown and source files — they don't contain them.

### File layout

```
my-project/
  anthill/
    anthill.toml          ← configuration (project, tools) — human-authored, rarely changes
    tasks.toml            ← task data — tool-managed, changes on every action
    rules.anthill         ← workflow rules — human-authored
  docs/
    auth-design.md        ← referenced by tasks, written by humans/agents
  src/
    models/user.rs        ← referenced by tasks, written by agents
```

### Term serialization (TOML/JSON)

Entity facts in the KB can be serialized to/from TOML or JSON via a standard `meta` + `data` envelope (see [Proposal 021: Term Serialization](../../docs/proposals/021-term-serialization.md)). The format is generic — any entity type can use it.

**anthill.toml** — configuration:

```toml
[project.meta]
entity = "anthill.stage0.Project"

[project.data]
name = "my-app"
language = "rust"
build = "cargo"

[tools.meta]
entity = "anthill.stage0.ToolDef"

[[tools.data]]
name = "cargo-test"
command = "cargo"
args = ["test"]
success = "ExitZero"
```

**tasks.toml** — processing data:

```toml
[meta]
entity = "anthill.stage0.Task"

[[data]]
id = "WI-AUTH-001"
description = "Define User entity and auth traits"
status = "Open"
depends_on = []
acceptance = [{ Compiles = "src" }, { ToolPasses = "cargo-test" }]
context = ["src/models/user.rs", "docs/auth-design.md"]

[[data]]
id = "WI-AUTH-002"
description = "Implement JWT token generation"
status = "Open"
depends_on = ["WI-AUTH-001"]
acceptance = [{ Compiles = "src" }, { ToolPasses = "cargo-test" }]
context = ["src/auth/jwt.rs"]
```

Both files produce facts in the KB: `Task(id: "WI-AUTH-001", status: Open, ...)`, `ToolDef(name: "cargo-test", ...)`. The tool writes the TOML; the KB loads and queries it.

### rules.anthill — workflow logic

```anthill
rule claimable(?id, ?desc)
  :- Task(id: ?id, status: Open, description: ?desc),
     all_deps_verified(?id)

rule blocked(?id, ?desc)
  :- Task(id: ?id, status: Open, description: ?desc),
     not(all_deps_verified(?id))
```

The anthill language handles logic. Data lives in standard formats.

## 5. The Toolset

All tools share the same `anthill/` state. No tool is primary — they cooperate via files.

| Tool | Purpose | When |
|------|---------|------|
| Claude Code + `/anthill` skill | Conversational workflow | Day one |
| `anthill` CLI | Validation, CI, scripting | When you need automation |
| `anthill-spawn` | Multi-agent coordination in git worktrees | When parallel agents are needed |

Layers are additive. Start with the skill alone.

## 6. Growth Path

Stage 0 constructs evolve without rewriting:

- **Tasks → Requirements**: acceptance grows from "tests pass" to formal contracts
- **Dependencies → Contamination**: invalid root → dependents marked stale automatically
- **TOML data → KB facts**: the tool already loads TOML into the KB; as the project matures, richer entity types and rules emerge naturally
- **Tool checks → Proofs**: acceptance becomes proof obligations for verification engines

At no point does the project stop and rewrite. Each stage adds a layer on top.
