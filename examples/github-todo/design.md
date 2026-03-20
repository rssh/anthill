# Stage 0: The Practical Bootstrap — Structured Work Decomposition for the Anthill

> **Example**: For a concrete, runnable example of Stage 0 usage (project config, work items, tools, feedback), see [`examples/github-todo/`](./).

## 1. Introduction

Stage 0 is the lightweight entry point to the anthill metasystem. It provides **structured work decomposition with machine-checkable acceptance criteria** — no proofs, no formal logic, no reasoning engine. Just tasks, tools, and tests.

Where the full anthill (see [metasystem-design-draft.md](../metasystem-design-draft.md)) describes a system of domains, proof obligations, trust levels, and stigmergic agents operating over a language-independent knowledge base, Stage 0 asks a simpler question: **can we decompose work into structured items with verifiable acceptance, and run those checks automatically?**

The answer is three entity types defined in the `anthill.stage0` standard domain of the core language (see [standard-library.md §2](standard-library.md#2-the-standard-domain-anthillstage0) for the full domain definition):

- **Project** — binds a knowledge base to a real codebase (source roots, tools, domains)
- **ToolDef** — binds an external command (compiler, test runner, linter) to the KB world
- **WorkItem** — structured task with acceptance criteria that bridge informal intent and formal requirements

These are not special grammar productions — they are ordinary entity types whose instances are facts in the KB. The `.anthill` file format provides syntactic sugar (`project`, `tool`, `workitem` blocks) that desugars to `fact` assertions in the `anthill.stage0` domain.

These constructs are sufficient for:
- Parallel work by multiple agents (human or LLM) on independent items
- Machine-checkable acceptance (did the tests pass? does it compile?)
- Tracking what was done, by whom, and whether it was verified
- Gradual growth toward the full anthill as the project matures

## 2. Motivation: The Bootstrap Cost Problem

The full anthill is powerful but has a high bootstrap cost. To use domains, proof obligations, and formal verification, a project must:
1. Define domain axioms in the core language
2. Formalize requirements with pre/postconditions
3. Set up proof engines or verification backends
4. Train or configure embedding models for semantic search

Real projects cannot start there. Consider:

- **cps2** (async programming framework in Scala): has a compiler plugin, tests, documentation. The immediate need is not "prove that CPS transforms preserve semantics" — it's "add match expression support, and verify it compiles and passes tests."

- **domains.gradsoft.ua** (domain registration service): has a web frontend, backend API, database layer. The immediate need is not "formalize the domain lifecycle state machine" — it's "add a new domain operation, and verify it works across all layers."

These projects can benefit from structured decomposition **today**, without any formalization overhead. Stage 0 provides this: define what needs to be done, define how to check it's done, let agents work in parallel, verify automatically.

## 4. Stage 0 Entity Types

Entity types and sorts in the `anthill.stage0` standard domain, with syntactic sugar for convenient authoring. The kernel language ([kernel-language.md](../../docs/kernel-language.md)) provides four constructs: `domain`, `sort` (abstract and defined/ADT), `rule`, and `operation`; `entity` is syntactic sugar for a single-constructor defined sort. Stage 0 uses `entity` and `fact` to define these types and their instances. The three primary entities are **Project**, **ToolDef**, and **WorkItem**; supporting types include **Feedback** (refinement comments) and the **Capability** sort (what agents can do).

For the full domain definition, see [standard-library.md §2](standard-library.md#2-the-standard-domain-anthillstage0). For the sugar grammar and file organization, see [standard-library.md §3–§8](standard-library.md#3-syntactic-sugar).

### 4.1 Project

The **Project** entity formalizes what §2.1 of the main draft describes conceptually — it binds a knowledge base to a real codebase. A project can be **simple** (single language/build) or **composite** (multiple modules with different languages and build systems).

When `sources` is omitted, the system infers source roots from `build` conventions (e.g., sbt → `src/main/scala` + `src/test/scala`). When `build` is also omitted, it detects from root markers (`build.sbt`, `pom.xml`, `package.json`, etc.).

Modules are referenced by name elsewhere: `$module` in tool args resolves to the module's root path, `Compiles(module: backend)` compiles a specific module, and `FileRef` paths can be relative to a module root.

### 4.2 ToolDef

A **ToolDef** binds an external command to the KB world — the bridge between the knowledge base and real builds, tests, and checks.

Common tools (sbt, npm, pytest, flyway, etc.) are provided as **standard packs** shipped with anthill and auto-imported via the `build` field or explicit `import tools` (see [standard-library.md §3.4](standard-library.md#34-tool-sugar)). Projects only define project-specific tools. The `$param` placeholders in args are substituted when the tool is invoked. Standard packs can be **overridden** per-project — declare a `tool` with the same name to replace the imported definition.

### 4.3 WorkItem

The **WorkItem** is the key entity type — lighter than a Requirement (no formal expression needed) but heavier than free text (structured, machine-checkable). Each WorkItem instance is a fact in the `anthill.stage0` domain.

**Key design choices:**

1. **`description` is flexible** — can be an inline string, an `Unspecified` term (partial formalization), or a `FileRef(path)` pointing to a markdown file. File references are natural for rich descriptions with examples and diagrams; the skill/CLI reads the file when presenting the item. An agent can create a WorkItem with just an id and acceptance criteria; the description can be refined later.

2. **`acceptance` is a list** — all criteria must pass for the item to be Verified. This enables compound checks: "compiles AND tests pass AND lint is clean."

3. **`generates`** — when a WorkItem reaches Verified status, it can automatically produce KB facts. This is the bridge from Stage 0 to the full anthill: verified work items generate persistent knowledge.

4. **`depends_on`** — creates a partial order over work items. Independent items can be worked in parallel. This is the lightweight precursor to the full dependency graph used for contamination propagation.

5. **`requires_capability`** — optional list of `Capability` values needed to work on this item. The spawner matches agent capabilities against this field. Capabilities are: `Code(languages)`, `Test`, `Refine`, `Review`, `Decompose`, `Architect`, `HumanJudgment`. See [standard-library.md §2](standard-library.md#2-the-standard-domain-anthillstage0) for the `Capability` sort.

6. **`status` transitions** follow a state machine with **refinement loops** — most transitions can cycle through feedback and revision before advancing:
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

**Refinement loops** are driven by `Feedback` facts (see [standard-library.md §3.6](standard-library.md#36-feedback-sugar)). An agent with `Refine` capability attaches feedback to a WorkItem; the responsible agent revises and produces a new fact (via `meta.supersedes`). This cycle repeats N times until the reviewer (with `Review` capability) accepts or rejects. Feedback facts persist as history — they show why the design evolved.

At Stage 0, the `trust` metadata field is simpler: typically `proposed` (for new items), `tested-N` (for items verified by tools), or `axiom` (for items asserted by humans). The full trust hierarchy (`proved`, `verified`, `empirical`, etc.) becomes relevant as the project grows. For metadata details, see [kernel-language.md §7](../../docs/kernel-language.md#7-metadata).

## 5. The Development Workflow

The Stage 0 workflow is the stigmergic loop (see [metasystem-design-draft.md §6](../metasystem-design-draft.md#6-agents-and-stigmergy)) in its simplest form.

### 5.1 Decomposition: From Intent to WorkItems

Decomposition turns a high-level description into structured WorkItems with acceptance criteria. It has three phases: input, proposal, and review — with an **iterative refinement loop** between proposal and review.

**Input.** Several entry points, all producing the same result:

```
anthill decompose "Add match expression support"           -- free text
anthill decompose --from-file FEATURE.md                   -- from a document
anthill decompose --from-failure sbt-test                  -- from a failing tool
```

In an MCP/LLM session, the agent calls `anthill_decompose(description)` or uses `/anthill decompose "..."`.

**Proposal.** The decomposer (LLM-assisted) reads:
- The input description
- Project configuration (languages, modules, tools)
- Existing WorkItems (to avoid duplication, link dependencies)
- Source files referenced or relevant
- Previous `ProposalRejected` WorkItems (to avoid repeating rejected approaches)
- Previous `Feedback` facts on this feature (to address earlier comments)

It writes WorkItems with `status: Draft` to a `.anthill.draft` file:

```
-- anthill/workitems/match-support.anthill.draft
workitem WI-CPS2-MATCH-001 {
  description: "Add AST pattern matching for match expressions"
  context: FileRef("compiler-plugin/src/main/scala/cps/plugin/CpsTransformPhase.scala")
  acceptance: Compiles({ path: "compiler-plugin/src/main/scala", scope: Main })
  requires_capability: Code(languages: ["scala"])
  depends_on: []
  status: Draft
  [trust: proposed, agent: "decomposer"]
}

workitem WI-CPS2-MATCH-002 { ... status: Draft }
...
```

The `.draft` suffix is a file-system representation of the `Draft` status — it makes the lifecycle visible at `ls` level. The semantic truth is the `status` field inside the WorkItem. Draft WorkItems are loaded into the KB but are not claimable — they're visible to reviewers.

**Review with refinement.** The reviewer provides feedback, the decomposer revises, and the cycle repeats until acceptance or rejection:

```
anthill review match-support         -- show Draft items from this file

-- Refinement loop (N iterations):
anthill feedback match-support \
  --content "merge WI-003 and WI-004, add scalafmt to acceptance"
                                     -- creates Feedback fact, decomposer revises Draft

-- Final decision:
anthill accept match-support         -- Draft → Open, rename .anthill.draft → .anthill
anthill reject match-support \
  --reason "wrong approach entirely"
                                     -- Draft → ProposalRejected, rename → .anthill.rejected
```

In Claude Code with the `/anthill` skill, the same flow is conversational:

```
User: /anthill decompose "add match support"
Claude: *writes .anthill.draft, shows 5 WorkItems*

User: "merge items 3 and 4, add scalafmt-check to all"
Claude: *records Feedback fact, revises Draft (iteration 2), shows updated items*

User: "WI-002 needs Code(["scala"]) capability"
Claude: *records Feedback, revises Draft (iteration 3)*

User: /anthill accept
Claude: *Draft → Open, .draft → .anthill*
```

Each revision produces a new WorkItem fact (via `meta.supersedes`, incrementing `meta.iteration`). Feedback facts accumulate in `.feedback.anthill` files — they persist as a record of why the decomposition looks the way it does.

Accept and reject do two things: transition the `status` field (semantic) and rename the file (representation). Accepted items become `status: Open` and claimable. Rejected items become `status: ProposalRejected(reason, at)` and remain in the KB as **negative pheromone** — the decomposer queries them before proposing again, avoiding previously rejected approaches.

### 5.2 The Loop

Once WorkItems are accepted, the stigmergic execution loop begins:

```
1. Agents (human or LLM) observe open items
   → each agent sees the list of Open items and their dependencies
   → agent picks an item whose depends_on are all Verified

2. Agent claims an item, works on it, delivers
   → modifies code, adds tests, updates docs
   → marks the item as Delivered

3. Acceptance runner verifies
   → runs all AcceptanceCriteria for the item
   → if all pass → Verified; if any fail → Rejected with diagnostics

4. Verified items may generate KB facts
   → e.g., "match expressions are supported in CPS transforms" [trust: tested-N]

5. Cycle continues with remaining Open items
   → new decomposition can be triggered for follow-up work
```

### 5.3 Parallel Execution

Independent WorkItems (no mutual `depends_on`) can be worked on simultaneously by different agents. The dependency graph defines the partial order:

```
                    WI-1: Parser support
                   ╱                    ╲
WI-2: Type checker    WI-3: Transform     WI-4: Error messages
        support         logic               (independent)
                   ╲                    ╱
                    WI-5: Integration tests
                              │
                    WI-6: Documentation
```

In this example, WI-2, WI-3, and WI-4 can proceed in parallel once WI-1 is Verified. WI-5 waits for WI-2 and WI-3. WI-4 has no dependencies at all and can start immediately.

### 5.4 The Acceptance Runner

The acceptance runner is the Stage 0 equivalent of the core verification procedures. It is much simpler — it just runs tools and checks results:

```
function verifyWorkItem(item: WorkItem): VerifyResult =
  for criterion in item.acceptance:
    match criterion:
      case ToolPasses(tool, params) =>
        result = runTool(tool, params)
        if not result.success: return Rejected(result.diagnostics)

      case Compiles(source) =>
        result = runTool(project.compiler(source), {})
        if not result.success: return Rejected(result.diagnostics)

      case FactHolds(domain, pattern) =>
        results = kb.query(domain, pattern)
        if results.isEmpty: return Rejected("fact not found: " + pattern)

      case Constraint(cond) =>
        result = kb.evaluate(cond)
        if not result: return Rejected("constraint failed: " + cond)

  return Verified(timestamp = now, results = collectedResults)
```

## 6. Concrete Examples

### 6.1 cps2: Adding Match Expression Support

**Project context:** cps2 is a Scala compiler plugin that transforms CPS (continuation-passing style) code. It needs to handle `match` expressions in async blocks.

```
project cps2 {
  language: scala
  build: sbt                               -- auto-imports std.sbt
  import tools: std.scalafmt
  tools: sbt-compile, sbt-test, sbt-test-only, scalafmt-check
}

-- Only project-specific tool: sbt-test-only with cps2 subproject path
tool sbt-test-only {
  command: "sbt"
  args: ["cps2/testOnly", "$testClass"]
  timeout: 10m
  success: ExitZero
}

-- WorkItem decomposition

workitem WI-CPS2-MATCH-001
  description: "Add AST pattern matching for match expressions in CPS transform phase"
  context:
    FileRef("compiler-plugin/src/main/scala/cps/plugin/CpsTransformPhase.scala")
    FileRef("compiler-plugin/src/main/scala/cps/plugin/TreeTransform.scala")
  acceptance:
    Compiles({ path: "compiler-plugin/src/main/scala", scope: Main })
  depends_on: []
  status: Open
  [agent: unassigned]
end

workitem WI-CPS2-MATCH-002
  description: "Implement CPS transform logic for simple match (scrutinee + literal cases)"
  context:
    WorkItemRef(WI-CPS2-MATCH-001)
    FileRef("compiler-plugin/src/main/scala/cps/plugin/MatchTransform.scala")
  acceptance:
    Compiles({ path: "compiler-plugin/src/main/scala", scope: Main })
    ToolPasses(sbt-test-only, { testClass: "cps.plugin.MatchSimpleTest" })
  depends_on: [WI-CPS2-MATCH-001]
  status: Open
end

workitem WI-CPS2-MATCH-003
  description: "Implement CPS transform for match with guard conditions"
  context:
    WorkItemRef(WI-CPS2-MATCH-002)
  acceptance:
    Compiles({ path: "compiler-plugin/src/main/scala", scope: Main })
    ToolPasses(sbt-test-only, { testClass: "cps.plugin.MatchGuardTest" })
  depends_on: [WI-CPS2-MATCH-001]
  status: Open
end

workitem WI-CPS2-MATCH-004
  description: "Implement CPS transform for nested match expressions"
  context:
    WorkItemRef(WI-CPS2-MATCH-002)
  acceptance:
    Compiles({ path: "compiler-plugin/src/main/scala", scope: Main })
    ToolPasses(sbt-test-only, { testClass: "cps.plugin.MatchNestedTest" })
  depends_on: [WI-CPS2-MATCH-002]
  status: Open
end

workitem WI-CPS2-MATCH-005
  description: "Full integration test: all match expression variants in async blocks"
  context:
    WorkItemRef(WI-CPS2-MATCH-002)
    WorkItemRef(WI-CPS2-MATCH-003)
    WorkItemRef(WI-CPS2-MATCH-004)
  acceptance:
    ToolPasses(sbt-test)
    ToolPasses(scalafmt-check)
  depends_on: [WI-CPS2-MATCH-002, WI-CPS2-MATCH-003, WI-CPS2-MATCH-004]
  generates:
    [Fact("cps2.transforms.matchSupported", Meta(trust: tested-N))]
  status: Open
end

workitem WI-CPS2-MATCH-006
  description: "Update documentation for match expression support"
  context:
    WorkItemRef(WI-CPS2-MATCH-005)
    FileRef("docs/match-expressions.md")
  acceptance:
    ToolPasses(sbt-compile)  -- docs may include compiled examples
  depends_on: [WI-CPS2-MATCH-005]
  status: Open
end
```

**Parallel structure:** WI-002 and WI-003 can proceed in parallel (both depend only on WI-001). WI-004 waits for WI-002. WI-005 waits for all three. WI-006 waits for WI-005. Two agents can work simultaneously on the transform logic variants.

### 6.2 domains.gradsoft.ua: Adding a New Domain Operation

**Project context:** A domain registration service with a web frontend (TypeScript), backend API (Scala), and database layer (SQL). Adding a "transfer domain" operation requires changes across all layers.

```
project domains-gradsoft {
  modules:
    module backend {
      root: "backend"
      language: scala
      build: sbt                           -- auto-imports std.sbt
    }
    module frontend {
      root: "frontend"
      language: typescript
      build: npm                           -- auto-imports std.npm
    }
    module db {
      root: "db"
      language: sql
    }
  import tools: std.flyway                 -- for db module
  tools: sbt-compile, sbt-test, npm-test, npm-build, flyway-migrate
}

-- No project-specific tool definitions needed —
-- all tools come from std.sbt, std.npm, and std.flyway

-- Cross-layer WorkItem decomposition

workitem WI-DOM-XFER-001
  description: "Database migration: add transfer_requests table and transfer status to domains"
  context:
    FileRef("db/migrations/")
    FileRef("backend/src/main/scala/ua/gradsoft/domains/model/Domain.scala")
  acceptance:
    ToolPasses(flyway-migrate, { dbUrl: "jdbc:postgresql://localhost:5432/domains_test" })
  depends_on: []
  status: Open
end

workitem WI-DOM-XFER-002
  description: "Backend: domain transfer API endpoint and service layer"
  context:
    FileRef("backend/src/main/scala/ua/gradsoft/domains/api/DomainController.scala")
    FileRef("backend/src/main/scala/ua/gradsoft/domains/service/DomainService.scala")
    WorkItemRef(WI-DOM-XFER-001)
  acceptance:
    Compiles(module: backend)
    ToolPasses(sbt-test)
  depends_on: [WI-DOM-XFER-001]
  status: Open
end

workitem WI-DOM-XFER-003
  description: "Frontend: transfer domain UI form and confirmation dialog"
  context:
    FileRef("frontend/src/components/DomainManagement.tsx")
    FileRef("frontend/src/api/domainApi.ts")
  acceptance:
    ToolPasses(npm-build)
    ToolPasses(npm-test)
  depends_on: []  -- frontend can proceed independently with mocked API
  status: Open
end

workitem WI-DOM-XFER-004
  description: "Integration: connect frontend to backend transfer endpoint"
  context:
    WorkItemRef(WI-DOM-XFER-002)
    WorkItemRef(WI-DOM-XFER-003)
    FileRef("frontend/src/api/domainApi.ts")
  acceptance:
    ToolPasses(npm-build)
    ToolPasses(npm-test)
    ToolPasses(sbt-test)
  depends_on: [WI-DOM-XFER-002, WI-DOM-XFER-003]
  generates:
    [Fact("domains.operations.transferSupported", Meta(trust: tested-N))]
  status: Open
end
```

**Cross-layer parallelism:** WI-001 (DB) and WI-003 (frontend) can proceed in parallel — different layers, no dependency. WI-002 (backend) waits for WI-001 (needs the new tables). WI-004 (integration) waits for both WI-002 and WI-003. A database specialist, a Scala developer, and a TypeScript developer can all work simultaneously.

## 7. Growth Path: From Stage 0 to the Full Anthill

Stage 0 constructs are designed to evolve naturally as the project matures. Each stage adds capabilities without invalidating previous work.

### Stage 0 → Stage 1: Verified WorkItems Generate Persistent Facts

At Stage 0, verified WorkItems produce simple facts: "this was checked and passed." At Stage 1, these facts enter the KB as first-class citizens:

```
-- Stage 0: WorkItem verified → simple record
workitem WI-CPS2-MATCH-005
  status: Verified(at: 2027-03-15, results: [sbt-test: pass, scalafmt: pass])
  generates: [Fact("cps2.transforms.matchSupported", Meta(trust: tested-N))]
end

-- Stage 1: The generated fact lives in a domain, participable in reasoning
domain cps2.transforms
  fact matchSupported
    "CPS transform handles match expressions correctly"
    [trust: tested-47, source: WI-CPS2-MATCH-005, iteration: 42]
end
```

### Stage 1 → Stage 2: Dependencies Extracted Between Facts

As facts accumulate, the system begins tracking dependencies between them — not just between WorkItems, but between the facts they generated:

```
-- Stage 2: dependency tracking
fact matchSupported depends_on [parserSupported, typeCheckerSupported]
-- Changing the parser may invalidate match support → staleness propagation
```

### Stage 2 → Stage 3: Contamination Propagation via Dependency Graph

The dependency graph enables contamination propagation (see [metasystem-design-draft.md §6.4](../metasystem-design-draft.md#64-pheromone-dynamics-contamination-decay-and-reinforcement)): when a root fact becomes invalid, all dependents are marked stale automatically. What was manual re-testing at Stage 0 becomes automatic staleness tracking.

### Stage 3 → Stage 4: Acceptance Criteria Grow into Contracts

WorkItem acceptance criteria evolve from "tool passes" to formal contracts:

```
-- Stage 0: tool-based acceptance
acceptance: ToolPasses(sbt-test-only, { testClass: "MatchSimpleTest" })

-- Stage 4: formal contract
requirement MATCH-TRANSFORM : functional
  "CPS transform of match preserves evaluation semantics"
  formal: forall(expr: MatchExpr, ctx: AsyncContext,
    equivalent(eval(transform(expr, ctx)), eval(expr)))
```

### Stage 4 → Stage 5: Contracts Get Formal Proofs

At Stage 5, the formal contracts from Stage 4 become proof obligations dispatched to proof engines (ctproof, Z3, Isabelle). The acceptance criterion is no longer "tests pass" but "proof accepted by the verification kernel."

**The key property of this growth path:** at no point does the project need to stop and rewrite. Each stage adds a layer on top of the previous one. WorkItems created at Stage 0 remain valid — they just gain a richer context as the project matures.

## 8. KB Service Subset for Stage 0

Stage 0 requires only a minimal subset of the full KB Service Protocol (see [metasystem-design-draft.md §5.5.3](../metasystem-design-draft.md#553-kb-service-protocol)). No proof checking, no unification, no reasoning engine.

### 8.1 Required Operations

```
service AnthillStage0:

  // WorkItem lifecycle
  createWorkItem(item: WorkItem)                    → WorkItemId
  queryWorkItems(filter: WorkItemFilter)             → List[WorkItem]
  claimWorkItem(id: WorkItemId, agent: AgentId)      → ClaimResult
  deliverWorkItem(id: WorkItemId, agent: AgentId)    → DeliverResult
  verifyWorkItem(id: WorkItemId)                     → VerifyResult
  rejectWorkItem(id: WorkItemId, reason: String)     → RejectResult

  // Feedback and refinement
  addFeedback(workitem: WorkItemId, content: Term)   → FeedbackId
  queryFeedback(workitem: WorkItemId)                → List[Feedback]

  // Tool invocation
  runTool(tool: Name, params: Bindings)              → ToolResult
  listTools()                                        → List[ToolDef]

  // Project introspection
  getProject()                                       → Project
  status()                                           → ProjectStatus

  // Simple fact storage (for generates)
  assertFact(fact: Term, meta: Meta)                 → FactId
  queryFacts(pattern: Term)                          → List[Fact]
```

### 8.2 What Is NOT Needed at Stage 0

The following full-anthill capabilities are deferred:

- **Proof checking** (`verify(proof, obligation)`) — no proofs yet
- **Consistency checking** (`checkConsistency(delta)`) — no formal axioms to contradict
- **Unification / resolution** (`unify`, `resolve`) — no reasoning engine
- **Refinement checking** (`checkRefinement`) — no Unspecified terms being formalized
- **Trust composition** — trust is simple: `proposed` → `tested-N` → `verified`
- **Embedding / semantic search** — WorkItems are found by structured query, not similarity
- **Budget management** — deferred to later stages
- **Domain visibility** — all facts are project-wide at Stage 0

These capabilities are added incrementally as the project grows through stages.

## 9. Implementation Plan

### 9.1 The Anthill Ecosystem

The anthill is not a monolithic tool — it is a set of **cooperating tools sharing `anthill/` state**. All tools read and write the same `anthill/` files in the git repository. No tool is "primary" — they observe and modify the anthill independently. This IS stigmergy: the tools themselves follow the ant pattern.

```
                       anthill/  (git-committed, shared state)
                      ╱     │      ╲           ╲
                ╱           │           ╲            ╲
  Claude Code        anthill CLI      anthill-ui      anthill-spawn
  + /anthill skill   (validate,       (web dashboard, (watch & spawn
  (Layer 0)          accept,          dep graph,       agents in
                     verify, CI)      kanban board)    git worktrees)
  (Layer 1)                           (Layer 2)       (Layer 3)
```

The layers are additive — a project can start with Layer 0 alone (just the skill) and add layers as it grows:

| Layer | Tool | Purpose | When needed |
|---|---|---|---|
| **0** | Claude Code + `/anthill` skill | Single-developer workflow, direct file read/write | From day one |
| **1** | `anthill` CLI | Validation, CI hooks, scripting, non-LLM agents | When you need automation beyond Claude Code |
| **2** | `anthill-ui` | Web dashboard, interactive dependency graph, kanban | When ASCII isn't enough |
| **3** | `anthill-spawn` | Multi-agent coordination, git worktrees, merge | When parallel agents are needed |

All layers produce identical results — they implement the same state machine over the same files. The `.anthill` file format (defined in [standard-library.md](standard-library.md)) is the integration point.

### 9.2 Layer 0: Claude Code Integration

The most immediate way to use anthill. No binary to install — just a Claude Code skill and an optional CLAUDE.md.

**The `/anthill` skill** is a prompt template installed once (user-level). It teaches Claude Code the anthill file format, the WorkItem lifecycle state machine, and how to validate transitions. Invoked as:

```
/anthill status                -- kanban summary: N draft, N open, N claimed, N verified
/anthill next                  -- find next claimable task (Open, deps satisfied)
/anthill decompose "desc"      -- propose WorkItems, write .anthill.draft
/anthill feedback "comment"    -- attach Feedback to current Draft/Delivered, trigger revision
/anthill accept [feature]      -- review & accept .draft → .anthill, Draft → Open
/anthill reject "reason"       -- reject .draft → .rejected, Draft → ProposalRejected
/anthill claim WI-002          -- set Claimed, read context, start working
/anthill verify [WI-002]       -- run acceptance tools via Bash, update status
/anthill graph                 -- ASCII dependency graph in terminal
```

What the skill does on each command:

1. Reads `anthill/project.anthill` — project structure, tools, modules
2. Reads `anthill/workitems/*.anthill` (+ `.draft`, `.rejected`) — current state
3. Performs the requested action (list, decompose, transition, verify)
4. Validates consistency (suffix matches status, deps exist, no cycles)
5. Writes updated `.anthill` files

The skill runs acceptance checks by invoking tools via Bash — `sbt test`, `npm build`, etc. — and interprets results against `SuccessCriterion`.

**CLAUDE.md** provides project-specific context. Minimal — the skill handles the generic protocol:

```markdown
## Anthill

This project uses anthill for work decomposition.
Configuration: anthill/project.anthill
Use /anthill commands to interact.

Project conventions:
- WorkItem IDs: WI-CPS2-<feature>-NNN
- Acceptance must include scalafmt-check
- Decomposition granularity: one item per source file change
```

The split: skill = generic anthill agent behavior (reusable, installed once); CLAUDE.md = project-specific conventions (per-project, committed to git).

### 9.3 Layer 1: CLI Tool (`anthill`)

A standalone binary for validation, CI integration, and non-LLM workflows. Implements the same operations as the skill but with structured input/output:

```
anthill init                          -- initialize anthill/ in current directory
anthill project show                  -- display project configuration

-- Decomposition (see §5.1)
anthill decompose "description"       -- (LLM-assisted) propose WorkItems (status: Draft)
anthill decompose --from-file F.md    -- decompose from a document
anthill decompose --from-failure tool -- decompose from a failing tool run
anthill review <feature>              -- show Draft items, open in editor
anthill feedback <feature> "comment"  -- attach Feedback fact, trigger revision
anthill accept <feature>              -- transition Draft → Open, rename .draft → .anthill
anthill reject <feature> --reason "." -- transition Draft → ProposalRejected

-- WorkItem management
anthill workitem create               -- create a WorkItem manually
anthill workitem list [--status=open] -- list WorkItems, filtered by status
anthill workitem show WI-001          -- show details of a WorkItem
anthill workitem graph [--format=dot] -- dependency graph (ASCII, DOT, or JSON)

-- Execution loop (see §5.2)
anthill claim WI-001                  -- claim a WorkItem for the current agent
anthill deliver WI-001                -- mark a WorkItem as delivered
anthill verify WI-001                 -- run acceptance criteria for a WorkItem
anthill verify --all                  -- verify all Delivered items
anthill status                        -- summary: N open, N claimed, N verified, N rejected

-- Validation
anthill validate                      -- check consistency: suffixes, deps, cycles, references
anthill tool list                     -- list defined tools
anthill tool run sbt-test             -- run a tool directly
```

The CLI is the **validation layer** — it catches inconsistencies that natural language interaction might miss (dangling deps, status/suffix mismatch, cycle detection). CI pipelines use `anthill validate` and `anthill verify --all` as gates.

The CLI can also expose an **MCP server** for LLM agents that aren't Claude Code (or for multi-agent scenarios):

```
anthill mcp-server                    -- start MCP server on stdio
```

This exposes the same operations as MCP tools (`anthill_list_workitems`, `anthill_claim_workitem`, etc.), enabling any MCP-capable LLM to participate in the stigmergic loop.

### 9.4 Layer 2: Web UI (`anthill-ui`)

A local web server for visualization. Reads `anthill/` files, watches for filesystem changes, renders:

- **Dependency graph** — interactive, zoomable (D3 or similar)
- **Kanban board** — columns: Draft | Open | Claimed | Delivered | Verified | Rejected
- **Agent activity log** — who claimed what, when, results
- **Acceptance run results** — tool output, pass/fail, duration
- **Live updates** — watches `anthill/` for changes, auto-refreshes

```
anthill ui                            -- starts http://localhost:3000
anthill ui --port 8080                -- custom port
```

The UI is read-mostly — it may support drag-drop status changes (which write back to `.anthill` files), but the primary interaction remains through Claude Code or CLI.

For quick one-shot visualization without a persistent server, Claude Code can generate and open an HTML file:

```
/anthill graph --browser              -- generates anthill/graph.html, opens in browser
```

### 9.5 Layer 3: Agent Spawner (`anthill-spawn`)

A paired tool that watches the anthill for unclaimed work and spawns LLM agents in isolated git worktrees.

**Git worktrees as agent workspaces.** Each spawned agent works in its own git worktree — same repository, separate working directory, independent branch:

```
my-project/                           ← main worktree (human + Claude Code)
  .git/
  anthill/
  src/

../my-project-wi-002/                 ← agent A's worktree (spawned)
  anthill/                             ← own branch: work/wi-002
  src/

../my-project-wi-003/                 ← agent B's worktree (spawned)
  anthill/                             ← own branch: work/wi-003
  src/
```

This provides complete isolation — agents don't interfere with each other or with the developer's main worktree. Each agent commits to its own branch.

**Agent pool configuration:**

```
-- .anthill-spawn/pool.anthill (or similar config)

agent-pool:
  - type: claude-code
    model: claude-opus-4-6
    capabilities: [Code, Test, Decompose]
    max-concurrent: 3
  - type: claude-code
    model: claude-sonnet-4-5
    capabilities: [Code, Test]
    max-concurrent: 5
  - type: local-llm
    model: deepseek-coder
    capabilities: [Code]
    max-concurrent: 1
```

**The spawn loop:**

```
loop:
  state = read anthill/workitems/*.anthill from main branch
  claimable = items where status == Open
              AND all deps Verified
              AND not assigned to an active worktree

  for item in claimable:
    agent = pool.find(matching: item.requires_capability)
    if agent available:
      branch = "work/" + item.id
      worktree = git worktree add <path> -b <branch>
      session = spawn agent in worktree  -- e.g., claude-code with /anthill skill
      track(item.id, session, worktree, branch)

  for tracked in active:
    if tracked.session.finished:
      if tracked.succeeded:
        merge(tracked.branch → main)    -- may require review/approval
        rerun_acceptance_on_main()       -- post-merge re-verification
        cleanup(tracked.worktree)
      else:
        log_failure(tracked)
        cleanup(tracked.worktree)
```

**Merge strategy.** When an agent's branch merges back to main:

- Code changes merge normally via git
- `anthill/` status updates merge (item goes Open → Verified in one merge)
- Independent items in separate files — no conflict
- **Post-merge re-verification** is essential: the main branch may have changed since the agent branched. The spawner (or a CI hook) runs `anthill verify --all-delivered` on main after each merge

**Claim coordination.** The spawner prevents duplicate claims — it tracks which items are assigned to active worktrees. If two agents somehow claim the same item (race condition), the merge to main will conflict on the status field, providing natural detection.

### 9.6 Data Model

WorkItem, ToolDef, Project, and their associated types (ContextRef, AcceptanceCriterion, WorkStatus, SuccessCriterion, etc.) as host-language data structures mirroring the entity definitions in [standard-library.md §2](standard-library.md#2-the-standard-domain-anthillstage0). Implementation in Scala (primary) and/or Python.

### 9.7 Storage

Two options, both suitable for Stage 0:

**Option A: File-based (`anthill/` directory)**

Uses `.anthill` files with the sugar grammar defined in [standard-library.md §8](standard-library.md#8-grammar-of-the-sugar). See [standard-library.md §6](standard-library.md#6-file-organization) for directory structure.

Advantages: human-readable, git-friendly, easy to inspect and edit manually. Natural integration with git worktrees (each worktree has its own copy). Works well for small-to-medium projects.

**Option B: SQLite (`anthill/anthill.db`)**

Advantages: efficient querying, atomic transactions, handles large numbers of items. Better for projects with hundreds of WorkItems.

The implementation should support both, with file-based as default and SQLite as an option for larger projects. Note: SQLite is less natural for the git worktree model (binary file merges are problematic); file-based is strongly preferred for multi-agent scenarios.

### 9.8 Acceptance Runner

The acceptance runner is a shell executor for ToolDef. Used by all layers — the skill calls tools via Bash, the CLI invokes them as subprocesses, the spawner re-runs them post-merge:

```
function runTool(tool: ToolDef, params: Bindings): ToolResult =
  // Substitute $param placeholders in args
  resolvedArgs = tool.args.map(arg => substituteParams(arg, params))

  // Execute the command
  process = execute(
    command = tool.command,
    args = resolvedArgs,
    workingDir = tool.workingDir orElse project.root,
    timeout = tool.timeout
  )

  // Check success criterion
  success = tool.success match
    case ExitZero           => process.exitCode == 0
    case ExitCode(n)        => process.exitCode == n
    case OutputMatches(pat) => pat.matches(process.stdout + process.stderr)
    case Custom(check)      => kb.evaluate(check)

  return ToolResult(
    tool = tool.name,
    success = success,
    exitCode = process.exitCode,
    stdout = process.stdout,
    stderr = process.stderr,
    duration = process.duration
  )
```

## 10. Summary

Stage 0 is where the anthill begins. It provides:

1. **Immediate value** — structured work decomposition, parallel execution, machine-checkable acceptance
2. **Zero formalization overhead** — no proofs, no domain axioms, no formal logic required
3. **Natural growth path** — every Stage 0 construct evolves into its full anthill counterpart
4. **Agent-agnostic** — humans, LLMs, and automated tools all interact through the same `.anthill` files
5. **Stigmergic** — no orchestrator; the WorkItem list IS the work queue; the dependency graph IS the coordination mechanism
6. **Ecosystem of paired tools** — skill, CLI, web UI, spawner share `anthill/` state; add layers as the project grows

Start with `/anthill decompose`. Review and accept. Let agents work — in the main worktree or in spawned worktrees. Verify automatically. The anthill grows from here.
