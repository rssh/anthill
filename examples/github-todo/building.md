# Building github-todo with Anthill

This document describes how to use anthill for the github-todo example — work item management with dependency tracking, acceptance verification, and optional GitHub sync.

## 1. Architecture: Two Separate Things

### The `anthill` CLI (the tool)

The `anthill` CLI is compiled from the anthill source code (`rustland/anthill-core`, `rustland/anthill-cli`). It is a generic tool — like `git` — that operates on any project's anthill data. It provides:

- KB loading (parse `.anthill` files + stdlib → knowledge base)
- SLD resolution (backward chaining through rules)
- Acceptance runner (execute ToolDef shell commands, check SuccessCriterion)
- Status transitions (assert new facts with meta.supersedes)
- Persistence (read/write `.anthill` files via FileStore)
- Query interface (resolve goals, print results)

The CLI is installed once. It contains no application-specific code.

### Project data (the facts)

`.anthill` files live **in the target project's repository**. They contain facts, rules, and domain definitions specific to that project. For github-todo, these files live in an `anthill-todo/` directory:

```
my-project/                           ← the user's project repository
  src/                                ← project source code (Rust, Scala, etc.)
  tests/
  anthill-todo/                       ← anthill data for this project
    project.anthill                   ← project configuration fact
    domain.anthill                    ← entity types
    rules.anthill                     ← workflow rules (claimable, blocked, ...)
    tools.anthill                     ← tool definition facts
    workitems/
      auth.anthill                    ← work item facts
      auth.feedback.anthill           ← feedback facts
```

These are **project data**, not anthill source code. They are committed to git, reviewed, and edited by developers and agents. They live in a regular visible directory — not hidden.

## 2. How It Works

The `anthill` CLI operates on the project data:

```
anthill -p anthill-todo/ status                        -- summary by status
anthill -p anthill-todo/ query "claimable(?id, ?desc)" -- find claimable items
anthill -p anthill-todo/ verify WI-AUTH-001             -- run acceptance criteria
anthill -p anthill-todo/ claim WI-AUTH-001              -- transition to Claimed
anthill -p anthill-todo/ next                           -- find next claimable item
anthill -p anthill-todo/ graph                          -- print dependency DAG
anthill -p anthill-todo/ feedback WI-AUTH-002 "use jsonwebtoken crate"
```

Each command:

```
1. Load stdlib (shipped with the CLI binary)
2. Load anthill-todo/*.anthill files into KB
   → domain.anthill defines entity types
   → project.anthill, tools.anthill, workitems/*.anthill provide facts
   → rules.anthill provides workflow rules
3. Execute the command (query, mutate, verify, ...)
4. Persist changes back to .anthill files
```

No Rust code is written by the project developer. The `.anthill` files define *what* (the knowledge); the CLI provides *how* (the runtime).

### What the CLI does internally

| Command | KB Operation | Side Effect |
|---------|-------------|-------------|
| `status` | Count facts by WorkStatus functor | Print summary |
| `next` | `resolve(claimable(?id, ?desc))` | Print next claimable item |
| `list [--status Open]` | `resolve(open_item(?id, ?desc))` | Print table |
| `show <id>` | `query(WorkItem(id: "<id>"))` | Print details + feedback |
| `graph` | Walk all WorkItem facts, extract depends_on | Print ASCII DAG |
| `claim <id>` | Assert WorkItem with status: Claimed | Persist to .anthill file |
| `deliver <id>` | Assert WorkItem with status: Delivered | Persist to .anthill file |
| `verify <id>` | Read acceptance criteria, run tools, assert Verified/Rejected | Execute shell commands |
| `feedback <id> "text"` | Assert Feedback fact | Persist to .feedback.anthill |

### How resolution works

The rules in `rules.anthill` drive backward chaining:

```anthill
rule claimable(?id, ?desc)
  :- WorkItem(id: ?id, status: Open, description: ?d),
     description_view(?d, ?desc),
     all_deps_verified(?id)
```

When the CLI runs `query "claimable(?id, ?desc)"`:

1. Parse the query string → KB term with variables
2. `kb.resolve([goal], config)` — SLD resolution
3. Resolution matches `claimable` rule head → proves body goals:
   - `WorkItem(id: ?id, status: Open, description: ?d)` — partial entity expansion fills the pattern's missing fields with `?`, then pattern-matches against WorkItem facts. (The fill is position-dependent since WI-716: a *pattern's* missing field is a wildcard, but a *fact's* missing optional field is stored as `none()` — which is why `description_view` and the `depends_on: none()` rule exist, WI-717.)
   - `description_view(?d, ?desc)` — unwraps a present description (`some(?desc)`); an omitted one surfaces as `none` so the item is still listed
   - `all_deps_verified(?id)` — recursively walks dependency list through more rules
4. Each successful proof yields a `Solution` with variable bindings
5. CLI prints bound values via `TermPrinter`

### How acceptance works

`verify <id>` reads the `acceptance` field from the WorkItem fact, then for each `AcceptanceCriterion`:

- **`ToolPasses(tool, params)`** — look up `ToolDef` fact by name, substitute `$param` placeholders in args, execute shell command, check `SuccessCriterion` (ExitZero, ExitCode, OutputMatches)
- **`Compiles(source)`** — infer compiler tool from project's `build` field, execute
- **`FactHolds(domain, pattern)`** — query KB for matching fact
- **`Constraint(term)`** — evaluate term

All criteria must pass for `Verified`; any failure yields `Rejected` with diagnostics.

## 3. Persistence: The Directory as a Store

The persistence layer (see [proposal 007](../../docs/proposals/007-persistence-layer.md)) treats the `anthill-todo/` directory as a **backing store** for the KB.

### The `stage0` file convention

The `FileStore` with `stage0` convention maps fact sorts to directory structure:

```
anthill-todo/
  project.anthill                     ← Project(...) fact
  tools/
    custom-tools.anthill              ← ToolDef(...) facts
  workitems/
    auth.anthill                      ← WorkItem(...) facts (Open/Claimed/Verified/...)
    auth.anthill.draft                ← WorkItem(..., status: Draft) facts
    auth.feedback.anthill             ← Feedback(...) facts
    auth.anthill.rejected             ← WorkItem(..., status: ProposalRejected) facts
  facts/
    verified.anthill                  ← facts generated by Verified work items
```

File suffixes reflect status (`.draft`, `.rejected`). The directory is loaded as a `bulk` store at startup (`pull()` reads all files into KB). Mutations are written back via `persist()` + `flush()`.

As the project grows, the file store could evolve to `queryable` — translating patterns to glob lookups (e.g., `WorkItem(id: "WI-AUTH-001")` → read `anthill-todo/workitems/WI-AUTH-001.anthill`) instead of loading everything into memory. The architecture supports this without changing the data files — only the `caps()` rule changes.

### Bootstrap sequence

```
1. Read anthill-todo/project.anthill       (bootstrap path, from -p flag)
   → Parse project config, store declarations, routing rules

2. For each declared bulk store:
   → pull(store): load all .anthill files into KB
   (For github-todo: FileStore loads workitems/, tools/, feedback)

3. For each declared queryable store:
   → Register as external oracle in the reasoning engine
   (For github-todo: none — everything is file-based)

4. KB is ready. Resolution can backward-chain through:
   - In-memory facts from bulk stores
   - On-demand queries to queryable stores
```

### Routing configuration

```anthill
namespace my-github-app
  import anthill.persistence
  import anthill.persistence.filesystem

  -- Bootstrap store: the anthill-todo/ directory
  fact bootstrap(FileStore(root: "anthill-todo", convention: stage0))

  -- Routing: all Stage 0 facts go to the file store
  rule route(WorkItem(?))  = FileStore("anthill-todo", stage0)
  rule route(Project(?))   = FileStore("anthill-todo", stage0)
  rule route(Feedback(?))  = FileStore("anthill-todo", stage0)
  rule route(ToolDef(?))   = FileStore("anthill-todo", stage0)
  rule route(?)            = FileStore("anthill-todo", stage0)
end
```

## 4. Extending with Custom Rust Code (optional)

When the generic CLI isn't enough — e.g., GitHub API sync, custom web UI, domain-specific acceptance logic — the project can build a custom Rust binary that depends on `anthill-core` as a library.

The `.anthill` data files stay the same. The Rust code adds application-specific side effects on top of the same KB.

```toml
[package]
name = "github-todo-extended"

[dependencies]
anthill-core = { path = "path/to/anthill/rustland/anthill-core" }
```

### Rust API for KB interaction

**Load:**
```rust
use anthill_core::kb::{KnowledgeBase, load};
use anthill_core::parse;

let mut kb = KnowledgeBase::new();
load::register_prelude(&mut kb);
// parse and load stdlib + project .anthill files
load::load_all(&mut kb, &parsed_refs, &load::NullResolver)?;
kb.resolve_builtins();
```

**Query:**
```rust
use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::term::{Term, TermId, VarId};

// Build goal: claimable(?id, ?desc)
let claimable_sym = kb.resolve_symbol("claimable");
let id_var = kb.fresh_var(kb.intern("id"));
let desc_var = kb.fresh_var(kb.intern("desc"));
let v_id = kb.alloc(Term::Var(id_var));
let v_desc = kb.alloc(Term::Var(desc_var));
let goal = kb.alloc(Term::Fn {
    functor: claimable_sym,
    pos_args: SmallVec::from_slice(&[v_id, v_desc]),
    named_args: SmallVec::new(),
});
let solutions = kb.resolve(&[goal], &ResolveConfig::default());
```

**Query from string:**
```rust
use anthill_core::kb::load::convert_query_term;

let source = format!("fact {query_str}");
let parsed = parse::parse(&source)?;
let parse_term_id = parsed.items[0].as_fact().unwrap().term;
let mut var_map = HashMap::new();
let goal = convert_query_term(
    &mut kb, &parsed.terms, &parsed.symbols,
    parse_term_id, 0, &mut var_map,
);
let solutions = kb.resolve(&[goal], &ResolveConfig::default());
```

**Mutate and persist:**
```rust
use anthill_core::persistence::file_store::{FileStore, FileConvention};

kb.assert_fact(new_wi_term, sort, domain, Some(meta));
store.persist(&kb, new_wi_term, sort, domain, meta)?;
store.flush(&kb)?;
```

### Example: GitHub sync

```rust
fn sync_to_github(kb: &KnowledgeBase, github: &GitHubClient, repo: &str) {
    let work_items = query_all_work_items(kb);
    for wi in work_items {
        let id = extract_string(kb, wi, "id");
        let desc = extract_string(kb, wi, "description");
        let status = extract_named(kb, wi, "status");
        let labels = status_to_labels(kb, status);
        match github.find_issue_by_title(repo, &id) {
            Some(issue) => github.update_issue(repo, issue.number, labels),
            None => github.create_issue(repo, &id, &desc, labels),
        }
    }
}
```

## 5. What Anthill-Core Needs to Provide

Existing facilities marked with [done], gaps marked with [needed].

### 5.1 Load Pipeline

| Facility | Status |
|----------|--------|
| `parse::parse(source) -> Result<ParsedFile>` | [done] |
| `load::register_prelude(kb)` | [done] |
| `load::load_all(kb, files, resolver)` | [done] |
| `kb.resolve_builtins()` | [done] |
| Sugar desugaring (project, tool, workitem, feedback → Fact) | [done] |
| Stdlib loading from filesystem | [done] |
| Stdlib shipped as `include_str!()` (no filesystem dependency) | [needed] — library users need embedded stdlib |

### 5.2 Query & Resolution

| Facility | Status |
|----------|--------|
| `kb.query(pattern)` — pattern matching over facts | [done] |
| `kb.resolve(goals, config)` — full SLD resolution | [done] |
| `kb.resolve_lazy(goals, config)` — lazy/streaming resolution | [done] |
| `convert_query_term(kb, ...)` — parse-time term → KB term | [done] |
| Partial entity expansion (missing fields → `?`) | [done] |
| Negation-as-failure (`not(goal)`) | [done] |
| Arithmetic/comparison builtins | [done] |
| High-level `query_from_string(kb, "claimable(?id, ?desc)")` | [needed] — convenience wrapper |

### 5.3 Term Construction & Inspection

| Facility | Status |
|----------|--------|
| `kb.alloc(Term::Fn { ... })` — low-level | [done] |
| `kb.intern(name)`, `kb.fresh_var(name)` | [done] |
| `kb.get_term(id)`, `kb.resolve_sym(sym)` | [done] |
| `TermPrinter::print_term(id)` | [done] |
| `kb.build_fn(functor, named_args)` — ergonomic construction | [needed] |
| `kb.extract_field(term, "status")` — named arg lookup | [needed] |
| `kb.list_to_vec(term)` — cons/nil → Vec | [needed] |

### 5.4 Mutation

| Facility | Status |
|----------|--------|
| `kb.assert_fact(term, sort, domain, meta)` | [done] |
| `kb.retract(rule_id)` | [done] |
| Fact supersession (query latest, skip superseded) | [needed] |

### 5.5 Persistence (see [proposal 007](../../docs/proposals/007-persistence-layer.md))

| Facility | Status |
|----------|--------|
| `Store::persist / flush` | [done] |
| `BulkStore::pull` | [done] |
| `FileStore` (Flat, ByDomain conventions) | [done] |
| `FileConvention::Stage0` (workitems/ dir, status-based suffixes) | [needed] |
| Routing rules (sort → store dispatch) | [needed] |
| Bootstrap sequence (load project.anthill first, then pull) | [needed] |
| Round-trip: load → mutate → persist → reload | [done] |

### 5.6 CLI

| Facility | Status |
|----------|--------|
| `anthill` binary with `-p <path>` | [needed] |
| `query`, `status`, `next`, `list`, `show` commands | [needed] |
| `claim`, `deliver`, `verify`, `feedback` commands | [needed] |
| Acceptance runner (ToolDef execution) | [needed] |
| `graph` (dependency DAG visualization) | [needed] |

## 6. Build Plan

### Phase 1: Prove the pipeline

Integration test: load `stdlib/ + examples/github-todo/*.anthill` → `resolve(claimable(?id, ?desc))`. Validates: grammar → parse → sugar → load → entity expansion → SLD resolution.

### Phase 2: CLI skeleton

The `anthill` binary with `query` and `status` commands. Enough to run `anthill -p anthill-todo/ query "claimable(?id, ?desc)"` and get results.

### Phase 3: CLI workflow commands

`claim`, `deliver`, `verify`, `feedback`. Acceptance runner. Persistence via `FileStore` with `stage0` convention.

### Phase 4: Self-hosting

Use anthill-todo on anthill's own development — the project manages its own work items via the tool it builds.
