# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is Anthill

A kernel language and knowledge base system for formal specification and reasoning. Four core constructs: `namespace`, `sort`, `rule`, `operation`. We can use logical variables in types as in logical terms (types unify — substitution, occurs-check); sort relations are facts. SLD resolution with discrimination tree indexing.

Specification: `docs/kernel-language.md` — canonical language spec (should be kept in sync with implementation). If you need to change specification - discuss this with user at first.

Design proposals: `docs/proposals/` (numbered 001–024+) — language extensions and design decisions.

## Project Layout

```
rustland/               Rust implementation (primary, most complete)
scaland/                Scala 3 implementation (parallel port, uses fastparse)
tree-sitter-anthill/    Tree-sitter grammar (grammar.js + Rust/Node bindings, used by rustland)
stdlib/anthill/         Standard library .anthill files (prelude, reflect, realization, persistence)
examples/github-todo/   Example project: work-item tracking with domain, rules, tools
anthill-todo/           This project's own work items: one `WI-….anthill.md` DOCUMENT
                        per item (an `## Attributes` chapter of one line per field,
                        then prose chapters), under a directory per status. Format:
                        `rustland/anthill-todo/docs/design/document-mapping.md`.
docs/                   Kernel language spec, stage0 design docs, proposals
```

## Implementations

### Rust (`rustland/`)

Primary implementation. Cargo workspace with crates: `anthill-core` (parser, KB, resolution, codegen), `anthill-cli`, `anthill-stl`, `anthill-todo`. Uses tree-sitter for parsing.

See `rustland/CLAUDE.md` for Rust-specific build commands, architecture, and conventions.

### Scala (`scaland/`)

Parallel implementation in Scala 3 (sbt build, fastparse). Mirrors the Rust architecture: `term`, `intern`, `parse`, `load`, `kb`, `resolve`, `subst`, `discrim`, `span`.

```bash
cd scaland
sbt testFull
sbt compile
```

**`testFull`, NOT `test`** (sbt 2). sbt 2's `test` is INCREMENTAL — it runs only
what the last change affected, and prints `No tests to run` when nothing did. An
acceptance that says "scaland green" and runs `test` can therefore pass having run
NOTHING, which is the one thing an acceptance must not do. `testFull` is sbt 2's
"executes all tests".

sbt 2 also keeps a background SERVER between invocations. If the build state changes
underneath it — a version bump, an external `clean` — a later `sbt -batch …` can answer
from the stale one and report `Total 0 … [success]`. MEASURED during the migration.
`sbt shutdown` first when a run reports fewer tests than it should.

### Tree-sitter Grammar (`tree-sitter-anthill/`)

```bash
cd tree-sitter-anthill
npx tree-sitter generate   # regenerate parser from grammar.js
npx tree-sitter test       # run grammar corpus tests
```

## Example and Skill

- `examples/github-todo/` — complete example: domain entities, work items, rules, tools, feedback. Used by integration tests (`github_todo_test.rs`).
- `/anthill-todo` skill (`skills/anthill-todo/SKILL.md`) — manages work items via the `anthill-todo` CLI. Build: `cd rustland && cargo build -p anthill-todo`. Run from project root. Skills live in the top-level `skills/`; there is no `.claude/skills/`.

## Anthill Language Syntax

```anthill
namespace anthill.example
  import anthill.prelude.{List, Option}
  export MySort

  sort MySort
    entity Variant1(field: Int)
    entity Variant2(name: String, value: Option[T = Int])
  end

  rule derived_fact(?x, ?y)
    :- Variant1(field: ?x), Variant2(name: ?y, value: some(?x))

  fact Variant1(field: 42)

  constraint unique_name
    :- Variant2(name: ?n, value: ?), Variant2(name: ?n, value: ?)
end
```

Variables: `?name` (named, shared within scope), `?` (anonymous, each occurrence distinct).

## Architecture (shared across implementations)

### Pipeline

```
.anthill source → parse (tree-sitter or fastparse) → ParsedFile (typed IR)
  → scan_definitions (4-pass: 1 define all names, 2 requires/imports,
                      3 rule-head Goals, 4 deferred predicate imports)
  → load → KnowledgeBase
```

**The standard library is its own load, SEALED, and a program is a later one**
(WI-20261009-AN6CQ; `load::load_program`, `docs/kernel-language.md` §8.3). The CLI,
anthill-todo and a generated bundle hand the loader the stdlib with its host bindings
FIRST, seal that load, and load the program's files in a second `load_all`. What a
program is held to by it: it may not supply the equality of a composite the stdlib
defines (`List`, `Option`, …) — it wraps the value in a sort of its own; it may not
declare a stdlib operation or type again; and it may not reach into a stdlib body, with
a `@[simp]` rule that rewrites one or a provision at stdlib types that changes who
answers a dispatch there. `load_all` over everything in one call is still how the
library's own files are loaded — `anthill … --no-stdlib <the library's directories>`.

**Cross-file mutual recursion is supported** (WI-321): pass 1 defines every name
across every file before any pass 2 runs, so two files whose sorts reference each
other both load. This ordering is load-bearing — see the `scan_definitions`
invariant comment and `wi321_cross_file_mutual_recursion_test`.

### Key Concepts

- **De Bruijn variables**: rules stored with `DeBruijn(u32)`, opened to fresh globals during resolution
- **Discrimination tree**: structural term matching index for fast rule/fact lookup
- **SLD resolution**: depth-first search with negation-as-failure, delay/rotation for unbound vars
- **Facts are rules**: a fact is a rule with empty body; constraints are integrity guards
- **`@[simp]` is the enablement, `<=>` is the admission** (WI-881/884/888) — an untagged equational rule is INERT; only the `@[simp]` tag makes a body-less operation's defining equation run (inlining LHS→RHS before dispatch — NOT spec-op backing, WI-818). A `@[simp]` head is an APPLICATION, and since WI-20260902-CZJ2N a BARE nullary head IS one — `rule tau <=> …` defines exactly as `rule tau() <=> …` does (the two are one term). The bare CALL SITE in an operation body is still not a redex; that reading is type-directed (§5.4) and is a separate ticket. The CONNECTIVE decides only whether the rule LOADS: `<=>` is the sole spelling admitted at a bodyless head and an `=` one is a load error (a GUARDED `lhs = rhs :- g` keeps `=`), while the tag alone decides whether it FIRES. Rule + traps: `docs/kernel-language.md` §5.3.

> **Localized invariants — not restated here.** Many subtle, silent-failure rules — label distinctness (tuple / entity / named-arg), distributive projections, tuple identity vs `<:`, requirement-dictionary layout, per-carrier host-op keying, cpp host templates — are each stated in `docs/kernel-language.md` and enforced by a doc-commented site (grep the rule name). When a change loads clean but behaves wrong, read the spec § and the enforcement-site comment before assuming the bug is new. History: WI-762/788/803/804/805/808/809/857/858/876/886.


# Repository rules

- before commit, when it is not documentation-only: check - if all test passed. Also run the `/code-review` skill (formerly called "simplify"); remind if it was not run.
- do not add attribution to commit.
- when running rust test, use script which allows monitoring:  rustland/scripts/test.sh 

# Development principles
 - avoid fallbacks, better know about errors early.
 - prefer a loud error over a silent skip: when a case can't be handled — a not-yet-supported / gated path, an unexpected value carrier, a missing field — surface it as an explicit error or diagnostic rather than silently `continue`/dropping it. Silent skips hide bugs and read as "handled" when they aren't.
 - prefer make illegal state unrpepresentable over check logic of the potentially incorrect state.
 - a test for a capability must DRIVE the capability: resolve the goal, call the operation, assert the value. "It loads clean" is not evidence that anything works — a test that only asserts a declaration loaded keeps passing when the name it uses resolves to nothing, and a suite of them stays green through a silent regression.
 - assert the CONTROL too: a test that passes both with and without the change measures nothing. Say at its site which tests fail when the change is backed out, and which pass either way by design.
 - full workspace test is expensive (more than 60 minutes on cloud), but necessory to catch regressions. So, make back-out measurement with local testset with temporary small binary and then add testset to full workflow.

# Work with anthill-todo
 - Prefer implement changes after review immediatly instead firing follow-ups tickets. Fire follow-up only if it is a big task, which can't be implemented inline.
 - If the size of code in change less then tocket description -- not open new ticket, make inline.
 - Monitor the number of open unblocked tickets in queue
 - Ask when you want to file a ticket. Never open a ticket without discussion.
