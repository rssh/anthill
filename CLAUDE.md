# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is Anthill

A kernel language and knowledge base system for formal specification and reasoning. Four core constructs: `namespace`, `sort`, `rule`, `operation`. We can use logical variables in types as in logical terms (types unify — substitution, occurs-check); sort relations are facts. SLD resolution with discrimination tree indexing.

> **Representation note (not "types are terms").** The old "types are terms" mantra was too abstract and invited a false conclusion — that types must be hash-consed `TermId`s. They need not be. Hash-consing is a storage *optimization* (O(1) structural equality, dedup, shared-subterm memory) that pays off for **persistent, heavily-shared structure** — asserted facts, rule heads, nominal sort identities. It is **not implied by type-hood**, and notably **not required by being indexed/searched**: the discrimination tree keys on purely structural `DiscrimKey`s, never on `TermId` identity, so a non-hash-consed carrier (a `Value::Node`/`Entity`, a transient query pattern) indexes and matches identically. It is specifically **inappropriate for binders** (arrow / dependent types), whose scope and alpha-equivalence don't fit a global dedup store. The genuinely load-bearing claim is only that types carry logical variables and unify.

Specification: `docs/kernel-language.md` — canonical language spec (should be kept in sync with implementation).

Design proposals: `docs/proposals/` (numbered 001–024+) — language extensions and design decisions.

## Project Layout

```
rustland/               Rust implementation (primary, most complete)
scaland/                Scala 3 implementation (parallel port, uses fastparse)
tree-sitter-anthill/    Tree-sitter grammar (grammar.js + Rust/Node bindings, used by rustland)
stdlib/anthill/         Standard library .anthill files (prelude, reflect, realization, persistence)
examples/github-todo/   Example project: work-item tracking with domain, rules, tools
anthill-todo/           Work-item .anthill files for this project's own task tracking
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
sbt test
sbt compile
```

### Tree-sitter Grammar (`tree-sitter-anthill/`)

```bash
cd tree-sitter-anthill
npx tree-sitter generate   # regenerate parser from grammar.js
npx tree-sitter test       # run grammar corpus tests
```

## Example and Skill

- `examples/github-todo/` — complete example: domain entities, work items, rules, tools, feedback. Used by integration tests (`github_todo_test.rs`).
- `/todo` skill (`.claude/skills/todo/SKILL.md`) — manages work items via `anthill-todo` CLI. Build: `cd rustland && cargo build -p anthill-todo`. Run from project root.

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

**Cross-file mutual recursion is supported** (WI-321): pass 1 defines every name
across every file before any pass 2 runs, so two files whose sorts reference each
other both load. This ordering is load-bearing — see the `scan_definitions`
invariant comment and `wi321_cross_file_mutual_recursion_test`.

### Key Concepts

- **Hash-consing (selective, not universal)**: persistent, heavily-shared structure (asserted facts, rule heads, sort identities) is interned in `TermStore` so structurally-identical terms share one `TermId` — but interned terms live for the KB's lifetime, so transient terms (query patterns, occurrence-derived twins) are deliberately NOT interned; they ride as `Value::Node`/`Entity` carriers and match structurally. See the Representation note at the top of this file.
- **Symbol table**: string interning (`Symbol(u32)`), scope-aware two-phase resolution (Unresolved → Resolved)
- **De Bruijn variables**: rules stored with `DeBruijn(u32)`, opened to fresh globals during resolution
- **Discrimination tree**: structural term matching index for fast rule/fact lookup
- **SLD resolution**: depth-first search with negation-as-failure, delay/rotation for unbound vars
- **Facts are rules**: a fact is a rule with empty body; constraints are integrity guards
- **Named args**: canonicalized to a stable order so a record hash-conses and
  discrim-matches regardless of source order — by DECLARED field order when the
  functor has a field schema, else by interning order
  (`canonicalize_record_named_args`, `kb/resolve.rs`). **Not** alphabetical, and
  **not** universal: it returns early for an ORDERED PRODUCT (a named tuple),
  whose source order IS its identity. Load-bearing — a named tuple's components
  are read positionally in source order (see `match_tuple_pattern`), so
  canonicalizing one would silently re-bind destructured components.

# Repository rules

- before commit, check - if all test passed. Also run the `/code-review` skill (formerly called "simplicity"); remind if it was not run.
- do not add attribution to commit.
- when running rust test, use script which allows monitoring:  rustland/scripts/test.sh 

# Development principles
 - avoid fallbacks, better know about errors early.
 - prefer a loud error over a silent skip: when a case can't be handled — a not-yet-supported / gated path, an unexpected value carrier, a missing field — surface it as an explicit error or diagnostic rather than silently `continue`/dropping it. Silent skips hide bugs and read as "handled" when they aren't.
