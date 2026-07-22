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
  whose component order is part of its TYPE IDENTITY (WI-788) — `(a: Int64, b:
  String)` differs from `(b: String, a: Int64)` (order) and from `(Int64, String)`
  (names). IDENTITY and `<:` ARE DIFFERENT RELATIONS: subtyping is fully
  name-keyed, so BOTH width (dropped from anywhere) and PERMUTATION hold
  (WI-804, WI-803). Do not carry the order rule across from identity into `<:` —
  that mistake refused correct programs. Order still binds where position is what
  is read: an arrow's PARAMETER LIST and UNIFICATION (`TupleAlign`'s three
  disciplines, `kb/typing.rs`). Canonicalizing a tuple's components would change
  its identity, hence the exemption. See `docs/kernel-language.md` §4.5.
- **A tuple's component labels are DISTINCT** (WI-805), refused at each of the THREE
  producers that key a tuple on labels the author WROTE: the literal and the tuple
  TYPE (`check_label_unique`, `parse/convert.rs`), and a `...rest: R` VARIADIC
  CAPTURE's leftover named args (`normalize_variadic_capture`, `kb/typing.rs`) —
  whose labels are written as call arguments and only become a tuple in the typer, so
  the parse guard cannot see them. Same rule the projection `x.(a, a)` and a call's
  named args already had; DERIVED schemas (`Concat`/`Project`) guard themselves.
  Every reader takes a name's FIRST match, so a repeated label leaves a component
  reachable by neither its name nor its position, with its declared type never
  checked — `(a: 1, b: 2, a: 3)` conformed to `(b: Int64, a: Int64)` on a clean load.
  Making the readers AGREE (WI-803) does not fix this: agreeing which component to
  read leaves the unread one unread. "Literal + type" felt exhaustive and was not —
  enumerate `named_tuple_value`'s callers before believing a producer list. NOT
  applied to an arrow's PARAMETER LIST: a repeated binder name there DOES shadow (the
  body reads the LAST one), but params are applied positionally so the shadowed one's
  type is still checked at every call — nothing is silently unchecked.
- **A named-argument list may not REPEAT A LABEL** (WI-809), for ANY callee — operation,
  entity constructor, function value, `fact`, rule-body atom — checked at
  `push_fn_term` + `push_dot_method_call` (two producers; the dot-call one is easy to miss).
  Done as SYNTAX because repetition within one list needs no type info, so one rule
  covers every callee. `mk(a: 1, a: 2)` on `entity mk(a: Int64, b: Int64)` built two
  `a` fields and NO `b`, failing only at run time. Still SEMANTIC in
  `named_arg_coverage_errors`, since neither is decidable from the list alone: an
  UNKNOWN label, and one re-binding a parameter already filled POSITIONALLY
  (`f(3, acc: 10)`). `normalize_variadic_capture`'s duplicate check is kept as the
  backstop for occurrences a MACRO synthesizes without passing through the parser.
- **An entity's field names are DISTINCT too** (WI-808), refused at `convert_entity`
  through the same owner (`check_label_unique`, which takes a per-kind rationale).
  NARROWER HARM than the tuple rule, and the comment says so: an entity's duplicate
  field is still built and read POSITIONALLY (`mk(1, 2)`, `case mk(p, q)`), so its
  type IS checked — what it loses is its ACCESS PATH, since `x.f` / named args / rule
  patterns all take the FIRST match. Refused because a field name is the field's
  public interface. Field names are scoped PER ENTITY — sibling entities in one sort
  may each declare `a`, which is the ordinary variant shape.
- **Destructuring binds by LABEL** (WI-803): the typer records which component
  name each binder takes into `Pattern::Tuple.labels`, and `match_tuple_pattern`
  fetches by name via `TupleComponents::by_label` — the same reader `t.x` uses.
  Reading by SLOT is what made a permuted value bind a component the typer typed
  from a different field (WI-788). A POSITIONAL carrier has no names, so it still
  reads by slot; that is exact, not a fallback, and it is how a spread call
  (`f(3, 10)`) arrives.

# Repository rules

- before commit, check - if all test passed. Also run the `/code-review` skill (formerly called "simplicity"); remind if it was not run.
- do not add attribution to commit.
- when running rust test, use script which allows monitoring:  rustland/scripts/test.sh 

# Development principles
 - avoid fallbacks, better know about errors early.
 - prefer a loud error over a silent skip: when a case can't be handled — a not-yet-supported / gated path, an unexpected value carrier, a missing field — surface it as an explicit error or diagnostic rather than silently `continue`/dropping it. Silent skips hide bugs and read as "handled" when they aren't.
