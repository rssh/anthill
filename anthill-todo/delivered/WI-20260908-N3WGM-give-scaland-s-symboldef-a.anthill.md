## Attributes

- id: WI-20260908-N3WGM-give-scaland-s-symboldef-a
- created: 2026-09-08T11:16:53Z

- status: Delivered
- status_agent: codex
- status_at: 2026-10-16T07:15:01Z

- acceptance: scaland-sbt-test

## Description

GIVE SCALAND'S `SymbolDef` A KIND SET, AND RETIRE `DeclarePredicatePass`.

rustland's `SymbolDef::Resolved` carries `kinds: SmallVec<[SymbolKind; 2]>` with
`add_kind` / `kinds()`, so a repeated `(name, scope)` ACCUMULATES roles. scaland's carries
a single `kind: SymbolKind` and `SymbolTable.define` returns the existing symbol on a
repeat, keeping whichever kind got there FIRST. There is no `addKind` / `hasKind` anywhere
in `scaland/core/src` (verified).

WHAT THAT COSTS TODAY, measured under WI-20260821-SBZ2A: proposal 061 mints a body-less
rule's predicate, and minting it INSIDE pass 1 — where rustland does — let the TEXT ORDER
decide the kind. `operation has(x) -> Bool` beside `rule has(?x)` was REFUSED with the
operation written first and LOADED CLEAN with the rule written first, stamping `has` a
`Goal` and silently swallowing the no-op line. SBZ2A closed it by deferring every
declaration into its own walk (`Loader.DeclarePredicatePass`, pass 1b, after pass 1 and
before pass 2) — the WI-321 invariant restored for that one kind by ORDERING rather than
by the mechanism rustland uses. With a kind set, pass 1b folds back into pass 1 and the
two loaders have one pass structure again.

IT IS NOT ONLY THE DECLARATION MINT. scaland records a name's other roles in SEPARATE
registries, one role each — `SortKind` per sort TERM (`registerSort`),
`constructorSymbols_`, `entityParent_` — and `KnowledgeBase.hasTypeReading` reads only
`SymbolKind.Sort`. So a FREE-STANDING `entity E(…)` (§6.3 sugar for `sort E { entity E(…) }`)
is `SymbolKind.Entity` plus a `SortKind.Constructor` registration and has NO type reading,
while the long form's `E` is a `Sort`. WI-940 pins the two spellings byte-equal in
Bootstrap's emission; whether they are the same at the SYMBOL is a question this ticket
should answer rather than inherit. WI-20260902-CZJ2N's note at `KnowledgeBase.alloc`
already names "a namespace-level ENTITY" as one of the five kinds it had to split.

THE COST IS THE READERS. ~20 sites pattern-match `SymbolDef.Resolved(_, _, kind, _)` by
name across `kb`, `resolve`, `load`, `codegen` and the tests, and rustland's own field doc
records the same hazard on its side: several of its readers "compare it to a single kind",
each correct only where the EXCLUSIVE reading is intended, and it says only a
site-by-site judgement can tell which was meant. Expect the same audit here — an
`exclusive kind` accessor beside `kinds` is likely, not a blanket sweep.

ACCEPTANCE: drive it. `operation has(…)` beside `rule has(?x)` must be refused in BOTH
text orders WITH the mint back inside pass 1 (that pair is
`RuleHeadDeclarationTest`'s "a declaration of a name another construct owns is refused",
which today measures pass 1b's ordering instead). `DeclarePredicatePass` deleted, its
`walkScopes` call with it. Every reader that narrowed to one kind must say at its site
which reading it takes. State which rows fail when the merge is backed out. sbt test green.


### Implementation

N3WGM implemented in scaland. `SymbolDef.Resolved` carries an ordered, duplicate-free
kind collection; `SymbolTable.define` accumulates roles on the same identity and
`addKind` records an additional role explicitly. `hasKind` / `kindsSet` are semantic
membership readers, `exclusiveKind` requires a singleton, and `primaryKind` preserves
the first declaration's keyword for reflection display only.

`DeclarePredicatePass` and both scope walks are removed. Plain predicate declarations
mint inside `DefinePass`; `defineSymbolOnce` now permits same-local role merges while
preserving the qualified-name collision gate. Declaration refusals inspect every role
at load time. Shadow checks use the completed ladder with own locals excluded and the
namespace/global boundary preserved, including later enclosing declarations across files.
Provides-block work is collected during pass 1 and executed after imports, preserving
G2BXZ's realized-sort lookup without another scope walk.

Reader audit: type readings, namespace ancestry, sort scopes and import/requires parent
admission use membership; declaration collisions reject any non-declarable role;
reflection `kind` uses primaryKind for display. Parser fixture assertions use exclusiveKind;
other destructuring sites read names/scopes and ignore kinds. Each narrowed reader states
its choice at its site.

Entity decision: a free-standing entity records Entity + Sort, so it has the explicit
sort form's type reading and preserves Ref(E) versus nullary Fn(E). Explicit `sort E {
entity E }` still has separate scoped symbols E (Sort) and E.E (Entity); nested variants
remain constructor-only. This change does not desugar identities or change entity-parent
edges. SymbolKindsTest drives the type-reading difference through term allocation; the
existing WI-940 code-generation equivalence and WI-985 parent tests also pass.

### Validation

Full `sbt testFull`: 733 passed (core 692, Scala generator 1, SMT generator 40), zero
failures. sbt used --server and writable /tmp boot/global/Ivy/temp directories because
the sandbox cannot write the normal home caches or /run/user socket directory.

Measured back-out: remove only `addKind(existing, kind)` from SymbolTable.define,
keeping the predicate mint in pass 1. Of 40 focused rows, exactly 3 fail:

- SymbolKindsTest: define accumulates roles in both orders and preserves symbol identity.
- SymbolKindsTest: a sort role added after Entity preserves the type's two nullary forms.
- RuleHeadDeclarationTest: a declaration of a name another construct owns is refused
  (the rule-first arm loads clean; operation-first remains a passing control).

The other 37 rows pass, including the explicit entity addKind and namespace-boundary
controls. Restored the merge before the final green testFull. `git diff --check` passes.
Manual diff review completed; the repository-requested pre-commit /code-review skill
was not installed, so it was not run. No commit made.

