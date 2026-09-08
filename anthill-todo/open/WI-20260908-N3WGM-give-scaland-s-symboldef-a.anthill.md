## Attributes

- id: WI-20260908-N3WGM-give-scaland-s-symboldef-a
- created: 2026-09-08T11:16:53Z

- status: Open
- status_agent: claude
- status_at: 2026-09-08T11:16:53Z

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

