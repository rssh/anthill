## Attributes

- id: WI-20260824-WXHNY-import-rebinding-import-a-b-c
- created: 2026-08-24T08:58:56Z

- status: Open
- status_agent: user
- status_at: 2026-08-24T08:58:56Z

- acceptance: cargo-test, scaland-sbt-test

## Description

IMPORT REBINDING: `import a.b.{C -> D, E}` — a file chooses the name it calls an import by. Proposal: docs/proposals/063-import-rebinding.md (DRAFT, prescriptive; read it first — this ticket is its delivery, not a restatement).

THE GAP. A file that needs two same-named things has no in-language repair: drop one import and qualify at every use, or rename someone else's declaration. Three shapes reach it — two namespaces declaring one short name; a file that wants a prelude name for its own use (the implicit prelude is shadowable by design, so a local `sort List` leaves `anthill.prelude.List` with NO short spelling in that file); and a name contested at a scope, where §8.6's ambiguity refusal is correct but leaves qualification as the only repair. Every language §8.6 cites for the plain form — Scala, Java, Rust — has this operator.

THE FORM, decided (user, 2026-08-24): `->`, in the BRACED form only. It is not a new meaning for the token — the proof `mapping` block already spells name-to-name correspondence as `mapping { src -> tgt }` (grammar.js:934), braces and arrow, so a selective import's `{C -> D}` is the same shape saying the same thing about names. A new `as` keyword was the rejected alternative. NOTE the precedent's exact strength: it is a precedent in the DESIGN, not in practice — no `.anthill` file and no fixture writes a `mapping` block; the shape lives in the grammar, parse/ir.rs, parse/convert.rs and kb/load.rs and nothing exercises it. ONE SPELLING, THE BRACED ONE: `import a.b.C -> D` is a PARSE ERROR with a located message naming the braced form. The clause-level position is grammatically free (nothing follows an import path today), so this is a CHOICE, not a constraint — the braces make `->` unmistakably a correspondence rather than an arrow type, they are `mapping {}`'s own shape, and the single-name case needs nothing new because `import a.b.{C}` is already legal. The WILDCARD form admits no rebinding either — `import a.b.* -> X` is a parse error, for a reason worth keeping distinct: a wildcard binds no name of its own (it splices a parent link, `add_import_parent` intern.rs:980), so there is no name for `->` to be about. A READER COLLISION THAT IS REAL AND ACCEPTED: `{C -> D}` in TERM position is already a legal, differently-meaning phrase — a singleton `set_literal` holding the arrow type `C -> D` (grammar.js:1423, prec(-2)). No PARSE conflict (`selective_import` is its own rule, reached only after `import`), but the same characters read two ways by position. Recorded as the cost of the choice, not argued away.

WHY IT IS CHEAP, and the one fact that makes it so: `SymbolTable::add_import(scope, local_name, sym, origin)` (intern.rs:945) ALREADY takes the local name independent of the symbol, and both `scopes[..].imports` and `import_origin` are keyed by it. The loader simply always passes the target's own short name today (`last_segment(&path)`, load.rs:8842). THE RESOLVER NEEDS NO CHANGE. A rebinding introduces no symbol, no clause and no declaration — `D` and `a.b.C` are ONE symbol under two spellings — so dispatch, discrimination indexing and `by_qualified_name` see nothing new. A reviewer should check that property first.

THE RULE THIS TICKET MUST SHIP WITH THE FORM, and it is a PRE-EXISTING SILENT OVERWRITE that rebinding makes trivial to hit on purpose: a second import binding a local name already bound in the same file, to a DIFFERENT symbol, must be a load error. Today `add_import` does `imports.insert(local_name, sym)` (a map insert, intern.rs:964) and `visible_import` takes the LAST visible writer (`writes.iter().rev().find(..)`, intern.rs:1130). No DuplicateImport / ConflictingImport error exists anywhere in the tree (grepped: NONE). So `import a.b.{Report}` followed by `import c.d.{Report}` loads clean, binds the second, and the first line is dead text with nothing said. Binding the same SYMBOL twice stays idempotent — `add_import` already dedups on `(origin, sym)` for WI-994's reload reason.

SITE CENSUS (the catch-all census, not the obvious two — a new IR variant's real population is the exhaustive matches):
  Rust:  tree-sitter-anthill/grammar.js:146 | parse/ir.rs:524 (ImportKind) | parse/convert.rs:3549,3575,3590 | kb/load.rs:8834 Plain, :8875 Selective, :8945 Wildcard | codegen/rust.rs:1264,1268,1273
  Scala: parse/AnthillParser.scala | parse/IR.scala:313 | parse/Converter.scala | load/Loader.scala | codegen/scala/Bootstrap.scala
CODEGEN IS THE ARM TO WATCH: it renders import lines back OUT, so an alias it drops produces output that compiles and means something else.

OPEN QUESTION, deliberately left to this ticket rather than settled in the proposal: a rebinding whose local name is also DECLARED in the same scope. Locals short-circuit before imports (intern.rs:1657), so the declaration wins and the import line is dead text, and nothing reports it — WI-999's capture check (`check_name_captures`, load.rs:13986) gates on `has_kind(decl.scope.owner(), Sort)`, so it covers sort MEMBERS only and a namespace-level clash is unchecked. The proposal prescribes the refusal FOR THE REBINDING FORM ONLY (the author chose that name, so a clash is unambiguously a mistake) and leaves the un-rebound case open pending a census: how many sites in stdlib, examples and the fixture corpus import a name their own scope also declares. RUN THAT CENSUS; it decides whether the two halves share one rule.

MEASURE BEFORE DELIVERING:
  (1) The duplicate-binding refusal HAS A POPULATION and it is currently unknown — the silent overwrite means nobody has ever been told. Census files binding one local name to two different symbols before adding the error; that number is the migration.
  (2) THE CONTROL IS THE OVERWRITE, NOT THE ALIAS. A test asserting `import a.b.{C -> D}` binds `D` measures the easy half and passes for a dozen wrong implementations. The separating rows: with the alias backed out, `D` must fail to resolve; and the two-imports-one-name program must go from SILENTLY BINDING THE LAST to a located error. Say at the test site which rows fail on a back-out and which pass either way by design.
  (3) THE GRAMMAR CHANGE MUST NOT PERTURB THE TWO NEIGHBOURS THAT SHARE ITS CHARACTERS. `set_literal` (`{ commaSep(_term) }`, prec(-2)) and `arrow_type` both live near this shape. Regenerate (`npx tree-sitter generate`) and run the grammar corpus (`npx tree-sitter test`); a new conflict there is the failure mode, and the `conflicts:` list at grammar.js:33 is where it would have to be declared. If one appears, that is EVIDENCE ABOUT THE CHOICE and not merely a chore — record it, do not only resolve it.

SPEC: kernel-language.md §8.6 *Import forms* gains the fourth form and the duplicate-binding rule; §"Namespaces and imports" keeps its three-form listing in sync. The proposal KEEPS its own text — the spec absorbs the rule, the proposal is not trimmed to a pointer.

RELATES TO: WI-995 (file-local — the property rebinding inherits and must NOT widen; another file writing the same scope sees nothing), WI-1089 (`import a.b.C` binds C and nothing else — a rebinding binds one name too, brings no contents), WI-476/WI-521 (the collision blocklist and the shadowable implicit prelude — the pressure that makes an alias necessary), WI-20260824-BFB9A (one spec operation, one symbol — the PRODUCING side of the same problem; that ticket refuses a rival declaration, this one gives the consuming side a name of its own). Independent of BFB9A: neither blocks the other.

ACCEPTANCE: the braced rebinding parses and loads in Rust; `import a.b.C -> D` and `import a.b.* -> X` are each a located parse error; a rebound name resolves in TERM, TYPE and QUERY position identically to the un-rebound one (drive all three — a test that only asserts it loads measures nothing); the duplicate-binding load error lands with its census recorded; §8.6 updated; scaland ported or its lag stated explicitly in the delivery note; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-08-24T09:22:44Z — feedback — user

CENSUS RUN (2026-08-24, claude) — the ticket's item (1), "the duplicate-binding refusal HAS A POPULATION and it is currently unknown". MEASURED: THE POPULATION IS ZERO.

METHOD. `SymbolTable::add_import` (intern.rs:945) instrumented to fire whenever the `import_origin` entry for `(scope, local_name)` already holds a write from the SAME file (`ImportOrigin::File`, compared by `SourceId::raw`) carrying a DIFFERENT symbol — i.e. exactly the silent last-writer-wins overwrite the ticket describes. Builtin / Invocation origins are excluded by construction, which is correct: the rule is per FILE. Full workspace via scripts/test.sh — 36 binaries, 5656 passed, 0 failed, 0 compile errors. Probe reverted; tree clean.

RESULT: 0 distinct names, 0 events. No file in stdlib, examples, the CLI corpus or any Rust fixture binds one local name to two different symbols.

WHAT THAT LICENSES, AND WHAT IT DOES NOT. It licenses adding the refusal with NO MIGRATION — the error can land in the same change as the form, and no existing program is repaired. It does NOT say the case cannot arise: zero is the corpus never exercising it, which is exactly what a SILENT overwrite predicts, since nobody has ever been told. The refusal's value is unchanged and its cost is now known to be nil.

CONSEQUENCE FOR THE TEST PLAN, item (2). The ticket says the separating row is "the two-imports-one-name program must go from SILENTLY BINDING THE LAST to a located error". That row now has to be WRITTEN as a new fixture rather than found among existing ones — there is no site in the corpus that changes behaviour when the refusal lands, so a back-out of the refusal alone would leave the whole suite green. Say so at the test site: this fixture is the only thing that measures the refusal.

