# 063: Import rebinding — a file may choose the name it calls an import by

**Canonical reference:** [`kernel-language.md` §8.6](../kernel-language.md), §"Import forms"; and §"Namespaces and imports", *An import is file-local (WI-995)*.

## Status: DRAFT (2026-08-25). Prescriptive. Every implementation claim below is a
code read at the date of writing and carries its site; nothing here is measured except
where it says so.

## Relates to

- **WI-995** (an import is file-local) — the property rebinding inherits, and must not widen.
- **WI-1089** (`import a.b.C` binds `C`, and nothing else) — rebinding binds one name too.
- **WI-476 / WI-521** (the collision blocklist; the implicit prelude as a lowest-precedence fallback) — the pressure that makes an alias necessary.
- **WI-20260824-BFB9A** (one spec operation, one symbol) — the *producing* side of the same problem. That ticket refuses a rival declaration; this proposal gives the *consuming* side a name of its own.
- §8.6, *An ambiguity ends the ladder* — the load error this gives an in-language repair for.

## The gap

A file that needs two same-named things has no in-language repair. Today the only
recourses are to drop one import and write the qualified path at every use, or to
rename someone else's declaration. Three shapes reach it:

1. **Two namespaces declare one short name.** `import a.Report` and `import b.Report`
   in one file. The second silently replaces the first (see *Collisions* below) — and
   even if it were refused, there would be nothing to write instead.
2. **A file wants a prelude name for its own use.** The implicit prelude is shadowable
   by design (WI-521): a local `sort List` wins, and `anthill.prelude.List` then has no
   short spelling in that file at all. Rebinding is what lets both stay reachable.
3. **A name is contested at a scope.** §8.6 makes an ambiguity end the ladder and be
   reported wherever the name is written. That is the right refusal, but the author's
   only repair is qualification at every site.

Two languages in the lineage §8.6 cites for the plain form — Scala and Rust — have this
operator; Java does not. Anthill's `import` grammar has three forms and no way to say
*under what name*.

## The form

```anthill
import a.b.{Report -> BReport}                      -- rebind one name
import a.b.{Report -> BReport, Status}              -- mixable with un-rebound names
import a.b.{Report -> BReport, *}                   -- alias one name and import the scope
import anthill.prelude.{List -> PreludeList}        -- take a prelude name under another spelling
```

`->` is the spelling, and it is **not a new meaning for the token**. The proof `mapping`
block already spells name-to-name correspondence exactly this way —
`mapping { src -> tgt }` (`grammar.js:934`), braces and arrow — so a selective import's
`{C -> D}` is the same shape saying the same thing about names. The alternative
considered and rejected was a new `as` keyword (Rust's, and Scala 3's): it buys a reading
that cannot be confused with an arrow type, and costs a keyword plus a second way to
spell a correspondence the language can already spell.

The `mapping` precedent is a precedent in the **design, not in practice**, and the
distinction is worth keeping: no `.anthill` file in the corpus writes a `mapping` block
and no fixture does either — the shape lives in the grammar, `parse/ir.rs`,
`parse/convert.rs` and `kb/load.rs`, and nothing exercises it. It is a real prior
decision about what `->` may mean, not evidence that authors already read it that way.

**ONE SPELLING, AND IT IS THE BRACED ONE.** `import a.b.C -> D` is a **parse error** with
a located message naming the braced form. The clause-level position is grammatically
free — nothing follows an import path today — so this is a *choice*, not a constraint:
the braces are what make `->` unmistakably a correspondence rather than an arrow type at
a glance, they are the shape `mapping {}` already uses, and the single-name case needs
nothing new because `import a.b.{C}` is already legal. Two spellings for one relation is
the cost being avoided.

**The wildcard token itself admits no rebinding.** `import a.b.* -> X` is likewise a
parse error, for a reason worth keeping distinct from the one above: a wildcard binds no
name of its own — it splices `a.b` in as a non-enclosing resolution parent
(`add_import_parent`, `intern.rs:990`) — so there is no name for `->` to be about.

**A braced selector may end in one wildcard.** This is the collision-repair form the
feature is expected to use most often:

```anthill
import left.*
import right.{C -> RightC, *}
```

It binds `RightC` to `right.C`, imports the remainder of `right`, and does **not**
contribute bare `C` from that wildcard. Bare `C` can therefore resolve to `left.C`
without the ambiguity the unfiltered pair `import left.*; import right.*` creates. The
exclusion belongs to this one wildcard justification: a local `C`, or a `C` admitted by
another import/`requires` edge, remains independently visible.

The remainder excludes both spellings of every preceding named item: its source name and
its bound local name. For `{C -> D, *}`, the wildcard contributes neither `C` nor a
separate member named `D`; the named selector contributes the one binding `D → C`. For
an un-rebound `{Status, *}`, the wildcard omits `Status` and the named-import rung
contributes it explicitly — a semantic distinction for C666A's explicit predicate-owner
rule, not redundant syntax.

One or more named items may precede `*`, but `*` occurs at most once and must be last.
`{*}` is not a second spelling for the existing `a.b.*` form. This is Scala's selector
order and remainder model: selectors name/rename exceptions first, and the final
wildcard imports what those selectors did not claim. It is **not** equivalent to the two
independent Anthill clauses `import a.b.*; import a.b.{C -> D}`, whose unfiltered
wildcard still contributes `C`.

The grammar refusing those two strings is not enough to meet the diagnostic rule.
Rust's tree-sitter error walk currently says only `syntax error near …`
(`parse/mod.rs:68`), and scaland's whole-parse failure is likewise generic
(`parse/AnthillParser.scala:71`). Both parse boundaries must recognize these two
post-import arrow shapes and replace the generic failure with a located diagnostic that
shows `import a.b.{C -> D}` for the plain case and says that a wildcard binds no name for
the wildcard case.

**A reader collision that is real and accepted.** `{C -> D}` in TERM position is already
a legal, differently-meaning phrase: a singleton `set_literal` containing the arrow type
`C -> D` (`grammar.js:1423`, `prec(-2)`). There is no parse conflict — `selective_import`
is its own rule, reached only after `import` — but the same characters read two ways
depending on position. That is the cost of this choice, recorded rather than argued away.

Grammar delta, `tree-sitter-anthill/grammar.js`:

```js
import_path: $ => seq(
  $.identifier,
  repeat(seq('.', $.identifier)),
  optional(seq('.', choice($.wildcard_import, $.selective_import))),
),

selective_import: $ => seq(
  '{',
  commaSep1($.import_item),
  optional(seq(',', field('wildcard', $.wildcard_import))),
  '}',
),
import_item:      $ => seq($.identifier, optional(seq('->', field('alias', $.identifier)))),
```

`import_clause` is unchanged. `import_path` is deliberately tightened while this grammar
is open: a selective or wildcard segment is a **terminal suffix**, never an interior
path segment. The current repeated `_import_segment` admits `import a.{C}.E` and
`import a.*.E`; the converters then collect `a` and `E` as the base path and can silently
read the former as `import a.E.{C}`. The rebinding twin
`import a.{C -> D}.E` must be a located parse error, not another spelling that changes
which path is imported. Scaland's `ident ~ ("." ~ importSegment).rep` is tightened to
the same identifiers-plus-optional-terminal-suffix shape.

## What rebinding does not change

Each of these is a property an alias could plausibly be thought to widen, and does not:

- **It is still file-local.** The alias is one file's choice of what its own text calls
  a symbol (WI-995). Another file writing the same scope sees nothing.
- **It is still not a re-export.** `import a.b.{n -> m}` requires `b` to *declare* `n`,
  exactly as the un-rebound form does. Rebinding does not make `m` importable from here.
- **It still brings no contents.** `import a.b.{C -> D}` binds `D` and nothing else
  (WI-1089). `D.member` reaches through the bound name; `import a.b.C.*` or `requires`
  brings `C`'s contents in. The mixed `{C -> D, *}` form brings `a.b`'s contents only
  because it writes the explicit wildcard parent link as well.
- **It does not reorder the resolution ladder.** A rebound name is still an imported
  alias — rung 2 of §8.6 — and does not become a new class of binder above rung-1 own
  locals. The explicit-alias/local collision is refused below rather than resolved by
  changing those rungs.
- **`internal` is unchanged.** You may not rebind what you may not import; the
  `forbid_internal_import` refusal fires on the target, before any name is bound.
- **The symbol is unchanged.** A rebinding introduces no symbol, no clause and no
  declaration. `D` and `a.b.C` are one symbol under two spellings, so nothing
  downstream — dispatch, discrimination indexing, `by_qualified_name` — sees a second
  entity. This is the property that makes the feature cheap, and the one a reviewer
  should check first.

## Collisions — the rule this proposal exists to state

**Two named import bindings with the same destination key and different symbols are a
load error.** The destination key is exactly
`(writing SourceId, destination ScopeId, local_name)`:

- a plain import contributes one named binding;
- every named item inside a selective or mixed import contributes one, while its trailing
  `*` contributes no named binding; therefore
  `import a.{C -> D, E -> D}` is covered without needing two clauses;
- two scopes in one file may independently bind `D`, and two files writing one scope may
  independently bind it, because neither pair has the same key;
- builtin and invocation imports carry no writing `SourceId` and do not enter this
  same-file collision check. This proposal does not turn the implicit prelude or `-i`
  names into file-local declarations.

For two successfully resolved bindings at one key, equal `Symbol`s are idempotent and
legal. Different `Symbol`s produce one load error at the **later source occurrence**,
which names the earlier occurrence and both qualified targets. "Later" is source order,
not the order `add_import` happens to be called.

This is not merely a rule for the new form; it is a **pre-existing silent overwrite**
that rebinding makes trivial to hit on purpose. `SymbolTable::add_import`
(`intern.rs:955`) writes `scopes[scope].imports.insert(local_name, sym)` — a map insert
— and `visible_import` (`intern.rs:1128`) resolves under `OwnFileOnly` by taking the
**last visible writer** (`writes.iter().rev().find(…)`). No `DuplicateImport` /
`ConflictingImport` error exists anywhere in the tree (grepped: none). So today

```anthill
import a.b.{Report}
import c.d.{Report}     -- silently wins; the first line becomes dead text
```

loads clean and binds `Report` to `c.d.Report`, with nothing said. Rebinding turns that
from an accident into a spelling an author can write deliberately
(`import a.{C -> D}`, `import x.{Y -> D}`), which is why the rule has to be stated before
the form ships rather than after.

**Binding the same symbol twice remains idempotent.** Two imports naming one symbol stay
legal, and rescanning a file must not grow the import-write ledger (WI-994). Rustland
currently dedups `(origin, sym)`; scaland moves the same pair to the end. Once a
different-symbol pair is refused, neither implementation may let that storage detail
choose the semantic winner or the diagnostic site.

## Local declarations — alias refusal, plain-form census

`import a.{C -> D}` written in a scope that also declares `sort D`. Locals short-circuit
before imports (`intern.rs:1747`), so the declaration wins and the import line is dead
text. Nothing reports it: WI-999's capture check (`check_name_captures`, `load.rs:14242`)
gates on `has_kind(decl.scope.owner(), Sort)`, so it covers sort **members** only and a
namespace-level clash is unchecked.

The rebinding form has a clear answer — the author *chose* that name, so a clash is
unambiguously a mistake and should be refused. The un-rebound form is the harder half:
`import a.b.List` beside a local `sort List` is the same dead text, but refusing it may
break existing programs, and narrowing it is a different decision from adding a form.

**This proposal prescribes the refusal for an explicitly rebound item only, and leaves
the un-rebound case open pending a census.** "Local" here means an entry in the
destination scope's own `Scope::locals`, regardless of which file declared it and of its
declaration kind; it does not mean a name found through a parent. The all-files pass-1
definition invariant makes that answer available before imports run. `C -> C` still
contains an explicit alias and takes the refusal. The census asks how many sites in
stdlib, examples and the fixture corpus import an un-rebound name their own scope also
declares; it decides whether the two halves can share one rule, and it is not run here.

**Why the explicit alias does not shadow the local.** That is the other coherent first
reading: the author deliberately wrote `-> D`, so let that per-file spelling win and
leave the declaration reachable as `..n.D`. It was considered and rejected for this
proposal because it is not merely a collision policy; it creates an import rung above
locals, with consequences in every reader of the resolver:

1. The precedence would depend on the arrow token. Beside a local `C`,
   `import a.{C}` would remain dead under the existing ladder while the identity spelling
   `import a.{C -> C}` would shadow it. Two imports that bind the same local spelling to
   the same symbol would have different name-resolution strength.
2. A declaration header is installed by qualified address, while names in its body use
   ordinary resolution. In

   ```anthill
   namespace n
     import a.{C -> D}
     sort D
       entity next(value: D)
     end
   end
   ```

   the header still declares `n.D`, but `D` in its own field would denote `a.C` if the
   alias outranked the namespace's local. Recursive self-reference silently becomes a
   foreign reference. A bare rule head or defining-equation subject would likewise
   resolve through the reordered ladder and attach to the imported symbol rather than
   the declaration at the writing address.
3. The local may be a binder with no reasonable qualified replacement. A sort-level
   type parameter named `D` is an own local too; allowing an import at that scope to win
   changes every signature occurrence from the parameter to `a.C` and leaves the
   parameter syntactically declared but semantically unused.
4. Imports are file-local and scope-wide, not textual blocks. If another file declares
   `n.D`, one file writing the address would read bare `D` as `a.C` while the declaring
   file reads it as `n.D`. File-local imports already permit different imported fallbacks,
   but putting one above an own program declaration makes the address's own name vary by
   reader too.
5. Both forward code generators would need semantic rewriting rather than ordinary host
   aliases. Rust cannot emit `use a::C as D` beside a generated local `D` in the same
   module without a duplicate-name error; Scala has the analogous namespace problem.
   Fully qualifying every aliased occurrence could implement the shadow, but then the
   proposed cheap host-alias lowering is no longer the feature being specified.

The load error loses no naming power: the imported target and the local declaration
cannot both own the one short spelling `D` anyway. The author can choose a distinct alias,
or use the target's qualified path where the collision is intentional. Refusal therefore
keeps the uniform locals-before-imports ladder and turns a likely body-retargeting defect
into a located choice the author must make.

## Implementation — a cheap alias and a filtered wildcard edge

**A named alias does not change the resolution ladder.**
`SymbolTable::add_import(scope, local_name, sym, origin)` (`intern.rs:955`) already takes
the local name independently of the symbol, and both `scopes[…].imports` and
`import_origin` are keyed by it. The loader does need two names where it carries one
today:

- `source_name` is `C`: it resolves `a.b.C`, appears in unresolved/internal diagnostics,
  and never changes;
- `local_name` is `D` when an alias is present and `C` otherwise: it is the sole string
  passed to `add_import` and the key used by the collision check.

That split must survive the deferred-predicate path. Rustland's `PendingImport`
(`kb/load.rs:8994`) currently stores one `short`, while scaland's pass-4 retry both
resolves and binds `p.short` (`load/Loader.scala:150`). Each pending record must instead
carry `source_name`, `local_name`, the source-qualified path, the item span, and its
source-order ordinal. After the source symbol resolves, the deferred path runs the same
`internal` gate and collision validation as an immediate import before it binds the
local name. Call order cannot define "later": pass 4 necessarily installs a deferred
source occurrence after direct imports that may appear below it in the file.

**The mixed wildcard does change parent-edge admission.** A standalone wildcard writes
an unfiltered justification for the `scope → imported_scope` parent edge. A mixed import
writes a justification admitting every name **except** the source and local spellings of
its named items. Expanding the target's current declarations into aliases is not
equivalent: rule-introduced names arrive in pass 3, a later file may add a secondary
entry, and the imported scope's own live edges are part of wildcard reach. The filter
therefore stays on the structural edge.

Rustland's `import_parent_origin` ledger (`intern.rs:528`) already records every
justification for a deduplicated edge because an import, `requires`, exposure and an
enclosing declaration may all write the same pair. It becomes a per-write ledger whose
entry carries admission as well as provenance, conceptually:

```rust
enum ParentAdmission {
    All,
    AllExcept(HashSet<String>),
}

struct ParentWrite {
    origin: ImportOrigin,
    site: Option<ImportSiteId>,
    admission: ParentAdmission,
}
```

`site` distinguishes two import occurrences from one file and gives incremental reload
a stable dedup key; declaration/exposure justifications have no source import site. A
normal wildcard records `All`. `{C -> D, Status, *}` records
`AllExcept({C, D, Status})` and separately installs the named aliases `D → C` and
`Status → Status`.

Parent traversal for a requested `name` keeps the edge when **any visible justification
admits that name**. This union rule is load-bearing:

- a second unfiltered wildcard from the same file makes `C` visible again;
- a `requires`/enclosing declaration that independently justifies the edge remains
  unfiltered, so a mixed import cannot subtract a name the declaration supplies;
- a filtered import written by another file is absent under `OwnFileOnly`, including its
  exclusions — one file cannot hide a name in another;
- two filtered writes with different exception sets contribute the union of their
  admitted names;
- the `ImportVisibility::All` audit makes foreign writes visible but still applies each
  write's own filter.

The existing origin questions (`import_parent_visible`, import-only/enclosing-stop,
exposure-only, and the capture walk's imported-edge test) must read the **visible,
name-admitting justifications for this lookup**, not the edge's aggregate origin list.
Otherwise an exclusion on one import can suppress an independent `requires`, or a write
that excludes the requested name can still flip the subtree into import semantics.
Scaland carries origins directly on `ScopeInclusion`; its twin is an admission field plus
an import-site identity on that justification, with the same any-admitting-write rule.

The filtered parent write is installed in pass 2 from the written selector names, before
the named sources need to resolve. This ordering matters for a deferred predicate:
`{p -> q, *}` must not expose bare `p` through the wildcard during pass 3 and let a rule
head bind it before pass 4 installs `q`. If `p` remains unresolved, the import still ends
in its ordinary load error; a failed load does not turn the temporary filtered edge into
a valid partial meaning.

Sites, both implementations, as a catch-all census rather than a list of the obvious two:

| | Rust | Scala |
|---|---|---|
| grammar / parser | `tree-sitter-anthill/grammar.js:133, 146`; `parse/mod.rs` diagnostics | `parse/AnthillParser.scala` grammar + diagnostics |
| IR | `parse/ir.rs:524` (`ImportKind`) | `parse/IR.scala:313` |
| converter | `parse/convert.rs:3525` | parser builds this IR directly |
| loader / pending retry | `kb/load.rs:4774, 8994, 9048` | `load/Loader.scala:145, 914` |
| import / parent-write ledgers | `intern.rs:522, 528, 955, 1128, 1157` | `intern/SymbolTable.scala:147, 178, 321, 350` |
| codegen | `codegen/rust.rs:1264, 1268, 1273` | `codegen/scala/Bootstrap.scala` |
| canonical spec | `docs/kernel-language.md` §8.6, *Import forms* | same document |

`ImportKind::Selective(Vec<Name>)` becomes the following shape (with the Scala-shaped
equivalent in scaland):

```rust
struct ImportItem {
    source: Name,
    alias: Option<Name>,
    span: Span,
}

enum ImportKind {
    Plain,
    Selective {
        items: Vec<ImportItem>,
        wildcard: bool,
    },
    Wildcard,
}
```

The existing `Wildcard` variant remains the one spelling `import a.b.*`; `Plain` stays
unchanged because the plain spelling admits no alias. The alias's own span is the
preferred diagnostic site; the whole-item span is retained so a collision can name the
complete binding. A mixed selective import installs its named aliases and calls
`add_import_parent` once with the `AllExcept` set for the same base path, origin and
import site. Named aliases still occupy the fixed import rung; the filter affects only
what that wildcard justification may contribute during parent traversal.

**Codegen is not one shared mechanical arm.** Rust codegen renders a rebound item as
`use path::{source as local};` and renders an ordinary item as it does today. It must
**not** render the mixed form as `use path::{source as local, *};`: Rust's glob remains an
independent glob and still contributes the source name, so that output recreates the
collision Anthill removed. Rust output must instead consume the resolved filtered-import
plan and either expand the admitted remainder to explicit imports or qualify resolved
use sites; the current parse-only codegen has no complete target inventory, so supplying
that plan is part of delivering the mixed form. A loud codegen refusal is preferable to
the grouped `use`, but is not a delivered capability.

Scala's surface import has the desired selector semantics, but Bootstrap
does **not** emit Scala imports: `importedNames` is currently only
`Map[anthillLeaf, fromPackage]` (`Bootstrap.scala:549`), and `TypeScope` uses the written
leaf when it places a type. Recording `D -> package` for `C -> D` would therefore render
or diagnose `package.D`, losing `C`. Its import environment must preserve the target —
for example `local -> ImportedName(fromPackage, sourceLeaf)` — and placement of `D` must
render/resolve the type identified by `(fromPackage, C)`, including the prelude/host-type
path, without pretending `D` is declared there. The same environment carries the mixed
wildcard's remainder filter so a bare source name is not placed through that import.
Dropped aliases or exclusions can produce output that compiles and means something
else, so both codegens need golden controls.

## What must be measured and driven before delivering

1. **The duplicate-binding refusal has a population.** Before the error is added, census
   how many files in stdlib, examples and the fixture corpus bind one local name to two
   different symbols today. That number is the migration, and it is currently unknown —
   the silent overwrite means nobody has ever been told.
2. **Drive the capability through a use.** A test that only inspects the parsed import or
   says the file loaded measures too little. Resolve/call through `D` (including a
   `D.member` path) and assert the returned value; assert that `D` and `a.b.C` identify
   one symbol; and keep the control that backing the alias out makes `D` fail to resolve.
   A deferred rule-introduced predicate imported as `p -> q` must also be called through
   `q`, so the source/local split in pass 4 is exercised.
   Drive the motivating filtered-wildcard program as well: under `import left.*` plus
   `import right.{C -> RightC, *}`, bare `C` reaches `left.C`, `RightC` reaches
   `right.C`, and another `right` name arrives through the parent link. With `left.*`
   removed, bare `C` is unresolved; with the exclusion removed, it is ambiguous. If
   `right` also declares `RightC`, the named alias still reaches `right.C` rather than
   that same-spelled member.
3. **Drive every collision boundary.** Cover separate clauses, two items in one selective
   clause, plain-versus-rebound, same-symbol idempotence, the same local spelling in two
   scopes, and two files writing one scope. With the refusal backed out, the
   different-symbol same-key program must return to silently binding a writer; with it
   present, the error is located at the textually later item even when the earlier item
   resolves only in pass 4.
4. **Drive the local and visibility controls.** An explicit alias colliding with an own
   local is refused, an un-rebound import beside that local retains its pre-census
   behavior, another file cannot see or re-import the alias, and an `internal` target is
   refused on both immediate and deferred resolution paths. A filtered wildcard in one
   file does not hide its source name in a second file writing the same scope.
5. **Drive edge-justification union, not only the happy filter.** A second plain wildcard
   and an independent `requires` edge each make the excluded source visible again; two
   filtered imports with different exception sets admit the union; and `{p -> q, *}`
   keeps bare `p` out during pass 3 even when `p` is a deferred rule-introduced
   predicate. Backing out the per-justification admission and filtering only by
   `(scope, parent)` must fail these controls.
6. **The grammar change must not perturb the two neighbours that share its characters.**
   `set_literal` (`{ commaSep(_term) }`, `prec(-2)`) and `arrow_type` both live near this
   shape. Regenerate (`npx tree-sitter generate`) and run the grammar corpus
   (`npx tree-sitter test`); a new conflict there is the failure mode, and the
   `conflicts:` list at `grammar.js:33` is where it would have to be declared. If a
   conflict does appear, that is evidence about the choice and not merely a chore —
   record it here rather than only resolving it. The same corpus must reject
   `{C -> D}.E`, `*.E`, the unbraced alias and `* -> X`; the last two must assert their
   tailored diagnostics rather than merely `is_err()`. The mixed form accepts one final
   `*` and rejects `{*}`, `{*, C -> D}` and `{C -> D, *, E}` so the wildcard has one
   position and one standalone spelling.
7. **Drive both code generators.** Rust output contains `source as local` for a selective
   alias and, for a mixed import, never emits a raw glob that reintroduces the excluded
   source; its resolved expansion/qualification must compile the two-scope collision
   driver. Scala output names the imported target's real source leaf, never
   `package.local`, and its placement does not recover an excluded source through the
   wildcard. Include the motivating prelude case so `List -> PreludeList` still reaches
   whatever host/profile mapping `List` would have received without rebinding. Backing
   out each codegen change must change the golden output to the wrong symbol or fail the
   generated compilation.
8. **Update the canonical spec in the delivery change.** §8.6's *Import forms* must carry
   the grammar, source/local-name semantics, terminal-suffix rule, mixed-wildcard
   remainder/exclusion rule, per-justification union, collision key, same-symbol
   idempotence, and explicit-alias/local refusal. The proposal is not a substitute for
   the canonical language specification.
