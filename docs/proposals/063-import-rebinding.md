# 063: Import rebinding — a file may choose the name it calls an import by

**Canonical reference:** [`kernel-language.md` §8.6](../kernel-language.md), §"Import forms"; and §"Namespaces and imports", *An import is file-local (WI-995)*.

## Status: DRAFT (2026-08-24). Prescriptive. Every implementation claim below is a code read of the Rust loader at the date of writing and carries its site; nothing here is measured except where it says so.

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

Every language in the lineage §8.6 cites for the plain form — Scala, Java, Rust — has
this operator. Anthill's `import` grammar has three forms and no way to say *under what
name*.

## The form

```anthill
import a.b.{Report -> BReport}                      -- rebind one name
import a.b.{Report -> BReport, Status}              -- mixable with un-rebound names
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

**The wildcard form admits no rebinding.** `import a.b.* -> X` is likewise a parse error,
for a reason worth keeping distinct from the one above: a wildcard binds no name of its
own — it splices `a.b` in as a non-enclosing resolution parent (`add_import_parent`,
`intern.rs:980`) — so there is no name for `->` to be about.

**A reader collision that is real and accepted.** `{C -> D}` in TERM position is already
a legal, differently-meaning phrase: a singleton `set_literal` containing the arrow type
`C -> D` (`grammar.js:1423`, `prec(-2)`). There is no parse conflict — `selective_import`
is its own rule, reached only after `import` — but the same characters read two ways
depending on position. That is the cost of this choice, recorded rather than argued away.

Grammar delta, `tree-sitter-anthill/grammar.js`:

```js
selective_import: $ => seq('{', commaSep1($.import_item), '}'),
import_item:      $ => seq($.identifier, optional(seq('->', field('alias', $.identifier)))),
```

`import_clause` and `import_path` are unchanged: rebinding lives entirely inside the
braced form.

## What rebinding does not change

Each of these is a property an alias could plausibly be thought to widen, and does not:

- **It is still file-local.** The alias is one file's choice of what its own text calls
  a symbol (WI-995). Another file writing the same scope sees nothing.
- **It is still not a re-export.** `import a.b.{n -> m}` requires `b` to *declare* `n`,
  exactly as the un-rebound form does. Rebinding does not make `m` importable from here.
- **It still brings no contents.** `import a.b.{C -> D}` binds `D` and nothing else
  (WI-1089). `D.member` reaches through the bound name; `import a.b.C.*` or `requires`
  brings `C`'s contents in.
- **`internal` is unchanged.** You may not rebind what you may not import; the
  `forbid_internal_import` refusal fires on the target, before any name is bound.
- **The symbol is unchanged.** A rebinding introduces no symbol, no clause and no
  declaration. `D` and `a.b.C` are one symbol under two spellings, so nothing
  downstream — dispatch, discrimination indexing, `by_qualified_name` — sees a second
  entity. This is the property that makes the feature cheap, and the one a reviewer
  should check first.

## Collisions — the rule this proposal exists to state

**A second import binding a local name already bound in the same file, to a *different*
symbol, is a load error.**

This is not merely a rule for the new form; it is a **pre-existing silent overwrite**
that rebinding makes trivial to hit on purpose. `SymbolTable::add_import`
(`intern.rs:964`) writes `scopes[scope].imports.insert(local_name, sym)` — a map insert
— and `visible_import` (`intern.rs:1130`) resolves under `OwnFileOnly` by taking the
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

**Binding the same symbol twice is idempotent**, and already is: `add_import` dedups on
`(origin, sym)` before pushing, for WI-994's reload reason. Two imports naming one
symbol stay legal.

## Open question — a rebinding against a local declaration

`import a.{C -> D}` written in a scope that also declares `sort D`. Locals short-circuit
before imports (`intern.rs:1657`), so the declaration wins and the import line is dead
text. Nothing reports it: WI-999's capture check (`check_name_captures`, `load.rs:13986`)
gates on `has_kind(decl.scope.owner(), Sort)`, so it covers sort **members** only and a
namespace-level clash is unchecked.

The rebinding form has a clear answer — the author *chose* that name, so a clash is
unambiguously a mistake and should be refused. The un-rebound form is the harder half:
`import a.b.List` beside a local `sort List` is the same dead text, but refusing it may
break existing programs, and narrowing it is a different decision from adding a form.

**This proposal prescribes the refusal for the rebinding form only, and leaves the
un-rebound case open pending a census** — how many sites in stdlib, examples and the
fixture corpus import a name their own scope also declares. That census decides whether
the two halves can share one rule, and it is not run here.

## Implementation — why it is cheap

**The resolver needs no change.** `SymbolTable::add_import(scope, local_name, sym,
origin)` (`intern.rs:945`) already takes the local name as a parameter independent of the
symbol, and both `scopes[…].imports` and `import_origin` are keyed by it. The loader
simply always passes the target's own short name today —
`last_segment(&path)` for the plain arm (`load.rs:8842`), the written name for the
selective arm. Rebinding is a matter of passing a different string.

Sites, both implementations, as a catch-all census rather than a list of the obvious two:

| | Rust | Scala |
|---|---|---|
| grammar / parser | `tree-sitter-anthill/grammar.js:146` | `parse/AnthillParser.scala` |
| IR | `parse/ir.rs:524` (`ImportKind`) | `parse/IR.scala:313` |
| converter | `parse/convert.rs:3549, 3575, 3590` | `parse/Converter.scala` |
| loader | `kb/load.rs:8834` (Plain), `:8875` (Selective), `:8945` (Wildcard) | `load/Loader.scala` |
| codegen | `codegen/rust.rs:1264, 1268, 1273` | `codegen/scala/Bootstrap.scala` |

`ImportKind::Selective(Vec<Name>)` becomes a per-item record carrying an optional alias;
`Plain` gains one. Both are exhaustive-match sites in two languages, so the compiler
names the readers — but **codegen is the arm to watch**: it renders import lines back
out, and an alias it drops produces output that compiles and means something else.

## What must be measured before delivering

1. **The duplicate-binding refusal has a population.** Before the error is added, census
   how many files in stdlib, examples and the fixture corpus bind one local name to two
   different symbols today. That number is the migration, and it is currently unknown —
   the silent overwrite means nobody has ever been told.
2. **The control is the overwrite, not the alias.** A test that only asserts
   `import a.b.{C -> D}` binds `D` measures the easy half. The row that separates this
   proposal from a no-op is: with the alias backed out, `D` must fail to resolve **and**
   the two-imports-one-name program must go from silently binding the last to a located
   error.
3. **The grammar change must not perturb the two neighbours that share its characters.**
   `set_literal` (`{ commaSep(_term) }`, `prec(-2)`) and `arrow_type` both live near this
   shape. Regenerate (`npx tree-sitter generate`) and run the grammar corpus
   (`npx tree-sitter test`); a new conflict there is the failure mode, and the
   `conflicts:` list at `grammar.js:33` is where it would have to be declared. If a
   conflict does appear, that is evidence about the choice and not merely a chore —
   record it here rather than only resolving it.
