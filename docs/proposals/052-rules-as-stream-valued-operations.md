# Proposal 052: Relations as first-class values (`Relation[T]`)

**Status:** Draft (2026-07-05)
**Depends on:** [026.1-value-integrated-kb-queries](026.1-value-integrated-kb-queries.md) (the `execute(kb, LogicalQuery) -> Stream[Substitution]` engine + the `LogicalQuery` ADT this is the typed face of), [010-query-system](010-query-system.md) (`LogicalQuery` constructors), [004-tuple-sorts](004-tuple-sorts.md) (named tuples — the schema `T`), [022-typing-as-facts](022-typing-as-facts.md) / WI-603 (rule-atom variable typing)
**Related:** [027.2-branch-from-streams](027.2-branch-from-streams.md) (the *effectful* dual — reflecting these streams into the `Branch` effect), [047-effects-as-monads-via-reflection](047-effects-as-monads-via-reflection.md) (`Branch ↦ Stream`), `stdlib/anthill/prelude/logical_stream.anthill` (`LogicalStream`), the provides-dispatch cluster (WI-424 find/map on Iterable, WI-599 finite map/filter, WI-608/609/614 requires/provides views) — the machinery the `provides` edge reuses, kernel spec §4.6 (named tuples)
**Affects:** typer (`Relation[T]` schema typing + the `provides LogicalStream[T]` edge + free-var subtraction + 1-field collapse), loader (rule reference → `Relation[T]`; application binds parameters; algebra ops → `LogicalQuery` constructors), stdlib (`Relation` sort + `provides LogicalStream[T]`)
**Design origin:** `docs/design/brainstorms/logic-monad-match-over-streams.md` (Layer 1)

## Motivation

Proposal 026.1 makes the resolver value-native — `execute(kb, q: LogicalQuery) -> Stream[Substitution]`
runs a reified query and yields a lazy stream of substitutions. That is the *engine*, and `LogicalQuery`
is even *composable* (conjunction, disjunction, guard, negation). But three things keep relational
search out of ordinary functional code:

1. **You reach it by hand-assembling a `LogicalQuery`, not by naming a rule.** The relation
   `queens(?board)` you already wrote is not itself a value you can compose or run.
2. **The element is a raw `Substitution`, untyped and unnamed.** No static type says "each solution is
   a `(board: Board)`", so a caller cannot destructure the answer with the field's type known.
3. **There is no typed relation *value*** — nothing you can bind an input on, join with another
   relation, or pass around, with the typer tracking its shape.

This proposal gives that value: a relation is a first-class **`Relation[T]`** — the *typed, composable
face* of `LogicalQuery` — whose schema `T` is the named tuple of its free variables, and which
**provides `LogicalStream[T]`** so it runs and is consumed through the ordinary Stream API. It needs no
interpreter change (projection + typing + a `provides` edge over 026.1). The *effectful* reading —
running a solution's body in direct style so it can re-enter search, via the `Branch` effect — is split
to [027.2](027.2-branch-from-streams.md); this is the pure-relational half.

## Design

### `Relation[T]` — the composable query, provides the runnable stream

```anthill
sort Relation[T] provides LogicalStream[T]    -- T = the schema: named tuple of free variables
```

One value, two faces, connected by `provides`:

- **Intensional (`Relation`):** a query not yet run. You can still bind its inputs, join it with other
  relations, project it, negate it (§"Relational algebra").
- **Extensional (`LogicalStream`, via `provides`):** because a `Relation[T]` *provides* `LogicalStream[T]`,
  it is usable directly wherever a stream is — the provision **runs the query lazily** (`splitFirst`
  advances the resolver one solution; = 026.1 `execute`). No explicit `.asStream`; "run" *is* the
  provision.

This is precisely the `IQueryable[T] : IEnumerable[T]` shape (SQL query : result set; miniKanren goal :
answer stream): `IQueryable` *extends* `IEnumerable` exactly as `Relation[T]` *provides* `LogicalStream[T]`.
A rule reference is a `Relation[T]`.

### The schema `T`

`T` is the **named tuple of the relation's free variables** — its un-supplied **head parameters**, in
declaration order. Body-internal variables are *existential*, not columns, and this is **forced by
relations being multi-clause**: a relation is defined by possibly several rules sharing one head but
with independent bodies (an implicit `union` — §Relational algebra), so the head is the only interface
common to every clause. Clause `ancestor(?x, ?y) :- parent(?x, ?z), ancestor(?z, ?y)` and a sibling
`ancestor(?x, ?y) :- parent(?x, ?y)` agree only on `(x, y)`, never on `?z` — which is why `union`
preserves the schema, and why the schema is exactly what the clauses share. To **expose** an
intermediate, put it in the head (a wider relation: `path(?x, ?z, ?y) :- …` makes `z` a column). These
head columns are, via the `provides` edge, the stream's element type (the *same* `T` on both faces).
Two degenerate arities:

- **one free variable → `T` is that value** (a 1-tuple auto-collapses): a relation with only `board`
  free is `Relation[Board]`, so `queens.head : Board`;
- **zero free variables → `T = Unit`** — a boolean/membership relation; non-empty ⇔ provable,
  multiplicity = number of proofs.

Named tuples are **ordered products and preserve declaration order** (kernel spec §4.6; verified — the
value representation does not reorder fields), so destructuring is order-faithful. Field types come from
the rule-atom variable typing computed at load (WI-603).

### `provides LogicalStream[T]` — consume with the ordinary Stream API

Consumption is not new surface: a `Relation[T]` inherits the whole Stream API through a provider
**chain** — `Relation[T]` → `LogicalStream[T]` → `Stream` (`LogicalStream` already declares
`fact Stream[T]`, `logical_stream.anthill`), dispatched by the **existing** provides machinery (WI-424
find/map, WI-599 map/filter, WI-608/609/614 requires/provides views). Providing `LogicalStream` gives
the rest of the chain transitively — there is no separate `Iterable`-vs-`Stream` choice to make.
Logic variables live in **rules** (the metalevel); functional code composes relation *values* with
operations and binds solutions with lexical `case`/`let`:

```anthill
let board  = queens.head                 -- first solution; runs one search step (partial: errors if empty)
let board? = queens.headOption           -- Option[Board] — None = no solution (total)
let (a, b) = queryTwoParams(x = 3).head  -- bind input x; destructure the solution
queens.map(board -> place(board))        -- lazy map, one per solution
queens.find(board -> valid(board))       -- inherited via provides, no re-implementation
```

There is **no `Solver` sort and no `all`/`one` keyword** — those were a redundant renaming of the
Stream API and belong to the effectful layer ([027.2](027.2-branch-from-streams.md)). Mapping for the
record: `one ≡ .head`/`.headOption`; `all ≡ the stream itself` / `.toList`.

### Relational algebra — operations, columns via lambdas over rows

On top of the provided stream interface, `Relation[T]` carries operations a bare stream *cannot* have,
each mapping to a `LogicalQuery` constructor (026.1). The rule for the whole surface: **any operation
that looks *inside* rows — a join condition, a filter, a projection — takes a lambda over the row(s)**,
and a column is read by **destructuring the row** in the binder — `lambda (x, y) -> …` — which is
existing syntax (kernel spec §4.6/§4.7, tuple destructuring). Bare column names in value position
(`on = x`) and shared free variables in operands (`cells(x, y) & p(x)`) are rejected — they would need
special name-resolution, i.e. a new construct.

> **Prerequisite (not yet in the language).** The nicer spelling — **field access `row.x`** — does *not*
> work today: kernel-language.md §6.7 dot-projection resolves only entity-constructor fields and sort
> components, **not named-tuple elements** (verified — `t.x` on a tuple, even a statically typed one, is
> a "no such member" error). Destructuring covers a single row cleanly; a *join* over two rows is
> awkward by destructuring alone (nested, fresh names) and reads far better with field access
> (`(a, b) -> eq(a.x, b.x)`). So 052's one real language prerequisite is **extending §6.7's dispatch to
> named-tuple components** — an extension of an existing construct, not a new one. See §Open questions.

| operation | form | `LogicalQuery` | schema effect |
|---|---|---|---|
| join (condition over both rows) | `join(r1, r2, (a, b) -> cond)` | `conjunction` | `T` = both rows' columns |
| filter | `where(r, (a) -> cond)` | `guarded` | unchanged |
| project | `select(r, (a) -> row)` | (projection) | `T` = the selected row |
| union (same schema, no columns touched) | `union(r1, r2)` / `r1 \| r2` | `disjunction` | same `T` |
| negation-as-failure | `negate(r)` / `not r` | `negation` | — |
| fix — column = constant (sugar) | `r.fix(x: 1)` | `guarded` + project | drops the column |
| run / consume | *inherited via `provides`* | `execute` | `LogicalStream[T]` |

`union` and `negate` touch no columns, so they keep the infix `|` / `not` sugar (plain operations, per
016). `join`/`where`/`select` each take a **row lambda** — there is no `&` join infix, because a useful
join needs a condition, and that condition is the lambda.

**`fix` is sugar** for the common "restrict a column to a constant, then drop it" — it needs no lambda
because its `x:` is a **named argument** (colon, exactly like `account(owner: "Alice")`) naming a schema
column on a single receiver; the typer matches `x` against the statically-known columns, so it is
implementable with existing syntax and no field access:

```anthill
cells                 : Relation[(x: Int, y: T)]
cells.fix(x: 1)       : Relation[(y: T)] = Relation[T]   -- ≡ where(lambda (x, y) -> eq(x, 1)), x dropped
cells.fix(x: 1, z: 2) : Relation[(y: T)]                 -- several columns
```

(Named-args use `:`; `=` is type-param syntax, and `{…}`-braces are *sets*.) Keep `fix` as a shorthand
or inline it to `where(...).select(...)`; it adds nothing new.

### Conditional join — the two shapes, in lambda form

A logic-variable join **already has a home — a rule** — and does not re-enter expression syntax:

```anthill
rule pCell(y) :- cells(x, y), p(x)      -- logic-variable join = an ordinary rule (existing syntax)
```

Composing `Relation` **values** in functional code uses the operations above. Columns are read by
**destructuring** the row in the lambda (existing syntax today); with the §6.7 field-access extension
they read as `row.x`. Both forms — the row is a named tuple whose field names are the relation's columns
(= the rule head's param-names, **statically known** at load, WI-603):

```anthill
-- destructuring (works today):
firstCell = cells.where(lambda (x, y) -> eq(x, 1)).select(lambda (x, y) -> y)
pCell     = cells.join(p, lambda ((x, y), (px)) -> eq(x, px)).select(lambda ((x, y), (px)) -> y)

-- field access (once §6.7 extends to named-tuple components — reads far better, esp. the join):
firstCell = cells.where(lambda c -> eq(c.x, 1)).select(lambda c -> c.y)
pCell     = cells.join(p, lambda (c, q) -> eq(c.x, q.x)).select(lambda (c, q) -> c.y)
```

Either way nothing floats free and no new construct appears: columns are reached by a lexical pattern
(destructuring) or by dot projection (§6.7, extended to tuples). The join's two rows are qualified by
their own binders (`(x,y)` vs `(px)`, or `c` vs `q`), so there is no clash. (`firstCell` may use the
`fix` shorthand: `cells.fix(x: 1)`.) The guiding constraint — *invent no new construction* — is why
`cells(x, y) & p(x)` (a construct) and `on = x` (a bare name needing new resolution) are out; field
access on tuples is an *extension* of §6.7, not a new form.

**Division of labor:** a logic-variable relational *definition* is a **rule** (the existing construct —
the shared variable is the join key there); value-level *composition* is **operations with row
lambdas** (`join`/`where`/`select`/`union`/`negate`), columns via named-tuple field access. No new
grammar on either path — `Relation`'s two faces (a metalevel rule result, held as a value that
`provides` a stream) are what let a rule's output drop into functional code as a composable value.

### Naming the relation — rule reference, label else head

A relation is cited by name: `queens`, or `Queen.find`. "If it has no name, use the head" is exactly
anthill's existing rule identity — a labeled rule (`rule find: ...`) is cited by its label, an
unlabeled rule by its **head functor** (`rules_by_label` vs `rules_by_functor`). A rule reference
resolves to a label if present, else the head — no new naming scheme.

### NotFound — the existing Stream contract, not new vocabulary

The empty solution set is just an empty stream; "not found" reuses the Stream API's partial/total split
— no bespoke `nil`-arm or `Error[NotFound]` at this layer:

| want | use | on empty |
|---|---|---|
| a value, assume present | `.head` | partial — errors per `Stream.head` |
| a total result | `.headOption` | `Option` — `None` = not found |
| all solutions | the stream / `.toList` | empty stream / list |

### Destructuring — positional today, by-name optional

Positional tuple destructuring **works today** and, because named tuples preserve declaration order,
binds faithfully: `let (x, y) = queryTwoParams(a = 3).head` binds `x`, `y` in the relation's free-var
order. Anonymous destructuring **by field name** is not in the grammar and its natural surface collides
with typed binders (`name: Type`); the IR (`Pattern::Tuple { named }`) and reflect (`named_tuple_pattern`)
already model it, so it is a small, optional surface extension — for order-independence, not correctness.

## Typing

Two new typer obligations, both over the 026.1 boundary:

1. **Schema synthesis.** For a relation used as a value, take its parameters (rule head / WI-603),
   subtract those supplied at the site (partial-entity expansion §8.3) → the **free** set; the schema
   `T` is the named tuple of the free set in declaration order, **collapsed to the element for one,
   `Unit` for zero**. Each algebra op transforms `T` per the table (fix removes, join merges, project
   selects).
2. **The `provides` edge.** `Relation[T] provides LogicalStream[T]` threads the *same* `T` as the
   stream element type, so every inherited Stream op (`head`/`map`/`find`/…) is typed at `T`. Running
   projects an answer `Substitution` onto the free `VarId`s into a named-tuple record (declaration
   order) — the one place a solution materializes, and only if not bound-through by a pattern.

No change to `Substitution`, `SearchStream`, or unification.

## Relationship to neighbouring proposals

- **026.1 is the engine and the ADT.** `Relation[T]` is the *typed composable face* of its
  `LogicalQuery` (the algebra ops = its constructors); running = `execute`. This adds the schema type,
  the `provides` edge, and the surface — no resolver capability.
- **027.2 is the effectful dual.** It reflects these streams into the `Branch` effect so a solution's
  body runs in direct style and may re-enter search (the eval↔SLD switch). The boundary is **nesting**;
  the `Solver`/`match`-over-a-solver surface lives entirely there.
- **The Stream/Iterable provides cluster** (WI-424/599/608/609/614) is reused unchanged — the
  consumption API is *inherited* through `provides`, not re-implemented.

## Build path

**Core:**
1. **`Relation[T]` + `provides LogicalStream[T]`** — the sort, the provision backed by `execute`
   (lazy `splitFirst`), and named-tuple projection of a `Substitution` onto the free vars (declaration
   order; 1-collapse / 0-`Unit`).
2. **Rule reference + fix** — resolve a bare/qualified rule name (label else head) to a `Relation[T]`;
   named-argument application binds parameters and narrows `T`.
3. **Schema typing** — synthesize `T` from the free set + WI-603 types; type the inherited Stream API
   at `T` through the `provides` edge.

**Increments:** join, union (`|`), project (`select`), negate (`not`) — one `LogicalQuery` constructor
+ one schema rule each; and the **named-tuple field-access extension** (§6.7 → tuple components,
**WI-638**) for the nicer `row.x` column surface (else destructuring).

Core is buildable now on existing pieces (026.1 engine, WI-603 var types, the provides cluster) with no
interpreter change.

## Open questions

1. **Named-tuple field access (the one language prerequisite — tracked as WI-638).** The lambda column
   surface reads best as `row.x`, but §6.7 dot-projection covers only entity fields and sort components,
   **not named-tuple elements** (verified: `t.x` on a tuple — even a statically typed one — is "no such
   member"). Decide between (a) **extending §6.7's dispatch to named-tuple components** (WI-638) — an
   extension of an existing construct, recommended, and useful to any tuple consumer — or (b) living
   with **destructuring** only (`lambda (x, y) -> …`), clean for one row but awkward for a join over two.
2. **Infix glyphs.** Only column-free operations take infix: `union`/`|` and `negate`/`not` (named
   canonical, infix sugar per 016). `join`/`where`/`select` each take a lambda, so there is **no `&`
   join infix**. Sub-question: whether `|` reuses the existing logical-or (WI-529) or a distinct glyph.
3. **1-field collapse boundary** — exactly where the 1-tuple → value collapse happens (typer vs.
   projection), and that it round-trips if the whole solution is passed around.
4. **Ordering / multiplicity** — solution order is the resolver's search order; whether consumption
   de-dupes or preserves multiplicity (bag vs. set) — default to the resolver's stream as-is, documented.

## Out of scope

- The `Branch` effect, `reflect(stream)`, solvers-as-handlers, the `match <solver> case` surface, and
  the eval↔SLD runtime switch — all [027.2](027.2-branch-from-streams.md).
- Direct-style search bodies that re-enter search (nested solve) — 027.2 (needs the switch).
- Scored / best-first consumption — [034-scored-branch-effect](034-scored-branch-effect.md), surfaced
  as a solver in 027.2.
- Changing the `LogicalQuery` ADT or the resolver (this is a surface + typing + `provides` layer only).
