# Proposal 052: Relations as first-class values (`Relation[T]`)

**Status:** Draft (2026-07-05; rev. 2026-08-15 — WI-638 landed; projection = distribute-dot (`select` retired); effect-row resolved; operation/relation shared-name syntax remains open)
**Depends on:** [026.1-value-integrated-kb-queries](026.1-value-integrated-kb-queries.md) (the `execute(kb, LogicalQuery) -> Stream[Solution]` engine — **landed**, `kb/execute.rs` — + the `LogicalQuery` ADT this is the typed face of), [010-query-system](010-query-system.md) (`LogicalQuery` constructors), [004-tuple-sorts](004-tuple-sorts.md) (named tuples — the schema `T`), [022-typing-as-facts](022-typing-as-facts.md) / WI-603 (rule-atom variable typing), **WI-638** (named-tuple field access `row.x` — **delivered**, the single-field `.` surface), **WI-639** (the distribute-dot `x.(f1, f2)` — **filed**, the multi-field projection surface `select` retires into), **WI-300** (rule-body requirement goals — **delivered**, how a clause body's `requires`-carrying ops get their dictionary)
**Related:** [027.2-branch-from-streams](027.2-branch-from-streams.md) (the *effectful* dual — reflecting these streams into the `Branch` effect), [047-effects-as-monads-via-reflection](047-effects-as-monads-via-reflection.md) (`Branch ↦ Stream`), [future/associated-relations](future/associated-relations.md) (the deferred per-instance-dispatched member axis), `stdlib/anthill/prelude/logical_stream.anthill` (`LogicalStream`), the provides-dispatch cluster (WI-424 find/map on Iterable, WI-599 finite map/filter, WI-608/609/614 requires/provides views) — the machinery the `provides` edge reuses, kernel spec §4.6 (named tuples) / §6.7 (dot projection — three modes)
**Affects:** typer (`Relation[T]` schema typing + the `provides LogicalStream[T, E]` edge + free-var subtraction + 1-field collapse + access-effect row), loader (rule reference → `Relation[T]` in both citation positions, incl. the new `field_access(Sort, ruleName)` → `Relation[T]` arm; application binds parameters; algebra ops → `LogicalQuery` constructors), stdlib (`Relation` sort + `provides LogicalStream[T, E]`)
**Design origin:** `docs/design/brainstorms/logic-monad-match-over-streams.md` (Layer 1)

## Motivation

Proposal 026.1 makes the resolver value-native — `execute(kb, q: LogicalQuery) -> Stream[Solution]`
runs a reified query and yields a lazy stream of solutions (each a `Substitution` + residual, WI-531).
That is the *engine* — **landed** (`kb/execute.rs`) — and `LogicalQuery`
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
sort Relation[T] provides LogicalStream[T, E = Error]
  -- T = the schema: named tuple of free variables
  -- E = the search access-effect row (⊇ {Error}); pinned to the resolver's effect, Typing §3
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
preserves the schema, and why the schema is exactly what the clauses share. A column's *type* across a
multi-clause relation is the **join (lub) of that head parameter's type in each clause** (WI-287 join
machinery — declaration-typed heads agree by construction, WI-603-inferred ones lub); a disjoint pair
(no lub) is a **load error**, never a silent widening to `Term`. A clause votes only where it has a
type to vote with: an **unconstrained** column contributes *nothing* to the lub and takes its type from
the clause that knows. A column is unconstrained when no operation parameter and no entity field types
it — its only occurrence is a rule subgoal (WI-714: the recursive clause of a transitive closure, which
is what makes a recursive relation typable with no assume-then-check iteration), or its only typing
source is an **uninstantiated spec type parameter** (WI-741: `eq(?x, "root")` types `?x` at
`PartialEq.T`, which is the *callee's* parameter and names no type at this call site). Neither is a
widening — a clause that really does say `Int64` against another's `String` is still the load error
above. To **expose** an
intermediate, put it in the head (a wider relation: `path(?x, ?z, ?y) :- …` makes `z` a column). These
head columns are, via the `provides` edge, the stream's element type (the *same* `T` on both faces).
One degenerate arity, and one that only looks degenerate:

- **one free variable → `T` is the ONE-FIELD named tuple**: a relation with only `board` free is
  `Relation[(board: Board)]`, so `queens.head : (board: Board)`, read as `row.board`. *(Revised —
  OQ5 below. This originally read "`T` is that value (a 1-tuple auto-collapses)", so
  `queens.head : Board`. That collapse erased the relation's arity and was dropped.)*
- **zero free variables → `T = Unit`** — a boolean/membership relation; non-empty ⇔ provable,
  multiplicity = number of proofs. `Unit` means zero columns and only that.

Named tuples are **ordered products and preserve declaration order** (kernel spec §4.6; verified — the
value representation does not reorder fields), so destructuring is order-faithful. Field types come from
the rule-atom variable typing computed at load (WI-603).

### `provides LogicalStream[T]` — consume with the ordinary Stream API

Consumption is not new surface: a `Relation[T]` inherits the whole Stream API through a provider
**chain** — `Relation[T]` → `LogicalStream[T]` → `Stream` (`LogicalStream` already declares
`fact Stream[T]`, `logical_stream.anthill`), dispatched by the **existing** provides machinery (WI-424
find/map, WI-599 map/filter, WI-608/609/614 requires/provides views). Providing `LogicalStream` gives
the rest of the chain transitively — there is no separate `Iterable`-vs-`Stream` choice to make.
(The provided stream is **not effect-free**: running search carries the resolver's `Error` row — see Typing §3.)
Logic variables live in **rules** (the metalevel); functional code composes relation *values* with
operations and binds solutions with lexical `case`/`let`:

```anthill
let board  = queens.head                 -- first solution; runs one search step (partial: errors if empty)
let board? = queens.headOption           -- Option[Board] — None = no solution (total)
let (a, b) = queryTwoParams(x: 3).head   -- bind input x (named arg, colon); destructure the solution
queens.map(board -> place(board))        -- lazy map, one per solution
queens.find(board -> valid(board))       -- inherited via provides, no re-implementation
```

There is **no `Solver` sort and no `all`/`one` keyword** — those were a redundant renaming of the
Stream API and belong to the effectful layer ([027.2](027.2-branch-from-streams.md)). Mapping for the
record: `one ≡ .head`/`.headOption`; `all ≡ the stream itself` / a **bounded** drain, `.takeN(n)`.

> **There is no `.toList` — the drain is bounded** (settled during the WI-714 build; earlier drafts of
> this proposal wrote `.toList`, which never existed in the stdlib on any sort). A relation is
> *maybe-infinite*: a recursive rule enumerates unboundedly. The eager drains (`collect` / `size` /
> `foldLeft` / `foldRight`) live on `FiniteCollection`, **not** on `Stream`, exactly because they walk to
> the end (WI-589 / [library/003](library/003-finite-collection.md) Phase C) — and *providing `collect` IS
> the finiteness guarantee*, which a relation cannot honor. `Relation`'s provision closure is
> `{LogicalStream, Stream, Iterable}` and stops short of `FiniteCollection`. The resolver's depth cap
> makes a drain terminate, but "terminates" is not "can be fully consumed": a truncated drain would
> silently return an incomplete answer. So bound first — `takeN` returns a `List`, which *does* provide
> `FiniteCollection`, and the fold happens where the finiteness is real:
> `foldLeft(r.takeN(100000), empty(), add)`. This is not a concession: 052's own motivating consumer
> (WI-713's `query_id_set`) is already capped at 100000 today, self-described as "a runaway guard".

### Relational algebra — conditions via row lambdas, projection via the distribute-dot, `fix` by key

On top of the provided stream interface, `Relation[T]` carries operations a bare stream *cannot* have,
each mapping to a `LogicalQuery` constructor (026.1). Two operations **read a column's value** — a join
*condition* and a filter *predicate* — and each takes a **lambda over the row(s)**; inside it a column
is reached through the binder, either by **destructuring** (`lambda (x, y) -> …`, kernel §4.6/§4.7) or by
**dot-access** (`lambda c -> c.x`, §6.7 field access, WI-638). The binder is what makes the column
**resolvable**: `c.x` types against `c`'s schema, whereas a bare `x` does not.

**Projection** doesn't read a value — it selects columns — and it is **not** a lambda op: it is the
general **distribute-dot** `x.(f1, f2)` (§"Projection"), whose members resolve *off the receiver* like
any `x.f`. **`fix`** names a column in **named-arg key position** (`fix(x: 1)`): a key is matched
structurally against the schema, never resolved as a value.

That key-vs-binder-vs-value distinction is the whole story of what is **rejected** — a column name in
*value* position with none of the three: a bare `x` floating in `on = x`, or a free variable shared
across operands (`cells(x, y) & p(x)`). There the name resolver tries to bind `x` as a scope symbol and
**fails**, or worse, silently mis-binds it to an unrelated in-scope `x`. This is exactly why a bare
`select(x, y)` is out, and why projection is instead the distribute-dot: its members resolve off the
receiver, never as free identifiers.

> **Language support — DELIVERED (WI-638).** The nicer spelling — **field access `row.x`** — now
> works. kernel-language.md §6.7 dot-projection gained a **third dispatch mode**, *named-tuple component
> access* (WI-638, commit `2102d0a5`): `t.x` and positional `t._N` on a value of named-tuple type,
> resolved name-keyed and order-independent against the tuple's `(name, type)` components. This was
> 052's one language prerequisite, and it is useful to any tuple consumer, not only relations.
> Destructuring (`lambda (x, y) -> …`) remains the clean alternative for a *single* row; field access
> reads far better for a *join* over two rows (`(a, b) -> eq(a.x, b.x)`) — nested destructuring there
> means fresh names and awkward shape — which is exactly why the extension was worth doing. This
> revision syncs §6.7's spec text to the three modes.

| operation | form | `LogicalQuery` | schema effect |
|---|---|---|---|
| join (condition over both rows) | `join(r1, r2, (a, b) -> cond)` | `conjunction` | `T` = both rows' columns |
| filter | `where(r, (a) -> cond)` | `guarded` | unchanged |
| project | `r.(f1, f2)` (rename `r.(a: f1, b: f2)`) | `projected` | `T` = the projected columns |
| union (same schema, no columns touched) | `union(r1, r2)` / `r1 \| r2` | `disjunction` | same `T` |
| negation-as-failure | `negate(r)` / `not r` | `negation` | operand must be `T = Unit`; result `T = Unit` |
| fix — column = constant (sugar) | `r.fix(x: 1)` | `guarded` + project | drops the column |
| run / consume | *inherited via `provides`* | `execute` | `LogicalStream[T]` |

`union` and `negate` touch no columns, so they keep the infix `|` / `not` sugar (plain operations, per
016). `join`/`where` each take a **row lambda** — there is no `&` join infix, because a useful join
needs a condition, and that condition (like a filter) is the lambda. **Projection** is the distribute-dot
`r.(f1, f2)` and **`fix`** is column-by-key — neither is a lambda op.

**`negate`'s operand contract is CHECKED AT LOAD** (WI-728). NAF over a relation with a free column
flounders — `not p(?x)` with `?x` unbound is undecidable, and reading the residual as a solution is a
silently wrong answer — so the operand must be a **membership** relation: zero free columns, spelled
`T = Unit`. The signature carries that as a type-level **predicate**, the fifth member
of the `Concat` / `Without` / `Project` / `FieldOf` type-constructor family and its first *unary* one:

```
operation negate(r: Relation) -> Relation[T = Membership[T = r.T], E = r.E]
```

`Membership[T]` reduces to `Unit` for a closed schema and raises otherwise, at the same return-type
normalization boundary the rest of the family reduces at — so it is checked universally, with nothing
keyed on `negate`'s identity. It is written in the RETURN rather than the parameter because a
`Relation[T = Unit]` *parameter* is still non-ground in `E`, and the argument-vs-parameter check is
gated on groundness; pinning `E` to close that gap over-narrows the row every caller must match. The
runtime guard in the host builtin stays as the backstop for what no type sees — a schema that was never
statically known (the WI-734 abstract-operand rule leaves the assertion symbolic), and a relation built
through reflect rather than from surface code.

**Projection — the distribute-dot `x.(f1, f2)`; `select` retired.** Projection is one use of a general
syntactic rule: `x.(m1, …, mn)` desugars to the **ordered/named** tuple `(m1: x.m1, …, mn: x.mn)` —
distribute the receiver over a member list; each `x.mi` is ordinary dot-dispatch (a field — but any
member, not only fields), and the result is **keyed by the member names**. Two properties make it safe
and schema-preserving:

- **Members resolve at *typing*, not at name-resolution.** Each `mi` lands in `field_access(x, mi)` dot
  position — exactly the `x.f` shape WI-638 already resolves against `x`'s type at the typer, *after*
  name resolution. So `mi` rides past the name resolver **unresolved** (never a scope symbol) and is
  resolved as a member of `x` during typing. This is why **rename `x.(a: f1, b: f2)` is fine**: it
  desugars to `(a: x.f1, b: x.f2)`, where the new labels `a`/`b` are construction keys and the sources
  `f1`/`f2` are dot-members (typed-resolved) — neither is a value-position free identifier. Bare
  `x.(f1, f2)` auto-labels: the member name is *both* the result key and the dot-member, `(f1: x.f1, …)`.
- **The result is the *ordered/named* tuple, not positional.** `x.(f1, f2)` ⇒ `(f1: x.f1, f2: x.f2)`,
  **not** `(x.f1, x.f2)` (which would auto-name `_1, _2` and lose the schema). Preserving the labels is
  what lets a projected relation keep its columns and re-join by name — so the distinction between a
  positional tuple and a labelled/ordered one is load-bearing here, not cosmetic.

**Lifted over a relation, `r.(f1, f2)` *is* projection** → `projected` (schema-preserving via the
name-keying). So **`select` is retired**: projection is the distribute-dot on a relation, and the same
`.( )` is a general named-tuple operation useful far beyond relations (the WI-638 generalization). Until
`.( )` lands, `projected` is reachable directly — the typer maps a name-keyed row-tuple to `projected`.

> **Superseded (WI-762).** `.( )` landed as WI-639, so that stopgap is retired: a name-keyed row tuple is
> **no longer** mapped to `projected`. Only a written `.( )` projects. The desugaring is structurally
> identical to the hand-written tuple, so `convert.rs` now MARKS it and the typer reads the mark instead
> of inferring projection-hood from the fields' shape and their receivers' source spans. Consequence, and
> intended: `r.(f1, f2)` is `Relation[T = (f1, f2)]`, while `(f1: r.f1, f2: r.f2)` is an ordinary tuple of
> two independent single-column relations. This is the same line the paragraph below already draws for
> *computed* columns — those leave the distribute-dot entirely and are written with `.map`, yielding a
> `Stream`, not a `Relation`. See kernel-language.md §6.8.

A **computed** column (an expression member like `x.f1 + 1`, not a bare member) is *not* projection —
the value is no longer joinable-as-a-column — so it is **out of the distribute-dot**: compute it
functionally with `.map` on the provided stream, which yields a plain `Stream`, not a `Relation`.
(Extended projection — a computed
column threaded back as a fresh joinable var + an equation `v = expr`, i.e. `guarded` + `conjunction`,
*staying* a `Relation` — is a later increment, not core.) **Engine note:** `projected` currently lowers
as a **pass-through** — `kb/execute.rs` flattens `projected`/`limited` to the inner query's goals and
leaves projection to the caller ("the resolver itself has nothing to do differently"). So 052 applies
the column restriction at **its own materialization step** (project the answer named tuple onto the
kept columns), not in the resolver — this is the one algebra op whose backing is not already wired.

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
or inline it to `where(...)` + a projection `.( )` that drops the fixed column; it adds nothing new.

### Conditional join — the two shapes, in lambda form

A logic-variable join **already has a home — a rule** — and does not re-enter expression syntax:

```anthill
rule pCell(y) :- cells(x, y), p(x)      -- logic-variable join = an ordinary rule (existing syntax)
```

Composing `Relation` **values** in functional code uses the operations above. Columns are read by
**destructuring** the row in the lambda, or — since WI-638 — by §6.7 named-tuple field access,
so they read as `row.x`. Both forms — the row is a named tuple whose field names are the relation's columns
(= the rule head's param-names, **statically known** at load, WI-603):

```anthill
-- the CONDITION reads column values (a lambda); PROJECTION is the distribute-dot .( ) (no lambda).
-- r.(y) lifts the tuple projection over the relation to `projected`, giving `Relation[(y: …)]`.
-- destructuring the condition's row:
firstCell = cells.where(lambda (x, y) -> eq(x, 1)).(y)
pCell     = cells.join(p, lambda ((x, y), (px)) -> eq(x, px)).(y)

-- dot-access in the condition (§6.7 field access, WI-638); projection is the same .(y) either way:
firstCell = cells.where(lambda c -> eq(c.x, 1)).(y)
pCell     = cells.join(p, lambda (c, q) -> eq(c.x, q.x)).(y)
```

Either way nothing floats free and no new construct appears: columns are reached by a lexical pattern
(destructuring) or by dot projection (§6.7 named-tuple mode, WI-638). The join's two rows are qualified by
their own binders (`(x,y)` vs `(px)`, or `c` vs `q`), so there is no clash. (`firstCell` may use the
`fix` shorthand: `cells.fix(x: 1)`.) The guiding constraint — *invent no new construction* — is why
`cells(x, y) & p(x)` (a construct) and `on = x` (a bare name needing new resolution) are out; field
access on tuples is §6.7's named-tuple component mode (WI-638), not a new form.

**Division of labor:** a logic-variable relational *definition* is a **rule** (the existing construct —
the shared variable is the join key there); value-level *composition* is **operations** — `join`/`where`
take a **row lambda** (columns via destructuring or dot-access), **projection** is the distribute-dot
`r.(f1, f2)`, `fix` names a column by **key**, and `union`/`negate` are column-free infix. No new grammar
on either path — `Relation`'s two faces (a metalevel rule result, held as a value that
`provides` a stream) are what let a rule's output drop into functional code as a composable value.

### Compiling a row lambda into a query — the expression-tree translation

`join`/`where`'s row lambda is **never applied** — it is compiled, *as syntax*, into the query. This is
exactly LINQ's `IQueryable`: the condition is captured as an **expression tree** and a provider
translates the tree into the backend query. Here the backend is the `LogicalQuery` ADT (026.1), not SQL.

**The mapping** — a `Bool`-valued expression tree → a goal; each node maps to a query-algebra
constructor:

| lambda expression | `LogicalQuery` |
|---|---|
| atomic predicate `eq(a,b)`, `lt(a,b)`, … | goal atom |
| `&&` / `\|\|` / `!` | `conjunction` / `disjunction` / `negation` |
| `c.x` (row field access) | the column's logic variable |
| literal | term constant |
| any other **row-independent** operand | a **parameter** of the recipe, captured at the call |

and the op wraps the result: `where` → `guarded(r.query, ⟨goal⟩)`, `join` → `conjunction` (over both
rows' columns). The compile is **partial** — only the goal-expressible `Bool` subset; anything else (an
`if`, a non-predicate call) is a **compile error**, the analog of LINQ's *"cannot translate to SQL"* (a
computed column goes through `.map` on the stream instead — it is no longer a `Relation`).

**An operand is admissible iff it does not read the row.** A column and a literal are the two shapes the
compiler can resolve *by itself*; every other operand — a `let`-bound name, an operation result, the
enclosing operation's own parameter — is one value for the whole restriction, and becomes the recipe's
second kind of hole: a **parameter**. The macro cannot fold it (it reads the lambda as *syntax*, before
any value exists), so it hands the **expression** to the runner as a captured argument, evaluated once in
the caller's scope and filled into the hole exactly as a column hole is filled from the schema. This is
what makes `fix(x: v)` and `where(λ c → eq(c.x, v)) + project` the same restriction for the same `v`.
An operand that *does* read the row (`eq(c.rank, bump(c.age))`) stays a compile error: there is no single
value to capture, and a query goal compares columns rather than evaluating an expression per row.

**Two phases, joined at the columns.** A relation's columns are logic variables minted only when the
relation *runs* (`VarId`s in the `Relation` value), so the compile splits:

- **compile-time** — parse the lambda's expression tree and build a **query-term recipe**: the
  `LogicalQuery` above with the columns left as **holes** (`c.x` compiled to *column position i*, not a
  name — positional, so no cross-scope name comparison).
- **runtime** — *extract the query term*: fill the holes with the relation's actual column `VarId`s.
  This is the variable alignment `union` already performs (`rename_query_vars`), one operand.

The query term is the **carrier-neutral representation** (a `Value` spine — `Value::Entity` constructors,
`VarId` columns, `Value::Term`/`Node` leaves), never a hash-consed `TermId` (the WI-348 boundary) — what
`build_logical_query_value` already produces for `negate`/`union`.

**Why the split is forced by codegen.** The translation can run *wherever the lambda's tree survives to
runtime* — a C# `Expression<>`, a Scala `Expr`, or the interpreter's `closure.body` (all LINQ-style:
translate on enumerate). It is forced **earlier**, to anthill's **compile-time**, only for a host that
keeps no tree at runtime — a plain Rust `Fn` after codegen carries no AST. Building the recipe at
compile-time and emitting a plain query into the generated code makes it codegen-safe on *every* host.

**Only the functional condition is a lambda; logic-variable conditions are rules.** A raw logic-variable
goal is **not** a `where`/`join` argument (`where(r, eq(?x, 1))` is out): it would carry the metalevel
(logic vars, rule-scoping) into functional expression syntax, and the clean form already exists — write
a **rule** (the Division of labor above). This is a **layer separation**, not a soundness rule; the
lambda binder is simply the *functional* way to name a column — field access on a row value.

**Implementation locus.** A **compile-time transform in the typer** builds the recipe: it reads the
lambda's already-typed occurrence (`c.x` resolved against the row schema) and emits the carrier-neutral
`LogicalQuery` `Value` directly — uniform with the Rust `negate`/`union` builtins. Authoring this
transform *in anthill* instead — user-extensible relational algebra via the
[043.1](043.1-compile-time-macros.md) compile-time macro — is the alternative route; it is not required
for the built-in ops (and carries the occurrence-build surface 043.1 specifies).

### Naming the relation — rule reference (label else head), and how a bare name parses

A relation is cited **by name**, and the name resolves the way rule identity already works — a labeled
rule (`rule find: …`) by its **label**, an unlabeled rule by its **head functor** (`rules_by_label` /
`rule_id_by_qn` vs `rules_by_functor`; rule head functors are scoped, carry qualified names, and import
like any symbol — kernel spec §"Rule head functors are scoped definitions"). A rule reference resolves
to a label if present, else the head — no new naming scheme. But **there are two citation positions, and
the grammar (§6.7) treats them differently** — this is load-bearing and was under-specified before:

- **Applied — `queens(board)`, `Queen.find(board)`, `queryTwoParams(x: 3)`.** A name followed by
  `(…)`/`{…}` parses as a **qualified-name application** (`fn_term(name: Queen.find, …)`), which
  `rule_id_by_qn` resolves directly to the rule. This is the primary form; every §"Relational algebra"
  operation that *supplies arguments* lives here, and it works on existing machinery.
- **Bare — `queens`, `Queen.find` as a first-class value** (to pass to an op, join, or dot-consume:
  `Queen.find.map(…)`, `join(Queen.find, …)`). Here the grammar bites: a bare **`Queen.find` parses as
  `field_access(Queen, find)`** — §6.7: a name with *no* trailing `(…)` is dot projection, **not** a
  qualified name — and today dot-dispatch resolves only operations / entity fields / sort components /
  named-tuple components (WI-638), **never a rule**. A bare *unqualified* `queens` is fine (it is a
  plain name, not a `field_access`); a bare *qualified* `Queen.find` value is the gap.

**052 owns one resolution arm for the bare qualified case:** when the receiver of a `field_access` is a
**sort / namespace symbol** — statically known at load, i.e. §6.7's mode-2 "sort component access" — and
the member names a **rule in that scope** (label else head functor), produce the **`Relation[T]`**
value. Same rule identity as above, surfaced as a value; a *resolve-time* arm (the receiver is a sort,
not a runtime value, so it is unambiguously distinguishable from value-level dot), parallel to how
WI-638 added the named-tuple arm. This is the only new naming work, and it makes bare `Queen.find` a
relation value uniformly with the bare unqualified `queens`.

**`x.name` on a *runtime value* is not a way to name a relation.** Dot on a value `x` is
operation-dispatch (the provides cluster): it reaches `x`'s *operations / fields*, and a rule is not a
member of a value's sort. A value yields a relation only via an **operation or field that *returns*
`Relation[T]`** (e.g. `node.neighbours() : Relation[Node]`), consumed like any relation — never by
dot-naming a rule off `x`.

### Requirements in a clause body — the rule-body dictionary (WI-300), and checking a missing one

A relation's clauses are rules, and a clause body may call an operation carrying a `requires` clause (a
spec / typeclass constraint). 052 must say how the requirement dictionary reaches that call — because it
is **not** the operation-call mechanism:

- **An operation gets its dictionary from its *caller*** — inserted requirement params filled at the
  `apply_within(…, requirements=[…])` call site, read via `var_ref` (the op-call model,
  `docs/design/operation-call-model.md`).
- **A rule has no caller.** SLD fires a relation against a *query* that supplies concrete values, so a
  clause resolves its *own* dictionary through the **delivered rule-body requirement model** (WI-300,
  `requirement-dictionaries.md §3`): a body `requires(X)` desugars (in the converter) to the builtin
  **`find_dictionary(X)`** goal, which the typer sweep rewrites to `find_dictionary(spec_base,
  op_functor, op_arg…)`, and the resolver discharges by **provides-resolution at the current
  substitution** — the dictionary binds into the resolver's Γ (the SLD analog of eval's
  `frame.requirements`) and the body's spec-ops dispatch through it. If the binding is
  **under-determined**, the goal **suspends as a residual** (WI-292 resolve-or-suspend / WI-067) — it is
  *never* NAF-decided false.

So 052 adds no requirement mechanism: a relation carrying `requires X` threads it exactly as any rule
body does, and **052 depends on WI-300** the way it depends on 026.1 for `execute`. A clause needing
`Eq[T]` either declares `requires Eq[T]` on the relation (propagating the obligation to whoever queries
it under a concrete `T`) or relies on an in-scope provision resolved at fire time.

**Checking a missing requirement (statically) — a real gap to close.** The requirement machinery
already reports a genuinely unsatisfiable requirement as a **loud type error** — `MissingRequiresForSpecOp`
(WI-325), the no-provision no-instance error, and "missing `requires X[T]` on enclosing sort" (WI-420).
**But that diagnostic pass (`req_insertion`) walks operation bodies (`kb.op_bodies`), *not* rule
`body_nodes`** — so today a *relation clause's* missing requirement is caught only at **resolution** (the
`find_dictionary` goal fails), not at **load**. To make it a load error — the repo's "loud error over a
silent skip" — 052's static face must **extend the `MissingRequiresForSpecOp` check to relation clause
bodies**: walk each clause's spec-op calls and flag any requirement that is neither declared `requires`
on the relation nor satisfiable by a provision. The one distinction the check must keep (WI-292): a
**statically-missing** requirement (no provision can satisfy it, undeclared) is an *error*; an
**under-determined** one (the type is not ground at the current binding) *suspends* — report the former,
never the latter.

### NotFound — the existing Stream contract, not new vocabulary

The empty solution set is just an empty stream; "not found" reuses the Stream API's partial/total split
— no bespoke `nil`-arm or `Error[NotFound]` at this layer:

| want | use | on empty |
|---|---|---|
| a value, assume present | `.head` | partial — raises `Error[EmptyStream]` |
| a total result | `.headOption` | `Option` — `None` = not found |
| the first solution and the rest | `.splitFirst` | `none` |
| all solutions | the stream / `.takeN(n)` (bounded — see above) | empty stream / list |

All of these **evaluate** on a relation. `Stream` defines `.head`/`.headOption`/`.tail` by default
**bodies** over `.splitFirst`, so a carrier supplying only the primitive inherits working
implementations; the equational laws alongside them are *specification*, and a law is not backing.

**Every one of them carries the relation's own observation row `E ⊇ {Error}`** — reading a relation
runs the resolver, which can fail — so none of these is callable from a pure operation. `.headOption`
is *total in its value* (`None` rather than a raise), not effect-free. On top of that row, `.head` and
`.tail` add `Error[EmptyStream]`, **guarded** by `isEmpty`; a relation is lazy, so that guard is never
statically refutable and the label always stays. Concretely, `queens.head` is `Board` with
`{Error, Error[EmptyStream]}`, while `queens.headOption` is `Option[Board]` with `{Error}`. Prefer
`.headOption` wherever "no solution" is an ordinary outcome — it drops a label, not the row.

Guard discharge is a general typer mechanism, not a relation-specific one: `Int64.div`'s
`Error[DivisionByZero] :- eq(b, 0)` *does* discharge against a literal divisor. It does not yet fire
for `isEmpty` on **any** carrier — `head(cons(7, nil))` in a pure operation is refused today, exactly
as on a relation. Closing that is WI-567; until it lands, "the guard stays" is the rule everywhere,
and the laziness argument above says only that a relation is where it must stay *permanently*.

A relation is an unordered **bag**: which solution `.head` returns is the resolver's enumeration
order, not a promise.

### Destructuring — positional today, by-name optional

Positional tuple destructuring **works today** and, because named tuples preserve declaration order,
binds faithfully: `let (x, y) = queryTwoParams(a: 3).head` binds `x`, `y` in the relation's free-var
order. Anonymous destructuring **by field name** is not in the grammar and its natural surface collides
with typed binders (`name: Type`); the IR (`Pattern::Tuple { named }`) and reflect (`named_tuple_pattern`)
already model it, so it is a small, optional surface extension — for order-independence, not correctness.

## Typing

Three new typer obligations, all over the 026.1 boundary:

1. **Schema synthesis.** For a relation used as a value, take its parameters (rule head / WI-603),
   subtract those supplied at the site (partial-entity expansion §8.3) → the **free** set; the schema
   `T` is the named tuple of the free set in declaration order (**`Unit` for zero**; no arity-one
   special case — OQ5), with each column typed at the **lub across clauses** (§"The schema `T`"). Each
   algebra op transforms `T` per the table (fix removes, join merges, project selects).
2. **The `provides` edge.** `Relation[T] provides LogicalStream[T, E]` threads the *same* `T` as the
   stream element type, so every inherited Stream op (`head`/`map`/`find`/…) is typed at `T`. Running
   projects an answer `Solution`'s substitution onto the free `VarId`s into a named-tuple record
   (declaration order) — the one place a solution materializes, and only if not bound-through by a
   pattern.
3. **The access-effect row.** Running a relation is **not pure**. The provision is backed by 026.1
   `execute(kb, q) -> Stream[T = Solution, E = Error] effects Error` (`reflect.anthill`) — search can
   raise (a depth limit, or an `Error.raise` from an operation body evaluated during resolution). So
   the provided stream is `LogicalStream[T, E]` with **`E ⊇ {Error}`**, and every inherited Stream op is
   typed at that row, *not* at `{}`; the `provides` edge threads `E` alongside `T`. `LogicalStream`'s
   stdlib `fact Stream[T]` currently omits the row and must carry it — a pre-existing gap the finiteness
   cluster (WI-357/365/368/…) already had to close at the consumption boundary for other Stream
   carriers, so the machinery exists. "Pure-relational" (§Motivation) means *free of the `Branch`
   effect* (027.2's nested-search control) — **not** effect-`{}`.

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
- **[043.1](043.1-compile-time-macros.md) is the *alternative* locus for the row-lambda compile.** Its
  compile-time macro is the user-extensible way to author the expression-tree → query translation in
  anthill; the built-in `where`/`join` instead do it as a typer pass (§"Compiling a row lambda into a
  query"), so 043.1 is a *related* mechanism, not a prerequisite.

## Build path

**Core:**
1. **`Relation[T]` + `provides LogicalStream[T, E]`** — the sort, the provision backed by `execute`
   (lazy `splitFirst`), and named-tuple projection of a `Solution`'s substitution onto the free vars
   (declaration order; `Unit` for zero columns, the named tuple otherwise).
2. **Rule reference + fix** — resolve a rule name to a `Relation[T]` in **both** citation positions
   (§Naming): applied `Sort.rule(…)` via `rule_id_by_qn`, and the **new bare-qualified arm** —
   `field_access(Sort, ruleName)` on a sort symbol → `Relation[T]` (the one new name-resolution piece).
   Named-argument application (`:`) binds parameters and narrows `T`.
3. **Schema typing** — synthesize `T` from the free set + WI-603 types (column type = lub across
   clauses); type the inherited Stream API at `T` **and the access-effect row `E ⊇ {Error}`** through
   the `provides` edge.

**Increments (one wired `LogicalQuery` constructor + one schema rule each):** join (`conjunction`),
union (`|`, `disjunction`), negate (`not`, `negation`), where (`guarded`) — all four constructors are
**already wired in `kb/execute.rs`**. `union`/`negate` are just constructor + schema (they combine query
*values*, no lambda — **delivered**); `where`/`join` additionally carry the **row-lambda compile**
(§"Compiling a row lambda into a query" — a compile-time expression-tree → query-term recipe over those
constructors, columns filled with the relation's `VarId`s at runtime; typer-pass locus). **Project** (→ `projected`) has no `select` op — it is the
**distribute-dot** `x.(f1, f2)` ⇒ `(f1: x.f1, f2: x.f2)`, lifted over a relation to `r.(f1, f2)` →
`projected` — and because the resolver lowers `projected` as a pass-through, it needs caller-side column
restriction at 052's materialization step. The single-field `x.f` is **delivered (WI-638)**; the
distribute-dot `x.(…)` is **WI-639** — a general §6.7 form (members resolved at *typing*, like WI-638;
result the ordered/named tuple), useful to any tuple consumer, not only relations. Until it lands,
`projected` is reached via a name-keyed row-tuple the typer recognizes. *(Superseded — WI-639 landed and
WI-762 retired that reading; see the note at "Lifted over a relation" above.)*

Core rests on **landed** pieces — the 026.1 `execute`/`lower_query` engine (`kb/execute.rs`, with
`conjunction`/`disjunction`/`negation`/`guarded` wired), WI-603 var types, the provides cluster — with
no interpreter change. The genuinely-new pieces are all typer/loader-level: schema synthesis +
effect-row threading, the bare-qualified rule-value resolution arm, the distribute-dot projection
(`x.(…)` + the relation lift to `projected`), and — for clauses that call `requires`-carrying spec-ops —
extending the `MissingRequiresForSpecOp` static check from op-bodies to relation clause bodies (else a
missing requirement surfaces at query time, not load; the runtime path itself is WI-300, delivered).

## Open questions

1. **Named-tuple field access — RESOLVED (delivered, WI-638).** Shipped as §6.7's third dispatch mode
   (`row.x` / positional `t._N`, name-keyed and order-independent). The lambda column surface reads as
   `row.x`; destructuring stays the one-row alternative. Remaining task is documentation hygiene — this
   revision syncs kernel-language.md §6.7 to describe the three modes.
2. **Bare `Sort.rule` value vs. field projection (naming parse).** §Naming resolves
   `field_access(Sort, ruleName)` on a *sort symbol* to a `Relation[T]`. Open sub-question: is this
   silent overload of `.` on a sort surprising next to value-level dot (operation dispatch), or is bare
   unqualified `queens` + applied `Sort.rule(…)` enough, leaving bare *qualified* relation values rare?
   Default: **add the arm** — a sort-symbol receiver is statically distinguishable from a value receiver,
   so there is no runtime ambiguity, and it keeps `Queen.find.map(…)` working.
3. **Projection surface — DECIDED: the distribute-dot `x.(f1, f2)`; `select` retired.** `x.(m1, …, mn)`
   ⇒ the **ordered/named** tuple `(m1: x.m1, …)`; general over any named tuple (members are any
   dot-member, not only fields), lifting over a relation to `r.(f1, f2)` → `projected`. **Safe by
   resolution timing:** each member rides in `field_access(x, mi)` dot-position, resolved at *typing*
   (WI-638) against `x`'s type, never as a value symbol at name-resolution — so bare keep (`x.(f1, f2)`)
   and rename (`x.(a: f1)`, ⇒ `(a: x.f1)`) both resolve. Bare `select(x, y)` is out; `select` is gone.
   The Mongo flag-tuple `(f1: 1, f2: 1)` was runner-up (no new grammar, an exclude form) but rejected for
   magic `1`/`0` and unnatural rename. Remaining sub-points:
   - **colon vs bare** — DECIDED: **bare** for keep (member name auto-labels), **colon** for rename
     (`x.(a: f1)`). No dangling-colon keep form.
   - **non-bare members** — a bare member auto-labels; a member that is a *call or expression*
     (`x.(count(), y)`) needs a label rule (label = the head identifier, or an explicit `n: expr`).
   - **positional variant** — `x.(f1, f2)` is deliberately the *named* tuple; write `(x.f1, x.f2)`
     explicitly if a positional result is ever wanted. Default: named only.
   - **exclude** — `.( )` lists what to *keep*; no exclude form (the Mongo variant's one edge); defer,
     or a later `x.(-f3)`.
   - **general feature** — the distribute-dot is bigger than 052 (like WI-638 was); it is filed as its
     own ticket, **WI-639** (a general §6.7 form). 052 just *consumes* it.
4. **Infix glyphs.** Only column-free operations take infix: `union`/`|` and `negate`/`not` (named
   canonical, infix sugar per 016). `join`/`where` take a lambda, projection is the distribute-dot, and
   `fix` names a column by key, so there is **no `&` join infix**. Sub-question: whether `|` reuses the
   existing logical-or (WI-529) or a distinct glyph.
5. **1-field collapse — DECIDED, AND THE DECISION IS TO DROP IT** (option A, WI-20260818-YQB1Y,
   2026-08-18). A relation's schema **is** its row type, always the full named tuple of its columns:
   `Relation[(age: Int64)]`, rows `(age: 30)`, read as `row.age`. Zero columns is `Unit` and means
   exactly that. There is no arity-one special case anywhere.

   **What was decided before, and why it was revisited.** The original answer was "do the 1-tuple →
   element collapse once, at the schema-typing / projection boundary, and keep the *stored* element as
   the 1-field record so passing the whole solution around round-trips". Its whole stated rationale was
   one line of ergonomics: "a relation with only `board` free is `Relation[Board]`, so
   `queens.head : Board`". Implementation split the two halves onto opposite sides of the boundary —
   the runtime VALUE kept `(column name, VarId)` for every column while the TYPE discarded the symbol —
   so the collapse was lossy in the type and not in the value.

   **THE MEASUREMENT THAT DECIDED IT** is that the erasure is of **ARITY**, not of a name. A collapsed
   schema no longer said how many columns it came from, so three schemas became the *same type*:

   - **one column** — its name was gone, so `Concat` / `Without` / `Project` each **refused** a
     one-column operand, and `Concat`/`Without` were not inverses at arity one;
   - **zero columns vs one `Unit`-typed column** — both `Unit`, so `Membership` accepted a relation
     that still had a column (WI-728's recorded limit) and only the drain refused it;
   - **n columns vs one column whose type is an n-field tuple** — both that tuple. This one was a
     **silent wrong answer**, not a refusal: over `entity pair_holder(p: (a: Int64, b: String))`,
     `rule pairs(?p)` joined with a two-column relation type-checked against a FOUR-column merged
     schema while the row `join_run` materialized had THREE. No type-level check could exist, because
     the two schemas were the same type; and no runtime check either, because **merging is name-free**
     — `fix` / `project` / `negate` each ask the value "is there a column of this name?" and refuse
     loudly, `Concat` has no such question. It was the one member of the family with no backstop on
     either side.

   **THE CENSUS.** The ticket's static count (`examples/`, `stdlib/`, `rustland/*/anthill/`) was that
   no one-column rule is consumed as a relation *value* — every citation is a goal in a rule body,
   where the schema type never arises — and that the only one-column drain anywhere,
   `examples/classic-mini/ancestor`, is reached by APPLICATION and does `length(ofBart.takeN(100))`
   without ever touching an element. Re-counted at delivery the shape holds (≈49 rule names with
   exactly one head variable, all cited as goals), though the exact number depends on whether
   equational `[simp]` heads are counted, so treat it as an order of magnitude rather than a figure.

   **WHAT ACTUALLY SETTLED IT WAS THE DELIVERY, NOT THE COUNT.** Dropping the collapse moves the type,
   the row and the term together, so ANY shipped source draining a one-column relation as a value would
   have failed to load. None did: every `.anthill` file under `stdlib/`, `examples/` and the project's
   own program is unchanged and the whole workspace suite is green — the only edits the change forced
   were in per-feature test fixtures. So the count of call sites that had to change from `x` to `x.col`
   in shipped code is **zero**, measured rather than surveyed.

   And the application case is an argument *for* dropping the collapse: `ancestor("bart")` is exactly
   where a column name used to be destroyed, and the narrowed relation now keeps its column.

   **THE ALTERNATIVE, RECORDED AND DECLINED.** *(B)* keep the collapsed row type behind a new
   `Collapse[T]` constructor in the family, reduced at the same boundary. It buys exactly the one
   ergonomic line above and nothing else; it needs a new constructor where (A) needs none; it does not
   make `Membership` arity-exact by itself; and it carries a risk (A) simply deletes — whether a ctor
   reduces across the `provides LogicalStream[T = T, E = E]` edge with the sort's own abstract `T` as
   operand, which WI-734 says leaves it symbolic. (A) is simpler than the code that shipped the
   collapse, not merely simpler than (B). *(WI-1131 had also removed the old objection to (A): a
   one-field named tuple was a syntax error as a VALUE until 2026-08-18, so "just use a one-element
   tuple" was not fully writable when this section first chose the collapse.)*

   **WHAT IT COST TO LAND**, since it is a breaking change to a specified rule and the price belongs
   next to the decision:

   - **Both halves of the paired convention moved together**, which kernel-language.md §6.8 required of
     any revision. The TERM half — `x.(f)` desugared at convert time to the scalar `x.f`, and a single
     rename `x.(a: f)` dropped its label — now builds `(f: x.f)` / `(a: x.f)` at every arity. The TYPE
     half (`relation_schema_type`) and the VALUE half (`materialize_solution`) moved with it. Keeping
     the collapse for a plain tuple while dropping it for a relation was considered and declined: it
     would make `r.(f)` and `t.(f)` mean different things at one surface.
   - **`where`'s bare-binder spelling is gone**, and the WHOLE-ROW sentinel with it. `eq(c, 30)` over a
     one-column relation used to compile to a sentinel hole that `where_run` filled with the sole
     column — correct only *because* the row was the column. A row is a tuple now, so no column
     variable carries it and a bare binder is a **loud error**; the spelling is `eq(c.age, 30)`, and a
     join reads `q.who`. This also dissolves the second, independent blocker WI-1128 recorded (one
     sentinel symbol shared by both `join` binders, able to say neither which row it meant nor match
     the sole-column arm over a merged column list): there is no per-binder keying to get right when
     there is no whole-row hole.
   - **The ctor reduction boundary became a FIXPOINT.** The residual `Without` leaves is now an
     operand `Concat` can merge, but the boundary made ONE pass over `TYPE_CTORS` and a ctor whose
     operand is a sibling DEFERS on it — so `Concat[A = Without[…]]` stalled anyway. The first
     attempt reordered the array to put `Without` first, which fixed that shape and **regressed its
     dual** `Without[T = Concat[…]]`, four lines of ordinary source that had loaded clean (found in
     review, measured both ways). The two are duals and no total order satisfies both, so the reorder
     was reverted and the boundary iterates to a fixpoint instead. That is what makes "`Concat` and
     `Without` are inverses at every arity" true rather than merely unblocked, and both directions
     are pinned.
   - **`Concat` was the one schema producer not routed through `relation_schema_type`** (review-found).
     With a `Unit` operand contributing an empty field list, its merged result could be empty — and an
     empty *named tuple* `()` is not the `Unit` a zero-column row actually materializes as. Merging two
     membership relations typed as `Relation[T = ()]`, and `Membership` over it reported an empty
     free-column list: this ticket's own defect, one arity further down. Fixed and pinned.
   - **WI-776's 1-collapse diagnostic was deleted**, not reworded. It explained an
     `expected (a: Int64), got Int64` pair in which both sides were correct — the two faces of the
     collapse. Nothing computes a bare element where a one-field tuple is expected any more, so every
     surviving instance of that pair is an ordinary author error whose two rendered types state the
     whole fault.
   - **Two recorded limits retired rather than patched**: WI-728's `Unit`-typed column (now refused at
     LOAD, and *without* depending on the `()`-vs-`Unit` typing gap) and WI-1128's unrefusable
     tuple-typed column (now a correct three-column schema, with the four-column declaration a load
     error). Their pins were rewritten to assert the capability, per the discipline each recorded.

   **What is still open and NOT part of this**: `Without[T = Concat[…]]`, the dual of the composition
   above, has no witness in any source and the one-pass order cannot serve both directions. A fixpoint
   over the family (written and measured once, and it works) is the change to make when it acquires
   one; recorded at `reduce_type_ctor`.
6. **Ordering / multiplicity — SETTLED for the relation face, and it now has a NAME** (WI-FFPGD).
   Solution order is still the resolver's search order. Multiplicity is the bag, as this item proposed:
   relation consumption takes the resolver's stream as-is, and `Relation.set` is the explicit collapse.
   What changed is that "the resolver's stream" stopped being one thing. The resolver's OTHER face — a
   query asking what `?t` can be — deduplicates by projecting each solution onto the QUERY's goals, so
   an existential body variable (`tagged(?t) :- check(t: ?t, witness: ?)`) does not multiply answers.
   That projection would erase exactly what this item preserves, so the two faces are told apart by
   `ResolveConfig::dedup_answers`, and `execute_logical_query` — 026.1's sole entry for value-driven KB
   queries, feeding `Relation.splitFirst` and `KB.execute` — is the one caller that turns it off. The
   bag is therefore a *stated* property of the relation entry point rather than a property the resolver
   happened to have. Kernel spec §8.3 carries both faces.
7. **Naming an operation and its relational face — OPEN; original convention WITHDRAWN, explicit
   relation selection PROPOSED.** The original question asked whether a Bool-valued predicate's two
   readings — the intensional relation and the boolean value — need two names, since they coincide in
   arity (unlike a function, whose relational reading is the arity+1 graph, WI-938). Its proposed
   convention (`<name>` the relation, `is<Name>` the boolean) is **withdrawn**: it imposed two declaration
   names and was based on a measurement that conflated a plain predicate with an operation carrying a
   derived relational view. Withdrawing that convention did **not** close the underlying question.

   **A PLAIN CLAUSE-DEFINED PREDICATE NEEDS NO SECOND NAME.** `examples/classic-mini/map-colouring` is
   the design working, with a passing test: `colouring` is a plain `rule`, `main` cites it bare as a
   `Relation[(wa: Colour, …)]` and drains it with `colouring.takeN(20)` — and there is **no boolean
   operation anywhere**. The faces come from **how many columns are bound**: all free enumerates, all
   bound gives `Relation[Unit]` whose non-emptiness *is* the boolean, which `negate`'s contract already
   defines. One name, two readings, chosen by application.

   **What made `Set.member` look like a counter-example was its own declaration.** Measured both ways:
   a pure rule cited where a `Relation` is expected loads clean (`cites_a_relation = true`), while an
   operation carrying the *identical* clauses is refused — because the rule heads land on the operation
   symbol and no `Goal` kind is ever minted (WI-896). So the relation face was unreachable for a
   self-inflicted reason, and a second name would have papered over it.

   **The defect underneath was an API one, and it was fixed instead.** `member(x: T, l: List)` took the
   ELEMENT first, so it could not dot-dispatch — §6.7 binds a receiver to the first parameter, and
   `l.member(7)` was refused `expected List, got Int64`. `List.member` / `Set.member` are now
   `contains(container, element)`, matching `Map.contains(m, key)` and `String.contains(s, sub)`, so
   `l.contains(x)` works. That is one name for one question across the containers — the opposite
   direction from the withdrawn convention, and the reason it is recorded as withdrawn rather than
   deferred.

   **What remains genuinely open** is the one-way gap this exposed, and it is not about naming: a
   body-derived relational reading is served in GOAL position (`bare_bodied_bool_relation` routes a bare
   Bool goal to `eq(op(args), true)`, using the declared `Eq` by construction — the sound path WI-580
   chose) but is **not** a first-class `Relation` VALUE, since `cites_a_relation` needs a `Goal`/`Rule`
   kind. Measured: `List.contains` answers as a goal and does not resolve where a `Relation` is
   expected. So a clause-defined predicate can be cited as a value and a body-defined one cannot.

   **The replacement direction is proposed, not yet decided:** keep ordinary calls operational and add
   an explicit form that selects the same symbol's relational face; treat same-name written rules as
   properties of the operation rather than competing definitions. Proposal 052 intentionally does not
   specify that form yet. Its exact syntax, delayed-call semantics, coherence for bodied and builtin
   operations, and stream multiplicity remain under exploration in
   [Operation and relational rules sharing one symbol](../design/brainstorms/operation-rule-shared-name.md).

   **The one instance the uniform routing cannot serve — `not` (WI-20260820-MH90F).** The goal-position
   rule above is sound because a Bool operation's relational reading IS its graph: `List.contains` and the
   relation it induces have the same extension, and the two faces differ only in how a caller consumes
   them. `not` is the member of the boolean vocabulary where that stops being true, and it is worth
   stating why, because it BOUNDS the replacement direction rather than merely inconveniencing it.

   `anthill.prelude.Bool.not` takes a Bool VALUE and returns one. `anthill.kernel.not` takes a reified
   GOAL (a `Term`) and is a control operator over the search: it SUCCEEDS when its goal has no solution,
   FAILS when it has one, and DELAYS while the goal still carries an unbound variable (floundering) or
   while its inner search only ran out of depth rather than refuting anything (WI-628). Three outcomes,
   and failure is not the VALUE `false` — a failed goal contributes no answer at all. So routing
   uniformly would not re-spell the goal, it would change what the goal says: `eq(Bool.not(P), true)`
   EVALUATES `P` as a boolean expression, where the `P` in `not(empty(?x))` is a goal to be RESOLVED and
   has no value to evaluate.

   The distance is measurable in `sort Bool`'s own law block, which asserts five laws about `not`:
   `not_true` / `not_false`, `not_not`, and both de Morgan directions. They are untagged, so nothing
   rewrites on them today (§5.3) — but they are the DECLARED algebra of the symbol, i.e. what `Bool.not`
   *means*, and one symbol cannot mean that and also mean NAF. Read as goals, none of them survives:

   - `not_true: not(true) <=> false` (and its `not_false` twin) — NAF over a goal that succeeds FAILS,
     and failing is not producing the value `false`. The equation has no goal-side reading at all,
     because neither side is a value.
   - `not_not: not(not(?a)) <=> ?a` — the equation says the two sides are interchangeable, and they are
     not: `?a` BINDS its variables where `not(not(?a))` discards whatever the inner search found, and for
     a non-ground `?a` the inner `not` flounders exactly where `?a` would have bound. Double negation
     under NAF is a check with the bindings thrown away, not an identity.
   - de Morgan — both directions need a goal `and`, and there is no `kernel.and`: goal conjunction is the
     comma (§6.6). Two of the five are not even spellable in goal position.

   **So the replacement direction is bounded, not blocked.** "An explicit form that selects the same
   symbol's relational face" presupposes a symbol whose relational face is the wanted one. `not` has
   none: NAF is not the graph of any function on values, so a `relation(Bool.not)` would select the
   singleton `{false}` — correctly, and uselessly. Two readings under two symbols chosen BY POSITION
   (WI-529 the value side, WI-1046 the goal side) is therefore not a gap in the mechanism this question
   is looking for; it is the right answer for the case where the two readings are two different
   FUNCTIONS. What the explicit form has to serve is the other case — one predicate, two consumptions —
   and its scope statement should say so rather than leave `not` looking like a counter-example to it.

   The third option — fold both into one operator over `Term`, with the Bool case a coercion that reifies
   `b` as the goal `eq(b, true)` — is REJECTED. It loses the law block above, and it costs the value
   side its lowering: an operation body must EVALUATE, and a codegen backend emits `Bool.not` as the
   host's `!`, which it cannot do for a primitive whose meaning is an effect on the resolver's search.

## Out of scope

- The `Branch` effect, `reflect(stream)`, solvers-as-handlers, the `match <solver> case` surface, and
  the eval↔SLD runtime switch — all [027.2](027.2-branch-from-streams.md).
- Direct-style search bodies that re-enter search (nested solve) — 027.2 (needs the switch).
- Scored / best-first consumption — [027.3-scored-branch-effect](027.3-scored-branch-effect.md), surfaced
  as a solver in 027.2.
- Changing the `LogicalQuery` ADT or the resolver (this is a surface + typing + `provides` layer only).
