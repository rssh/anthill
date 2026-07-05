# Proposal 052: Relations as first-class values (`Relation[T]`)

**Status:** Draft (2026-07-05; rev. 2026-07-05 — WI-638 landed; projection = distribute-dot (`select` retired); effect-row + naming resolved)
**Depends on:** [026.1-value-integrated-kb-queries](026.1-value-integrated-kb-queries.md) (the `execute(kb, LogicalQuery) -> Stream[Solution]` engine — **landed**, `kb/execute.rs` — + the `LogicalQuery` ADT this is the typed face of), [010-query-system](010-query-system.md) (`LogicalQuery` constructors), [004-tuple-sorts](004-tuple-sorts.md) (named tuples — the schema `T`), [022-typing-as-facts](022-typing-as-facts.md) / WI-603 (rule-atom variable typing), **WI-638** (named-tuple field access `row.x` — **delivered**, the single-field `.` surface), **WI-639** (the distribute-dot `x.(f1, f2)` — **filed**, the multi-field projection surface `select` retires into), **WI-300** (rule-body requirement goals — **delivered**, how a clause body's `requires`-carrying ops get their dictionary)
**Related:** [027.2-branch-from-streams](027.2-branch-from-streams.md) (the *effectful* dual — reflecting these streams into the `Branch` effect), [047-effects-as-monads-via-reflection](047-effects-as-monads-via-reflection.md) (`Branch ↦ Stream`), `stdlib/anthill/prelude/logical_stream.anthill` (`LogicalStream`), the provides-dispatch cluster (WI-424 find/map on Iterable, WI-599 finite map/filter, WI-608/609/614 requires/provides views) — the machinery the `provides` edge reuses, kernel spec §4.6 (named tuples) / §6.7 (dot projection — three modes)
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
(no lub) is a **load error**, never a silent widening to `Term`. To **expose** an
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
record: `one ≡ .head`/`.headOption`; `all ≡ the stream itself` / `.toList`.

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
| negation-as-failure | `negate(r)` / `not r` | `negation` | — |
| fix — column = constant (sugar) | `r.fix(x: 1)` | `guarded` + project | drops the column |
| run / consume | *inherited via `provides`* | `execute` | `LogicalStream[T]` |

`union` and `negate` touch no columns, so they keep the infix `|` / `not` sugar (plain operations, per
016). `join`/`where` each take a **row lambda** — there is no `&` join infix, because a useful join
needs a condition, and that condition (like a filter) is the lambda. **Projection** is the distribute-dot
`r.(f1, f2)` and **`fix`** is column-by-key — neither is a lambda op.

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
-- r.(y) lifts the tuple projection over the relation to `projected`; .(y) 1-collapses to the value.
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
| a value, assume present | `.head` | partial — errors per `Stream.head` |
| a total result | `.headOption` | `Option` — `None` = not found |
| all solutions | the stream / `.toList` | empty stream / list |

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
   `T` is the named tuple of the free set in declaration order, **collapsed to the element for one,
   `Unit` for zero**, with each column typed at the **lub across clauses** (§"The schema `T`"). Each
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

## Build path

**Core:**
1. **`Relation[T]` + `provides LogicalStream[T, E]`** — the sort, the provision backed by `execute`
   (lazy `splitFirst`), and named-tuple projection of a `Solution`'s substitution onto the free vars
   (declaration order; 1-collapse / 0-`Unit`).
2. **Rule reference + fix** — resolve a rule name to a `Relation[T]` in **both** citation positions
   (§Naming): applied `Sort.rule(…)` via `rule_id_by_qn`, and the **new bare-qualified arm** —
   `field_access(Sort, ruleName)` on a sort symbol → `Relation[T]` (the one new name-resolution piece).
   Named-argument application (`:`) binds parameters and narrows `T`.
3. **Schema typing** — synthesize `T` from the free set + WI-603 types (column type = lub across
   clauses); type the inherited Stream API at `T` **and the access-effect row `E ⊇ {Error}`** through
   the `provides` edge.

**Increments (one wired `LogicalQuery` constructor + one schema rule each):** join (`conjunction`),
union (`|`, `disjunction`), negate (`not`, `negation`), where (`guarded`) — all four constructors are
**already wired in `kb/execute.rs`**. **Project** (→ `projected`) has no `select` op — it is the
**distribute-dot** `x.(f1, f2)` ⇒ `(f1: x.f1, f2: x.f2)`, lifted over a relation to `r.(f1, f2)` →
`projected` — and because the resolver lowers `projected` as a pass-through, it needs caller-side column
restriction at 052's materialization step. The single-field `x.f` is **delivered (WI-638)**; the
distribute-dot `x.(…)` is **WI-639** — a general §6.7 form (members resolved at *typing*, like WI-638;
result the ordered/named tuple), useful to any tuple consumer, not only relations. Until it lands,
`projected` is reached via a name-keyed row-tuple the typer recognizes.

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
5. **1-field collapse boundary — recommend the typer, single site.** Do the 1-tuple → element collapse
   once, at the schema-typing / projection boundary (`Relation[(board: Board)]` presents as
   `Relation[Board]`); keep the *stored* element as the 1-field record so passing the whole solution
   around round-trips, and treat the collapse as a consumption-site presentation only. Zero → `Unit`.
6. **Ordering / multiplicity** — solution order is the resolver's search order; whether consumption
   de-dupes or preserves multiplicity (bag vs. set) — default to the resolver's stream as-is, documented.

## Out of scope

- The `Branch` effect, `reflect(stream)`, solvers-as-handlers, the `match <solver> case` surface, and
  the eval↔SLD runtime switch — all [027.2](027.2-branch-from-streams.md).
- Direct-style search bodies that re-enter search (nested solve) — 027.2 (needs the switch).
- Scored / best-first consumption — [034-scored-branch-effect](034-scored-branch-effect.md), surfaced
  as a solver in 027.2.
- Changing the `LogicalQuery` ADT or the resolver (this is a surface + typing + `provides` layer only).
