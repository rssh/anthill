# Entity representation — carrier and runtime mapping

**Reference (2026-07-13). Internal representation only.** How an entity is
represented in the KB: **which** carrier holds it (§1 — a value element forces
`Value`) and **how** the runtime converts between carriers at the two crossing
points (§4 — the five rules). Distilled from WI-267 / WI-268 / WI-716 so the rules
below aren't rediscovered from inline comments each time.

## 1. `Term` vs `Value` is a carrier difference — the system is carrier-neutral

Same structure, two storage forms:

- **`Term`** — hash-consed `TermId` in `TermStore` (`kb/term.rs`). Persistent; what
  the discrim tree indexes and SLD unifies.
- **`Value`** — runtime representation (`eval/value.rs`).

Both implement **`TermView`** (functor + positional/named args), so nearly all
code walks either identically — it is **carrier-neutral**. Only the two crossings
below convert, and only at the few sites that *require* one carrier: `assert` /
`persist` / query lowering need a real `TermId`; the interpreter builds
`Value::Entity`.

```
Value::Entity  ──alloc_from_value  (Rule 1)──▶  Term::Fn        lower
Term::Fn       ──materialize_entity (Rule 2)─▶  Value::Entity   materialize
```

**Which carrier — a value element forces `Value`.** Carrier follows *content*, not
sort. A `Term` is hash-consed, so every child must be hash-consable too; a child
that is not — a `Value::Node` occurrence, a runtime handle (`Closure`, `Cell`,
`Stream`, …) — poisons the whole structure up to `Value`. Hence: **anything that
transitively contains a value-only element is carried as a `Value`, never a
hash-consed `Term`.** Rule 1 (§4) enforces it — lowering a `Value` whose content
isn't representable is a `LowerError`, never a synthetic term. This is purely a
representation fact, independent of the entity's sort. (The type system's
`denoted` ⇒ `Value` is the *same* rule applied to the `Type` sort — a dependent
type contains a `denoted(NodeOccurrence)`, value-only; delivered under WI-342,
principle in CLAUDE.md.)

## 2. Structural shapes

**`Term`** (variants relevant here):

| variant | shape | meaning |
|---|---|---|
| `Fn` | `{ functor: Symbol, pos_args: [TermId], named_args: [(Symbol, TermId)] }` | entity application; `functor` is the **fully-qualified interned symbol** |
| `Ref` | `Ref(Symbol)` | bare name; **canonical form of a nullary constructor** (Rule 4) |
| `Var` | `Var(Var)` | logic variable — `DeBruijn` in stored rules, `Global` during resolution |
| `Const` | `Const(Literal)` | Int / BigInt / Float / Bool / String / Handle |
| `Ident` | `Ident(Symbol)` | unresolved bare identifier; loader promotes to `Ref` / `Var` |

**`Value`** — mirror carriers + runtime-only handles:

| variant | shape | note |
|---|---|---|
| `Entity` | `{ functor: Symbol, pos: [Value], named: [(Symbol, Value)] }` | runtime entity; structurally isomorphic to `Term::Fn` |
| `Term` | `{ id: TermId }` | a carried hash-consed term |
| `Var` | `Var(Var)` | logic variable |
| scalars | `Int, BigInt, Float, Bool, Str, Unit` | ↔ `Const` |
| `Node` | `Rc<NodeOccurrence>` | occurrence carrier (binder / positional content); **not** hash-consable → never lowers to a `Term` |
| handles | `Closure, OpRef, Stream, Substitution, Map, Cell, Requirement` | no term equivalent → Rule 1 **errors** on these |

**Named-arg order** in both is canonical: **declaration order** for a registered
entity (`entity_field_names`), else `Symbol::index()`. A fact and a matching
pattern therefore carry byte-identical arg order — the discrim tree depends on it.

**`pos_args` is empty in a canonical entity — with one exception.** `Term::Fn` is
the *general* functor-application form (predicates, ad-hoc structures, reflect
encodings — not only entities), so it carries a positional slot. A **registered
entity** (declared fields) normally canonicalizes to **named-only**: lowering /
load desugar each positional arg to its declaration-order field (WI-500/433,
`positional_to_named_plan`), emptying `pos_args`. Positional args survive only in
two cases:

- an **anonymous / ad-hoc structure** — no `entity_field_names`, so there is
  nothing to map positions onto;
- a **reflect encoding form** (`if_expr`, `match_expr`, `apply`, `lambda_expr`, …
  — reflect.anthill) — a *real entity with named fields*, but whose positional
  shape **is** the `Expr`/`Pattern` encoding, so it is deliberately excluded from
  the desugar (`is_reflect_form_functor` / the `anthill.reflect.*` namespace). This
  is the one *entity* that stays positional.

So non-empty `pos_args` ⟺ the functor is one of those two, or a runtime-built value
that has not been through a canonicalizing producer. Over-arity positional on a
registered entity is a `LowerError`, never stored.

**"Before lowering" was doing too much work here, and WI-20260827-T2470 is what it
hid.** The sentence above used to end "or a *pre-canonical* / runtime-built value
before lowering", which reads as though a positional entity is always on its way to
Rule 1 and will be canonicalized there. An **evaluated** entity is not: an operation
body's `some(x)` produced a `Value::Entity` that was compared, unified, and indexed
*as it stood* — `finish_constructor` did not desugar — so `Fn{some, pos:[x]}` met the
`Fn{some, named:[value: x]}` every other producer builds and the four consumers that
key on literal shape (`unify_concrete`'s arity fail-fast,
`sem_eq_values`/`views_structurally_equal`, `DiscrimKey`, hash-consing) read them as
different values. The operation answered nothing, definitely, so NAF over it proved
the falsehood. `Option.optionPure` (`= some(a)`) and `Option.optionMap`
(`some(f(x))`) were both this spelling, along with 47 more sites in `stdlib/anthill`.

The obligation is therefore on **every producer of a value whose shape is its
identity**, not only on the `Value → Term` lowering — Rules 1 and 6 together, and
Rule 6 is the one that was missing. A **reader**-side fix was rejected: the four
consumers above are independent, so teaching each that `f(1)` and `f(x: 1)` denote
one value is four places to drift, where normalizing at the writer states the
rank-among-not-named rule once (`positional_to_named_plan`).

## 3. Value positions vs pattern positions

Facts, rules, and queries share one desugaring (Rules 3–4) so a query matches
stored facts via the discrim tree — but the **absent-optional fill** keys on
whether a position is a *value* or a *pattern* (WI-716):

| position | absent **optional** field | where |
|---|---|---|
| **value** — the loader *produces* it | `none()` | a fact head; an entity-**deriving** rule head |
| **pattern** — matched against facts | `fresh_var` ("matches anything") | a query; a rule-**body** atom; a reflect `Term`-typed field's quoted content |

An absent **required** field always `fresh_var`s; positional→named desugar
(WI-433/500) and nullary→`Ref` (Rule 4) apply everywhere. Over-arity is a
`LoadError` on the loader path (a bad stored fact corrupts the KB) but is left
positional / no-match on a query.

> **Why value ≠ pattern (WI-716).** The absent-field fill is *pattern* semantics —
> "unspecified = matches anything." Right for a query or rule-body atom, wrong for a
> value the loader *produces* (a fact head, or an entity-**deriving** rule head): an
> absent `Option` field there means `none()`, not a var — a var would make the entity
> `∀v. E(field: v)`, which unsoundly unifies `some(?)` (an item omitting the field
> would match a `some(?x)` query, `?x` unbound). One twist: a reflect `Term`-typed
> field holds a **quoted pattern**, not a value, so the value flag is cleared inside
> it — an omitted optional there stays a var (else a stored
> `FactHolds(pattern: E(id: ?x))` would match only `none()`-valued facts). All of it
> stays discrim-aligned: a `none()` value still unifies a pattern's var (so
> `E(id: ?)` finds it) but correctly *fails* `field: some(?)`.

Mechanically: `self.in_value_position` is set by `load_fact` and by `load_rule`
for each head, and cleared by `convert_arg_value` when recursing into a reflect
`Term`-typed field. The expansion at `load.rs:6969` reads it; `convert_query_term`
(`:5314`) always var-fills.

## 4. The six rules

**1 — Lower (Value → Term).** `alloc_from_value` · `kb/execute.rs:273`.
Recurse into fields → desugar positional→named in decl order (WI-500) → sort named
canonically → `KB::alloc` (nullary → `Ref`, Rule 4). Non-representable `Value`
(handles, `Node`, `Unit`, `Tuple`) → `LowerError`, never a synthetic term.
`Value::Term` → id verbatim; `Value::Var` → `Term::Var`.

**2 — Materialize (Term → Value).** `materialize_entity` · `eval/builtins.rs:1454`
(drivers `term_as_entity:1407`, `term_to_value:1543`).
Field schema looked up by **`entity_field_types`** (free-standing entities have no
`entity_parent`, so *not* `strict_parent_sort`) → each field taken by name in
`named_args`, else by index in `pos_args` → absent **or `Var`-valued** `Option`
field → `none()` → missing **required** field → `None` (fail loud). (Since WI-716 a
value position stores `none()` for an absent optional directly, so the `Var`-valued
branch is now a residual safety net for non-value terms — e.g. a materialized pattern.)

**3 — Fill absent named fields.** loader · `kb/load.rs:6969` (fact/rule) + `:5314`
(query).
Every unprovided named field of a registered entity is filled so all facts/patterns
of one functor index uniformly. **The filler keys on value vs pattern (WI-716):** in
a value position (`self.in_value_position` — a fact head or entity-deriving rule
head, but *not* inside a reflect `Term` field) an absent **optional** field gets
`none()`; a pattern (query, rule body, or reflect `Term` content) — and an absent
**required** field — gets `fresh_var(name)`. **Positional args count as provided**
(WI-267). Then sort named by decl order. See §3.

**4 — Nullary constructor form.** `KB::alloc` · `kb/mod.rs:1063`.
A nullary `Fn{c}` of a constructor `c` is stored as `Ref(c)` (gated on
`is_constructor_symbol`) — **one `TermId` for both spellings**; prints bare `c`,
reloads as `Ref(c)`. (WI-511, supersedes WI-267's matcher patch; `WI-267` is a
tracker tag, absent from code — grep WI-436/WI-511.) The `head()` /
`functor_view_head` view bridge still normalizes carriers that bypass `alloc`
(transient patterns, `Value::Node`).

**5 — Option detection.** `is_option_type` · `kb/typing.rs:14202`.
A field's declared type is `parameterized(base: sort_ref(Option), …)`, not a bare
`Option` — so match on the type **head** (`Parameterized{base}` or `SortRef` ==
`anthill.prelude.Option`). Carrier-neutral (`TermView`). This is the gate that
makes Rules 2 and 3 default optionals correctly.

**6 — Build (source → Value / occurrence).** `finish_constructor` ·
`eval/eval.rs` + `anf_flatten` · `kb/resolve.rs` (WI-20260827-T2470).
A constructor APPLICATION written in an operation body is canonicalized where it is
built, not where it is later lowered — same `positional_to_named_plan`, same
rank-among-NOT-named rule, so a mixed `two(2, a: 1)` puts 2 in `b`. Two sites because
two paths reach a body: `finish_constructor` for every call the evaluator reduces,
`anf_flatten` for the arm-body residual the WI-580 unfold builds when the scrutinee is
unground (that one rides as a `Value::Node` into a `unify` goal and is never reified,
so Rule 1 never sees it). Both `Skip` the two exceptions §2 lists. The PATTERN twin of
`anf_flatten` — `fresh_pattern_occ`, same file — already did this, with its own
open-coded copy of the rank rule; that copy gets the MIXED spelling wrong and is
WI-20260827-1F0QP.

> **This rule implements Rule 1's desugar and NOT Rule 3's fill, and that is a gap
> rather than a design.** The loader's canonical form for a declared entity is the
> positional→named desugar **plus** the absent-field expansion — so a rule body's
> `two(a: 1)` indexes as `two(a: 1, b: ?)`, and (WI-716) an absent *optional* field in a
> value position becomes `none()`. This rule does only the first half, so an
> **under-applied** constructor in an operation body keeps a smaller `named_arity` than
> its loader-canonical twin and `unify_concrete`'s `na != nb` fail-fast decides the
> equation FALSE. MEASURED: `operation f() -> Two = two(1)` and `operation g() -> Two =
> two(a: 1)` both answer nothing, the NAMED one included — so the gap is orthogonal to
> the positional axis and pre-dates WI-20260827-T2470. **WI-20260827-XFB56** owns it, and
> owns deciding what an operation body should build for an absent *required* field,
> which is not the same question the loader answers for a pattern.

## 5. Worked example — `WorkItem` round trip

`entity WorkItem(id, description?, context?, acceptance, depends_on?, generates?,
requires_capability?, status)` — `?` marks `Option` (`domain.anthill:77`).
`ToolPasses(tool: String, params: Option[Term])`.

Lifecycle `load → materialize → with_X → alloc_from_value → persist`:

| step | what happens | rules |
|---|---|---|
| load fact | 4 omitted `Option` fields ← `none()` (WI-716); in `ToolPasses("cargo-test")`, `tool` goes named via the desugar, `params?` ← `none()`; `status: Open` → `Ref(Open)` | 3, 4, 5 |
| materialize | `none()` slots read back as `none()`; `Open` → nullary `Value::Entity` | 2, 5 |
| `with_X` | rebuild `Value::Entity`, one field replaced (pure value) | — |
| lower | fields recurse; named re-sorted to decl order; `Open` → `Ref(Open)` | 1, 4 |
| persist | `none()` fields omitted; `Open` prints bare; on-disk shape == load | 1, 4 |

Historically the fragile spot was the **Rule 3 ⇄ Rule 2 handshake**: the loader
injected vars for indexing and materialization stripped them back to `none()` — and
a slip leaked a synthetic var name into a persisted fact (WI-267, and the user-facing
`params: ?params` that WI-716 fixed). WI-716 removed that coupling for facts: an
absent optional is `none()` at storage, so there is no injected var to strip.

## Source map

| Rule | File · symbol |
|---|---|
| 1 lower | `kb/execute.rs:273` · `alloc_from_value` |
| 2 materialize | `eval/builtins.rs:1454` · `materialize_entity` (+ `term_as_entity:1407`, `term_to_value:1543`) |
| 3 fill absent fields | `kb/load.rs:6969` (fact) + `:5314` (query) |
| 4 nullary `Ref` form | `kb/mod.rs:1063` · `KB::alloc`; printer `persistence/print.rs:706` |
| 5 Option detection | `kb/typing.rs:14202` · `is_option_type` |
| 6 build (source → Value) | `eval/eval.rs` · `finish_constructor`; `kb/resolve.rs` · `anf_flatten` |

Lines drift; the code tags `WI-500`, `WI-511`, `WI-436`, `WI-433`, `WI-342`,
`WI-477`, `WI-391`, `WI-109`, `WI-20260827-T2470` are stable anchors.

## See also

- `docs/kernel-language.md` §6.3 — the surface `entity` sugar (points here for the
  runtime mapping).
- CLAUDE.md "Representation note" — the carrier rule at the principle level; the
  type system applies it to `denoted` (a dependent type is `Value`-carried, WI-342).
