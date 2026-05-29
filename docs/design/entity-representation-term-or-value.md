# Entity representation — hash-consed `Term` vs `Value`, and the `denoted` containment rule

## Status

Design (2026-05-29). **Internal representation only — no external/language
change.** Generalizes the earlier "binder types off the term store" framing:
the real subject is **how entities are represented**, of which arrow/binder
types are one instance. Same category as `occurrence-as-value-type.md`.

## 1. The general question

How is an **entity** — a `Type`, or any sort entity — represented inside the KB?

The schema of an entity is defined in the stdlib, **independent of carrier**.
For types that is `stdlib/anthill/prelude/sort.anthill`: `Type` is a sort whose
entities are `sort_ref`, `parameterized`, `arrow`, `denoted(value: NodeOccurrence)`,
`effects_rows(EffectExpression)`, `named_tuple`, `type_var`, `nothing`, … . The
schema says *what a type is*; it does **not** say how it is stored.

There are two concrete carriers, and an abstraction over them:

- **hash-consed `Term`** (`TermId` in the `TermStore`) — content-addressable,
  structurally canonical, shared.
- **`Value`** (`eval/value.rs`) — runtime representation, including
  `Value::Node(Rc<NodeOccurrence>)` for positional / binder content.
- **`TermView`** (`kb/term_view.rs`) — the trait all three carriers implement
  (`(&KB, TermId)`, `Value`, and `Rc<NodeOccurrence>`). It exposes a uniform
  structural interface — functor + positional/named arguments — so any consumer
  can **walk / "parse" term-like structure identically regardless of carrier**.

So "is a type a `Term` or a `Value`?" is the wrong question. **A type is an
entity described by `sort.anthill`, *carried* by whichever representation its
content allows, and *seen* through `TermView`.** All three carriers can
represent a type; `TermView` is what lets the rest of the system not care
which. The old "types are terms" mantra collapsed schema, carrier, and
abstraction into one word and thereby implied the wrong carrier.

## 2. The carrier rule (`denoted` ⇒ `Value`)

Hash-consing requires content-addressable, structurally-canonical content:
identical structure ⇒ one `TermId`. A **`denoted`** carries a `NodeOccurrence`
(per the schema, `denoted(value: NodeOccurrence)`), and a `NodeOccurrence` is
**not hash-consable** — it is identity-bearing (`Rc`, pointer identity),
positional (span/owner), and alpha-sensitive (when it stands for a bound name).
Therefore:

> **If an entity (transitively) contains a `denoted` occurrence, it must be
> carried as a `Value`, not a hash-consed `Term`.** `denoted` poisons
> hash-consing upward — every container of a `denoted` is a `Value`
> (`Value::Node` carries the occurrence).

Conversely, an entity with **no** `denoted` (e.g. `Int`, `List[T]`,
`Option[Int]`, a *non-dependent* arrow) is ground, content-addressable, and may
be a hash-consed `Term`. The boundary is **`denoted`-containment**, not
type-hood and not (directly) binder-hood.

The rule is **recursive and sort-agnostic** — it follows containment through
*any* sort, not just `Type`. Notably it reaches **`EffectExpression`**: its
`present(label: Type)` / `absent(label: Type)` carry `Type`s, so an effect row
like `{ -Modify[c] }` whose label contains `denoted(c)` transitively contains a
`denoted` → contains a `Value` → **the `EffectExpression` row is itself
`Value`-carried**, and so is any `arrow` / `effects_rows` wrapping it. There is
no "effects are special" exemption; `denoted`-containment propagates uniformly
upward through `Type`, `EffectExpression`, and every container sort.

## 3. Why this subsumes "arrows off `TermId`"

Arrows are not special. A *dependent* arrow — one whose effects or return type
reference a binder, `(c: Cell) -> R ! {-Modify[c]}` or
`() -> Cell ! {Modify[result]}` — contains `denoted(c)` / `denoted(result)`.
By §2 it is therefore a `Value`. A *non-dependent* arrow contains no `denoted`
and stays a hash-consed `Term`.

This also disposes of the alpha-equivalence difficulty cleanly: a dependent
arrow is a `Value` built on the `NodeOccurrence` substrate, **which already
models binders** (`Lambda`/`Let` bind params; `VarRef` references them). So a
binder-referencing effect is a `VarRef`-into-the-arrow's-parameter, and
alpha-equivalence is the `NodeOccurrence` representation's concern — *not* De
Bruijn indices grafted into the hash-consed store, and *not* a special arrow
node. The earlier doc's options A–D were all attempts to solve, at the arrow
level, a problem that the carrier rule solves at the entity level.

## 4. *All* structural operations are `TermView` algorithms

If `Term`, `Value`, and `NodeOccurrence` all implement `TermView`, then **every**
operation over term-like structure should be **defined on `TermView`**, not on
any one carrier — not just some. The full set:

- **`match`** — structural matching of a pattern against a target. `match_view<V:
  TermView>` (kb/mod.rs) already does exactly this on the resolver's binding side
  (proposal 026.1 Q2): a hash-consed candidate matched against a `Value` / row
  without hash-consing it. This is the precedent the rest follow.
- **`unify`** — `unify(a: impl TermView, b: impl TermView)`: walk functor +
  arguments through the view, bind logical variables in the substitution,
  occurs-check — carrier-agnostic. A `Term`-carried type and a `Value`-carried
  type unify by the *same* code. This is the load-bearing content of "types
  behave like terms": they unify with logical variables **through `TermView`**.
- **Alpha-equivalence** — a `TermView`-level relation: two views are
  alpha-equivalent iff their structures match up to renaming of bound positions.
  Cast here it stops being an arrow special case (the earlier doc's A–D) — one
  structural relation over any carrier, ranging over whatever binder the view
  exposes (`NodeOccurrence`'s `Lambda`/`VarRef`, an arrow's params).
- **`walk` / `decompose` / occurs-check / display** — likewise: structural
  traversal is the view's job, so each is written once.

So `TermView` is *the* structural interface and the carrier is invisible to
every algorithm above. The `denoted`/`Value` carrier and these `TermView`
algorithms together replace "De Bruijn in the hash-consed store."

Current state / gap: only `match_view` is `TermView`-based today (resolver
binding side). The **typer's `unify_types`** (typing.rs) is still `TermId`-only,
and there is no `TermView`-level alpha-equivalence. Making types
carrier-polymorphic means moving the typer's `match`/`unify`/alpha-equivalence/
`walk` onto `TermView`. That is the core of the migration.

### 4·1 Two unifications: one substrate, distinct relations

There are two unification-shaped operations today, and they are **correctly
different relations** — `TermView` consolidates their *substrate*, not the
relations:

- **resolution-unify** — `match_term` / `match_view` (mod.rs): exact, syntactic,
  first-order unification of a goal/head against a target. **No subtyping** (SLD
  must not subtype — it would be unsound). Already `TermView`-based.
- **type-check** — `unify_types` / `types_compatible` / `is_subtype` (typing.rs):
  unification **up to subtyping** — arrow **variance** (contravariant param,
  covariant result), `effects_rows` **row-rewriting**, sort_ref↔parameterized
  compatibility. A *separate*, `TermId`-only walker today; shares only
  `Substitution` with the resolver.

Moving the typer onto `TermView` (§8) is **not** merging these. The end state:
**one structural substrate** — `TermView` accessors + `Substitution` + var-bind +
occurs-check — with the **two relations layered on top** (resolution's exact
match; the typer's subtype/unify/row relation, keeping its variance/row logic).
A caveat keeps the *traversals* from fully merging: subtyping is **directional /
variance-flipping**, whereas `match_view` is symmetric exact matching — so the
type side reuses the low-level view accessors but keeps its own variance/row
layer; it cannot simply *be* `match_view`.

## 4a. Choosing the carrier — by creation site

Carrier follows the *need* of the site that creates the type. Three criteria,
which usually agree because the creation site fixes them together:

- **Source-derived & an error target** → **`NodeOccurrence`** (carries span/owner
  → a mismatch points back to what the user wrote).
- **Internally synthesized & not itself the error** (inference vars,
  instantiations) → **`Value`** (no span of its own; errors point at the
  *expression*, which has its own occurrence).
- **Well-known / ground / shared** (prelude types, nominal identities, index
  keys) → **hash-consed `Term`** (sharing + O(1) equality earn their keep).

Floor: `denoted`-containment forces **≥ `Value`** (never `Term`).

A survey of the builders' callers makes this concrete (and the criteria align):

| Builder | Called from | Kind of type | Carrier |
|---|---|---|---|
| `make_denoted` | **`load.rs` only** | source-derived, error target | **`NodeOccurrence`** (and floor satisfied) |
| `make_type_var` | **`typing.rs` only** | synthesized inference var | **`Value`** |
| `make_sort_ref` | mostly well-known nominal | ground identity / index key | **`Term`** |
| `make_arrow_type` / `make_parameterized_type` / `make_named_tuple_type` | **mixed** (load=source, typing=synthesized) | per-site | source→`NodeOccurrence`, synth→`Value`, ground→`Term` |

Sharp finding: **`make_denoted` is called *only* from the loader** — every
`denoted` is born from source, exactly where span-bearing error reporting is
wanted. So `denoted`-containing types naturally want `NodeOccurrence`, which
*simultaneously* satisfies the carrier rule (non-hash-consed) and the
error-reporting goal. A synthesized `denoted` (none today) would be plain
`Value`. The criteria don't compete; the creation site usually settles all
three.

## 5. Today vs target — and why this *is* WI-341

Today `denoted` is built as `denoted(value: Ref(sym))` (`make_denoted`,
load.rs). A `Ref` *is* hash-consable, so today's `denoted`-containing types are
(lossily — see WI-341) hash-consed `Term`s. That is the degenerate case where
the carrier rule doesn't bite because `denoted` isn't yet carrying a real
occurrence.

The moment `denoted` carries a real `NodeOccurrence` (its schema form — the
WI-341 deeper change), the carrier rule **activates**: every `denoted`-container
must become a `Value`. So **"`denoted` → `NodeOccurrence`" and "`denoted`-
containers become `Value`" are the same change.** WI-341 step 1 (result-region
by symbol identity) is delivered and independent; this carrier work is the
general form of step 2, no longer arrow-specific.

## 6. Touch-points (to scope staged work)

- `stdlib/anthill/prelude/sort.anthill` — the carrier-independent schema (no
  change; it already says `denoted(value: NodeOccurrence)`).
- `kb/term_view.rs` — the abstraction; the typer must consume it for types.
- `kb/typing.rs` — `unify_types` / `unify_arrow` / `arrow_parts` /
  `effects_rows_*` / WI-307 row functions become `TermView`-based (carrier-
  agnostic).
- `kb/subst.rs` — `Substitution` already binds `VarId → Value`; a `Value`-carried
  type is `Value::Node(...)` (or a `Value::Type`), no `TermId` required.
- `kb/mod.rs` `make_denoted` + load.rs lowering — emit a `NodeOccurrence`-carrying
  `denoted`; propagate `Value`-ness to containers.
- `kb/region.rs` — result/region effects read `denoted`; the resource becomes an
  occurrence reference (subsumes WI-341 step 1's registry).
- `persistence` / `reflect` / `codegen` — type printing/reflection;
  reflection binds `Value::Node` (the occurrence-as-value-type carrier).
- `scaland` — mirrors the representation (parallel impact).

## 7. Staging

1. **Principle adopted** (CLAUDE.md): types unify via logical variables; carrier
   is not implied by type-hood. (done)
2. **State the carrier rule** (this doc): `denoted`-containment ⇒ `Value`;
   `TermView` is the unification abstraction. (done)
3. **`denoted` carries a `NodeOccurrence`** + containers become `Value`; the
   typer unifies over `TermView`. This is the substantive build, naturally
   driven by §5.5 / 046 dependent effects (the first real `denoted`-in-type
   producers) and absorbing WI-341 step 2.
4. Non-`denoted` entities stay hash-consed `Term` — no migration.

Non-goals: removing hash-consing for facts/rules/nominal identities or for
non-`denoted` structural types; building §5.5 region analysis (046).

## 8. Open questions

1. **Carrier choice** — *which* carrier per site is settled by §4a (source →
   NodeOccurrence, synthesized → Value, well-known → Term; `denoted` floor ≥
   Value). Remaining **mechanics**: does a `Value`-carried type reuse
   `Value::Node(Rc<NodeOccurrence>)` (riding the `NodeKind::Type` slot
   `occurrence-as-value-type.md` reserves) or a dedicated `Value::Type`? And how
   is the source-`NodeOccurrence` vs synthesized-`Value` split realized when the
   same builder (`make_arrow_type`, …) serves both?
2. **Typer over `TermView`** — moving the typer's `match` / `unify` /
   alpha-equivalence / `walk` (all of §4) off `TermId`-only onto `TermView`; how
   much becomes generic vs a type-specific view; where the `TermView`-level
   alpha-equivalence relation lives; interaction with the existing resolver-side
   `match_view`.
3. **Equality / caching** without hash-cons identity for `Value`-carried types —
   what backs the `TermId ==` fast paths (`a_effects == b_effects`, dispatch
   caches)? Per-node canonical hashing / `Rc::ptr_eq` / up-to-alpha memoization.
4. **Containment propagation mechanics** — how is "contains a `denoted`"
   detected and propagated at construction (a built `Value` when any child is a
   `Value`/occurrence), and at the loader boundary?
5. **Reflection / `scaland`** parallels.

## 9. What "done" looks like (staged)

- Principle + carrier rule documented (done).
- `denoted` carries a `NodeOccurrence`; a `denoted`-containing type is a `Value`,
  not a hash-consed `Term`; the typer unifies it via `TermView`.
- A dependent arrow (`(c: Cell) -> R ! {-Modify[c]}`) is alpha-equivalent to its
  renamed twin under unification, with the binding handled by the
  `NodeOccurrence` substrate — no De Bruijn in the global store.
- `Modify[result]` identity carried by the occurrence, not `<op>.result` name
  surgery (subsumes WI-341 step 1).
- v1a row tests, WI-328 lacks tests, WI-314 region tests green; full
  `cargo-test` green.
