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

## 4. Unify and alpha-equivalence are `TermView` algorithms

If `Term`, `Value`, and `NodeOccurrence` all implement `TermView`, then the
operations over term-like structure should be **defined on `TermView`**, not on
any one carrier. Two in particular:

- **Unification** — `unify(a: impl TermView, b: impl TermView)` walks functor +
  arguments through the view, binds logical variables in the substitution,
  occurs-checks — all carrier-agnostic. A type backed by a `Term` and a type
  backed by a `Value` unify by the *same* code. This is the genuinely
  load-bearing content of "types behave like terms": they unify with logical
  variables **through `TermView`**, regardless of carrier.
- **Alpha-equivalence** — likewise a `TermView`-level relation: two views are
  alpha-equivalent iff their structures match up to renaming of bound positions.
  Cast at this level, alpha-equivalence stops being an arrow-representation
  special case (the earlier doc's A–D) — it is one structural relation over any
  carrier, and the binder it ranges over is whatever the view exposes (a
  `NodeOccurrence`'s `Lambda`/`VarRef`, an arrow's params). The `denoted`/`Value`
  carrier and the `TermView` algorithm together replace "De Bruijn in the
  hash-consed store."

Current state / gap: `match_view<V: TermView>` (kb/mod.rs) exists and is used on
the **binding side of resolution** (proposal 026.1 Q2 — external rows / `Value`s
unify against hash-consed candidates without being hash-consed). The **typer's
`unify_types`** (typing.rs) is still `TermId`-only, and there is no
`TermView`-level alpha-equivalence yet. Making types carrier-polymorphic means
expressing the typer's unification — and a new alpha-equivalence relation —
over `TermView`. That is the core of the migration.

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

1. **`Value` carrier for a type** — reuse `Value::Node(Rc<NodeOccurrence>)`
   (types ride the `NodeKind::Type` slot `occurrence-as-value-type.md` reserves),
   or add a dedicated `Value::Type`? Note the positional caveat: a source-written
   type occurrence is positional (fits `NodeKind::Type`); a synthesized /
   unified type value is not.
2. **Typer over `TermView`** — how much of `unify_types` becomes
   `TermView`-generic vs a type-specific view; where the new `TermView`-level
   **alpha-equivalence** relation lives and how it ranges over the binder the
   view exposes; interaction with the existing resolver-side `match_view`.
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
