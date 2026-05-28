# Effect sets

## Status: Brainstorming draft — **promoted to Proposal 045** (`docs/proposals/045-effect-sets-and-expressions.md`)

How effect *sets* (rows) should work in anthill — representation, kinds, syntax,
and checking. This records the exploration, the variant space (A/B/D/E/F), and
the leading candidate; the committed design (B-presence over E, the `+`/`-`
effect-expression algebra, `effects E = ?`) lives in **Proposal 045**.

## Relates to

- **Proposal 013 — Abstract Effect Parameters** (partially implemented: grammar
  + parse IR + codegen + KB loading; **effect *checking* not done**). 013 built
  the plumbing; this is the *semantics* it deferred.
- **Proposal 003 — Effect Annotations on Arrow Sorts** (`(A) -> B @ E`).
- **Proposal 027 — Effect Handlers and Standard Effects** (`Modify`/`Error`/
  `Branch`; ambient runtime-handler model).
- **Proposal 037** — `Modify[target]` parameter-name effects.
- **WI-301** — "effect-set type args" (reframed here: effect-sets are *not* type
  args).
- **WI-302 / `denoted`** — computed *value* types in type-arg position. Strictly
  orthogonal to effects; mentioned only to keep the boundary clear.
- `docs/proposals/typing_pass_spec.anthill` — `result_effects` / `check_effects`
  / `external_effects` / `union_effects` are exactly this layer.

## What anthill has today — present, but unreconciled

All the pieces exist; none are wired together.

| piece | what it is | gap |
|---|---|---|
| `Set` (`prelude/set.anthill`, 24 lines) | **typeclass**: `empty`/`insert`/`member`/`subset`/`union`/`intersection`/`difference` + **equational laws** (idempotent & commutative `insert`; `union`/`subset` identities) | orphan; only *base-case* laws (no recursive `member`/`subset`/`union` over `insert`) |
| `EffectSet` (`prelude/effect-set.anthill`) | `Set` specialized to `T = Effect[?]` (`sort E = ?; requires Set[S=E, T=Effect[?]]`) | orphan; abstract (no concrete value); not wired |
| `Function.E` (`prelude/function.anthill`) | the effect-set **parameter** of `Function[A,B,E]`; `apply(f,x) -> B effects E`; `PureFunction = Function[…,E={}]` | `E` declared `sort E = ?` (mis-kinded as a sort/type); "encoding of empty effect sets" left open |
| `arrow.effects` (reflect `Type`, `prelude/sort.anthill`) | the effect-set on a function type | `effects: List[Type]`, not an `EffectSet` |
| `effects` clause / `@` (grammar.js:355, 1017) | surface syntax; `_effect_type = simple_type \| parameterized_type \| variable_term` | so **`?E` already parses** in effect position, but unkinded |

So `effects {Modify[c], ?E}` already parses; individual effects (`Modify[c]`) are
already types; `union`/`subset`/`member` already exist as `Set` ops; the empty
set is `Set.empty()`. **Effect *checking* is unimplemented (013).**

## Principles

1. **Individual effect = type.** `Modify[c]`, `Reads[d]`, `Error[T]` live in the
   type lattice. No change.
2. **Effect-*set* ≠ type — but it is *part of (arrow) types*.** `{E1, E2}` is a
   row with its *own* order (subset subsumption `{A} ⊆ {A,B}`), distinct from the
   type lattice; it does **not** belong in `Type` or in type-argument (`[…]`)
   position. It appears specifically as the effect component of **arrow** types
   (and lazy structures carry effects via their *internal* arrows/thunks, so
   arrows are the sole carrier — no need to annotate arbitrary types).
3. **Compile-time / staged.** `Type` and effect rows are compile-time/meta
   entities. This is the *two-level* (object vs meta) split — **not** full
   dependent typing (Idris), where one language unifies terms/types and types may
   depend on *runtime* values.
4. **`Modify[c]` precedent.** A value/path already sits in effect position and is
   well-formed (proposal 037), so "expression in effect position" must be too.

## Why effect *polymorphism* is mandatory: collections & streams

A wrong convention here yields a *wrong* effect-set:

- **HOF propagation (eager).** `map`/`fold`/`filter` over a `List` have *exactly
  the callback's effects* — `apply`'s `effects E` is the canonical case. Without
  "this op's effects = the arg's effects," you under- or over-declare.
- **Lazy streams (deferred).** A `Stream` runs the callback on *consumption*, not
  at `map`-time; the effects are *latent in the stream value*, carried by its
  internal force-arrow (`() -> … @ E`). Attributing them to `map` is wrong;
  dropping them is wrong.

## The variant space

Two axes: **where effect-sets live** (in `Type` / own kind / a plain sort /
nowhere — only relations) × **how polymorphism is expressed** (type-param /
row-var / membership-constraint / inference).

- **A — effect-set ∈ `Type`.** Add an `effect_set` `Type` constructor; `E` stays
  a type-param; reuse `[E = …]` instantiation. *Minimal new code; the quick path
  to making the spec check.* Cost: type-lattice **impurity** (an effect-set in
  the lattice, with `subset` rather than `refines` subsumption) — contradicts
  principle 2. *(Refs: no standard analog — effect systems keep the row a
  distinct kind, not a type-of-values.)*

- **B — effects as *relations* (surface: `allow` / `disallow`).** Track
  membership rather than reifying the set. The natural surface carries the
  permission **modality** that bare `in`/`not in` lack:
  - **`allow E`** — E is *permitted* (upper-bound "may"; `(E in effects)`);
  - **`disallow E`** — E is *forbidden* ("must not" / guaranteed absent;
    `(E not in effects)`).

  **Closed-world**: the `allow`-list *is* the frame — unstated effects are
  disallowed by NAF; explicit `disallow` forbids an effect despite polymorphism
  (a handled effect, or a callback constrained IO-free). Polymorphism via
  **presence variables**; propagation via rules
  (`op_effects(map(f),E) :- op_effects(f,E)`). *(Refs — **effects**: Wadler &
  Blott, “How to make ad-hoc polymorphism less ad hoc”, POPL 1989, and Jones,
  “Qualified Types”, 1994 — effects-as-constraints, the mtl `Member`/`MonadState`
  form; Lindley & Cheney, “Row-based effect types for database integration”, 2012
  — presence/row polymorphism applied to effects in Links. The underlying
  row/presence *technique* originates in **record** typing, not effects — Rémy,
  “Type inference for records in a natural extension of ML”, 1989; Leijen,
  “Extensible records with scoped labels”, 2005.)*

  **Declaration-home sub-axis:** a dedicated clause, *or* **homed in `ensures`**
  (the "postcondition" form) — no new clause, just a membership predicate over a
  special `effects` term denoting the op's own row:

  ```
  operation set(target: T, value: T) -> Unit
    ensures (Modify in effects)          -- allow:   Modify permitted
                                         -- (Modify not in effects) = disallow
  ```

  with `allow E` / `disallow E` as modality sugar for
  `ensures (E in effects)` / `ensures (E not in effects)`. Read closed-world, and
  **project to the effect-set value on the `arrow` type** (first-class functions
  / `apply` need effects *on the type*, not in an `ensures`). This unifies effects
  with `requires`/`ensures`.

  **Caveat (B folds into E):** *pure*-B — no effect-set value at all — conflicts
  with the spec's value-style (`result_effects` returns a set; `arrow.effects`
  stores one). In practice B rides on **E**: `allow` = `member`, `disallow` =
  `not member`, subsumption = `subset`. So B is the relational/permission
  *surface*; E is the value *representation* under it.

- **D — effect-set as its own *kind*; rewrite `Function`.** `EffectExpression`/
  `EffectSet` kind, `?E in effects` row-var binders, kinded quantifiers;
  `arrow.effects` carries an `EffectExpression` (denoting an `EffectSet`);
  reconcile `Set`/`EffectSet`/`Function`/`arrow`. *Principled; clean kinds; most
  machinery (new kind + binder syntax).* *(Refs: Leijen, “Koka: Programming with
  Row-Polymorphic Effect Types”, MSFP 2014, and “Type-Directed Compilation of
  Row-Typed Algebraic Effects”, POPL 2017; Kiselyov, Sabry & Swords, “Extensible
  Effects”, Haskell 2013, and Kiselyov & Ishii, “Freer Monads, More Extensible
  Effects”, 2015; Hillerström & Lindley, “Liberating Effects with Rows and
  Handlers”, 2016.)*

- **E — effect-set as an ordinary *sort* + ACI operators (minimal-rewrite middle).**
  `EffectSet` is just a normal sort (already so, via `requires Set[…]`);
  effect-set *values* are `empty`/`insert` terms with **ACI equational laws**
  (Maude-style operator attributes); `Function.E` **stays `sort E = ?`** but
  constrained to `EffectSet`; polymorphism is **ordinary logic-var unification
  modulo ACI**; checking is `Set`'s `subset`/`union`/`member`. *No new kind, no
  `?E in effects` syntax, no `Type` pollution* — basically *complete what
  `effect-set.anthill` already gestures at*. *(Refs: Clavel et al., “All About
  Maude”, 2007, and Meseguer, “Conditional Rewriting Logic as a Unified Model of
  Concurrency”, 1992 — ACI operator attributes + equational matching; Stickel,
  “A Unification Algorithm for Associative-Commutative Functions”, JACM 1981.)*

- **F — fully inferred, no declared effects.** Signatures don't carry effects;
  the typer derives every expression's effect-set by rules on demand. Maximally
  logic-native, but loses declared/checked signatures (we want `effects ?E`), so
  probably too far. *(Refs: Lucassen & Gifford, “Polymorphic Effect Systems”,
  POPL 1988; Talpin & Jouvelot, “The Type and Effect Discipline”, 1992; Nielson
  & Nielson, “Type and Effect Systems”, 1999.)*

(The earlier "**G** — effects as `ensures` postcondition statements" is **not a
separate variant** — it's B's *declaration-home* sub-axis (`ensures (E in
effects)` homed in the contract), folded into B above.)

Non-starters: **monomorphic-only** (breaks the HOF/stream correctness above);
**SMT-discharged subsumption** (overkill — equational `Set` rules decide subset).

## Effects are *expressions*, not sets — denoting effect-sets

What `effects` / `@` / `arrow.effects` / `Function.E` carry is an
**`EffectExpression`**, *not* an `EffectSet` directly. The expression language is
the effect algebra: atoms (`{E1, E2}`, `*`, `{}`, a row variable `?E`, *or a
computed call* such as `result_effects(br)`) combined by `∪` / `\` / `-` / `∩`.
It **denotes** an `EffectSet` — its normal form under the `Set` + ACI laws
(possibly still symbolic if it contains a row variable). Checking is *normalize,
then subsume*.

This is the **effect-level analog of `denoted`** (WI-302): a *type* can be denoted
by a compile-time expression; an *effect-set* is denoted by a compile-time effect
expression. Same staged/two-level shape — the expression is meta-level,
normalized to the `Set` value (E). It also fits the spec directly:
`result_effects(br)` is exactly a computed effect-expression. So the
representation is two layers: **`EffectExpression`** (carried / surface — ops +
variables + computed calls) → **`EffectSet`** (its `Set`-value denotation, E).

## Key insight: `Set` + ACI equational laws is the substrate

The `Set` typeclass already provides exactly the effect-row vocabulary the
variants need — `member` = `(E in)`, `subset` = subsumption (`actual ⊆ declared`),
`union` = composition / `union_effects`. And **set semantics comes from
equational laws** (idempotent + commutative `insert`), not a bespoke algorithm.
That reframes the scary part:

- **"Row/AC unification" → equational matching modulo ACI.** Associative-
  commutative-idempotent matching is the **Maude** approach, and it's what
  anthill's equational / `[simp]` engine (WI-139 / proposal 043) is for — far
  more native than grafting row-unification into the resolver.
- **Open rows + row vars fall out of the term form.** Effect-set value =
  `insert(insert(empty(), Modify[c]), …)`; a **row variable** is a logic var
  `?E`; an **open row** `{Modify[c] | ?E}` is `insert(?E, Modify[c])`. Matching
  these needs the ACI laws to fire.

**B folds into E (and pure-B conflicts with the spec).** Once an effect-set is a
`Set` *value* (E), B's relational surface is free:
`(E in effects)` ≡ `member(E, S)`, `(E not in effects)` ≡ `not member(E, S)`
(NAF), subsumption ≡ `subset`, composition ≡ `union`. The only version of B that
*conflicts* with E is **pure-B** — *no* effect-set value at all. But the spec is
already value-style (`result_effects(br)` *returns* a set; `Function[E = …]`
binds to it; `arrow.effects` stores one) *and* relational (`union_effects` is a
3-place relation). E supports that mix natively; pure-B can't (nothing to return
/ store), so it would force a value→relational spec rewrite for no clear gain.
⇒ **treat B as the relational surface layered on E, not as an alternative to it.**

## Surface syntax (cross-cutting — applies across A/D/E)

- **`@ <row>` on arrow types.** `(A) -> B @ E`; effects are part of *arrow* types
  only (lazy structures carry them via internal arrows). No effect-sets in `[…]`.
- **Effect-set literal.** closed `{ Modify[c], Reads[d] }`; open / tail-var
  `{ Modify[c] | ?E }`; empty `{}` = `Set.empty()`; single `E` (sugar). **Use
  `Set[Type]`, not `List[Type]`** — effects are unordered & idempotent, which
  `List` misrepresents; `Set` matches the ACI semantics (whether to give it a
  delimiter distinct from value `set_literal` is open).
- **Effect-set operations — the lattice** (effects ordered by `subset` ⊆;
  `sort.anthill` already declares `Lattice[T = Type]`):
  - `{}` — **bottom** (pure); the closed-world default.
  - `*` — **top** ("any/all effects"; `S ⊆ *` always). The gradual / FFI /
    untyped escape hatch, and the *opposite pole* from the `{}` default.
    Distinct from a row variable `?E` (which is bounded — binds to *some*
    concrete row — whereas `*` is the universal set). Not in `Set` yet → add as
    the universal element.
  - `∪` (`union`) — **join**: composition (sequential effects), HOF propagation
    (= the spec's `union_effects`). The workhorse.
  - `∩` (`intersection`) — **meet**: `Set` has it, but its effect meaning is the
    unusual *must / common-to-all-paths* (lower bound); branch typing uses `∪`,
    not `∩`. Keep for lattice completeness, but it's **not** part of core
    checking (which is `⊆` + `∪`) and offering it invites misuse.
  - `\` (`difference`) — **bounded negation = handler discharge**: handling `E`
    turns row `S` into `S \ {E}`, so `\` is exactly the *type of a handler*
    (proposal 027). The useful negation operation.
  - `⊆` (`subset`) — **the order**: subsumption (`actual ⊆ declared`).
- **Negation = `* \ S`, representable as a *symbolic co-finite set*.** The effect
  universe is **open** (new effect kinds declarable), so you never *enumerate* a
  complement — but `* \ S` is a fine symbolic value. Example:
  `effects (* - Modify[kb])` = *"may do anything except touch kb"* — the
  co-finite surface for `disallow Modify[kb]` ("does not write to kb").
  **Checking reduces to membership negation:** `subset(X, * \ S) ⟺ X ∩ S = {}`
  (none of `S` in `X`), decidable even over the open universe. So the
  representable effect-sets are **finite or co-finite** (`* \ finite`) — a Boolean
  subalgebra: `{}`/`*` bounds, `∪` join, `\` difference/complement, `⊆` order.
  - The genuinely *hard* negation is **not** these co-finite *constants*
    (decidable) but `not in` over a **row variable** `?E` — asserting absence on
    an *unknown* tail needs a presence variable (hard-problem #1).
  - `\` over a *finite* `S` doubles as **handler discharge** (`S \ {E}`,
    proposal 027).
- **Binders.** `?E in effects` as a kind-annotated binder (vs the mis-kinded
  `sort E = ?`), optionally generalized to `?v in <domain>` (`?T in Type`,
  `?E in effects`, …) to unify the three things anthill spells three ways. (Only
  needed in the strict-kinding D; E can leave `Function.E` as a constrained
  `sort E = ?`.)

## Leading candidate & ranking

**E** is the sweet spot: principled (effect-set is a `Set`-sort *value*, not a
`Type`), least invasive (`Function` barely changes; reuse equational ACI +
ordinary unification + the existing `Set`/`EffectSet`), and it *gives B's
relational surface for free*. **D** = E made stricter with explicit row-kinding /
binders (cleaner kinds, more ceremony). **A** = the quick-but-impure shortcut
(and **A→D/E later is a breaking change** — pulling effect-set back out of
`Type` — so A risks rework). **pure-B / F** = the value-free / inferred edges,
which the spec's value-style resists.

So the menu is **E ▸ D ▸ A** for the *representation*, with **B as the relational
/ permission surface over E**.

**The "declaration-home" axis collapses — it's sugar, not a fork.** In a
refinement/contracts view a **type *is* shorthand for a pre/post predicate**
(`x: Int` is a refinement; `-> Y @ E` is a postcondition about result + effects).
So `@ E` on a type, `ensures (E in effects)`, and `allow`/`disallow` are
**interchangeable surfaces over one predicate** — the effect-row contract
(`member`, checked by `subset`). This is especially natural in anthill ("types
are terms" → a type is first-class data that can *be* a predicate). The only
reason the *type* surface stays load-bearing: a **function value's contract must
travel with the value** — a named op can use `ensures`, but an anonymous lambda
passed to `map` carries its pre/post (incl. effects) on its *type*. So the type
form is the *value-attached* sugar (mandatory for first-class functions);
`ensures` is the ergonomic form for named ops; both desugar to the same thing.

Net leaning: **one notion — an effect-row contract predicate (= `Set`
membership, checked by `subset`) over the E representation — with `@ E` /
`ensures (E in effects)` / `allow`/`disallow` as interchangeable sugars.**

## Reconciliation plan (mostly wiring, given E)

1. Make `arrow.effects` carry an `EffectExpression` (not `List[Type]`) — denoting
   an `EffectSet`; same for the `@` annotation.
2. Decide the concrete value form: ACI-normalized `empty`/`insert` term (the
   `EffectSet` denotation of the `EffectExpression`).
3. Ensure **ACI matching actually fires** during effect checking (via `[simp]`
   or ACI operator attributes) — *the* real semantic commitment.
4. Complete the `Set` laws: recursive `member(x, insert(s,y))`,
   `subset(insert(s,x), t)`, `union(insert(s,x), t)`, etc.
5. Coherent element typing: `Effect[?]` (which `Type`s are effects) vs `Modify[c]`
   being itself a `Type` ("effect = type").
6. `empty()` / `PureFunction = Function[…, E = empty()]`.
7. Kind `Function.E` / the `effects`/`@` value as an `EffectExpression` over
   `EffectSet` (constrained `sort E = ?` for E; explicit `?E in effects` for D).

## Hard problems (intrinsic to any effect system, just relocated)

1. **Negation + polymorphism.** `(E not in effects)` is sound only on a *closed*
   row; for a partly-unknown polymorphic row, "absent" can't be discharged
   locally — it must propagate to callers (the classic scoped-labels / presence
   problem; presence variables exist to solve exactly this).
2. **Propagation as resolution.** If `op_effects` is computed by rules,
   effect-checking joins SLD resolution — with the usual termination/decidability
   questions.
3. **Open vs closed rows** and how `union`/`subset` interact with both under ACI.

## Prior art / analogs

| anthill option | closest prior art |
|---|---|
| **D / E** — effect-set value, rows + unification | **Koka** (row-polymorphic effects, scoped labels, HM row unification); Haskell **extensible-effects** (`polysemy`/`fused-effects`/`effectful`, `Eff '[…]` open-row tail var); PureScript `Run`; **Frank**; **Maude** ACI sets (the equational route) |
| **B** — `(E in effects)` / `(E not in effects)` | *effects*: **Links** row-based effects (Lindley & Cheney 2012); Haskell **mtl** `Member`/`MonadState` (Wadler & Blott 1989, Jones 1994 — qualified types). The *presence/row technique* it uses is from **record** typing (Rémy 1989; Leijen 2005), not effects. |
| **A** — effect-set as a type-of-values | rare; most languages keep the row its own thing |

**Handlers ⟹ effects.** Any language with effect handlers is an *effect* system,
so **Effekt** sits with **Koka / Frank / Eff** — its "capabilities" are merely
*how it delivers handlers* (reified + passed explicitly/lexically) vs anthill's
*implicit-ambient* handlers (proposal 027). Both are effect systems.

The one genuinely different thing is **Scala 3 capture checking**: **no
handlers** — a capability is a plain *resource value* (`FileSystem`, `CanThrow`)
used directly, and the system tracks **which capabilities a value captures /
whether they escape scope** (an escape/aliasing discipline over *values*, not
effect interpretation). It answers "where do capability *values* flow?", not
"what effects happen," so it's a *different axis* — out of the table above.
(NB anthill's own capability flavor is `Modifiable[T = X]` + a registered handler
— "authority to `Modify` X exists" — a separate *gate*, distinct from the row.)

Origins: **Talpin–Jouvelot / Gifford–Lucassen** type-and-effect (region/memory
inference, late ’80s–’90s). **OCaml 5** has effect *handlers* but **untyped** —
the typing is the open part (≈ us). Lessons: D/E's "row unification" is a known,
shipped technique (Koka) — and via `Set`+ACI it's *equational matching* you
already have machinery for; B's `not in`-on-open-rows is exactly the
presence-variable problem — presence variables from records (Rémy 1989), applied
to effects in Links (Lindley & Cheney 2012).

## Driving examples to keep honest

- `List.map`, `List.fold`, `Stream.map` (propagation, eager and lazy);
  `Function.apply … effects E`.
- `Modify[c]` / `Modify[self]` (value-path in effect position; proposal 037).
- **"this function does not write"** — `disallow Modify` / `ensures (Modify not
  in effects)`: a *guaranteed* absence (not just NAF-default "unmentioned"). On a
  polymorphic op it must constrain the callback's row to exclude `Modify` *and*
  propagate to callers — i.e. it forces real **negative / presence-variable**
  support (hard-problem #1), not just positive membership. A hard requirement.
- The spec's `type_check_operation` (`result_effects(br)`, `union_effects`,
  `check_effects`, `external_effects`) — the consumer that must check under
  whatever we pick (and which is already value+relational).

## Non-goals / boundaries

- **`denoted` (WI-302)** is value-computed *types*, not effects — orthogonal,
  lands independently.
- Effect *handlers* and the runtime catalog are proposal 027; this is the
  *static* (compile-time) effect-row language.

## Next steps

1. Confirm the leading candidate (**E** representation + **B**'s effect-row
   contract predicate), and which **interchangeable sugars** to offer for it
   (`@ E` on the type — mandatory for function values; `ensures (E in effects)`;
   `allow`/`disallow`) — a surface choice, not a semantic fork.
2. Pin syntax: `@ <row>` on arrows; `Set[Type]` literal (closed/open/empty);
   binder (constrained `sort E = ?` for E, or `?E in effects` for D); the
   `ensures (E in effects)` / `allow`/`disallow` surface + its closed-world (NAF)
   reading.
3. Resolve the hard points: ACI matching fires; `not in` / open-row soundness;
   `op_effects` rules vs resolution.
4. Complete the `Set`/`EffectSet` laws; wire `arrow.effects` → `EffectExpression`
   (denoting `EffectSet`);
   reconcile `Function` ↔ `arrow`.
5. Promote to a numbered proposal; *only then* touch `typing_pass_spec` and
   013's effect-checking.

## Operation effect-parameters — kinding `E` in `op[…]`  *(added 2026-05-27, firming up 045)*

**Problem.** An operation's type-parameter list can mix a *type* parameter and an
*effect-set* parameter:

```
twice[A, B, E](f: A => B @ E)        -- A, B : types ;  E : effect-set (a row)
```

`A`, `B` are kinded as types; `E` is an effect-set — a **different kind**
("effect-set ≠ type", Principles §2). How is `E` distinguished / kinded inside
`[…]`? The sort-level `effects E = ?` binder and **by-position** binding already
cover the common cases (`Function`, `Stream`, `map`); this is the *free
standalone operation* case. (Tracked as **WI-318**; 045 §2.1 sketches a
candidate.)

Variants — 1–3 from the question, 4–6 added:

1. **Bare list, kind by use.** `[A, B, E]`; the loader kinds each entry by *how
   it is used* (an `@ …` / effects position ⇒ effect-set, a type position ⇒
   type). `?E` already parses in effect position today, just unkinded — this lets
   position assign the kind. **+** no new syntax. **−** needs kind-inference + a
   consistency check (error if `E` is used both ways); the list no longer states
   the kinds at a glance.

2. **Effect-set = a recognised sub-kind of `Type`.** `effects E = ?` ≡
   `sort E = ?` + `fact is_effect_expression(E)` — *or* an `EffectExpression`
   **variant of `Type`**, the way `named_tuple` already is. Then `[A, B, E]` is
   uniform (all type-params) and `E` is the fact-marked one. **+** reuses *all*
   type-param machinery (instantiation `[E = …]`, binder, unification); a real
   precedent ("if named tuples can be a special `Type`, why not effect
   expressions?"). **−** it **re-merges** the kinds 045 §1 split apart (that split
   was the *root-problem fix*), and reverses G1's just-landed choice to give
   `EffectExpression` its **own sort** — under (2) it becomes a `Type` variant and
   `arrow.effects` is a `Type`. (This is the doc's variant **A** — "reuse the
   type-param slot" — made principled with a marker fact.)

3. **Explicit marker in the list.** `twice[A, B, @E]` — reuse the arrow `@`; or
   `twice[A, B, effects E]` (the `effects` keyword, 045 §2.1). **+** explicit; the
   list states the kinds; no inference. **−** small grammar addition; two possible
   markers (`@` vs `effects`) to choose between.

4. **Kinded quantifier.** `twice[A, B, E: Effects](…)` — a *kind ascription*, the
   general form the doc's variant **D** names ("kinded quantifiers"). **+** uniform
   and future-proof (any later kind — `R: Region`, `N: Nat` — uses the same slot);
   explicit. **−** the most machinery (a kind grammar + kind-checking), heavier
   than a single marker for the one kind we have today.

5. **Separate channel — don't mix kinds in one list.** Effect params get their own
   home: an operation-level `effects E = ?` clause (no `[…]` entry), or a second
   bracket `twice[A, B]{E}(…)` (types in `[…]`, effect-sets in `{…}`, echoing the
   `{…}` set literal). **+** each list stays single-kind (no inference, no
   ambiguity). **−** more surface; `{…}` overloads the set-literal braces.

6. **No list entry — bind by position only** (045 §3). Don't list `E` (or even
   `A, B`): the signature's free variables are implicitly quantified, kinded by
   position — `twice(f: A => B @ E)` binds `A, B` (type) and `E` (effect) from
   `f`'s type. **+** zero ceremony for the polymorphic case (which dominates).
   **−** needs implicit type/effect-var quantification (today `[…]` is explicit);
   no at-a-glance parameter list.

**The crux** (rippling through all six): **is an effect-set a kind *distinct from*
`Type` (own sort — G1's `EffectExpression`; variants 3/4/5/6) or a *recognised
sub-kind of* `Type` (variant 2)?** 045 §1 and the landed `EffectExpression` sort
take the distinct-kind line; variant 2 is the one-kind alternative — attractive
precisely because the param-list problem then *vanishes* (effect params are type
params), at the cost of re-merging the kinds and redoing G1. Decide this in
WI-318 *before* the grammar, since it also redirects G1.

**Lean (for WI-318):** holding "effect-set ≠ type" (consistent with §1 + G1), the
**kinded quantifier (4)** subsumes (3) and generalises, with **by-position (6)** as
the no-ceremony default — don't *require* a list entry when `E` comes from a
parameter; when a free op genuinely binds one, write `[…, E: Effects]`. Variant
**2** is the serious counter-proposal, worth taking *only if* we accept
effect-expressions as a (marked) kind of `Type`. (The next chapter revisits this
from first principles and shows the *phantom* worry largely dissolves.)

## Are effect-expressions *types*? — the runtime-mirror argument  *(added 2026-05-28)*

The operation-effect-parameter question above hinges on a deeper one: **is an
effect-expression a kind distinct from `Type` (own sort — G1's `EffectExpression`)
or a recognisable sub-kind of `Type` (variant 2)?** The classical test is "a
type classifies runtime values with operations." Working that test through for
effect-expressions reshapes the answer.

### Two value-classifier readings, and 027 today

If effect-expressions classify runtime values, *what* values? Two coherent
readings, both with PL precedent:

- **Reading 1 — handler configuration.** A value of type `{ Modify[c], Error[T] }`
  is a *handler bundle* supplying those effects; `with(b, body)` passes it as a
  first-class value. Eff / Frank / multicore-OCaml live here.
- **Reading 2 — effect-record / dictionary.** Each effect is a record of its
  operations (`Modify.get`, `Modify.set`); the set is a composite dictionary.
  Type-class / Wadler–Blott qualified-types lineage; also the older `Set + ACI`
  view that 045 pivoted away from.

**Anthill today (027) is *neither*** — handlers are *ambient* (registered on the
`Interpreter`), not values you bind. So no runtime value has type `{ Modify[c] }`
*as anthill currently runs*. That is where the "phantom Type variant" objection
originally came from — and it was contingent on 027 staying ambient, not
fundamental.

### Type-level rows vs runtime representation — decoupled

A common confusion needs disposing of: 045's row-unification pivot picked **rows
over Set/ACI** at the *type level*. That is **independent** of the runtime
representation of effect-set values:

- Typed *by a row directly* — the value's type *is* the row — same row machinery
  applies; runtime can be a dictionary or a chain or anything. **Compatible** with
  the pivot. (Haskell type classes do exactly this: row-of-constraints types +
  dictionary passing.)
- Typed *by `Set[Effect[?]]`* — a parameterised `Set` value — would reintroduce
  Set/ACI *as a second type-level mechanism* alongside rows. *That* is what 045
  dropped.

So Reading 2 doesn't conflict with the pivot as long as the value's type *is* the
row, not a `Set[Effect]`. Type-level checking and runtime representation describe
one algebraic object via different representations.

### The row-distinctive algebra: lacks and the tail *gate* operations

An effect-expression isn't an effect *set*: it carries **present labels**, a
**lacks** set, and an **open tail**. A runtime mirror's algebra splits in two —
the set-common ops plus the row-distinctive ones that a set cannot express:

- *Constructors / observers (set-common, mirror §3):* `empty`, `present(K)`,
  `absent(K)`, `open(ρ)`, `merge`, plus observers on three dimensions
  (`presents` / `lacks` / `tail`).
- *Row-distinctive:* `forbid(r, K)` (the lacks dimension as an op),
  `close(r)` (commit the tail), `extend(r, K)` (**gated** by lacks + tail),
  `subsumes(a, b)` (respect `b`'s lacks, extend its tail), `unify(a, b)`
  (fails on `+K`/`-K` clash).
- *Operational (only when the value carries handlers):* `with(b, body)`,
  `lookup(b, K)`.

The key insight: **lacks and the tail aren't decorative data, they *gate* the
operations themselves.** A set's `insert` is unconditional; a row's `extend` is
permitted only when lacks and tail allow. A set's `union` is total; a row's
`merge` *fails* on present/absent clash. Erase lacks and the tail and the row
algebra collapses to the set algebra — the row-distinctive ops vanish.

### Canonical pattern: `{?E, -Modify[xs]}`

The interesting row-with-lacks pattern in practice is an **open tail + a
targeted lacks**:

```
for_each[T, E](xs: List[T], f: T -> Unit @ {?E, -Modify[xs]}) -> Unit @ ?E
```

`for_each` accepts a callback that may do *arbitrary* effects (the open tail
`?E`) but is *guaranteed not* to mutate `xs`. The lacks prevents the iteration
from concurrently mutating the very list being iterated; the tail keeps
`for_each` composable with any effects. Compile-time, zero runtime cost. A plain
set cannot even *spell* the guarantee — this is what justifies the row-with-lacks
apparatus over the set algebra.

### Runtime-runtime: erased witness + the deny-handler trick

At *execution* time, in a type-erased implementation (Eff, Koka,
multicore-OCaml), lacks and the tail carry **no runtime data** — they're
guarantees enforced before execution and then gone. The runtime witness is the
**dispatch chain** — the actual stack of installed handlers — and the row is its
*static description*. There's no `Row` struct in memory; the chain *is* the
object the row describes.

A natural enrichment: **install a `default-deny` handler at the chain root** for
each lacked effect, so that an attempted invocation of `-K` is an actual
throwable runtime error rather than UB. That gives `-K` an explicit *runtime
witness* — a deny-handler in the chain — belt-and-braces with the static check.

A reified-row alternative — store the `EffectExpression` term alongside the chain
and have `install` / `lookup` consult it dynamically — is possible but duplicates
the typer's work; most algebraic-effect runtimes don't bother.

### What *is* a type? — three readings

The classical / strict / modern / categorical spectrum matters for the answer:

1. **Classical** — types classify runtime *values*; phantom is an edge case.
   *(Effect-rows fail in the ambient model; pass under Reading 1.)*
2. **Specification / erased-tolerant** (mainstream today) — a type is a
   *specification* of value/computation shape; runtime witness *optional*. Java
   generics (erased), Rust `PhantomData`, dependent-type propositions live here.
   *(Effect-rows pass — the spec role is exactly what they play.)*
3. **Categorical** — anything that appears as `T` in `e : T`. *(Trivially pass.)*

Under (2) / (3) — the mainstream modern view — **effect-rows are types**. Runtime
erasure doesn't disqualify them any more than it disqualifies Java's erased
generics.

### `Effectful[R]` — monadic reification as an *additive* option

A clean way to make effect-rows *unambiguously* first-class is to add a monadic
carrier sort:

```
sort EffectsRunner
  effects E = ?
  sort Effectful { sort R = ? }
  operation reify[A, B](f: A -> B @ E, a: A) -> Effectful[R = B]
end
```

`Effectful[R = B]` is a *value* representing an effectful computation that
yields `B` when run; `reify` lifts `f(a)` into the carrier; a
`with_handlers(eff, hs) -> R` discharges it back to a direct result. This is the
Eff / Frank / Free-monad / mtl lineage.

**Direct style and monadic style are two surfaces of the same semantics**, not
competing models. The mechanical translation is Free-monad / CPS, and
algebraic-effect runtimes typically use *both* (direct surface, monadic
interpretation under the hood). The direct form of `reify` is just anthill's
existing `Function.apply : (f: Function[A, B, E], x: A) -> B effects E`; the
monadic form returns a reified `Effectful[R = B]` instead. Same evaluation, two
presentations:

| | direct | monadic |
|---|---|---|
| signature | `apply(f, a) -> B effects E` | `reify(f, a) -> Effectful[R = B]` |
| when effects fire | immediately | when `with_handlers` runs the carrier |

Adding `Effectful[R]` is **additive**, not a replacement — same relationship as
iterators vs `for` loops; both coexist, picked per use site. If anthill exposes
`Effectful[R]`, effect-rows naturally parameterise it (`Effectful[E, R]`) and
become first-class types in every classical sense — no ambiguity, no phantom
worry.

### Verdict — the phantom objection has dissolved

Three converging arguments:

1. **The modern definition of *type* already accommodates effect-rows** —
   runtime witness is optional; the specification role is enough.
2. **There *is* a runtime witness anyway** — the dispatch chain (and an explicit
   deny-handler for `-K`) — even in 027's ambient model.
3. **The `Effectful[R]` direction** (if taken) makes effect-rows unambiguously
   first-class types.

So the phantom-Type-variant objection to variant 2 has **dissolved**. Effect-rows
qualify as types under the prevailing usage; what's left for the kind debate is
*surface ergonomics* — how visible to make them in user-facing param lists —
which is no longer a fundamental disagreement, just a style choice between
**variant 2** (uniform `[A, B, E]`) and **variant 4** (kinded quantifier
`[E: Effects]`).

The whole kind question therefore collapses onto a single design fork that is
downstream of two larger questions: **027's handler model** (stay ambient, or
expose handler bundles as values?) and **whether anthill adopts `Effectful[R]`
reification**. Both are bigger than the param-list itself.
