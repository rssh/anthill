# Effect sets

## Status: Brainstorming draft

How effect *sets* (rows) should work in anthill — representation, kinds, syntax,
and checking. No final decision; this records the exploration, the variant space,
and the leading candidate so it isn't lost in chat.

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
   depend on *runtime* values. The split is what keeps the type system tractable.
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
  principle 2. *(Prior art: rare.)*

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
  (`op_effects(map(f),E) :- op_effects(f,E)`). *(Links / Rémy presence
  polymorphism; Haskell mtl `Member`.)*

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

- **D — effect-set as its own *kind*; rewrite `Function`.** `EffectSet` kind,
  `?E in effects` row-var binders, kinded quantifiers; `arrow.effects` carries an
  `EffectSet`; reconcile `Set`/`EffectSet`/`Function`/`arrow`. *Principled; clean
  kinds; most machinery (new kind + binder syntax).* *(Koka, Haskell
  extensible-effects.)*

- **E — effect-set as an ordinary *sort* + ACI operators (minimal-rewrite middle).**
  `EffectSet` is just a normal sort (already so, via `requires Set[…]`);
  effect-set *values* are `empty`/`insert` terms with **ACI equational laws**
  (Maude-style operator attributes); `Function.E` **stays `sort E = ?`** but
  constrained to `EffectSet`; polymorphism is **ordinary logic-var unification
  modulo ACI**; checking is `Set`'s `subset`/`union`/`member`. *No new kind, no
  `?E in effects` syntax, no `Type` pollution* — basically *complete what
  `effect-set.anthill` already gestures at*. *(Maude ACI sets.)*

- **F — fully inferred, no declared effects.** Signatures don't carry effects;
  the typer derives every expression's effect-set by rules on demand. Maximally
  logic-native, but loses declared/checked signatures (we want `effects ?E`), so
  probably too far. *(Talpin–Jouvelot / region inference.)*

(The earlier "**G** — effects as `ensures` postcondition statements" is **not a
separate variant** — it's B's *declaration-home* sub-axis (`ensures (E in
effects)` homed in the contract), folded into B above.)

Non-starters: **monomorphic-only** (breaks the HOF/stream correctness above);
**SMT-discharged subsumption** (overkill — equational `Set` rules decide subset).

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

1. Make `arrow.effects` carry an `EffectSet` (not `List[Type]`); same for the
   `@` annotation.
2. Decide the concrete value form: ACI-normalized `empty`/`insert` term.
3. Ensure **ACI matching actually fires** during effect checking (via `[simp]`
   or ACI operator attributes) — *the* real semantic commitment.
4. Complete the `Set` laws: recursive `member(x, insert(s,y))`,
   `subset(insert(s,x), t)`, `union(insert(s,x), t)`, etc.
5. Coherent element typing: `Effect[?]` (which `Type`s are effects) vs `Modify[c]`
   being itself a `Type` ("effect = type").
6. `empty()` / `PureFunction = Function[…, E = empty()]`.
7. Kind `Function.E` / the `effects`/`@` variable as `EffectSet` (constrained
   `sort E = ?` for E; explicit `?E in effects` for D).

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
| **B** — `(E in effects)` / `(E not in effects)` | **Links / Rémy** row types with *presence polymorphism* (Present/Absent/poly + presence variables); Haskell **mtl** `Member` / `MonadState` (qualified types) |
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
presence-variable problem (Links/Rémy).

## Driving examples to keep honest

- `List.map`, `List.fold`, `Stream.map` (propagation, eager and lazy);
  `Function.apply … effects E`.
- `Modify[c]` / `Modify[self]` (value-path in effect position; proposal 037).
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
4. Complete the `Set`/`EffectSet` laws; wire `arrow.effects` → `EffectSet`;
   reconcile `Function` ↔ `arrow`.
5. Promote to a numbered proposal; *only then* touch `typing_pass_spec` and
   013's effect-checking.
