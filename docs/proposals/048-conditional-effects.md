# Proposal 048 — Conditional (guarded) effects

## Status: Draft (2026-06-15)

> **Purpose.** An effect-row element may carry a **guard** — a value-predicate over the
> operation's parameters — so its presence is conditional:
> `effects { Error[DivisionByZero] :- eq(b, 0) }`. At a call site the typer **discharges**
> (drops) a guarded element when it can **refute** the guard (prove `neq(b, 0)`). This unifies a
> partial operation and its "safe" variant into **one** operation: `div` carries the guarded
> error, and a caller that establishes `b ≠ 0` (a literal divisor, an enclosing `if`/`match`
> guard, a KB fact) pays no effect at all. It stays entirely within the effect system — **no
> precondition, no obligation, no proof argument**; effects still just propagate, and discharging
> a guard is an *optional* optimization, not a required proof. It refines proposal-013 effects and
> is the design home for WI-067 (effect discharge from local proofs).

## Depends on
- 013 (effects as sorts and facts), 045 (effect rows / row polymorphism — delivered as WI-307),
  027.1 (value-dependent effects — `Modify[c]` — the existing value-*parameterized* effect this
  generalizes), 026 (expression evaluator — abstract interpretation for literal-divisor guards),
  018 §"Discharge mechanisms" (the existing obligation-discharge taxonomy: abstract interp, KB
  resolution, explicit rules, context propagation, external proofs).

## Relates to
- WI-066 (integer-division `Error[DivisionByZero]`, delivered — the *unconditional* effect; the
  degenerate "guard always holds" case this generalizes), WI-067 (context propagation / discharge
  — **this proposal is its declaration layer + mechanism**), WI-010 / WI-382 (resolver-as-type-
  checker — guard discharge *is* SLD refutation over the row), WI-329 (typer effect-row discharge),
  WI-347 (contracts pre/post — the precondition alternative this deliberately does **not** use).

## Motivation

WI-066 made `Int64.div` / `mod` / `rem` / `divExact` (and `Field.div` / `recip`) carry
`effects Error[DivisionByZero]` **unconditionally**. That is correct but blunt: dividing by a
statically-known non-zero divisor cannot fail, yet still incurs the effect, forcing every caller
to declare or handle an error that can never occur — and the effect then ripples up arbitrarily
deep call chains.

The two obvious escapes are both unsatisfying:

- **Two operations** — `div` (effectful) plus `safeDiv` / `divNonZero` (pure, takes a non-zero
  witness). This does not scale: the same split recurs for `mod`, `rem`, `head`, `nth`, … — one
  "safe" twin per partial op — and it never unifies the *concept*; the relationship between the
  two names is informal.
- **A precondition** — `div(a, b) requires neq(b, 0)`. This conflates two different systems: a
  precondition is an *obligation* (a proof debt at the call site), whereas partiality is an
  *effect*. Mixing `requires` (obligation) with `Error[…]` (effect) in one construct is the
  confusion this proposal avoids.

**Conditional effects** keep everything in the effect system: one operation, whose error element
is *guarded* by the condition under which it can fire, and *discharged* when that condition is
refuted. It generalizes uniformly to every partial operation.

## Design

### Guarded effect elements

An effect-row element may carry a `:- guard`, read exactly like the `:-` in `rule head :- body`
and `constraint inv :- guard` — "this effect, **when** the guard holds":

```anthill
operation div(a: Int64, b: Int64) -> Int64
  effects { Error[DivisionByZero] :- eq(b, 0) }
```

- The element is present **iff** its guard is not refuted.
- Unguarded elements (the overwhelming common case) are unchanged: `effects {Modify[s]}` etc.
- A row may freely mix guarded and unguarded elements:
  `effects { Modify[s], Error[DivisionByZero] :- eq(b, 0) }`.
- The guard is a **value-predicate over the operation's own parameters** — the same value-
  dependence `Modify[c]` already exhibits (an effect parameterized by a value). Here the *presence*
  is value-dependent rather than the *index*; both sit in the 027.1 / 045 family, so guarded
  effects are not a new kind of citizen.

Why effect-first with `:- guard` (rather than `guard -: effect` or `if … then … else {}`):

- `:-` ("if/when") is the dominant anthill convention — every `rule` and `constraint` uses it — so
  no new operator-in-new-context is introduced.
- In a row that lists effects, the effect reads first and the condition qualifies it.
- The **`else` branch disappears**: an unrefuted guard keeps the element, a refuted one drops it;
  there is no second branch to write. (Contrast `if eq(b,0) then Error[DivisionByZero] else {}`,
  which turns the row into a computed expression and adds noise — see *Rejected alternatives*.)

### It is not a precondition — there is no obligation

A guarded effect imposes **no proof debt**. If a caller does not refute the guard, nothing is
forced: the effect simply propagates, to be declared or handled wherever convenient — exactly like
every other effect. Refuting the guard (proving `neq(b, 0)`) is an **optional optimization** that
removes the element. This is the key difference from a precondition / WI-347 contract, which
*requires* discharge at the call. "Submit a proof that `b ≠ 0`" is therefore the wrong mental
model: you never have to; you either let the effect ride or let the typer notice `b ≠ 0`.

### Discharge = refutation (the typer/resolver)

At each call, for every guarded element the typer attempts to prove the guard **false** from the
call context:

- proven false → element **dropped**, the call contributes `{}` for it;
- proven true → element present (and `div(_, 0)` on a literal `0` may additionally be a static
  error);
- **undecided → conservatively present** (contributes the concrete effect).

What the call contributes depends on what each guard's variables are bound to:

- a **ground** argument (a literal, or a value the call context pins down) lets the typer run the
  refutation, yielding a **concrete** contribution (`{}` if refuted, the bare effect otherwise);
- an argument that is the **enclosing operation's own parameter** cannot be refuted there, so the
  guard **propagates upward with the parameter substituted** — `div(a, b)` inside `f(a, b)` makes
  `f` itself carry `Error[DivisionByZero] :- eq(b, 0)`, exactly as the value-dependent
  `Modify[c] ↦ Modify[s]` rewrite already substitutes (the `substitute_ref_syms` path).

So guarded elements are **not** confined to declarations: an operation's *inferred* row can carry
them, and a row collapses to a fully concrete one only at a ground call site. Row unification is
therefore **extended**, not bypassed, to relate guarded rows — see *Lattice of guarded rows
(merge and subtyping)* below.

The sources of a refutation of `eq(b, 0)` (i.e. a proof of `neq(b, 0)`) are precisely the existing
discharge mechanisms (018 §"Discharge mechanisms"), which is why this needs no new *proof* surface:

1. **Abstract interpretation** — a literal divisor: `div(a, 5)` refutes `eq(5, 0)` by evaluation.
2. **Context propagation** — an enclosing `if neq(b, 0) then …` or a `match` arm that has
   eliminated the zero case (this is WI-067).
3. **KB resolution** — `neq(b, 0)` derivable from facts/rules in scope.
4. **Explicit proof** — for hard cases, a `proof` declaration / tactic (025 / 031).

### An effect row is a Horn theory

Each guarded element `Ei :- gi` is its own Horn clause ("`Ei` holds when `gi`"); a row
`{ E1, E2, E3 :- g3 }` is their conjunction — `E1`, `E2` unconditional, `E3` guarded by `g3` (the
`:- g3` binds the **single** preceding element, not the row). Discharge is **SLD refutation** of an
individual `gi`. That aligns guarded-effect discharge with the resolver-as-type-checker direction
(WI-010 / WI-382): the per-element guard check is the *same* resolution engine, not a bespoke
conditional bolted onto the effect checker.

### Lattice of guarded rows (merge and subtyping)

Because guards propagate (above), a row is not always concrete, so the two declarative relations on
rows — the order (**subtyping**) and the join (**merge**) — must be defined on *guarded* rows, not
only concrete ones. Denote a guarded row as a **context-indexed family** of concrete rows: for a
valuation `γ` of the operation's parameters,

```
R(γ)  =  { unguarded atoms }  ∪  { E | (E :- g) ∈ R, γ ⊨ g }
```

— a guarded atom `E :- g` contributes `E` exactly in the contexts where its guard holds.

**Subtyping** is this family lifted pointwise (`R1 <: R2  ⟺  ∀γ. R1(γ) ⊆ R2(γ)`), which per shared
label reduces to **guard entailment**:

```
(E :- g1) <: (E :- g2)   ⟺   g1 ⊨ g2
```

For a fixed label the guards form the Boolean lattice ordered by entailment: `:- false` is ⊥ (pure
/ never fires), `:- true` is ⊤ (the unconditional WI-066 effect), and the row is the per-label
product. Consequences: `{E :- g} <: {E}` always; `{} <:` everything; `{E :- g} <: {}` iff `g` is
unsatisfiable. **A tighter guard is the more-pure subtype.** This — not structural set inclusion —
is the relation the refinement checks must use: operation-override (WI-347) requires the refining
atom's guard to entail the base's (`g_sub ⊨ g_base`); spec-vs-carrier dispatch (WI-350, open
question B) requires `g_carrier ⊨ g_spec`; `requires`-satisfaction likewise.

**Merge (join / least upper bound)** is row union, with same-label guards joined by **disjunction**
(meet, rarely needed, is conjunction):

```
(E :- g1) ⊔ (E :- g2)  =  E :- (g1 ∨ g2)
```

This is what a body accumulating effects from two undischargeable calls computes. The existing
value-level union (`merge_effects`, structural-dedup) already *keeps* both `E :- g1` and `E :- g2`
as distinct atoms — which **is** the unreduced disjunction (present iff either guard holds) — so
the implementation cost is normalization, not a new merge: a row may stay an unreduced multiset
(implicit DNF), and entailment `g1 ⊨ g2` is decided only when subtyping demands it.

**Composition degrades guards through computed arguments.** Substituting a guard's variable with a
*variable* (a threaded-through parameter) keeps it refutable; substituting it with a *computed,
opaque* expression does not. In `lambda x -> op2(op1(x))`, `op1`'s guards thread out over the
lambda's parameter `x`, but `op2`'s guard over its parameter `y := op1(x)` becomes a predicate over
an opaque effectful result — outside the refutable (and arguably the representable) fragment — and
stays conservatively present. The honest law: **a guard survives composition only as far as its
guarded parameter is threaded through as a variable**; the first link of a pipeline keeps its
guards, later links degrade. This bounds how far discharge reaches.

**Decidability.** Both discharge (refute `g`) and subtyping (decide `g1 ⊨ g2`) run on the same KB
resolution engine under the `step_cap` runaway guard (cf. WI-179); an undecided entailment falls
back to treating the guards as opaque/distinct — sound, because that keeps more effects and rejects
more refinements.

### `div`, restated

```anthill
operation div(a: Int64, b: Int64) -> Int64 effects { Error[DivisionByZero] :- eq(b, 0) }
```

- `div(a, 5)` — pure (literal refutes the guard).
- `if neq(b, 0) then div(a, b) else 0` — pure in the `then` branch; the whole op is total.
- `div(a, b)` with `b` unknown — carries `Error[DivisionByZero]`.

There is **no `safeDiv` primitive**: "safe" use is just `div` with the guard refuted; if a reader
wants the name, it is a one-line alias, not a second algorithm. WI-066's unconditional
`effects Error[DivisionByZero]` is the degenerate `:- true` (never-refutable) case; this proposal
refines it to `:- eq(b, 0)`.

### Generalization

The pattern is uniform across partial operations:

```anthill
operation head(xs: List[T]) -> T   effects { Error[Empty]      :- isEmpty(xs) }
operation nth(xs: List[T], i: Int64) -> T effects { Error[OutOfBounds] :- outOfBounds(i, xs) }
```

One mechanism for every partiality — the altitude that two-ops and overloading cannot reach.

## Rejected / deferred alternatives

- **Precondition** `requires neq(b, 0) [else Error[…]]` — conflates an obligation with an effect
  (this session). Rejected.
- **`if guard then E else {}`** effect-expression — makes effects computed values of an
  if-expression; strictly more expressive (the `else` can be another effect) but adds `else {}`
  noise in the common case and turns the row from a declarative set of atoms into an evaluated
  expression that complicates unification. **Deferred** for a future case that genuinely needs
  effect-A-or-effect-B branching.
- **Two operations** (`div` + `divNonZero`) — does not scale, does not unify. Remains available as
  a *user-level alias*, not a primitive.
- **Overloading on a refinement type** (`div(b: NonZero)`) — two implementations under one name,
  plus a refinement-type apparatus and flow-narrowing to retype the argument. More machinery, less
  unification. Rejected as primary.

## Grammar delta

An effect-row element gains an optional trailing `:- guard`. Builds on the `effect_row` node
(WI-375); unguarded elements are unchanged. Two productions extend `_effect_type`:

```
guarded_effect:       seq(_simple_effect, ':-', _term)                 -- bare:  E :- p
paren_guarded_effect: seq('(', _simple_effect, ':-', rule_body, ')')   -- paren: ( E :- p, q )
```

The plain-vs-guarded choice is a clean one-token decision (is the token after the label `:-`?).

The guard binds to the **single preceding element** (per-element, not the row):
`{ Modify[s], Error[…] :- eq(b, 0) }` guards only `Error[…]`.

- A **bare** guard (`guarded_effect`) is a single goal `$._term` (`:- eq(b, 0)`), so the row `,`
  stays the outer separator. It cannot be a bare conjunction `:- p, q` (the second comma reads as
  the next element), nor `:- (p, q)` (`(p, q)` parses as a *tuple*, not a conjunction).
- A **conjunctive** guard parenthesizes the whole element (`paren_guarded_effect`), so the `:-`
  body is a real Horn `rule_body` delimited by `)`: `{ (E1 :- p, q), E2, E3 :- r }`. The parens are
  an *element* delimiter, not a guard wrapper. (Equivalently, name the conjunction as a derived
  predicate — `rule g(?x, ?y) :- p(?x), q(?y)` then `… :- g(x, y)` — which needs no grammar; the
  paren form is the inline convenience.)

`paren_guarded_effect` reopens `(` in effect position, which `_effect_set` otherwise rejects to
fail fast on the `effects (Modify self)` typo (grammar.js: "the single-effect form rejects type
variants that begin with `(`"). The **mandatory `:-`** preserves that protection: a bare `( E )`
without a guard is still not admitted, so the typo fails at the missing `:-` rather than consuming
the `(` as an arrow/tuple type.

This per-element scoping is the *inverse* of `:-` in a `rule`, where the comma-conjunction body is
the outer structure (the source of the "row- or element-scoped?" confusion); see open question A.

## Representation (`anthill.prelude.sort`)

The stored form is a new `EffectExpression` element beside `present` / `absent` / `open` / `merge`
(`stdlib/anthill/prelude/sort.anthill`):

```anthill
entity guarded(label: Type, guard: List[anthill.reflect.Term])
```

`label` is the effect `Type` (as in `present`); `guard` is the guard's **Horn body** — a
conjunction of goal terms over the operation's parameters, mirroring `rule_body`
(`commaSep1($._term)`). A bare `E :- p` stores `[p]`; the paren element `( E :- p, q )` stores
`[p, q]`; `present(label)` is the degenerate empty guard `guarded(label, [])` (`:- true`).

The guard's carrier **follows `EffectExpression`'s, and is contingent — not fundamental.** Today
`EffectExpression` is a *hash-consed term* (it rides in the arrow's `effects` field), and
occurrences cannot be hash-consed term args (WI-251), so the guard is `List[Term]` and at discharge
is materialized to occurrence goals via `term_body_to_nodes` (the same terms→nodes path a rule body
takes at assert) and refuted by the resolver. But hash-consing is a storage optimization, **not** a
property of type-hood (CLAUDE.md representation note), and term-backing arrows in particular cuts
against that note; the node-world migration already moved rule bodies
(`RuleEntry.body_nodes: Vec<Rc<NodeOccurrence>>`, WI-246) and op bodies to `NodeOccurrence`. Under a
node-world `Type`/`EffectExpression` the guard would simply be `List[NodeOccurrence]`, **uniform
with rule/op bodies**, and the term-vs-occurrence split disappears — see open question F. The
disjunctive merge above needs **no** new constructor — two `guarded` atoms on one label *are* the
unreduced `g1 ∨ g2`. `open` (row tail) and `absent` are unaffected; `decompose_effect_row` gains a
`guarded` arm that, after discharge, yields a `present` or drops the atom.

## Typer delta (this is WI-067)

At a call site, for each guarded element of the callee's declared row, attempt to refute the guard
against the arguments' static knowledge (sources above); emit a concrete contribution. Conservative
default: a guard that cannot be refuted keeps its effect.

## Semantics / soundness

Discharge only **drops** an effect when `¬guard` is *proven*; an unrefuted guard conservatively
keeps it. So a guarded effect is never dropped when it could fire — the static row remains a sound
over-approximation of runtime behavior. The guard is a **static** (type-level) device: it changes
only the inferred effect row, never runtime behavior. The runtime failure path is unchanged from
WI-066 (today `EvalError::DivisionByZero`; the handler-catchable bridge is a separate follow-up).

## Phasing

1. **Grammar + representation** — admit `Effect :- guard` in effect rows; the loader stores the
   guard as the `EffectExpression.guarded` element (the representation is already in
   `anthill.prelude.sort`).
2. **Typer discharge (WI-067)** — refute guards at call sites; literal (abstract-interp) and
   flow-fact (`if`/`match`) sources first, then KB resolution.
3. **Migrate the partial primitives** — change `Int64.div` / `mod` / `rem` / `divExact` (and
   `Field.div` / `recip`) from unconditional `Error[DivisionByZero]` to
   `{ Error[DivisionByZero] :- eq(b, 0) }`; update the WI-066 tests (a literal-divisor and a
   guarded-branch call now type pure).
4. **Generalize** — apply to other partial stdlib operations (`head`, `nth`, …) as their error
   payloads are introduced.

## Open questions

- **A. Guard vocabulary.** Any boolean operation (`eq`/`neq`/`isEmpty`/`outOfBounds`), or a
  restricted decidable fragment? Discharge must terminate — tie refutation to KB resolution under
  the `step_cap` runaway guard (cf. WI-179), so an undecidable/expensive guard simply stays
  conservatively present rather than hanging the typer.
- **B. Abstract receivers / dispatch.** A guard over an abstract spec-op parameter may be
  undischargeable at the spec level; it stays conservatively present and is discharged (if at all)
  at the concrete carrier. Confirm this composes with carrier-aware dispatch (WI-350).
- **C. Relationship to the existing constraint.** `int64.anthill` already has
  `constraint div_nonzero_primary: neq(?b, 0) :- div(?_, ?b)`. Is the guarded effect **derived**
  from that constraint (DRY — one statement of the precondition) or **declared independently** on
  the op (`:- eq(b, 0)`)? Lean: declare on the op; keep the constraint as an integrity guard. They
  state the same fact from two angles; decide whether to couple them.
- **D. Interaction with absence atoms.** Can a guard combine with a 045 absence atom
  (`-Modify[x]`)? Defer until a concrete need.
- **E. Runtime catchability.** When divide-by-zero is eventually routed through `raise_error` so an
  Error handler can catch it (the WI-066 review's Finding-1 follow-up), the static guard discharge
  and the dynamic handler must agree on when the effect is "really" present. Separate, but track it.
- **F. Carrier of `EffectExpression` (and the guard).** The guard is `List[Term]` only because
  `EffectExpression` rides inside a hash-consed arrow term; per the representation note hash-consing
  is not required for types (and is disclaimed for binders/arrows), so this is contingent. Two
  consequences:
  - A guard goal referencing a **local binder** (a lambda/`let` variable, not just an op parameter
    — the `lambda x -> op2(op1(x))` case) is still term-representable today: it rides an
    `anthill.reflect.Positioned(pos, internal)` leaf (`make_positioned`) — the same hash-consed
    bridge `denoted` value-in-type uses, where `pos` reifies the binder's absolute binding-site so
    alpha-distinct locals don't collide in the global store. This does **not** violate WI-251
    (`Positioned`'s args are `Term`, not a raw `NodeOccurrence`); it is the term-world *encoding* of
    occurrence content. So `List[Term]` is not limited to op-parameter guards.
  - `Positioned` is the existence proof that the term↔occurrence divide is bridgeable. A node-world
    `Type`/`EffectExpression` with an on-demand `Node → TermId` mapping (the inversion: occurrences
    primary; hash-consed terms a *derived* index where dedup / the `unify_effect_rows` identity
    fast-path actually pays) would let the guard be `List[NodeOccurrence]`, uniform with rule/op
    bodies, dissolving the term-vs-occurrence split. Larger than 048 — tracked as **WI-470**; until
    then 048 uses `List[Term]` (with `Positioned` for local-binder goals).
