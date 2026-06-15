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

The contribution to the caller's row is therefore always a **concrete** row — guarded elements
live only in *declarations* and are resolved per call. **Row unification / composition is
unchanged**; nothing guarded ever propagates upward.

The sources of a refutation of `eq(b, 0)` (i.e. a proof of `neq(b, 0)`) are precisely the existing
discharge mechanisms (018 §"Discharge mechanisms"), which is why this needs no new *proof* surface:

1. **Abstract interpretation** — a literal divisor: `div(a, 5)` refutes `eq(5, 0)` by evaluation.
2. **Context propagation** — an enclosing `if neq(b, 0) then …` or a `match` arm that has
   eliminated the zero case (this is WI-067).
3. **KB resolution** — `neq(b, 0)` derivable from facts/rules in scope.
4. **Explicit proof** — for hard cases, a `proof` declaration / tactic (025 / 031).

### An effect row is a Horn theory

A row `{ E1, E2, E3 :- g }` is a small Horn theory; discharge is **SLD refutation** over it. That
aligns guarded-effect discharge with the resolver-as-type-checker direction (WI-010 / WI-382): the
per-element guard check is the *same* resolution engine, not a bespoke conditional bolted onto the
effect checker.

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

An effect-row element gains an optional trailing `:- guard`, where `guard` is a boolean term over
the operation's parameters. Builds on the `effect_row` node (WI-375). Unguarded elements are
unchanged; the addition is conflict-local to the row production.

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

1. **Grammar** — admit `Effect :- guard` in effect rows; the loader stores the guard alongside the
   element.
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
