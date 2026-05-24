# Proposal 045 — Effect sets, effect expressions, and effect checking

## Status: Draft (2026-05-24)

> Promotes `docs/brainstorms/effect-sets.md`, which has the full variant
> analysis (A/B/D/E/F), the prior art, and the hard problems. This proposal
> commits to a design: the brainstorm's **B (presence) surface over E (a `Set`
> value)**, with effect-sets as a new bindable kind and an explicit `+`/`-`
> **effect-expression** algebra.

## Summary

Introduce **effect-sets** as a new kind of entity — distinct from types,
bindable to a logic value — declared `effects E = ?` / `effects E = (expr)`
(parallel to `sort E = ?`), built by an **effect-expression** algebra
(`+e`, `-e`, `{}`, `+*`, `-*`, `merge`), carried by operation `effects` clauses
and arrow `@` annotations, and **checked** by verifying that an operation's
actual effects *satisfy* its declared effect expression.

Two-layer model (the effect-level analog of `denoted`, WI-302): an
**`EffectExpression`** (the algebra) **denotes** an **`EffectSet`** — a `Set` of
effect *types*, normalized modulo the ACI equational laws of `prelude/set.anthill`.
Checking is presence subsumption (`subset` + `not member`).

## Motivation

- **Individual effect = type; effect-set ≠ type.** `Modify[c]`, `Reads[d]`,
  `Error[T]` are types in the lattice; a *set* of them is a row with its own
  `subset` order — not a `Type`, but a component of (arrow) types. Today the only
  representation is `arrow(…, effects: List[Type])`, and effect *checking* is
  unimplemented (proposal 013).
- **Polymorphism is mandatory.** `map`/`fold`/`Stream.map` have *exactly the
  callback's effects* (`Function.apply … effects E`); a wrong convention gives a
  wrong effect-set.
- **Negative guarantees are required.** "this function does not write" —
  `-Modify` / `(Modify not in effects)` — a *guaranteed* absence, not just
  "unmentioned."
- The reference typer (`docs/proposals/typing_pass_spec.anthill`) already
  *computes* effect rows (`union_effects` to combine, `check_effects` to verify;
  `result_effects` merely projects the row out of a `TypeResult`); this proposal
  is the effect-expression layer those computations build and check against.

Mis-encoding effects as a `sort E = ?` type parameter is the root problem (it
forces an effect-set into type position). This proposal gives effect-sets their
own kind.

## 1. Effect-sets — a new kind

- An **effect-set** is a new entity kind. It is **not** a `Type`; it is the row
  of effects on an arrow. Its *elements* are effect types (`Effect[?]`), and an
  individual effect (`Modify[c]`) remains a `Type`.
- The value is a `Set` of effect types over the existing `Set`/`EffectSet`
  substrate (`prelude/set.anthill`, `prelude/effect-set.anthill`):
  `member` / `subset` / `union` / `difference`, with the **ACI equational laws**
  (idempotent + commutative `insert`) giving set semantics by *equational
  matching* (Maude-style), not bespoke unification.
- An effect-set is **bindable to a logic value**: a logic variable can range
  over effect-sets (a row / presence variable). This is how polymorphism and
  propagation work — ordinary unification of an effect-set–kinded variable,
  modulo ACI.

## 2. Declaration — `effects E = ?` / `effects E = (expr)`

Where one writes `sort E = ?` for a type parameter, write **`effects E = ?`** for
an effect-set parameter:

```
sort Function
  sort A = ?
  sort B = ?
  effects E = ?                                  -- was: sort E = ?
  operation apply(f: Function[A,B,E], x: A) -> B effects E
```

- `effects E = ?` — a free effect-set variable (polymorphic).
- `effects E = (expr)` — `E` bound to an effect expression.
- `PureFunction = Function[…, E = {}]` (empty effect-set; `Set.empty()`).

This makes the effect-set parameter its own kind, distinct from a `sort`
(type) parameter — fixing the `sort E = ?` kind-confusion.

## 3. Effect expressions

An **effect expression** denotes an effect-set as a **presence profile** (each
effect label: present / absent / unspecified). Atoms and operators:

| form | meaning |
|---|---|
| `{}` | empty (pure) — nothing present |
| `*` | universal — everything present (top) — *deferred, see §7.5; first cut says "allow all" by omitting the annotation* |
| `e` | a single effect, e.g. `Modify[c]` |
| `E` | an effect-set variable (`effects E = ?`) |
| `+ e` | **presence** — add `e` |
| `- e` | **absence** — remove / forbid `e` |
| `+ *` | allow all (→ `*`) — *deferred, see §7.5* |
| `- *` | disallow all (→ `{}`) — *deferred, see §7.5* |
| `merge(x, y)` | combine two expressions; **conflict** (a label `+` in one, `-` in the other) ⇒ **incompatible** (error) |
| `{ E1, …, EN }` | set literal — **sugar** for iterated `merge` (see below) |

The normal form is a **base** (`{}` / `*` / a variable `E`) plus finitely many
`+`/`-` overrides — i.e. a **finite or co-finite** set (the Boolean subalgebra of
the brainstorm). Examples:

```
effects {}                     -- pure
effects (+ Modify[c])          -- may modify c
effects (* - Modify[kb])       -- "does not touch kb" — anything except Modify[kb]  (needs `*`; deferred, §7.5)
effects E                      -- polymorphic (propagates the callback's row)
effects merge(E, + Reads[d])   -- the callback's effects, plus Reads[d]
```

`+ e` / `- e` are exactly **presence polymorphism** (label present / absent /
poly); `* - e` is the co-finite "anything but `e`"; a variable base is an open
row. This is the surface form of the `Set` algebra (`∪`/`\`); it **evaluates /
normalizes** (via the ACI laws) to an `EffectSet`. (`merge` is `union` on
presences but *fails* on a present/absent clash — that's the incompatibility.)

**The set literal is `merge` sugar.** `{ E1, …, EN }` desugars to iterated
`merge` over the empty base, so it is not a separate primitive:

```
{ E1, …, EN }  ≡  merge(E1, merge(E2, … merge(EN-1, EN)))
{ }            ≡  {}            -- empty base (pure)
{ e }          ≡  + e          -- a bare effect denotes its singleton presence
```

Because the elements are effect *expressions* (and a bare effect `e` is its
singleton presence `+e`), the literal inherits `merge`'s conflict semantics:
`{ +Modify[c], -Modify[c] }` is **incompatible** for free — no special-casing.
This lets us offer the familiar `{…}` set surface *and* the `+`/`-`/`merge`
algebra without two semantics: the braces are pure sugar.

**Inferring effects is not one of these forms.** The table lists everything you
can *write* — there are no other building blocks. Working out which effects a
function actually has is a *different* thing: it reads the function's code and
*returns* an effect expression (built from the forms above). The typer does
this — it takes the `union` of the effects of the operations the body calls,
minus the effects its handlers discharge. You could also expose it as a reflect
builtin, e.g. `infer_effects(occ: NodeOccurrence) -> EffectExpression`.

The point: that operation **consumes code and produces an expression**. It is
not itself a form you write, so it does not belong in the table — which is why
the earlier `result_effects(br)` row was wrong.

## 4. Where declared (interchangeable sugars)

Per the brainstorm's "a type is shorthand for a pre/post predicate," the
declaration surface is interchangeable — all denote the same effect-row contract:

- **`effects <expr>`** clause on an operation; **`@ <expr>`** on an arrow type
  (the *value-attached* form — a function value's effect contract travels with
  its type, mandatory for first-class functions / `apply`).
- **`ensures (e in effects)`** ≡ `+ e`; **`ensures (e not in effects)`** ≡ `- e`
  — the contract-homed form (closed-world: unstated ⇒ absent by NAF), projected
  to the effect-set on the arrow.

## 5. Checking — "satisfies the definition, or not"

For each operation:

1. **Compute the actual effect expression** of the body: `union` of the effect
   expressions of the operations it calls and of its callback effect-variables
   (propagation: `op_effects(map(f, xs)) = op_effects(f)`), with **handlers
   discharging** the effect they handle (`\` / `- e`).
2. **Check it satisfies the declared expression**, modulo ACI:
   - every declared `+ e` is *permitted*: actual `⊆` allowed (`subset`);
   - every declared `- e` *holds*: `e ∉` actual (`not member`) — including on a
     polymorphic base, where it constrains the variable's row (a presence
     variable carrying the absence);
   - effect-set variables unify / propagate.
3. Result: **satisfies** (the body's effects are within the declaration) or a
   **type error** (an undeclared effect, a violated `- e`, or a `merge`
   incompatibility).

"Input vs output effects": an operation transforms an *input* effect context to
an *output* row — a **handler** has `output = input \ {handled}`; a plain op's
output is what it performs. Checking relates the output to the declaration.

## 6. Representation (reflect) and reconciliation

- New: **`EffectExpression`** (the algebra of §3), which **denotes** an
  **`EffectSet`** (the `Set`-value normal form). The effect-level analog of
  `denoted`.
- `arrow.effects` and `Function.E` carry an **`EffectExpression`** (not
  `List[Type]`); the typer normalizes to an `EffectSet` for checking.
- Reconcile the orphaned pieces: `Set` (complete the recursive `member`/`subset`/
  `union`/`difference` laws), `EffectSet` (= `Set` of `Effect[?]`), `Function`
  (`sort E = ?` → `effects E = ?`), `arrow` (effects field → `EffectExpression`).
- **ACI matching must fire** during effect checking (via `[simp]` / proposal 043
  or ACI operator attributes) — *the* core semantic commitment.

## 7. Open questions / hard points

1. **Negation on open rows — mostly handled by laziness.** Because an
   `EffectExpression` is *symbolic* and only normalizes to an `EffectSet` when
   its variables are ground (§6's two-layer split), `merge(E, - e)` over a free
   `E` simply stays an unevaluated term. It is normalized — and the conflict
   checked — only when `E` is bound, which happens at every concrete use (the
   call site supplying the callback). At that point the check is local and
   decidable: if the bound row contains `e`, the `merge` conflicts → the call
   site is rejected; otherwise fine. So `effects merge(E, - Modify[kb])` ("this
   function forbids its callback from modifying kb") needs **no presence
   variables and no substrate change** — just deferred evaluation.
   The residual (optional, not a soundness issue): checking a polymorphic
   declaration *in isolation*, never instantiated — under laziness we defer
   judgment, so we cannot tell at definition-time whether `merge(E, - e)` is even
   satisfiable. **Question: do we want abstract definition-time checking of
   never-grounded polymorphic effect declarations** (which is where presence
   variables — Rémy/Links; Lindley & Cheney 2012 — would buy something), or is
   lazy per-instantiation checking sufficient?
2. **`merge` conflict semantics — *resolved*: hard error.** A present/absent
   clash (`+e` in one operand, `-e` in the other) is a **hard error**, not a
   propagating `⊥`/`incompatible` value. Since `merge(E, …)` only normalizes
   once `E` is ground (per (1)), the error fires at normalization — at the site
   that produced the conflicting row (a call site binding a callback whose
   effects violate a declared `- e`, or a directly-written `merge(+e, -e)`),
   pointing there. No unsatisfiable-row value to track. Open only: the exact
   diagnostic wording / which operand the message blames.
3. **Decidability of effect-checking — induction on the body, fixpoint for
   recursion.** For a **non-recursive** operation, `op_effects` is a `union`/
   discharge fold over the *finite* body term, so it terminates by structural
   induction on the body — a well-founded measure (the same shape as the typer's
   `synth`/`check` walk). For **(mutual) recursion**, `op_effects(f)` depends on
   itself; this is a **monotone fixpoint** over the row lattice. It terminates by
   the ascending-chain condition: only finitely many effect labels occur in the
   program, so the lattice of reachable rows is finite and the `union` ascent
   stabilizes. Open only: confirming the fixpoint is taken over that finite
   label set (not over open/co-finite rows that could grow without bound), and
   how it is scheduled within SLD resolution.
4. **Grammar surface — *resolved for `{…}`*; one operator still open.** The set
   literal `{ E1, …, EN }` is sugar for iterated `merge` (§3), so it adds no new
   semantics. We have `merge(x, y)` for **union** and `- e` for **removing one
   named effect**. The only open question: do we also need an operator that
   subtracts a *whole* effect-set, `difference(E1, E2)` (remove everything in
   `E2` from `E1`)? It matters only for **handler discharge of a variable
   set** — when a handler removes a set of effects that isn't statically known.
   If discharge always names the handled effects, repeated `- e` is enough and
   no new operator is needed.
5. **`*` (top) — *deferred*: start without a writable top.** The first cut uses
   **finite rows only**, with "allow all" handled by the **default** rather than
   a `*` atom:
   - **No effects annotation ⇒ allow-all** (open / unchecked) — including a bare
     arrow `A -> B` with no `@`. This is how you say "may do anything."
   - **An explicit `effects (…)` clause ⇒ closed world**: only the listed
     effects are permitted, unstated ⇒ absent (NAF). Pure is the explicit
     `effects {}`; specific rows are `+ e` / `{ … }`; absence is `- e` checked
     against ground rows.

   This is **open by default, closed once you annotate** (note: this *reverses*
   a "`{}` default" — the default is allow-all, not pure). It drops `*`, `+ *`,
   `- *`, and the co-finite `* - e` ("anything but `e`") for now: a writable top
   is only needed for allow-all *inside* a composed expression, and it raises
   consistency questions (what is `merge(*, - e)` vs `merge(*, + e)`? does `*`
   fit the normal form or need its own representation in `Set`?). Revisit once
   finite rows work; `* - Modify[kb]` is the motivating use to come back for.

## Prior art

- **B (presence / constraints)** — effects-as-constraints: Wadler & Blott, POPL
  1989; Jones, *Qualified Types*, 1994 (mtl `Member`/`MonadState`). Presence/row
  polymorphism applied to **effects**: Lindley & Cheney, *Row-based effect types
  for database integration*, 2012 (Links). The row/presence *technique* itself is
  from **record** typing (Rémy 1989; Leijen 2005 — *not* effects).
- **D/E (rows + unification; ACI)** — Leijen, *Koka* (MSFP 2014; POPL 2017);
  Kiselyov et al., *Extensible Effects* (2013) / *Freer Monads* (2015);
  Hillerström & Lindley 2016; Maude ACI (Clavel et al. 2007; Stickel, JACM 1981).
- **Origins** — Lucassen & Gifford, POPL 1988; Talpin & Jouvelot 1992; Nielson &
  Nielson 1999.
- **Handlers** (separate axis; proposal 027) — Plotkin & Pretnar, ESOP 2009.
  Capability/capture-checking (Scala) is a *different* discipline (no handlers;
  tracks capability-value escape), not the effect row.

## Relation to other proposals / WIs

- **013 (Abstract Effect Parameters)** — this *completes* its deferred effect
  *checking*, and reframes `sort E = ?` effect params as `effects E = ?`.
- **003 (Effect Annotations on Arrow Sorts)** — `@ <expr>` generalizes the arrow
  effect annotation to a full effect expression.
- **027 (Effect Handlers)** — handlers *discharge* effects (`\`); the runtime
  catalog is 027's, the static checking is here.
- **WI-301 (effect-set type args)** — *subsumed / reframed*: effect-sets are not
  type arguments; they're effect expressions on arrows (out of `[…]` position).
- **WI-302 / `denoted`** — the *type-level* analog (a type denoted by a computed
  expression); effect expressions are the same idea for effect-sets.

## Next steps

1. Land the `Set`/`EffectSet` laws + `*` (top) + ACI matching (the substrate).
2. `EffectExpression` reflect sort + the `+`/`-`/`merge` grammar.
3. `effects E = ?` declaration; `arrow.effects` / `Function.E` →
   `EffectExpression`.
4. Effect checking (satisfaction; propagation; handler discharge), with presence
   variables for open-row absence.
5. Migrate `typing_pass_spec` effect handling onto this; only then is its
   effect-checking honest.
