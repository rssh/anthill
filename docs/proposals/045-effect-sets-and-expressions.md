# Proposal 045 — Effect sets, effect expressions, and effect checking

## Status: Draft (2026-05-24; row-unification pivot 2026-05-25)

> Promotes `docs/brainstorms/effect-sets.md`, which has the full variant
> analysis (A/B/D/E/F), the prior art, and the hard problems. This proposal
> commits to a design: the brainstorm's **B (presence) surface**, **checked by
> the textbook row-polymorphism algorithm in the typer**. (Earlier drafts framed
> checking as ACI matching over a `Set` value; that is dropped — see §5/§6.
> Effects are dominated by the *polymorphic* case, which is row polymorphism's
> home, and absence on open rows is its `lacks` machinery, not a hard problem.)

## Summary

Introduce **effect-sets** as a new kind of entity — distinct from types,
bindable to a logic value (a **row variable**) — declared `effects E = ?` /
`effects E = (expr)` (parallel to `sort E = ?`), written via an
**effect-expression** algebra (`e`/`+e`, `-e`, `{}`, `?`/`E`, `merge`), carried by
operation `effects` clauses and arrow `@` annotations, and **checked** by
verifying that an operation's actual effects *satisfy* its declaration.

The surface **`EffectExpression`** (the algebra) **elaborates to a row** — a set
of present labels + an optional row-variable tail (+ `lacks` constraints for
`-e`). Checking is **row unification** (presence-polymorphic rows; Rémy 1989,
Lindley & Cheney 2012), run inside the typer as the effects-component of
arrow-type unification (`unify_arrow` / `arrow_compatible`) — using the typer's
existing type-variable substrate for the tail variable.

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
- The value is a **row**: a set of present effect-type labels plus an optional
  **row-variable tail** (open row), and — for absence — `lacks` constraints on
  that tail. Set semantics (order/duplicates irrelevant) come from the row
  representation, not from generic equational `Set` matching.
- An effect-set is **bindable to a logic value**: the row tail is an ordinary
  logic/type variable (`Var::Global`), so polymorphism and propagation are just
  **row unification** of that variable (§5). This is presence-polymorphic rows
  (Rémy 1989; Lindley & Cheney 2012), not a bespoke scheme.

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
| `{}` | empty (pure) — nothing present, closed |
| `e` | a single effect, e.g. `Modify[c]` — **present** (listing a label means presence; this is the default) |
| `E` / `?` | a row variable — named (`effects E = ?`) or anonymous (`?`). An open tail. |
| `+ e` | presence, **explicit** — same as bare `e`; `+` is optional sugar |
| `- e` | **absence** — forbid `e` (a `lacks` constraint on the tail). The `-` is the only load-bearing marker, since presence is the default. |
| `merge(x, y)` | combine two expressions; **conflict** (a label present in one, `-`/absent in the other) ⇒ row-unification failure |
| `{ E1, …, EN }` | set literal — **sugar** for iterated `merge` (see below); elements may be `+e` / `-e` / a base row variable |

A row is a **base** (`{}` closed, or an open row variable `E`/`?`) plus finitely
many `+`/`-` overrides. There is **no `*` (universal top)**: an open row variable
*is* the surface "top" — see §7.5. Examples:

```
effects {}                  -- pure (closed empty row)
effects { ? }               -- allow all (open tail, no constraint)
effects { Modify[c] }       -- closed: only Modify[c]   (bare = present; no `+` needed)
effects { ?, -Modify[kb] }  -- "does not touch kb": anything except Modify[kb]
effects E                   -- polymorphic (propagates the callback's row E)
effects merge(E, Reads[d])  -- the callback's effects, plus Reads[d]
effects { E, -Modify[kb] }  -- the callback's effects, but guaranteed not Modify[kb]
```

**Variable convention (kind by position).** A variable in **effect position**
(inside an `effects …` clause or an `@ …` arrow annotation) is, by convention, an
**effect-set / row variable** — never a value or ordinary type variable. This is
the only possible confusion (anthill variables `?` / `?name` are otherwise
syntactically distinct from labels like `Modify[kb]`), and position settles it,
the same way `sort T = ?` kinds `T` as a type. So `?` is a fresh anonymous row
variable, `?r` a named one (reusable to refer to the same tail), and a bare `E`
references a declared `effects E = ?` binder. Such a variable is the effect row
of a `Function`-typed parameter in the same signature, or a sort-level
`effects E = ?` binder — never free-floating.

Listing a label means **present** (the default), so `+` is optional sugar; only
`- e` (absence) is a marked, load-bearing form — a `lacks` constraint on the
tail. An open variable base is an open row, and `{ ?, -e }` is the co-finite
"anything but `e`". The expression **elaborates to a row** (present labels + tail
variable + `lacks`); `merge` is row extension, but *fails* on a present/absent
clash — that's the incompatibility, surfaced as a row-unification failure.

**The set literal is `merge` sugar.** `{ E1, …, EN }` desugars to iterated
`merge` over the empty base, so it is not a separate primitive:

```
{ E1, …, EN }  ≡  merge(E1, merge(E2, … merge(EN-1, EN)))
{ }            ≡  {}            -- empty base (pure)
{ e }          ≡  e            -- a bare effect denotes its singleton presence
```

Because the elements are effect *expressions* (a bare effect `e` is its
singleton presence, `- e` a `lacks`, `?`/`E` an open tail), the literal inherits
`merge`'s conflict semantics: `{ Modify[c], -Modify[c] }` is **incompatible** for
free — no special-casing. This lets us offer the familiar `{…}` set surface *and*
the `merge`/`-` algebra without two semantics: the braces are pure sugar.

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

## 5. Checking — row unification in the typer

Effect checking is the **textbook row-polymorphism algorithm** (presence-
polymorphic rows: Rémy 1989; Lindley & Cheney 2012 for effects), run **inside
the typer** as the effects-component of arrow-type unification — *not* a generic
ACI/`Set` rewrite. This is the right home because effects are dominated by the
*polymorphic* case (`map`/`fold`/`Stream.map` carry exactly the callback's row),
which is precisely what row polymorphism is built for, and because absence on an
open row (`- e`) is exactly its **lacks**-constraint machinery — dissolving the
old "negation on open rows" hard problem rather than deferring it.

A row is a set of **present** labels plus an optional **row-variable tail** `ρ`
(open row), and — for `- e` — **lacks** constraints on `ρ`. The tail variable is
an ordinary type variable (`Var::Global`), bound through the typer's existing
`Substitution`/`occurs_in`/`walk_type`.

For each operation:

1. **Compute the actual row** of the body: union of the rows of the operations
   it calls and of its callback row-variables (propagation:
   `op_effects(map(f, xs)) = op_effects(f)`), with **handlers discharging** the
   effect they handle (drop a label / strengthen a lacks).
2. **Unify / subtype against the declared row** (the row-rewrite rule): to match
   `{ l | ρ1 }` against another row, surface `l` in it, unify the label
   presences, unify the tails; an open declared row absorbs extra actual labels
   into its tail, a closed one does not; a `- e` declaration adds `lacks e` to
   the tail and **fails if the actual row presents `e`**.
3. Result: **satisfies** (rows unify / actual is a row-subtype) or a **type
   error** (an undeclared effect against a closed row, a `lacks` violation, or a
   `merge` conflict).

This *replaces* today's two half-measures: `unify_arrow` (`typing.rs`) currently
**skips the effects field entirely**, and `arrow_compatible` does only a naive
positional `⊆` subset check with no row variables.

"Input vs output effects": an operation transforms an *input* effect context to
an *output* row — a **handler** has `output = input` minus the handled label; a
plain op's output is what it performs. Checking relates the output to the
declaration.

**Phasing.** v1a: open rows with present labels + tail variable — real row
unification in `unify_arrow`, open-row subtyping in `arrow_compatible` — covering
the common polymorphic-propagation case (no `- e`). v1b: add **lacks**
constraints for `- e` absence guarantees.

## 6. Representation (reflect) and reconciliation

- New: **`EffectExpression`** (the algebra of §3) — the surface a programmer
  writes. It **elaborates to a row**: present labels + an optional row-variable
  tail (+ lacks constraints in v1b). `+ e` → present, `- e` → lacks, `E` → tail
  variable, `merge` → row extension/unification, `{}` → closed empty row.
- `arrow.effects` and `Function.E` carry this **row** (replacing the closed
  `List[Type]`); the typer unifies rows directly.
- `Function`: `sort E = ?` → **`effects E = ?`** (declares a row variable, not a
  type parameter).
- **Effect checking is row unification in the typer — not generic ACI/`Set`
  rewriting.** The row-rewrite rule lives in `unify_arrow` / `arrow_compatible`
  (`typing.rs`), using the typer's existing type-variable substrate for the tail
  variable. The `[simp]`/ACI/canonical-`Set` substrate (§ earlier drafts) is
  **decoupled from effect checking**: it remains only as optional machinery for
  *general* sets (and the runtime effect catalog), not on the checking path.
  `Set`/`EffectSet` stay orphaned until a general-set consumer needs them.

## 7. Open questions / hard points

1. **Negation on open rows — *resolved* by row polymorphism (no longer a hard
   part).** Adopting row unification in the typer (§5) means `- e` on an open row
   is just a **lacks constraint** on the tail variable `ρ` (`ρ lacks e`), the
   standard presence-polymorphic mechanism (Rémy 1989; Lindley & Cheney 2012). It
   is checked *abstractly at definition time* — no waiting for `E` to be ground,
   no laziness hack: unifying a row that presents `e` against a tail carrying
   `lacks e` fails directly, and the constraint propagates to call sites through
   ordinary tail-variable unification. So `effects merge(E, - Modify[kb])` ("this
   function forbids its callback from modifying kb") is a row `{ … | ρ }` with
   `ρ lacks Modify[kb]`, principal and decidable. This is **v1b** of §5. (The
   earlier laziness framing is superseded — it was an artifact of the canonical-
   `Set` approach, which we dropped.)
2. **`merge` conflict semantics — *resolved*: hard error (a unification
   failure).** A present/absent clash (`+e` in one operand, `-e` in the other) is
   a **hard error**, not a propagating `⊥` value. Under row unification it is
   simply a **failed unification** — presenting label `e` against a tail that
   `lacks e` — raised at the point the two rows are unified (a call site whose
   callback row violates a declared `lacks`, or a directly-written
   `merge(+e, -e)`), pointing there. No unsatisfiable-row value to track. Open
   only: the exact diagnostic wording / which side the message blames.
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
5. **`*` (top) — *dropped*: the open row variable is the surface top.** There is
   no `*` / `+ *` / `- *`. An **open row variable** (`?` anonymous, or a named
   `E`) already provides everything a universal top was wanted for, using the
   substrate we need anyway for polymorphism:
   - **allow all** — `effects { ? }` (open tail, no constraint), or simply
     **omitting** the annotation;
   - **anything but `e`** (the co-finite case) — `effects { ?, - e }` (open tail
     + a `lacks e`), with no lattice-top;
   - **pure** — `effects {}` (closed empty row);
   - **specific** — `effects { +e, … }` (closed) or `effects { E, … }` (open).

   The distinction is **base**: `{}` is a closed empty row, `{ ? }` / `{ E }` is
   an open row whose tail variable absorbs any extra actual effects (covariant-
   effects subtyping — what `arrow_compatible` already does). A `- e` is a
   `lacks` constraint on that tail. This sidesteps the consistency questions a
   constant `*` raised (`merge(*, ±e)`, fitting the normal form). A constant top
   would return **only** if some internal lattice computation ever needs it — the
   surface and checking do not.

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

The checking algorithm is **row unification in the typer** (§5), not the
ACI/`Set` substrate. Phases:

1. **v1a — row unification (open rows, presence only).** Represent the
   `arrow.effects` row as present labels + an optional row-variable tail (an
   ordinary `Var::Global`). Implement the row-rewrite rule in `unify_arrow`
   (which today skips effects entirely) and open-row subtyping in
   `arrow_compatible` (today a naive `⊆` subset check). Covers polymorphic
   propagation — the common case.
2. **EffectExpression surface + grammar** (`+`/`-`/`merge`/`{}`/`E`), elaborating
   to a row; `effects E = ?` declaration binding a row variable; `arrow.effects`
   / `Function.E` carry the row.
3. **v1b — lacks constraints.** Add `- e` absence guarantees as `lacks`
   constraints on the tail variable (§7.1), checked abstractly at definition
   time.
4. **Handler discharge** — a handler drops the handled label / strengthens a
   lacks (relation to proposal 027).
5. **Migrate `typing_pass_spec`** effect handling onto row unification; only then
   is its effect-checking honest.
6. *(Optional, decoupled.)* The `[simp]`/ACI/canonical-`Set` substrate, only if a
   *general*-set consumer appears — not needed for effect checking.
