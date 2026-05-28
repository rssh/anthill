# Proposal 045 — Effect sets, effect expressions, and effect checking

## Status: Draft (2026-05-24; row-unification pivot 2026-05-25; variant-7 adoption 2026-05-28)

> Promotes `docs/brainstorms/effect-sets.md`, which has the full variant
> analysis (A/B/D/E/F, plus the 2026-05-27/05-28 chapters on operation
> effect-parameters and the runtime-mirror argument). This proposal commits to
> a design: the brainstorm's **B (presence) surface**, **checked by the
> textbook row-polymorphism algorithm in the typer**, **with the effect-row
> representation realized via the brainstorm's variant 7** —
> `effects_rows(EffectExpression)` as a new `Type` enum variant +
> `EffectsRuntime` as a kind-anchor sort + an `effects` keyword that desugars
> to `sort + requires EffectsRuntime[…]`. (Earlier drafts framed checking as
> ACI matching over a `Set` value; that is dropped — see §5/§6. Earlier
> drafts also kept `EffectExpression` outside `Type` and added a parallel
> `effects E = ?` binder; variant 7 puts a single constructor across the
> Type/EffectExpression boundary and reuses the type-parameter substrate via
> the `requires` constraint — see §1/§2. Effects are dominated by the
> *polymorphic* case, which is row polymorphism's home, and absence on open
> rows is its `lacks` machinery, not a hard problem.)

## Summary

Introduce **effect-rows** — a structured `Type` enum variant
`effects_rows(EffectExpression)` (parallel to the existing
`denoted(NodeOccurrence)`) — wrapping the `EffectExpression` row algebra
(`e`/`+e`, `-e`, `{}`, `?`/`E`, `merge`) so it can sit in `Type`'s arrow-effects
slot and in the type-arg slots of parameterized sorts. Declare an effect-row
parameter via the **`effects`** keyword at sort-item position, which
desugars to `sort E = ? requires EffectsRuntime[Effects = E]` — the carrier
sort `EffectsRuntime` is the kind anchor. The loader auto-emits the
`requires` from any `effects <expr>` clause walking its free variables, so
users write `effects E` and get an effect-kinded parameter without
per-operation binder ceremony. Effect-rows are carried by operation
`effects` clauses and arrow `@` annotations, and **checked** by verifying
that an operation's actual effects *satisfy* its declaration.

The surface **`EffectExpression`** (the algebra) **elaborates to a row** — a set
of present labels + an optional row-variable tail (+ `lacks` constraints for
`-e`). Checking is **row unification** (presence-polymorphic rows; Rémy 1989,
Lindley & Cheney 2012), run inside the typer as the effects-component of
arrow-type unification (`unify_arrow` / `arrow_compatible`) — using the typer's
existing type-variable substrate for the tail variable. `unify_arrow`
pattern-matches `Type` variants and dispatches the `effects_rows(...) ↔
effects_rows(...)` case to the row-rewrite rule (one extra match arm beyond
today's `Type` cases).

## Motivation

- **Individual effect = type; effect-set ≠ type.** `Modify[c]` and `Error[T]`
  are types in the lattice; a *set* of them is a row with its own
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

## 1. Effect-rows — a structured `Type` variant

- An **effect-row** is a *structured* `Type` enum variant:
  **`effects_rows(expr: EffectExpression)`**, sitting next to `sort_ref`,
  `parameterized`, `named_tuple`, `arrow`, `type_var`, `denoted`, and `nothing`
  in `stdlib/anthill/prelude/sort.anthill`. Its **internal structure** is the
  row algebra `EffectExpression` (§3, §6); its **outer position** is `Type`,
  so it sits in the type-arg slot of parameterized sorts (notably
  `EffectsRuntime[Effects = E]`, §2) and in `Type.arrow`'s `effects` field.
- An individual effect (`Modify[c]`, `Error[T]`) remains an ordinary `Type` (a
  parameterized `Effect[?]`); the row is built from those labels by the
  `EffectExpression` algebra. The boundary between `Type` and
  `EffectExpression` is **not dissolved** — `EffectExpression` is still its
  own reflect sort with its own normal form — but **one constructor
  (`effects_rows`) crosses it**, the way `denoted(NodeOccurrence)` already
  crosses the type / value-occurrence boundary.
- The row **value** is the row algebra's normal form: a set of present
  effect-type labels + an optional **row-variable tail** + `lacks` constraints
  for absence. Set semantics (order/duplicates irrelevant) come from the row
  representation, not from generic equational `Set` matching.
- Effect-row variables are **ordinary type variables** at the surface — the
  tail variable is a `Var::Global`. The kind discriminator
  (`EffectsRuntime[Effects = E]`, §2) is a `requires` constraint the typer
  checks at binding-site (it rejects any `Type` binding to
  `EffectsRuntime.Effects` that is not `effects_rows(...)`-shape).
  Polymorphism and propagation are **row unification** of the tail variable
  (§5; Rémy 1989; Lindley & Cheney 2012), dispatched on the
  `Type::effects_rows(...)` variant tag inside `unify_arrow`.
- **Rationale.** This is **variant 7** of `docs/brainstorms/effect-sets.md`,
  with the 2026-05-28 runtime-mirror chapter as its conceptual rationale.
  The brainstorm's Principle 2 ("effect-set ≠ type") is softened to
  "effect-row is a *structured* `Type` variant, with the row algebra living
  inside it." The variant has internal structure (`EffectExpression`) that
  *generates* its refines relation, so the brainstorm's earlier variant-A
  "type-lattice impurity" objection does not apply.

## 2. Declaration — the `effects` keyword as sugar over `sort + requires`

The `effects` keyword at sort-item position is **kind-sugar** for an ordinary
type parameter plus a kind-discriminating `requires`:

| surface | desugars to |
|---|---|
| `effects E = ?` | `sort E = ?  requires EffectsRuntime[Effects = E]` |
| `effects E = X` | `sort E = X  requires EffectsRuntime[Effects = E]` |
| `effects E` (bare) | `effects E = ?` (abbreviation, parallel to bare `sort E`) |

(Using positional shorthand: `EffectsRuntime[E]` ≡ `EffectsRuntime[Effects = E]`.)

`Function` declares cleanly:

```
sort Function
  sort A
  sort B
  effects E
  operation apply(f: Function[A, B, E], x: A): B effects E
```

`Function.E` is now correctly kinded — the `EffectsRuntime[E]` `requires`
forces `E` to be `effects_rows(...)`-shape at binding-site, fixing the old
`sort E = ?` mis-kinding — without inventing a new kind grammar.

- `effects E = ?` — a free effect-row variable (polymorphic).
- `effects E = X` — `E` bound to a specific effect-row expression `X`.
- `PureFunction = Function[…, E = effects_rows(empty_row)]` (the closed
  empty row).

### 2.0 The kind anchor — `EffectsRuntime`

The `EffectsRuntime` sort itself is a **pure kind anchor** in this proposal:

```
sort EffectsRuntime
  sort Effects = ?
end
```

— no entities, no operations. Its sole role is to serve as the right-hand
side of the `requires` constraint the `effects` keyword desugars to.

A handler-bundle role for `EffectsRuntime` (capability-passing dispatch
parallel to its kind-anchor role) is captured as a follow-on in
`docs/brainstorms/effect-sets.md` §"Addendum — `EffectsRuntime` as the
handler-bundle witness" and is **not adopted in this proposal** — see §"Out
of scope" below. This proposal keeps 027's ambient-handler model unchanged.

### 2.0.1 The bridge rule

The bridge between the value-level constructor and the kind discriminator is
one typing rule emitted by the loader once:

```
rule type_of(?occ, EffectsRuntime[Effects = effects_rows(?expr)])
  :- is_entity_of(?occ, effects_rows(?expr))
```

Any `Type` binding to `EffectsRuntime.Effects` that is not
`effects_rows(...)`-shape fails the `requires` at binding-site.

### 2.1 Binding effect-row variables on an operation — dissolved by auto-requires

Earlier drafts debated how to bind an effect-row variable in the
type-parameter list of a *free standalone operation* (e.g. `map[A, B, E](f,
xs)`), where neither a sort-level `effects E` binder nor a function-typed
parameter supplies one. Candidate surfaces included a new `[…, effects E]`
slot, a kinded quantifier `[E: Effects]`, a separate bracket, or an `@`
marker — see `docs/brainstorms/effect-sets.md` §"Operation effect-parameters"
(2026-05-27, variants 1–6).

**Variant 7 dissolves this.** Because `effects E` is now sugar for
`sort E = ? requires EffectsRuntime[Effects = E]` (§2), the type-parameter
list is uniform — the same `[A, B, E]` shape used for ordinary type
parameters carries effect-row variables too:

```
operation map[A, B, E](f: Function[A, B, E], xs: List[A])
   -> List[B] effects E
```

The loader walks each operation's `effects <expr>` clause, collects its free
variables, and **auto-emits** `requires EffectsRuntime[Effects = E_i]` per
free variable into the operation's `requires` list:

| effects clause | auto-emitted requires |
|---|---|
| `effects E` | `requires EffectsRuntime[E]` |
| `effects merge(E1, E2)` | `requires EffectsRuntime[E1]`, `requires EffectsRuntime[E2]` |
| `effects { E, -Modify[kb] }` | `requires EffectsRuntime[E]` |
| `effects { Modify[c] }` (closed; no free vars) | (none) |

Operations also inheriting from a sort-level `effects E` binder redundantly
emit the same constraint; idempotent — loader dedupes or accepts both, no
behavioral difference.

The kind is inferred from position, exactly as the by-position convention
in §3 already specified. No new grammar; no `[…, effects E]` slot; no kinded
quantifier; **WI-318 is closed by adoption of variant 7.**

Kind-conflict between *type* and *effect* uses of the same variable surfaces
as an ordinary over-constrained type error (the variable has to satisfy both
the `effects_rows` shape and its other use sites), uniformly with how anthill
handles any over-constrained system. No separate kind-mismatch pass.

The two former binding sites (sort-level `effects E = ?` and by-position via a
function-typed parameter) remain valid — in both cases the desugaring is the
same `sort + requires` shape, just initiated by different surface forms; the
auto-requires inference fires uniformly on operation `effects` clauses
regardless of where the variable was bound. The `effects Effect` placeholder
in `prelude/collection.anthill` and `prelude/iteration.anthill` — the
`Effect` kind-marker standing in for a missing row variable — migrates to a
real bound variable at the same time.

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
effects merge(E, Modify[d]) -- the callback's effects, plus Modify[d]
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

The effect-set contract is written two interchangeable ways, both denoting the
same row:

- **`effects <expr>`** clause on an operation; **`@ <expr>`** on an arrow type
  (the *value-attached* form — a function value's effect contract travels with
  its type, mandatory for first-class functions / `apply`).

*Dropped for now* — an `ensures`-homed surface (`ensures (e in effects)` ≡ `+ e`,
`ensures (e not in effects)` ≡ `- e`, projected to the row). It is
**closed-world** (NAF: unstated ⇒ absent), so it can describe only a *closed*
row — never the open polymorphic tail (`effects E`) that dominates §5 — and it
overlaps `effects` / `@`. Revisit only if a closed-world contract-homed surface
is specifically wanted; until then `effects` and `@` are the sole
effect-declaration forms.

## 5. Checking — row unification in the typer

Effect checking is the **textbook row-polymorphism algorithm** (presence-
polymorphic rows: Rémy 1989; Lindley & Cheney 2012 for effects), run **inside
the typer** as the effects-component of arrow-type unification — *not* a generic
ACI/`Set` rewrite. This is the right home because effects are dominated by the
*polymorphic* case (`map`/`fold`/`Stream.map` carry exactly the callback's row),
which is precisely what row polymorphism is built for, and because absence on an
open row (`- e`) is exactly its **lacks**-constraint machinery — dissolving the
old "negation on open rows" hard problem rather than deferring it.

### 5.1 The row

A row is a set of **present** labels plus an optional **row-variable tail** `ρ`
(open row), and — for `- e` — **lacks** constraints on `ρ`. The tail variable is
an ordinary type variable (`Var::Global`), bound through the typer's existing
`Substitution`/`occurs_in`/`walk_type`. A label is an effect type, written `Effect[arg]`. The bracket is
type-application sugar: surface `Modify[c]` parses to
`parametrized(sym_ref(anthill.prelude.Modify), [T = c])`. The type-argument `T`
is itself a `Type`; when `arg` is a *value* name, the name-case (WI-302) wraps it
in the `denoted` entity — a `TypeExpr`, the type denoted by a compile-time value
— so the **stored** label is `parametrized(sym_ref(Modify), [T = denoted(c)])`.
Examples below stay in the surface form `Modify[c]`; the `denoted` term appears
only when the internal representation is itself the point.

### 5.2 `effect_derive` — the row a call produces

The typer derives each call's row from one specified relation (proposal 046 has
the case analysis behind its form):

```
effect_derive(callee_sig, callee_body, args, ctx)  →  output_row
```

- **`callee_sig`** — *what is called*, resolved to its **signature**. For a
  **named operation** this is its `OperationInfo` — carrying the arrow type, the
  `effects` row, *and* any `[feeds: …]` **metadata** (046 §4.2, gated on WI-309).
  For a **higher-order parameter `f`** it is just the parameter's arrow type
  (`f : … ! Eᶠ`), no metadata. **The metadata lives on `OperationInfo`, not on
  the `Type`** — the arrow `Type` (`sort.anthill`) is hash-consed and shared
  across operations, so it must stay metadata-free (two ops with the same
  signature share one arrow `TermId` but may have different `feeds`).
  `effect_derive` consults the operation's `OperationInfo` (by symbol) for the
  *declarative* feed-relationship. So `callee_sig` is the callee's **signature
  record** (`OperationInfo` for a named op; a bare arrow `Type` for a value), and
  the metadata is passed **as a field of that record** — not as a separate
  argument and not in the `Type`.
- **`callee_body`** — the callee's **body occurrence** (`operation_body`), or
  `none` for opaque/foreign callees. The *implementation* source of the
  **feed-relationship**, read only when needed (the HOF case, §5.5) and only when
  no `[feeds: …]` metadata is declared. **Source priority:** declared `feeds`
  metadata (on `OperationInfo`) → else `callee_body` → else opaque (`E` left a
  row variable).
- **`args`** — the actual arguments, each a *(denotation, type)* pair. The
  denotation resolves the callee's *own* value-parameters (`denoted(pᵢ) ↦
  denoted(argᵢ)`).
- **`ctx`** — the typing environment (provenance, active handlers).

**Correctness property:** `output_row` is **well-scoped** — it contains **no
variable bound by the callee's (or a callback's) parameters**; every such
variable is eliminated by resolving it against `args` / `callee_body`.

**Procedure:**

1. **Unify** `callee_sig`'s formal parameter *types* against `args`' types,
   binding the effect variables (`E`, tail `ρ`).
2. **Substitute** the callee's *own* value-parameters by the argument
   denotations (`denoted(pᵢ) ↦ denoted(argᵢ)`).
3. `output_row` = the effect field under (unify ∘ substitute), `∪` the
   arguments' own performed rows — **required to be well-scoped**.

Steps 1–3 cover **introduction, propagation, discharge, and first-order region
effects** (`set`, `swap`, `map`, `option_fold`, handlers): each parameter in the
effect field is the callee's *own*, resolved to its argument (in caller scope) —
so the output is well-scoped. A handler discharges *by its type* (result row =
body row minus the handled label, via a shared `ρ`).

The one case these steps do **not** make well-scoped is a **higher-order call
whose callback row references the callback's own parameter** (`foreach(λ x →
set(x))` ⇒ a stray `denoted(x)`). Making *that* well-scoped requires reading the
**feed-relationship** from `callee_body` and abstracting the result — the
implementation is deferred (§5.5, proposal 046), but the **form above is the
correct, final one**: the deferred work plugs into it without changing the
signature or the well-scopedness obligation.

### 5.2.1 Default + per-effect dispatch

Steps 1–3 are the **default** derivation: uniform, effect-agnostic
(propagate the row by unification; discharge via the handler's type). But
`effect_derive` is a **framework**, not a monolith — an effect kind may
contribute its *own* derivation for its *own* labels:

> For each effect **kind** `K` present in the row, `effect_derive` selects `K`'s
> derivation and applies it to `K`'s **slice** (the labels of kind `K`), then
> unions the slices. Kinds with no contribution use the **default**.

So an effect definition implements only its slice; adding a new effect needs no
change to `effect_derive`'s core.

**Per-effect derivation interface.** A `K`-derivation receives `K`'s slice plus
the same context `effect_derive` has, and returns `K`'s (well-scoped)
contribution to `output_row`:

```
derive_K( slice_K, callee_sig, callee_body, args, ctx )  →  derived_slice_K
   slice_K        : the labels of kind K in the input row
   derived_slice_K: K's contribution to output_row (well-scoped, §5.2)
```

**How `K`'s derivation is found** (first match wins):

1. a **rule** with the conventional functor `effect_derive`, defined **in `K`'s
   effect sort**; resolved like the `[simp]` index. Declarative transforms
   express directly over the row (e.g. handler discharge ≡ `merge(in, - e)`). A
   derivation that needs the host's dataflow (`ctx`/provenance/regions) crosses
   the **rule ↔ host boundary** in one of two directions: **pull** — the rule
   body calls a **builtin** (an implementation primitive it invokes); or
   **push** — a Rust analysis pass **emits KB predicates / stamps node
   attributes** that the rule then reads declaratively (e.g. an escape pass
   asserting `escapes(binding, result)`, or per-occurrence region attributes).
   Either way the host dataflow is *data the rule consumes*, not a separate
   dispatch path. This is how `Modify` plugs in its region resolution + masking
   (proposal 046): the heavy escape/region analysis stays in Rust, but its
   results enter the KB so the declarative `effect_derive` rule — and any other
   rule — can read them.
2. otherwise the **default** (propagate + discharge-by-type).

**v1 ships only the default** — control effects (`Error`, `Branch`) need
nothing else (their discharge is by type, sound). The first non-default
contribution is **`Modify`'s** `effect_derive` rule (fed by a region
analysis — pull or push, above), and it is **proposal 046**. So v1 is the
framework + default; 046 is `Modify`'s slice.

**Reconciling WI-314.** WI-314 shipped `Modify`'s narrow result-region masking
as a Rust pass (`kb/region.rs` `op_boundary_effects`) called **directly** at the
operation boundary — ahead of any `effect_derive` rule, since v1 ships only the
default. Under the model above that pass is precisely the **host-dataflow** half:
promoting it to *emit* its region/escape results into the KB (predicates /
attributes) for `Modify`'s `effect_derive` rule to read is what brings it under
the declarative dispatch (proposal 046). So the hardcoded pass is **not** a
divergence from this framework — it is the dataflow the rule depends on,
currently wired straight to the boundary because the rule half is not yet built.

### 5.3 Worked examples

```
introduction   set(c,v) : (Cell[T], T) → Unit ! { Modify[c] }
               effect_derive: field {Modify[c]}, c ↦ the actual arg

propagation    map(f: Function[A,B,E], xs) → List[B] ! E
               f : A → B ! { Error[T] }   ⇒ unify E := {Error[T]}   ⇒ output {Error[T]}

two HO params  option_fold(o, on_none: ()→B ! E1, on_some: A→B ! E2) → B ! merge(E1,E2)
               E1 := on_none's row, E2 := on_some's row (distinct vars), output = merge

discharge      handle : (body: ()→X ! { Error[T], ρ }) → X ! ρ
               body : ()→X ! {Error[T], Modify[c]}  ⇒ ρ := {Modify[c]}  ⇒ output {Modify[c]}

—— the one deferred case (proposal 046, §5.5) ——
HOF+param      foreach(λ x → set(x, …)) ⇒ naïvely { Modify[x] }   -- x escapes: ILL-SCOPED
               well-scoped output needs callee_body (x ↦ elements(xs)) + region abstraction
threading      foldLeft(xs, z, f: (B,A)→B) — same: callback params acc/elem need resolving via
               callee_body, then abstraction; deferred to 046.
```

The five above are well-scoped (each parameter is the callee's own, resolved to
its argument). `option_fold`: two HO params ⇒ two *distinct* variables, combined
by the declared `merge(E1,E2)`. The last two are the §5.5 deferred case: a
callback whose row references *its own* parameter.

### 5.4 Checking an operation

1. **Compute the body row** by `effect_derive` over the body (structural forms —
   `let`/`if`/`match`/`lambda` — default-propagate the union of children; a
   `lambda` parks its body row on its arrow).
2. **Unify / subtype against the declared row** (the row-rewrite rule): to match
   `{ l, ρ1 }` against another row, surface `l`, unify the presences, unify the
   tails; an open declared row absorbs extra actual labels into its tail, a
   closed one does not; a `- e` declaration adds `lacks e` and **fails if the
   actual row presents `e`**.
3. Result: **satisfies** or a **type error** (undeclared effect against a closed
   row, `lacks` violation, or `merge` conflict).

This *replaces* today's two half-measures: `unify_arrow` (`typing.rs`) currently
**skips the effects field entirely**, and `arrow_compatible` does only a naive
positional `⊆` subset check with no row variables.

### 5.5 The deferred boundary — the one ill-scoped case (proposal 046)

There is exactly one case the §5.2 steps do **not** make well-scoped: a
**higher-order call whose callback row references the callback's own parameter**.
`foreach(λ x → set(x, …))` would yield `{ Modify[x] }` — but `x` is the
*callback's* parameter, bound by its arrow; at the `foreach` call there is no
argument to substitute it with (`foreach` binds `x` to elements of `xs` only
inside its *own body*). That output mentions `x` but not `xs` — **ill-scoped**,
which the §5.2 correctness property forbids.

Producing a well-scoped output here requires reading the **feed-relationship**
from `callee_body` (`x ↦ elements(xs)`), then **abstracting** the resulting
*unbounded* per-iteration denotations (`denoted(h)` for every `h ∈ xs`) into a
finite **region**, and applying **provenance/masking** (is the region an *input*
parameter or a *fresh output*?). That implementation — region abstraction, escape
analysis, the recursion fixpoint — is the subject of **proposal 046** and is
deferred *in detail*. The `effect_derive` **form (§5.2) is already correct**: it
takes `callee_body` and obliges a well-scoped output; 046 only fills in the body.

Note: a mutable constructor like `Cell.new` has row `{ Modify[result] }` — it
initializes the region it returns, and `result` flows out (it is the return), so
the label is well-scoped. So `map(λ x → Cell.new(x))` is honestly
`{ Modify[result] }` (it modifies the fresh cells it returns); whether a write to
a freshly-returned region is *observable* is the provenance/masking question —
and its narrow **result-reachability slice is now delivered (WI-314)**: an
operation-boundary mask (`kb/region.rs`) **drops** `Modify[result]` when the
operation's return type cannot carry the region (the cell is discarded —
`make_and_read : Int`) and **keeps** it, re-keyed to the op's own `result`, when
it can (`make : Cell`), so `Cell.new` is non-viral. The **full** provenance /
aliasing answer — and the region reachable only through a returned named sort's
field (WI-316) — remains **proposal 046**. Either way it is masking, not a
separate `Alloc` effect.

**Phasing.** v1a: open rows with present labels + tail variable — real row
unification in `unify_arrow`, open-row subtyping in `arrow_compatible` — covering
polymorphic propagation. v1b: `lacks` constraints for `- e`. The region layer
(resolution + provenance + masking) is **proposal 046** — except its narrow
result-reachability mask, **delivered in WI-314** (`Modify[result]` at the
operation boundary; see the `Cell.new` note above).

### 5.6 Handler discharge (the static check)

Discharge is **045's** side; proposal 027 supplies the runtime handler — the
`HandlerAction` carrier, continuations, the standard catalog — that *realises*
the contract this type describes. 045 models none of that machinery; it checks
only the **row**.

A handler that discharges effect `K` has a type that **shares a row tail** `ρ`
between its body parameter and its result, with `K` **present** on the body side
and **absent** from the result:

```
handle_K : (body: () -> X ! { K[…], ρ }) -> X ! ρ
```

Checking a call `handle_K(λ → e)` is then **ordinary row unification** (§5) — no
special machinery:

1. derive `e`'s row by `effect_derive`;
2. unify it against `{ K[…], ρ }` — surface the `K` label and bind the tail `ρ`
   to the **residual** (everything in `e`'s row other than `K`);
3. the call's row is `ρ`: `K` is **dropped**, every other effect propagates.
   So `e : () -> X ! { Error[T], Modify[c] }` under `handle_Error` gives
   `ρ := { Modify[c] }`, output `{ Modify[c] }` (the §5.3 example).

Because discharge is carried entirely by the handler's **type** (a shared tail,
label present → absent), it is the **default** derivation (§5.2.1): sound for the
control effects (`Error`, `Branch`) and available the moment v1a's row
unification lands — no per-effect rule. v1 discharges a **single named** label
per shared tail; discharging a *statically-unknown effect-set* at once would need
`difference` (§7 item 4, deferred) — until then, name the handled labels and
discharge them one tail at a time.

## 6. Representation (reflect) and reconciliation

Four substrate pieces, three of them new (variant 7):

1. **`EffectExpression`** — the row algebra reflect sort (G1, retained;
   `stdlib/anthill/prelude/effect-expression.anthill`): an `enum` with
   `empty_row` (`{}`), `present(label)` (`e` / `+e`), `absent(label)` (`- e`
   ⇒ a `lacks`), `open(tail)` (a row-variable tail `E` / `?`, carried as a
   `Type.type_var`), and `merge(left, right)` (union; the set literal `{…}` is
   iterated `merge`). It is **both** the §3 surface algebra *and* the stored
   inner representation — its **normal form** (present labels + optional tail
   + `lacks`, `merge`s flattened) is the row the typer unifies. (Closes the
   G1 representation gap; also settles the §5.3/§5.4 `{ l | ρ }` vs §3
   `{ …, ? }` tail-notation split in favour of the `open` element form
   `{ …, ρ }`, now applied throughout §5.) `EffectExpression` does **not**
   belong to `Type`; it is its own reflect sort, *wrapped into Type by item
   (2)*.

2. **`Type::effects_rows(EffectExpression)`** — a **new variant** of the
   `Type` enum, in `stdlib/anthill/prelude/sort.anthill`, parallel to the
   existing `denoted(NodeOccurrence)`. This is the bridge from the row algebra
   (1) into `Type` position, so an effect-row can sit in a sort's type-arg
   slot (notably `EffectsRuntime[Effects = effects_rows(...)]`) and so
   `Type.arrow`'s `effects` field can carry it. The variant has no behavior of
   its own — it's a pure structural wrapper, exactly like `denoted`.

3. **`EffectsRuntime` carrier sort**
   (`stdlib/anthill/prelude/effects-runtime.anthill` or merged into
   `effects.anthill`):

   ```
   sort EffectsRuntime
     sort Effects = ?
   end
   ```

   **Pure kind anchor** — no entities, no operations. Exists so the desugaring
   of §2's `effects E = ?` clause (`sort E = ? requires EffectsRuntime[E]`)
   has a real sort to constrain against. (The handler-bundle role for this
   sort — capability-passing dispatch — is captured as a brainstorm follow-on,
   not adopted here; see §"Out of scope".)

4. **Loader-emitted bridge rule + auto-requires inference:**

   ```
   rule type_of(?occ, EffectsRuntime[Effects = effects_rows(?expr)])
     :- is_entity_of(?occ, effects_rows(?expr))
   ```

   plus the loader pass that walks each operation's `effects <expr>` clause,
   collects free variables, and emits `requires EffectsRuntime[Effects = E_i]`
   per free var (§2.1).

**`Type.arrow.effects` field.** Today `List[Type]` (each element a label).
Under this proposal: **singular `Type` of `effects_rows(merged_expr)` shape**
— one row per arrow, matching the brainstorm's "surface and row are one
sort." Wiring the arrow field + the row unification is **WI-307**; the
target shape it builds against is item (2) wrapped around an
`EffectExpression` normal form. (A staged migration may temporarily keep
`List[Type]` with each element constrained to `effects_rows`-shape; the
singular form is the target.)

**`Function.E`** is now declared as `effects E` (§2), which desugars to
`sort E = ? requires EffectsRuntime[E]` — correctly kinded without a new
binder. `PureFunction = Function[…, E = effects_rows(empty_row)]`.

**Effect checking is row unification in the typer — not generic ACI/`Set`
rewriting.** The row-rewrite rule lives in `unify_arrow` /
`arrow_compatible` (`typing.rs`), using the typer's existing type-variable
substrate for the tail variable. `unify_arrow` pattern-matches on `Type`
variants; the new `effects_rows(...) ↔ effects_rows(...)` arm extracts the
inner `EffectExpression`s and runs the row-rewrite on them. Other `Type`
variants do term unification, same as today.

The `[simp]`/ACI/canonical-`Set` substrate (earlier drafts) is **decoupled
from effect checking** — it remains only as optional machinery for *general*
sets (and the runtime effect catalog), not on the checking path. `Set` stays
orphaned until a general-set consumer needs it; **`EffectSet` was removed**
(2026-05-28) — superseded by the `EffectExpression` reflect sort (now
wrapped into `Type` by `effects_rows`, not used as a standalone).

### Out of scope (captured for follow-on)

The brainstorm's 2026-05-28 addendum ("`EffectsRuntime` as the
handler-bundle witness") proposes extending the `EffectsRuntime` sort with a
`perform` operation, a `merge` composition rule, and a witness-based
dispatch path — collapsing 027's ambient-handler registry, 027.1's
allocator dispatch, and 037's `Modifiable[T]` gate into a single witness.
That direction **is not adopted in this proposal**. This proposal lands
only the variant-7 substrate (items 1–4 above); 027 and 027.1 continue to
use the ambient-handler model unchanged. The capability-passing direction
is captured in the brainstorm as a strictly-additive follow-on for a later
proposal.

## 7. Open questions / hard points

1. **Negation on open rows — *resolved* by row polymorphism (no longer a hard
   part).** Adopting row unification in the typer (§5) means `- e` on an open row
   is just a **lacks constraint** on the tail variable `ρ` (`ρ lacks e`), the
   standard presence-polymorphic mechanism (Rémy 1989; Lindley & Cheney 2012). It
   is checked *abstractly at definition time* — no waiting for `E` to be ground,
   no laziness hack: unifying a row that presents `e` against a tail carrying
   `lacks e` fails directly, and the constraint propagates to call sites through
   ordinary tail-variable unification. So `effects merge(E, - Modify[kb])` ("this
   function forbids its callback from modifying kb") is a row `{ …, ρ }` with
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
   stabilizes. **Resolved (WI-317 implements):** the fixpoint runs over **ground**
   rows — an operation's *own* effects over the finite set of effect labels
   occurring in the program — so the ascending chain is over subsets of a finite
   set and stabilises by ACC. Open/co-finite rows do **not** enter the fixpoint:
   a polymorphic tail variable (`ρ`) or a `lacks` is *propagated by row
   unification*, not *grown* by the `union` ascent, so nothing grows without
   bound. Scheduling is the **typer's, not the resolver's**: inference walks the
   call-graph **SCCs** (acyclic order between SCCs; within a cyclic SCC iterate
   from `{}` to stabilisation), memoising `op_effects` per operation, so a
   declarative `effect_derive` rule (§5.2.1) is evaluated against the *current*
   estimate each iteration rather than recursing through SLD (which would loop).
   The *checked* model (v1a) needs none of this — a recursive call reads the
   callee's *declaration*; the fixpoint is only for **inferred** effects
   (WI-317).
4. **Grammar surface — *resolved for `{…}`*; `difference` deferred.** The set
   literal `{ E1, …, EN }` is sugar for iterated `merge` (§3), so it adds no new
   semantics. We have `merge(x, y)` for **union** and `- e` for **removing one
   named effect**. *Decided — not in v1:* there is **no** whole-effect-set
   subtraction operator `difference(E1, E2)`. It would matter only for **handler
   discharge of a statically-unknown effect-set**; whenever discharge *names* the
   handled effects, repeated `- e` suffices. `difference` is introduced later
   **only if** such a variable-set discharge case actually arises.
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
6. **Operation effect-parameter binding (was: WI-318) — *resolved* by adoption
   of variant 7 (§2.1).** The earlier debate over how to bind an effect-row
   variable in a free standalone operation's type-parameter list (a new
   `[…, effects E]` slot, a kinded quantifier `[E: Effects]`, a separate
   bracket, a marker) is dissolved. Under variant 7, `[A, B, E]` is uniform,
   the `effects E` clause is the binding site, and the loader auto-emits
   `requires EffectsRuntime[E]` per free variable. **WI-318 closes on
   adoption of this proposal.**
7. **Grammar position for the `effects` item-keyword — *open, narrow*.** The
   new `effects` keyword at sort-item position (§2) is disambiguated by
   position from the existing post-signature `effects (…)` clause; the
   grammar addition is confirmed-trivial but to be specified concretely
   alongside WI-307.
8. **`Type.arrow.effects` shape — *target singular, migration possibly
   staged*.** Target shape is singular `Type` of `effects_rows`-form (one row
   per arrow). A staged migration may temporarily keep `List[Type]` with each
   element constrained to `effects_rows`-shape; the collapse to singular is a
   follow-on of WI-307.

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
  *checking*, and reframes `sort E = ?` effect params as `effects E = ?`
  (which under variant 7 desugars to `sort E = ? requires EffectsRuntime[E]`
  — the kind is now carried by the `requires` constraint, not by a parallel
  binder substrate).
- **003 (Effect Annotations on Arrow Sorts)** — `@ <expr>` generalizes the arrow
  effect annotation to a full effect expression.
- **027 (Effect Handlers)** — handlers *discharge* effects (`\`); the runtime
  catalog is 027's, the static checking is here. This proposal keeps 027's
  ambient-handler model unchanged; a capability-passing alternative
  (`EffectsRuntime` as the handler-bundle witness) is captured as a
  brainstorm follow-on but is **not adopted here** — see §"Out of scope" in
  §6.
- **WI-301 (effect-set type args)** — *subsumed / reframed*: effect-sets are not
  raw type arguments; they're `effects_rows(...)`-shape `Type` values that
  bind to `EffectsRuntime.Effects` (and to `arrow.effects`).
- **WI-302 / `denoted`** — the *type-level* analog (a type denoted by a
  computed expression); effect expressions are the same idea for effect-sets,
  and `effects_rows` is the same `Type`-enum-variant pattern (`denoted`
  wraps a `NodeOccurrence`, `effects_rows` wraps an `EffectExpression`).
- **WI-307 (wire `arrow.effects` → row)** — implements §6's substrate items
  1–4 plus the singular `Type.arrow.effects` migration; row unification in
  `unify_arrow` builds against the `effects_rows(...)` variant.
- **WI-318 (operation effect-var binding)** — ***closes on adoption of this
  proposal***. The candidate surfaces it tracked (variants 1–6 of the
  brainstorm's 2026-05-27 chapter) are dissolved by variant 7's auto-requires
  inference — uniform `[A, B, E]` list, kind carried by `requires`, inferred
  from the `effects` clause.

## Next steps

The checking algorithm is **row unification in the typer** (§5), not the
ACI/`Set` substrate. Phases (variant-7 substrate first, then row checking):

0. **Substrate — variant-7 ingredients.** Add the
   `effects_rows(EffectExpression)` variant to the `Type` enum
   (`stdlib/anthill/prelude/sort.anthill`). Add the `EffectsRuntime` carrier
   sort (pure kind anchor; `stdlib/anthill/prelude/`). Emit the
   `type_of(?occ, EffectsRuntime[Effects = effects_rows(?expr)])` bridge rule
   from the loader. Implement the auto-requires inference pass walking each
   operation's `effects <expr>` clause and emitting
   `requires EffectsRuntime[Effects = E_i]` per free variable. Add the
   `effects` keyword at sort-item position, desugaring to
   `sort + requires EffectsRuntime[…]`. Migrate `Function.E`, `Stream.E`,
   and the `effects Effect` placeholders in `prelude/collection.anthill` /
   `prelude/iteration.anthill` to the new declaration form. (No row
   *checking* yet — just the substrate the checking will build against.)
1. **v1a — row unification (open rows, presence only).** Represent the
   `arrow.effects` field as `Type` of `effects_rows(...)`-shape (singular;
   staged migration may keep `List[Type]`-with-each-element-of-`effects_rows`-
   shape temporarily — see §7.8). Implement the row-rewrite rule in
   `unify_arrow` (which today skips effects entirely) — adding the
   `(effects_rows(e1), effects_rows(e2)) → unify_row(e1, e2)` arm — and
   open-row subtyping in `arrow_compatible` (today a naive `⊆` subset
   check). Covers polymorphic propagation — the common case.
2. **EffectExpression surface + grammar** (`+`/`-`/`merge`/`{}`/`E`),
   elaborating to an `EffectExpression` wrapped in `effects_rows(...)`;
   binding sites on operations / arrows.
3. **v1b — lacks constraints.** Add `- e` absence guarantees as `lacks`
   constraints on the tail variable (§7.1), checked abstractly at definition
   time.
4. **Handler discharge** (§5.6) — the handler's shared-tail type drops the
   handled label by row unification; wire it to proposal 027's runtime
   handlers (under the ambient model — capability-passing via the
   `EffectsRuntime` witness is a captured follow-on in the brainstorm
   addendum, not in this proposal's scope).
5. **Migrate `typing_pass_spec`** effect handling onto row unification; only
   then is its effect-checking honest.
6. *(Optional, decoupled.)* The `[simp]`/ACI/canonical-`Set` substrate, only
   if a *general*-set consumer appears — not needed for effect checking.
