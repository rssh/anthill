# WI-502 — Constrained-term substrate (type-directed firing on the prove path)

## Status

Design — converged 2026-06-26. **Supersedes the scope of** [`typed-term-carrier.md`](./typed-term-carrier.md),
which framed this narrowly as a `min_sort` *sidecar* on a hash-consed term. That framing
was correct but minority-centric: it organized the design around the interned `TermId`,
when in fact most terms in resolution are non-interned `Value`s. This spec reframes the
work as a **constraint substrate** of which *type is one kind*, and is carrier-centric.

**Cluster:** WI-292 (resolver-side type-directed `[simp]`), WI-567 / WI-566 (guard discharge
over rule-defined predicates). **Builds on:** WI-328 (the `lacks` constraint side-table),
WI-537 (the Γ `Env{types,flow}` local-interpretation substrate), WI-109 (`Value::Var`),
WI-246 (rule body atoms as occurrences). **Proposals:** 043 §4 (`[simp]`), 049 (`<=>`),
045/046 (effect rows), 050 (Γ).

## Why

The SLD resolver holds **type-erased** terms, so it cannot fire type-directed rules on the
prove path:

- **WI-292 / 043 §4:** type-directed `[simp]` fires in the typer (`simp_fire_guard_holds`,
  `typing.rs`) over typed occurrences, but the resolver holds erased terms and
  `equation_is_requires_guarded`-**skips** the same rules.
- **WI-567 / WI-566:** a guarded effect `head(l) … { Error[EmptyList] :- isEmpty(l) }` will
  not discharge, because *refuting* `isEmpty(l)` / `Eq[List].eq` requires their type-directed
  definitions fired on the prove path; the definitional chain bottoms out in a spec op
  (`splitFirst`) the erased resolver cannot dispatch. Only native-scalar guards (`eq(b,0)`
  over `Int64`) discharge today.

**Goal:** type-directed reasoning on the prove path that **reads** a term's type rather than
**re-deriving** it. A second, structurally re-derived notion of type can drift from the
typer's — explicitly rejected.

## Model — the load-bearing invariants

**M1 — Untyped kernel, by stratification.** The resolver *computes* the type relation:
types are terms, `subsort`/instance membership are facts, type-unification is SLD. So the
kernel sits **below** the type layer and must never branch on a type (else: regress).
`unify` / `match` / `discrim` stay structural and type-blind. **Type-specificity is an
untyped guard over type-terms**, not a typed mode. The surface `add(?x: Int, ?y: Int)`
**desugars** to a guard (`min_sort(?x) = Int …`); the engine sees one more goal, never a
"type." Hash-consing surviving (the old doc's argument) is a *symptom* of M1, not its root.

**M2 — Type is one kind of constraint.** Anthill already runs a constraint system — for
*effects* (row-polymorphism + `lacks`, WI-307/WI-328). Generalize it: the `lacks`
side-table becomes a **tagged constraint store**; type-constraints (`subsort`,
`min_sort = T`, disequality) are kind #2. A *constrained term* is a `(skeleton, store)`
pair, and the resolution answer generalizes **σ → (σ, residual C)**: an undecided
type-guard is not a failure to delay around — it is a residual constraint in the answer.

**M3 — Carrier-centric, not `TermId`-centric.** Most terms are `Value::Node`/`Entity`/`Var`
— per-environment, non-shared — and carry constraints directly (a `NodeOccurrence` already
has `inferred_type`). The hash-consed `Value::Term(TermId)` is the *minority* and the *only*
carrier needing external pairing. The real invariant is **shared vs per-environment, not
TermId vs Value**: a constraint may sit *on* a carrier iff the carrier is per-environment;
shared carriers route through the per-branch store. **A value's type caches on its carrier,
per variant:** `Value::Node`'s `inferred_type` slot; a scalar's trivial literal-kind; and for
the shared `Value::Term(TermId)`, an external **`(type, inner)` pair wrapper** — the
per-environment type can *never* sit on the shared `TermId` itself, so a bare `Value::Term`
has no cache home until it is wrapped. (WI-348: logic never materializes a `TermId` from a
`Value`.)

**M4 — Two homes, split by firing-invariance.**
- *Static type of an occurrence* (the same across every firing) → on the per-occurrence
  carrier (`NodeKind::Expr.inferred_type`). Shared is safe *because* it is invariant.
- *Per-branch refinement* (`?x := Int64` in this proof) + *all var-coupled constraints* →
  the per-branch **substitution store**, keyed by `VarId` (where `lacks` already lives).

**M5 — Functional model ⇒ explicit wakeup (no attributed-variable cells).** In this engine a
variable is an inert `VarId(u32)`, a binding is an entry in `Substitution.bindings:
HashMap<VarId, Value>` (there is **no** `Binding` type), and a branch is a *clone* — there
are no mutable variable cells and no trail. SWI/SICStus attributed variables (cell + unify
hook + trail) are therefore **not reachable** without reifying variables and abandoning
clone-branching. So we **emulate** them: a parallel `VarId`-keyed constraint map on the
substitution, with **wakeup invoked explicitly at every bind site** (no auto-hooks). This is
exactly why `lacks` works in the typer (`bind_row_tail` calls it) and is inert in the
resolver (`bind_compressed` does not).

**M6 — Compute once; carry by the ops already running.** The type is inferred once at the
typing boundary and maintained by the *same* De Bruijn opening + substitution the resolver
already performs — because the type shares the term's logical variables, **σ is type
refinement for free**. **Binding is navigation, not caching:** `min_sort(?x)` *follows*
`?x`'s binding to a value and reads **that value's carrier cache** (M3) — the cache is on the
value, never on the binding edge. An *unbound* `?x` has no value; its type comes from its
constraint in the store (M4), or is unknown. A value's cache is established **once** when it
first acquires a type (a bare `Value::Term` is wrapped into its `(type, inner)` pair then —
else it has nowhere to cache and recomputes). **Never memoize by bare `TermId`**
(per-environment: `nil : List[?T]`). Re-derivation is confined to two bounded, *loud* points:
the resolver/simplify **entry** (untyped today — widen the typing boundary there) and
**refresh boundaries** where σ cannot link the type's vars (surface loudly, never silent
drift).

**M7 — Lifetime is branch-scoped and already correct.** A constraint must live from its
birth step until a result row, dying on backtrack — the *same* lifetime as a binding. The
resolver **already provides this**: every frame push does `frame.subst.clone()`
(`resolve.rs:1667`, `1712`, `1626`), which deep-copies the whole chain including `lacks`;
popping frames on backtrack discards branch-specific constraints. (Correction to an earlier
read: the substitution *object* is per-frame, but its *content* has branch lifetime via
clone-threading — "substitution is one-step" is a red herring.) The genuine gaps are **not**
lifetime: (a) no *wakeup* — `bind_compressed` never discharges carried constraints against
new bindings; (b) a constraint *generated* into a throwaway per-step `extra` would be
dropped (does not occur today, but would bite naïve resolver-side generation).

## Two shapes of type-directed firing (both read one constrained carrier)

- **Shape A — instance dispatch (monomorphize at the boundary).** `eq`, `isEmpty`,
  `splitFirst` resolve to a concrete instance (`Eq[List].eq`, `List.splitFirst`). The typer
  already knows the instance (`lookup_spec_op_dispatch`); **rewrite the body-atom/guard
  functor to the resolved instance's qualified symbol before it reaches the resolver.** The
  existing structural discrim tree (`DiscrimKey::Functor`) then indexes it by that distinct
  symbol — *the "type indexing" problem dissolves; the type was used transiently to pick a
  name.* Covers WI-567.

- **Shape B — type side-condition (untyped guard).** `add(?x, 0) = ?x` is one polymorphic
  rule guarded by a type predicate. There is nothing to monomorphize: the rule is retrieved
  structurally, the **type flows from the typed redex into `?x` at unification** (M6), and an
  untyped guard (`subsort(min_sort(?x), Numeric)`) fires-or-not. Covers WI-292.

These nest: in `add(?x, 0) = ?x` the literal `0`, read as the generic `zero[T]`, is a Shape-A
dispatch *inside* a Shape-B law. Whether `0` denotes `zero[T]` (generic) or a literal
(monomorphic) is a modeling choice the carried type of `?x` disambiguates at firing.

## Limitation ↔ generation (CLP/CHR framing)

A constraint both *prunes* and *generates* (CLP labeling; CHR propagation):
- **Limitation / check (now):** discharge `subsort(min_sort(?x), Numeric)` against sort facts.
- **Generation / label (later):** when forward progress needs an underdetermined type —
  `requires Numeric[?T]` with `?T` unbound — *enumerate* admissible instances. Dispatch under
  uncertainty **is** labeling.

We adopt the *frame* at the representation level now and **stage the power**: check + suspend
ships first; generative labeling is deferred (opt-in, same representation). Bound the
constraint *language* to **decidable fragments** — sort-lattice `subsort`, instance facts,
disequality. Arbitrary-predicate / full-refinement constraints (where satisfiability and the
NAF interaction get hard) are a door opened deliberately, not by drift.

## Implementation plan (staged; each step lands independently)

**Step 0 — Persistent substitution substrate (prerequisite refactor; WI-569).**
Swap `Substitution.bindings: HashMap → imbl::HashMap` (`imbl` is already a direct dep,
`anthill-core/Cargo.toml:18`; precedent: `eval/map_arena.rs`). `imbl`'s API mirrors `std`'s,
so all ~37 `.bindings` call sites compile unchanged; the one real edit is `bind_compressed`
(`subst.rs`), whose in-place `iter_mut` path-compression becomes collect-keys + a fold of
functional `insert`s (a persistent map has no `iter_mut`). **The parent chain is kept** —
closer reading showed it is *not* a cost problem: hot-path frame substs are always
`parent = None` (built flat via `clone()` + `bind_compressed`), so their clone is O(1) once
`bindings` is persistent; the only parented subst is the transient `work` in `builtin_unify`
(`resolve.rs:3046`), shallow and never stored in a frame. Parent removal is therefore optional
cleanup, deferred. *Behavior-preserving.* Payoff: every `frame.subst.clone()` becomes **O(1)**
with no call-site edit — converting per-step copy from O(depth × bindings) to O(depth) (the
WI-537 Γ shape) — and the Step-1 constraint store rides along as a free O(1)-clone field.
Validate with `scripts/test.sh` + `/code-review`.

**Step 1 — Constraint store.** Generalize `lacks` into a tagged, persistent (`imbl`)
`VarId`-keyed store on `Substitution`; `lacks` = kind #1, type-constraint = kind #2.
Expose residual `C` on the answer. Write-mostly (no new consumer yet), as Γ was after WI-537.

**Step 2 — Carry + wakeup in the bind path. *(DELIVERED — generic core + loud guard.)*** The
literal "one in-line choke-point that wakes" framing collided with the architecture, so the
delivered shape is a **generic core + a loud bypass guard**, leaving the working effect-row
path specialized. Two findings drove this: (i) `bind_row_tail`'s lacks CHECK validates the
*labels being merged in* and needs the typer's effect-row decomposition vocabulary — **not
available in `subst.rs`**, so it cannot be subsumed by a generic in-`Substitution` wakeup;
(ii) the low-level bind methods sit on the resolver hot path and bind synthetic/alias vars, so
an in-line wakeup would double-fire with `bind_row_tail` and run on every path-compression
repoint. Delivered:
- **Carry-through-merge** (M7(b)): `Substitution::absorb_constraints` unions another subst's
  top-level store; wired into the resolver's `SuccessWithBindings` lift (the single funnel for
  every builtin `extra` + `builtin_unify`'s `work`) and the reflect `subst_compose`. (The
  `&dyn Substitution` `bridge.rs` compose can't reach `s2`'s constraints across the trait
  boundary — documented limitation, extend the trait when a self-hosted producer needs it.)
- **Wakeup choke-point**: `Substitution::bind_waking` does **merge-on-alias** (binding
  `?x := ?y` moves `?x`'s constraints onto `?y`); the per-kind CHECK is staged — `Type` →
  Step 5, `Lacks` → stays in `bind_row_tail`. Wired into the resolver's value-bind sites.
- **Loud-on-bypass** (M7(a)): `bind_compressed` (synthetic/resolver-only) asserts the bound
  var carries no constraints, so a constraint-carrying var that bypasses `bind_waking` fails
  **loudly** rather than dropping the wakeup (gated on a non-empty store → free on the hot path).
`bind_row_tail` is unchanged: it is the typer-specialized instance of the same pattern, sharing
the store plumbing + the `push_constraint_deduped` dedup. Write-mostly still — no resolver-side
producer until Step 3, so the wakeup is exercised by tests only.

**Step 3 — Static type on the carrier + read API. *(DELIVERED — core A+B; C+E deferred to Step 5.)***
Delivered:
- **(A) Stop dropping `inferred_type` on open/subst** (the original WI-502 bug):
  `NodeOccurrence::rebuilt_expr` carries the typer-stamped type (and `Synthesized`
  provenance) through every occurrence rebuild — `simp_rewrite::reassemble`,
  `open_debruijn_node`/`node_to_debruijn` tails, the `substitute_occurrence` tail. The carry
  is VERBATIM: sound because `min_sort` reads only the SORT HEAD, which is functor-determined
  (a rebuild keeps the same functor) and so invariant under the type-parameter refinement a
  child substitution performs; a var-head reads `None`, never a stale concrete sort (the M6
  refresh-boundary guarantee, satisfied by head-only reads — no type re-derivation).
- **(B) `min_sort_of_value(kb, σ, value)`** — the value-level read API (M6 "binding is
  navigation"): a var follows its σ-binding (cycle-guarded loop, since SLD σ is not
  occurs-checked) → reads the bound value's carrier cache; a `Value::Node` reads its
  `inferred_type`; a scalar reads its literal-kind; an unbound-but-constrained var falls back to
  the Step-1 store (`type_constraints_of`). A bare constructed `Value::Term` reads `None`.
Deferred to Step 5 (WI-292), the consumer that exercises them: **(C)** the compute-once entry
(re-typing the untyped `apply_eq_rules` prove/simplify entry — its `TermId` redex carries no
stamp), and **(E)** the `(type, inner)` pair wrapper for a bare `Value::Term` (a `Value::Typed`
variant is too invasive — 1844 `Value::` arms / WI-538 silent-wildcard trap — so a narrow
external pair at the boundary, when Step 5 needs it). Still write-mostly: `min_sort_of_value`
has no production caller and `add_type_constraint` no producer until Step 5; the loud refresh
boundary is the head-only read returning `None` rather than re-deriving (M6).

**Step 4 — Shape A monomorphization at the typing boundary.** Rewrite type-directed spec-op
calls in rule bodies / guarded-effect guards to the resolved instance's qualified functor via
`lookup_spec_op_dispatch` over the carried type. **Unblocks WI-567.** Naming: a distinct
functor `Symbol`; identity stays `RuleId` — do **not** reintroduce QN-as-identity (the WI-558
duplicate-QN trap). An op-vs-rule disambiguation suffix only if a real collision appears.

**Step 5 — Shape B guard firing in the resolver.** The guard is *recorded at load*
(compute-once): from the explicit `?x: T` surface, or derived by the typer from the
operation's signature / enclosing sort (e.g. `add : Numeric → … ⊢ ?x : Numeric`) — never
re-derived per firing. **Checking an input `v` against `?x : Numeric` is then three untyped
reads:** (1) σ binds `?x := v`; (2) `min_sort(v)` reads `v`'s carrier cache (M3) — head-sort
for a constructed value, literal-kind for a scalar, the store's bound for an unbound `v`;
(3) `subsort(min_sort(v), Numeric)` is an ordinary **SLD query over sort/instance facts**
(M1) — no typed engine. Outcome: succeed → fire; `min_sort(v)` known but not `<: Numeric` →
don't fire; **`min_sort(v)` under-determined ⇒ suspend** the guard as a residual constraint,
never NAF-decide (the WI-067 `var_ref`-non-ground hazard, one level up). **This is WI-292**,
now standing on the substrate; all soundness lives in the suspend rule.

**Step 6 — Generative labeling (deferred).** Enumerate instances for an unbound-type dispatch.
Opt-in, same representation. Out of scope for first delivery.

## Soundness watch-points

- **Flounder, don't decide.** Under-determined carried type ⇒ suspend as residual `C`; a
  negative/NAF guard over a runtime-unknown type must not succeed *or* fail (WI-067).
- **No QN-as-identity.** Monomorphic FQN is a *functor symbol*; rule identity stays `RuleId`
  (WI-558).
- **No silent drop.** The choke-point bind API fails loudly if bypassed (Step 2).
- **Decidable fragment only** (Step §limitation↔generation).
- **Never on the interned `TermId`** (M3).
- **A value's type cache needs a home before it is read.** Binding does not cache it; the
  carrier does (M3/M6). A bare `Value::Term` read for its type with no pair wrapper recomputes
  — the compute-once boundary must wrap it. The pair caches the **root** type (enough for
  whole-value guards / Shape-A dispatch); **subterm** type reads are O(1) only when subterms
  are themselves cached carriers (structural `Value::Node`), and recompute on bare
  `Value::Term` subterms. Known limitation; revisit if guards read subterm types.

## Unblocks

- **WI-567** (concrete `head` discharge via Step 4), **WI-292** (resolver `[simp]` via Step 5),
  **WI-566** (Phase-4 discharge over rule-defined predicates).

## Prior art & in-repo precedents

CLP / CLP(FD), attributed variables, CHR (propagation = "limitation becomes generation"),
order-sorted logic, refinement types ("type is a predicate"). In-repo: `lacks` side-table
(WI-328), Γ `Env{types,flow}` (WI-537), `imbl` persistent maps (`eval/map_arena.rs`), the
typer's `lookup_spec_op_dispatch` / `simp_fire_guard_holds`.

## Decisions recorded (do not re-litigate)

1. Keep the **functional** unification model; do **not** reify variables into cells + trail.
2. The **substitution is the home** for var-coupled constraints — lifetime-correct (M7), made
   cheap via `imbl` (Step 0). Attributed-variable behavior is *emulated* with explicit wakeup.
3. **Check + suspend now; label later**; decidable fragment only.
4. **Shape A monomorphizes at the boundary; Shape B guards in the resolver.** Both read one
   constrained carrier.
5. Type lives on the **per-environment carrier / per-branch store**, **never** on the interned
   `TermId`.
