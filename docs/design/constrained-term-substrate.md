# Typed terms — values and variables carry their type

## Status

Design — **origin** 2026-06-20 (as `typed-term-carrier.md`), generalized 2026-06-26, **converged
2026-06-27** (this doc merges the two). This file is now the single live design; it folds in
[`typed-term-carrier.md`](./typed-term-carrier.md) (reduced to a redirect) and **supersedes** the
earlier "constraint substrate / Shape A–B / `min_sort`-builtin" framing that lived here — see
*§Decisions* for what was dropped and why.

**Foundation for** typed *rule patterns* (the WI-502 goal). **Consumers (dependent tickets):**
WI-292 (type-directed `[simp]` firing), WI-573 (guarded-effect guard discharge), WI-567 / WI-566
(guard discharge over rule-defined predicates), **runtime monomorphization** (dispatch on a
value's carried type). **Builds on:** WI-328 (the `lacks` constraint side-table), WI-537 (the Γ
`Env{types,flow}` substrate), WI-109 (`Value::Var`), WI-246 (rule-body atoms as occurrences).
**Proposals:** 043 §4 (`[simp]`), 049 (`<=>`), 045/046 (effect rows), 050 (Γ).

## Why — type-dependent rules

WI-502 originated as **"how do we work with type-dependent rules."** Two gaps block it:

1. **No syntax for typed rule patterns** — no way to *write* a rule whose pattern is conditioned
   on a type (a LHS that matches `add(?x, ?y)` only when `?x : Numeric`).
2. **No machinery in the resolver to match them** — even given the syntax, the resolver holds
   type-erased terms and cannot evaluate a pattern's type-condition.

Native type-directed `[simp]` rules not firing is a *symptom* of these gaps: the typer fires them
(`simp_fire_guard_holds`) over typed occurrences, but the resolver `equation_is_requires_guarded`-
**skips** them because it has no type to read. The foundation under both gaps is the same — **terms
and rules carry their type**, so type-directed reasoning **reads** the type rather than
re-deriving it (a second, structurally re-derived notion of type can drift from the typer's —
explicitly rejected).

## The primitive — `typed(untyped-value, env) → typed-value`

Typing is an operation: **`typed : (untyped-value, env) → typed-value`** — run **once**, at the
boundary, turning a value-without-type into a value-with-type. The `env` is the **source** of type
information (the answer to "where does the type come from?"): the variable types in scope, the
enclosing operation's signature, the in-scope `requires`. `typed` is not a new engine — it is the
typer (`type_check_node(kb, env, occ)` is exactly `typed` for the occurrence carrier), lifted to a
value-level signature and made explicit about its env.

**This replaces `min_sort`.** `min_sort : Term → Sort?` had **no env** — it tried to *recover* a
sort from a value with no source, so it returned `None` on exactly the values that matter (a bare
constructed `Value::Term`: `cons(1, nil)` → `None`, though `cons` plainly names `List`). `typed`
**pushes** the type at the typing site instead of **pulling** it at the read site; with the type
carried there is nothing to recover and nothing to fail. `min_sort` / `min_sort_of_value` are
removed.

**Totality.** `typed` always *produces* a typed value — never `None`. An under-determined part
comes back as a **type-variable / constraint** inside the typed value, not a failure: a free var →
its env constraint; a constructed value → `List[typed(child, env)]`; a scalar → its literal sort.
That is the totality `min_sort` could not give.

## The carrier — one type representation, on the value

The type cannot live *on* the shared term. A term's type is a property of the term **in an
environment** (`nil` is `List[?T]`; `?x` is whatever its context constrains), and hash-consing
shares one `TermId` across every environment — a type slot *on* the term would have to hold every
environment's type at once, i.e. **unshare** it. Rejected. So the type rides **alongside the
term**, and *how* depends on the carrier (M3/M4: a type may sit *on* a carrier iff the carrier is
per-environment; a shared carrier is wrapped). `typed(value, env)` is therefore **per-variant**:

- **Self-typed — fixed sort, no parameters:** scalars (`Int/BigInt/Float/Bool/Str`) → literal
  sort; `Unit` → `Unit`. Read directly; no slot.
- **Source occurrence:** `Value::Node` → its `inferred_type` slot, stamped by the typer. A node is
  a *source-text* entity (it has `span` / `owner` / `OccurrenceOrigin`) — the op-body / rule-pattern
  carrier. A runtime value is **not** from source, so it can never be a node.
- **Constructed value → `ty` field:** `Value::Entity`, `Value::Tuple`, and `Value::Term` each carry
  a new **`ty: Option<Rc<Value>>`** field holding the *same* `Value` type-term. `None` = not yet
  typed; `typed(value, env)` fills it and **always keeps it** — no per-instance "should I store?"
  check. The field is **uniform across all constructed values**, so a value's typed-ness is a single
  **O(1) `Some`/`None` test** rather than a recursive walk of its children. (Whether to store a
  *tuple's* type — trivially recreatable as the product of its children — is genuinely low-stakes;
  uniformity + that cheap typed-check decides it. For entity/term recreation is non-trivial anyway:
  constructor signature + unification, and a nullary/polymorphic ctor like `nil : List[?T]` needs the
  **env**, unrecoverable later.) `Rc`, not `Box`: types are copied with values, so the type is
  **shared** on clone, not deep-copied — like the existing `pos: Rc<[Value]>` storage. Rides on the
  per-instance `Value`, never on the shared `TermId` (M3).
- **Typed via constraint:** `Value::Var` → its constraint-store entry (the typed-variable half).
- **Runtime handles — they fold into the groups above** (per the typed-value review):
  - `Closure` → **structural**: the arrow from `param_pattern` + `body` (param types, body result
    type, effects), like `Tuple`.
  - `OpRef` → **nominal**: its type is the op's signature arrow, read from the KB by the op
    `Symbol` (a symbol names a type, as a constructor names a sort); it already carries its
    dispatch `dict`.
  - `Requirement` (the dispatch dictionary) and `OpRef` → also exposed as **first-class reflect**
    objects (`reflect.Dictionary` / `reflect.OpRef`), denoted type a reflective projection
    (**WI-577**).
  - `Map` / `Cell` → **structural over typed contents** (one entry's `K`/`V`, the held value's
    `T`); an empty `Map` → `Map[?K, ?V]` (nullary fallback, like `nil`). Runtime monomorphization
    never reads `K`/`V`/`T` — container ops are monomorphic over the representation.
  - `Substitution` → **self-typed**, the fixed `Substitution` meta sort (like `Unit`).
  - `Stream` → **`Ref(Stream)` ≡ `Parameterized(Stream, Id)`**: `Stream` under a parameter-
    substitution σ — σ = Id (fresh `?T`, `?E`) minimally, **refined by the env** at the create/bind
    site (M6). The handle stays bare; the value's `ty` field holds `Parameterized(Stream, σ)`. *(Resolved.)*

**Unifying view — a type is a sort under a parameter-substitution.** Every value's type is
`Parameterized(S, σ)` (≡ `Fn{S, σ}`), and `Ref(S)` is exactly `Parameterized(S, Id)` — the sort
under the identity substitution. So "non-parametrized" is the **zero-param** case, "unknown params"
is **σ = Id** (fresh vars), and refinement is **σ-composition** (M6 — the same substitution the
resolver already threads). The per-variant differences above are only in *how much of σ the value
or the env supplies* — never in the type's shape. No bare-vs-applied distinction, no special handle
type: `typed(value, env)` yields `(S, σ)`, σ starting at Id and composed up as the env pins params.

**Match on the term; carry the type; depend on it via a guard.** Three distinct steps — *not*
"ignore the type":

- **Match / index** decides on the *term* shape — `discrim` insert/query, the decomposition in
  `builtin_unify` / `match_view`, the substitution walk — read through `TermView`, which projects to
  functor / args (carrier-agnostic, WI-342/348/349). It does **not** branch on the type: that
  regresses (to unify a type you'd have to type it, which unifies… M1).
- **Carry** — `ty` is **preserved and σ-refined** through clone / De Bruijn open / substitution,
  **never dropped**. Because a type is itself a term, σ refines it for free. (The "WI-502 bug" is
  exactly that open/subst currently *drop* the type; the fix — carry it — is the runtime-value analog
  of WI-572's `rebuilt_expr`, which carries a node's `inferred_type` through reassembly.)
- **Type-dependence — the essence of WI-502** — is a **guard**, not a kernel branch: a type-directed
  rule `add(?x: Numeric, 0) = ?x` desugars to `… :- subsort(typeof(?x), Numeric)`; the guard **reads
  the carried `ty`** and resolves `subsort` by SLD over the sort facts → fire / don't-fire / suspend.
  The carried type exists *so this guard is evaluable* — today the resolver skips such rules
  (`equation_is_requires_guarded`) for lack of a type to read.

The symmetric kernel touch is on a typed **variable**: binding `?x := v` wakes its `?x : T`
constraint (M5 / Step 2's `bind_waking`) and checks `subsort(typeof(v), T)` — bind / fail / suspend.
An unconstrained bind skips it (gated on a non-empty store, free on the hot path). Both the guard
and the wakeup stay in the **decidable fragment** (subsort lattice + instance facts over ground
sorts), so they terminate — unlike a type-branch *inside* a structural primitive, which would
recurse unboundedly. The type-rule machinery rides **above** the kernel, reading the carried type.

## Two carriers of type — value and variable

The type is carried in two complementary places, and **both are needed**:

- **Typed value** — the *concrete* type carried **on the value**. This is what **runtime
  monomorphization** reads: at a dispatch point a concrete value is flowing (`5`, `cons(1, nil)`)
  and there is no variable left to look up, so the type must ride on the value; its concrete type
  (`Int64`, `List`) selects the instance (the `requires` dictionary). *Runtime monomorphization is
  dispatch on the carried concrete type — not a rewrite of the stored rule, and not the abandoned
  compile-time functor-renaming; the rules stay polymorphic, the typed value drives the dispatch.*
- **Typed variable** — the type carried as a **constraint** on the logical variable (the Step-1
  constraint store). This is the *declared / upper-bound* type, for **checking** (`?x : Numeric`).
  A value whose term still has free vars carries their types as these constraints.

The constraint gives the declared bound (`Numeric`); monomorphization needs the concrete type
(`Int64`) on the value. The **typed-variable** half (Steps 1–3) is delivered; the **typed-value**
half (the `ty: Option<Rc<Value>>` field on the runtime value) is deferred and load-bearing — defer it and you lose both
`typed`-totality *and* runtime monomorphization at once.

## Model — the load-bearing invariants

**M1 — Untyped kernel, by stratification.** The type **relation** — `subsort`, instance
membership, `provides` — is **facts** (`SortProvidesInfo`, sort relations) queried by **SLD**
(`prove_from_gamma` → `kb.resolve`; provider synthesis is an SLD query over `SortProvidesInfo`,
typing.rs:8096 — `sort_provides` walks the same facts in Rust as a hot-path shortcut). Type
**unification** (type terms with logical vars) and the typing **process** itself (inference —
`check_apply` / `type_check_node` / `typed`) are **Rust** today, not SLD — an SLD reimplementation
is *planned* (a compact, self-hosted description), not current. The stratification invariant holds
regardless: the kernel's structural **matching** (`discrim`, the decomposition in `unify` / `match`)
never branches on a type (else: regress) — its *one* type-aware point is the bounded constraint-check
at the **bind** of a typed variable (§"the load-bearing rule"); the relation otherwise rides
**above** as ordinary facts the same engine queries.
**Type-specificity is an untyped guard over type-terms** — a typed pattern `add(?x: Numeric, …)`
desugars to a guard `subsort(τ, Numeric)` where `τ` is `?x`'s **carried** type; the engine sees one
more goal, never a "type." Hash-consing surviving (the old `typed-term-carrier` argument) is a
*symptom* of M1, not its root.

**M2 — Type is one kind of constraint (the typed-variable half).** Anthill already runs a
constraint system — for *effects* (row-polymorphism + `lacks`, WI-307/WI-328). Generalize it: the
`lacks` side-table becomes a **tagged constraint store**; type-constraints (`subsort`, `τ = T`,
disequality) are kind #2. A *typed variable* is a `VarId` plus its store entry, and the resolution
answer generalizes **σ → (σ, residual C)**: an undecided type-guard is not a failure to delay
around — it is a residual constraint in the answer. (The complement is the typed-*value* carrier
above; constraints type variables, the carrier types values.)

**M3 — On the per-instance `Value`, never on the interned `TermId`.** A `Value` *instance*
(`Value::Node`/`Entity`/`Tuple`/`Term`/`Var`) is per-environment and non-shared, so it can carry its
type directly: a `NodeOccurrence` already has `inferred_type`, and `Entity`/`Tuple`/`Term` gain a
`ty: Option<Rc<Value>>` field. The interned `TermId` *inside* a `Value::Term` is the shared thing,
and the type can *never* sit on it (one `TermId` spans every environment). The invariant is
**per-instance `Value` vs shared `TermId`**: the type rides on the instance's field, while the
`TermId` it references stays a pure structural key. (WI-348: logic never materializes a `TermId`
from a `Value`.)

**M4 — Two homes, split by *occurrence vs variable*.**
- *Static type of an **occurrence*** (an expression's type — `p(x)`'s result, the same across every
  firing) → the per-occurrence carrier (`NodeKind::Expr.inferred_type`). Per-occurrence is *correct*
  here: distinct occurrences have distinct types.
- *A **variable's** constraints* — its **type** (M2's kind #2) alongside `lacks` (kind #1) and
  disequality — → a map **keyed by the variable's identity**, **one entry per variable**: the
  per-branch **substitution store** keyed by `VarId` at resolution, and its template-phase analog
  keyed by `DeBruijn` index on the rule. **Never per-occurrence, never a new `Value` variant.** A
  *non-linear* pattern proves why: in `p(x, x)` the one variable `x` has one type, shared by both
  occurrences — keyed, exactly as its **binding** is keyed (the two `x`s must bind alike). The type
  rides where the variable's identity already lives. *(The store is general — type is one kind of
  constraint among `lacks`/disequality, M2 — so this is "a variable's constraints," not just its
  type.)*

> **Typed-pattern surface (designed below):** a variable's type is declared **once** (e.g.
> `p(?x: T, ?x)`, not on each occurrence), mirroring the keyed-once storage; for a non-operation head
> it declares the relation's signature. Full design in §"Typed rule patterns — surface and matching";
> the explicit-binder *grammar* is not yet parsed (the implicit `[simp]`/`requires` form needs none).

**M5 — Explicit wakeup at the bind site (from the functional model).** A variable is an inert
`VarId(u32)`, a binding is an entry in `Substitution.bindings`, and a branch is a *clone* — no
mutable cells, no trail. The constraint mechanism follows **directly** from that, from first
principles:
- a variable's constraints live in a parallel `VarId`-keyed map on the substitution;
- a constraint can only become decidable when its variable **gains information** — i.e. when it is
  **bound** — so the check runs **at the bind site**, on the bound variable's own constraints;
- there is no mutable cell to hang an auto-hook on, so the check is invoked **explicitly** there
  (`bind_waking`);
- lifetime is automatic — the constraint map rides *inside* the cloned substitution, so it forks
  and is discarded with the branch (M7).

Concretely, binding `?x := v` runs `?x`'s store entries against `v`: a *type* constraint `?x : T`
→ check `subsort(typeof(v), T)`; a *lacks* constraint → its label check — deciding **bind / fail /
suspend**. (This is the same wakeup discipline CLP systems — **SWI-Prolog**, **SICStus** — provide
via *attributed variables*: a unify hook on a mutable variable cell + a trail. We reach it from the
functional side instead, with no mutable substrate. It is also why `lacks` worked in the typer
(`bind_row_tail`) but was inert in the resolver until the Step-2 `bind_waking` choke-point.)

**M6 — Compute once; carry by the ops already running.** The type is produced **once** by `typed`
at the boundary, then maintained by the *same* De Bruijn opening + substitution the engine already
performs — because the type shares the term's logical variables, **σ is type refinement for free**.
**Binding is navigation:** the carried type of `?x` follows `?x`'s binding to a value and reads
*that value's carrier* (M3); an *unbound* `?x`'s type comes from its store constraint (M4), or is a
type-variable. Re-derivation is confined to two bounded, *loud* points: the **boundary** where an
untyped value enters (`typed` runs there — the typer, and the resolver/simplify entry that today
takes a bare `TermId`), and **refresh boundaries** where σ cannot link the type's vars (surface
loudly, never silent drift). The env `typed` is given is both the *source* and the *soundness
obligation*: it must be the env that genuinely types the value.

**M7 — Lifetime is branch-scoped and already correct.** A type-constraint must live from its birth
step until a result row, dying on backtrack — the *same* lifetime as a binding. The resolver
already provides this: every frame push does `frame.subst.clone()` (`resolve.rs:1667`, `1712`,
`1626`), deep-copying the whole chain; popping on backtrack discards branch-specific constraints.
The genuine gaps were **not** lifetime: (a) no *wakeup* (closed by Step 2's choke-point bind path);
(b) a constraint generated into a throwaway per-step `extra` would be dropped (does not occur
today, but would bite naïve resolver-side generation).

## Typed rule patterns — surface and matching

This is the **goal** the substrate above exists for: rules whose firing depends on a type. It comes
in two surface forms — an **explicit** type bound on a pattern variable, and the **implicit** guard a
`[simp]` rule inherits from its enclosing sort's `requires` — and both **desugar to the same thing**:
a type-relation goal over a variable's *carried* type.

### Surface — the same conventions as operations

A typed rule's **type-variables and annotations** use the **operation conventions**, not a
rule-specific dialect: `[E]` introduces a type-variable (then written `E` — the `?`-dropping
shortcut), and `: T` annotates a value position, exactly as an operation signature does. `[E]` and an
inline `?E` are the *same* variable, one with the `?` kept; which mode it resolves in (flex at a
match, rigid at the load-time well-formedness check) is the ordinary phase distinction, not a
rule-vs-op one.

A **bound**, though, is a rule *condition*, not a `requires`. `requires` is the precondition/contract
construct, declared on a *sort* or *operation*; a rule's conditions live in its body. So a bound on a
rule is a **guard** (its `:- …`), or the inline `?x: T` annotation that desugars to one. The
correspondence is **op/sort `requires` ≡ rule `:- guard`** — the same notion ("conditions of
applicability"), each in its construct's natural slot (proposal 043 §4.1: a `[simp]` rule's guard is
its `:- …` *plus* the enclosing sort's inherited `requires`).

```anthill
rule head[E](cons(?h: E, ?t: List[E])) = ?h            -- E links head & tail-element types
rule add[T](?x: T, 0) = ?x :- Numeric[T]               -- a bound on T is a guard
rule add(?x: Numeric, 0) = ?x                          -- inline `?x: Numeric` desugars to that guard
```

A type-variable's bound is declared **once**; a non-linear pattern shows why (M4): in `p[T](?x: T, ?x)`
the single variable `?x` has one type `T`, shared by both occurrences exactly as its binding is — they
must bind alike *and* type alike. A *conflicting* re-annotation is a load error (loud, not silently
merged).

### Rules about an operation — the functional twin, bounds owed on use

A rule whose head is an **operation** (`append`, `member` in `list.anthill`) is the **relational /
equational twin** of that op: the operation is the executable form the evaluator calls; the rules are
the laws the resolver / rewriter / prover use (`append(nil, ?ys) <=> ?ys`; the Prolog-style
`member/2`). The rule's variables take their types from the op's signature — but the op's `requires`
is **not blanket-inherited**. Read `requires` as an implicit parameter (a spec dictionary): it is
**available** in the shared scope, yet **owed only where the rule actually consumes the spec op**:

- `member`'s rules decide membership by **unification** (`cons(head: ?x, …)`), never calling `eq`, so
  they **owe no `Eq[T]`** — `member(waypoint, …)` over a non-`Eq` `Waypoint` is answerable
  relationally. The *operation* `member` calls `eq(head, x)`, so it owes `Eq[T]`. Same symbol; the
  bound is owed only by the form that consumes it.
- `append` consumes no spec op in either form, so neither owes a bound; its `<=>` rules fire
  unconditionally.

This is the WI-562 principle one level down: scope a `requires` obligation to where the spec op is
*called*, not to the whole symbol (a sort-level `requires Eq[T]` had wrongly blocked `nth` on
`List[Waypoint]`). So a `[simp]` rule's **implicit** guard is exactly the enclosing sort/op's
`requires` *as consumed by that rule* — the WI-283 guard the typer honors (`simp_fire_guard_holds`)
and the resolver today **skips** (`equation_is_requires_guarded`) for lack of a carried type to read;
the typed-value substrate is what lets the resolver honor it. Firing therefore honors **what the rule
consumes** — a spec op (`eq`) → read the carried type and discharge its bound; pure unification → no
guard — never a blanket symbol-level `requires`.

A **non-operation head** (a bare relation with no executable twin) is typed the **same way** — same
conventions, same owed-on-consumption, same carried-type firing. Op-head vs non-op-head is **not a
typing distinction**: an op-head only *adds* an executable twin and an inherited signature to draw arg
types from. A bare relation simply has no signature to inherit, so its arg types come from the rule
itself — the head's `[…]` / `: T` annotations, or inference from the clause bodies (consistency-checked
across clauses) — but the typing *manner* is one.

### Desugaring — a typed pattern is an untyped pattern + a guard

`head(…, ?x: T, …) :- body` *means*:

```
head(…, ?x, …) :- conforms(typeof(?x), T), body
```

- `typeof(?x)` is the **carried** type of `?x`'s binding (the typed value's `ty`, M3; for an unbound
  `?x`, its constraint-store bound).
- `conforms(τ, T)` is the type-relation in the **decidable fragment** — `subsort(τ, T)` for a sort
  bound, `provides(τ, T)` for a spec bound — an ordinary SLD goal over the sort lattice + instance
  facts (M1). The engine sees one more goal, never a "type".

This is the *meaning*; the *realization* folds it into matching.

### Matching — the bind-wakeup carries the check

A typed pattern is **not** matched by a type-aware matcher (M1: structural matching never branches on
a type — regress). Instead:

1. **Load** the bound as a `Type(T)` **constraint on the variable** (Step-1 store), keyed by the
   `DeBruijn` index on the rule template, opened to the fresh `VarId` at `with_fresh_vars`.
2. **Structurally match** the head against the redex as usual — `discrim`/`unify` over functor/args,
   type-blind — which **binds** `?x := v`.
3. The bind routes through the choke-point bind path (Step-2 `bind_waking`), which **wakes** `?x`'s
   `Type(T)` constraint: it reads `typeof(v)` off `v`'s carried type (M3 — or runs `typed(v, env)`
   once if `v` arrived untyped), and checks `conforms(typeof(v), T)`:
   - **holds** (definite) → keep the binding; the rule fires.
   - **refuted** (definite ¬) → fail this binding; the rule doesn't apply here.
   - **under-determined** (`v`'s type still carries free type-vars, or the relation can't be decided
     over them) → **suspend** as a residual `C` in the answer (σ → (σ, C)); never NAF-decide (WI-067).

Because the check rides the variable's identity, a non-linear `p(?x: T, ?x)` checks `T` **once** (at
the bind of `?x`) and both occurrences inherit it — the reason the type lives on the variable (M4),
not per-occurrence.

The desugared **body-guard** form (`conforms(typeof(?x), T)` as an explicit goal after the structural
match) is semantically equivalent and is the fallback for a guard that spans *several* variables (a
compound the per-variable wakeup can't express). The constraint+wakeup is preferred: it prunes at the
bind site rather than after a full head match, and it is the substrate already built (Steps 1–3).

### Status

The **implicit** `[simp]`/`requires` path needs **no** new syntax — only a resolver that reads the
carrier's carried type, which the typed-value carrier (WI-578) supplies; replacing
`equation_is_requires_guarded`'s blanket skip with the wakeup check above is the resolver consumer
**WI-292**. The **explicit** `?x: T` binder is *new grammar* (a typed binder in a rule LHS, plus the
loader installing the `Type` constraint) — a follow-on once the implicit path is proven, tracked
under the WI-502 "typed rule pattern syntax" item.

## Limitation ↔ generation (CLP/CHR framing)

A constraint both *prunes* and *generates* (CLP labeling; CHR propagation):
- **Limitation / check (now):** discharge `subsort(τ, Numeric)` against sort facts.
- **Generation / label (later):** when forward progress needs an under-determined type —
  `requires Numeric[?T]` with `?T` unbound — *enumerate* admissible instances. Dispatch under
  uncertainty **is** labeling.

We adopt the *frame* now and **stage the power**: check + suspend ships first; generative labeling
is deferred (opt-in, same representation). Bound the constraint *language* to **decidable
fragments** — sort-lattice `subsort`, instance facts, disequality. Arbitrary-predicate /
full-refinement constraints are a door opened deliberately, not by drift.

## Implementation plan (staged)

**Delivered substrate (the typed-variable half):**
- **Step 0 — persistent substitution (WI-569).** `Substitution.bindings: imbl::HashMap`, so every
  `frame.subst.clone()` is O(1) and the constraint store rides along as a free O(1)-clone field.
- **Step 1 — constraint store = typed variables (WI-570).** The `lacks` side-table generalized to a
  tagged, persistent `VarId`-keyed store (`Lacks` #1, `Type` #2); residual `C` exposed on the
  answer.
- **Step 2 — carry + wakeup in the bind path (WI-571).** `absorb_constraints` carries constraints
  through merge; `bind_waking` merges-on-alias and wakes; `bind_compressed` asserts loudly if a
  constraint-carrying var bypasses it.
- **Step 3 — carry the type through open/subst + a value-level read (WI-572).** `inferred_type`
  survives De Bruijn open/close + substitution + simp reassembly (`NodeOccurrence::rebuilt_expr`).
  *(The value-level reader delivered here, `min_sort_of_value`, is **superseded** by `typed` — see
  below.)*

**Remaining (the typed-value half + the read primitive + the machinery):**
- **Typed-value carrier — `ty: Option<Rc<Value>>` on the runtime-value variants** (the deferred
  WI-572 (E); its absence is what makes the read return `None` and loses runtime monomorphization).
  The field goes on `Value::Entity`, `Value::Tuple`, and `Value::Term`, holding the *same* `Value`
  type-term as `inferred_type` (one representation). `typed` **always stores** the type it computed
  (`None` = not-yet-typed) — no per-instance "derivable?" check (a false economy: re-deriving on read
  costs more than holding one cheap `Rc`). `typed` is **variant-preserving** (`Term`→`Term(+ty)`,
  `Entity`→`Entity(+ty)`; no `Term`→`Entity` conversion, which is ill-defined for a non-constructor
  `TermId`). Scalars / `Unit` are self-typed; `Value::Var` uses the constraint store; `Value::Node`
  keeps `inferred_type`. A `Value::Typed` enum variant is rejected as too invasive (~1844 `Value::`
  match arms / the WI-538 silent-wildcard trap), and a non-`Value` wrapper struct can't be a
  resolver goal/binding/result — so the type rides as a field on the existing variant instead. The runtime handles mostly fold in (the carrier section):
  `Closure` structural, `OpRef` nominal + reflect (WI-577), `Requirement` reflect (WI-577),
  `Map`/`Cell` structural over contents, `Substitution` self-typed, `Stream` →
  `Ref(Stream)` ≡ `Parameterized(Stream, Id)` (σ refined by the env — the carrier section).
- **`typed(value, env)` boundary op + remove `min_sort`.** Run the typer once where an untyped
  value enters — the typer, and the resolver/simplify entry that today takes a bare `TermId` with
  no type (the deferred WI-572 (C)). Retire `min_sort` / `min_sort_of_value`; callers read the
  carried type.
- **Resolver machinery for typed rule patterns.** The surface syntax (`?x: T` in a rule LHS,
  desugaring to a `subsort` guard over the carried type) and the matcher reading the carried type,
  so a requires-guarded rule the resolver skips today becomes *matchable*.

**Consumers (dependent tickets, not WI-502 itself):** WI-292 (type-directed `[simp]` firing),
WI-573 (guarded-effect guard discharge over spec-op guards), runtime monomorphization (dispatch on
the carried concrete type), WI-574 (generative labeling — deferred).

## Soundness watch-points

- **Flounder, don't decide.** An under-determined carried type ⇒ suspend as residual `C`; a
  negative/NAF guard over a runtime-unknown type must not succeed *or* fail (WI-067).
- **`typed` is only as sound as its env.** The env must be the one that genuinely types the value;
  where σ cannot link the type's vars (a refresh boundary), surface loudly — never silently
  mistype.
- **The structural kernel stays type-blind.** `discrim`/`unify`/`match`/subst see only the term
  component; the type-rule machinery rides above, reading the carried type. The kernel never
  branches on a type (M1).
- **No silent drop.** The choke-point bind API fails loudly if bypassed (Step 2).
- **Decidable fragment only** (§Limitation ↔ generation).
- **Never on the interned `TermId`** (M3) — the type rides in the per-environment pair / occurrence,
  never on the shared `TermId`.

## Prior art & in-repo precedents

CLP / CLP(FD), attributed variables, CHR (propagation = "limitation becomes generation"),
order-sorted logic, refinement types ("type is a predicate"). In-repo: `lacks` side-table
(WI-328), Γ `Env{types,flow}` (WI-537), `imbl` persistent maps (`eval/map_arena.rs`), the typer's
`type_check_node` (which `typed` generalizes) and `simp_fire_guard_holds`.

## Decisions recorded (do not re-litigate)

1. Keep the **functional** unification model; do **not** reify variables into cells + trail.
2. The **substitution is the home** for var-coupled constraints — lifetime-correct (M7), made cheap
   via `imbl` (Step 0). Attributed-variable behavior is *emulated* with explicit wakeup.
3. **Check + suspend now; label later**; decidable fragment only.
4. **Typing is `typed(value, env)`; `min_sort` is removed.** Type info is *pushed* at the typing
   boundary (the env is the source), carried on the value, and *read* downstream — never *pulled* /
   re-derived by a source-less reader. `typed` is total (unknowns ride as type-variables /
   constraints).
5. **Type lives on the per-environment carrier / per-branch store, never on the interned `TermId`.**
   Value carries its *concrete* type (→ runtime monomorphization at dispatch); variable carries its
   type as a *constraint* (→ checking). Both are needed.
6. **The structural kernel is type-blind; the type-rule machinery rides above it.** *(Supersedes the
   dropped "Shape A monomorphize-at-boundary / Shape B fire-in-resolver" split: compile-time
   functor-renaming re-derived the `requires`-dictionary dispatch and could not name an under-
   determined carrier anyway; the resolver matching a typed pattern reads the carried type instead
   of being made to recompute one. Revised 2026-06-27.)*
