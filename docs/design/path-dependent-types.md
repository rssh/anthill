# Path-dependent types in Anthill

## Status: design (started 2026-06-05)

Driven by the `DataProvider` use-case — a generic provider held in a wrapper. This
is the parked **WI-376 "abstract-receiver stays-poly"** question, generalized: a
projection `p.M` where `p` is an *expression* is a **path-dependent type**.

This doc starts from **one fully-worked example that needs no new term
representation**, answers the representation question it raises, states the two
rules that form the model's spine, and marks what the harder cases add.

> **Divergence from Scala (the headline).** Anthill identifies a projection `p.M` by
> **unifying the receiver expression `p`** (up to the substitution), not by the
> **syntactic path** (Scala). `let y = z` makes `y.M ≡ z.M`; Scala rejects it. Falls
> out of "types are terms; receivers are expressions, compared by unification."

**Framing — two mechanisms, both over _expression types_** (types that embed an
expression). Anthill *already has* unification of such types: a type may embed an
expression occurrence (a denoted occurrence, and now an `ExprCarried` receiver), and
the typer unifies them carrier-agnostically. The spine (§3) is two uses of it:

- **identity** — *unify the expression types* (so `y.T ≡ z.T` exactly when `y` and `z`
  unify);
- **grounding** — *track an expression's type through control flow* (so
  `type(s.provider)` refines to `SubscriberStore` where the construction is visible).

**Related work — Scala 3 experimental modularity**
([modularity](https://scala-lang.org/api/3.8.4/docs/experimental/modularity.html)),
the closest existing mechanism, fixes the contrast. Scala's `tracked` parameters keep
an expression's precise **type** in the instance type — the **grounding** axis (the
route for the plain-field case, §5) — but leave identity **nominal over the path**
(even tracked, `val y = z` keeps `y.T ≠ z.T`). Anthill instead **unifies the
expressions** themselves (the receiver occurrence, against the substitution — a
compile-time term, *not* the runtime `Value`), so identity follows for free. One-line
contrast: **Scala tracks the expression's type (grounding only); Anthill also unifies
the expression (grounding + identity).**

## 1. The one working example

```anthill
sort DataProvider
  sort K = ?
  operation hasKey(k: K) -> Boolean

sort SubscriberStore                       -- a concrete provider
  provides DataProvider[K = String]
  entity subscriberStore

sort State                                 -- a wrapper that CARRIES the provider type P
  sort P = ?
  requires DataProvider[P]                 -- P provides DataProvider ⟹ abstract P has member K + hasKey
  entity state(provider: P)

operation check(s: State, k: s.provider.K) -> Boolean
  = s.provider.hasKey(k)
```

**In `check`'s body** `s : State` has `P` abstract, so `s.provider.K` is **rigid** —
a type keyed by the path `s.provider` plus member `K`. The body type-checks by
*path identity*: `k : s.provider.K` is exactly the `K` that `s.provider.hasKey`
expects. The bound `requires DataProvider[P]` is **load-bearing for the abstract
body**: it is the dual of `SubscriberStore`'s `provides` (line above) — it gives an
abstract `P` its *declared interface* (`K`, `hasKey`), so `s.provider.K` is a
well-formed rigid neutral rather than "no member `K`". (`requires Spec[X]` names the
**carrier** `X`, the dual of `X provides Spec[…]`; the spec's own param `K` stays
abstract, projected as `P.K`.) Without it `P` is an unconstrained `sort P = ?` and the
abstract projection is ill-formed — the concrete call below needs no bound because there
`P` is instantiated to a provider.

**At a concrete call** the path grounds:

```anthill
check(state(provider = subscriberStore), "abc")   -- ✓  k : s.provider.K = String
check(state(provider = subscriberStore), 42)        -- ✗  42 : Int64 ≠ String
```

The trace — each step is existing or near-existing machinery:

1. **Construction infers `P`.** `state(provider = subscriberStore)` with
   `subscriberStore : SubscriberStore` ⟹ the occurrence's type is
   `State[P = SubscriberStore]`. *(Bidirectional inference on the constructor path —
   **WI-384**.)*
2. **Field access reads `P` back.** For a receiver of type `State[P = SubscriberStore]`,
   `s.provider` has the field's declared type `P` with `P = SubscriberStore`
   substituted from the receiver's type-args ⟹ `s.provider : SubscriberStore`.
   *(Field type through type-args — the same substitution `build_pattern_subst`
   already does for pattern field types.)*
3. **Project the member.** `s.provider.K` = the `K` member of `SubscriberStore`
   = `String` (it provides `DataProvider[K = String]`). *(The projection eliminator —
   **WI-376 / WI-397**.)*

## 2. The representation question (the one you raised)

> *Can't represent typed terms — or do we add an optional type to the expression?*

Anthill **already has the second**, and for the parametric wrapper it is enough. The
model separates:

- the **term** — hash-consed, structural, **untyped** (`state(provider = subscriberStore)`
  as pure structure);
- the **occurrence** — the expression node, which **carries a type slot** (the
  inferred type of *that* occurrence).

Path-dependent typing rides the occurrence's type slot; **no new kind of term**:

- at the **construction** occurrence, the slot holds `State[P = SubscriberStore]`
  (`P` inferred from the argument — WI-384);
- at the **`s.provider`** field-access occurrence, its type is read *from the receiver
  occurrence's type* by substituting `P` — i.e. `type(s.provider) = field-of(type(s))`.
  That is your *"field access from type."*

So the grounding rule `type(C(f = e).f) = type(e)` is realized as: the constructor
binds `P := type(e)` into the occurrence's type, and field access reads it back. **No
value reduction, no refinement type, no new term kind** — the existing
untyped-term / typed-occurrence split already carries it, *for the parametric
wrapper*. (The plain-field wrapper is where more is genuinely needed — §5.)

This is also the right *altitude*: it is type inference (a reduction in the **type**
term, `type(provider(s)) → type(ss)`), never value evaluation — `s.provider` the
expression does **not** reduce to `ss`.

## 3. The two rules (the spine)

1. **Grounding — track the expression's type through control flow.** `type(p.M)` =
   the `M`-member of `type(p)`, where `type(p)` is the receiver expression's type *as
   tracked at that program point* (flow-typing): a visible construction refines it
   (`type(C(f = e).f) = type(e)`), a declared parametric type carries it (`P`), and
   behind an abstraction boundary it is just the declared type. Concrete when
   `type(p)` pins `M`; **rigid** (keyed by `p` + `M`) otherwise — grounding reaches
   exactly as far as the tracked type carries information.
2. **Identity — σ-equality of the receivers.** A path type embeds its receiver: `y.T`
   is `ExprCarried(y, T)`. To decide whether `p.M` and `q.M` are the same type, the
   typer checks whether the receivers `p` and `q` are **σ-equal** — *the same term once
   the current substitution σ is applied*: resolve each through σ (following the
   `let`/unification aliases σ records) and compare structurally. It is a **check, not
   a binding** — never "could they be *made* equal" (that is unification, and it would
   be the unsound non-injective decomposition), only "are they *already* equal under
   σ". `let y = z` records `y ↦ z`, so `y` and `z` are σ-equal, so `y.T ≡ z.T` and
   `Cell[y.T]`, `Cell[z.T]` interchange; two distinct receivers stay distinct. Note the
   receivers are *values* (`s`, `s.provider`), not types — so this bottoms out in
   ordinary term-equality one level below the type-equality it defines (no circularity)
   and is purely compile-time (never the runtime `Value`). σ-equality sits **stronger
   than syntactic-path equality** (Scala, where `let y = z` leaves `y.T ≠ z.T`) and
   **weaker than semantic equality / unifiability**. Decidable; soundness is separate
   (immutable `let` ⟹ the aliased values are one runtime value). *(The flexible case —
   a receiver still a variable, so σ can't yet decide — suspends rather than guesses a
   binding; §4.)*

These are complementary, not competing: rule 1 says *what type* a projection
resolves to; rule 2 says *when two (rigid) projections are the same type*.

## 4. Equality is definitional conversion; constraints solve by delay

Path-type **equality** is not ML's nominal `sharing` — it is the **definitional
conversion** of a dependent type theory, restricted to three reductions and closed
under congruence:

- **ζ** (receiver) — `p.M ≡ q.M` when the receivers `p`, `q` are **σ-equal** (the same
  term once the substitution is applied — a non-binding check; `let y = z` ⟹
  `y.M ≡ z.M`);
- **δ** (manifest) — `p.M ⟶ τ` when `type(p)` makes `M` manifest (grounding, §3);
- **η** (`.Sort`) — `p.Sort ⟶ type(p)`, reifying the receiver's whole type.

The three are confluent (δ and η act on different members; ζ is orthogonal) and
terminate on finite type structure (recursive providers need the usual cycle guard).
A *rigid* `p.M` is a **neutral** — a projection stuck on a variable receiver — and two
neutrals are equal only structurally, never by inverting the projection.

**Projection heads are non-injective — the one soundness rule.** `peek(a).T` and
`peek(b).T` can both be `Int64` without `a = b`, so the unifier must **not** decompose
`p.M =?= q.M` into `p =?= q`. `ExprCarried` is an **opaque head** in unification:
δ-ground both sides and unify the results; if both stay neutral, **check σ-equality of
the receivers** — the **α-equality routine modulo the substitution's equivalence
classes**: compare structurally, two terms equal at a variable iff they are in the
**same class**, with α-renaming at binders. The routine **accepts the set of classes**
(σ as a union-find): a substitution `x ↦ y` (from `let x = y`, or a unification) puts
`x`, `y` in one class, so comparing `x.T` and `y.T` succeeds — `y.T ≡ z.T` for
`let y = z`, while two distinct receivers stay distinct, never forced equal by a
guessed binding (a *check*, never a *binding*). One routine serves both this receiver
check and α-equivalence of binders (arrow / dependent types — the deferred `Positioned`
reading). This is
a **custom unification rule at that head** (**WI-400**) — and it is the whole of what
keeps the equality sound. **In the Rust typer it is an arm of `unify_types`** (the
typer's own type-unifier — `unify_types` / `unify_view_structural` in `kb/typing.rs`,
*distinct* from the discrimination tree): a σ-equality check over the typer's
`Substitution` — resolve both receivers through σ, compare structurally, α-rename at
binders. ML never meets this — it only *checks* declared sharing, never *infers*
abstract-type equality; DTT meets it and answers the same way (neutrals are opaque).

> **Rust now, anthill later — why WI-400 does not depend on WI-370.** Today the typer is
> **Rust** (`kb/typing.rs`), with its own type-unifier `unify_types`, *separate from* the
> discrimination tree (which is the unifier only for *fact resolution* / SLD). So
> σ-equality is a Rust routine at the `ExprCarried` arm of `unify_types`, over the typer's
> substitution — no trie machinery. **WI-370** — custom unification *at a
> discrimination-tree node* — is the realization of the same idea in the *self-hosted*
> typer, where typing is re-expressed as anthill rules run by the SLD resolver
> (**WI-010**) and checked equal to the Rust typer (**WI-079**). That track is necessarily
> **downstream** of a working bootstrapped typer — the anthill typer cannot be landed
> before there is a typer to check its rules — so WI-370 sits *after* WI-400, never before
> it. WI-370 therefore leaves the `typing` build set for the self-hosting /
> everything-is-facts track (with its driver **WI-371**, the op-body-as-fact collapse).

**Inference = collect constraints, defer maximally, solve at the end** (the 011 view;
the resolver already is a constraint solver with delay/wake). A flexible
projection-equality `?p.M =?= ?q.M` arises only where a receiver is a logic variable —
i.e. in **rule bodies**, never in operation signatures — and is an ordinary delayable
goal: it suspends and wakes when its receivers bind, like every other goal over
unbound vars. **Delay, never reject.** Rejecting outside the pattern fragment would
make rule typing order-sensitive (a well-typed rule fails by atom order) and would
contradict the resolver's own delay discipline.

**The soundness invariant** is the repo's *loud error over silent skip*, lifted to
constraints: **every deferred constraint ends confirmed, refuted, or surfaced as a
residual obligation — never silently accepted or dropped.** Two implementation
obligations follow:

1. **Wake-registration** — a deferred `?p.M =?= ?q.M` is registered on its receiver
   vars, so grounding (`?p := P1`, `?q := P2`) re-checks it (`String =?= Int64` → fail).
   The resolver's delay/rotation already does this; the duty is not to let the goal
   fall off.
2. **Set-level final solve** — a residual `?a.K =?= ?b.K ∧ ?a ≠ ?b` is pairwise-fine
   but globally unsatisfiable unless two *distinct* providers share a `K` (a
   KB-existence question). Decidable over a finite KB — but only if the final solve is
   over the *set*, not per-constraint.

With that invariant the feared case — *unsatisfiable but uncaught* — cannot produce an
unsound **accept**: an undischarged residual becomes a reported obligation, not a
silent pass. The cost falls the other way (over-flagging a satisfiable residual —
incompleteness), which 011 reframes as a work-item.

**Residual accounting = 011's three levels**, read off the final set:

| final residual | typedness | guarantee |
|---|---|---|
| refuted | **ill-typed** (`¬∃` binding) | reject |
| free vars remain | **well-typed**, with obligations | sound only as "∃ a binding," not runtime safety |
| empty | **universally typed / ground** | the level realization / codegen requires |

So equality is conversion (ζ/δ/η over non-injective heads), inference is delay with
no-silent-drop, and "typed" is a three-level residual reading — the projection corner
is just the general typing architecture made concrete.

## 4.1 Realizing σ-equality on the Rust typer (WI-400) — eager let-alias + structural ζ

*(Added 2026-06-09, after **WI-399** landed the let-site elimination chokepoint and
the env-free `unify_types` boundary. Decision: **eager let-alias**, not σ-tracked
receiver vars.)*

§3–4 speak of "σ as a union-find: resolve each receiver through σ, following the
`let`/unification aliases σ records." **On the current Rust substrate that structure
does not exist.** The type substitution `Substitution.bindings` is `VarId → Value`
(logic-var bindings, plus the `lacks` row side-table); a `let y = z` is recorded in the
**typing env** as `y → type(z)` — the *type*, not the receiver alias `y ≡ z`. Nothing
maps a value-receiver name to its alias. So "resolve receivers through σ" has nothing to
read, and a union-find read *inside* `unify_types` would re-introduce the receiver
context that WI-399 deliberately kept **out** of the env-free unifier. WI-400 is
therefore realized as **eager let-alias canonicalization at the (env-bearing) site +
plain structural ζ in `unify_types`**:

**δ at the sites; ζ in `unify_types`.** δ-grounding (project the manifest member off the
receiver's *known* type) needs `type(receiver)`, which lives only in the env — so it
runs at the elimination **sites** that hold the env (operation call:
`check_apply_iter` / `param_to_arg_type`; let annotation: `visit_type` /
`var_bindings` — **WI-399's eager elimination *is* δ**). `unify_types` has no env, so
what reaches it is **already a neutral** (δ could not ground it at the site). Its WI-400
arm is therefore **purely ζ**: a structural equality of two neutral `ExprCarried` heads
— and it **replaces the WI-399 safety-net guard** (the `return false` on an `ExprCarried`
head) at that exact line. The "δ-ground both, then if-neutral check σ" of §4 is thus
**split across the two layers**, not one call.

**The operation-*body* site is WI-400's PRIMARY site (correction, 2026-06-09 — probes
BIDIR-3 / 3b).** δ runs not only at the call and `let` sites but at
**`check_operation_bodies`**, where each parameter is bound into the body env with its
*declared* type. A projection param type (`k: s.cell.T`) must be **δ-grounded against the
receiver param's declared type when manifest** (`s: Wrapper[P = Inner[T = String]]` ⟹
`k : String`) and **neutral-formed when abstract** (`s: State`, `P` open ⟹
`k : ⟨s.provider⟩.K`), *before* the body is checked. This site is currently **unwired** —
a manifest `k: s.cell.T` in a body stays the raw neutral `?.T` and the body fails
(`expected String, got ?.T`), and the §1 motivating example
(`check(s: State, k: s.provider.K) = s.provider.hasKey(k)`) *is* a body-check. So
**WI-400's primary work is the body-binding site**, not the `unify_types` ζ arm — the ζ
arm is *downstream*, the equality check between two neutrals the body-site produces. (At
the body site the receiver's type is the *declared* param type — fixed, **no**
bidirectional inference — so eager δ-ground / neutral-form there is sound and complete;
deferral remains only the flexible rule-body case.)

**Receiver aliasing is canonicalized eagerly at the `let`.** When `let y = <stable
receiver path>` binds `y` to a variable / field-access chain (`let y = z`,
`let y = s.provider`), the site records that `y`'s **receiver canonicalizes** to that
path (a receiver-alias entry in the env, alongside the type binding). Projection
**formation** (still at the env-bearing site) resolves a receiver through this map before
building the `ExprCarried`, so `y.M` and `z.M` both carry the **same canonical receiver
`z`** → the structural ζ in `unify_types` succeeds with no alias lookup of its own. That
is the "eager" in eager-let-alias: the alias is applied where the env is, so the neutral
that flows into the type is already canonical and `unify_types` stays env-free (the
WI-399 invariant). The §4 **union-find-over-σ generality is the deferred flexible /
rule-body case** — aliases introduced by *unification* (two receiver vars unified during
rule-body inference), which arise only where receivers are logic variables; there the
resolver's delay/wake supplies the equivalence dynamically, under no-silent-drop. The
base scope (operation signatures + immutable `let`) needs no union-find.

Only a **stable** path aliases: `let y = z` / `let y = s.f` canonicalize (immutable
`let` ⟹ the aliased names are one runtime value — §3's soundness note); `let y = f()`
does **not** — `y` is its own neutral receiver (`y.M` keyed by `y`), exactly as a fresh
abstract value should be.

**Two substrate changes WI-400 makes (base scope):**

1. **Abstract receiver → neutral, not error.** Today `project_type_member` raises a loud
   *"abstract-receiver projection is not yet supported"* when the receiver's member is
   not manifest. WI-400 replaces that with **returning the rigid neutral
   `ExprCarried(canonical-receiver, M)`** — this *is* the parked **WI-376
   abstract-stays-poly**, which WI-400 therefore **co-delivers** (it is the precondition
   for any neutral to exist for ζ to compare). The §1 working example needs *only* this
   plus structural ζ of **syntactically identical** receivers (`Ref(s).provider` appears
   identically in `k`'s type and the `hasKey` call) — **no alias map at all**; the
   let-alias canonicalization is the *increment* that buys the Scala divergence
   (`let y = z ⟹ y.T ≡ z.T`).
2. **A receiver-alias map on the env** (`Symbol → canonical receiver path`), populated at
   stable `let`, read at projection formation. New state, but env-local and scoped like
   `var_bindings`.

**Binder-free base scope.** Receivers here are first-order value paths (`s.f.g`) — no
binders — so the ζ check is a binderless structural compare. The "one routine, also
α-equivalence of binders (arrow / dependent types)" of §4 is the **deferred**
`Positioned` / arrow reading; the base WI-400 routine does not build α-renaming.

#### Increment C DELIVERED (2026-06-09) — eager let-alias (`let y = z ⟹ y.M ≡ z.M`)

The receiver-alias map (substrate change 2 above) landed, completing the WI-400 core. A
`let` whose value is a **stable receiver path** (a value reference / field-access chain —
immutable `let` ⟹ one runtime value) records the bound name's **canonical receiver path**
on the typing env (`TypingEnv.receiver_aliases`, populated at `LetAfterValue` via
`stable_receiver_path`; heads stored already de-aliased, so transitive `let w = y` resolves
to `y`'s target). At the env-bearing **let-annotation** site a projection is canonicalized
through that map *before* elimination (`canonicalize_projection_receivers` →
`build_projection_from_segs`), so `y.M` carries the **same** receiver as `z.M` and the ζ
arm equates them. `unify_types` stays env-free (the WI-399 invariant): canonicalization
runs entirely at the site. An **unstable** value (`let y = pick(p)`) records no alias — `y`
stays its own neutral receiver (the §4.1 stability rule).

Two enabling fixes: `stable_receiver_path` reads the `Expr::VarRef` form a param/let
reference actually takes; and the loader's `try_expr_carried_projection` is now
**local-aware** (consults `lookup_local_name` before the static scope, mirroring
`remap_symbol`) so a projection off a **let-local** receiver (`let y = p; … : y.K`)
resolves its head at all — previously "unresolved name 'y.K'". Acceptance:
`wi400…::let_alias_canonicalizes_receiver` / `_distinct_receiver_rejected` /
`let_unstable_value_does_not_alias`. Limitation: the canonicalization handles the top-level
let-annotation projection; a projection NESTED inside a parameterized/denoted annotation is
unchanged (the same carrier-promotion boundary eliminate documents). **Value-position field
access** (`let y = s.provider`) remains a separate unsupported form (design §5.1 INC-1b), so
the let-alias is exercised via a value-reference receiver (`let y = p`, `p : DataProvider`).

#### Increment B DELIVERED (2026-06-09) — abstract→neutral + the ζ arm

The neutral-formation + σ-equality core landed; the **eager-let-alias** map (substrate
change 2 above) is **increment C** (above). What B does:

- **`project_type_member` → `ProjResult::{Grounded, Neutral}`** (the abstract→neutral
  relaxation, co-delivering **WI-376 abstract-stays-poly**). Neutral when the member is
  *declared* on the receiver's interface: a declared-but-unbound type-parameter of a
  concrete sort (`peek(l: List) -> l.T`, bare `List` — `T` is `List`'s param), OR a member
  lent to an abstract type-variable receiver by its declaring sort's `requires Spec[param]`
  bound (`s.provider : P`, `State requires DataProvider[P]`, `K` a param of DataProvider).
  A member **no** interface declares stays a **loud** error. The callers keep the original
  `ExprCarried` for a neutral (no reconstruction).
- **The declaring sort is threaded** from `resolve_field_type` (which knows the field's
  owning sort) through `resolve_receiver_path_type` → `project_type_member`, because the
  abstract type-param's *source identity* is **erased** on the substrate — it opens to a
  fresh logic var named `_`, so its sort (and thus its `requires`) cannot be recovered from
  the var alone.
- **The ζ arm** is `expr_carried_zeta`, shared by `unify_types` **and both
  `types_compatible` (subtype) dispatchers** (so the two relations refuse a bare projection
  symmetrically — the return-type conformance check goes through `types_compatible`, *not*
  `unify_types`). It replaces the WI-399 `return false` guard: two neutrals are equal iff
  same member off structurally-equal receivers; a neutral never equals a concrete type;
  placed after the `type_var`/`nothing` wildcards so a neutral still flows into an
  unconstrained var for inference.
- **`occurrence_structural_eq` (+ display) gained a `DotApply` arm** — a compound receiver
  `s.provider` is a `DotApply` occurrence, previously unhandled (so it compared unequal and
  printed `?`). Now ζ equates `s.provider` with `s.provider` and prints `s.provider.K`.
- **The body-site loop is a true fixpoint** (iterate while `decl` *changes*, not while a
  projection *remains*): a stable abstract neutral eliminates to itself and is bound as-is;
  only a post-fixpoint `Err` (genuinely un-dischargeable) is surfaced.

**Test matrix (acceptance):**

- **abstract-stays-poly** ✓ (B) — `peek(l: List) -> l.T` is well-formed (forms a neutral),
  and the WI-399 loud error is now reachable only for a *genuinely missing* member, not an
  unbound one (`wi376_projection_test::projection_bare_receiver_stays_poly`,
  `wi399_let_projection_test::let_projection_missing_member_off_abstract_is_loud_error`,
  `wi400…::abstract_projection_missing_member_is_loud`).
- **path-identity (within an operation)** ✓ (B) —
  `idK(s: State, k: s.provider.K) -> s.provider.K = k` typechecks: `k`'s type and the
  declared return are the *same* neutral (`wi400…::abstract_projection_path_identity_within_op`).
- **Non-decomposition** ✓ (B) — `s.provider.K` and `t.provider.K` are distinct neutrals; ζ
  does **not** unify `s =?= t` (`wi400…::abstract_projection_distinct_receivers_rejected`).
  This is the soundness core of the non-injective head.
- **body-site manifest δ-ground (BIDIR-3b)** ✓ (increment A) —
  `idElem(s: Wrapper[P = Inner[T = String]], k: s.cell.T) -> String = k` typechecks.
- **§1 *full* typechecks** — *not* B. The §1 motivating body `s.provider.hasKey(k)` needs
  abstract spec-op **dispatch** through the `requires` bound (resolving `hasKey` on the
  abstract `s.provider : P`) — a **separate concern** from the projection/ζ core (probed
  2026-06-09: the projection now forms the neutral; the residual error is *"unknown
  functor"* at the `hasKey` dispatch). The within-operation path-identity that the ζ core
  *does* deliver is `idK` above.
- **let-alias** ✓ (C) — `let y = z ⟹ y.M ≡ z.M`: `let y = p; let m: y.K = k` conforms via
  receiver canonicalization, while `let y = pick(p)` (unstable) does not alias
  (`wi400…::let_alias_canonicalizes_receiver` / `_distinct_receiver_rejected` /
  `let_unstable_value_does_not_alias`).
- **flexible / rule-body** — **deferred**: `?p.M =?= ?q.M` with logic-var receivers
  **suspends** (the resolver delay/wake); not formed in the base operation-signature scope.

**Deferred from B + C (all sound — no false accept; at most over-rejection / less-precise
error):**

- **nested let-alias canonicalization** — increment C canonicalizes a TOP-LEVEL
  let-annotation projection (`let m: y.K`); a projection nested in a parameterized/denoted
  annotation (`let m: List[T = y.K]`) is unchanged (the carrier-promotion boundary).
- **value-position field access** (`let y = s.provider`) — a separate unsupported form
  (§5.1 INC-1b); the let-alias is exercised via a value-reference receiver (`let y = p`).
- **cross-call neutral threading** — `relay(l: List) -> l.T = peek(l)` does *not* typecheck:
  at the call the neutral keeps the *callee's* receiver symbol (`peek`'s `l`) rather than
  substituting the argument expression, so it ζ-mismatches the caller's `l.T`. The
  call-site eliminator works on *types* and lacks the argument *expression* needed to
  rebuild the neutral's receiver. Incompleteness, not unsoundness (a neutral-vs-concrete
  return is still correctly rejected). Within-operation path-identity (`idK`) is unaffected.
- **carrier-precise `requires` matching** — `abstract_member_declared_by_requires` consults
  the declaring sort's *whole* `requires` chain rather than only the bound whose carrier is
  the specific param; matters only when a sort has several parameters each with their own
  `requires` (a minor over-acceptance).
- **abstract spec-op dispatch** for the §1 body (above) — its own concern.

### Bidirectional flow — the checklist example (WI-427 + WI-400)

The whole effort is rooted in **bidirectional** inference (WI-379). The acceptance
example below must thread information in *both* directions **and** through a projection —
it is the regression anchor for the `expected → argument` direction (**WI-427**) and the
projection it feeds. (The bidirectional-inference design itself — WI-379's delivered
`argument → expected` half and WI-427's `expected → argument` half, plus the variance
soundness caveat — lives in [`expansion-during-unification.md`](expansion-during-unification.md)
§8 + its variance note; this example is duplicated there by reference.)

```anthill
operation check(s: Wrapper[P = Inner[T = String]], k: s.cell.T) -> String
operation poly[X]() -> Wrapper[P = Inner[T = X]]      -- X appears ONLY in the return
operation caller() -> String = check(poly(), "abc")   -- must typecheck
```

Three flows must meet:

1. **expected → argument (WI-427, not yet built).** `poly()`'s `X` appears only in its
   return, so it is unconstrained *from the argument*; it is pinned to `String` only by
   the **param type** `Wrapper[P = Inner[T = String]]` flowing *down* into the argument.
   Today this fails (`X unconstrained`) — args are synthesized in isolation
   (`push_visit_no_hint`). This is the missing half of "both sides."
2. **projection off the now-grounded receiver (WI-398, delivered).** With
   `poly() : Wrapper[P = Inner[T = String]]`, the call-site projection `s.cell.T` grounds
   to `String`.
3. **argument → parameter (WI-379, delivered).** `"abc" : String` checks against
   `k : String`.

Soundness twin: `check(poly(), 42)` must be **rejected** for the *right* reason
(`k : String`, `42 : Int64`) — not the current `X unconstrained`. When both pass,
"bidirectional from both sides" is restored end-to-end. **On-disk anchor:**
`wi427_bidirectional_flow_test`, `#[ignore]`'d until WI-427 lands.

## 5. What the harder cases add (deferred)

- **Plain (non-parametric) field** — `entity stateErased(provider: DataProvider)`.
  The construction's type is just `StateErased`; the declared field type
  `DataProvider` does **not** carry the specific provider, so
  `stateErased(provider = ss).provider` grounds only if the type is **refined** to
  record the field's actual type (`StateErased{provider: SubscriberStore}`). *This* is
  where "typed terms / refinement types" are genuinely required — and it is why the
  parametric form is the right starting point. (Scala 3's experimental `tracked val
  provider` is exactly this route: it keeps the constructor argument's precise type in
  the instance type, grounding `stateErased(provider = ss).provider.K`.) An abstract
  `stateErased` param stays rigid regardless.
- **Arbitrary-expression receiver** — `(expr).M`. The substrate already holds the
  receiver as a `NodeOccurrence`, so the type machinery is uniform; it adds (a) a
  grammar form (`(expr).M` does not parse yet) and (b) a **stability guard** —
  projecting an *abstract* member off an *unstable* receiver is a loud error
  (`makeProvider().K`); `let p = makeProvider(); p.K` is the escape.
### Sealing & escape (ML's avoidance problem) — resolved: the base model is escape-free

A path type is **rigid** (ungrounded) only when its receiver's type is abstract, and
that abstraction always comes from a **declared** boundary — it is never minted inside
a body. So a rigid `p.M` roots at exactly one of three places, and only the last can
escape:

| root of a rigid `p.M` | in scope | escapes? |
|---|---|---|
| **top-level / global** (`defaultKVStore`) | everywhere | never (ML's `Stdlib.Map.t`) |
| **operation interface** (a param / type-param) | the op + its callers | never (rooted at the boundary) |
| **hidden local** (sealing / existential-unpack / local type definition) | one body | yes — *and all three are absent* |

All three hidden-local introducers are **absent from the base model** — no sealing (an
abstracting return), no existentials, no local sort definitions — so no scope-local
type can be *formed*. Escape (ML's avoidance problem, where no principal avoiding-type
exists) is therefore **unformable, not merely rejected**.

**The deeper reason it cannot arise: abstraction is a call-site contract, discharged
statically per call.** `requires` and `ensures` are one mechanism — the
dictionary-passing / `req_insertion` path (011's per-call elaboration, resolved at
type-check time):

- **`requires`** discharges an op's abstract **inputs** — the caller supplies the
  dictionaries;
- **`ensures`** discharges its abstract **outputs** — the caller assumes the manifest
  facts (`ensures result.K = String` is ML's `with type t = string`, a translucent
  manifest written as a postcondition — sound because types are terms, so an equation
  is a fact).

Both **ground the abstraction at the call**, from the caller's view, so nothing
abstract *survives* a call into runtime — hence no escape and no runtime existential
packaging. An abstraction **not** discharged at the call (an unmet `requires`, an
un-manifested `ensures`) is an undischarged residual → no-silent-drop **rejects** it
(§4). That yields one rule:

> **A return must be interface-expressible** — concrete, rooted at the op's own
> inputs, or made so by an `ensures` manifest. The `requires`/`ensures` dual covers
> abstract inputs and outputs symmetrically.

**Build note.** Implement **strict** first — *forbid the abstracting return* (a return
must be concrete or input-rooted); it is the degenerate case and covers every current
use-case. Add the **`ensures`-manifest** admit-form (translucent returns — `K`
manifest, `V` still abstract) when a real need appears. **Existentials** — deliberately
letting an abstraction *outlive* its call — are the separate opt-in, co-designed
if/when wanted.

## 5.1 Value-position projection — projection is one arm of the *generic dot*

The projections so far are **type-position** (`k: s.cell.T`, a return / param / effect
annotation). The **value-position** form is the simple-looking case the architecture
currently *misses*:

```anthill
let x = [1,2,3].T     -- x = Int64, a value of sort Type
```

`.T` projects the element-type member off the receiver's type and **reifies it as a
value** (`anthill.prelude.Type` is `sort Type = ?`, the opaque handle for a reified type
— types are terms). The meaning is exactly δ-grounding (§3 rule 1):
`type([1,2,3]) = List[Int64]`, project `T` ⟹ `Int64`; so `x : Type`, `x = Int64`.

**Why it errors today, and the global gap.** Value-position member access goes through
*one* place — the `DotApply` build frame in `kb/typing.rs` — which resolves `member`
**only to an operation** (a method, or a spec-provided op), synthesizing
`op(receiver, …)`; anything else falls to `DotDispatchNoMatch`. So `[1,2,3].T` looks for
an *operation* `T` on `List`, finds none, and errors (*"no such member (dot dispatch)"* —
probe-confirmed, 2026-06-09). Meanwhile the **type-position** projection is a *separate*
subsystem (`eliminate_type_projections` → `resolve_receiver_path_type` →
`project_type_member`). The two share nothing but `project_type_member`, and the
value-position dot never reaches it.

That is the **"something global we are missing"**: *member resolution off the receiver's
type is one operation with several arms — method, field, and type-member projection — and
`project_type_member` is the type-member arm.* The value-position dot wires only the
method arm; the type-position path reimplements receiver-typing (`resolve_field_type`) and
uses `project_type_member` directly. The unification is a single resolver

```
resolve_member(type(receiver), member) -> Method(op) | Field(τ) | TypeProjection(τ)
```

used by **both** the `DotApply` frame and the annotation-side receiver resolver. `.Sort`
(η) is the whole-type case of the `TypeProjection` arm; plain value-position field access
(the existing **INC-1b** follow-up — see the `DotApply` frame's TODO) is the `Field` arm.
So the right altitude is not "add a value-position `.T` special case" but "give the dot
its `TypeProjection` arm, the same one the annotation path already projects with."

**Implementation (value-position, concrete — the immediate win).** In the `DotApply`
build frame, *before* the `DotDispatchNoMatch` error and after method resolution fails:
if `member` is `Sort` or a type member the receiver's sort declares
(`kb.type_params_of_sort(recv_sort)` contains it), call
`project_type_member(kb, &recv.ty, &short, &ctx, dot_span)` — **the receiver's type
`recv.ty` is already inferred and in hand** at this frame (it is what `recv_sort` is read
from), so no bespoke receiver-typing is needed here, unlike the annotation path. Produce a
`TypeResult` whose **value** is the reified projected type and whose **type** is
`anthill.prelude.Type` (the typer already mints this sort for type-valued expressions,
`kb/typing.rs:1595`). A concrete receiver ⟹ δ-grounds to the member (`Int64`); an abstract
receiver ⟹ a **neutral** `Type` value (the WI-400 relaxation: project returns the rigid
neutral rather than erroring).

**Relationship to WI-400 / eager-let-alias.** `[1,2,3].T` is a *concrete* receiver, so it
is pure δ — no σ-equality, no aliasing. The two meet only when the receiver is abstract:
`let a = abstractProvider; let x = a.K` makes `x` a neutral `Type` value, and
`let z = x` aliases it (eager-let-alias, §4.1), so `z` and `x` denote the **same** neutral
type. So value-position projection rides the *same* δ / ζ / eager-let-alias model — it is
not a new mechanism, only the missing wiring of the type-member arm into the generic dot.

## 6. Seam map

| piece | seam |
|---|---|
| construction infers `P` | **WI-384** |
| `s.provider.K` classified + eliminated (compound receiver) | **WI-376** + **WI-397** |
| `k : s.provider.K` depends on param `s` (cross-param + synthesis order) | **WI-398** |
| projection at `let` / body / `requires`, not only call args | **WI-399** ✓ (delivered 2026-06-09: eager δ-elimination at the let annotation site + a loud `unify_types` guard refusing an un-eliminated `ExprCarried`) |
| identity by unification; rigid abstract member; abstract-stays-poly | **WI-376** (keystone) — **DELIVERED 2026-06-09**: abstract-stays-poly co-delivered by WI-400 inc. B (the requires-side + the bare-concrete case), plus the cross-sort provider **divergent member name** (`List provides Iterable[List[T], T]` ⟹ `l.Element` grounds to `List`'s `T`; `project_via_provided_spec` in the concrete arm of `project_type_member`, effect members excluded per WI-396) |
| equality = ζ/δ/η conversion; non-injective `ExprCarried` head; delay + no-silent-drop | **WI-400** — **increments B + C DELIVERED** (2026-06-09): σ-equality ζ arm (`expr_carried_zeta`) in `unify_types` **and** both `types_compatible` dispatchers, replacing the WI-399 guard; abstract→neutral (`project_type_member` → `ProjResult`), co-delivering WI-376 abstract-stays-poly; **eager let-alias** (`let y = z ⟹ y.M ≡ z.M`, the receiver-alias map). **Remaining:** flexible/rule-body delay, §1 abstract dispatch, value-position field access (§5.1) — §4.1 |
| value-position projection (`let x = [1,2,3].T`); the generic dot's `TypeProjection` arm | **§5.1** (own follow-on — wire `project_type_member` into the `DotApply` frame; not yet a WI) |
| `expected → argument` inference (push the param type into a polymorphic arg); the missing half of bidirectional flow | **WI-427** (anchor: the §4.1 bidirectional-flow checklist example) |

The parametric working example of §1 needs **WI-384 + WI-376 + WI-397 + WI-398**, the
two rules of §3, and the conversion/delay discipline of §4 (its soundness rule is
**WI-400**, an arm of the Rust typer's `unify_types`). **WI-370** (custom unification at a
discrimination-tree node) is the *self-hosted* realization of that same soundness rule,
deferred to the anthill-typing track (WI-010 / WI-079) — downstream of the bootstrapped
Rust typer, not a prerequisite of any seam here. The plain-field and arbitrary-expression
cases (§5) are the genuinely new representation work, deferred.
