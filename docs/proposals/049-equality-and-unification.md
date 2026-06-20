# Proposal 049: Equality test vs. unification — `=` and `<=>`

**Status:** Draft
**Depends on:** [033-resolver-primitives-and-disjunction](033-resolver-primitives-and-disjunction.md)
**Related:** [026-expression-evaluator](026-expression-evaluator.md), [043-simp-rewrite](043-simp-rewrite.md)
**Affects:** `rustland/anthill-core/src/kb/{resolve,load,simp_rewrite}.rs`, `tree-sitter-anthill/grammar.js`, `scaland/.../parse`, `stdlib/anthill/prelude/*`, `stdlib/anthill/kernel/`, `docs/kernel-language.md`

## Motivation

A rule body that computes a value cannot name it. After WI-482/WI-483 a dispatched
`?p.x` *evaluates* during resolution, so `eq(7, ?p.x)` succeeds once `?p.x` reduces —
but `eq(?v, ?p.x)` does **not** bind `?v`. The resolver's `eq` (`builtin_eq` /
`eq_operands`, `resolve.rs:2442`/`2478`) is a pure comparator: it walks and reduces
both operands and then calls `values_equal` (`views_structurally_equal`); on a flex
operand it returns `EqOperands::Delay`, never `SuccessWithBindings`. A flex `eq` that
is never discharged becomes a **residual that masquerades as a solution** (WI-282's
old "1 solution" was a residual) — a silent skip, against the project's "loud error
over silent skip" rule.

The obvious patch — "make `eq` bind its unbound operand" — is wrong, and seeing *why*
it is wrong yields the right design.

### `eq` is a dispatched operation; binding is a resolver effect a layer below

`eq` is declared in the `Eq` spec as `eq(a: T, b: T) -> Bool` (kernel-language.md
§"Eq"). It **dispatches** to a carrier body (`IntEq.eq` → an `i64` compare) and it
**produces a value**. Binding a logical variable is not a value an operation can
return — it is a **substitution effect on the resolver frame**. So an operation that
"sometimes binds" would reach *below its own layer* to mutate the substitution. That is
not merely implicit-and-surprising; it is a **layer violation**.

The two capabilities are different *kinds* of thing living in different *layers*:

- **`=` / `eq`** — a prelude **operation**: dispatched, carrier-specific, value-producing.
- **unification** — a **resolver primitive**: structural, carrier-agnostic, effecting
  the substitution. The precedent is `push_choice` (proposal 033): an
  operation-shaped signature in `anthill.kernel` whose real semantics is a frame effect.

This proposal gives unification its own operator and keeps `=` a pure test.

## The concept map

Equality-shaped relations sit on two independent axes — **structural** (compare raw
structure) vs **semantic** (dispatch to a carrier), and **test** (yield `Bool`) vs
**bind** (unify):

|                | test (no binding)              | bind (unify)                                   |
|----------------|--------------------------------|------------------------------------------------|
| **structural** | `===` — Prolog `==` *(parked)*  | **`<=>` — unify**                              |
| **semantic**   | **`=` — `Eq.eq`**               | E-unification / AC-matching *(engine, not an operator)* |

- **`===`** (structural test) is what `builtin_eq` *literally is today*
  (`views_structurally_equal`, no dispatch). It is **parked** — it only earns a surface
  once a carrier defines an equality that *differs* from structure (set equality,
  eq-mod-n). None exists.
- **`=`** (semantic test) is the user-facing equality operation. For every current
  carrier semantic equality *is* structural, so the resolver's structural shortcut is
  sound today (see Invariant).
- **`<=>`** (structural unify) is the new operator this proposal adds.
- **bottom-right** (unify modulo a carrier's equational theory — AC-matching) is an
  **engine capability**, not a user operator; it is the plausible future home of simp
  AC-normalization, and is explicitly out of scope here.

There is no fifth concept. The design names the two cells we use (`=`, `<=>`) and parks
`===`.

## Design

### `<=>` ≜ `anthill.kernel.unify`

`<=>` has two surfaces over one `builtin_unify` — a **typed object-level** face (returns
`Bool`, binds via a frame effect) and a **term-level `reflect`** face (returns the
substitution as data). Both are defined here; *why* there are two and how they coincide is
*Two faces of one search* below.

```anthill
namespace anthill.kernel
  operation unify(a: T, b: T) -> Bool                                    -- object-level: resolver-implemented; binds via a frame effect (parallels Eq.eq)
end

namespace anthill.reflect
  operation unify(a: Term, b: Term, kb: KB) -> Option[T = Substitution]  -- term-level: none = no unifier; some(σ) = mgu (the substitution, as data)
end
```

Resolver-implemented (a `builtin_unify`), **not** an `Eq` operation. `<=>` is **just
structural unification**, and its only evaluation is **head-normalizing a node when the
unify walk reaches it** — there is *no* separate "reduce both operands fully, then unify"
pass. A bottom-first derive pass would pay to reduce subterms that a head mismatch or a
variable binding then makes irrelevant. Laziness costs nothing extra here:
`views_structurally_equal` is a *test* (it never binds), so the unification step is a
fresh recursive routine regardless — composing the per-node reduction *into* that
recursion is the same pieces, not more code. `builtin_unify(a, b)`:

1. **Head-normalize each side on entry** via the existing head-directed `reduce_operand`
   (`resolve.rs:3075` — `reduce_dot_value` + `reduce_op_value`, WI-482/483). It is
   *head-only* — it projects a `?p.x` or folds a foldable `peek(?b)`, but does **not**
   descend into constructor args — so it touches only the current node's head.
2. **Opaque op-call ⇒ Delay.** If either head is an unreduced complex op-call
   (`is_unreduced_op_call`), delay the whole goal (WI-483 substitution transparency,
   unchanged).
3. **Variable ⇒ bind and stop.** If either head is a flex var, bind it to the *other
   head-normalized side* and return `BuiltinResult::SuccessWithBindings(extra)` (the form
   pattern arithmetic already uses via `finish_result` / `ResultTarget::Bind`,
   `resolve.rs:2600`). The bound term's interior is **not** reduced — `?v <=> ?p.x` binds
   the projected value; `?v <=> cons(slow(), nil)` binds the cell with `slow()` still
   unreduced. The bind **occurs-checks**: `?v <=> f(?v)` is a loud failure, never a cyclic
   term ("know errors early").
4. **Functor / arity mismatch ⇒ fail-fast.** `f(…) <=> g(…)` with `f ≠ g` (or unequal
   arity) fails **without reducing any child** — the work the bottom-first order forfeits.
5. **Functor match ⇒ recurse** `aᵢ <=> bᵢ`, each child head-normalized on reach (step 1),
   binding sub-variables on either side: `some(?x) <=> some(3)` binds `?x ↦ 3` (today's
   `eq` *fails* this — unify is the honest substrate behaviour).
6. **Scalars / constants** compare by value.
7. **Symmetric.** Either side may be the variable side; direction is not part of the
   operator (see simp, below).

Head-normalization is **not** dispatch — projecting `?p.x` / folding `peek(?b)` is
WI-482/483 substitution-transparency reduction, not carrier-`eq` selection — so the
Invariant ("`<=>` … never dispatches") is untouched.

The caller-var pre-check (`body_builtins_delay_on_caller_vars_nodes`, `resolve.rs:3134`)
is relaxed for `<=>`: a bare-var first operand of `<=>` must **not** pre-residualize the
rule — the whole point is to let the body run and bind it.

### `=` stays a pure test

`builtin_eq` is unchanged in spirit — it tests and never binds. The companion fix:
an **undischarged** flex `=` (or `<=>`) must not be counted as a definite solution. This
is the residual-honesty fix at the solution-reporting boundary (`Solution.residual` /
NAF-groundness), and it must **not** break legitimate delay-and-rotate (`eq(?x, ?y)`
where later goals bind both) — only the *never-discharged* residual is the bug.

With `=` test-only, the NAF/floundering hazard **evaporates for `=`**: a test never
binds, so `not(=)` is always safe.

### simp and equational rules: radius-3 migration

A `[simp]` rule is today `eq(LHS, RHS)` plus a `[simp]` attribute that orients it L→R
(`meta_has_flag(.., "simp")`, `load.rs:2682`); the logical engine's `apply_eq_rules`
(`resolve.rs:1506`) already treats *every* empty-body `eq(LHS,RHS)` rule as an L→R
rewrite. So `=` is **already** doing unify-and-derive inside simp — the directionality is
smuggled through an attribute. This proposal surfaces it: every **`is_equation` rule
head** migrates `=` → `<=>`.

The migration boundary is the loader's **existing** `is_equation` classification
(empty-body eq-headed rule the engine rewrites) vs. a body-position `eq` goal. So it is
**classification-driven, not textual**:

- migrate to `<=>`: oriented rewrites — prelude `lt(?a,?b) = gt(?b,?a)`,
  `neq(?a,?b) = not(eq(?a,?b))`, list/option/`[simp]`/`[unfold]` equations.
- **stay `=`**: contracts (`ensures eq(balance(result), …)`), constraints, and body
  guard tests — these are body goals, not `is_equation` heads, and a postcondition must
  *test*, never *bind*.

**Selection stays indexed; the relabel is a functor swap, not a scan.** Matching a redex
against equational rules is *clause selection* — one redex vs many rule heads, the
discrimination tree's job, **not** a sequential `unify` over every candidate. The
resolver path already does this: `apply_eq_rules` queries `eq(current, ?result)` through
`query()` (`resolve.rs:1554`) and the tree returns `(rid, subst)` pre-narrowed. So `=` →
`<=>` is a **relabel of the indexed head functor**: `is_equation`, `eq_functor()`, and
the `apply_eq_rules` query pattern learn to recognize `<=>`-headed empty-body equations,
and selection stays on `query()`. The typer's simp firing (`try_fire`,
`simp_rewrite.rs:271`) still **scans** `rules_by_functor(eq_sym)` and runs `match_view`
per rule — the sequential-enumeration anti-pattern — so this proposal moves it onto
`query()` (the [043](043-simp-rewrite.md) §4.6 item) rather than renaming the scanned
functor. One constraint: selection is one-sided **matching** (the redex's own variables
must not bind — you choose a rewrite, you do not generalize the subject), distinct from
the two-sided **unification** a `<=>` *body goal* performs; the discrim path used for
simp selection runs in match mode.

### `<=>` is symmetric; `[simp]` supplies firing direction

An equation like `add(?x, 0) <=> ?x` is **logically symmetric** but only one orientation
terminates. Keep the operator symmetric and let the `[simp]`/`[unfold]` tag pick the
firing direction. Consequence: logical content is symmetric and **citable both ways**
via `using` (the theorem registry / proof system may rewrite either direction); the
auto-normalizer's orientation is the tag's job. A directional glyph (`~>`) would
mis-state the equational content and is rejected.

### `let ?v = expr` — directed sugar

Goal-position binding reads better as "introduce a name" than as a symmetric equation.
`let ?v = expr` is **sugar over `?v <=> expr`** — one primitive (`unify`), two surfaces:
`<=>` for symmetric equations, `let` for binding a fresh variable in a goal sequence.
(`?v <=> ?p.x` is the WI-482 acceptance form.)

**`:=` is reserved, not spent here.** It is earmarked for the *operation* form of
`Cell.set` (proposal 037 §2) — destructive assignment to a mutable cell: `c := v` ≜
`Cell.set(c, v)`, carrying `Modify[c]`. That sits on a different axis from `let`:
`let ?v = expr` binds a *logical variable* once (monotonic, single-assignment, `<=>`
underneath), whereas `c := v` *overwrites* mutable state. Spending `:=` on goal-position
binding would conflate single-assignment unification with mutation and burn the natural
glyph for assignment, so the `:=` surface is deferred to a future Cell-ergonomics
proposal.

### NAF discipline for `<=>`

A `<=>` (it binds) under `not` needs a safety rule. Primary: **static allowedness** — a
variable occurring in a `<=>` under negation must be bound by an earlier positive goal;
otherwise a **load-time loud error** ("know errors early"). Backstop: the
undischarged-residual honesty above. `=`-as-test needs no NAF discipline.

### Where `<=>` sits

These comparison/match/unify notions are one **generality continuum** — the
logic-programming idea that, pushed far enough, *nearly any* algorithm is a custom
unification (narrowing, procedural attachment, E-unification). Formally it is
**E-unification**: find σ with σa =_E σb, parameterized by the equational theory E. `<=>`
is E = ∅ (syntactic); AC enlarges E for effect rows, alpha for binders, a carrier for its
own equations. A second, orthogonal axis is *rigidity* — a **test** freezes both sides,
**matching** one, **unification** neither. So the labels (*unify*, *match*,
*alpha-equivalence*, *test*) are **conventional cuts** of one (E, rigidity) space, not
fundamental kinds: alpha-equivalence *is* unification once alpha is in E.

The cut earns its keep where the **cost** changes, not where the math does. That is the
one objective thing here: E = ∅ is unitary, decidable, and discrim-indexed; AC is
finitary; an arbitrary E is undecidable and unindexable. So `<=>` sits at the **origin**
(E = ∅, both sides free, term-level) not because the rest "aren't unification" but because
∅ is the only point that is unitary, indexable, and carrier-agnostic. The engineering law
is therefore: place each symbol at the *smallest* E (and the most rigidity) that works.
The neighbours are steps off that origin, and this proposal keeps `<=>` at it rather than
folding them in:

- **Matching** (simp / discrim selection) = `<=>` made **one-sided** (the redex's own vars
  stay rigid). A restriction of unification, not a theory on top of it.
- **`=` / `===`** = drop the binding (test-side); `=` adds carrier semantics, `===` is the
  parked structural test.
- **Alpha-equivalence** = E enlarged with bound-variable renaming (its *test* case when
  both sides are ground): binder equality, arising only where there are binders (arrow /
  dependent types, in the *type* language). It reads as "not unification" only because
  `<=>` is binder-free (the Invariant) — a *different E*, not a different kind.
- **Type unification** (`unify_view_structural`, `typing.rs:13822`) is a **separate, mixed**
  engine for the *type* language — not "`<=>` with arms". It *binds* type-vars at some
  heads, but *tests* at others (alpha at binders; the non-injective `ExprCarried`
  sigma-equality is a non-binding check, WI-400) and unifies effect rows *modulo AC*
  (`unify_effect_rows`). Term-level structural unify and type-level mixed-unify stay two
  engines.

**How they would fold (WI-370), when wanted.** Not designed here, but the path is
concrete: the discrim tree grows a *custom node* at heads with no structural `DiscrimKey`
— op-body control-flow (`let`/`if`/`match`, the WI-371 op-body-as-fact driver) or a head
flagged custom — where it halts trie descent and **delegates the residual match to a
registered `TermView` unifier**: structural `<=>` for op-body subterms, the typer's mixed
arms for a self-hosted type-unify (WI-010/WI-079). Structural pruning still handles
everything down to that node, so the common-case index is unchanged and no per-body trie
mirror is materialized; only the irreducible residual is custom-matched. The plugged-in
unifier is one of the operations placed above — WI-370 is the **delegation seam**, the
controlled step down the continuum, not a new comparison.

The type dimension reaches simp without disturbing any of this. Type-specific simp is
structural **selection + a carried-type guard**: the discrim tree selects structurally
("selection stays indexed", above), then the guard `min_sort(arg)` ⇒
`sort_provides(carrier, spec)` (`simp_fire_guard_holds`, `typing.rs:18951`) fires it.
Converging the resolver's current skip with the typer's firing — proposal-043 §4's "one
rewriter" — needs only the inferred type **carried** on the value (WI-502 — see
[typed-term carrier](../design/typed-term-carrier.md)) and a `min_sort` builtin reading it
(WI-292): a guard layered on structural selection,
**orthogonal** to `<=>` and needing no custom unification. `<=>`'s `T` in
`unify(a: T, b: T)` is the typer-time face of that same type; the resolver erases it and
unifies structurally (sound — structural unify never depends on `T`).

### Two faces of one search: `<=>` and `reflect.unify`

The kernel signature `unify(a: T, b: T) -> Bool` is honest about its *layer* but not its
*work*: `Bool` names the test outcome and hides the real product — the substitution. That
hiding is right at the object level (binding is a frame effect a layer below an operation's
return, per Motivation), but wrong for the two consumers that live *at* the substitution —
reflection, and the self-hosted type resolver (WI-010), which runs typing rules over **raw
terms with no typing in scope**. They need the substitution as a value.

So `<=>` gets a second, de-sugared representation — the **term-level `reflect.unify`**
defined alongside the kernel face above. It is already half-present in `reflect`, which
carries a `Substitution` sort (`apply` / `compose` / `lookup`, "bindings from
query/unification", `reflect.anthill:561`), the `Term` ↔ `TermRepr` bridge, and KB `query`;
the pairwise `unify` is the missing piece.

This is the **honest signature**: term-level (no `T`), substitution-returning, no sugar.
`<=>` is its object-level face — `a <=> b` ≡ *compute `reflect.unify(a, b)`, then install
σ into the frame* rather than return it. One `builtin_unify`, two faces: return the
substitution (meta) or effect it (object). The Motivation's "an operation can't return a
binding" is an *object*-level truth — at the meta level the substitution simply *is* the
value, so no layer is violated.

**And the operation already exists, as a search.** A single-pattern discrimination-tree
search *is* unification-yielding-a-substitution: `match_view` (`mod.rs:2008`) inserts one
pattern, queries with the other, returns the non-contradiction σ — that is matching
(one-sided); `<=>` is its symmetric two-sided generalization (the rigidity axis).
`query(kb, pattern)` is the same search with the *whole KB's* heads inserted. So `<=>`
(one pattern), clause/redex selection (many patterns), and `reflect.unify` are **one
operation — discrim-search + substitution — at different fan-out and rigidity**: the E = ∅
row of the continuum, exposed as data. (A richer E returns `Stream[Substitution]` rather
than `Option` — the solution-multiplicity in the return type *is* the operation's place on
the continuum, and the WI-370 custom node is what produces a richer E.)

### Invariant

> `<=>` is structural-only and never dispatches. `=` is semantic and may someday
> dispatch (today a structural shortcut, valid while every carrier's equality is
> structural).

This sentence states exactly when the two diverge and which to reach for, and defers the
`===` (structural-test) cell until a semantic-equality carrier appears.

## Lexing

`<=>` is a single token, lexed **greedy-longest before `<=`** (lte). `a <= b` is lte;
`a <=> b` is unify. Applies to both `tree-sitter-anthill/grammar.js` and the scaland
fastparse grammar. scaland **mirrors grammar + loader only** (no typer).

## Build order

1. **Residual-honesty fix** (**WI-519**) — decision-free, independent of `<=>`; an
   undischarged flex `=`/`<=>`/goal stops counting as a solution. Lands first.
2. **Grammar** (**WI-522**) — `<=>` (+ `let`) in tree-sitter and fastparse; greedy lex.
3. **Kernel `unify`** (**WI-523**) — `anthill.kernel.unify` decl + `builtin_unify`
   (per-node head-normalize via `reduce_operand` → fail-fast structural unify →
   `SuccessWithBindings`, **occurs-checked** on bind) + relax the caller-var pre-check for
   `<=>`. Teach `is_equation` / `eq_functor()` / `apply_eq_rules` + the typer's `try_fire`
   to recognize `<=>`-headed equations, moving `try_fire` off its `rules_by_functor` scan
   onto `query()` (one-sided match mode; the type-independent half of
   [043](043-simp-rewrite.md) §4.6). Also expose the term-level
   `reflect.unify(a: Term, b: Term, kb) -> Option[Substitution]` face — a thin wrapper
   returning `builtin_unify`'s substitution as data — for reflection and the WI-010
   self-hosted resolver.
4. **`let` desugar** (**WI-524**) to `<=>` in the loader.
5. **NAF allowedness** (**WI-525**) — static load-time check for `<=>` under `not`.
6. **Radius-3 migration** (**WI-526**) — `is_equation` heads `=` → `<=>` across
   prelude/stdlib (classification-driven; contracts/constraints/guards untouched). Needs
   the `<=>`-equation recognition from step 3 (WI-523).
7. **Docs** (**WI-527**) — `kernel-language.md` (Eq/Ordered/Numeric examples,
   rule-semantics §) and proposal 043 (`lhs = rhs` → `lhs <=> rhs`).
8. **scaland** (**WI-528**) — grammar + loader mirror.

**Typed half — parked, separate from this type-erased sequence:** carried-`min_sort`
type-directed `[simp]` firing, **WI-502** (design = the
[typed-term carrier](design/typed-term-carrier.md)) and **WI-292** (impl); hangs off step
3, deferred pending linked type-design issues.

## Non-goals

- The `===` structural-equality-test operator (parked until a non-structural-equality
  carrier exists).
- E-unification / AC-matching in simp — unify modulo a carrier's equational theory (a
  future engine capability, not an operator; downstream of WI-502 + WI-370, see *Where
  `<=>` sits*).
- Making `=` actually dispatch through a carrier `eq` body at resolution time (the
  structural shortcut is sound while all carriers are structural; revisit with the first
  semantic-equality carrier).
