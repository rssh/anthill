# Proposal 050: Local Interpretation (the logical environment)

**Status:** Draft (2026-06-21)
**Depends on:** [018-expressions-and-operation-implementation](018-expressions-and-operation-implementation.md) (expression IR), [022-typing-as-facts](022-typing-as-facts.md) (typing substrate)
**Related:** [026-expression-evaluator](026-expression-evaluator.md) (the *runtime* sibling — same walk, runtime values), [025-proof-constructs](025-proof-constructs.md) (a consumer — in-body proofs), [048-conditional-effects](048-conditional-effects.md) (a consumer — WI-067 effect discharge), [013-abstract-effects](013-abstract-effects.md) / [045-effect-sets-and-expressions](045-effect-sets-and-expressions.md)
**Affects:** `rustland/anthill-core/src/kb/typing.rs` (`TypingEnv`, the `if`/`match` checking)

## Motivation

Several analyses need the *same* thing: to know, at a given point inside an
operation body, **which logical facts hold**. Effect discharge ([048](048-conditional-effects.md) /
WI-067) needs it to refute a guard inside `if neq(b, 0) then div(a, b)`; **operation
contracts (`requires` / `ensures`; see [025](025-proof-constructs.md) §"Proof for
operation contracts") need it to check a callee's `requires` and to record its
`ensures` for the code after a call**; an in-body `proof`
([025](025-proof-constructs.md)) needs it as premises; refinement narrowing,
`match` exhaustiveness, and constant-folding all want it too.

Today the typer threads only **type bindings** — `TypingEnv`
(`typing.rs`) carries `var_bindings: HashMap<Symbol, Value>` and resource
tracking, but no set of known logical *facts*; the condition of an `if` is
type-checked to `Bool` and then **discarded** (its truth is never made available
inside the branch); `match` guards are parsed but **never type-checked or
consulted**. So every one of the analyses above would otherwise reinvent
flow-sensitive fact tracking.

This proposal defines that tracking **once** — *local interpretation* — so every
consumer reuses it.

## What it is

Local interpretation is the **static sibling of the [026](026-expression-evaluator.md)
runtime evaluator**: the same forward walk over the body's `ExprOccurrence` IR,
but instead of computing runtime `Value`s it computes a **logical environment**
`Γ` — the set of facts true at each program point. It is **flow-sensitive** (each
occurrence has its own `Γ`) and **constructive** (a fact enters `Γ` only because a
seed, binding, or branch established it).

It runs as part of (or alongside) the typing pass, which already walks every body.

## The logical environment `Γ`

- `Γ` is a set of **facts** in the ordinary goal/atom vocabulary (the same
  `Value`-carried occurrences a `rule` body or a guard ([048](048-conditional-effects.md))
  is made of — so `Γ` and a guard speak one language).
- **Seed** `Γ₀` at body entry: the operation's `requires`-clause facts, its
  signature facts (parameter sorts, `result` typing), and in-scope KB facts.
- Each occurrence has a `Γ_in`; the pass produces a `Γ_out`.

## Modification rules (the abstract interpretation)

A forward pass `Γ_in → construct → Γ_out`:

- **binding** `let x = e` → `Γ_out = Γ_in ∪ { x ≡ e }` (plus any result fact `e`
  itself established). `match`-arm pattern variables bind the same way (the typer
  already does this for *types* via `extend_env_from_pattern`; here it also
  contributes the pattern **fact**).
- **operation call** `y = callee(args)` → the **Hoare rule for a call**, with `σ`
  mapping the callee's parameters to `args` (and `result` to `y`):
  - **`requires` is checked** — the callee's precondition `σ(requires)` must follow
    from `Γ_in`, discharged by the same resolver query (and, failing the trivial
    flow, the same in-body-`proof` fallback) as a guarded effect. An undischarged
    precondition is an obligation / error, never a silent pass.
  - **`ensures` is assumed** — `Γ_out = Γ_in ∪ { σ(ensures) }`: the callee's
    postcondition (with `result` ↦ `y`) becomes a known fact for the code *after*
    the call. This is how contract knowledge **flows** — an op `ensures
    neq(result, 0)` lets a later `div(_, y)` refute its `eq(y, 0)` guard straight
    from `Γ`, with no branch test written.

  So a call both **consumes** `Γ` (to check `requires`) and **enriches** it (with
  `ensures`); `ensures` postconditions are, in practice, the main thing that
  populates `Γ` beyond branch conditions and bindings. The same query bridge
  (below) serves guard discharge, `requires`-checking, and the use of `ensures`
  facts — one mechanism, three callers.
- **in-body `proof`** of `P` ([025](025-proof-constructs.md)) → once **verified**
  (its proof context seeded from `Γ_in`, and able to cite proofs up its lexical
  scope chain — see *Nesting* below), `Γ_out = Γ_in ∪ { P }`: the proved
  proposition becomes a known fact for the code after it — the **local-lemma**
  pattern, symmetric to a call's `ensures`. So a `proof` is both a **consumer** of
  `Γ` (its premises) *and* a **producer** into `Γ` (its conclusion): prove a fact
  once, then discharge / `requires`-check / cite it downstream. An *unproved* proof
  adds nothing and stands as an obligation/error — never a speculative fact.
- **`if cond then T else E`** → **fork**: check `T` with `Γ_in ∪ { cond }` and `E`
  with `Γ_in ∪ { ¬cond }`. This is where `if neq(b, 0)` puts `neq(b, 0)` into the
  then-branch. *(Today both branches share one env — this adds the fork + the
  condition narrowing.)*
- **`match s … case p → …`** → each arm with `Γ_in ∪ { fact(p) } ∪ { ¬fact(pᵢ) :
  earlier arms i }` — the constructor known inside the arm, and the negations of
  earlier arms (the "past `case 0`" narrowing). An explicit arm **guard** adds its
  predicate. *(The per-arm env fork already exists for pattern type bindings; this
  threads the fact and type-checks the guard, which is currently unvisited.)*
- **sequencing** accumulates.
- **join** (after an `if`/`match`) → the **meet** (intersection): only facts true
  on every incoming path survive past the merge.

`Γ` is monotone within a straight-line region and forks/meets at control flow —
ordinary forward dataflow, nothing bespoke.

### Nesting — `Γ` and the proof scope chain

Environments **nest** with lexical structure: each scope's `Γ` extends its
enclosing scope's, so `Γ` at a point already carries every fact established by the
ancestors on the path to it — the seed, outer bindings, the branch condition of
every enclosing `if`/`match`, and every preceding call's `ensures` or proof's
conclusion.

The **proof scope chain follows the same nesting.** An in-body `proof` may
**reference other proofs in scope** — earlier sibling proofs in the *same*
environment, and proofs in any *enclosing* environment, up to the **top-level**
proofs attached to rules at sort / namespace scope ([025](025-proof-constructs.md)).
A deep proof can therefore cite an outer lemma (or a top-level theorem) by name,
exactly as it can use an outer `Γ` fact: it is one lexical visibility, exposed two
ways — as *facts* (through `Γ`) and as citable *proofs* (lemmas). What a proof
cannot see is a *sibling* scope it is not nested in — a fact proved only in the
`then` branch is not in scope in the `else` branch, which is exactly what the
join's meet already enforces for `Γ`.

## Querying `Γ` (the resolver bridge)

To **prove or refute** a goal `G` at a program point, run `G` against `Γ ∪ KB` on
the existing SLD resolver under the `step_cap` runaway guard. The soundness guard
is the resolver's **floundering prevention**: a goal whose variables are unknown
*runtime parameters* (not KB facts) **delays** rather than succeeding — the
open-world reading of a value that is not in the closed KB. *(The typer does not
call `kb.resolve` during body checking today; this bridge is the load-bearing
new mechanism — see [048](048-conditional-effects.md) §"Discharge is constructive
refutation, not negation-as-failure" for why the polarity must be exactly this.)*

## Consumers

1. **Operation contracts (`requires` / `ensures`).** Every call checks the callee's
   `requires` against `Γ` and assumes its `ensures` into `Γ` (the *operation call*
   modification rule above). The canonical producer/consumer pair: `ensures` facts
   are the main thing that *populates* `Γ`, and `requires` the main thing that
   *queries* it — and a discharged `requires` is, structurally, the same resolver
   query as an effect-guard refutation.
2. **Effect discharge ([048](048-conditional-effects.md) / WI-067), Tier 1.** At a
   guarded call `callee(args)` with element `L :- G`, build the call substitution
   `σ` (callee params ↦ actual args), then attempt to **constructively refute**
   `σ(G)` from `Γ` at the call site (+ ground evaluation + KB). Refuted ⇒ drop the
   effect; otherwise keep / propagate. This is the "trivial flow."
3. **In-body proofs ([025](025-proof-constructs.md)), Tier 2.** A `proof` written
   inside a body (or a control-flow branch) takes **`Γ` at that point** as its
   premises and may **cite other proofs up its lexical scope chain** (sibling →
   enclosing → top-level; see *Nesting*). When the trivial flow (Tier 1) cannot
   refute a guard, discharge falls back to checking such a proof, which may combine
   `Γ`, ancestor proofs, KB rules, or an external tool. Its verified conclusion is
   in turn **added to `Γ`** (the *in-body `proof`* modification rule), so a proved
   lemma feeds later discharge / `requires` checks. See 025 §"In-body and
   control-flow proofs."
4. **(future)** refinement-type narrowing, `match` exhaustiveness witnesses, and
   reuse of the const-fold evaluator ([039](039-term-level-constants.md)) for the
   ground fragment.

## Implementation (grounded in the current typer)

The scout of `typing.rs` shows the fork/join *substrate already exists*; the new
work is the fact channel and the resolver bridge:

- **Exists:** the iterative typer Rc-clones/forks `TypingEnv` per visit; **`match`
  already forks a per-arm env** (`(*outer_env).clone()` + `extend_env_from_pattern`)
  and joins at `MatchFinal`; `if` clones the env for both branches.
- **Net-new (small):**
  1. a **fact channel** on `TypingEnv` — `facts: Rc<Vec<Value>>` (or a normalized,
     indexed fact store) beside `var_bindings`;
  2. **`if`-fork narrowing** — fork the env at the `Expr::If` visit, extending
     `then`/`else` with `cond` / `¬cond` (today both share one env, condition
     discarded);
  3. **match-guard typing + threading** — type-check the arm guard (currently
     unvisited) and add its predicate (plus earlier-arm negations) to the arm `Γ`;
  4. the **resolver bridge** — a `discharge`/`refute(goal, Γ)` helper that calls
     `kb.resolve` over `Γ ∪ KB` with floundering prevention.

So the visitor + branch fork/join is largely in place; the cost is concentrated in
the fact representation and the resolver bridge, not in restructuring the typer.

## Soundness

A fact enters `Γ` only from the seed, a binding, or a branch condition that
established it — never speculatively. Queries against `Γ` are **positive proofs**;
a goal that cannot be proved (because it ranges over an unknown runtime parameter)
stays *unknown*, enforced by floundering prevention. This is exactly what lets
effect discharge ([048](048-conditional-effects.md)) drop an effect *only* on a
proven `¬guard`, never on failure-to-prove.

## Open questions

- **A. Fact representation.** Raw goal `Value`s vs a normalized, indexed fact
  store (faster refutation, dedup, easier `¬` handling). Start raw, normalize when
  a hot path demands it.
- **B. Join precision.** Plain meet (intersection) vs limited path-sensitivity for
  hot cases (e.g. keeping a disjunction after a join). Plain meet first.
- **C. Negation of a condition.** `¬cond` for the `else` branch / earlier match
  arms: structural negation (`neq` for `eq`) vs a reified `not(cond)` fact that the
  resolver consumes — must agree with the open-world/floundering treatment.
- **D. Persistence across calls.** How far `Γ` reaches — within one body only, or
  does the guard-propagation in [048](048-conditional-effects.md) (a guarded atom
  inferred onto the enclosing op's row) carry a residual obligation outward?
- **E. Relation to [022](022-typing-as-facts.md) / the self-hosted typing pass.**
  Could `Γ` *be* facts asserted into the typing-pass KB, so local interpretation is
  itself expressed as rules, rather than a bespoke Rust dataflow?
