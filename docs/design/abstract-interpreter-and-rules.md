# Abstract interpretation and rules — the body as the single source, specialization on demand

## Status

Design (2026-07-03). **Realizes** the design-first acceptance of **WI-580** ("operation body as the
single source of truth — derive rule views, retire hand-written duplicates"), and **re-answers its
scope item 1**: derived rules are *not* materialized as semantic KB objects; the body is unfolded
on demand by a single specializer.

**Implementation status (2026-07-09).** §3.3's SLD one-step unfold is **delivered** as
abstract-interpretation-on-suspend: when a `SemEq` goal has an operand that is an unground bodied
op-call whose body `match`es on a flex scrutinee — the shape the direct call (`reduce_op_value` /
the eval bridge) *suspends* on — the resolver case-splits the body into one choice-point per arm
(`KnowledgeBase::unfold_eq_operand`, engine in `kb/body_specialize.rs::folded_call_match`). This
covers **structural** ops (relational `append(?a, ys) = zs` solves; `code(?c) = ?v` enumerates), so
`list.anthill`'s `length`/`append` `<=>` twins are **retired** (a ground call folds via the bridge,
a non-ground occurrence unfolds). Soundness gates in place: only DISJOINT constructor arms
case-split (a catch-all needs earlier-arm negation guards — undecidable on an unground scrutinee →
declined to a WI-519 residual, not over-generated); effectful / `requires`-carrying bodies are
declined (not yet threaded); an op-call OTHER operand is declined.

**`member` — the eq-vs-unification soundness fix, DELIVERED (2026-07-09).** `member`'s `:-`
unification twins are **retired**: they branched on `cons(head: ?x, …)` (structural unify),
diverging unsoundly from the body's declared `eq(head, x)` for a type whose `eq` is not structural
equality. The relational view is now derived from the body — the resolver routes a *bare* rule-less
bodied **Bool** goal (`member(?x, ?l)`) to `eq(member(?x, ?l), true)`
(`KnowledgeBase::bare_bodied_bool_relation` + the `step_init` routing), so a ground call decides
via the eval bridge *using the declared `Eq`* and an unground one suspends to a WI-519 residual (§5,
the "sound checker, not generator"). The route is gated **effect-free** (an effectful body is not a
logical relation — `Stream.isEmpty` is excluded) but NOT requires-free (unlike the unfold's
`folded_call_match` gate): `member`'s `requires Eq[T]` is discharged at the body's own `eq(head, x)`
call by value-directed dispatch, which the bridge honours. A carrier whose `eq` is defined by
`<=>` *rules* (rather than a runnable body) is still decided — the bridge fires those rules by
ordinary SLD — so retiring the structural twins strands nothing decidable. This is the §5 semantics **without** the nested-choice
`if`-flattening / an owed `requires Eq[T]` on the unfold: those are needed only to *case-split* a
relational `member` over an **unground list**, which is inherently non-terminating (infinitely many
lists contain `?x`; the `= true` operand — unlike `append`'s finite `zs` — does not bound the
recursion). The bridge-plus-residual realizes §5's "evaluate or suspend `eq` per branch" and
*terminates*; the `if`-flattening unfold path stays deferred until a bodied Bool op has a
**terminating** relational consumer (design §10 Q4: add a mechanism only when a consumer serves it).
The requires-gate in `folded_call_match` therefore still declines `member` for the unfold — correct,
since the bridge (not the unfold) serves it. **Deferred:**
the typer inlining site (§3.2) — abandoned as type-unsound (it rewrote a call before the signature
check); the prover site (§3.4). **Related:** proposal [043](../proposals/043-simp-rewrite.md)
(`[simp]` rewriting), proposal 049 (`<=>`), WI-283 (typer-hosted firing — the natural host for the
inlining site), WI-502 / [`constrained-term-substrate.md`](./constrained-term-substrate.md) and
WI-246 (the resolver substrate the SLD site is gated on), WI-519 (undecided-as-data — where a
suspended guard lands), WI-578 (typed-value carrier — unaffected, per WI-580), proposal
[050](../proposals/050-local-interpretation.md) (Γ — the specializer's logical environment; §6
supplies its missing effect-kill rule), proposal
[046](../proposals/046-region-tracking-and-effect-derive.md) (the footprint/region vocabulary the
transfer is keyed on), proposal [048](../proposals/048-conditional-effects.md) (guarded effects —
guard refutation composes with the kill), proposals
[027](../proposals/027-effect-handlers-and-standard-effects.md) /
[047](../proposals/047-effects-as-monads-via-reflection.md) /
[037](../proposals/037-anthill-state-model.md) (pluggable effects — the declarations §6.2/§6.5
derive the Γ-transfer from).

## 1. Why — duplication, and one latent unsoundness

`stdlib/anthill/prelude/list.anthill` hand-writes a rule twin next to each operation body:

- `length` (body at :30, rules at :35-36) and `append` (body at :56, rules at :60-61): the `<=>`
  rules are the body's match arms **restated verbatim** — pure duplication, mechanically derivable.
- `member` (body at :48, rules at :52-53): **not** a safe duplicate. The body branches on
  `eq(head, x)` — the declared `Eq` operation; the rules branch on `cons(head: ?x, …)` —
  **unification**. For a type whose `Eq` is not structural equality the rules give wrong answers.
  A latent soundness gap, not just redundancy.

Duplicates can drift or, as `member` shows, silently diverge. WI-580's principle (agreed
2026-06-28): the **body is the one definition**; its equational, relational, and proof views must
come *from* it.

WI-580 as originally scoped would fix this by **deriving rules at load and materializing them**.
This doc supersedes that mechanism: materialized derived rules are still a *second representation*
in the KB — two objects every consumer can disagree about, plus a derivation pass to maintain. The
design below keeps the body as the **only** semantic representation and produces each view **on
demand**, by abstract interpretation.

## 2. The key equivalence — a derived rule IS one step of abstract interpretation

`rule append(cons(head: ?x, tail: ?xs), ?ys) <=> cons(head: ?x, tail: append(?xs, ?ys))` is
exactly what abstractly interpreting `append`'s body yields when the scrutinee is specialized to
`cons(?x, ?xs)`: the `match` reduces, one arm survives, the recursive call remains as a residual.

So "generate rules from the body" and "abstractly interpret the body at the use site" are **not
rival semantics — they are the same specialization at different binding times**:

| | derivation (WI-580 original) | on-demand (this design) |
|---|---|---|
| when | load time, per constructor | use time, at the *actual* argument pattern |
| product | materialized rules, discrim-indexed | transient residual (materialization = cache only, §8) |
| depth | one constructor layer per rule | as deep as the argument is known (under fuel) |
| coverage | ops someone derived for | **every** pure bodied op, uniformly |
| drift | none in-source, but a second KB object | structurally impossible — one representation |

This reframing makes the question tractable: it is about **caching and binding time**, not about
what the rules mean. Everything below is consequences.

**One step, precisely.** One step = unfold *this* operation's body once with the call's arguments
substituted; reduce each `match` whose scrutinee's head constructor is known; leave every nested
call — including the recursive one — as a residual call. Deeper reduction is *repeated* one-steps
under fuel, which is exactly the WI-283 firing discipline already shipped (fuel-on-`Visit`, fired
result re-visited on the same work-stack).

## 3. The specializer — one engine, per-consumer entry points

One shared **body specializer** (the abstract interpreter). Each consumer invokes it at its
natural time; none reads a materialized derived rule.

### 3.1 Evaluator — unchanged

The interpreter already runs bodies directly. Nothing needed; the evaluator is the proof that the
body is executable knowledge.

### 3.2 Typer / compile-time rewriting — threshold-gated inlining

At a typed occurrence `append(cons(1, nil), ys)`, specialize the body against the actual
arguments; **if the residual's size is under a threshold, inline it** (then the WI-283 loop
re-visits and may fire again, fuel-bounded). This subsumes what a derived `[simp]` rule would do
and does it better: a concrete argument reduces through several layers in one specialization,
where per-constructor rules fire one layer per fuel step.

This is the classic inliner heuristic — *Secrets of the GHC Inliner* (unfold when the specialized
body's size, after discounts for statically-known arguments, is below a threshold). The host is
the existing WI-283 per-node hook in `build_type` (reassemble → try-fire → re-visit); "fire a
`[simp]` rule" and "inline a small specialized body" are the same move at that hook, differing
only in where the RHS comes from.

**The threshold is sound here** because declining to inline loses nothing: the call stays opaque
and is still evaluated at runtime.

### 3.3 SLD resolver — one-step unfold, case-split on unknown scrutinees

The one consumer that needs something rule-*shaped*: relational and backwards use
(`member(?x, ?l)` enumerating members) requires a **case split** — one choice point per match arm,
the scrutinee unified against the arm's constructor pattern, the arm's residual body becoming the
alternative's goals. On demand, that means the resolver **mints alternatives from a body** instead
of only from indexed rules:

- goal functor has a body → one-step unfold;
- scrutinee head known → deterministic reduction (no choice point);
- scrutinee unknown/partial → one alternative per arm (`nil` arm: unify `?l <=> nil`, residual
  `false`; `cons` arm: unify `?l <=> cons(?h, ?t)`, residual `if eq(?h, ?x) …`);
- recursion terminates per-step by construction — the residual's recursive call is a new *goal*,
  handled by SLD's own search, not by the specializer.

**The choice-point substrate already exists — proposal
[033](../proposals/033-resolver-primitives-and-disjunction.md) /
[033.1](../proposals/033.1-cut-and-the-barrier-mechanism.md).** The kernel has native goal-side
disjunction: `Candidate::Continuation` (a body-only candidate, no head match), the n-ary
`ChoicePoint` machinery under the binary `push_choice` surface, shared-tail semantics with
σ-clone-per-branch isolation, projection-level dedup, and barrier-tagged choice points for cut
(033.1, WI-568). 033's own design principle is §2's principle stated for the resolver: inline
rule-lifting ("synthesize `or_NNN` rules per call site") "works for one feature but does not
compose" — one primitive instead. Materialized derived rules *are* rule-lifting; the unfold is
the primitive-based rewrite. The mapping:

- **known-constructor scrutinee** → one `Continuation([arm-residual ⧺ tail])`, no choice point;
- **unknown scrutinee, constructor-disjoint arms** (the normal case) → an n-ary `ChoicePoint`,
  one `Continuation` per arm: `[s <=> pᵢ, armᵢ-residual, …tail]`. The shared tail carries the
  result var `?R`, linking every arm to the caller — exactly 033's shared-tail semantics, whose
  correctness argument (σ-clone isolation, no tail renaming) is already written;
- **overlapping arms** (catch-alls) → later alternatives carry earlier-arm *negation* goals —
  undecidable on an unbound scrutinee ⇒ WI-519 undecided residual, never lost/duplicated answers.
  (The same `¬fact(pⱼ)` negations 050's match rule puts into Γ — one rule, static and relational
  faces.);
- **arm bodies flatten to goal conjunctions** (ANF-style: nested calls become `g(x) <=> ?t`
  subgoals; `if c then A else B <=> ?R` mints
  `or((c <=> true, A <=> ?R), (c <=> false, B <=> ?R))` — branches mutually exclusive by `c`'s
  value). This is classic functional-logic flattening: the unfold is **needed narrowing** (the
  Curry evaluation model), riding 033's choice points as substrate;
- **cut/NAF for free**: unfold-minted `Continuation`s are barrier-tagged like any choice point
  (033.1), so an enclosing cut prunes them with no special casing; NAF sees them as ordinary
  candidates in the sub-resolution.

What remains gated on the carrier substrate is *representation*, not mechanism: bodies are
`NodeOccurrence` trees and `Continuation` carries `Vec<TermId>`, so per-unfold minting
transit-interns transient goals (the accepted `lower_query` precedent) until the `Vec<Value>`
goal migration lands — 033 Q4 explicitly keeps that door open ("do not key off `goals:
Vec<TermId>` as a load-bearing contract"; the WI-246 line). Type-directed arm applicability
interacts with WI-502 as before.

**Precedence during migration:** while a functor has both hand-written rules and a body
(`member` today), rules win — body-unfold fires only for rule-less bodied functors, preserving
the status quo until WI-580's retirement flips each duplicate; "both exist" should eventually be
a loader warning (it is exactly the duplication WI-580 outlaws).

### 3.4 Prover / SMT — defining equations extracted on demand

Proof wants defining equations, but proof obligations are generated per-proof anyway; the same
one-step specializer produces the equation set for an operation when a proof needs it (each arm's
specialization *is* a defining equation). Extra **laws** (e.g. `append` associativity) are
**theorems proved from the body** — never hand-written defining rules (unchanged from WI-580).

### 3.4.1 Implementation design (WI-669)

**Status:** in progress (2026-07-11). The SLD prover tier (`by derivation` / `discharge_by_derivation`,
`kb/proof_verify.rs`) already reads bodies through §3.3's delivered unfold. The remaining piece is
the **SMT tier** (`by z3`): `anthill-smt-gen` translates rule/fact bodies to SMT-LIB but has no path
from an *operation body* to defining equations — a bodied op called in a proof-rule body is left
uninterpreted. WI-669 closes that.

**What a "defining equation" is here.** For a pure `op(params) -> T = body`, one-step-specialize
`body` and read its arms. Each arm is a **guarded equation** `op(params) = resultᵢ :- guardᵢ`, where
`guardᵢ` is the conjunction of branch conditions reaching that arm — for `match`, the
scrutinee-vs-pattern unification; for `if`, `cond = true` on the then-arm and `cond = false` on the
else-arm — and `resultᵢ` is the reduced arm body. Admitted arm sets are exhaustive and mutually
exclusive, so the set is equivalent to one functional definition
`op(params) = ite(guard₁, r₁, ite(guard₂, r₂, …))`. Recursion in a `resultᵢ` (a sub-call
`op(smaller)`) is **not** unfolded by the specializer — it is a fresh call the *consumer* re-drives
on demand (bounded by the concrete argument structure), the same "recursion is search, not the
specializer" discipline as §3.3.

**Engine entry point** (`kb/body_specialize.rs` — landed 2026-07-11, increment 1a). `defining_equations`
(a sibling to `folded_call_match`) reduces the body one step and `flatten_arms` splits it into guarded
arms, exposed as `KnowledgeBase::op_defining_equations(op)` over the op's parameters as DeBruijn vars:

```rust
pub struct DefiningEquation { pub guards: Vec<DefiningGuard>, pub result: Rc<NodeOccurrence> }
pub struct DefiningGuard   { pub cond: Rc<NodeOccurrence>, pub negated: bool }
impl KnowledgeBase { pub fn op_defining_equations(&mut self, op: Symbol) -> Option<Vec<DefiningEquation>> }
```

- **Carrier-neutral — occurrences, not `TermId`.** A defining equation is transient, on-demand-derived
  structure, which the Representation note says *not* to intern; and smt-gen already consumes rule
  bodies as occurrences (WI-246). So the equation stays a goal occurrence and the consumer never forces
  the **partial** occurrence→`TermId` conversion — which cannot represent control-flow (`occurrence_to_term`
  asserts/⊥s on `If`/`Match`), an intrinsic fact of goal position, not an incompleteness. Any lowering
  happens at the consumer's own atom boundary, which rejects an unrepresentable shape loudly. *(An
  earlier draft returned `TermId`; that round-trip reintroduced the boundary WI-246/668 removed and
  created a partial-transformation crash/⊥ hazard — dropped.)*
- Reuse `bind_params` + `reduce`; `flatten_arms` splits a residual `Expr::If` into two guarded arms
  (then: `cond`; else: ¬`cond`), recursing so nested `if`s accumulate conditions.
- **Admitted this increment: `if` + single-expression bodies.** A residual `match` is declined
  (`None`) — ADT defining equations need SMT datatype support (future) + WI-679; `reduce` already
  declines `let`/higher-order. Loud decline throughout.
- **Gates:** keep **purity** (an effectful body is not an equation, §9). The `requires` gate is kept
  for now (relaxing it to carry the dictionary as an antecedent is future); the arithmetic consumers
  are requires-free. No flex-scrutinee / disjoint-constructor gate — those are §3.3 *relational*
  guards; here guards are asserted explicitly.
- **`let`** needs `Expr::Let` in `reduce` — the transponder follow-on (WI-679); increment-1 and WI-681
  consumers are `let`-free.

**The SMT seam (increment 1b).** A proof references the equations by **calling the bodied op in the
proof-rule body** — no new surface syntax (§3.4), and (function-as-relation) with the result as the
trailing arg: `clamp(?x, ?r)`. The driver holds `&mut kb`; before it emits the obligation
(`dispatch_z3` → `run_smt_subquery`), it scans the obligation rule's body-nodes for goals whose functor
is a **rule-less bodied op** and, for each, synthesizes a transient defining rule
(`KnowledgeBase::synthesize_op_defining_rule`, sibling to `op_defining_equations` in
`kb/body_specialize.rs`):

- **Refold, don't re-flatten.** `op_defining_equations` returns the *flattened* guarded arms; the seam
  refolds them into one nested `Expr::If` occurrence — `ite(conj(g₀), r₀, ite(conj(g₁), r₁, … r_last))`,
  dropping the last arm's guard (arms are exhaustive + ordered, so the fallthrough is unconditional). A
  guard conjunction is built from the arm's `DefiningGuard`s: a negated guard wraps its `cond` in
  `Bool.not`, multiple guards join under `Bool.and`. (For a single top-level `if` — the demonstrator and
  the lf1 GPS consumer — this is just `Expr::If { cond, then_arm, else_arm }`, no `and`/`not`.)
- **Fresh-`Global` frame, not raw DeBruijn.** The synth head `op(g₀…g_{n-1}, g_result)` and body
  `g_result = <refolded-if>` are built over **fresh `Var::Global`s** (one per param, one for the result),
  then handed to `assert_rule_debruijn_with_nodes`, which collects those Globals and converts them to
  De Bruijn with the correct arity. Feeding raw `Var::DeBruijn` occurrences (as `op_defining_equations`
  emits) would leave the collector with zero head vars → arity-0 → a malformed rule; the fresh-Global
  round is the load-bearing detail. Head **functor is the op symbol itself** (registered under label
  `<op_qn>__defeq` for idempotency) so smt-gen's ordinary `rules_by_functor → try_inline_rule_call`
  path inlines it at the `clamp(?x, ?r)` call unchanged (`anthill-smt-gen/src/lib.rs`).

**Prerequisite: WI-680 (smt-gen conditional lowering).** The refold produces an `Expr::If`; smt-gen's
`translate_expr` had **no** expression-position conditional path (only arithmetic + inequalities-as-goals),
so an `ite`/`if` subterm died with `unhandled arithmetic op 'ite'` — a *general* gap that also blocks
stdlib's own hand-written `ite` twins (`sign`/`max`/`min`). Extracted as prerequisite **WI-680**: teach
`translate_expr` to emit `(ite …)` for `Expr::If` and the `Bool.ite` functor, with a `translate_condition`
helper (inequalities + `eq` + `Bool.and/or/not`). *(An earlier draft of this note claimed "no smt-gen
change"; that was wrong — the conditional lowering is unavoidable, and belongs in smt-gen as a general
capability, not smuggled through the seam.)* A residual the emitter still can't lower (an ADT arm) is
rejected at smt-gen's own non-`Fn`-goal / `translate_condition` boundary — loud, at the right layer.

Increment 1b's demonstrator is a small **arithmetic / `if`** bodied-op property (not `append`/`length`:
those are ADT `match` bodies, which the SMT tier can't lower without datatype support). This is also
closer to the lf1 consumers, which are all arithmetic. It discharges with **no** hand-written `<=>` twin.

**Consumers:**
- **arithmetic / `if` bodied-op property** — WI-669 increment-1b demonstrator. `if`/expr, `let`-free.
- **lf1 GPS `desired_position`** ([WI-681]) — single-arm `Vec3` body, `let`-free; derives the
  formation-geometry separation `|offset|` from the body, retiring the hand-planted `4.0` in
  `real_pose_at(0, Follower, …)`. Needs a QF_NRA `cos²+sin²=1` fact — a backend wrinkle, not engine.
- **lf1 transponder ranking** (follow-on) — the real drift case: `decrease_violation_transponder`'s
  hand-written `?upc_next = ?upc + 1` appears to **diverge** from `step`'s clamp-through-0
  (`else if gte(upc,0) then upc+1 else 0`), which snaps a post-armed `upc < 0` straight to `0`, not
  `upc+1` (confirm at runtime). Deriving from the body removes the drift and may revise the `N = 6`
  bound. Blocked on `let` in `reduce`.

## 4. The threshold — an optimization knob, NEVER a semantic gate

- **Typer site (§3.2):** threshold-gated. Declining to inline leaves a runtime-evaluable call;
  purely a compile-time cost/benefit choice.
- **Resolver site (§3.3):** **no threshold.** If `member(?x, ?l)`'s unfold were skipped because a
  residual "looks big", answers silently disappear — a data-dependent silent skip, exactly what the
  project's loud-error principle forbids. One-step unfolding at SLD is naturally bounded (one
  unfold per goal; recursion belongs to the search), so it needs no size limit.

Stated as an invariant: **relational completeness never depends on a heuristic; the threshold
governs eager inlining only.**

## 5. `member` walked through — the strongest argument for on-demand

The derivation route must turn `if eq(head, x) then true else member(x, tail)` into clauses — and
the else-arm's condition is `eq(h, x) <=> false`, **not** negation-as-failure, over a spec op that
may not decide (abstract `T`, custom `Eq`). That is a delicate clause-synthesis problem: a
correct derived clause set is

```
member(?x, cons(head: ?h, tail: ?t)) <=> true  :- eq(?h, ?x) <=> true
member(?x, cons(head: ?h, tail: ?t)) <=> ?r    :- eq(?h, ?x) <=> false, member(?x, ?t) <=> ?r
```

— noticeably more machinery than the two (unsound) hand-written rules it replaces, and it needs a
three-way story when `eq` neither proves nor refutes.

The abstract interpreter just **evaluates or suspends the `eq` call in each branch**:

- the declared `Eq` is used *by construction* — the WI-580 soundness fix falls out for free, and
  the relational query correctly owes `Eq[T]` on consumption (the op-scoped `requires`, WI-562);
- an undecidable `eq` (abstract `T`) **suspends as residual**, which slots directly into the
  WI-519 model — the solution comes back `undecided(subst, residual)`, carried as data, never
  NAF-decided.

No clause encoding to invent; the if/else three-valuedness is the resolver's existing three-way
outcome.

## 6. Γ inside the specializer — and how effects transform it

**The specializer carries Γ** — proposal [050](../proposals/050-local-interpretation.md)'s logical
environment — implicitly from §2 already: "reduce a `match` whose scrutinee's head is known" is a
Γ read; entering an arm adds the pattern fact (plus earlier-arm negations); an `if` forks on
`cond` / `¬cond`. 050 describes the same walk (local interpretation is "the static sibling of the
runtime evaluator") and lists constant-folding and narrowing among its future consumers — **the
specializer IS local interpretation with one more output channel, the residual.** Γ's production
rules are 050's; this section adds the piece 050 leaves open: **effects**.

### 6.1 Effects are the only thing that invalidates Γ — so each effect needs a transfer rule

050's modification rules cover pure constructs and the *contract* channel of a call (`requires`
checked, `ensures` assumed: `Γ_out = Γ_in ∪ σ(ensures)`). As drafted the call rule has **no kill
component** — unsound the moment Γ holds resource-dependent facts and the callee's row modifies:

```
let v = c.get          -- Γ gains  v ≡ c.get
bump(c)                -- effects { Modify[c] }
…                      -- without a kill, Γ still identifies v with c's CURRENT
                       -- content → a downstream fold/rewrite uses stale knowledge
```

**Corrected call rule** (the Hoare rule for an effectful call) — kill *before* assume:

```
check σ(requires) against Γ_in
Γ_out = (Γ_in \ kill(E_callee, Γ_in)) ∪ σ(ensures)
```

**Strong update falls out of the composition**, no special case: `Cell.set(c, v)` carries
`Modify[c]` (kills the stale `c.get ≡ old`) and `ensures c.get ≡ v` (re-establishes the new
state). A guarded effect ([048](../proposals/048-conditional-effects.md)) composes too:
`Modify[c] :- G` with `σ(G)` refuted from `Γ_in` kills nothing — effect discharge and Γ-kill
share one refutation.

### 6.2 The transfer is DERIVED from what a pluggable effect already declares

Does an effect carry an "abstract-interpretation part"? **Yes — and pluggably, because it is not a
new artifact.** Pluggable effects are a day-one commitment
([027](../proposals/027-effect-handlers-and-standard-effects.md): abstract handler contract +
`RuntimeAPI` + per-host mappings; [047](../proposals/047-effects-as-monads-via-reflection.md): an
effect *declares its denotation monad in its own API*, "the spec both realizations honor"). A
pluggable effect therefore already declares three things for its **concrete** semantics:

1. its **row footprint** (045/046) — which resources it touches; a `Modify[c]` label names a
   concrete resource;
2. its **carrier / denotation monad** (027's `HandlerAction` / 047's monad-in-API) — its control
   shape;
3. its **branch-interaction contract** (037) — how its resources behave under Choice/backtracking.

The Γ-transfer is a **generic derivation over these three declarations** — no fourth authored
artifact. The state side derives from the footprint:

| declared footprint | derived Γ rule |
|---|---|
| `Modify[c]` in the row | **kill** every Γ fact that depends on `c` |
| read of `c` | kill nothing; **mark** facts derived from the result as `depends_on c` (the provenance a later `Modify[c]` kill consumes) |
| no readable state (output-only: `Console`, …) | identity |
| parametric / unknown row `?E` | **top**: kill *all* resource-dependent facts — never default to pure (the WI-374 principle); value-only facts survive. Surfaced on the warnings channel, not silent |

and the control side derives from the carrier (§6.5). So a **new user effect gets its Γ-treatment
automatically from the same declarations that make it runnable** — abstract interpretation stays
pluggable without trusting user transfer code. Honesty of the inputs is not a new trust surface:
the effect checker (046 `effect_derive`) keeps rows honest for anthill bodies, and host-bound
handlers were *already* the trusted axioms of the realization layer.

A fourth, *optional* declaration extends Γ in the positive direction — the effect's **state-fact
vocabulary** (queryable predicates over its resources that interpretation maintains in Γ); see
§6.8.

**Free-form transfer code is not the default extension point** — but see §6.5 for the explicitly
trusted escape hatch.

### 6.3 The frame rule is free, by immutability

Values are immutable; only resource-mediated knowledge can go stale. **A Γ fact in which no
resource occurs survives every effect** — `x ≡ add(y, 1)` is immortal; `v ≡ c.get` dies with
`Modify[c]`. Dependency = the resource term occurs in the fact (syntactic first cut), extended by
the read-provenance marking of §6.2.

### 6.4 Knowledge vs replacement — the §9 refusal, sharpened

Two different acts must not be conflated:

- **Interpretation for REPLACEMENT** (rewriting / inlining) — requires referential transparency;
  an equation across a `Modify` is not meaning-preserving. The §9 refusal stands for the rewrite
  *product*.
- **Interpretation for KNOWLEDGE** (Γ propagation) — always proceeds *through* an effectful call
  via the transfer. The residual keeps every effectful call, in order; Γ flows through them and
  keeps later match-reduction / guard-discharge precise.

So an effectful body is not a wall: the specializer walks it Γ-correctly, and simply may not emit
an equation across the effect.

### 6.5 Mechanism — the abstract interpreter is one more realization target

027 splits the handler model into an **abstract contract**, a host-neutral **`RuntimeAPI`
surface**, and **per-host mappings** (Rust / Scala / C). 047 makes the effect's declared monad
"the spec both realizations honor" — the interpreter realizes it by reflection, codegen lowers it
to the host's monad. The abstract interpreter slots into exactly this architecture as a **third
realization target — the "abstract host"**: an effect's Γ-step is its *handler in the abstract
domain*, and the `AbstractEnv` API is the abstract analogue of `RuntimeAPI`.

**The `AbstractEnv` API surface** (what a Γ-step may call): `kill_dependent(resource)`,
`kill_all_resource_dependent()`, `mark_dependency(binding, resource)`, read-only Γ queries — and
**no `assume`**: fact *introduction* stays in the contract channel (`ensures`, discharged per
050), never in an effect step.

**The control side is forced by the carrier.** 027's `HandlerAction` variants map mechanically to
Γ rules — nothing new to invent:

| `HandlerAction` | Γ meaning |
|---|---|
| `Pure(v)` | linear: Γ continues; footprint kills/marks of §6.2 apply; `v`'s abstract value carries type + deps |
| `Throw(p)` | this path ends; its Γ flows only to the catch/reify boundary (047 §5), meeting the other throwing paths there |
| `Fail` | path infeasible: Γ = ⊥ — the join ignores dead branches |
| `Choice(v, alts)` | fork Γ per alternative; join = 050's meet. **037's branch-interaction contract is exactly the fork rule**: a branch-local-snapshot resource gives every alternative the *same* Γ snapshot (rollback restores state); a sticky-by-physics resource (Console) has no readable Γ anyway |
| `Suspend(k)` | at the resume point: **top** on resource-dependent facts — arbitrary activity may interleave before resume (a scheduler contract could later refine this) |

**Soundness — supersedes an earlier framing.** A "knowledge-decreasing API" does **not** by
itself make arbitrary step implementations sound: the *identity* step is decreasing-expressible
yet unsound for a writing effect — **under-killing keeps facts that no longer hold**. Soundness
comes from **derivation, not authorship**: the Γ-step is computed from the declared row / carrier
/ branch-contract (§6.2), and those declarations are kept honest by the existing machinery (the
effect checker for anthill bodies; the realization-layer trust boundary for host bindings). In
abstract-interpretation terms the derived step over-approximates the declared monad's concrete
step by construction.

**The escape hatch is explicit and trusted.** An effect may *override* its derived step with a
hand-written abstract witness — an implementation of an `AbstractStep` spec, provided through the
same requirement-slot mechanism as 047's handlers — to buy precision the derivation can't see
(e.g. a transactional effect whose Γ-knowledge legitimately survives its reify boundary because
aborted writes roll back). Because under-killing is expressible there, such a witness is a
**trusted artifact of the realization layer**, standing beside host handlers (013/027's declared
unsafe boundary) — not ordinary user code. Default derived steps ship for the standard effect
catalog exactly as default handlers do (027 §Handler installation). (§6.7 narrows when the hatch
is needed at all: an *anthill-written* handler derives its precision from its own body — the
trusted witness remains only for **host** handlers.)

**Later, self-hosted:** 027 already names the future direction "write handlers in anthill
itself"; the same applies here — kernel abstract witnesses written in anthill, with the
obligation *"this step over-approximates the declared monad's step"* proved as a theorem (the
WI-580 discipline: laws are theorems, not trusted rules).

### 6.6 The abstract-interpretation state — and Γ as its fact view

**State is primary; Γ is a view.** The interpreter's working representation is not a fact set but
structured **abstract-interpretation state**, per component:

| state component | today / origin | fact vocabulary it maps to |
|---|---|---|
| types of vars / places | `TypingEnv` (WI-537 `Env{types,flow}`) | typing facts `x : T` ([022](../proposals/022-typing-as-facts.md)) |
| local value bindings (the store face) | `TypingEnv.var_bindings` | equations `x ≡ e`, `c.get ≡ v` |
| path conditions (the relational face) | 050's fact channel (`FlowEnv`) | themselves — natively facts |
| dependency index | new (the transfer substrate, §6.2) | `depends_on(p, c)` — mostly internal; serves kills |
| effect state | §6.8 | the effect's declared vocabulary (`file_open(f)`, …) |
| requirement slots | §6.7 | `provided(E, w)` |

Each component is structured, persistent host data, forked and met **natively and
per-component** — bindings meet pointwise (keep where both sides agree), facts by intersection,
dependency sets by union — never as one undifferentiated fact set.

**Γ is the mapping of this state into facts** — the fact view the 050 resolver bridge queries.
This is 050's open-question-E resolution generalized from types to every component: "the typer
keeps types and logical facts in separate envs — but the resolver sees them unified as facts",
types "snapshotted into Γ as typing facts on demand". The mapping is each component's **declared
vocabulary** (third column above). Two realizations, an implementation choice per component:

- **materialize on demand** — reify the goal-relevant slice into a transient indexed overlay at a
  discharge query. Such facts are **`Value`-carried, never `TermStore`-interned** (transient,
  per-branch — interning would leak them for the KB's lifetime; the discrim tree keys
  structurally, so a Value-carried overlay indexes fine);
- **virtual relation** — the component answers pattern queries directly as a computed relation;
  the resolver's builtin-predicate mechanism (`builtin_field_access`, `builtin_unify`) is the
  precedent. No double representation at all.

Either way the bridge stays uniform — one SLD query over (fact view ∪ ambient KB) — and the
self-hosted `holds(fact, point)` endgame keeps its substrate.

**State-as-KB is the other pole — and the vocabulary makes it a per-component choice, not a
fork.** The alternative to host-structured components is representing the state *itself* as a KB
(a persistent KB-shaped value; same caveats: an overlay, never the mutable KB; Value-carried,
never interned). It buys: no mapping layer at all — state IS facts, the abstraction-function
obligation is vacuous for that component; free introspection; and the natural substrate for the
self-hosted endgame — with state as a KB, the interpreter's *transitions* can become rules over
it (022's typing-as-facts direction, applied to the interpreter itself). It costs: the hot loop
("type of `x`", every node) becomes an indexed query instead of a map read, and the
per-component meet semantics reappear as fact-shape conventions. Because consumers see only the
**vocabulary**, the choice is per component and migratable (050's own argument: "no consumer
distinguishes a Rust-produced Γ from a rule-derived one"): born-fact-shaped, low-volume,
query-heavy components — path conditions, effect state (§6.8), requirement slots — can be
KB-native from day one; hot, iterate-heavy components — types, locals, the deps index — stay
host-structured, understood as **caches/indexes over the same vocabulary**; the KB-native
fraction grows as the tabling gate (050 §Resolution) lands. The endgame is state-as-KB
throughout, host structures surviving only as indexes.

**The soundness obligation moves onto the mapping, per component:** every fact a component emits
must hold in every concrete state its abstract state describes — the abstraction-function
condition, stated once per vocabulary instead of once per consumer.

**Extensibility falls out:** a new abstract domain (say, numeric ranges) plugs in as a new state
component plus its vocabulary (`gte(x, 0)` facts) — every consumer (guard discharge, `requires`
checking, 050's worked Int-lemma example) benefits unchanged, because consumers only ever see the
fact view.

A semantic note on vocabulary: KB `assert`/`retract` mean *the world changed*; a state update
means *we know more/less* — a killed fact may still hold. Same query shape, different meaning —
which is why the mutation interface belongs to the state, not to the KB.

**Interface: capability-split over the state components** — the channel discipline of §6.5 made
structural: each caller gets the mutators of specific components, so "effect steps never assume"
is enforced by what they can call, not by convention:

| channel | may call | component touched |
|---|---|---|
| binding sites (`let`, match arms) | `set_value(place, v)` — strong update: unset + bind, one op | store face |
| effect steps (derived or witness) | `unset_value` / `kill_dependent` / `mark_dependency` — nothing else | store face + deps index (indexed sweep) |
| contract channel (`ensures`, branch conditions, verified proofs) | `assume(fact)` | relational face / effect state |
| discharge / rewriting | `prove` / `refute` — read-only | the fact view (the 050 bridge) |
| control flow | `fork` / `meet` | all components, natively |

The §6.1 kill-before-assume ordering thereby stops being a rule to remember: the effect step
*cannot* re-establish knowledge — only the contract channel can.

### 6.7 Abstract-interpreting the handler — only above the host line (which is where it matters)

Can the handler itself be abstract-interpreted? **Only above the host line.** Most base-catalog
handlers *cannot* be explained inside anthill — they are realization-layer host code touching
real resources or kernel internals (027 is explicit: Modify, Console, Error's host fallback,
Branch's `push_choice` "must live in the host"). There is nothing to walk. This blindness is not
peculiar to the abstract interpreter — **codegen cannot see inside a host handler either**, and
047 already gives the answer for both: *the monad declared in the API is the spec every
realization honors*. Three layers fall out:

| layer | example | abstract meaning comes from |
|---|---|---|
| **host primitives** (bottom) | stdio Console, default Modify, `push_choice` | the declared spec ONLY — row footprint + operation contracts (`ensures`) + monad/carrier shape, i.e. §6.2's derivation. Not a fallback here: the primary and only mechanism. Honesty = the existing host-handler conformance/trust story; a host handler with genuinely complex abstract semantics (a host DB transaction manager) takes the §6.5 trusted witness |
| **anthill-written derived handlers / wrappers** (middle) | 047's `try_catch` / `bracket` / `transaction` — "library functions over `provide`/`perform`"; a buffered-store wrapper; 027's "write handlers in anthill" direction (derived effects) | interpretation of the body (below) — the WI-580 principle recursed: the body is the single source of its abstract meaning; it bottoms out in `RuntimeAPI` primitives with kernel-assigned transfers (`kb_assert` ≙ `Modify[kb]`, `push_choice` ≙ Choice-shape, `raise_error` ≙ Throw-shape) |
| **ordinary op bodies** (top) | everything else | §3 |

The split lands fortunately: the bottom layer's abstract semantics are **simple by nature** —
that is why they are primitives ("mutate this resource", "emit output") — so declaration-derived
transfers capture them without loss; the *complex* Γ-behavior (transaction boundaries, buffering,
undo) lives in the composition layer, which is exactly the layer expressible in anthill over the
primitives. **Interpretation is impossible where it isn't needed, and possible where it is.**

**What interpreting a middle-layer handler yields**, in increasing ambition:

1. **Footprint** — the body's derived effect row. This is 046 `effect_derive` applied to the
   handler body — *already-planned machinery*, not a new analysis. Payoff: a buffered store
   handler writes `Modify[buffer]`, not `Modify[store]` → only buffer-facts die. The §6.5
   "transactional precision" example is thereby **computed, not trusted**.
2. **Carrier shape** — which `HandlerAction` variants the body can actually return. A Pure-only
   handler needs no fork/⊥ machinery at its perform sites; the §6.5 table narrows to the possible
   variants. (027's handlers-never-hold-the-continuation design pays off: no abstract
   continuations needed — the caller-side walk applies the carrier's Γ-meaning at the perform
   site.)
3. **Value summaries** — result knowledge: a Reader handler returns *its* constant; `Cell.set`'s
   `ensures` re-establishes `c.get ↦ v` *through* the handler indirection.

**Soundness — bound and refine:**

- The effect *declaration* is the upper bound, enforced by
  `derived_row(handler body) ⊑ declared row` (+ the handled effect discharged) — the same
  effects-⊆ refinement check as operation override (the WI-347 precedent). That check is what
  makes §6.2's declaration-derived transfer sound when the installed handler is **unknown**.
- A statically-known handler's interpreted summary is a **tighter transfer**, sound because
  bounded by the check.
- **Host handlers stay axioms** at the declaration bound (or a §6.5 trusted witness — now needed
  *only* for them).

**Handler-known-ness is ordinary Γ knowledge.** `provide(effect, witness)` is a store-face
`set_value(requirement_slot, witness)` (§6.6); a perform site consults Γ: slot bound to a known
witness (the lexical `try_catch` / `transaction` library shapes, 047 §7) ⇒ specialize through the
witness's op body — **one more dispatch indirection for the §3 specializer** (WI-350-style
carrier dispatch), not a new engine; slot unknown (embedder-installed) ⇒ the declaration bound.
No bespoke "handler visibility" analysis.

**Degradations, honest:** dynamically-installed handlers are invisible ⇒ declaration bound;
exotic delimited-control bodies degrade to carrier-level abstraction (the §6.5 table); a
recursive handler body needs a summary fixpoint — though the kill side is exactly 046's bounded
per-operation question, already designed.

### 6.8 Effects as fact providers — state vocabularies in Γ, typestate for free

Effects are not only killers of knowledge. An effect may declare a **state-fact vocabulary** —
predicates over its resources (`file_open(f)`, `in_transaction(store)`, `lock_held(m)`,
`provided(E, w)`) — that live in Γ, are queryable through the 050 resolver bridge, and are
added/removed as interpretation proceeds. **No new channel is needed**; the lifecycle rides the
two existing ones, plus Γ's scoping:

- **added** by an operation's `ensures` *in the effect's own vocabulary* —
  `open(f) ensures file_open(f)` — the contract channel; effect steps still cannot `assume`
  (§6.6's capability table gains no new row);
- **removed** by the footprint kill: state facts mention their resource, so `close(f)`'s
  `Modify[f]` sweeps `file_open(f)` with everything else f-dependent. §6.1's kill-before-assume
  ordering *is* the state transition — kill the old state, `ensures` establishes the new;
- **region-scoped** facts (`provided(E, w)`, `in_transaction(store)`) ride Γ's lexical layering
  (050 §Nesting): pushed at the `provide`/`bracket` entry, dropped with the scope. §6.7's
  handler-slot knowledge is one instance of this pattern.

**The payoff is typestate/protocol checking with no new checker.** An operation's `requires`
written in the vocabulary — `read(f: File) requires file_open(f)` — is discharged from Γ by the
same bridge as any guard. Static KB rules compose over the dynamic facts at query time
(`can_read(f) :- file_open(f), readable(f)` — the bridge queries Γ ∪ KB). Branch joins give the
right conservatism free: a file opened only in the then-branch is not known open after the meet.
Interprocedurally it is standard assume-guarantee: 050's Γ₀ seed puts a callee's
`requires file_open(f)` into its body's Γ; the caller discharges it at the call site.

*Observation (not a commitment):* some of 027's ad-hoc gating — "statically prevented inside
Branch" for sticky-by-physics resources — becomes expressible as a `requires` over a region fact
(`in_branch`), i.e. one more consumer of the same discharge mechanism.

Soundness is unchanged: additions are contract-channel (`ensures` — checked for anthill bodies,
trusted at the host line exactly like every host binding already is); removals are the kill
channel; region facts are scope-bounded by construction.

## 7. What survives from WI-580's scope

1. ~~Derive and materialize `<=>`/relational rules from bodies~~ → **one on-demand body
   specializer** (this doc); materialization only as cache (§8).
2. **Retire the hand-written duplicates** — `list.anthill` `length`/`append` rule twins (pure
   duplication) and `member` rules (unsound divergence) are deleted once the consumer that used
   them (resolver relational queries, typer rewrites) reads the body instead. Unchanged.
3. **Laws are theorems**, proved from the body. Unchanged.
4. **Hand-written rules survive only for genuine standalone relations** — predicates with no
   operation body. Unchanged. (Consequently the explicit typed-pattern surface of
   [`constrained-term-substrate.md`](./constrained-term-substrate.md) §"Typed rule patterns" is
   needed only for bodyless relations, as WI-580 already noted.)

## 8. Materialization demoted to a cache

If profiling shows per-goal re-specialization matters (SLD hot loops re-unfolding the same op), the
specializations may be **memoized keyed by the body** — per `(op, arm)` or per redex shape — and
even fed to the discrimination tree for candidate narrowing. A cache **cannot drift**: it is
invalidated with the body it is keyed on. This recovers every performance property of load-time
derived rules ("derived rules as cache, body as truth") without re-admitting a second semantic
representation. Not part of the initial implementation.

## 9. Refusals and bounds

- **Effectful bodies do not unfold at rewrite sites** (typer inlining, SLD unfold-as-rewrite): an
  effect is not a rewrite. Refuse loudly at the specializer entry (the caller sees "not
  specializable: effects `{…}`"), don't silently skip. (True under either approach; recorded here
  because the specializer is now the single choke point that must enforce it. Sharpened by §6.4:
  the refusal is for the *rewrite product* only — Γ propagation through the effectful call
  proceeds via the effect transfer.)
- **Fuel** bounds repeated one-steps at the typer site (reuse `SIMP_FUEL` semantics: fuel spent on
  fire, `fuel==0` leaves the partial redex gracefully). The SLD site spends no fuel — one unfold
  per goal, recursion is search.
- **Higher-order / abstract callees:** a call whose functor is not a statically-known bodied op
  (a `Function`-typed value, an abstract spec op with no body) is not a specialization site —
  stays opaque at the typer, ordinary goal at SLD.

## 10. Open questions

1. **Resolver choice-point minting** — *largely resolved by 033/033.1* (see §3.3: match arms are
   `Candidate::Continuation`s on the existing n-ary `ChoicePoint`). Remaining: the residual-goal
   representation (transit-interned `TermId`s now, `Vec<Value>` goals per 033 Q4 / the WI-246
   line), and type-directed arm applicability (WI-502).
2. **Threshold calibration** at the typer site — start with a flat residual-size bound; add
   GHC-style discounts for constructor-headed arguments only if needed.
3. **Cache design** (§8) — keying (per-arm vs per-redex-shape), interaction with discrim
   most-specific-first firing ([`project_simp_specificity_discrim`]: concrete edges beat var
   edges — cached specializations must not outrank a user's more-specific `[simp]` rule).
4. **Which consumer lands first** — the typer site is nearly free (WI-283 hook + a size measure);
   the SLD site is the one that retires `member`'s unsound rules, but is gated. Retirement of the
   `list.anthill` duplicates must wait for whichever consumer actually served them.
