# Proposal 031: Structured Proofs

**Status:** Draft
**Depends on:** [030-theorem-registry](030-theorem-registry.md) (witness machinery, MetaCompose, β.3 + β.6 checking, γ cite resolution), [032-symmetric-rule-arrows](032-symmetric-rule-arrows.md) (single-arrow rule grammar; head is the conclusion).
**Related:** [025-proof-constructs](025-proof-constructs.md), [025.1-z3-tactic-dsl](025.1-z3-tactic-dsl.md)
**Affects:** `tree-sitter-anthill/grammar.js` (proof-body syntax), `rustland/anthill-core/src/parse/` (IR + converter), `rustland/anthill-cli/src/prove.rs` (dispatch_structured), `stdlib/anthill/realization/realization.anthill` (ProofBodyStructured constructor)

## Motivation

Proposal 030 established the kernel-checked-witnesses architecture: tactics propose, the kernel checks. The current tactic palette covers:

- `by z3(...)` — single-shot SMT discharge.
- `by derivation(...)` — SLD goal resolution.
- `by trust(reason: ...)` — explicit user trust.
- Meta-tactics `induction(...)`, `ranking(...)` — fixed-shape compositions over named sub-rules.

These tactics are **monolithic** in the sense that one tactic invocation is one ProofRecord with one witness. When Z3 NRA can't close a chain end-to-end, the user has only two choices: split the lemma into multiple separate rule+proof pairs (forcing each into the registry separately, with the chaining manually wired through `using` cites), or fall back to `by trust(...)` and lose the mechanical content.

The lf1 case is concrete: `step_distance_lemma`'s derivation has seven distinct steps (position-distance unfolding → transition substitution → reverse triangle → scalar homogeneity → triangle → velocity envelope → arithmetic). Three of those steps mechanize cleanly in QF_LRA / QF_NRA; one is genuinely physical (velocity envelope); the rest are geometric. Today the only way to capture this in source is to write seven separate rules, seven separate proof blocks, and seven `using` chains. The structural decomposition that *humans* can see in the math becomes implicit in the cite graph — auditable but not visually obvious.

This proposal adds **structured proofs**: a tactic that lets the user write the chain step-by-step inside a single `proof` block, with each step carrying its own discharge tactic. The kernel verifies each step (using the existing α.3 witness machinery) and chains them via the existing β.3 MetaCompose semantics.

## Three architectural framings

### Framing A — separate-lemma decomposition (today's only option)

The user splits the lemma into N separate rules, each with its own proof block. Cites chain via `using`.

**Where this works:** large, reusable lemmas where the intermediate claims have value on their own (other proofs can cite them).

**Where this hurts:** intermediate claims that are mechanical bookkeeping ("the position differences after substitution sum the velocity differences"). Forced into the registry, indexed by name, polluting the trust report — but they're not real lemmas, just steps.

### Framing B — structured proofs (this proposal)

A `proof X` block can contain multiple `rule h_i: <claim>` clauses, each with its own `by <tactic>` discharge. The kernel verifies each step under the accumulated hypotheses (h_1, …, h_{i-1}). The lemma's head (its single conclusion, per proposal 032) is discharged at the end by a trailing `using ... by ...` clause.

**Where this is right:** decompositions where intermediate claims are *internal* to one proof — not citable elsewhere, just part of this lemma's chain. The trust report shows the whole proof at the lemma level; per-step witnesses are inside the MetaCompose.

**Where this is wrong:** if intermediate claims ARE reusable (other proofs would cite them), they should be top-level lemmas via Framing A. Structured proofs are not a replacement for proper rule decomposition; they're a complement.

### Framing C — fully-tactic-language (Coq / Lean style)

Proof blocks become a small imperative language with `intro`, `apply`, `rewrite`, `assert`, `clear`, `by`, etc. A complete proof tactic engine.

**Where this would help:** general-purpose proof construction, theorem prover ergonomics.

**Where this would hurt:** anthill's stance-2 commitment is "small kernel, untrusted tactics". A full tactic language is a parallel implementation of a proof assistant — substantial work, large kernel surface, not aligned with the project's scope.

This proposal commits to **Framing B**. The structured-proof tactic is a single new dispatch path; intermediate steps reuse the existing witness types and check mechanisms; nothing in the kernel changes.

## Design

### Source syntax — no new keywords

A structured proof body is a sequence of inner `rule` declarations followed by a final `using ... by ...` discharge. Reuses the existing `rule`, `:-`, `-:`, `by`, `using`, `end` keywords; no new ones. Each inner rule follows the proposal-032 single-arrow grammar — exactly one of `:-` or `-:` (or neither, for a bare-head step).

```anthill
proof X
  rule h1: <head/conclusion>
    :- <premises>             -- backward form, OR
    [using <cite-list>]
    by <tactic>

  rule h2:
    <premises>
    -: <head/conclusion>      -- forward form (mirror of `:-`), OR
    by <tactic>

  rule h3: <head/conclusion>  -- bare-head form: claim with no premises
    by <tactic>

  -- ... more inner rules

  -- Final discharge of the enclosing lemma's own head (its conclusion),
  -- citing the inner rules by label. No `rule` introducer here —
  -- this clause is a discharge directive, not a rule.
  using h1, h2, ...
  by <tactic>
end
```

**Inner-rule semantics:** each `rule h_i: ... by <tactic>` inside a proof block is a *step* — a local lemma scoped to this proof. The kernel discharges it via the per-step tactic, exactly as a top-level `proof h_i by <tactic> end` would. Each step's witness goes into the structured proof's MetaCompose sub-list. Step cite-resolution (`using h_3, ...` from a later step) consults the same in-flight registry the top-level `using` chain does.

**Concluding clause:** the trailing `using ... by <tactic>` (no `rule` introducer) discharges the enclosing proof's lemma — the rule whose name appears after `proof <name>`. The `using` cite-list typically references the inner-rule labels (`h_1`, `h_2`, …) so the chain's intermediate facts are asserted as hypotheses for the final discharge.

The inner-rule form mirrors the top-level rule form exactly. There's nothing new to learn syntactically — a proof block is a sequence of mini-rules (each in either backward `:-`, forward `-:`, or bare-head form) plus a final discharge clause. Forward (`-:`) often reads more naturally for proof steps ("from premises, derive conclusion"); backward (`:-`) reads better when the claim is the focus and premises are supporting material.

### Disambiguation: structured vs. single-tactic

A `proof X` block is **structured** iff it contains at least one inner `rule` declaration. Otherwise it's the existing single-tactic form (`proof X by <tactic> end`). The grammar can detect this by lookahead — `proof X` followed by `rule` or `by` chooses the right parse.

### Discharge semantics

For each inner rule `rule h_i: ... by tactic_i`:

1. Build the discharge context: the enclosing lemma's body, plus all previously-asserted inner rules' heads `h_1`, …, `h_{i-1}` as hypotheses.
2. Run `tactic_i` to produce a witness `w_i` for the inner rule's head (its conclusion) under that context. The witness is whatever shape `tactic_i` produces — `SmtDischarge` for z3, `SldDerivation` for derivation, `TrustedAxiom` for trust, etc.
3. Each inner rule's witness is a real witness in the kernel-checked sense. β's check pass replays it.

For the trailing `using <cites> by <tactic>` clause:

1. Build the same context plus all inner-rule hypotheses (added via the inner-rule labels `h_1`, …, `h_n` in the `using` list).
2. Discharge the enclosing lemma's head under that context.
3. Produce the final witness.

The structured-proof tactic packages all witnesses into a `MetaCompose`:

```rust
ProofWitness::MetaCompose {
  tactic_name: "structured".into(),
  sub: vec![w_1, w_2, ..., w_n, w_final],
}
```

β.3's MetaCompose checker recurses on each sub-witness. β.6's trust aggregation propagates trust flags through the whole tree. γ.1's cite gate applies per inner rule (cited rules in their `using` lists must be Discharged).

### Hypothesis splicing — the load-bearing mechanism

The previous step's head `h_{i-1}` becomes a hypothesis for `h_i`'s discharge. Concretely:

For an SMT-discharged step `rule h_i: lte(?x, ?y) by z3(logic: "LRA")`:
- The consumer's preamble normally has the rule's body as `(assert ...)` clauses.
- For a structured step, ALSO add `(assert <h_1's head>)`, `(assert <h_2's head>)`, …, `(assert <h_{i-1}'s head>)` to the preamble.
- These are ground assertions in the consumer's vars (the step's head was already discharged in a previous sub-call; its truth is now an axiom for this step).

For an SLD-discharged step `rule h_i: ...claim... by sld`:
- The resolver runs against the KB extended with the step heads as facts.
- This may need a transient-fact mechanism (assert the step heads into a session-scoped fact set, retract them after the proof completes). Implementation detail.

For a `trust`-discharged step:
- No SMT or SLD invocation; the step's head is asserted via TrustedAxiom witness.
- Subsequent steps can use the claim as if it had been mechanically discharged. The trust flag propagates.

#### Implementation strategy: transient KB rule synthesis

Phase b dispatches structured proofs by **synthesizing a transient KB rule per step** at dispatch time, then routing the step through the existing `dispatch()` path (`dispatch_z3` / `dispatch_trust` / `dispatch_derivation`). The rationale:

- **Reuses the existing `using` machinery.** Each synthesized step rule uses the same proposal-032 transitional encoding as labeled positive rules (synthetic 0-arg label-functor as KB head, user's claim as conclusion). Subsequent steps and the concluding clause cite step QNs through the standard `ProofConfig.assumptions` path, which renders cited rules via `lift_rule_to_implication_clause` in `anthill-smt-gen` — no new render helper needed.
- **Witness composition is automatic.** `dispatch_structured` calls the existing `dispatch()` for each step, collecting the returned witness (`SmtDischarge`, `TrustedAxiom`, `SldDerivation`, …) and inserting the step's resolved QN into `discharged_this_run`. The concluding clause's discharge then sees these QNs as ordinary cites; β.3 / β.6 / γ.1 process the resulting `MetaCompose { tactic_name: "structured", sub: [...] }` without modification.
- **Trust propagation works out-of-the-box.** A trust-discharged step inserts itself into `discharged_this_run` with `DischargeKind::Trusted(reason)`. The concluding clause's cite-resolution returns `Trusted` for that step, which propagates through the structured-proof MetaCompose into the parent's witness tree.
- **Idempotent re-runs.** Step QNs are resolved at load time as `<parent_proof_qn>.<label>` (deterministic). The synthesis helper checks `kb.by_functor(label_sym)` and skips if the rule already exists, so re-running prove against the same KB does not duplicate clauses.

The alternative — splicing each step's head term into `ProofConfig.assumptions` as an inline `(assert …)` clause — was considered but rejected once implementation revealed the friction: variable-naming would need explicit per-step prefixing to avoid collision with the parent rule's `var_<i>` SMT names; trust witnesses wouldn't flow through cite-resolution; the `using` machinery would need a parallel "is this a synthetic step" code path. The transient-rule approach piggybacks on infrastructure that's already battle-tested for the cited-lemma case and adds ~30 lines of synthesis logic in `dispatch_structured`.

Step `using` lists are encoded at load time with **resolved qualified names**: step-local labels (`h1`, `h2`, …) become `<parent_proof_qn>.<label>`; external cites (`triangle_inequality`) go through scope-aware resolution to their namespace QN. Phase b's dispatcher consumes the resolved QNs directly without re-running scope lookup.

### Free variables and binding scope

A step's head may contain free variables not bound by previous steps. Two cases:

**Existentially-quantified step**: `rule h: ∃ ?x. P(?x) by sld` — the resolver finds a witness for `?x` and binds it for subsequent steps. This is SLD's natural mode.

**Universally-quantified step**: `rule h: Q(?x) :- P(?x) by z3(...)` (or its forward mirror `rule h: P(?x) -: Q(?x)`) — Z3 verifies the universal, the claim is asserted as a forall axiom for subsequent steps.

The default for SLD is existential; the default for SMT is universal. Where it matters, the syntax can carry an explicit quantifier prefix; for v0 we adopt the default-by-tactic convention.

### Witness shape and check semantics

A structured proof produces:
```
MetaCompose {
  tactic_name: "structured",
  sub: [w_step1, w_step2, ..., w_conclude],
}
```

β.3's MetaCompose checker iterates each sub-witness and verifies it. The structural contract is: every sub-witness produced by `tactic_i` must have the shape `tactic_i` is documented to produce (an `SmtDischarge` for z3, etc.). β.6's trust aggregation handles the priority: any Failed sub fails the whole proof; trust propagates if all sub-witnesses pass-or-trust.

Phase γ.1's cite gate: each step's `using` clause is checked the same way as a top-level proof's `using` — every cited rule must be Discharged. Citations from a step can reference any rule (within scope), including other steps' claims (`using h1, h3` is valid in a later step).

### Sidecar persistence

WI-124's witness sidecar layer captures the full MetaCompose tree. A structured proof's sidecar JSON has the shape:

```json
{
  "rule_qn": "...step_distance_lemma",
  "verdict_label": "Proved",
  "witness": {
    "type": "MetaCompose",
    "tactic_name": "structured",
    "sub": [
      { "type": "SmtDischarge", "backend": "z3", "logic": "LRA",
        "document_hash": "...", "verdict": { "kind": "Unsat" }, ... },
      { "type": "TrustedAxiom", "reason": "velocity envelope" },
      ...
    ]
  },
  "state_hash": "...",
  "written_at": "..."
}
```

Each sub-witness's payload (SMT documents for SmtDischarge sub-witnesses) lives content-addressed under the existing blob layer. `anthill check` replays each sub-witness via β's existing infrastructure.

## Lifecycle integration

### Load

A `proof X` block with structured body parses into `ProofBody::Structured(StructuredProofBody)`. The IR carries:
- A list of `ProofStep { name, claim, using, tactic }`.
- A final `Conclude { using, tactic }`.

Loader registers this just like other proof shapes — a `ProofRecord` fact with `body = ProofBodyStructured(steps_term, conclude_term)`. The body terms are list-cons-shaped (consistent with WI-A's encoding pattern for proof bodies).

### Prove

The CLI's prove driver dispatches structured proofs to a new `dispatch_structured` function. It iterates steps, accumulating hypotheses, threading the accumulated context through each step's per-tactic discharge. The final `conclude` discharges under the full context.

### Check

`anthill check` reads the sidecar's MetaCompose witness and replays each sub-witness via β's existing per-witness checkers (β.1 for SmtDischarge, β.3 recursively for nested MetaCompose, β.4 for ScopeAxiom, β.5 for Specialization, β.6 for trust aggregation, β.7 for tampering).

## Concrete worked example: step_distance_lemma in lf1

The current by-trust step_distance_lemma in `safety_common.anthill` (rewritten in proposal-032 single-arrow form: the head is the real conclusion; the synthetic `step_distance_lemma(?w)` label term is gone, replaced by the rule's name):

```anthill
rule step_distance_lemma:
  lte(abs(?d_next - ?d_prev), ?delta)
    :- distance_at_step(?k, ?d_prev),
       ?k_next = ?k + 1,
       distance_at_step(?k_next, ?d_next)

proof step_distance_lemma
  by trust(reason: "Composition of triangle_inequality + velocity_envelope + real_pose_at transition; mechanical discharge blocked by three smt-gen limits — see comment.")
end
```

becomes a structured proof using only inner `rule` declarations + a trailing `using ... by ...` clause. Each inner step uses one arrow (forward `-:` reads naturally for proof-step authoring); a step that's a bare claim with no premises has neither arrow:

```anthill
proof step_distance_lemma
  -- h1: distance_at_step is the norm of position difference.
  -- Definitional unfolding via SLD against position_distance rule.
  rule h1:
    distance_at_step(?k, ?d_prev)
    -: ?d_prev = norm_of_pose_diff(?k)
    by sld

  -- h2: transition rule + algebraic substitution. Bare-head claim.
  rule h2: p_L(?k+1) − p_F(?k+1) = (p_L(?k) − p_F(?k)) + (v_L(?k) − v_F(?k)) · ?T_c
    by z3(logic: "QF_LRA")

  -- h3: reverse triangle inequality. The geometric leaf.
  rule h3:
    norm_of_pose_diff(?k_next) - norm_of_pose_diff(?k)
    -: lte(abs(...), norm((v_L − v_F) · T_c))
    using triangle_inequality
    by z3(logic: "NRA")

  -- h4: scalar homogeneity of norm. Bare-head claim, trusted.
  rule h4: norm((v_L − v_F) · T_c) = T_c · norm(v_L − v_F)
    by trust(reason: "Scalar homogeneity of Euclidean norm")

  -- h5: triangle on velocity diff. Bare-head claim citing triangle_inequality.
  rule h5: lte(T_c · norm(v_L − v_F), T_c · (norm(v_L) + norm(v_F)))
    using triangle_inequality
    by z3(logic: "QF_NRA")

  -- h6: velocity envelope (the genuinely physical claim).
  rule h6: lte(T_c · (norm(v_L) + norm(v_F)), T_c · (?vL_max + ?vF_max))
    using velocity_envelope
    by z3(logic: "QF_LRA")

  -- h7: collapse to delta. Bare-head equational claim.
  rule h7: T_c · (?vL_max + ?vF_max) = ?delta
    by sld

  -- Final discharge: chain h1..h7 yields the lemma's head.
  using h1, h2, h3, h4, h5, h6, h7
  by z3(logic: "QF_LRA")
end
```

The proof block is a sequence of mini-rules each with its own `by <tactic>`, followed by a trailing `using ... by ...` that discharges the enclosing lemma's head citing the inner rules by label. No new keywords — every form is reused from the existing rule grammar (single-arrow form per proposal 032).

The trust report after this lands lists three named trust dependencies:
- `triangle_inequality` (cited by h3 and h5; from its own proof block).
- h4 (`Scalar homogeneity of Euclidean norm`; trusted in this proof).
- `velocity_envelope` (cited by h6; from its own proof block).

Versus today's "step_distance_lemma is opaquely trusted" — finer-grained, audit-friendly. Mechanical backends (dReal, KeYmaera X) replace per-step `by trust(...)` with per-step `by dreal(...)` without changing the proof's structure.

The trust report (`anthill check --report-trust`) now lists:
- `step_distance_lemma`: trusted via h4 (scalar norm homogeneity).
- `step_distance_lemma`: trusted via velocity_envelope (cited from h6).
- `triangle_inequality`: trusted (from triangle_inequality's own proof block).

Three named, audit-friendly trust dependencies — finer-grained than today's "the whole lemma is trusted." Six steps mechanize. When dReal lands, h3, h4, h5 promote from trust to mechanical discharge by changing only those steps' `by ...` clauses; the rule and its overall proof structure stay.

## Implementation plan

### Phase a — schema and parser

- a.1 Grammar: add `proof_body` choice for structured form. `step` and `conclude` clauses inside a proof block.
- a.2 Parse IR: `ProofBody::Structured(steps: Vec<ProofStep>, conclude: ConcludeClause)`. `ProofStep { name, claim, using, tactic }`. `ConcludeClause { using, tactic }`.
- a.3 Loader: encode the structured body as a Term tree (`ProofBodyStructured(steps: list, conclude: term)`) consistent with WI-A's existing body-shape encoding.

### Phase b — dispatch

- b.1 New `dispatch_structured(kb, rule_qn, steps, conclude, ...)` in prove.rs. Iterates steps; for each, builds the discharge context (rule body + previously-asserted step claims as hypotheses); runs the per-step tactic; collects the witness.
- b.2 Hypothesis splicing for SmtDischarge sub-tactics: extend the consumer's preamble with `(assert <step_claim>)` for each prior step. Already factored through `ProofConfig.assumptions` (γ.1 mechanism); structured proofs reuse it.
- b.3 SLD-side step support: the resolver runs against the KB extended with step-scoped transient facts. For v0, the simplest version: convert the step's claim to a fact and assert it temporarily via the existing assumption stack (WI-108).
- b.4 Concluding step: same as a regular step but discharges the rule's head under all accumulated hypotheses.
- b.5 Witness assembly: wrap all sub-witnesses (one per step + concluding step) in `MetaCompose { tactic_name: "structured", sub: ... }`.

### Phase c — check

- c.1 β.3's MetaCompose check already recurses on each sub-witness. Structured proofs require no additional check logic — they reuse the existing per-witness verifiers.
- c.2 Sidecar persistence (WI-124) already serializes nested MetaCompose witnesses recursively. No new code.

### Phase d — migration and lf1 demo

- d.1 Rewrite `step_distance_lemma`'s discharge as a structured proof per the worked example above. Verify three trust dependencies surface in `--report-trust`.
- d.2 Document the per-step trust → mechanical-discharge promotion path: replacing a step's `by trust(...)` with `by z3(...)` or `by dreal(...)` (when dReal lands) doesn't change the proof's structure; only that step's witness shape flips.

## Grammar changes — no new keywords

The structured proof body reuses `rule`, `:-`, `-:`, `by`, `using`, `end` — all already in the language. Extend `proof_body` to accept a sequence of inner rule declarations followed by an optional trailing `using ... by ...` clause. Inner rules use the proposal-032 single-arrow form (one of `:-`, `-:`, or no arrow):

```js
// Existing: proof X by <tactic> end
// New: proof X (rule h: ... by ...)+ [using ... by ...] end

proof_body: $ => choice(
  // single-tactic form (existing)
  seq(
    optional(seq('using', $.name_list)),
    'by',
    field('tactic', $.proof_strategy),
  ),
  // structured form (new): inner rules + trailing discharge
  seq(
    repeat1($.inner_rule_step),
    optional($.proof_concluding_clause),
  ),
),

// Same shape as a top-level rule_declaration (proposal 032 single-arrow form)
// plus a mandatory `by`. Exactly one of `:-`, `-:`, or neither.
inner_rule_step: $ => seq(
  'rule',
  optional(seq(field('label', $.name), ':')),
  choice(
    seq(field('heads', $.rule_heads), ':-', field('body', $.rule_body)),
    seq(field('body', $.rule_body), '-:', field('heads', $.rule_heads)),
    field('heads', $.rule_heads),    // bare-head step: claim with no premises
  ),
  optional($.meta_block),
  optional(seq('using', $.name_list)),
  'by',
  field('tactic', $.proof_strategy),
),

// Trailing discharge of the enclosing lemma's head.
proof_concluding_clause: $ => seq(
  optional(seq('using', $.name_list)),
  'by',
  field('tactic', $.proof_strategy),
),
```

Disambiguation: the parser distinguishes structured from single-tactic by lookahead. `proof X by ...` is single-tactic; `proof X rule ...` is structured.

The grammar gains exactly **zero new keywords**. `inner_rule_step` is structurally identical to a top-level `rule_declaration` (single-arrow form, multi-head allowed via `,` per proposal 032) plus a mandatory tactic — same `:-` / `-:` / bare-head, `by`, `using`, `meta_block` clauses. The loader recognises the inner-rule context (it's inside a `proof X` block, not at top level) and treats each one as a step in the structured discharge.

### Optional colocation: trailing `proof` block on a rule

When a rule's only role is to be proved (no external `using`-citers), the split between `rule X: H :- B` and `proof X ... end` is ceremony. Optionally extend `rule_declaration` to accept a trailing `proof ... end` block:

```js
rule_declaration: $ => seq(
  /* existing fields, single-arrow per proposal 032 */,
  optional($.meta_block),
  // new: optional trailing proof block, no name (implicitly proves
  // the enclosing rule).
  optional(seq(
    'proof',
    $.proof_body,
    'end',
  )),
),
```

`rule X: H :- B proof <body> end` (or its forward equivalent `rule X: B -: H proof <body> end`) desugars at load time into:
1. The rule X declaration (without the trailing proof).
2. A separate `proof X` block with the same body.

Both go through the existing convert + load paths. Reuses `proof` and `end` keywords; no new ones. The user-visible payoff is colocation; the kernel-level effect is identical to writing them separately.

### Choosing between forms

| Form | When to use |
|---|---|
| `rule X: H :- B` + separate `proof X …` | X is reusable; the rule statement deserves emphasis. |
| `rule X: H :- B proof <body> end` (trailing) | X is internal; only the proof discharges it. |
| `proof X by <tactic> end` (single-tactic) | The rule's discharge is one solver invocation. |
| `proof X rule h1: … by … rule hn: … by … using h1..hn by … end` (structured) | The discharge needs multi-step composition. |

All produce the same registry membership and witness shape; the choice is documentary.

## Out of scope

- A full tactic-language (Framing C). Structured proofs are a step-list with per-step tactic dispatch — not a programmable interactive prover.
- Proof reconstruction / decision-procedure integration (e.g. structured-to-Coq export). Witness round-trip beyond anthill is a separate concern.
- Implicit step-claim vars: structured proofs require each step to name its claim (`rule h: <head>`). Anonymous steps + automatic claim derivation (Mizar-style "thus" / "qed") are post-v0.
- Step-level `[simp]` / `[hint]` attributes. Steps are local to the proof; ambient-on-other-proofs semantics doesn't apply. If a step's claim is reusable, promote it to a top-level rule (Framing A).

## Open questions

1. **Hypothesis substitution for steps with new free vars.** When step `h_i` introduces a new free var `?x` (existentially quantified), how does it become available to `h_{i+1}`? For SLD-driven steps this is SLD's normal scoping; for SMT-driven steps the free var has to be Skolemised somehow. v0 punts: vars introduced by existential SMT-discharge are post-emission Skolemised by Z3's get-model and asserted as ground constants for downstream use. Hacky; revisit.

2. **Backward step ordering.** Should the user be able to write a step that depends on a *later* step (forward reference)? Coq's `assert` allows it via `[goal]` postponement. Anthill v0: no. Steps are strictly sequential.

3. **Step claim equality vs. SLD rewriting.** If `rule h_i: foo(?x) = bar(?x)` is asserted via z3-discharge, does SLD treat it as a rewrite for subsequent steps? Probably not without explicit `[simp]` tag — consistent with WI-139's default.

4. **Concluding step's relation to the lemma's head.** The lemma has a single head (its conclusion, per proposal 032); the trailing `using ... by ...` discharges that head under accumulated hypotheses. If the lemma's head is `⊥` (denial / violation-shape rule), the discharge target is `false` and the encoding becomes "body + step claims are unsat" — same shape as a top-level denial proof. The discharge clause is still required; there is no implicit "body-unsat" verdict.

5. **Structured proofs as MetaCompose vs. separate witness type.** The proposal reuses MetaCompose with `tactic_name: "structured"`. Alternative: a fresh `Structured { steps: Vec<StepWitness> }` constructor. The MetaCompose path is cheaper (no schema change), but loses some type-level distinction. v0 picks MetaCompose for compatibility with existing β.3 / sidecar / aggregation.

6. **Multi-head inner steps.** Per proposal 032, a rule may have multiple heads (conjunctive sugar). An inner step `rule h_i: A, B by <tactic>` is admissible: the step concludes both `A` and `B` (subject to the tactic discharging the conjunction). Subsequent steps see both `A` and `B` as hypotheses. Open question: should we exposed per-conjunct citation (`using h_i#1` for `A` only)? Recommendation: not initially — `using h_i` cites the group; cite-resolution gives the consumer both conjuncts, the solver picks what it needs.

## Summary

Structured proofs land as a single new tactic (`by structured` is implicit when a proof body has inner `rule` clauses) that decomposes a lemma's discharge into ordered named steps, each with its own discharge tactic and witness. Inner steps follow the proposal-032 single-arrow rule grammar (`:-`, `-:`, or bare-head) — same syntax authors already use for top-level rules. The kernel verifies each step using the proposal-030 witness machinery; the structural composition is `MetaCompose { tactic_name: "structured" }`. β.3, β.6, sidecar persistence, γ cite resolution all compose without modification.

The drone example is the natural first consumer: `step_distance_lemma`'s seven-step derivation (1 trust + 1 trust-cited + several mechanical) becomes expressible end-to-end. The trust surface decomposes from "one opaque lemma" to "scalar norm homogeneity (trust) + velocity envelope (trust)" — finer-grained, audit-friendly. Future mechanical-discharge backends (dReal, KeYmaera X) plug in per-step without touching the proof's structure.

Cost is bounded: phase a (grammar + IR), phase b (dispatch), phase d (lf1 migration). Phase c (check) is essentially free — β.3's existing recursion handles structured proofs as a special case of MetaCompose. Estimate: 1-2 weeks of focused work.

The architectural payoff is significant: structured proofs are the missing "user-supplied chain when full automation isn't available" link in proposal-030's stance-2 architecture. Without them, the only fallback for partial-mechanization is `by trust(...)` at the lemma level — coarse and audit-unfriendly. With them, partial mechanization is per-step; each unverified step is named, scoped, and replaceable.
