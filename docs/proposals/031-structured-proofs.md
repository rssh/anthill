# Proposal 031: Structured Proofs

**Status:** Draft
**Depends on:** [030-theorem-registry](030-theorem-registry.md) (witness machinery, MetaCompose, β.3 + β.6 checking, γ cite resolution)
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

A `proof X` block can contain multiple `step h_i: <claim>` clauses, each with its own `by <tactic>` discharge. The kernel verifies each step under the accumulated hypotheses (h_1, …, h_{i-1}). The lemma's `-:` conclusion is discharged at the end (`conclude`).

**Where this is right:** decompositions where intermediate claims are *internal* to one proof — not citable elsewhere, just part of this lemma's chain. The trust report shows the whole proof at the lemma level; per-step witnesses are inside the MetaCompose.

**Where this is wrong:** if intermediate claims ARE reusable (other proofs would cite them), they should be top-level lemmas via Framing A. Structured proofs are not a replacement for proper rule decomposition; they're a complement.

### Framing C — fully-tactic-language (Coq / Lean style)

Proof blocks become a small imperative language with `intro`, `apply`, `rewrite`, `assert`, `clear`, `by`, etc. A complete proof tactic engine.

**Where this would help:** general-purpose proof construction, theorem prover ergonomics.

**Where this would hurt:** anthill's stance-2 commitment is "small kernel, untrusted tactics". A full tactic language is a parallel implementation of a proof assistant — substantial work, large kernel surface, not aligned with the project's scope.

This proposal commits to **Framing B**. The structured-proof tactic is a single new dispatch path; intermediate steps reuse the existing witness types and check mechanisms; nothing in the kernel changes.

## Design

### Source syntax

A structured proof body has two shapes:

```anthill
proof X
  step h1: <claim>
    [using <cite-list>]
    by <tactic>
  step h2: <claim>
    by <tactic>
  -- ...
  conclude
    [using <cite-list>]
    by <tactic>
end
```

Each `step` declares a named intermediate claim (`h_i: <term>`) and a tactic for discharging it. The tactic can be any of the existing kinds (`z3`, `derivation`, `trust`, induction, ranking) or new ones added later.

`conclude` discharges the lemma's own `-:` conclusion under all the accumulated `step` hypotheses. The cite-list and tactic on `conclude` apply to the final discharge.

### Discharge semantics

For each step `h_i: claim_i by tactic_i`:

1. Build the discharge context: the target rule's body, plus all previously-asserted step claims `h_1`, …, `h_{i-1}` as hypotheses.
2. Run `tactic_i` to produce a witness `w_i` for `claim_i` under that context. The witness is whatever shape `tactic_i` produces — `SmtDischarge` for z3, `SldDerivation` for derivation, `TrustedAxiom` for trust, etc.
3. Each step's witness is a real witness in the kernel-checked sense. β's check pass replays it.

For `conclude by tactic`:

1. Build the same context plus all step hypotheses.
2. Discharge the rule's `-:` conclusion under that context.
3. Produce the final witness.

The structured-proof tactic packages all witnesses into a `MetaCompose`:

```rust
ProofWitness::MetaCompose {
  tactic_name: "structured".into(),
  sub: vec![w_1, w_2, ..., w_n, w_conclude],
}
```

β.3's MetaCompose checker recurses on each sub-witness. β.6's trust aggregation propagates trust flags through the whole tree. γ.1's cite gate applies per-step (cited rules in `using` lists must be Discharged).

### Hypothesis splicing — the load-bearing mechanism

The previous step's claim `h_{i-1}` becomes a hypothesis for `h_i`'s discharge. Concretely:

For an SMT-discharged step `h_i: lte(?x, ?y) by z3(logic: "LRA")`:
- The consumer's preamble normally has the rule's body as `(assert ...)` clauses.
- For a structured step, ALSO add `(assert <h_1's claim>)`, `(assert <h_2's claim>)`, …, `(assert <h_{i-1}'s claim>)` to the preamble.
- These are ground assertions in the consumer's vars (the step's claim was already discharged in a previous sub-call; its truth is now an axiom for this step).

For an SLD-discharged step `h_i: ...claim... by sld`:
- The resolver runs against the KB extended with the step claims as facts.
- This may need a transient-fact mechanism (assert the step claims into a session-scoped fact set, retract them after the proof completes). Implementation detail.

For a `trust`-discharged step:
- No SMT or SLD invocation; the step's claim is asserted via TrustedAxiom witness.
- Subsequent steps can use the claim as if it had been mechanically discharged. The trust flag propagates.

### Free variables and binding scope

A step's claim may contain free variables not bound by previous steps. Two cases:

**Existentially-quantified step**: `step h: ∃ ?x. P(?x) by sld` — the resolver finds a witness for `?x` and binds it for subsequent steps. This is SLD's natural mode.

**Universally-quantified step**: `step h: ∀ ?x. P(?x) ⇒ Q(?x) by z3(...)` — Z3 verifies the universal, the claim is asserted as a forall axiom for subsequent steps.

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

The current setup in `safety_common.anthill` is split:

```anthill
rule step_distance_lemma(?w)
  :- distance_at_step(?k, ?d_prev),
     ?k_next = ?k + 1,
     distance_at_step(?k_next, ?d_next),
     ?w = ?d_next - ?d_prev
  -: lte(abs(?d_next - ?d_prev), ?delta)

proof step_distance_lemma
  by trust(reason: "Composition of triangle_inequality + velocity_envelope + real_pose_at transition; mechanical discharge blocked by three smt-gen limits — see comment.")
end
```

becomes a single `lemma` block colocating claim + proof:

```anthill
lemma step_distance_lemma
  :- distance_at_step(?k, ?d_prev),
     ?k_next = ?k + 1,
     distance_at_step(?k_next, ?d_next),
     ?w = ?d_next - ?d_prev
  -: lte(abs(?d_next - ?d_prev), ?delta)

  -- Step 1: distance_at_step is the norm of position difference.
  -- Definitional unfolding via SLD against position_distance rule.
  step h1: distance_at_step(?k, ?d_prev) ⇒ ?d_prev = ‖p_L(k) − p_F(k)‖
    by sld

  -- Step 2: transition rule + algebraic substitution.
  step h2: p_L(k+1) − p_F(k+1) = (p_L(k) − p_F(k)) + (v_L(k) − v_F(k)) · T_c
    by z3(logic: "QF_LRA")

  -- Step 3: reverse triangle inequality. The geometric leaf.
  step h3: |‖p_L(k+1) − p_F(k+1)‖ − ‖p_L(k) − p_F(k)‖| ≤ ‖(v_L − v_F) · T_c‖
    using triangle_inequality
    by z3(logic: "NRA")

  -- Step 4: scalar homogeneity of norm.
  step h4: ‖(v_L − v_F) · T_c‖ = T_c · ‖v_L − v_F‖
    by trust(reason: "Scalar homogeneity of Euclidean norm")

  -- Step 5: triangle on velocity diff + envelope.
  step h5: T_c · ‖v_L − v_F‖ ≤ T_c · (‖v_L‖ + ‖v_F‖)
    using triangle_inequality
    by z3(logic: "QF_NRA")

  -- Step 6: velocity envelope (the genuinely physical claim).
  step h6: T_c · (‖v_L‖ + ‖v_F‖) ≤ T_c · (v_L_max + v_F_max)
    using velocity_envelope
    by z3(logic: "QF_LRA")

  -- Step 7: collapse to delta.
  step h7: T_c · (v_L_max + v_F_max) = ?delta
    by sld

  -- Conclude: chain h1..h7 yields the lemma's `-:` conclusion.
  conclude
    by z3(logic: "QF_LRA")
end
```

The claim (lines 2-6) and proof (lines 8-onwards) sit in one block. The lemma is still citable from elsewhere — `using step_distance_lemma` resolves through the registry exactly as it would with the split form — but the source-level reading is unified: the claim's free vars (`?k`, `?d_prev`, `?d_next`, `?delta`) flow into the `step` claims directly without any name-resolution gymnastics.

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
- b.4 Concluding step: same as a regular step but discharges the rule's `-:` conclusion under all accumulated hypotheses.
- b.5 Witness assembly: wrap all sub-witnesses (one per step + concluding step) in `MetaCompose { tactic_name: "structured", sub: ... }`.

### Phase c — check

- c.1 β.3's MetaCompose check already recurses on each sub-witness. Structured proofs require no additional check logic — they reuse the existing per-witness verifiers.
- c.2 Sidecar persistence (WI-124) already serializes nested MetaCompose witnesses recursively. No new code.

### Phase d — migration and lf1 demo

- d.1 Rewrite `step_distance_lemma`'s discharge as a structured proof per the worked example above. Verify three trust dependencies surface in `--report-trust`.
- d.2 Document the per-step trust → mechanical-discharge promotion path: replacing a step's `by trust(...)` with `by z3(...)` or `by dreal(...)` (when dReal lands) doesn't change the proof's structure; only that step's witness shape flips.

## Grammar changes

Add to `proof_body`:

```js
structured_proof_body: $ => seq(
  repeat1($.proof_step),
  $.proof_conclude,
),

proof_step: $ => seq(
  'step',
  field('name', $.name),
  ':',
  field('claim', $._term),
  optional(seq('using', $.name_list)),
  optional(seq('by', field('tactic', $.proof_strategy))),
),

proof_conclude: $ => seq(
  'conclude',
  optional(seq('using', $.name_list)),
  optional(seq('by', field('tactic', $.proof_strategy))),
),
```

Two new keywords: `step` and `conclude`. Both reserved within proof-body context only.

### `lemma` block — colocated rule + structured proof

For lemmas whose only role is to be proved (no external `using`-citers), the split between `rule` declaration and `proof` block is ceremony. Add a new top-level `lemma` declaration that combines both:

```js
lemma_declaration: $ => seq(
  'lemma',
  field('name', $.name),
  optional(seq(':-', field('body', $.rule_body))),
  optional(seq('-:', field('conclusion', $.rule_body))),
  optional($.meta_block),
  $.structured_proof_body,
  'end',
),
```

The loader desugars `lemma X :- … -: … [meta] step … conclude … end` into two declarations:

1. `rule X :- … -: … [meta]` — the rule (with whatever attributes the lemma carries).
2. `proof X` with `ProofBody::Structured(steps, conclude)` — the discharge.

Both go through the existing convert + load paths. The rule remains citable via `using X` from any consumer; the witness machinery is unchanged. The user-visible payoff is *colocation*: the lemma's claim and discharge live in one source block, reading top-to-bottom as "here's what we're proving, here's how."

The Coq parallel:
```
Theorem step_distance_lemma : forall k d_prev d_next, …
  -> abs (d_next - d_prev) <= delta.
Proof.
  intros.
  apply triangle_inequality.
  …
Qed.
```

Anthill's `lemma` is the same idea — combined claim + proof, parsed-and-loaded as if the user wrote both pieces separately.

Two new keywords: `lemma` (top-level) and `end` (already a keyword closing many block constructs). `step` and `conclude` remain proof-body-context keywords.

### Choosing between forms

| Form | When to use |
|---|---|
| `rule X …` + `proof X …` | X is reusable elsewhere; the rule statement deserves emphasis (a top-level theorem). |
| `lemma X …` (combined) | X is internal; only the proof discharges it; no external citers. |

Both produce the same registry membership and witness shape; the choice is documentary.

## Out of scope

- A full tactic-language (Framing C). Structured proofs are a step-list with per-step tactic dispatch — not a programmable interactive prover.
- Proof reconstruction / decision-procedure integration (e.g. structured-to-Coq export). Witness round-trip beyond anthill is a separate concern.
- Implicit step-claim vars: structured proofs require each step to name its claim (`h: <claim>`). Anonymous steps + automatic claim derivation (Mizar-style "thus" / "qed") are post-v0.
- Step-level `[simp]` / `[hint]` attributes. Steps are local to the proof; ambient-on-other-proofs semantics doesn't apply. If a step's claim is reusable, promote it to a top-level rule (Framing A).

## Open questions

1. **Hypothesis substitution for steps with new free vars.** When step `h_i` introduces a new free var `?x` (existentially quantified), how does it become available to `h_{i+1}`? For SLD-driven steps this is SLD's normal scoping; for SMT-driven steps the free var has to be Skolemised somehow. v0 punts: vars introduced by existential SMT-discharge are post-emission Skolemised by Z3's get-model and asserted as ground constants for downstream use. Hacky; revisit.

2. **Backward step ordering.** Should the user be able to write a step that depends on a *later* step (forward reference)? Coq's `assert` allows it via `[goal]` postponement. Anthill v0: no. Steps are strictly sequential.

3. **Step claim equality vs. SLD rewriting.** If `h_i: foo(?x) = bar(?x)` is asserted via z3-discharge, does SLD treat it as a rewrite for subsequent steps? Probably not without explicit `[simp]` tag — consistent with WI-139's default.

4. **Concluding step's relation to the lemma's `-:`.** The lemma has its own `-:` conclusion; `conclude` discharges THAT under accumulated hypotheses. If the lemma has no `-:` (violation-shape rule), `conclude` has nothing to discharge — error at parse, or implicit "body-unsat" verdict?

5. **Structured proofs as MetaCompose vs. separate witness type.** The proposal reuses MetaCompose with `tactic_name: "structured"`. Alternative: a fresh `Structured { steps: Vec<StepWitness> }` constructor. The MetaCompose path is cheaper (no schema change), but loses some type-level distinction. v0 picks MetaCompose for compatibility with existing β.3 / sidecar / aggregation.

## Summary

Structured proofs land as a single new tactic (`by structured` is implicit when a proof body has `step` clauses) that decomposes a lemma's discharge into ordered named steps, each with its own discharge tactic and witness. The kernel verifies each step using the proposal-030 witness machinery; the structural composition is `MetaCompose { tactic_name: "structured" }`. β.3, β.6, sidecar persistence, γ cite resolution all compose without modification.

The drone example is the natural first consumer: `step_distance_lemma`'s seven-step derivation (1 trust + 1 trust-cited + several mechanical) becomes expressible end-to-end. The trust surface decomposes from "one opaque lemma" to "scalar norm homogeneity (trust) + velocity envelope (trust)" — finer-grained, audit-friendly. Future mechanical-discharge backends (dReal, KeYmaera X) plug in per-step without touching the proof's structure.

Cost is bounded: phase a (grammar + IR), phase b (dispatch), phase d (lf1 migration). Phase c (check) is essentially free — β.3's existing recursion handles structured proofs as a special case of MetaCompose. Estimate: 1-2 weeks of focused work.

The architectural payoff is significant: structured proofs are the missing "user-supplied chain when full automation isn't available" link in proposal-030's stance-2 architecture. Without them, the only fallback for partial-mechanization is `by trust(...)` at the lemma level — coarse and audit-unfriendly. With them, partial mechanization is per-step; each unverified step is named, scoped, and replaceable.
