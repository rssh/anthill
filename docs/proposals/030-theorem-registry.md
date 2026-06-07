# Proposal 030: Certified ProofRecord and Translation Policy

**Status:** Implemented (α + β.1/β.3–β.7 + γ + WI-124 sidecar persistence + δ.1–δ.3 + ε.1/ε CLI flag set landed). β.2 (SldDerivation real replay) and δ.4/δ.5 (smt-gen call-site policy integration + logic-fragment selection) remain — see §Implementation status.
**Depends on:** [025-proof-constructs](025-proof-constructs.md), [025.1-z3-tactic-dsl](025.1-z3-tactic-dsl.md)
**Related:** [023-kb-guards](023-kb-guards.md), [029-rust-mapping-split](029-rust-mapping-split.md)
**Supersedes / consolidates:** in-session WI-C2 sketches (opaque-rule annotations, `relation` declarations, axiom-acceptance citation) — their content is replaced by phase δ's per-predicate translation policy plus the `ScopeAxiom` / `Specialization` witness machinery. WI-A (`using` clause), WI-B (`ProofConfig.assumptions`), WI-C1 (`-:` conclusion + lift) remain landed but get reframed: `using` becomes registry-mediated (phase γ), `assumptions` becomes the splicing mechanism for translated theorems, `lift_rule_to_implication_clause` becomes a pure translation function over registered ProofRecords.
**Affects:** `rustland/anthill-core/` (KB schema, parse IR, loader), `rustland/anthill-cli/` (prove driver, cache, check), `rustland/anthill-smt-gen/` (translation policy, certificate emission), `stdlib/anthill/realization/`, all backends

## Motivation

`docs/kernel-language.md` §1 states the architectural intent:

> *The kernel is deliberately small — analogous to the kernel of a proof assistant (Lean, Coq) that is small, trusted, and verifies proofs, while tactics (large, untrusted) find them.*

The implementation today does not match this intent in two specific ways. First, a successful `proof X by z3(...)` produces a CLI verdict but no checkable certificate; the `ProofRecord` lifecycle fact records that X was discharged, but not *what evidence* the discharge produced. Second, the recently-added `using <Y>` clause (WI-A) is a text-injection mechanism that is *not gated* on Y having actually been proved — it lifts Y's body+conclusion to a forall implication and splices it into X's preamble regardless of Y's proof status. Sound only if the user maintains the discipline of proving every cited rule first; in practice this collapses to *axiom acceptance*: the user writes the lemma, declares it cited, and the consumer's discharge proceeds as if the lemma were true.

This proposal closes both gaps. It does not introduce a parallel `Theorem` object — the kernel already has `Rule` (the declaration), and `ProofRecord` (the lifecycle marker for a proof attempt). What is missing is **proof evidence**: a typed witness that a tactic emits, that the kernel checks, and that the cite mechanism consults. Plus: a **translation policy** that fixes the SMT-vocabulary alignment problem at the kernel layer rather than via per-rule annotations.

## Three architectural stances

Before designing, name the choice the design makes.

### Stance 1 — Backend-internal proofs

A proof is whatever the discharging backend says it is. Z3's `(check-sat) → unsat` is the verdict; nothing more is recorded. Cross-proof composition is impossible at the language level — users either reorganize source so each invocation has every needed clause in scope, or accept that proofs don't compose. `using` exists as a UX shorthand but doesn't carry meaningful soundness semantics.

This is what most rule engines (Datalog, Soufflé, Prolog without lemma extensions) do.

### Stance 2 — Kernel-checked proofs, untrusted tactics

The kernel knows what a `Rule`'s claim is (mechanically projected from its body and `-:` conclusion). A successful proof of that claim produces a *witness* the kernel checks. Tactics propose; the kernel checks. Discharged ProofRecords are usable from other proofs by citation, with the cite gated on the witness having been kernel-checked. There is no parallel `Theorem` object — a "theorem" is just a rule whose ProofRecord is in `Discharged` state with a valid witness.

This is what proof assistants do, expressed via the existing kernel primitives instead of a new object.

### Stance 3 — Specification + multi-backend

Anthill is syntax with conventions; each backend interprets the source as it likes. There is no anthill-level proof. Composition happens at the source level rather than at the proof level.

This proposal commits to **stance 2**. The kernel reuses what it already has (Rule, ProofRecord) and adds only what's genuinely missing: the witness on the ProofRecord, and the translation policy that aligns vocabulary across proofs.

## Key insight: theorem = rule + discharged ProofRecord

There is no separate `Theorem` sort. The kernel has:

- **`Rule`** — declaration. After WI-C1, has body + optional `-:` conclusion. The rule's *theorem statement* is the mechanical projection `∀ free-vars(body ∪ conclusion). body ⇒ (and conclusion)` (positive form) or `∀ free-vars(body). ¬(and body)` (violation form). The projection is computed on demand from the rule's IR; nothing is stored.
- **`ProofRecord`** — lifecycle marker. Records which rule, which tactic, what status. Already in the KB after WI-A's loader changes.

What 030 adds is the certificate evidence and a state-hash on the ProofRecord, plus the translation policy. The "theorem registry" is just `ProofRecord` facts queryable like any other facts in the KB. Citing rule Y from proof X is "look up `ProofRecord(rule = Y)` and check its result/witness/state_hash before using Y's projected statement."

## Design

### Schema additions

Two extensions to existing schema, two genuinely new sorts.

#### Extend `ProofRecord` (in `stdlib/anthill/realization/realization.anthill`)

```anthill
entity ProofRecord(
  rule          : String,                         -- existing
  strategy      : Term,                           -- existing
  body          : Term,                           -- existing
  result        : ObligationStatus,               -- existing
  dependencies  : List[T = String],               -- existing
  using         : List[T = String],               -- existing (WI-A)

  -- new for 030:
  witness       : ProofWitness,                   -- the certificate
  state_hash    : String                          -- hash of the dep slice
)
```

The `witness` field carries the certificate evidence; the `state_hash` is the hash of every kb-state slice the discharge depended on (every visited rule's canonical IR + every visited fact's content). On rule-IR drift, the hash changes, the cached witness invalidates, the cite-side `using` fails until re-discharge.

`ObligationStatus` may also gain `Unknown(reason: String)` for honest "Z3 timed out" reporting; the existing `Pending` / `Discharged(...)` / `Failed(...)` covers most lifecycle states.

#### Add `ProofWitness` (genuinely new, in `stdlib/anthill/realization/witness.anthill`)

```anthill
namespace anthill.realization.witness

  -- The proof certificate: structured evidence per tactic kind.
  -- Distinct constructors so the kernel can route checking by case.
  sort ProofWitness

    -- SMT discharge — the certificate is the SMT-LIB document the
    -- backend ran (referenced by content hash so we don't bloat
    -- ProofRecord facts) plus the verdict and any unsat-core
    -- annotation. The kernel re-runs the document on demand.
    entity SmtDischarge(
      backend        : String,             -- "z3" | "cvc5" | future
      logic          : String,             -- e.g. "QF_LRA"
      document_hash  : String,             -- content hash; the actual
                                           -- document is in the prove cache
      verdict        : SmtVerdict,
      core           : Option[T = String]  -- unsat-core lines, if requested
    )

    -- SLD derivation — the resolution tree. Replayable. Stored as
    -- a hash with full content in the cache; cheap to verify by
    -- replaying step-by-step against the current KB.
    entity SldDerivation(tree_hash: String)

    -- Meta-tactic composition — the tactic dispatched N sub-queries
    -- and AND-combined their verdicts. The certificate is the list
    -- of sub-witnesses (each itself a ProofWitness).
    entity MetaCompose(tactic_name: String, sub: List[T = ProofWitness])

    -- Definitional witness for kernel-derived lemmas: lemmas that
    -- are true by virtue of a scope's declared structure. The
    -- `aspect` discriminates which structural feature the witness
    -- rests on:
    --   - "requires.<SE-flat>" — the lemma is one of the scope's
    --     `requires` clauses, identified by the flattened Sort-Expr.
    --   - "induction" — the lemma is the auto-generated induction
    --     principle for an inductive sort.
    --   - (future aspects can extend this without schema changes.)
    -- The kernel re-reads the cited declaration and dispatches per
    -- aspect to verify. Not in the trust base.
    entity ScopeAxiom(scope_kind: String, scope_qn: String, aspect: String)

    -- Use-site specialization: combine a parametric ProofRecord
    -- with concrete `provides` discharges to obtain a specialized
    -- theorem at the given sort substitution. The kernel checks
    -- structurally — substitution well-formed, all parametric
    -- requires obligations covered by the supplied instance proofs.
    entity Specialization(
      parametric    : String,                       -- QN of parametric ProofRecord
      substitution  : List[T = SortBinding],        -- T_i ↦ ConcreteSort
      instances     : List[T = String]              -- ProofRecord QNs covering the parametric requires
    )

    -- User-asserted axiom — explicit trust, no kernel check.
    -- Permitted but flagged in any proof tree containing it.
    entity TrustedAxiom(reason: String)
  end

  entity SortBinding(abstract_param: String, concrete_sort: String)

  sort SmtVerdict
    entity Unsat
    entity Sat(model_hash: String)
    entity Unknown(reason: String)
  end
end
```

Notes:

- Witnesses reference cache content by hash, not by inline value. `document_hash`, `tree_hash`, `model_hash` are content keys into the proof cache. This keeps `ProofRecord` facts compact (small enough to live in source) and reuses the cache infrastructure from proposal 025.1.
- `MetaCompose` is recursive (sub-witnesses are themselves `ProofWitness`). Anthill's realization layer already supports recursive entity definitions (`List`, `Tree`); `ProofWitness` follows the same pattern.
- `TrustedAxiom` is the *explicit* opt-in for axiom acceptance. The current `using`'s silent axiomatic content goes away; users who genuinely want to assert without proof must say so in source via this constructor.

#### Add `TranslationPolicy` (new, in `stdlib/anthill/realization/policy.anthill`)

```anthill
namespace anthill.realization.policy

  -- Per-(predicate, backend) policy controlling how the predicate
  -- is lowered when emitted. Project-wide, set once per predicate;
  -- applies in every proof.
  entity TranslationPolicy(
    predicate : String,                  -- predicate qualified name
    backend   : String,                  -- "smt-z3", "smt-cvc5", "lean", ...
    policy    : PredicatePolicy
  )

  sort PredicatePolicy
    -- Inline the body at every call site; predicate symbol disappears.
    -- Default for closed-body, non-recursive predicates with no
    -- cite-side use.
    entity Inline

    -- Declare via `(define-fun NAME (typed-args) Bool body)`. Symbol
    -- preserved; calls become symbol references; body is interpreted
    -- on demand by the solver.
    entity DefineFun

    -- Declare via `(declare-fun NAME (typed-args) Bool)` — uninterpreted.
    -- Body is *not* translated. Meaning enters via separate axioms or
    -- TrustedAxiom witnesses. Used for predicates with no useful body
    -- (specification placeholders, hybrid-systems claims).
    entity DeclareFun

    -- Combination of DefineFun's symbol-preservation with explicit
    -- forall-asserted equivalence: emits `(declare-fun NAME …)` plus
    -- `(assert (forall (args) (= (NAME args) body)))`. Useful for
    -- recursive predicates that don't fit `define-fun-rec` cleanly.
    entity LiftedAxiom
  end
end
```

The policy is a fact, not a declaration on the rule. This intentionally separates *what a predicate is* (the rule) from *how a backend translates it* (the policy). Override channels (project-wide default, per-namespace, per-predicate annotation) all reduce to writing `TranslationPolicy` facts during loading.

### Tactic contract

Every tactic, when invoked from `proof X by <tactic>(...)`, returns one of:

- `Ok(witness: ProofWitness)` — success. The witness must be a structurally-valid `ProofWitness` term. The tactic does not write to the KB; it returns the witness.
- `Err(reason)` — failure. No record updated. Verdict reports to the user.

Registration is the kernel's responsibility:

1. Compute the rule's projected statement (forall implication).
2. Compute the state hash from visited rules / facts.
3. Run `kernel_check(witness, statement, state)` per witness constructor.
4. If checked, write `ProofRecord` (or update an existing one) with `result = Discharged`, `witness = <witness>`, `state_hash = <hash>`.
5. If check fails, registration is rejected. The user gets an explicit "verification failed" error.

The current `dispatch_z3`, `dispatch_ranking`, `dispatch_induction`, `dispatch_derivation` paths in `prove.rs` get rewrapped to return `Result<ProofWitness, Error>` instead of `Verdict`. The CLI layer above wraps the registration outcome into a print-line for the user.

### Certificate checking semantics

The kernel doesn't *trust* witnesses — it *checks* them, per constructor.

#### `SmtDischarge`

The kernel fetches the document from the cache by `document_hash`, re-runs the named backend, and checks that the verdict matches what's recorded. If mismatched, registration fails.

This is "audit by replay." The SMT solver itself is in the trust base — a faulty Z3 returning `unsat` for a sat document is undetected. Documented as a trust boundary; future work could integrate Z3's `(get-proof)` for solver-independent verification.

For v0, audit-by-replay is sufficient: the kernel ensures the recorded document matches what the rule generates today, so editing the rule changes the document, changes the document hash, and forces re-checking.

#### `SldDerivation`

The kernel fetches the resolution tree from the cache by `tree_hash` and replays it against the current KB. Each step must unify against a rule head whose body's premises were all derived earlier in the tree. A step that doesn't unify, references a retracted rule, or skips a goal fails the check.

Replay is mechanical and fast. SLD checking adds the SLD resolver to the trust base in a different sense than SMT: the resolver's behavior is anthill-internal, so its correctness is part of anthill's correctness story (vs Z3 which is external).

#### `MetaCompose`

Each sub-witness is checked recursively. The composition is checked structurally: the meta-tactic's name (`induction`, `ranking`, `bmc`, …) corresponds to a registered meta-tactic schema; the sub-witnesses must satisfy the schema's contract. For example:

- `induction(over: Int64)` requires a base sub-proof (proving the claim at `0`) and a step sub-proof (proving `P(n) ⇒ P(n+1)`); the kernel verifies the count and shape.
- `ranking(boundedness, decrease)` requires a boundedness sub-proof (proving `R(state) ≥ 0`) and a strict-decrease sub-proof (proving `R(state') < R(state)` on the relevant transitions).

The schemas live as KB facts — `MetaTacticContract(name, ...)` — so they can be extended without changing the kernel. The existing `induction(...)` and `ranking(...)` Z3 dispatches in `prove.rs` get re-shaped to emit `MetaCompose` witnesses with their sub-discharges, instead of flat `SmtDischarge` over a synthetic combined document.

#### `ScopeAxiom`

The witness names a scope (sort or operation) and asserts the lemma is true by virtue of that scope's declaration containing a particular `requires` clause. The kernel checks by re-reading the declaration in the current KB and verifying:

- The named scope exists.
- The scope's `requires` clauses include the Sort-Expr matching the lemma's identity (the `<S-qn>.requires.<SE-flat>` form).
- The Sort-Expr's defining sort/spec is loaded and its laws are accessible.

The proof is *constituted by* the source declaration. If the user removes the `requires` clause or edits the Sort-Expr, the witness fails to check on next access and the ProofRecord invalidates. This is not a trust escape hatch — the kernel verifies the structural fact that the declaration says what it says. (Compare `define-fun` in SMT-LIB: the function's meaning is constituted by its body; nothing else needs to be proved.)

`ScopeAxiom` is **not in the trust base**: the verifier doesn't take anyone's word for it; the source either contains the clause or it doesn't.

#### `Specialization`

The witness composes a parametric ProofRecord with a list of concrete instance ProofRecords plus a substitution map. The kernel checks structurally:

- The named parametric ProofRecord exists and is in `Discharged` state with valid state-hash.
- The substitution maps each abstract sort parameter named in the parametric's `parametric_context` to a concrete sort.
- For each abstract `requires` in the parametric's context, the supplied instance ProofRecord QN is resolvable, in `Discharged` state, with a statement that matches the abstract `requires`-spec instantiated at the substituted sort.
- The substitution is well-formed (no abstract parameter is mapped twice; no concrete sort references abstract parameters).

When all checks pass, the specialization yields a *derived* statement: the parametric's projected statement under the substitution. The kernel does not separately discharge anything — the soundness comes from (a) the parametric ProofRecord being checked already, and (b) the instance proofs covering exactly the parametric's open obligations.

`Specialization` is **not in the trust base** either: it's a structural composition the kernel verifies by definition.

#### `TrustedAxiom`

The kernel records the axiom and propagates a "trusted" flag through any ProofRecord whose witness tree contains a TrustedAxiom. The CLI surfaces the flag in verdict output ("X depends on trusted axiom Y"). Caches treat the trust flag as part of the cache key (so removing the trusted axiom invalidates downstream theorems).

### Scope of meta-tactic sub-witnesses

A meta-tactic like `induction` produces a `MetaCompose` whose sub-witnesses each carry their own hypotheses (e.g. the inductive hypothesis for the step sub-proof). Where do those hypotheses live? Two architectural framings name the choice:

#### Framing A — sub-witness-local hypotheses (v0)

Hypotheses introduced by a meta-tactic are **local to the relevant sub-witness's discharge context**. They do not enter the kernel registry.

- For an `SmtDischarge` sub-witness, the hypothesis appears as an `(assert ...)` clause inside the sub-witness's SMT-LIB document.
- For an `SldDerivation` sub-witness, the hypothesis appears as a temporary entry on the SLD assumption stack (per WI-108's existing scoping).
- The hypothesis is implicit in the document or tree the kernel re-checks; nothing additional is stored.

The kernel checks `MetaCompose` witnesses *structurally*: the meta-tactic's contract specifies the hypothesis shape ("the step sub-witness's document must contain an assertion matching the IH shape `∀ ?n. P(?n) ⇒ P(succ(?n))`"); the kernel verifies that shape is present in the sub-witness's payload. The kernel does not register the hypothesis as a citable theorem.

This is the *atomic-step* picture: from the kernel's perspective, the meta-tactic delivers a universal claim via a verifiable structural decomposition; the work that needs the IH happens one black-box solver invocation away. Big-proof composition (cross-rule citation through the registry) is for proven theorems; small-proof internals (IH inside an inductive step) stay inside the solver. This matches how working proof assistants treat atomic tactics — Lean's `induction` produces a term whose body has the IH bound; the kernel doesn't separately track IH; the term either type-checks or doesn't.

**Why local-only**: temporary kernel facts with lifecycle (born when a meta-tactic enters, expire when it exits) are error-prone and require scope tracking the v0 kernel does not need. In practice, induction-style meta-tactics work well with hypotheses bundled into a single sub-witness's discharge — Z3's quantifier instantiation for IH is reliable in the patterns we care about.

**Limitation of Framing A**: a step sub-proof cannot itself contain a `using` clause that references the IH as if it were a registered theorem. *Compound* inductive proofs — where the step needs both the IH and citations of other proven theorems via `using` — are not supported in v0. Authors must:
- Restructure the step so it is a single atomic solver discharge with all hypotheses bundled, or
- Use a `TrustedAxiom` to bridge the IH-needing portion (with the trust flag surfacing the gap).

#### Framing B — scoped registry entries (v1, future)

For compound proofs, a future extension promotes meta-tactic-introduced hypotheses to **scoped temporary** registry entries. Lifecycle: born when the meta-tactic dispatches a sub-witness, expire when that sub-witness completes, never visible outside the meta-tactic's enclosing scope.

Implementation sketch (deferred from v0):
- `ProofRecord` gains an optional `scope: SubProofId` field. Top-level theorems have `scope = None`; transient ones carry a scope identifier.
- The registry's lookup respects scope: a `using` inside sub-proof `S` may resolve names to scope-`S` entries; outside `S`, those entries are invisible.
- Meta-tactic implementations declare which transient entries they introduce per sub-dispatch.
- Kernel garbage-collects scope-S entries when S's sub-witness completes.

This is real engineering — sub-proof identifier propagation, lifetime checking, registry scope rules — and worth doing when a compound use case actually demands it. Not part of stance-2's first cut; revisited in proposal 030.1 (or a successor) when needed.

#### v0 commits to Framing A

For everything 030 implements: meta-tactics are atomic from the registry's perspective. Their internal structural decomposition is recorded in the `MetaCompose` witness for kernel-checking purposes; the IH-style hypotheses live inside sub-witnesses' own contexts. Compound proofs are explicitly unsupported in v0 with an honest workaround (`TrustedAxiom` + visible trust flag); the architectural extension to support them lives behind Framing B and is captured in the open questions.

### Statement projection

The rule's "theorem statement" is computed on demand:

```
project(rule):
  if rule has -: conclusion:
    statement = forall free-vars(body ∪ conclusion).
                  (and body) ⇒ (and conclusion)
  else:
    statement = forall free-vars(body).
                  not (and body)
```

`free-vars(...)` returns variables paired with their inferred sorts. Type inference works locally on the rule: variables appearing as field-access roots are typed by the entity that has the named field; variables in arithmetic ops are typed by the operator's signature; variables in entity-destructure positions are typed by the destructured entity. Untyped variables (no constraint at all) default to the predicate's argument sort if available, else `Real` with a warning.

The projection is a pure function over the rule's IR. No cached or stored intermediate. The state hash captures any rule-IR change so cite-side stability is automatic.

### `requires` clauses as auto-registered lemmas

Anthill already has `requires <Sort-Expr>` as a clause inside `sort` declarations and on `operation`s. This proposal makes each `requires` clause an **auto-registered ProofRecord** at load time — no new syntax, no new keyword, just a richer kernel interpretation of what's already there.

#### Per-clause registration

For each `requires <SE>` clause inside scope `S` (where `S` is a sort or operation), the kernel registers a ProofRecord at load time with:

- **Name**: `<S-qn>.requires.<SE-flat>` — sort-expr-keyed flattening of the Sort-Expr, e.g. `anthill.algebra.A.requires.Eq_T` for `requires Eq[T]` inside sort `A`. Stable under reordering of `requires` clauses; unstable only when the user edits the Sort-Expr itself (and that's a substantive change that should invalidate the lemma).
- **Statement**: the conjunction of `SE`'s laws (pulled from `SE`'s defining sort/spec) instantiated at the clause's binding. For `requires Eq[T]` inside A with abstract param T, the statement is `∀ (a: T) (b: T). (eq a b) = (eq b a) ∧ (eq a a) ∧ ...` — Eq's laws under the abstract T.
- **Witness (parametric case)**: `ScopeAxiom(scope_kind: "sort" | "operation", scope_qn: <S-qn>, aspect: "requires.<SE-flat>")`. The kernel checks this witness by re-reading `S`'s declaration in the current KB and verifying the clause is present with the same Sort-Expr. The proof is *by definition*: the lemma holds because the source declaration says it does. Not in the trust base — `S`'s source IS the proof, mechanically checkable.
- **Witness (specialized case)**: `Specialization` composing the parametric ProofRecord with the concrete provides-discharge ProofRecords. Auto-generated when `provides A[T = X]` discharges and Int64's spec laws have their own ProofRecords.

A sort with three `requires` clauses produces three ProofRecords. There is no aggregate `Requires[A]` lemma — the conjunction is on demand at translation time, not stored.

#### Implicit citation from enclosing scope

Inside scope `S` (sort or operation), every rule's effective `using` set automatically includes all of `S`'s `requires`-clause ProofRecords, plus those of any enclosing scopes (transitively up the chain). The user does not write `using anthill.algebra.A.requires.Eq_T` for inside-A proofs — it's added by the kernel at cite-resolution time.

Explicit citation from outside `S` uses the standard `using <name>` syntax with the auto-registered QN: `using anthill.algebra.A.requires.Eq_T`.

#### Translation-time bundling

At the SMT-emission layer, the kernel may collapse N implicitly-cited `requires` ProofRecords into one `(assert (forall (...) (and law₁ law₂ ... law_n)))` for compactness, or emit each as a separate `(assert (forall ...))` for Z3 quantifier-handling reliability. The choice is per-backend and per-policy (phase δ). The source-level model is unaffected.

#### Why `ScopeAxiom` is not a trust escape hatch

`ScopeAxiom` looks like it could be abused: "any source declaration is automatically a 'proof'." In practice the witness is checked by the kernel against the actual declaration. It is a **definitional-witness** — the lemma's truth is *constituted by* the declaration's existence and shape, not asserted as a trust statement. If `S` is removed or its `requires` clause edited, the witness fails to check (the cited declaration no longer exists with that shape) and the ProofRecord invalidates. This is structurally the same as how a `define-fun` definition makes a function symbol's meaning constituted by its body; `ScopeAxiom` is the analogous "by definition" witness for spec requirements.

`TrustedAxiom` remains the user-facing opt-in for unproven axioms: things the user vouches for without evidence. The two are distinguishable in the proof tree and propagate trust differently.

### Auto-generated induction principles as registered theorems

Anthill auto-generates an induction principle for each inductive sort and supported primitive: enums (`enum Color { Red; Green; Blue }`), inductive ADTs (`sort List[T] { entity nil; entity cons(head: T, tail: List[T]) }`), and primitives with a well-founded ordering (`Int64.induction(?P, ?lo, ?hi)`, `BigInt.induction(?P)` already in the stdlib). These principles are first-class registered theorems under stance 2 — same `ScopeAxiom` mechanism as `requires` clauses, different aspect.

#### Per-sort registration

For each inductive/primitive sort `T`, the kernel registers a ProofRecord at load time with:

- **Name**: `<T-qn>.induction`. Single canonical principle per sort.
- **Statement**: the canonical induction principle for `T`'s inductive structure.
  - Enum: `∀ P. (and P(c₁) P(c₂) … P(c_n)) ⇒ ∀ x: T. P(x)`.
  - Inductive ADT: structural induction over constructors, with an IH per recursive arg.
  - Primitive `Int64`: well-founded `∀ P. (P(0) ∧ ∀ n. P(n) ⇒ P(n+1)) ⇒ ∀ k: Int64. P(k)` (or its variants for bounded ranges, BigInt, etc.).
- **Witness**: `ScopeAxiom(scope_kind: "sort", scope_qn: <T-qn>, aspect: "induction")`. The kernel checks by re-reading T's declaration, verifying T is inductively defined (or a primitive with declared well-foundedness), and confirming the cached principle's statement matches the canonical principle for T's current constructor list / measure. If the user adds/removes a constructor, the witness fails to check and the principle invalidates.
- **Parametric context**: for polymorphic sorts like `List[T]`, the principle is parametric over `T`. `parametric_context = [ParametricBinding(abstract_sort: "T", requires: [...])]` — including any `requires` of `T` from the sort's declaration.

Higher-order quantification (over the predicate `P`) lives at the kernel-statement level only. Translation to backends specializes `P` at the consumer's specific predicate before emission — see *meta-tactic dispatch* below — so the SMT solver never sees raw HO quantification.

#### Source of truth for the `induction(over: T)` meta-tactic

The `induction(...)` meta-tactic's contract is **derived from** T's auto-registered induction principle, not hardcoded. When the kernel checks `MetaCompose(tactic_name: "induction", sub: [...])`:

1. Look up `<T-qn>.induction`'s registered principle.
2. Read its statement to determine the expected sub-witness shape:
   - Enum with N constructors → expect N sub-witnesses, each proving `P(c_i)`.
   - Inductive ADT → expect base sub-witnesses for nullary constructors plus step sub-witnesses (with IH) for recursive constructors.
   - Primitive Int64 → expect a base sub-witness (`P(0)`) plus a step sub-witness (`∀ n. P(n) ⇒ P(n+1)`).
3. Verify the sub-witnesses match.

This unifies the meta-tactic and its contract: one source of truth (the auto-generated principle), and the meta-tactic is just a structured user-facing way to invoke it. New constructors automatically expand the contract; the kernel and meta-tactic stay in sync without separate updates.

#### Citable for manual induction proofs

Without going through the meta-tactic syntactically, a user may explicitly cite `<T-qn>.induction` and supply ground sub-proofs:

```anthill
proof some_universal_claim
  using anthill.prelude.Int64.induction
  by z3(logic: "LIA")
end
```

The cite resolves to the registered principle; the proof block discharges in a context where the principle's universal claim is asserted. This is the same `using` machinery as any other cite — no special handling.

`Int64.induction(?P, ?lo, ?hi)`, `BigInt.induction(?P)` and similar already-stdlib rules become *the source-level shorthand* for these auto-registered principles. The stdlib file declares the rule; the kernel observes it's an induction principle for the primitive sort and generates the matching ProofRecord with `ScopeAxiom(aspect: "induction")` witness automatically. (For sorts the user defines, the same auto-generation happens at sort load.)

#### Specialization for polymorphic sorts

`List.induction` is parametric over `T`. A use at `T = Int64` produces a `Specialization(parametric: "List.induction", substitution: [{abstract_param: "T", concrete_sort: "Int64"}], instances: [...])` ProofRecord. The instance-proofs list covers any `requires` `T` had in `List`'s declaration; for `List[T]` with no T-requires, the instances list is empty and `Specialization` is purely a substitution operation.

#### Composition with `requires` (open question)

For polymorphic inductive sorts with parametric `requires` — e.g. `sort List[T] requires Eq[T]` — the inductive step's proof may need `Eq[T]`'s laws to discharge. Two cite mechanisms compose:

- `List.induction` provides the structural inductive shape.
- `List.requires.Eq_T` provides the abstract law content.

Both are implicitly cited inside `List`'s scope. At a use site for `T = Int64`, both specialize together via `Specialization`. The composition is mechanical but worth a careful check on first implementation; flagged in open questions.

### Per-predicate translation policy

The vocabulary-alignment problem is a translation-layer concern with a clean stance-2 framing: **the kernel decides once, per predicate per backend, how each call is lowered**. The decision is project-wide and applies to every proof equally.

Policy resolution at translation time:

1. Look up `TranslationPolicy(predicate = <qn>, backend = <bk>, policy = <p>)` in the KB.
2. If absent, apply the backend's *inferred default*:
   - `Inline` for closed-body atomic predicates with no cite-side use observed.
   - `LiftedAxiom` for predicates that appear in any `using` clause.
   - `DefineFun` (or `define-fun-rec`) for self-recursive predicates the backend supports.
   - `DeclareFun` for predicates whose only proof is `TrustedAxiom`.
3. Emit per-policy.

Override channels: namespace-level meta blocks can write TranslationPolicy facts at load time; per-predicate rule meta blocks can write them; CLI flags can override during `prove`. The precedence is: CLI > per-rule meta > namespace meta > inferred default.

For Lean / dReal / future backends, each defines its own per-policy emission, but the *policy choice* may be shared across backends where semantics align. This is what makes anthill multi-backend at the architectural level: the kernel speaks predicates, theorems, and policies; each backend speaks its native form derived from kernel-level decisions.

### `using` semantics, reframed

`proof X using Y₁, Y₂, ... by <tactic>(...)` resolves each `Yᵢ` against the KB. The driver also computes X's **implicit citation set** — every `requires`-clause ProofRecord supplied by X's enclosing scope chain (sort + namespace + operation requires, transitively closed up the scope tree). Implicit and explicit cites are joined into one effective citation list before discharge.

For each citation (explicit or implicit):

1. Look up the corresponding `ProofRecord`.
   - **Absent or `result != Discharged`**: hard error. *"Cannot cite Yᵢ in proof X: Yᵢ has not been proved (no Discharged ProofRecord)."* (For implicit cites this is impossible if the auto-registration in §`requires` clauses as auto-registered lemmas` is done; missing ProofRecord indicates a kernel bug.)
   - **Present but `state_hash` mismatches current KB state**: re-discharge first (or, if there's a proof block in the same `prove` invocation, schedule it before X). If re-discharge fails, X's discharge fails with a clear error.
2. Project the cited rule to its theorem statement (mechanical).
3. Translate the statement under the project's per-predicate policy, into the consumer's backend vocabulary.
4. Splice the rendered translations into X's discharge as `(assert ...)` clauses, before X's body and conclusion.

The crucial change: **resolution is ProofRecord-mediated, not text-based.** The cite is sound iff the witness was kernel-checked and the state-hash is current. The cite has consistent vocabulary iff the per-predicate policy is the same everywhere — which is the case by construction at stance 2.

The current `lift_rule_to_implication_clause` becomes a *translation function* — input: a Rule + its ProofRecord + the project's policy; output: a backend-specific SMT-LIB clause. It is no longer the soundness mechanism; the registry-via-ProofRecord is.

### Cache and invalidation

Today's proof cache (proposal 025.1) keys on the emitted SMT-LIB document plus visited rule IRs (WI-096). Stance 2 lifts caching naturally:

- A `ProofRecord`'s `state_hash` is the canonical hash of every kb-state slice the proof depended on.
- A `ProofRecord` is *stale* if the current KB's slice for any of its dependencies hashes differently than recorded.
- Stale records are re-discharged before they can be cited.
- Witness payloads (SMT documents, SLD trees, model strings) live in the prove cache, content-addressed.

This is more granular than per-document keying. Two proofs sharing dependencies share cache invalidation. Editing a single fact invalidates exactly the proofs whose dependencies include that fact, no more and no less.

### Lifecycle: load, prove, check

Stance 2 has three distinct operations on the proof registry. They run together during normal development but are conceptually separate, and they map to three CLI commands — two of which already exist as scaffolds in `rustland/anthill-cli/src/main.rs`.

#### 1. Load (`anthill load`)

Triggered by anything that touches source. Operations:

- Parse the source.
- Auto-register meta-lemmas:
  - For each `requires <SE>` clause: register a ProofRecord with `ScopeAxiom(aspect: "requires.<SE>")`, status `Discharged`.
  - For each inductive sort / supported primitive: register `<sort-qn>.induction` with `ScopeAxiom(aspect: "induction")`, status `Discharged`.
- Materialize `ProofRecord` placeholders for each `proof` block in source, status `Pending`.

Load is read-source-write-KB. It establishes the registry's *shape* without verifying anything beyond syntactic consistency. Fast.

Today's `anthill load` does the parse + counts but no auto-registration; phase α adds the registration steps.

#### 2. Prove (`anthill prove`)

Triggered explicitly. Side-effect-bearing. Operations:

- For each `Pending` ProofRecord, run its proof block's tactic. On success, the kernel checks the returned witness; on accept, transition to `Discharged` and write the witness + state-hash. On reject, transition to `Failed`.
- For each `Discharged` ProofRecord whose state-hash is stale, re-run the discharge.

Today's `anthill prove` runs tactics but doesn't write witnesses or state-hashes; the cache infrastructure is per-SMT-document, not per-ProofRecord. Phase α extends this; phase γ rewires `using` to consult the registry.

#### 3. Check (`anthill check`)

**Already exists as a CLI scaffold** (`run_check` in `main.rs:1082`) — currently a stub that prints fact/rule counts and the message *"constraint evaluation not yet implemented."* Stance 2 fills in the body.

Operations (read-only on KB and cache):

- Walk every `Discharged` ProofRecord in the registry.
- For each, compute the current state-hash from the rule's IR + transitively-visited deps. Compare to recorded `state_hash`.
- Run kernel-checking on the witness per its constructor:
  - `SmtDischarge` → re-run the cached SMT-LIB document, verify verdict matches.
  - `SldDerivation` → replay the resolution tree.
  - `MetaCompose` → structural validation; recurse on sub-witnesses.
  - `ScopeAxiom` → re-read the cited declaration, dispatch on aspect.
  - `Specialization` → verify substitution + lookup parametric and instance ProofRecords.
  - `TrustedAxiom` → record the trust flag; not validated.
- Report: which records pass, which are stale (state-hash mismatch), which fail (witness rejected), which transitively depend on `TrustedAxiom`.

The semantic distinction from `prove --refresh-cache`: `check` validates *recorded* witnesses against the current KB; it doesn't re-run tactics or produce new documents. It's the integrity audit, not the discovery process.

CLI surface (filling in the existing scaffold):

```
anthill check [path...]
    --shallow         skip witness replay (state-hash + structural only)
    --deep            full replay (default for CI)
    --report-stale    list stale ProofRecords without re-checking
    --report-trust    surface TrustedAxiom dependencies
    --filter=<glob>   restrict to specific rule QNs
```

The CI pattern becomes: developer runs `prove`; commits source + ProofRecord facts (witness payloads stay in cache, content-addressed); CI runs `check` to verify the registry's integrity without re-running discovery.

`check` and `prove` share kernel-check routines via phase β's witness-checking layer; they differ only in side effects (`check` is read-only) and in their treatment of `Pending` / stale records (`prove` re-discharges; `check` reports).

## Concrete worked example: lf1 universal-over-k closure

To make the design concrete, here is how the lf1 chain composes under stance 2.

### Step 1 — `reachability_band` is registered

Today's `reachability_band` rule has `body = eq(?marker, true)` — a placeholder; the real claim is implicit in the induction tactic structure. Under 030 it's restated with an explicit `-:`:

```anthill
rule reachability_band(?k, ?d)
  :- gte(?k, 0),
     distance_at_step(?k, ?d)
  -: gte(?d, d_min),
     lte(?d, d_max)
```

The induction tactic discharges this via four sub-queries (`base_lower_violation`, `base_upper_violation`, `lower_violation`, `upper_violation`). Each sub-query produces an `SmtDischarge` witness; the meta-tactic combines them into a `MetaCompose(tactic_name = "induction", sub = [w₁, w₂, w₃, w₄])`.

The kernel checks the `MetaCompose`:
- The contract `MetaTacticContract(name = "induction", over = "Int64")` requires a base witness at `0` and a step witness covering `P(n) ⇒ P(n+1)`.
- The four sub-witnesses match the contract (two-bound base + two-bound step).
- Each sub-witness's `SmtDischarge` is checked by replay.
- All checks pass; the kernel writes `ProofRecord(rule = "reachability_band", result = Discharged, witness = MetaCompose(...), state_hash = <hash>)`.

The rule's projected statement is `∀ (k: Int64) (d: Real). (k ≥ 0 ∧ distance_at_step(k, d)) ⇒ (d ≥ d_min ∧ d ≤ d_max)` — derived on demand from the rule's IR, not stored.

### Step 2 — `safety_min_distance` cites

```anthill
rule safety_min_distance(?l, ?f, ?d)
  :- reachable_real(?l, ?f),
     position_distance(?d, ?l, ?f)
  -: gte(?d, d_min)

proof safety_min_distance
  using reachability_band, distance_at_step_definition
  by z3(logic: "UFLRA")
end
```

`distance_at_step_definition` is a separate rule + proof: `∀ (l: Pose) (f: Pose) (d: Real). (reachable_real(l, f) ∧ position_distance(d, l, f)) ⇒ (∃ k. k ≥ 0 ∧ distance_at_step(k, d))`. Discharged via SLD derivation against the rules' bodies — no arithmetic. Its ProofRecord carries an `SldDerivation` witness.

When `safety_min_distance` discharges:

1. Both cited rules' ProofRecords are looked up. Both have `result = Discharged`, both state-hashes match. Good.
2. Each is projected to its theorem statement.
3. Each statement is translated via the project's per-predicate policy — `position_distance` and `distance_at_step` get `LiftedAxiom`; `reachable_real` is `Inline`.
4. The lifted forall implications are spliced into the consumer's preamble.
5. `safety_min_distance`'s body and conclusion are translated and discharged. Z3 instantiates the cited foralls at the consumer's vars; the bridge supplies the existential k; reachability_band supplies the band membership; the consumer's `-:` conclusion follows.
6. Discharge produces an `SmtDischarge` witness; the kernel checks; the ProofRecord registers; future proofs may cite `safety_min_distance` in turn.

There is no axiom acceptance: every cited rule has a checked witness. Every cited statement is a mechanical projection of the rule's IR. The translation policy is project-wide, so the predicates appear with the same SMT-LIB symbols in every proof.

### Step 3 — invalidation

If the user edits `position_distance`'s body, the kernel observes:
- `safety_min_distance`'s state hash includes `position_distance`'s IR; the hash changes.
- The cached `safety_min_distance` ProofRecord is stale.
- On next `prove`, `safety_min_distance` is re-discharged.
- `reachability_band` is unchanged (it doesn't depend on `position_distance`'s IR — `distance_at_step` is the abstract bridge); its ProofRecord remains valid.
- Re-discharge is fast: cache hits on `reachability_band` and `distance_at_step_definition`; only `safety_min_distance` actually re-runs Z3.

This is granular, sound, and matches user intuition: editing a definition invalidates exactly what depended on it.

## Implementation plan

### Phase α — Witness schema and tactic contract (foundation)

**Goal:** `ProofWitness` exists as a schema; tactics return witnesses; `ProofRecord` carries them.

- α.1 ✓ — Schema: `ProofWitness` (with `SmtDischarge`, `SldDerivation`, `MetaCompose`, `ScopeAxiom`, `Specialization`, `TrustedAxiom`), `SmtVerdict`, `SortBinding` declared in `stdlib/anthill/realization/witness.anthill`. (Note: `MetaTacticContract` deferred to β.3 follow-up.)
- α.2 ✓ — `ProofRecord` extended with `witness`, `state_hash`, `parametric_context`. Loader writes placeholders for legacy records.
- α.3 ✓ — Dispatch paths refactored to `DispatchOutcome { verdict, witness, visited_rules }`.
- α.4 ✓ — `state_hash(kb, visited)` in `cache::key`; computed per-ProofRecord in `run_prove` after dispatch.
- α.5 ✓ — Content-addressed blob storage in `cache::blob`. SMT documents and sat models persist via `store_blob`; witnesses carry real `document_hash` / `model_hash`.
- α.6 ✓ — `register_requires_axiom_witnesses` walks `SortRequiresInfo` facts at load and emits ScopeAxiom-witnessed ProofRecords.
- α.7 ✓ — `register_induction_axiom_witnesses` walks `SortInfo` facts; v0 covers `kind = "enum"` sorts. Recursive ADTs (kind = "sort" with self-referential constructor fields) deferred.
- α.8 ✓ — `register_specialization_witnesses` walks `SortProvidesInfo` facts (Variant 3 design via WI-119: explicit `provides` declares intent; Specialization records emitted automatically). β.5 enforces substitution well-formedness; full instance-list coverage deferred (records carry empty instances list in v0).

This phase delivers: `prove` writes augmented ProofRecords. No new user-visible features yet; existing `proof` blocks just gain witnesses on success.

### Phase β — Certificate checking

**Goal:** the kernel checks witnesses; trust boundaries are explicit.

- β.1 ✓ — `check_smt_discharge_payload` re-runs the cached SMT-LIB document, re-hashes the loaded blob (catches tamper), compares verdict to the witness.
- β.2 ✗ deferred — needs resolver instrumentation to capture a real derivation tree; current witness uses a placeholder `tree_hash`. Picks up when a project actually relies on derivation discharges.
- β.3 ✓ — `check_meta_compose_witness` (KB-side) and the matching sidecar path recurse on each sub-witness. Per-meta-tactic shape contracts (`induction` expects base + step, `ranking` expects boundedness + decrease) deferred — needs the `MetaTacticContract` schema, which is still pending.
- β.4 ✓ — `check_scope_axiom_witness` re-reads `SortInfo` / `SortRequiresInfo` facts and dispatches on `aspect`. Encoding parity with α.6's `flatten_spec` is enforced by direct reuse of the same helper.
- β.5 ✓ — `check_specialization_witness` validates substitution well-formedness + parametric ProofRecord existence. v0 instance-list always empty (per α.8 v0), so coverage is structural; full per-law coverage check pending α.8 instance-list population.
- β.6 ✓ — `aggregate_meta_outcomes` combines sub-witness statuses with priority Failed > Skipped > Trusted > Pass. Trust reasons aggregate across the full subtree.
- β.7 ✓ — Multi-layered tamper detection: blob content sha256 re-check at load (catches manual file edits); verdict-replay (catches sidecar lying about its document); the `lying_sidecar_verdict_fails` and `tampered_blob_fails_content_hash_check` unit tests pin these properties.

### Phase γ — `using` consults the registry

**Goal:** citations are ProofRecord-mediated and gated on Discharged status with valid state-hash.

- γ.1 ✓ — `lift_rule_to_implication_clause` retained as the lift primitive; the caller-side `cite_status` gate enforces the Discharged precondition. Pending / Failed / NotFound surface as hard `EmitError` on the consumer's discharge.
- γ.2 ✓ — `cite_status(kb, cited_qn, cli, discharged_this_run)` consults: (1) in-memory discharged-this-run set; (2) KB ProofRecord witness shape (ScopeAxiom + Specialization → discharged-by-construction; non-placeholder TrustedAxiom → Trusted); (3) on-disk witness sidecar. Each cite either resolves or surfaces a per-rule error message.
- γ.3 ✓ — Kahn's topological sort over the `using` graph in `topo_sort_by_using`. Cycles emit a stderr warning and append the cyclic members to the order's tail; per-rule cite-resolution then surfaces the ambiguity.
- γ.4 ✓ — `implicit_cites_for(rule_qn, kb)` walks parent QN segments outer-to-inner and collects every `<scope>.requires.<flat>` ProofRecord as an implicit citation. `dispatch_z3` builds `effective = explicit + implicit` and passes it to `render_cited_lemmas`.

After γ, the silent axiomatic content of the current `using` is gone. Every cite resolves to a checked theorem or fails loudly.

### Phase δ — Per-predicate translation policy

**Goal:** vocabulary alignment is automatic and project-wide.

- δ.1 ✓ — Schema landed at `stdlib/anthill/realization/policy.anthill`.
- δ.2 ✓ — `policy_for(kb, predicate, backend, cited_predicates)` defaults to `LiftedAxiom` for cite-side-used predicates, `Inline` otherwise.
- δ.3 partial — Source-level `fact TranslationPolicy(...)` declarations override the inferred default. Namespace meta blocks, per-rule meta blocks, and CLI flags are not yet wired (deferred — source-fact override covers the most common case).
- δ.4 ✗ deferred — smt-gen call-site emission still inlines unconditionally. Existing `lift_rule_to_implication_clause` already produces the LiftedAxiom shape for `using`-cited predicates, so the practical behavior matches policy.δ.2 for v0; the refactor lands when there's a concrete consumer (e.g. multiple proofs citing the same predicate where dedup'd `define-fun` + `assert (forall ...)` would shorten the document).
- δ.5 ✗ deferred — logic-fragment selection from policy mix is meaningful only after δ.4 lands.

### Phase ε — Migration and cleanup

**Goal:** old infrastructure deprecated; new infrastructure is the source of truth.

- ε.1 ✓ — `cargo build --workspace` emits zero warnings; stale `#[allow(dead_code)]` markers and dead imports swept; `lift_rule_to_implication_clause` docstring updated to point at γ.1's `cite_status` as the discharge gate. The text-injection warn-and-proceed path is gone — γ.2's hard-error replaced it during the γ landing.
- ε.2 ✓ — done during the lf1 work that motivated this proposal: the four `safety_*` proofs are positive-form rules with `-:` conclusions, citing `reachability_band` and `distance_at_step_definition` via `using`.
- ε.3 ✓ — done in the same wave: `reachability_band` carries an explicit `-:` conclusion (lf1 commits prior to phase α landing).
- ε.4 ✓ — this section + §Soundness boundary below.
- ε.5 ✓ — `run_check` body wired in commit `8b5fc08` (β.1) and progressively extended; full CLI flag set (`--shallow` / `--deep` / `--report-stale` / `--report-trust` / `--filter` / `--solver`) landed in commit `1780e9e`.

## Soundness boundary

The trust base after phase α + β + γ + WI-124 + ε:

| Component | Trusted? | Why |
|---|---|---|
| **Z3 solver verdict** (and any future solver in the SmtDischarge replay path) | yes | β.1 audits by replay: re-runs the recorded SMT-LIB document, checks the verdict matches. A faulty solver returning unsat for a sat document is undetected. Documented limitation; future work could integrate Z3's `(get-proof)` for solver-independent verification. |
| **The kernel's loader, term store, and resolver** | yes | Standard "language implementation" trust base. Tampering at this level would also defeat the witness machinery. |
| **Source declarations (sort / requires / induction / provides clauses)** | yes (read-only) | β.4 verifies a `ScopeAxiom` witness by re-reading the cited declaration in the current KB. The declaration *constitutes* the proof; the kernel mechanically checks the structural fact ("the clause is present with this shape"). Editing the source invalidates the witness on next access. |
| **Content-addressed blob store (cache::blob)** | partial | Tamper detection is sha256-strong: a manually-edited blob fails the content-hash re-check at load time (β.7). An attacker who replaces both the blob and the corresponding hash in a sidecar must also produce a document Z3 accepts with the claimed verdict — i.e. actually prove the property. |
| **Witness sidecar JSON** (`cache::witness`) | not trusted alone | A sidecar pointing at a forged blob fails as above. A sidecar that lies about the verdict (claims Unsat for a Sat document) fails the replay step. |
| **TrustedAxiom witnesses** | yes — explicit user opt-in | Surfaced through every containing witness via β.6's aggregation. Users see the trust dependency in CLI output; `anthill check --report-trust` lists them. |
| **MetaCompose composition** | not trusted alone | β.3 + β.6 recurse on each sub-witness; the overall outcome is the worst of the per-sub outcomes. |
| **Specialization composition** | not trusted alone | β.5 verifies substitution well-formedness + parametric ProofRecord existence. The parametric's own check transitively guards soundness. |

**What is not in the trust base:**
- The user's `proof X by z3(...)` block — its tactic is untrusted; the produced witness is checked.
- `using` text injection — γ.1's gate makes the cite resolve through the registry; un-discharged cites fail loudly.
- The SLD resolver (when β.2 lands) — replay against the current KB will be the audit mechanism.
- Translation policy choices — δ's policy fact is a routing decision; the resulting SMT document still goes through SmtDischarge replay.

## Implementation status

Phase coverage at a glance (see commits referenced inline):

| Phase | Status |
|---|---|
| α — witness schema, ProofRecord ext, dispatch refactor, state hash, blob storage, auto-registration | **8/8 landed** |
| β — kernel-side certificate checking | **6/7 landed** (β.2 SldDerivation deferred; no current consumer) |
| γ — `using` consults the registry | **4/4 landed** |
| δ — per-predicate translation policy | **schema + lookup + source-fact override landed** (δ.4 smt-gen call-site integration + δ.5 logic-fragment selection deferred) |
| ε — migration and cleanup | **CLI flag set + cleanup landed** (ε.1, ε.4, ε.5 done; ε.2/ε.3 done during the lf1 work that motivated 030) |
| WI-124 — sidecar witness persistence | **landed** (closes the prove → check loop across CLI invocations) |

**Demonstrated end-to-end on the lf1 example** (`examples/webots-modelling/lf1/`):
- `anthill prove`: 11 user safety proofs discharge to Z3 unsat (4 SmtDischarge, 2 MetaCompose under induction/ranking, plus 5 violation-shape sub-proofs).
- `anthill check`: 43/43 ProofRecords verify clean — 11 user proofs (sidecar-replayed), 2 meta-tactic compositions (recursive replay), 1 Specialization (structural), 29 auto-registered ScopeAxioms (declaration re-read).
- 0 trusted, 0 failed, 0 skipped.

**Deferred sub-phases (no current blocker):**
- β.2 — SldDerivation real replay needs resolver instrumentation; no current project depends on derivation-tactic discharges.
- δ.4 — smt-gen call-site policy integration becomes meaningful when projects have multiple proofs citing the same predicate; lf1 already works with the existing per-cite lift.
- δ.5 — logic-fragment selection from policy mix follows δ.4.
- α.7 recursive-ADT detection — current α.7 covers `kind = "enum"` sorts; recursive ADTs (kind = "sort" with self-referential constructor fields) would extend the detection.
- α.8 instance-list population — current Specialization records carry empty `instances` lists; β.5 would do per-law coverage check once instances are populated.
- `MetaTacticContract` schema — β.3 currently does only the universal "every sub-witness verifies" check; per-meta-tactic shape contracts (induction expects base + step, ranking expects boundedness + decrease) would require the schema.

## Grammar changes

The grammar grows in two places:

- **Conclusion clause `-:` on rules** — already added (WI-C1). Stays as-is.
- **`using <name-list>` clause on proof blocks** — already added (WI-A). Stays; gains registry-mediated semantics in phase γ.
- **Optional translation policy in rule meta** — `[translation: lifted_axiom]` etc. New; opt-in. Default behavior is inferred per backend.

No new top-level keywords. The earlier-discussed `relation` / `axiom` constructs are *not* introduced — their content is captured by `DeclareFun` policy plus `TrustedAxiom` witnesses.

## Migration path from current state

Current state: WI-A (using clause), WI-B (ProofConfig.assumptions), WI-C1 (`-:` conclusion + lift) landed. WI-C2 reverted.

Migration to phase α-end:

1. **Statement projection** is straightforward; `lift_rule_to_implication_clause` already does most of the work. Refactor it to a typed-statement function.
2. **Tactic interface** is mechanical refactoring. Existing tactics keep working; only return type changes.
3. **Witness schema** requires new realization stdlib files. Each new realization sort is one anthill file plus loader hooks.
4. **State hash** reuses cache infrastructure.
5. **ProofRecord extension** is a small loader change.

Phase β can land alongside α (witness checking is independent of statement projection). γ depends on α and β. δ can begin once γ has landed. ε is end-of-line cleanup.

## Scope: what 030 is and is not

**In scope:**
- Witness representation per tactic kind, on `ProofRecord`.
- Kernel-side certificate checking with explicit semantics per witness constructor.
- `TrustedAxiom` as the explicit, opt-in axiom-acceptance mechanism.
- `using` reframed as registry consultation gated on Discharged + state-hash.
- Per-predicate translation policy as the systematic answer to vocabulary alignment.
- Backend-agnostic schema; backend-specific implementations.

**Out of scope:**
- Z3-internal proof certificates (Z3's `(get-proof)`). Stance-2 v0 uses replay-based checking; future work.
- Lean/dReal/cvc5 backends. Schema accommodates them; implementation is per-backend.
- A separate `Theorem` sort. Theorems are rules with discharged ProofRecords; no parallel object.
- User-overridable theorem-statement projections (non-Horn theorem shapes). Mechanical projection only for v0.
- Cross-project theorem composition. Single project per `prove` invocation; cross-project caching is a separate concern.

## Open questions

1. **Z3 trust boundary** — *open*. Audit-by-replay treats Z3 as part of the trust base. Acceptable for v0; documented in §Soundness boundary. Future work could integrate Z3's `(get-proof)` output and a lightweight proof checker.

2. **Mutual recursion in `define-fun-rec`** — *open*. Some predicates (`real_pose_at` referencing itself) need mutually recursive definitions. SMT-LIB supports this via `define-funs-rec`. Termination metrics may need user input.

3. **Type inference for projected statements** — *open*. Local inference works for well-typed rules but has corner cases (variables that appear only in opaque positions, polymorphic predicate calls). Default to user-visible warnings on inference fallback; allow explicit annotation via `forall (?d: Real)` syntax in rule heads (a small future grammar extension).

4. **Default policy for new predicates** — *resolved* (δ.2 landed). `policy_for` defaults to `LiftedAxiom` when the predicate appears in any `using` clause across the project, `Inline` otherwise. δ.4 (smt-gen call-site emission) deferred but the policy decision is in place.

5. **Cache durability** — *resolved*. Witness payloads (SMT documents, sat models) live in `<XDG cache>/projects/<repo-hash>/blobs/v1/`, content-addressed by sha256. Sidecars live in the parallel `witnesses/` subtree. Source-side `.anthill` files stay clean.

6. **Backwards compatibility** — *resolved*. The `-:` conclusion clause + lift mechanism (WI-C1) is in place; existing `proof X by z3(...)` blocks work. The lf1 `safety_*` proofs were migrated as part of ε.2/ε.3.

7. **Trust visualization** — *resolved* (β.6 + ε flag set landed). `aggregate_meta_outcomes` collects every TrustedAxiom reason in a witness tree; `anthill check` surfaces them as `⚠ <rule>: trusted axiom (<reason>)` lines. `anthill check --report-trust` filters output to only the trust dependencies.

8. **Multi-tenancy** — *open*. Concurrent `prove` invocations against the same project still race on cache writes. Lock the cache directory; serialize per-record-name. Implementation detail, no observed problem in v0.

9. **Quantifier instantiation usability (completeness, not soundness)** — *open*. When `using` injects a forall-quantified cited claim, Z3's heuristic instantiation may or may not fire on the consumer's body. This is *completeness*, not soundness: an unhelpful Z3 verdict (sat where the cite would suffice with the right instantiation) means the user must add patterns, ground witnesses, or restructure — not that the system is unsound. The cite remains an asserted hypothesis in any interpretation Z3 considers, and the cite's truth is what 030 guarantees via kernel-checked witnesses. Tools to consider as quality-of-life follow-ups (none are blockers): emit `:pattern` triggers in the lifted forall (mechanical, cheap, Z3-specific); allow user-written `using <Y>(witness: <ground-args>)` for explicit ground instantiation (small grammar extension); CLI diagnostics that suggest patterns when a discharge fails near a `using` boundary.

10. **Compound meta-tactic proofs (Framing A → Framing B transition)** — *open, deferred*. v0 commits to *Framing A* (sub-witness-local hypotheses; see Design § Scope of meta-tactic sub-witnesses) — meta-tactic-introduced hypotheses like the inductive hypothesis stay local to the sub-witness's discharge context and do not enter the kernel registry. This breaks when a step's own proof wants to compose other registered theorems via `using` while also having access to IH. *Framing B* introduces scoped temporary registry entries: a meta-tactic, when dispatching a sub-witness, registers a transient fact ("IH is true, scoped to this sub-witness") that lives in the registry only for the duration of the sub-witness's discharge. Implementation requires a `scope: Option[T = SubProofId]` field on ProofRecord, scope-aware querying, sub-proof identifier propagation through nested meta-tactic calls, and lifetime cleanup. Punted from v0; revisited when compound use cases demand it.

11. **Composition of induction principle and `requires` for polymorphic inductive sorts** — *partially resolved*. The current α.6 + α.7 + α.8 pipeline emits separate Specialization records per aspect (induction, requires-clause). γ.4's enclosing-scope walker implicitly cites both. A use site for `T = Int64` produces specialized versions of both via separate `Specialization` ProofRecords. Whether to also produce a *single* combined specialization (more compact) or stay with per-aspect granularity (current behavior, simpler) remains open; v0's per-aspect approach is sound regardless.

12. **`provides` discharge mechanism (WI-119)** — *resolved* (Variant 3 chosen). Source-level `provides A[T = X]` declares satisfaction intent → loader emits `SortProvidesInfo` fact → α.8 verifies + emits Specialization ProofRecords. See WI-119's recorded decision: explicit declarations preferred over implicit derivation (intent vs coincidence is information-bearing). Variant 1 (no clause; derive from existence of supporting proofs) and Variant 2 (compile RHS / mechanical substitution) explicitly rejected.

## Summary

This proposal committed anthill to *stance 2* — proof-assistant architecture with kernel-checked proofs, untrusted tactics, and ProofRecord-mediated citation — by augmenting what already exists rather than introducing new top-level objects. There is no `Theorem` sort; theorems are rules whose ProofRecords are in `Discharged` state with a kernel-checked witness. The `using` mechanism's silent axiomatic content has been replaced with mechanical witness checking. Vocabulary alignment is now policy-driven (schema + lookup + default inference landed; smt-gen call-site integration deferred).

Five phases (α-ε) lay out the incremental implementation. As of the §Implementation status table above: α (8/8) and γ (4/4) are complete; β has 6/7 (β.2 SldDerivation deferred); δ landed schema + lookup + source-fact override (smt-gen integration deferred); ε is complete except where overlapping deferrals apply. WI-124 added the witness sidecar layer that closes the prove → check loop across CLI invocations.

The lf1 universal-over-k closure is expressible end-to-end without trust gaps: `reachability_band` is restated with `-:`, discharged via induction, witness checked; the four `safety_*` proofs cite via `using`; cites are registry-mediated and reproducible; `anthill check` reports 43/43 pass on the loaded registry. No axiom acceptance, no opaque flags, no degenerate rules.

The cost was real — phases α-γ landed across many commits — but the infrastructure is the price of the architectural commitment in `kernel-language.md` §1. Anthill is now the small-trusted-kernel system its design principles describe — by adding precisely what was missing (witnesses, state-hashes, content-addressed storage, registry-mediated cites) rather than parallel infrastructure.
