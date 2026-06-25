//! WI-558: proof-verification pass — the "prove-pass gate" deferred by
//! WI-538.
//!
//! The loader records every top-level `proof <rule> by <strategy>` as a
//! `ProofRecord` fact with `result: Pending` and a placeholder
//! `TrustedAxiom("pending — not yet discharged")` witness ([`super::load`]).
//! WI-538 wired *in-body* `by derivation` proofs to discharge inline in the
//! typer (`prove_from_gamma`), but **top-level** proofs were never checked as
//! part of the load/type pipeline — only by an explicit `anthill prove`, which
//! moreover writes its verdict to a sidecar, never back into the KB.
//!
//! This module supplies the missing piece for the in-process tier:
//!
//! * [`discharge_by_derivation`] — the canonical `by derivation` SLD discharge
//!   (resolve the target rule's body under the resolver's floundering guard),
//!   shared with the cli `dispatch_derivation` so the two never drift on what
//!   "a derivation" means.
//! * [`set_proof_result`] — flip a `ProofRecord`'s `result`
//!   (`Pending → Discharged | Failed`) and, on discharge, its `witness`, by
//!   retract + re-assert. Shared by the core pass and the cli prove write-back.
//! * [`verify_proofs`] — walk the Pending `ProofRecord` facts and discharge the
//!   `by derivation` ones, recording a real `SldDerivation` witness on success
//!   and `Failed(Unknown(..))` on a non-derivation (loud + conservative — never
//!   silently `Discharged`). Tier-B (`by z3` / external) and open obligations
//!   are left **Pending** (reported [`ProofVerdict::Deferred`]); the cli gate
//!   over `anthill-smt-gen` owns those, since z3 lives downstream of core.
//!
//! Tier-B verification, the `Γ`-snapshot for in-body proofs, and auto-chaining
//! into `anthill check` are deferred (see `docs/design/local-proof.md` OQ-A/B).
//! This pass is also the discharge entry point WI-539 Part 2 (`<op>.<clause>`
//! contract proofs) hands a constructed goal + context to.

use std::collections::HashMap;

use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::{Symbol, SymbolKind};
use crate::kb::resolve::ResolveConfig;
use crate::kb::subst::Substitution;
use crate::kb::term::{Literal, Term, TermId};
use crate::kb::typing::{
    clause_conjuncts, get_named_arg, is_value_precondition_clause, prove_from_gamma,
    substitute_ref_terms, FlowEnv,
};
use crate::kb::{KnowledgeBase, RuleId};

/// Default SLD search bound for an un-parameterised `by derivation` proof.
/// Mirrors the cli `dispatch_derivation` default.
pub const DEFAULT_DERIVATION_DEPTH: usize = 200;

// ── by-derivation discharge ──────────────────────────────────────────

/// Outcome of a `by derivation` SLD discharge attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerivationOutcome {
    /// A definite derivation was found; `tree_hash` references it (the
    /// phase-α.3 placeholder convention — a full derivation-tree capture is
    /// the deferred α.5 upgrade).
    Proved { tree_hash: String },
    /// No definite derivation within the search bound. SLD is semi-decidable,
    /// so this is "not proved", *not* "disproved".
    NoDerivation,
    /// The proof names a rule QN with no symbol in the KB.
    RuleNotFound,
    /// The QN resolves but indexes no rules/facts.
    NoRules,
}

/// The phase-α.3 placeholder tree hash for an SLD derivation of `rule_qn`.
/// Shared by the core pass and the cli derivation dispatch so a derivation
/// witness reads identically regardless of which path produced it.
pub fn derivation_tree_hash(rule_qn: &str) -> String {
    format!("sld-derivation:{rule_qn}")
}

/// Discharge a `proof <rule_qn> by derivation` obligation by bounded SLD
/// resolution over the live KB (the proof's context: every scope / inherited /
/// definition rule indexed under `rule_qn`). A fact head is trivially proved;
/// otherwise the rule's body is resolved under `definite_only` so a floundered
/// residual is **not** mistaken for a derivation (WI-519). Mirrors the cli
/// `dispatch_derivation` inner loop, which now delegates here.
pub fn discharge_by_derivation(
    kb: &mut KnowledgeBase,
    rule_qn: &str,
    max_depth: usize,
    max_solutions: usize,
) -> DerivationOutcome {
    let rule_sym = match kb.try_resolve_symbol(rule_qn) {
        Some(s) => s,
        None => return DerivationOutcome::RuleNotFound,
    };
    let rules = kb.rules_by_functor(rule_sym);
    if rules.is_empty() {
        return DerivationOutcome::NoRules;
    }
    let config = ResolveConfig {
        max_depth,
        max_solutions: max_solutions.max(1),
        simplify: true,
        // WI-519: a proof must be DEFINITE — a floundered residual is not a
        // derivation, so it must not yield a solution here.
        definite_only: true,
        // `gamma` (the WI-537 overlay) is None for a top-level proof — its
        // context is the static KB, not a flow snapshot.
        ..Default::default()
    };
    for rule_id in rules {
        if kb.is_fact(rule_id) {
            return DerivationOutcome::Proved { tree_hash: derivation_tree_hash(rule_qn) };
        }
        // Resolve the rule's body as a goal list. The occurrence body
        // (`Value::Node` goals) is used directly — the resolver is
        // Value-internal, so no term lowering is needed (WI-246).
        let empty = Substitution::new();
        let (fresh_nodes, _links) = kb.with_fresh_vars(rule_id, &empty);
        let goals: Vec<Value> = fresh_nodes.into_iter().map(Value::Node).collect();
        if !kb.resolve_goals(goals, &config).is_empty() {
            return DerivationOutcome::Proved { tree_hash: derivation_tree_hash(rule_qn) };
        }
    }
    DerivationOutcome::NoDerivation
}

// ── verdict write-back ────────────────────────────────────────────────

/// What verdict to record onto a `ProofRecord`, for [`set_proof_result`].
#[derive(Debug, Clone)]
pub enum VerdictWrite {
    /// `result = Discharged(Proved(witness, solver, duration: 0ms))` and
    /// `ProofRecord.witness = witness`. `witness` is a `ProofWitness` term the
    /// caller built (e.g. [`make_sld_witness`] for derivation).
    Discharged { witness: TermId, solver: String },
    /// `result = Failed(Unknown(reason))`. The `witness` field is left
    /// untouched (no failure witness shape exists; `result` is authoritative).
    FailedUnknown { reason: String },
    /// `result = Failed(Disproved(counterexample, solver))`, the
    /// counterexample rendered as a string-bearing reflect term.
    FailedDisproved { counterexample: String, solver: String },
}

/// Build the `ProofWitness.SldDerivation(tree_hash)` term.
pub fn make_sld_witness(kb: &mut KnowledgeBase, tree_hash: &str) -> TermId {
    let sym = kb.resolve_symbol("anthill.realization.witness.ProofWitness.SldDerivation");
    let th = kb.alloc(Term::Const(Literal::String(tree_hash.to_string())));
    let k = kb.intern("tree_hash");
    kb.make_entity_term(sym, SmallVec::new(), SmallVec::from_slice(&[(k, th)]))
}

/// Flip the `result` (and, for [`VerdictWrite::Discharged`], the `witness`)
/// field of the `ProofRecord` fact `rid`: rebuild the head with those fields
/// replaced, retract the old fact, assert the new one. Keyed by the exact
/// `RuleId` (NOT the rule QN) so two `proof <same-rule>` declarations — which
/// the loader records as two distinct `ProofRecord` facts with identical `rule`
/// fields — each receive their own verdict, with no first-match clobbering.
/// Returns `true` when `result` was rewritten; a malformed record (non-`Fn`
/// head, or one missing a `result` field) is a kernel-invariant violation,
/// surfaced loudly (`debug_assert`) rather than silently no-op'd.
pub fn set_proof_result(kb: &mut KnowledgeBase, rid: RuleId, verdict: VerdictWrite) -> bool {
    let head = kb.rule_head(rid);
    let (functor, mut named) = match kb.get_term(head) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        _ => {
            debug_assert!(false, "set_proof_result: ProofRecord {rid:?} has a non-Fn head");
            return false;
        }
    };
    let (result_term, witness_term) = build_verdict_terms(kb, verdict);

    // Replace `result` (always) and `witness` (only when the verdict carries
    // one) in place, matching fields by resolved short name (`get_named_arg`
    // semantics). Declared field order is preserved; `make_entity_term`
    // re-canonicalises it regardless (WI-299).
    let mut wrote_result = false;
    for entry in named.iter_mut() {
        match kb.resolve_sym(entry.0) {
            "result" => {
                entry.1 = result_term;
                wrote_result = true;
            }
            "witness" => {
                if let Some(w) = witness_term {
                    entry.1 = w;
                }
            }
            _ => {}
        }
    }
    // Every `ProofRecord` carries a `result` field (realization.anthill); a
    // missing one would mean asserting an unchanged fact while the caller
    // reports a flip — surface it rather than quietly diverge.
    debug_assert!(wrote_result, "set_proof_result: ProofRecord {rid:?} has no `result` field");

    let sort = kb.rule_sort(rid);
    let domain = kb.rule_domain(rid);
    // Build the new head BEFORE retracting so its shared subterms (rule,
    // strategy, body, …) are incref'd and survive the old fact's release.
    let new_head = kb.make_entity_term(functor, SmallVec::new(), named);
    kb.retract(rid);
    kb.assert_fact(new_head, sort, domain, None);
    wrote_result
}

/// Construct the `ObligationStatus` (result) term and the optional replacement
/// `witness` term for a [`VerdictWrite`].
fn build_verdict_terms(kb: &mut KnowledgeBase, verdict: VerdictWrite) -> (TermId, Option<TermId>) {
    match verdict {
        VerdictWrite::Discharged { witness, solver } => {
            let proved = make_proof_result_proved(kb, witness, &solver);
            let result = make_obligation_status(kb, "Discharged", proved);
            (result, Some(witness))
        }
        VerdictWrite::FailedUnknown { reason } => {
            let unknown = make_proof_result_unknown(kb, &reason);
            let result = make_obligation_status(kb, "Failed", unknown);
            (result, None)
        }
        VerdictWrite::FailedDisproved { counterexample, solver } => {
            let disproved = make_proof_result_disproved(kb, &counterexample, &solver);
            let result = make_obligation_status(kb, "Failed", disproved);
            (result, None)
        }
    }
}

/// `ObligationStatus.<variant>(result: <proof_result>)`.
fn make_obligation_status(kb: &mut KnowledgeBase, variant: &str, proof_result: TermId) -> TermId {
    let sym = kb.resolve_symbol(&format!("anthill.realization.ObligationStatus.{variant}"));
    let k = kb.intern("result");
    kb.make_entity_term(sym, SmallVec::new(), SmallVec::from_slice(&[(k, proof_result)]))
}

/// `ProofResult.Proved(witness, solver, duration: 0ms)`. The duration is a
/// fixed `0ms` placeholder — the pass does not (and, for deterministic facts,
/// must not) record wall-clock time.
fn make_proof_result_proved(kb: &mut KnowledgeBase, witness: TermId, solver: &str) -> TermId {
    let sym = kb.resolve_symbol("anthill.prelude.Meta.ProofResult.Proved");
    let solver_t = kb.alloc(Term::Const(Literal::String(solver.to_string())));
    let dur = make_zero_duration(kb);
    let k_w = kb.intern("witness");
    let k_s = kb.intern("solver");
    let k_d = kb.intern("duration");
    kb.make_entity_term(
        sym,
        SmallVec::new(),
        SmallVec::from_slice(&[(k_w, witness), (k_s, solver_t), (k_d, dur)]),
    )
}

/// `ProofResult.Unknown(reason)`.
fn make_proof_result_unknown(kb: &mut KnowledgeBase, reason: &str) -> TermId {
    let sym = kb.resolve_symbol("anthill.prelude.Meta.ProofResult.Unknown");
    let reason_t = kb.alloc(Term::Const(Literal::String(reason.to_string())));
    let k = kb.intern("reason");
    kb.make_entity_term(sym, SmallVec::new(), SmallVec::from_slice(&[(k, reason_t)]))
}

/// `ProofResult.Disproved(counterexample, solver)`. The counterexample rides
/// as a string-bearing reflect term (the cli has no structured model term).
fn make_proof_result_disproved(kb: &mut KnowledgeBase, counterexample: &str, solver: &str) -> TermId {
    let sym = kb.resolve_symbol("anthill.prelude.Meta.ProofResult.Disproved");
    let ce = kb.alloc(Term::Const(Literal::String(counterexample.to_string())));
    let solver_t = kb.alloc(Term::Const(Literal::String(solver.to_string())));
    let k_c = kb.intern("counterexample");
    let k_s = kb.intern("solver");
    kb.make_entity_term(
        sym,
        SmallVec::new(),
        SmallVec::from_slice(&[(k_c, ce), (k_s, solver_t)]),
    )
}

/// `Duration(amount: 0, unit: "ms")`.
fn make_zero_duration(kb: &mut KnowledgeBase) -> TermId {
    let sym = kb.resolve_symbol("anthill.prelude.Duration.Duration");
    let amount = kb.alloc(Term::Const(Literal::Int(0)));
    let unit = kb.alloc(Term::Const(Literal::String("ms".to_string())));
    let k_a = kb.intern("amount");
    let k_u = kb.intern("unit");
    kb.make_entity_term(
        sym,
        SmallVec::new(),
        SmallVec::from_slice(&[(k_a, amount), (k_u, unit)]),
    )
}

// ── the pass ──────────────────────────────────────────────────────────

/// Per-record outcome of [`verify_proofs`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofVerdict {
    /// A `by derivation` proof was discharged; the record is now
    /// `Discharged` with an `SldDerivation` witness.
    Discharged,
    /// A `by derivation` proof did not derive; the record is now
    /// `Failed(Unknown(..))`. Loud and conservative — never silently
    /// discharged. `reason` explains why.
    Failed { reason: String },
    /// Not a tier this in-process pass discharges (Tier-B `by z3` / external,
    /// or an open obligation). Left **Pending** for the cli gate.
    Deferred { reason: String },
}

/// One entry of the [`verify_proofs`] report.
#[derive(Debug, Clone)]
pub struct ProofReport {
    pub rule_qn: String,
    pub verdict: ProofVerdict,
}

/// Verify every Pending `ProofRecord` in the KB. `by derivation` records are
/// discharged via [`discharge_by_derivation`] and their `result` flipped to
/// `Discharged` (real `SldDerivation` witness) or `Failed(Unknown(..))`
/// (loud + conservative). Tier-B / open records are left Pending and reported
/// as [`ProofVerdict::Deferred`]. Returns a per-record report in the order the
/// records were visited.
pub fn verify_proofs(kb: &mut KnowledgeBase) -> Vec<ProofReport> {
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return Vec::new(),
    };

    // Snapshot the work-list first (RuleId + rule QN + tier), so the
    // retract/assert in `set_proof_result` can't invalidate an in-flight index
    // walk, and so each record's verdict is written back to its OWN `RuleId`
    // (two `proof <same-rule>` decls → two records, no first-match clobber).
    let mut work: Vec<(RuleId, String, Tier)> = Vec::new();
    for rid in kb.rules_by_functor(record_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head(rid);
        let named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args.clone(),
            _ => continue,
        };
        // Kernel-auto-registered records (ScopeAxiom / Specialization) are
        // discharged by construction — never user-dispatched.
        if is_auto_registered(kb, &named) {
            continue;
        }
        // Only ground user proofs (a String `rule` QN) are dischargeable. The
        // KB also holds symbolic ProofRecords whose fields are bare `Ref`s (e.g.
        // template / partially-applied records); these are NOT user obligations,
        // and `read_string_field` returns `None` for them — the same skip the
        // cli `read_proof_record` makes via `lookup_string`. A genuinely
        // malformed record is caught loudly downstream at the write
        // (`set_proof_result`), where a missing `result` field is a real bug.
        let rule_qn = match read_string_field(kb, &named, "rule") {
            Some(s) => s,
            None => continue,
        };
        // Already-resolved (Discharged / Failed) records are intentionally
        // skipped — only Pending obligations are candidates.
        if !result_is_pending(kb, &named) {
            continue;
        }
        work.push((rid, rule_qn, classify_tier(kb, &named)));
    }

    let mut report = Vec::with_capacity(work.len());
    for (rid, rule_qn, tier) in work {
        let verdict = match tier {
            Tier::Derivation => {
                // WI-539 Part 2: a `proof <op>.<clause> by derivation` is a CONTRACT
                // proof, not a rule derivation — its QN names an operation + clause,
                // not a rule. Discharge it against the op's body; any other
                // derivation target is a plain rule SLD derivation (the QN indexes a
                // rule). Bind the classification once (no double `contract_target`).
                if let Some((op_sym, clause)) = contract_target(kb, &rule_qn) {
                    discharge_contract_proof(kb, rid, &rule_qn, op_sym, clause)
                } else {
                    // Map the outcome to either the proved tree hash or a failure
                    // reason, then build + write the verdict in ONE place.
                    let proved = match discharge_by_derivation(kb, &rule_qn, DEFAULT_DERIVATION_DEPTH, 1) {
                        DerivationOutcome::Proved { tree_hash } => Ok(tree_hash),
                        DerivationOutcome::NoDerivation => Err(format!(
                            "no derivation found within depth {DEFAULT_DERIVATION_DEPTH}"
                        )),
                        DerivationOutcome::RuleNotFound => Err("target rule not in KB".to_string()),
                        DerivationOutcome::NoRules => Err("target QN indexes no rules".to_string()),
                    };
                    let (write, verdict) = match proved {
                        Ok(tree_hash) => {
                            let witness = make_sld_witness(kb, &tree_hash);
                            (
                                VerdictWrite::Discharged { witness, solver: "derivation".to_string() },
                                ProofVerdict::Discharged,
                            )
                        }
                        Err(reason) => (
                            VerdictWrite::FailedUnknown { reason: reason.clone() },
                            ProofVerdict::Failed { reason },
                        ),
                    };
                    let wrote = set_proof_result(kb, rid, write);
                    debug_assert!(wrote, "verify_proofs: write-back failed for `{rule_qn}` ({rid:?})");
                    verdict
                }
            }
            Tier::External(tool) => ProofVerdict::Deferred {
                reason: format!("external `by {tool}` — run `anthill prove` (z3 lives downstream of core)"),
            },
            Tier::Open => ProofVerdict::Deferred {
                reason: "open obligation (no `by` clause)".to_string(),
            },
        };
        report.push(ProofReport { rule_qn, verdict });
    }
    report
}

// ── WI-539 Part 2: operation-contract proofs ──────────────────────────
//
// A `proof <op>.ensures by derivation` (proposal 025 §"Proof for operation
// contracts") proves that an operation's BODY satisfies its predicate
// postcondition. The proof side owns the *predicate* `ensures` (a proposition
// over `result`, e.g. `eq(top(result), x)`); a *type* `ensures` (a Sort-headed
// return refinement) is a typing concern, not proved here. Only a CONCRETE
// INLINE body is discharged — an abstract op's `ensures` is a spec axiom that
// callers USE (WI-539 Part 1), and an external-binding body is a deferred
// follow-on; both are left Pending/Deferred, never silently Discharged.

/// The contract clause keywords a `<op>.<clause>` proof target may name — the
/// SINGLE source of truth shared by the loader (which BUILDS the `<op>.<clause>`
/// QN, [`super::load`]`::contract_proof_target_qn`) and this pass (which SPLITS
/// it back, [`contract_target`]), so the two cannot drift on which suffixes mark
/// a contract proof. Each maps to a [`ContractClause`] via [`ContractClause::from_keyword`].
pub(crate) const CONTRACT_CLAUSE_KEYWORDS: [&str; 2] = ["requires", "ensures"];

/// The contract clause a `<op>.<clause>` proof target names.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ContractClause {
    Ensures,
    Requires,
}

impl ContractClause {
    /// The clause for one of [`CONTRACT_CLAUSE_KEYWORDS`]; `None` otherwise.
    fn from_keyword(kw: &str) -> Option<ContractClause> {
        match kw {
            "ensures" => Some(ContractClause::Ensures),
            "requires" => Some(ContractClause::Requires),
            _ => None,
        }
    }
}

/// The placeholder tree hash for a discharged operation-contract proof — the
/// contract twin of [`derivation_tree_hash`], distinct so a witness reads as a
/// contract derivation rather than a plain rule SLD.
pub fn contract_tree_hash(rule_qn: &str) -> String {
    format!("contract-derivation:{rule_qn}")
}

/// If `rule_qn` is a contract-proof target `<op-qn>.ensures` / `<op-qn>.requires`
/// whose `<op-qn>` resolves to an `Operation`, the `(op symbol, clause)`. The
/// loader interns such a QN for the `ProofRecord.rule` field
/// ([`super::load`]`::contract_proof_target_qn`); this is the read-back split.
/// `None` for a plain rule proof (which the rule-derivation path handles).
fn contract_target(kb: &KnowledgeBase, rule_qn: &str) -> Option<(Symbol, ContractClause)> {
    for kw in CONTRACT_CLAUSE_KEYWORDS {
        let Some(op_qn) = rule_qn.strip_suffix(&format!(".{kw}")) else {
            continue;
        };
        // The suffix names a clause; the target is a contract proof iff the prefix
        // resolves to an Operation (else it is a plain rule whose name happens to
        // end in the keyword — leave it to the rule-derivation path).
        let op_sym = kb.try_resolve_symbol(op_qn)?;
        let clause = ContractClause::from_keyword(kw)?;
        return (kb.kind_of(op_sym) == Some(SymbolKind::Operation)).then_some((op_sym, clause));
    }
    None
}

/// Discharge an operation-contract proof and write the verdict back onto its
/// `ProofRecord` (`rid`). Strategy (the body symbolic execution): map each
/// parameter to a fresh GROUND skolem constant and `result` to the operation
/// applied to those skolems, substitute that σ into every predicate `ensures`
/// conjunct, materialize each as an occurrence goal (so its op-calls FOLD via the
/// resolver's `reduce_op_value` body reduction — a flex var would instead delay),
/// seed Γ with the op's predicate `requires` (the preconditions assumed on body
/// entry), and prove each goal from Γ ∪ KB. A universal contract proved for fresh
/// opaque skolems holds for all inputs (the eigenvariable reading). ALL conjuncts
/// must prove for the contract to discharge.
fn discharge_contract_proof(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    rule_qn: &str,
    op_sym: Symbol,
    clause: ContractClause,
) -> ProofVerdict {
    // A `requires`-contract proof has nothing to derive: a precondition is
    // ASSUMED at the call site (WI-539 Part 1, the "use" side), not proved at the
    // definition. Leave it Pending rather than claim a verdict.
    if clause == ContractClause::Requires {
        return ProofVerdict::Deferred {
            reason: "requires-contract proof: a precondition is assumed at the call site \
                     (WI-539 Part 1), not proved at the definition"
                .to_string(),
        };
    }
    let rec = match super::op_info::lookup_operation_info(kb, op_sym) {
        Some(r) => r,
        None => {
            return ProofVerdict::Deferred {
                reason: "no OperationInfo for the contract target".to_string(),
            }
        }
    };
    // Prove only in CONCRETE INLINE form (proposal 025). No body ⇒ abstract op
    // (its `ensures` is a spec axiom callers use) or an external-binding body (a
    // deferred follow-on) — discharged by a concrete provider, never here.
    if rec.body_node.is_none() {
        return ProofVerdict::Deferred {
            reason: "no concrete inline body to prove against (abstract op or external \
                     binding — discharged by a concrete provider)"
                .to_string(),
        };
    }
    // The PREDICATE `ensures` clauses (functor-headed, non-`Sort`) — the proof
    // side. A type `ensures` (Sort-headed return member) is a typing concern.
    let pred_ensures: Vec<Value> = rec
        .ensures
        .iter()
        .filter(|c| is_value_precondition_clause(kb, c))
        .cloned()
        .collect();
    if pred_ensures.is_empty() {
        return ProofVerdict::Deferred {
            reason: "no predicate `ensures` clause to prove (a type `ensures` is checked \
                     by typing, not by a proof)"
                .to_string(),
        };
    }

    // σ: each parameter ↦ a fresh ground skolem `Ref` (so the body grounds to
    // opaque constants the resolver compares definitely, instead of flex vars it
    // would delay on — the eigenvariable reading of a ∀-quantified contract).
    let mut sigma: HashMap<Symbol, TermId> = HashMap::new();
    for (param_sym, _ty) in &rec.params {
        let sk_sym = kb.intern_unique("contract_skolem");
        let sk = kb.alloc(Term::Ref(sk_sym));
        sigma.insert(*param_sym, sk);
    }
    // `result` ↦ the body with its parameters skolemized — the symbolic execution
    // step: `result` IS what the body computes. A pure-value body (`cons(head: x,
    // tail: s)`) grounds `result` outright; an op-call body leaves only the inner
    // call to fold while proving (one fewer fold level than `result ↦ op(args)`).
    let body_occ = rec.body_node.as_ref().expect("body_node present (checked above)");
    let body_term = super::node_occurrence::occurrence_to_term(kb, body_occ);
    let body_sub = substitute_ref_terms(kb, body_term, &sigma);
    let op_qn = kb.qualified_name_of(op_sym).to_string();
    if let Some(result_sym) = kb.try_resolve_symbol(&format!("{op_qn}.result")) {
        sigma.insert(result_sym, body_sub);
    }

    // Seed Γ with the predicate preconditions (assumed on body entry): an
    // `ensures` that follows from a `requires` reads its premise straight from Γ.
    let mut flow = FlowEnv::empty();
    for c in &rec.requires {
        if !is_value_precondition_clause(kb, c) {
            continue;
        }
        for conj in contract_clause_conjuncts(kb, c) {
            let conj = substitute_ref_terms(kb, conj, &sigma);
            if let Some(node) = kb.term_body_to_nodes(&[conj]).into_iter().next() {
                flow = flow.assume(kb, Value::Node(node));
            }
        }
    }

    // Discharge every predicate `ensures` conjunct from Γ ∪ KB. The goal is
    // materialized as an occurrence so its op-calls fold to ground values.
    for c in &pred_ensures {
        let conjuncts = contract_clause_conjuncts(kb, c);
        // A predicate `ensures` that passed the filter (functor-headed, non-Sort)
        // but yields NO goal term is an unsupported value carrier — NOT vacuously
        // true. Fail closed (loud over silent): never fall through to a Discharged
        // verdict for a clause we could not even read as a goal.
        if conjuncts.is_empty() {
            return write_contract_failed(
                kb,
                rid,
                rule_qn,
                "an `ensures` clause could not be read as a goal (unsupported value carrier)",
            );
        }
        for conj in conjuncts {
            let conj = substitute_ref_terms(kb, conj, &sigma);
            let goal = match kb.term_body_to_nodes(&[conj]).into_iter().next() {
                Some(n) => Value::Node(n),
                None => {
                    return write_contract_failed(
                        kb,
                        rid,
                        rule_qn,
                        "could not materialize an `ensures` goal occurrence",
                    )
                }
            };
            if !prove_from_gamma(kb, &flow, &goal) {
                return write_contract_failed(
                    kb,
                    rid,
                    rule_qn,
                    "an `ensures` conjunct is not derivable from the body",
                );
            }
        }
    }

    // All conjuncts proved — discharge with a contract-derivation witness.
    let witness = make_sld_witness(kb, &contract_tree_hash(rule_qn));
    let wrote = set_proof_result(
        kb,
        rid,
        VerdictWrite::Discharged { witness, solver: "contract-derivation".to_string() },
    );
    debug_assert!(wrote, "discharge_contract_proof: write-back failed for `{rule_qn}` ({rid:?})");
    ProofVerdict::Discharged
}

/// The conjuncts of a contract clause `Value` — read the goal term, then split a
/// `conjunction(..)` into its goals (reusing [`clause_conjuncts`]). Carrier-faithful
/// (WI-348): a hash-consed `Value::Term` is the term; a denoted `Value::Node` lowers
/// via `occurrence_to_term`; a value-fact's `Value::Entity` clause (an op with a
/// denoted effect carries its clauses as value carriers — [`super::op_info::clause_list_field`])
/// lowers via the total `value_to_term` boundary (WI-390). Every carrier
/// [`is_value_precondition_clause`] accepts is handled, so an accepted clause never
/// silently yields zero conjuncts (which would otherwise fall through to a false
/// Discharge). A genuinely unlowerable value returns no conjuncts; the caller treats
/// that as a discharge FAILURE, not a vacuous pass.
fn contract_clause_conjuncts(kb: &mut KnowledgeBase, clause: &Value) -> Vec<TermId> {
    let g = match clause {
        Value::Term(t) => *t,
        Value::Node(occ) => super::node_occurrence::occurrence_to_term(kb, occ),
        other => match super::node_occurrence::value_to_term(kb, other) {
            Ok(t) => t,
            Err(_) => return Vec::new(),
        },
    };
    clause_conjuncts(kb, g)
}

/// Write a `Failed(Unknown(reason))` verdict onto a contract `ProofRecord` and
/// return the matching [`ProofVerdict`] — conservative (a non-derivable contract
/// is Failed, never silently Discharged), in ONE place.
fn write_contract_failed(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    rule_qn: &str,
    reason: &str,
) -> ProofVerdict {
    let wrote = set_proof_result(
        kb,
        rid,
        VerdictWrite::FailedUnknown { reason: reason.to_string() },
    );
    debug_assert!(wrote, "write_contract_failed: write-back failed for `{rule_qn}` ({rid:?})");
    ProofVerdict::Failed { reason: reason.to_string() }
}

// ── record readers ───────────────────────────────────────────────────

/// The discharge tier of a `ProofRecord`, read from its `strategy` field.
enum Tier {
    /// `by derivation` — discharged in-process by SLD.
    Derivation,
    /// `by <tool>` (z3, …) — Tier-B, deferred to the cli gate. Carries the
    /// tool name for the report.
    External(String),
    /// No `by` clause — `ProofStrategyOpen`.
    Open,
}

fn classify_tier(kb: &KnowledgeBase, named: &SmallVec<[(Symbol, TermId); 2]>) -> Tier {
    let strategy = match get_named_arg(kb, named, "strategy") {
        Some(t) => t,
        None => return Tier::Open,
    };
    match strategy_tool_name(kb, strategy) {
        Some(name) if name == "derivation" => Tier::Derivation,
        Some(name) => Tier::External(name),
        None => Tier::Open,
    }
}

/// The tool name of a strategy term: `ProofStrategyKind(name: <s>, ..)` → `s`;
/// `ProofStrategyOpen` (a nullary constructor, stored as `Term::Ref` — WI-511)
/// or any other shape → `None`.
fn strategy_tool_name(kb: &KnowledgeBase, strategy: TermId) -> Option<String> {
    let functor = term_functor_sym(kb, strategy)?;
    if kb.qualified_name_of(functor) == "anthill.realization.ProofStrategyOpen" {
        return None;
    }
    match kb.get_term(strategy) {
        Term::Fn { named_args, .. } => read_string_field(kb, named_args, "name"),
        _ => None,
    }
}

/// True if the record's `result` field is `ObligationStatus.Pending` (a nullary
/// constructor, stored as `Term::Ref` — WI-511).
fn result_is_pending(kb: &KnowledgeBase, named: &SmallVec<[(Symbol, TermId); 2]>) -> bool {
    match get_named_arg(kb, named, "result") {
        Some(t) => term_functor_sym(kb, t).is_some_and(|f| {
            kb.qualified_name_of(f) == "anthill.realization.ObligationStatus.Pending"
        }),
        None => false,
    }
}

/// True if the record's `witness` is a kernel-auto-registered shape
/// (ScopeAxiom / Specialization), which is discharged by construction.
fn is_auto_registered(kb: &KnowledgeBase, named: &SmallVec<[(Symbol, TermId); 2]>) -> bool {
    let witness = match get_named_arg(kb, named, "witness") {
        Some(t) => t,
        None => return false,
    };
    let functor = match term_functor_sym(kb, witness) {
        Some(f) => f,
        None => return false,
    };
    let short = kb.qualified_name_of(functor).rsplit('.').next().unwrap_or("");
    short == "ScopeAxiom" || short == "Specialization"
}

/// The functor symbol of a term, reading both the `Fn` form and the bare `Ref`
/// form a nullary constructor canonicalises to (WI-511), plus an unresolved
/// `Ident`. The single funnel every functor read in this module routes through,
/// so a nullary constructor (`Pending`, `ProofStrategyOpen`) is never silently
/// skipped by a `Term::Fn`-only match.
fn term_functor_sym(kb: &KnowledgeBase, tid: TermId) -> Option<Symbol> {
    match kb.get_term(tid) {
        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => Some(*functor),
        _ => None,
    }
}

/// Read a `String`-const named field off a fact's named args.
fn read_string_field(
    kb: &KnowledgeBase,
    named: &SmallVec<[(Symbol, TermId); 2]>,
    key: &str,
) -> Option<String> {
    let tid = get_named_arg(kb, named, key)?;
    match kb.get_term(tid) {
        Term::Const(Literal::String(s)) => Some(s.clone()),
        _ => None,
    }
}
