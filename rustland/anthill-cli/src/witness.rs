//! Proof witnesses (Proposal 030 phase α.3).
//!
//! Rust-side mirror of the `anthill.realization.witness.ProofWitness`
//! schema declared in `stdlib/anthill/realization/witness.anthill`.
//! The kernel checks witnesses, ProofRecords carry them, the CLI
//! produces them on tactic success.
//!
//! This module is intentionally minimal: it carries data, not
//! behaviour. Witness checking (phase β) lives elsewhere; witness
//! storage (phase α.5) writes these into the prove cache and
//! references them by hash from ProofRecord facts.

/// One proof witness per ProofRecord. Tactics produce these on
/// success; the kernel checks them; ProofRecord.witness stores a
/// reference to the produced witness (typically via content-hashed
/// payload in the prove cache).
#[derive(Debug, Clone)]
#[allow(dead_code)] // Constructors will be used as α.3+ wires more dispatch paths
pub enum ProofWitness {
    /// SMT discharge — the certificate is the SMT-LIB document the
    /// backend ran (referenced by content hash; document lives in
    /// the prove cache) plus the verdict and any unsat-core
    /// annotation. Kernel re-runs the document on demand to verify.
    SmtDischarge {
        backend: String,
        logic: String,
        document_hash: String,
        verdict: SmtVerdict,
        core: Option<String>,
    },

    /// SLD derivation — the resolution tree, referenced by content
    /// hash. Replayable; cheap to verify by replaying step-by-step
    /// against the current KB.
    SldDerivation {
        tree_hash: String,
    },

    /// Meta-tactic composition — the tactic dispatched N sub-queries
    /// and AND-combined their verdicts. Recursive: sub-witnesses are
    /// themselves ProofWitness values.
    MetaCompose {
        tactic_name: String,
        sub: Vec<ProofWitness>,
    },

    /// Definitional witness for kernel-derived lemmas: lemmas that
    /// are true by virtue of a scope's declared structure.
    /// `aspect` discriminates which structural feature the witness
    /// rests on — see proposal 030 §Certificate checking semantics.
    ScopeAxiom {
        scope_kind: String,   // "sort" | "operation"
        scope_qn: String,
        aspect: String,       // "requires.<SE-flat>" | "induction" | …
    },

    /// Use-site specialization — combine a parametric ProofRecord
    /// with concrete instance ProofRecords plus a substitution map.
    Specialization {
        parametric: String,
        substitution: Vec<SortBinding>,
        instances: Vec<String>,
    },

    /// User-asserted axiom — explicit trust, no kernel check.
    /// Trust flag propagates through any witness tree that contains
    /// a TrustedAxiom; CLI surfaces the dependency in verdict output.
    TrustedAxiom {
        reason: String,
    },
}

/// The recorded SMT verdict. Re-checked by replay during `anthill check`.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum SmtVerdict {
    Unsat,
    Sat { model_hash: String },
    Unknown { reason: String },
}

/// Substitution entry for `Specialization`. Maps an abstract sort
/// parameter to a concrete sort.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct SortBinding {
    pub abstract_param: String,
    pub concrete_sort: String,
}
