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
// ScopeAxiom / Specialization / TrustedAxiom variants are
// constructed at the Term level in `anthill_core::kb::load` (loader
// emits them as KB facts directly, bypassing this Rust enum). They
// remain in the enum so `to_shape` can mirror the full DTO surface
// for any future serialization path that does originate them in
// Rust — and so the variant set stays in lockstep with
// `cache::WitnessShape`.
#[derive(Debug, Clone)]
#[allow(dead_code)]
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
pub enum SmtVerdict {
    Unsat,
    Sat { model_hash: String },
    Unknown { reason: String },
}

/// Substitution entry for `Specialization`. Maps an abstract sort
/// parameter to a concrete sort. Mirrors `cache::SortBindingDto`-
/// equivalent field set; constructed at the Term level in the
/// loader, never via this Rust struct (loaders bypass the enum).
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct SortBinding {
    pub abstract_param: String,
    pub concrete_sort: String,
}

impl ProofWitness {
    /// Serialize into the `cache::WitnessShape` DTO so the prove
    /// driver can persist the witness as a sidecar that `check`
    /// reads back. WI-124 — proposal 030 witness persistence.
    pub fn to_shape(&self) -> anthill_smt_gen::cache::WitnessShape {
        use anthill_smt_gen::cache::{SmtVerdictDto, WitnessShape};
        match self {
            ProofWitness::SmtDischarge { backend, logic, document_hash, verdict, core } => {
                WitnessShape::SmtDischarge {
                    backend: backend.clone(),
                    logic: logic.clone(),
                    document_hash: document_hash.clone(),
                    verdict: match verdict {
                        SmtVerdict::Unsat => SmtVerdictDto::Unsat,
                        SmtVerdict::Sat { model_hash } => SmtVerdictDto::Sat {
                            model_hash: model_hash.clone(),
                        },
                        SmtVerdict::Unknown { reason } => SmtVerdictDto::Unknown {
                            reason: reason.clone(),
                        },
                    },
                    core: core.clone(),
                }
            }
            ProofWitness::SldDerivation { tree_hash } => {
                WitnessShape::SldDerivation { tree_hash: tree_hash.clone() }
            }
            ProofWitness::MetaCompose { tactic_name, sub } => {
                WitnessShape::MetaCompose {
                    tactic_name: tactic_name.clone(),
                    sub: sub.iter().map(|w| w.to_shape()).collect(),
                }
            }
            ProofWitness::ScopeAxiom { scope_kind, scope_qn, aspect } => {
                WitnessShape::ScopeAxiom {
                    scope_kind: scope_kind.clone(),
                    scope_qn: scope_qn.clone(),
                    aspect: aspect.clone(),
                }
            }
            ProofWitness::Specialization { parametric, substitution, instances } => {
                WitnessShape::Specialization {
                    parametric: parametric.clone(),
                    substitution: substitution.iter()
                        .map(|sb| (sb.abstract_param.clone(), sb.concrete_sort.clone()))
                        .collect(),
                    instances: instances.clone(),
                }
            }
            ProofWitness::TrustedAxiom { reason } => {
                WitnessShape::TrustedAxiom { reason: reason.clone() }
            }
        }
    }
}
