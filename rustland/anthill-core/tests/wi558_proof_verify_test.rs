//! WI-558 — the proof-verification pass (`kb::proof_verify::verify_proofs`).
//!
//! The loader records a top-level `proof <rule> by <strategy>` as a
//! `ProofRecord` fact with `result: Pending`. WI-538 discharged only *in-body*
//! `by derivation` proofs inline in the typer; top-level proofs were never
//! checked as part of the pipeline. `verify_proofs` walks the Pending records
//! and discharges the `by derivation` ones via the SLD resolver, flipping
//! `result` to `Discharged` (with a real `SldDerivation` witness) or
//! `Failed(Unknown(..))` — never silently `Discharged`. Tier-B (`by z3`) and
//! open obligations are left Pending for the cli gate.

mod common;

use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;

/// The `result`-field functor short name for the ProofRecord whose `rule`
/// QN ends with `rule_suffix` — e.g. `"Discharged"` / `"Failed"` / `"Pending"`.
fn result_variant(kb: &KnowledgeBase, rule_suffix: &str) -> Option<String> {
    let head = proof_record_head(kb, rule_suffix)?;
    let result = named_field(kb, head, "result")?;
    functor_short(kb, result)
}

/// The `witness`-field functor short name for the ProofRecord matching
/// `rule_suffix`.
fn witness_variant(kb: &KnowledgeBase, rule_suffix: &str) -> Option<String> {
    let head = proof_record_head(kb, rule_suffix)?;
    let witness = named_field(kb, head, "witness")?;
    functor_short(kb, witness)
}

fn proof_record_head(kb: &KnowledgeBase, rule_suffix: &str) -> Option<TermId> {
    let record_sym = kb.try_resolve_symbol("anthill.realization.ProofRecord")?;
    for rid in kb.rules_by_functor(record_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head(rid);
        if let Some(rule_tid) = named_field(kb, head, "rule") {
            if let Term::Const(Literal::String(s)) = kb.get_term(rule_tid) {
                if s.ends_with(rule_suffix) {
                    return Some(head);
                }
            }
        }
    }
    None
}

fn named_field(kb: &KnowledgeBase, term: TermId, key: &str) -> Option<TermId> {
    match kb.get_term(term) {
        Term::Fn { named_args, .. } => named_args
            .iter()
            .find(|(s, _)| kb.resolve_sym(*s) == key)
            .map(|(_, v)| *v),
        _ => None,
    }
}

fn functor_short(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    // A nullary constructor (`Pending`) is stored as `Term::Ref` (WI-511), so
    // read both forms.
    let functor = match kb.get_term(term) {
        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => *functor,
        _ => return None,
    };
    Some(
        kb.qualified_name_of(functor)
            .rsplit('.')
            .next()
            .unwrap_or("")
            .to_string(),
    )
}

#[test]
fn top_level_by_derivation_is_discharged_with_real_witness() {
    let mut kb = common::load_kb_with(
        r#"
        namespace test.verify.simple
          entity Light(state: String)
          fact Light(state: "bright")

          rule shines(?b) :- Light(state: ?b)
          proof shines by derivation end
        end
        "#,
    );

    // Pre-pass: the loader recorded it as Pending.
    assert_eq!(
        result_variant(&kb, "shines").as_deref(),
        Some("Pending"),
        "loader should record the proof as Pending"
    );

    let report = verify_proofs(&mut kb);
    let entry = report
        .iter()
        .find(|r| r.rule_qn.ends_with("shines"))
        .expect("a report entry for `shines`");
    assert_eq!(entry.verdict, ProofVerdict::Discharged, "shines should discharge");

    // Post-pass: result flipped to Discharged with an SldDerivation witness.
    assert_eq!(
        result_variant(&kb, "shines").as_deref(),
        Some("Discharged"),
        "result should be flipped to Discharged"
    );
    assert_eq!(
        witness_variant(&kb, "shines").as_deref(),
        Some("SldDerivation"),
        "witness should be a real SldDerivation (not the Pending TrustedAxiom placeholder)"
    );
}

#[test]
fn top_level_by_derivation_that_does_not_derive_is_failed_not_discharged() {
    let mut kb = common::load_kb_with(
        r#"
        namespace test.verify.fail
          entity Light(state: String)
          fact Light(state: "bright")

          rule dark(?x) :- Light(state: ?x), eq(?x, "off")
          proof dark by derivation end
        end
        "#,
    );

    let report = verify_proofs(&mut kb);
    let entry = report
        .iter()
        .find(|r| r.rule_qn.ends_with("dark"))
        .expect("a report entry for `dark`");
    assert!(
        matches!(entry.verdict, ProofVerdict::Failed { .. }),
        "an underivable proof must be Failed, got {:?}",
        entry.verdict
    );

    // Conservative: Failed, never silently Discharged.
    assert_eq!(
        result_variant(&kb, "dark").as_deref(),
        Some("Failed"),
        "result should be Failed, not Discharged"
    );
}

#[test]
fn tier_b_by_z3_is_left_pending_not_silently_discharged() {
    let mut kb = common::load_kb_with(
        r#"
        namespace test.verify.tierb
          entity Light(state: String)
          fact Light(state: "bright")

          rule shines(?b) :- Light(state: ?b)
          proof shines by z3 end
        end
        "#,
    );

    let report = verify_proofs(&mut kb);
    let entry = report
        .iter()
        .find(|r| r.rule_qn.ends_with("shines"))
        .expect("a report entry for `shines`");
    assert!(
        matches!(entry.verdict, ProofVerdict::Deferred { .. }),
        "a `by z3` proof must be Deferred to the cli gate, got {:?}",
        entry.verdict
    );

    // The in-process pass must NOT touch a Tier-B record's result.
    assert_eq!(
        result_variant(&kb, "shines").as_deref(),
        Some("Pending"),
        "Tier-B record must stay Pending (conservative — z3 lives downstream of core)"
    );
}
