//! WI-539 Part 2 / proposal 025 §"Proof for operation contracts" — a
//! `proof <op>.ensures by derivation` that proves an operation's BODY satisfies
//! its PREDICATE postcondition (a proposition over `result`, e.g.
//! `eq(result.value, x)`). The proof-verification pass (`verify_proofs`)
//! skolemizes the parameters, binds `result` to the body (the symbolic-execution
//! step), seeds Γ with the op's predicate `requires`, and discharges each
//! predicate-`ensures` conjunct from Γ ∪ KB.
//!
//! Scope (the focused inline-body slice): a CONCRETE INLINE body whose
//! postcondition reduces by reflexivity, field projection, or a Γ premise. A
//! type `ensures` (Sort-headed return member) is a TYPING concern, not proved
//! here; an ABSTRACT op's `ensures` is a spec axiom callers USE (WI-539 Part 1),
//! left Deferred — never silently Discharged.

mod common;

use anthill_core::kb::proof_verify::{verify_proofs, ProofReport, ProofVerdict};
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;

/// Functor short name of a term, reading both `Fn` and the bare `Ref` a nullary
/// constructor canonicalizes to (WI-511).
fn functor_short(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    let functor = match kb.get_term(term) {
        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => *functor,
        _ => return None,
    };
    Some(kb.qualified_name_of(functor).rsplit('.').next().unwrap_or("").to_string())
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

/// The `ProofRecord` head whose `rule` QN ends with `rule_suffix`.
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

/// The `result`-field functor short name (`Discharged` / `Failed` / `Pending`).
fn result_variant(kb: &KnowledgeBase, rule_suffix: &str) -> Option<String> {
    let head = proof_record_head(kb, rule_suffix)?;
    functor_short(kb, named_field(kb, head, "result")?)
}

/// The `witness`-field functor short name.
fn witness_variant(kb: &KnowledgeBase, rule_suffix: &str) -> Option<String> {
    let head = proof_record_head(kb, rule_suffix)?;
    functor_short(kb, named_field(kb, head, "witness")?)
}

/// The verdict the pass reported for the record whose QN ends with `suffix`.
fn verdict_for(report: &[ProofReport], suffix: &str) -> ProofVerdict {
    report
        .iter()
        .find(|r| r.rule_qn.ends_with(suffix))
        .unwrap_or_else(|| panic!("no report entry ending in `{suffix}`"))
        .verdict
        .clone()
}

#[test]
fn predicate_ensures_by_field_projection_discharges() {
    // `wrap(x) = box(value: x)` with `ensures eq(result.value, x)`. Skolemize
    // `x ↦ c`, bind `result ↦ box(value: c)`; the goal `eq(box(value: c).value,
    // c)` projects to `eq(c, c)` ⇒ proved. The contract discharges, with a real
    // contract-derivation witness (not the Pending placeholder).
    let mut kb = common::load_kb_with(
        r#"
        namespace wi539c.box
          sort Box
            entity box(value: Int64)
            operation wrap(x: Int64) -> Box
              ensures eq(result.value, x)
              = box(value: x)
            proof wrap.ensures by derivation end
          end
        end
        "#,
    );

    assert_eq!(
        result_variant(&kb, "wrap.ensures").as_deref(),
        Some("Pending"),
        "loader records the contract proof as Pending"
    );

    let report = verify_proofs(&mut kb);
    assert_eq!(
        verdict_for(&report, "wrap.ensures"),
        ProofVerdict::Discharged,
        "the body establishes the postcondition — the contract should discharge"
    );
    assert_eq!(
        result_variant(&kb, "wrap.ensures").as_deref(),
        Some("Discharged"),
        "result flipped to Discharged"
    );
    assert_eq!(
        witness_variant(&kb, "wrap.ensures").as_deref(),
        Some("SldDerivation"),
        "a real derivation witness, not the Pending TrustedAxiom placeholder"
    );
}

#[test]
fn reflexive_ensures_discharges() {
    // `ensures eq(result, box(value: x))` with the matching body — `result` binds
    // to exactly that construction, so the goal is reflexive.
    let mut kb = common::load_kb_with(
        r#"
        namespace wi539c.refl
          sort Box
            entity box(value: Int64)
            operation wrap(x: Int64) -> Box
              ensures eq(result, box(value: x))
              = box(value: x)
            proof wrap.ensures by derivation end
          end
        end
        "#,
    );
    let report = verify_proofs(&mut kb);
    assert_eq!(verdict_for(&report, "wrap.ensures"), ProofVerdict::Discharged);
}

#[test]
fn false_ensures_is_failed_not_discharged() {
    // The body yields `result.value = x`, so `ensures eq(result.value, 0)` does
    // NOT hold. Conservative: Failed, never silently Discharged.
    let mut kb = common::load_kb_with(
        r#"
        namespace wi539c.bad
          sort Box
            entity box(value: Int64)
            operation wrap(x: Int64) -> Box
              ensures eq(result.value, 0)
              = box(value: x)
            proof wrap.ensures by derivation end
          end
        end
        "#,
    );
    let report = verify_proofs(&mut kb);
    assert!(
        matches!(verdict_for(&report, "wrap.ensures"), ProofVerdict::Failed { .. }),
        "an unestablished postcondition must be Failed"
    );
    assert_eq!(
        result_variant(&kb, "wrap.ensures").as_deref(),
        Some("Failed"),
        "result should be Failed, not Discharged"
    );
}

#[test]
fn requires_premise_enables_ensures() {
    // `known(?x) :- eq(?x, 0)` — false for a fresh skolem, so `known(c)` is NOT
    // KB-provable. `needs_pre` carries `requires known(x)`, which the pass assumes
    // into Γ; the `ensures known(result)` (result ↦ x) then reads `known(c)`
    // straight from Γ ⇒ discharged. `no_pre` lacks the premise, so the SAME
    // ensures is NOT derivable ⇒ Failed. The contrast shows requires→Γ is
    // load-bearing.
    let mut kb = common::load_kb_with(
        r#"
        namespace wi539c.pre
          rule known(?x) :- eq(?x, 0)
          operation needs_pre(x: Int64) -> Int64
            requires known(x)
            ensures known(result)
            = x
          operation no_pre(x: Int64) -> Int64
            ensures known(result)
            = x
          proof needs_pre.ensures by derivation end
          proof no_pre.ensures by derivation end
        end
        "#,
    );
    let report = verify_proofs(&mut kb);
    assert_eq!(
        verdict_for(&report, "needs_pre.ensures"),
        ProofVerdict::Discharged,
        "the precondition assumed into Γ discharges the postcondition"
    );
    assert!(
        matches!(verdict_for(&report, "no_pre.ensures"), ProofVerdict::Failed { .. }),
        "without the precondition premise the same postcondition is not derivable"
    );
}

#[test]
fn abstract_op_ensures_is_deferred_not_discharged() {
    // An abstract op (no body) `ensures` is a spec axiom that callers USE
    // (WI-539 Part 1), not proved here. Left Deferred / Pending — never silently
    // Discharged (proposal 025: prove only in concrete form).
    let mut kb = common::load_kb_with(
        r#"
        namespace wi539c.abstr
          sort Thing
            entity thing(v: Int64)
            operation describe(t: Thing) -> Int64
              ensures eq(result, result)
            proof describe.ensures by derivation end
          end
        end
        "#,
    );
    let report = verify_proofs(&mut kb);
    assert!(
        matches!(verdict_for(&report, "describe.ensures"), ProofVerdict::Deferred { .. }),
        "an abstract op's ensures has no concrete body to prove against"
    );
    assert_eq!(
        result_variant(&kb, "describe.ensures").as_deref(),
        Some("Pending"),
        "a Deferred contract proof stays Pending (never silently Discharged)"
    );
}
