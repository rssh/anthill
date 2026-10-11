//! Proposal 030 phase α.7 — auto-registration of induction
//! principles as ProofRecord facts with `ScopeAxiom(aspect:
//! "induction")` witnesses.

use crate::common::load_kb_with as load_with;
use crate::common::proof_records_rendered as proof_records;

#[test]
fn enum_sort_emits_induction_proof_record() {
    let src = r#"
        namespace test.induction_axiom
          enum Color
            entity Red
            entity Green
            entity Blue
          end
        end
    "#;
    let kb = load_with(src);
    let records = proof_records(&kb);
    let r = records
        .iter()
        .find(|r| r.contains("test.induction_axiom.Color.induction") && r.contains("ScopeAxiom"))
        .unwrap_or_else(|| {
            panic!("expected an induction ProofRecord for enum Color; saw:\n{records:#?}")
        });
    assert!(
        r.contains(r#"scope_kind: "sort""#),
        "expected scope_kind: \"sort\"; got {r}"
    );
    assert!(
        r.contains(r#"aspect: "induction""#),
        "expected aspect: \"induction\"; got {r}"
    );
    assert!(
        r.contains(r#"state_hash: "scope-axiom""#),
        "expected sentinel state_hash; got {r}"
    );
}

#[test]
fn induction_registration_is_idempotent_across_loads() {
    let src = r#"
        namespace test.induction_idem
          enum Mode
            entity One
            entity Two
          end
        end
    "#;
    let mut kb = crate::common::load_unsealed(&[src]);
    let count1 = proof_records(&kb)
        .iter()
        .filter(|r| r.contains("test.induction_idem.Mode.induction"))
        .count();
    // Re-load: idempotence must dedupe.
    crate::common::expect_loaded(crate::common::present_all_again(&mut kb, &[src]));
    let count2 = proof_records(&kb)
        .iter()
        .filter(|r| r.contains("test.induction_idem.Mode.induction"))
        .count();
    assert_eq!(
        count1, count2,
        "induction auto-registration must be idempotent — got {count1} → {count2}"
    );
    assert_eq!(count1, 1, "expected exactly one induction record");
}
