//! Proposal 030 phase α.8 / WI-119 Variant 3 / WI-120 — `provides`
//! discharge emits Specialization-witnessed ProofRecords for each
//! requires-clause of the provided spec.

use crate::common::load_kb_with as load_with;
use crate::common::proof_records_rendered as proof_records;

#[test]
fn provides_clause_emits_specialization_proof_record() {
    // B's `PartialEq`/`Eq` provisions and its `eq` body are not decoration: `A`
    // requires `Eq[T = T]`, so a `B` that provides `A[T = B]` and nothing else
    // is INCOHERENT and the loader says so. WI-966 — the error had been
    // discarded here, and both tests in this file asserted over a KB that never
    // finished loading. Discharging the requirement is what this fixture always
    // meant to describe.
    //
    // Sort A has a requires clause; sort B claims `provides A[T = B]`.
    // The α.6 pass auto-registers <A-qn>.requires.<SE> for A's requires — `<SE>` the
    // required spec's qualified text, `anthill.prelude.Eq[T = <A-qn>.T]`; the α.8 pass
    // walks the SortProvidesInfo fact for B and emits <B-qn>.provides.<A-qn>[T = <B-qn>].<SE>
    // whose witness is a Specialization referencing <A-qn>.requires.<SE> plus the
    // [T = <B-qn>] substitution (WI-20261011-S8CYD).
    let src = r#"
        namespace test.provides_alpha8
          import anthill.prelude.{Bool, PartialEq, Eq}
          sort A
            sort T = ?
            requires anthill.prelude.Eq[T = T]
          end
          sort B
            entity b
            provides PartialEq[T = B]
            provides Eq[T = B]
            provides A[T = B]
            operation eq(x: B, y: B) -> Bool = true
          end
        end
    "#;
    let kb = load_with(src);
    let records = proof_records(&kb);
    let r = records
        .iter()
        .find(|r| {
            r.contains(
                "rule: \"test.provides_alpha8.B.provides.test.provides_alpha8.A[T = \
                 test.provides_alpha8.B].anthill.prelude.Eq[T = test.provides_alpha8.A.T]\"",
            ) && r.contains("Specialization")
        })
        .unwrap_or_else(|| {
            panic!("expected a Specialization-witnessed ProofRecord; saw:\n{records:#?}")
        });
    assert!(
        r.contains("Specialization"),
        "witness must be Specialization; got {r}"
    );
    assert!(
        r.contains(
            "parametric: \"test.provides_alpha8.A.requires.anthill.prelude.Eq[T = \
             test.provides_alpha8.A.T]\""
        ),
        "witness must reference the parametric ProofRecord of A's law; got {r}"
    );
    assert!(
        r.contains(
            "substitution: [SortBinding(abstract_param: \"T\", concrete_sort: \
             \"test.provides_alpha8.B\")]"
        ),
        "witness must say the provision's binding, by the sort's qualified name; got {r}"
    );
    assert!(
        r.contains(r#"state_hash: "specialization""#),
        "expected sentinel state_hash; got {r}"
    );
}

#[test]
fn provides_emission_is_idempotent_across_loads() {
    let src = r#"
        namespace test.provides_alpha8_idem
          import anthill.prelude.{Bool, PartialEq, Eq}
          sort AA
            sort T = ?
            requires anthill.prelude.Eq[T = T]
          end
          sort CC
            entity cc
            provides PartialEq[T = CC]
            provides Eq[T = CC]
            provides AA[T = CC]
            operation eq(x: CC, y: CC) -> Bool = true
          end
        end
    "#;
    let mut kb = crate::common::load_unsealed(&[src]);
    let count1 = proof_records(&kb)
        .iter()
        .filter(|r| r.contains("test.provides_alpha8_idem.CC.provides."))
        .count();
    crate::common::expect_loaded(crate::common::present_all_again(&mut kb, &[src]));
    let count2 = proof_records(&kb)
        .iter()
        .filter(|r| r.contains("test.provides_alpha8_idem.CC.provides."))
        .count();
    assert_eq!(
        count1, count2,
        "α.8 specialization emission must be idempotent — got {count1} → {count2}"
    );
    assert!(count1 >= 1, "expected at least one Specialization record");
}
