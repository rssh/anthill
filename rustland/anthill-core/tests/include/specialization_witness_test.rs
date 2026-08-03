//! Proposal 030 phase α.8 / WI-119 Variant 3 / WI-120 — `provides`
//! discharge emits Specialization-witnessed ProofRecords for each
//! requires-clause of the provided spec.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    crate::common::expect_loaded(load::load_all(&mut kb, &refs, &NullResolver));
    kb
}

fn proof_records(kb: &mut KnowledgeBase) -> Vec<String> {
    // WI-922: found by HEAD FUNCTOR, which is the RESOLVED symbol —
    // `kb.intern(qn)` mints a different one in a disjoint space.
    let sort_sym = kb.try_resolve_symbol("anthill.realization.ProofRecord")
        .expect("resolve anthill.realization.ProofRecord");
    let rules = kb.rules_by_functor(sort_sym);
    let heads: Vec<_> = rules.iter().map(|&r| kb.rule_head(r)).collect();
    let printer = TermPrinter::new(kb);
    let mut out: Vec<String> = heads.into_iter()
        .map(|h| printer.print_term(h))
        .collect();
    out.sort();
    out
}

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
    // The α.6 pass auto-registers <A-qn>.requires.Eq_T for A's
    // requires; the α.8 pass walks the SortProvidesInfo fact for B
    // and emits B.provides.A.Eq_T whose witness is a Specialization
    // referencing A.requires.Eq_T plus the [T = B] substitution.
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
    let mut kb = load_with(src);
    let records = proof_records(&mut kb);
    let r = records.iter()
        .find(|r| r.contains("test.provides_alpha8.B.provides.A.")
                  && r.contains("Specialization"))
        .unwrap_or_else(|| panic!(
            "expected a Specialization-witnessed ProofRecord; saw:\n{records:#?}"
        ));
    assert!(r.contains("Specialization"),
        "witness must be Specialization; got {r}");
    assert!(r.contains("parametric:"),
        "witness must reference a parametric ProofRecord; got {r}");
    assert!(r.contains("substitution:"),
        "witness must include a substitution list; got {r}");
    assert!(r.contains(r#"state_hash: "specialization""#),
        "expected sentinel state_hash; got {r}");
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
    let mut kb = load_with(src);
    let count1 = proof_records(&mut kb).iter()
        .filter(|r| r.contains("test.provides_alpha8_idem.CC.provides."))
        .count();
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let s = std::fs::read_to_string(p).unwrap();
        parse::parse(&s).unwrap()
    }).collect();
    parsed.push(parse::parse(src).unwrap());
    let refs: Vec<_> = parsed.iter().collect();
    crate::common::expect_loaded(load::load_incremental(&mut kb, &refs, &NullResolver));
    let count2 = proof_records(&mut kb).iter()
        .filter(|r| r.contains("test.provides_alpha8_idem.CC.provides."))
        .count();
    assert_eq!(count1, count2,
        "α.8 specialization emission must be idempotent — got {count1} → {count2}");
    assert!(count1 >= 1, "expected at least one Specialization record");
}
