//! Proposal 030 phase α.8 / WI-119 Variant 3 / WI-120 — `provides`
//! discharge emits Specialization-witnessed ProofRecords for each
//! requires-clause of the provided spec.

mod common;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = common::stdlib_dir();
    let files = common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

fn proof_records(kb: &mut KnowledgeBase) -> Vec<String> {
    let sort_term = kb.make_name_term("anthill.realization.ProofRecord");
    let rules = kb.by_sort(sort_term);
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
    // Sort A has a requires clause; sort B claims `provides A[T = B]`.
    // The α.6 pass auto-registers <A-qn>.requires.Eq_T for A's
    // requires; the α.8 pass walks the SortProvidesInfo fact for B
    // and emits B.provides.A.Eq_T whose witness is a Specialization
    // referencing A.requires.Eq_T plus the [T = B] substitution.
    let src = r#"
        namespace test.provides_alpha8
          export A, B
          sort A
            sort T = ?
            requires anthill.prelude.Eq[T = T]
          end
          sort B
            provides A[T = B]
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
          export AA, CC
          sort AA
            sort T = ?
            requires anthill.prelude.Eq[T = T]
          end
          sort CC
            provides AA[T = CC]
          end
        end
    "#;
    let mut kb = load_with(src);
    let count1 = proof_records(&mut kb).iter()
        .filter(|r| r.contains("test.provides_alpha8_idem.CC.provides."))
        .count();
    let stdlib = common::stdlib_dir();
    let files = common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let s = std::fs::read_to_string(p).unwrap();
        parse::parse(&s).unwrap()
    }).collect();
    parsed.push(parse::parse(src).unwrap());
    let refs: Vec<_> = parsed.iter().collect();
    let _ = load::load_incremental(&mut kb, &refs, &NullResolver);
    let count2 = proof_records(&mut kb).iter()
        .filter(|r| r.contains("test.provides_alpha8_idem.CC.provides."))
        .count();
    assert_eq!(count1, count2,
        "α.8 specialization emission must be idempotent — got {count1} → {count2}");
    assert!(count1 >= 1, "expected at least one Specialization record");
}
