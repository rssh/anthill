//! Proposal 030 phase α.7 — auto-registration of induction
//! principles as ProofRecord facts with `ScopeAxiom(aspect:
//! "induction")` witnesses.


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
fn enum_sort_emits_induction_proof_record() {
    let src = r#"
        namespace test.induction_axiom
          export Color
          enum Color
            entity Red
            entity Green
            entity Blue
          end
        end
    "#;
    let mut kb = load_with(src);
    let records = proof_records(&mut kb);
    let r = records.iter()
        .find(|r| r.contains("test.induction_axiom.Color.induction") && r.contains("ScopeAxiom"))
        .unwrap_or_else(|| panic!(
            "expected an induction ProofRecord for enum Color; saw:\n{records:#?}"
        ));
    assert!(r.contains(r#"scope_kind: "sort""#),
        "expected scope_kind: \"sort\"; got {r}");
    assert!(r.contains(r#"aspect: "induction""#),
        "expected aspect: \"induction\"; got {r}");
    assert!(r.contains(r#"state_hash: "scope-axiom""#),
        "expected sentinel state_hash; got {r}");
}

#[test]
fn induction_registration_is_idempotent_across_loads() {
    let src = r#"
        namespace test.induction_idem
          export Mode
          enum Mode
            entity One
            entity Two
          end
        end
    "#;
    let mut kb = load_with(src);
    let count1 = proof_records(&mut kb).iter()
        .filter(|r| r.contains("test.induction_idem.Mode.induction"))
        .count();
    // Re-load: idempotence must dedupe.
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let s = std::fs::read_to_string(p).unwrap();
        parse::parse(&s).unwrap()
    }).collect();
    parsed.push(parse::parse(src).unwrap());
    let refs: Vec<_> = parsed.iter().collect();
    let _ = load::load_incremental(&mut kb, &refs, &NullResolver);
    let count2 = proof_records(&mut kb).iter()
        .filter(|r| r.contains("test.induction_idem.Mode.induction"))
        .count();
    assert_eq!(count1, count2,
        "induction auto-registration must be idempotent — got {count1} → {count2}");
    assert_eq!(count1, 1, "expected exactly one induction record");
}
