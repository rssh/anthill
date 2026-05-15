//! Proposal 030 phase α.6 — auto-registration of `requires` clauses
//! as ProofRecord facts with `ScopeAxiom` witnesses.


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
fn requires_clause_emits_scope_axiom_proof_record() {
    let src = r#"
        namespace test.scope_axiom
          export A
          sort A
            requires anthill.prelude.Eq[T = A]
          end
        end
    "#;
    let mut kb = load_with(src);
    let records = proof_records(&mut kb);
    let r = records.iter()
        .find(|r| r.contains("test.scope_axiom.A.requires.") && r.contains("ScopeAxiom"))
        .unwrap_or_else(|| panic!(
            "expected a ScopeAxiom-witnessed ProofRecord for sort A; saw:\n{records:#?}"
        ));
    assert!(r.contains(r#"scope_kind: "sort""#),
        "expected scope_kind: \"sort\"; got {r}");
    assert!(r.contains("test.scope_axiom.A"),
        "expected scope_qn referencing the requiring sort; got {r}");
    assert!(r.contains(r#"aspect: "requires."#),
        "expected aspect prefix \"requires.\"; got {r}");
    assert!(r.contains(r#"state_hash: "scope-axiom""#),
        "expected sentinel state_hash for scope-axiom record; got {r}");
}

#[test]
fn auto_registration_is_idempotent_across_loads() {
    let src = r#"
        namespace test.scope_axiom_idem
          export A
          sort A
            requires anthill.prelude.Eq[T = A]
          end
        end
    "#;
    let mut kb = load_with(src);
    let count1 = proof_records(&mut kb).iter()
        .filter(|r| r.contains("test.scope_axiom_idem.A.requires."))
        .count();
    // A second load of the same source on the same KB must not
    // duplicate the auto-registered ProofRecord.
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
        .filter(|r| r.contains("test.scope_axiom_idem.A.requires."))
        .count();
    assert_eq!(count1, count2,
        "auto-registration should be idempotent — got {count1} → {count2}");
    assert_eq!(count1, 1, "expected exactly one auto-registered record");
}
