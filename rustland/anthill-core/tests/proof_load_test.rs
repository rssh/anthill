//! Verifies the loader emits a ProofRecord fact per `proof` block
//! and that its strategy/body fields round-trip the parsed info.

mod common;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = common::stdlib_dir();
    let files = common::collect_anthill_files(&stdlib);

    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
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

fn render_facts_for(kb: &mut KnowledgeBase, sort_qn: &str) -> Vec<String> {
    let sort_term = kb.make_name_term(sort_qn);
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
fn proof_record_is_emitted_with_strategy() {
    let src = r#"
        namespace test.proof_load
          rule lower_violation(?x) :- gt(?x, 0)
          proof lower_violation
            by z3(timeout: 5000, logic: "LRA")
          end
        end
    "#;
    let mut kb = load_with(src);
    let records = render_facts_for(&mut kb, "anthill.realization.ProofRecord");
    assert!(
        !records.is_empty(),
        "expected at least one ProofRecord fact; found:\n  {records:?}"
    );
    let r = records.iter().find(|r| r.contains("lower_violation"))
        .unwrap_or_else(|| panic!("no ProofRecord for lower_violation; saw:\n{records:#?}"));
    assert!(r.contains("ProofStrategyKind"), "no strategy: {r}");
    assert!(r.contains("z3"),                "wrong tool: {r}");
    assert!(r.contains("Pending"),           "should start Pending: {r}");
}

#[test]
fn proof_with_no_strategy_is_open_obligation() {
    let src = r#"
        namespace test.proof_load_open
          rule foo(?x) :- bar(?x)
          proof foo end
        end
    "#;
    let mut kb = load_with(src);
    let records = render_facts_for(&mut kb, "anthill.realization.ProofRecord");
    let r = records.iter().find(|r| r.contains("test.proof_load_open.foo"))
        .unwrap_or_else(|| panic!("no ProofRecord for foo; saw:\n{records:#?}"));
    assert!(r.contains("ProofStrategyOpen"), "open obligation should use ProofStrategyOpen: {r}");
}

#[test]
fn proof_with_query_keeps_text() {
    let src = r#"
        namespace test.proof_load_query
          rule add_comm(?a, ?b) :- eq(?a, ?b)
          proof add_comm
            by z3
            query "(assert true)"
          end
        end
    "#;
    let mut kb = load_with(src);
    let records = render_facts_for(&mut kb, "anthill.realization.ProofRecord");
    let r = records.iter().find(|r| r.contains("add_comm"))
        .unwrap_or_else(|| panic!("no ProofRecord for add_comm; saw:\n{records:#?}"));
    assert!(r.contains("ProofBodyQuery"), "wrong body: {r}");
    assert!(r.contains("(assert true)"),  "query text not retained: {r}");
}

#[test]
fn no_regression_without_proof() {
    let src = r#"
        namespace test.proof_load_none
          rule foo(?x) :- bar(?x)
        end
    "#;
    let mut kb = load_with(src);
    // Should be no ProofRecord facts from this namespace.
    let records = render_facts_for(&mut kb, "anthill.realization.ProofRecord");
    assert!(
        records.iter().all(|r| !r.contains("test.proof_load_none")),
        "no proofs declared, but found: {records:?}"
    );
}
