//! WI-20260911-SXZ3G — A RELATION ANSWERS IN CLAUSE ORDER.
//!
//! The discrimination tree keeps a node's edges in a std `HashMap`, seeded per map instance, so
//! a goal with a VARIABLE at an indexed position got its candidates in an order that changed from
//! run to run: map-colouring's three `palette` facts, declared red, green, blue, answered in four
//! orders over six CLI runs. They are now sorted by `RuleId`, the order the clauses were asserted
//! in (`KnowledgeBase::query_view`, facts before rules and each group in clause order;
//! `query_fact_heads` in clause order) — which WI-20261115-YR3N7's domain needs too: an unbound
//! value matches every head of a derived `fill`, and generation must take them in the order the
//! derivation writes them.
//!
//! The constructors are DECLARED a, b, c and the facts ASSERTED c, a, b, so neither the symbols'
//! order nor the map's is the answer; two KBs are built in one process, two maps with two seeds.
//!
//! BACK-OUT, measured 2026-11-18 (axis [S] of `wi_yr3n7_domain_check_test`'s table): the sort
//! key back to facts-before-rules alone fails `facts_answer_in_clause_order` and
//! `the_order_holds_through_a_nested_walk`, and ten rows of the domain suites, whose derived
//! `fill` is a clause per constructor since YR3N7. The CONTROLS pass either way BY DESIGN: a
//! BOUND position never walks the map (`a_bound_position_answers_one_row`), and the COUNT is three
//! whatever the order. Scaland's `ClauseOrderTest` is this file on that carrier, measured the
//! same way.

use anthill_core::eval::Value;

use crate::common::{constructor_qn, load_kb_with, query_unary};

const SRC: &str = r#"
namespace sxz3g
  sort L
    entity a
    entity b
    entity c
  end
  fact p(c)
  fact p(a)
  fact p(b)
  fact n(3)
  fact n(1)
  fact n(2)
  fact q(k: 2, v: 7)
  fact q(k: 1, v: 5)
  fact q(k: 2, v: 6)
  fact q(k: 1, v: 8)
  rule qk(?k) :- q(k: ?k, v: ?)
  rule qv(?v) :- q(k: ?, v: ?v)
end
"#;

fn names(kb: &anthill_core::kb::KnowledgeBase, rows: &[(Value, bool)]) -> Vec<String> {
    rows.iter()
        .map(|(v, _)| {
            let qn = constructor_qn(kb, v);
            qn.rsplit('.').next().unwrap_or(&qn).to_string()
        })
        .collect()
}

fn ints(rows: &[(Value, bool)]) -> Vec<i64> {
    rows.iter()
        .map(|(v, _)| match v {
            Value::Int(n) => *n,
            other => panic!("an integer row, got {other:?}"),
        })
        .collect()
}

/// Three facts answer in the order they were asserted, on two independently built KBs. FAILS
/// under the back-out.
#[test]
fn facts_answer_in_clause_order() {
    for _ in 0..2 {
        let mut kb = load_kb_with(SRC);
        let rows = query_unary(&mut kb, "sxz3g.p");
        assert_eq!(names(&kb, &rows), ["c", "a", "b"]);
        assert_eq!(ints(&query_unary(&mut kb, "sxz3g.n")), [3, 1, 2]);
    }
}

/// Through a NESTED walk — a variable at both of a fact's positions — the rows still come in
/// clause order, not grouped by the first position's edge (`7, 6, 5, 8` or `5, 8, 7, 6`). A
/// query answers once per distinct answer (§8.3), so `qk` is `2, 1`, each at its first proof.
/// FAILS under the back-out.
#[test]
fn the_order_holds_through_a_nested_walk() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(ints(&query_unary(&mut kb, "sxz3g.qv")), [7, 5, 6, 8]);
    assert_eq!(ints(&query_unary(&mut kb, "sxz3g.qk")), [2, 1]);
}

/// CONTROL, passing either way by design: a bound position is one lookup, no walk.
#[test]
fn a_bound_position_answers_one_row() {
    let mut kb = load_kb_with(SRC);
    let goal = crate::common::query_pattern_term(&mut kb, "sxz3g.p(sxz3g.L.b)");
    let sols = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
    assert_eq!(sols.len(), 1);
}
