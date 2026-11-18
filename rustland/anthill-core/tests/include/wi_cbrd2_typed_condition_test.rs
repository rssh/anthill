//! A CONDITION IS COMPARED AT ITS TYPE (WI-20261105-CBRD2, the run-time equality's producers).
//! Two places built an equality goal with no member, an equality no type reached, answered by
//! its operands' values:
//!
//! * A `Bool`-valued expression in goal position is a condition: the call of a `Bool`
//!   operation (`isBig(?n)`), a projection (`box(…).flag`), a nullary operation spelled bare.
//!   The resolver reads it as the goal `eq(<expression>, true)`, now pinned to `Bool`'s own
//!   `eq`: a comparison at `Bool` by construction.
//! * A relation's query (`where`, `join`, `fix` conditions among its goals) is typed when
//!   `Relation.splitFirst` runs it, as `KB.execute` types the query it reads: `eq(c.name,
//!   "alice")` is decided at the type the relation's column holds.
//!
//! The answers are the same either way, the member comparing these operands as their values
//! do: what the rows measure is that no equality is compared with no member
//! (`resolve::untyped_equalities_by_this_thread`), beside the answers.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * The condition's goal built with no class: the three `Bool` rows fail on the count, their
//!   answers unchanged.
//! * The relation's query run untyped: [`a_relation_condition_is_compared_at_its_column`] fails
//!   on the count, its answers unchanged.

use anthill_core::kb::resolve::untyped_equalities_by_this_thread;

use crate::common::{load_kb_with, load_stdlib_kb, query_pattern_term};

const SRC: &str = "namespace test.cbrd2.cond\n  \
    import anthill.prelude.{Int64, Bool}\n  \
    sort Box\n    entity box(n: Int64, flag: Bool)\n  end\n  \
    operation isBig(n: Int64) -> Bool = Int64.gt(n, 3)\n  \
    operation always() -> Bool = true\n  \
    entity Src(n: Int64)\n  \
    fact Src(n: 1)\n  \
    fact Src(n: 5)\n  \
    rule big(?n) :- Src(n: ?n), isBig(?n)\n  \
    rule small(?n) :- Src(n: ?n), not(isBig(?n))\n  \
    rule dottrue(1) :- box(n: 1, flag: true).flag\n  \
    rule dotfalse(1) :- box(n: 1, flag: false).flag\n  \
    rule dotneg(1) :- not(box(n: 1, flag: false).flag)\n  \
    rule bare(1) :- always\nend\n";

/// The definite answers of `pattern` and the equalities compared with no member while it ran,
/// the shared base loaded first so its own load is not counted.
fn answers_counting(kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str) -> (usize, usize) {
    drop(load_stdlib_kb());
    let goal = query_pattern_term(kb, &format!("test.cbrd2.cond.{pattern}"));
    let before = untyped_equalities_by_this_thread();
    let got = kb.resolve(&[goal], &Default::default());
    let untyped = untyped_equalities_by_this_thread() - before;
    (got.iter().filter(|s| s.is_definite()).count(), untyped)
}

/// A `Bool` operation's call as a rule-body goal, and under `not`: `big` keeps the `5` row,
/// `small` the `1` row.
#[test]
fn a_bool_operations_call_as_a_goal_is_compared_at_bool() {
    let mut kb = load_kb_with(SRC);
    for (pattern, want) in [("big(5)", 1), ("big(1)", 0), ("big(?n)", 1), ("small(?n)", 1)] {
        let (got, untyped) = answers_counting(&mut kb, pattern);
        assert_eq!(got, want, "`{pattern}`");
        assert_eq!(untyped, 0, "`{pattern}` compared an equality with no member");
    }
}

/// A projection as a condition, both polarities and under `not`.
#[test]
fn a_projection_as_a_condition_is_compared_at_bool() {
    let mut kb = load_kb_with(SRC);
    for (pattern, want) in [("dottrue(1)", 1), ("dotfalse(1)", 0), ("dotneg(1)", 1)] {
        let (got, untyped) = answers_counting(&mut kb, pattern);
        assert_eq!(got, want, "`{pattern}`");
        assert_eq!(untyped, 0, "`{pattern}` compared an equality with no member");
    }
}

/// A nullary `Bool` operation spelled bare, which the view rebuilds as its application.
#[test]
fn a_bare_nullary_condition_is_compared_at_bool() {
    let mut kb = load_kb_with(SRC);
    let (got, untyped) = answers_counting(&mut kb, "bare(1)");
    assert_eq!(got, 1);
    assert_eq!(untyped, 0, "`bare(1)` compared an equality with no member");
}

const RELATIONS: &str = r#"
namespace test.cbrd2.relc
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where, join}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)
  sort Membership
    entity member(who: String, dept: String)
  end
  fact member(who: "alice", dept: "eng")
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  rule member_row(?who, ?dept) :- member(who: ?who, dept: ?dept)
  operation whereAlice() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> eq(c.age, 30)).takeN(5)
  operation joined() -> List[(name: String, age: Int64, who: String, dept: String)] effects Error =
    person_row.join(member_row, lambda (c, q) -> eq(c.name, q.who)).takeN(5)
  operation fixed() -> List[(name: String)] effects Error =
    let rel = person_row
    let f = rel.fix(age: 25)
    f.takeN(5)
end
"#;

/// `where`, `join` and `fix` drained: each keeps one row, its condition compared at the
/// relation's column type.
#[test]
fn a_relation_condition_is_compared_at_its_column() {
    let mut interp = crate::common::interp_for(RELATIONS);
    let mut untyped = Vec::new();
    for (op, rows) in [("whereAlice", 1), ("joined", 1), ("fixed", 1)] {
        let before = untyped_equalities_by_this_thread();
        let v = interp
            .call(&format!("test.cbrd2.relc.{op}"), &anthill_core::eval::HostValue::all(&[])).map(|h| h.value)
            .unwrap_or_else(|e| panic!("`{op}` runs: {e:?}"));
        untyped.push((op, untyped_equalities_by_this_thread() - before));
        assert_eq!(crate::common::list_heads(&v).len(), rows, "`{op}`");
    }
    assert!(
        untyped.iter().all(|(_, n)| *n == 0),
        "equalities compared with no member: {untyped:?}"
    );
}
