//! `PartialEq.eq` / `neq` IN A RULE BODY'S VALUE SLOT IS ITS `Bool` VALUE (user, 2026-10-30;
//! proposal 068 §1.3, kernel-language §8.3), and so is `struct_eq` (`===`). Found while
//! delivering WI-20261023-HH0HT. They are operations, `-> Bool`, and denote their value as
//! any other operation's call does:
//! `?t <=> (Int64, PartialEq.eq(1, 1))` binds `(Int64, true)`. They were read as goal-only
//! builtins written as data, so the call was kept as the term — `(Int64, eq(1, 1))` in a
//! DEFINITE answer, against 068 §1.2 — and a relation handed one compared the term:
//! `flag(PartialEq.eq(1, 1))` over `fact flag(true)` answered nothing, so `not(...)` over it
//! held. At the top of `<=>` the call was a residual (`unify(?_, eq(1, 1))`), never decided.
//!
//! ## Back-out
//!
//! The `PartialEq.eq` arm of `run_builtin_for_value` (`kb/resolve/evaluate.rs`) made a no-op
//! under a switch, one build (measured 2026-10-30): every row here fails but the control, and
//! so does `wi_k4jgc_evaluation_strategy_test::an_equality_passed_to_a_relation_is_its_value`.
//!
//! CONTROL, green either way by design: `a_goal_only_builtin_written_as_data_stays_the_term`.

use crate::common::{load_kb_with, shown_rows};

const PROGRAM: &str = r#"
namespace test.eqvalue
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Pq
    entity pq(v: Int64)
    operation eq(x: Pq, y: Pq) -> Bool = false
  end
  fact flag(true)

  rule top(?t) :- ?t <=> PartialEq.eq(1, 1)
  rule inTuple(?t) :- ?t <=> (Int64, PartialEq.eq(1, 1))
  rule inList(?t) :- ?t <=> [PartialEq.neq(1, 2), PartialEq.neq(3, 3)]
  rule structural(?t) :- ?t <=> (1 === 1, pq(v: 1) === pq(v: 2))
  rule ownEq(?t) :- ?t <=> (0, PartialEq.eq(pq(v: 1), pq(v: 1)))
  rule tested(?r) :- PartialEq.eq(1, 1) = true, ?r <=> 1
  rule argument(?r) :- flag(PartialEq.eq(1, 1)), ?r <=> 1
  rule refuted(?r) :- not(flag(PartialEq.eq(1, 1))), ?r <=> 1
  rule late(?b) :- ?b <=> (1, PartialEq.eq(?x, 2)), ?x <=> 2
  rule unbound(?b) :- ?b <=> PartialEq.eq(?x, 1)
  rule dataGoal(?t) :- ?t <=> (1, anthill.reflect.nonvar(5))
end
"#;

fn rows(rel: &str) -> Vec<(String, bool)> {
    let mut kb = load_kb_with(PROGRAM);
    shown_rows(&mut kb, &format!("test.eqvalue.{rel}"))
}

fn one(value: &str) -> Vec<(String, bool)> {
    vec![(value.to_string(), true)]
}

/// Its value wherever a value is built: at the top of `<=>`, in a tuple, in a list, through
/// the carrier's own `eq`, which says `false` of identical operands, and structurally.
#[test]
fn an_equality_in_a_value_slot_is_its_value() {
    assert_eq!(rows("top"), one("true"));
    assert_eq!(rows("inTuple"), one("(Int64, true)"));
    assert_eq!(rows("inList"), one("[true, false]"));
    assert_eq!(rows("ownEq"), one("(0, false)"));
    assert_eq!(rows("structural"), one("(true, false)"));
}

/// Where it is read: a comparison's operand, and a goal's argument, which the relation is
/// handed as the value — so a negation over the goal is refuted, not proved.
#[test]
fn an_equality_read_by_a_goal_is_its_value() {
    assert_eq!(rows("tested"), one("1"));
    assert_eq!(rows("argument"), one("1"));
    assert_eq!(rows("refuted"), Vec::<(String, bool)>::new());
}

/// It waits for an operand it reads, and runs once that is bound: definite when a later goal
/// binds it, one conditional row when nothing does.
#[test]
fn an_equality_waits_for_its_operand() {
    assert_eq!(rows("late"), one("(1, true)"));
    let unbound = rows("unbound");
    assert!(
        unbound.len() == 1 && !unbound[0].1,
        "one conditional row: {unbound:?}"
    );
}

/// CONTROL, passing either way by design: a goal-only builtin written as data is not a
/// computation, and stays the term.
#[test]
fn a_goal_only_builtin_written_as_data_stays_the_term() {
    assert_eq!(rows("dataGoal"), one("(1, nonvar(5))"));
}
