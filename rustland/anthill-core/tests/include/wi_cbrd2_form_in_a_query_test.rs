//! A CALL IN A QUERY'S COMPOUND FORM IS TYPED (WI-20261105-CBRD2; proposal 073 §1, §6.2). A query
//! is typed where it is read (`load::convert_query_terms` → `typing::route_query_goals`), a goal
//! that calls a spec operation owing an instance typed as a rule body's is. A resolver builtin
//! owes none (`owes_an_instance`): the builtin answers its goal at every carrier. So
//! `6 <=> (let a = 5  a + 1)` was typed nowhere — its one call, `Additive.add`, a builtin's — and
//! the interpreter, which evaluates the form and no builtin answers in, dispatched `Additive.add`
//! to `Int64.add` from the value (`resolve::value_dispatches_by_this_thread`; the gate's one such
//! event outside the rule bodies, `wi_y6qw2`'s compound expression).
//!
//! Inside a compound form — a `let`, an `if`, a `match`, a `lambda` — a spec operation's call owes
//! an instance, a builtin's or one a host binding answers elsewhere included
//! (`rule_goal_routes::calls_an_operation_owing_a_dictionary`), and the goal is typed as the same
//! form in a rule body is: `a + 1` is `Int64.add`'s call.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch, then removed. The control is the switch unset: every row
//! passes.
//!
//! * A call in a form not counted: [`a_call_in_a_querys_form_is_typed`] fails at the `let`, one
//!   dispatch from the value; the answers stand.
//! * [`the_same_form_in_a_rule_body_is_typed_already`] passes either way: the control, the rule
//!   body's walk typing the form whole.

use anthill_core::kb::resolve::{value_dispatches_by_this_thread, ResolveConfig};

use crate::common::{load_kb_with, load_stdlib_kb, query_pattern_term, query_unary};

const PROGRAM: &str = "namespace test.cbrd2.qf\n  import anthill.prelude.{Int64}\n  \
                       rule six(?r) :- ?r <=> (let a = 5\n    a + 1)\nend\n";

/// `f`'s result and the dispatches from a value during it, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = value_dispatches_by_this_thread();
    let r = f();
    (r, value_dispatches_by_this_thread() - before)
}

/// The query's answers: (all, definite).
fn holds(kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str) -> (usize, usize) {
    let goal = query_pattern_term(kb, pattern);
    let (solutions, _) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    (solutions.len(), solutions.iter().filter(|s| s.residual.is_empty()).count())
}

/// A `let`, an `if` and a `match` written in a query each hold once, definitely, with nothing
/// dispatched from a value.
#[test]
fn a_call_in_a_querys_form_is_typed() {
    let mut kb = load_kb_with(PROGRAM);
    for pattern in [
        "6 <=> (let a = 5  a + 1)",
        "10 <=> (if 1 = 1 then 10 else 20)",
        "100 <=> (match 1 case 1 -> 100 case _ -> 200)",
    ] {
        let (answers, dispatches) = counting(|| holds(&mut kb, pattern));
        assert_eq!(answers, (1, 1), "{pattern}");
        assert_eq!(dispatches, 0, "{pattern}: a member found from the value");
    }
}

/// The same `let` in a rule body answers `6`, its `a + 1` typed with the form. Passes either way.
#[test]
fn the_same_form_in_a_rule_body_is_typed_already() {
    let mut kb = load_kb_with(PROGRAM);
    let (rows, dispatches) = counting(|| query_unary(&mut kb, "test.cbrd2.qf.six"));
    assert_eq!(rows.len(), 1);
    assert!(matches!(rows[0], (anthill_core::eval::Value::Int(6), true)), "{rows:?}");
    assert_eq!(dispatches, 0);
}
