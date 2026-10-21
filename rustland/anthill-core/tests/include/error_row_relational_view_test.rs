//! A BODIED OPERATION WHOSE ROW IS `Error` HAS ITS RELATIONAL VIEWS — the goal `f(args, ?r)`
//! and, for a `Bool` operation, the bare goal `f(args)` answer what the call answers in a
//! value slot (`KnowledgeBase::effect_row_admits_relational_view`).
//!
//! THE DEFECT (found 2026-10-21 while designing WI-20261013-GGXCX): the views admitted an empty
//! or a parametric row only, so over `three() -> Int64 effects {Error} = 3` the goal
//! `three(?r)` had no reading, no clauses, and FAILED — where `?r <=> three()` answers 3 — and
//! `not(three(3))` held. The same for a `Bool` operation, and for a body that raises: its goal
//! failed, so `not(…)` over it proved a falsehood, where the call in a value slot is a
//! conditional answer.
//!
//! BACK-OUT, measured: with `effect_member_is_error` dropped from the gate, every row here
//! fails except `the_value_slot_twin_answers_as_before`, which passes either way by design.
//! An effect other than `Error`, and a host function's row, keep the strict reading; neither
//! is driven here (a host function performing its effect itself is WI-20260926-7D48J's row,
//! `Error` at a host function WI-20260827-NFXPZ's).

const PROGRAM: &str = r#"
namespace errview
  import anthill.prelude.{Int64, Bool, Error, EmptyStream}

  entity oops(why: Int64)

  operation three() -> Int64 effects {Error} = 3
  operation narrow() -> Int64 effects {Error[T = EmptyStream]} = 5
  operation boom() -> Int64 effects {Error[T = oops]} = Error.raise(oops(why: 1))
  operation isPos(n: Int64) -> Bool effects {Error} = n > 0
  operation boomB(n: Int64) -> Bool effects {Error[T = oops]} = Error.raise(oops(why: n))

  rule valueSlot(?r) :- ?r <=> three()
  rule goalForm(?r) :- three(?r)
  rule notGoalForm(?r) :- not(three(3)), ?r <=> 1
  rule appliedRow(?r) :- narrow(?r)
  rule boolView(?r) :- isPos(3), ?r <=> 1
  rule notBoolView(?r) :- not(isPos(3)), ?r <=> 1
  rule raised(?r) :- boom(?r)
  rule notRaised(?r) :- not(boom(3)), ?r <=> 1
  rule notRaisedBool(?r) :- not(boomB(3)), ?r <=> 1
end
"#;

fn kb() -> anthill_core::kb::KnowledgeBase {
    crate::common::load_kb_with(PROGRAM)
}

/// CONTROL, PASSES EITHER WAY: the call in a value slot ran before the change.
#[test]
fn the_value_slot_twin_answers_as_before() {
    assert_eq!(crate::common::one_definite_int(&mut kb(), "errview.valueSlot"), Some(3));
}

#[test]
fn the_goal_form_answers_the_call() {
    assert_eq!(crate::common::one_definite_int(&mut kb(), "errview.goalForm"), Some(3));
}

/// The falsehood: `not(three(3))` held.
#[test]
fn a_negation_over_the_goal_form_fails() {
    let rows = crate::common::query_unary(&mut kb(), "errview.notGoalForm");
    assert!(rows.is_empty(), "`three(3)` holds, so its negation fails, got {rows:?}");
}

/// An applied member, `Error[T = EmptyStream]`, is read by its head.
#[test]
fn an_applied_error_member_is_admitted() {
    assert_eq!(crate::common::one_definite_int(&mut kb(), "errview.appliedRow"), Some(5));
}

#[test]
fn the_bool_view_answers_the_call() {
    let mut kb = kb();
    assert_eq!(crate::common::one_definite_int(&mut kb, "errview.boolView"), Some(1));
    let rows = crate::common::query_unary(&mut kb, "errview.notBoolView");
    assert!(rows.is_empty(), "`isPos(3)` holds, so its negation fails, got {rows:?}");
}

/// A body that raises does not reduce, as in a value slot: its goal is a conditional answer,
/// and a negation over it is no definite truth.
#[test]
fn a_raising_body_is_undecided_and_its_negation_proves_nothing() {
    let mut kb = kb();
    for qn in ["errview.raised", "errview.notRaised", "errview.notRaisedBool"] {
        let rows = crate::common::query_unary(&mut kb, qn);
        assert!(
            !rows.is_empty() && rows.iter().all(|(_, definite)| !definite),
            "{qn}: one conditional answer, got {rows:?}"
        );
    }
}
