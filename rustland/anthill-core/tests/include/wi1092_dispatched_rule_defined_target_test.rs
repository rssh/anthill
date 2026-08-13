//! WI-1092 — a rule-defined operation is runnable when NAMED and not when DISPATCHED.
//!
//! An operation whose only definition is a set of `<=>` rules has no runnable body.
//! Eval knows how to run one anyway: `reduce_apply` checks `cites_a_relation` on a
//! SPELLED functor and hands it to the relation machinery, and a spec-op call left
//! un-pinned is discharged by `eq_bridge_target` / `prove_rule_predicate_value` through
//! ordinary SLD — which is the mechanism WI-580 delivered `List.member` over a
//! rule-defined `eq` on, and which still works.
//!
//! `dispatch_resolved_operation` — the tail every DICTIONARY-threaded dispatch and
//! every `OpRef` apply goes through — has neither. Its WI-818 fall-through classifies
//! such a target through `unrunnable_target_error`, so a call that resolved CORRECTLY
//! to the carrier's own rule-defined member decides nothing, and the caller reads that
//! as `false`. Being more precise about the target is what costs it the answer.
//!
//! PINS THE CURRENT DEFECT. The value asserted below is the WRONG one; the correct
//! answer is stated at the site and is WI-1092's acceptance. Kept green rather than
//! failing so the defect is measured rather than merely described — and so the fix has
//! something to flip.

use anthill_core::eval::Value;

/// A carrier whose `PartialEq` is a rule-defined member, reached two ways in one
/// program.
///
///   * `Holder.same` is generic over `HT` and `requires PartialEq[T = HT]`, so its
///     `PartialEq.eq(a, b)` is DEFERRED to the frame's dictionary. That dictionary
///     resolves to `Color.ceq` — correctly; the provision's `eq = ceq` binding is
///     honoured — and `ceq` then decides nothing.
///   * the control calls `PartialEq.eq(red(), red())` on CONCRETE arguments, with no
///     dictionary anywhere, and gets the right answer.
///
/// The control is the whole test. Without it, `Ok(Int(0))` reads as "these two reds
/// are not equal", which is a defensible thing for a program to say; beside a `1` from
/// the same `eq` on the same values it is unambiguous.
///
/// NOT AVAILABLE as a control: the same program with the `requires` deleted. WI-325
/// refuses the abstract call outright ("missing `requires PartialEq[T = …]` on
/// enclosing sort"), so on this spelling the dictionary is not optional — which is
/// also why the defect cannot be worked around by writing the generic differently.
#[test]
fn a_dispatched_rule_defined_eq_answers_false_where_the_named_one_is_right() {
    let program = |call: &str| {
        format!(
            r#"
namespace wi1092.ruledef
  import anthill.prelude.{{Bool, Int64, Eq, PartialEq}}
  sort Color
    entity red
    entity blue
    operation ceq(a: Color, b: Color) -> Bool
    rule ceq(red, red) <=> true
    rule ceq(blue, blue) <=> true
    rule ceq(red, blue) <=> false
    rule ceq(blue, red) <=> false
    provides PartialEq[T = Color, eq = ceq]
    provides Eq[T = Color]
  end
  sort Holder
    sort HT = ?
    requires PartialEq[T = HT]
    operation same(a: HT, b: HT) -> Bool = PartialEq.eq(a, b)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = if {call} then 1 else 0
  end
end
"#
        )
    };
    let eval = |src: &str| {
        let mut interp = crate::common::interp_for(src);
        interp.call("wi1092.ruledef.Driver.drive", &[Value::Int(0)])
    };

    // CONTROL — the NAMED route: concrete arguments, no dictionary, right answer.
    let control = eval(&program("PartialEq.eq(red(), red())"));
    assert!(
        matches!(control, Ok(Value::Int(1))),
        "control: `red` equals `red` under the carrier's own rule-defined `ceq`, \
         reached with no dictionary — the route WI-580 delivered; got {control:?}"
    );

    // PINS A CURRENT DEFECT — the DISPATCHED route on the same `eq`, same values.
    let dispatched = eval(&program("Holder.same(red(), red())"));
    assert!(
        matches!(dispatched, Ok(Value::Int(0))),
        "CURRENT DEFECT (correct = Ok(Int(1)), the control's answer): a dictionary \
         dispatch resolves to `Color.ceq` and then cannot run it, because \
         `dispatch_resolved_operation` has no relation arm and its WI-818 fall-through \
         reads a claused-but-bodyless target as unrunnable. The program loads clean and \
         nothing is raised. When WI-1092 lands this must assert Ok(Int(1)); got \
         {dispatched:?}"
    );
}
