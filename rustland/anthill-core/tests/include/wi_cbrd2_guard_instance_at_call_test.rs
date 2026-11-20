//! A CALL'S GUARD READS ITS ARGUMENT AS THE INSTANCE THE CALL MAKES (WI-20261105-CBRD2; proposal
//! 073 §2). At a call such as `head(cons(7, nil))` the typer decides the callee's effect guard,
//! `Error[EmptyStream] :- isEmpty(s)`, at the call's argument: it proves or refutes
//! `isEmpty(cons(7, nil))` (`refute_guard`, `prove_from_gamma`), and drops the effect where the
//! guard is refuted. `isEmpty` takes `s: Self` of `Stream`, a sort whose values are instances,
//! and the goal handed the resolver held the plain list: the bridge that evaluated it found
//! `List`'s `Stream` dictionary from the list's own sort (`Interpreter::pair_by_own_sort`;
//! `resolve::value_pairings_by_this_thread`). 164 of the gate's 201 pairings were these.
//!
//! The guard's goal at the call now pairs each such argument with its sort's dictionary, as a
//! rule body's call is paired at load (`rule_goal_routes::pack_calls_under`): at the type the
//! call gave an argument whose value says nothing of it until it runs (`listOf(7)`), and at a
//! type its element leaves open (`[]`'s `List[T = ?]`) where the provision reads nothing of the
//! element (`List provides Stream`). An argument naming a parameter of the caller is left as it
//! is: the goal over it is decided by what the caller's branch knows of that parameter
//! (WI-567), and never evaluated.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every row
//! passes; every verdict stands under each.
//!
//! * The guard's goal left unpaired: every row fails on the pairings, one per guard decided.
//! * The call's types for its arguments not read (`known`):
//!   [`an_argument_the_call_typed_is_paired_at_its_type`] fails, `listOf(7)` left unpaired.
//! * A type its element leaves open not built at: [`an_empty_list_at_a_typed_parameter_is_paired_too`]
//!   fails, `[]` left unpaired.
//! * An argument naming a parameter paired too: `wi567_flow_guard_discharge_test`'s
//!   `else_branch_is_empty_discharges`, `then_branch_not_is_empty_discharges` and
//!   `a_discharged_call_still_evaluates` fail, `isEmpty(Instance(d, xs))` matching no fact the
//!   branch knows of `xs`; these rows pass unchanged.

use anthill_core::kb::resolve::value_pairings_by_this_thread;

use crate::common::{load_errors_of, load_stdlib_kb};

/// `f`'s result and the pairings from a value's own sort during it, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = value_pairings_by_this_thread();
    let r = f();
    (r, value_pairings_by_this_thread() - before)
}

fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, Option, EmptyStream, Error}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Stream.{{head, tail, isEmpty}}
  sort Use
{body}
  end
end
"#
    )
}

/// `head` of a non-empty list owes nothing — its guard is refuted at the list — and of the
/// tail of a one-element list owes `Error[EmptyStream]`; each decided with nothing found from a
/// value.
#[test]
fn a_guard_at_a_call_pairs_its_argument() {
    let (errors, pairings) = counting(|| {
        load_errors_of(&program(
            "test.cbrd2.gia.ok",
            "    operation first() -> Int64 = head(cons(7, nil))\n    \
             operation third() -> Int64 = head(tail(tail(cons(1, cons(2, cons(7, nil))))))",
        ))
    });
    assert_eq!(errors, Vec::<String>::new(), "each guard refuted at its argument");
    assert_eq!(pairings, 0, "a dictionary found from a value's own sort");
    let (errors, pairings) = counting(|| {
        load_errors_of(&program("test.cbrd2.gia.owes", "    operation past() -> Int64 = head(tail(cons(7, nil)))"))
    });
    assert!(
        errors.iter().any(|e| e.contains("undeclared effect") && e.contains("EmptyStream")),
        "`head` of an empty tail owes `Error[EmptyStream]`: {errors:?}"
    );
    assert_eq!(pairings, 0, "a dictionary found from a value's own sort");
}

/// `[]` handed to `xs: List[T = Int64]`: the empty list alone leaves its element open, and the
/// call's type for it pairs it; `head([])` owes `Error[EmptyStream]`.
#[test]
fn an_empty_list_at_a_typed_parameter_is_paired_too() {
    let (errors, pairings) =
        counting(|| load_errors_of(&program("test.cbrd2.gia.empty", "    operation f() -> Int64 = head([])")));
    assert!(
        errors.iter().any(|e| e.contains("undeclared effect") && e.contains("EmptyStream")),
        "`head([])` owes `Error[EmptyStream]`: {errors:?}"
    );
    assert_eq!(pairings, 0, "a dictionary found from a value's own sort");
}

/// An argument that is an expression — `listOf(7)`, a call — has the type the call gave it, which
/// nothing in it says until it runs: `head(listOf(7))` pairs it at `List[T = Int64]`, and the
/// guard, refuted where the call runs to `cons(7, nil)`, drops `Error[EmptyStream]`.
#[test]
fn an_argument_the_call_typed_is_paired_at_its_type() {
    let (errors, pairings) = counting(|| {
        load_errors_of(&program(
            "test.cbrd2.gia.call",
            "    operation listOf(n: Int64) -> List[T = Int64] = cons(n, nil)\n    \
             operation f() -> Int64 = head(listOf(7))",
        ))
    });
    assert_eq!(errors, Vec::<String>::new(), "the guard refuted at the call's value");
    assert_eq!(pairings, 0, "a dictionary found from a value's own sort");
}
