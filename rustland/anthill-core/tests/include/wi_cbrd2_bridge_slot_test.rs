//! A RULE-BODY CALL'S SLOT IS ROUTED WHERE ITS RECEIVER'S TYPE PUTS IT (WI-20261105-CBRD2). A
//! call of an operation whose sort requires a spec — `combineBox(b: Self)` in `sort Box` with
//! `requires Combiner[T]` — owes the clause a dictionary for the sort's slot, at the type its
//! receiver's type binds there. The router (`slot_route`) looked for a parameter typed by the
//! slot's binding alone, `T`; `b: Self` is `Box[T = T]`, so it found none and gave the call a
//! read of its own, which nothing filled: the SLD bridge derived the dictionary from the
//! argument's value when the goal ran (`call_op_bridged`). A rule declaring the requirement,
//! `combines_to[A](?b: Box[T = A], ?r) :- Combiner[A], …`, took the bridge's dictionary, not
//! its own; one declaring nothing loaded clean. The slot is now read off the receiver's type:
//! at a declared type parameter it is that guard's dictionary, and at a type a head column
//! reaches that the clause declares nothing at the clause is refused, a rule taking no
//! dictionary it does not declare (060.1 §1, proposal 073 §6.2).
//!
//! The answers are the ones the values gave, so the rows measure the reading
//! (`resolve::bridge_derivations_by_this_thread`) beside them.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch (the slot not read off a parameter's type), then removed.
//! The control is the switch unset: every row passes.
//!
//! * [`a_call_at_a_declared_element_takes_the_clauses_guard`] fails on the count.
//! * [`a_call_at_an_element_the_clause_declares_nothing_at_is_refused`] fails: the clause
//!   loads clean.
//! * [`a_slot_inside_a_parameters_type_is_read_off_the_argument`] fails: the undeclared clause
//!   loads clean.
//!
//! [`a_call_at_a_concrete_element_or_in_an_operation_body_is_unchanged`] passes either way by
//! design. So does `wi_9wvt7_review6_test::a_caught_account_is_read_and_raised_again_is_the_runtimes`:
//! a slot read off a type the clause's typing left open in the body, `?r <=> Error.reify(…)`'s
//! error type, is read when the call runs, as before.

use anthill_core::kb::resolve::bridge_derivations_by_this_thread;

use crate::common::{load_errors_of, load_kb_with, load_stdlib_kb, pattern_answer_counts};

fn src(ns: &str, rule: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end
  sort Tag
    entity tag(n: Int64)
  end
  sort TagCombiner
    provides Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  end
  sort Box
    sort T = ?
    requires Combiner[T]
    entity box(content: T)
    operation combineBox(b: Self) -> T =
      match b
        case box(c) -> combine(c, c)
  end
  import {ns}.Box.{{combineBox}}
{rule}
  rule q(?r) :- combines_to(box(content: tag(n: 5)), ?r)
end
"#
    )
}

/// `f`'s result and the derivations from argument values it made, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = bridge_derivations_by_this_thread();
    let r = f();
    (r, bridge_derivations_by_this_thread() - before)
}

/// `combines_to[A]` declares `Combiner[A]`: the call's slot is that guard's dictionary, which
/// a query and a rule's citation pass, and `combineBox(box(tag(5)))` is `tag(99)`.
#[test]
fn a_call_at_a_declared_element_takes_the_clauses_guard() {
    let ns = "test.cbrd2.slot.d";
    let program = src(
        ns,
        "  rule combines_to[A](?b: Box[T = A], ?r) :- Combiner[A], ?r <=> combineBox(?b)",
    );
    for pattern in [
        format!("{ns}.combines_to({ns}.Box.box(content: {ns}.Tag.tag(n: 5)), {ns}.Tag.tag(n: 99))"),
        format!("{ns}.q({ns}.Tag.tag(n: 99))"),
    ] {
        let mut kb = load_kb_with(&program);
        let (got, derived) = counting(|| pattern_answer_counts(&mut kb, &pattern));
        assert_eq!(derived, 0, "`{pattern}` derived a dictionary from the values");
        assert_eq!(got, (1, 1), "`{pattern}`");
    }
}

/// `combines_to(?b, ?r)` declares nothing, and `?b`'s element is open: refused at load, as a
/// rule-body call at a type the clause declares nothing at is.
#[test]
fn a_call_at_an_element_the_clause_declares_nothing_at_is_refused() {
    let errs = load_errors_of(&src("test.cbrd2.slot.u", "  rule combines_to(?b, ?r) :- ?r <=> combineBox(?b)"));
    assert!(
        errs.len() == 1 && errs[0].contains("a requirement of `Combiner` the clause declares"),
        "{errs:?}"
    );
}

/// The controls: at a concrete element the typer builds the dictionary at load, and an
/// operation body's call is its own business; both answer as before.
#[test]
fn a_call_at_a_concrete_element_or_in_an_operation_body_is_unchanged() {
    let ns = "test.cbrd2.slot.c";
    let mut kb = load_kb_with(&src(
        ns,
        "  rule combines_to(?b: Box[T = Tag], ?r) :- ?r <=> combineBox(?b)\n  \
         operation viaOp() -> Tag = combineBox(box(content: tag(n: 5)))",
    ));
    assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.q({ns}.Tag.tag(n: 99))")), (1, 1));
}

/// The slot of an operation's own `requires` at its type parameter, reached through a list
/// parameter (`total[A](xs: List[T = A]) requires Tagger[T = A]`), is read off the list's
/// element the same way: refused where the clause declares nothing there, the clause's guard
/// where it declares `Tagger[A]`.
#[test]
fn a_slot_inside_a_parameters_type_is_read_off_the_argument() {
    let program = |ns: &str, rule: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List}}
  import anthill.prelude.List.{{cons, nil}}
  sort Tagger
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort IntTagger
    provides Tagger[T = Int64]
    operation tag(x: Int64) -> Int64 = 3
  end
  operation total[A](xs: List[T = A]) -> Int64 requires Tagger[T = A] =
    match xs
      case nil -> 0
      case cons(h, t) -> Tagger.tag(h) + total(t)
{rule}
  rule q(?r) :- t([1, 2], ?r)
end
"#
        )
    };
    let errs = load_errors_of(&program("test.cbrd2.slot.lu", "  rule t(?xs, ?r) :- ?r <=> total(?xs)"));
    assert!(
        errs.len() == 1 && errs[0].contains("a requirement of `Tagger` the clause declares"),
        "{errs:?}"
    );
    let ns = "test.cbrd2.slot.ld";
    let mut kb = load_kb_with(&program(ns, "  rule t[A](?xs: List[T = A], ?r) :- Tagger[A], ?r <=> total(?xs)"));
    let (got, derived) = counting(|| pattern_answer_counts(&mut kb, &format!("{ns}.q(6)")));
    assert_eq!(derived, 0, "`q(6)` derived a dictionary from the values");
    assert_eq!(got, (1, 1), "`q(6)`");
}
