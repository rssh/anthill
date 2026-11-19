//! A RULE OF A SORT HOLDS THE REQUIREMENTS ITS SORT STATES, at an instance built over the
//! sort's parameters (WI-20261105-CBRD2; kernel-language §5.3, "as the sort's operations do").
//! In `sort Box requires PartialEq[T = T]`, `rule twin(?x: Self, ?y: Self) :- ?y = ?x` compares
//! two `Box[T = T]`s: `Box`'s derived equality over the `PartialEq[T = T]` the sort requires. A
//! call at the parameter itself, `Conv.conv(?x: T, …)`, read the sort's requirement already
//! (`call_read_is_the_sorts_requirement`). A call at an instance OVER it took a read of its own
//! that no citation fills, and found the provider from the boxes' values when it ran
//! (`resolve::value_reads_by_this_thread`).
//!
//! The clause now reads the sort's requirement at the parameter as it reads a guard
//! (`sort_requirements_at_slot`, the form `add_sort_requirement_read` gives a requirement a
//! goal hands on), and the call takes the dictionary the provisions build over that read
//! (`composed_from_guards`). A citation fills the read as it fills any guard at a typed head.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch, then removed. The control is the switch unset: every row
//! passes.
//!
//! * [`a_sort_rule_composes_the_sorts_requirement`] fails on the reads, one per goal; every
//!   verdict stands.
//! * [`a_bracketed_citation_is_the_control`] passes either way: a citation whose bracket fixes
//!   the parameter hands the clause what it reads.
//! * [`a_citation_leaving_the_parameter_open_is_refused`] fails with HEAD's source: the goal
//!   loads, the call's read left to the values.

use anthill_core::kb::resolve::value_reads_by_this_thread;

use crate::common::{load_kb_with, load_stdlib_kb, pattern_answer_counts};

/// `f`'s result and the reads for a call it answered from a value, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = value_reads_by_this_thread();
    let r = f();
    (r, value_reads_by_this_thread() - before)
}

const BOX: &str = r#"
namespace test.cbrd2.sortreq
  import anthill.prelude.{Int64, List, Option, PartialEq}
  import anthill.prelude.Option.{some}
  sort Box
    sort T = ?
    entity box(v: T)
    requires PartialEq[T = T]
    rule twin(?x: Self, ?y: Self) :- ?y = ?x
    rule twinOpt(x: Option[T = Self], y: Option[T = Self]) :- y = x
  end
  rule ints(1) :- Box.twin(box(v: 1), box(v: 1))
  rule apart(1) :- Box.twin(box(v: 1), box(v: 2))
  rule opts(1) :- Box.twinOpt(some(box(v: 1)), some(box(v: 1)))
  rule empties(1) :- Box[T = List[T = Int64]].twin(box(v: []), box(v: []))
end
"#;

/// The equality at `Self` and at `Option[T = Self]`, through a rule goal and asked as a query:
/// each verdict the values give, nothing read from them.
#[test]
fn a_sort_rule_composes_the_sorts_requirement() {
    let mut kb = load_kb_with(BOX);
    let ns = "test.cbrd2.sortreq";
    for (query, holds) in [
        (format!("{ns}.ints(?r)"), true),
        (format!("{ns}.apart(?r)"), false),
        (format!("{ns}.opts(?r)"), true),
        (format!("{ns}.Box.twin({ns}.Box.box(v: 3), {ns}.Box.box(v: 3))"), true),
        (format!("{ns}.Box.twin({ns}.Box.box(v: 3), {ns}.Box.box(v: 4))"), false),
    ] {
        let (answers, reads) = counting(|| pattern_answer_counts(&mut kb, &query));
        assert_eq!(answers, if holds { (1, 1) } else { (0, 0) }, "{query}");
        assert_eq!(reads, 0, "{query}: a dictionary read off the values");
    }
}

/// `Box[T = List[T = Int64]].twin(box(v: []), box(v: []))`: the bracket fixes the element the
/// empty lists leave open. Passes either way (the module doc).
#[test]
fn a_bracketed_citation_is_the_control() {
    let mut kb = load_kb_with(BOX);
    let (answers, reads) = counting(|| pattern_answer_counts(&mut kb, "test.cbrd2.sortreq.empties(?r)"));
    assert_eq!(answers, (1, 1));
    assert_eq!(reads, 0);
}

/// A goal citing the rule with its columns untyped, `rule open(?a, ?b) :- Box.twin(?a, ?b)`,
/// fixes no `T`, and no caller can pass the requirement the clause reads: refused at load,
/// naming `PartialEq`, as a goal of a rule's guard at an open type is (§5.3).
#[test]
fn a_citation_leaving_the_parameter_open_is_refused() {
    let src = BOX.replace("  rule empties(1)", "  rule open(?a, ?b) :- Box.twin(?a, ?b)\n  rule empties(1)");
    let errors = crate::common::load_errors_of(&src);
    assert!(
        errors.iter().any(|e| e.contains("open.body") && e.contains("a requirement of `PartialEq`")),
        "refused at the goal, naming `PartialEq`: {errors:?}"
    );
}
