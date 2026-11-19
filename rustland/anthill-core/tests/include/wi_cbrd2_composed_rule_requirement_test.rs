//! WI-20261105-CBRD2 — a rule-body call at an instance built over the clause's type parameter
//! takes the dictionary a conditional provision builds from the clause's guards (proposal
//! 060.1 §1): `?a = ?b` at `Box[T = A]` under `PartialEq[T = A]` is `Box`'s `eq`, entered
//! through `Box`'s `PartialEq` holding the guard's dictionary, as the same comparison in an
//! operation body under `requires PartialEq[T = A]` is. A condition the guard holds in its
//! spec's chain (`PartialEq[T = A]` of `Eq[T = A]`) is that sub-dictionary. Where no guard
//! builds the instance, the clause is refused, as its operation-body twin is. A woven equality
//! enters its member through the dictionary its read bound, so the bridge derives none from
//! the values, counted by `bridge_derivations_by_this_thread`.
//!
//! Before: such a call had no member. The typer left a rule-body goal at an open instance
//! untyped (the bridge was to read the provider off the argument values), so `=` was compared
//! with no member, counted by `untyped_equalities_by_this_thread`, and a call of an operation
//! whose `requires` sits at that instance (`List.contains` at `List[T = Box[T = A]]`) was
//! refused, "the clause declares none".
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * The composition off (`composed_from_guards` answering `None`): the three rows that compose
//!   fail, each clause refused at load, "the clause declares none".
//! * The open goal not handed to its clause (the `NoMatch` arm of `check_apply_call` returning
//!   untyped as before): the two equality rows and the sort-requirement row fail on the count,
//!   an equality compared with no member, and the refusal row fails, both clauses loading.
//!   The `contains` row passes by design: its requirement is a slot of its callee's chain,
//!   which the weave read before.
//! * A woven equality pinned to its member with no entry (`woven_equality` keeping the bare
//!   pin): the two equality rows and the sort-requirement row fail on the count of
//!   dictionaries the bridge derived, one each; their answers are unchanged.

use anthill_core::kb::resolve::{bridge_derivations_by_this_thread, untyped_equalities_by_this_thread};

use crate::common::{load_errors_of, load_kb_with, shown_rows};

fn program(ns: &str, rules: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Option, List, PartialEq, Eq}}
  import anthill.prelude.Option.{{some}}
  sort Box
    sort T = ?
    entity box(v: T)
  end
{rules}
end
"#
    )
}

/// The rows `rel` answers, how many equalities were compared with no member doing so, and how
/// many dictionaries the bridge derived from argument values.
fn rows_untyped_derived(src: &str, rel: &str) -> (Vec<(String, bool)>, usize, usize) {
    let mut kb = load_kb_with(src);
    let untyped = untyped_equalities_by_this_thread();
    let derived = bridge_derivations_by_this_thread();
    let rows = shown_rows(&mut kb, rel);
    (
        rows,
        untyped_equalities_by_this_thread() - untyped,
        bridge_derivations_by_this_thread() - derived,
    )
}

fn one() -> Vec<(String, bool)> {
    vec![("1".to_owned(), true)]
}

/// `=` at `Box[T = A]`, `List[T = A]` and `Option[T = A]` under `PartialEq[T = A]` is the
/// composite's own `eq`, its element compared through the guard's dictionary: equal pairs
/// answer, an unequal one does not, and nothing is compared with no member.
#[test]
fn an_equality_at_a_composite_of_the_guarded_parameter_is_its_member() {
    for (n, (at, same, other)) in [
        ("Box[T = A]", "box(v: 1)", "box(v: 2)"),
        ("List[T = A]", "[1, 2]", "[1]"),
        ("Option[T = A]", "some(1)", "some(2)"),
    ]
    .into_iter()
    .enumerate()
    {
        let ns = format!("cbrd2.crr.eq{n}");
        let rules = format!(
            "  rule same[A](?a: {at}, ?b: {at}) :- PartialEq[T = A], ?a = ?b\n  \
             rule yes(1) :- same({same}, {same})\n  rule no(1) :- same({same}, {other})\n"
        );
        let src = program(&ns, &rules);
        assert_eq!(rows_untyped_derived(&src, &format!("{ns}.yes")), (one(), 0, 0), "{at}");
        assert_eq!(rows_untyped_derived(&src, &format!("{ns}.no")), (vec![], 0, 0), "{at}");
    }
}

/// Under `Eq[T = A]` the condition is the `PartialEq` sub-dictionary of the guard's.
#[test]
fn a_condition_the_guard_holds_in_its_chain_is_its_sub_dictionary() {
    let ns = "cbrd2.crr.chain";
    let rules = "  rule same[A](?a: List[T = A], ?b: List[T = A]) :- Eq[T = A], ?a = ?b\n  \
                 rule yes(1) :- same([1, 2], [1, 2])\n  rule no(1) :- same([1, 2], [2, 1])\n";
    let src = program(ns, rules);
    assert_eq!(rows_untyped_derived(&src, &format!("{ns}.yes")), (one(), 0, 0));
    assert_eq!(rows_untyped_derived(&src, &format!("{ns}.no")), (vec![], 0, 0));
}

/// A call of an operation whose `requires` is at a composite of the parameter takes the
/// composed dictionary too: `List.contains` at `List[T = Box[T = A]]` under `Eq[T = A]`
/// builds `Eq[T = Box[T = A]]` from the guard. It was refused, "the clause declares none".
#[test]
fn a_calls_requirement_at_a_composite_is_built_from_the_guard() {
    let ns = "cbrd2.crr.contains";
    let rules = "  rule has[A](?l: List[T = Box[T = A]], ?x: Box[T = A]) :- Eq[T = A], List.contains(?l, ?x)\n  \
                 rule yes(1) :- has([box(v: 1), box(v: 2)], box(v: 2))\n  \
                 rule no(1) :- has([box(v: 1)], box(v: 2))\n";
    let src = program(ns, rules);
    assert_eq!(rows_untyped_derived(&src, &format!("{ns}.yes")), (one(), 0, 0));
    assert_eq!(rows_untyped_derived(&src, &format!("{ns}.no")), (vec![], 0, 0));
}

/// Where no guard builds the instance, the clause is refused: a generic clause whose guard is
/// of another spec, and a sort's own rule at its parameter in a sort that requires nothing —
/// as `operation same(x: Self, y: Self) -> Bool = x = y` in that sort is. Both loaded and
/// compared the two values with no member.
#[test]
fn an_equality_no_guard_builds_is_refused() {
    let generic = program(
        "cbrd2.crr.noguard",
        "  sort Tag\n    sort T = ?\n    operation tag(x: T) -> Int64\n  end\n  \
         rule same[A](?a: Box[T = A], ?b: Box[T = A]) :- Tag[T = A], ?a = ?b\n",
    );
    let sort_rule = program("cbrd2.crr.sortrule", "")
        .replace("    entity box(v: T)\n", "    entity box(v: T)\n    rule twin(?x: Self, ?y: Self) :- ?y = ?x\n");
    for src in [generic, sort_rule] {
        let errors = load_errors_of(&src);
        assert!(
            errors.iter().any(|e| e.contains("a requirement of `PartialEq` the clause declares")),
            "refused, naming the requirement: {errors:#?}"
        );
    }
}

/// A sort that requires `PartialEq[T = T]` supplies its rule's equality at `Self`, read where
/// the rule is cited and handed to the member it dispatches to.
#[test]
fn a_sort_requirement_answers_the_sorts_rule() {
    let ns = "cbrd2.crr.sortreq";
    let src = program(ns, "  rule both(1) :- Box.twin(box(v: 1), box(v: 1))\n").replace(
        "    entity box(v: T)\n",
        "    entity box(v: T)\n    requires PartialEq[T = T]\n    rule twin(?x: Self, ?y: Self) :- ?y = ?x\n",
    );
    assert_eq!(rows_untyped_derived(&src, &format!("{ns}.both")), (one(), 0, 0));
}
