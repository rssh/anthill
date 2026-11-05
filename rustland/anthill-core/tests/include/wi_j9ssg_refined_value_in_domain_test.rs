//! WI-20261104-J9SSG — A VALUE OF A REFINING SORT IS IN THE DOMAIN OF THE SORT IT REFINES.
//!
//! `sort Other requires Base` makes an `Other` a `Base` (kernel-language §8.2: a sort that
//! refines another is a subtype of each instance its `requires` clauses give it), and the typer
//! accepts `rule inBase(?x: Base) :- ?x <=> other(7)`. The column's type test did not: `Base`'s
//! `fill` knows only `Base`'s own constructors, so the rule answered nothing, as did every column
//! that reaches `Base` through a type argument or a field. Found where proposal 060.1's citation
//! fixes a rule's type parameter at the caller's instance (§8.10): `either[P]` cited at `P =
//! Base` with a caught `other(n: 7)` answered nothing at `Result[E = Base]`
//! (`wi_atvc1…::a_callers_wider_pattern_reaches_a_reify_through_a_rule`).
//!
//! A derived `fill`'s last case fills a bound value of a refining sort at its own sort, where
//! its type conforms to the instance the dictionary describes; an open bound is pinned through
//! the instance the refinement gives (`Wide[W = ?w]` at a `Narrow` is `W = Int64`), as a call's
//! type argument is.
//!
//! BACK-OUT, measured one axis at a time (each a temporary switch in one build, removed):
//!  * [R] the refining case off — both holding rows, and the wider-pattern row of
//!    `wi_atvc1_rule_goal_implicit_arguments_test` (`wideDirect` and `wideOuter` answer 0);
//!  * [Q] the pin through the refinement off — `an_open_bound_is_pinned_through_the_refinement`.
//!
//! On the tree before (fbaa5317), every holding row answered nothing. The controls pass under
//! both axes and on that tree: a value of an unrelated sort, a refinement at another instance,
//! and the enumeration of an unbound column, which is the sort's own constructors.

use crate::common::{definite_unary, load_kb_with, query_pattern_term};
use anthill_core::kb::resolve::ResolveConfig;

const SRC: &str = r#"
namespace refdom
  import anthill.prelude.{Int64, String, Result, List}
  import anthill.prelude.Result.{err}
  sort Base
    entity base
  end
  sort Other
    requires Base
    entity other(n: Int64)
  end
  sort Wide
    sort W = ?
    entity wide(w: W)
  end
  sort Narrow
    requires Wide[W = Int64]
    entity narrow(k: Int64)
  end
  sort Holder
    entity holder(b: Base)
  end
  rule inBase(?x: Base) :- ?x <=> other(7)
  rule inRes(?x: Result[T = Int64, E = Base]) :- ?x <=> err(other(7))
  rule inHolder(?x: Holder) :- ?x <=> holder(b: other(7))
  rule inList(?x: List[T = Base]) :- ?x <=> [base, other(7)]
  rule inWideInt(?x: Wide[W = Int64]) :- ?x <=> narrow(k: 3)
  rule allBase(?x: Base) :- true
  rule wideStr(?x: Wide[W = String]) :- true
  rule wideInt(?x: Wide[W = Int64]) :- true
  rule anyWide(?x: Wide) :- true
end
"#;

/// Does the ground query `pattern` hold, definitely?
fn holds(kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str) -> bool {
    let goal = query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .any(|s| s.is_definite())
}

/// A column at `Base`, at `Result[E = Base]`, a field typed `Base`, a list of `Base`, and
/// `Wide[W = Int64]` given a `Narrow`: each answers its one value. FAILS under [R]: each answers
/// nothing, as on the tree before.
#[test]
fn a_refining_value_is_in_the_refined_domain() {
    let mut kb = load_kb_with(SRC);
    for rel in ["inBase", "inRes", "inHolder", "inList", "inWideInt"] {
        assert_eq!(definite_unary(&mut kb, &format!("refdom.{rel}")).len(), 1, "{rel}");
    }
    assert!(holds(&mut kb, "refdom.allBase(refdom.Other.other(7))"), "a query's `Other` at `Base`");
    assert!(
        holds(&mut kb, "refdom.wideInt(refdom.Narrow.narrow(3))"),
        "a query's `Narrow` at `Wide[W = Int64]`"
    );
}

/// `?x: Wide` is `Wide[W = ?w]`, and a `Narrow` pins `?w` to `Int64`, the instance its
/// `requires` clause gives it, and is then filled as at `Wide[W = Int64]`. FAILS under [Q]: the
/// column's test refuses the value; and under [R]. A `Wide` of its own passes under both axes.
#[test]
fn an_open_bound_is_pinned_through_the_refinement() {
    let mut kb = load_kb_with(SRC);
    assert!(holds(&mut kb, "refdom.anyWide(refdom.Narrow.narrow(3))"));
    assert!(holds(&mut kb, "refdom.anyWide(refdom.Wide.wide(1))"), "CONTROL: a `Wide` of its own");
}

/// CONTROLS, passing under every axis: a `Narrow` is no `Base`, and no `Wide[W = String]`; a
/// `Wide` holds at the instance its argument is; and an unbound column at `Base` is filled with
/// `Base`'s own constructors, as before — the refining case reads a bound value only.
#[test]
fn what_no_refinement_admits_is_refused() {
    let mut kb = load_kb_with(SRC);
    assert!(!holds(&mut kb, "refdom.allBase(refdom.Narrow.narrow(3))"), "an unrelated sort");
    assert!(!holds(&mut kb, "refdom.wideStr(refdom.Narrow.narrow(3))"), "another instance");
    assert!(holds(&mut kb, "refdom.wideStr(refdom.Wide.wide(\"a\"))"));
    assert!(!holds(&mut kb, "refdom.wideStr(refdom.Wide.wide(1))"));
    let all = definite_unary(&mut kb, "refdom.allBase");
    assert_eq!(all.len(), 1, "`base` alone: {all:?}");
    assert_eq!(crate::common::constructor_qn(&kb, &all[0]), "refdom.Base.base");
}
