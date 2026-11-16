//! A CONSTRAINT'S GOALS ARE TYPED WHERE THEY ARE READ (WI-20261105-CBRD2). An integrity guard —
//! a quantified `constraint`, or one registered with `KB.add_guard` — is checked by lowering its
//! `LogicalQuery` to goals and resolving them. The goals were untyped: over `sort Pred { sort T
//! = ?  operation ok(x: T) -> Bool }` and `Leaf` providing it, `constraint allOk: no ?y: src(?y)
//! -: Pred.ok(?y)` reached the body-less `Pred.ok` with neither a pin nor a dictionary, and the
//! bridge found `Leaf`'s member from the value `leaf(v: 3)`. The goals are now routed as one
//! query's are (`KnowledgeBase::type_query_goals`): `?y` at the type `src`'s column gives it,
//! the call decided there at `Leaf.ok`. One whose requirement no type fixes is refused: at load
//! for a constraint (`LoadError::ConstraintRefused`, where the clause typing of the constraint
//! has not refused it first), and at an assert for a guard added at run time, which rejects the
//! fact.
//!
//! The verdicts are the ones the values gave, so the rows measure the reading
//! (`resolve::unpinned_spec_goals_by_this_thread`, which counts the goals of a body-less spec
//! operation the search read with neither a pin nor a woven dictionary) beside them.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch (the goals left as lowered), then removed. The control is
//! the switch unset: every row passes.
//!
//! * [`a_constraint_is_decided_at_its_member`] and [`a_guard_added_at_run_time_is_typed`] fail
//!   on the count, their verdicts unchanged.
//! * [`a_guard_at_a_type_nothing_fixes_is_refused`] fails: the check answers `Holds`, read off
//!   each value.
//! * [`a_refused_guard_rejects_the_fact_it_cannot_check`] fails: the fact is admitted.
//! * [`a_later_load_is_refused_for_a_guard_that_does_not_type`] fails: the later load is clean.
//!
//! [`a_constraint_at_a_type_nothing_fixes_is_refused_as_its_clause`] passes either way by
//! design: the constraint's clause is typed as a headless rule's body, and refused there.

use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::kb::load::{LoadError, LoadOptions};
use anthill_core::kb::resolve::unpinned_spec_goals_by_this_thread;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::{ClauseKind, GuardCheck, KnowledgeBase};
use smallvec::SmallVec;

use crate::common::{load_in_a_later_call, load_kb_with, load_stdlib_kb, query_pattern_term, unrendered_load_errors_of};

/// `Leaf`'s `ok` holds above 2, `Twig`'s never.
fn program(ns: &str, decls: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
  sort Pred
    sort T = ?
    operation ok(x: T) -> Bool
  end
  sort Leaf
    entity leaf(v: Int64)
    provides Pred[T = Leaf]
    operation ok(x: Leaf) -> Bool = match x case leaf(v) -> v > 2
  end
  sort Twig
    entity twig(w: Int64)
    provides Pred[T = Twig]
    operation ok(x: Twig) -> Bool = false
  end
{decls}
end
"#
    )
}

/// `f`'s result and the goals it read with no member, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = unpinned_spec_goals_by_this_thread();
    let r = f();
    (r, unpinned_spec_goals_by_this_thread() - before)
}

/// Each quantifier over `src(leaf(v: 3))` and over `src(leaf(v: 1))`, with the goal and its
/// twin, and through a rule whose head types its column: violated or held as the member says.
#[test]
fn a_constraint_is_decided_at_its_member() {
    for (n, (facts, constraint, violated)) in [
        ("fact src(leaf(v: 3))", "no ?y: src(?y) -: Pred.ok(?y)", true),
        ("fact src(leaf(v: 1))", "no ?y: src(?y) -: Pred.ok(?y)", false),
        ("fact src(leaf(v: 3))", "no ?y: src(?y) -: Pred.ok(?y, true)", true),
        ("fact src(leaf(v: 3))", "forall ?y: src(?y) -: Pred.ok(?y)", false),
        ("fact src(leaf(v: 1))", "forall ?y: src(?y) -: Pred.ok(?y)", true),
        ("fact src(leaf(v: 3))", "some ?y: src(?y) -: Pred.ok(?y)", false),
        ("fact src(leaf(v: 3))", "no ?y: src(?y) -: not(Pred.ok(?y))", false),
        (
            "fact held(leaf(v: 3))\n  rule src(?y: Leaf) :- held(?y)",
            "no ?y: src(?y) -: Pred.ok(?y)",
            true,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let src = program(&format!("test.cbrd2.ct.c{n}"), &format!("  {facts}\n  constraint chk: {constraint}"));
        let (errs, unpinned) = counting(|| unrendered_load_errors_of(&src));
        let errs: Vec<&LoadError> = errs.iter().map(|e| e.peel()).collect();
        assert_eq!(unpinned, 0, "`{constraint}` over `{facts}` read a goal with no member");
        if violated {
            assert!(
                matches!(errs.as_slice(), [LoadError::ConstraintViolated { label: Some(l) }] if l == "chk"),
                "`{constraint}` over `{facts}`: {errs:#?}"
            );
        } else {
            assert!(errs.is_empty(), "`{constraint}` over `{facts}`: {errs:#?}");
        }
    }
}

/// The control: `src` holding a `Leaf` and a `Twig`, `no ?y: src(?y) -: Pred.ok(?y)` names no
/// one instance, and its clause, typed as a headless rule's body, is refused naming `Pred`.
#[test]
fn a_constraint_at_a_type_nothing_fixes_is_refused_as_its_clause() {
    let src = program(
        "test.cbrd2.ct.open",
        "  fact src(leaf(v: 3))\n  fact src(twig(w: 1))\n  constraint chk: no ?y: src(?y) -: Pred.ok(?y)",
    );
    let errs: Vec<String> = unrendered_load_errors_of(&src).iter().map(|e| e.to_string()).collect();
    assert!(
        errs.len() == 1 && errs[0].contains("a requirement of `Pred` fixed where the call"),
        "{errs:?}"
    );
}

/// `anthill.reflect.LogicalQuery.<short>`, which the test builds a guard of.
fn lq(kb: &KnowledgeBase, short: &str) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol(&format!("anthill.reflect.LogicalQuery.{short}"))
        .unwrap_or_else(|| panic!("LogicalQuery.{short}"))
}

/// `pattern_query(term: goal)`.
fn pattern(kb: &mut KnowledgeBase, goal: TermId) -> Value {
    let term = kb.intern("term");
    Value::Entity {
        functor: lq(kb, "pattern_query"),
        pos: Rc::from(Vec::<Value>::new()),
        named: Rc::from(vec![(term, Value::term(goal))]),
    }
}

/// `f(?y)`, `f` named in full.
fn goal_on(kb: &mut KnowledgeBase, f: &str, y: TermId) -> TermId {
    let functor = kb.try_resolve_symbol(f).unwrap_or_else(|| panic!("{f}"));
    kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_slice(&[y]),
        named_args: SmallVec::new(),
    })
}

/// `no ?y: <ns>.src(?y) -: <ns>.Pred.ok(?y)`, built as a program builds one for `KB.add_guard`.
fn no_ok_guard(kb: &mut KnowledgeBase, ns: &str) -> Value {
    let name = kb.intern("y");
    let var = kb.fresh_var(name);
    let y = kb.alloc(Term::Var(Var::Global(var)));
    let src = goal_on(kb, &format!("{ns}.src"), y);
    let ok = goal_on(kb, &format!("{ns}.Pred.ok"), y);
    let (condition, body) = (kb.intern("condition"), kb.intern("body"));
    let (condition_q, body_q) = (pattern(kb, src), pattern(kb, ok));
    Value::Entity {
        functor: lq(kb, "no_q"),
        pos: Rc::from(Vec::<Value>::new()),
        named: Rc::from(vec![(condition, condition_q), (body, body_q)]),
    }
}

/// A guard added at run time over `src(leaf(v: 3))` is violated, decided at `Leaf.ok`.
#[test]
fn a_guard_added_at_run_time_is_typed() {
    let ns = "test.cbrd2.ct.run";
    let mut kb = load_kb_with(&program(ns, "  fact src(leaf(v: 3))"));
    let guard = no_ok_guard(&mut kb, ns);
    kb.add_guard(guard);
    let (checks, unpinned) = counting(|| kb.check_all_guards());
    assert_eq!(unpinned, 0, "the check read a goal with no member");
    assert_eq!(checks, vec![GuardCheck::Violated(None)]);
}

/// Over `src` holding a `Leaf` and a `Twig`, `?y` is at no one type: the guard's goals are
/// refused where they are read, naming `Pred`, and not decided value by value.
#[test]
fn a_guard_at_a_type_nothing_fixes_is_refused() {
    let ns = "test.cbrd2.ct.mixed";
    let mut kb = load_kb_with(&program(ns, "  fact src(leaf(v: 1))\n  fact src(twig(w: 1))"));
    let guard = no_ok_guard(&mut kb, ns);
    kb.add_guard(guard);
    let checks = kb.check_all_guards();
    assert!(
        matches!(checks.as_slice(), [GuardCheck::Refused(None, detail)] if detail.contains("Pred")),
        "{checks:?}"
    );
}

/// A later load checks every guard again, the one added at run time among them, and is refused
/// for the one whose goals do not type: `ConstraintRefused`, naming `Pred`.
#[test]
fn a_later_load_is_refused_for_a_guard_that_does_not_type() {
    let ns = "test.cbrd2.ct.later";
    let mut kb = load_kb_with(&program(ns, "  fact src(leaf(v: 1))\n  fact src(twig(w: 1))"));
    let guard = no_ok_guard(&mut kb, ns);
    kb.add_guard(guard);
    let errs = load_in_a_later_call(&mut kb, "namespace test.cbrd2.ct.later2\nend\n", LoadOptions::default())
        .err()
        .unwrap_or_default();
    let errs: Vec<&LoadError> = errs.iter().map(|e| e.peel()).collect();
    assert!(
        matches!(errs.as_slice(), [LoadError::ConstraintRefused { label: None, detail }] if detail.contains("Pred")),
        "{errs:#?}"
    );
}

/// A fact asserted under such a guard is rejected, the guard being unable to check it: over
/// `sort Bag { sort T = ?  entity src(x: T) }` holding a `Leaf` and a `Twig`, `Bag.src(x: ?y)`
/// puts `?y` at no one type.
#[test]
fn a_refused_guard_rejects_the_fact_it_cannot_check() {
    let ns = "test.cbrd2.ct.assert";
    let mut kb = load_kb_with(&program(
        ns,
        "  sort Bag\n    sort T = ?\n    entity src(x: T)\n  end\n  \
         fact Bag.src(x: leaf(v: 1))\n  fact Bag.src(x: twig(w: 1))",
    ));
    let term_of = |kb: &mut KnowledgeBase, pattern: &str| {
        let goal = query_pattern_term(kb, pattern);
        anthill_core::kb::node_occurrence::value_to_term(kb, &Value::Node(goal)).expect("a pattern has a term")
    };
    let src = term_of(&mut kb, &format!("{ns}.Bag.src(x: ?y)"));
    let y = match kb.get_term(src) {
        Term::Fn { named_args, .. } => named_args[0].1,
        other => panic!("`Bag.src(x: ?y)` is an application, got {other:?}"),
    };
    let ok = goal_on(&mut kb, &format!("{ns}.Pred.ok"), y);
    let (condition, body) = (kb.intern("condition"), kb.intern("body"));
    let (condition_q, body_q) = (pattern(&mut kb, src), pattern(&mut kb, ok));
    let guard = Value::Entity {
        functor: lq(&kb, "no_q"),
        pos: Rc::from(Vec::<Value>::new()),
        named: Rc::from(vec![(condition, condition_q), (body, body_q)]),
    };
    let cid = kb.add_guard(guard);
    let trigger = *kb.guard_trigger_sorts(cid).first().expect("`Bag.src` triggers the guard");
    let fact = term_of(&mut kb, &format!("{ns}.Bag.src(x: {ns}.Leaf.leaf(v: 0))"));
    let domain = kb.try_resolve_symbol(ns).expect("the namespace");
    assert_eq!(kb.assert_checked(fact, ClauseKind::Fact, trigger, domain, None), None);
}
