//! WI-583 — position-directed gating of Bool-returning operations as rule-body
//! goals. A bare `:- valid(?x)` (with `valid: T -> Bool`) resolves as
//! `eq(valid(?x), true)` — true=success, false=fail, unbound=suspend — while a
//! NON-Bool operation in goal position is a LOUD load error, not a silent
//! failed relation lookup.
//!
//! The happy-path resolution is inherited from WI-580 inc2
//! (`bare_bodied_bool_relation` routing in `resolve.rs::step_init`); the loud
//! error for a non-Bool op in goal position (`check_rule_body_goal_ops` in
//! `kb/typing.rs`) is WI-583's own contribution.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// Count DEFINITE solutions of a zero-arg predicate (1 = the body goal
/// succeeds, 0 = it fails). Mirrors `push_choice_test::zero_arg_solutions`.
fn zero_arg_solutions(kb: &mut KnowledgeBase, pred: &str) -> usize {
    let sym = kb
        .try_resolve_symbol(pred)
        .unwrap_or_else(|| panic!("no symbol {pred}"));
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// The pure Bool op fixture: `is_five` is rule-less, bodied, effect-free, and
/// Bool-returning — exactly `bare_bodied_bool_relation`'s shape.
const BOOL_OP_SRC: &str = r#"
namespace test.wi583
  import anthill.prelude.{Bool, Int64}
  import anthill.prelude.PartialEq.{eq}
  operation is_five(x: Int64) -> Bool = eq(x, 5)
  rule five_yes() :- is_five(5)
  rule five_no()  :- is_five(3)
  rule check(?x)  :- is_five(?x)
end
"#;

/// Happy path: a pure Bool op used bare in a rule body resolves as
/// `eq(op(args), true)` — true ⇒ success, false ⇒ fail.
#[test]
fn wi583_pure_bool_op_in_goal_succeeds_and_fails() {
    let mut kb = crate::common::load_kb_with(BOOL_OP_SRC);
    assert_eq!(
        zero_arg_solutions(&mut kb, "test.wi583.five_yes"),
        1,
        "is_five(5) ⇒ true ⇒ eq(true,true) ⇒ goal succeeds",
    );
    assert_eq!(
        zero_arg_solutions(&mut kb, "test.wi583.five_no"),
        0,
        "is_five(3) ⇒ false ⇒ eq(false,true) ⇒ goal fails",
    );
}

/// Suspend: an UNBOUND argument leaves `eq(is_five(?x), true)` with an
/// unreduced op-call operand → the eval bridge suspends to a residual, NOT a
/// fabricated definite answer (WI-067 discipline; the dual of the WI-580
/// `member(5, ?l)` residual case).
#[test]
fn wi583_unbound_arg_in_bool_goal_suspends() {
    let mut kb = crate::common::load_kb_with(BOOL_OP_SRC);
    let sym = kb.try_resolve_symbol("test.wi583.check").unwrap();
    let xs = kb.intern("_x");
    let x = kb.fresh_var(xs);
    let xt = kb.alloc(Term::Var(Var::Global(x)));
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(&[xt]),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "an unbound `is_five(?x)` goal must suspend (residual), never invent a \
         definite answer; got {} solution(s), some definite",
        sols.len(),
    );
}

/// The loud error: a NON-Bool operation (`ident: Int64 -> Int64`) in goal
/// position is a load error, not a silent failed relation lookup.
#[test]
fn wi583_non_bool_op_in_goal_is_load_error() {
    let src = r#"
namespace test.wi583nb
  import anthill.prelude.{Bool, Int64}
  operation ident(x: Int64) -> Int64 = x
  rule bad() :- ident(5)
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("a non-Bool op in goal position must be a LOUD load error");
    assert!(
        errs.iter().any(|e| e.contains("ident") && e.contains("goal position")),
        "the error must name the offending op and the goal-position category; got: {errs:?}",
    );
}

/// Coverage of a nested goal position: a non-Bool op UNDER a goal connective
/// (`not(…)`) is also flagged — the walk recurses through `not`/`or`/
/// `push_choice`, whose arguments are goal positions.
#[test]
fn wi583_non_bool_op_under_not_is_load_error() {
    let src = r#"
namespace test.wi583nn
  import anthill.prelude.{Bool, Int64}
  operation ident(x: Int64) -> Int64 = x
  rule bad_not() :- not(ident(5))
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("a non-Bool op nested under `not` in goal position must be a load error");
    assert!(
        errs.iter().any(|e| e.contains("ident") && e.contains("goal position")),
        "a non-Bool op under `not` must be flagged; got: {errs:?}",
    );
}

/// Regression guard #1: a Bool-returning op in goal position must NOT be
/// flagged (it is gated to `eq(op, true)`), i.e. `BOOL_OP_SRC` loads clean.
#[test]
fn wi583_bool_op_in_goal_loads_clean() {
    assert!(
        crate::common::try_load_kb_with(BOOL_OP_SRC).is_ok(),
        "a Bool-returning op in goal position is legal (routed to eq(_,true)) — must not error",
    );
}

/// Regression guard #2: a genuine RELATION (a fact-/rule-backed functor) in
/// goal position resolves relationally and must NOT be flagged, even when it is
/// non-Bool-shaped — only a rule-LESS operation is a category error.
#[test]
fn wi583_relation_in_goal_still_resolves() {
    let src = r#"
namespace test.wi583rel
  sort Thing
    entity a
    entity b
  end
  fact likes(a)
  rule who_likes() :- likes(a)
  rule nobody()    :- likes(b)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        zero_arg_solutions(&mut kb, "test.wi583rel.who_likes"),
        1,
        "a fact-backed relation in goal position resolves relationally (fact likes(a))",
    );
    assert_eq!(
        zero_arg_solutions(&mut kb, "test.wi583rel.nobody"),
        0,
        "no fact likes(b) ⇒ 0 solutions — a relation, not a category error",
    );
}

/// A dot-dispatched sort-scoped non-Bool op (`b.unwrap` → `Box.unwrap(b)`,
/// which RESOLVES to the operation) is flagged — the check catches a
/// properly-resolved sort-scoped op, not only namespace-level ones.
#[test]
fn wi583_dot_dispatched_sort_scoped_non_bool_is_error() {
    let src = r#"
namespace test.wi583dot
  import anthill.prelude.{Bool, Int64}
  sort Box
    entity mk(v: Int64)
    operation unwrap(b: Box) -> Int64 = 0
  end
  rule bad() :- mk(3).unwrap
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("a dot-dispatched sort-scoped non-Bool op in goal position must be a load error");
    assert!(
        errs.iter().any(|e| e.contains("unwrap") && e.contains("goal position")),
        "the error must name the resolved sort-scoped op; got: {errs:?}",
    );
}

/// Regression guard #3 (review candidate 2): an op with a NON-concrete return
/// (a bare type parameter that could instantiate to `Bool`) is NOT flagged —
/// only a concrete non-Bool return head is a category error.
#[test]
fn wi583_generic_return_op_in_goal_not_flagged() {
    let src = r#"
namespace test.wi583gen
  import anthill.prelude.{Bool, Int64}
  operation pick[T](x: T) -> T = x
  rule ok() :- pick(5)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        !errs.iter().any(|e| e.contains("goal position")),
        "a generic-return op (return may be Bool) must NOT be flagged as non-Bool; got: {errs:?}",
    );
}
