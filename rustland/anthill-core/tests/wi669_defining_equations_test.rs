//! WI-669 — body-derived defining equations for the prover/SMT tier
//! (design `docs/design/abstract-interpreter-and-rules.md` §3.4.1).
//!
//! `KnowledgeBase::op_defining_equations` specializes a pure bodied operation
//! one step over its parameters (as DeBruijn vars) and returns one guarded
//! equation per `if`-branch path — the equation set a proof asserts instead of
//! a hand-written `<=>` twin. This exercises the engine directly:
//!   - a single-arm arithmetic body → one unconditional equation;
//!   - an `if` body → two arms with a condition / negated-condition guard;
//!   - a `match` body → loud decline (ADT defining equations are future).

mod common;

use std::rc::Rc;

use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::op_info::all_operation_params;
use anthill_core::kb::KnowledgeBase;

const SRC: &str = r#"
namespace test.wi669
  import anthill.prelude.{Int64, Bool, Option}
  import anthill.prelude.Numeric.{add}
  import anthill.prelude.Ordered.{gte}
  import anthill.prelude.Option.{some, none}

  sort Ops
    operation double(x: Int64) -> Int64 = add(x, x)

    operation clamp(x: Int64) -> Int64 =
      if gte(x, 0) then x else 0

    operation grade(x: Int64) -> Int64 =
      if gte(x, 0)
        then if gte(x, 5) then 2 else 1
        else 0

    operation first_or(o: Option[T = Int64], d: Int64) -> Int64 =
      match o
        case some(v) -> v
        case none    -> d
  end
end
"#;

/// The op `Symbol` whose short name is `short`.
fn op_sym(kb: &KnowledgeBase, short: &str) -> Symbol {
    all_operation_params(kb)
        .into_iter()
        .map(|(s, _)| s)
        .find(|s| kb.resolve_sym(*s).rsplit('.').next() == Some(short))
        .unwrap_or_else(|| panic!("operation `{short}` not found"))
}

/// The short name of an occurrence's head functor (`add(...)` → `"add"`).
fn head_short(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> String {
    match occ.as_expr() {
        Some(Expr::Apply { functor, .. }) => {
            kb.resolve_sym(*functor).rsplit('.').next().unwrap_or("").to_string()
        }
        other => panic!("expected a functor application, got {other:?}"),
    }
}

#[test]
fn single_arm_body_yields_one_unconditional_equation() {
    let mut kb = common::load_kb_with(SRC);
    let d = op_sym(&kb, "double");
    let eqs = kb.op_defining_equations(d).expect("double must derive an equation");
    assert_eq!(eqs.len(), 1, "one arm for a single-expression body");
    assert!(eqs[0].guards.is_empty(), "an unconditional body has no guards");
    assert_eq!(head_short(&kb, &eqs[0].result), "add", "result is the body `add(?0, ?0)`");
    if let Some(Expr::Apply { pos_args, .. }) = eqs[0].result.as_expr() {
        assert_eq!(pos_args.len(), 2);
    }
}

#[test]
fn if_body_yields_two_guarded_arms() {
    let mut kb = common::load_kb_with(SRC);
    let c = op_sym(&kb, "clamp");
    let eqs = kb.op_defining_equations(c).expect("clamp must derive equations");
    assert_eq!(eqs.len(), 2, "then-arm and else-arm");

    // then-arm: guarded by `gte(?0, 0)` (not negated).
    assert_eq!(eqs[0].guards.len(), 1);
    assert!(!eqs[0].guards[0].negated, "then-arm holds when the condition is true");
    assert_eq!(head_short(&kb, &eqs[0].guards[0].cond), "gte");

    // else-arm: the SAME condition, negated.
    assert_eq!(eqs[1].guards.len(), 1);
    assert!(eqs[1].guards[0].negated, "else-arm holds when the condition is false");
    assert_eq!(head_short(&kb, &eqs[1].guards[0].cond), "gte");
}

#[test]
fn match_body_declines_loudly() {
    let mut kb = common::load_kb_with(SRC);
    let f = op_sym(&kb, "first_or");
    assert!(
        kb.op_defining_equations(f).is_none(),
        "an ADT `match` body has no SMT defining-equation form in this increment"
    );
}

// ── WI-669 inc-1b: synthesize a transient defining rule ──────────────────────

/// The `?result = <rhs>` body node of `op`'s synthesized defining rule: the
/// single body goal is `eq(?result, rhs)`; return `rhs` (the refolded body).
fn synth_body_rhs(kb: &mut KnowledgeBase, op: Symbol) -> Rc<NodeOccurrence> {
    let rid = kb.synthesize_op_defining_rule(op).expect("op must synthesize a defining rule");
    let body = kb.rule_body_nodes(rid);
    assert_eq!(body.len(), 1, "the defining rule has one `?result = <rhs>` body goal");
    match body[0].as_expr() {
        Some(Expr::Apply { pos_args, .. }) if pos_args.len() == 2 => Rc::clone(&pos_args[1]),
        other => panic!("body goal must be `eq(?result, rhs)`, got {other:?}"),
    }
}

#[test]
fn synth_single_arm_body_is_bare_result_no_if() {
    let mut kb = common::load_kb_with(SRC);
    let d = op_sym(&kb, "double");
    let rid = kb.synthesize_op_defining_rule(d).expect("double synthesizes");
    // head `double(?0, ?result)`: one param + the result slot.
    assert_eq!(kb.rule_arity(rid), 2, "one parameter plus the result var");
    // The head functor is the op itself, so the emitter's rules_by_functor inline
    // finds it.
    assert!(
        kb.rules_by_functor(d).contains(&rid),
        "the synth rule is keyed under the op's own functor"
    );
    // A single-expression body refolds to its bare result — no `if`.
    let rhs = synth_body_rhs(&mut kb, d);
    assert_eq!(head_short(&kb, &rhs), "add", "double's body is `add(?0, ?0)`, no conditional");
}

#[test]
fn synth_if_body_refolds_to_ite() {
    let mut kb = common::load_kb_with(SRC);
    let c = op_sym(&kb, "clamp");
    let rhs = synth_body_rhs(&mut kb, c);
    match rhs.as_expr() {
        Some(Expr::If { condition, .. }) => {
            assert_eq!(head_short(&kb, condition), "gte", "clamp's guard is `gte(x, 0)`");
        }
        other => panic!("clamp's body must refold to an `Expr::If`, got {other:?}"),
    }
}

#[test]
fn synth_nested_if_refolds_with_and_not() {
    let mut kb = common::load_kb_with(SRC);
    let g = op_sym(&kb, "grade");
    let rhs = synth_body_rhs(&mut kb, g);
    // grade: if x>=0 then (if x>=5 then 2 else 1) else 0. Three arms refold to
    // `ite(and(g0,g1), 2, ite(and(g0, not g1), 1, 0))`: the outer guard conjoins,
    // the middle guard negates.
    let Some(Expr::If { condition, else_branch, .. }) = rhs.as_expr() else {
        panic!("grade must refold to a nested `Expr::If`");
    };
    assert_eq!(head_short(&kb, condition), "and", "the outer arm's guard is a conjunction");
    let Some(Expr::If { condition: inner_cond, .. }) = else_branch.as_expr() else {
        panic!("grade's else must be the next `Expr::If`");
    };
    // inner condition is `and(gte(x,0), not(gte(x,5)))` — assert the `not` appears.
    assert_eq!(head_short(&kb, inner_cond), "and", "the middle arm's guard is a conjunction");
    if let Some(Expr::Apply { pos_args, .. }) = inner_cond.as_expr() {
        assert!(
            pos_args.iter().any(|a| head_short(&kb, a) == "not"),
            "the middle arm negates the inner guard"
        );
    }
}

#[test]
fn synth_match_body_declines() {
    let mut kb = common::load_kb_with(SRC);
    let f = op_sym(&kb, "first_or");
    assert!(
        kb.synthesize_op_defining_rule(f).is_none(),
        "a `match` body has no synthesizable defining rule in this increment"
    );
}

#[test]
fn synth_is_idempotent() {
    let mut kb = common::load_kb_with(SRC);
    let c = op_sym(&kb, "clamp");
    let first = kb.synthesize_op_defining_rule(c).expect("first synth");
    let second = kb.synthesize_op_defining_rule(c).expect("second synth");
    assert_eq!(first, second, "a second synthesis reuses the existing defining rule");
    assert_eq!(
        kb.rules_by_functor(c).len(), 1,
        "no duplicate defining rule is registered"
    );
}

// ── WI-681: transitive seam reaches an op called one inline-level down ────────

const SEAM_SRC: &str = r#"
namespace test.wi669seam
  import anthill.prelude.{Int64}
  import anthill.prelude.Numeric.{add}

  sort Ops
    operation twice(x: Int64) -> Int64 = add(x, x)
  end

  -- `twice` is called inside `helper`, not directly in `obligation`.
  rule helper(?r) :- Ops.twice(?x, ?r)
  rule obligation(?w) :- helper(?w)
end
"#;

#[test]
fn transitive_seam_synthesizes_op_called_one_level_down() {
    let mut kb = common::load_kb_with(SEAM_SRC);
    let twice = op_sym(&kb, "twice");
    // Before: `twice` has only its op body — no relational defining rule.
    assert!(
        kb.rules_by_functor(twice).iter().all(|r| kb.is_fact(*r)),
        "no defining rule for `twice` before the seam runs"
    );
    // The obligation calls `twice` only transitively (through `helper`), so the
    // scan must recurse into the inlined rule's body to reach it.
    kb.synthesize_body_derived_defrules("test.wi669seam.obligation");
    assert!(
        kb.rules_by_functor(twice).iter().any(|r| !kb.is_fact(*r)),
        "the transitive seam synthesizes `twice`'s defining rule"
    );
}

