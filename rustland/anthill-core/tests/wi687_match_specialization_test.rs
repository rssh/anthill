//! WI-687 — per-call-site defining-equation specialization of a MATCH-headed op.
//!
//! `op_defining_equations` / `synthesize_op_defining_rule` build ONE generic
//! rule over abstract parameters, and DECLINE a `match`-headed body: a `match`
//! whose scrutinee is a parameter (`match o`) or a field of one (`match b.inner`)
//! cannot reduce over an abstract `?0`. WI-687 retries such a body per call-site:
//! given the proof goal's concrete-constructor arguments (`some(?v)`,
//! `Box(inner: some(?v), …)`), it builds a fresh-Global shape skeleton, reduces
//! the `match` at the known constructor heads, and synthesizes a
//! CONSTRUCTOR-SHAPED defining rule (`pick(some(?0), ?1, ?result)`), which the
//! SMT emitter inlines by binding the head structurally against the call.
//!
//! This exercises the derivation engine + seam directly; the end-to-end SMT emit
//! and z3 discharge live in `anthill-smt-gen/tests/wi687_match_headed_test.rs`.

mod common;

use std::rc::Rc;

use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::op_info::all_operation_params;
use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::{KnowledgeBase, RuleId};

const SRC: &str = r#"
namespace test.wi687
  import anthill.prelude.{Int64, Bool, Option}
  import anthill.prelude.Numeric.{add, sub}
  import anthill.prelude.Ordered.{gte}
  import anthill.prelude.Option.{some, none}

  entity Box(inner: Option[T = Int64], base: Int64)

  sort Ops
    -- match directly on a parameter (`none()` is the nullary-constructor
    -- pattern; a bare `none` would be a catch-all VAR binder).
    operation pick(o: Option[T = Int64], base: Int64) -> Int64 =
      match o
        case none() -> base
        case some(x) -> if gte(x, 0) then add(base, x) else sub(base, x)

    -- match on a FIELD of a parameter (the lf1 `step` shape)
    operation pickf(b: Box) -> Int64 =
      match b.inner
        case none() -> b.base
        case some(x) -> if gte(x, 0) then add(b.base, x) else sub(b.base, x)
  end

  -- Obligation goals supplying concrete-constructor arguments.
  rule ob_pick_some(?w) :- Ops.pick(some(?v), ?b, ?r), ?w = ?r
  rule ob_pick_none(?w) :- Ops.pick(none, ?b, ?r), ?w = ?r
  rule ob_pickf_some(?w) :- Ops.pickf(Box(inner: some(?v), base: ?b), ?r), ?w = ?r
  -- A bare-variable argument: no concrete constructor, so the match can't reduce.
  rule ob_pick_abstract(?w) :- Ops.pick(?o, ?b, ?r), ?w = ?r
end
"#;

fn op_sym(kb: &KnowledgeBase, short: &str) -> Symbol {
    all_operation_params(kb)
        .into_iter()
        .map(|(s, _)| s)
        .find(|s| kb.resolve_sym(*s).rsplit('.').next() == Some(short))
        .unwrap_or_else(|| panic!("operation `{short}` not found"))
}

fn short(kb: &KnowledgeBase, s: Symbol) -> String {
    kb.resolve_sym(s).rsplit('.').next().unwrap_or("").to_string()
}

/// The one synthesized (non-fact) defining rule for `op`, or `None`.
fn synth_rule(kb: &KnowledgeBase, op: Symbol) -> Option<RuleId> {
    kb.rules_by_functor(op).into_iter().find(|r| !kb.is_fact(*r))
}

/// Render a head/body term's shape compactly for structural assertions:
/// `pick(some(?0), ?1, ?2)`, `add(?1, ?0)`, `ite(...)`.
fn render(kb: &KnowledgeBase, tid: anthill_core::kb::term::TermId) -> String {
    match kb.get_term(tid) {
        Term::Var(Var::DeBruijn(i)) => format!("?{i}"),
        Term::Var(v) => format!("{v:?}"),
        Term::Const(l) => format!("{l:?}"),
        Term::Ref(s) | Term::Ident(s) => short(kb, *s),
        Term::Fn { functor, pos_args, named_args } => {
            let mut parts: Vec<String> = pos_args.iter().map(|a| render(kb, *a)).collect();
            for (fs, a) in named_args {
                parts.push(format!("{}: {}", short(kb, *fs), render(kb, *a)));
            }
            format!("{}({})", short(kb, *functor), parts.join(", "))
        }
        other => format!("{other:?}"),
    }
}

fn body_rhs(kb: &KnowledgeBase, rid: RuleId) -> Rc<NodeOccurrence> {
    let body = kb.rule_body_nodes(rid);
    assert_eq!(body.len(), 1, "defining rule has one `?result = <rhs>` goal");
    match body[0].as_expr() {
        Some(Expr::Apply { pos_args, .. }) if pos_args.len() == 2 => Rc::clone(&pos_args[1]),
        other => panic!("body goal must be `eq(?result, rhs)`, got {other:?}"),
    }
}

fn head_short(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> String {
    match occ.as_expr() {
        Some(Expr::Apply { functor, .. }) => short(kb, *functor),
        Some(Expr::If { .. }) => "if".to_string(),
        other => panic!("unexpected rhs head: {other:?}"),
    }
}

#[test]
fn generic_match_synth_declines() {
    // Baseline: the abstract-parameter derivation cannot reduce a match body.
    let mut kb = common::load_kb_with(SRC);
    let pick = op_sym(&kb, "pick");
    assert!(kb.op_defining_equations(pick).is_none(), "generic match derivation declines");
    assert!(kb.synthesize_op_defining_rule(pick).is_none(), "generic synth declines");
    assert!(synth_rule(&kb, pick).is_none(), "no defining rule was registered");
}

/// The named-arg `TermId` value of a `Fn` term whose field short-name is `field`.
fn named_child(kb: &KnowledgeBase, tid: anthill_core::kb::term::TermId, field: &str)
    -> anthill_core::kb::term::TermId {
    match kb.get_term(tid) {
        Term::Fn { named_args, .. } => named_args
            .iter()
            .find(|(s, _)| short(kb, *s) == field)
            .map(|(_, t)| *t)
            .unwrap_or_else(|| panic!("no `{field}` field in {}", render(kb, tid))),
        other => panic!("expected Fn, got {other:?}"),
    }
}

/// The positional-arg `TermId`s + functor short-name of a `Fn` head term.
fn head_parts(kb: &KnowledgeBase, tid: anthill_core::kb::term::TermId)
    -> (String, Vec<anthill_core::kb::term::TermId>) {
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, .. } => (short(kb, *functor), pos_args.to_vec()),
        other => panic!("head must be a Fn, got {other:?}"),
    }
}

/// The functor short-name of a `Fn`/`Ref`/`Ident` term (its constructor head).
fn term_functor(kb: &KnowledgeBase, tid: anthill_core::kb::term::TermId) -> String {
    match kb.get_term(tid) {
        Term::Fn { functor, .. } => short(kb, *functor),
        Term::Ref(s) | Term::Ident(s) => short(kb, *s),
        other => panic!("expected a constructor term, got {other:?}"),
    }
}

/// Whether a `some(...)` term carries a single De Bruijn var child (the fresh
/// skeleton leaf) — positional or named, we don't pin which.
fn some_wraps_debruijn(kb: &KnowledgeBase, tid: anthill_core::kb::term::TermId) -> bool {
    match kb.get_term(tid) {
        Term::Fn { pos_args, named_args, .. } => {
            let mut children = pos_args.to_vec();
            children.extend(named_args.iter().map(|(_, t)| *t));
            children.len() == 1
                && matches!(kb.get_term(children[0]), Term::Var(Var::DeBruijn(_)))
        }
        _ => false,
    }
}

#[test]
fn per_call_site_specializes_match_on_param() {
    let mut kb = common::load_kb_with(SRC);
    let pick = op_sym(&kb, "pick");
    kb.synthesize_body_derived_defrules("test.wi687.ob_pick_some");

    let rid = synth_rule(&kb, pick).expect("per-call-site synth registers a defining rule");
    // Constructor-shaped head: the Option param becomes `some(?0)`, not a flat `?0`.
    let (f, pos) = head_parts(&kb, kb.rule_head(rid));
    assert_eq!(f, "pick");
    assert_eq!(pos.len(), 3, "two params (o, base) + result slot");
    assert_eq!(term_functor(&kb, pos[0]), "some", "the Option param head carries the `some` spine");
    assert!(some_wraps_debruijn(&kb, pos[0]), "`some`'s value is a fresh skeleton leaf var: {}",
        render(&kb, pos[0]));

    // some-arm: the body reduces to `if x>=0 then base+x else base-x` over the
    // skeleton leaves — an `Expr::If` (WI-680 refold), NOT a residual match.
    let rhs = body_rhs(&kb, rid);
    assert_eq!(head_short(&kb, &rhs), "if", "the match reduced to the some-arm's conditional");
}

#[test]
fn per_call_site_specializes_none_arm() {
    let mut kb = common::load_kb_with(SRC);
    let pick = op_sym(&kb, "pick");
    kb.synthesize_body_derived_defrules("test.wi687.ob_pick_none");

    let rid = synth_rule(&kb, pick).expect("none-arg synth registers a defining rule");
    let (f, pos) = head_parts(&kb, kb.rule_head(rid));
    assert_eq!(f, "pick");
    assert_eq!(short(&kb, match kb.get_term(pos[0]) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(s) | Term::Ident(s) => *s,
        other => panic!("none head arg unexpected: {other:?}"),
    }), "none", "the nullary `none` spine is preserved in the head");
    // none-arm is the unconditional `base` — one arm, no `if`, just the base var.
    let rhs = body_rhs(&kb, rid);
    assert!(
        matches!(rhs.as_expr(), Some(Expr::Var(Var::DeBruijn(_)))),
        "none arm returns the base parameter unconditionally, got {:?}",
        rhs.as_expr()
    );
}

#[test]
fn per_call_site_specializes_match_on_field() {
    let mut kb = common::load_kb_with(SRC);
    let pickf = op_sym(&kb, "pickf");
    kb.synthesize_body_derived_defrules("test.wi687.ob_pickf_some");

    let rid = synth_rule(&kb, pickf).expect("field-match synth registers a defining rule");
    // The whole Box argument's spine is preserved (inner Option shape included).
    let (f, pos) = head_parts(&kb, kb.rule_head(rid));
    assert_eq!(f, "pickf");
    assert_eq!(pos.len(), 2, "one Box param + result slot");
    // pos[0] is Box(...); its `inner` field carries the `some` spine.
    assert_eq!(term_functor(&kb, pos[0]), "Box", "the head arg keeps the Box spine");
    let inner = named_child(&kb, pos[0], "inner");
    assert_eq!(term_functor(&kb, inner), "some", "the Box's inner Option field keeps `some`");
    assert!(some_wraps_debruijn(&kb, inner), "inner `some` wraps a fresh skeleton leaf: {}",
        render(&kb, inner));

    let rhs = body_rhs(&kb, rid);
    assert_eq!(head_short(&kb, &rhs), "if", "the field match reduced to the some-arm conditional");
}

#[test]
fn per_call_site_declines_bare_variable_argument() {
    // A bare `?o` argument gives no constructor shape, so the match can't reduce
    // — the op is left un-synthesized (the emitter would then fail loudly).
    let mut kb = common::load_kb_with(SRC);
    let pick = op_sym(&kb, "pick");
    kb.synthesize_body_derived_defrules("test.wi687.ob_pick_abstract");
    assert!(
        synth_rule(&kb, pick).is_none(),
        "a bare-var argument does not specialize the match"
    );
}
