//! WI-538 / proposal 025 §"In-body and control-flow proofs" — a `proof`
//! statement inside an operation body / control-flow branch.
//!
//! The construct reuses the existing `proof` clauses (`target`, `by
//! <strategy>`, `using`) in statement position, plus an optional
//! `conclude <goal>` for an inline proposition (the guard-discharge case,
//! which has no rule to name), followed by a continuation expression.
//!
//! These cover (1) the construct end-to-end — parse → load → `Expr::Proof`
//! occurrence → typer (the typer's Tier-A discharge over Γ runs without
//! error), and (2) the proposal-050 in-body-`proof` modification rule the
//! typer wires: a goal proved from a Γ-seeded premise is `assume`d into Γ,
//! so its conclusion is available as a Γ fact for downstream code.
//!
//! Observing the Tier-A discharge *outcome* end-to-end needs a Γ *reader*
//! (effect discharge, WI-067), which is deferred; the discharge logic
//! itself is exercised directly here via `prove_from_gamma`.

mod common;

use anthill_core::eval::value::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::term::Term;
use anthill_core::kb::term::Var;
use anthill_core::kb::typing::{prove_from_gamma, FlowEnv};
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

/// `f(args)` as a transient goal `Value` — the shape the typer puts in Γ.
fn goal(functor: Symbol, args: Vec<Value>) -> Value {
    Value::Entity {
        functor,
        pos: Rc::from(args),
        named: Rc::from(Vec::new()),
        ty: None,
    }
}

/// An op parameter as a fresh non-ground flex `Var::Global` (open-world:
/// `eq`/`neq` flounder on it, so only a Γ fact discharges a guard).
fn param(kb: &mut KnowledgeBase, name: &str) -> Value {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    Value::term(kb.alloc(Term::Var(Var::Global(vid))))
}

fn neq_sym(kb: &mut KnowledgeBase) -> Symbol {
    kb.try_resolve_symbol("anthill.prelude.PartialEq.neq").expect("neq")
}

#[test]
fn in_body_proof_short_form_loads_as_expr_proof_and_types() {
    // The short form `proof <rule> by <strategy> end <body>` — no
    // `conclude` (the proposal-025 short proof). Loads as `Expr::Proof`
    // and the op types (the proof is transparent to types: its type is
    // the continuation's).
    let kb = common::load_kb_with(
        r#"
        namespace wi538.short
          sort Box
            entity box(value: Int64)
            rule trivial(?x)
            operation f(b: Box) -> Int64 =
              proof trivial by derivation end
              0
          end
        end
        "#,
    );
    let f = kb.try_resolve_symbol("wi538.short.Box.f").expect("f symbol");
    let body = kb.op_body_node(f).expect("op body node for f");
    match body.as_expr() {
        Some(Expr::Proof { target, strategy, using, conclude, body }) => {
            assert_eq!(kb.resolve_sym(*target), "trivial", "target is the rule name");
            assert_eq!(
                strategy.map(|s| kb.resolve_sym(s)),
                Some("derivation"),
                "strategy is `derivation`",
            );
            assert!(using.is_empty(), "no `using` cites");
            assert!(conclude.is_none(), "short form has no conclude goal");
            assert!(body.as_expr().is_some(), "the continuation is an expression");
        }
        other => panic!("expected Expr::Proof, got {other:?}"),
    }
}

#[test]
fn in_body_proof_conclude_form_loads_as_expr_proof_and_types() {
    // The `conclude` form `proof <handle> by <strategy> conclude <P> end
    // <body>` — `P` is an inline goal over a local parameter (the
    // guard-discharge case, no rule to name). Loads with the conclude
    // occurrence and the op types.
    let kb = common::load_kb_with(
        r#"
        namespace wi538.concl
          sort Box
            entity box(value: Int64)
            operation f(b: Box) -> Int64 =
              proof handle by derivation conclude eq(b, b) end
              0
          end
        end
        "#,
    );
    let f = kb.try_resolve_symbol("wi538.concl.Box.f").expect("f symbol");
    let body = kb.op_body_node(f).expect("op body node for f");
    match body.as_expr() {
        Some(Expr::Proof { target, conclude, .. }) => {
            assert_eq!(kb.resolve_sym(*target), "handle", "target is the citation handle");
            assert!(conclude.is_some(), "conclude goal present");
        }
        other => panic!("expected Expr::Proof, got {other:?}"),
    }
}

#[test]
fn in_body_proofs_compose_in_sequence() {
    // Two in-body proofs in a row, then the continuation — the proof is a
    // statement that sequences like `let`, so they nest right.
    let kb = common::load_kb_with(
        r#"
        namespace wi538.seq
          sort Box
            entity box(value: Int64)
            rule one(?x)
            rule two(?x)
            operation f(b: Box) -> Int64 =
              proof one by derivation end
              proof two by derivation end
              0
          end
        end
        "#,
    );
    let f = kb.try_resolve_symbol("wi538.seq.Box.f").expect("f symbol");
    let body = kb.op_body_node(f).expect("op body node for f");
    // Outer proof `one`, whose body is the inner proof `two`.
    let Some(Expr::Proof { target, body, .. }) = body.as_expr() else {
        panic!("outer node is not Expr::Proof");
    };
    assert_eq!(kb.resolve_sym(*target), "one");
    let Some(Expr::Proof { target: inner, .. }) = body.as_expr() else {
        panic!("inner node is not Expr::Proof");
    };
    assert_eq!(kb.resolve_sym(*inner), "two");
}

#[test]
fn proof_is_transparent_to_simp_rewriting() {
    // Regression (code-review, confirmed): a `[simp]` rewrite that fires
    // inside the proof's body must propagate through the typer's ProofStmt
    // reassembly. `simp_rewrite::reassemble` previously dropped it
    // (`Expr::Proof` fell into the leaf catch-all `_ => Rc::clone(occ)`),
    // so the stored tree kept the UN-rewritten body — green typing but a
    // broken downstream tree.
    //
    // The `[simp]` dot rule rewrites `?b.special(7)` → `regular(b, 7)`
    // during typing (no `special` op exists). Wrapped in a proof, the
    // STORED continuation must be the rewritten `regular(...)`, not the
    // original `dot_apply(...)`.
    let kb = common::load_kb_with(
        r#"
        namespace wi538.simp
          sort Box
            entity box(value: Int64)
            operation regular(b: Box, x: Int64) -> Int64 = x
            rule dr: dot_apply(?e, special, ?x) = regular(?e, ?x) [simp]
            operation wrapped(b: Box) -> Int64 =
              proof p by derivation conclude eq(0, 0) end
              ?b.special(7)
          end
        end
        "#,
    );
    let wrapped = kb.try_resolve_symbol("wi538.simp.Box.wrapped").expect("wrapped");
    let body = kb.op_body_node(wrapped).expect("wrapped body");
    let Some(Expr::Proof { body: cont, .. }) = body.as_expr() else {
        panic!("wrapped op body is not Expr::Proof");
    };
    // The [simp] dot rule fired during typing; the proof must have
    // propagated the rewrite into the stored tree.
    match cont.as_expr() {
        Some(Expr::Apply { functor, .. }) => assert_eq!(
            kb.resolve_sym(*functor), "regular",
            "the [simp] rewrite must propagate through the proof — continuation \
             should be `regular`, got apply:{}", kb.resolve_sym(*functor)),
        Some(Expr::DotApply { .. }) => panic!(
            "the [simp] rewrite was DROPPED: the proof continuation is still \
             dot_apply (simp_rewrite::reassemble missing the Expr::Proof arm)"),
        other => panic!("unexpected proof continuation form: {other:?}"),
    }
}

#[test]
fn discharged_conclusion_becomes_a_downstream_gamma_fact() {
    // The proposal-050 in-body-`proof` modification rule, as the typer's
    // `Expr::Proof` handler wires it: a goal proved from a Γ-seeded
    // premise is `assume`d into Γ, so downstream code finds it as a fact
    // (symmetric to a call's `ensures`).
    let mut kb = common::load_kb_with("namespace wi538.feed\nend\n");
    let neq = neq_sym(&mut kb);
    let b = param(&mut kb, "?b");
    let neq_b_0 = goal(neq, vec![b, Value::Int(0)]);

    // Precondition: a symbolic neq(b, 0) with EMPTY Γ flounders — NOT
    // provable (the WI-537 open-world soundness guard).
    assert!(
        !prove_from_gamma(&mut kb, &FlowEnv::empty(), &neq_b_0),
        "neq(b,0) is unprovable with empty Γ (floundering)"
    );

    // The typer assumes a VERIFIED conclusion into Γ (here neq(b, 0), as
    // a Tier-A proof of it from an enclosing premise would).
    let enriched = FlowEnv::empty().assume(&kb, neq_b_0.clone());

    // Downstream: the conclusion is now a Γ fact — provable where it was
    // not before. This is "available as a Γ fact for downstream code."
    assert!(
        prove_from_gamma(&mut kb, &enriched, &neq_b_0),
        "the assumed conclusion is available downstream as a Γ fact"
    );
}
