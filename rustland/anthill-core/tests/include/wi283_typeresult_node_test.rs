//! WI-283 — `TypeResult.node`: the typer is tree-producing.
//!
//! Every `TypeResult` now carries the (possibly-rewritten) occurrence it
//! is the type of (`{ty, env, effects, node}`). This is the substrate for
//! firing `[simp]` rules in the typer: a parent build-frame reassembles
//! itself from its children's result `node`s, and a firing frame swaps in
//! a synthesized RHS. No rule fires yet, so the invariant these tests pin
//! is the *identity* baseline: `type_check_node(occ).node` is the very
//! occurrence passed in (`Rc::ptr_eq`), across the leaf, the
//! `check_*_iter` (Apply/Constructor) path, and a build-frame (`If`) path.
//! They also check node↔type coherence: the result's `node` is the
//! occurrence the `Stamp` frame wrote the inferred type onto.

use std::rc::Rc;

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::Literal;
use anthill_core::kb::typing::{type_check_node, TypingEnv};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::span::{SourceId, SourceSpan};

/// stdlib only — these cases need just the prelude sorts.
fn load_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    assert!(!files.is_empty(), "no stdlib files found");
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib load failed");
    kb
}

/// A source-origin expression occurrence with a throwaway span.
fn occ(expr: Expr) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(expr, SourceSpan::new(SourceId::from_raw(0), 0, 0), None)
}

/// Type `input` (asserting success) and assert the result's `node` is the
/// *same* occurrence (identity — nothing rewrites yet) and that the
/// inferred type the `Stamp` frame recorded lives on that node.
fn assert_node_identity(kb: &mut KnowledgeBase, input: &Rc<NodeOccurrence>) {
    let env = TypingEnv::empty();
    let r = type_check_node(kb, &env, input, None)
        .unwrap_or_else(|e| panic!("expected the occurrence to type-check; got {e:?}"));
    assert!(
        Rc::ptr_eq(&r.node, input),
        "TypeResult.node must be the input occurrence (identity) until a rule fires",
    );
    // node↔type coherence: Stamp wrote `r.ty` onto `r.node`. WI-342:
    // `inferred_type` stays a hash-consed `TermId` (the Stamp frame re-grounds
    // the carrier-agnostic `ty`); for this ground type it is the same TermId.
    assert_eq!(
        r.node.inferred_type(),
        r.ty.as_term(),
        "the result's node carries the inferred type the Stamp frame recorded",
    );
}

#[test]
fn node_identity_for_leaf() {
    let mut kb = load_kb();
    let n3 = occ(Expr::Const(Literal::Int(3)));
    assert_node_identity(&mut kb, &n3);
}

#[test]
fn node_identity_for_constructor() {
    let mut kb = load_kb();
    let nil = kb
        .try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil registered");
    let cons = kb
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons registered");
    let head = kb.intern("head");
    let tail = kb.intern("tail");

    // cons(head: 1, tail: nil()) routes through the Constructor build
    // frame + check_constructor_iter — the node must come back identical.
    let o1 = occ(Expr::Const(Literal::Int(1)));
    let onil = occ(Expr::Constructor { name: nil, pos_args: vec![], named_args: vec![] });
    let ocons = occ(Expr::Constructor {
        name: cons,
        pos_args: vec![],
        named_args: vec![(head, Rc::clone(&o1)), (tail, Rc::clone(&onil))],
    });
    assert_node_identity(&mut kb, &ocons);
    // Children are typed and carry their own node-type too.
    assert!(o1.inferred_type().is_some(), "child `1` typed");
    assert!(onil.inferred_type().is_some(), "child `nil()` typed");
}

#[test]
fn node_identity_for_if_build_frame() {
    let mut kb = load_kb();
    // `if true then 1 else 2` routes through the IfExpr build frame.
    let cond = occ(Expr::Const(Literal::Bool(true)));
    let then_b = occ(Expr::Const(Literal::Int(1)));
    let else_b = occ(Expr::Const(Literal::Int(2)));
    let oif = occ(Expr::If {
        condition: cond,
        then_branch: then_b,
        else_branch: else_b,
    });
    assert_node_identity(&mut kb, &oif);
}
