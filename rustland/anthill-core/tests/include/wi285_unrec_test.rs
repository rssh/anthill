//! WI-285 — the typer's last recursive-helper arms (If / collection
//! literals) are now work-stack Build frames, so the whole typer is one
//! iterative walk.
//!
//! A deeply-nested else-if chain nests in the *else* branch, so the
//! former `check_if_expr` re-entered `type_check_node` once per level —
//! the residual host-stack-overflow class the other arms' earlier
//! un-recursing removed. With the `IfExpr` Build frame the descent is on
//! the heap, so a chain far deeper than the host-stack budget types
//! without crashing. The collection-literal test pins behavior
//! preservation for the `ListLit`/`SetLit`/`TupleLit` frames.

use std::rc::Rc;

use anthill_core::kb::load;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::Literal;
use anthill_core::kb::typing::{min_sort, type_check_node, TypingEnv};
use anthill_core::kb::KnowledgeBase;
use anthill_core::span::{SourceId, SourceSpan};

/// Interning + builtins, no stdlib parse — the const leaves and
/// `make_sort_ref_by_name` the typer uses here need nothing more.
fn minimal_kb() -> KnowledgeBase {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    kb
}

/// A source-origin expression occurrence with a throwaway span.
fn occ(expr: Expr) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(expr, SourceSpan::new(SourceId::from_raw(0), 0, 0), None)
}

/// A sort symbol resolves to `name` exactly or to a qualified path
/// ending in `.name`.
fn sort_is(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>, name: &str) {
    let ms = min_sort(kb, occ).expect("occurrence should carry a min_sort");
    let full = kb.resolve_sym(ms);
    assert!(
        full == name || full.ends_with(&format!(".{name}")),
        "expected min_sort {name}, got {full}",
    );
}

#[test]
fn deeply_nested_else_if_types_without_host_stack_overflow() {
    let mut kb = minimal_kb();
    // if true then 0 else (if true then 0 else (… else 0)) — nested in
    // the else branch DEPTH levels deep. The recursive `check_if_expr`
    // re-entered `type_check_node` per level, so a chain this deep
    // overflowed the host stack; the `IfExpr` Build frame keeps it on
    // the heap.
    const DEPTH: usize = 50_000;
    let mut node = occ(Expr::Const(Literal::Int(0)));
    for _ in 0..DEPTH {
        let condition = occ(Expr::Const(Literal::Bool(true)));
        let then_branch = occ(Expr::Const(Literal::Int(0)));
        node = occ(Expr::If { condition, then_branch, else_branch: node });
    }
    let env = TypingEnv::empty();
    let r = type_check_node(&mut kb, &env, &node, None);
    assert!(r.is_ok(), "deep else-if chain should type-check; got {:?}", r.err());
    // The if's type is the then-branch's type (Int) — confirms the
    // IfExpr frame *assembles* the result, not merely survives.
    sort_is(&kb, &node, "Int");
}

#[test]
fn collection_literal_frames_assemble_types() {
    // Behavior preservation for the un-recursed collection arms.
    let mut kb = minimal_kb();
    let env = TypingEnv::empty();

    // [1, 2, 3] : List[T = Int]; first element carries its own type too.
    let first = occ(Expr::Const(Literal::Int(1)));
    let list = occ(Expr::ListLit(vec![
        Rc::clone(&first),
        occ(Expr::Const(Literal::Int(2))),
        occ(Expr::Const(Literal::Int(3))),
    ]));
    assert!(type_check_node(&mut kb, &env, &list, None).is_ok(), "list literal should type");
    sort_is(&kb, &list, "List");
    sort_is(&kb, &first, "Int"); // child stamping preserved

    // {1} : Set[T = Int].
    let set = occ(Expr::SetLit(vec![occ(Expr::Const(Literal::Int(1)))]));
    assert!(type_check_node(&mut kb, &env, &set, None).is_ok(), "set literal should type");
    sort_is(&kb, &set, "Set");

    // (1, true) : named-tuple — types Ok, fields stamped.
    let tup_int = occ(Expr::Const(Literal::Int(1)));
    let tup = occ(Expr::TupleLit {
        positional: vec![Rc::clone(&tup_int), occ(Expr::Const(Literal::Bool(true)))],
        named: vec![],
    });
    assert!(type_check_node(&mut kb, &env, &tup, None).is_ok(), "tuple literal should type");
    sort_is(&kb, &tup_int, "Int"); // positional field stamped
}
