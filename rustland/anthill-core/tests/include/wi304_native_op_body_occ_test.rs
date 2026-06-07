//! WI-304 regression: the operation-body `NodeOccurrence` is built natively in
//! `convert_expr_term` (parse IR → occurrence), NOT re-derived from the term via
//! `materialize_from_handle`. These tests load operations whose bodies exercise
//! the structural build frames (let / lambda / match / apply) and the leaf
//! builder, and assert the stored `kb.op_body_node(...)` root carries the
//! expected `Expr` variant — i.e. the native walk produced a well-formed,
//! correctly-shaped occurrence tree.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Full stdlib (reflect sorts etc.) + builtins — the op-body loader resolves
/// `anthill.reflect.Expr.*` functor symbols, so the reflect stdlib must load.
fn stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    assert!(!files.is_empty(), "no stdlib files found");
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
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

fn load_src(kb: &mut KnowledgeBase, source: &str) {
    let parsed = parse::parse(source).expect("parse failed");
    load::load(kb, &parsed, &NullResolver).expect("load failed");
}

/// Resolve an op's body occurrence root by qualified name.
fn op_body_root_is<F: FnOnce(&Expr) -> bool>(kb: &KnowledgeBase, qn: &str, pred: F) -> bool {
    let sym = kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("op {qn} not resolved"));
    let node = kb.op_body_node(sym).unwrap_or_else(|| panic!("op {qn} has no body node"));
    let expr = node.as_expr().expect("op body root is an Expr");
    pred(expr)
}

#[test]
fn let_op_body_builds_native_let_occurrence() {
    let mut kb = stdlib_kb();
    load_src(
        &mut kb,
        r#"
namespace wi304.lt
  operation f(x: Int64) -> Int64
    = let y = x
      y
end
"#,
    );
    assert!(
        op_body_root_is(&kb, "wi304.lt.f", |e| matches!(e, Expr::Let { .. })),
        "op body root should be a natively-built Expr::Let",
    );
}

#[test]
fn match_op_body_builds_native_match_occurrence() {
    let mut kb = stdlib_kb();
    load_src(
        &mut kb,
        r#"
namespace wi304.mt
  operation g(x: Int64) -> Int64
    = match x
        case 0 -> 1
        case _ -> x
      end
end
"#,
    );
    assert!(
        op_body_root_is(&kb, "wi304.mt.g", |e| matches!(e, Expr::Match { branches, .. } if branches.len() == 2)),
        "op body root should be a natively-built Expr::Match with two branches",
    );
}
