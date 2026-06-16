//! WI-487 — an op-body `?b` that references a parameter carries that
//! parameter's own `Symbol`, not a freshly-interned twin.
//!
//! ROOT CAUSE (diagnosed under WI-483): a `?b` reference in an operation body
//! is a `Term::Var(Global)` in the parse IR. The generic `convert_term` mints a
//! FRESH logical var, re-interning the name, so the body var and the
//! `OperationInfo` param Symbol diverged and only bridged by short name
//! downstream (the typer's now-removed short-name fallback, eval `find_local`).
//! The loader's `load_op_body_var` now resolves a param-named `?b` to the
//! param's Symbol, so an op_body_node param var Symbol == the matching
//! `OperationInfo.params[i]` Symbol — letting the typer's exact `lookup_var`
//! hit and unblocking the WI-483 method-op fold (match a param by Symbol).

use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{for_each_child, Expr, NodeKind, NodeOccurrence};
use anthill_core::kb::term::Var;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use std::rc::Rc;

fn load_kb(extra: &str) -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|errs| panic!("load: {errs:?}"));
    kb
}

/// Collect the name `Symbol` of every `Expr::Var(Global)` in a body subtree.
fn collect_global_var_names(occ: &Rc<NodeOccurrence>, out: &mut Vec<Symbol>) {
    if let NodeKind::Expr { expr, .. } = &occ.kind {
        if let Expr::Var(Var::Global(vid)) = expr {
            out.push(vid.name());
        }
        for_each_child(expr, |c| collect_global_var_names(c, out));
    }
}

/// The acceptance: a `?b` receiver in `use_peek(b: Box) -> Int64 = ?b.peek()`
/// carries the same Symbol the OperationInfo records for param `b`.
#[test]
fn op_body_param_var_shares_operationinfo_symbol() {
    let src = r#"
        namespace wi487.peek
          export Box
          sort Box
            entity box(value: Int64)
            operation peek(b: Box) -> Int64 = 42
            operation use_peek(b: Box) -> Int64 = ?b.peek()
          end
        end
    "#;
    let kb = load_kb(src);
    let use_peek = kb
        .try_resolve_symbol("wi487.peek.Box.use_peek")
        .expect("use_peek symbol");

    // The param Symbol the OperationInfo records.
    let rec = anthill_core::kb::op_info::lookup_operation_info(&kb, use_peek)
        .expect("OperationInfo for use_peek");
    assert_eq!(rec.params.len(), 1, "use_peek has one param");
    let param_sym = rec.params[0].0;
    assert_eq!(kb.resolve_sym(param_sym), "b");

    // The op body's `?b` var(s) must carry that exact Symbol — by IDENTITY,
    // not merely by name. Before WI-487 this was a distinct freshly-interned
    // "b" Symbol.
    let body = kb.op_body_node(use_peek).expect("op_body_node for use_peek");
    let mut names = Vec::new();
    collect_global_var_names(body, &mut names);
    assert!(
        !names.is_empty(),
        "expected at least one ?b var in the body node, found none"
    );
    for n in &names {
        assert_eq!(
            *n,
            param_sym,
            "op-body var '{}' (Symbol {:?}) must equal the OperationInfo param Symbol {:?}",
            kb.resolve_sym(*n),
            n,
            param_sym
        );
    }
}

/// A let-bound `?x` shadowing nothing param-named keeps the generic behavior
/// (binder and body var share an intern) — the fix only special-cases
/// param-named free vars, so a non-param `?x` still type-checks and evaluates.
#[test]
fn op_body_non_param_var_still_loads() {
    let src = r#"
        namespace wi487.local
          export Box
          sort Box
            entity box(value: Int64)
            operation twice(b: Box) -> Int64 =
              let x = 21
                x + x
          end
        end
    "#;
    // No panic / load error: the `?x`-free let body loads and types fine.
    let _kb = load_kb(src);
}

/// SHADOWING regression: the parser shares ONE parse `VarId` for every `?b` in
/// an operation, even across lexical scopes. Here `?b` denotes a `Tag` (a `let`
/// binder) in the value position and the `Box` parameter in the body. The fix
/// must resolve each occurrence by ITS OWN scope — the let-ref via the generic
/// (intern-named) path so it dispatches `read` on `Tag`, the param-ref via the
/// param Symbol so it dispatches `peek` on `Box`. A `vid`-keyed cache that let
/// the first-visited occurrence's Symbol leak to the other would mis-dispatch
/// one method (and, with the short-name fallback now gone, fail to type-check).
#[test]
fn op_body_shadowed_and_param_var_resolve_independently() {
    let src = r#"
        namespace wi487.shadow
          export Box
          export Tag
          sort Box
            entity box(value: Int64)
            operation peek(b: Box) -> Int64 = 42
          end
          sort Tag
            entity tag(label: Int64)
            operation read(t: Tag) -> Int64 = 7
          end
          operation pick(b: Box) -> Int64 =
            let inner =
              let b = tag(label: 9)
                ?b.read()
            ?b.peek()
        end
    "#;
    // Both `?b` occurrences must dispatch on the right sort and type-check.
    let _kb = load_kb(src);
}
