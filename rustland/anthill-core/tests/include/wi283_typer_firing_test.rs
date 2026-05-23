//! WI-283 — type-directed `[simp]` firing woven into the typer.
//!
//! Firing moved from the standalone pre-typer `simp_rewrite::run` pass into
//! the typer's `build_type` walk: as the typer types an Apply/Constructor
//! node (children typed first), it reassembles the node from its children's
//! (possibly-rewritten) `TypeResult.node`s, fires a matching `[simp]` rule,
//! and re-types the RHS to fixpoint. The rewrite propagates up via
//! `TypeResult.node`. These tests pin the firing behaviour at the typer
//! call site (`type_check_node`), reusing the `add_zero` rule shape; the
//! shared firing helpers themselves are also covered by `simp_rewrite`'s
//! unit tests over the bare occurrence representation.

use std::rc::Rc;

use anthill_core::intern::Symbol;
use anthill_core::kb::load;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::typing::{min_sort, type_check_node, TypingEnv};
use anthill_core::kb::KnowledgeBase;
use anthill_core::span::{SourceId, SourceSpan};
use smallvec::SmallVec;

/// A KB with the prelude registered — the typer needs the
/// `anthill.prelude.Type.*` / `Int` / `Bool` symbols to build leaf types.
/// (The bare-`new()` `simp_rewrite` unit tests don't, since they call the
/// firing helpers directly without type-checking.)
fn fresh_kb() -> KnowledgeBase {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    kb
}

fn span() -> SourceSpan {
    SourceSpan::new(SourceId::from_raw(0), 0, 10)
}

fn occ(e: Expr) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(e, span(), None)
}

/// Assert the `[simp]` equation `add(?x, 0) = ?x` (ground-headed, Global
/// vars — the minimal shape; mirrors `simp_rewrite`'s test helper).
/// Returns the `add` symbol.
fn assert_add_zero(kb: &mut KnowledgeBase) -> Symbol {
    let eq_sym = kb.eq_functor();
    let add = kb.intern("add");
    let x_sym = kb.intern("x");
    let vx = kb.fresh_var(x_sym);
    let var_x = kb.alloc(Term::Var(Var::Global(vx)));
    let zero = kb.alloc(Term::Const(Literal::Int(0)));
    let lhs = kb.alloc(Term::Fn {
        functor: add,
        pos_args: SmallVec::from_slice(&[var_x, zero]),
        named_args: SmallVec::new(),
    });
    let eq_head = kb.alloc(Term::Fn {
        functor: eq_sym,
        pos_args: SmallVec::from_slice(&[lhs, var_x]),
        named_args: SmallVec::new(),
    });
    let simp_sym = kb.intern("simp");
    let meta_sym = kb.intern("meta");
    let tru = kb.alloc(Term::Const(Literal::Bool(true)));
    let meta = kb.alloc(Term::Fn {
        functor: meta_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(simp_sym, tru)]),
    });
    let sort = kb.make_name_term("Eq");
    let domain = kb.make_name_term("test");
    kb.assert_fact(eq_head, sort, domain, Some(meta));
    add
}

/// Assert the *non-terminating* `[simp]` equation `add(?a, ?b) = add(?b, ?a)`
/// (a commutative law — the design's canonical "must stay bare or it loops"
/// example). Returns the `add` symbol.
fn assert_add_comm(kb: &mut KnowledgeBase) -> Symbol {
    let eq_sym = kb.eq_functor();
    let add = kb.intern("add");
    let a_sym = kb.intern("a");
    let b_sym = kb.intern("b");
    let va = kb.fresh_var(a_sym);
    let vb = kb.fresh_var(b_sym);
    let var_a = kb.alloc(Term::Var(Var::Global(va)));
    let var_b = kb.alloc(Term::Var(Var::Global(vb)));
    let lhs = kb.alloc(Term::Fn {
        functor: add,
        pos_args: SmallVec::from_slice(&[var_a, var_b]),
        named_args: SmallVec::new(),
    });
    let rhs = kb.alloc(Term::Fn {
        functor: add,
        pos_args: SmallVec::from_slice(&[var_b, var_a]),
        named_args: SmallVec::new(),
    });
    let eq_head = kb.alloc(Term::Fn {
        functor: eq_sym,
        pos_args: SmallVec::from_slice(&[lhs, rhs]),
        named_args: SmallVec::new(),
    });
    let simp_sym = kb.intern("simp");
    let meta_sym = kb.intern("meta");
    let tru = kb.alloc(Term::Const(Literal::Bool(true)));
    let meta = kb.alloc(Term::Fn {
        functor: meta_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(simp_sym, tru)]),
    });
    let sort = kb.make_name_term("Eq");
    let domain = kb.make_name_term("test");
    kb.assert_fact(eq_head, sort, domain, Some(meta));
    add
}

#[test]
fn nonterminating_simp_rule_is_fuel_bounded_not_a_stack_overflow() {
    // A commutative `[simp]` rule loops forever (add(7,8) → add(8,7) → …).
    // The typer firing must bottom out at `fuel == 0` and return — exactly
    // as the fuel-bounded `simp_rewrite::run` did — rather than recursing
    // the host stack to overflow. Reaching the assertion at all proves
    // termination; the surviving redex (`add` is not a registered op) then
    // surfaces as a type error.
    let mut kb = fresh_kb();
    let add = assert_add_comm(&mut kb);

    let seven = occ(Expr::Const(Literal::Int(7)));
    let eight = occ(Expr::Const(Literal::Int(8)));
    let body = occ(Expr::Apply {
        functor: add,
        pos_args: vec![seven, eight],
        named_args: vec![],
        type_args: vec![],
    });

    let env = TypingEnv::empty();
    let r = type_check_node(&mut kb, &env, &body, None);
    assert!(
        r.is_err(),
        "a non-terminating [simp] rule must bottom out at fuel 0 leaving the \
         (untypeable) redex, not loop or crash",
    );
}

#[test]
fn typer_fires_simp_rule_at_apply() {
    let mut kb = fresh_kb();
    let add = assert_add_zero(&mut kb);

    // body: add(7, 0)
    let seven = occ(Expr::Const(Literal::Int(7)));
    let zero = occ(Expr::Const(Literal::Int(0)));
    let body = occ(Expr::Apply {
        functor: add,
        pos_args: vec![Rc::clone(&seven), zero],
        named_args: vec![],
        type_args: vec![],
    });

    let env = TypingEnv::empty();
    let r = type_check_node(&mut kb, &env, &body, None).expect("add(7,0) types");

    // add_zero fired during type-checking: the result node is the reused
    // matched child `7`, and it carries Int as its inferred type.
    assert!(
        matches!(r.node.as_expr(), Some(Expr::Const(Literal::Int(7)))),
        "expected add(7,0) to rewrite to 7, got {:?}",
        r.node.as_expr(),
    );
    assert!(
        Rc::ptr_eq(&r.node, &seven),
        "the RHS reuses the matched `7` child occurrence (identity preserved)",
    );
    let ms = min_sort(&kb, &r.node).expect("rewritten node carries a declared sort");
    let ty_name = kb.resolve_sym(ms);
    assert!(ty_name == "Int" || ty_name.ends_with(".Int"), "result type Int, got {ty_name}");
}

#[test]
fn typer_cascades_nested_redex_to_fixpoint() {
    let mut kb = fresh_kb();
    let add = assert_add_zero(&mut kb);

    // body: add(add(7, 0), 0) — inner fires → 7, then outer add(7,0) fires → 7.
    let seven = occ(Expr::Const(Literal::Int(7)));
    let zero_inner = occ(Expr::Const(Literal::Int(0)));
    let zero_outer = occ(Expr::Const(Literal::Int(0)));
    let inner = occ(Expr::Apply {
        functor: add,
        pos_args: vec![Rc::clone(&seven), zero_inner],
        named_args: vec![],
        type_args: vec![],
    });
    let body = occ(Expr::Apply {
        functor: add,
        pos_args: vec![inner, zero_outer],
        named_args: vec![],
        type_args: vec![],
    });

    let env = TypingEnv::empty();
    let r = type_check_node(&mut kb, &env, &body, None).expect("nested add types");
    assert!(
        Rc::ptr_eq(&r.node, &seven),
        "add(add(7,0),0) should cascade to the innermost matched `7`, got {:?}",
        r.node.as_expr(),
    );
}

#[test]
fn typer_rewrites_redex_under_an_if_branch() {
    // Reassembly must propagate a rewrite out of a wrapper frame (`If`):
    // `if true then add(7,0) else 9` → the then-branch becomes `7`.
    let mut kb = fresh_kb();
    let add = assert_add_zero(&mut kb);

    let cond = occ(Expr::Const(Literal::Bool(true)));
    let seven = occ(Expr::Const(Literal::Int(7)));
    let zero = occ(Expr::Const(Literal::Int(0)));
    let then_b = occ(Expr::Apply {
        functor: add,
        pos_args: vec![Rc::clone(&seven), zero],
        named_args: vec![],
        type_args: vec![],
    });
    let else_b = occ(Expr::Const(Literal::Int(9)));
    let body = occ(Expr::If { condition: cond, then_branch: then_b, else_branch: else_b });

    let env = TypingEnv::empty();
    let r = type_check_node(&mut kb, &env, &body, None).expect("if types");
    match r.node.as_expr() {
        Some(Expr::If { then_branch, .. }) => {
            assert!(
                Rc::ptr_eq(then_branch, &seven),
                "the if's then-branch should be the rewritten `7`, got {:?}",
                then_branch.as_expr(),
            );
        }
        other => panic!("expected an If node (rebuilt with rewritten branch), got {other:?}"),
    }
}

#[test]
fn typer_and_resolver_phases_agree() {
    // Phase agreement (proposal 043 §4.7): the same `[simp]` rule reduces
    // add(7, 0) → 7 both in the resolver (term, via `simplify`) and in the
    // typer (occurrence, via `type_check_node`).
    let mut kb = fresh_kb();
    let add = assert_add_zero(&mut kb);

    let seven_t = kb.alloc(Term::Const(Literal::Int(7)));
    let zero_t = kb.alloc(Term::Const(Literal::Int(0)));
    let add_t = kb.alloc(Term::Fn {
        functor: add,
        pos_args: SmallVec::from_slice(&[seven_t, zero_t]),
        named_args: SmallVec::new(),
    });
    assert_eq!(kb.simplify(add_t), seven_t, "resolver phase: add(7,0) → 7");

    let seven_o = occ(Expr::Const(Literal::Int(7)));
    let zero_o = occ(Expr::Const(Literal::Int(0)));
    let body = occ(Expr::Apply {
        functor: add,
        pos_args: vec![Rc::clone(&seven_o), zero_o],
        named_args: vec![],
        type_args: vec![],
    });
    let env = TypingEnv::empty();
    let r = type_check_node(&mut kb, &env, &body, None).expect("typer phase types");
    assert!(
        matches!(r.node.as_expr(), Some(Expr::Const(Literal::Int(7)))),
        "typer phase: add(7,0) → 7, got {:?}",
        r.node.as_expr(),
    );
}
