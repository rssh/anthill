//! WI-425: a DotApply occurrence and the `dot_apply` term the loader emits for
//! the same `r.name(args)` are ISOMORPHIC through `TermView`.
//!
//! WI-397 made `Expr::DotApply` structural in the occurrence view, but the view
//! was NOT isomorphic to the term twin: the loader always builds
//! `dot_apply(receiver, name, args: List[ApplyArg])` — arity-3 named — while
//! the view read a field form as arity-2 `{name, receiver}` and rode a method
//! form's call args as direct positional/named children. The two carriers thus
//! produced DIFFERENT discrim keys, so a fact stored under one carrier could
//! never match a query in the other (discrim-query-is-the-unifier: that is a
//! wrong answer, not a perf loss).
//!
//! Acceptance (ticket): identical TermView head/keys/children for both
//! carriers; indexing one carrier and querying with the other matches.

use std::rc::Rc;

use anthill_core::eval::value::Value;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::term_view::{views_structurally_equal, TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::span::SourceSpan;
use anthill_core::intern::Symbol;
use smallvec::SmallVec;

/// A KB with the full stdlib loaded — every reflect / prelude symbol the
/// dot_apply encoding uses is resolved, exactly as in any loader-built KB.
fn stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
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
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib loads");
    kb
}

fn fn_term(kb: &mut KnowledgeBase, functor: Symbol, named: &[(Symbol, TermId)]) -> TermId {
    kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(named),
    })
}

/// The TERM twin for `p.shift(1, k: 2)`, built exactly like the loader does
/// (load.rs `LoadBuildFrame::DotApply` / `mk_apply_arg` / `build_list`):
/// `dot_apply(receiver: Ref(p), name: Ref(shift),
///            args: [ApplyArg(name: none(), value: 1),
///                   ApplyArg(name: some(value: Ref(k)), value: 2)])`.
fn dot_term(kb: &mut KnowledgeBase, pos_value: TermId) -> TermId {
    let dot_apply = kb.try_resolve_symbol("anthill.reflect.Expr.dot_apply").unwrap();
    let apply_arg = kb.try_resolve_symbol("anthill.reflect.ApplyArg").unwrap();
    let cons = kb.try_resolve_symbol("anthill.prelude.List.cons").unwrap();
    let nil = kb.try_resolve_symbol("anthill.prelude.List.nil").unwrap();
    let some = kb.try_resolve_symbol("anthill.prelude.Option.some").unwrap();
    let none = kb.try_resolve_symbol("anthill.prelude.Option.none").unwrap();
    let (p, shift, k) = (kb.intern("p"), kb.intern("shift"), kb.intern("k"));
    let (k_receiver, k_name, k_args) =
        (kb.intern("receiver"), kb.intern("name"), kb.intern("args"));
    let (k_head, k_tail, k_value) =
        (kb.intern("head"), kb.intern("tail"), kb.intern("value"));

    let receiver = kb.alloc(Term::Ref(p));
    let name_ref = kb.alloc(Term::Ref(shift));
    let none_t = fn_term(kb, none, &[]);
    let arg0 = fn_term(kb, apply_arg, &[(k_name, none_t), (k_value, pos_value)]);
    let k_ref = kb.alloc(Term::Ref(k));
    let some_t = fn_term(kb, some, &[(k_value, k_ref)]);
    let two = kb.alloc(Term::Const(Literal::Int(2)));
    let arg1 = fn_term(kb, apply_arg, &[(k_name, some_t), (k_value, two)]);
    let nil_t = fn_term(kb, nil, &[]);
    let cell1 = fn_term(kb, cons, &[(k_head, arg1), (k_tail, nil_t)]);
    let cell0 = fn_term(kb, cons, &[(k_head, arg0), (k_tail, cell1)]);
    fn_term(kb, dot_apply, &[(k_receiver, receiver), (k_name, name_ref), (k_args, cell0)])
}

fn occ(expr: Expr) -> Rc<NodeOccurrence> {
    use anthill_core::span::SourceId;
    NodeOccurrence::new_expr(expr, SourceSpan::new(SourceId::from_raw(0), 0, 0), None)
}

/// The OCCURRENCE for the same `p.shift(1, k: 2)` — receiver `Ref(p)`, member
/// `shift`, one positional + one named call arg, as the loader's
/// `node_occurrence::BuildFrame::DotApply` builds it.
fn dot_occ(kb: &mut KnowledgeBase, pos_child: Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
    let (p, shift, k) = (kb.intern("p"), kb.intern("shift"), kb.intern("k"));
    occ(Expr::DotApply {
        receiver: occ(Expr::Ref(p)),
        name: shift,
        pos_args: vec![pos_child],
        named_args: vec![(k, occ(Expr::Const(Literal::Int(2))))],
    })
}

#[test]
fn dotapply_view_is_isomorphic_to_term_twin() {
    let mut kb = stdlib_kb();
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let term = dot_term(&mut kb, one);
    let node = Value::Node(dot_occ(&mut kb, occ(Expr::Const(Literal::Int(1)))));

    // Identical heads: same functor, pos_arity 0, named_arity 3.
    match (node.head(&kb), term.head(&kb)) {
        (
            ViewHead::Functor { functor: fa, pos_arity: pa, named_arity: na },
            ViewHead::Functor { functor: fb, pos_arity: pb, named_arity: nb },
        ) => {
            assert_eq!(fa, fb, "same dot_apply functor");
            assert_eq!((pa, na), (0, 3), "occurrence head is arity-3 named");
            assert_eq!((pb, nb), (0, 3), "term head is arity-3 named");
        }
        (a, b) => panic!("non-functor head: occ={a:?} term={b:?}"),
    }

    // Identical named keys, in the same order (the discrim walk descends in
    // `named_keys` order — order divergence alone would desync the walk).
    assert_eq!(
        node.named_keys(&kb),
        term.named_keys(&kb),
        "named keys identical and identically ordered",
    );

    // Full deep structural equality, both directions.
    assert!(
        views_structurally_equal(&kb, &node, &term),
        "occurrence ≡ term through TermView",
    );
    assert!(
        views_structurally_equal(&kb, &term, &node),
        "term ≡ occurrence through TermView",
    );
}

#[test]
fn dotapply_cross_carrier_discrim_match() {
    let mut kb = stdlib_kb();
    let fact_sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test");
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let term = dot_term(&mut kb, one);
    kb.assert_fact(term, fact_sort, domain, None);

    // Index the TERM carrier, query with the OCCURRENCE carrier: must match.
    let node = Value::Node(dot_occ(&mut kb, occ(Expr::Const(Literal::Int(1)))));
    assert_eq!(
        kb.query_view(&node).len(),
        1,
        "occurrence query matches the term-indexed fact",
    );

    // Precision: a different call arg must NOT match.
    let other = Value::Node(dot_occ(&mut kb, occ(Expr::Const(Literal::Int(9)))));
    assert_eq!(kb.query_view(&other).len(), 0, "different arg does not match");

    // Term-side pattern unified against the occurrence target (the temp-tree
    // direction `match_view` exercises): must also match.
    assert!(
        kb.match_view(term, &node).is_some(),
        "term pattern matches the occurrence target",
    );
}

#[test]
fn dotapply_occurrence_goal_var_binds_through_args_list() {
    // A goal-side var INSIDE the synthesized `args` spine (the positional call
    // arg's value) binds against the term fact's subterm — the deferred
    // VarPath extraction (WI-373) descends both carriers along the same keys.
    let mut kb = stdlib_kb();
    let fact_sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test");
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let term = dot_term(&mut kb, one);
    kb.assert_fact(term, fact_sort, domain, None);

    let x = kb.intern("x");
    let vid = kb.fresh_var(x);
    let goal = Value::Node(dot_occ(&mut kb, occ(Expr::Var(Var::Global(vid)))));
    let hits = kb.query_view(&goal);
    assert_eq!(hits.len(), 1, "var-arg occurrence goal matches the fact");
    assert_eq!(
        hits[0].1.resolve_as_value(vid).map(|v| v.expect_term()),
        Some(one),
        "?x bound to the fact's positional arg value through the args list",
    );
}
