//! WI-228 — thread WI-224's `ResolvedRequiresNode` through dispatch into the
//! requirement-projection IR emitter.
//!
//! Before WI-228, `find_unique_impl_op` collapsed both `Leaf` and
//! `Conditional` resolutions into `DispatchOutcome::Unique(symbol)` —
//! sub_resolutions dropped on the floor. Pin-now's apply_within
//! emitted requirements via the per-dep recursive search (WI-227's
//! `build_dep_projection`), which had no way to see what the
//! conditional impl was actually constructed from. Symptom: a
//! conditional impl in real source produced an empty requirements
//! list (the previous test path threaded `callee_spec_sort =
//! spec_sort`, and the spec has no `requires`).
//!
//! After WI-228, `dispatch_spec_op_with_tree` returns the full
//! `ResolvedRequiresNode` alongside the impl symbol; `record_apply_within_concrete`
//! threads it into `build_projected_requirements_list_from_tree`, which
//! walks `tree.sub_resolutions` and emits one IR entry per impl-side
//! `requires` slot via WI-227's `emit_tree_as_projection`. A
//! conditional impl now produces nested `construct_requirement` IR
//! through real dispatch.
//!
//! Reference: docs/design/operation-call-model.md §"Resolution"
//! ("Output ResolvedRequiresNode is the direct input to the requirement-
//! insertion pass"); WI-227 commit 91578d2 for the IR emitter.

mod common;

use anthill_core::kb::term::Term;
use anthill_core::kb::typing::get_named_arg;
use common::interp_for;

#[test]
fn pin_now_threads_conditional_tree_into_nested_construct_requirement() {
    // Setup: an EqList carrier that conditionally provides Eq for
    // List[T = A] given Eq[T = A]. The driver calls `eq(x, y)` at
    // T = List[Int] — Pin-now resolves to EqList.eq with a
    // Conditional tree whose sole sub_resolution is the rustland's
    // `fact Eq[T = Int]` leaf (Int as the carrier).
    let src = r#"
namespace test.wi228.pin_now_tree
  import anthill.prelude.{Eq, List, Int, Bool}
  export EqList, Driver
  sort EqList
    sort A = ?
    requires Eq[T = A]
    fact Eq[T = List[T = A]]
    operation eq(x: List[T = A], y: List[T = A]) -> Bool = true
  end
  sort Driver
    import anthill.prelude.Eq.{eq}
    operation drive(x: List[T = Int], y: List[T = Int]) -> Bool = eq(x, y)
  end
end
"#;
    let interp = interp_for(src);
    let kb = interp.kb();

    let eq_spec_sym = kb
        .try_resolve_symbol("anthill.prelude.Eq.eq")
        .expect("Eq.eq registered");
    let int_sym = kb
        .try_resolve_symbol("anthill.prelude.Int")
        .expect("Int registered");
    let impl_eq_sym = kb
        .try_resolve_symbol("test.wi228.pin_now_tree.EqList.eq")
        .expect("EqList.eq registered");
    let aw_sym = kb
        .try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .expect("apply_within in stdlib");
    let cr_sym = kb
        .try_resolve_symbol("anthill.reflect.Expr.construct_requirement")
        .expect("construct_requirement in stdlib");
    let nil_sym = kb
        .try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil in stdlib");
    let cons_sym = kb
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons in stdlib");

    // Find Driver.drive's `eq()` call rewrite.
    let mut rewritten_for_eq = None;
    for (rewritten_tid, spec_sym) in kb.dispatch_origin_iter() {
        if spec_sym == eq_spec_sym {
            rewritten_for_eq = Some(rewritten_tid);
        }
    }
    let rewritten_tid =
        rewritten_for_eq.expect("eq(x, y) at T = List[Int] must be Pin-now-rewritten");

    // apply_within(fn = Ref(EqList.eq), args = ?, requirements = ?)
    let (functor, named_args) = match kb.get_term(rewritten_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("rewritten term must be Fn; got {other:?}"),
    };
    assert_eq!(
        functor, aw_sym,
        "Pin-now to impl with `requires` must emit apply_within; got {}",
        kb.qualified_name_of(functor)
    );

    let fn_tid = get_named_arg(kb, &named_args, "fn").expect("apply_within `fn`");
    match kb.get_term(fn_tid) {
        Term::Ref(s) => assert_eq!(
            *s, impl_eq_sym,
            "fn must Ref the impl op (EqList.eq); got Ref({})",
            kb.qualified_name_of(*s)
        ),
        other => panic!("apply_within fn must be Ref(impl); got {other:?}"),
    }

    // WI-234 Model 1: requirements is a single-entry list containing
    // the dispatching dict (the whole resolved tree, not just its
    // sub-resolutions). Shape:
    //   requirements = cons(
    //     construct_requirement(EqList, [          -- the dispatching dict
    //       construct_requirement(Int, [])         -- EqList's sole sub-instance
    //     ]),
    //     nil
    //   )
    let eqlist_sym = kb
        .try_resolve_symbol("test.wi228.pin_now_tree.EqList")
        .expect("EqList sort registered");

    let reqs_tid = get_named_arg(kb, &named_args, "requirements").expect("requirements arg");
    let (list_functor, list_named) = match kb.get_term(reqs_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("requirements list must be Fn; got {other:?}"),
    };
    assert_eq!(
        list_functor, cons_sym,
        "single dispatching dict wrapped in cons; got {}",
        kb.qualified_name_of(list_functor)
    );

    // Tail = nil (single-entry list under Model 1).
    let tail_tid = get_named_arg(kb, &list_named, "tail").expect("cons tail");
    let tail_functor = match kb.get_term(tail_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("tail must be Fn; got {other:?}"),
    };
    assert_eq!(tail_functor, nil_sym, "single-entry list's tail must be nil");

    // Head = construct_requirement(EqList, [<sub>]) — the dispatching
    // dict for the callee, with EqList as the impl carrier.
    let head_tid = get_named_arg(kb, &list_named, "head").expect("cons head");
    let (head_functor, head_named) = match kb.get_term(head_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("dispatching dict must be Fn; got {other:?}"),
    };
    assert_eq!(
        head_functor, cr_sym,
        "Pin-now's dispatching dict must be construct_requirement; got {}",
        kb.qualified_name_of(head_functor)
    );

    let outer_impl_tid = get_named_arg(kb, &head_named, "impl_functor")
        .expect("outer construct_requirement impl_functor");
    let outer_impl_sym = match kb.get_term(outer_impl_tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        other => panic!("impl_functor must be a Ref; got {other:?}"),
    };
    assert_eq!(
        outer_impl_sym, eqlist_sym,
        "outer dispatching dict carrier must be EqList; got {}",
        kb.qualified_name_of(outer_impl_sym)
    );

    // Inner: EqList's sub_requires has one entry — the resolved Eq[T = Int]
    // = Int (per the stdlib's `fact Eq[T = Int]`).
    let outer_subreqs_tid = get_named_arg(kb, &head_named, "requirements")
        .expect("outer construct_requirement requirements");
    let (outer_subreqs_functor, outer_subreqs_named) = match kb.get_term(outer_subreqs_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("outer sub-reqs must be Fn; got {other:?}"),
    };
    assert_eq!(
        outer_subreqs_functor, cons_sym,
        "EqList has one require → its sub-reqs cons-list has one entry"
    );
    let inner_head_tid = get_named_arg(kb, &outer_subreqs_named, "head")
        .expect("inner cons head");
    let (inner_head_functor, inner_head_named) = match kb.get_term(inner_head_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("inner head must be Fn; got {other:?}"),
    };
    assert_eq!(
        inner_head_functor, cr_sym,
        "sub-instance for Eq[T=Int] must be construct_requirement(Int, []); got {}",
        kb.qualified_name_of(inner_head_functor)
    );
    let inner_impl_tid = get_named_arg(kb, &inner_head_named, "impl_functor")
        .expect("inner construct_requirement impl_functor");
    let inner_impl_sym = match kb.get_term(inner_impl_tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        other => panic!("inner impl_functor must be a Ref; got {other:?}"),
    };
    assert_eq!(
        inner_impl_sym, int_sym,
        "Eq[T = Int]'s carrier is Int (per stdlib's `fact Eq[T = Int]`); got {}",
        kb.qualified_name_of(inner_impl_sym)
    );

    // Innermost requirements list = nil — Int has no transitive deps.
    let innermost_tid = get_named_arg(kb, &inner_head_named, "requirements")
        .expect("inner construct_requirement requirements arg");
    let innermost_functor = match kb.get_term(innermost_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("innermost requirements must be Fn; got {other:?}"),
    };
    assert_eq!(
        innermost_functor, nil_sym,
        "Int has no requires; innermost requirements must be nil"
    );
}
