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

    // requirements list = cons(construct_requirement(Int, nil), nil).
    // Outer: EqList's sole `requires Eq[T = A]` at A = Int.
    // Inner: rustland's `fact Eq[T = Int]` resolves to Int as carrier
    //        (no IntEq sort exists — the stdlib uses Int directly).
    // Tail: nil — EqList declares only one require.
    let reqs_tid = get_named_arg(kb, &named_args, "requirements").expect("requirements arg");
    let (list_functor, list_named) = match kb.get_term(reqs_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("requirements list must be Fn; got {other:?}"),
    };
    assert_eq!(
        list_functor, cons_sym,
        "EqList has one transitive dep; pre-WI-228 emitted nil here. Got {}",
        kb.qualified_name_of(list_functor)
    );

    // Tail of the outer cons must be nil — EqList has exactly one require.
    let tail_tid = get_named_arg(kb, &list_named, "tail").expect("cons tail");
    let tail_functor = match kb.get_term(tail_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("tail must be Fn; got {other:?}"),
    };
    assert_eq!(tail_functor, nil_sym, "single-dep list's tail must be nil");

    // Head: construct_requirement(impl_functor = Ref(Int), requirements = nil).
    let head_tid = get_named_arg(kb, &list_named, "head").expect("cons head");
    let (head_functor, head_named) = match kb.get_term(head_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("head must be Fn; got {other:?}"),
    };
    assert_eq!(
        head_functor, cr_sym,
        "WI-228: conditional sub-resolution must emit construct_requirement (not requirement_at_current); got {}",
        kb.qualified_name_of(head_functor)
    );

    let impl_tid =
        get_named_arg(kb, &head_named, "impl_functor").expect("construct_requirement impl_functor");
    let impl_sym = match kb.get_term(impl_tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        other => panic!("impl_functor must be a Ref; got {other:?}"),
    };
    assert_eq!(
        impl_sym, int_sym,
        "Eq[T = Int]'s carrier is Int (per anthill-stl/anthill/int.anthill's \
         `fact Eq[T = Int]`); got {}",
        kb.qualified_name_of(impl_sym)
    );

    // Innermost requirements list = nil — Int has no transitive deps.
    let sub_reqs_tid = get_named_arg(kb, &head_named, "requirements")
        .expect("inner construct_requirement requirements arg");
    let sub_functor = match kb.get_term(sub_reqs_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("inner requirements must be Fn; got {other:?}"),
    };
    assert_eq!(
        sub_functor, nil_sym,
        "Int has no requires; nested requirements must be nil"
    );
}
