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


use anthill_core::kb::typing::{CallClass, ResolvedRequiresNode};
use crate::common::interp_for;

#[test]
fn pin_now_threads_conditional_tree_into_nested_construct_requirement() {
    // Setup: an EqList carrier that conditionally provides Eq for
    // List[T = A] given Eq[T = A]. The driver calls `eq(x, y)` at
    // T = List[Int64] — Pin-now resolves to EqList.eq with a
    // Conditional tree whose sole sub_resolution is the rustland's
    // `fact Eq[T = Int64]` leaf (Int64 as the carrier).
    //
    // WI-325 made `List` itself declare `requires Eq[T]`, so the
    // stdlib emits Eq.eq apply_within rewrites of its own; those
    // collide with `Driver.drive`'s eq rewrite in the hash-consed
    // `dispatch_rewrites` table (per `materialize_apply`'s synthetic
    // `apply(fn=spec_op, args=nil)` key). The test now inspects the
    // typer's per-occurrence CallClass directly — `resolved_tree`
    // carries the same nested impl-sort structure
    // `record_apply_within_concrete` would emit into the IR, so the
    // WI-228 invariant ("tree is threaded into the rewrite") is
    // verified at the source where it lives.
    let src = r#"
namespace test.wi228.pin_now_tree
  import anthill.prelude.{Eq, List, Int64, Bool}
  export EqList, Driver
  sort EqList
    sort A = ?
    requires Eq[T = A]
    fact Eq[T = List[T = A]]
    operation eq(x: List[T = A], y: List[T = A]) -> Bool = true
  end
  sort Driver
    import anthill.prelude.Eq.{eq}
    operation drive(x: List[T = Int64], y: List[T = Int64]) -> Bool = eq(x, y)
  end
end
"#;
    let interp = interp_for(src);
    let kb = interp.kb();

    let int_sym = kb
        .try_resolve_symbol("anthill.prelude.Int64")
        .expect("Int64 registered");
    let impl_eq_sym = kb
        .try_resolve_symbol("test.wi228.pin_now_tree.EqList.eq")
        .expect("EqList.eq registered");
    let eqlist_sym = kb
        .try_resolve_symbol("test.wi228.pin_now_tree.EqList")
        .expect("EqList sort registered");
    let drive_sym = kb
        .try_resolve_symbol("test.wi228.pin_now_tree.Driver.drive")
        .expect("Driver.drive registered");

    // Driver.drive's body has a single classified spec-op call (the
    // `eq(x, y)`); collect every CallClass on that body and pick the
    // ConcreteApplyWithin entry naming EqList.eq.
    let body = kb.op_body_node(drive_sym).expect("Driver.drive has a body");
    let mut classifications: Vec<CallClass> = Vec::new();
    anthill_core::kb::node_occurrence::visit_classifications(body, &mut |_, c| {
        classifications.push(c.clone());
    });

    let (fn_target_sym, callee_spec_sort, resolved_tree) = classifications
        .iter()
        .find_map(|c| match c {
            CallClass::ConcreteApplyWithin {
                fn_target_sym,
                callee_spec_sort,
                resolved_tree,
                ..
            } if *fn_target_sym == impl_eq_sym => Some((
                *fn_target_sym,
                *callee_spec_sort,
                resolved_tree.clone(),
            )),
            _ => None,
        })
        .expect("Driver.drive's eq() must classify as ConcreteApplyWithin → EqList.eq");

    assert_eq!(
        fn_target_sym, impl_eq_sym,
        "fn_target_sym must be EqList.eq; got {}",
        kb.qualified_name_of(fn_target_sym)
    );
    assert_eq!(
        callee_spec_sort, eqlist_sym,
        "callee_spec_sort must be EqList (the carrier sort); got {}",
        kb.qualified_name_of(callee_spec_sort)
    );

    // WI-228: the resolved_tree carries the full impl tree the IR
    // emitter walks. Shape: Conditional { impl_sort = EqList,
    // sub_resolutions = [Leaf { impl_sort = Int64 }] }.
    let tree = resolved_tree
        .expect("ConcreteApplyWithin for Pin-now Conditional must carry resolved_tree");
    let (outer_impl_sort, sub_resolutions) = match tree {
        ResolvedRequiresNode::Conditional { impl_sort, sub_resolutions, .. } => {
            (impl_sort, sub_resolutions)
        }
        other => panic!(
            "resolved_tree must be Conditional (EqList has a `requires` chain); \
             got {other:?}"
        ),
    };
    assert_eq!(
        outer_impl_sort, eqlist_sym,
        "outer impl_sort must be EqList; got {}",
        kb.qualified_name_of(outer_impl_sort)
    );
    assert_eq!(
        sub_resolutions.len(),
        1,
        "EqList has one require → tree has one sub_resolution"
    );
    let inner_impl_sort = match &sub_resolutions[0] {
        ResolvedRequiresNode::Leaf { impl_sort, .. } => *impl_sort,
        ResolvedRequiresNode::Conditional { impl_sort, .. } => *impl_sort,
        other => panic!(
            "sub-resolution for Eq[T = Int64] must be Leaf/Conditional naming Int64; \
             got {other:?}"
        ),
    };
    assert_eq!(
        inner_impl_sort, int_sym,
        "Eq[T = Int64]'s carrier is Int64 (per stdlib's `fact Eq[T = Int64]`); got {}",
        kb.qualified_name_of(inner_impl_sort)
    );
}
