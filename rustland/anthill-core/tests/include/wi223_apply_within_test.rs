//! WI-223 / WI-237 — `apply_within` reduction tests (acceptance #2).
//!
//! Pin that:
//!   1. `apply_within(fn, args, requirements)` evaluates the requirements
//!      channel synchronously and threads the resulting handles into the
//!      callee frame via `dispatch_call_with_requirements`.
//!   2. Plain `apply` paths still install an empty `frame.requirements`
//!      (no regression).
//!
//! Under the names model (WI-237) the callee's frame.requirements are
//! keyed by synthesized names: `__req_self` for the dispatching dict
//! plus `__req_<spec>` per impl-parent transitive requires entry. The
//! body reads them via `var_ref(name = Ref(__req_*))`.
//!
//! Reference: docs/design/operation-call-model.md §"Names model",
//! §"Eval mechanics: AwaitState with requirements".


use smallvec::SmallVec;

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;

use crate::common::load_kb_with;

fn make_nil(kb: &mut KnowledgeBase) -> TermId {
    let nil_sym = kb.try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil registered");
    kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    })
}

fn make_cons(kb: &mut KnowledgeBase, head: TermId, tail: TermId) -> TermId {
    let cons_sym = kb.try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons registered");
    let head_field = kb.intern("head");
    let tail_field = kb.intern("tail");
    kb.alloc(Term::Fn {
        functor: cons_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (head_field, head),
            (tail_field, tail),
        ]),
    })
}

fn make_singleton(kb: &mut KnowledgeBase, item: TermId) -> TermId {
    let nil = make_nil(kb);
    make_cons(kb, item, nil)
}

#[test]
fn apply_within_evaluates_requirements_then_dispatches_to_anthill_op() {
    // `produce()` is a no-arg anthill op. apply_within calls it with one
    // freshly-constructed requirement value in the requirements channel.
    // The arena's live count climbs by one before dispatch and returns
    // to baseline after the body returns + requirement drops.
    let src = r#"
namespace test.wi223.apply_within
  operation produce() -> Int64 = 42
end
"#;
    let mut kb = load_kb_with(src);
    let target_sym = kb.try_resolve_symbol("test.wi223.apply_within.produce")
        .expect("produce registered");
    let impl_sym = kb.intern("test.wi223.apply_within.SomeImpl");
    let aw_sym = kb.try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .unwrap();
    let cr_sym = kb.try_resolve_symbol("anthill.reflect.Expr.construct_requirement")
        .unwrap();

    // requirements = [construct_requirement(SomeImpl, [])]
    let nil = make_nil(&mut kb);
    let impl_ref = kb.alloc(Term::Ref(impl_sym));
    let impl_field = kb.intern("impl_functor");
    let reqs_field = kb.intern("requirements");
    let cr = kb.alloc(Term::Fn {
        functor: cr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (impl_field, impl_ref),
            (reqs_field, nil),
        ]),
    });
    let cr_list = make_singleton(&mut kb, cr);

    // apply_within(fn = produce, args = [], requirements = [cr])
    let fn_field = kb.intern("fn");
    let args_field = kb.intern("args");
    let fn_ref = kb.alloc(Term::Ref(target_sym));
    let nil2 = make_nil(&mut kb);
    let aw_term = kb.alloc(Term::Fn {
        functor: aw_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (fn_field, fn_ref),
            (args_field, nil2),
            (reqs_field, cr_list),
        ]),
    });

    let mut interp = Interpreter::new(kb);
    let pre_live = interp.requirement_arena_live_count();
    let value = interp.run_with_requirements(aw_term, SmallVec::new())
        .expect("apply_within should reduce");
    assert_eq!(value.as_int(), Some(42),
        "produce body should run and return 42");
    // The requirement was alive across the dispatch (installed in the
    // callee frame) and should be released after produce returns.
    assert_eq!(interp.requirement_arena_live_count(), pre_live,
        "requirement allocated for the dispatch must be reclaimed");
}

#[test]
fn apply_within_with_requirement_dispatch_resolves_via_handle_functor() {
    // WI-234 Model 1: dispatching dict at requirements[0] drives the
    // dispatch. apply_within's `fn` is a spec-op-like Symbol (here we
    // use a synthetic `Spec.foo` short whose qualified name doesn't
    // exist yet — runtime concatenates dict.functor + ".foo" to find
    // the impl). frame.requirements[0] = the dispatching dict whose
    // functor selects IntFooImpl vs StringFooImpl.
    let src = r#"
namespace test.wi223.dispatch_form
  -- Two impl ops with the same short name. Dispatching through
  -- requirements[0]'s functor picks one or the other.
  sort IntFooImpl
    operation foo() -> Int64 = 100
  end
  sort StringFooImpl
    operation foo() -> Int64 = 200
  end
end
"#;
    let mut kb = load_kb_with(src);
    let int_impl = kb.try_resolve_symbol("test.wi223.dispatch_form.IntFooImpl")
        .expect("IntFooImpl registered");

    let aw_sym = kb.try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .unwrap();
    let cr_sym = kb.try_resolve_symbol("anthill.reflect.Expr.construct_requirement")
        .unwrap();

    // A synthetic spec-op-like symbol (the short name "foo"). The
    // runtime will resolve `<IntFooImpl_qn>.foo` via the dispatching
    // dict's functor.
    let foo_spec_qn = "test.wi223.dispatch_form.Spec.foo";
    let foo_spec_sym = kb.intern(foo_spec_qn);

    // Build the dispatching dict expression: construct_requirement(IntFooImpl, []).
    let int_impl_ref = kb.alloc(Term::Ref(int_impl));
    let impl_field = kb.intern("impl_functor");
    let reqs_inner_field = kb.intern("requirements");
    let nil = make_nil(&mut kb);
    let dict_expr = kb.alloc(Term::Fn {
        functor: cr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (impl_field, int_impl_ref),
            (reqs_inner_field, nil),
        ]),
    });
    let dict_list = make_singleton(&mut kb, dict_expr);

    // apply_within(fn = Ref(foo_spec_sym), args = [], requirements = [<dict>])
    let fn_field = kb.intern("fn");
    let args_field = kb.intern("args");
    let reqs_field = kb.intern("requirements");
    let fn_ref = kb.alloc(Term::Ref(foo_spec_sym));
    let nil2 = make_nil(&mut kb);
    let aw_term = kb.alloc(Term::Fn {
        functor: aw_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (fn_field, fn_ref),
            (args_field, nil2),
            (reqs_field, dict_list),
        ]),
    });

    let mut interp = Interpreter::new(kb);
    let value = interp.run_with_requirements(aw_term, SmallVec::new())
        .expect("apply_within with dispatching dict should reduce");
    assert_eq!(value.as_int(), Some(100),
        "IntFooImpl.foo should run when the dispatching dict's functor is IntFooImpl");
}

#[test]
fn apply_within_threads_requirements_to_callee_frame_for_introspection() {
    // The callee's body is `var_ref(name: Ref(__req_self))`, exercising
    // the full thread-through under the names model: apply_within
    // evaluates the requirements list, frame-push binds `__req_self` to
    // the dispatching dict (and `__req_<spec>` to each transitive entry
    // — but `read_my_req` has no enclosing sort so there are none).
    // The body reads `__req_self` by name and yields the handle.
    //
    // Setup: register an anthill op `read_my_req() -> Int64`. Override its
    // body via the dispatch_rewrites mechanism: hand-build a
    // `var_ref(name: Ref(__req_self))` term and rewrite the original body
    // term to point at it.
    let src = r#"
namespace test.wi223.thread_through
  operation read_my_req() -> Int64 = 0
end
"#;
    let mut kb = load_kb_with(src);
    let target_sym = kb.try_resolve_symbol("test.wi223.thread_through.read_my_req")
        .unwrap();
    let impl_sym = kb.intern("test.wi223.thread_through.MyImpl");
    let aw_sym = kb.try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .unwrap();
    let cr_sym = kb.try_resolve_symbol("anthill.reflect.Expr.construct_requirement")
        .unwrap();
    let var_ref_sym = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .unwrap();

    // Override the read_my_req body with a fresh NodeOccurrence reading
    // `var_ref(name: __req_self)` — names-model way to fetch the
    // dispatching dict from the frame. Post-WI-248 the eval walks
    // `kb.op_bodies` directly, so we replace the body NodeOccurrence
    // by synthesizing one against the original body: the new occurrence
    // inherits the span from `from` and records the test pass that
    // produced it via `OccurrenceOrigin::Synthesized`.
    let _ = var_ref_sym;
    let req_self_sym = kb.intern("__req_self");
    let original_body = kb.op_body_node(target_sym)
        .expect("read_my_req body materialized in kb.op_bodies")
        .clone();
    let pass = kb.register_pass("test.wi223.body_override");
    let body_node = anthill_core::kb::node_occurrence::NodeOccurrence::synthesized_expr(
        anthill_core::kb::node_occurrence::Expr::VarRef { name: req_self_sym },
        original_body,
        pass,
        Some(target_sym),
    );
    kb.set_op_body_node(target_sym, body_node);

    // requirements = [construct_requirement(MyImpl, [])]
    let nil = make_nil(&mut kb);
    let impl_ref = kb.alloc(Term::Ref(impl_sym));
    let impl_field = kb.intern("impl_functor");
    let reqs_field = kb.intern("requirements");
    let cr = kb.alloc(Term::Fn {
        functor: cr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (impl_field, impl_ref),
            (reqs_field, nil),
        ]),
    });
    let cr_list = make_singleton(&mut kb, cr);

    // apply_within(fn = read_my_req, args = [], requirements = [cr])
    let fn_field = kb.intern("fn");
    let args_field = kb.intern("args");
    let fn_ref = kb.alloc(Term::Ref(target_sym));
    let nil2 = make_nil(&mut kb);
    let aw_term = kb.alloc(Term::Fn {
        functor: aw_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (fn_field, fn_ref),
            (args_field, nil2),
            (reqs_field, cr_list),
        ]),
    });

    let mut interp = Interpreter::new(kb);
    let value = interp.run_with_requirements(aw_term, SmallVec::new())
        .expect("apply_within with introspecting body should reduce");
    match value {
        Value::Requirement(h) => {
            assert_eq!(h.functor(), impl_sym,
                "callee's frame.requirements[__req_self] should be the \
                 requirement we constructed at the apply_within site");
        }
        other => panic!("expected Value::Requirement(MyImpl), got {other:?}"),
    }
}
