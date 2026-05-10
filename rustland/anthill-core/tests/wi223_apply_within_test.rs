//! WI-223 — `apply_within` reduction tests (acceptance #2).
//!
//! Pin that:
//!   1. `apply_within(fn, args, requirements)` evaluates the requirements
//!      channel synchronously and threads the resulting handles into the
//!      callee frame via `dispatch_call_with_requirements`.
//!   2. Plain `apply` paths still install an empty `frame.requirements`
//!      (no regression).
//!
//! The fn-position `requirement_at_current` dispatch form is out of scope
//! for this commit (still returns "not yet supported" in eval).
//!
//! Reference: docs/design/operation-call-model.md §"Eval mechanics:
//! AwaitState with requirements".

mod common;

use smallvec::SmallVec;

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;

use common::load_kb_with;

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
  operation produce() -> Int = 42
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
    // Defer-to-requirement form: apply_within's `fn` is
    // `requirement_at_current(slot: 0, op: Some(Eq.eq))`. The eval reads
    // frame.requirements[0]'s functor (an impl sort name like
    // `IntEqImpl`) and resolves `IntEqImpl.eq` for dispatch. The op
    // body's return value confirms the right impl ran.
    let src = r#"
namespace test.wi223.dispatch_form
  -- Two impl ops with the same short name. Dispatching through
  -- requirement_at_current(slot=0, op=foo) picks one or the other based
  -- on the functor of frame.requirements[0].
  sort IntFooImpl
    operation foo() -> Int = 100
  end
  sort StringFooImpl
    operation foo() -> Int = 200
  end
end
"#;
    let mut kb = load_kb_with(src);
    let int_impl = kb.try_resolve_symbol("test.wi223.dispatch_form.IntFooImpl")
        .expect("IntFooImpl registered");
    let foo_short = kb.intern("foo");

    let aw_sym = kb.try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .unwrap();
    let raac_sym = kb.try_resolve_symbol("anthill.reflect.Expr.requirement_at_current")
        .unwrap();
    let some_sym = kb.try_resolve_symbol("anthill.prelude.Option.some")
        .expect("Option.some registered");

    // Build `requirement_at_current(slot: 0, op: some(foo_short))`.
    let zero = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(0)));
    let foo_ref = kb.alloc(Term::Ref(foo_short));
    let value_field = kb.intern("value");
    let some_wrap = kb.alloc(Term::Fn {
        functor: some_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(value_field, foo_ref)]),
    });
    let slot_field = kb.intern("slot");
    let op_field = kb.intern("op");
    let dispatch_fn = kb.alloc(Term::Fn {
        functor: raac_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (slot_field, zero),
            (op_field, some_wrap),
        ]),
    });

    // apply_within(fn = dispatch_fn, args = [], requirements = [])
    let fn_field = kb.intern("fn");
    let args_field = kb.intern("args");
    let reqs_field = kb.intern("requirements");
    let nil = make_nil(&mut kb);
    let aw_term = kb.alloc(Term::Fn {
        functor: aw_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (fn_field, dispatch_fn),
            (args_field, nil),
            (reqs_field, nil),
        ]),
    });

    let mut interp = Interpreter::new(kb);

    // Seed an IntFooImpl requirement at slot 0; dispatch should pick
    // IntFooImpl.foo, returning 100.
    let int_req = interp.alloc_requirement(int_impl, SmallVec::new());
    let mut requirements: SmallVec<[_; 2]> = SmallVec::new();
    requirements.push(int_req);
    let value = interp.run_with_requirements(aw_term, requirements)
        .expect("apply_within with dispatch form should reduce");
    assert_eq!(value.as_int(), Some(100),
        "IntFooImpl.foo should run when frame.requirements[0] is IntFooImpl");
}

#[test]
fn apply_within_threads_requirements_to_callee_frame_for_introspection() {
    // The callee's body is `requirement_at_current(slot: 0)`, exercising
    // the full thread-through: apply_within evaluates the requirements
    // list, builds the callee frame with frame.requirements = [<handle>],
    // the body reads slot 0 and yields it as Value::Requirement.
    //
    // Setup: register an anthill op `read_my_req() -> Int`. Override its
    // body via the dispatch_rewrites mechanism: hand-build a
    // `requirement_at_current(0)` term and rewrite the original body
    // term to point at it (using the existing dispatch_rewrites map).
    let src = r#"
namespace test.wi223.thread_through
  operation read_my_req() -> Int = 0
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
    let raac_sym = kb.try_resolve_symbol("anthill.reflect.Expr.requirement_at_current")
        .unwrap();

    // Build requirement_at_current(slot: 0). Used as the body override.
    let zero = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(0)));
    let slot_field = kb.intern("slot");
    let req_at_current = kb.alloc(Term::Fn {
        functor: raac_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(slot_field, zero)]),
    });

    // Rewrite the produce body: dispatch_rewrites swaps source term →
    // rewritten term during reduce_expr. The original body is some int
    // literal; redirect it to req_at_current.
    let original_body = anthill_core::eval::eval::lookup_operation_body(&kb, target_sym)
        .map(|(t, _)| t)
        .expect("read_my_req body");
    kb.record_dispatch_rewrite(original_body, req_at_current, target_sym);

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
                "callee's frame.requirements[0] should be the requirement \
                 we constructed at the apply_within site");
        }
        other => panic!("expected Value::Requirement(MyImpl), got {other:?}"),
    }
}
