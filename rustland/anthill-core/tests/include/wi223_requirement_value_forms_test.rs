//! WI-223 — runtime support for the operation-call model: tests that the
//! eval reduces the requirement-typed value forms emitted by the
//! requirement-insertion pass:
//!
//!   - `requirement_at_current(slot)` → `Value::Requirement(frame.requirements[slot])`
//!   - `requirement_at_sort(chain, slot)` → projected sub-requirement
//!   - `construct_requirement(impl, [...])` → freshly-allocated arena slot
//!
//! Tests use `Interpreter::run_with_requirements` to seed the frame's
//! requirements before stepping the body — exercising reductions in
//! isolation from the WI-222 rewrite pass that will eventually emit them.
//!
//! Reference: docs/design/operation-call-model.md §"Two primitives:
//! requirement_at_current and requirement_at_sort", §"Construction site".


use smallvec::SmallVec;

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::KnowledgeBase;

use crate::common::load_kb_with;

fn fresh_interp() -> Interpreter {
    // Stdlib alone — no user source needed; we construct IR terms by hand.
    let kb = load_kb_with("namespace test.wi223.empty\nend\n");
    Interpreter::new(kb)
}

fn alloc_int(kb: &mut KnowledgeBase, n: i64) -> anthill_core::kb::term::TermId {
    kb.alloc(Term::Const(Literal::Int(n)))
}

/// Build `var_ref(name: <sym>)` — a named requirement read (WI-237
/// names model; replaced the positional `requirement_at_current`).
fn build_req_var_ref(
    kb: &mut KnowledgeBase,
    var_ref_sym: anthill_core::intern::Symbol,
    name_sym: anthill_core::intern::Symbol,
) -> anthill_core::kb::term::TermId {
    let name_ref = kb.alloc(Term::Ref(name_sym));
    let name_field = kb.intern("name");
    kb.alloc(Term::Fn {
        functor: var_ref_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_field, name_ref)]),
    })
}

#[test]
fn var_ref_yields_frame_requirement_handle() {
    // Pre-seed a single named requirement; an op body that reads
    // `var_ref(name: __req_probe)` must return a Value::Requirement
    // whose functor matches what we passed in.
    let mut interp = fresh_interp();
    let probe_sym = interp.kb_mut().intern("test.wi223.IntFooImpl");
    let handle = interp.alloc_requirement(probe_sym, SmallVec::new());
    let expected_functor = handle.functor();

    let var_ref_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("reflect.Expr.var_ref registered");
    let req_name = interp.kb_mut().intern("__req_probe");
    let expr = build_req_var_ref(interp.kb_mut(), var_ref_sym, req_name);

    let mut requirements: SmallVec<[_; 2]> = SmallVec::new();
    requirements.push((req_name, handle));
    let value = interp.run_with_requirements(expr, requirements)
        .expect("var_ref should reduce to the frame requirement");

    match value {
        Value::Requirement(h) => {
            assert_eq!(h.functor(), expected_functor,
                "Value::Requirement should carry the seeded handle's functor");
        }
        other => panic!("expected Value::Requirement, got {other:?}"),
    }
}

#[test]
fn var_ref_unbound_requirement_errors() {
    // Frame has 0 requirements; reading `var_ref(name: __req_probe)` as
    // a value must dispatch_call-miss and surface a clear error rather
    // than panicking. Defensive case for the eval loud-failure discipline.
    let mut interp = fresh_interp();
    let var_ref_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref registered");
    let req_name = interp.kb_mut().intern("__req_probe");
    let expr = build_req_var_ref(interp.kb_mut(), var_ref_sym, req_name);

    let result = interp.run_with_requirements(expr, SmallVec::new());
    assert!(result.is_err(),
        "unbound requirement name must error, not panic; got {result:?}");
}

#[test]
fn requirement_at_sort_projects_sub_handle() {
    // Build a parent requirement carrying a child; an op body of
    // `requirement_at_sort(chain: requirement_at_current(0), slot: 0)`
    // must yield the child handle.
    let mut interp = fresh_interp();
    let parent_sym = interp.kb_mut().intern("test.wi223.ParentImpl");
    let child_sym = interp.kb_mut().intern("test.wi223.ChildImpl");

    let child_handle = interp.alloc_requirement(child_sym, SmallVec::new());
    let mut bundle: SmallVec<[_; 1]> = SmallVec::new();
    bundle.push(child_handle);
    let parent_handle = interp.alloc_requirement(parent_sym, bundle);

    let var_ref_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .unwrap();
    let raas_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.requirement_at_sort")
        .expect("requirement_at_sort registered");

    // chain = var_ref(name: __req_parent) — a names-model requirement
    // read; requirement_at_sort projects its slot 0.
    let req_name = interp.kb_mut().intern("__req_parent");
    let inner = build_req_var_ref(interp.kb_mut(), var_ref_sym, req_name);
    let zero = alloc_int(interp.kb_mut(), 0);
    let chain_field = interp.kb_mut().intern("chain");
    let slot_field = interp.kb_mut().intern("slot");
    let expr = interp.kb_mut().alloc(Term::Fn {
        functor: raas_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(chain_field, inner), (slot_field, zero)]),
    });

    let mut requirements: SmallVec<[_; 2]> = SmallVec::new();
    requirements.push((req_name, parent_handle));
    let value = interp.run_with_requirements(expr, requirements)
        .expect("requirement_at_sort should reduce successfully");

    match value {
        Value::Requirement(h) => {
            assert_eq!(h.functor(), child_sym,
                "projected handle should be the child's");
        }
        other => panic!("expected Value::Requirement, got {other:?}"),
    }
}

#[test]
fn construct_requirement_allocates_fresh_arena_slot() {
    // `construct_requirement(impl_functor: Foo, requirements: [])`
    // allocates a brand-new requirement value with no sub-requirements.
    // The arena's live count climbs by one over the body's execution.
    let mut interp = fresh_interp();
    let foo_sym = interp.kb_mut().intern("test.wi223.Foo");

    let cr_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.construct_requirement")
        .expect("construct_requirement registered");

    let impl_field = interp.kb_mut().intern("impl_functor");
    let reqs_field = interp.kb_mut().intern("requirements");
    let impl_ref = interp.kb_mut().alloc(Term::Ref(foo_sym));
    let nil_sym = interp.kb()
        .try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil registered");
    let nil = interp.kb_mut().alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let expr = interp.kb_mut().alloc(Term::Fn {
        functor: cr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (impl_field, impl_ref),
            (reqs_field, nil),
        ]),
    });

    let pre = interp.requirement_arena_live_count();
    let value = interp.run_with_requirements(expr, SmallVec::new())
        .expect("construct_requirement should reduce successfully");

    match value {
        Value::Requirement(h) => {
            assert_eq!(h.functor(), foo_sym,
                "constructed handle's functor should match the requested impl");
            assert_eq!(h.arity(), 0, "no sub-requirements expected");
            // Drop the value so the slot is freed before we read live count.
            drop(h);
            assert_eq!(interp.requirement_arena_live_count(), pre,
                "constructed slot must release after Value::Requirement drops");
        }
        other => panic!("expected Value::Requirement, got {other:?}"),
    }
}

#[test]
fn construct_requirement_bundles_subrequirements() {
    // Construct a parent that bundles a child requirement (built via a
    // nested construct_requirement). The cascade-drop test in the arena
    // unit suite already proves the dispose path; here we pin the IR
    // wiring: the eval produces a parent whose 0-th sub-requirement is
    // the freshly-built child.
    let mut interp = fresh_interp();
    let parent_sym = interp.kb_mut().intern("test.wi223.Parent");
    let child_sym = interp.kb_mut().intern("test.wi223.Child");

    let cr_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.construct_requirement")
        .unwrap();
    let cons_sym = interp.kb()
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons registered");
    let nil_sym = interp.kb()
        .try_resolve_symbol("anthill.prelude.List.nil")
        .unwrap();
    let impl_field = interp.kb_mut().intern("impl_functor");
    let reqs_field = interp.kb_mut().intern("requirements");
    let head_field = interp.kb_mut().intern("head");
    let tail_field = interp.kb_mut().intern("tail");

    let nil = interp.kb_mut().alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });

    // Inner: construct_requirement(Child, [])
    let child_ref = interp.kb_mut().alloc(Term::Ref(child_sym));
    let child_construct = interp.kb_mut().alloc(Term::Fn {
        functor: cr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (impl_field, child_ref),
            (reqs_field, nil),
        ]),
    });

    // Outer: construct_requirement(Parent, [child_construct])
    let cons = interp.kb_mut().alloc(Term::Fn {
        functor: cons_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (head_field, child_construct),
            (tail_field, nil),
        ]),
    });
    let parent_ref = interp.kb_mut().alloc(Term::Ref(parent_sym));
    let parent_construct = interp.kb_mut().alloc(Term::Fn {
        functor: cr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (impl_field, parent_ref),
            (reqs_field, cons),
        ]),
    });

    let value = interp.run_with_requirements(parent_construct, SmallVec::new())
        .expect("construct_requirement chain should reduce");

    match value {
        Value::Requirement(h) => {
            assert_eq!(h.functor(), parent_sym, "parent functor preserved");
            assert_eq!(h.arity(), 1, "parent should bundle one sub-requirement");
            let sub = h.project(0);
            assert_eq!(sub.functor(), child_sym,
                "parent's 0-th sub-requirement should be the child");
        }
        other => panic!("expected Value::Requirement, got {other:?}"),
    }
}
