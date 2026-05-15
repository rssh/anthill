//! WI-223 — closure-requirements snapshot/restore tests (acceptance #4).
//!
//! Pin that:
//!   1. A lambda construction site captures the enclosing frame's
//!      `requirements` into the closure (snapshot at lambda time, not
//!      invocation time).
//!   2. Closure invocation installs `closure.requirements` into the new
//!      frame, overriding any apply-side requirements channel — the
//!      "HO-call exception" per `docs/design/operation-call-model.md`
//!      §"Closure invocation: the one runtime exception".
//!
//! Reference: docs/design/operation-call-model.md §"Closures carry their
//! own requirements".


use smallvec::SmallVec;

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;

use crate::common::load_kb_with;

fn fresh_interp() -> Interpreter {
    let kb = load_kb_with("namespace test.wi223.closure_reqs\nend\n");
    Interpreter::new(kb)
}

fn build_lambda(
    kb: &mut KnowledgeBase,
    body: TermId,
) -> TermId {
    // Construct a `lambda(param: <wildcard>, body: <body>)` term that
    // ignores its argument and reduces to `body`.
    let lambda_sym = kb.try_resolve_symbol("anthill.reflect.Expr.lambda")
        .expect("Expr.lambda registered");
    let wildcard_sym = kb.try_resolve_symbol("anthill.reflect.Pattern.wildcard")
        .expect("Pattern.wildcard registered");
    let wildcard = kb.alloc(Term::Fn {
        functor: wildcard_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let param_field = kb.intern("param");
    let body_field = kb.intern("body");
    kb.alloc(Term::Fn {
        functor: lambda_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (param_field, wildcard),
            (body_field, body),
        ]),
    })
}

#[test]
fn lambda_construction_snapshots_enclosing_frame_requirements() {
    // Reduce a lambda term in a frame seeded with one requirement.
    // The resulting closure should hold that same requirement in
    // `closure.requirements`.
    let mut interp = fresh_interp();
    let probe_sym = interp.kb_mut().intern("test.wi223.closure_reqs.SomeImpl");
    let h = interp.alloc_requirement(probe_sym, SmallVec::new());

    // Body doesn't matter for snapshot test — use a literal so the
    // closure is well-formed.
    let body = interp.kb_mut().alloc(
        Term::Const(anthill_core::kb::term::Literal::Int(0)),
    );
    let lambda_term = build_lambda(interp.kb_mut(), body);

    let req_name = interp.kb_mut().intern("__req_probe");
    let mut requirements: SmallVec<[_; 2]> = SmallVec::new();
    requirements.push((req_name, h.clone()));
    let value = interp.run_with_requirements(lambda_term, requirements)
        .expect("lambda reduction should succeed");

    let closure_h = match value {
        Value::Closure(h) => h,
        other => panic!("expected Value::Closure, got {other:?}"),
    };
    let snapshot = interp.closure_requirements_for_test(&closure_h);
    assert_eq!(snapshot.len(), 1,
        "lambda must snapshot the enclosing frame's single requirement");
    assert_eq!(snapshot[0].1.functor(), h.functor(),
        "snapshotted handle should reference the same impl");
}

#[test]
fn closure_invocation_installs_snapshotted_requirements_in_callee_frame() {
    // End-to-end: build a let-bound closure whose body reads
    // `requirement_at_current(slot: 0)`, then invoke it via a plain
    // `apply` (no requirements channel). The closure's snapshotted
    // requirement should appear in the callee frame, proving
    // `closure.requirements` wins over the (empty) apply-side channel.
    let mut interp = fresh_interp();
    let probe_sym = interp.kb_mut().intern("test.wi223.closure_reqs.SnapImpl");
    let h = interp.alloc_requirement(probe_sym, SmallVec::new());

    // Body of the lambda: var_ref(name: __req_probe) — a named
    // requirement read (WI-237 names model).
    let var_ref_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .unwrap();
    let req_name = interp.kb_mut().intern("__req_probe");
    let req_name_ref = interp.kb_mut().alloc(Term::Ref(req_name));
    let name_field0 = interp.kb_mut().intern("name");
    let req_read = interp.kb_mut().alloc(Term::Fn {
        functor: var_ref_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_field0, req_name_ref)]),
    });
    let lambda_term = build_lambda(interp.kb_mut(), req_read);

    // let f = <lambda_term> in apply(fn = "f", args = [tuple()])
    let f_sym = interp.kb_mut().intern("f");
    let var_pattern_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Pattern.var_pattern")
        .unwrap();
    let none_sym = interp.kb()
        .try_resolve_symbol("anthill.prelude.Option.none")
        .expect("Option.none registered");
    let none_term = interp.kb_mut().alloc(Term::Fn {
        functor: none_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let f_ref = interp.kb_mut().alloc(Term::Ref(f_sym));
    let name_field = interp.kb_mut().intern("name");
    let type_ann_field = interp.kb_mut().intern("type_ann");
    let var_pattern = interp.kb_mut().alloc(Term::Fn {
        functor: var_pattern_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (name_field, f_ref),
            (type_ann_field, none_term),
        ]),
    });

    // apply(fn = f, args = [ApplyArg(name: None, value: int_lit(0))])
    // The lambda's pattern is wildcard so the arg is ignored — use any
    // simple literal.
    let apply_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.apply")
        .unwrap();
    let int_lit_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.int_lit")
        .unwrap();
    let zero_lit = interp.kb_mut().alloc(
        Term::Const(anthill_core::kb::term::Literal::Int(0)),
    );
    let value_field = interp.kb_mut().intern("value");
    let unit_arg = interp.kb_mut().alloc(Term::Fn {
        functor: int_lit_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(value_field, zero_lit)]),
    });
    let apply_arg_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.ApplyArg")
        .expect("ApplyArg registered");
    let arg_struct = interp.kb_mut().alloc(Term::Fn {
        functor: apply_arg_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (name_field, none_term),
            (value_field, unit_arg),
        ]),
    });
    // args list: cons(arg_struct, nil)
    let nil_sym = interp.kb().try_resolve_symbol("anthill.prelude.List.nil").unwrap();
    let cons_sym = interp.kb().try_resolve_symbol("anthill.prelude.List.cons").unwrap();
    let nil_t = interp.kb_mut().alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let head_field = interp.kb_mut().intern("head");
    let tail_field = interp.kb_mut().intern("tail");
    let args_list = interp.kb_mut().alloc(Term::Fn {
        functor: cons_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (head_field, arg_struct),
            (tail_field, nil_t),
        ]),
    });
    let fn_field = interp.kb_mut().intern("fn");
    let args_field = interp.kb_mut().intern("args");
    let f_ref2 = interp.kb_mut().alloc(Term::Ref(f_sym));
    let apply_term = interp.kb_mut().alloc(Term::Fn {
        functor: apply_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (fn_field, f_ref2),
            (args_field, args_list),
        ]),
    });

    let let_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.let_expr")
        .unwrap();
    let pattern_field = interp.kb_mut().intern("pattern");
    let body_field = interp.kb_mut().intern("body");
    let let_term = interp.kb_mut().alloc(Term::Fn {
        functor: let_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (pattern_field, var_pattern),
            (value_field, lambda_term),
            (body_field, apply_term),
        ]),
    });

    let mut requirements: SmallVec<[_; 2]> = SmallVec::new();
    requirements.push((req_name, h.clone()));
    let value = interp.run_with_requirements(let_term, requirements)
        .expect("let-bound closure invocation should reduce");
    match value {
        Value::Requirement(observed) => {
            assert_eq!(observed.functor(), h.functor(),
                "closure body should observe the requirement snapshotted at \
                 lambda construction time, not the invocation-site context");
        }
        other => panic!("expected Value::Requirement, got {other:?}"),
    }
}

#[test]
fn lambda_constructed_with_empty_frame_snapshots_empty_requirements() {
    // Counter-test: a lambda built with frame.requirements = [] should
    // hold an empty `closure.requirements`.
    let mut interp = fresh_interp();
    let body = interp.kb_mut().alloc(
        Term::Const(anthill_core::kb::term::Literal::Int(0)),
    );
    let lambda_term = build_lambda(interp.kb_mut(), body);

    let value = interp.run_with_requirements(lambda_term, SmallVec::new())
        .expect("lambda reduction should succeed");
    let closure_h = match value {
        Value::Closure(h) => h,
        other => panic!("expected Value::Closure, got {other:?}"),
    };
    let snapshot = interp.closure_requirements_for_test(&closure_h);
    assert!(snapshot.is_empty(),
        "lambda built in an empty-requirements frame must snapshot empty");
}
