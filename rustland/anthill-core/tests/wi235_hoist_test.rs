//! WI-235 — let-hoist for repeated construct_requirement literals.
//!
//! After WI-234, every Pin-now / Direct apply_within emission carries
//! a `requirements = [construct_requirement(impl, [...])]` channel.
//! Hash-consing dedupes identical TermIds across call sites, but each
//! runtime evaluation of `construct_requirement` allocates a fresh
//! arena slot. WI-235 adds a hoist phase to `req_insertion::run` that
//! identifies duplicate dispatching-dict shapes per body and let-binds
//! them once at the body root, replacing per-call construct_requirements
//! with var_ref to the shared binding.

mod common;

use anthill_core::kb::term::Term;
use anthill_core::kb::typing::get_named_arg;
use common::interp_for;

/// Three identical Pin-now spec-op calls in one body. The body needs
/// the dispatching dict three times; after hoisting it should appear
/// once via let_expr and be referenced via var_ref at each call site.
///
/// We pin: (1) at least one rewritten apply_within now has var_ref in
/// its requirements channel (proof the hoist fired) and (2) the body
/// root is rewritten to a let_expr (the hoist wrap).
#[test]
fn hoist_dedupes_repeated_pin_now_construct_requirement() {
    // Custom spec `MySpec[T=?]` with one body-less op `mark`. Impl
    // `MyIntImpl` provides `MySpec[T=Int]` AND declares its own
    // `requires` — that's what forces the call to route through
    // apply_within with construct_requirement (ConcreteApplyWithin
    // Pin-now path) instead of plain apply (PinNow).
    //
    // We need a non-empty `requires` chain on the impl. We satisfy
    // that with a trivial helper spec `MyHelper[T=?]` whose impl has
    // no further requires.
    let src = r#"
namespace test.wi235.hoist
  import anthill.prelude.{Int, Bool}
  export MySpec, MyHelper, MyHelperInt, MyIntImpl, Driver
  sort MySpec
    sort T = ?
    operation mark(x: T) -> Bool
  end
  sort MyHelper
    sort T = ?
    operation tag(x: T) -> Bool
  end
  sort MyHelperInt
    fact MyHelper[T = Int]
    operation tag(x: Int) -> Bool = true
  end
  sort MyIntImpl
    fact MySpec[T = Int]
    requires MyHelper[T = Int]
    operation mark(x: Int) -> Bool = true
  end
  sort Driver
    import test.wi235.hoist.MySpec.{mark}
    operation drive(x: Int, y: Int, z: Int) -> Bool =
      if mark(x) then mark(y) else mark(z)
  end
end
"#;
    let interp = interp_for(src);
    let kb = interp.kb();

    let aw_sym = kb.try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .expect("apply_within");
    let var_ref_sym = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref");
    let let_expr_sym = kb.try_resolve_symbol("anthill.reflect.Expr.let_expr")
        .expect("let_expr");
    let cr_sym = kb.try_resolve_symbol("anthill.reflect.Expr.construct_requirement")
        .expect("construct_requirement");
    let cons_sym = kb.try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons");
    let spec_op = kb.try_resolve_symbol("test.wi235.hoist.MySpec.mark")
        .expect("MySpec.mark registered");
    let drive_sym = kb.try_resolve_symbol("test.wi235.hoist.Driver.drive")
        .expect("Driver.drive registered");

    // Count rewritten apply_withins whose requirements channel head is
    // a var_ref vs a construct_requirement. Look up via the original
    // apply TermId (not dispatch_origin_iter), so we read the CURRENT
    // rewrite — post-hoist updates `dispatch_rewrites` in place.
    let apply_tids: Vec<_> = kb.occurrence_store().classifications_iter()
        .filter_map(|(occ, class)| {
            match class {
                anthill_core::kb::typing::CallClass::ConcreteApplyWithin {
                    spec_op_sym, ..
                } if *spec_op_sym == spec_op => Some(kb.occurrence_store().term(occ)),
                _ => None,
            }
        })
        .collect();
    let mut var_ref_count = 0;
    let mut cr_count = 0;
    for apply_tid in &apply_tids {
        let rewritten_tid = match kb.dispatch_rewrite_of(*apply_tid) {
            Some(t) => t,
            None => continue,
        };
        let Term::Fn { functor, named_args, .. } = kb.get_term(rewritten_tid)
        else { continue };
        if *functor != aw_sym { continue; }
        let Some(reqs_tid) = get_named_arg(kb, named_args, "requirements")
        else { continue };
        let Term::Fn { functor: list_fn, named_args: list_named, .. } =
            kb.get_term(reqs_tid)
        else { continue };
        if *list_fn != cons_sym { continue; }
        let Some(head_tid) = get_named_arg(kb, list_named, "head")
        else { continue };
        if let Term::Fn { functor: head_fn, .. } = kb.get_term(head_tid) {
            if *head_fn == var_ref_sym { var_ref_count += 1; }
            else if *head_fn == cr_sym { cr_count += 1; }
        }
    }
    assert!(
        var_ref_count >= 2,
        "WI-235 hoist must fire: at least two of the three MySpec.mark \
         calls should reference a hoisted var_ref (got var_ref_count={var_ref_count}, \
         cr_count={cr_count})"
    );

    // The op's body must be overridden with a let_expr wrap (WI-235).
    let wrapped = kb.op_body_override(drive_sym)
        .expect("op body should be overridden with a let_expr wrap");
    match kb.get_term(wrapped) {
        Term::Fn { functor, .. } => assert_eq!(*functor, let_expr_sym,
            "body-root rewrite must be a let_expr; got functor {}",
            kb.qualified_name_of(*functor)),
        other => panic!("body-root rewrite must be a Fn; got {other:?}"),
    }
}

/// Behavior check: the hoisted version evaluates to the same value as
/// the un-hoisted form would. We exercise the rewritten body and assert
/// it returns true (the impl's mark always returns true).
#[test]
fn hoisted_body_evaluates_to_same_value() {
    use anthill_core::eval::value::Value;

    let src = r#"
namespace test.wi235.hoist_eval
  import anthill.prelude.{Int, Bool}
  export MySpecE, MyHelperE, MyHelperEInt, MyImplE, EvalDriver
  sort MySpecE
    sort T = ?
    operation mark(x: T) -> Bool
  end
  sort MyHelperE
    sort T = ?
    operation tag(x: T) -> Bool
  end
  sort MyHelperEInt
    fact MyHelperE[T = Int]
    operation tag(x: Int) -> Bool = true
  end
  sort MyImplE
    fact MySpecE[T = Int]
    requires MyHelperE[T = Int]
    operation mark(x: Int) -> Bool = true
  end
  sort EvalDriver
    import test.wi235.hoist_eval.MySpecE.{mark}
    operation drive(a: Int, b: Int, c: Int) -> Bool =
      if mark(a) then mark(b) else mark(c)
  end
end
"#;
    let mut interp = interp_for(src);
    let value = interp.call(
        "test.wi235.hoist_eval.EvalDriver.drive",
        &[Value::Int(1), Value::Int(2), Value::Int(3)],
    ).expect("drive should reduce");
    assert_eq!(value.as_bool(), Some(true),
        "hoisted body must still return the impl's mark result (true)");
}

/// Body-root rewrite check: with 4 calls in nested branches, the body
/// root is wrapped in a let_expr. (We don't directly probe arena
/// counts — the previous test already pins runtime correctness, and
/// IR-level evidence that the let-wrap exists is sufficient.)
#[test]
fn hoist_emits_body_root_let_wrap_for_nested_branches() {
    let src = r#"
namespace test.wi235.hoist_nested
  import anthill.prelude.{Int, Bool}
  export MySpecN, MyHelperN, MyHelperNInt, MyImplN, ArenaDriver
  sort MySpecN
    sort T = ?
    operation mark(x: T) -> Bool
  end
  sort MyHelperN
    sort T = ?
    operation tag(x: T) -> Bool
  end
  sort MyHelperNInt
    fact MyHelperN[T = Int]
    operation tag(x: Int) -> Bool = true
  end
  sort MyImplN
    fact MySpecN[T = Int]
    requires MyHelperN[T = Int]
    operation mark(x: Int) -> Bool = true
  end
  sort ArenaDriver
    import test.wi235.hoist_nested.MySpecN.{mark}
    operation drive(a: Int, b: Int) -> Bool =
      if mark(a) then
        if mark(b) then mark(a) else mark(b)
      else
        mark(a)
  end
end
"#;
    let interp = interp_for(src);
    let kb = interp.kb();
    let drive_sym = kb.try_resolve_symbol("test.wi235.hoist_nested.ArenaDriver.drive")
        .expect("ArenaDriver.drive registered");
    let let_expr_sym = kb.try_resolve_symbol("anthill.reflect.Expr.let_expr")
        .expect("let_expr");
    let wrapped = kb.op_body_override(drive_sym)
        .expect("op body should be overridden");
    match kb.get_term(wrapped) {
        Term::Fn { functor, .. } => assert_eq!(*functor, let_expr_sym,
            "op body override must be a let_expr"),
        _ => panic!("op body override must be a Fn"),
    }
}

