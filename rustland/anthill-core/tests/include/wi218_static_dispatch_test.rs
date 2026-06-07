//! WI-218 — static-dispatch rewrite for spec ops.
//!
//! After typing, calls to body-less spec ops resolved to a Unique impl
//! must be rewritten so the eval invokes the impl body directly. The
//! rewrite is recorded in `kb.dispatch_rewrites` (term → rewritten term)
//! and `kb.dispatch_origin` (rewritten term → original spec op symbol).
//!
//! This test pins the runtime acceptance: a body that calls a spec op
//! by bare name actually executes the impl body, not erroring with
//! 'unknown operation'.


use anthill_core::eval::Value;
use crate::common::interp_for;

#[test]
fn spec_op_call_dispatches_to_impl_body_at_runtime() {
    // Tiny spec/impl pair. Spec `Foo` has a body-less op `describe(x: T)`
    // parameterized by T. Impl `IntFoo` declares `fact Foo[T = Int64]`
    // and supplies a concrete `describe(x: Int64) -> String` body.
    // Caller-side `main_test(n: Int64)` calls bare `describe(n)`. Without
    // WI-218 the eval errors 'unknown operation: describe'; with the
    // rewrite the eval invokes IntFoo.describe and returns "an int".
    let src = r#"
namespace test.wi218
  import anthill.prelude.{Int64, String}

  sort Foo
    sort T = ?
    operation describe(x: T) -> String
  end

  sort IntFoo
    fact Foo[T = Int64]
    operation describe(x: Int64) -> String = "an int"
  end

  sort Driver
    import test.wi218.Foo.{describe}
    operation main_test(n: Int64) -> String = describe(n)
  end
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.wi218.Driver.main_test", &[Value::Int(42)])
        .expect("main_test should run");
    assert_eq!(result.as_str(), Some("an int"),
        "expected impl body to run; got {result:?}");
}

#[test]
fn dispatch_origin_records_the_spec_op_symbol() {
    // The provenance side table: dispatch_origin maps the rewritten
    // apply TermId back to the original spec op symbol so reflection /
    // debug / proof-record specialization can recover "this was originally
    // Foo.describe".
    let src = r#"
namespace test.wi218_origin
  import anthill.prelude.{Int64, String}

  sort Bar
    sort T = ?
    operation describe(x: T) -> String
  end

  sort IntBar
    fact Bar[T = Int64]
    operation describe(x: Int64) -> String = "concrete"
  end

  sort Driver
    import test.wi218_origin.Bar.{describe}
    operation main_test(n: Int64) -> String = describe(n)
  end
end
"#;
    let interp = interp_for(src);
    let kb = interp.kb();
    // After load, dispatch_rewrites should have at least one entry
    // (for main_test's body's `describe(n)` call). And every rewritten
    // apply's dispatch_origin should be the spec op (Bar.describe).
    let bar_describe = kb.try_resolve_symbol("test.wi218_origin.Bar.describe")
        .expect("Bar.describe should be registered");
    let int_bar_describe = kb.try_resolve_symbol("test.wi218_origin.IntBar.describe")
        .expect("IntBar.describe should be registered");

    let mut found_origin_record = false;
    for (rewritten_tid, spec_sym) in kb.dispatch_origin_iter() {
        if spec_sym == bar_describe {
            found_origin_record = true;
            // The rewritten term should be an apply with fn = IntBar.describe.
            use anthill_core::kb::term::Term;
            if let Term::Fn { named_args, .. } = kb.get_term(rewritten_tid) {
                let fn_arg = named_args.iter()
                    .find(|(s, _)| kb.resolve_sym(*s) == "fn")
                    .map(|(_, v)| *v);
                if let Some(fn_tid) = fn_arg {
                    if let Term::Ref(s) = kb.get_term(fn_tid) {
                        assert_eq!(*s, int_bar_describe,
                            "rewritten apply.fn should point at IntBar.describe");
                    }
                }
            }
        }
    }
    assert!(found_origin_record,
        "expected dispatch_origin to record a Bar.describe → impl rewrite");
}
