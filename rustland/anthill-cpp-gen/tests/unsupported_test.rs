//! Negative tests for the cpp17-stl profile's "unsupported feature"
//! error pass.
//!
//! Two classes of features cannot be lowered to RAII-only C++:
//!   1. Self-referential anonymous lambdas — `let f = lambda(?x) -> f(...)`.
//!      The emitted `[=](auto x){ return body; }` has no name in scope
//!      for `f`, and "fixing" it (Y-combinator or `std::function`) either
//!      bloats the call site or introduces refcounted heap closures.
//!   2. Runtime use of `anthill.reflect.*` / `anthill.persistence.*`
//!      sorts. Both rely on a hash-consed term store, which has no host
//!      counterpart in cpp17-stl.
//!
//! These tests assert that codegen rejects these inputs with a clear
//! error message, rather than emitting non-compilable C++.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::{load_kb_with, load_kb_with_lenient};

#[test]
fn recursive_anonymous_lambda_rejected() {
    // `let f = lambda(?x) -> f(x)` — the lambda body refers to its own
    // binder. The IIFE lowering would emit
    //   auto f = [=](auto x){ return f(x); };
    // which doesn't compile (the inner `f` shadows nothing and the
    // outer `f` isn't visible inside its own initializer).
    //
    // `synthesize_method_body` catches `lower_expr` errors and turns
    // them into TODO comments in the emitted body, so the diagnostic
    // surfaces in the produced C++ string rather than as a top-level
    // `Err`. We assert it shows up there.
    let source = r#"
        namespace test.unsupported
          import anthill.prelude.{Int64}
          export Calc
          sort Calc
            operation lam(n: Int64) -> Int64 =
              let f = lambda x -> f(x)
              n
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.unsupported.Calc")
        .expect("emit_traits_struct surfaces unsupported features as TODO comments");

    assert!(
        cpp.contains("recursive anonymous lambda not supported"),
        "expected unsupported-recursive-lambda diagnostic in body, got:\n{cpp}"
    );
    assert!(
        cpp.contains("named operation"),
        "diagnostic should suggest lifting to a named operation:\n{cpp}"
    );
}

#[test]
fn non_recursive_let_lambda_still_works() {
    // Sanity check: a `let f = lambda(?x) -> add(x, 1)` (no self-ref)
    // must still lower successfully. The detector keys on the binder
    // name appearing inside the lambda body — when it doesn't, the
    // existing IIFE + generic-lambda emission applies unchanged.
    let source = r#"
        namespace test.unsupported_ok
          import anthill.prelude.{Int64}
          export Calc
          sort Calc
            operation lam(n: Int64) -> Int64 =
              let g = lambda x -> add(x, 1)
              n
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.unsupported_ok.Calc")
        .expect("non-recursive lambda must still lower");
    assert!(
        cpp.contains("[=](auto x) { return (x + 1); }"),
        "non-recursive lambda body should lower normally:\n{cpp}"
    );
}

#[test]
fn reflect_sort_in_signature_rejected() {
    // An operation whose return type is `TermRepr` (from anthill.reflect)
    // requires the host language to have a hash-consed term store. The
    // cpp17-stl profile has none, so codegen must refuse.
    let source = r#"
        namespace test.unsupported_reflect
          import anthill.reflect.{TermRepr}
          export Inspector
          sort Inspector
            operation peek() -> TermRepr
          end
        end
    "#;
    let kb = load_kb_with(source);
    let err = emit_traits_struct(&kb, "test.unsupported_reflect.Inspector")
        .expect_err("reflect sort in op signature must be rejected");

    let msg = err.to_string();
    assert!(
        msg.contains("does not support runtime reflection"),
        "expected reflection-unsupported diagnostic, got: {msg}"
    );
    assert!(
        msg.contains("anthill.reflect.TermRepr"),
        "diagnostic should name the offending sort: {msg}"
    );
}

#[test]
fn persistence_sort_in_signature_rejected() {
    // Same idea for `anthill.persistence.Store`: a host with no
    // serialization story for live anthill terms cannot honor the
    // operation surface, so codegen refuses up front.
    let source = r#"
        namespace test.unsupported_persistence
          import anthill.persistence.{Store}
          import anthill.prelude.{Unit}
          export Bridge
          sort Bridge
            operation tell(s: Store) -> Unit
          end
        end
    "#;
    let kb = load_kb_with(source);
    let err = emit_traits_struct(&kb, "test.unsupported_persistence.Bridge")
        .expect_err("persistence sort in op signature must be rejected");

    let msg = err.to_string();
    assert!(
        msg.contains("does not support runtime persistence"),
        "expected persistence-unsupported diagnostic, got: {msg}"
    );
    assert!(
        msg.contains("anthill.persistence.Store"),
        "diagnostic should name the offending sort: {msg}"
    );
}
