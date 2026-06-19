//! WI-517 — type-annotated lambda binders.
//!
//! The grammar accepts an optional `: Type` annotation on a lambda binder,
//! written in parens: a single binder `lambda (x: T) -> body`, or a tuple
//! `lambda (a: A, b: B) -> body`. The annotation lets a lambda be written
//! WITHOUT an expected-type context (e.g. a bare `let f = lambda (x: Int64)
//! -> ...`) and documents intent in foldLeft-style callbacks.
//!
//! End-to-end coverage:
//! 1. A single typed binder pins the parameter type with no expected arrow,
//!    so an overloaded body call (`+`) resolves instead of staying a
//!    dispatch-ambiguity over an untyped param.
//! 2. A body that contradicts the annotation is rejected loudly.
//! 3. Tuple binders pin each element's type with no expected arrow.
//!
//! The grammar/parse side is exercised in
//! `tree-sitter-anthill/test/corpus/expressions.txt`.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra source → load errors (typer diagnostics among them).
fn load_errs(extra: &str) -> Vec<load::LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).err().unwrap_or_default()
}

fn fmt(errs: &[load::LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

#[test]
fn single_typed_binder_pins_param_without_expected_context() {
    // `let f = lambda (x: Int64) -> x + 1` has NO expected-type context for
    // the lambda. The `x: Int64` annotation pins the parameter so the
    // overloaded `+` (`Numeric.add`) in the body resolves. Without the
    // annotation `x` would be a fresh var and `+` would be dispatch-ambiguous.
    let src = r#"
namespace test.wi517.single
  import anthill.prelude.{Int64}

  operation go() -> Int64 =
    let f = lambda (x: Int64) -> x + 1
    f(5)
end
"#;
    let errs = load_errs(src);
    assert!(errs.is_empty(), "annotated single binder should type-check:\n{}", fmt(&errs));
}

#[test]
fn body_contradicting_annotation_is_rejected() {
    // Soundness: the binder is annotated `x: String`, but the body passes it
    // to `needs_int(n: Int64)`. The annotation pins `x : String`, so the call
    // conflicts and is rejected — the annotation is not silently ignored.
    let src = r#"
namespace test.wi517.mismatch
  import anthill.prelude.{Int64, String}

  operation needs_int(n: Int64) -> Int64 = n
  operation go() -> Int64 =
    let f = lambda (x: String) -> needs_int(x)
    5
end
"#;
    let errs = load_errs(src);
    assert!(!errs.is_empty(), "body contradicting the binder annotation must be rejected");
}

#[test]
fn tuple_binder_annotation_contradicting_known_context_is_rejected() {
    // Soundness: a tuple-destructuring lambda is passed to a HOF whose callback
    // takes `(Int64, Int64)`, but element `a` is annotated `String`. The
    // context-known component type (Int64) wins for the binding, so the body's
    // `needs_str(a)` (which expects String) is a loud mismatch — the lambda's
    // arrow cannot advertise `(Int64, Int64)` while its body treats `a` as
    // String. (Regression: an earlier draft let the annotation override the
    // known component type, accepting this unsoundly.)
    let src = r#"
namespace test.wi517.tuplemismatch
  import anthill.prelude.{Int64, String, Function}

  operation apply_pair(f: Function[(Int64, Int64), Int64], p: (Int64, Int64)) -> Int64 = f(p)
  operation needs_str(s: String) -> Int64 = 0
  operation go() -> Int64 =
    apply_pair(lambda (a: String, b: Int64) -> needs_str(a), (1, 2))
end
"#;
    let errs = load_errs(src);
    assert!(!errs.is_empty(), "a tuple binder annotation contradicting the known callback component type must be rejected");
}

#[test]
fn typed_tuple_binders_pin_elements_without_expected_context() {
    // `lambda (a: Int64, b: Int64) -> a + b` with no expected arrow: each
    // element annotation pins its binder, so the overloaded `+` resolves.
    // Exercises the per-element `type_ann` path in `extend_env_from_pattern`.
    let src = r#"
namespace test.wi517.tuple
  import anthill.prelude.{Int64}

  operation go() -> Int64 =
    let f = lambda (a: Int64, b: Int64) -> a + b
    5
end
"#;
    let errs = load_errs(src);
    assert!(errs.is_empty(), "annotated tuple binders should type-check:\n{}", fmt(&errs));
}
