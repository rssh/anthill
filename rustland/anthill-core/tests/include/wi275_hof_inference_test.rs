//! WI-275 — bidirectional inference for higher-order arguments.
//!
//! A lambda or a bare operation reference passed in a `Function`-typed
//! parameter slot is checked against that declared `Function[A, B, E]`:
//!
//! 1. An inline lambda (`map(xs, lambda x -> add(x, 1))`) types its
//!    parameter from `A`, so an overloaded body call (`add`) resolves
//!    instead of failing as a dispatch ambiguity over an untyped param.
//! 2. A bare operation name (`map(xs, inc)`) is eta-lifted to a function
//!    value of the operation's arrow type.
//! 3. Soundness boundary: a bare operation whose arrow type does NOT
//!    conform to the expected `Function` slot is still rejected — the eta
//!    builds the operation's real signature and unifies it, it does not
//!    rubber-stamp any name.
//!
//! The runtime half (an eta'd operation reference applied as a function
//! value) is exercised in `eval_test::m2_hof_inference_sort_and_map`.

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
fn inline_lambda_param_typed_from_function_slot() {
    // `lambda x -> x + 1` previously left `x` an unconstrained var, so the
    // overloaded `+` (`Numeric.add`) in the body was dispatch-ambiguous. With
    // the declared `Function[Int64, Int64]` pushed into the argument, `x : Int64`
    // and the body resolves.
    let src = r#"
namespace test.wi275.inline
  import anthill.prelude.{List, Int64, Function}

  operation my_map(xs: List[T = Int64], f: Function[Int64, Int64]) -> List[T = Int64] =
    match xs
      case nil() -> nil()
      case cons(h, t) -> cons(f(h), my_map(t, f))

  operation go() -> List[T = Int64] = my_map([1, 2, 3], lambda x -> x + 1)
end
"#;
    let errs = load_errs(src);
    assert!(errs.is_empty(), "inline lambda HOF arg should type-check:\n{}", fmt(&errs));
}

#[test]
fn bare_named_operation_eta_lifted_to_function_value() {
    // A bare `inc` in a `Function[Int64, Int64]` slot is the operation as a
    // function value, not its return type `Int64`.
    let src = r#"
namespace test.wi275.named
  import anthill.prelude.{List, Int64, Function}

  operation my_map(xs: List[T = Int64], f: Function[Int64, Int64]) -> List[T = Int64] =
    match xs
      case nil() -> nil()
      case cons(h, t) -> cons(f(h), my_map(t, f))

  operation inc(n: Int64) -> Int64 = n + 1
  operation go() -> List[T = Int64] = my_map([1, 2, 3], inc)
end
"#;
    let errs = load_errs(src);
    assert!(errs.is_empty(), "bare named-op HOF arg should type-check:\n{}", fmt(&errs));
}

#[test]
fn wrong_typed_operation_in_function_slot_is_rejected() {
    // Soundness: the eta builds `bad`'s real arrow type `String -> Bool`,
    // which does not conform to the expected `Function[Int64, Int64]` — so the
    // typer rejects it rather than accepting any operation name.
    let src = r#"
namespace test.wi275.neg
  import anthill.prelude.{List, Int64, String, Function, Bool}

  operation my_map(xs: List[T = Int64], f: Function[Int64, Int64]) -> List[T = Int64] =
    match xs
      case nil() -> nil()
      case cons(h, t) -> cons(f(h), my_map(t, f))

  operation bad(s: String) -> Bool = true
  operation go() -> List[T = Int64] = my_map([1, 2, 3], bad)
end
"#;
    let errs = load_errs(src);
    assert!(
        !errs.is_empty(),
        "a String -> Bool operation must not conform to Function[Int64, Int64]",
    );
    let formatted = fmt(&errs);
    assert!(
        formatted.contains("my_map.f") || formatted.contains("Function"),
        "expected a Function-slot mismatch diagnostic, got:\n{formatted}",
    );
}

#[test]
fn body_less_builtin_in_function_slot_is_rejected_not_crashed() {
    // Soundness: the eta only lifts an operation the runtime can run as a
    // function value (one with an anthill body). A body-less builtin (`as_term`)
    // has no runtime `Value::OpRef` form, so it must NOT type-check as a function
    // value — otherwise it would load clean and then crash at eval as a zero-arg
    // call. It stays a loud type error (its return type does not conform to the
    // expected `Function`).
    let src = r#"
namespace test.wi275.builtin
  import anthill.prelude.{List, Int64, Function}
  import anthill.reflect.{Term}

  operation my_map(xs: List[T = Int64], f: Function[Int64, Term]) -> List[T = Term] =
    match xs
      case nil() -> nil()
      case cons(h, t) -> cons(f(h), my_map(t, f))

  operation go() -> List[T = Term] = my_map([1, 2, 3], as_term)
end
"#;
    let errs = load_errs(src);
    assert!(
        !errs.is_empty(),
        "a body-less builtin must not eta-lift into a Function slot",
    );
    let formatted = fmt(&errs);
    assert!(
        formatted.contains("my_map.f") || formatted.contains("Function"),
        "expected a Function-slot mismatch diagnostic, got:\n{formatted}",
    );
}
