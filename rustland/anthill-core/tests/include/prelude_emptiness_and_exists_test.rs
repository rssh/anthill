//! `Option.isEmpty` / `nonEmpty`, and `exists` beside `find`, DRIVEN.
//!
//! Every case evaluates and asserts the value. That matters more than usual here:
//! the CLI cannot demonstrate any of these, because a `Bool`-returning operation
//! yields nothing through the arity+1 relational view — measured, and true of a
//! bare `operation p() -> Bool = true` as much as of these, so it is a property of
//! that surface and not of the additions.
//!
//! WHAT FAILS WHEN BACKED OUT: delete any one of the five operations and its case
//! fails to load. The `find` rows are the CONTROL — they pass either way, and they
//! are here because `exists` is DEFINED as `find(...).nonEmpty()`, so an `exists`
//! that agreed with itself but disagreed with `find` would be the interesting bug.

use anthill_core::eval::Value;

fn probe(body: &str) -> String {
    format!(
        r#"
namespace probe
  import anthill.prelude.{{List, Int64, Bool, Option}}
  import anthill.prelude.List.{{nil, cons}}
  import anthill.prelude.Option.{{some, none}}

  operation xs() -> List[T = Int64] = cons(head: 1, tail: cons(head: 2, tail: nil))
  operation empty_xs() -> List[T = Int64] = nil

  operation run() -> {body}
end
"#
    )
}

fn eval_bool(body: &str) -> bool {
    let v = crate::common::interp_for(&probe(body))
        .call("probe.run", &[])
        .unwrap_or_else(|e| panic!("probe.run failed for `{body}`: {e:?}"));
    match v {
        Value::Bool(b) => b,
        other => panic!("expected Bool for `{body}`, got {other:?}"),
    }
}

#[test]
fn option_is_empty_answers_both_ways() {
    assert!(eval_bool("Bool = Option.isEmpty(none)"));
    assert!(!eval_bool("Bool = Option.isEmpty(some(1))"));
}

#[test]
fn option_non_empty_is_the_negation() {
    assert!(!eval_bool("Bool = Option.nonEmpty(none)"));
    assert!(eval_bool("Bool = Option.nonEmpty(some(1))"));
}

#[test]
fn iterable_non_empty_answers_both_ways() {
    assert!(eval_bool("Bool = xs().nonEmpty()"));
    assert!(!eval_bool("Bool = empty_xs().nonEmpty()"));
    // isEmpty predates this change; here as the control that nonEmpty is its inverse
    // rather than a second, independently-wrong walk.
    assert!(!eval_bool("Bool = xs().isEmpty()"));
    assert!(eval_bool("Bool = empty_xs().isEmpty()"));
}

#[test]
fn exists_agrees_with_find_on_every_case() {
    // present, absent, and empty — and each paired with the `find` it is defined over.
    assert!(eval_bool("Bool = xs().exists(lambda x -> x === 2)"));
    assert!(eval_bool("Bool = Option.nonEmpty(xs().find(lambda x -> x === 2))"));

    assert!(!eval_bool("Bool = xs().exists(lambda x -> x === 9)"));
    assert!(!eval_bool("Bool = Option.nonEmpty(xs().find(lambda x -> x === 9))"));

    assert!(!eval_bool("Bool = empty_xs().exists(lambda x -> x === 1)"));
}
