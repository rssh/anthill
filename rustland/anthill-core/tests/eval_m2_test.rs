//! Integration tests for M2 of the expression evaluator (WI-043).
//!
//! Covers: pattern matching, lambdas + closures, list/tuple literals,
//! MatchFailed on non-exhaustive match.

mod common;

use anthill_core::eval::{EvalError, Interpreter, Value};

use common::load_kb_with;

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int, got {v:?}"))
}

#[test]
fn m2_match_wildcard() {
    let src = r#"
namespace test.m2_match_wild
  operation main() -> Int =
    match 7
      case _ -> 1
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_match_wild.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 1);
}

#[test]
fn m2_match_var_binds_scrutinee() {
    let src = r#"
namespace test.m2_match_var
  operation main() -> Int =
    match 42
      case x -> x
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_match_var.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 42);
}

#[test]
fn m2_match_literal_picks_arm() {
    let src = r#"
namespace test.m2_match_lit
  operation choose(n: Int) -> Int =
    match n
      case 1 -> 10
      case 2 -> 20
      case _ -> 99
  operation main() -> Int = choose(2)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_match_lit.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 20);
}

#[test]
fn m2_match_failed_raises_error() {
    // No wildcard, no matching literal → MatchFailed.
    let src = r#"
namespace test.m2_match_fail
  operation choose(n: Int) -> Int =
    match n
      case 1 -> 10
      case 2 -> 20
  operation main() -> Int = choose(3)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let err = interp.call("test.m2_match_fail.main", &[]).unwrap_err();
    assert!(
        matches!(err, EvalError::MatchFailed { .. }),
        "expected MatchFailed, got {err:?}",
    );
}

#[test]
fn m2_lambda_identity() {
    let src = r#"
namespace test.m2_lambda
  operation main() -> Int =
    let f = lambda x -> x
    f(5)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_lambda.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 5);
}

#[test]
fn m2_lambda_closes_over_outer_binding() {
    let src = r#"
namespace test.m2_closure
  operation main() -> Int =
    let k = 7
    let f = lambda x -> k
    f(99)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_closure.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 7);
}

#[test]
fn m2_list_literal_builds_cons_chain() {
    // `cons(h, t)` is a positional pattern; at runtime the evaluator presents
    // entity named fields (head/tail) after positional, so positional patterns
    // still line up with the cons constructor shape.
    let src = r#"
namespace test.m2_list
  import anthill.prelude.{List}

  operation first(xs: List[T = Int]) -> Int =
    match xs
      case cons(h, t) -> h
      case _ -> 0
  operation main() -> Int = first([10, 20, 30])
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_list.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 10);
}

#[test]
fn m2_closure_arena_reclaims_on_drop() {
    // After the call completes, every closure allocated during evaluation
    // must be reclaimed — closures are only reachable through the returned
    // `Value`, and a scalar return drops them all. Guards WI-055's refcount
    // wiring: prior to it, the arena grew monotonically.
    let src = r#"
namespace test.m2_closure_gc
  operation main() -> Int =
    let f = lambda x -> x
    let g = lambda y -> y
    f(7)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_closure_gc.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 7);
    assert_eq!(
        interp.closure_arena_live_count(),
        0,
        "all closures should be reclaimed after the call returns",
    );
}

#[test]
fn m2_tuple_literal_and_pattern() {
    let src = r#"
namespace test.m2_tuple
  operation pair_first(p: (Int, Int)) -> Int =
    match p
      case (a, _) -> a
  operation main() -> Int = pair_first((3, 4))
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_tuple.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 3);
}

#[test]
fn m2_empty_list_matches_nil() {
    // `[]` builds a `nil`-constructor Value::Entity with no args. Pattern
    // `nil()` (zero-arg constructor pattern) must match it.
    let src = r#"
namespace test.m2_empty_list
  import anthill.prelude.{List}

  operation is_empty(xs: List[T = Int]) -> Int =
    match xs
      case nil() -> 1
      case _ -> 0
  operation main() -> Int = is_empty([])
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_empty_list.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 1);
}

#[test]
fn m2_list_recursive_walk_with_tco() {
    // Walk a list to its end and return a constant — proves pattern match
    // on cons/nil plus operation recursion (TCO) compose cleanly. With
    // stack cap 4 the three-element walk would fail instantly if TCO
    // weren't collapsing the self-call's frame.
    let src = r#"
namespace test.m2_walk
  import anthill.prelude.{List}

  operation walk(xs: List[T = Int]) -> Int =
    match xs
      case nil() -> 99
      case cons(_, t) -> walk(t)
  operation main() -> Int = walk([1, 2, 3])
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    interp.set_stack_depth_cap(4);
    let result = interp.call("test.m2_walk.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 99);
}

#[test]
fn m2_higher_order_lambda() {
    // Pass a lambda as an argument; the callee invokes it. Exercises that
    // Value::Closure threads correctly through apply's arg-collection and
    // through the callee's local lookup.
    let src = r#"
namespace test.m2_ho
  import anthill.prelude.{Function}

  operation apply_twice(f: Function[Int, Int], x: Int) -> Int =
    f(f(x))
  operation main() -> Int =
    let g = lambda n -> n
    apply_twice(g, 5)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_ho.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 5);
}

#[test]
fn m2_user_defined_reduce_on_list_and_set() {
    // `reduce` isn't in stdlib yet (WI-064 tracks that). Define it in test
    // code for both a cons-spine list and a positional SetLiteral. The
    // step function is a lambda that pattern-matches a pair tuple and
    // calls the `add` builtin — exercises the closure-calls-builtin path
    // called out in the WI-043 acceptance ("let f = λ(x) -> x+1 in f(2)").
    let src = r#"
namespace test.m2_reduce
  import anthill.prelude.{List, Set, Function, Int}

  operation reduce_list(xs: List[T = Int], acc: Int, f: Function[(Int, Int), Int]) -> Int =
    match xs
      case nil() -> acc
      case cons(h, t) -> reduce_list(t, f((acc, h)), f)

  operation reduce_set3(s: Set[T = Int], acc: Int, f: Function[(Int, Int), Int]) -> Int =
    match s
      case SetLiteral(a, b, c) -> f((f((f((acc, a)), b)), c))
      case _ -> acc

  operation main() -> Int =
    let add_pair = lambda (a, b) -> a + b
    let list_sum = reduce_list([1, 2, 3, 4], 0, add_pair)
    reduce_set3({10, 20, 30}, list_sum, add_pair)
end
"#;
    let mut interp = common::interp_for(src);
    // list_sum = 0+1+2+3+4 = 10; set_sum = 10+10+20+30 = 70.
    let result = interp.call("test.m2_reduce.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 70);
}

#[test]
fn m2_set_literal_dedupes_duplicates() {
    // {10, 20, 20, 30} has four positional elements at parse time; after
    // SetLiteral dedup (scalar_eq on Int) it carries three. `count` uses
    // arity-exact constructor patterns to report which cardinality the
    // runtime actually produced.
    let src = r#"
namespace test.m2_set_dedup
  import anthill.prelude.{Set}

  operation count(s: Set[T = Int]) -> Int =
    match s
      case SetLiteral(_, _, _) -> 3
      case SetLiteral(_, _, _, _) -> 4
      case _ -> 0
  operation main() -> Int = count({10, 20, 20, 30})
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_set_dedup.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 3);
}

#[test]
fn m2_set_literal_as_entity() {
    // `{1, 2, 3}` parses as SetLiteral entity. The evaluator wraps it as
    // `Value::Entity { functor: SetLiteral, pos: [1,2,3], named: [] }`
    // (generic entity path — no dedicated `Value::Set` yet). Destructuring
    // via `SetLiteral(a, b, c)` binds positions in order.
    let src = r#"
namespace test.m2_set
  import anthill.prelude.{Set}

  operation first_of_three(s: Set[T = Int]) -> Int =
    match s
      case SetLiteral(a, _, _) -> a
      case _ -> 0
  operation main() -> Int = first_of_three({10, 20, 30})
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m2_set.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 10);
}
