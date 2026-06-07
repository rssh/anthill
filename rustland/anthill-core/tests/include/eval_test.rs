//! Merged integration tests for the expression evaluator (WI-042 milestones M1–M5).
//!
//! Previously split into eval_m{1..5}_test.rs + eval_m5_modify_test.rs (6 binaries).
//! Consolidated to amortize stdlib-load and macOS test-binary-launch costs.
//! Test names retain the `m1_` / `m2_` / ... prefixes for filtering.


use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::eval::stream::StreamSource;
use crate::common::{
    buffered_console, interp_for, load_kb_with, register_modify_handler,
    scripted_console_input,
};

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int, got {v:?}"))
}

fn expect_bool(v: Value) -> bool {
    v.as_bool().unwrap_or_else(|| panic!("expected Bool, got {v:?}"))
}

fn expect_float(v: Value) -> f64 {
    if let Value::Float(f) = v {
        f
    } else {
        panic!("expected Float, got {v:?}")
    }
}


// ─── from eval_m1_test.rs ───
#[test]
fn m1_literal_return() {
    let src = r#"
namespace test.m1_lit
  operation main() -> Int
    = 42
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_lit.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 42);
}

#[test]
fn m1_if_true_then_else() {
    let src_true = r#"
namespace test.m1_if_true
  operation main() -> Int
    = if true then 1 else 2
end
"#;
    let kb = load_kb_with(src_true);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_if_true.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 1);
}

#[test]
fn m1_if_false_then_else() {
    let src = r#"
namespace test.m1_if_false
  operation main() -> Int
    = if false then 1 else 2
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_if_false.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 2);
}

#[test]
fn m1_let_binds_local() {
    // Block-style let: `let x = value <newline> body` (no `in` keyword).
    let src = r#"
namespace test.m1_let
  operation main() -> Int
    = let x = 7
      x
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_let.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 7);
}

#[test]
fn m1_operation_call() {
    // `main` calls a zero-arg helper that returns a literal.
    let src = r#"
namespace test.m1_call
  operation helper() -> Int
    = 11
  operation main() -> Int
    = helper()
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_call.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 11);
}

#[test]
fn m1_operation_call_with_arg() {
    // Identity operation exercises param binding + arg plumbing.
    let src = r#"
namespace test.m1_arg
  operation id(x: Int) -> Int
    = x
  operation main() -> Int
    = id(99)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_arg.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 99);
}

#[test]
fn m1_non_tail_recursion_hits_depth_cap() {
    // Non-tail recursion (the recursive call wrapped in a `let` makes this
    // frame non-trivially "waiting"): each call genuinely adds an activation
    // frame and the cap catches runaway recursion. Tail infinite recursion
    // would instead loop forever under TCO — see `m1_tail_recursion_deep`.
    let src = r#"
namespace test.m1_non_tail
  operation f() -> Int =
    let _ = f()
    0
  operation main() -> Int = f()
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    interp.set_stack_depth_cap(64);
    let err = interp.call("test.m1_non_tail.main", &[]).unwrap_err();
    match err {
        EvalError::DepthExceeded { cap } => assert_eq!(cap, 64),
        other => panic!("expected DepthExceeded, got {other:?}"),
    }
}

#[test]
fn m1_infinite_tail_loop_hits_step_cap() {
    // TCO makes `loop() = loop()` run in O(1) stack. Without a step cap
    // that's an infinite time loop — `depth_cap` can't catch it because
    // the stack doesn't grow. `step_cap` is the orthogonal limit designed
    // for this: it bounds wall-time work, not memory. Together the two
    // caps cover the full recursion failure-mode matrix.
    let src = r#"
namespace test.m1_loop
  operation loop() -> Int = loop()
  operation main() -> Int = loop()
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::with_config(
        kb,
        anthill_core::eval::EvalConfig {
            depth_cap: None,
            step_cap: Some(1_000),
        },
    );
    let err = interp.call("test.m1_loop.main", &[]).unwrap_err();
    match err {
        EvalError::StepsExhausted { cap } => assert_eq!(cap, 1_000),
        other => panic!("expected StepsExhausted, got {other:?}"),
    }
}

#[test]
fn m1_recursive_operation_multi_level() {
    // Multi-level recursive operation using only M1 primitives (no
    // arithmetic, no pattern matching). The recursion is terminated by a
    // Bool-threaded state machine: each call tightens the args toward the
    // base case `(true, true) -> 42`, taking 3 tail calls from the initial
    // `(false, false)`. Proves operation-call recursion works at M1 and
    // that TCO keeps all three calls in a constant-depth stack — cap=2
    // would suffice; we use 4 to keep headroom for the test driver.
    let src = r#"
namespace test.m1_rec
  operation go(a: Bool, b: Bool) -> Int =
    if a then
      if b then 42
      else go(true, true)
    else go(true, false)
  operation main() -> Int = go(false, false)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    interp.set_stack_depth_cap(4);
    let result = interp.call("test.m1_rec.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 42);
}

// ─── from eval_m2_test.rs ───
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
    let add_pair: Function[(Int, Int), Int] = lambda (a, b) -> a + b
    let list_sum = reduce_list([1, 2, 3, 4], 0, add_pair)
    reduce_set3({10, 20, 30}, list_sum, add_pair)
end
"#;
    let mut interp = crate::common::interp_for(src);
    // list_sum = 0+1+2+3+4 = 10; set_sum = 10+10+20+30 = 70.
    let result = interp.call("test.m2_reduce.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 70);
}

#[test]
fn m2_hof_inference_sort_and_map() {
    // WI-275: bidirectional inference for higher-order arguments. A
    // comparator-parameterized sort and a `map` are driven, the transform/
    // comparator supplied THREE ways the typer previously rejected at the call
    // site for want of a param type:
    //   * an inline tuple lambda      `lambda (a, b) -> a < b`
    //   * an inline single lambda     `lambda x -> x + 1`
    //   * a BARE named operation      `lt_int` / `inc` (eta-lifted to a value)
    // Each call site pushes the declared `Function[...]` param type into the
    // argument, so the lambda's params type and a bare op name becomes a
    // function value. The descending case proves the comparator is actually
    // applied (different comparator ⇒ different order), not ignored.
    let src = r#"
namespace test.m2_hof_inf
  import anthill.prelude.{List, Function, Int, Bool}

  operation insert_by(x: Int, xs: List[T = Int], lt: Function[(Int, Int), Bool]) -> List[T = Int] =
    match xs
      case nil() -> cons(x, nil())
      case cons(h, t) ->
        if lt((x, h))
        then cons(x, cons(h, t))
        else cons(h, insert_by(x, t, lt))

  operation sort_by(xs: List[T = Int], lt: Function[(Int, Int), Bool]) -> List[T = Int] =
    match xs
      case nil() -> nil()
      case cons(h, t) -> insert_by(h, sort_by(t, lt), lt)

  operation map_int(xs: List[T = Int], f: Function[Int, Int]) -> List[T = Int] =
    match xs
      case nil() -> nil()
      case cons(h, t) -> cons(f(h), map_int(t, f))

  operation encode3(xs: List[T = Int]) -> Int =
    match xs
      case cons(a, cons(b, cons(c, _))) -> a * 100 + b * 10 + c
      case _ -> 0

  operation lt_int(a: Int, b: Int) -> Bool = a < b
  operation inc(n: Int) -> Int = n + 1

  operation main_lambda() -> Int = encode3(sort_by([3, 1, 2], lambda (a, b) -> a < b))
  operation main_named() -> Int = encode3(sort_by([3, 1, 2], lt_int))
  operation main_desc() -> Int = encode3(sort_by([3, 1, 2], lambda (a, b) -> a > b))
  operation main_map_lambda() -> Int = encode3(map_int([1, 2, 3], lambda x -> x + 1))
  operation main_map_named() -> Int = encode3(map_int([1, 2, 3], inc))
end
"#;
    let mut interp = crate::common::interp_for(src);
    let run = |interp: &mut Interpreter, op: &str| {
        expect_int(interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")))
    };
    // Ascending sort of [3,1,2] ⇒ [1,2,3] ⇒ 123, both lambda and named comparator.
    assert_eq!(run(&mut interp, "test.m2_hof_inf.main_lambda"), 123);
    assert_eq!(run(&mut interp, "test.m2_hof_inf.main_named"), 123);
    // Descending comparator ⇒ [3,2,1] ⇒ 321 (proves the comparator is applied).
    assert_eq!(run(&mut interp, "test.m2_hof_inf.main_desc"), 321);
    // map (+1) over [1,2,3] ⇒ [2,3,4] ⇒ 234, both lambda and named transform.
    assert_eq!(run(&mut interp, "test.m2_hof_inf.main_map_lambda"), 234);
    assert_eq!(run(&mut interp, "test.m2_hof_inf.main_map_named"), 234);
}

/// WI-420 (sound path): the gate rejects passing a BARE requires-carrying op as
/// a function value, but a genuine LAMBDA that calls such an op is fine. Here a
/// lambda calling `List.member` (List requires Eq[T]) is passed to a HOF with
/// NO requirement of its own and invoked there; it must evaluate correctly —
/// proving the gate did not affect closures and the lambda's requirement is
/// discharged regardless of the caller's (empty) requirement scope. (The
/// IR-level snapshot/restore guarantee for ABSTRACT requirements is pinned by
/// wi223_closure_requirements_test.)
#[test]
fn wi420_lambda_over_requires_op_passed_to_hof_evals() {
    let src = r#"
namespace test.wi420.lam
  import anthill.prelude.{List, Int, Bool, Function}
  import anthill.prelude.List.{member}

  operation use_pred(f: Function[A = Int, B = Bool], v: Int) -> Bool =
    f(v)

  operation found() -> Bool =
    use_pred(lambda e -> member(e, [1, 2, 3]), 2)

  operation absent() -> Bool =
    use_pred(lambda e -> member(e, [1, 2, 3]), 9)
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert!(
        expect_bool(interp.call("test.wi420.lam.found", &[]).expect("found runs")),
        "lambda calling a requires-op (member) must eval true for a present element",
    );
    assert!(
        !expect_bool(interp.call("test.wi420.lam.absent", &[]).expect("absent runs")),
        "lambda calling a requires-op (member) must eval false for an absent element",
    );
}

/// WI-420 (full fix): a `requires`-carrying op (`List.member`, since `List
/// requires Eq[T]`) passed BARE as a function value to a HOF with no
/// requirement of its own, applied to a concrete Int list. The `Value::OpRef`
/// captures the `Eq[Int]` dispatch dict (resolved by the typer at the eta site,
/// where the expected arrow pins `List.T := Int`) at mint, and installs it into
/// member's callee frame at apply — so member's `eq(head, x)` finds `__req_eq`
/// instead of crashing with "requirement param `__req_eq` not bound". This is
/// the exact crash WI-420 fixes.
#[test]
fn wi420_eta_concrete_member_evals() {
    let src = r#"
namespace test.wi420eta
  import anthill.prelude.{List, Int, Bool, Function}
  import anthill.prelude.List.{member}

  operation use_pair(f: Function[A = (Int, List[T = Int]), B = Bool], x: Int, xs: List[T = Int]) -> Bool =
    f((x, xs))

  operation present() -> Bool = use_pair(member, 2, [1, 2, 3])
  operation absent() -> Bool = use_pair(member, 9, [1, 2, 3])
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert!(
        expect_bool(interp.call("test.wi420eta.present", &[]).expect("present runs")),
        "2 IS a member of [1,2,3] — member eta'd as a HOF arg must eval true (WI-420)",
    );
    assert!(
        !expect_bool(interp.call("test.wi420eta.absent", &[]).expect("absent runs")),
        "9 is NOT a member of [1,2,3] — member eta'd as a HOF arg must eval false (WI-420)",
    );
}

/// WI-420 (same-sort eta): `S.check` eta-lifts its sibling `S.are_eq` (both on
/// `S requires Eq[T]`) into a HOF and applies it. A DIRECT same-sort call
/// inherits the enclosing frame at eval, but the eta'd `OpRef` ESCAPES to the
/// HOF's frame (which forwards an empty channel) — so the OpRef must capture
/// S's dispatching dict (the enclosing frame's `__req_self`) at mint, else
/// are_eq's `eq(a,b)` crashes on an unbound `__req_eq`. (Soundness hole found by
/// /code-review: the same-sort guard previously returned no dict.)
#[test]
fn wi420_eta_same_sort_captures_self_dict() {
    let src = r#"
namespace test.wi420ss
  import anthill.prelude.{Int, Bool, Function, Eq}
  import anthill.prelude.Eq.{eq}
  sort S
    sort T = ?
    requires Eq[T]
    operation are_eq(a: T, b: T) -> Bool = eq(a, b)
    operation use_pred(f: Function[A = (T, T), B = Bool], x: T, y: T) -> Bool = f((x, y))
    operation check(x: T, y: T) -> Bool = use_pred(are_eq, x, y)
  end
  operation eq_t() -> Bool = S.check(1, 1)
  operation eq_f() -> Bool = S.check(1, 2)
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert!(
        expect_bool(interp.call("test.wi420ss.eq_t", &[]).expect("eq_t runs")),
        "same-sort eta: are_eq(1,1) must eval true — OpRef captured S's __req_self (WI-420)",
    );
    assert!(
        !expect_bool(interp.call("test.wi420ss.eq_f", &[]).expect("eq_f runs")),
        "same-sort eta: are_eq(1,2) must eval false (WI-420)",
    );
}

#[test]
fn wi064_stdlib_combinators_fold_map_find() {
    // WI-064: the stdlib higher-order combinators run end-to-end on a List
    // (admissible as a Stream via `List provides Stream`). The transforms /
    // predicate are named ops (eta-lifted to function values, WI-275).
    //   * fold_left / fold_right reduce a list to its sum (the acceptance);
    //   * map (the lazy `mapped` carrier that provides Stream) transforms each
    //     element — `collect`-ed back to a List;
    //   * find returns the first matching element.
    // `map` needs explicit `[Dst, Eff]` (the output element / effect are not
    // yet inferred from the transform / source — a WI-275-class refinement).
    let src = r#"
namespace test.wi064
  import anthill.prelude.{List, Int, Stream, Bool, Option}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Stream.{collect, fold_left, fold_right, find}
  import anthill.prelude.MappedStream.{map}

  operation addp(a: Int, b: Int) -> Int = a + b
  operation subt(a: Int, b: Int) -> Int = a - b
  operation inc(n: Int) -> Int = n + 1
  operation is_big(n: Int) -> Bool = n > 2

  operation encode3(xs: List[T = Int]) -> Int =
    match xs
      case cons(a, cons(b, cons(c, _))) -> a * 100 + b * 10 + c
      case _ -> 0

  operation sum() -> Int = fold_left([1, 2, 3, 4], 0, addp)
  operation sumr() -> Int = fold_right([1, 2, 3, 4], 0, addp)
  -- Non-commutative `subt` separates the two folds (and would catch a swapped
  -- tuple order): fold_left ((0-1)-2)-3 = -6; fold_right 1-(2-(3-0)) = 2.
  operation foldl_sub() -> Int = fold_left([1, 2, 3], 0, subt)
  operation foldr_sub() -> Int = fold_right([1, 2, 3], 0, subt)
  -- map (+1) over [1,2,3] ⇒ [2,3,4]: collect ⇒ 234; folded ⇒ 9; empty ⇒ 0.
  operation mapped_inc() -> Int = encode3(collect(map[Dst = Int, Eff = {}]([1, 2, 3], inc)))
  operation mapped_sum() -> Int = fold_left(map[Dst = Int, Eff = {}]([1, 2, 3], inc), 0, addp)
  operation mapped_empty() -> Int = fold_left(map[Dst = Int, Eff = {}]([], inc), 0, addp)
  -- find: first match mid-list, first match at head, and no match (none).
  operation found() -> Int = unwrap(find([1, 2, 3, 4], is_big))
  operation found_first() -> Int = unwrap(find([3, 1, 2], is_big))
  operation found_none() -> Int = unwrap(find([1, 2], is_big))
  operation unwrap(o: Option[T = Int]) -> Int =
    match o
      case some(x) -> x
      case none() -> 0 - 1
end
"#;
    let mut interp = crate::common::interp_for(src);
    let run = |interp: &mut Interpreter, op: &str| {
        expect_int(interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")))
    };
    // fold_left / fold_right sum: 1+2+3+4 = 10 (the reduce-to-sum acceptance).
    assert_eq!(run(&mut interp, "test.wi064.sum"), 10);
    assert_eq!(run(&mut interp, "test.wi064.sumr"), 10);
    // Direction-sensitive (non-commutative subtraction): left ≠ right.
    assert_eq!(run(&mut interp, "test.wi064.foldl_sub"), -6);
    assert_eq!(run(&mut interp, "test.wi064.foldr_sub"), 2);
    // map (+1): collect ⇒ [2,3,4] ⇒ 234; map then fold ⇒ 9; empty source ⇒ 0.
    assert_eq!(run(&mut interp, "test.wi064.mapped_inc"), 234);
    assert_eq!(run(&mut interp, "test.wi064.mapped_sum"), 9);
    assert_eq!(run(&mut interp, "test.wi064.mapped_empty"), 0);
    // find: first match (mid), first match (head), no match (⇒ none ⇒ -1).
    assert_eq!(run(&mut interp, "test.wi064.found"), 3);
    assert_eq!(run(&mut interp, "test.wi064.found_first"), 3);
    assert_eq!(run(&mut interp, "test.wi064.found_none"), -1);
}

#[test]
fn wi413_lazy_filter_skips_via_self_recursion() {
    // WI-413 / WI-410: the lazy `FilteredStream` carrier runs end-to-end. Its
    // `splitFirst` SELF-RECURSES on a reconstructed `filtered(rest, pred)` to
    // SKIP a dropped element — the shape that leaked an undeclared `??_` effect
    // before WI-413. `filter` returns a Stream, so it composes with the eager
    // consumers (`collect` / `fold_left`). The predicate is a named op
    // (eta-lifted to a function value, WI-275); `filter` takes explicit
    // `[S, Eff]` like its sibling `map[Dst, Eff]`.
    let src = r#"
namespace test.wi413filter
  import anthill.prelude.{List, Int, Stream, Bool, Option}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.Stream.{collect, fold_left}
  import anthill.prelude.FilteredStream.{filter}

  operation addp(a: Int, b: Int) -> Int = a + b
  operation is_big(n: Int) -> Bool = n > 2

  operation encode2(xs: List[T = Int]) -> Int =
    match xs
      case cons(a, cons(b, _)) -> a * 10 + b
      case cons(a, _) -> a
      case _ -> 0

  -- filter (n > 2) over [1,2,3,4] ⇒ [3,4]: the leading 1 and 2 are SKIPPED by
  -- the self-recursion. collect ⇒ 34; sum ⇒ 7.
  operation kept_collect() -> Int = encode2(collect(filter[S = Int, Eff = {}]([1, 2, 3, 4], is_big)))
  operation kept_sum() -> Int = fold_left(filter[S = Int, Eff = {}]([1, 2, 3, 4], is_big), 0, addp)
  -- A leading run of drops then a single keep: [1,2,3] ⇒ [3] ⇒ 3.
  operation kept_last() -> Int = fold_left(filter[S = Int, Eff = {}]([1, 2, 3], is_big), 0, addp)
  -- All dropped ⇒ empty ⇒ 0 (every element skipped via self-recursion to none).
  operation kept_none() -> Int = fold_left(filter[S = Int, Eff = {}]([1, 2], is_big), 0, addp)
  -- All kept ⇒ no skips: [3,4,5] ⇒ 12.
  operation kept_all() -> Int = fold_left(filter[S = Int, Eff = {}]([3, 4, 5], is_big), 0, addp)
end
"#;
    let mut interp = crate::common::interp_for(src);
    let run = |interp: &mut Interpreter, op: &str| {
        expect_int(interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")))
    };
    assert_eq!(run(&mut interp, "test.wi413filter.kept_collect"), 34);
    assert_eq!(run(&mut interp, "test.wi413filter.kept_sum"), 7);
    assert_eq!(run(&mut interp, "test.wi413filter.kept_last"), 3);
    assert_eq!(run(&mut interp, "test.wi413filter.kept_none"), 0);
    assert_eq!(run(&mut interp, "test.wi413filter.kept_all"), 12);
}

#[test]
fn wi414_nth_dispatches_concrete_eq() {
    // WI-414: `nth` uses `eq(i, 0)` (on a CONCRETE `Int`) under List's sort-level
    // `requires Eq[T]`. That call must resolve to `fact Eq[Int]` CONCRETELY rather
    // than defer to an unbound `__req_eq` — so `nth` is runtime-callable from an
    // external namespace (previously a compile-clean call that aborted with
    // `DeferToRequirement: __req_eq not bound`). The fix gates the defer-to-
    // requirement match: a concrete per-call value never defers to an OPEN-T
    // requirement entry. (`nth`'s body uses `if/then/else`, not the rule-only
    // `ite` op, so it is evaluable.)
    let src = r#"
namespace test.wi414
  import anthill.prelude.{List, Int, Option}
  import anthill.prelude.List.{nth}

  operation unwrap(o: Option[Int]) -> Int =
    match o
      case some(x) -> x
      case none() -> 0 - 1
  operation at0() -> Int = unwrap(nth([10, 20, 30], 0))
  operation at1() -> Int = unwrap(nth([10, 20, 30], 1))
  operation at2() -> Int = unwrap(nth([10, 20, 30], 2))
  operation oob() -> Int = unwrap(nth([10, 20, 30], 5))
  operation neg() -> Int = unwrap(nth([10, 20, 30], 0 - 1))
end
"#;
    let mut interp = crate::common::interp_for(src);
    let run = |interp: &mut Interpreter, op: &str| {
        expect_int(interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")))
    };
    assert_eq!(run(&mut interp, "test.wi414.at0"), 10);
    assert_eq!(run(&mut interp, "test.wi414.at1"), 20);
    assert_eq!(run(&mut interp, "test.wi414.at2"), 30);
    assert_eq!(run(&mut interp, "test.wi414.oob"), -1);
    assert_eq!(run(&mut interp, "test.wi414.neg"), -1);
}

/// WI-415: the CALL-SITE dual of WI-414. `member`'s `eq(head, x)` is genuinely
/// ABSTRACT (head : the element T), so it correctly DEFERS — but a call
/// `member(2, [1,2,3])` from a namespace with no `requires` must CONSTRUCT the
/// `Eq[Int]` requirement from `fact Eq[Int]` and thread it into member's frame,
/// rather than leave `__req_eq` unbound. The typer builds the parent-bundle
/// dispatching dict at compile stage (where the call-site subst still pins
/// `List.T := Int`, so `Eq[T]` substitutes to `Eq[Int]`) and stores it on the
/// `ConcreteApplyWithin` classification; eval installs it into the callee's
/// frame via the same path an explicit `apply_within` dict takes.
#[test]
fn wi415_member_call_constructs_concrete_eq_requirement() {
    let src = r#"
namespace test.wi415
  import anthill.prelude.{List, Int, Bool}
  import anthill.prelude.List.{member}

  operation has2() -> Bool = member(2, [1, 2, 3])
  operation has9() -> Bool = member(9, [1, 2, 3])
end
"#;
    let mut interp = crate::common::interp_for(src);
    let run_b = |interp: &mut Interpreter, op: &str| {
        expect_bool(interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")))
    };
    assert_eq!(run_b(&mut interp, "test.wi415.has2"), true);
    assert_eq!(run_b(&mut interp, "test.wi415.has9"), false);
}

/// WI-418: the cross-sort ABSTRACT requirement-forwarding case — the third of
/// the WI-415 gaps (and reachable only after WI-416 fixed the typer overflow
/// this scenario used to hit).
///
/// `Coll requires Eq[T]` and its op `contains` delegates to `List.member` on
/// its OWN abstract element `x : Coll.T`. The outer `Coll.contains([1,2,3], 2)`
/// is concrete (`Coll.T := Int`), so WI-415 threads `Eq[Int]` into `contains`'s
/// frame as `__req_eq`. The inner `member(x, items)` is cross-sort (member's
/// parent is `List`, not `Coll`) AND abstract (`x : Coll.T`): WI-418 makes the
/// typer build a dispatching dict for it whose `Eq` slot is a Strategy-1
/// `var_ref(__req_eq)` — forwarding `contains`'s frame `__req_eq` onward to
/// `member`'s frame (`Coll`'s `requires Eq[T]` covers `member`'s `Eq[List.T]` at
/// `List.T = Coll.T`). Without it `member`'s deferred `eq(head, x)` aborted with
/// `DeferToRequirement: __req_eq not bound`.
#[test]
fn wi418_cross_sort_abstract_call_forwards_caller_requirement() {
    let src = r#"
namespace test.wi418
  import anthill.prelude.{List, Int, Bool, Eq}
  sort Coll
    sort T = ?
    requires Eq[T]
    operation contains(items: List[T], x: T) -> Bool = List.member(x, items)
  end
  operation has2() -> Bool = Coll.contains([1, 2, 3], 2)
  operation has9() -> Bool = Coll.contains([1, 2, 3], 9)
end
"#;
    let mut interp = crate::common::interp_for(src);
    let run_b = |interp: &mut Interpreter, op: &str| {
        expect_bool(interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")))
    };
    assert_eq!(run_b(&mut interp, "test.wi418.has2"), true);
    assert_eq!(run_b(&mut interp, "test.wi418.has9"), false);
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

// ─── from eval_m3_test.rs ───
#[test]
fn m3_arithmetic_via_infix() {
    let src = r#"
namespace test.m3_arith
  operation main() -> Int = 2 + 3 * 4
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_arith.main", &[]).unwrap()), 14);
}

#[test]
fn m3_arithmetic_nested() {
    let src = r#"
namespace test.m3_nested
  operation double(n: Int) -> Int = n + n
  operation main() -> Int = double(5) * 2 - 1
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_nested.main", &[]).unwrap()), 19);
}

#[test]
fn m3_comparison_gt() {
    let src = r#"
namespace test.m3_cmp
  import anthill.prelude.Ordered.{gt}
  operation main() -> Bool = gt(7, 3)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_bool(interp.call("test.m3_cmp.main", &[]).unwrap()), true);
}

#[test]
fn m3_comparison_via_infix() {
    let src = r#"
namespace test.m3_lt
  operation main() -> Bool = 1 < 2
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_bool(interp.call("test.m3_lt.main", &[]).unwrap()), true);
}

#[test]
fn m3_if_with_comparison() {
    let src = r#"
namespace test.m3_if_cmp
  operation max_of(a: Int, b: Int) -> Int =
    if a < b then b else a
  operation main() -> Int = max_of(4, 7)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_if_cmp.main", &[]).unwrap()), 7);
}

#[test]
fn m3_bool_and_or_not() {
    let src = r#"
namespace test.m3_bool
  import anthill.prelude.Bool.{and, or, not}
  operation main() -> Bool = and(or(true, false), not(false))
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_bool(interp.call("test.m3_bool.main", &[]).unwrap()), true);
}

#[test]
fn m3_int_neg_abs() {
    let src = r#"
namespace test.m3_neg_abs
  import anthill.prelude.Int.{neg, abs}
  operation main() -> Int = abs(neg(42))
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_neg_abs.main", &[]).unwrap()), 42);
}

#[test]
fn m3_int_mod() {
    let src = r#"
namespace test.m3_mod
  import anthill.prelude.Int.{mod}
  operation main() -> Int = mod(17, 5)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_mod.main", &[]).unwrap()), 2);
}

#[test]
fn m3_eq_on_ints() {
    let src = r#"
namespace test.m3_eq
  operation main() -> Bool = 3 = 3
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_bool(interp.call("test.m3_eq.main", &[]).unwrap()), true);
}

#[test]
fn m3_non_tail_recursion_accumulates_frames() {
    // Non-tail recursion: `sumUntil(n-1) + 1` wraps the recursive call in
    // `add _ 1`, so each level leaves an ApplyArgs-waiting frame on the
    // stack. TCO eliminates the intermediate dispatch frames but not the
    // pending-add frames — expected O(n) stack, same as any CEK machine.
    //
    // With cap=16 and n=100, the stack should overflow. With cap=200,
    // same program succeeds and returns n.
    let src = r#"
namespace test.m3_nontail
  import anthill.prelude.Ordered.{gt}
  operation sumUntil(n: Int) -> Int =
    if gt(n, 0) then sumUntil(n - 1) + 1 else 0
  operation main(n: Int) -> Int = sumUntil(n)
end
"#;

    // Small cap trips the DepthExceeded: non-tail recursion genuinely
    // needs ~n frames.
    let mut interp = crate::common::interp_for(src);
    interp.set_stack_depth_cap(16);
    let err = interp.call("test.m3_nontail.main", &[Value::Int(100)]).unwrap_err();
    assert!(
        matches!(err, anthill_core::eval::EvalError::DepthExceeded { .. }),
        "expected DepthExceeded with tight cap; got {err:?}",
    );

    // With a generous cap the same program runs — confirming the limit is
    // memory, not a fundamental runtime flaw.
    let mut interp = crate::common::interp_for(src);
    interp.set_stack_depth_cap(1000);
    let result = interp.call("test.m3_nontail.main", &[Value::Int(100)]).expect("call main");
    assert_eq!(expect_int(result), 100);
}

#[test]
fn m3_int_division() {
    // `/` desugars to `div`. Int import brings `Int.div` into scope as a
    // truncated integer division. Verifies `7 / 2 == 3` (truncation).
    let src = r#"
namespace test.m3_div
  import anthill.prelude.Int.{div}
  operation main() -> Int = 7 / 2
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_div.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 3);
}

#[test]
fn m3_int_division_by_zero() {
    let src = r#"
namespace test.m3_div0
  import anthill.prelude.Int.{div}
  operation main() -> Int = 10 / 0
end
"#;
    let mut interp = interp_for(src);
    let err = interp.call("test.m3_div0.main", &[]).unwrap_err();
    assert!(
        matches!(err, anthill_core::eval::EvalError::DivisionByZero { .. }),
        "expected DivisionByZero, got {err:?}",
    );
}

#[test]
fn m3_float_arithmetic() {
    // `Numeric.add/sub/mul` dispatch on arg variants: Float/Float → Float.
    let src = r#"
namespace test.m3_float_arith
  operation main() -> Float = 1.5 + 2.25 * 2.0
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_arith.main", &[]).expect("call main");
    let got = expect_float(result);
    assert!((got - 6.0).abs() < 1e-9, "expected ~6.0, got {got}");
}

#[test]
fn m3_float_division() {
    let src = r#"
namespace test.m3_float_div
  import anthill.prelude.Float.{div}
  operation main() -> Float = 10.0 / 4.0
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_div.main", &[]).expect("call main");
    assert!((expect_float(result) - 2.5).abs() < 1e-9);
}

#[test]
fn m3_float_nan_detection() {
    // IEEE: `0.0 / 0.0 = NaN`, and `NaN != NaN` — so users detect NaN
    // via `isNaN`, not equality. `1.0 / 0.0 = +Infinity`, detected via
    // `isInfinite`. `isFinite` is true only for real-number values.
    let src = r#"
namespace test.m3_float_nan
  import anthill.prelude.Float.{div, isNaN, isInfinite, isFinite}

  operation nan_of_zero_over_zero() -> Bool = isNaN(0.0 / 0.0)
  operation inf_of_one_over_zero() -> Bool = isInfinite(1.0 / 0.0)
  operation finite_of_sum() -> Bool = isFinite(1.5 + 2.25)
  operation main() -> Bool =
    and(and(nan_of_zero_over_zero(), inf_of_one_over_zero()), finite_of_sum())
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_nan.main", &[]).expect("call main");
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn m3_float_division_by_zero_is_infinity() {
    // Float.div is IEEE-total: 1.0 / 0.0 = +Infinity, not an error. This
    // is the reason Float doesn't need the Error[DivisionByZero] effect
    // that Int.div carries.
    let src = r#"
namespace test.m3_float_div0
  import anthill.prelude.Float.{div}
  operation main() -> Float = 1.0 / 0.0
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_div0.main", &[]).expect("call main");
    assert!(expect_float(result).is_infinite(), "expected infinity");
}

#[test]
fn m3_float_addition_loses_precision_at_scale() {
    // IEEE 754 f64 has 52 mantissa bits plus the implicit leading one, so
    // numbers past ~2^53 can't represent `+1` as a distinct value. Here
    // 1e20 + 1.0 == 1e20 — the `+1` is rounded away. The grammar's
    // float_literal regex `/-?[0-9]+\.[0-9]+/` has no scientific notation,
    // so the constant is written out in full.
    let src = r#"
namespace test.m3_float_precision
  operation main() -> Bool =
    let x = 100000000000000000000.0
    x + 1.0 = x
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_precision.main", &[]).expect("call main");
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn m3_bigint_arithmetic() {
    // BigInt literals parse as `Literal::BigInt` (when they exceed i64);
    // the evaluator unboxes them into `Value::BigInt`. Arithmetic uses
    // num_bigint — no overflow, arbitrary precision.
    let src = r#"
namespace test.m3_bigint
  import anthill.prelude.{BigInt}
  operation main() -> BigInt =
    100000000000000000000 + 100000000000000000000
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_bigint.main", &[]).expect("call main");
    match result {
        Value::BigInt(n) => {
            assert_eq!(n.to_string(), "200000000000000000000");
        }
        other => panic!("expected BigInt, got {other:?}"),
    }
}

#[test]
fn m3_bigint_comparison() {
    let src = r#"
namespace test.m3_bigint_cmp
  import anthill.prelude.{BigInt}
  import anthill.prelude.Ordered.{gt}
  operation main() -> Bool =
    gt(200000000000000000000, 100000000000000000000)
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_bigint_cmp.main", &[]).expect("call main");
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn m3_bigint_to_int_fits() {
    // Value that fits in i64 round-trips via to_int → Option.some.
    let src = r#"
namespace test.m3_bigint_to_int
  import anthill.prelude.{BigInt, Option, Int}
  import anthill.prelude.BigInt.{to_bigint, to_int}

  operation main() -> Int =
    match to_int(to_bigint(42))
      case some(x) -> x
      case none() -> 0
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_bigint_to_int.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 42);
}

#[test]
fn m3_int_to_float_and_bigint_to_float() {
    // Int.to_float is exact for small values; BigInt.to_float rounds to
    // nearest representable double. 1e20 fits in Float as 1.0e20.
    let src = r#"
namespace test.m3_bigint_to_float
  import anthill.prelude.BigInt.{to_float, to_bigint}

  operation main() -> Float =
    to_float(to_bigint(42)) + to_float(100000000000000000000)
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_bigint_to_float.main", &[]).expect("call main");
    // 42 + 1e20 ≈ 1e20 (the 42 is below mantissa precision); match floats
    // are approximate — assert it's at least 1e20 in magnitude.
    let f = expect_float(result);
    assert!(f >= 1.0e20, "expected ≥ 1e20, got {f}");
}

#[test]
fn m3_int_add_overflow_errors() {
    // Int arithmetic is exact — unlike Float, there's no large x where
    // x + 1 == x. Instead, the interesting edge case is overflow: i64::MAX
    // + 1 can't fit. We use checked_add, so this surfaces as
    // EvalError::Overflow rather than silently wrapping to i64::MIN. The
    // test drives via a Rust-side arg rather than a source literal, since
    // the Int literal grammar handles signed i64 but we want to be exact
    // about the boundary.
    let src = r#"
namespace test.m3_int_overflow
  operation inc(n: Int) -> Int = n + 1
  operation main() -> Int = inc(9223372036854775807)
end
"#;
    let mut interp = interp_for(src);
    let err = interp.call("test.m3_int_overflow.main", &[]).unwrap_err();
    match err {
        anthill_core::eval::EvalError::Overflow { op } => assert_eq!(op, "Numeric.add"),
        other => panic!("expected Overflow, got {other:?}"),
    }
}

#[test]
fn m3_float_comparison_and_max() {
    let src = r#"
namespace test.m3_float_cmp
  import anthill.prelude.Ordered.{max}
  operation main() -> Float = max(1.5, 2.75)
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_cmp.main", &[]).expect("call main");
    assert!((expect_float(result) - 2.75).abs() < 1e-9);
}

#[test]
fn m3_operator_precedence() {
    // `x + y * z + w` should parse as `(x + (y * z)) + w`. For x=1 y=2 z=3 w=4
    // the correct value is 1 + 6 + 4 = 11. Incorrect groupings give: 21
    // ((x+y)*(z+w)), 15 (x+y*(z+w)), 13 ((x+y)*z+w). Any of those would be
    // flagged by this assertion.
    let src = r#"
namespace test.m3_prec
  operation compute(x: Int, y: Int, z: Int, w: Int) -> Int =
    x + y * z + w
  operation main() -> Int = compute(1, 2, 3, 4)
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_prec.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 11);
}

#[test]
fn m3_tco_10000_tail_calls() {
    // Classic tail-recursive countdown. Under TCO, the recursive call
    // replaces the current frame on dispatch, so activation-stack depth
    // stays at 1 regardless of N. With a cap of 16 we can still run 10000
    // iterations; if TCO were broken, push-per-call would overflow at
    // ~depth 16.
    let src = r#"
namespace test.m3_tco
  import anthill.prelude.Ordered.{gt}
  operation loop(n: Int) -> Int =
    if gt(n, 0) then loop(n - 1) else 0
  operation main() -> Int = loop(10000)
end
"#;
    let mut interp = interp_for(src);
    interp.set_stack_depth_cap(16);
    let result = interp.call("test.m3_tco.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 0);
}

#[test]
fn m3_string_concat_and_length() {
    let src = r#"
namespace test.m3_string
  import anthill.prelude.String.{concat, length}
  operation greeting() -> String = concat("hi ", "there")
  operation main() -> Int = length(greeting())
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_string.main", &[]).unwrap()), 8);
}

// ─── from eval_m4_test.rs ───
#[test]
fn m4_empty_stream_yields_none() {
    // StreamSource::Empty — immediate exhaustion. Drives the Rust-side
    // pump directly, confirming the arena + Empty arm.
    let mut interp = interp_for("namespace test.m4_empty end\n");
    let h = interp.alloc_stream(StreamSource::Empty);
    assert!(interp.stream_split_first(&h).unwrap().is_none());
}

#[test]
fn m4_pure_stream_yields_once_then_empty() {
    // StreamSource::Pure(v) — single-shot stream. First pump yields the
    // value; second pump yields none. Confirms in-place mutation of the
    // arena slot from Pure → Empty.
    let mut interp = interp_for("namespace test.m4_pure end\n");
    let payload = Value::Int(42);
    let h = interp.alloc_stream(StreamSource::Pure(Some(payload.clone())));
    let (v, rest) = interp.stream_split_first(&h).unwrap().expect("first pump yields");
    assert_eq!(v.as_int(), Some(42));
    assert!(interp.stream_split_first(&rest).unwrap().is_none(), "second pump yields none");
}

#[test]
fn m4_resolver_stream_iterates_ancestor_query() {
    // Acceptance test. Load a user KB with an `ancestor` relation, build
    // `pattern_query(ancestor(...))` from the Rust side, wrap the resulting
    // `SearchStream` as a `Value::Stream`, then drive it through
    // `splitFirst` from an anthill program.
    let source = r#"
namespace test.m4_ancestor
  import anthill.prelude.{LogicalStream}
  import anthill.prelude.LogicalStream.{splitFirst}
  import anthill.prelude.Pair.{pair}

  sort Person
    entity alice
    entity bob
    entity carol
  end

  sort Family
    entity ancestor(parent: Person, child: Person)
  end
  fact ancestor(parent: alice, child: bob)
  fact ancestor(parent: bob, child: carol)

  operation drain(s: LogicalStream) -> Int =
    match splitFirst(s)
      case some(pair(_, rest)) -> 1 + drain(rest)
      case none() -> 0
end
"#;
    let mut interp = interp_for(source);

    // Build the LogicalQuery from the Rust side. We query
    // `ancestor(parent: ?p, child: bob)` — expect one solution (p=alice).
    // Field names on an entity are scoped to the entity; resolve qualified
    // so the discrim tree sees the same Symbol the loader used.
    let kb = interp.kb_mut();
    let ancestor_sym = kb.try_resolve_symbol("test.m4_ancestor.Family.ancestor")
        .expect("ancestor symbol");
    let bob_sym = kb.try_resolve_symbol("test.m4_ancestor.Person.bob").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
        .expect("pattern_query");
    // The loader's `reintern` path (load.rs:1867) creates unqualified
    // short-name symbols for named-arg keys in a fact head, so the query
    // pattern must use the same short-name Symbol to hash-cons equal
    // to the stored fact. Using the qualified entity-field Symbol (from
    // scan_definitions) gives a *different* Symbol and the discrim tree
    // won't match.
    let parent_field = kb.intern("parent");
    let child_field = kb.intern("child");
    let term_field = kb.intern("term");
    let p_name = kb.intern("p");
    let vid = kb.fresh_var(p_name);
    use anthill_core::kb::term::{Term, Var};
    let var_p = kb.alloc(Term::Var(Var::Global(vid)));
    // Nullary constructors in fact position are stored as `Term::Ref`, not
    // `Term::Fn` with empty args — the loader resolves bare identifiers
    // to Refs when they're known symbols. Match that shape so the discrim
    // tree sees a structural match.
    let bob_term = kb.alloc(Term::Ref(bob_sym));

    // pattern_query( ancestor(parent: ?p, child: bob) )
    let ancestor_pattern = Value::Entity {
        functor: ancestor_sym,
        pos: Vec::new().into(),
        named: vec![
            (parent_field, Value::Term(var_p)),
            (child_field, Value::Term(bob_term)),
        ].into(),
    };
    let query = Value::Entity {
        functor: pattern_query_sym,
        pos: Vec::new().into(),
        named: vec![(term_field, ancestor_pattern)].into(),
    };

    // Lower + wrap as a Value::Stream on the Rust side (since we can't
    // construct a `KB` value from anthill code cleanly yet).
    let search = interp.kb_mut().execute_logical_query(&query).expect("execute lowered");
    let stream_handle = interp.alloc_stream(StreamSource::Resolver(Some(search)));
    let stream_val = Value::Stream(stream_handle);

    let count = interp.call("test.m4_ancestor.drain", &[stream_val])
        .expect("drain runs end-to-end");
    assert_eq!(count.as_int(), Some(1), "drain count for single-match query");
}

#[test]
fn m4_resolver_stream_iterates_multiple_solutions() {
    // Same as the single-solution test but the query has an unbound
    // `child`, so both facts match — we expect 2 yields before none.
    let source = r#"
namespace test.m4_multi
  import anthill.prelude.{LogicalStream}
  import anthill.prelude.LogicalStream.{splitFirst}
  import anthill.prelude.Pair.{pair}

  sort Person
    entity alice
    entity bob
    entity carol
  end

  sort Family
    entity ancestor(parent: Person, child: Person)
  end
  fact ancestor(parent: alice, child: bob)
  fact ancestor(parent: bob, child: carol)

  operation drain(s: LogicalStream) -> Int =
    match splitFirst(s)
      case some(pair(_, rest)) -> 1 + drain(rest)
      case none() -> 0
end
"#;
    let mut interp = interp_for(source);

    let kb = interp.kb_mut();
    let ancestor_sym = kb.try_resolve_symbol("test.m4_multi.Family.ancestor").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let parent_field = kb.intern("parent");
    let child_field = kb.intern("child");
    let term_field = kb.intern("term");
    let p = kb.intern("p");
    let c = kb.intern("c");
    let vp = kb.fresh_var(p);
    let vc = kb.fresh_var(c);
    use anthill_core::kb::term::{Term, Var};
    let var_p = kb.alloc(Term::Var(Var::Global(vp)));
    let var_c = kb.alloc(Term::Var(Var::Global(vc)));

    let ancestor_pattern = Value::Entity {
        functor: ancestor_sym,
        pos: Vec::new().into(),
        named: vec![
            (parent_field, Value::Term(var_p)),
            (child_field, Value::Term(var_c)),
        ].into(),
    };
    let query = Value::Entity {
        functor: pattern_query_sym,
        pos: Vec::new().into(),
        named: vec![(term_field, ancestor_pattern)].into(),
    };

    let search = interp.kb_mut().execute_logical_query(&query).expect("execute lowered");
    let stream_handle = interp.alloc_stream(StreamSource::Resolver(Some(search)));
    let stream_val = Value::Stream(stream_handle);

    let count = interp.call("test.m4_multi.drain", &[stream_val])
        .expect("drain runs");
    // A fully-unbound query matches both user facts plus the synthetic
    // per-entity "declaration fact" the loader asserts from
    // `entity ancestor(parent: Person, child: Person)` (load.rs:2950,
    // asserted with sort=Entity, functor=ancestor). We count structural
    // matches regardless of sort, hence 3 rather than 2. The single-
    // match test pins `child: bob` and avoids this by excluding the
    // declaration fact.
    assert_eq!(count.as_int(), Some(3), "drain count for fully-unbound query");
}

#[test]
fn m4_take_n_on_infinite_native_stream() {
    // Infinite producer (Native closure emits 1, 2, 3, …) paired with a
    // bounded consumer. Confirms:
    //   - splitFirst is pulled exactly N times (the closure's counter
    //     reports its final value),
    //   - takeN returns N on early termination,
    //   - the arena slot is reclaimed when the stream handle drops, even
    //     though the underlying producer could have kept emitting.
    let src = r#"
namespace test.m4_take
  import anthill.prelude.{LogicalStream}
  import anthill.prelude.LogicalStream.{splitFirst}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.Ordered.{gt}

  operation takeN(s: LogicalStream, n: Int) -> Int =
    if gt(n, 0) then
      match splitFirst(s)
        case some(pair(_, rest)) -> 1 + takeN(rest, n - 1)
        case none() -> 0
    else 0
end
"#;
    let mut interp = interp_for(src);

    // Counter captured by-move into the producer closure. Each pump bumps
    // the counter and yields it — unbounded source, no None return path.
    let pulls = std::rc::Rc::new(std::cell::Cell::new(0i64));
    let pulls_for_closure = pulls.clone();
    let producer = Box::new(move || {
        let n = pulls_for_closure.get() + 1;
        pulls_for_closure.set(n);
        Some(Value::Int(n))
    });
    let handle = interp.alloc_stream(StreamSource::Native(producer));
    assert_eq!(interp.stream_arena_live_count(), 1);

    let count = interp.call("test.m4_take.takeN", &[
        Value::Stream(handle),
        Value::Int(5),
    ]).expect("takeN runs");
    assert_eq!(count.as_int(), Some(5), "takeN returns 5");

    // Producer was pumped exactly 5 times — confirms laziness: we didn't
    // drain ahead of the consumer.
    assert_eq!(pulls.get(), 5, "producer was pulled once per solution");

    // The handle we passed into takeN was moved — takeN's locals dropped
    // on return. Arena slot must be reclaimed.
    assert_eq!(interp.stream_arena_live_count(), 0, "slot reclaimed after early termination");
}

#[test]
fn m4_mplus_finite_then_infinite() {
    // MPlus{finite, infinite}: the consumer first sees everything the
    // finite (left) side produces, then transitions to the infinite
    // (right) side. Pumping N > |finite| values confirms:
    //   - Ordering: left drains before right — left's element comes first.
    //   - Right is not pulled until left exhausts — infinite's counter
    //     shows only (N - |finite|) pulls.
    //   - After left exhausts, the continuation handle points at right
    //     directly (the MPlus wrapper is collapsed), so pulling more
    //     from that handle doesn't re-traverse the exhausted left.
    let mut interp = interp_for("namespace test.m4_mplus end\n");

    let left = interp.alloc_stream(StreamSource::Pure(Some(Value::Int(99))));

    let pulls = std::rc::Rc::new(std::cell::Cell::new(0i64));
    let pulls_for_closure = pulls.clone();
    let producer = Box::new(move || {
        let n = pulls_for_closure.get() + 1;
        pulls_for_closure.set(n);
        Some(Value::Int(n))
    });
    let right = interp.alloc_stream(StreamSource::Native(producer));

    let mut stream = interp.alloc_stream(StreamSource::MPlus { left, right });
    assert_eq!(interp.stream_arena_live_count(), 3);

    let mut values = Vec::new();
    for _ in 0..4 {
        let (v, rest) = interp.stream_split_first(&stream).unwrap().expect("more");
        values.push(v);
        stream = rest;
    }

    let ints: Vec<i64> = values.iter().filter_map(|v| v.as_int()).collect();
    assert_eq!(ints, vec![99, 1, 2, 3], "left drains before right, in order");
    assert_eq!(pulls.get(), 3, "infinite was pulled exactly (N - |finite|) times");

    drop(stream);
    assert_eq!(interp.stream_arena_live_count(), 0, "all arena slots reclaimed");
}

#[test]
fn m4_mplus_finite_then_empty() {
    // MPlus{finite, empty}: consumer sees the left side's elements and
    // then `none` — the right-empty arm must terminate cleanly rather
    // than looping forever or producing a spurious extra yield.
    let mut interp = interp_for("namespace test.m4_mplus_fe end\n");
    let left = interp.alloc_stream(StreamSource::Pure(Some(Value::Int(42))));
    let right = interp.alloc_stream(StreamSource::Empty);
    let stream = interp.alloc_stream(StreamSource::MPlus { left, right });

    let (v, rest) = interp.stream_split_first(&stream).unwrap().expect("first yields");
    assert_eq!(v.as_int(), Some(42));
    assert!(interp.stream_split_first(&rest).unwrap().is_none(), "then exhausted");

    drop(rest);
    drop(stream);
    assert_eq!(interp.stream_arena_live_count(), 0);
}

#[test]
fn m4_mplus_empty_then_finite() {
    // MPlus{empty, finite}: left yields none on the first pump, so the
    // resolver recurses into right immediately. The continuation handle
    // the caller gets back points at `right` directly — the MPlus
    // wrapper is effectively collapsed after left exhausts.
    let mut interp = interp_for("namespace test.m4_mplus_ef end\n");
    let left = interp.alloc_stream(StreamSource::Empty);
    let right = interp.alloc_stream(StreamSource::Pure(Some(Value::Int(7))));
    let stream = interp.alloc_stream(StreamSource::MPlus { left, right });

    let (v, rest) = interp.stream_split_first(&stream).unwrap().expect("first yields");
    assert_eq!(v.as_int(), Some(7), "right's element surfaces when left is empty");
    assert!(interp.stream_split_first(&rest).unwrap().is_none());

    drop(rest);
    drop(stream);
    assert_eq!(interp.stream_arena_live_count(), 0);
}

#[test]
fn m4_stream_handle_reclaimed_after_exhaustion() {
    // Pump a Pure stream to exhaustion, drop all handles — the arena slot
    // must be reclaimed. Confirms refcount + Drop cascade.
    let mut interp = interp_for("namespace test.m4_rc end\n");
    let h = interp.alloc_stream(StreamSource::Pure(Some(Value::Int(1))));
    assert_eq!(interp.stream_arena_live_count(), 1);
    let _ = interp.stream_split_first(&h).unwrap();
    let _ = interp.stream_split_first(&h).unwrap();
    drop(h);
    assert_eq!(interp.stream_arena_live_count(), 0, "slot reclaimed");
}

// ─── from eval_m5_test.rs ───
#[test]
fn m5_println_captured_to_buffer() {
    let src = r#"
namespace test.m5_print
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, print, println, ConsoleOutput}

  operation greet(c: Console) -> Unit effects ConsoleOutput =
    println(c, "hello")
end
"#;
    let mut interp = interp_for(src);
    let (buf, handler) = buffered_console();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", handler)
        .expect("register output handler");

    // Pass the Console entity as the argument.
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console")
        .expect("Console.console symbol");
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new().into(), named: Vec::new().into() };

    interp.call("test.m5_print.greet", &[console_val]).expect("greet runs");
    assert_eq!(buf.borrow().as_str(), "hello\n");
}

#[test]
fn m5_print_no_newline() {
    let src = r#"
namespace test.m5_print2
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, print, ConsoleOutput}

  operation speak(c: Console) -> Unit effects ConsoleOutput = print(c, "hi")
end
"#;
    let mut interp = interp_for(src);
    let (buf, handler) = buffered_console();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", handler).unwrap();
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new().into(), named: Vec::new().into() };
    interp.call("test.m5_print2.speak", &[console_val]).expect("speak runs");
    assert_eq!(buf.borrow().as_str(), "hi");
}

#[test]
fn m5_eprintln_goes_only_to_stderr_buffer() {
    let src = r#"
namespace test.m5_eprint
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, println, eprintln, ConsoleOutput, ConsoleError}

  operation diag(c: Console) -> Unit effects {ConsoleError, ConsoleOutput} =
    let _ = eprintln(c, "oops")
    println(c, "ok")
end
"#;
    let mut interp = interp_for(src);
    let (out_buf, out_handler) = buffered_console();
    let (err_buf, err_handler) = buffered_console();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", out_handler).unwrap();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleError", err_handler).unwrap();
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new().into(), named: Vec::new().into() };
    interp.call("test.m5_eprint.diag", &[console_val]).expect("diag runs");
    assert_eq!(out_buf.borrow().as_str(), "ok\n");
    assert_eq!(err_buf.borrow().as_str(), "oops\n");
}

#[test]
fn m5_read_line_returns_scripted_input() {
    let src = r#"
namespace test.m5_read
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, read_line, ConsoleInput}

  operation ask(c: Console) -> String effects ConsoleInput = read_line(c)
end
"#;
    let mut interp = interp_for(src);
    let (queue, handler) = scripted_console_input(&["ruslan", "ignored_second_line"]);
    interp.register_effect_handler("anthill.prelude.Console.ConsoleInput", handler).unwrap();
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new().into(), named: Vec::new().into() };

    let got = interp.call("test.m5_read.ask", &[console_val]).expect("ask runs");
    assert_eq!(got.as_str(), Some("ruslan"));
    // One line remains in the queue — the second scripted line.
    assert_eq!(queue.borrow().len(), 1);
}

#[test]
fn m5_read_then_print_roundtrip() {
    let src = r#"
namespace test.m5_round
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, println, read_line, ConsoleInput, ConsoleOutput}

  operation echo(c: Console) -> Unit effects {ConsoleInput, ConsoleOutput} =
    let line = read_line(c)
    println(c, line)
end
"#;
    let mut interp = interp_for(src);
    let (buf, out_h) = buffered_console();
    let (_q, in_h) = scripted_console_input(&["alice"]);
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", out_h).unwrap();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleInput", in_h).unwrap();
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new().into(), named: Vec::new().into() };
    interp.call("test.m5_round.echo", &[console_val]).expect("echo runs");
    assert_eq!(buf.borrow().as_str(), "alice\n");
}

#[test]
fn m5_unhandled_effect_errors_cleanly() {
    // No handler registered -> invoking Console.print should surface a
    // clean Internal error, not panic. This is the fallback if a user
    // forgets to register a handler (or registered only one side).
    let src = r#"
namespace test.m5_unhandled
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, println, ConsoleOutput}

  operation speak(c: Console) -> Unit effects ConsoleOutput = println(c, "x")
end
"#;
    let mut interp = interp_for(src);
    // Deliberately no register_effect_handler call.
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new().into(), named: Vec::new().into() };
    let err = interp.call("test.m5_unhandled.speak", &[console_val]).unwrap_err();
    assert!(
        matches!(&err, anthill_core::eval::EvalError::Internal(msg)
            if msg.contains("no handler") && msg.contains("ConsoleOutput")),
        "expected 'no handler' for ConsoleOutput, got {err:?}",
    );
}

#[test]
fn m5_handler_replacement_works_mid_run() {
    // Register a handler, run, swap it, run again — verifies the
    // take/register round-trip actually replaces and doesn't just
    // stack underneath.
    let src = r#"
namespace test.m5_swap
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, println, ConsoleOutput}

  operation speak(c: Console, s: String) -> Unit effects ConsoleOutput = println(c, s)
end
"#;
    let mut interp = interp_for(src);
    let (buf1, h1) = buffered_console();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", h1).unwrap();
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new().into(), named: Vec::new().into() };
    interp.call("test.m5_swap.speak", &[console_val.clone(), Value::Str("first".into())]).unwrap();
    assert_eq!(buf1.borrow().as_str(), "first\n");

    let (buf2, h2) = buffered_console();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", h2).unwrap();
    interp.call("test.m5_swap.speak", &[console_val, Value::Str("second".into())]).unwrap();
    assert_eq!(buf2.borrow().as_str(), "second\n", "new handler captured");
    // The original buffer is untouched by the second call.
    assert_eq!(buf1.borrow().as_str(), "first\n", "old buffer unchanged");
}

// ─── from eval_m5_modify_test.rs ───
#[test]
fn m5_modify_counter_write_then_read() {
    let src = r#"
namespace test.m5_counter
  import anthill.prelude.{Int, Unit, Modify}
  import ModifyRuntime.{get, set}

  sort CounterState
    entity counter
  end

  operation write(n: Int) -> Unit effects Modify[T = CounterState] = set(counter(), n)
  operation read() -> Int = get(counter())
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    interp.call("test.m5_counter.write", &[Value::Int(42)]).expect("write");
    let got = interp.call("test.m5_counter.read", &[]).expect("read");
    assert_eq!(got.as_int(), Some(42), "read returns last-set value");

    interp.call("test.m5_counter.write", &[Value::Int(7)]).expect("overwrite");
    let got = interp.call("test.m5_counter.read", &[]).expect("read again");
    assert_eq!(got.as_int(), Some(7), "subsequent read sees the overwrite");
}

#[test]
fn m5_modify_get_before_set_errors() {
    let src = r#"
namespace test.m5_unset
  import anthill.prelude.{Int}
  import ModifyRuntime.{get}

  sort CounterState
    entity counter
  end

  operation read() -> Int = get(counter())
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    let err = interp.call("test.m5_unset.read", &[]).unwrap_err();
    match err {
        EvalError::Internal(msg) => assert!(msg.contains("no value set"), "got {msg}"),
        other => panic!("expected Internal 'no value set', got {other:?}"),
    }
}

#[test]
fn m5_modify_two_resources_are_independent() {
    // Two distinct resource entities should not share state.
    let src = r#"
namespace test.m5_independent
  import anthill.prelude.{Int, Unit, Modify}
  import ModifyRuntime.{get, set}

  sort Cells
    entity a
    entity b
  end

  operation put_a(n: Int) -> Unit effects Modify[T = Cells] = set(a(), n)
  operation put_b(n: Int) -> Unit effects Modify[T = Cells] = set(b(), n)
  operation get_a() -> Int = get(a())
  operation get_b() -> Int = get(b())
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);
    interp.call("test.m5_independent.put_a", &[Value::Int(1)]).unwrap();
    interp.call("test.m5_independent.put_b", &[Value::Int(99)]).unwrap();
    let a = interp.call("test.m5_independent.get_a", &[]).unwrap();
    let b = interp.call("test.m5_independent.get_b", &[]).unwrap();
    assert_eq!(a.as_int(), Some(1));
    assert_eq!(b.as_int(), Some(99));
}

#[test]
fn m5_modify_self_referential_set_errors_with_cyclic_reference() {
    // `set(counter, counter)` would store the resource-identifier entity
    // as its own value — the simplest self-cycle. The handler's bounded
    // structural walk catches this.
    let src = r#"
namespace test.m5_cycle
  import anthill.prelude.{Unit, Modify}
  import ModifyRuntime.{set}

  sort CycleState
    entity counter
  end

  operation bad() -> Unit effects Modify[T = CycleState] = set(counter(), counter())
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);
    let err = interp.call("test.m5_cycle.bad", &[]).unwrap_err();
    assert!(
        matches!(err, EvalError::CyclicReference),
        "expected CyclicReference, got {err:?}",
    );
}

#[test]
fn m5_modify_rust_side_roundtrip() {
    // Drive Modify directly through the handler from Rust — no anthill
    // program involved. Confirms the arena is usable by host-side code
    // (e.g. for seeding initial state before an anthill entry point).
    let mut interp = interp_for("namespace test.m5_rs end\n");
    register_modify_handler(&mut interp);

    // Minimal Entity-shaped target: a nullary constructor the anthill
    // side hasn't declared. We intern the symbol directly.
    let target_sym = interp.kb_mut().intern("rs_counter");
    let target = Value::Entity { functor: target_sym, pos: Vec::new().into(), named: Vec::new().into() };

    let set_sym = interp.kb_mut().intern("set");
    interp.invoke_effect_handler("anthill.prelude.Modify", set_sym, &[target.clone(), Value::Int(100)])
        .expect("set ok");
    let get_sym = interp.kb_mut().intern("get");
    let got = interp.invoke_effect_handler("anthill.prelude.Modify", get_sym, &[target])
        .expect("get ok");
    assert_eq!(got.as_int(), Some(100));
}

#[test]
fn m5_modify_handler_taken_is_none() {
    // take_effect_handler pulls the handler out; subsequent invoke should
    // surface a clean "no handler" error rather than panicking.
    let mut interp = interp_for("namespace test.m5_take end\n");
    register_modify_handler(&mut interp);
    let taken = interp.take_effect_handler("anthill.prelude.Modify");
    assert!(taken.is_some(), "take returns the previously-registered handler");

    let target_sym = interp.kb_mut().intern("x");
    let target = Value::Entity { functor: target_sym, pos: Vec::new().into(), named: Vec::new().into() };
    let get_sym = interp.kb_mut().intern("get");
    let err = interp.invoke_effect_handler("anthill.prelude.Modify", get_sym, &[target]).unwrap_err();
    assert!(
        matches!(&err, EvalError::Internal(m) if m.contains("no handler")),
        "expected 'no handler' Internal, got {err:?}",
    );
}

#[test]
fn wi389_throw_action_surfaces_as_raised() {
    // WI-389: a handler returning HandlerAction::Throw(payload) is
    // interpreted at the dispatch site as EvalError::Raised carrying the
    // same payload — the substrate WI-073's Error handler builds on.
    // Error-ness lives in the channel (the Throw variant), not in the
    // value: the payload is an ordinary opaque Value, preserved verbatim.
    use anthill_core::eval::effects::HandlerAction;
    let mut interp = interp_for("namespace test.wi389 end\n");

    let payload = Value::Str("boom".into());
    let payload_for_handler = payload.clone();
    interp.register_effect_handler(
        "anthill.prelude.Modify",
        Box::new(move |_interp, _op_sym, _args| {
            Ok(HandlerAction::Throw(payload_for_handler.clone()))
        }),
    ).expect("register throwing handler");

    let op_sym = interp.kb_mut().intern("raise");
    let err = interp
        .invoke_effect_handler("anthill.prelude.Modify", op_sym, &[])
        .unwrap_err();
    match err {
        EvalError::Raised { payload: got } => {
            assert_eq!(got.as_str(), Some("boom"), "payload preserved through the channel");
        }
        other => panic!("expected EvalError::Raised, got {other:?}"),
    }
}

#[test]
fn wi389_fail_action_surfaces_its_reason() {
    // WI-389: Fail carries a reason (the "why" of the branch abort). Until
    // the Branch substrate (WI-075) wires the real resolver-fail path, a
    // Fail reaching the dispatch site surfaces as a loud, structured
    // UnsupportedHandlerAction whose rendered message includes that reason.
    use anthill_core::eval::effects::HandlerAction;
    let mut interp = interp_for("namespace test.wi389_fail end\n");
    interp.register_effect_handler(
        "anthill.prelude.Modify",
        Box::new(|_interp, _op_sym, _args| {
            Ok(HandlerAction::Fail(Value::Str("no candidate matched".into())))
        }),
    ).expect("register failing handler");

    let op_sym = interp.kb_mut().intern("fail");
    let err = interp
        .invoke_effect_handler("anthill.prelude.Modify", op_sym, &[])
        .unwrap_err();
    match &err {
        EvalError::UnsupportedHandlerAction { action, detail, .. } => {
            assert_eq!(*action, "Fail");
            assert!(
                detail.as_deref().unwrap_or("").contains("no candidate matched"),
                "the Fail reason should be carried, got {detail:?}",
            );
        }
        other => panic!("expected UnsupportedHandlerAction, got {other:?}"),
    }
    // The rendered message says both the reason and which substrate is missing.
    let rendered = err.to_string();
    assert!(rendered.contains("no candidate matched"), "rendered: {rendered}");
    assert!(rendered.contains("WI-075"), "rendered: {rendered}");
}

#[test]
fn wi073_raise_surfaces_as_raised_with_payload() {
    // WI-073 (end-to-end): invoking the Error.raise operation routes through
    // the error_raise builtin to the default Error handler (installed by
    // register_standard_effect_handlers), which Throws the payload; the
    // dispatch site surfaces it as EvalError::Raised carrying that payload
    // verbatim. Chain: raise -> builtin -> Error handler -> Throw -> Raised.
    let mut interp = interp_for("namespace test.wi073 end\n");
    interp.register_standard_effect_handlers().expect("register standard effect handlers");

    let err = interp
        .call("anthill.prelude.Error.raise", &[Value::Str("kaboom".into())])
        .unwrap_err();
    match err {
        EvalError::Raised { payload } => {
            assert_eq!(payload.as_str(), Some("kaboom"), "payload preserved verbatim");
        }
        other => panic!("expected EvalError::Raised, got {other:?}"),
    }
}

#[test]
fn wi350_eval_resolves_abstract_spec_op_from_value_runtime_sort() {
    // WI-350 (eval leg): a body-less spec op (`Box.peek` — a self-receiver
    // spec, `peek(b: Box)`) called on a concrete value resolves the impl
    // from the value's OWN runtime sort. The typer leaves abstract-receiver
    // spec-op calls un-rewritten (the concrete impl is the value's concern,
    // not pinnable statically); the interpreter must then resolve
    // `Box.peek(lbox(7))` to `ListBox.peek` via the receiver value's functor
    // → parent sort → sort-ops table. Without the leg, dispatch raises
    // `UnknownOperation` on the body-less `Box.peek`.
    let src = r#"
namespace test.wi350_box
  sort Box
    sort T = ?
    operation peek(b: Box) -> Int
  end
  sort ListBox
    entity lbox(item: Int)
    fact Box[T = Int]
    operation peek(b: ListBox) -> Int = match b case lbox(x) -> x
  end
  -- `b : Box` is an abstract spec value, so `Box.peek(b)` types through the
  -- interface and stays `Box.peek` (no static impl pinned). At runtime `b`
  -- is the concrete ListBox the caller threads in.
  operation use_box(b: Box) -> Int = Box.peek(b)
  operation main() -> Int = use_box(lbox(7))
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.wi350_box.main", &[])
        .expect("in-body Box.peek on a ListBox value resolves via the value's runtime sort");
    assert_eq!(expect_int(result), 7);
}

#[test]
fn wi343_list_splitfirst_is_a_functional_stream_primitive() {
    // proposal library/002: List provides Stream, with `splitFirst` as the
    // primitive (not a hollow `fact Stream[T]`). `splitFirst(aList)` must
    // dispatch to List's impl (concrete carrier, WI-350) and decompose a
    // non-empty list to `some(pair(head, tail))`, so a List genuinely acts as
    // a Stream at runtime. (The element type does not thread through the
    // destructured `Pair` at the type level yet — a separate typer-inference
    // limitation — so this asserts the runtime `some(...)` decomposition
    // rather than extracting a typed element.)
    let src = r#"
namespace test.wi343_list_stream
  import anthill.prelude.{List, Bool}
  import anthill.prelude.List.{splitFirst}
  import anthill.prelude.Option.{some, none}

  operation nonempty_via_splitfirst() -> Bool =
    match splitFirst([1, 2])
      case some(_) -> true
      case none() -> false
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let nonempty = interp.call("test.wi343_list_stream.nonempty_via_splitfirst", &[])
        .expect("splitFirst on a non-empty List must dispatch to List's Stream impl");
    assert_eq!(expect_bool(nonempty), true, "splitFirst([1,2]) must be some(...)");
}

/// WI-365 / WI-362 trip-wire. `collect` is a `Stream` spec op whose DEFAULT BODY
/// (over the primitive `splitFirst`) now typechecks on the abstract `Stream`
/// sort. Consuming a `List` as a `Stream`, `collect([1,2,3])` dispatches to that
/// default body; its inner `splitFirst` resolves to `List`'s impl, peeling the
/// list element by element back into a `List`. `length` of the result is 3 —
/// proving the default body is both typecheckable (WI-365) and executable end to
/// end (WI-362).
#[test]
fn wi362_collect_over_list_when_typer_grounds_effect_and_element() {
    let src = r#"
namespace test.wi362_collect
  import anthill.prelude.{List, Int}
  import anthill.prelude.List.{length}
  import anthill.prelude.Stream.{collect}

  operation collect_len() -> Int = length(collect([1, 2, 3]))
end
"#;
    // `interp_for` registers the standard eval builtins (`length`'s `add`,
    // etc.); the bare `Interpreter::new` would leave them unregistered.
    let mut interp = interp_for(src);
    let len = interp.call("test.wi362_collect.collect_len", &[])
        .expect("collect over a List, dispatched through Stream's default body, must run");
    assert_eq!(expect_int(len), 3, "collect([1,2,3]) then length must be 3");
}

/// `takeN` default body, executed end to end: `takeN([1,2,3,4,5], 2)` peels two
/// elements via `splitFirst`, short-circuiting at `n = 0` through the lazy `if`.
#[test]
fn wi362_take_n_over_list_executes() {
    let src = r#"
namespace test.wi362_taken
  import anthill.prelude.{List, Int}
  import anthill.prelude.List.{length}
  import anthill.prelude.Stream.{takeN}

  operation taken_len() -> Int = length(takeN([1, 2, 3, 4, 5], 2))
end
"#;
    // `interp_for` registers the standard eval builtins (`gt`/`sub` in takeN,
    // `add` in length); the bare `Interpreter::new` would leave them unregistered.
    let mut interp = interp_for(src);
    let len = interp.call("test.wi362_taken.taken_len", &[])
        .expect("takeN over a List, dispatched through Stream's default body, must run");
    assert_eq!(expect_int(len), 2, "takeN([1,2,3,4,5], 2) then length must be 2");
}

/// WI-362 Part 1: `Stream` provides `Iterable` (`iterator(s) = s`, proposal
/// library/002 "Relationship to Stream"). Asserts the provider fact
/// `SortProvidesInfo(sort_ref: Stream, spec: SortView(Iterable, …))` is
/// registered, so a value typed as a `Stream` is admissible wherever an
/// `Iterable` is required (the shared read interface). Loading the stdlib at all
/// already proves `stream.anthill` (incl. the `stream`↔`iterable` cyclic import
/// and `iterator(s: Stream) -> Stream = s`) typechecks; this pins the provision
/// itself rather than just clean load.
#[test]
fn wi362_stream_provides_iterable() {
    use anthill_core::kb::term::Term;
    let interp = interp_for("namespace test.wi362_iter\nend\n");
    let kb = interp.kb();
    let provides = kb
        .try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .expect("SortProvidesInfo sort must exist");
    // Functor qualified name of a name term (`Fn` / `Ref` / `Ident`).
    let functor_qn = |t| match kb.get_term(t) {
        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
            Some(kb.qualified_name_of(*functor).to_string())
        }
        _ => None,
    };
    let found = kb.rules_by_functor(provides).into_iter().any(|rid| {
        if !kb.is_fact(rid) {
            return false;
        }
        let Some(named) = kb.fact_head_named_args(rid) else {
            return false;
        };
        let get = |key: &str| {
            named
                .iter()
                .find(|(s, _)| kb.resolve_sym(*s) == key)
                .map(|(_, t)| *t)
        };
        let (Some(sort_ref), Some(spec)) = (get("sort_ref"), get("spec")) else {
            return false;
        };
        // sort_ref base = Stream; spec = SortView(Iterable, …) → first positional
        // arg's functor = Iterable.
        let carrier_is_stream = functor_qn(sort_ref).as_deref() == Some("anthill.prelude.Stream");
        let spec_base = match kb.get_term(spec) {
            Term::Fn { pos_args, .. } => pos_args.first().copied().and_then(functor_qn),
            _ => None,
        };
        carrier_is_stream && spec_base.as_deref() == Some("anthill.prelude.Iterable")
    });
    assert!(
        found,
        "stream.anthill must register `fact Iterable[C = Stream]` \
         (SortProvidesInfo sort_ref=Stream, spec base=Iterable)",
    );
}
