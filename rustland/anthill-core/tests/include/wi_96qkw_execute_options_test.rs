//! WI-20261122-96QKW — THE CALLER SETS THE BUDGET OF `KB.execute`, AND READS WHAT IT COST.
//!
//! `KnowledgeBase::execute_typed_logical_query` ran every search at the default budget (depth
//! 100, 10 000 000 steps), and the `SearchStream` it handed out kept its `ResolveStats` private.
//! A membership relation written over the cons spine opens one clause per element: the query's
//! goal is at depth 0 and the goal on the `k`-th cell at `k - 1`, so over a list of 150 the last
//! element is found at depth 149 and a miss is refuted at 150 — and at the default both end
//! truncated at depth 100. Now:
//!  * Rust: `execute_typed_logical_query_with(q, &ExecuteOptions { max_depth, max_steps })`, and
//!    `SearchStream::next_solution` / `SearchStream::stats` — a pull that keeps the stream, and
//!    its statistics at any point of the pull, after the end too;
//!  * anthill: `KB.execute_with(kb, query, ExecuteOptions(max_depth, max_steps))`, a field that
//!    is `none()` keeping the default, a limit hit raised as `search_truncated` naming the
//!    caller's limit, a limit below 0 refused as `malformed_query`.
//!
//! BACK-OUT, measured 2026-11-22 one part at a time over this file (8 rows, green on the change):
//!  * [O] `execute_config` ignoring `options` (the default budget always) — 4 fail: the two
//!    `at_depth_200_...` rows (both goals cut at 100), `a_program_sets_max_depth` and
//!    `a_small_max_steps_ends_at_the_callers_steps` (depth 100's cut, not the caller's);
//!  * [S] `SearchStream::stats` handing out the counters alone, its truncation fields as
//!    `ResolveStats::default()` leaves them — 1 fails:
//!    `at_the_default_budget_both_goals_are_truncated_at_depth_100` (`truncated` false after
//!    a truncated end);
//!  * [N] `ExecuteOptions::from_limits` taking a negative limit as 0 instead of refusing it —
//!    1 fails: `a_negative_limit_is_a_malformed_query` (the search runs, cut at depth 0).
//! CONTROLS, passing either way by design: `execute_keeps_the_default_budget` (the default is
//! the default) and `a_field_left_none_keeps_the_default` (under [O] the default is all there
//! is). The host bridge's face is `anthill-stl`'s `execute_with_runs_at_the_callers_budget`,
//! which fails with its `execute_at` ignoring the options (measured: cut at depth 100).

use crate::common::interp_for;
use anthill_core::eval::{HostValue, Interpreter, Value};
use anthill_core::kb::execute::ExecuteOptions;
use anthill_core::kb::resolve::{ResolveConfig, SearchFailure, SearchLimit, SearchStream};

const SRC: &str = r#"
namespace test.qkw96
  import anthill.prelude.{Int64, String, Bool, Error, Option, Stream, Result, List}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{Term, Solution, as_term, make_fn, ResolveStreamFailure, ExecuteOptions, LogicalQuery}
  import anthill.reflect.ResolveStreamFailure.{search_truncated, malformed_query}
  import anthill.reflect.SearchLimit.{depth, steps}
  import anthill.reflect.KB.{kb, execute, execute_with}
  import anthill.reflect.LogicalQuery.{pattern_query}

  -- Membership over the cons spine: one clause opened per element, so the goal on the k-th
  -- cell is k - 1 deep (the query's own goal is 0), and a miss in a list of n reaches nil at n.
  fact isIn(?x, cons(head: ?x, tail: ?))
  rule isIn(?x, cons(head: ?, tail: ?t)) :- isIn(?x, ?t)

  -- n, n - 1, …, 1.
  operation down(n: Int64) -> List[T = Int64] =
    if n > 0 then cons(head: n, tail: down(n - 1)) else nil

  -- `isIn(x, [150, …, 1])`: 1 is the last element, 0 is in no position.
  operation membership(x: Int64) -> LogicalQuery =
    pattern_query(term: make_fn("test.qkw96.isIn", [as_term(x), as_term(down(150))]))

  -- 1 where the stream yields an answer, 0 where it ends.
  operation answered(s: Stream[T = Solution, E = Error[ResolveStreamFailure]]) -> Int64
    effects Error[ResolveStreamFailure] =
    match splitFirst(s)
      case none()  -> 0
      case some(_) -> 1

  -- The first pull's outcome: 1 an answer, 0 the end, -1000 - d a cut at depth d,
  -- -1000000 - n a cut at n steps, -7 a refusal.
  operation read(r: Result[E = ResolveStreamFailure, T = Int64]) -> Int64 =
    match r
      case ok(n) -> n
      case err(search_truncated(depth(d))) -> -1000 - d
      case err(search_truncated(steps(n))) -> -1000000 - n
      case err(malformed_query(_)) -> -7
      case err(_) -> -9

  operation withDefault(x: Int64) -> Int64 =
    read(Error.reify(lambda () -> answered(execute(kb(), membership(x)))))
  operation withDepth(x: Int64, d: Int64) -> Int64 =
    read(Error.reify(lambda () -> answered(execute_with(kb(), membership(x), ExecuteOptions(max_depth: some(d), max_steps: none())))))
  operation withSteps(x: Int64, n: Int64) -> Int64 =
    read(Error.reify(lambda () -> answered(execute_with(kb(), membership(x), ExecuteOptions(max_depth: some(200), max_steps: some(n))))))
  operation withNone(x: Int64) -> Int64 =
    read(Error.reify(lambda () -> answered(execute_with(kb(), membership(x), ExecuteOptions(max_depth: none(), max_steps: none())))))
end
"#;

/// The `LogicalQuery` `isIn(x, [150, …, 1])`, built by the fixture.
fn membership(interp: &mut Interpreter, x: i64) -> Value {
    interp
        .call("test.qkw96.membership", &HostValue::all(&[Value::Int(x)]))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`membership({x})` builds the query: {e:?}"))
}

/// `test.qkw96.<op>(args)`, an `Int64`.
fn call_int(interp: &mut Interpreter, op: &str, args: &[Value]) -> i64 {
    match interp.call(&format!("test.qkw96.{op}"), &HostValue::all(args)).map(|h| h.value) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{op}` answers an Int64, got {other:?}"),
    }
}

/// The first pull of `stream`, with the stream kept for its statistics.
fn first_pull(interp: &mut Interpreter, stream: &mut SearchStream) -> Result<Option<bool>, SearchFailure> {
    stream
        .next_solution(interp.kb_mut())
        .map(|sol| sol.map(|s| s.is_definite()))
}

/// At the default budget, the goal that holds (1, the 150th element) and the one that fails (0)
/// are both cut at depth 100, and the stream's statistics say so after the end — the steps it
/// took, and `truncated`.
///
/// FAILS WHEN BACKED OUT [S]: `truncated` is false.
#[test]
fn at_the_default_budget_both_goals_are_truncated_at_depth_100() {
    let mut interp = interp_for(SRC);
    for x in [1, 0] {
        let q = membership(&mut interp, x);
        let mut stream = interp
            .kb_mut()
            .execute_typed_logical_query_with(&q, &ExecuteOptions::default())
            .expect("the query types");
        match first_pull(&mut interp, &mut stream) {
            Err(SearchFailure::Truncated {
                limit: SearchLimit::Depth { max_depth: 100 },
            }) => {}
            other => panic!("isIn({x}, …) at the default budget is cut at depth 100, got {other:?}"),
        }
        let stats = stream.stats();
        assert!(stats.truncated, "isIn({x}, …): the stats report the truncated end");
        assert!(!stats.out_of_fuel, "isIn({x}, …): depth cut it, not fuel");
        assert!(stats.steps > 100, "isIn({x}, …): the steps it took are counted, got {}", stats.steps);
    }
}

/// At depth 200 the goal that holds is answered, definitely, and the stream's statistics read
/// at that answer say nothing was cut before it.
///
/// FAILS WHEN BACKED OUT [O]: the pull is cut at depth 100.
#[test]
fn at_depth_200_the_goal_that_holds_is_answered() {
    let mut interp = interp_for(SRC);
    let q = membership(&mut interp, 1);
    let options = ExecuteOptions {
        max_depth: 200,
        ..ExecuteOptions::default()
    };
    let mut stream = interp
        .kb_mut()
        .execute_typed_logical_query_with(&q, &options)
        .expect("the query types");
    match first_pull(&mut interp, &mut stream) {
        Ok(Some(true)) => {}
        other => panic!("isIn(1, [150, …, 1]) holds at depth 200, got {other:?}"),
    }
    let at_answer = stream.stats();
    assert!(!at_answer.truncated, "nothing was cut before the answer");
    assert!(at_answer.steps >= 150, "the answer took a step per element, got {}", at_answer.steps);
    match first_pull(&mut interp, &mut stream) {
        Ok(None) => {}
        other => panic!("one proof, and then a complete end; got {other:?}"),
    }
    assert!(!stream.stats().truncated, "the end is complete");
}

/// At depth 200 the goal that fails ends — a complete end, a refutation — and the statistics
/// say it was not truncated.
///
/// FAILS WHEN BACKED OUT [O]: the pull is cut at depth 100.
#[test]
fn at_depth_200_the_goal_that_fails_is_refuted() {
    let mut interp = interp_for(SRC);
    let q = membership(&mut interp, 0);
    let options = ExecuteOptions {
        max_depth: 200,
        ..ExecuteOptions::default()
    };
    let mut stream = interp
        .kb_mut()
        .execute_typed_logical_query_with(&q, &options)
        .expect("the query types");
    match first_pull(&mut interp, &mut stream) {
        Ok(None) => {}
        other => panic!("isIn(0, [150, …, 1]) is refuted at depth 200, got {other:?}"),
    }
    let stats = stream.stats();
    assert!(!stats.truncated, "the end is complete");
    assert!(stats.steps > 150, "the miss took a step per element, got {}", stats.steps);
    match first_pull(&mut interp, &mut stream) {
        Ok(None) => {}
        other => panic!("a pull after the end reports the end again, got {other:?}"),
    }
}

/// From a program: `execute_with` at `max_depth: some(200)` answers both goals, where `execute`
/// cuts both at 100. The limit is the caller's to the step: the 150th element is found at depth
/// 149, where the miss is cut, and refuted at 150 — and a cut names the caller's limit.
///
/// FAILS WHEN BACKED OUT [O]: every call is cut at depth 100.
#[test]
fn a_program_sets_max_depth() {
    let mut interp = interp_for(SRC);
    let with_depth = |interp: &mut Interpreter, x: i64, d: i64| {
        call_int(interp, "withDepth", &[Value::Int(x), Value::Int(d)])
    };
    assert_eq!(with_depth(&mut interp, 1, 200), 1, "1 holds at depth 200");
    assert_eq!(with_depth(&mut interp, 0, 200), 0, "0 is refuted at depth 200");
    assert_eq!(with_depth(&mut interp, 1, 149), 1, "the 150th element is 149 deep");
    assert_eq!(with_depth(&mut interp, 0, 149), -1000 - 149, "the miss is cut at 149");
    assert_eq!(with_depth(&mut interp, 0, 150), 0, "and refuted at 150");
    assert_eq!(with_depth(&mut interp, 1, 0), -1000, "depth 0 asks the query's goal alone");
}

/// A small `max_steps` ends the search fast, with `search_truncated(steps(n))` naming the
/// caller's `n`.
///
/// FAILS WHEN BACKED OUT [O]: the search runs at the default fuel, and the cut is depth 100's.
#[test]
fn a_small_max_steps_ends_at_the_callers_steps() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        call_int(&mut interp, "withSteps", &[Value::Int(0), Value::Int(50)]),
        -1_000_000 - 50,
        "search_truncated(steps(50))"
    );
}

/// A limit below 0 is refused before the search starts, as `malformed_query`, on both fields.
///
/// FAILS WHEN BACKED OUT [N]: the search runs, and is cut at depth 0.
#[test]
fn a_negative_limit_is_a_malformed_query() {
    let mut interp = interp_for(SRC);
    assert_eq!(call_int(&mut interp, "withDepth", &[Value::Int(1), Value::Int(-1)]), -7);
    assert_eq!(call_int(&mut interp, "withSteps", &[Value::Int(1), Value::Int(-1)]), -7);
    match ExecuteOptions::from_limits(None, Some(-3)) {
        Err(detail) => assert!(detail.contains("`max_steps` is -3"), "the refusal names the field: {detail}"),
        Ok(options) => panic!("a negative limit is refused, got {options:?}"),
    }
}

/// CONTROL: `execute` keeps the default budget, from a program as from Rust.
#[test]
fn execute_keeps_the_default_budget() {
    let mut interp = interp_for(SRC);
    let default_depth = ResolveConfig::default().max_depth as i64;
    assert_eq!(call_int(&mut interp, "withDefault", &[Value::Int(1)]), -1000 - default_depth);
    assert_eq!(call_int(&mut interp, "withDefault", &[Value::Int(0)]), -1000 - default_depth);
    assert_eq!(ExecuteOptions::default().max_depth, ResolveConfig::default().max_depth);
    assert_eq!(ExecuteOptions::default().max_steps, ResolveConfig::default().max_steps);
}

/// CONTROL: a field that is `none()` keeps the default — both `none()` is `execute`.
#[test]
fn a_field_left_none_keeps_the_default() {
    let mut interp = interp_for(SRC);
    let default_depth = ResolveConfig::default().max_depth as i64;
    assert_eq!(call_int(&mut interp, "withNone", &[Value::Int(1)]), -1000 - default_depth);
    assert_eq!(
        ExecuteOptions::from_limits(Some(200), None).expect("in range"),
        ExecuteOptions {
            max_depth: 200,
            ..ExecuteOptions::default()
        }
    );
}

