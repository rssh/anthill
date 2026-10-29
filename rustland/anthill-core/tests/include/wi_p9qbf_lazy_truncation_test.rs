//! WI-20260913-P9QBF — a LAZY search cut at its depth limit does not end as a complete
//! empty answer set: where the stream would end, it raises the declared
//! `Error[ResolveStreamFailure]` with `search_truncated(max_depth)`.
//!
//! WI-628 made the EAGER drains honest (`drain_all` / `drain_verdict` carry `truncated`, so
//! NAF, guards and counts read a cut search as undecided), but `SearchStream::split_first`
//! reported only faults, and its exhaustion exit answered `Ok(None)` whether or not a branch
//! was abandoned. Every lazy face — `execute`, a relation drain, `isEmpty` — read the end as
//! "that was all".
//!
//! LEDGER, measured with each part backed out alone in one build:
//! * the exhaustion arm in `SearchStream::exhausted` — every row marked "FAILS WHEN BACKED
//!   OUT (the exhaustion arm)" ends `Ok(None)` / `none()` / a short count instead;
//! * the account (`RuntimeAccount::SearchTruncated` in `ALL`) — the construction rows load,
//!   and `a_rule_body_drain_that_was_cut_is_a_truncation_not_a_value` reports a fault;
//! * the disposition (`SearchTruncated` read as `Truncation` by `raised_disposition`) —
//!   `a_rule_body_drain_that_was_cut_is_a_truncation_not_a_value` records a fault message.
//! The controls pass either way by design, and say so at their site.

use crate::common::{interp_for, load_errors_of, load_kb_with, query_pattern_term};
use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::kb::resolve::{ResolveConfig, SearchFailure};

/// `Deep` is cut at the depth limit with no answer. `Some1` has one answer, which every
/// level of its recursion derives again, so it yields rows and is then cut. `Reach` is a
/// recursion that ends well below the limit — the control. `deep` / `some1` / `reach` are
/// the same three cited as relations.
const SRC: &str = r#"
namespace test.p9qbf
  import anthill.prelude.{Int64, String, Bool, Error, Option, Stream, Result, List}
  import anthill.prelude.List.{length}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{Term, Solution, fresh_var, as_term, ResolveStreamFailure}
  import anthill.reflect.ResolveStreamFailure.{search_truncated}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.LogicalQuery.{pattern_query}

  sort Probes
    entity Deep(x: Int64)
    entity Some1(x: Int64)
    entity Link(from: Int64, to: Int64)
    entity Reach(from: Int64, to: Int64)
  end

  rule Deep(x: ?x) :- Deep(x: ?x)
  fact Some1(x: 1)
  rule Some1(x: ?x) :- Some1(x: ?x)
  fact Link(from: 1, to: 2)
  fact Link(from: 2, to: 3)
  rule Reach(from: ?a, to: ?b) :- Link(from: ?a, to: ?b)
  rule Reach(from: ?a, to: ?c) :- Link(from: ?a, to: ?b), Reach(from: ?b, to: ?c)

  rule deep(?x) :- Deep(x: ?x)
  rule some1(?x) :- Some1(x: ?x)
  rule reach(?a, ?b) :- Reach(from: ?a, to: ?b)

  operation executeDeep() -> Int64 effects Error[ResolveStreamFailure] =
    match splitFirst(execute(kb(), pattern_query(term: as_term(Deep(x: fresh_var[Int64]("x"))))))
      case none()  -> 0
      case some(_) -> 1

  operation executeReach() -> Int64 effects Error[ResolveStreamFailure] =
    match splitFirst(execute(kb(), pattern_query(term: as_term(Reach(from: 3, to: fresh_var[Int64]("t"))))))
      case none()  -> 0
      case some(_) -> 1

  operation deepStream() -> Stream[T = Solution, E = Error[ResolveStreamFailure]]
    effects Error[ResolveStreamFailure] =
    execute(kb(), pattern_query(term: as_term(Deep(x: fresh_var[Int64]("x")))))

  operation some1Stream() -> Stream[T = Solution, E = Error[ResolveStreamFailure]]
    effects Error[ResolveStreamFailure] =
    execute(kb(), pattern_query(term: as_term(Some1(x: fresh_var[Int64]("x")))))

  operation reachStream() -> Stream[T = Solution, E = Error[ResolveStreamFailure]]
    effects Error[ResolveStreamFailure] =
    execute(kb(), pattern_query(term: as_term(Reach(from: 1, to: fresh_var[Int64]("t")))))

  operation caughtDepth() -> Int64 =
    match Error.reify(lambda () -> executeDeep())
      case ok(n) -> n
      case err(search_truncated(d)) -> d
      case err(_) -> -1

  operation deepCount() -> Int64 effects Error = length(deep.takeN(10))
  operation deepIsEmpty() -> Bool effects Error = deep(1).isEmpty()
  operation some1Count(n: Int64) -> Int64 effects Error = length(some1.takeN(n))
  operation reachCount() -> Int64 effects Error = length(reach.takeN(100))
  operation reachIsEmpty() -> Bool effects Error = reach(3, 1).isEmpty()

  rule counted(?n) :- ?n <=> deepCount()
end
"#;

const SEARCH_TRUNCATED: &str = "anthill.reflect.ResolveStreamFailure.search_truncated";

/// The raised payload's constructor, by qualified name, and the payload.
fn raised(interp: &Interpreter, result: Result<Value, EvalError>, what: &str) -> (String, Value) {
    match result {
        Err(EvalError::Raised {
            payload: payload @ Value::Entity { .. },
            ..
        }) => {
            let Value::Entity { functor, .. } = &payload else { unreachable!() };
            (interp.kb().qualified_name_of(*functor).to_string(), payload)
        }
        other => panic!("{what}: expected a raised entity payload, got {other:?}"),
    }
}

/// The `max_depth` field of a `search_truncated` payload.
fn max_depth_of(interp: &Interpreter, payload: &Value) -> i64 {
    let Value::Entity { named, .. } = payload else {
        panic!("expected an entity payload, got {payload:?}")
    };
    match named
        .iter()
        .find(|(k, _)| interp.kb().local_name_of(*k) == "max_depth")
        .map(|(_, v)| v)
    {
        Some(Value::Int(d)) => *d,
        other => panic!("`max_depth` is an Int64 field, got {other:?} in {payload:?}"),
    }
}

/// `execute` over a search cut at the depth limit RAISES `search_truncated`, naming the
/// limit, in place of `none()`.
///
/// FAILS WHEN BACKED OUT (the exhaustion arm): `executeDeep` answers `Ok(Int(0))`.
#[test]
fn execute_over_a_cut_search_raises_search_truncated() {
    let mut interp = interp_for(SRC);
    let result = interp.call("test.p9qbf.executeDeep", &[]);
    let (ctor, payload) = raised(&interp, result, "executeDeep");
    assert_eq!(ctor, SEARCH_TRUNCATED);
    assert_eq!(
        max_depth_of(&interp, &payload),
        ResolveConfig::default().max_depth as i64,
        "`max_depth` is the limit of the search the stream runs"
    );
}

/// The raise is the declared `Error[ResolveStreamFailure]`, so a boundary typed at it
/// catches it, and the program MATCHES the account and reads its field.
///
/// FAILS WHEN BACKED OUT (the exhaustion arm): `caughtDepth` answers 0, the `ok(n)` arm.
#[test]
fn a_program_catches_and_matches_search_truncated() {
    let mut interp = interp_for(SRC);
    match interp.call("test.p9qbf.caughtDepth", &[]) {
        Ok(Value::Int(d)) => assert_eq!(d, ResolveConfig::default().max_depth as i64),
        other => panic!("the boundary catches `search_truncated(d)`; got {other:?}"),
    }
}

/// The RELATION face raises it too, through `takeN` and through `isEmpty` — the latter read
/// the end of a cut search as "no member".
///
/// FAILS WHEN BACKED OUT (the exhaustion arm): `deepCount` answers 0 and `deepIsEmpty`
/// `true`.
#[test]
fn a_relation_over_a_cut_search_raises_search_truncated() {
    let mut interp = interp_for(SRC);
    for op in ["test.p9qbf.deepCount", "test.p9qbf.deepIsEmpty"] {
        let result = interp.call(op, &[]);
        let (ctor, _) = raised(&interp, result, op);
        assert_eq!(ctor, SEARCH_TRUNCATED, "{op}");
    }
}

/// ROWS BEFORE THE CUT ARE ANSWERS and come out first: each pull of `Some1`'s stream yields a
/// definite row, and only the pull that would END the stream raises. A pull after that is
/// refused (`stream_misused`), not answered as the end, which would read the rows already
/// taken as all there are.
///
/// FAILS WHEN BACKED OUT (the exhaustion arm): the last pull is `Ok(None)`.
#[test]
fn rows_before_the_cut_come_out_first() {
    let mut interp = interp_for(SRC);
    let handle = match interp.call("test.p9qbf.some1Stream", &[]) {
        Ok(Value::Stream(h)) => h,
        other => panic!("`execute` returns a stream, got {other:?}"),
    };
    let solution_definite = interp
        .kb()
        .try_resolve_symbol("anthill.reflect.Solution.definite")
        .expect("the Solution enum is loaded");
    let mut rows = 0usize;
    let end = loop {
        match interp.stream_split_first(&handle) {
            Ok(Some((Value::Entity { functor, .. }, _))) => {
                assert_eq!(functor, solution_definite, "every row before the cut is definite");
                rows += 1;
            }
            Ok(Some((other, _))) => panic!("a row is a Solution entity, got {other:?}"),
            Ok(None) => panic!("a search cut at its limit must not end as a complete set ({rows} rows)"),
            Err(e) => break e,
        }
    };
    assert!(rows >= 1, "the fact's answer comes out before the cut");
    let (ctor, _) = raised(&interp, Err(end), "the end of Some1's stream");
    assert_eq!(ctor, SEARCH_TRUNCATED);
    let again = interp.stream_split_first(&handle).map(|_| Value::Unit);
    let (ctor, _) = raised(&interp, again, "a pull after the raise");
    assert_eq!(ctor, "anthill.reflect.ResolveStreamFailure.stream_misused");
}

/// The same on the relation face: a consumer that stops BEFORE the end never sees the cut,
/// and one that drains to it does.
///
/// The first half passes either way by design (`takeN(5)` stops early); the second FAILS
/// WHEN BACKED OUT (the exhaustion arm): `some1Count(1000)` answers the short count.
#[test]
fn a_relation_hands_out_its_rows_before_the_cut() {
    let mut interp = interp_for(SRC);
    match interp.call("test.p9qbf.some1Count", &[Value::Int(5)]) {
        Ok(Value::Int(5)) => {}
        other => panic!("five rows are there before the cut; got {other:?}"),
    }
    let result = interp.call("test.p9qbf.some1Count", &[Value::Int(1000)]);
    let (ctor, _) = raised(&interp, result, "some1Count(1000)");
    assert_eq!(ctor, SEARCH_TRUNCATED);
}

/// CONTROL, passes either way by design: a recursion that ENDS below the limit ends as it
/// did — `none()` from `execute`, every row from a relation, `true` from `isEmpty` of a pair
/// it does not hold, and an ordinary end after the last row.
#[test]
fn a_search_that_ends_below_the_limit_ends_as_before() {
    let mut interp = interp_for(SRC);
    match interp.call("test.p9qbf.executeReach", &[]) {
        Ok(Value::Int(0)) => {}
        other => panic!("`Reach(from: 3, ..)` has no answer, and the search is complete; got {other:?}"),
    }
    match interp.call("test.p9qbf.reachCount", &[]) {
        Ok(Value::Int(3)) => {}
        other => panic!("`reach` holds (1,2), (2,3), (1,3); got {other:?}"),
    }
    match interp.call("test.p9qbf.reachIsEmpty", &[]) {
        Ok(Value::Bool(true)) => {}
        other => panic!("`reach(3, 1)` holds nothing; got {other:?}"),
    }
    let handle = match interp.call("test.p9qbf.reachStream", &[]) {
        Ok(Value::Stream(h)) => h,
        other => panic!("`execute` returns a stream, got {other:?}"),
    };
    let mut rows = 0;
    while interp
        .stream_split_first(&handle)
        .unwrap_or_else(|e| panic!("a complete search ends without a raise; got {e:?}"))
        .is_some()
    {
        rows += 1;
    }
    assert_eq!(rows, 2, "`Reach(from: 1, ..)` has two answers");
}

/// THE CORE DOOR: `split_first` answers `SearchFailure::Truncated` with the stream's own
/// limit at the exhaustion exit, after the rows, and `Ok(None)` for a search that ended.
///
/// FAILS WHEN BACKED OUT (the exhaustion arm): `Deep` and `Some1` end `Ok(None)`.
#[test]
fn split_first_reports_the_cut_at_its_end() {
    let mut kb = load_kb_with(SRC);
    crate::common::supply_invocation_imports(&mut kb, &["test.p9qbf.*"]);
    let config = ResolveConfig {
        max_depth: 7,
        ..ResolveConfig::default()
    };
    let drain = |kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str| {
        let goal = query_pattern_term(kb, pattern);
        let mut stream = kb.resolve_lazy(&[goal], &config);
        let mut rows = 0usize;
        loop {
            match stream.split_first(kb) {
                Ok(Some((sol, rest))) => {
                    assert!(sol.is_definite(), "{pattern}: every row is definite");
                    rows += 1;
                    stream = rest;
                }
                Ok(None) => return (rows, None),
                Err(failure) => return (rows, Some(failure)),
            }
        }
    };
    match drain(&mut kb, "Deep(x: ?x)") {
        (0, Some(SearchFailure::Truncated { max_depth: 7 })) => {}
        other => panic!("`Deep` is cut at the stream's limit 7 with no row; got {other:?}"),
    }
    match drain(&mut kb, "Some1(x: ?x)") {
        (rows, Some(SearchFailure::Truncated { max_depth: 7 })) if rows >= 1 => {}
        other => panic!("`Some1` yields its rows, then is cut; got {other:?}"),
    }
    // CONTROL, passes either way: the recursion ends at depth 3.
    match drain(&mut kb, "Reach(from: 1, to: ?t)") {
        (2, None) => {}
        other => panic!("`Reach(from: 1, ..)` has two rows and ends; got {other:?}"),
    }
}

/// THE EAGER DOORS ARE UNCHANGED, passes either way by design: `resolve_with_stats` still
/// answers a cut search with its rows and `truncated`, no fault, and a negation over a cut
/// goal is undecided — no definite answer — as WI-628 made it.
#[test]
fn the_eager_doors_are_unchanged() {
    let mut kb = load_kb_with(&SRC.replace(
        "  rule counted(?n)",
        "  import anthill.kernel.{not}\n  rule notDeep :- not(Deep(x: 1))\n  rule counted(?n)",
    ));
    crate::common::supply_invocation_imports(&mut kb, &["test.p9qbf.*"]);
    let config = ResolveConfig::default();
    let goal = query_pattern_term(&mut kb, "Deep(x: ?x)");
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(
        solutions.is_empty() && stats.truncated && stats.errors.is_empty(),
        "`Deep`: no row, truncated, no fault; got {} rows, truncated {}, errors {:?}",
        solutions.len(),
        stats.truncated,
        stats.errors
    );
    let goal = query_pattern_term(&mut kb, "notDeep");
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(
        solutions.iter().all(|s| !s.is_definite()) && stats.truncated,
        "`not(Deep(x: 1))` is undecided over a cut search; got {} rows ({} definite), truncated {}",
        solutions.len(),
        solutions.iter().filter(|s| s.is_definite()).count(),
        stats.truncated
    );
}

/// A RULE BODY'S CALL THAT DRAINS A CUT SEARCH HAS NO VALUE, and the rule's search is
/// incomplete: `deepCount()` raises `search_truncated` inside the bridge, which reads it as a
/// truncation below — the goal waits, the search is marked cut, and no fault message is
/// recorded, since nothing is wrong with the callee.
///
/// FAILS WHEN BACKED OUT: the exhaustion arm — `counted` answers `?n = 0` definitely; the
/// account, or the disposition — `stats.errors` holds "raised search_truncated(…)".
#[test]
fn a_rule_body_drain_that_was_cut_is_a_truncation_not_a_value() {
    let mut kb = load_kb_with(SRC);
    crate::common::supply_invocation_imports(&mut kb, &["test.p9qbf.*"]);
    let goal = query_pattern_term(&mut kb, "counted(?n)");
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(
        solutions.iter().all(|s| !s.is_definite()),
        "a count over a cut search is not an answer; got {} definite rows",
        solutions.iter().filter(|s| s.is_definite()).count()
    );
    assert!(stats.truncated, "the rule's search is incomplete");
    assert!(
        stats.errors.is_empty(),
        "a truncation is no fault of the callee; got {:?}",
        stats.errors
    );
}

/// `search_truncated` IS ONE OF THE RUNTIME'S ACCOUNTS: a program matches it (above) and
/// does not construct one, in an operation body or in a clause — the bridge reads a raise's
/// cause off its constructor, so a forged one would pass for a cut search.
///
/// FAILS WHEN BACKED OUT (the account): both shapes load.
#[test]
fn a_program_does_not_construct_search_truncated() {
    let header = "namespace test.p9qbf.forge\n  import anthill.prelude.{Int64, Error}\n  \
                  import anthill.reflect.{ResolveStreamFailure}\n  \
                  import anthill.reflect.ResolveStreamFailure.{search_truncated}\n";
    for (shape, item) in [
        (
            "an operation body's raise",
            "operation forge() -> Int64 effects {Error[ResolveStreamFailure]} = \
             Error.raise(search_truncated(max_depth: 1))",
        ),
        ("a fact", "fact held(search_truncated(max_depth: 1))"),
    ] {
        let errs = load_errors_of(&format!("{header}  {item}\nend\n"));
        crate::common::assert_refused_naming(
            &errs,
            &[SEARCH_TRUNCATED, "does not construct one"],
            shape,
        );
    }
}
