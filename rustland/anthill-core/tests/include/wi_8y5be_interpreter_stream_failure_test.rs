//! WI-20260911-8Y5BE — the INTERPRETER face of `KB.execute` produces the declared
//! `Error[ResolveStreamFailure]`, as the host bridge does.
//!
//! The ticket delivered the payload on the host bridge (`anthill-stl`'s
//! `SearchStreamAdapter`) and left this face describing it only as an upper bound:
//! `stream_split_first`'s resolver pump ignored the search's recorded faults and handed
//! a faulted pull back as an `undecided` row, and `kb_execute` turned a query that does
//! not lower into `EvalError::Internal`. A handler written against the declared row
//! never fired here. Both now raise through the `Error` effect.

use crate::common::interp_for;
use anthill_core::eval::{EvalError, Value};

/// An ill-typed comparison the resolver cannot ASK — `tag` declares no types, so the
/// typer cannot see that `?x` is a `String` — reached through an entity-headed rule so
/// an operation body can query it. `?x` is BODY-ONLY on purpose: written in the head,
/// it takes the field's declared `String` and the typer refuses the comparison at load.
///
/// `probe` answers 1 when the first pull yields a row and 0 when the stream is empty;
/// `clean_probe` is the same query over a rule with no comparison. `faulty_stream` hands
/// the stream itself back so a test can pull it more than once. `faulty_rel` is the same
/// body cited as a RELATION, comparing against `2` so the fixture's text holds
/// `PartialOrd.gt(?x, 1)` exactly once and a span match names `Faulty`'s comparison.
const SRC: &str = r#"
namespace test.wi8y5be
  import anthill.prelude.{Stream, Option, Pair, String, Int64, PartialOrd, List}
  import anthill.prelude.List.{length}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term, Solution, fresh_var, as_term, ResolveStreamFailure}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.LogicalQuery.{pattern_query}

  sort Probes
    entity Faulty(x: String)
    entity Clean(x: String)
  end

  fact tag("a")
  rule Faulty(x: ?y) :- tag(?y), tag(?x), PartialOrd.gt(?x, 1)
  rule Clean(x: ?x) :- tag(?x)

  operation probe() -> Int64 effects Error[ResolveStreamFailure] =
    match splitFirst(execute(kb(), pattern_query(term: as_term(Faulty(x: fresh_var[String]("x"))))))
      case none()  -> 0
      case some(_) -> 1

  operation clean_probe() -> Int64 effects Error[ResolveStreamFailure] =
    match splitFirst(execute(kb(), pattern_query(term: as_term(Clean(x: fresh_var[String]("x"))))))
      case none()  -> 0
      case some(_) -> 1

  operation faulty_stream() -> Stream[T = Solution, E = Error[ResolveStreamFailure]]
    effects Error[ResolveStreamFailure] =
    execute(kb(), pattern_query(term: as_term(Faulty(x: fresh_var[String]("x")))))

  rule faulty_rel(?y) :- tag(?y), tag(?x), PartialOrd.gt(?x, 2)
  operation rel_count() -> Int64 effects Error = length(faulty_rel.takeN(10))
end
"#;

/// The named field `name` of an entity payload.
fn field<'v>(interp: &anthill_core::eval::Interpreter, payload: &'v Value, name: &str) -> &'v Value {
    match payload {
        Value::Entity { named, .. } => named
            .iter()
            .find(|(k, _)| interp.kb().local_name_of(*k) == name)
            .map(|(_, v)| v)
            .unwrap_or_else(|| panic!("payload has no `{name}` field: {payload:?}")),
        other => panic!("expected an entity payload, got {other:?}"),
    }
}

/// A faulted query RAISES `evaluation_failure`, carrying the resolver's words and the
/// written comparison's occurrence.
///
/// FAILS WHEN BACKED OUT (the fault check in `SearchStream::split_first`): `probe`
/// returns `Ok(Int(1))`, the faulted pull handed back as an `undecided` row. CONTROL:
/// `a_clean_query_still_yields_its_row`.
#[test]
fn a_faulted_query_raises_evaluation_failure() {
    let mut interp = interp_for(SRC);
    let payload = match interp.call("test.wi8y5be.probe", &[]) {
        Err(EvalError::Raised { payload }) => payload,
        other => panic!(
            "a goal the search could not ask must raise the declared Error, not yield a \
             row; got {other:?}"
        ),
    };
    match &payload {
        Value::Entity { functor, .. } => assert_eq!(
            interp.kb().qualified_name_of(*functor),
            "anthill.reflect.ResolveStreamFailure.evaluation_failure"
        ),
        other => panic!("expected an entity payload, got {other:?}"),
    }
    match field(&interp, &payload, "reason") {
        Value::Str(reason) => assert!(
            reason.contains("two DIFFERENT literal sorts"),
            "`reason` carries the resolver's own words; got {reason}"
        ),
        other => panic!("`reason` is a String, got {other:?}"),
    }
    let at = field(&interp, &payload, "at");
    assert_eq!(
        interp.kb().qualified_name_of(match at {
            Value::Entity { functor, .. } => *functor,
            other => panic!("`at` is an Option entity, got {other:?}"),
        }),
        "anthill.prelude.Option.some",
        "the written comparison is a positioned occurrence"
    );
    let span = match field(&interp, at, "value") {
        Value::Node(occ) => occ.span,
        other => panic!("`at` carries the occurrence itself, got {other:?}"),
    };
    assert_eq!(
        SRC.get(span.start() as usize..span.end() as usize),
        Some("PartialOrd.gt(?x, 1)"),
        "`at` locates the WRITTEN comparison in the fixture"
    );
}

/// CONTROL, passes either way by design: the same query shape over a rule with no
/// comparison still yields its row, so the fault arm has not swallowed the ordinary path.
#[test]
fn a_clean_query_still_yields_its_row() {
    let mut interp = interp_for(SRC);
    match interp.call("test.wi8y5be.clean_probe", &[]) {
        Ok(Value::Int(1)) => {}
        other => panic!("a healthy query streams its row; got {other:?}"),
    }
}

/// A query that does not LOWER raises `malformed_query` rather than an internal fault.
/// The typer refuses a non-`LogicalQuery` argument in source, so this calls the builtin
/// directly, the way a host embedder or a reflect-built value reaches it.
///
/// FAILS WHEN BACKED OUT (`kb_execute`'s raise): the call returns `EvalError::Internal`.
#[test]
fn a_query_that_does_not_lower_raises_malformed_query() {
    let mut interp = interp_for(SRC);
    let kb = interp.call("anthill.reflect.KB.kb", &[]).expect("the ambient kb()");
    let payload = match interp.call("anthill.reflect.KB.execute", &[kb, Value::Int(1)]) {
        Err(EvalError::Raised { payload }) => payload,
        other => panic!("a non-query must raise malformed_query; got {other:?}"),
    };
    match &payload {
        Value::Entity { functor, .. } => assert_eq!(
            interp.kb().qualified_name_of(*functor),
            "anthill.reflect.ResolveStreamFailure.malformed_query"
        ),
        other => panic!("expected an entity payload, got {other:?}"),
    }
}

/// The functor's qualified name of an entity payload carried by a raise.
fn raised_functor(interp: &anthill_core::eval::Interpreter, err: EvalError) -> String {
    match err {
        EvalError::Raised {
            payload: Value::Entity { functor, .. },
        } => interp.kb().qualified_name_of(functor).to_string(),
        other => panic!("expected a raised entity payload, got {other:?}"),
    }
}

/// A CAUGHT fault leaves the stream REFUSING further pulls rather than reporting it
/// ended. A pull after the raise is `stream_misused`, as the host bridge answers the
/// same re-pull: an ordinary end-of-stream would let the consumer read the rows it
/// already has as a complete answer set.
///
/// FAILS WHEN BACKED OUT (parking the slot as `Empty` instead of `Faulted`): the second
/// pull is `Ok(None)`.
#[test]
fn a_pull_after_a_fault_is_refused_not_ended() {
    let mut interp = interp_for(SRC);
    let handle = match interp.call("test.wi8y5be.faulty_stream", &[]) {
        Ok(Value::Stream(h)) => h,
        other => panic!("`execute` returns a stream, got {other:?}"),
    };
    let first = interp
        .stream_split_first(&handle)
        .expect_err("the first pull reports the fault");
    assert_eq!(
        raised_functor(&interp, first),
        "anthill.reflect.ResolveStreamFailure.evaluation_failure"
    );
    let second = interp
        .stream_split_first(&handle)
        .expect_err("a pull after the fault is refused, not answered as the end");
    assert_eq!(
        raised_functor(&interp, second),
        "anthill.reflect.ResolveStreamFailure.stream_misused"
    );
}

/// The raise reaches an installed `Error` HANDLER — the reason it is routed through the
/// effect at all rather than built as a bare `EvalError::Raised`. The handler records the
/// payload and resumes, which the runtime refuses as non-resumable; that refusal is only
/// reachable through the handler, so it doubles as proof of the routing.
///
/// FAILS WHEN BACKED OUT (the fault check in `SearchStream::split_first`): the handler
/// never fires and `probe` answers 1.
#[test]
fn a_faulted_query_is_catchable_by_an_error_handler() {
    use anthill_core::eval::effects::HandlerAction;
    use std::cell::RefCell;
    use std::rc::Rc;

    let mut interp = interp_for(SRC);
    let seen: Rc<RefCell<Vec<Value>>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&seen);
    interp
        .register_effect_handler(
            "anthill.prelude.Error",
            Box::new(move |_i, _op, args| {
                sink.borrow_mut().extend(args.iter().cloned());
                Ok(HandlerAction::Pure(Value::Unit))
            }),
        )
        .expect("register Error handler");
    let resumed = interp.call("test.wi8y5be.probe", &[]);
    assert!(
        matches!(&resumed, Err(EvalError::Internal(msg)) if msg.contains("non-resumable")),
        "a handler that resumes a raise is refused as non-resumable; got {resumed:?}"
    );
    let payloads = seen.borrow();
    assert_eq!(payloads.len(), 1, "the handler fires exactly once; got {payloads:?}");
    match &payloads[0] {
        Value::Entity { functor, .. } => assert_eq!(
            interp.kb().qualified_name_of(*functor),
            "anthill.reflect.ResolveStreamFailure.evaluation_failure"
        ),
        other => panic!("expected an evaluation_failure entity, got {other:?}"),
    }
}

/// The RELATION face reports the same fault. Its pump used to ignore the search's
/// faults: the faulted goal residualized, so the drain raised `relation_floundered` —
/// "never decided" for a goal that could not be asked, and a payload the SLD bridge
/// SCHEDULES rather than reports.
///
/// FAILS WHEN BACKED OUT (the fault check in `SearchStream::split_first`): the raise is
/// `relation_floundered`.
#[test]
fn a_faulted_relation_raises_evaluation_failure_not_floundered() {
    let mut interp = interp_for(SRC);
    let err = interp
        .call("test.wi8y5be.rel_count", &[])
        .expect_err("a relation over a faulted search must not drain");
    assert_eq!(
        raised_functor(&interp, err),
        "anthill.reflect.ResolveStreamFailure.evaluation_failure"
    );
}

/// A NEGATION THE RESOLVER DECIDED IS NOT A FAULT, even though its sub-search recorded
/// one. `p(1)`'s single clause faults on its first disjunct and PROVES on its second, so
/// `not(p(1))` definitively fails and `q` has no answers. `step_naf` keeps the sub-search's
/// message as a DIAGNOSTIC on that path — the answer is complete — and the lazy door must
/// not report it as a fault.
///
/// One clause with a disjunction, not two clauses, so the fault is recorded BEFORE the
/// proof whatever the clause order: `drain_verdict` stops at the first definite answer,
/// and with two clauses the proving one could run first and record nothing.
///
/// FAILS WHEN BACKED OUT (`split_first` reading `errors` instead of `faults`): the pull is
/// `Err`. The first assertion is what keeps this from passing vacuously: the diagnostic
/// is really there.
#[test]
fn a_decided_negation_over_a_faulted_subsearch_is_not_a_fault() {
    use anthill_core::kb::resolve::ResolveConfig;
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi8y5be.naf
  import anthill.prelude.{Int64, String, PartialOrd}
  import anthill.kernel.{not, or}
  fact item(1)
  fact tag("a")
  rule p(?k) :- tag(?x), or(PartialOrd.gt(?x, 1), true), item(?k)
  rule q(?k) :- item(?k), not(p(?k))
end
"#,
    );
    crate::common::supply_invocation_imports(&mut kb, &["test.wi8y5be.naf.*"]);
    let goal = crate::common::query_pattern_term(&mut kb, "q(?k)");
    let (solutions, stats) = kb.resolve_with_stats(&[goal.clone()], &ResolveConfig::default());
    assert!(
        solutions.is_empty() && stats.errors.iter().any(|e| e.message.contains("two DIFFERENT literal sorts")),
        "the fixture must decide `q` empty WITH the sub-search's diagnostic recorded; \
         got {} solutions, errors {:?}",
        solutions.len(),
        stats.errors
    );
    let stream = kb.resolve_lazy(&[goal], &ResolveConfig::default());
    match stream.split_first(&mut kb) {
        Ok(None) => {}
        Ok(Some(_)) => panic!("`not(p(1))` fails, so `q` has no answer"),
        Err(fault) => panic!(
            "a decided negation is not a fault; its sub-search's message is a diagnostic. \
             Got: {}",
            fault.error.message
        ),
    }
}
