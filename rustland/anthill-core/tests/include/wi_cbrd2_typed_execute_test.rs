//! A QUERY BUILT AS A VALUE IS TYPED WHEN `KB.execute` READS IT (WI-20261105-CBRD2, proposal
//! 010.1 §3.2, stage 1, decided with the user 2026-11-15). `KB.execute` routes the goals of the
//! `LogicalQuery` it is handed as a written query's are (`load::convert_query_terms`): a call of
//! a spec's member, `=` among them, is decided at the types the query fixes, a relation's goal is
//! passed the dictionary its types build, and a query the typer refuses raises
//! `malformed_query` before the search starts. `Relation.splitFirst` runs a query its citation's
//! load typed, and is not typed again.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch (`kb_execute` calling the untyped
//! `execute_logical_query`), then removed. The control is the switch unset: every row passes.
//!
//! * [`a_relation_goal_built_at_run_time_is_passed_its_dictionary`]: `cited` raises
//!   `evaluation_failure`, "the requirement `anthill.prelude.PartialEq` of a clause was passed
//!   by no caller";
//! * [`a_query_whose_types_do_not_fit_is_refused_before_it_runs`]: `mismatch` raises
//!   `evaluation_failure` from inside `Pt.eq` (`match_failed` on the `Int64`), not
//!   `malformed_query`.
//!
//! [`a_fault_at_a_goal_built_at_run_time_has_no_position`] fails with the position check in
//! `ResolveError::located_at` backed out (measured): `at` is `some` of an occurrence spanning
//! nothing, where the untyped `KB.execute` gave `none()`; it passes with the typing switch, the
//! goal then being the entity it was built as.
//!
//! [`an_equality_built_at_run_time_answers_through_its_carriers_member`],
//! [`a_query_that_owes_nothing_answers_as_before`] and
//! [`a_relation_cited_in_code_is_typed_where_it_is_written`] pass either way by design: the
//! first is answered by the equality index without the change (it reads the operand's
//! constructor and finds `Pt.eq`), and it is the row that keeps answering when the index's
//! run-time readers go; the other two have nothing to type at run time.

use crate::common::{interp_for, load_kb_with, one_definite_int};
use anthill_core::eval::{EvalError, Value};

/// `Pt`'s own `eq` compares `x` alone, so `pt(1, 2)` and `pt(1, 9)` are equal by it and apart
/// by structure: an answer of `1` is `Pt`'s member.
const SRC: &str = r#"
namespace test.cbrd2.exec
  import anthill.prelude.{Int64, Bool, String, PartialEq, Eq, Option, List}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.reflect.{Term, as_term, make_fn, fresh_var, ResolveStreamFailure}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.LogicalQuery.{pattern_query}

  sort Pt
    entity pt(x: Int64, y: Int64)
    provides PartialEq[T = Pt]
    provides Eq[T = Pt]
    operation eq(a: Pt, b: Pt) -> Bool =
      match a case pt(ax, ay) -> match b case pt(bx, by) -> PartialEq.eq(ax, bx)
  end

  fact pt(x: 1, y: 2)

  rule sameR[A](?a: A, ?b: A) :- PartialEq[T = A], ?a = ?b

  entity Goal(g: Term)
  fact Goal(g: pt(1, 2) = pt(1, 9))

  operation ask(goal: Term) -> Int64 effects Error[ResolveStreamFailure] =
    match splitFirst(execute(kb(), pattern_query(term: goal)))
      case none() -> 0
      case some(_) -> 1

  operation plain() -> Int64 effects Error[ResolveStreamFailure] =
    ask(as_term(pt(x: 1, y: fresh_var[Int64]("y"))))
  operation cited() -> Int64 effects Error[ResolveStreamFailure] =
    ask(make_fn("test.cbrd2.exec.sameR", [as_term(pt(1, 2)), as_term(pt(1, 9))]))
  operation built() -> Int64 effects Error[ResolveStreamFailure] =
    ask(make_fn("anthill.prelude.PartialEq.eq", [as_term(pt(1, 2)), as_term(pt(1, 9))]))
  operation mismatch() -> Int64 effects Error[ResolveStreamFailure] =
    ask(make_fn("anthill.prelude.PartialEq.eq", [as_term(pt(1, 2)), as_term(1)]))
  operation divZero() -> Int64 effects Error[ResolveStreamFailure] =
    ask(make_fn("anthill.prelude.Int64.div", [as_term(1), as_term(0), fresh_var[Term]("r")]))

  operation same[A](a: A, b: A) -> Int64 effects Error requires PartialEq[T = A] =
    match sameR(a, b).splitFirst()
      case none() -> 0
      case some(_) -> 1
  operation viaRelation() -> Int64 effects Error = same(pt(1, 2), pt(1, 9))

  rule stored(?n) :- Goal(g: ?g), ?n <=> ask(?g)
end
"#;

/// `test.cbrd2.exec.<op>()` called from the interpreter.
fn call(op: &str) -> Result<Value, EvalError> {
    let mut interp = interp_for(SRC);
    interp.call(&format!("test.cbrd2.exec.{op}"), &[])
}

/// The constructor and `detail` / `reason` of the `ResolveStreamFailure` `op` raises.
fn raised(op: &str) -> (String, String) {
    let mut interp = interp_for(SRC);
    let payload = match interp.call(&format!("test.cbrd2.exec.{op}"), &[]) {
        Err(EvalError::Raised { payload, .. }) => payload,
        other => panic!("`{op}` must raise a ResolveStreamFailure; got {other:?}"),
    };
    let Value::Entity { functor, named, .. } = &payload else {
        panic!("expected an entity payload, got {payload:?}");
    };
    let text = named
        .iter()
        .find(|(k, _)| matches!(interp.kb().local_name_of(*k), "detail" | "reason"))
        .map(|(_, v)| match v {
            Value::Str(s) => s.to_string(),
            other => panic!("the payload's text is a String, got {other:?}"),
        })
        .unwrap_or_default();
    (interp.kb().qualified_name_of(*functor).to_string(), text)
}

/// `sameR`'s clause takes `PartialEq` at its `A`. Cited by a goal built at run time, the query's
/// types fix `A = Pt` when `KB.execute` reads it, and the dictionary they build is passed, as a
/// written query `sameR(pt(1, 2), pt(1, 9))` passes it.
#[test]
fn a_relation_goal_built_at_run_time_is_passed_its_dictionary() {
    match call("cited") {
        Ok(Value::Int(1)) => {}
        other => panic!("`sameR(pt(1, 2), pt(1, 9))` holds through `Pt.eq`; got {other:?}"),
    }
}

/// A `Pt` compared with an `Int64` is refused where the query is typed, as `malformed_query`,
/// and `Pt.eq` never runs on the `Int64`.
#[test]
fn a_query_whose_types_do_not_fit_is_refused_before_it_runs() {
    let (ctor, detail) = raised("mismatch");
    assert_eq!(ctor, "anthill.reflect.ResolveStreamFailure.malformed_query", "{detail}");
    assert!(
        detail.contains("expected Pt, got Int64"),
        "the detail is the typer's refusal; got {detail}"
    );
}

/// A goal built at run time that types and then faults has no position: `evaluation_failure`'s
/// `at` is `none()`, never the empty span of the occurrence the typing built from the value.
#[test]
fn a_fault_at_a_goal_built_at_run_time_has_no_position() {
    let mut interp = interp_for(SRC);
    let payload = match interp.call("test.cbrd2.exec.divZero", &[]) {
        Err(EvalError::Raised { payload, .. }) => payload,
        other => panic!("`div(1, 0, ?r)` must raise evaluation_failure; got {other:?}"),
    };
    let Value::Entity { functor, named, .. } = &payload else {
        panic!("expected an entity payload, got {payload:?}");
    };
    assert_eq!(
        interp.kb().qualified_name_of(*functor),
        "anthill.reflect.ResolveStreamFailure.evaluation_failure"
    );
    let at = named
        .iter()
        .find(|(k, _)| interp.kb().local_name_of(*k) == "at")
        .map(|(_, v)| v)
        .expect("the payload has an `at` field");
    match at {
        Value::Entity { functor, .. } => assert_eq!(
            interp.kb().qualified_name_of(*functor),
            "anthill.prelude.Option.none",
            "a built goal carries no source position; got {at:?}"
        ),
        other => panic!("`at` is an Option entity, got {other:?}"),
    }
}

/// `=` built at run time, and the same `=` stored as code in a `Term` field, answer through
/// `Pt`'s own `eq`: `1` where a structural comparison gives `0`.
#[test]
fn an_equality_built_at_run_time_answers_through_its_carriers_member() {
    match call("built") {
        Ok(Value::Int(1)) => {}
        other => panic!("`pt(1, 2) = pt(1, 9)` holds through `Pt.eq`; got {other:?}"),
    }
    let mut kb = load_kb_with(SRC);
    assert_eq!(
        one_definite_int(&mut kb, "test.cbrd2.exec.stored"),
        Some(1),
        "the goal stored in `Goal`'s `Term` field holds through `Pt.eq`"
    );
}

/// A pattern owes no requirement, and answers as `KB.execute` answered it untyped.
#[test]
fn a_query_that_owes_nothing_answers_as_before() {
    match call("plain") {
        Ok(Value::Int(1)) => {}
        other => panic!("`pt(x: 1, y: ?y)` finds the fact; got {other:?}"),
    }
}

/// A relation cited in an operation body is typed at load where it is written: `same`'s
/// dictionary reaches `sameR`'s `=`, and its stream is not typed again when it runs.
#[test]
fn a_relation_cited_in_code_is_typed_where_it_is_written() {
    match call("viaRelation") {
        Ok(Value::Int(1)) => {}
        other => panic!("`same(pt(1, 2), pt(1, 9))` holds through `Pt.eq`; got {other:?}"),
    }
}
