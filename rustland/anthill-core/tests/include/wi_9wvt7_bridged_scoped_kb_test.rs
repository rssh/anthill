//! WI-20260908-9WVT7 (found by its review) — a SCOPED KB (`KB.loaded`) MADE BY A RULE-BODY
//! CALL stayed applied to the resolver's KB after the call.
//!
//! A rule-body call is evaluated by a scratch interpreter LENT the resolver's own KB
//! (`KnowledgeBase::run_in_bridge_interp`), and a scoped load is applied to that KB in place,
//! undone when its last holder goes. A call that ANSWERED a value still holding one — a `KB`,
//! or a `Result` around one — handed the KB back with the layer applied, so every later goal,
//! of the same clause or another, read the scoped source's facts: `loads(?r), seen(n: ?n)`
//! answered the loaded `42` beside the base's `1`, the same two goals swapped answered only
//! `1`, and a failed clause's or a failed negation's layer survived the backtrack. Now the
//! layer is discarded before the KB goes back, and such an answer is refused
//! (`EvalError::ScopedKbOutlivesCall`): the call has no value.
//!
//! WHAT FAILS UNDER THE BACK-OUT — MEASURED: `Interpreter::release_layers_for_handback` taken
//! out of `run_in_bridge_interp` → `a_scoped_kb_does_not_outlive_a_rule_body_call` and
//! `no_route_leaves_a_layer_behind`. PASSES EITHER WAY BY DESIGN:
//! `reading_the_scoped_kb_inside_the_call_answers` — the repair the refusal names, whose
//! handle is gone before the call ends.

use anthill_core::kb::resolve::ResolveConfig;

const PROGRAM: &str = r#"
namespace test.bkb
  import anthill.prelude.{Int64, String, Error, Result, List}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{KB, LoadFailed}

  sort Seen
    entity Seen(n: Int64)
  end
  fact Seen(n: 1)

  -- The scoped KB itself is the answer: through a rule-body reify, and through an operation.
  rule loads(?r) :- Error.reify(lambda () -> KB.loaded(cons("namespace zz.a  import test.bkb.{Seen}  fact Seen(n: 42)  end", nil())), ?r)
  rule afterLoad(?n) :- loads(?r), Seen(n: ?n)
  rule beforeLoad(?n) :- Seen(n: ?n), loads(?r)

  operation load1(src: String) -> Result[E = LoadFailed, T = KB] =
    Error.reify(lambda () -> KB.loaded(cons(src, nil())))
  rule loadsOp(?r) :- load1("namespace zz.b  import test.bkb.{Seen}  fact Seen(n: 43)  end", ?r)
  rule afterLoadOp(?n) :- loadsOp(?r), Seen(n: ?n)

  -- A clause that loads and then fails, beside one that reads; and a negation over it.
  rule branch(0) :- loads(?r), Seen(n: 99)
  rule branch(?n) :- Seen(n: ?n)
  rule loadsThenFails(?r) :- loads(?r), Seen(n: 99)
  rule underNot(?n) :- not loadsThenFails(?), Seen(n: ?n)

  -- The repair: read what the scoped KB answers inside the call, and return that.
  operation seenCount(src: String) -> Int64 =
    match Error.reify(lambda () -> KB.loaded(cons(src, nil())))
      case ok(k) -> KB.facts_of(k, Seen).length()
      case err(_) -> 0
  rule countInside(?n) :- seenCount("namespace zz.c  import test.bkb.{Seen}  fact Seen(n: 44)  end", ?n)
  rule countThenBase(?n) :- countInside(?c), Seen(n: ?m), ?n <=> ?c * 100 + ?m
end
"#;

/// Every value `qn(?r)` answers, definite or not, as an Int64.
#[track_caller]
fn every_answer(kb: &mut anthill_core::kb::KnowledgeBase, qn: &str) -> Vec<i64> {
    let rows = crate::common::query_unary(kb, qn);
    let mut out: Vec<i64> = rows
        .iter()
        .map(|(v, _)| {
            crate::common::scalar_int(kb, v).unwrap_or_else(|| panic!("{qn}: an Int64, got {v:?}"))
        })
        .collect();
    out.sort_unstable();
    out
}

/// THE DEFECT. After a rule-body call answered a scoped KB, the base's facts are all a later
/// goal reads, in either goal order, and the call that answered it is the fault.
#[test]
fn a_scoped_kb_does_not_outlive_a_rule_body_call() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(every_answer(&mut kb, "test.bkb.afterLoad"), vec![1]);
    assert_eq!(every_answer(&mut kb, "test.bkb.beforeLoad"), vec![1]);
    let goal = crate::common::query_pattern_term(&mut kb, "test.bkb.loads(?r)");
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(sols.iter().all(|s| !s.is_definite()), "no definite answer");
    assert!(
        stats
            .errors
            .iter()
            .any(|e| e.message.contains("cannot outlive the call that loaded it")),
        "the call that answered the scoped KB is the fault: {:?}",
        stats.errors
    );
}

/// The operation-body route, a clause that loads and then fails, and a negation over one.
#[test]
fn no_route_leaves_a_layer_behind() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(every_answer(&mut kb, "test.bkb.afterLoadOp"), vec![1]);
    assert_eq!(every_answer(&mut kb, "test.bkb.branch"), vec![1]);
    assert_eq!(every_answer(&mut kb, "test.bkb.underNot"), vec![1]);
}

/// PASSES EITHER WAY BY DESIGN — the repair: the scoped KB read inside the call (the base's
/// one fact and the scoped source's), and the base alone after it.
#[test]
fn reading_the_scoped_kb_inside_the_call_answers() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.bkb.countThenBase"), Some(201));
}
