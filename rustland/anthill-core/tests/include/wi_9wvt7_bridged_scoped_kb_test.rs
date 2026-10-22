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
//! (`EvalError::ScopedKbOutlivesCall`): the call has no value. What the scratch interpreter's
//! const cache holds is let go first, so a `const` holding a scoped KB, read by a call that
//! answers an `Int64`, is not taken for its answer; and a call that RAISED a payload holding
//! one is refused naming the raise.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build:
//!
//!   * `Interpreter::release_layers_for_handback` taken out of `run_in_bridge_interp` →
//!     `a_scoped_kb_does_not_outlive_a_rule_body_call`, `no_route_leaves_a_layer_behind`,
//!     `a_const_holding_a_scoped_kb_is_no_answer` (the const's layer stays applied, and the
//!     goal after the call reads its fact: `245` beside `201`) and
//!     `a_raise_holding_a_scoped_kb_names_the_raise` (the generic advice);
//!   * the const cache kept → `a_const_holding_a_scoped_kb_is_no_answer` (refused, where the
//!     answer is `2`);
//!   * a raise refused as an answer is → `a_raise_holding_a_scoped_kb_names_the_raise`.
//!
//! PASSES EITHER WAY BY DESIGN: `reading_the_scoped_kb_inside_the_call_answers` — the repairs
//! the refusal names, whose handle is gone before the call ends.

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
      case ok(k) -> KB.facts_of(k, Seen[]).length()
      case err(_) -> 0
  rule countInside(?n) :- seenCount("namespace zz.c  import test.bkb.{Seen}  fact Seen(n: 44)  end", ?n)
  rule countThenBase(?n) :- countInside(?c), Seen(n: ?m), ?n <=> ?c * 100 + ?m

  -- The repair in a lambda: the call that loads is an operand, the reading one its caller.
  operation mkReader(src: String) -> () -> Int64 =
    match Error.reify(lambda () -> KB.loaded(cons(src, nil())))
      case ok(k) -> lambda () -> KB.facts_of(k, Seen[]).length()
      case err(_) -> lambda () -> 0
  operation applyIt(f: () -> Int64) -> Int64 = f()
  rule nestedOperand(?n) :- applyIt(mkReader("namespace zz.f  import test.bkb.{Seen}  fact Seen(n: 47)  end"), ?n)
  rule inLambda(?n) :- applyIt(lambda () -> applyIt(mkReader("namespace zz.f  import test.bkb.{Seen}  fact Seen(n: 47)  end")), ?n)
  rule inLambdaThenBase(?n) :- inLambda(?c), Seen(n: ?m), ?n <=> ?c * 100 + ?m

  -- A const holding a scoped KB, read by an operation that answers an Int64.
  operation mkK() -> Result[E = LoadFailed, T = KB] =
    Error.reify(lambda () -> KB.loaded(cons("namespace zz.d  import test.bkb.{Seen}  fact Seen(n: 45)  end", nil())))
  const ck: Result[E = LoadFailed, T = KB] = mkK()
  operation countVia() -> Int64 =
    match ck
      case ok(k) -> KB.facts_of(k, Seen[]).length()
      case err(_) -> 0
  rule viaConst(?n) :- countVia(?n)
  rule viaConstThenBase(?n) :- countVia(?c), Seen(n: ?m), ?n <=> ?c * 100 + ?m

  sort KbAt
    entity kbAt(k: KB, n: Int64)
  end
  -- A match no case of which answers raises `match_failed`, its payload holding the
  -- scrutinee, and so the scoped KB.
  operation pick(b: KbAt) -> Int64 = match b case kbAt(k, n) | n > 100 -> n
  operation loadAndPick(src: String) -> Int64 =
    match Error.reify(lambda () -> KB.loaded(cons(src, nil())))
      case ok(k) -> pick(kbAt(k, 1))
      case err(_) -> 0 - 1
  rule raisesKb(?n) :- loadAndPick("namespace zz.e  import test.bkb.{Seen}  fact Seen(n: 46)  end", ?n)
  rule raisesKbThenBase(?m) :- raisesKb(?n), Seen(n: ?m)
end
"#;

/// The fault messages `qn(?r)` records, with no definite answer beside them.
#[track_caller]
fn faults(kb: &mut anthill_core::kb::KnowledgeBase, qn: &str) -> Vec<String> {
    let goal = crate::common::query_pattern_term(kb, &format!("{qn}(?r)"));
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(sols.iter().all(|s| !s.is_definite()), "{qn}: no definite answer");
    stats.errors.iter().map(|e| e.message.clone()).collect()
}

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
///
/// `Seen`'s `1` once for each shape `loads`' column fills (WI-20261013-WF14Z): the clause
/// reads `?r`'s type off `Error.reify`'s result column, a `Result`, and an inferred column type
/// is its bound, which fills the column the faulted call leaves unbound with an `ok` and an
/// `err`, as a written one does.
#[test]
fn a_scoped_kb_does_not_outlive_a_rule_body_call() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(every_answer(&mut kb, "test.bkb.afterLoad"), vec![1, 1]);
    assert_eq!(every_answer(&mut kb, "test.bkb.beforeLoad"), vec![1, 1]);
    let errors = faults(&mut kb, "test.bkb.loads");
    assert!(
        errors.iter().any(|e| e.contains("its value holds a scoped KB")
            && e.contains("cannot leave the call that made it")),
        "the call that answered the scoped KB is the fault: {errors:?}"
    );
    // An operand's call is a run of its own: the fault is the operand's, and names it.
    let errors = faults(&mut kb, "test.bkb.nestedOperand");
    assert!(
        errors.iter().any(|e| e.starts_with("`test.bkb.mkReader` could not be evaluated")
            && e.contains("its value holds a scoped KB")),
        "the operand that answered the reader is the fault: {errors:?}"
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

/// A `const` holding a scoped KB stays in the scratch interpreter's const cache after the
/// call that forced it, and the call ANSWERED an `Int64`: the cache is let go before the KB
/// goes back, so the answer is the count — the base's one fact and the scoped source's —
/// and the goal after it reads the base alone.
#[test]
fn a_const_holding_a_scoped_kb_is_no_answer() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.bkb.viaConst"), Some(2));
    assert_eq!(every_answer(&mut kb, "test.bkb.viaConstThenBase"), vec![201]);
}

/// A call that RAISED a payload holding a scoped KB is refused naming the raise, and the goal
/// after it reads the base alone.
#[test]
fn a_raise_holding_a_scoped_kb_names_the_raise() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let errors = faults(&mut kb, "test.bkb.raisesKb");
    assert!(
        errors.iter().any(|e| e.contains("it raised match_failed(")
            && e.contains("whose payload holds a scoped KB")),
        "the raise is named: {errors:?}"
    );
    assert_eq!(every_answer(&mut kb, "test.bkb.raisesKbThenBase"), vec![1]);
}

/// PASSES EITHER WAY BY DESIGN — the repairs: the scoped KB read inside the call (the base's
/// one fact and the scoped source's), and in a lambda the rule calls; the base alone after
/// each.
#[test]
fn reading_the_scoped_kb_inside_the_call_answers() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.bkb.countThenBase"), Some(201));
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.bkb.inLambdaThenBase"), Some(201));
}
