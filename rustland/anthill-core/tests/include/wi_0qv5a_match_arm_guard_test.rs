//! WI-20260907-0QV5A — A `match` ARM GUARD IS EVALUATED, AND A FALSE ONE FALLS THROUGH
//! TO THE NEXT ARM.
//!
//! WHAT WAS WRONG. `Interpreter`'s `AwaitState::MatchDispatch` cloned `branch.guard` into
//! its await state and then selected the first arm whose PATTERN matched. The guard was
//! never read, never evaluated and never reported, so a guarded arm was indistinguishable
//! from an unguarded one at run time — on a program that loaded clean. Not a missing
//! diagnostic: a wrong answer. `match n case x | eq(x, 1) -> "one" case _ -> "other"`
//! answered `"one"` for every `n`.
//!
//! AND THE TWO LAYERS DISAGREED, which is what made it more than an unimplemented
//! feature. The TYPER already read a guarded arm as CONDITIONAL — WI-537's
//! `match_arm_gamma_facts` deliberately contributes no negation from a guarded earlier arm
//! ("`case 0 | g -> …` matches only when g holds, so a later arm cannot conclude s ≠ 0"),
//! and WI-20260824-Q0093 type-checks the guard's `Bool` DESTINATION. Eval's reading was
//! "this arm always matches". `docs/kernel-language.md` §4.8 states the typer's.
//!
//! ── WHAT THE FIX IS ──
//!
//! [`AwaitState::MatchGuard`] (`eval/frame.rs`) — its own suspend state, because a guard
//! is an arbitrary expression that may call an operation, so the arm scan cannot stay
//! synchronous once it reaches one. `eval/eval.rs`'s `scan_match_arms` is the scan both
//! states enter: `MatchDispatch` when the scrutinee arrives, `MatchGuard` when a guard
//! answered `false` and the scan resumes at the arms AFTER the declining one.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ──
//!
//! Back-out = `scan_match_arms` enters an arm whose pattern matched without consulting
//! its guard, the pre-change reading (mechanically: `branch.guard.filter(|_| false)`, so
//! the guarded path is unreachable and everything else — the state, the pre-filter, the
//! binding install — stays). MEASURED over this file's 8 rows: **7 FAIL, 1 PASSES**.
//!
//! * [`a_guard_that_holds_takes_its_arm_and_a_false_one_falls_through`] — `pick(7)`
//!   answers `"one"`.
//! * [`a_false_guard_resumes_at_the_next_arm`] — `rank(2)` answers `"first"`.
//! * [`a_guard_that_calls_an_operation_drives_the_suspend_path`] — `classify(9)` answers
//!   `"small"`.
//! * [`a_false_guards_bindings_do_not_reach_a_later_arm`] — `shadow(5)` answers 1, the
//!   guarded arm taken outright. (The NEAR-MISS fix — installing the arm's bindings on the
//!   match's own frame before evaluating the guard — answers 5 instead, which is the leak
//!   this row is really for; the back-out reaches it by the shorter road.)
//! * [`every_arm_guarded_and_declining_raises_match_failed`] — `strict(2)` answers `"one"`,
//!   and `strict(3)` would too: the silent-first-matching-arm shape, with no raise anywhere.
//! * [`a_raising_guard_is_the_matchs_own_effect`] — nothing raises, so the handler is never
//!   consulted and `boom(1)` answers `"taken"`.
//! * [`a_guarded_arm_whose_pattern_does_not_match_never_runs_its_guard`] — its `red` half:
//!   the matching arm is entered without running the guard that should have raised.
//!
//! THE ONE THAT PASSES EITHER WAY is [`an_unguarded_match_is_unmoved`], and that is what it
//! is for: the scan was rewritten, so a regression in the shared `scan_match_arms` shows up
//! on an unguarded program rather than only on the guarded rows.
//!
//! ── AND FOUR NEIGHBOURS THE CHANGE DESYNCED, each with one row and one back-out ──
//!
//! Every one of them was a SECOND answer to "is this arm taken?", and every one of them
//! was RIGHT while eval's answer was "always". Each back-out is its own mutation and each
//! fails exactly one row — measured one at a time, then all four together (8 pass / 3 fail
//! here, plus the cpp-gen row in its own crate):
//!
//! 1. `body_specialize::folded_call_match` — the SLD case split enumerated a guarded arm
//!    as an unconditional alternative. Backed out, `Ops.rank(?h) = 1` answers **1 DEFINITE**
//!    solution binding `?h` to `warm`, on a program where evaluating `Ops.rank(warm())`
//!    RAISES. Row: [`a_guarded_arm_is_not_case_split_into_an_unconditional_alternative`].
//! 2. `typing::collect_covered_entities` — exhaustiveness counted a guarded arm as
//!    covering, so the check promised an arm for a value that now raises. Backed out, the
//!    guarded `enum` program loads clean. Row:
//!    [`a_guarded_arm_does_not_cover_its_constructor_for_exhaustiveness`].
//! 3. `persistence/print.rs` — the renderer dropped the guard, so `match n { x => "one"; _
//!    => "other"; }` was the render of BOTH the guarded program and the guard-free one.
//!    Row: [`a_rendered_match_shows_its_arm_guards`].
//! 4. `anthill-cpp-gen::lower_match_branches_node` — emitted the tag check alone, so the
//!    generated C++ took an arm the interpreter declines. REFUSED now (the chain's last
//!    branch is its catch-all, so a guarded final arm has no fallthrough to lower to).
//!    Row: that crate's `wi_0qv5a_guarded_arm_refusal_test`, which carries TWO — the
//!    refusal itself, and the WI-891 channel it rides: `/code-review` found it filed as a
//!    bare `CppCodegenError`, which is FATAL, so one guarded arm anywhere in a KB emitted
//!    no C++ for any other operation or sort. It is a `capability_gap` now, degrading the
//!    one method to a `static_assert`. The same review found the one guard-blind reader
//!    this census missed — `node_references_name`, which decides whether an anonymous
//!    lambda names its own binder — and its row is there too.
//!
//! Guard-aware already, and checked rather than assumed: `select_arm` (declines), WI-537's
//! `match_arm_gamma_facts` (no negation from a guarded earlier arm), `flow_derive` (merges
//! the guard's effect row), `simp_rewrite` (rewrites it structurally),
//! `load::const_node_is_pure` (walks it), and smt-gen's cache key (hashes it through
//! `for_each_child`).
//!
//! ── ONE ARM THIS FILE CANNOT DRIVE, stated rather than credited ──
//!
//! `AwaitState::MatchGuard`'s non-`Bool` delivery (the `None` of `literal_bool`) has no
//! source program that reaches it: Q0093's `boolean_position_error` refuses a non-`Bool`
//! guard at LOAD, and that refusal is pinned by
//! `wi_q0093_type_value_occurrence_matrix_test::a_boolean_position_refuses_a_type_value_-
//! and_says_which_slot`. The arm exists because not every `Expr::Match` reaching eval came
//! through that check — `term_to_occurrence` rebuilds one from a reflect `Term` — and it
//! is a loud `TypeMismatch` rather than a silent "not true", which is the repo's
//! loud-over-silent rule. Nothing here measures it.

use std::cell::RefCell;
use std::rc::Rc;

use anthill_core::eval::effects::HandlerAction;
use anthill_core::eval::{EvalError, Value};
use anthill_core::kb::term_view::TermView;

use crate::common::interp_for;

/// The whole fixture, in one namespace so every row runs against one load.
const SRC: &str = r#"
namespace test.qv5a
  import anthill.prelude.{Bool, Int64, String}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.Ord.{lt}

  sort Colour
    entity red
    entity green
  end

  sort Trouble
    entity trouble
  end

  -- BOTH DIRECTIONS over one program: one guard, taken and not taken.
  operation pick(n: Int64) -> String =
    match n
      case x | eq(x, 1) -> "one"
      case _ -> "other"

  -- THREE arms, so "resume at the NEXT arm" is distinguishable from "resume at
  -- the LAST arm": arm 0's pattern matches every n and its guard decides.
  operation rank(n: Int64) -> String =
    match n
      case x | eq(x, 1) -> "first"
      case x | eq(x, 2) -> "second"
      case _ -> "rest"

  -- A guard that CALLS a user operation, so the guard suspends into a callee
  -- frame and its value comes back through `deliver` — the suspend/resume path,
  -- not a literal folded in place.
  operation is_small(n: Int64) -> Bool = lt(n, 3)
  operation classify(n: Int64) -> String =
    match n
      case x | is_small(x) -> "small"
      case _ -> "big"

  -- The CONTROL: no guard anywhere. Passes with and without the change.
  operation plain(n: Int64) -> String =
    match n
      case 1 -> "one"
      case _ -> "other"

  -- A false guard's pattern bindings must not reach a later arm. `x` is bound
  -- OUTSIDE the match; arm 0 rebinds it to the scrutinee and then declines, so
  -- the wildcard arm must read the outer 99.
  operation shadow(n: Int64) -> Int64 =
    let x = 99
    match n
      case x | eq(x, 1) -> 1
      case _ -> x

  -- Every arm guarded, every guard false for n = 3: the scan runs out of arms
  -- and must raise `Error[MatchFailed]`, not fall into the last one.
  operation strict(n: Int64) -> String =
    match n
      case x | eq(x, 1) -> "one"
      case x | eq(x, 2) -> "two"

  -- A guard that RAISES. WI-537 merges the guard's effect row into the match's,
  -- so `Error` is declared on the operation and the raise is the match's own
  -- effect rather than something escaping past it.
  operation boom(n: Int64) -> String effects Error[Trouble] =
    match n
      case x | raises(x) -> "taken"
      case _ -> "untaken"
  operation raises(n: Int64) -> Bool effects Error[Trouble] = Error.raise(trouble())

  -- A guard behind a pattern that does NOT match: `red` and `green` are distinct
  -- constructors, so arm 0's guard — which raises — must never be reached for a
  -- `green` scrutinee, and must be reached for a `red` one.
  operation colour_of(n: Int64) -> Colour =
    match n
      case 0 -> red()
      case _ -> green()
  operation only_reached_through_the_pattern(n: Int64) -> String effects Error[Trouble] =
    match colour_of(n)
      case red() | raises(1) -> "red"
      case _ -> "not red"
end
"#;

fn expect_str(v: &Value, why: &str) -> String {
    match v {
        Value::Str(s) => s.clone(),
        other => panic!("{why}: expected a String value, got {other:?}"),
    }
}

/// THE CORE ROW — one program, one guard, both directions. A guard that holds enters its
/// arm; the same guard false falls through.
///
/// FAILS ON THE BACK-OUT: `pick(7)` answers `"one"`. This is the assertion
/// `wi_q0093_type_value_occurrence_matrix_test` pinned the OTHER way around while eval
/// ignored guards; that control is now this row.
#[test]
fn a_guard_that_holds_takes_its_arm_and_a_false_one_falls_through() {
    let mut interp = interp_for(SRC);
    let held = interp
        .call("test.qv5a.pick", &[Value::Int(1)])
        .unwrap_or_else(|e| panic!("pick(1): {e:?}"));
    assert_eq!(
        expect_str(&held, "pick(1)"),
        "one",
        "a guard that holds takes its own arm"
    );
    let declined = interp
        .call("test.qv5a.pick", &[Value::Int(7)])
        .unwrap_or_else(|e| panic!("pick(7): {e:?}"));
    assert_eq!(
        expect_str(&declined, "pick(7)"),
        "other",
        "a false guard must fall through to the next arm — answering \"one\" here is the \
         pre-WI-20260907-0QV5A reading, where the guard was cloned into the await state \
         and never read"
    );
}

/// FALLTHROUGH GOES TO THE **NEXT** ARM, not to the last one. Arm 0's pattern is a plain
/// binder, so it matches every `n` and only its guard decides; arm 1 is the same shape.
/// `rank(2)` therefore requires arm 0 to decline AND arm 1 to be tried and taken.
///
/// FAILS ON THE BACK-OUT: `rank(2)` and `rank(3)` both answer `"first"`. It would also
/// fail on a fix that resumed at the LAST arm (`rank(2)` would answer `"rest"`), which is
/// the reason the fixture has three arms rather than two.
#[test]
fn a_false_guard_resumes_at_the_next_arm() {
    let mut interp = interp_for(SRC);
    for (n, want) in [(1, "first"), (2, "second"), (3, "rest")] {
        let v = interp
            .call("test.qv5a.rank", &[Value::Int(n)])
            .unwrap_or_else(|e| panic!("rank({n}): {e:?}"));
        assert_eq!(
            expect_str(&v, "rank"),
            want,
            "rank({n}) must reach the arm whose guard is the first to hold"
        );
    }
}

/// THE SUSPEND/RESUME PATH. The guard is a call to a user-declared operation over the
/// arm's own binding, so evaluating it pushes a child frame, dispatches, and delivers the
/// answer back into `AwaitState::MatchGuard`. A guard that were only ever a folded literal
/// would never exercise that.
///
/// FAILS ON THE BACK-OUT on its second call: `classify(9)` answers `"small"`. The first
/// call is the right answer for the wrong reason either way, which is why both are here.
#[test]
fn a_guard_that_calls_an_operation_drives_the_suspend_path() {
    let mut interp = interp_for(SRC);
    let small = interp
        .call("test.qv5a.classify", &[Value::Int(2)])
        .unwrap_or_else(|e| panic!("classify(2): {e:?}"));
    assert_eq!(expect_str(&small, "classify(2)"), "small");
    let big = interp
        .call("test.qv5a.classify", &[Value::Int(9)])
        .unwrap_or_else(|e| panic!("classify(9): {e:?}"));
    assert_eq!(
        expect_str(&big, "classify(9)"),
        "big",
        "the guard's CALL must be evaluated and its answer consulted"
    );
}

/// CONTROL — an unguarded `match` answers exactly as it did. PASSES EITHER WAY BY DESIGN:
/// it is what says the arm scan was rewritten without moving ordinary matching, so a
/// regression in the shared `scan_match_arms` shows up here rather than only in the
/// guarded rows.
#[test]
fn an_unguarded_match_is_unmoved() {
    let mut interp = interp_for(SRC);
    let one = interp
        .call("test.qv5a.plain", &[Value::Int(1)])
        .unwrap_or_else(|e| panic!("plain(1): {e:?}"));
    assert_eq!(expect_str(&one, "plain(1)"), "one");
    let other = interp
        .call("test.qv5a.plain", &[Value::Int(2)])
        .unwrap_or_else(|e| panic!("plain(2): {e:?}"));
    assert_eq!(expect_str(&other, "plain(2)"), "other");
}

/// THE ARM'S BINDINGS ARE THE GUARD'S, AND A DECLINING ARM'S DO NOT SURVIVE IT.
///
/// `x` is bound to 99 outside the match. Arm 0's pattern rebinds `x` to the scrutinee
/// (5) — the guard reads THAT one, which is why `eq(x, 1)` is false — and then declines.
/// The wildcard arm's body reads `x`, and it must be the outer 99: the arm-0 binding was
/// installed on the GUARD's child frame, which the delivery popped, and never on the frame
/// running the match.
///
/// FAILS ON THE BACK-OUT for a different reason worth naming: without the guard the first
/// arm is TAKEN, so the operation answers 1. It also fails on the near-miss fix that
/// installs the arm's bindings on the match's own frame before evaluating the guard — that
/// answers 5, the leaked binding.
#[test]
fn a_false_guards_bindings_do_not_reach_a_later_arm() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.qv5a.shadow", &[Value::Int(5)])
        .unwrap_or_else(|e| panic!("shadow(5): {e:?}"));
    assert_eq!(
        v.literal_int64(interp.kb()),
        Some(99),
        "the wildcard arm must read the `let`-bound 99; 5 is arm 0's binding leaking past \
         its own false guard, and 1 is the guard not being consulted at all. Got {v:?}",
    );
}

/// THE EXHAUSTIVENESS END. Every arm is guarded and every guard is false, so the scan runs
/// out of arms — which is the same exhaustion as no pattern matching, and raises the same
/// `Error[MatchFailed]` (WI-610) with the scrutinee that failed.
///
/// FAILS ON THE BACK-OUT: `strict(2)` answers `"one"` and `strict(3)` would too — arm 0's
/// pattern is a plain binder, so ignoring the guard makes it swallow every scrutinee and
/// nothing ever raises. That is the silent-arm shape this ticket names. The two positive
/// calls sit in the same row so the exhaustion assertion is not the only thing driving the
/// fixture.
#[test]
fn every_arm_guarded_and_declining_raises_match_failed() {
    let mut interp = interp_for(SRC);
    for (n, want) in [(1, "one"), (2, "two")] {
        let v = interp
            .call("test.qv5a.strict", &[Value::Int(n)])
            .unwrap_or_else(|e| panic!("strict({n}): {e:?}"));
        assert_eq!(expect_str(&v, "strict"), want);
    }

    let err = interp
        .call("test.qv5a.strict", &[Value::Int(3)])
        .expect_err("every arm declined, so the match is exhausted");
    match &err {
        EvalError::Raised { payload } => match payload {
            Value::Entity { functor, named, .. } => {
                assert_eq!(
                    interp.kb().qualified_name_of(*functor),
                    "anthill.prelude.MatchFailed.match_failed",
                    "guard exhaustion raises the same payload an unmatched scrutinee does",
                );
                let scrutinee = named
                    .iter()
                    .find(|(s, _)| interp.kb().local_name_of(*s) == "scrutinee")
                    .map(|(_, v)| v);
                assert_eq!(
                    scrutinee.and_then(|v| v.literal_int64(interp.kb())),
                    Some(3),
                    "the payload carries the value that found no arm; got {payload:?}",
                );
            }
            other => panic!("expected a match_failed entity payload, got {other:?}"),
        },
        other => panic!("expected Raised, got {other:?}"),
    }
}

/// A GUARD THAT RAISES IS THE MATCH'S OWN EFFECT. WI-537 merges the guard's effect row
/// into the match's, so `boom` declares `Error[Trouble]` and the raise is routed through
/// the installed `Error` handler exactly as one from an arm body would be — it does not
/// escape the match, and the guarded arm is not entered.
///
/// FAILS ON THE BACK-OUT: the guard is never evaluated, so nothing raises, the handler is
/// never consulted, and `boom(1)` answers `"taken"`.
///
/// THE LOAD HALF IS ASSERTED TOO, and it passes either way by design — WI-537 merged the
/// guard's row before this ticket. It is here because the run half alone cannot tell "the
/// row reaches the match" from "nothing checks the row": the same operation with `effects`
/// omitted must be refused naming the effect the GUARD raises, and nothing else in this
/// file or its neighbours drives that pairing.
#[test]
fn a_raising_guard_is_the_matchs_own_effect() {
    // The load half first, since it says what the run half is a consequence of.
    let undeclared = r#"
namespace test.qv5aeff
  import anthill.prelude.{Bool, Int64, String}

  sort Trouble
    entity trouble
  end

  operation raises(n: Int64) -> Bool effects Error[Trouble] = Error.raise(trouble())
  operation quiet(n: Int64) -> String =
    match n
      case x | raises(x) -> "taken"
      case _ -> "untaken"
end
"#;
    let errs = match crate::common::try_load_kb_with(undeclared) {
        Err(errs) => errs,
        Ok(_) => panic!(
            "a guard that raises contributes its row to the MATCH, so an operation that              declares no `effects` must be refused"
        ),
    };
    assert!(
        errs.iter()
            .any(|e| e.contains("undeclared effect") && e.contains("Trouble")),
        "the refusal must name the effect the guard raises; got {errs:?}",
    );

    let mut interp = interp_for(SRC);
    let seen: Rc<RefCell<Option<Value>>> = Rc::new(RefCell::new(None));
    let seen_h = seen.clone();
    interp
        .register_effect_handler(
            "anthill.prelude.Error",
            Box::new(move |_i, _op, args| {
                *seen_h.borrow_mut() = args.first().cloned();
                Ok(HandlerAction::Throw(
                    args.first().cloned().unwrap_or(Value::Unit),
                ))
            }),
        )
        .expect("register Error handler");

    let err = interp
        .call("test.qv5a.boom", &[Value::Int(1)])
        .expect_err("the guard raises, so the call does not answer");
    assert!(
        matches!(err, EvalError::Raised { .. }),
        "a raise is non-resumable, so a Throwing handler still aborts as Raised; got {err:?}",
    );
    let payload = seen
        .borrow()
        .clone()
        .expect("the Error handler was consulted for the guard's raise");
    match &payload {
        Value::Entity { functor, .. } => assert_eq!(
            interp.kb().qualified_name_of(*functor),
            "test.qv5a.Trouble.trouble",
            "the guard's own payload reached the handler",
        ),
        other => panic!("expected the guard's raised entity, got {other:?}"),
    }
}

/// THE GUARD IS REACHED ONLY THROUGH THE PATTERN, AND THROUGH IT IT IS REACHED. Arm 0 is
/// `case red() | raises(1)`, whose guard raises if it runs at all. For a `green` scrutinee
/// the pattern does not match, so the guard must not run and the answer is the wildcard
/// arm's; for a `red` one the pattern matches, so the guard runs and the call raises.
///
/// FAILS ON THE BACK-OUT on its `red` half: the guard is never evaluated, so arm 0 is
/// entered and the call answers `"red"`. The `green` half passes either way — it is what
/// separates "the guard is consulted" from "the guard is consulted BEFORE the pattern",
/// which nothing else in this file would notice.
#[test]
fn a_guarded_arm_whose_pattern_does_not_match_never_runs_its_guard() {
    let mut interp = interp_for(SRC);
    let green = interp
        .call(
            "test.qv5a.only_reached_through_the_pattern",
            &[Value::Int(1)],
        )
        .unwrap_or_else(|e| panic!("a non-matching pattern must not reach its guard: {e:?}"));
    assert_eq!(
        expect_str(&green, "only_reached_through_the_pattern(1)"),
        "not red"
    );

    let err = interp
        .call(
            "test.qv5a.only_reached_through_the_pattern",
            &[Value::Int(0)],
        )
        .expect_err("a MATCHING pattern reaches its guard, which raises");
    assert!(
        matches!(err, EvalError::Raised { .. }),
        "the matching arm's guard must run; got {err:?}",
    );
}

// ── THE THREE NEIGHBOURS THIS CHANGE DESYNCED, AND THEIR REPAIRS ────────────────
//
// Making eval consult a guard falsified three readings that were CORRECT while it did
// not — each of them a second answer to "is this arm taken?", each of them previously
// agreeing with eval's "always". They are repaired here rather than deferred, because a
// deferred one is a second evaluator of the same construct shipping a different answer.
// (The fourth is in `anthill-cpp-gen`; its refusal is driven by that crate's
// `wi_0qv5a_guarded_arm_refusal_test`.)

/// NEIGHBOUR 1 — THE SLD CASE SPLIT. `body_specialize::folded_call_match` expands an
/// unground bodied op-call into one alternative per `match` arm
/// (`resolve.rs::unfold_eq_operand`), and `UnfoldArm` carries a pattern and a body and
/// nothing else — so a guarded arm was enumerated as though its constructor alone decided
/// it. It now declines the whole unfold when any arm is guarded, exactly as `select_arm`
/// beside it already declined rather than picking past one.
///
/// MEASURED, and the wrong answer was DEFINITE. Backing the decline out (`if false &&
/// b.guard.is_some()`), `rank(?h) = 1` answers **1 definite** solution binding `?h` to
/// `warm` — a positive, decided claim that `rank(warm) = 1`, which the SECOND half of this
/// row shows the evaluator contradicting: `never()` is false and `cool()` does not match,
/// so `Ops.rank(warm())` RAISES. With the decline both queries suspend (one floundered
/// answer, nothing bound).
///
/// THE `cool` QUERY SUSPENDS TOO, and that is the deliberate price: the decline is over
/// the whole match, not the guarded arm, because "no earlier arm was taken" is itself
/// undecidable once an earlier arm carries a guard. Completeness lost, soundness kept —
/// `folded_call_match`'s own doc states that trade for the shapes it already declined.
#[test]
fn a_guarded_arm_is_not_case_split_into_an_unconditional_alternative() {
    let src = r#"
namespace test.qv5arel
  import anthill.prelude.{Bool, Int64}

  sort Hue
    entity warm
    entity cool
  end

  sort Ops
    operation never() -> Bool = false
    operation rank(h: Hue) -> Int64 =
      match h
        case warm() | never() -> 1
        case cool() -> 2
  end

  rule warm1(?h) :- Ops.rank(?h) = 1
  rule cool2(?h) :- Ops.rank(?h) = 2
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    for q in ["test.qv5arel.warm1", "test.qv5arel.cool2"] {
        let decided = crate::common::definite_unary(&mut kb, q);
        assert!(
            decided.is_empty(),
            "{q}: a guarded arm must not be case-split into an unconditional \
             alternative — a DEFINITE answer here is the relational reading deciding \
             what the evaluator declines. Got {decided:?}",
        );
    }

    // THE OTHER HALF — what the relational answer would have contradicted. Same program,
    // evaluated: `warm` matches arm 0's pattern, its guard is false, `cool()` does not
    // match, so the match is exhausted.
    let mut interp = interp_for(src);
    let warm = interp
        .call(
            "test.qv5arel.Ops.rank",
            &[Value::Entity {
                functor: interp
                    .kb()
                    .try_resolve_symbol("test.qv5arel.Hue.warm")
                    .expect("warm resolves"),
                pos: Vec::new().into(),
                named: Vec::new().into(),
            }],
        )
        .expect_err("every arm declined, so `rank(warm())` raises");
    assert!(
        matches!(warm, EvalError::Raised { .. }),
        "the evaluated reading raises where the case split answered 1; got {warm:?}",
    );
}

/// NEIGHBOUR 2 — THE EXHAUSTIVENESS CHECK. `typing::collect_covered_entities` counted a
/// guarded arm's constructor as covered (and a guarded BINDER as a catch-all), which was
/// right while eval entered a guarded arm unconditionally and is wrong now: the check
/// would promise that a `warm` scrutinee finds an arm, and the run would raise
/// `MatchFailed` on exactly that value. A guarded arm now covers nothing — the same
/// reading a written `: T` annotation already gets (spec §"Nullary only, and at every
/// depth").
///
/// FAILS ON THE BACK-OUT of that skip: the guarded program loads clean. The CONTROL below
/// is the same two arms with the guard removed — it loads either way, which is what says
/// this refuses guarded coverage rather than coverage.
#[test]
fn a_guarded_arm_does_not_cover_its_constructor_for_exhaustiveness() {
    let program = |guard: &str, ns: &str| {
        format!(
            r#"
namespace test.qv5aex{ns}
  import anthill.prelude.{{Bool, Int64}}

  enum Hue
    entity warm
    entity cool
  end

  operation never() -> Bool = false
  operation rank(h: Hue) -> Int64 =
    match h
      case warm(){guard} -> 1
      case cool() -> 2
end
"#
        )
    };
    let errs = match crate::common::try_load_kb_with(&program(" | never()", "g")) {
        Err(errs) => errs,
        Ok(_) => panic!(
            "a GUARDED `warm` arm leaves `warm` uncovered — the match can now raise \
             `MatchFailed` on it, so the check must say so at load"
        ),
    };
    assert!(
        errs.iter()
            .any(|e| e.contains("non-exhaustive match on Hue") && e.contains("missing warm")),
        "the refusal must name the constructor the guarded arm no longer covers; got {errs:?}",
    );

    // CONTROL — the same arms unguarded still cover, so the check is about the GUARD and
    // not about `warm()` patterns. Loads either way by design.
    crate::common::try_load_kb_with(&program("", "p"))
        .unwrap_or_else(|e| panic!("an UNGUARDED `warm` arm still covers `warm`: {e:?}"));
}

/// NEIGHBOUR 3 — THE RENDERER. `TermPrinter::write_occurrence`'s `Expr::Match` arm dropped
/// the guard, so a guarded arm and an unguarded one rendered as the same text. Harmless
/// while a guard changed nothing; now it hides the half of the arm that decides, in the
/// writer the load diagnostics quoting a body go through.
///
/// FAILS ON THE BACK-OUT of the three added lines: the render is
/// `match n { x => "one"; _ => "other"; }`, indistinguishable from the guard-free program.
#[test]
fn a_rendered_match_shows_its_arm_guards() {
    use anthill_core::persistence::print::TermPrinter;
    let kb = crate::common::load_kb_with(SRC);
    let sym = kb
        .try_resolve_symbol("test.qv5a.pick")
        .expect("pick resolves");
    let body = kb.op_body_node(sym).expect("pick has a body");
    let printed = TermPrinter::new(&kb).print_occurrence(body);
    assert_eq!(
        printed, r#"match n { x | eq(x, 1) => "one"; _ => "other"; }"#,
        "the guard must be rendered between the pattern and the arrow",
    );
}
