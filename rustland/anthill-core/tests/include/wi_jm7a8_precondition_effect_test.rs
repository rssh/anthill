//! WI-20260830-JM7A8 — AN UNSATISFIED VALUE PRECONDITION MUST NOT SUPPRESS THE SAME
//! CALL'S EFFECT ATTRIBUTION.
//!
//! The two verdicts a call can fail are INDEPENDENT: a `requires` clause is a proof
//! obligation over the KB (§5.4), an effect is a row the body incurs (§5.5). Before this
//! ticket the first one reported and the second silently vanished, because
//! `check_apply_iter` raised the precondition as an `Err` — which aborts the call before
//! its effect row is built, so `check_operation_bodies` took its error-only arm and the
//! op-boundary coverage check never ran at all. The surviving diagnostic looked complete.
//!
//! MEASURED ON `examples/guardians` (the ticket's own case, recorded at
//! `docs/design/measured.md` C2a): moving `Email.send`'s precondition onto `to`, the
//! argument its guarded `Permission[Outbox]` already reads, deleted the
//! `undeclared effect: Permission[T = Outbox]` line from `rejected/computed_recipient`
//! and `rejected/letbound_recipient` — the two fixtures that exist to measure §5.5's
//! conservative direction on an undecided guard. A contract added to one operation
//! deleted coverage two files away without deleting a test.
//!
//! ## The fix, and what each test below separates
//!
//! A precondition failure is now RECORDED into a per-body sink
//! (`TypingEnv::deferred_preconditions`) and the call keeps typing, so its effects are
//! attributed; `check_operation_bodies` drains the sink on BOTH arms of the body match.
//! The sink is `None` by default — a caller that does not drain still gets the hard
//! `Err`, so nothing can be swallowed by a route that was never taught to report.
//!
//! THE CHANGE HAS THREE SEPARABLE PARTS, so it was backed out three ways and each row
//! below says which back-out reds it. A row green under all three would measure nothing.
//!
//!   * **(a) the deferral** — restore `return Err(err)` at the precondition site.
//!   * **(b) the drain's placement** — drain only when the body typed `Ok`.
//!   * **(c) the sink's carrier** — make it a by-value `RefCell<Vec<_>>` on the env
//!     (cloning the env then copies it) and drain from `result.env`.
//!
//! | test | what it measures | (a) | (b) | (c) |
//! |---|---|---|---|---|
//! | `both_verdicts_are_reported_for_one_call` | THE ARM | RED | ok | ok |
//! | `two_calls_each_report_their_own_precondition` | one abort no longer hides the rest | RED | ok | ok |
//! | `a_failing_call_in_an_argument_position_reports_both` | the deferral survives a non-top-level position | RED | ok | ok |
//! | `a_body_that_also_fails_elsewhere_still_reports_its_precondition` | drain placement AND carrier | ok | RED | RED |
//! | `a_covered_effect_still_reports_exactly_one_error` | THE CONTROL | ok | ok | ok |
//!
//! **What (c) settled, against the prediction.** The carrier was chosen expecting the
//! argument-position fixture to be what needs it — the build frames return the FRAME's
//! env, so an argument's own env is dropped. Measured: that fixture is green under (c)
//! too, because a Visit that binds nothing pushes the SAME `Rc<TypingEnv>` to its
//! children, so an argument's write lands in the very allocation the parent then clones
//! out. What actually needs a sink reachable from the operation's OWN handle is the
//! `Err` arm: a body that failed to type produces no `TypeResult` and therefore no env to
//! read a by-value channel out of. That is one fixture, and it is the last row but one.
//!
//! THE NO-SINK PATH IS NOT MEASURED HERE, and its controls live where they were written:
//! `wi557_rule_body_precondition_scope_test` (a rule body's ground-refuted precondition
//! still raises, and a floating one still does not) runs against an env that installs no
//! sink, so it is what says the default stayed `Err`.

/// A callee carrying BOTH contract tiers over DIFFERENT arguments — a value precondition
/// on `body`, an unconditional `Permission[Cap]` in its row — and a caller that declares
/// neither enough authority nor a cleared body.
///
/// `cleared` is a declared relation with one row, so `cleared("ok")` is provable at a
/// call site and `cleared("nope")` is not. Nothing here depends on a guard: the effect is
/// declared flat, so the effect verdict is decided by the caller's `effects` row alone
/// and cannot be confused with a guard discharge.
fn program(body: &str, caller_effects: &str, call: &str) -> String {
    format!(
        r#"
sort demo.Cap
end

namespace demo
  import anthill.prelude.{{String}}
  rule cleared(?t)
  fact cleared("ok")
end

sort demo.Svc
  import anthill.prelude.{{Unit, String, Error, Permission}}
  import demo.{{Cap, cleared}}
  operation send(to: String, body: String) -> Unit
    requires cleared(body)
    effects {{Error, Permission[Cap]}}
  operation ignore(x: Unit) -> Unit = x
end

sort demo.App
  import anthill.prelude.{{Unit, String, Error, Permission}}
  import demo.{{Svc, Cap}}
  entity mk
  operation run(self: App) -> Unit
    effects {caller_effects} =
      {call}
end
"#,
        caller_effects = caller_effects,
        call = call.replace("BODY", body),
    )
}

fn errors_for(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

const PRECONDITION: &str = "unsatisfied precondition";
const UNDECLARED: &str = "undeclared effect: Permission[T = Cap]";

#[test]
fn both_verdicts_are_reported_for_one_call() {
    // THE ARM. One call, two independent failures: `cleared("nope")` is unprovable, and
    // the caller's row grants `Error` alone while `Svc.send` performs `Permission[Cap]`.
    //
    // WHAT FAILS WHEN THE CHANGE IS BACKED OUT: this row. Restoring the `return Err(…)`
    // at the precondition site leaves the first assertion green and the second red — the
    // effect line disappears, which is the defect verbatim.
    let errs = errors_for(&program(
        "nope",
        "{Error}",
        r#"Svc.send(to: "a", body: "BODY")"#,
    ));
    assert!(
        errs.iter().any(|e| e.contains(PRECONDITION)),
        "the precondition must still be reported; got: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains(UNDECLARED)),
        "the SAME call's undeclared effect is owed beside it — reporting one and \
         dropping the other leaves a diagnostic that looks complete; got: {errs:#?}"
    );
    // EXACTLY two: continuing past the precondition must not manufacture a third
    // verdict about a call the typer has already judged.
    assert_eq!(
        errs.len(),
        2,
        "expected exactly the two verdicts; got: {errs:#?}"
    );
}

#[test]
fn a_covered_effect_still_reports_exactly_one_error() {
    // THE CONTROL, and it passes with the change backed out — that is what it is for.
    // The same unprovable precondition, with the caller's row WIDENED to cover
    // `Permission[Cap]`, must report ONE error and not two. A change that reported the
    // effect unconditionally, or that double-reported the precondition once per drain
    // site, is red here and green above.
    let errs = errors_for(&program(
        "nope",
        "{Error, Permission[Cap]}",
        r#"Svc.send(to: "a", body: "BODY")"#,
    ));
    assert_eq!(
        errs.len(),
        1,
        "a covered effect owes no second verdict; got: {errs:#?}"
    );
    assert!(
        errs[0].contains(PRECONDITION),
        "and the one owed is the precondition; got: {errs:#?}"
    );
}

#[test]
fn a_failing_call_in_an_argument_position_reports_both() {
    // THE FAILING CALL IS NOT THE BODY. `Svc.send` here is the ARGUMENT of `Svc.ignore`,
    // so its verdict has to survive a frame that reassembles around it — the shape the
    // ticket's own guardians case has (`let sent = Email.send(…)` inside a larger body),
    // one nesting level tighter.
    //
    // WHAT FAILS WHEN IT IS BACKED OUT: back-out (a) only. This row was written expecting
    // it to be what forces the SHARED sink, and MEASURED it is not — see the module
    // header: a Visit that binds nothing hands its children the same `Rc<TypingEnv>`, so
    // an argument's write is already in the allocation the parent clones out, and a
    // by-value channel passes here too. It measures the deferral reaching the boundary
    // from a nested position, which is worth its own row, and it does not measure the
    // carrier — the `Err`-arm row below is what does.
    let errs = errors_for(&program(
        "nope",
        "{Error}",
        r#"Svc.ignore(x: Svc.send(to: "a", body: "BODY"))"#,
    ));
    assert!(
        errs.iter().any(|e| e.contains(PRECONDITION)),
        "an argument-position call's precondition must reach the boundary; got: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains(UNDECLARED)),
        "and so must its effect; got: {errs:#?}"
    );
}

#[test]
fn a_body_that_also_fails_elsewhere_still_reports_its_precondition() {
    // WHY THE DRAIN IS AFTER THE MATCH AND NOT INSIDE ITS `Ok` ARM, AND WHY THE SINK IS
    // SHARED. Here the body's `let` carries an annotation the value cannot satisfy (`Unit`
    // bound at `String`), so `LetAfterValue` returns `Err` and the whole body lands in the
    // error arm — but the precondition was already recorded on the way in and is still
    // owed.
    //
    // WHAT FAILS WHEN IT IS BACKED OUT: back-outs (b) AND (c), and it is the only row that
    // reds under either. (b) is the direct reading — an `Ok`-only drain drops it. (c) is
    // the same fact about the CARRIER: a failed body produces no `TypeResult`, so there is
    // no result env for a by-value channel to be read out of, and the sink has to be
    // reachable from the operation's own handle. Both back-outs leave this row's
    // precondition silently gone — the class of loss the ticket is about, one arm over.
    //
    // THE DEFERRAL ITSELF IS NOT WHAT THIS MEASURES: under back-out (a) the precondition
    // IS the body's error and reports from the `Err` arm anyway, so this row is green
    // there.
    let errs = errors_for(&program(
        "nope",
        "{Error}",
        r#"let bad: String = Svc.send(to: "a", body: "BODY")
      bad"#,
    ));
    assert!(
        errs.iter().any(|e| e.contains(PRECONDITION)),
        "a body that failed for an unrelated reason still owes the precondition it \
         recorded; got: {errs:#?}"
    );
}

#[test]
fn two_calls_each_report_their_own_precondition() {
    // ONE ABORT NO LONGER HIDES THE REST. Two calls, each with an unprovable
    // precondition: raising aborted the body at the first, so the second was never
    // judged. Recording judges both.
    //
    // WHAT FAILS WHEN IT IS BACKED OUT: `errs.len()` drops to 1 and the second call's
    // `"worse"` never appears. Asserted on the CLAUSE TEXT, not on the count alone — the
    // count alone is also satisfied by one error reported twice.
    let errs = errors_for(&program(
        "",
        "{Error, Permission[Cap]}",
        r#"let a = Svc.send(to: "a", body: "nope")
      Svc.send(to: "b", body: "worse")"#,
    ));
    assert!(
        errs.iter().any(|e| e.contains(r#"cleared("nope")"#)),
        "the first call's clause; got: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains(r#"cleared("worse")"#)),
        "and the second call's, which the abort used to hide; got: {errs:#?}"
    );
}
