//! WI-329 (proposal 045 §5.6, WI-307 phase 4) — HANDLER DISCHARGE, the static half.
//!
//! A handler that discharges effect `K` is an ORDINARY operation whose type SHARES a
//! row tail `ρ` between its body parameter and its result, with `K` present on the body
//! side and absent from the result:
//!
//! ```text
//! handle_K : (body: () -> X @ {K[…], ρ}) -> X @ {ρ}
//! ```
//!
//! There is no `handle_K` GRAMMAR and no per-effect typer rule: §5.6's whole claim is
//! that discharge is carried by the handler's TYPE, so checking `handle_K(λ → e)` is the
//! ordinary call-site row machinery — `ρ` binds to the residual (everything in `e`'s row
//! other than `K`) and the call's row IS `ρ`. Proposal 027's runtime handler is a
//! separate capability; nothing here asserts a handler exists at run time, only that the
//! program is well-typed. Accordingly the handlers below have stand-in bodies (`= 0`):
//! a handler that actually ran its body (`= body()`) would incur `{K, ρ}` against its own
//! declared `{ρ}` and be rejected — that discharge is 027's, not the typer's.
//!
//! WHAT THESE TESTS MEASURE, PER BACK-OUT. Two independent changes shipped with this
//! ticket; each test's doc says which one it pins, and the ones that pin NEITHER say so.
//!
//!   (1) THE PRODUCER FIX (`check_apply`'s `substituted_op_effects` loop). A callee whose
//!       declared row is a bare row VARIABLE — `effects {Rho}`, i.e. every handler —
//!       resolves at the call site, once arg-unification has BOUND that tail, to a bare
//!       `EffectExpression` (`merge(present(Modify), …)`) with no `effects_rows(…)`
//!       wrapper. The loop recognized only the wrapper, so it pushed the whole ROW as a
//!       single "label" into the call's flat effect list. At the operation boundary that
//!       is invisible — `explode_incurred_effect_row` re-explodes it there (WI-441) — but
//!       the LAMBDA arrow builder is not so forgiving: `make_arrow_value` wraps every
//!       element in `present(label = …)`, minting the malformed `present(label =
//!       merge(…))`. So a handler call nested INSIDE a lambda handed to another handler
//!       carried one opaque label, and the outer handler's callback-row check refused it.
//!       Backing this out fails the `nested_*` tests below.
//!
//!   (2) THE DISCHARGE INFERENCE (`infer_discharged_row_tails`, run once after both
//!       arg-unify loops). Ordinary unification binds `ρ` whenever the body DOES perform
//!       the handled label — the declared row then has no unmatched label and
//!       `unify_effect_rows`' closed/open arm binds `ρ := only_a`. It binds nothing when
//!       the body does NOT perform it (a pure body, or the outer of two handlers for the
//!       same label): the declared `K` has no counterpart in the actual row, which is not
//!       an EQUALITY, so that arm refuses without binding and the call died at
//!       `check_unconstrained_type_params` ("type parameter 'Rho' is unconstrained") —
//!       while the same program spelled `handle_Error[Rho = {}](…)` loaded. Callback
//!       conformance is SUBTYPING (`validate_arg_against_param` owns the verdict; the arg
//!       loops discard unify's boolean), so such a call is admissible and `ρ` is the
//!       actual's residual. The pass computes that residual as the UNION over every
//!       parameter naming the tail, which is why it is a pass and not a binding inside the
//!       relation — see `a_tail_shared_by_two_parameters_takes_the_union_of_their_constraints`
//!       for the program the per-argument version broke. Backing this out fails the
//!       `body_that_does_not_perform_*` tests.
//!
//! MEASURED, both back-outs run against all 21 tests in this file:
//!
//!   * back out (1) → 3 fail (`nested_handlers_drop_labels_successively`,
//!     `nested_handlers_discharge_in_either_order`,
//!     `nested_same_handler_discharges_once_and_then_finds_nothing`), each with the
//!     malformed `declares \`merge[left = present[…], …]\`` message;
//!   * back out (2) → 5 fail (`a_body_that_does_not_perform_the_handled_label_is_admitted`,
//!     `…_still_carries_the_rest`, `an_undischarged_label_…_is_reported_as_an_effect`,
//!     `nested_same_handler_discharges_once_and_then_finds_nothing`,
//!     `nested_same_handler_does_not_empty_the_row`), each with
//!     `type parameter 'Rho' … is unconstrained`.
//!
//! `nested_same_handler_discharges_once_and_then_finds_nothing` is the one test that
//! fails under EITHER back-out — it needs (1) to compose and (2) because the outer
//! `handle_Error` sees a body whose `Error` the inner one already dropped. The two
//! `*_ctl` rejects in the (2) group are refused under both, so their assertion is on the
//! MESSAGE, not the verdict — that is what makes them measure anything.

/// The shared DECLARATIONS: the effectful bodies and the two handlers. No call is made
/// here, so no discharge happens in this file — it stays loadable under either back-out
/// and cannot take the per-case fixtures down with it.
const DECLS: &str = r#"
namespace wi329.decl
  import anthill.prelude.{Int64, Error, Modify, Clock}

  sort Res
  end

  -- Bodies, by which labels they perform.
  operation may_fail(r: Res) -> Int64
    effects {Error[Int64], Modify[Res]}
  = 41

  operation both(r: Res) -> Int64
    effects {Error[Int64], Modify[Res], Clock}
  = 41

  operation only_fails() -> Int64
    effects {Error[Int64]}
  = 41

  operation modifies_only(r: Res) -> Int64
    effects {Modify[Res]}
  = 41

  operation pure_body() -> Int64
    effects {}
  = 7

  -- The handler shape: `K` present on the body side, ABSENT from the result, sharing
  -- the tail `Rho`. The body is a stand-in (see the module doc).
  operation handle_Error[Rho](body: () -> Int64 @ {Error[Int64], Rho}) -> Int64
    effects {Rho}
  = 0

  operation handle_Modify[Sig](body: () -> Int64 @ {Modify[Res], Sig}) -> Int64
    effects {Sig}
  = 0

  -- TWO parameters sharing ONE tail — the shape that decides WHERE the discharge
  -- inference may run. `a` presents the handled label, `b` does not; both name `Rho`.
  operation two[Rho](a: () -> Int64 @ {Error[Int64], Rho}, b: () -> Int64 @ {Rho}) -> Int64
    effects {Rho}
  = 0

  operation clocked() -> Int64
    effects {Clock}
  = 5

  -- The NON-discharging twin: identical except that `Error` stays in the RESULT row.
  -- It is what makes the discharge tests non-vacuous — same call shape, same body,
  -- opposite verdict, and the only difference is the result row.
  operation keep_Error[Rho](body: () -> Int64 @ {Error[Int64], Rho}) -> Int64
    effects {Error[Int64], Rho}
  = 0
end
"#;

/// One consumer namespace per case, loaded as its own file beside [`DECLS`], so no two
/// cases (and in particular no arm and its control) can fail together for a reason that
/// belongs to the other.
fn consumer(tag: &str, body: &str) -> String {
    format!(
        "namespace wi329.c_{tag}\n  \
           import anthill.prelude.{{Int64, Error, Modify, Clock}}\n  \
           import wi329.decl.{{Res, may_fail, both, only_fails, modifies_only, pure_body, handle_Error, handle_Modify, keep_Error, two, clocked}}\n\
         {body}\n\
         end\n"
    )
}

fn expect_load(tag: &str, body: &str, what: &str) {
    let src = consumer(tag, body);
    if let Err(errs) = crate::common::try_load_kb_with_files(&[DECLS, &src]) {
        panic!("expected {what} to load, got load errors: {errs:#?}");
    }
}

fn expect_reject(tag: &str, body: &str, wants: &[&str], what: &str) {
    let src = consumer(tag, body);
    match crate::common::try_load_kb_with_files(&[DECLS, &src]) {
        Ok(_) => panic!("expected {what} to be REJECTED, but it loaded"),
        Err(errs) => {
            let joined = errs.join("\n");
            for want in wants {
                assert!(
                    joined.contains(want),
                    "expected the rejection of {what} to mention {want:?}, got:\n{joined}"
                );
            }
        }
    }
}

// ── The core discharge (v1a row unification; PRE-EXISTING) ─────────────────────────
//
// These four pass with AND without both of this ticket's changes — they are the
// BASELINE that §5.6's "available the moment v1a's row unification lands" was already
// true for, recorded here because WI-329 had no test of its own and nothing else drives
// a shared-tail handler type. What makes them non-vacuous as a GROUP is that each accept
// is paired with a reject that differs in exactly one thing.

/// `e : {Error[Int64], Modify[Res]}` under `handle_Error` ⇒ the call's row is
/// `{Modify[Res]}` — 045 §5.3/§5.6's worked example. The enclosing operation declares
/// exactly the residual.
#[test]
fn discharge_drops_the_handled_label() {
    expect_load(
        "discharge",
        "  operation t(r: Res) -> Int64\n    effects {Modify[Res]}\n  = handle_Error(lambda () -> may_fail(r))",
        "handle_Error over a {Error, Modify} body under a declared {Modify} row",
    );
}

/// The other half of the sandwich: the residual is not merely ADMITTED by the declared
/// row, it is CARRIED. Declaring `{}` is refused because `Modify[Res]` survives the
/// discharge — so `discharge_drops_the_handled_label` above is not passing on a row that
/// was emptied wholesale.
#[test]
fn discharge_keeps_every_unhandled_label() {
    expect_reject(
        "discharge_ctl",
        "  operation t(r: Res) -> Int64\n    effects {}\n  = handle_Error(lambda () -> may_fail(r))",
        &["Modify"],
        "a {} declaration under a call whose residual is {Modify[Res]}",
    );
}

/// And the label really is dropped BY THE RESULT ROW, not by anything about the call
/// shape: `keep_Error` differs from `handle_Error` only in keeping `Error` in its result,
/// and the identical call is then refused for `Error`.
#[test]
fn a_handler_that_keeps_the_label_in_its_result_does_not_discharge() {
    expect_reject(
        "keep",
        "  operation t(r: Res) -> Int64\n    effects {Modify[Res]}\n  = keep_Error(lambda () -> may_fail(r))",
        &["Error"],
        "keep_Error (Error retained in the result row) under a declared {Modify} row",
    );
}

/// A residual of more than one label: `{Error, Modify, Clock}` minus `Error` is BOTH
/// remaining labels, not just the first. Paired with its own control below.
#[test]
fn discharge_leaves_a_multi_label_residual_intact() {
    expect_load(
        "multi",
        "  operation t(r: Res) -> Int64\n    effects {Modify[Res], Clock}\n  = handle_Error(lambda () -> both(r))",
        "handle_Error over a three-label body under its two-label residual",
    );
}

/// Control for the above: dropping either surviving label from the declaration is
/// refused, so the residual is exactly `{Modify[Res], Clock}` — not a subset that
/// happens to be admitted.
#[test]
fn a_multi_label_residual_is_not_partially_dropped() {
    expect_reject(
        "multi_ctl",
        "  operation t(r: Res) -> Int64\n    effects {Clock}\n  = handle_Error(lambda () -> both(r))",
        &["Modify"],
        "a {Clock}-only declaration under a {Modify, Clock} residual",
    );
}

/// The eta'd spelling reaches the same verdict as the lambda one — a nullary op passed
/// by NAME is lifted to `() -> Int64 @ {Error[Int64]}` (WI-700) and discharges to `{}`.
/// PASSES EITHER WAY: it needs neither of this ticket's changes (the body performs the
/// handled label and the call is not nested), and is here because the eta path is a
/// different arrival at `validate_callback_effect_row` than the lambda one.
#[test]
fn discharge_works_through_an_eta_lifted_operation_reference() {
    expect_load(
        "eta",
        "  operation t() -> Int64\n    effects {}\n  = handle_Error(only_fails)",
        "handle_Error(only_fails) — the eta'd nullary spelling, residual {}",
    );
}

// ── Nested handlers (PINS THE PRODUCER FIX) ───────────────────────────────────────
//
// Each of the three below fails on a back-out of the `substituted_op_effects` flatten,
// with `expected callback effects admitted by parameter `body` … (a closed row), got …
// declares `merge[left = present[…], …]`` — the malformed single-label row.

/// `{Error, Modify, Clock}` −`Modify` −`Error` = `{Clock}`: the inner handler's residual
/// is what the outer one discharges FROM.
#[test]
fn nested_handlers_drop_labels_successively() {
    expect_load(
        "nest",
        "  operation t(r: Res) -> Int64\n    effects {Clock}\n  = handle_Error(lambda () -> handle_Modify(lambda () -> both(r)))",
        "handle_Error ∘ handle_Modify over a three-label body, residual {Clock}",
    );
}

/// The same two handlers in the opposite nesting order reach the same residual —
/// discharge is per-label and order-independent.
#[test]
fn nested_handlers_discharge_in_either_order() {
    expect_load(
        "nest_rev",
        "  operation t(r: Res) -> Int64\n    effects {Clock}\n  = handle_Modify(lambda () -> handle_Error(lambda () -> both(r)))",
        "handle_Modify ∘ handle_Error over a three-label body, residual {Clock}",
    );
}

/// Control for both: the surviving `Clock` must still be declared. Without this, the two
/// tests above would also pass on a typer that simply emptied the row at every nesting.
/// PASSES UNDER BACK-OUT (1) TOO, and deliberately so — there the call is refused by the
/// malformed-row message, which happens to render `Clock` inside the merge it prints. It
/// is a control for the RESIDUAL, not a detector for the producer fix; the three tests
/// above are that.
#[test]
fn nesting_does_not_discharge_an_unhandled_label() {
    expect_reject(
        "nest_ctl",
        "  operation t(r: Res) -> Int64\n    effects {}\n  = handle_Error(lambda () -> handle_Modify(lambda () -> both(r)))",
        &["Clock"],
        "a {} declaration under two nested handlers whose residual is {Clock}",
    );
}

// ── A body that does not perform the handled label (PINS THE INFERENCE FIX) ────────

/// `handle_Error(λ → pure_body())`: nothing to discharge, and that is not an error —
/// `ρ` binds to the body's (empty) row and the call's row is `{}`. Before the inference
/// fix this was refused as "type parameter 'Rho' is unconstrained", while the explicitly
/// instantiated twin below loaded; the two spellings now agree.
#[test]
fn a_body_that_does_not_perform_the_handled_label_is_admitted() {
    expect_load(
        "absent",
        "  operation t() -> Int64\n    effects {}\n  = handle_Error(lambda () -> pure_body())",
        "handle_Error over a pure body, residual {}",
    );
}

/// The SOUNDNESS control for that arm, and the reason it binds `ρ` to the residual
/// rather than defaulting it to `{}`: with `Error` absent but `Modify[Res]` performed,
/// `ρ` must be `{Modify[Res]}`.
#[test]
fn a_body_that_does_not_perform_the_handled_label_still_carries_the_rest() {
    expect_load(
        "absent_rest",
        "  operation t(r: Res) -> Int64\n    effects {Modify[Res]}\n  = handle_Error(lambda () -> modifies_only(r))",
        "handle_Error over a Modify-only body, residual {Modify[Res]}",
    );
}

/// …and declaring `{}` for that call is refused. THE MESSAGE IS THE MEASUREMENT here:
/// this program was rejected before the inference fix too, but as an unconstrained type
/// PARAMETER — a refusal that says nothing about effects. It must now be refused for the
/// effect that actually escapes, so the assertion names `undeclared effect` and `Modify`
/// and would fail on a back-out even though the verdict is unchanged.
#[test]
fn an_undischarged_label_under_an_absent_handled_label_is_reported_as_an_effect() {
    expect_reject(
        "absent_ctl",
        "  operation t(r: Res) -> Int64\n    effects {}\n  = handle_Error(lambda () -> modifies_only(r))",
        &["undeclared effect", "Modify"],
        "a {} declaration under handle_Error over a Modify-only body",
    );
}

/// Handling the SAME label twice: the outer `handle_Error` sees a body whose `Error` the
/// inner one already dropped, so it is the `absent` case reached by nesting. THE ONE TEST
/// THAT FAILS UNDER EITHER BACK-OUT — it needs the producer flatten to compose and the
/// inference fix to bind the outer `ρ`.
#[test]
fn nested_same_handler_discharges_once_and_then_finds_nothing() {
    expect_load(
        "nest_same",
        "  operation t(r: Res) -> Int64\n    effects {Modify[Res]}\n  = handle_Error(lambda () -> handle_Error(lambda () -> may_fail(r)))",
        "handle_Error nested over itself, residual {Modify[Res]}",
    );
}

/// Its control: the residual still propagates through the doubled handler.
#[test]
fn nested_same_handler_does_not_empty_the_row() {
    expect_reject(
        "nest_same_ctl",
        "  operation t(r: Res) -> Int64\n    effects {}\n  = handle_Error(lambda () -> handle_Error(lambda () -> may_fail(r)))",
        &["Modify"],
        "a {} declaration under handle_Error nested over itself",
    );
}

/// A tail shared by TWO parameters takes the UNION of what they force, not whichever
/// argument reached it first. `a` is pure — it constrains `Rho` not at all — while `b`
/// forces `Rho ⊇ {Clock}`; the call's row is `{Clock}`.
///
/// THIS IS A GUARD AGAINST A FIX THAT WAS TRIED AND MEASURED WRONG, not a pin for the
/// shipped one. WI-329's first cut bound the tail inside `unify_effect_rows`' closed/open
/// arm on its FAILING path, which looks free because it is the same `bind_row_tail` the
/// success path makes. It is not: that relation runs once per ARGUMENT with its boolean
/// discarded, so `a` closed `Rho` to `{}` and `b` was then refused — this program stopped
/// loading. It loads under the pre-WI-329 arms and under the shipped
/// `infer_discharged_row_tails`, and fails only under that abandoned cut, which is
/// precisely the regression it exists to catch.
///
/// Two NEIGHBOURING shapes are refused both before and after this ticket and are NOT
/// pinned here: the same `two` at an ERRORING `a` (unify succeeds and closes `Rho` on the
/// success path), and a `two_plain[Rho](a: @{Rho}, b: @{Rho})` with no handled label at
/// all. That is the same eager close one path over, it is pre-existing, and it has an
/// owner — WI-20260820-RDNS4.
#[test]
fn a_tail_shared_by_two_parameters_takes_the_union_of_their_constraints() {
    expect_load(
        "shared_tail",
        "  operation t() -> Int64\n    effects {Clock}\n  = two(lambda () -> pure_body(), lambda () -> clocked())",
    "a row tail shared by a pure parameter and a {Clock} parameter",
    );
}

// ── The explicit row instantiation agrees with the inferred one ───────────────────

/// Writing the tail out by hand reaches the same row: `[Rho = {Modify[Res]}]` is what
/// inference derives in `discharge_drops_the_handled_label`. PASSES EITHER WAY (the
/// explicit shape never depended on the inference arm) — it is here because the
/// DISAGREEMENT between the two spellings is what the inference fix removed, and a test
/// of only the inferred side could not see it.
#[test]
fn an_explicitly_written_residual_tail_is_the_one_inference_derives() {
    expect_load(
        "explicit",
        "  operation t(r: Res) -> Int64\n    effects {Modify[Res]}\n  = handle_Error[Rho = {Modify[Res]}](lambda () -> may_fail(r))",
        "handle_Error[Rho = {Modify[Res]}] over a {Error, Modify} body",
    );
}

/// And a WRONG explicit tail is still refused — the callback row closes to
/// `{Error[Int64], Clock}`, which does not admit the body's `Modify[Res]`.
#[test]
fn a_wrong_explicit_residual_tail_is_refused() {
    expect_reject(
        "explicit_bad",
        "  operation t(r: Res) -> Int64\n    effects {Clock}\n  = handle_Error[Rho = {Clock}](lambda () -> may_fail(r))",
        &["handle_Error", "Modify"],
        "handle_Error[Rho = {Clock}] over a body performing Modify[Res]",
    );
}

// ── What discharge buys WI-701: proposal 054's Branch × External sandwich ─────────
//
// WI-701 ships a BLUNT load-time gate — an operation whose DECLARED row presents both
// `Branch` and `External` is refused, because neither branch-interaction contract is
// available for state the runtime cannot mediate (054 §"Branch and External"). Its
// delivery note names WI-329 as "the follow-on that makes it compositional rather than
// blunt": a solver's `reify` DISCHARGES `Branch`, so `External` becomes legal again at
// exactly the point the search has committed. These three drive that end to end.
//
// ALL THREE PASS UNDER EITHER BACK-OUT — the reified body performs exactly the handled
// label, so neither of this ticket's changes is on their path. They are here for the
// COMPOSITION claim (which nothing else drives), not as back-out detectors.

/// The solver-shaped declarations: a `Branch` body and a `reify` handler that discharges
/// it. Separate from [`DECLS`] because `Branch`/`External` carry WI-701's extra gate and
/// must not join the ordinary discharge fixtures.
const SOLVER_DECLS: &str = r#"
namespace wi329.solver
  import anthill.prelude.{Int64, Branch}

  operation search(x: Int64) -> Int64
    effects {Branch}
  = 41

  operation reify[Rho](body: () -> Int64 @ {Branch, Rho}) -> Int64
    effects {Rho}
  = 0
end
"#;

fn expect_load_solver(src: &str, what: &str) {
    if let Err(errs) = crate::common::try_load_kb_with_files(&[SOLVER_DECLS, src]) {
        panic!("expected {what} to load, got load errors: {errs:#?}");
    }
}

fn expect_reject_solver(src: &str, wants: &[&str], what: &str) {
    match crate::common::try_load_kb_with_files(&[SOLVER_DECLS, src]) {
        Ok(_) => panic!("expected {what} to be REJECTED, but it loaded"),
        Err(errs) => {
            let joined = errs.join("\n");
            for want in wants {
                assert!(
                    joined.contains(want),
                    "expected the rejection of {what} to mention {want:?}, got:\n{joined}"
                );
            }
        }
    }
}

/// The un-discharged floor is unchanged: declaring both labels on one operation is still
/// WI-701's blunt refusal. Discharge does not weaken it.
#[test]
fn declaring_branch_and_external_together_is_still_refused() {
    expect_reject_solver(
        r#"
namespace wi329.be_both
  import anthill.prelude.{Int64, Branch, External}
  operation bad() -> Int64 effects {Branch, External} = 1
end
"#,
        &["Branch", "External"],
        "an operation declaring both Branch and External",
    );
}

/// The sound idiom: search over tracked state, then write the world AFTER the commit.
/// `reify` discharges `Branch`, so the enclosing operation declares `{External}` alone
/// and WI-701's gate has nothing to fire on — the blunt co-occurrence check becomes
/// compositional without changing.
#[test]
fn external_is_legal_again_after_branch_is_discharged() {
    expect_load_solver(
        r#"
namespace wi329.be_ok
  import anthill.prelude.{Int64, External}
  import wi329.solver.{search, reify}

  operation write_world(x: Int64) -> Int64 effects {External} = x

  operation sandwich(x: Int64) -> Int64
    effects {External}
  = write_world(reify(lambda () -> search(x)))
end
"#,
        "External written after reify discharged Branch",
    );
}

/// The control that makes the above mean something: WITHOUT the reify, `Branch` escapes
/// into an operation declaring `{External}` and the load fails. So the sandwich loads
/// because the discharge happened, not because `Branch` was never there.
#[test]
fn an_undischarged_branch_cannot_reach_an_external_operation() {
    expect_reject_solver(
        r#"
namespace wi329.be_bad
  import anthill.prelude.{Int64, External}
  import wi329.solver.{search}

  operation write_world(x: Int64) -> Int64 effects {External} = x

  operation bad_sandwich(x: Int64) -> Int64
    effects {External}
  = write_world(search(x))
end
"#,
        &["undeclared effect", "Branch"],
        "External written under an UNdischarged Branch",
    );
}

// ── The discharged program RUNS ───────────────────────────────────────────────────

/// Loading is the whole of WI-329's capability (the runtime handler is 027), but a
/// program whose row only type-checks is worth little — so drive one through the
/// evaluator. `handle_Error`'s stand-in body returns `0`, and `run_handled` declares the
/// discharged `{}` row. PASSES EITHER WAY by design: the body performs exactly the
/// handled label, so neither change is on its path.
#[test]
fn a_program_whose_row_was_discharged_evaluates() {
    let src = consumer(
        "eval",
        "  operation run_handled() -> Int64\n    effects {}\n  = handle_Error(lambda () -> only_fails())",
    );
    let mut interp = crate::common::interp_for_files(&[DECLS, &src]);
    let got = interp
        .call("wi329.c_eval.run_handled", &[])
        .unwrap_or_else(|e| panic!("call run_handled: {e:?}"));
    assert_eq!(
        got.as_int(),
        Some(0),
        "handle_Error's stand-in body returns 0"
    );
}
