//! Γ's answer about a goal is THREE-VALUED, and `prove_from_gamma`'s bool folds two
//! of the three together.
//!
//! `prove_from_gamma` answers "did Γ derive this", so a goal Γ REFUTES and a goal Γ
//! cannot DECIDE both come back `false`. The fold is safe — an undecided guard does
//! not fire, the conservative direction — but the two need opposite repairs, and only
//! one of them is a repair at all: an `ensures` conjunct over an operation PARAMETER
//! is not "underivable from the body", it is undecided, because the parameter is
//! universally quantified and closed-world absence is not its negation (proposal 050 /
//! WI-067). Telling that author to fix a body that is not wrong is the defect.
//!
//! `prove_from_gamma_verdict` un-folds it, reading the resolver's new
//! `BuiltinResult::Unknown` / `Solution::undecided` channel — which exists because a
//! builtin could previously answer only Success / Delay / Failure, so the open-world
//! case was faked as a `force_delay` that could never be discharged and arrived at the
//! drain byte-identical to a genuine flounder.
//!
//! CONTROLS, and what each measures. Back out the split — make
//! `prove_from_gamma_verdict` return `Refuted` wherever it now returns `Undecided`,
//! which is exactly what the bool did — and:
//!   * `an_open_world_parameter_goal_is_undecided` FAILS. It is the only row that
//!     distinguishes the two verdicts, and it is the whole point of the change.
//!   * `a_ground_false_goal_is_refuted` PASSES EITHER WAY, by design: it is the row
//!     that says `Undecided` has not swallowed the refutation case. A change that
//!     returned `Undecided` for everything would satisfy the first row and fail this
//!     one, which is why both are needed. It also pins `Refuted`'s STRICTNESS — the
//!     verdict is reserved for a COMPLETE search with no answers at all, so a
//!     floundered or depth-truncated non-answer must not arrive here.
//!   * `a_ground_true_goal_is_proved` PASSES EITHER WAY, by design: the fast path is
//!     byte-identical to `prove_from_gamma`'s, and this pins that adding the second
//!     resolve did not disturb it.
//!
//! The open-world producer itself is driven here too, not merely declared: the goal
//! reaches `value_has_open_world_ref` through the loader's real `Expr::Proof`
//! occurrence, the same pair the typer calls (`in_body_proof_goal` +
//! the prover), under the same empty Γ a body-entry proof sees.

use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};
use anthill_core::kb::typing::{
    in_body_proof_goal, prove_from_gamma, prove_from_gamma_verdict, FlowEnv, GammaVerdict,
};

fn src(ns: &str, goal: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, PartialEq}}
  import anthill.prelude.PartialEq.{{eq, neq}}

  operation caller(n: Int64) -> Int64 =
    proof h by derivation conclude {goal} end
    0
end
"#
    )
}

/// Load the fixture, take the `Expr::Proof` the loader built, and run the typer's own
/// pair on it — the `pub` helpers the typer calls, not a re-spelling of them.
fn verdict(ns: &str, goal: &str) -> GammaVerdict {
    let source = src(ns, goal);
    let mut kb = crate::common::load_kb_with(&source);
    let caller = kb
        .try_resolve_symbol(&format!("{ns}.caller"))
        .expect("caller symbol");
    let body = kb.op_body_node(caller).expect("caller body node");
    let Some(Expr::Proof {
        target, conclude, ..
    }) = body.as_expr()
    else {
        panic!("caller body is not Expr::Proof: {:?}", body.as_expr());
    };
    let (target, conclude) = (*target, conclude.clone());
    let goal_v = in_body_proof_goal(&mut kb, target, conclude.as_ref());
    prove_from_gamma_verdict(&mut kb, &FlowEnv::empty(), &goal_v)
}

/// The same fixture through the BOOL bridge, to show what it collapses.
fn proves(ns: &str, goal: &str) -> bool {
    let source = src(ns, goal);
    let mut kb = crate::common::load_kb_with(&source);
    let caller = kb
        .try_resolve_symbol(&format!("{ns}.caller"))
        .expect("caller symbol");
    let body = kb.op_body_node(caller).expect("caller body node");
    let Some(Expr::Proof {
        target, conclude, ..
    }) = body.as_expr()
    else {
        panic!("caller body is not Expr::Proof");
    };
    let (target, conclude) = (*target, conclude.clone());
    let goal_v = in_body_proof_goal(&mut kb, target, conclude.as_ref());
    prove_from_gamma(&mut kb, &FlowEnv::empty(), &goal_v)
}

#[test]
fn an_open_world_parameter_goal_is_undecided() {
    // `n` is an operation PARAMETER — universally quantified, lowered as a `var_ref`
    // binder reference. `eq(n, 1)` is neither derivable nor refutable: Γ is empty, and
    // the absence of a fact about a universal is not its negation. This is the row the
    // bool cannot express.
    assert_eq!(
        verdict("gv.open", "eq(n, 1)"),
        GammaVerdict::Undecided { universal: true },
        "`eq(n, 1)` over the parameter `n` is UNDECIDED, not refuted — the resolver \
         answers `Unknown{{OpenWorldParameter}}` on it"
    );
}

#[test]
fn a_ground_false_goal_is_refuted() {
    // CONTROL (passes either way by design): nothing here is open-world, so the
    // verdict must be REFUTED. Without this row a change that answered `Undecided`
    // everywhere would look correct.
    assert_eq!(
        verdict("gv.refuted", "eq(1, 2)"),
        GammaVerdict::Refuted,
        "`eq(1, 2)` is ground and false — Γ has everything it needs, so this is a \
         refutation and must not be reported as undecided"
    );
}

#[test]
fn a_ground_true_goal_is_proved() {
    // CONTROL (passes either way by design): the fast path is byte-identical to
    // `prove_from_gamma`'s, and this pins that the added second resolve did not
    // disturb it.
    assert_eq!(
        verdict("gv.proved", "eq(1, 1)"),
        GammaVerdict::Proved,
        "`eq(1, 1)` is ground and true — Γ derives it"
    );
}

#[test]
fn the_bool_bridge_collapses_undecided_onto_refuted() {
    // THE DEFECT, stated as a measurement rather than as prose: the two rows the
    // verdict tells apart are the SAME answer through `prove_from_gamma`. This row is
    // what says the new function is not a rename — it fails if `prove_from_gamma` ever
    // starts distinguishing them, which is the point at which this test's premise (and
    // the reason `prove_from_gamma_verdict` exists) would need revisiting.
    assert!(
        !proves("gv.boolopen", "eq(n, 1)"),
        "the bool bridge answers `false` for the UNDECIDED goal"
    );
    assert!(
        !proves("gv.boolref", "eq(1, 2)"),
        "the bool bridge answers `false` for the REFUTED goal too — one answer, two \
         verdicts, which is what `prove_from_gamma_verdict` un-folds"
    );
}

// ── the AUTHOR-VISIBLE half: opaque skolems ───────────────────────────────────
//
// `discharge_contract_proof` is the delivered consumer. Before this change its
// non-proof branch printed one sentence — "an `ensures` conjunct is not derivable
// from the body" — for refuted, undischarged and undecided alike.
//
// The undecided case there is NOT the `var_ref` one: `proof_verify.rs` maps each
// parameter to "a fresh GROUND skolem constant" so the body grounds to something the
// resolver compares definitely — and it compares it a little too definitely.
// `ensures eq(x, 1)` becomes `eq(c, 1)`, the structural compare says FALSE, and the
// author is told the body does not derive it. Nothing derived OR refuted it: the
// site's own doc calls `c` an EIGENVARIABLE, standing for every input.
//
// MEASURED, and the measurement is why the fix is shaped this way: wiring the message
// against the `var_ref` recognizer alone produced `got: an ensures conjunct is not
// derivable from the body` — the guard never fired, because a skolem is an ordinary
// `Term::Ref`. Hence the registry and the post-verdict reconsideration.
//
// CONTROLS, and what each measures. Back out `reconsider_verdict_over_skolem` (return
// `result` unconditionally) and:
//   * `an_open_world_contract_says_undecided_not_underivable` FAILS — the row the
//     change exists for.
//   * `a_negated_contract_over_a_skolem_is_also_undecided` FAILS, and it is a
//     SEPARATE axis: `neq(c, 1)` fails by turning a wrong SUCCESS into Unknown, where
//     the row above turns a wrong FAILURE into one. A fix that only converted
//     `Failure` would pass the first and fail this.
//   * `a_discharging_contract_is_unaffected` PASSES EITHER WAY under that back-out,
//     by design — but it is the row that catches the two WRONG shapes of this fix, and
//     both were tried: widening `value_has_open_world_ref` to skolems (suppresses
//     `eq(c, c)` before dispatch), and comparing the GOAL's operands for structural
//     identity (the projection in `eq(box(value: c).value, c)` has not reduced yet).
//     It failed under the second, which is how the polarity rule was arrived at.

fn contract_verdict(src: &str, suffix: &str) -> ProofVerdict {
    let mut kb = crate::common::load_kb_with(src);
    let report = verify_proofs(&mut kb);
    report
        .iter()
        .find(|r| r.rule_qn.ends_with(suffix))
        .unwrap_or_else(|| panic!("no proof-report entry ending in `{suffix}`"))
        .verdict
        .clone()
}

fn contract_src(ns: &str, ensures: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Box
    entity box(value: Int64)
    operation wrap(x: Int64) -> Box
      ensures {ensures}
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#
    )
}

fn failure_reason(ns: &str, ensures: &str) -> String {
    match contract_verdict(&contract_src(ns, ensures), "wrap.ensures") {
        ProofVerdict::Failed { reason } => reason,
        other => panic!("expected Failed for `ensures {ensures}`, got {other:?}"),
    }
}

#[test]
fn an_open_world_contract_says_undecided_not_underivable() {
    // A wrong FAILURE becomes Unknown: `eq(c, 1)` compares false structurally, but `c`
    // is an eigenvariable and nothing decided it.
    let reason = failure_reason("gv.ct.open", "eq(x, 1)");
    assert!(
        reason.contains("could not be DECIDED"),
        "must report the UNDECIDED wording; got: {reason}"
    );
    assert!(
        !reason.contains("is not derivable from the body"),
        "must not borrow the refutation wording, which names a repair that does not \
         exist for a universal; got: {reason}"
    );
    assert!(
        reason.contains("Either the body does not establish the conjunct"),
        "must name BOTH readings rather than reassure the author; got: {reason}"
    );
}

#[test]
fn a_negated_contract_over_a_skolem_is_also_undecided() {
    // THE OTHER DIRECTION, and its own axis: `neq(c, 1)` SUCCEEDS structurally — `c`
    // is not the literal `1` — but `c` might BE 1, so the success is as wrong as the
    // failure above. A fix that only reconsidered `Failure` passes the row above and
    // fails this one.
    let reason = failure_reason("gv.ct.neg", "neq(x, 1)");
    assert!(
        reason.contains("could not be DECIDED"),
        "a structurally-successful `neq` over an eigenvariable is undecided too, and \
         must not discharge the contract; got: {reason}"
    );
}

#[test]
fn a_discharging_contract_is_unaffected() {
    // CONTROL (passes either way by design): the reflexivity carve-out. `eq(result.value,
    // x)` projects to `eq(c, c)`, which holds for every `c`, so the contract still
    // discharges. This is the row that fails if the recognizer is widened to suppress
    // every skolem-mentioning goal before dispatch.
    let v = contract_verdict(
        &contract_src("gv.ct.ok", "eq(result.value, x)"),
        "wrap.ensures",
    );
    assert!(
        matches!(v, ProofVerdict::Discharged),
        "`eq(result.value, x)` projects to `eq(c, c)` and must still discharge; got {v:?}"
    );
}

// ── the MULTI-GOAL frame channel ──────────────────────────────────────────────
//
// Every row above resolves a goal that is the ONLY goal in its frame, so each takes
// `step_init`'s `goals.len() == 1` shortcut: it yields its `Solution` on the spot,
// carrying the cause directly. That path exercises none of the machinery that exists
// for the other case — `ResolverFrame::undecided`, `record_undecided_on_frame`, the
// `consecutive_delays >= goals.len()` gate's `frame.undecided.clone()`, and
// `step_naf`'s cause plumbing were ALL dead in the corpus, measured by probe.
//
// A rule body puts two goals in one frame. Both mention parameters, so both answer
// `Unknown` and both ROTATE: the first records and rotates (cd=1), the second records
// and rotates (cd=2), and `cd >= goals.len()` then fires the gate — which is the only
// site that reads the frame's list.
//
// WHAT IT DISCRIMINATES, and why the assertion is on `universal` rather than on
// "failed": if the frame channel is dead, the gate still yields a Solution whose
// `residual` holds both goals — it just has an EMPTY `undecided`. That is
// `Undecided { universal: false }`, the "delayed on a variable nothing bound" reading,
// for the case this whole change exists to tell apart. So the row fails with the wrong
// verdict rather than with no answer, which is exactly the confusion being tested.

fn multi_goal_verdict(ns: &str) -> GammaVerdict {
    let source = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, PartialEq}}
  import anthill.prelude.PartialEq.{{eq}}

  rule two_goals(?x, ?y) :- eq(?x, 1), eq(?y, 2)

  operation caller(n: Int64, m: Int64) -> Int64 =
    proof h by derivation conclude two_goals(n, m) end
    0
end
"#
    );
    let mut kb = crate::common::load_kb_with(&source);
    let caller = kb
        .try_resolve_symbol(&format!("{ns}.caller"))
        .expect("caller symbol");
    let body = kb.op_body_node(caller).expect("caller body node");
    let Some(Expr::Proof {
        target, conclude, ..
    }) = body.as_expr()
    else {
        panic!("caller body is not Expr::Proof: {:?}", body.as_expr());
    };
    let (target, conclude) = (*target, conclude.clone());
    let goal_v = in_body_proof_goal(&mut kb, target, conclude.as_ref());
    prove_from_gamma_verdict(&mut kb, &FlowEnv::empty(), &goal_v)
}

#[test]
fn an_undecided_goal_survives_rotation_in_a_multi_goal_frame() {
    assert_eq!(
        multi_goal_verdict("gv.multi"),
        GammaVerdict::Undecided { universal: true },
        "both body goals answer `Unknown` and ROTATE, so the cause reaches the drain \
         only through `ResolverFrame::undecided`. A dead frame channel yields the same \
         residual with an empty `undecided` — i.e. `universal: false`, the wrong verdict"
    );
}

#[test]
fn a_negated_contract_goal_over_a_skolem_carries_its_cause_through_naf() {
    // `not(P)` takes a DIFFERENT route than the rows above: `step_naf` sub-resolves `P`
    // and reads the result through `DrainVerdict`, which had only `residual: bool`. The
    // inner `eq(c, 1)` answers `Unknown` correctly and residualizes correctly — and the
    // cause died at the drain, so the goal came out wearing the flounder wording.
    //
    // The pre-existing note at that yield blamed a narrower cause ("an open-world ref
    // reached through a RULE BODY"), on the theory that `open_world_param` covers
    // anything present in `inner`. It does not: that gate tests `value_has_open_world_ref`
    // only, so a SKOLEM in `inner` walks past it into the ground branch. This row is the
    // shape that note said could not reach it.
    //
    // CONTROL: back out `DrainVerdict::undecided` (drop the field's population in
    // `drain_verdict`) and this row alone fails, with the UNDISCHARGED wording — the
    // other skolem rows go through the builtin path and are unaffected.
    let reason = failure_reason("gv.ct.naf", "not(eq(x, 1))");
    assert!(
        reason.contains("could not be DECIDED"),
        "a negated goal over an eigenvariable is undecided too, and must not borrow the \
         flounder wording; got: {reason}"
    );
    assert!(
        !reason.contains("left UNDISCHARGED"),
        "`not(eq(c, 1))` did not delay on an unbound variable — nothing will ever bind \
         an eigenvariable; got: {reason}"
    );
}

#[test]
fn an_ordering_contract_over_a_skolem_reports_the_resolver_s_fault() {
    // THE ORDERING FAMILY takes neither route the rows above take. It is excluded from
    // `skolem_verdict_is_value_dependent` on purpose — the polarity rule needs one
    // verdict per tag meaning "the operands reduced to the same thing", and `gt` has
    // none (`gt(c, c)` is false, but so is `gt(1, 2)`). So `gt(c, 0)` never reaches the
    // skolem reconsideration at all.
    //
    // What it reaches is `builtin_cmp`'s NO-ORDER arm: `c` is a `Term::Ref`, not an
    // ordered literal, so `value_ord` has nothing to compare. That arm reports a FAULT.
    //
    // MEASURED BEFORE THIS ROW EXISTED, and it is why the row exists: the fault was
    // dropped (`prove_from_gamma_verdict` drained with `resolve_goals_with_truncation`,
    // which returns no errors) and the residual read as an ordinary flounder — the
    // author was told the conjunct "was left UNDISCHARGED … having delayed on a variable
    // nothing bound", when nothing had delayed. "Bind what it waits on" is advice no
    // binding can satisfy.
    //
    // CONTROL: back out `GammaVerdict::Faulted` (drop the `stats.errors` read) and this
    // row alone fails, with that flounder wording. Every other row here goes through the
    // equality family and never produces a `ResolveError`.
    let src = r#"
namespace gv.ord
  import anthill.prelude.{Int64, Bool, PartialOrd}
  import anthill.prelude.PartialOrd.{gt}
  sort Box
    entity box(value: Int64)
    operation wrap(x: Int64) -> Box
      ensures gt(x, 0)
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#;
    let ProofVerdict::Failed { reason } = contract_verdict(src, "wrap.ensures") else {
        panic!("an ordering `ensures` over a parameter cannot discharge");
    };
    assert!(
        reason.contains("could not be EVALUATED"),
        "must report the resolver's FAULT, not a flounder; got: {reason}"
    );
    assert!(
        reason.contains("no order for this operand pair"),
        "and must carry the resolver's own words, which name the operand pair — the \
         whole point of the error channel; got: {reason}"
    );
    assert!(
        !reason.contains("Bind what it waits on"),
        "nothing was waiting on a binding; got: {reason}"
    );
}

#[test]
fn a_verdict_the_skolem_did_not_decide_is_left_alone() {
    // THE OVER-APPROXIMATION THIS ROW EXISTS FOR. The reconsideration gate asks "does
    // this goal MENTION a skolem", but the polarity rule's justification is about the
    // skolem being the operand the verdict TURNED ON. A comparison settled by the head
    // CONSTRUCTOR mentions the skolem and is not decided by it.
    //
    // `neq(box(value: c), nil)` succeeds because `box` and `nil` are different
    // constructors — true for every `c`, so the success is forced and must stand.
    // Flipping it to `Unknown` un-discharges a contract that has always discharged.
    let src = r#"
namespace gv.headctor
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq, neq}
  sort Box
    entity box(value: Int64)
    entity nil
    operation wrap(x: Int64) -> Box
      ensures neq(result, nil)
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#;
    let v = contract_verdict(src, "wrap.ensures");
    assert!(
        matches!(v, ProofVerdict::Discharged),
        "`neq(box(value: c), nil)` is decided by the CONSTRUCTORS, not by `c` — the \
         skolem reconsideration must not touch it; got {v:?}"
    );
}

#[test]
fn a_fault_inside_a_negation_comes_up_through_the_sub_search() {
    // `not(P)` drains a SUB-STREAM and reads it through `DrainVerdict`, which carried
    // `truncated` and `undecided` across that boundary but not `errors` — so a fault
    // raised inside `P` was recorded on the sub-stream and dropped with it.
    //
    // `not(gt(x, 1))` over an eigenvariable: the inner `gt(c, 1)` hits the no-order arm
    // (`c` is a `Term::Ref`, not an ordered literal) and reports a fault. Without the
    // fold, `prove_from_gamma_verdict` sees `stats.errors == []` and falls through to
    // the generic "left UNDISCHARGED / bind what it waits on" wording — a repair no
    // binding can perform.
    //
    // CONTROL: drop the `for err in v.errors` fold in `step_naf` and this row alone
    // fails; `an_ordering_contract_over_a_skolem_reports_the_resolver_s_fault` uses the
    // same arm WITHOUT a negation and so never crosses the sub-search boundary.
    let src = r#"
namespace gv.naforder
  import anthill.prelude.{Int64, Bool, PartialOrd}
  import anthill.prelude.PartialOrd.{gt}
  import anthill.kernel.{not}
  sort Box
    entity box(value: Int64)
    operation wrap(x: Int64) -> Box
      ensures not(gt(x, 1))
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#;
    let ProofVerdict::Failed { reason } = contract_verdict(src, "wrap.ensures") else {
        panic!("a negated ordering `ensures` over a parameter cannot discharge");
    };
    assert!(
        reason.contains("could not be EVALUATED"),
        "the fault must cross the `not(…)` sub-search boundary; got: {reason}"
    );
    assert!(
        !reason.contains("Bind what it waits on"),
        "nothing was waiting on a binding; got: {reason}"
    );
}

#[test]
fn a_named_field_difference_is_skolem_free_too() {
    // THE SAME DEFECT AS `a_verdict_the_skolem_did_not_decide_is_left_alone`, one level
    // down — and this is the COMMON case, not the exotic one: anthill entities are
    // NAMED-argument carriers, so a same-constructor pair has `pos_arity == 0` and a
    // walk that only iterates positional children finds nothing to compare and reports
    // "no skolem-free difference" for every one of them.
    //
    // `neq(pair(a: c, b: 3), pair(a: 1, b: 2))` is true for every `c` — field `b` is 3
    // against 2 — so the success is forced and the contract must discharge.
    let src = r#"
namespace gv.named
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq, neq}
  sort Pair
    entity pair(a: Int64, b: Int64)
    operation mk(x: Int64) -> Pair
      ensures neq(result, pair(a: 1, b: 2))
      = pair(a: x, b: 3)
    proof mk.ensures by derivation end
  end
end
"#;
    let v = contract_verdict(src, "mk.ensures");
    assert!(
        matches!(v, ProofVerdict::Discharged),
        "field `b` differs 3 vs 2 with no skolem in sight, so `neq` is forced; got {v:?}"
    );
}

/// THE PROJECTION TABLE. `difference_is_skolem_free` second-guesses a verdict the
/// builtin produced AFTER folding projections and op-calls, but walked the goal's RAW
/// operands — so `box(value: c).value` arrived as a `dot_apply` node against a `Const`,
/// the heads differed, and the pair was called a skolem-free difference. The
/// closed-world verdict then stood.
///
/// `neq(result.value, 1)` on `wrap(x) = box(value: x)` is FALSE for `wrap(1)`, and it
/// reported **Discharged** — an unsound contract discharge, which is the one outcome
/// this whole change exists to prevent.
///
/// The `skolem_verdict_is_value_dependent` doc records making exactly this mistake once
/// already ("the PROJECTION is reduced inside the builtin"); this is the same mistake
/// repeated at the second gate.
fn projection_row(ensures: &str) -> ProofVerdict {
    let src = format!(
        r#"
namespace gv.proj{n}
  import anthill.prelude.{{Int64, Bool, PartialEq}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Box
    entity box(value: Int64)
    operation wrap(x: Int64) -> Box
      ensures {ensures}
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#,
        n = ensures.len(),
        ensures = ensures
    );
    contract_verdict(&src, "wrap.ensures")
}

fn undecided_reason(v: &ProofVerdict) -> bool {
    matches!(v, ProofVerdict::Failed { reason } if reason.contains("could not be DECIDED"))
}

#[test]
fn a_skolem_behind_a_projection_is_still_the_skolem() {
    // The two rows that were WRONG. Both are about `c` and neither may be decided.
    let neq_proj = projection_row("neq(result.value, 1)");
    assert!(
        undecided_reason(&neq_proj),
        "`neq(box(value: c).value, 1)` reduces to `neq(c, 1)` — FALSE for wrap(1), so \
         discharging it is unsound; got {neq_proj:?}"
    );
    let eq_proj = projection_row("eq(result.value, 1)");
    assert!(
        undecided_reason(&eq_proj),
        "`eq(box(value: c).value, 1)` reduces to `eq(c, 1)` — undecided, not refuted; \
         got {eq_proj:?}"
    );
}

#[test]
fn the_unprojected_rows_are_unchanged() {
    // CONTROLS (passed before this fix and must keep passing): the same comparisons
    // without a projection, which reach the walk already reduced.
    for e in ["neq(x, 1)", "eq(x, 1)", "neq(result, box(value: 1))"] {
        let v = projection_row(e);
        assert!(undecided_reason(&v), "`{e}` must stay undecided; got {v:?}");
    }
}
