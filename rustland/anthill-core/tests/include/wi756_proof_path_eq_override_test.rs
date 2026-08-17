//! WI-756 (WI-502 consumer) — the PROOF-OBLIGATION `prove_from_gamma` sites
//! must decide `eq`/`neq` over a carrier with its OWN equality SEMANTICALLY,
//! never by the structural comparison.
//!
//! WI-573 gated only the guard-REFUTATION route (`refute_guard` →
//! `conjunct_refuted`, whose floor suspended an `eq`-family conjunct whose
//! operands reach an overriding carrier; WI-755 has since retired that gate — see
//! the `*_rule_body_refutation_*` section). The other three `prove_from_gamma`
//! call sites never passed through it:
//!
//!   1. `typing.rs` `Expr::Proof` — WI-538's in-body `proof … by derivation`;
//!   2. `typing.rs` `precondition_proved` — WI-539's call-site `requires`;
//!   3. `proof_verify.rs` `discharge_contract_proof` — WI-558's contract
//!      `ensures`.
//!
//! Their polarity is the OPPOSITE of WI-573's: the hazard is not an unsound
//! refutation dropping an effect, it is an unsound PROOF — a precondition deemed
//! satisfied, or an `ensures` conjunct deemed derivable, on a structural verdict
//! the carrier's own `eq` contradicts. Nothing exercised a custom-eq carrier on
//! any of the three.
//!
//! MEASURED HERE, per site: sites 2 and 3 were ALREADY semantic — WI-616 made
//! `eq`/`neq` the resolver's `BuiltinTag::SemEq`/`SemNeq`, and all three sites
//! resolve THROUGH the resolver, so they inherit its dispatch discipline rather
//! than needing a typer gate. Those rows are characterization + regression.
//! Site 1 was NOT: it handed the resolver the RAW `conclude` occurrence, whose
//! bare identifiers op-body lowering wraps as `var_ref` — so the open-world gate
//! read the nullary constructor `Red` as a runtime binder and force-delayed. It
//! decided NOTHING there (not structurally either — conservative, so no unsound
//! proof), and no in-body proof over a bare constructor could discharge at all,
//! not even the reflexive `conclude eq(Red, Red)`. WI-756 routes that goal
//! through the goal-lowering boundary the other two sites already cross
//! (`typing::in_body_proof_goal`); WI-592 is the boundary's own rule that a
//! `var_ref` naming a CONSTRUCTOR is a closed datum.
//!
//! WHY THE FIXTURE IS `eq = true`, and not `eq = false`: the resolver answers
//! REFLEXIVITY before any dispatch (`sem_eq_values` — structurally identical
//! operands are equal under any lawful `Eq`), so an override that disagrees on
//! IDENTICAL operands is not discriminating. The discriminating shape is
//! DISTINCT operands the carrier calls EQUAL: `eq(Green, Red)` is then TRUE and
//! `neq(Green, Red)` FALSE, each the opposite of the structural verdict. Both
//! directions are asserted — `eq` where the structural verdict would REFUSE a
//! sound obligation, `neq` where it would PROVE an unsound one.
//!
//! Putting site 1's goal in that form exposed the OTHER half of the same rule:
//! Γ's producers were still spelling constructors the source way. The last
//! section covers it — `FlowEnv::assume` now normalizes every fact through the
//! same `goal_form`, and two producer channels turn out to have been broken for
//! constructor operands in programs containing no proof at all.
//!
//! CONTROLS. Every `custom_*` row is paired with a `structural_*` row on the
//! same program with the `operation eq` member removed; the pair fails if the
//! override stops being consulted (both rows agree) as much as if it starts
//! being consulted where there is none. MEASURED, not predicted, per half —
//! each half backed out on its own, against these 26 rows:
//!   * back out `in_body_proof_goal`'s lowering (hand the raw `conclude`
//!     occurrence over again) ⇒ 4 fail: `custom_eq_in_body_proof_discharges`,
//!     `structural_carrier_in_body_reflexive_proof_discharges`, the discharging
//!     half of `buried_override_in_body_proof_stays_unproved`, and
//!     `an_in_body_proof_reads_the_gamma_its_producers_write`;
//!   * back out `goal_form` in `FlowEnv::assume` ⇒ 3 fail:
//!     `if_premise_over_a_constructor_discharges_a_later_requires`,
//!     `let_bound_constructor_discharges_a_later_requires`, and again
//!     `an_in_body_proof_reads_the_gamma_its_producers_write` — the one row that
//!     fails under EITHER back-out, because what it measures is the two halves
//!     AGREEING, which is the whole point of there being one `goal_form`.
//! Everything else passes EITHER WAY, by design and not by accident:
//!   * the site-1 rows that assert a NON-discharge cannot distinguish the fix —
//!     the back-out discharges nothing at all, so it produces their outcome too.
//!     They bound the fix from the other side: it must not make a
//!     structurally-false, a symbolic, or a buried-override conclusion provable;
//!   * every site-2 and site-3 row pins WI-616's behaviour at sites WI-756 did
//!     not touch. They are this file's regression guard, not its measurement:
//!     they fail if a future typer-side gate re-structuralizes those paths;
//!   * the two `*_rule_body_refutation_*` rows pinned the asymmetry WI-755 owned.
//!     WI-755 has since landed and the custom half flipped from ACCEPT to REJECT,
//!     so that pair now measures WI-755 (back out its gate removal and the custom
//!     row loads clean again) rather than WI-756 — see their own section note;
//!   * `match_arm_constructor_...` and `if_premise_over_an_int_literal_...` are
//!     the channels that already worked — see the last section's note.
//!
//! WHAT NOTHING HERE PINS, stated because it is easy to assume otherwise: that
//! the typer's `Expr::Proof` arm CALLS `in_body_proof_goal`. Reverting that one
//! line to the pre-WI-756 inline `Value::Node(conclude)` leaves the whole
//! workspace green (measured), and no test can close that hole behaviourally —
//! the site's only effect is `assume`ing a conclusion into a Γ that already
//! derives it, and `an_in_body_proof_reads_the_gamma_its_producers_write` drives
//! the pair itself rather than through the typer. `wi538_local_proof_test` pins
//! that the arm exists and types, not which goal it builds.

use std::rc::Rc;

use anthill_core::eval::value::Value;
use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::proof_verify::{verify_proofs, ProofReport, ProofVerdict};
use anthill_core::kb::typing::{in_body_proof_goal, prove_from_gamma, FlowEnv};

/// `Color`'s own `eq` holds of ANY two colours, so under this carrier's equality
/// `eq(Green, Red)` is TRUE and `neq(Green, Red)` is FALSE — both the opposite
/// of the structural verdict. The same fixture shape as
/// `wi573_eq_override_discharge_test::CUSTOM_EQ_TRUE_PRELUDE`.
const CUSTOM_EQ: &str = r#"
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = true
  end
"#;

/// The CONTROL carrier: `provides Eq` with no `eq` member, so structural
/// equality IS this carrier's equality and every verdict below flips.
const STRUCTURAL_EQ: &str = r#"
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
  end
"#;

/// Load the stdlib + `src` and keep only the loader's VERDICT — the site-2 rows
/// assert on load errors, never over the KB.
fn load_result(src: &str) -> Result<(), Vec<String>> {
    crate::common::try_load_kb_with(src).map(|_| ())
}

/// The one `UnsatisfiedPrecondition` diagnostic. Matched on BOTH fragments so an
/// unrelated failure that merely mentions `precondition` cannot satisfy it.
fn is_unsatisfied_precondition(errs: &[String], goal_functor: &str) -> bool {
    errs.iter().any(|e| {
        e.contains("unsatisfied precondition")
            && e.contains(&format!("precondition `{goal_functor}`"))
    })
}

// ── site 2: WI-539 call-site `requires` (`precondition_proved`) ─────────────
//
// `needy` carries a value precondition over its `Color` parameter; the caller
// passes `Green`. σ grounds the clause to `<goal>(Green, Red)`, which the
// obligation must PROVE from Γ ∪ KB (`definite_only` — an undecided goal stays
// UNPROVED, the obligation default, never NAF-"satisfied").

fn requires_src(ns: &str, color: &str, goal: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Option}}
  import anthill.prelude.Option.{{some, none}}
{color}
  operation needy(c: Color) -> Int64
    requires {goal}
    = 0

  operation caller() -> Int64 =
    needy(Green)
end
"#
    )
}

#[test]
fn custom_eq_requires_proves_where_structural_would_refuse() {
    // THE positive half. `requires eq(c, Red)` at `needy(Green)`: structurally
    // `Green != Red`, so a structural verdict would leave the obligation
    // UNPROVED and the call would not load. Under `Color.eq = true` the carrier
    // says the two ARE equal, so the precondition is discharged and the program
    // loads clean.
    let res = load_result(&requires_src("wi756.reqeq.custom", CUSTOM_EQ, "eq(c, Red)"));
    assert!(
        res.is_ok(),
        "`Color.eq` holds of `(Green, Red)`, so the call-site precondition \
         `eq(c, Red)` must be PROVED semantically and the program must load; \
         got: {:#?}",
        res.err()
    );
}

#[test]
fn structural_carrier_requires_eq_stays_unproved() {
    // CONTROL for the row above: the SAME program with the `eq` member removed.
    // Structural equality is now this carrier's equality, `eq(Green, Red)` is
    // false, and the obligation is undischarged — a loud error. If this row ever
    // starts loading, the override is being invented where none was declared.
    let errs = load_result(&requires_src(
        "wi756.reqeq.struct",
        STRUCTURAL_EQ,
        "eq(c, Red)",
    ))
    .expect_err(
        "a carrier with NO `eq` override is decided structurally: `eq(Green, Red)` \
         is false, so the precondition is unproved and the call must not load",
    );
    assert!(
        is_unsatisfied_precondition(&errs, "eq"),
        "expected an unsatisfied `eq` precondition; got: {errs:#?}"
    );
}

#[test]
fn custom_eq_requires_refuses_where_structural_would_prove() {
    // THE UNSOUND-PROOF direction — the hazard this ticket names. `requires
    // neq(c, Red)` at `needy(Green)`: structurally `Green != Red` HOLDS, so a
    // structural verdict would PROVE the obligation and wave the call through.
    // Under `Color.eq = true` the carrier calls them equal, so `neq` is FALSE
    // and the precondition must NOT discharge.
    let errs = load_result(&requires_src(
        "wi756.reqneq.custom",
        CUSTOM_EQ,
        "neq(c, Red)",
    ))
    .expect_err(
        "`Color.eq` holds of `(Green, Red)`, so `neq(c, Red)` is FALSE under this \
         carrier's equality; proving it (as the structural verdict would) is the \
         unsound proof WI-756 guards — the call must not load",
    );
    assert!(
        is_unsatisfied_precondition(&errs, "neq"),
        "expected an unsatisfied `neq` precondition; got: {errs:#?}"
    );
}

#[test]
fn structural_carrier_requires_neq_proves() {
    // CONTROL for the row above: without the override, `neq(Green, Red)` IS this
    // carrier's inequality and the obligation discharges. Pairs with
    // `custom_eq_requires_refuses_where_structural_would_prove` to show the
    // refusal there comes from the OVERRIDE and not from `neq` being
    // undischargeable in general.
    let res = load_result(&requires_src(
        "wi756.reqneq.struct",
        STRUCTURAL_EQ,
        "neq(c, Red)",
    ));
    assert!(
        res.is_ok(),
        "a carrier with no override decides `neq(Green, Red)` structurally — TRUE \
         — so the precondition discharges and the program must load; got: {:#?}",
        res.err()
    );
}

#[test]
fn custom_eq_requires_stays_unproved_for_a_symbolic_operand() {
    // The acceptance's NON-GROUND row, at the polarity where it bites: `neq` over
    // a symbolic argument. `caller(c)` forwards its own parameter, so σ leaves the
    // clause over an open-world `var_ref` the resolver DELAYS on, and
    // `definite_only` maps that Delay to UNPROVED — the obligation default —
    // rather than to the structural verdict (which would be TRUE and would
    // wrongly discharge). Not a control for the override: it fails on the
    // structural carrier too, by floundering.
    let src = format!(
        r#"
namespace wi756.reqsymbolic
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq}}
{CUSTOM_EQ}
  operation needy(c: Color) -> Int64
    requires neq(c, Red)
    = 0

  operation caller(c: Color) -> Int64 =
    needy(c)
end
"#
    );
    let errs = load_result(&src).expect_err(
        "a symbolic argument leaves `neq(c, Red)` undecided; `definite_only` keeps \
         it UNPROVED (never structurally decided), so the call must not load",
    );
    assert!(
        is_unsatisfied_precondition(&errs, "neq"),
        "expected an unsatisfied `neq` precondition; got: {errs:#?}"
    );
}

#[test]
fn buried_override_operand_stays_unproved() {
    // The acceptance's BURIED-OVERRIDE row, again at the `neq` polarity where a
    // structural verdict would PROVE. The operands are `Option[Color]`: the top
    // carrier `Option` has no override, so no head dispatch fires, but `Color`'s
    // own `eq` is reachable INSIDE the operand — and the structural comparison
    // recurses into it. `some(Green)` vs `some(Red)` is structurally unequal, so
    // `neq` would prove; the resolver instead SUSPENDS on the reachable override
    // (`value_reaches_eq_override`) and the obligation stays unproved.
    let errs = load_result(&format!(
        r#"
namespace wi756.reqburied.custom
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Option}}
  import anthill.prelude.Option.{{some, none}}
{CUSTOM_EQ}
  operation needy(o: Option[T = Color]) -> Int64
    requires neq(o, some(Red))
    = 0

  operation caller() -> Int64 =
    needy(some(Green))
end
"#
    ))
    .expect_err(
        "a custom `eq` on the ELEMENT carrier of `Option[Color]` makes the \
         structural `neq(some(Green), some(Red))` verdict unsound; the obligation \
         must stay UNPROVED rather than discharge structurally",
    );
    assert!(
        is_unsatisfied_precondition(&errs, "neq"),
        "expected an unsatisfied `neq` precondition; got: {errs:#?}"
    );
}

#[test]
fn structural_carrier_buried_operand_proves() {
    // CONTROL for the row above: the same nesting with NO override anywhere.
    // `neq(some(Green), some(Red))` is decided structurally — TRUE — and the
    // obligation discharges. Without this row the suspension above could equally
    // be "container operands never prove", which would make it measure nothing.
    let res = load_result(&format!(
        r#"
namespace wi756.reqburied.struct
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Option}}
  import anthill.prelude.Option.{{some, none}}
{STRUCTURAL_EQ}
  operation needy(o: Option[T = Color]) -> Int64
    requires neq(o, some(Red))
    = 0

  operation caller() -> Int64 =
    needy(some(Green))
end
"#
    ));
    assert!(
        res.is_ok(),
        "a wholly structural `Option[Color]` decides `neq(some(Green), some(Red))` \
         structurally — TRUE — so the precondition discharges; got: {:#?}",
        res.err()
    );
}

// ── the two POLARITIES of site 2 agree again (WI-755) ──────────────────────
//
// `check_apply_iter` runs BOTH: `precondition_proved` (which reaches the resolver
// and so consults the carrier's `eq`, as every row above shows) and, in RULE-BODY
// context only, `precondition_refuted` (via `conjunct_refuted`). WI-756 measured
// those two DISAGREEING: `conjunct_refuted` sat behind WI-573's pre-gate, which
// suspended every eq-family conjunct over an overriding carrier rather than
// deciding it, so the same call with the same definitely-false precondition was
// REJECTED on a structural carrier and ACCEPTED on an overriding one. WI-756
// recorded that asymmetry here rather than fixing it — its owner was **WI-755**
// (retire the now-stale pre-gate, WI-573's deferred "option (a)").
//
// **WI-755 landed**, so the two rows below now agree: the refutation polarity
// reaches the resolver, `neq(Red, Red)` is refuted by reflexivity under either
// carrier, and both programs are rejected with the same diagnostic. The custom row
// is the one that flips — restore the deleted pre-gate (its call in
// `conjunct_refuted` AND the ~140 lines of helpers removed with it; recover both
// from WI-755's commit) and it loads clean again, which is what makes this pair
// (not just its effect-discharge twin,
// `wi573_eq_override_discharge_test::custom_eq_override_dispatches_and_drops`) a
// measurement of WI-755 rather than a restatement of it.
//
// WI-755 did keep a NARROW residual of that gate, for the one shape the resolver
// cannot see — a carrier whose override is its own `neq`, which keys nothing in an
// `eq`-built dispatch index. It is not what these rows exercise (their carrier
// overrides `eq`), and the proof-side face of that hole predates WI-755 and is
// WI-1125's: a `requires neq(c, Red)` over a `neq`-only carrier PROVES here, and
// did before this file existed. Every fixture above overrides `eq`, which is why
// WI-756 never reached it.

/// A rule-body call to `needy(Red)`, whose precondition `neq(c, Red)` is FALSE
/// under either carrier's own equality — structurally by reflexivity, and under
/// the override for the same reason (`sem_eq_values` answers reflexivity before
/// any dispatch). The ONLY difference between the two programs is the
/// `operation eq` member.
fn rule_body_src(ns: &str, color: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq}}
{color}
  sort Holder
    entity holder(c: Color)
  end

  operation needy(c: Color) -> Int64
    requires neq(c, Red)
    = 0

  rule uses(?r)
    :- holder(c: ?), eq(?r, needy(Red))
end
"#
    )
}

#[test]
fn structural_carrier_rule_body_refutation_rejects() {
    // The refutation polarity, working: `neq(Red, Red)` is unprovable AND
    // constructively refuted (its negation `eq(Red, Red)` proves reflexively), so
    // the rule-body call is a DEFINITE violation and raises — the WI-602 behaviour.
    let errs = load_result(&rule_body_src("wi756.rulebody.struct", STRUCTURAL_EQ)).expect_err(
        "`neq(Red, Red)` is definitely FALSE, so a rule-body call to `needy(Red)` \
         is a decided violation and must be rejected (WI-602)",
    );
    assert!(
        is_unsatisfied_precondition(&errs, "neq"),
        "expected the rule-body precondition violation; got: {errs:#?}"
    );
}

#[test]
fn custom_eq_rule_body_refutation_rejects_too() {
    // THE ASYMMETRY, CLOSED (WI-755). The identical program, plus one `operation
    // eq` member. The precondition is just as definitely false — `Color.eq` is
    // reflexive whatever else it says, so `neq(Red, Red)` is FALSE under this
    // carrier's own equality too — and now `precondition_refuted` asks: with the
    // WI-573 pre-gate gone, the conjunct reaches the resolver, whose `sem_eq_values`
    // answers reflexivity before any dispatch. So the violation is DECIDED and the
    // rule body is rejected, exactly as its structural control is.
    //
    // This row is one of the two WI-755 measures: restore the deleted pre-gate (see
    // the section note for what "restore" involves) and it loads clean again — that
    // WAS its assertion until WI-755, under its old name
    // `custom_eq_rule_body_refutation_is_suspended_by_the_wi573_gate`.
    // `structural_carrier_rule_body_refutation_rejects` passes either way
    // — the gate never fired on a carrier with no override — so it is the control
    // that says the rejection here is about the polarity, not about `neq(Red, Red)`
    // being unrejectable in general.
    let errs = load_result(&rule_body_src("wi756.rulebody.custom", CUSTOM_EQ)).expect_err(
        "`neq(Red, Red)` is definitely FALSE under the override too (reflexivity is \
         answered before dispatch), so the rule-body call to `needy(Red)` is a \
         decided violation and must be rejected — the same verdict as its \
         structural control",
    );
    assert!(
        is_unsatisfied_precondition(&errs, "neq"),
        "expected the rule-body precondition violation over the OVERRIDING \
         carrier; got: {errs:#?}"
    );
}

// ── site 3: WI-558 contract `ensures` (`discharge_contract_proof`) ──────────
//
// `proof pick.ensures by derivation` binds `result` to the op's BODY (`Green`)
// and discharges each predicate `ensures` conjunct from Γ ∪ KB. The verdict is
// written back onto the `ProofRecord`, so it is directly observable.

fn ensures_src(ns: &str, color: &str, goal: &str) -> String {
    contract_src(ns, color, "Color", goal, "Green")
}

/// The same contract, over a chosen return type / body — so the buried-override
/// rows can return `Option[T = Color]` without a second near-copy of the fixture.
fn contract_src(ns: &str, color: &str, ret: &str, goal: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Eq, PartialEq, Option}}
  import anthill.prelude.Option.{{some, none}}
{color}
  operation pick() -> {ret}
    ensures {goal}
    = {body}

  proof pick.ensures by derivation end
end
"#
    )
}

/// The verdict `verify_proofs` reported for `<ns>.pick.ensures`.
fn ensures_verdict(report: &[ProofReport]) -> ProofVerdict {
    let hits: Vec<&ProofReport> = report
        .iter()
        .filter(|r| r.rule_qn.ends_with("pick.ensures"))
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one `pick.ensures` contract record; got {:?}",
        report.iter().map(|r| &r.rule_qn).collect::<Vec<_>>()
    );
    hits[0].verdict.clone()
}

#[test]
fn custom_eq_contract_ensures_discharges() {
    // `ensures eq(result, Red)` with body `Green`. Structurally `Green != Red`,
    // so the conjunct would not be derivable and the contract would FAIL; under
    // `Color.eq = true` it is derivable and the contract discharges.
    let mut kb = crate::common::load_kb_with(&ensures_src(
        "wi756.enseq.custom",
        CUSTOM_EQ,
        "eq(result, Red)",
    ));
    assert_eq!(
        ensures_verdict(&verify_proofs(&mut kb)),
        ProofVerdict::Discharged,
        "`Color.eq` holds of `(Green, Red)`, so the postcondition `eq(result, Red)` \
         IS derivable from the body and the contract must discharge"
    );
}

#[test]
fn structural_carrier_contract_ensures_eq_fails() {
    // CONTROL: the same contract on the override-free carrier. `eq(Green, Red)`
    // is structurally false, so the conjunct is not derivable and the contract
    // fails — the verdict the custom row must differ from.
    let mut kb = crate::common::load_kb_with(&ensures_src(
        "wi756.enseq.struct",
        STRUCTURAL_EQ,
        "eq(result, Red)",
    ));
    assert!(
        matches!(
            ensures_verdict(&verify_proofs(&mut kb)),
            ProofVerdict::Failed { .. }
        ),
        "with no override the postcondition `eq(result, Red)` is structurally false \
         and the contract must FAIL"
    );
}

#[test]
fn custom_eq_contract_ensures_refuses_where_structural_would_discharge() {
    // The UNSOUND-PROOF direction at site 3. `ensures neq(result, Red)` with body
    // `Green`: structurally `Green != Red` holds, so a structural verdict would
    // certify the contract. Under `Color.eq = true` the two are equal, `neq` is
    // false, and the contract must NOT be discharged.
    let mut kb = crate::common::load_kb_with(&ensures_src(
        "wi756.ensneq.custom",
        CUSTOM_EQ,
        "neq(result, Red)",
    ));
    assert!(
        matches!(
            ensures_verdict(&verify_proofs(&mut kb)),
            ProofVerdict::Failed { .. }
        ),
        "`neq(Green, Red)` is FALSE under this carrier's own equality; discharging \
         the contract (as the structural verdict would) is the unsound proof \
         WI-756 guards"
    );
}

#[test]
fn structural_carrier_contract_ensures_neq_discharges() {
    // CONTROL for the row above: without the override, `neq(Green, Red)` is this
    // carrier's inequality and the contract discharges. Pairs with the custom row
    // to show the failure there is the OVERRIDE talking, not `neq` being
    // undischargeable in a contract.
    let mut kb = crate::common::load_kb_with(&ensures_src(
        "wi756.ensneq.struct",
        STRUCTURAL_EQ,
        "neq(result, Red)",
    ));
    assert_eq!(
        ensures_verdict(&verify_proofs(&mut kb)),
        ProofVerdict::Discharged,
        "with no override `neq(Green, Red)` is structurally TRUE, so the contract \
         must discharge"
    );
}

#[test]
fn buried_override_contract_ensures_stays_undischarged() {
    // The BURIED-OVERRIDE row at site 3. `pick() -> Option[T = Color]` returns
    // `some(Green)` and claims `neq(result, some(Red))`. `Option` has no override
    // so nothing dispatches at the head, but `Color`'s own `eq` is reachable
    // INSIDE the operand — which the structural recursion would ignore, decide
    // "unequal", and certify the contract on. The resolver suspends instead, so
    // the conjunct is not derivable and the contract must NOT discharge.
    let mut kb = crate::common::load_kb_with(&contract_src(
        "wi756.ensburied.custom",
        CUSTOM_EQ,
        "Option[T = Color]",
        "neq(result, some(Red))",
        "some(Green)",
    ));
    assert!(
        matches!(
            ensures_verdict(&verify_proofs(&mut kb)),
            ProofVerdict::Failed { .. }
        ),
        "a custom `eq` on the ELEMENT carrier makes the structural \
         `neq(some(Green), some(Red))` verdict unsound; the contract must stay \
         undischarged rather than be certified structurally"
    );
}

#[test]
fn structural_carrier_buried_contract_ensures_discharges() {
    // CONTROL for the row above: the same nesting with no override anywhere is
    // decided structurally — `neq(some(Green), some(Red))` is TRUE — and the
    // contract discharges. Without it the suspension above could equally be
    // "a container postcondition never discharges".
    let mut kb = crate::common::load_kb_with(&contract_src(
        "wi756.ensburied.struct",
        STRUCTURAL_EQ,
        "Option[T = Color]",
        "neq(result, some(Red))",
        "some(Green)",
    ));
    assert_eq!(
        ensures_verdict(&verify_proofs(&mut kb)),
        ProofVerdict::Discharged,
        "a wholly structural `Option[Color]` decides the postcondition \
         structurally — TRUE — so the contract must discharge"
    );
}

// ── site 1: WI-538 in-body `proof … by derivation` ─────────────────────────
//
// WHY THESE ROWS DRIVE `in_body_proof_goal` + `prove_from_gamma` RATHER THAN
// ASSERTING ON THE LOAD: the site's only effect is to `assume` a discharged
// conclusion into the typer's transient Γ, and Γ is never stored. That
// assumption has NO end-to-end observable either — Γ ⊆ what KB ∪ Γ already
// derives at that point, so every downstream `prove_from_gamma` (a call-site
// `requires`, a guard discharge) re-derives the conclusion on its own whether or
// not the proof discharged. So these drive the site's OWN goal construction (the
// `pub` helper the typer calls, not a re-spelling of it) against the site's own
// prover, on the `Expr::Proof` occurrence the loader actually built, under the
// same empty Γ a body-entry proof sees. What they do NOT cover is the typer's
// wiring of that pair — see the header's "what nothing here pins"; it is not a
// gap another test could close.

fn inbody_src(ns: &str, color: &str, goal: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Option}}
  import anthill.prelude.Option.{{some, none}}
{color}
  operation caller(c: Color) -> Int64 =
    proof h by derivation conclude {goal} end
    0
end
"#
    )
}

fn inbody_discharges(ns: &str, color: &str, goal: &str) -> bool {
    discharges_conclude(&inbody_src(ns, color, goal), ns)
}

/// Load `src`, take the `Expr::Proof` the loader built for `<ns>.caller`, and
/// run the site's own pair — `in_body_proof_goal` then `prove_from_gamma` under
/// the empty Γ — returning the discharge verdict.
fn discharges_conclude(src: &str, ns: &str) -> bool {
    let mut kb = crate::common::load_kb_with(src);
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
    let goal = in_body_proof_goal(&mut kb, target, conclude.as_ref());
    prove_from_gamma(&mut kb, &FlowEnv::empty(), &goal)
}

#[test]
fn custom_eq_in_body_proof_discharges() {
    // `conclude eq(Green, Red)` over the custom carrier: TRUE under `Color.eq`,
    // false structurally. Fails (false) if WI-756's goal lowering is backed out —
    // the raw occurrence's `var_ref`-wrapped constructors force-delay.
    assert!(
        inbody_discharges("wi756.inbeq.custom", CUSTOM_EQ, "eq(Green, Red)"),
        "`Color.eq` holds of `(Green, Red)`, so the in-body `by derivation` proof \
         of `eq(Green, Red)` must discharge"
    );
}

#[test]
fn structural_carrier_in_body_proof_does_not_discharge() {
    // CONTROL: the same proof on the override-free carrier is structurally false
    // and must NOT discharge. Without it the row above would also pass if the
    // site started proving every `eq` goal.
    assert!(
        !inbody_discharges("wi756.inbeq.struct", STRUCTURAL_EQ, "eq(Green, Red)"),
        "with no override `eq(Green, Red)` is structurally FALSE — the in-body \
         proof must not discharge"
    );
}

#[test]
fn structural_carrier_in_body_reflexive_proof_discharges() {
    // The WI-756 lowering itself, measured WITHOUT any override: `conclude
    // eq(Red, Red)` is reflexively true on the plain structural carrier, and
    // before WI-756 it still did not discharge — the constructor operands rode as
    // `var_ref` and force-delayed. So this row isolates the goal-lowering fix from
    // the override question entirely; it flips to false on a back-out.
    assert!(
        inbody_discharges("wi756.inbrefl", STRUCTURAL_EQ, "eq(Red, Red)"),
        "a bare nullary constructor is a closed datum (WI-592): the reflexive \
         `conclude eq(Red, Red)` must discharge"
    );
}

#[test]
fn buried_override_in_body_proof_stays_unproved() {
    // The BURIED-OVERRIDE row at site 1. `conclude neq(some(Green), some(Red))`:
    // structurally TRUE (so the raw structural verdict would discharge it and
    // then `assume` it into Γ), but `Color`'s `eq` is reachable inside both
    // operands, so the resolver suspends and the proof must not discharge.
    assert!(
        !inbody_discharges(
            "wi756.inbburied.custom",
            CUSTOM_EQ,
            "neq(some(Green), some(Red))"
        ),
        "a custom `eq` on the ELEMENT carrier makes the structural verdict \
         unsound; the in-body proof must not discharge on it"
    );
    // CONTROL: with no override the same conclusion IS structurally decided and
    // the proof discharges — so the suspension above is the override talking,
    // not "a container conclusion never discharges". (This row also fails on a
    // back-out of the WI-756 lowering, for the constructor reason.)
    assert!(
        inbody_discharges(
            "wi756.inbburied.struct",
            STRUCTURAL_EQ,
            "neq(some(Green), some(Red))"
        ),
        "with no override anywhere, `neq(some(Green), some(Red))` is structurally \
         TRUE and the in-body proof must discharge"
    );
}

#[test]
fn a_conclude_that_is_not_a_goal_shape_stays_unlowered_and_unproved() {
    // The `None` arm of the lowering, DRIVEN. `conclude` takes a full `_term`,
    // which admits an args-bearing dot (`?c.same(Red)`) — and the goal is built
    // BEFORE the conclude's children are visited, so no dot dispatch has run on
    // it yet. That shape is deliberately not reifiable (`try_occurrence_to_term`
    // returns `None`; its doc calls the `None` arms back-pressure and says not to
    // "finish" them), so the goal rides on unlowered and simply does not
    // discharge — the same conservative outcome an unprovable goal gets.
    // CONTROL: this row is why the lowering calls `try_occurrence_to_term` and
    // not the asserting `occurrence_to_term`. MEASURED with the latter swapped
    // in: this row — and only this row of the 21 — fails, panicking at
    // `node_occurrence.rs`'s `occurrence_to_term: unexpected non-goal Expr`
    // during typing. Legal source, turned into a crash.
    let src = r#"
namespace wi756.inbnongoal
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = true
    operation same(a: Color, b: Color) -> Bool = true
  end

  operation caller(c: Color) -> Int64 =
    proof h by derivation conclude ?c.same(Red) end
    0
end
"#;
    assert!(
        !discharges_conclude(src, "wi756.inbnongoal"),
        "a non-goal `conclude` must stay undischarged, not be proved"
    );
}

#[test]
fn in_body_proof_over_a_binder_stays_unproved() {
    // The open-world floor the lowering must NOT erode: `c` is a runtime
    // parameter, so `conclude eq(c, Red)` lowers to a genuine `var_ref` and
    // FLOUNDERS — undischarged, on the custom carrier as much as the structural
    // one. This is the row that fails if the WI-756 lowering ever strips binders
    // as well as constructors (which would make a symbolic conclusion provable and
    // then assumable into Γ — an unsound proof).
    assert!(
        !inbody_discharges("wi756.inbbinder.custom", CUSTOM_EQ, "eq(c, Red)"),
        "`c` is an open-world parameter: `eq(c, Red)` must flounder, not discharge, \
         even where the carrier's `eq` holds of every ground pair"
    );
    assert!(
        !inbody_discharges("wi756.inbbinder.struct", STRUCTURAL_EQ, "eq(c, Red)"),
        "the same flounder on the override-free carrier"
    );
}

// ── the Γ VOCABULARY: producers and consumers must spell a constructor alike ──
//
// Routing site 1's goal through the goal-lowering boundary was only half the
// rule. Γ's PRODUCERS carry a raw source occurrence — an `if` condition, a `let`
// binding's value, a `match` arm's pattern — and the overlay is consulted
// STRUCTURALLY, ahead of the builtin (`resolve.rs`'s `gamma_candidates_for`), so
// a fact spelling `Red` as `var_ref` cannot discharge a goal spelling it `Ref`.
// `FlowEnv::assume` now normalizes every fact through the same `goal_form`, so
// the two sides share one vocabulary by construction rather than by agreement.
//
// This was NOT only a consequence of WI-756's goal change: two of the three
// producer channels were already broken for CONSTRUCTOR operands, in programs
// with no proof in them at all. MEASURED by backing `goal_form` out of `assume`:
// `if_premise_over_a_constructor_discharges_a_later_requires` and
// `let_bound_constructor_discharges_a_later_requires` FAIL (unsatisfied
// precondition); `match_arm_constructor_discharges_a_later_requires` and
// `if_premise_over_an_int_literal_still_discharges` pass either way — the match
// arm's fact builder already spelled its constructor as a closed datum, and the
// Int literal never had the two spellings to confuse. The last two are what say
// the fix did not invent the capability, only spread it.

/// `needy` requires `eq(c, Red)` — a precondition over a CONSTRUCTOR that only a
/// Γ fact can discharge, since `c` is symbolic and the goal flounders in the KB.
const NEEDY_COLOR: &str = r#"
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
  end
  operation needy(c: Color) -> Int64
    requires eq(c, Red)
    = 0
"#;

#[test]
fn if_premise_over_a_constructor_discharges_a_later_requires() {
    // The WI-539 `precondition_proved_by_if_guard` shape with a CONSTRUCTOR
    // operand instead of an Int literal: the then-branch Γ carries `eq(c, Red)`,
    // which is the callee's precondition exactly. It must discharge.
    let src = format!(
        r#"
namespace wi756.gammaif
{NEEDY_COLOR}
  operation caller(c: Color) -> Int64 =
    if eq(c, Red) then needy(c) else 0
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "the `if` premise IS the callee's precondition; it must discharge it \
         over a constructor operand as it does over a literal; got: {:#?}",
        res.err()
    );
}

#[test]
fn if_premise_over_an_int_literal_still_discharges() {
    // CONTROL: the literal shape WI-539 already covers — passes with or without
    // the normalization, and says the fix did not invent Γ discharge, only made
    // the constructor spelling reach it.
    let src = r#"
namespace wi756.gammaifint
  import anthill.prelude.{Int64}
  operation needy(b: Int64) -> Int64
    requires neq(b, 0)
    = 0
  operation caller(b: Int64) -> Int64 =
    if neq(b, 0) then needy(b) else 0
end
"#;
    let res = load_result(src);
    assert!(
        res.is_ok(),
        "the WI-539 literal if-guard must keep discharging; got: {:#?}",
        res.err()
    );
}

#[test]
fn let_bound_constructor_discharges_a_later_requires() {
    // The SECOND producer channel: a `let` binding fact `eq(d, Red)`. The value
    // rides as a child of a compound fact, not as the fact itself, which is why
    // the normalization has to recurse into carrier children.
    let src = format!(
        r#"
namespace wi756.gammalet
{NEEDY_COLOR}
  operation caller() -> Int64 =
    let d = Red
    needy(d)
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "`let d = Red` puts `eq(d, Red)` in Γ, which is `needy`'s precondition \
         under σ; it must discharge; got: {:#?}",
        res.err()
    );
}

#[test]
fn match_arm_constructor_discharges_a_later_requires() {
    // The THIRD channel — already correct before WI-756 (its fact builder spells
    // the pattern constructor as a closed datum), so this row passes either way.
    // It is here because the three channels must agree: a later change that
    // normalizes one and not the others has to fail something.
    let src = format!(
        r#"
namespace wi756.gammamatch
{NEEDY_COLOR}
  operation caller(c: Color) -> Int64 =
    match c
      case Red -> needy(c)
      case Green -> 0
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "the `case Red` arm narrows Γ to `eq(c, Red)`, discharging `needy`'s \
         precondition; got: {:#?}",
        res.err()
    );
}

#[test]
fn an_in_body_proof_reads_the_gamma_its_producers_write() {
    // The two halves meeting: Γ seeded EXACTLY as the `if` fork seeds it (the raw
    // condition occurrence, normalized on the way in), then site 1's own goal
    // proved against it. Without the producer half this returns false — the
    // lowered goal cannot match a raw fact — which is the capability the goal
    // change would otherwise have cost.
    //
    // The RAW-goal half is the vocabulary statement, not a requirement on user
    // programs: a goal in the source spelling must NOT match Γ, because that is
    // the accident this pair replaces. Both directions measured; before the
    // producer half they read exactly the other way round.
    let src = r#"
namespace wi756.gammaproof
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
  end

  operation caller(c: Color) -> Int64 =
    if eq(c, Red) then
      proof p by derivation conclude eq(c, Red) end
      1
    else 0
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let caller = kb
        .try_resolve_symbol("wi756.gammaproof.caller")
        .expect("caller symbol");
    let body = kb.op_body_node(caller).expect("caller body node");
    let Some(Expr::If {
        condition,
        then_branch,
        ..
    }) = body.as_expr()
    else {
        panic!("caller body is not Expr::If: {:?}", body.as_expr());
    };
    let (condition, then_branch) = (Rc::clone(condition), Rc::clone(then_branch));
    let Some(Expr::Proof {
        target, conclude, ..
    }) = then_branch.as_expr()
    else {
        panic!(
            "then-branch is not Expr::Proof: {:?}",
            then_branch.as_expr()
        );
    };
    let (target, conclude) = (*target, conclude.clone());
    // Γ as the `if` fork supplies it.
    let flow = FlowEnv::empty().assume(&mut kb, Value::Node(condition));
    let goal = in_body_proof_goal(&mut kb, target, conclude.as_ref());
    assert!(
        prove_from_gamma(&mut kb, &flow, &goal),
        "the in-body proof's goal must be discharged by the `if` premise the \
         enclosing fork put in Γ — producer and consumer share one vocabulary"
    );
    let raw = Value::Node(Rc::clone(conclude.as_ref().expect("conclude")));
    assert!(
        !prove_from_gamma(&mut kb, &flow, &raw),
        "a goal in the SOURCE spelling must not match Γ: Γ speaks the goal \
         vocabulary, and the raw spelling matching was the accident WI-756 removed"
    );
}
