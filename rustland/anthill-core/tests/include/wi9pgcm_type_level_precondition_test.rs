//! WI-9PGCM — an operation's `requires` over a TYPE-LEVEL variable is an
//! obligation the call site can discharge.
//!
//! `send(body: Text[L = ?l]) requires flows_to(?l, Public)` names `?l`, which is
//! bound in the PARAMETER TYPE and is not among the operation's value parameters.
//! WI-539's call-site check proves a value precondition under σ (param symbol ↦
//! argument term) from Γ, and σ cannot carry `?l`. Before this ticket the clause
//! therefore reached the resolver with a FREE variable — and a free variable is
//! witnessed EXISTENTIALLY, so `flows_to(?l, Public)` proved itself off the
//! unrelated `flows_to(Public, Public)` fact at every call. The obligation read as
//! a guarantee and gated nothing.
//!
//! The fix walks the clause through the call's TYPE substitution first (the same
//! `subst` the declared effects are walked through), which decides `?l` from the
//! argument's declared type. Three states follow, and the tests below are one per
//! state:
//!
//!   * DECIDED and provable — `send(banner())` with `banner() -> Text[L = Public]`
//!     ⇒ `flows_to(Public, Public)`, a fact. Loads.
//!   * DECIDED and unprovable — `send(fetch())` with `fetch() -> Text[L =
//!     Untrusted]` ⇒ `flows_to(Untrusted, Public)`, deliberately absent from the
//!     lattice. A loud `UnsatisfiedPrecondition` naming the binding.
//!   * UNDETERMINED — a clause still carrying a FLEX variable, which no caller has
//!     bound and no later pass has solved. Floats, never decided by absence
//!     (WI-067 / WI-292).
//!
//! WI-K88TN REVISED THE THIRD STATE and this file is its home too, since the same
//! six programs measure both. A label-polymorphic wrapper is NOT the undetermined
//! case: `relay(t: Text[L = ?m]) = send(t)` has `?m` RIGID in its body — universally
//! quantified, the caller's to choose (`rigidify_unwritten_sort_params`: "Inside the
//! body it is therefore rigid; at a CALL it is flexible again") — so `flows_to(?m,
//! Public)` there is `∀m. flows_to(m, Public)`, DECIDED and false. Regime (a),
//! DECLARE-OR-REFUSE: the wrapper writes the clause or the body is a load error, and
//! the declared clause is then an assumption in the body's Γ that discharges it.
//!
//! WHY (a) AND NOT (b) — inferring the clause onto the signature — is recorded on
//! [`value_carries_undecided_var`]'s doc. Briefly: (b) leaves the contract invisible
//! at the declaration, needs a call-graph fixpoint, and STILL needs (a)'s refusal for
//! a clause naming a variable no signature binds
//! (`an_obligation_no_signature_binds_is_refused`). The other half of the same clause
//! list already runs (a) — a body incurring an undeclared effect is refused — so this
//! makes `requires` and `effects` agree. Corpus cost measured before landing: ZERO
//! new refusals across 212 `.anthill` files.
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT (repo rule "assert the CONTROL
//! too"). WI-K88TN is FOUR independent axes and each needs its own back-out; every test
//! below names the one it measures, and all four sets are MEASURED, not predicted:
//!   * (A) THE GATE SPLIT (`view_carries_undecided_var`'s `ViewHead::Var(v) =>
//!     !v.is_rigid()` reverted to `=> true`) — a rigid clause floats again, so 6 tests
//!     load clean and FAIL: `rigid_label_obligation_is_decided_and_refused`,
//!     `the_wrapper_no_longer_swallows_the_obligation`,
//!     `the_obligation_propagates_through_two_wrappers`,
//!     `an_obligation_no_signature_binds_is_refused`,
//!     `mixed_conjunct_over_a_rigid_label_is_decided_whole`,
//!     `a_guard_still_gates_an_undeclared_wrapper`.
//!   * (B) THE Γ₀ SEED (`gamma0` reverted to `FlowEnv::empty()`) — a DECLARED contract
//!     is no longer readable inside its own body, so 4 FAIL:
//!     `declaring_the_clause_discharges_it_from_gamma`,
//!     `a_declared_wrapper_gates_its_own_callers`,
//!     `mixed_conjunct_declared_discharges_and_still_gates`,
//!     `a_declared_clause_discharges_in_a_match_guard_too`. This back-out is what
//!     separates PROVED from SKIPPED: those programs also loaded BEFORE WI-K88TN, but by
//!     the float's `continue` running ahead of `precondition_proved` — the declaration
//!     was never read. Backing it out refuses them at the CALLEE's `requires`, inside
//!     the body, rather than at the wrapper's own — the wrong reason made visible.
//!   * (C) THE GUARD Γ (the match-arm guard's `arm_flow` reverted to `FlowEnv::empty()`)
//!     — 1 FAILS: `a_declared_clause_discharges_in_a_match_guard_too`. It is the only
//!     test in two back-out sets, and correctly so: the guard needs both the seed to
//!     exist and the threading to reach it.
//!   * (D) THE WITNESS/PARAMETER SPLIT (`clause_rigid_kind`'s `HasWitness` arm answering
//!     `AllParams`, i.e. every rigid read as declarable) — 1 FAILS:
//!     `an_obligation_no_signature_binds_is_refused`. It changes no VERDICT, only which
//!     repair is prescribed, which is why it needs its own axis and why that test drives
//!     the prescribed repair rather than only asserting the message text.
//!   * `a_universally_true_obligation_needs_no_declaration` passes under ALL FOUR by
//!     design and measures a fifth thing: that a rigid clause reaches the PROVER rather
//!     than a Γ-membership test. Its control is the rule-vs-fact swap in its own body.
//!
//! (C) AND (D) WERE FOUND BY `/code-review`, NOT BY THIS FILE, and both are worth the
//! note. (C) was a REGRESSION this ticket introduced — a position the Γ seed did not
//! reach, invisible while the obligation floated and a false refusal once it was
//! decided. (D) was a message that prescribed a repair which, applied, returned the
//! byte-identical error. Neither was reachable from the six rows the ticket named.
//!
//! WI-9PGCM's own rows are unmoved by WI-K88TN and stay its controls:
//!   * `untrusted_label_into_public_only_sink_is_refused` — FAILS when 9PGCM is
//!     backed out (loads clean before it: that was the whole defect).
//!   * `refusal_names_the_binding_that_refuted_it` — FAILS (before 9PGCM there is no
//!     refusal at all, and the diagnostic printed the goal's head alone).
//!   * `existential_witness_does_not_discharge_the_obligation` — FAILS. The mechanism
//!     test: it distinguishes "the label was never read" from "the label was read and
//!     happened to pass".
//!   * `public_label_into_public_only_sink_loads` — PASSES EITHER WAY by design, the
//!     control that neither fix simply started refusing every call.
//!   * `mixed_conjunct_decided_and_unprovable_is_refused` — FAILS when 9PGCM is
//!     backed out; `mixed_conjunct_both_halves_decided_loads` passes either way.
//!
//! The `mixed_conjunct_*` group covers the shape `clause_conjuncts` cannot split — a
//! SINGLE goal naming both a type-level variable and a value parameter. Its verdict
//! is decided by the LABEL in every state, which is why it needs no rule of its own.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load stdlib + user source together; surface load errors as strings. Identical
/// harness to `wi539_call_site_contracts_test::load_result`, whose call-site
/// contract check this exercises through its type-level half.
fn load_result(source: &str) -> Result<(), Vec<String>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    parsed.push(parse::parse(source).expect("parse user source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

/// The taint vocabulary of `docs/measurements/guardians/d2c_callsite.anthill`: a
/// two-point lattice whose `Untrusted → Public` edge is deliberately ABSENT, a
/// label carried as a sort type parameter, and two sources whose label comes from
/// the TOOL SIGNATURE rather than from a constructor call.
///
/// `{ns}` is per-test so each case gets its own namespace in the one KB.
fn taint_prelude(ns: &str) -> String {
    format!(
        r#"
enum {ns}.Level
  entity Untrusted
  entity Public
end

enum {ns}.Text
  import anthill.prelude.{{String}}
  sort L = ?
  entity mk(raw: String)
end

namespace {ns}
  import anthill.prelude.{{Unit, String, Int64}}
  import {ns}.Level.{{Untrusted, Public}}
  import {ns}.Text
  import {ns}.Text.{{mk}}

  fact flows_to(Public, Public)
  fact flows_to(Untrusted, Untrusted)
  -- ABSENT, and the point of the whole file: flows_to(Untrusted, Public)

  operation fetch() -> Text[L = Untrusted]
  operation banner() -> Text[L = Public]

  operation send(body: Text[L = ?l]) -> Unit
    requires flows_to(?l, Public)

  -- MIXED: ONE atom naming both a type-level variable and a value parameter.
  fact allowed(Public, 1)
  operation gate(body: Text[L = ?l], n: Int64) -> Unit
    requires allowed(?l, n)
"#
    )
}

/// Did the load fail with the one `UnsatisfiedPrecondition` diagnostic, naming
/// `goal` in full? Matched on BOTH fragments so an unrelated failure that merely
/// mentions a precondition cannot satisfy it — the shape
/// `wi756_proof_path_eq_override_test::is_unsatisfied_precondition` uses.
fn is_unsatisfied_precondition(errs: &[String], goal: &str) -> bool {
    errs.iter().any(|e| {
        e.contains("unsatisfied precondition") && e.contains(&format!("precondition `{goal}`"))
    })
}

#[test]
fn untrusted_label_into_public_only_sink_is_refused() {
    // THE ACCEPTANCE. `send(fetch())`: the argument's declared type binds
    // `?l := Untrusted` in the call's type substitution, so the obligation is
    // `flows_to(Untrusted, Public)` — no fact, no rule, no solution. The call may
    // not load.
    let src = format!(
        "{}\n  operation leak() -> Unit =\n    send(fetch())\nend\n",
        taint_prelude("test.wi9pgcm.leak")
    );
    let errs = load_result(&src).expect_err(
        "`send(fetch())` carries `Untrusted` into a sink requiring `flows_to(?l, Public)`; \
         with the lattice edge absent the precondition cannot be proved and the call must \
         be refused",
    );
    assert!(
        is_unsatisfied_precondition(&errs, "flows_to(Untrusted, Public)"),
        "expected the call-site precondition diagnostic for the grounded goal; got: {errs:#?}"
    );
}

#[test]
fn refusal_names_the_binding_that_refuted_it() {
    // The diagnostic must say WHICH label failed. `flows_to` alone — the goal's
    // head, which is all the TYPE renderer printed — cannot distinguish the
    // refused call from the legal one beside it, and both spell the clause
    // `flows_to(?l, Public)` at the declaration.
    let src = format!(
        "{}\n  operation leak() -> Unit =\n    send(fetch())\nend\n",
        taint_prelude("test.wi9pgcm.msg")
    );
    let errs = load_result(&src).expect_err("the refused call is asserted above");
    let joined = errs.join("\n");
    assert!(
        joined.contains("Untrusted"),
        "the refusal must name the binding that refuted it, not just the goal's \
         functor; got: {joined}"
    );
    assert!(
        joined.contains("test.wi9pgcm.msg.send"),
        "the refusal must name the callee whose contract went undischarged; got: {joined}"
    );
}

#[test]
fn public_label_into_public_only_sink_loads() {
    // CONTROL (passes either way by design). The same sink, the same clause, a
    // source whose signature says `Public`: `flows_to(Public, Public)` is a fact,
    // so the obligation discharges and the body loads. This is what says the fix
    // GATES rather than simply refuses.
    let src = format!(
        "{}\n  operation ok() -> Unit =\n    send(banner())\nend\n",
        taint_prelude("test.wi9pgcm.ok")
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "`send(banner())` grounds the precondition to `flows_to(Public, Public)`, which is \
         a fact — the call must load clean. got: {:#?}",
        res.err()
    );
}

#[test]
fn existential_witness_does_not_discharge_the_obligation() {
    // THE MECHANISM TEST, and the one that separates "gated" from "accidentally
    // passing". Before the fix the free `?l` was witnessed existentially, so the
    // `Public` self-edge discharged EVERY call — including the `Untrusted` one.
    // Here the self-edge is the ONLY fact about `Public` and the call is about
    // `Untrusted`: if the label were still being ignored, this would load.
    //
    // The prelude's second fact (`flows_to(Untrusted, Untrusted)`) is what makes
    // this sharper than the acceptance test — a witness exists for BOTH argument
    // positions independently, so nothing but reading the actual binding refuses
    // the call.
    let src = format!(
        "{}\n  operation leak() -> Unit =\n    send(fetch())\nend\n",
        taint_prelude("test.wi9pgcm.exist")
    );
    let errs = load_result(&src).expect_err(
        "a fact about a DIFFERENT label must not discharge this call's obligation; \
         an existential witness for `?l` is not a proof about the argument",
    );
    assert!(
        is_unsatisfied_precondition(&errs, "flows_to(Untrusted, Public)"),
        "the obligation must be judged at the argument's binding, not at whatever \
         binding happens to have a fact; got: {errs:#?}"
    );
}

#[test]
fn rigid_label_obligation_is_decided_and_refused() {
    // INVERTED BY WI-K88TN, and this is the test that names the regime. It was
    // `undetermined_label_floats_rather_than_failing`, asserting `is_ok` on the
    // strength of "an undetermined label must suspend". `?m` is NOT undetermined: it
    // is RIGID in `relay`'s body — universally quantified, the caller's to choose —
    // so the obligation at `send(t)` is `∀m. flows_to(m, Public)`, which is DECIDED
    // and false (only `Public` flows to `Public`). Regime (a): declare it or be
    // refused. The float still covers a genuinely undetermined clause, which is a
    // FLEX variable and not this.
    //
    // FAILS when the gate split is backed out (`ViewHead::Var(v) => !v.is_rigid()`
    // back to `=> true`): the clause floats again and the source loads.
    let src = format!(
        "{}\n  operation relay(t: Text[L = ?m]) -> Unit =\n    send(t)\nend\n",
        taint_prelude("test.wi9pgcm.poly")
    );
    let errs = load_result(&src).expect_err(
        "`?m` is universally quantified in the body, so `flows_to(?m, Public)` holds \
         for no instantiation; the wrapper must be refused rather than launder it",
    );
    assert!(
        errs.iter().any(|e| e.contains("flows_to(?m, Public)")),
        "the diagnostic must name the goal in the spelling the author wrote — `?m`, \
         the source form, not the `!m` a rigid prints as; got: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("declared here")),
        "and it must name the REPAIR, which is a declaration and not a call-site \
         fact; got: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("poly.relay.requires")),
        "and it is attributed to the operation that owes the declaration — `relay` — \
         not to the callee `send`, whose own contract is fine; got: {errs:#?}"
    );
}

#[test]
fn declaring_the_clause_discharges_it_from_gamma() {
    // THE OTHER HALF OF REGIME (a), and the reason the fix is two pieces rather than
    // one: the refusal above is only legitimate if the repair it demands WORKS. With
    // `requires flows_to(?m, Public)` written on `relay`, the body's `send(t)`
    // obligation is discharged from Γ — proposal 050's Hoare reading, `relay`'s own
    // precondition assumed inside its body (`op_requires_gamma`).
    //
    // FAILS when the Γ₀ seed is backed out (`gamma0` → `FlowEnv::empty()`), and that
    // is the control that separates PROVED from SKIPPED: before WI-K88TN this source
    // also loaded, but by the float's `continue` running ahead of `precondition_
    // proved` — the declaration was never read. Backing the seed out now refuses it
    // at `send.requires`, which is that same "never read" made visible.
    let src = format!(
        "{}\n  operation relay(t: Text[L = ?m]) -> Unit\n    \
         requires flows_to(?m, Public)\n    = send(t)\nend\n",
        taint_prelude("test.wi9pgcm.declared")
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "a declared `requires` is an ASSUMPTION inside the body it guards; it must \
         discharge the callee obligation it was written for. got: {:#?}",
        res.err()
    );
}

#[test]
fn a_universally_true_obligation_needs_no_declaration() {
    // THE GATE GATES, IT DOES NOT BLANKET-REFUSE — and this is where the shipped fix
    // departs from the ticket's prescribed "try Γ ALONE, structural match, never a
    // resolver query". A rigid clause goes to the PROVER, not to a Γ-membership test,
    // so a wrapper whose obligation holds for EVERY label needs no `requires` line:
    // `anything(?x)` is proved by a rule with a free head variable, which binds the
    // skolem by ordinary universal instantiation.
    //
    // Γ-membership alone would refuse this and demand a contract that says nothing.
    // The existential vacuity WI-9PGCM removed is a FLEX hazard specifically — a
    // skolem never binds (`unify_concrete`), so it cannot be witnessed off an
    // unrelated fact the way a free variable was.
    //
    // FAILS when the rule below is changed to a FACT about one label
    // (`fact anything(Public)`), which is the discriminating control: that is
    // provable existentially and not universally, and the wrapper must then be
    // refused. PASSES either way on the gate split — it is about what reaches the
    // prover, not about whether anything does.
    let src = format!(
        "{}\n  rule anything(?x)\n    :- true\n\
         \n  operation strict(body: Text[L = ?l]) -> Unit\n    \
         requires anything(?l)\n\
         \n  operation wrap(t: Text[L = ?m]) -> Unit =\n    strict(t)\nend\n",
        taint_prelude("test.wi9pgcm.univ")
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "`anything(?m)` is provable for EVERY label, so the wrapper owes no \
         declaration; the gate must decide the clause, not refuse it unread. \
         got: {:#?}",
        res.err()
    );
}

#[test]
fn the_wrapper_no_longer_swallows_the_obligation() {
    // WI-K88TN's headline: THE LEAK IS CLOSED. This was
    // `wrapper_swallows_the_obligation_pending_propagation`, asserting `is_ok` and
    // pinning where the float stopped so a follow-up had a place to flip. This is
    // that flip. `relay` declares no contract, so it is refused at its own body —
    // the leak never reaches `relay(fetch())`, because the laundering declaration
    // does not load in the first place.
    //
    // THE REFUSAL LANDS ON `relay`, NOT ON `leak`, and that is regime (a) rather
    // than (b): under (b) `relay` would load with an inferred contract and only
    // `leak` would be refused. The reported op is the CALLEE whose obligation went
    // undischarged (`send`), at the span inside `relay`'s body.
    //
    // FAILS when the gate split is backed out: both operations load and `fetch()`'s
    // Untrusted payload reaches the Public-only sink.
    let src = format!(
        "{}\n  operation relay(t: Text[L = ?m]) -> Unit =\n    send(t)\n\
         \n  operation leak() -> Unit =\n    relay(fetch())\nend\n",
        taint_prelude("test.wi9pgcm.thru")
    );
    let errs = load_result(&src).expect_err(
        "a contract-less polymorphic wrapper must not launder its callee's \
         obligation; the wrapper itself is the load error",
    );
    assert!(
        errs.iter().any(|e| e.contains("flows_to(?m, Public)")),
        "the diagnostic names the obligation the wrapper dropped; got: {errs:#?}"
    );
}

#[test]
fn a_declared_wrapper_gates_its_own_callers() {
    // THE WHOLE POINT, END TO END: with the contract declared, `relay` propagates
    // the obligation to ITS callers, and they are decided there. `relay(banner())`
    // binds `?m := Public` ⇒ `flows_to(Public, Public)`, a fact — loads.
    // `relay(fetch())` binds `?m := Untrusted` ⇒ `flows_to(Untrusted, Public)`,
    // absent — refused, naming `relay`'s own `requires` rather than `send`'s.
    //
    // The two arms are in ONE test because their difference is the measurement: a
    // fix that merely refuses everything passes the second arm and fails the first.
    //
    // FAILS when the Γ₀ seed is backed out — BOTH arms, and at the wrong site
    // (`send.requires`, inside the body, rather than `relay.requires` at the call).
    let ok_src = format!(
        "{}\n  operation relay(t: Text[L = ?m]) -> Unit\n    \
         requires flows_to(?m, Public)\n    = send(t)\n\
         \n  operation ok() -> Unit =\n    relay(banner())\nend\n",
        taint_prelude("test.wi9pgcm.gateok")
    );
    let res = load_result(&ok_src);
    assert!(
        res.is_ok(),
        "the declared wrapper must still ACCEPT a call that satisfies it — \
         otherwise the fix refuses rather than gates. got: {:#?}",
        res.err()
    );

    let bad_src = format!(
        "{}\n  operation relay(t: Text[L = ?m]) -> Unit\n    \
         requires flows_to(?m, Public)\n    = send(t)\n\
         \n  operation leak() -> Unit =\n    relay(fetch())\nend\n",
        taint_prelude("test.wi9pgcm.gatebad")
    );
    let errs =
        load_result(&bad_src).expect_err("the declared contract must refuse an Untrusted argument");
    assert!(
        is_unsatisfied_precondition(&errs, "flows_to(Untrusted, Public)"),
        "the obligation is now decided at the WRAPPER's call site, with both halves \
         judged; got: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("gatebad.relay")),
        "and it is reported against `relay`'s own `requires` — the contract that \
         propagated it — not against `send`; got: {errs:#?}"
    );
}

#[test]
fn the_obligation_propagates_through_two_wrappers() {
    // TRANSITIVITY, which regime (a) gets for free and regime (b) would have needed
    // a call-graph fixpoint for: each wrapper is checked against its OWN signature,
    // so a wrapper of a wrapper owes the same declaration for the same reason. No
    // pass walks a callee's body to discover this.
    //
    // FAILS when the gate split is backed out (both wrappers load).
    let src = format!(
        "{}\n  operation relay(t: Text[L = ?m]) -> Unit\n    \
         requires flows_to(?m, Public)\n    = send(t)\n\
         \n  operation relay2(t: Text[L = ?n]) -> Unit =\n    relay(t)\nend\n",
        taint_prelude("test.wi9pgcm.twohop")
    );
    let errs = load_result(&src).expect_err(
        "the second wrapper declares nothing, so `relay`'s propagated obligation \
         stops there and must be refused",
    );
    assert!(
        errs.iter().any(|e| e.contains("flows_to(?n, Public)")),
        "named in the SECOND wrapper's own variable — the obligation is restated in \
         the vocabulary of the signature that owes it; got: {errs:#?}"
    );
}

#[test]
fn an_obligation_no_signature_binds_is_refused() {
    // THE RESIDUE, and it is why regime (b) could not have replaced (a): here the
    // floated clause names `?k`, a variable bound by NOTHING — not by `f`'s
    // signature, not by any caller. There is no slot to infer a contract ONTO, so
    // even the inferring regime would have to refuse it. Under (a) it is the
    // ordinary case: `f`'s body raises an obligation it cannot discharge.
    //
    // FAILS when the gate split is backed out (loads clean — measured).
    let src = format!(
        "{}\n  operation pick() -> Text[L = ?k]\n\
         \n  operation f() -> Unit =\n    send(pick())\nend\n",
        taint_prelude("test.wi9pgcm.residue")
    );
    let errs = load_result(&src).expect_err(
        "the obligation names a label no signature binds; nothing can discharge it \
         and nothing can declare it, so the body is a load error",
    );
    assert!(
        errs.iter().any(|e| e.contains("opaque witness")),
        "it must be reported as the WITNESS case, not the declarable one; got: {errs:#?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("declared here")),
        "and it must NOT prescribe a declaration. `?k` is an existential ρ opened from \
         `pick()`'s return, so a `requires` on `f` mints an unrelated flex variable and \
         changes nothing. That is why a `Var::Rigid` alone cannot classify this and \
         `param_rigids` membership does; got: {errs:#?}"
    );

    // AND THE REPAIR THE OTHER MESSAGE WOULD HAVE PRESCRIBED IS DRIVEN, not merely
    // asserted from the message text: writing it must leave the verdict unchanged. This
    // is the test that would have caught the wrong message — the assertion above pins
    // what is printed, this pins that the printed advice is not a lie. Found by
    // /code-review: the first shipped message prescribed exactly this line, and applying
    // it returned the BYTE-IDENTICAL error, which is a loop.
    let repaired = format!(
        "{}\n  operation pick() -> Text[L = ?k]\n\
         \n  operation f() -> Unit\n    requires flows_to(?k, Public)\n    \
         = send(pick())\nend\n",
        taint_prelude("test.wi9pgcm.residue2")
    );
    let still = load_result(&repaired)
        .expect_err("declaring the clause cannot help: `?k` there is a different variable");
    assert!(
        still.iter().any(|e| e.contains("opaque witness")),
        "the declaration changes nothing, which is what the witness message says; \
         got: {still:#?}"
    );
}

#[test]
fn a_declared_clause_discharges_in_a_match_guard_too() {
    // FOUND BY /code-review, and it was a REGRESSION this ticket introduced rather than
    // a gap it left. A match-arm guard is checked by a NESTED `type_check_node_gated`
    // rather than by a work-stack `Visit`, and that entry hard-coded Γ₀ to
    // `FlowEnv::empty()` — harmless while a rigid obligation FLOATED, and a false
    // refusal the moment it became DECIDED. So a wrapper that correctly declared its
    // contract was refused for calling the constrained operation in a guard.
    //
    // MEASURED both ways: on HEAD this source LOADED; with the gate split and the
    // un-threaded guard Γ it was refused; with `arm_flow` threaded it loads again. The
    // arm-BODY spelling below is the control that says the two positions must agree — it
    // loaded throughout, which is what made the guard form's refusal an inconsistency
    // rather than a policy.
    //
    // FAILS when the guard's Γ is reverted to `FlowEnv::empty()`.
    let guard_src = format!(
        "{}\n  operation checkg(body: Text[L = ?l], n: Int64) -> Bool\n    \
         requires allowed(?l, n)\n\
         \n  operation relay(t: Text[L = ?m], n: Int64) -> Int64\n    \
         requires allowed(?m, n)\n    = match t\n        \
         case mk(r) | checkg(t, n) -> 1\n        \
         case _ -> 0\nend\n",
        taint_prelude("test.wi9pgcm.guard")
    );
    let res = load_result(&guard_src);
    assert!(
        res.is_ok(),
        "a declared `requires` is in Γ for the arm GUARD as much as for the arm body; \
         a guard is a position in the body, not a fresh frame. got: {:#?}",
        res.err()
    );

    let body_src = format!(
        "{}\n  operation checkg(body: Text[L = ?l], n: Int64) -> Bool\n    \
         requires allowed(?l, n)\n\
         \n  operation relay(t: Text[L = ?m], n: Int64) -> Int64\n    \
         requires allowed(?m, n)\n    = match t\n        \
         case mk(r) -> if checkg(t, n) then 1 else 0\n        \
         case _ -> 0\nend\n",
        taint_prelude("test.wi9pgcm.guardbody")
    );
    assert!(
        load_result(&body_src).is_ok(),
        "CONTROL, and it passes either way by design: the same call in the arm BODY \
         reaches Γ through the work-stack `Visit` and never lost it"
    );
}

#[test]
fn a_guard_still_gates_an_undeclared_wrapper() {
    // The other half of the fix above: threading Γ into the guard must not turn the
    // guard into a hole. An UNDECLARED wrapper calling the constrained operation in a
    // guard is refused exactly as it is in a body — Γ carries what was declared, and
    // nothing was.
    //
    // FAILS when the gate split is backed out. PASSES either way on the guard-Γ fix,
    // which is why it is stated separately: it measures that the fix narrowed nothing.
    let src = format!(
        "{}\n  operation checkg(body: Text[L = ?l], n: Int64) -> Bool\n    \
         requires allowed(?l, n)\n\
         \n  operation relay(t: Text[L = ?m], n: Int64) -> Int64\n    \
         = match t\n        \
         case mk(r) | checkg(t, n) -> 1\n        \
         case _ -> 0\nend\n",
        taint_prelude("test.wi9pgcm.guardgate")
    );
    let errs =
        load_result(&src).expect_err("an undeclared wrapper is refused in a guard as in a body");
    assert!(
        errs.iter().any(|e| e.contains("allowed(?m, n)")),
        "got: {errs:#?}"
    );
}

// ── the MIXED conjunct: one atom, a type-level variable AND a value parameter ──
//
// `clause_conjuncts` splits a comma list, so these are the case it CANNOT split:
// `requires allowed(?l, n)` is a single goal. The three states must still come out
// right, and the undetermined one must float the atom WHOLE — there is no half of
// an atom to judge on its own.

#[test]
fn mixed_conjunct_decided_and_provable_loads() {
    // `gate(banner(), 1)` ⇒ `allowed(Public, 1)`, a fact. Both halves decided.
    // PASSES EITHER WAY by design (before the change the free `?l` found the same
    // fact existentially) — it is the control that the mixed shape still loads.
    let src = format!(
        "{}\n  operation ok2() -> Unit =\n    gate(banner(), 1)\nend\n",
        taint_prelude("test.wi9pgcm.mixok")
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "both halves of `allowed(?l, n)` are decided and the fact exists; the call \
         must load clean. got: {:#?}",
        res.err()
    );
}

#[test]
fn mixed_conjunct_decided_and_unprovable_is_refused() {
    // `gate(fetch(), 1)` ⇒ `allowed(Untrusted, 1)` — the type half is decided to a
    // label no fact covers. The mixed shape gates exactly as the pure one does.
    //
    // FAILS when the change is backed out: with `?l` free the goal proves off
    // `allowed(Public, 1)`.
    let src = format!(
        "{}\n  operation leak2() -> Unit =\n    gate(fetch(), 1)\nend\n",
        taint_prelude("test.wi9pgcm.mixbad")
    );
    let errs = load_result(&src).expect_err(
        "the type half of the mixed atom binds `?l := Untrusted`, which no `allowed` \
         fact covers; the call must be refused",
    );
    assert!(
        is_unsatisfied_precondition(&errs, "allowed(Untrusted, 1)"),
        "the diagnostic must show the atom with BOTH halves as judged; got: {errs:#?}"
    );
}

#[test]
fn mixed_conjunct_over_a_rigid_label_is_decided_whole() {
    // INVERTED BY WI-K88TN, from `mixed_conjunct_undetermined_floats_whole`. The old
    // reading was "an atom naming an undecided label is undecided whatever its other
    // argument is", and the premise is what changed: `?m` is RIGID in `relay2`'s
    // body, so it is not undecided. The atom is decided WHOLE for the same reason it
    // used to float whole — there is no half of an atom to judge separately — and
    // `∀m. allowed(m, n)` holds for no `m`.
    //
    // THE MIXED SHAPE NEEDS NO SEPARATE RULE, which is the point worth pinning: the
    // value operand `n` is a `var_ref` functor and not a variable (WI-552), so it
    // never affected this gate's verdict in either direction. What decides the atom
    // is its LABEL, before and after.
    //
    // FAILS when the gate split is backed out (floats again, loads clean).
    let src = format!(
        "{}\n  operation relay2(t: Text[L = ?m], n: Int64) -> Unit =\n    gate(t, n)\nend\n",
        taint_prelude("test.wi9pgcm.mixfloat")
    );
    let errs = load_result(&src).expect_err(
        "the atom's label is universally quantified in this body, so the whole atom \
         is decided and unprovable",
    );
    assert!(
        errs.iter().any(|e| e.contains("allowed(?m, n)")),
        "the diagnostic shows the atom with BOTH operands in source spelling — the \
         rigid label as `?m` and the value parameter as `n`, which is exactly the \
         `requires` line the repair must write; got: {errs:#?}"
    );
}

#[test]
fn mixed_conjunct_declared_discharges_and_still_gates() {
    // The mixed shape's repair, driven the same way the pure one is: declaring
    // `requires allowed(?m, n)` on the wrapper discharges the body obligation from Γ
    // AND propagates it, so a bad call is still refused with both operands judged.
    // Γ must match a clause carrying a rigid label beside a `var_ref` value param —
    // the case the pure rows never exercise.
    //
    // FAILS when the Γ₀ seed is backed out (the declared wrapper is refused).
    let ok_src = format!(
        "{}\n  operation relay2(t: Text[L = ?m], n: Int64) -> Unit\n    \
         requires allowed(?m, n)\n    = gate(t, n)\n\
         \n  operation ok3() -> Unit =\n    relay2(banner(), 1)\nend\n",
        taint_prelude("test.wi9pgcm.mixdecl")
    );
    let res = load_result(&ok_src);
    assert!(
        res.is_ok(),
        "a declared mixed clause must discharge the body obligation and admit a \
         satisfying call. got: {:#?}",
        res.err()
    );

    let bad_src = format!(
        "{}\n  operation relay2(t: Text[L = ?m], n: Int64) -> Unit\n    \
         requires allowed(?m, n)\n    = gate(t, n)\n\
         \n  operation leak3() -> Unit =\n    relay2(fetch(), 1)\nend\n",
        taint_prelude("test.wi9pgcm.mixleak")
    );
    let errs = load_result(&bad_src)
        .expect_err("the propagated mixed clause must refuse an Untrusted argument");
    assert!(
        is_unsatisfied_precondition(&errs, "allowed(Untrusted, 1)"),
        "both operands judged at the wrapper's call site; got: {errs:#?}"
    );
}
