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
//!   * UNDETERMINED — a label-polymorphic wrapper whose own caller has not bound
//!     the label. Floats, never decided by absence (WI-067 / WI-292).
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT (repo rule "assert the CONTROL
//! too"):
//!   * `untrusted_label_into_public_only_sink_is_refused` — FAILS (loads clean
//!     before the change: this is the whole defect).
//!   * `refusal_names_the_binding_that_refuted_it` — FAILS (before the change
//!     there is no refusal at all, and the diagnostic printed the goal's head
//!     alone even when there was one).
//!   * `existential_witness_does_not_discharge_the_obligation` — FAILS (before
//!     the change the `Public` self-edge discharges a call about `Untrusted`; it
//!     is the mechanism test, and it is the one that distinguishes "the label was
//!     never read" from "the label was read and happened to pass").
//!   * `public_label_into_public_only_sink_loads` — PASSES EITHER WAY by design.
//!     It is the control that the fix did not simply start refusing every call.
//!   * `undetermined_label_floats_rather_than_failing` — PASSES EITHER WAY by
//!     design, but for DIFFERENT reasons on the two sides (existential witness
//!     before, the undetermined-floats rule after). It is the control that pins
//!     the WI-067 polarity, which a stricter fix would have broken.
//!   * `wrapper_swallows_the_obligation_pending_propagation` — PASSES EITHER WAY
//!     by design. It pins where the float stops, so the follow-up that propagates
//!     an undetermined obligation onto the enclosing contract has a place to flip.
//!   * `mixed_conjunct_decided_and_unprovable_is_refused` — FAILS when backed out.
//!     The other two `mixed_conjunct_*` cases pass either way by design; see each.
//!
//! The `mixed_conjunct_*` trio covers the shape `clause_conjuncts` cannot split — a
//! SINGLE goal naming both a type-level variable and a value parameter — where the
//! undetermined state has to float the atom whole.

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
fn undetermined_label_floats_rather_than_failing() {
    // CONTROL (passes either way by design, for different reasons on each side).
    // `relay` is polymorphic in its label: no caller has bound `?m`, so at
    // `send(t)` the obligation is `flows_to(?m, Public)` with `?m` undecided.
    // WI-067 / WI-292: act on a DECIDED obligation, never on an undetermined one
    // — a version of this fix that refused an unbound label would refuse every
    // label-polymorphic declaration.
    let src = format!(
        "{}\n  operation relay(t: Text[L = ?m]) -> Unit =\n    send(t)\nend\n",
        taint_prelude("test.wi9pgcm.poly")
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "an undetermined label must suspend, not fail: the enclosing operation is \
         polymorphic in it and its own caller decides it. got: {:#?}",
        res.err()
    );
}

#[test]
fn wrapper_swallows_the_obligation_pending_propagation() {
    // WHERE THE FLOAT STOPS, pinned so a future fix has a place to flip. `relay`
    // is polymorphic in its label and declares no contract of its own, so the
    // obligation it floats above is never re-asked: at `relay(fetch())` the typer
    // checks `relay`'s own `requires` (there is none) and the callee's `send`
    // obligation is not among them. So the leak DOES get through the wrapper.
    //
    // This is NOT the defect this ticket fixes and not a regression from it —
    // before the change the direct call leaked too. Closing it means PROPAGATING
    // an undetermined obligation onto the enclosing operation's contract (either
    // demanding it be declared, or inferring it), which is a design decision this
    // ticket's controls deliberately exclude ("must suspend rather than fail").
    // Filed as WI-20260822-K88TN, which names this test as the one that must flip.
    //
    // PASSES EITHER WAY by design: it asserts the boundary, not the fix.
    let src = format!(
        "{}\n  operation relay(t: Text[L = ?m]) -> Unit =\n    send(t)\n\
         \n  operation leak() -> Unit =\n    relay(fetch())\nend\n",
        taint_prelude("test.wi9pgcm.thru")
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "a contract-less polymorphic wrapper swallows its callee's obligation \
         today — the float is not re-asked at the wrapper's own call site. When \
         obligation propagation lands, this test flips to `is_err`. got: {:#?}",
        res.err()
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
fn mixed_conjunct_undetermined_floats_whole() {
    // THE CASE THE CODE COMMENT ARGUES. `relay2` is label-polymorphic, so at
    // `gate(t, n)` the atom is `allowed(?m, n)` with `?m` undecided — and an atom
    // with an undecided argument is undecided whatever its other argument is. It
    // floats WHOLE; the `n` half is not judged separately, because there is no
    // separate half.
    //
    // PASSES EITHER WAY by design, and for different reasons: before the change the
    // free `?m` was witnessed existentially by `allowed(Public, 1)`. What would have
    // differed is a corpus with no `allowed` fact at all — there the old code raised,
    // on the strength of the fact table rather than of this call.
    let src = format!(
        "{}\n  operation relay2(t: Text[L = ?m], n: Int64) -> Unit =\n    gate(t, n)\nend\n",
        taint_prelude("test.wi9pgcm.mixfloat")
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "an atom naming an undecided label is undecided whatever its value operand \
         is; it must float rather than raise. got: {:#?}",
        res.err()
    );
}
