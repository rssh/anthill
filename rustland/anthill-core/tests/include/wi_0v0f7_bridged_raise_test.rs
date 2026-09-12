//! WI-20260911-0V0F7 — a raise that ESCAPES a bridged operation is a FAULT, not
//! "no solutions".
//!
//! `bridge_op_to_eval` turned every `EvalError` into `None`, so a goal whose callee RAN
//! AND RAISED came back indistinguishable from one the fold merely declined, and the
//! empty answer set read as a relation with nothing in it. MEASURED on `main`, on an
//! operation whose effect row is EMPTY so nothing else warns:
//!
//! ```text
//! operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k
//! rule answer(?r)  :- guardExhaustible(0, ?r)    ->  no solutions, stats.errors == []
//! rule control(?r) :- guardExhaustible(5, ?r)    ->  ?r = 5
//! ```
//!
//! THE ARGUMENT MUST BE A LITERAL, and three fixtures were written wrong before that
//! was known. Spelled `guardExhaustible(0 - 5, ?r)` the operand reaches the bridge
//! UN-REDUCED, so the guard compares a `Node` against an `Int64` and the bridge answers
//! `TypeMismatch { expected: "Ord scalars of matching type", got: "Node and Int64" }` —
//! a DIFFERENT defect that presents as the same silent `no solutions`.
//! `the_literal_and_the_unreduced_operand_are_two_different_faults` pins both, so the
//! next reader does not have to find that out with a probe inside the bridge's `Err`
//! arm the way this one did.
//!
//! WHAT A BACK-OUT PRODUCES, MEASURED rather than asserted — `bridge_disposition`
//! forced to `Schedule` for every variant, which is the `Err(_) => None` it replaces:
//! **5 passed, 7 failed**. The seven are every row about a fault being REPORTED:
//! `a_raise_that_escapes_a_bridged_operation_is_reported`,
//! `the_literal_and_the_unreduced_operand_are_two_different_faults`,
//! `a_faulted_extent_read_refuses_rather_than_under_reporting`,
//! `a_constraint_guard_over_a_raising_callee_blocks_the_load`,
//! `a_contract_over_a_raising_callee_reports_the_raise`,
//! `a_carrier_eq_that_raises_is_reported_too`,
//! `the_raise_partition_is_by_cause_not_by_channel`.
//! The five that pass either way are the five controls, one per consumer, each saying
//! at its own site what it is controlling for.
//!
//! THE PARTITION IS BY CAUSE, NOT BY CHANNEL, which is the half a first attempt got
//! wrong: `raise_relation_floundered` (WI-737) and `raise_load_failed` (WI-SPGBP) ride
//! `EvalError::Raised` and are not domain failures of the callee.
//! `the_raise_partition_is_by_cause_not_by_channel` drives that and fails the moment
//! the test becomes `matches!(e, EvalError::Raised { .. })`.

use anthill_core::eval::{BridgeDisposition, EvalError, Value};
use anthill_core::kb::extent::ExtentReadError;
use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};
use anthill_core::kb::resolve::ResolveConfig;

/// The fixture the ticket was measured on. `match n case k | k > 0 -> k` is
/// GUARD-EXHAUSTIBLE — it loads clean (a `sort` scrutinee's arms are not checked for
/// exhaustiveness) and raises `Error[MatchFailed]` through the HOST channel at `n = 0`,
/// so the raise does not need `Error` in the row and nothing else in the program warns.
const GUARD_EXHAUSTIBLE: &str = r#"
namespace bru.guard
  import anthill.prelude.{Int64}

  operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k

  rule answer(?r) :- guardExhaustible(0, ?r)
  rule control(?r) :- guardExhaustible(5, ?r)
  rule unreduced(?r) :- guardExhaustible(0 - 5, ?r)
end
"#;

fn resolve(src: &str, pattern: &str) -> (Vec<anthill_core::kb::resolve::Solution>, Vec<String>) {
    let mut kb = crate::common::load_kb_with(src);
    let goal = crate::common::query_pattern_term(&mut kb, pattern);
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let msgs = stats.errors.iter().map(|e| e.message.clone()).collect();
    (sols, msgs)
}

// ── THE ACCEPTANCE ────────────────────────────────────────────────────────────

#[test]
fn a_raise_that_escapes_a_bridged_operation_is_reported() {
    let (sols, errors) = resolve(GUARD_EXHAUSTIBLE, "bru.guard.answer(?r)");
    assert_eq!(
        errors.len(),
        1,
        "exactly one fault, deduped on push; got: {errors:?}"
    );
    assert!(
        errors[0].contains("bru.guard.guardExhaustible"),
        "the fault must name the OPERATION whose run did not return; got: {}",
        errors[0]
    );
    assert!(
        errors[0].contains("match_failed"),
        "and it must render the raised PAYLOAD. `operand_label` — the obvious \
         labeller to reach for — is a SORT labeller: it printed `RAISED `String`` for \
         `Error.raise(\"disk full\")`. `render_raised_payload` is the one owner of a \
         payload's text; got: {}",
        errors[0]
    );
    assert!(
        errors[0].contains("Error.reify"),
        "the repair named must be `Error.reify`. The obvious second suggestion — \
         declare the label and call it from a context that can handle it — is refused \
         on purpose: `effect_member_is_parametric` rejects `Error[T = P]` by design, so \
         declaring the label stops the WI-938 relational hook firing at all, i.e. 0 \
         solutions with `stats.errors` EMPTY, which is where this started; got: {}",
        errors[0]
    );
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "and no answer may be DEFINITE — the operation never returned a value"
    );
}

#[test]
fn a_bridged_operation_that_returns_reports_nothing() {
    // CONTROL (passes either way by design): the channel is quiet on a healthy bridge,
    // so the row above is not measuring "the fault list is simply never empty". This is
    // the ticket's own control — `guardExhaustible(5, ?r)` answers `?r = 5`.
    let (sols, errors) = resolve(GUARD_EXHAUSTIBLE, "bru.guard.control(?r)");
    assert!(
        errors.is_empty(),
        "a bridged call that RETURNED reports no fault; got {errors:?}"
    );
    assert!(
        sols.iter().any(|s| s.is_definite()),
        "`guardExhaustible(5)` = 5, so this must answer definitely"
    );
}

#[test]
fn the_literal_and_the_unreduced_operand_are_two_different_faults() {
    // BOTH present as `no solutions` and they are NOT the same defect. `0 - 5` reaches
    // the bridge un-reduced, so the guard `k > 0` compares a `Node` against an `Int64`
    // and the callee dies a TypeMismatch before it can raise. Only a probe inside the
    // bridge's `Err` arm told them apart when this was first measured; now the channel
    // does, which is the whole point of having one.
    //
    // CONTROL: this row passes under the back-out too, on its emptiness assertion
    // alone — so it is the `contains` pair that measures the channel.
    let (sols, errors) = resolve(GUARD_EXHAUSTIBLE, "bru.guard.unreduced(?r)");
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "an un-reduced operand still yields no definite answer"
    );
    assert_eq!(errors.len(), 1, "one fault; got {errors:?}");
    assert!(
        errors[0].contains("type mismatch"),
        "the un-reduced operand is a TYPE MISMATCH inside the callee, not a raise; \
         got: {}",
        errors[0]
    );
    assert!(
        !errors[0].contains("match_failed"),
        "and it must not be reported as the raise it is not; got: {}",
        errors[0]
    );
}

// ── ONE ROW PER CONSUMER ──────────────────────────────────────────────────────
//
// Four consumers were each written when faults were rare and specific — the only
// producer was `builtin_cmp`'s no-order arm. A bridged raise is far more common, and
// each row below says what that consumer now does with one.

#[test]
fn a_faulted_extent_read_refuses_rather_than_under_reporting() {
    // `read_facts_resolved` — the public 057 seam (anthill-todo's store, the CLI's
    // entry discovery, cpp-gen's realization rows). It already refuses loudly on
    // TRUNCATION ("a missing answer is undecided, not refuted"); a row whose derivation
    // RAISED owes the same refusal, and before this returned a silently SHORT list.
    //
    // CONTROL: `a_clean_extent_read_still_returns_its_rows` below passes either way.
    let src = r#"
namespace bru.ext
  import anthill.prelude.{Int64}
  operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k
  sort Rows
    entity derived(v: Int64)
    rule derived(v: ?x) :- guardExhaustible(0, ?x)
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let f = kb
        .try_resolve_symbol("bru.ext.Rows.derived")
        .expect("derived functor");
    let err = kb
        .read_facts_resolved(f, &[])
        .expect_err("a row whose derivation raised must refuse, not come back short");
    assert!(
        matches!(err, ExtentReadError::SearchFaulted { .. }),
        "and it must refuse as a FAULT, not as a truncation — the two have different \
         repairs; got {err:?}"
    );
    let text = err.to_string();
    assert!(
        text.contains("match_failed"),
        "carrying the raised payload; got: {text}"
    );
}

#[test]
fn a_clean_extent_read_still_returns_its_rows() {
    // CONTROL (passes either way by design): the new refusal did not swallow the
    // ordinary read.
    let src = r#"
namespace bru.extok
  import anthill.prelude.{Int64}
  operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k
  sort Rows
    entity derived(v: Int64)
    rule derived(v: ?x) :- guardExhaustible(5, ?x)
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let f = kb
        .try_resolve_symbol("bru.extok.Rows.derived")
        .expect("derived functor");
    let rows = kb
        .read_facts_resolved(f, &[])
        .expect("a healthy derivation still reads");
    assert_eq!(rows.len(), 1, "one row: `derived(v: 5)`; got {rows:?}");
}

#[test]
fn a_constraint_guard_over_a_raising_callee_blocks_the_load() {
    // THE CONSUMER THAT CAN STOP A PREVIOUSLY-LOADING PROGRAM, and the reason this
    // ticket says the decision had to be deliberate.
    //
    // The eager guards resolve `definite_only: true`, so a faulted goal's residual
    // never reaches them and they decide from EMPTINESS — guarded only by `truncated`,
    // which `ReduceFaults::fault` sets. Without that bit this constraint LOADS: the
    // quantified search comes back empty because the callee raised, and `no ?x: …`
    // reads empty as HOLDS. That is the silent-skip this repo's rules forbid — a
    // constraint reported satisfied by a search that never ran.
    //
    // THE SPLIT IS THE SAME ONE `builtin_cmp`'s no-order arm already makes, which is
    // why this is uniformity rather than a new policy: a FAULT at the producing site
    // marks the stream incomplete (`record_error`), while `step_naf`'s fold of a
    // sub-search's faults onto a DECIDED outer answer does not (`note_error`).
    //
    // CONTROL: `a_constraint_guard_over_a_returning_callee_still_loads` below.
    let src = r#"
namespace bru.cons
  import anthill.prelude.{Int64}
  operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k
  fact seed(0)
  constraint none_big: no ?x: seed(?x) -: guardExhaustible(?x, 1)
end
"#;
    let err = match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!(
            "a guard whose quantified search FAULTED must not be decided from its \
             emptiness — the callee raised, so nothing was measured"
        ),
        Err(errs) => errs.join("\n"),
    };
    assert!(
        err.contains("undecidable"),
        "the guard must report UNDECIDABLE rather than deciding; got:\n{err}"
    );
    assert!(
        err.contains("match_failed"),
        "and must carry the resolver's own words rather than blaming a depth budget \
         the search never approached; got:\n{err}"
    );
}

#[test]
fn a_constraint_guard_over_a_returning_callee_still_loads() {
    // CONTROL (passes either way by design): the guard path is not simply blocked for
    // every program that calls a bridged operation.
    let src = r#"
namespace bru.consok
  import anthill.prelude.{Int64}
  operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k
  fact seed(5)
  constraint none_big: no ?x: seed(?x) -: guardExhaustible(?x, 1)
end
"#;
    crate::common::try_load_kb_with(src)
        .expect("`guardExhaustible(5) = 5`, which is not 1, so the constraint HOLDS");
}

#[test]
fn a_contract_over_a_raising_callee_reports_the_raise() {
    // `prove_from_gamma_verdict` — the typer's contract bridge. It reads
    // `stats.errors.first()` and reports `GammaVerdict::Faulted`, so the author gets
    // the resolver's own words instead of the generic "left UNDISCHARGED … bind what it
    // waits on", which is advice no binding can satisfy here.
    //
    // WHAT THIS ROW ALSO RECORDS. `stats.errors` is per-STREAM while `Solution::
    // undecided` is per-ANSWER, so a raise on an UNRELATED branch of the same search
    // can now name an operation the conjunct never mentions. That ordering — fault
    // asked after the undecided cause, before the refutation check — is unchanged here
    // and is the site's own decision; what changes is that a bridged raise makes the
    // population reaching it far larger. A genuine `Refuted` is unreachable behind a
    // fault either way, because `ReduceFaults::fault` marks the stream incomplete and
    // only a complete empty search licenses the closed-world reading.
    //
    // CONTROL: `a_contract_over_a_returning_callee_discharges` below.
    let src = r#"
namespace bru.gam
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}
  sort Box
    entity box(value: Int64)
    operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k
    operation wrap(x: Int64) -> Box
      ensures eq(guardExhaustible(0), 0)
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let report = verify_proofs(&mut kb);
    let entry = report
        .iter()
        .find(|r| r.rule_qn.ends_with("wrap.ensures"))
        .expect("a proof-report entry for `wrap.ensures`");
    let ProofVerdict::Failed { reason } = &entry.verdict else {
        panic!(
            "a contract whose conjunct calls an operation that RAISED cannot discharge; \
             got {:?}",
            entry.verdict
        );
    };
    assert!(
        reason.contains("could not be EVALUATED"),
        "it must report the resolver's FAULT rather than a flounder; got: {reason}"
    );
    assert!(
        reason.contains("match_failed"),
        "and carry the raised payload, so the author sees what actually happened \
         instead of being told to bind something; got: {reason}"
    );
}

#[test]
fn a_contract_over_a_returning_callee_discharges() {
    // CONTROL (passes either way by design): the contract bridge is not simply failing
    // for every `ensures` that mentions a bridged operation.
    let src = r#"
namespace bru.gamok
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}
  sort Box
    entity box(value: Int64)
    operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k
    operation wrap(x: Int64) -> Box
      ensures eq(guardExhaustible(5), 5)
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let report = verify_proofs(&mut kb);
    let entry = report
        .iter()
        .find(|r| r.rule_qn.ends_with("wrap.ensures"))
        .expect("a proof-report entry for `wrap.ensures`");
    assert!(
        matches!(entry.verdict, ProofVerdict::Discharged),
        "`guardExhaustible(5) = 5` holds, so the contract discharges; got {:?}",
        entry.verdict
    );
}

#[test]
fn a_carrier_eq_that_raises_is_reported_too() {
    // THE SIBLING BRIDGE. `sem_eq_dispatch` runs a carrier's OWN `eq` member through
    // `bridge_eq_op_to_eval`, and its `Err` arm read `BuiltinResult::delay()` — "re-ask
    // me once something binds", which is false twice over here: the operands are already
    // ground, and nothing was said. The same defect this ticket is about, one bridge
    // over, and it takes the same `bridge_disposition` partition rather than a second
    // reading of it.
    //
    // TWO DIFFERENT VALUES, and the first fixture written for this used the same one
    // twice and passed with the arm backed out: `sem_eq_core`'s outcome 1 is
    // REFLEXIVITY, a verdict with no lookups, so `eq(green(), green())` never reaches
    // dispatch at all.
    //
    // CONTROL: `a_carrier_eq_that_returns_reports_nothing` below.
    let src = r#"
namespace bru.eqr
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}
  import anthill.kernel.{unify}

  sort Colour
    provides PartialEq[T = Colour]
    entity red
    entity green
    operation eq(a: Colour, b: Colour) -> Bool = match a case red() -> true
  end

  rule answer(?r) :- eq(green(), red()), unify(?r, 1)
  rule control(?r) :- eq(red(), green()), unify(?r, 1)
end
"#;
    let (sols, errors) = resolve(src, "bru.eqr.answer(?r)");
    assert_eq!(errors.len(), 1, "one fault; got {errors:?}");
    assert!(
        errors[0].contains("bru.eqr.Colour.eq") && errors[0].contains("match_failed"),
        "naming the carrier's own `eq` and the raised payload; got: {}",
        errors[0]
    );
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "and the goal residualizes rather than deciding — which it did before too, \
         silently; the fault is the half that was missing"
    );
}

#[test]
fn a_carrier_eq_that_returns_reports_nothing() {
    // CONTROL (passes either way by design): a carrier `eq` that RETURNS is quiet.
    let src = r#"
namespace bru.eqrok
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}
  import anthill.kernel.{unify}

  sort Colour
    provides PartialEq[T = Colour]
    entity red
    entity green
    operation eq(a: Colour, b: Colour) -> Bool = match a case red() -> true
  end

  rule control(?r) :- eq(red(), green()), unify(?r, 1)
end
"#;
    let (sols, errors) = resolve(src, "bru.eqrok.control(?r)");
    assert!(errors.is_empty(), "no fault; got {errors:?}");
    assert!(
        sols.iter().any(|s| s.is_definite()),
        "`Colour.eq(red, green)` answers `true`, so this decides"
    );
}

// ── THE PARTITION ─────────────────────────────────────────────────────────────

#[test]
fn the_raise_partition_is_by_cause_not_by_channel() {
    // `raise_relation_floundered` (WI-737 — an eval-side relation drain whose sub-search
    // stayed undischarged) and `raise_load_failed` (WI-SPGBP — `KB.loaded` reporting
    // that its sources do not load) ride `EvalError::Raised` and are NOT domain failures
    // of the callee. Testing the CHANNEL instead of the CAUSE sweeps them in, which is
    // what the reverted first attempt did.
    //
    // DRIVEN AT THE PREDICATE, not through a fixture: reaching either raise from a
    // bridged rule body needs a program that is itself about something else, and a row
    // whose fixture stops loading for an unrelated reason would go quietly green.
    //
    // CONTROL: `a_raise_that_escapes_a_bridged_operation_is_reported` is the same
    // predicate over a genuine raise, so the two together say the partition is on the
    // right seam rather than that the channel was left off. Back out the cause read
    // (`matches!(e, EvalError::Raised { .. }) => Fault`) and THIS row fails while that
    // one keeps passing.
    let kb = crate::common::load_kb_with(
        r#"
namespace bru.part
  import anthill.prelude.{Int64}
  fact anchor(1)
end
"#,
    );
    let raise_of = |qname: &str| {
        let functor = kb
            .try_resolve_symbol(qname)
            .unwrap_or_else(|| panic!("`{qname}` must be in the loaded prelude"));
        EvalError::Raised {
            payload: Value::Entity {
                functor,
                pos: Vec::new().into(),
                named: Vec::new().into(),
            },
        }
    };
    for qname in [
        "anthill.prelude.RelationFloundered.relation_floundered",
        "anthill.reflect.LoadFailed.load_failed",
    ] {
        assert_eq!(
            raise_of(qname).bridge_disposition(&kb),
            BridgeDisposition::Schedule,
            "`{qname}` is not a domain failure of the callee — it must reach the bridge \
             as Schedule, so the goal delays with nothing said"
        );
    }
    assert_eq!(
        raise_of("anthill.prelude.MatchFailed.match_failed").bridge_disposition(&kb),
        BridgeDisposition::Fault,
        "and every OTHER payload is a fault — a host raise rides a row it never appears \
         in, which is exactly the case the acceptance measures"
    );
}
