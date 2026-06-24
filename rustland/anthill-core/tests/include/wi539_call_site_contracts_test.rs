//! WI-539 (proposal 050 "operation call" modification rule): call-site operation
//! contracts over the local-interpretation environment Γ.
//!
//! At a call `y = callee(args)` the typer now, with σ mapping the callee's
//! parameters to the actual arguments (and `result` to `y`):
//!   * **checks `requires`** — the callee's value precondition `σ(requires)` must
//!     be PROVED from Γ (the same `prove_from_gamma` bridge a guarded effect is
//!     refuted with, at the OPPOSITE polarity — an obligation, not an optional
//!     drop). An unproved precondition (including one that flounders over a
//!     symbolic argument) is a loud `UnsatisfiedPrecondition` error.
//!   * **assumes `ensures`** — the callee's postcondition `σ(ensures)` enters Γ
//!     for the code after the call, so a later guard discharge / requires-check
//!     reads it straight from Γ with no branch test written.
//!
//! Both are asserted at LOAD time (the contract check runs during the typing pass
//! that loading drives), the same harness as `wi067_guard_discharge_test`.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load stdlib + user source together; surface load errors as strings.
/// Identical harness to `wi067_guard_discharge_test::load_result`.
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
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

// ── requires (the obligation half) ──────────────────────────────────────────

/// `needy` carries a value precondition `requires neq(b, 0)`. The caller body
/// varies per test; only bodies that establish `neq(b, 0)` at the call may load.
const NEEDY_PRELUDE: &str = r#"
  import anthill.prelude.{Int64}

  operation needy(b: Int64) -> Int64
    requires neq(b, 0)
    = b
"#;

#[test]
fn precondition_proved_by_nonzero_literal() {
    // `needy(5)` — σ maps `b ↦ 5`, the precondition `neq(5, 0)` is proved by
    // ground evaluation, so the obligation is discharged and the call loads clean.
    let src = format!(
        r#"
namespace anthill.test.wi539lit
{NEEDY_PRELUDE}
  operation caller() -> Int64 =
    needy(5)
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "a non-zero literal argument proves `neq(5, 0)`, discharging the \
         precondition; the call must load clean. got: {:#?}",
        res.err()
    );
}

#[test]
fn precondition_proved_by_if_guard() {
    // `if neq(b, 0) then needy(b)` — the then-branch Γ carries `neq(b, 0)` (the
    // 050 if-fork narrowing), so the precondition is proved straight from Γ.
    let src = format!(
        r#"
namespace anthill.test.wi539if
{NEEDY_PRELUDE}
  operation caller(b: Int64) -> Int64 =
    if neq(b, 0) then needy(b) else 0
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "an enclosing `if neq(b, 0)` narrows Γ so `needy(b)` in the then-branch \
         proves its precondition; the body must load clean. got: {:#?}",
        res.err()
    );
}

#[test]
fn precondition_unproved_for_symbolic_argument() {
    // `needy(b)` with `b` an unconstrained parameter: `neq(b, 0)` flounders
    // (open-world — `b` could be 0), so the precondition is NOT proved. An
    // undischarged obligation is a loud error (never NAF-"satisfied").
    let src = format!(
        r#"
namespace anthill.test.wi539sym
{NEEDY_PRELUDE}
  operation caller(b: Int64) -> Int64 =
    needy(b)
end
"#
    );
    let errs = load_result(&src).expect_err(
        "a symbolic argument cannot prove `neq(b, 0)`, so the precondition is \
         undischarged and the call must fail to load",
    );
    assert!(
        errs.iter().any(|e| e.contains("precondition")),
        "expected an unsatisfied-precondition error; got: {errs:#?}"
    );
}

#[test]
fn precondition_unproved_for_zero_literal() {
    // `needy(0)` — the precondition `neq(0, 0)` is FALSE, so it cannot be proved
    // and the obligation fails (the dual of the literal-nonzero pass: a positive
    // proof is required, and there is none).
    let src = format!(
        r#"
namespace anthill.test.wi539zero
{NEEDY_PRELUDE}
  operation caller() -> Int64 =
    needy(0)
end
"#
    );
    let errs = load_result(&src).expect_err(
        "a literal-zero argument makes `neq(0, 0)` false — unprovable, so the \
         precondition is undischarged and the call must fail",
    );
    assert!(
        errs.iter().any(|e| e.contains("precondition")),
        "expected an unsatisfied-precondition error; got: {errs:#?}"
    );
}

// ── ensures (the contract-knowledge-into-Γ half) ────────────────────────────

/// `mk_nonzero` promises `ensures neq(result, 0)`; `anyInt` promises nothing.
/// Both take a seed (so the call is an `Apply` with arguments — the `ensures`
/// rule keys off a direct call binding). The bodies are immaterial: WI-539 checks
/// `ensures` at the CALL site, not against the body (that is the deferred Part 2,
/// the `<op>.<clause>` contract-proof).
const ENSURES_PRELUDE: &str = r#"
  import anthill.prelude.{Int64}
  import anthill.prelude.Int64.{div}

  operation mk_nonzero(seed: Int64) -> Int64
    ensures neq(result, 0)
    = seed

  operation anyInt(seed: Int64) -> Int64
    = seed
"#;

#[test]
fn ensures_discharges_a_later_div_guard() {
    // `let y = mk_nonzero(7); let q = div(100, y); q`. The callee's
    // `ensures neq(result, 0)` enters Γ as `neq(y, 0)` (`result ↦ y`), so
    // `div(100, y)` refutes its guard `eq(y, 0)` straight from Γ (WI-479 migrated
    // `div` to the guarded `Error[DivisionByZero] :- eq(b, 0)`). The body is then
    // PURE, so `caller` need not declare the effect — contract knowledge flowing
    // through Γ. (The `div` is bound by an inner `let` ending in a bare var rather
    // than left as the trailing op body: a bare-call let-chain tail directly before
    // `end` trips a GLR parse ambiguity — orthogonal to the contract logic here.)
    let src = format!(
        r#"
namespace anthill.test.wi539ens
{ENSURES_PRELUDE}
  operation caller() -> Int64 =
    let y = mk_nonzero(7)
    let q = div(100, y)
    q
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "the callee's `ensures neq(result, 0)` must enter Γ as `neq(y, 0)` and \
         discharge the `div(100, y)` guard; the body is pure. got: {:#?}",
        res.err()
    );
}

#[test]
fn no_ensures_keeps_the_div_guard() {
    // The same body over `anyInt`, which promises NOTHING: Γ carries no
    // disequality for `y`, so `div(100, y)`'s guard `eq(y, 0)` is NOT refuted and
    // `Error[DivisionByZero]` stays conservatively present — an undeclared use
    // must fail. This isolates the `ensures` as the cause of the discharge above.
    let src = format!(
        r#"
namespace anthill.test.wi539noens
{ENSURES_PRELUDE}
  operation caller() -> Int64 =
    let y = anyInt(7)
    let q = div(100, y)
    q
end
"#
    );
    let errs = load_result(&src).expect_err(
        "without an `ensures`, nothing in Γ refutes `eq(y, 0)`, so the guarded \
         `Error[DivisionByZero]` is present; omitting it must fail",
    );
    assert!(
        errs.iter().any(|e| e.contains("DivisionByZero")),
        "expected the conservatively-present Error[DivisionByZero] to surface as \
         undeclared; got: {errs:#?}"
    );
}

// ── multi-goal (conjunction) clauses ────────────────────────────────────────

#[test]
fn requires_multi_goal_conjunction_all_proved() {
    // A `requires` with two comma-separated goals lowers to ONE
    // `conjunction(neq(b,0), gt(b,0))` clause. `needy2(5)` grounds both conjuncts
    // (`neq(5,0)`, `gt(5,0)` — proved by evaluation), so the precondition holds and
    // the call loads clean. Without splitting the conjunction the typer would try
    // to prove the opaque `conjunction(...)` as one goal (no SLD rule resolves it)
    // and spuriously reject this valid call.
    let src = r#"
namespace anthill.test.wi539conjreq
  import anthill.prelude.{Int64}
  operation needy2(b: Int64) -> Int64
    requires neq(b, 0), gt(b, 0)
    = b
  operation caller() -> Int64 = needy2(5)
end
"#;
    let res = load_result(src);
    assert!(
        res.is_ok(),
        "a multi-goal `requires neq(b,0), gt(b,0)` must be checked conjunct-by-conjunct; \
         `needy2(5)` proves both and must load clean. got: {:#?}",
        res.err()
    );
}

#[test]
fn ensures_multi_goal_conjunction_conjunct_discharges() {
    // A multi-goal `ensures neq(result,0), gt(result,0)` lowers to one
    // `conjunction(...)` clause; assuming it must split into the per-goal facts
    // `neq(y,0)` and `gt(y,0)`. The `div(100, y)` guard `eq(y,0)` is refuted by the
    // `neq(y,0)` conjunct, so the body is pure. Without splitting, Γ would hold one
    // opaque `conjunction(...)` fact the guard query `neq(y,0)` never matches, and
    // the call would fail to load.
    let src = r#"
namespace anthill.test.wi539conjens
  import anthill.prelude.{Int64}
  import anthill.prelude.Int64.{div}
  operation mk2(seed: Int64) -> Int64
    ensures neq(result, 0), gt(result, 0)
    = seed
  operation caller() -> Int64 =
    let y = mk2(7)
    let q = div(100, y)
    q
end
"#;
    let res = load_result(src);
    assert!(
        res.is_ok(),
        "a multi-goal `ensures` must enter Γ as separate conjunct facts so the \
         `neq(y,0)` conjunct discharges the `div(100, y)` guard; the body is pure. \
         got: {:#?}",
        res.err()
    );
}
