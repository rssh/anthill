//! WI-680 — smt-gen lowers a conditional (`ite`/`if`) and its boolean
//! condition in EXPRESSION position.
//!
//! Before WI-680, `translate_expr` handled arithmetic and treated inequalities
//! only as body-GOAL assertions; an `ite`/`if` subterm died with
//! `unhandled arithmetic op 'ite'`. That blocked any rule whose body binds a
//! variable to a conditional — including the defining rule WI-669 synthesizes
//! from a bodied op's `if`. Here a hand-written `ite`-bodied rule stands in for
//! the synthesized one (the surface `if` is parser-gated to operation bodies,
//! so a rule-body twin must spell it `ite(...)`).
//!
//! Coverage:
//!   - the emitted SMT contains a real `(ite <cond> ...)` (structural);
//!   - each Bool connective (`and`/`or`/`not`) is z3-validated by a verdict that
//!     FLIPS if the connective were miswired (a contradiction/tautology whose
//!     result depends on the exact connective, not just its presence);
//!   - z3 proves a TRUE property (`clamp(x) >= 0`) unsat and finds a
//!     counterexample for a FALSE one (`clamp(x) > 0`) — the lowering is not
//!     vacuously always-unsat;
//!   - a genuinely-free input var appearing ONLY inside an `ite` in a
//!     `FunctionLike` result's `(define-fun ...)` is still declared.

use super::common::{load_kb_with, run_z3, z3_available};

use anthill_smt_gen::{emit_satisfiability_check, emit_satisfiability_check_with, ProofConfig};

const SRC: &str = r#"
namespace test.wi680
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Ordered.{gte, lt, lte}
  import anthill.prelude.Bool.{and, or, not, ite}

  -- Hand-written stand-in for the WI-669 body-derived defining rule:
  -- clamp(x) = if x >= 0 then x else 0, spelled with the `ite` functor
  -- (surface `if` does not parse in a rule body).
  rule clamp(?x, ?r)
    :- ?r = ite(gte(?x, 0), ?x, 0)

  -- TRUE property `clamp(x) >= 0`: the violation `clamp(x) < 0` is unsat.
  rule clamp_negative(?w)
    :- clamp(?x, ?r),
       lt(?r, 0),
       ?w = ?r

  -- FALSE property `clamp(x) > 0`: the violation `clamp(x) <= 0` is sat
  -- (x < 0 gives clamp(x) = 0 <= 0). Guards against a vacuous lowering.
  rule clamp_nonpos(?w)
    :- clamp(?x, ?r),
       lte(?r, 0),
       ?w = ?r

  -- Structural connective coverage (works without z3): and(_, not(_)).
  rule band(?x, ?r)
    :- ?r = ite(and(gte(?x, 0), not(gte(?x, 10))), 1, 0)

  rule band_negative(?w)
    :- band(?x, ?r),
       lt(?r, 0),
       ?w = ?r

  -- `and` semantics: and(x>=0, x<0) is a CONTRADICTION ⇒ r is always 0.
  -- Violation `r >= 1` is unsat iff `and` is real (sat if it were `or`).
  rule cand(?x, ?r)
    :- ?r = ite(and(gte(?x, 0), lt(?x, 0)), 1, 0)
  rule cand_ge1(?w)
    :- cand(?x, ?r), gte(?r, 1), ?w = ?r

  -- `or` semantics: or(x>=0, x<0) is a TAUTOLOGY ⇒ r is always 2.
  -- Violation `r <= 1` is unsat iff `or` is real (sat if it were `and`).
  rule cor(?x, ?r)
    :- ?r = ite(or(gte(?x, 0), lt(?x, 0)), 2, 1)
  rule cor_le1(?w)
    :- cor(?x, ?r), lte(?r, 1), ?w = ?r

  -- `not` semantics: r = 1 iff NOT(x>=0), i.e. x < 0.
  -- Violation `x>=0 AND r>=1` is unsat iff `not` is real (sat if it were id).
  rule cnot(?x, ?r)
    :- ?r = ite(not(gte(?x, 0)), 1, 0)
  rule cnot_pos(?w)
    :- cnot(?x, ?r), gte(?x, 0), gte(?r, 1), ?w = ?r

  -- Finding-2 case: ?x appears ONLY inside the ite in a FunctionLike result's
  -- define-fun; it must be declared or z3 errors on an unknown constant.
  rule freevar(?w)
    :- ?w = ite(gte(?x, 0), ?x, 0)
end
"#;

fn emit(rule: &str) -> String {
    let kb = load_kb_with(SRC);
    emit_satisfiability_check(&kb, rule)
        .unwrap_or_else(|e| panic!("emit {rule}: {}", e.message))
}

/// Emit + run z3, returning its trimmed verdict. A z3 error (e.g. an undeclared
/// constant) yields neither "sat" nor "unsat", so the callers' `assert_eq!`
/// catches ill-formed SMT — it cannot silently pass.
fn verdict(rule: &str, slug: &str) -> String {
    let kb = load_kb_with(SRC);
    let smt = emit_satisfiability_check_with(&kb, rule, &ProofConfig::default())
        .unwrap_or_else(|e| panic!("emit {rule}: {}", e.message));
    run_z3(slug, &smt)
}

#[test]
fn ite_lowers_to_smt_ite_in_expression_position() {
    let smt = emit("test.wi680.clamp_negative");
    assert!(
        smt.contains("(ite (>= "),
        "the ite-bodied rule must lower to an SMT `(ite (>= ...) ...)` — got:\n{smt}"
    );
}

#[test]
fn boolean_connectives_lower_in_condition() {
    let smt = emit("test.wi680.band_negative");
    assert!(
        smt.contains("(and ") && smt.contains("(not "),
        "and(_, not(_)) condition must lower to `(and ...)` / `(not ...)` — got:\n{smt}"
    );
}

#[test]
fn true_property_is_unsat() {
    if !z3_available() { eprintln!("z3 not available — skipping"); return; }
    let v = verdict("test.wi680.clamp_negative", "wi680_clamp_nonneg");
    assert_eq!(v, "unsat", "clamp(x) >= 0 holds ⇒ its violation is unsat — got {v:?}");
}

#[test]
fn false_property_is_sat() {
    if !z3_available() { eprintln!("z3 not available — skipping"); return; }
    let v = verdict("test.wi680.clamp_nonpos", "wi680_clamp_nonpos");
    assert_eq!(v, "sat", "clamp(x) > 0 is FALSE (x<0 ⇒ clamp=0) ⇒ its violation is sat — got {v:?}");
}

#[test]
fn and_semantics_z3() {
    if !z3_available() { eprintln!("z3 not available — skipping"); return; }
    // and(x>=0, x<0) is a contradiction ⇒ r=0 ⇒ `r>=1` unsat. Would be sat if
    // `and` were lowered as `or`.
    let v = verdict("test.wi680.cand_ge1", "wi680_and");
    assert_eq!(v, "unsat", "`and` contradiction ⇒ r never 1 — got {v:?}");
}

#[test]
fn or_semantics_z3() {
    if !z3_available() { eprintln!("z3 not available — skipping"); return; }
    // or(x>=0, x<0) is a tautology ⇒ r=2 ⇒ `r<=1` unsat. Would be sat if `or`
    // were lowered as `and`.
    let v = verdict("test.wi680.cor_le1", "wi680_or");
    assert_eq!(v, "unsat", "`or` tautology ⇒ r always 2 — got {v:?}");
}

#[test]
fn not_semantics_z3() {
    if !z3_available() { eprintln!("z3 not available — skipping"); return; }
    // r=1 iff not(x>=0) i.e. x<0; so `x>=0 AND r>=1` unsat. Would be sat if
    // `not` were the identity.
    let v = verdict("test.wi680.cnot_pos", "wi680_not");
    assert_eq!(v, "unsat", "`not(x>=0)` false when x>=0 ⇒ r=0 — got {v:?}");
}

#[test]
fn free_var_only_in_ite_body_is_declared() {
    if !z3_available() { eprintln!("z3 not available — skipping"); return; }
    // `?x` appears only inside the ite in `freevar`'s (define-fun var_w ...);
    // with the body_smtlib scan it is declared and z3 solves (sat). Without it,
    // z3 errors on an unknown constant ⇒ verdict != "sat".
    let v = verdict("test.wi680.freevar", "wi680_freevar");
    assert_eq!(v, "sat", "a free input inside an ite-bound result must be declared — got {v:?}");
}
