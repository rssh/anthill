//! WI-686 — close a body-derived constructor whose field is computed from a
//! SCALAR operation parameter (not just entity params).
//!
//! WI-681 taught `close_occ` to close a returned constructor over its ENTITY
//! params (a `Vec3` whose fields read `leader.position.x` / `offset.x`). But a
//! scalar param appearing bare inside a returned constructor field —
//! `Wrapper(v: if gte(x, 0) then x else 0)`, `x` a `Float` param — died with
//! "a scalar operation parameter inside a constructor cannot be closed across
//! the inline boundary": scalar params live in the callee STRING map, not the
//! entity `env`.
//!
//! WI-686 threads that string map into `close_occ` as a second channel: a
//! scalar DeBruijn resolves to its caller-frame SMT fragment (a `var_k` stays a
//! resolvable var; anything else rides as a pre-rendered fragment) rather than
//! erroring. The op then synthesizes a defining rule (WI-669 seam), which the
//! emitter inlines at `Ops.clamp(?x, ?r)`; the later `?r.v` field access lowers
//! to the `ite` over the caller's `?x`.
//!
//! Coverage:
//!   - structural: the emitted SMT carries a real `(ite (>= ...) ...)` reached
//!     THROUGH the closed constructor's field access (would be a `close_occ`
//!     error before WI-686);
//!   - z3: the TRUE property `clamp(x) >= 0` (violation `clamp(x) < 0`) is
//!     unsat, and the FALSE property `clamp(x) > 0` (violation `clamp(x) <= 0`)
//!     is sat — the ite is real and correctly wired to the scalar param, not
//!     vacuously always-unsat.

use super::common::{load_kb_with, run_z3, z3_available};
use anthill_core::intern::Symbol;
use anthill_core::kb::op_info::all_operation_params;
use anthill_core::kb::KnowledgeBase;
use anthill_smt_gen::{emit_satisfiability_check_with, ProofConfig};

fn build_kb() -> KnowledgeBase {
    let source = r#"
        namespace test.smt_gen.wi686
          import anthill.prelude.{Float, Bool}
          import anthill.prelude.Ordered.{lt, lte, gte}

          entity Wrapper(v: Float)

          sort Ops
            operation clamp(x: Float) -> Wrapper =
              let clamped = if gte(x, 0.0) then x else 0.0
              Wrapper(v: clamped)
          end

          -- TRUE property `clamp(x).v >= 0`: the violation `< 0` is unsat.
          rule clamp_negative(?w)
            :- Ops.clamp(?x, ?r),
               ?v = ?r.v,
               lt(?v, 0.0),
               ?w = ?v

          -- FALSE property `clamp(x).v > 0`: the violation `<= 0` is sat
          -- (x < 0 gives clamp = 0 <= 0). Guards against a vacuous lowering.
          rule clamp_nonpos(?w)
            :- Ops.clamp(?x, ?r),
               ?v = ?r.v,
               lte(?v, 0.0),
               ?w = ?v

          -- Concrete-literal input: the scalar arg is `-2.0`, threaded into
          -- the callee string map as the rendered fragment `(- 2.0)` (NOT a
          -- forwarded `var_j`) — exercising `scalar_param_occ`'s frozen-
          -- fragment path with a compound literal. clamp(-2).v = 0, so the
          -- violation `< 0` is unsat AND the input `(- 2.0)` reaches the ite.
          rule clamp_neg_literal(?w)
            :- Ops.clamp(-2.0, ?r),
               ?v = ?r.v,
               lt(?v, 0.0),
               ?w = ?v
        end
    "#;
    load_kb_with(source)
}

fn clamp_sym(kb: &KnowledgeBase) -> Symbol {
    all_operation_params(kb)
        .into_iter()
        .map(|(s, _)| s)
        .find(|s| kb.resolve_sym(*s).rsplit('.').next() == Some("clamp"))
        .expect("clamp op")
}

fn emit(rule: &str) -> String {
    let mut kb = build_kb();
    // The seam step: synthesize clamp's body-derived defining rule so the
    // emitter inlines it at the `Ops.clamp(?x, ?r)` call.
    kb.synthesize_op_defining_rule(clamp_sym(&kb))
        .expect("clamp synthesizes a defining rule");
    let cfg = ProofConfig { logic: Some("QF_LRA".to_string()), ..Default::default() };
    emit_satisfiability_check_with(&kb, rule, &cfg)
        .unwrap_or_else(|e| panic!("emit {rule}: {}", e.message))
}

#[test]
fn scalar_param_constructor_field_lowers_to_ite() {
    let smt = emit("test.smt_gen.wi686.clamp_negative");
    // The scalar-param `if` reaches the document as an `ite` — reached only by
    // closing the returned Wrapper over the scalar channel and field-accessing
    // its `v`. Before WI-686 this emit errored in `close_occ`.
    assert!(
        smt.contains("(ite (>= "),
        "the scalar-param constructor field must lower to `(ite (>= ...) ...)`:\n{smt}"
    );
}

#[test]
fn true_property_is_unsat() {
    if !z3_available() {
        eprintln!("z3 not available — skipping");
        return;
    }
    let smt = emit("test.smt_gen.wi686.clamp_negative");
    let v = run_z3("wi686_clamp_nonneg", &smt);
    assert_eq!(v, "unsat", "clamp(x).v >= 0 holds ⇒ its violation is unsat — got {v:?}\n{smt}");
}

#[test]
fn false_property_is_sat() {
    if !z3_available() {
        eprintln!("z3 not available — skipping");
        return;
    }
    let smt = emit("test.smt_gen.wi686.clamp_nonpos");
    let v = run_z3("wi686_clamp_nonpos", &smt);
    assert_eq!(v, "sat", "clamp(x).v > 0 is FALSE (x<0 ⇒ clamp=0) ⇒ its violation is sat — got {v:?}\n{smt}");
}

#[test]
fn concrete_literal_input_flows_through_frozen_fragment() {
    let smt = emit("test.smt_gen.wi686.clamp_neg_literal");
    // The `-2.0` scalar arg reaches the ite as the rendered fragment `(- 2.0)`
    // — the frozen-fragment (non-`var_j`) path of `scalar_param_occ`.
    assert!(
        smt.contains("(- 2.0)"),
        "the concrete -2.0 input must reach the ite via the frozen fragment:\n{smt}"
    );
    if !z3_available() {
        eprintln!("z3 not available — skipping z3 check");
        return;
    }
    // clamp(-2).v = 0, so the violation `clamp(-2).v < 0` is unsat. Were the
    // scalar param NOT closed (left free), it would be sat.
    let v = run_z3("wi686_clamp_neg_literal", &smt);
    assert_eq!(v, "unsat", "clamp(-2).v = 0 ⇒ `< 0` violation is unsat — got {v:?}\n{smt}");
}
