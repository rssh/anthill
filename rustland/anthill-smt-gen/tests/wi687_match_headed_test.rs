//! WI-687 — end-to-end SMT emit + z3 for a MATCH-headed bodied op specialized
//! per call-site.
//!
//! `pick(o: Option[Float], base) = match o { none() -> base; some(x) -> if x>=0
//! then base+x else base }` has a top-level `match` on the `o` parameter. The
//! generic (abstract-parameter) defining-rule synthesis declines it; the seam
//! (`synthesize_body_derived_defrules`) retries per call-site, building a
//! CONSTRUCTOR-SHAPED defining rule `pick(some(?0), ?1, ?result) :- ?result =
//! ite(?0>=0, ?1+?0, ?1)` from the obligation's concrete `some(?x)` argument.
//! The emitter's `try_inline_rule_call` binds that head STRUCTURALLY against the
//! call, connecting the caller's `?x` / `?base` to the ite.
//!
//! Coverage:
//!   - structural: the emitted SMT carries a real `(ite (>= ...) ...)`;
//!   - z3 (some arm selected + ite real): `pick(some(x),base) >= base` holds
//!     (violation `< base` unsat), and `> base` is sat (x>0 witness) — a wrong
//!     none-arm reduction would make `> base` unsat;
//!   - z3 (none arm selected): `pick(none, base) = base`, so `> base` is unsat.

use super::common::{load_kb_with, run_z3, z3_available};
use anthill_core::kb::KnowledgeBase;
use anthill_smt_gen::{emit_satisfiability_check_with, ProofConfig};

fn build_kb() -> KnowledgeBase {
    let source = r#"
        namespace test.smt_gen.wi687
          import anthill.prelude.{Float, Bool, Option}
          import anthill.prelude.Ordered.{lt, gt, gte}
          import anthill.prelude.Numeric.{add}
          import anthill.prelude.Option.{some, none}

          sort Ops
            -- top-level match on the Option parameter; `none()` is the
            -- nullary-constructor pattern (a bare `none` is a catch-all var).
            operation pick(o: Option[T = Float], base: Float) -> Float =
              match o
                case none() -> base
                case some(x) -> if gte(x, 0.0) then add(base, x) else base
          end

          -- TRUE property `pick(some(x), base) >= base`: violation `< base` unsat.
          -- Unsat needs BOTH ite arms (x>=0: base+x>=base; x<0: base>=base), so it
          -- genuinely exercises the reduced conditional.
          rule pick_lt_base(?w)
            :- Ops.pick(some(?x), ?base, ?r),
               lt(?r, ?base),
               ?w = ?r

          -- `pick > base` is SAT (x>0 gives base+x > base): confirms the SOME arm
          -- was selected (not none) and the ite is real, not vacuously unsat.
          rule pick_gt_base(?w)
            :- Ops.pick(some(?x), ?base, ?r),
               gt(?r, ?base),
               ?w = ?r

          -- none arm: pick(none, base) = base, so `pick > base` is unsat — a wrong
          -- some-arm reduction here would instead be sat.
          rule pick_none_gt_base(?w)
            :- Ops.pick(none, ?base, ?r),
               gt(?r, ?base),
               ?w = ?r
        end
    "#;
    load_kb_with(source)
}

fn emit(rule: &str) -> String {
    let mut kb = build_kb();
    // The seam: per-call-site synthesize pick's match-headed defining rule at the
    // obligation's concrete-constructor argument, so the emitter inlines it.
    kb.synthesize_body_derived_defrules(rule);
    let cfg = ProofConfig { logic: Some("QF_LRA".to_string()), ..Default::default() };
    emit_satisfiability_check_with(&kb, rule, &cfg)
        .unwrap_or_else(|e| panic!("emit {rule}: {}", e.message))
}

#[test]
fn match_headed_some_arm_lowers_to_ite() {
    let smt = emit("test.smt_gen.wi687.pick_lt_base");
    // The reduced some-arm `if x>=0 then base+x else base` reaches the document as
    // an `ite`, reached ONLY by reducing the match at the concrete `some(?x)` and
    // structurally binding the head `some(?0)` to the caller's `?x`.
    assert!(
        smt.contains("(ite (>= "),
        "the match-headed some-arm must lower to `(ite (>= ...) ...)`:\n{smt}"
    );
}

#[test]
fn some_arm_true_property_is_unsat() {
    if !z3_available() {
        eprintln!("z3 not available — skipping");
        return;
    }
    let smt = emit("test.smt_gen.wi687.pick_lt_base");
    let v = run_z3("wi687_pick_ge_base", &smt);
    assert_eq!(v, "unsat",
        "pick(some(x),base) >= base holds ⇒ its violation `< base` is unsat — got {v:?}\n{smt}");
}

#[test]
fn some_arm_selected_not_none() {
    if !z3_available() {
        eprintln!("z3 not available — skipping");
        return;
    }
    let smt = emit("test.smt_gen.wi687.pick_gt_base");
    let v = run_z3("wi687_pick_gt_base", &smt);
    assert_eq!(v, "sat",
        "pick(some(x),base) > base is satisfiable (x>0) ⇒ the some arm was selected \
         and the ite is real — got {v:?}\n{smt}");
}

#[test]
fn none_arm_selected() {
    if !z3_available() {
        eprintln!("z3 not available — skipping");
        return;
    }
    let smt = emit("test.smt_gen.wi687.pick_none_gt_base");
    let v = run_z3("wi687_pick_none_gt_base", &smt);
    assert_eq!(v, "unsat",
        "pick(none, base) = base ⇒ `> base` is unsat (a wrong some-arm reduction would \
         be sat) — got {v:?}\n{smt}");
}
