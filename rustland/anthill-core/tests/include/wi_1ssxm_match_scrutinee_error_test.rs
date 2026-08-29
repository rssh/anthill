//! WI-20260829-1SSXM — a MATCH SCRUTINEE's type error is no longer SILENTLY DROPPED.
//!
//! `TypeBuildFrame::MatchAfterScrutinee` read the scrutinee's result through `.ok()`
//! three times and never re-pushed its `Err`. The match then typed its arms against
//! `scr_ty = None` and put the UN-REWRITTEN scrutinee node back into the stored tree, so
//! an ill-typed scrutinee made the whole match report NOTHING and the program LOADED.
//! Every other build frame propagates a child failure (`LambdaBody` re-pushes it;
//! `IfExpr` / `Apply` / `Constructor` run their children through `collect_arg_errors`);
//! this was the only one that did not.
//!
//! WHAT WI-20260828-N2FHM ALREADY CLOSED, AND WHY THESE CASES ARE NOT IT. That ticket
//! added `surviving_dot_apply`, a backstop refusing a STORED body that still holds an
//! `Expr::DotApply` — the one consequence eval cannot report (it raises
//! `Internal("unhandled Expr variant in eval")`, which is not a `Raised` payload, so no
//! handler sees it). It closes the DOT case and nothing else. Every case below is a
//! scrutinee error with NO dot in it, so the backstop cannot see any of them: before the
//! propagation each of these programs loaded clean and the error was simply gone.
//!
//! WHAT THE PROPAGATION COST, on the corpus: 13 tests across three unrelated roots, all
//! of them programs the typer had already decided were ill-typed. Two were genuine
//! under-specifications repaired in place (`anthill-todo/anthill/store.anthill`'s
//! unpinned `term_as_entity`; `kb_query_test` / `wi531_solution_residual_test` splitting
//! a bare `Stream` through `LogicalStream.splitFirst`). The third was an untypable
//! fixture body — see the note on `Mapped.splitFirst` in
//! `wi590_witness_param_carrier_test` for the decision.
//!
//! CONTROLS AND WHAT EACH SEPARATES:
//!   * `control_the_same_error_in_an_argument_position` — the SAME ill-typed call as an
//!     ARGUMENT, which `Apply`'s `collect_arg_errors` has always propagated. It is what
//!     attributes the defect to the SCRUTINEE POSITION rather than to the expression.
//!   * `control_the_pinned_spelling_loads` — the repair spelling for the unconstrained
//!     case (`unpin[Int64](1)`), which is what `store.anthill:391` now writes.
//!   * `control_a_well_typed_match_still_runs` — a well-typed match over the same
//!     operations, DRIVEN to its value. It is what says the propagation refuses ill-typed
//!     scrutinees and not matches.
//! All three pass with the change backed out.
//!
//! BACKING THE CHANGE OUT — restore the three `.ok()` reads in `MatchAfterScrutinee`
//! (`scr_ty` / `scr_effects` / `scr_node` back to `Option`, with `scr_node` falling back
//! to `occ`'s written scrutinee) ⟹ `a_type_mismatch_in_a_scrutinee_fails_the_load` and
//! `an_unconstrained_type_param_in_a_scrutinee_fails_the_load` both fail, and they fail
//! by LOADING CLEAN — which is the defect. The three controls pass either way.

/// Every case shares these declarations; only the operation under test differs.
fn program(ops: &str) -> String {
    format!(
        r#"
namespace wi1ssxm
  import anthill.prelude.{{List, Option, Int64, String, Bool}}
  import anthill.prelude.List.{{headOption}}
  import anthill.prelude.Option.{{some, none}}

  operation rows() -> List[T = Int64] = [1, 2, 3]

  -- The R1 shape in miniature: a type param that appears ONLY in the return, so
  -- nothing but a written type arg or an expected type can pin it.
  operation unpin[E](n: Int64) -> Option[T = E] = none

  operation consume(o: Option[T = Int64]) -> Bool =
    match o
      case some(_) -> true
      case none() -> false

{ops}
end
"#
    )
}

/// Load `program(ops)` and return the load errors (empty when it loads clean).
fn load_errors(ops: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(&program(ops)) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

// ── DRIVING CASES — each loaded CLEAN before the propagation ─────────────────

/// DRIVES THE FIX. An op-arg type mismatch inside the scrutinee: `headOption` takes a
/// `List` and is handed a `String`. No dot anywhere, so `surviving_dot_apply` never sees
/// it. RED with the propagation backed out — the program loads with zero errors.
#[test]
fn a_type_mismatch_in_a_scrutinee_fails_the_load() {
    let errs = load_errors(
        "  operation bad_scrutinee() -> Bool =\n    \
           match headOption(\"not a list\")\n      \
             case some(_) -> true\n      \
             case none() -> false",
    );
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "an ill-typed match scrutinee must FAIL THE LOAD, not be dropped; got {errs:?}",
    );
    assert!(
        errs.iter().any(|e| e.contains("headOption")),
        "the refusal must name the scrutinee's own call; got {errs:?}",
    );
}

/// DRIVES THE FIX — the R1 class, and the reason the corpus had a live instance of it.
/// A match scrutinee supplies NO expected type, so a callee whose type param appears
/// only in its RETURN is left unconstrained there. `store.anthill:391` wrote exactly
/// this against `term_as_entity` and loaded clean for it. RED with the propagation
/// backed out.
#[test]
fn an_unconstrained_type_param_in_a_scrutinee_fails_the_load() {
    let errs = load_errors(
        "  operation bad_unpinned() -> Bool =\n    \
           match unpin(1)\n      \
             case some(_) -> true\n      \
             case none() -> false",
    );
    assert!(
        errs.iter().any(|e| e.contains("unconstrained")),
        "an unconstrained type param in a match scrutinee must FAIL THE LOAD; got {errs:?}",
    );
    assert!(
        errs.iter().any(|e| e.contains("'E'")),
        "the refusal must name the parameter it could not pin; got {errs:?}",
    );
}

// ── CONTROLS — every one passes with the change backed out ───────────────────

/// CONTROL — the SAME ill-typed call, moved out of the scrutinee into an ARGUMENT.
/// `Apply` drains its children through `collect_arg_errors` and always has, so this was
/// a load error before the propagation too. Holding the expression fixed and varying
/// only its POSITION is what attributes the defect to `MatchAfterScrutinee` rather than
/// to `headOption`, to strings, or to the type checker at large.
#[test]
fn control_the_same_error_in_an_argument_position() {
    let errs = load_errors("  operation bad_argument() -> Bool = consume(headOption(\"not a list\"))");
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "an ill-typed ARGUMENT has always been a load error; got {errs:?}",
    );
}

/// CONTROL — the repair spelling for the unconstrained case, which is what
/// `store.anthill:391` now writes (`term_as_entity[WorkItem](t)`). Writing the type arg
/// pins `E` with no expected type in sight, so the scrutinee types and the match loads.
/// Green either way: with the swallow in place this loaded too, for the wrong reason.
#[test]
fn control_the_pinned_spelling_loads() {
    let errs = load_errors(
        "  operation pinned() -> Bool =\n    \
           match unpin[Int64](1)\n      \
             case some(_) -> true\n      \
             case none() -> false",
    );
    assert!(
        errs.is_empty(),
        "writing the type arg pins `E`, so the match must load; got {errs:?}",
    );
}

/// CONTROL — and the one that DRIVES rather than loads. A well-typed match over the same
/// `headOption` runs and answers. It is what separates "the frame propagates a real
/// failure" from "the frame now fails matches": if the early return were reached on an
/// `Ok` scrutinee this would stop loading, and if the scrutinee's node or type were lost
/// on the way through it would stop answering `true`.
#[test]
fn control_a_well_typed_match_still_runs() {
    let mut interp = crate::common::interp_for(&program(
        "  operation good() -> Bool =\n    \
           match headOption(rows())\n      \
             case some(_) -> true\n      \
             case none() -> false",
    ));
    let v = interp.call("wi1ssxm.good", &[]).expect("good must run");
    assert_eq!(
        crate::common::scalar_bool(interp.kb(), &v),
        Some(true),
        "a well-typed match over a non-empty list must answer true; got {v:?}",
    );
}
