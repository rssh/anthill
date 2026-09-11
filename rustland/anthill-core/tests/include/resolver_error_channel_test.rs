//! `BuiltinResult::Error` — the resolver can finally SAY a goal was un-evaluable.
//!
//! Before this, a builtin had three outcomes and none of them fit an ill-typed or
//! unsupported goal. `builtin_cmp`'s no-order arm — `gt("a", 3)`, a String against an
//! Int64 — worked around it three times over:
//!
//!   * `Delay { truncated: true }` faked the OUTCOME. The operands are already GROUND,
//!     so "re-ask me once something binds" was simply false; `Delay` was chosen because
//!     residualizing was the one available shape that made no claim.
//!   * `eprintln!("[wi879] …")` faked the DIAGNOSTIC, on stderr, deduped in a
//!     process-wide `thread_local` so the SECOND query in a process printed nothing.
//!   * (`truncated: true` was NOT a fake and is unchanged — an un-evaluable goal really
//!     does mean emptiness is not refutation.)
//!
//! `Error` replaces the first two: the goal still residualizes, and its message rides
//! `ResolveStats::errors` where a test can assert it and a CLI can render it.
//!
//! CONTROLS, and what each measures. Back out the arm (return
//! `BuiltinResult::Delay { truncated: true }` and drop the message) and:
//!   * `an_unorderable_comparison_reports_a_diagnostic` FAILS — the only row that
//!     measures the new channel.
//!   * `an_unorderable_comparison_still_residualizes` PASSES EITHER WAY, by design. It
//!     is the WI-879 property this change had to PRESERVE — that arm's own doc calls the
//!     residual "the machine-readable half … what a test can assert" — and it is what
//!     fails instead if `Error` is given aborting or branch-failing semantics.
//!   * `a_well_typed_comparison_reports_nothing` PASSES EITHER WAY, by design: it says
//!     the channel is not simply always non-empty.

use anthill_core::kb::resolve::ResolveConfig;

/// `tag("a")` binds `?x` from a predicate that declares no types, so the typer cannot
/// see the operand sorts and `gt(?x, 1)` reaches the resolver as a String/Int64 pair.
/// (Written DIRECTLY the typer refuses it — that is WI-879's own control.)
const CROSS_SORT: &str = r#"
namespace rec.mix
  import anthill.prelude.{Int64, String, Bool, PartialOrd}
  import anthill.kernel.{unify}

  fact tag("a")
  rule answer(?r) :- tag(?x), PartialOrd.gt(?x, 1), unify(?r, 5)
end
"#;

const WELL_TYPED: &str = r#"
namespace rec.ok
  import anthill.prelude.{Int64, Bool, PartialOrd}
  import anthill.kernel.{unify}

  fact tag(7)
  rule answer(?r) :- tag(?x), PartialOrd.gt(?x, 1), unify(?r, 5)
end
"#;

fn resolve_answer(src: &str, ns: &str) -> (Vec<anthill_core::kb::resolve::Solution>, Vec<String>) {
    let mut kb = crate::common::load_kb_with(src);
    let goal = crate::common::query_pattern_term(&mut kb, &format!("{ns}.answer(?r)"));
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let msgs = stats.errors.iter().map(|e| e.message.clone()).collect();
    (sols, msgs)
}

#[test]
fn an_unorderable_comparison_reports_a_diagnostic() {
    let (_, errors) = resolve_answer(CROSS_SORT, "rec.mix");
    assert_eq!(
        errors.len(),
        1,
        "exactly one fault, deduped on push — the arm is reached once per candidate \
         pair, which is O(N²) in the extent and is why the `eprintln` it replaces \
         deduped too; got: {errors:?}"
    );
    assert!(
        errors[0].contains("two DIFFERENT literal sorts"),
        "the message must name the CAUSE, not merely that something went wrong — this \
         is a String against an Int64, which `SortMismatch` tells apart from an \
         unimplemented ordering dispatch; got: {}",
        errors[0]
    );
}

#[test]
fn an_unorderable_comparison_still_residualizes() {
    // CONTROL (passes either way by design): `Error` must not abort the search and must
    // not fail the branch — "not greater" is a claim there is nothing here to make.
    // WI-879 asserts on exactly this residual.
    let (sols, _) = resolve_answer(CROSS_SORT, "rec.mix");
    assert!(
        !sols.is_empty(),
        "the goal must still come back as a residual answer, not vanish"
    );
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "and no answer may be DEFINITE — the comparison was never evaluated"
    );
}

#[test]
fn a_well_typed_comparison_reports_nothing() {
    // CONTROL (passes either way by design): the channel is quiet on a healthy search.
    let (sols, errors) = resolve_answer(WELL_TYPED, "rec.ok");
    assert!(
        errors.is_empty(),
        "a healthy search reports no fault; got {errors:?}"
    );
    assert!(
        sols.iter().any(|s| s.is_definite()),
        "`gt(7, 1)` holds, so this must answer definitely"
    );
}

// ── the CONSTRAINT GUARDS ─────────────────────────────────────────────────────
//
// The guards resolve with `definite_only: true`, so a faulted goal's residual never
// reaches them and they decide from emptiness — guarded by `truncated`, which
// `record_error` sets. That part was already right. What was wrong is what they SAY:
// the reason was a `&'static str` naming the depth budget, so a cross-sort comparison
// inside `negation(query(…))` reported "undecidable within depth budget" for a search
// that never came near a depth limit, while the resolver's own message — which names
// the operand pair — was dropped with `ResolveStats::errors`.
//
// CONTROL: revert `guard_undecided_reason` to the static wording and this row fails on
// the second assertion while still passing the first, since the guard's VERDICT was
// never the problem.

#[test]
fn a_faulted_constraint_guard_says_why() {
    // The REAL quantified-constraint syntax (`no ?x: <goal> -: <goal>`), which is what
    // drives `eval_count_guard`. `tag("a")` binds `?x` from a predicate declaring no
    // types, so `gt(?x, 1)` reaches the resolver as a String/Int64 pair and faults.
    let src = r#"
namespace rec.guard
  import anthill.prelude.{Int64, String, Bool, PartialOrd}
  fact tag("a")
  constraint no_big: no ?x: tag(?x) -: PartialOrd.gt(?x, 1)
end
"#;
    // The guard cannot decide, so the load blocks with `ConstraintUndecidable` — that
    // part was already right and is not what this row measures.
    let err = match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!("a guard that cannot be decided must block the load"),
        Err(errs) => errs.join("\n"),
    };
    assert!(
        err.contains("undecidable"),
        "the guard must not DECIDE from a search that reported a fault; got:\n{err}"
    );
    assert!(
        err.contains("two DIFFERENT literal sorts"),
        "and it must carry the resolver's own words rather than blaming a depth budget \
         the search never approached — the reason used to be a `&'static str` naming \
         the budget, with `ResolveStats::errors` dropped; got:\n{err}"
    );
}

#[test]
fn a_fault_on_a_branch_that_did_not_decide_does_not_mark_the_search_incomplete() {
    // `not(p)` where p's FIRST candidate faults and its SECOND proves definitely. The
    // answer is complete — the faulted candidate contributed nothing to it — so the
    // fault must be REPORTED without claiming the search was cut short.
    //
    // THE REGRESSION THIS PINS. Folding the sub-search's faults up is right (they die
    // with the sub-stream otherwise), but the first version of that fold went through
    // `record_error`, which also sets `truncated` — on every path, including this one.
    // The eager guards all resolve `definite_only`, so `from_emptiness(true, truncated,
    // …)` then reports UNDECIDABLE for a constraint that was definitively decided: a
    // load-time failure where there was none. `note_error` records the message and
    // leaves the completeness claim alone.
    //
    // CONTROL: `an_unorderable_comparison_reports_a_diagnostic` still requires
    // `truncated` to be set on the path where the fault DOES decide the outcome — so
    // the two rows together say the split is on the right seam, not that `truncated`
    // was simply dropped.
    let src = r#"
namespace rec.naf
  import anthill.prelude.{Int64, String, Bool, PartialOrd}
  import anthill.kernel.{unify, not}

  fact tag("a")
  fact seven(7)
  rule p :- tag(?x), PartialOrd.gt(?x, 1)
  rule p :- seven(?y), PartialOrd.gt(?y, 1)
  rule ok(?r) :- not(p), unify(?r, 1)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let goal = crate::common::query_pattern_term(&mut kb, "rec.naf.ok(?r)");
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(
        !stats.errors.is_empty(),
        "the faulted candidate's message must survive the sub-search"
    );
    assert!(
        !stats.truncated,
        "`p` was PROVED by its second candidate, so `not(p)` is definitively decided — \
         marking the outer search incomplete here turns a decided constraint into an \
         undecidable one at every eager guard"
    );
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "`not(p)` fails, so there is no definite answer ({} solutions)",
        sols.len()
    );
}
