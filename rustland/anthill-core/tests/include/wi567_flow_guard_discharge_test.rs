//! WI-567 (proposal 048 Phase 4 / 050 consumer 2), the ticket's LAST open
//! acceptance clause: `head` under an emptiness guard types PURE.
//!
//! Three of the four clauses shipped earlier — `List.head(cons(..))` discharges
//! by literal abstract interpretation, `head` on an unknown list keeps
//! `Error[EmptyStream]`, and `headOption` arrived with WI-818. What stayed
//! refused was the FLOW-FACT tier (050 channel 2, "a verbatim-matching flow-fact
//! in Γ"): `if not(isEmpty(xs)) then head(xs)` and its else-form both kept the
//! effect. TWO INDEPENDENT DEFECTS held it, one per polarity:
//!
//!  1. **Γ was unreachable for a `not` goal.** `BuiltinTag::Not` was dispatched
//!     in `step_init` ABOVE the Γ-overlay consult, so a `not(P)` goal went
//!     straight to `step_naf` — which re-derives ¬P by sub-resolving `P`, and
//!     an open-world `P` (`isEmpty` of a symbolic parameter) rightly flounders.
//!     The assumption sitting in Γ, structurally identical to the goal, was
//!     never looked at. Every other builtin already consulted Γ first.
//!
//!  2. **The two sides spelled `not` differently.** Boolean operators are
//!     POSITION-DIRECTED (kernel-language.md §6.6): an `if` condition is an
//!     operation-body VALUE expression, so `if not(..)` loads as the dispatched
//!     `anthill.prelude.Bool.not` (WI-529's `redirect_op_body_boolean` — the one
//!     routing event in a whole stdlib load). The consumer builds GOAL
//!     vocabulary: `refute_guard` → `negate_goal` mints `anthill.kernel.not`.
//!     Γ is matched STRUCTURALLY, so the fact was unequal to the very goal it
//!     was about. `typing::goal_form` now routes the fact's connective through
//!     `KnowledgeBase::goal_position_boolean` — the loader's own table, shared
//!     rather than re-spelled.
//!
//! ── CONTROL ─────────────────────────────────────────────────────────────
//!
//! MEASURED by MUTATING each fix in place (never by deleting — a deletion
//! measures loadability, not capability), running the whole `wi_tests` binary
//! each time. Both numbers below are observed, not predicted:
//!
//! * Back out (1) alone — `Not` dispatched above the Γ consult again:
//!   **3 failed / 3200 passed** — `then_branch_not_is_empty_discharges`,
//!   `else_branch_is_empty_discharges`, `a_discharged_call_still_evaluates`.
//! * Back out (2) alone — `goal_form_proposition` returns its input:
//!   **2 failed / 3201 passed** — `then_branch_not_is_empty_discharges` and
//!   `a_discharged_call_still_evaluates`. The ELSE arm still passes: its Γ fact
//!   is minted by `negate_goal` and is already in goal vocabulary, so defect (2)
//!   never applied to it.
//!
//! So the three discharge arms are the witnesses and they measure DIFFERENT
//! halves — `else_branch_…` is the one that separates (1) from (2), and
//! `a_discharged_call_still_evaluates` fails under BOTH because its program is
//! the then-branch form and does not load. (Predicting two failures for
//! back-out (1) and forgetting the eval arm is exactly the error the
//! measurement caught.)
//!
//! The four refusal arms below pass with the change and without it BY DESIGN —
//! they are here to BOUND the fix, not to detect it: each is a program whose Γ
//! does NOT entail non-emptiness, and a fix that discharged on "a `not` /
//! `isEmpty` fact is somewhere in Γ" would turn them green.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load stdlib + user source and surface load errors as strings — the shared
/// WI-478 / WI-067 guarded-effect harness. The effect check runs during
/// loading, so a DISCHARGED call lets the caller omit the effect and load
/// clean, and an undischarged one surfaces it as undeclared.
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

/// A caller over ONE list parameter, declaring NO effects — so it loads iff
/// `List.head`'s guarded `Error[EmptyStream]` discharged at the call.
fn caller(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace anthill.test.{ns}
  import anthill.prelude.{{Int64, List}}
  import anthill.prelude.Stream.{{isEmpty}}

  operation caller(xs: List[T = Int64]) -> Int64 =
    {body}
end
"#
    )
}

/// The undischarged guard's signature at the caller.
fn assert_effect_refused(errs: &[String], what: &str) {
    let text = errs.join("\n");
    assert!(
        text.contains("undeclared effect") && text.contains("EmptyStream"),
        "{what}: expected the conservatively-present `Error[EmptyStream]` to \
         surface as an undeclared effect; got:\n{text}"
    );
}

// ── The two discharge arms — the witnesses ──────────────────────────

#[test]
fn then_branch_not_is_empty_discharges() {
    // THE TICKET'S OWN CLAUSE (2), verbatim: `head` inside `if not(isEmpty(l))`
    // types PURE. Γ(then) carries the condition, whose `Bool.not` head is routed
    // to the goal `kernel.not` on the way in (defect 2); the guard's negation is
    // the same goal, and the Γ overlay is now consulted for it before NAF can
    // flounder (defect 1). Needs BOTH fixes.
    let src = caller(
        "wi567then",
        "if not(isEmpty(xs)) then List.head(xs) else 0",
    );
    assert!(
        load_result(&src).is_ok(),
        "`if not(isEmpty(xs))` must narrow Γ so `List.head(xs)` in the \
         then-branch discharges `Error[EmptyStream]`; got: {:#?}",
        load_result(&src).err()
    );
}

#[test]
fn else_branch_is_empty_discharges() {
    // The other polarity: the ELSE arm of `if isEmpty(xs)`. Here Γ's fact is
    // minted by `negate_goal` and so is ALREADY `kernel.not(isEmpty(xs))` —
    // defect 2 never applied. It was defect 1 alone that refused it, which is
    // why this arm and the one above measure different halves of the fix.
    let src = caller(
        "wi567else",
        "if isEmpty(xs) then 0 else List.head(xs)",
    );
    assert!(
        load_result(&src).is_ok(),
        "the else-branch of `if isEmpty(xs)` must narrow Γ with the negation so \
         `List.head(xs)` discharges `Error[EmptyStream]`; got: {:#?}",
        load_result(&src).err()
    );
}

// ── The refusal arms — the bound, not the detector ──────────────────

#[test]
fn unguarded_call_keeps_effect() {
    // THE LOAD-BEARING NEGATIVE CONTROL for both arms above: the identical call
    // with NO `if` at all. Γ is empty, the guard `isEmpty(xs)` over a symbolic
    // parameter cannot be refuted, and the effect stays. Without this row the
    // two `is_ok()` assertions above would also pass under a typer that dropped
    // every guarded effect unconditionally.
    let src = caller("wi567bare", "List.head(xs)");
    let errs = load_result(&src).expect_err(
        "a `head` on an unconstrained list parameter cannot refute `isEmpty(xs)`, \
         so `Error[EmptyStream]` is conservatively present",
    );
    assert_effect_refused(&errs, "unguarded call");
}

#[test]
fn inverted_polarity_keeps_effect() {
    // The SAME shapes as `then_branch_…`, one branch over: in the THEN arm of
    // `if isEmpty(xs)` the list is known EMPTY, so the guard genuinely HOLDS.
    // Γ carries `isEmpty(xs)`; refuting needs `not(isEmpty(xs))`, which is not
    // there. A fix keying on "Γ mentions isEmpty(xs)" rather than on the
    // NEGATION would turn this green.
    let src = caller(
        "wi567inv",
        "if isEmpty(xs) then List.head(xs) else 0",
    );
    let errs = load_result(&src).expect_err(
        "in the then-branch of `if isEmpty(xs)` the guard HOLDS; the effect must \
         stay present",
    );
    assert_effect_refused(&errs, "inverted polarity");
}

#[test]
fn negated_conditions_else_arm_keeps_effect() {
    // The fourth quadrant, and the one that pins the ROUTING'S REACH: the else
    // arm of `if not(isEmpty(xs))` also knows the list is empty. Γ's fact is
    // `not(not(isEmpty(xs)))` — `negate_goal` wraps the condition, and
    // `goal_form` then routes the INNER `Bool.not` too, since a negation's
    // operand is the one operand position that is itself a proposition (§6.6:
    // "a goal's ARGUMENT is a value expression and keeps the `Bool` reading").
    // Double-negation elimination is NOT performed, so nothing discharges —
    // which is the correct verdict here, and is why this row cannot detect a
    // regression in the routing's depth, only in its polarity.
    let src = caller(
        "wi567notelse",
        "if not(isEmpty(xs)) then 0 else List.head(xs)",
    );
    let errs = load_result(&src).expect_err(
        "the else-branch of `if not(isEmpty(xs))` knows the list IS empty; the \
         effect must stay present",
    );
    assert_effect_refused(&errs, "negated condition's else arm");
}

#[test]
fn a_fact_about_another_parameter_does_not_discharge() {
    // PER-PARAMETER EXACTNESS. `ys` is narrowed non-empty; the call is on `xs`.
    // `gamma_candidates_for`'s discrim query unifies a goal variable as a
    // WILDCARD, so without its `views_structurally_equal` filter the `ys` fact
    // would match — and unsoundly discharge a guard about a DIFFERENT list.
    // Moving the Γ consult ahead of NAF (defect 1) newly routes `not` goals
    // through that filter, so this is the row that says the filter still holds
    // for them.
    let src = r#"
namespace anthill.test.wi567other
  import anthill.prelude.{Int64, List}
  import anthill.prelude.Stream.{isEmpty}

  operation caller(xs: List[T = Int64], ys: List[T = Int64]) -> Int64 =
    if not(isEmpty(ys)) then List.head(xs) else 0
end
"#;
    let errs = load_result(src).expect_err(
        "a Γ fact about `ys` must not discharge a guard about `xs`",
    );
    assert_effect_refused(&errs, "fact about another parameter");
}

// ── The discharged program still RUNS ───────────────────────────────

#[test]
fn a_discharged_call_still_evaluates() {
    // A load verdict is not evidence that anything works: `then_branch_…` above
    // asserts the program TYPES, and would keep passing if the discharge had
    // broken what it computes. Drive it — `caller` on a two-element list takes
    // the then-branch and must return the head, 7.
    let src = r#"
namespace anthill.test.wi567eval
  import anthill.prelude.{Int64, List}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.Stream.{isEmpty}

  operation caller(xs: List[T = Int64]) -> Int64 =
    if not(isEmpty(xs)) then List.head(xs) else 0

  operation run() -> Int64 =
    caller(cons(head: 7, tail: cons(head: 8, tail: nil)))

  operation run_empty() -> Int64 =
    caller(nil)
end
"#;
    let mut interp = crate::common::interp_for(src);
    let got = interp.call("anthill.test.wi567eval.run", &[]);
    assert!(
        matches!(got, Ok(anthill_core::eval::Value::Int(7))),
        "the discharged `head` must still evaluate to the head element; got {got:?}"
    );
    // The else arm is reached for an empty list — the branch whose existence is
    // what makes the then-arm's discharge sound in the first place.
    let mut interp = crate::common::interp_for(src);
    let empty = interp.call("anthill.test.wi567eval.run_empty", &[]);
    assert!(
        matches!(empty, Ok(anthill_core::eval::Value::Int(0))),
        "an empty list must take the else arm and never reach `head`; got {empty:?}"
    );
}
