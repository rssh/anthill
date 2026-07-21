//! WI-795: an arity-only arrow mismatch rendered `expected X, got X` — the SAME text on
//! both sides — so the diagnostic that owns every callback arity defect could not express
//! the defect it owns.
//!
//! ROOT CAUSE: WI-791 made an arrow's parameter-list arity a GROUND SIBLING of the param
//! slot rather than part of the param type, and the type renderer walks the param spine
//! only. Two arrows differing solely in the arity child therefore render identically. The
//! CHECK was correct throughout — it refused every program here before this ticket, and
//! refuses them still; only the message changed.
//!
//! The two sides came out identical rather than merely uninformative because of WHERE a
//! lambda's parameter types come from. A lambda takes them from the CONTEXT, so a
//! 2-binder lambda at a 3-parameter slot carries the SLOT's 3-component list under an
//! arity of 2 — an arrow that contradicts itself, and whose param list is not the
//! lambda's own. Printing that list is what made the message unreadable: the user was
//! shown their code's type as being the very type it was being refused against.
//!
//! THE FIX renders the mismatched pair TOGETHER (`render_mismatch_pair`) rather than each
//! side alone, since "the arities differ" is a property of the pair. When they do differ,
//! each side is qualified with its own parameter count, and a side whose param slot is
//! not its own drops the spelling entirely.
//!
//! WHY IT MATTERS: WI-794's per-binder annotation check deliberately STANDS DOWN at
//! unequal arity — at a misaligned zip it would blame a specific annotation for a missing
//! parameter — and hands the case off to this diagnostic. A handoff target that renders
//! `expected X, got X` makes that a downgrade rather than a delegation.

use crate::common::try_load_kb_with;

/// Load `src`, expecting rejection, and return the diagnostics joined.
fn reject(src: &str, why: &str) -> String {
    try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("{why}: expected rejection, but it loaded clean"))
        .join("\n")
}

/// Split `expected …, got …` back into its two rendered sides.
///
/// Every assertion here goes through this rather than through `contains`, because
/// `contains` is exactly the assertion that was blind to this bug: the pre-fix message
/// contains its expected side and its actual side both, and satisfies any number of
/// substring checks, while being the useless `expected X, got X`. Comparing the two sides
/// to EACH OTHER is the only assertion that fails on the defect.
fn mismatch_sides(msg: &str) -> (String, String) {
    let (_, pair) = msg.split_once("expected ").unwrap_or_else(|| {
        panic!("not a type-mismatch diagnostic: {msg}");
    });
    let (expected, actual) = pair.split_once(", got ").unwrap_or_else(|| {
        panic!("type-mismatch diagnostic has no `, got` half: {msg}");
    });
    (expected.trim().to_string(), strip_origin_suffix(actual.trim()).to_string())
}

/// Strip the WI-510 provenance suffix — ` [Kind @ file:line]`, which
/// `type_mismatch_origin_suffix` appends AFTER the actual type when
/// `ANTHILL_DIAG_ORIGIN` is set.
///
/// Measured, not hypothetical: without this, 5 of the 8 exact-match assertions in this
/// file fail under `ANTHILL_DIAG_ORIGIN=1` — which is precisely the variable a developer
/// debugging a type-mismatch diagnostic reaches for, i.e. the one run in which these
/// tests most need to be trustworthy.
///
/// Matched by SHAPE rather than stripped blindly: a parameterized type legitimately ends
/// in `]` (`Option[T = Int64]`, `Vec[arity = 3]`), so only a trailing bracket group that
/// also contains ` @ ` — the suffix's own separator — is removed.
fn strip_origin_suffix(side: &str) -> &str {
    match side.rsplit_once(" [") {
        Some((head, tail)) if tail.ends_with(']') && tail.contains(" @ ") => head,
        _ => side,
    }
}

// ── the ticket's repro ─────────────────────────────────────────

/// THE MEASURED SYMPTOM, verbatim from the ticket. On WI-794's delivery commit this read
/// `expected (a: Int64, b: Int64, c: Int64) -> Int64, got (a: Int64, b: Int64, c: Int64)
/// -> Int64` — byte-identical sides.
///
/// The `x: String` annotation is deliberate and is NOT what should be reported: WI-794's
/// per-binder check stands down here precisely because the arity disagrees, so this is
/// the handoff in action. The fault to name is the 2-binder lambda, not the annotation.
const TICKET_REPRO: &str = r#"
namespace test.wi795.repro
  import anthill.prelude.{Int64, String}
  operation apply3(f: (a: Int64, b: Int64, c: Int64) -> Int64) -> Int64
    = f(1, 2, 3)
  operation drive() -> Int64
    = apply3(lambda (x: String, y) -> 0)
end
"#;

/// THE ACCEPTANCE CRITERION, and the one assertion the bug does not survive: the two
/// rendered sides must DIFFER. Nothing weaker catches this — see `mismatch_sides`.
///
/// MEASURED: with the qualification disabled in `render_mismatch_pair` (i.e. the pre-fix
/// per-side rendering), 6 of the 8 tests here fail including this one, and the 2 that
/// pass are exactly the two "must NOT change" controls at the bottom of this file — which
/// is what makes them controls rather than filler.
#[test]
fn the_two_rendered_sides_of_an_arity_mismatch_differ() {
    let msg = reject(TICKET_REPRO, "a 2-binder lambda does not fit a 3-parameter slot");
    let (expected, actual) = mismatch_sides(&msg);
    assert_ne!(
        expected, actual,
        "an arity mismatch must not render the same type twice; got: {msg}"
    );
}

/// Both counts are stated, IN THE RIGHT ORDER. Direction needs its own assertion because
/// a transposed pair renderer still produces two DIFFERING sides, so the acceptance
/// criterion above cannot see it.
///
/// MEASURED, not assumed — the counts were transposed in `render_mismatch_pair` in place
/// and the tests re-run: 5 of the 8 here failed, plus all 10 arity assertions in
/// wi782/wi791/wi792. The 3 that did NOT fail are exactly the ones that should not —
/// `the_two_rendered_sides_..._differ` (two transposed sides still differ, which is why
/// direction needs this test) and the two unchanged-rendering controls.
#[test]
fn the_diagnostic_states_the_arity_of_each_side() {
    let msg = reject(TICKET_REPRO, "a 2-binder lambda does not fit a 3-parameter slot");
    let (expected, actual) = mismatch_sides(&msg);
    assert!(
        expected.starts_with("a 3-parameter function"),
        "the SLOT's arity (3) belongs on the expected side; got: {msg}"
    );
    assert!(
        actual.starts_with("a 2-parameter function"),
        "the LAMBDA's arity (2) belongs on the actual side; got: {msg}"
    );
}

/// The lambda's side does NOT print a parameter list, because it has none of its own: the
/// `(a: Int64, b: Int64, c: Int64)` it carries is the SLOT's, inherited by WI-517's
/// context-wins priority. Printing it is what produced the original identical-sides
/// message, and it contradicts the count standing beside it.
#[test]
fn a_context_supplied_parameter_list_is_not_attributed_to_the_lambda() {
    let msg = reject(TICKET_REPRO, "a 2-binder lambda does not fit a 3-parameter slot");
    let (expected, actual) = mismatch_sides(&msg);
    assert!(
        expected.contains("(a: Int64, b: Int64, c: Int64)"),
        "the slot DID write its parameter list and must still show it; got: {msg}"
    );
    assert!(
        !actual.contains("Int64"),
        "the lambda wrote no parameter list; showing the slot's is what made the two \
         sides identical. got: {msg}"
    );
}

// ── the other direction: both sides wrote their own list ───────

/// The complement, and the guard against "suppress the spelling whenever arity differs":
/// when BOTH sides genuinely wrote the parameter list their arity describes, both keep
/// it. Only a slot-inherited list is dropped.
///
/// This also pins the direction independently of the repro: here the SMALLER count is on
/// the expected side, so a transposed pair renderer cannot satisfy both this and
/// `the_diagnostic_states_the_arity_of_each_side`.
#[test]
fn an_arity_mismatch_between_two_written_parameter_lists_keeps_both_spellings() {
    let msg = reject(
        r#"
namespace test.wi795.bothwritten
  import anthill.prelude.{Int64}
  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64
    = f(1, 2)
  operation three(x: Int64, y: Int64, z: Int64) -> Int64
    = x
  operation drive() -> Int64
    = apply2(three)
end
"#,
        "a 3-parameter operation does not fit a 2-parameter slot",
    );
    let (expected, actual) = mismatch_sides(&msg);
    assert_eq!(expected, "a 2-parameter function (a: Int64, b: Int64) -> Int64");
    assert_eq!(actual, "a 3-parameter function (_1: Int64, _2: Int64, _3: Int64) -> Int64");
}

/// THE ZERO BOUNDARY, measured rather than reasoned about: a 0-parameter arrow's slot is
/// an EMPTY named tuple, which renders `()` and is self-consistent, so it keeps its
/// spelling like any other written list. Pinned because "is this list the side's own?"
/// short-circuits at arity 1, and 0 is the only other count that could plausibly have
/// been special-cased into the suppressed branch by accident.
#[test]
fn a_zero_parameter_arrow_is_self_consistent_and_keeps_its_spelling() {
    let msg = reject(
        r#"
namespace test.wi795.zero
  import anthill.prelude.{Int64}
  operation apply0(f: () -> Int64) -> Int64
    = f()
  operation one(x: Int64) -> Int64
    = x
  operation drive() -> Int64
    = apply0(one)
end
"#,
        "a 1-parameter operation does not fit a 0-parameter slot",
    );
    let (expected, actual) = mismatch_sides(&msg);
    assert_eq!(expected, "a 0-parameter function () -> Int64");
    assert_eq!(actual, "a 1-parameter function Int64 -> Int64");
}

/// THE KNOWN INCOMPLETENESS, pinned so it is a decision rather than a surprise. At arity
/// 1 the param slot is the sole parameter's TYPE, and every type is a well-formed one, so
/// "is this list the side's own?" cannot be answered and answers `true`. A 1-binder lambda
/// at a 2-parameter slot therefore DOES show the context's list as its own — the very
/// attribution suppressed at arity 2+.
///
/// It is tolerated here and not there because the message still works: the count is
/// stated, the fault named is the arity, and the two sides differ — WI-791's arity-1 paren
/// wrap renders the inherited list as `((a: Int64, b: Int64))`, one tuple parameter,
/// against the slot's unwrapped two. Closing it would need to know whether the type was
/// WRITTEN, which the finished arrow does not record.
#[test]
fn a_one_binder_lambda_still_shows_an_inherited_sole_parameter_type() {
    let msg = reject(
        r#"
namespace test.wi795.onebinder
  import anthill.prelude.{Int64}
  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64
    = f(1, 2)
  operation drive() -> Int64
    = apply2(lambda (x) -> 0)
end
"#,
        "a 1-binder lambda does not fit a 2-parameter slot",
    );
    let (expected, actual) = mismatch_sides(&msg);
    assert_eq!(expected, "a 2-parameter function (a: Int64, b: Int64) -> Int64");
    assert_eq!(actual, "a 1-parameter function ((a: Int64, b: Int64)) -> Int64");
    assert_ne!(expected, actual, "the sides must still differ even here");
}

// ── what must NOT change ───────────────────────────────────────

/// THE REGRESSION GUARD the ticket asks for by name: an arrow mismatch that differs in a
/// param TYPE at EQUAL arity renders exactly as it did before — no arity clause anywhere.
/// The qualification is gated on the arities being present and UNEQUAL, and no param-type
/// difference satisfies that.
#[test]
fn an_equal_arity_param_type_mismatch_is_rendered_unchanged() {
    let msg = reject(
        r#"
namespace test.wi795.paramtype
  import anthill.prelude.{Int64, String}
  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64
    = f(1, 2)
  operation two(x: Int64, y: String) -> Int64
    = x
  operation drive() -> Int64
    = apply2(two)
end
"#,
        "a (Int64, String) operation does not fit an (Int64, Int64) slot",
    );
    let (expected, actual) = mismatch_sides(&msg);
    assert_eq!(expected, "(a: Int64, b: Int64) -> Int64");
    assert_eq!(actual, "(_1: Int64, _2: String) -> Int64");
    assert!(
        !msg.contains("-parameter function"),
        "the arities agree — nothing here is an arity defect; got: {msg}"
    );
}

/// An arity mismatch that is ALSO a type mismatch still reports the type difference, so
/// the arity clause adds information rather than replacing it.
#[test]
fn an_arity_and_type_mismatch_still_reports_the_type_difference() {
    let msg = reject(
        r#"
namespace test.wi795.both
  import anthill.prelude.{Int64, String}
  operation apply3(f: (a: Int64, b: Int64, c: Int64) -> Int64) -> Int64
    = f(1, 2, 3)
  operation two(x: Int64, y: String) -> Int64
    = x
  operation drive() -> Int64
    = apply3(two)
end
"#,
        "a 2-parameter (Int64, String) operation does not fit a 3-parameter slot",
    );
    let (expected, actual) = mismatch_sides(&msg);
    assert_eq!(expected, "a 3-parameter function (a: Int64, b: Int64, c: Int64) -> Int64");
    assert_eq!(actual, "a 2-parameter function (_1: Int64, _2: String) -> Int64");
}

/// A non-arrow mismatch is untouched — the pair renderer must not reach for an `arity`
/// child on types that have none.
#[test]
fn a_scalar_mismatch_is_rendered_unchanged() {
    let msg = reject(
        r#"
namespace test.wi795.scalar
  import anthill.prelude.{Int64, String}
  operation takes(x: Int64) -> Int64
    = x
  operation drive() -> Int64
    = takes("hello")
end
"#,
        "a String does not fit an Int64 slot",
    );
    let (expected, actual) = mismatch_sides(&msg);
    assert_eq!(expected, "Int64");
    assert_eq!(actual, "String");
}
