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
//!
//! WI-20261104-6HVXM RETIRED THE COUNT (proposal 002 §"Correction (2026-11-03)",
//! kernel-language §4.4): an arrow is `Function[A, B, E]`, its parameter list its tuple `A`,
//! so there is no arity child to differ in and no `a N-parameter function` qualification.
//! Each side is its OWN tuple: a lambda's is its binders' (kernel-language §4.7), refused at
//! its pattern where it does not fit the slot's `A` (`pattern-position`); an operation's is
//! its parameters', re-expressed at the slot's labels where it meets the slot by position.
//! What this file pinned — the two sides differ, each shows what it wrote, the
//! context's list is not shown as the lambda's — is pinned here under that rendering, and
//! the one-binder row, which the count refused, now runs: a callable of one parameter takes
//! the slot's whole tuple.

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
    (
        expected.trim().to_string(),
        strip_origin_suffix(actual.trim()).to_string(),
    )
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
/// the handoff in action. The fault to name is the 2-binder lambda, not the annotation:
/// since WI-20261104-6HVXM its two binders against the slot's three components, at the
/// lambda's pattern.
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
/// MEASURED (WI-795): with the qualification disabled in `render_mismatch_pair` (the
/// per-side rendering), 6 of the 8 tests here failed including this one. Since
/// WI-20261104-6HVXM the sides differ because each is its own tuple, the lambda's refused
/// at its pattern.
#[test]
fn the_two_rendered_sides_of_an_arity_mismatch_differ() {
    let msg = reject(
        TICKET_REPRO,
        "a 2-binder lambda does not fit a 3-parameter slot",
    );
    let (expected, actual) = mismatch_sides(&msg);
    assert_ne!(
        expected, actual,
        "an arity mismatch must not render the same type twice; got: {msg}"
    );
}

/// Each side is its own tuple, IN THE RIGHT ORDER: the slot's three components on the
/// expected side, the lambda's two binders on the actual side, refused at the lambda's
/// pattern. Direction needs its own assertion because a transposed pair still produces two
/// DIFFERING sides, so the acceptance criterion above cannot see it.
#[test]
fn each_side_shows_its_own_tuple() {
    let msg = reject(
        TICKET_REPRO,
        "a 2-binder lambda does not fit a 3-parameter slot",
    );
    assert!(msg.contains("(pattern-position)"), "refused at the lambda's pattern; got: {msg}");
    let (expected, actual) = mismatch_sides(&msg);
    assert_eq!(
        expected, "(a: Int64, b: Int64, c: Int64)",
        "the SLOT's tuple belongs on the expected side; got: {msg}"
    );
    assert!(
        actual.starts_with("(_1: String, _2: "),
        "the LAMBDA's two binders belong on the actual side; got: {msg}"
    );
}

/// The lambda's side does NOT print the slot's parameter list: the lambda's tuple is its own
/// binders' (kernel-language §4.7), `(_1: String, _2: …)`. Printing the slot's
/// `(a: Int64, b: Int64, c: Int64)` there, inherited by WI-517's context-wins priority, is
/// what produced the original identical-sides message.
#[test]
fn a_context_supplied_parameter_list_is_not_attributed_to_the_lambda() {
    let msg = reject(
        TICKET_REPRO,
        "a 2-binder lambda does not fit a 3-parameter slot",
    );
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

/// The complement, and the guard against "suppress the spelling whenever the sizes differ":
/// when BOTH sides genuinely wrote their parameter list, both keep it — the operation's under
/// its own labels, since it meets the slot by neither label nor position.
///
/// This also pins the direction independently of the repro: here the SMALLER tuple is on
/// the expected side, so a transposed pair renderer cannot satisfy both this and
/// `each_side_shows_its_own_tuple`.
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
    assert_eq!(expected, "(a: Int64, b: Int64) -> Int64");
    assert_eq!(actual, "(x: Int64, y: Int64, z: Int64) -> Int64");
}

/// THE ZERO BOUNDARY, measured rather than reasoned about: a 0-parameter arrow's `A` is
/// the EMPTY tuple, which renders `()`, so it keeps its spelling like any other written
/// list; the one-parameter operation's side is its parameter's type, `Int64`.
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
    assert_eq!(expected, "() -> Int64");
    assert_eq!(actual, "Int64 -> Int64");
}

/// A ONE-BINDER LAMBDA TAKES THE SLOT'S WHOLE TUPLE (kernel-language §4.4, a callable of one
/// parameter drops what its tuple lacks), so `lambda (x) -> 0` at `(a: Int64, b: Int64) ->
/// Int64` loads and runs: `x` is `(a: 1, b: 2)` and the body answers 0. [Refused before
/// WI-20261104-6HVXM, by the count, rendering the inherited list as `((a: Int64, b: Int64))`.]
#[test]
fn a_one_binder_lambda_takes_the_slots_whole_tuple() {
    let mut interp = crate::common::interp_for(
        r#"
namespace test.wi795.onebinder
  import anthill.prelude.{Int64}
  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64
    = f(1, 2)
  operation drive() -> Int64
    = apply2(lambda (x) -> x.b)
end
"#,
    );
    match interp.call("test.wi795.onebinder.drive", &[]) {
        Ok(anthill_core::eval::Value::Int(v)) => assert_eq!(v, 2, "`x.b` of `(a: 1, b: 2)`"),
        other => panic!("drive: expected Int(2), got {other:?}"),
    }
}

// ── what must NOT change ───────────────────────────────────────

/// THE REGRESSION GUARD the ticket asks for by name: an arrow mismatch that differs in a
/// param TYPE at an equal size. The operation meets the slot by position, so its side is
/// rendered at the slot's labels — `b` is where the `String` would land.
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
    assert_eq!(actual, "(a: Int64, b: String) -> Int64");
}

/// A size mismatch that is ALSO a type mismatch still reports the type difference: the
/// operation's own tuple shows its `String`.
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
    assert_eq!(expected, "(a: Int64, b: Int64, c: Int64) -> Int64");
    assert_eq!(actual, "(x: Int64, y: String) -> Int64");
}

/// A non-arrow mismatch is untouched.
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
