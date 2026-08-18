//! WI-1131 (spec §4.5) — a ONE-FIELD NAMED TUPLE is writable as a VALUE, not only as a
//! type. `(a: 1)` is a tuple literal; `(1)` is still grouping.
//!
//! THE DEFECT WAS AN UNCONSTRUCTIBLE PARAMETER. `operation f(t: (a: Int64)) -> Int64 =
//! t.a` has always loaded — the one-component tuple TYPE is spelled by `tuple_type`'s
//! fully-general single-component arm. The VALUE side had no arity-one form at all, so
//! no caller could write an argument for it. Measured on the tree before this change:
//!
//! ```text
//! let t = (a: 1)     ->  syntax error near `a: 1`
//! let t = (a: 1,)    ->  tuple literal cannot mix positional and named arguments
//!                        missing `name`
//! ```
//!
//! The second pair is the worse half: nothing positional was written. `tuple_literal`
//! required 2+ elements, tree-sitter error-recovered into that production with a MISSING
//! node, and `push_tuple_literal`'s all-or-nothing check then fired on the wreckage —
//! a diagnostic naming a fault the author did not commit.
//!
//! WHY THE 2+ RULE WAS RIGHT AND STILL OVER-BROAD. `(1)` MUST stay `paren_expr`: a
//! single parenthesized term is grouping, and the comma is the only thing that could
//! tell a 1-tuple from it. That argument does not reach the NAMED case — `a: 1` is not
//! a `_term`, so `(a: 1)` has no parenthesized-expression reading to protect. The
//! grammar now carries a named-only arity-one arm; the probe WI-1131 asked for came back
//! clean (`tree-sitter generate` reports no conflicts beyond the one DECLARED for the
//! trailing comma, and the corpus goes 205 -> 209 all green, the four new rows pinning
//! `(a: 1)`, `(a: 1,)`, `(1)`-stays-grouping and `(1,)`). The rival the ticket named —
//! a parenthesized TYPED BINDER in expression position — was already pinned by
//! `expressions.txt`'s `lambda (y: Int) -> …` and `lambda (acc: Int, elem: Int) -> …`
//! rows, and both stayed green: a lambda's parameter is a `_pattern`, so `(y: Int)`
//! reaches `pattern_typed`, never `tuple_literal`.
//!
//! `(1,)` IS STILL REFUSED, but by a message that names the rule. The grammar admits it
//! solely so `convert.rs` can say so at the literal's own span
//! (`TUPLE_ARITY_ONE_IS_NAMED_ONLY`) instead of leaving a MISSING node to be reported as
//! `missing `name``.
//!
//! ## BACK-OUT — MEASURED, not predicted. `tuple_literal` restored to its pre-WI-1131
//! ## two-arm form (the conflict declaration and the converter guard disabled with it):
//! ## 6 red, 3 green.
//!
//! RED — these fail, and they are what the change buys:
//!   * `one_field_named_tuple_is_writable_as_a_value`   — `(a: 1)` is a syntax error again
//!   * `one_field_named_tuple_fills_a_one_field_parameter` — same, at the call site
//!   * `one_field_named_tuple_conforms_in_return_position` — same, at an op-return
//!   * `one_field_named_tuple_takes_a_trailing_comma`   — `(a: 1,)` is a syntax error again
//!   * `trailing_comma_does_not_claim_a_positional_named_mix` — the false mix claim returns
//!   * `a_lone_positional_component_names_its_own_rule` — the message reverts to
//!     `missing `name`` at a zero-width span
//!
//! GREEN EITHER WAY, by design — stated so no one reads them as evidence:
//!   * `a_single_parenthesized_term_stays_grouping` — THE CONTROL the arity rule exists
//!     for. `(1)` was grouping before and is grouping after; the row's job is to show
//!     the new arm did not eat it.
//!   * `two_component_named_tuple_still_works` — the arity the language always had.
//!   * `a_genuinely_mixed_tuple_still_reports_the_mix` — `(1, b: 2)` DID mix, and the
//!     all-or-nothing check must keep saying so; the new arms must not swallow it.
//!
//! Each row builds its OWN source. A load error is fatal to its whole namespace, so a
//! control sharing a fixture with an arm would go red on the back-out too and measure
//! nothing.
//!
//! THE OTHER IMPLEMENTATION diverged three ways, and the shared WI-777 parity corpus is
//! what surfaced it. Scaland already BUILT `(a: 1)` as a one-field literal and nothing
//! measured it; it REJECTED every trailing comma in a literal, `(1, 2,)` included, which
//! rustland has always accepted (a `~/` cut inside the element repetition); and it
//! accepted `(1,)` silently as grouping. The corpus grew the three cases that fix the
//! verdicts on both sides (`accept/one_named_tuple_value{,_trailing_comma}`,
//! `reject/one_positional_tuple_value`); scaland's shapes are pinned in its own
//! `ParseTest`.

use crate::common::{interp_for, parse_errs, parses_clean, try_load_kb_with};
use anthill_core::eval::Value;

/// A namespace holding `decls`, whose `drive()` is the thing every row runs.
fn src(decls: &str) -> String {
    format!(
        r#"
namespace test.wi1131
  import anthill.prelude.{{Int64}}
{decls}
end
"#
    )
}

/// Load, run `drive()`, return its value. Panics with the diagnostics on a load error,
/// so a regression names what it caught rather than failing as a bare unwrap.
fn drive(decls: &str) -> Value {
    let source = src(decls);
    if let Err(errs) = try_load_kb_with(&source) {
        panic!("expected a clean load; got:\n  {}", errs.join("\n  "));
    }
    let mut interp = interp_for(&source);
    interp
        .call("test.wi1131.drive", &[])
        .expect("drive() runs")
}

/// `drive()`'s value as an `i64`. `Value` has no `PartialEq`, so the variant is matched
/// and the payload compared — the idiom `wi1130_positional_capture_test` uses.
fn drive_int(decls: &str) -> i64 {
    match drive(decls) {
        Value::Int(n) => n,
        other => panic!("expected an Int; got {other:?}"),
    }
}

// ── The arms ────────────────────────────────────────────────────────────────

/// `(a: 1)` is a tuple literal, and its single component is readable by name. The value
/// `1` is the component's, not the operation's: `drive` returns `t.a`, so a `(a: 1)` that
/// silently degenerated to the scalar `1` (the §6.8 1-collapse shape) would fail on the
/// field access, not agree with this row by accident.
#[test]
fn one_field_named_tuple_is_writable_as_a_value() {
    assert_eq!(
        drive_int("  operation drive() -> Int64 =\n    let t = (a: 1)\n    t.a"),
        1
    );
}

/// THE TICKET. `f(t: (a: Int64))` was always declarable and never callable. The argument
/// is written at the call site — `f((a: 1))` — and reaches `t.a`.
#[test]
fn one_field_named_tuple_fills_a_one_field_parameter() {
    assert_eq!(
        drive_int(
            "  operation f(t: (a: Int64)) -> Int64 = t.a\n\
             \x20 operation drive() -> Int64 = f((a: 1))"
        ),
        1
    );
}

/// The other end of the same channel: the literal in a RETURN position, conforming to a
/// declared one-component tuple type. Supply and read are two questions, and §4.5 now
/// claims BOTH — that a one-component type is inhabited by its own literal "in any
/// position" — so the claim is measured at an op-return as well as at an op-arg.
/// `drive` reads the component back, so a value that had silently 1-collapsed to `Int64`
/// would fail here rather than agree by accident.
#[test]
fn one_field_named_tuple_conforms_in_return_position() {
    assert_eq!(
        drive_int(
            "  operation mk() -> (a: Int64) = (a: 1)\n\
             \x20 operation drive() -> Int64 = mk().a"
        ),
        1
    );
}

/// The trailing comma is admitted at arity one, as it already was at 2+ (`(a: 1, b: 2,)`).
/// This is the row the grammar's declared GLR conflict exists for: at the `,` the parser
/// cannot yet tell a closing one-element form from a continuing 2+ one.
#[test]
fn one_field_named_tuple_takes_a_trailing_comma() {
    assert_eq!(
        drive_int("  operation drive() -> Int64 =\n    let t = (a: 1,)\n    t.a"),
        1
    );
}

/// The separate defect WI-1131 names: `(a: 1,)` reported `tuple literal cannot mix
/// positional and named arguments` about a program with nothing positional in it. The
/// source now parses with NO diagnostics at all, which is strictly stronger than
/// asserting that one string is absent.
#[test]
fn trailing_comma_does_not_claim_a_positional_named_mix() {
    parses_clean(&src(
        "  operation drive() -> Int64 =\n    let t = (a: 1,)\n    t.a",
    ));
}

/// `(1,)` stays refused — arity one is NAMED-only — but by a message stating that rule at
/// the literal's span, not by a MISSING node reported as `missing `name``. The
/// `!contains` half is the point of the row: the refusal must not have inherited the
/// false mix claim either.
///
/// EVERY POSITIONAL SPELLING, not just the literal one. `_fn_arg` has three non-named
/// alternatives and the grammar arm covers exactly that set (`_positional_fn_arg`); a
/// first cut spelled it `$._term`, which is narrower by two, and the two it missed fell
/// straight back into the `missing `name`` wreck this row exists to pin gone. A row that
/// tested only `(1,)` would have passed over that.
#[test]
fn a_lone_positional_component_names_its_own_rule() {
    for element in ["1", "?x: T", "lambda y -> y"] {
        let errs = parse_errs(&src(&format!(
            "  operation drive() -> Int64 =\n    let t = ({element},)\n    t"
        )));
        let joined = errs.join("\n");
        assert!(
            joined.contains("one-element tuple literal must name its component"),
            "`({element},)`: the refusal must name the arity-one rule; got: {errs:?}"
        );
        assert!(
            !joined.contains("mix positional and named"),
            "`({element},)`: nothing positional-and-named was written; got: {errs:?}"
        );
        assert!(
            !joined.contains("missing `name`"),
            "`({element},)`: the recovery-node message must be gone; got: {errs:?}"
        );
    }
}

// ── The controls ────────────────────────────────────────────────────────────

/// THE CONTROL the arity rule exists for, in both directions. `(1)` is grouping: it
/// evaluates as the scalar `1`, and it does NOT conform to the one-component tuple type
/// `(a: Int64)` — if the new arm had made a single parenthesized term a 1-tuple, the
/// second half would load clean. Green with and without the change, by design.
#[test]
fn a_single_parenthesized_term_stays_grouping() {
    assert_eq!(
        drive_int("  operation drive() -> Int64 =\n    let t = (1)\n    t"),
        1
    );
    let errs = try_load_kb_with(&src("  operation drive() -> (a: Int64) = (1)"))
        .err()
        .expect("`(1)` is an Int64, not a one-component tuple");
    assert!(
        errs.join("\n").contains("expected (a: Int64), got Int64"),
        "grouping must not conform to a one-component tuple; got: {errs:?}"
    );
}

/// The arity the language always had, unchanged by the new arms. Green either way.
#[test]
fn two_component_named_tuple_still_works() {
    assert_eq!(
        drive_int("  operation drive() -> Int64 =\n    let t = (a: 1, b: 2)\n    t.a"),
        1
    );
}

/// `(1, b: 2)` DID mix positional and named, and `push_tuple_literal`'s all-or-nothing
/// check must keep saying so. Green either way — the row guards that widening the
/// grammar did not route a genuine mix into one of the new one-element arms.
#[test]
fn a_genuinely_mixed_tuple_still_reports_the_mix() {
    let errs = parse_errs(&src(
        "  operation drive() -> Int64 =\n    let t = (1, b: 2)\n    t",
    ));
    assert!(
        errs.join("\n")
            .contains("tuple literal cannot mix positional and named arguments"),
        "a real mix must still be reported; got: {errs:?}"
    );
}
