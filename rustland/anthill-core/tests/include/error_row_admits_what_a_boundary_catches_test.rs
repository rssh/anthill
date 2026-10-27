//! AN `Error` LABEL OF A ROW MEANS WHAT A BOUNDARY AT ITS PAYLOAD CATCHES (user, 2026-10-27:
//! "effects should mean the same as catch"). A declared `Error[X]` admits every label
//! `Error.reify[T1 = X]` discharges — the one test of proposal 071 §1.5 — and a denied
//! `-Error[X]` denies them; the bare `Error` is the pattern `?`, which admits a label at any
//! payload. A declared row compared its labels exactly: `effects {Error[Wide]}` refused a raise
//! of `Narrow`, which a boundary at `Wide` catches.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ── measured 2026-10-27, each alone ──
//!
//! * A declared row admits by the boundary's test (`error_label_admits` in the op-effects
//!   check): `a_declared_label_admits_what_its_boundary_catches`,
//!   `a_raise_admitted_by_a_wider_row_is_caught_by_its_boundary`.
//! * A denied label denies by it (`label_violates_absence`): the declared row and the row
//!   admitting what it denies, of `a_denied_label_denies_what_its_boundary_catches`.
//! * A denial asked before an admitting atom in the callback check (`callback_row_error`'s
//!   label loop): the slot `@ {Error, -Error[Wide]}` of the same row, which took the callback.
//! * A declared bare `Error` admits any payload in the callback check
//!   (`labels_match_by_subsumption`): `wi_dk83q_identical_substitution_test::
//!   a_callback_slot_reads_its_label_as_written_bare` and `wi_9wvt7_guarded_callback_row_test::
//!   a_slot_denying_error_refuses_a_division_callback`, whose `-Error` slot then refuses through
//!   its row variable instead.
//!
//! PASS EITHER WAY BY DESIGN: `a_label_its_boundary_does_not_catch_is_still_refused`, the
//! refusals the rule keeps; and the slot `@ {EffP, -Error[Wide]}` of
//! `a_denied_label_denies_what_its_boundary_catches`, which the callback check already judged
//! by the boundary's test.

use anthill_core::eval::Value;

const SORTS: &str = r#"
namespace test.rowcatch
  import anthill.prelude.{Int64, String, Option, Error, Nothing}
  import anthill.prelude.Result.{ok, err}
  sort Wide
    entity broad(n: Int64)
  end
  sort Narrow
    requires Wide
    entity slim(n: Int64)
  end
  sort Boom
    sort Reason = ?
    entity boom(reason: Reason)
  end
  operation raiseNarrow() -> Int64 effects {Error[Narrow]} = Error.raise(slim(1))
"#;

fn program(ops: &str) -> String {
    format!("{SORTS}\n{ops}\nend\n")
}

/// Each declared row admits the raise a boundary at its payload catches: a subsort, a
/// covariant argument at the bottom, a slot left open, the bare `Error`, and a call whose
/// own row names the narrower label.
#[test]
fn a_declared_label_admits_what_its_boundary_catches() {
    for (shape, op) in [
        (
            "a subsort",
            "  operation r() -> Int64 effects {Error[Wide]} = Error.raise(slim(1))",
        ),
        (
            "a call raising a subsort",
            "  operation r() -> Int64 effects {Error[Wide]} = raiseNarrow()",
        ),
        (
            "a covariant argument",
            "  operation r() -> Int64 effects {Error[Option[T = Int64]]} =
    Error.raise(Option.none[T = Nothing]())",
        ),
        (
            "a slot left open",
            "  operation r(n: Int64) -> Int64 effects {Error[Boom]} =
    if n < 0 then Error.raise(boom(5)) else Error.raise(boom(\"s\"))",
        ),
        (
            "the bare Error",
            "  operation r() -> Int64 effects {Error} = Error.raise(boom(5))",
        ),
        (
            "a slot denying another sort",
            "  operation r() -> Int64 effects {Error, -Error[Narrow]} = Error.raise(broad(2))",
        ),
        (
            "a parameter's default",
            "  operation r(n: Int64 = Error.raise(slim(1))) -> Int64 effects {Error[Wide]} = n",
        ),
    ] {
        let errs = crate::common::load_errors_of(&program(op));
        assert!(errs.is_empty(), "{shape}: loads clean, got {errs:#?}");
    }
}

/// What a wider row admitted is caught at run time by a boundary at that row's payload, and
/// by one at the narrower sort the raise carries: the row is a bound on what escapes, and the
/// raise keeps its own type.
#[test]
fn a_raise_admitted_by_a_wider_row_is_caught_by_its_boundary() {
    let src = program(
        "  operation wideRow() -> Int64 effects {Error[Wide]} = Error.raise(slim(4))
  operation atWide() -> Int64 =
    match Error.reify[T1 = Wide](lambda () -> wideRow())
      case ok(_) -> 1
      case err(slim(n)) -> n + 10
      case err(_) -> 3
  operation inner() -> Int64 effects {Error[Wide]} =
    match Error.reify[T1 = Narrow](lambda () -> wideRow())
      case ok(_) -> 1
      case err(_) -> 2
  operation atNarrow() -> Int64 =
    match Error.reify(lambda () -> inner())
      case ok(n) -> n
      case err(_) -> 3
  operation bareRow() -> Int64 effects {Error} = Error.raise(boom(5))
  operation atAny() -> Int64 =
    match Error.reify(lambda () -> bareRow())
      case ok(_) -> 1
      case err(_) -> 2",
    );
    let mut interp = crate::common::interp_for(&src);
    for (op, want) in [("atWide", 14), ("atNarrow", 2), ("atAny", 2)] {
        let v = interp.call(&format!("test.rowcatch.{op}"), &[]).expect("runs");
        assert!(matches!(v, Value::Int(n) if n == want), "{op}: expected {want}, got {v:?}");
    }
}

/// A denied label denies what a boundary at it catches, in a declared row and in a callback
/// slot; the denial wins over a present label that admits the raise; and a row that admits
/// what it denies is refused where it is declared.
#[test]
fn a_denied_label_denies_what_its_boundary_catches() {
    let errs = crate::common::load_errors_of(&program(
        "  operation r() -> Int64 effects {Error, -Error[Wide]} = raiseNarrow()",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["r.effects", "denied effect: Error[T = Narrow]"],
        "a declared row",
    );
    let errs = crate::common::load_errors_of(&program(
        "  operation run[EffP](f: () -> Int64 @ {EffP, -Error[Wide]}) -> Int64 effects {EffP} = f()
  operation r() -> Int64 effects {Error[Narrow]} = run(lambda () -> raiseNarrow())",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["run.f", "to lack `Error[T = Wide]`"],
        "a callback slot",
    );
    let errs = crate::common::load_errors_of(&program(
        "  operation run(f: () -> Int64 @ {Error, -Error[Wide]}) -> Int64 effects {Error} = f()
  operation r() -> Int64 effects {Error} = run(lambda () -> raiseNarrow())",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["run.f", "to lack `Error[T = Wide]`"],
        "a callback slot whose bare `Error` admits the raise",
    );
    let errs = crate::common::load_errors_of(&program(
        "  operation r() -> Int64 effects {Error[Narrow], -Error[Wide]} = raiseNarrow()",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["test.rowcatch.r", "both ADMITS and LACKS `Error[T = Wide]`"],
        "a row admitting what it denies",
    );
}

/// The refusals the rule keeps: a narrower row does not admit a raise of the wider sort, and a
/// boundary at the narrower sort does not discharge the wider label, which stays in the
/// caller's row.
#[test]
fn a_label_its_boundary_does_not_catch_is_still_refused() {
    let errs = crate::common::load_errors_of(&program(
        "  operation r() -> Int64 effects {Error[Narrow]} = Error.raise(broad(2))",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["r.effects", "undeclared effect: Error[T = Wide]"],
        "a wider raise under a narrower row",
    );
    let errs = crate::common::load_errors_of(&program(
        "  operation wideRow() -> Int64 effects {Error[Wide]} = Error.raise(slim(4))
  operation r() -> Int64 =
    match Error.reify[T1 = Narrow](lambda () -> wideRow())
      case ok(_) -> 1
      case err(_) -> 2",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["r.effects", "undeclared effect: Error[T = Wide]"],
        "a narrower boundary over a wider row",
    );
}
