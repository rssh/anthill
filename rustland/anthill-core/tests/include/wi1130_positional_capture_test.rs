//! WI-1130 (proposal 056 §5.4) — a POSITIONAL argument may fill a `...rest: R` variadic
//! capture slot directly, `R` binding that argument's own type.
//!
//! THE CAPTURE PARAMETER IS A POSITION TOO. `cap[R](...rest: R)` declares one parameter,
//! and an ordinary positional argument binds it — which is what 056's status line,
//! `normalize_variadic_capture`'s doc comment and kernel-language.md §5.4 have always
//! said. The binding was already happening; `normalize_variadic_capture` then fired
//! ANYWAY and appended its own synthesized `rest: ()`, giving one parameter two bindings
//! and killing the call. Measured before the fix, on `cap[R](...rest: R) -> R = rest`:
//!
//! ```text
//! cap(5)  ->  type mismatch in cap.rest (op-arg): expected Int64, got ()
//!             type mismatch in cap.rest (op-arg): expected a named argument matching a
//!               distinct unbound parameter, got named argument 'rest' binds a parameter
//!               already given
//! ```
//!
//! Read `expected Int64`: `R` had ALREADY been inferred FROM the positional argument. So
//! this was a double-bind bug in a half-landed feature, not an unbuilt one — which is why
//! the `_N` reading of 056 §3 OQ #2 was REJECTED rather than implemented. Collecting a
//! positional leftover as `_1` would have made `cap(5)` mean `(_1: 5)` while
//! `cap(rest: 5)` kept meaning `5` — two spellings of one argument, two values, silent.
//!
//! ONE SOURCE PER ROW, deliberately. The back-out below turns the arms into LOAD errors,
//! and a load error is fatal to its whole namespace: had the controls shared a fixture
//! with the arms they would have gone red too and measured nothing.
//!
//! ## BACK-OUT — MEASURED, not predicted (the clause disabled in place, `if false && …`,
//! ## rather than deleted, so the fixtures still load): 8 red, 4 green.
//!
//! RED — these fail, and they are what the change buys:
//!   * `positional_fills_the_capture_slot`         — `cap(5)` becomes the double-bind pair
//!   * `positional_and_named_spellings_agree`      — same, on its `cap(5)` half
//!   * `positional_fills_slot_after_a_declared_param` — `cap(1, 2)` becomes the same pair
//!   * `surplus_positional_reports_arity_alone`    — the count goes 1 -> 3
//!   * `named_leftover_after_a_positional_is_refused` — the message reverts to the
//!     synthesized record's (`expected Int64, got (a: Int64)`), so both the `a`-naming
//!     assertion and the `!contains` control fail
//!   * `positional_capture_reaches_the_consumer` — still a load error on a back-out, but
//!     the double-bind's, not `Without`'s, so the message assertion fails
//!   * `single_leftover_is_not_offered_an_unwritable_repair` /
//!     `two_leftovers_are_offered_the_record_repair` — the refusal they read does not
//!     exist without the clause, so neither repair string is present
//!
//! GREEN EITHER WAY, by design — stated so no one reads them as evidence:
//!   * `named_capture_still_works` / `named_capture_after_a_declared_param_still_works` /
//!     `explicitly_named_capture_parameter_still_binds_directly` — the three CONTROLS.
//!     They ride channels this change does not touch; their job is to show it broke
//!     nothing, not to show it did anything.
//!   * `empty_capture_is_the_identity` — THE TRAP. With no positional leftover the fold
//!     was always correct, so `cap(1)` yields `R = ()` both before and after. It measures
//!     nothing about this change and is kept only to pin OQ #6 against future edits.
//!     (Same shape as WI-1129's degenerate capture row.)

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::Value;

/// The capture as the ONLY parameter — every positional argument is a leftover.
fn only_capture(body: &str, ret: &str) -> String {
    format!(
        r#"
namespace test.wi1130
  import anthill.prelude.{{Int64, String}}
  operation cap[R](...rest: R) -> R = rest
  operation drive() -> {ret} = {body}
end
"#
    )
}

/// One declared parameter BEFORE the capture — positional arg 0 fills `x`, arg 1 is the
/// leftover that reaches `rest`.
fn declared_then_capture(body: &str, ret: &str) -> String {
    format!(
        r#"
namespace test.wi1130
  import anthill.prelude.{{Int64, String}}
  operation cap[R](x: Int64, ...rest: R) -> R = rest
  operation drive() -> {ret} = {body}
end
"#
    )
}

/// Load, run `drive()`, return its value. Panics with the diagnostics on a load error, so
/// a regression names what it caught rather than failing as a bare unwrap.
fn drive(src: &str) -> Value {
    if let Err(errs) = try_load_kb_with(src) {
        panic!("expected a clean load; got:\n  {}", errs.join("\n  "));
    }
    let mut interp = interp_for(src);
    interp.call("test.wi1130.drive", &[]).expect("drive() runs")
}

/// `drive()`'s value as an `i64`. `Value` has no `PartialEq`, so the variant is matched
/// and the payload compared — the same idiom `wi727_fix_test` uses.
fn drive_int(src: &str) -> i64 {
    match drive(src) {
        Value::Int(n) => n,
        other => panic!("expected an Int; got {other:?}"),
    }
}

/// The diagnostics of a source that must NOT load.
fn load_errs(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => panic!("expected a load error; the source loaded clean"),
        Err(errs) => errs,
    }
}

// ── The arms ────────────────────────────────────────────────────────────────

/// `cap(5)` on `cap[R](...rest: R) -> R = rest` — the positional argument binds the
/// capture parameter and `R` is `Int64`, so the body returns the argument itself.
#[test]
fn positional_fills_the_capture_slot() {
    assert_eq!(drive_int(&only_capture("cap(5)", "Int64")), 5);
}

/// THE ASSERTION THAT IS THE DECISION: the positional and the explicitly-named spellings
/// of one argument denote the SAME value. Under the rejected `_N` reading these would
/// have been `(_1: 5)` and `5` — this equality is what that design would have broken.
#[test]
fn positional_and_named_spellings_agree() {
    let positional = drive_int(&only_capture("cap(5)", "Int64"));
    let named = drive_int(&only_capture("cap(rest: 5)", "Int64"));
    assert_eq!(positional, 5);
    assert_eq!(named, 5);
    assert_eq!(positional, named, "`cap(5)` and `cap(rest: 5)` must agree");
}

/// The same, with a declared parameter ahead of the capture: `1` fills `x`, `2` is the
/// leftover that fills `rest`.
#[test]
fn positional_fills_slot_after_a_declared_param() {
    assert_eq!(drive_int(&declared_then_capture("cap(1, 2)", "Int64")), 2);
}

/// TWO positional leftovers, ONE slot. The WI-1100 arity check owns this, and after the
/// fix it is the ONLY error the call reports — the COUNT is the assertion, since the
/// double-bind used to contribute two more. The tail must now name BOTH channels the slot
/// admits: `cap(1, 2)` above is legal, and a tail saying only "named arguments" would read
/// as forbidding it.
#[test]
fn surplus_positional_reports_arity_alone() {
    let errs = load_errs(&declared_then_capture("cap(1, 2, 3)", "Int64"));
    assert_eq!(errs.len(), 1, "expected the arity error alone; got:\n  {}", errs.join("\n  "));
    let msg = &errs[0];
    assert!(msg.contains("cap.arity"), "not the arity error: {msg}");
    assert!(msg.contains("got 3 arguments"), "does not count the source's arguments: {msg}");
    assert!(
        msg.contains("one further positional argument") && msg.contains("named arguments"),
        "the tail must name BOTH channels the `...rest` slot admits: {msg}"
    );
    // NO EXPECTED COUNT, and that is the point. It used to say "expected 1 argument"
    // while the tail described a slot that takes a further one — an author reading the
    // first clause would delete the legal `cap(1, 2)`. A range would be wrong too: the
    // named channel is unbounded, so `cap(1, a: 2, b: 3)` writes three legally. The shape
    // is stated instead, and the only counts are the author's own. (Found by
    // `/code-review`, whose proposed "1 or 2 arguments" this measurement rejected.)
    assert!(
        msg.contains("declares 1 parameter"),
        "the fixed list's size is what can be counted: {msg}"
    );
    assert!(
        !msg.contains("expected 1 argument") && !msg.contains("1 or 2 arguments"),
        "no expected COUNT belongs here — no range describes an unbounded channel: {msg}"
    );
}

/// THE REPAIR ADVICE MUST BE WRITABLE. With ONE leftover the refusal must NOT offer
/// `rest: (…)`: a one-field named tuple has no spelling — `cap(1, rest: (a: 3))` is
/// `syntax error near \`a: 3\``, measured — so that advice would send the author at a
/// repair the grammar rejects. WI-1131 owns the gap. Found by a `/code-review` pass; this
/// row and its sibling below drive the two branches of the suggestion.
#[test]
fn single_leftover_is_not_offered_an_unwritable_repair() {
    let joined = load_errs(&declared_then_capture("cap(1, 2, a: 3)", "Int64")).join("\n");
    assert!(
        joined.contains("drop that positional argument"),
        "the always-valid repair must be offered: {joined}"
    );
    assert!(
        !joined.contains("pass the whole record"),
        "a one-field record has no spelling; it must not be suggested: {joined}"
    );
}

/// The sibling branch: with TWO leftovers `rest: (a: 3, b: 4)` IS writable, so the
/// alternative is offered. Drives the `leftovers.len() >= 2` arm — without it the
/// condition could be stuck-off and the test above would still pass.
#[test]
fn two_leftovers_are_offered_the_record_repair() {
    let joined =
        load_errs(&declared_then_capture("cap(1, 2, a: 3, b: 4)", "Int64")).join("\n");
    assert!(
        joined.contains("'a'") && joined.contains("'b'"),
        "both leftovers must be named: {joined}"
    );
    assert!(
        joined.contains("pass the whole record"),
        "a two-field record IS writable, so the alternative belongs here: {joined}"
    );
}

/// A positional argument filled the slot AND a named leftover wants it — the two channels
/// are exclusive, so this is refused. The message must name `a`, THE ARGUMENT THE AUTHOR
/// WROTE (the WI-757 class), and must never show the synthesized capture record: before
/// the fix it read `expected Int64, got (a: Int64)`, describing the rewrite instead of the
/// source. The `!contains` is the control on that half — it is what fails on a back-out
/// even if some other message happened to mention `a`.
#[test]
fn named_leftover_after_a_positional_is_refused() {
    let errs = load_errs(&declared_then_capture("cap(1, 2, a: 3)", "Int64"));
    let joined = errs.join("\n");
    assert!(
        joined.contains("'a'"),
        "the refusal must name the author's own argument `a`: {joined}"
    );
    assert!(
        joined.contains("already fills `rest`"),
        "the refusal must say why `a` cannot be placed: {joined}"
    );
    assert!(
        !joined.contains("(a: Int64)"),
        "the synthesized capture record must never reach a user-facing message: {joined}"
    );
}

// ── The controls ────────────────────────────────────────────────────────────

/// CONTROL — the NAMED capture channel, untouched. Green with and without the change.
#[test]
fn named_capture_still_works() {
    assert_eq!(drive_int(&only_capture("cap(a: 5).a", "Int64")), 5);
}

/// CONTROL — a named leftover alongside a filled declared parameter. Green either way.
#[test]
fn named_capture_after_a_declared_param_still_works() {
    assert_eq!(drive_int(&declared_then_capture("cap(1, a: 2).a", "Int64")), 2);
}

/// CONTROL — the explicit-record guard, deliberately LEFT STANDING by WI-1130: a named
/// argument that names the capture parameter binds it directly rather than being folded
/// into a record. That is why `cap(a: 5)` yields `(a: Int64)` while `cap(rest: 5)` yields
/// a bare `Int64` — a label-keyed divergence this ticket did not touch. Green either way.
#[test]
fn explicitly_named_capture_parameter_still_binds_directly() {
    assert_eq!(drive_int(&declared_then_capture("cap(1, rest: 2)", "Int64")), 2);
}

/// THE TRAP — passes with AND without the change, and so measures nothing about it. With
/// no positional leftover the fold was already correct, so `cap(1)` yields the empty
/// record both ways. Kept only to pin 056 OQ #6 (the empty capture is the identity, not an
/// error) against future edits.
#[test]
fn empty_capture_is_the_identity() {
    let v = drive(&declared_then_capture("cap(1)", "()"));
    // The empty RECORD, not `Value::Unit` — the fold builds a named tuple with no
    // components, which is what makes `Without[T, ()]` the identity rather than a special
    // case. Measured here rather than assumed.
    match v {
        Value::Tuple { pos, named } => {
            assert!(pos.is_empty() && named.is_empty(), "the empty capture has no components");
        }
        other => panic!("the empty capture is an empty named tuple; got {other:?}"),
    }
}

// ── The consumer ────────────────────────────────────────────────────────────

/// A path that was UNREACHABLE before this change: a positional argument binding `fix`'s
/// `...args: R`, which hands `Without[T, Drop]` a `Drop` that is not a record. The
/// double-bind used to kill the call first, so nothing ever exercised the layering 056
/// §2.2 states — the capture stays **unconstrained** (`R` collects whatever arrives) and
/// the CONSUMER's type constructor supplies the meaning. It holds: `Without` refuses it
/// with its own message, named and self-explaining, rather than accepting a nonsense
/// schema. Not a silent skip, which is what this row exists to prove.
#[test]
fn positional_capture_reaches_the_consumer() {
    let src = r#"
namespace test.wi1130fix
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.Relation.{fix}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation bad() -> List[String] effects Error =
    let rel = person_row
    let f = rel.fix(30)
    f.takeN(9)
end
"#;
    let joined = load_errs(src).join("\n");
    assert!(
        joined.contains("`Without` drop operand must be a record"),
        "the consumer must be the one refusing it, by its own rule: {joined}"
    );
}
