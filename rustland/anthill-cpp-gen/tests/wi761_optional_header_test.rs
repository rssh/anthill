//! WI-761: "nothing to emit" and "failed to emit" are DISTINCT outcomes.
//!
//! `emit_namespace_header_in` used to return a plain `CppCodegenError` both when
//! a namespace declared nothing emittable (benign) and when lowering genuinely
//! failed (e.g. an op requiring an effect the profile can't realize, WI-576).
//! The CLI's optional `anthill.geometry` sidecar treated ANY error as "namespace
//! empty" and swallowed it, so a real failure vanished as a silently-absent
//! header. The optional entry point now returns `Ok(None)` for empty and `Err`
//! only for a genuine failure, so the CLI skips the first and reports the second.

use super::common;

use anthill_cpp_gen::{emit_namespace_header, emit_optional_namespace_header_with_profile};
use common::load_kb_with;

/// An empty / carrier-only namespace is the benign "nothing here" outcome:
/// `Ok(None)`, never an error the optional-header caller must interpret.
#[test]
fn empty_namespace_is_ok_none() {
    let mut kb = load_kb_with(
        r#"
        namespace test.wi761.empty
          import anthill.prelude.{Float}
        end
    "#,
    );
    let out = emit_optional_namespace_header_with_profile(&mut kb, "test.wi761.empty", None)
        .expect("an empty namespace is a benign outcome, not a codegen error");
    assert!(
        out.is_none(),
        "empty namespace must yield Ok(None), got {out:?}"
    );
}

/// The bug: a GENUINE lowering failure stays an `Err`, distinguishable from the
/// empty case above — never collapsed into the same "namespace empty" signal the
/// optional-header path skips. Here an op requires `ConsoleOutput`, which the cpp
/// `cpp20-stl` profile cannot realize (WI-576). Before WI-761 this arrived at the
/// CLI's geometry `.ok()` / `if let Ok(..)` as an error indistinguishable from
/// "empty" and the diagnostic naming the effect + profile was silently dropped.
#[test]
fn genuine_lowering_failure_is_err_not_none() {
    let mut kb = load_kb_with(
        r#"
        namespace test.wi761.fails
          import anthill.prelude.{Unit, String}
          import anthill.prelude.Console.{ConsoleOutput}
          sort Logger
            operation shout(msg: String) -> Unit
              effects ConsoleOutput
          end
        end
    "#,
    );
    let err = emit_optional_namespace_header_with_profile(
        &mut kb,
        "test.wi761.fails",
        Some("cpp20-stl".to_string()),
    )
    .expect_err("an unrealizable effect must surface as Err, not be swallowed as Ok(None)");

    let msg = err.to_string();
    assert!(
        msg.contains("ConsoleOutput"),
        "must name the offending effect: {msg}"
    );
    assert!(
        msg.contains("cpp20-stl"),
        "must name the active profile: {msg}"
    );
}

/// A namespace that DOES declare something lowers to `Ok(Some(header))`.
#[test]
fn nonempty_namespace_is_ok_some() {
    let mut kb = load_kb_with(
        r#"
        namespace test.wi761.ok
          import anthill.prelude.{Int64}
          entity Point(x: Int64, y: Int64)
        end
    "#,
    );
    let out = emit_optional_namespace_header_with_profile(&mut kb, "test.wi761.ok", None)
        .expect("a non-empty namespace lowers without error");
    let header = out.expect("a non-empty namespace yields Ok(Some(header))");
    assert!(
        header.contains("struct Point"),
        "header must carry the declared entity:\n{header}"
    );
}

/// The REQUIRED entry point keeps failing loudly on the SAME empty namespace the
/// optional path skips — a typo'd primary `--namespace` must not silently produce
/// nothing (the reason the error-on-empty behavior exists at all).
#[test]
fn required_entry_point_still_errors_on_empty() {
    let mut kb = load_kb_with(
        r#"
        namespace test.wi761.empty2
          import anthill.prelude.{Float}
        end
    "#,
    );
    assert!(
        emit_namespace_header(&mut kb, "test.wi761.empty2").is_err(),
        "a required namespace declaring nothing must fail loudly, not skip"
    );
}
