//! WI-066 — integer division partiality encoded as an `Error[DivisionByZero]`
//! effect.
//!
//! `Int64.div` / `mod` / `rem` / `divExact` (and `Field.div` / `recip`) declare
//! `effects Error[DivisionByZero]` (stdlib `int64.anthill` / `field.anthill`),
//! and `effects.anthill` adds the `DivisionByZero` payload sort alongside
//! `MatchFailed`. So an operation whose body performs integer division must
//! declare (or handle) that effect — the typer threads it via
//! `check_operation_bodies`, exactly like any other declared op effect.
//!
//! The runtime still surfaces a divide-by-zero as `EvalError::DivisionByZero`
//! (mirroring how match-failure surfaces as `EvalError::MatchFailed`, not via
//! the Error handler) — see `eval_test::m3_int_division_by_zero`. These tests
//! pin the STATIC effect threading.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra source → load errors (empty Vec on clean load).
fn try_load(extra: &str) -> Vec<load::LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .err()
        .unwrap_or_default()
}

fn errors_text(errs: &[load::LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

/// An op body doing integer division but declaring no effect row must FAIL to
/// load: it incurs `Error[DivisionByZero]` (declared on `Int64.div`) which is
/// not in its (empty) declared row.
#[test]
fn int_div_without_declared_effect_fails_to_load() {
    let errs = try_load(
        r#"
namespace test.wi066.undeclared
  import anthill.prelude.Int64.{div}
  operation half(n: Int64) -> Int64 = div(n, 2)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "expected a load error: half/2 incurs Error[DivisionByZero] but declares no effect row"
    );
    let text = errors_text(&errs);
    assert!(
        text.contains("undeclared effect") && text.contains("DivisionByZero"),
        "error should name the undeclared Error[DivisionByZero]; got:\n{text}"
    );
}

/// The same op WITH `effects Error[DivisionByZero]` declared loads clean.
#[test]
fn int_div_with_declared_effect_loads() {
    let errs = try_load(
        r#"
namespace test.wi066.declared
  import anthill.prelude.Int64.{div}
  -- Error and DivisionByZero resolve via the implicit prelude (WI-066:
  -- DivisionByZero is in IMPLICIT_PRELUDE_EFFECTS alongside MatchFailed), so no
  -- explicit import is needed — mirroring how Error[MatchFailed] is referenced.
  operation half(n: Int64) -> Int64 effects Error[DivisionByZero] = div(n, 2)
end
"#,
    );
    assert!(
        errs.is_empty(),
        "expected clean load with the effect declared; got:\n{}",
        errors_text(&errs)
    );
}

/// `mod` carries the same effect (the `/`-family is uniform): an undeclared use
/// is a load error.
#[test]
fn int_mod_carries_division_by_zero_effect() {
    let errs = try_load(
        r#"
namespace test.wi066.modrem
  import anthill.prelude.Int64.{mod}
  operation wrap(a: Int64, b: Int64) -> Int64 = mod(a, b)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "mod should incur Error[DivisionByZero]; an undeclared use must not load"
    );
    assert!(
        errors_text(&errs).contains("undeclared effect"),
        "got:\n{}",
        errors_text(&errs)
    );
}
