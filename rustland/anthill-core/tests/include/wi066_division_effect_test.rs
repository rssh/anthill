//! WI-066 / WI-479 — integer division partiality as a *guarded*
//! `Error[DivisionByZero]` effect.
//!
//! WI-066 made `Int64.div` / `mod` / `rem` / `divExact` (and `Field.div` /
//! `recip`) carry `effects Error[DivisionByZero]` **unconditionally**. WI-479
//! (proposal 048 Phase 3) refines that to the *guarded*
//! `effects { Error[DivisionByZero] :- eq(b, 0) }` (stdlib `int64.anthill` /
//! `field.anthill`): the effect is present **iff** its guard `eq(b, 0)` is not
//! refuted at the call. So the typer now DROPS the effect where it can prove
//! `neq(b, 0)` (WI-067 discharge) — a literal non-zero divisor or an enclosing
//! `if`/`match` guard — and keeps it where it cannot (a symbolic divisor, a
//! literal zero). The static row stays a sound over-approximation: drop only on
//! a positive proof of `¬guard`, never by negation-as-failure.
//!
//! Open question C (WI-479): the guard is **declared** on the op
//! (`:- eq(b, 0)`), NOT derived from the existing integrity constraint
//! `div_nonzero_primary: neq(?b, 0) :- div(?_, ?b)` (that constraint is kept,
//! unchanged, as an assert-time guard) — deriving discharge from `neq`/`not(eq)`
//! would route it through NAF, the polarity hazard 048 warns against.
//!
//! At runtime a divide-by-zero is routed through the `Error` handler as a
//! `division_by_zero(op:)` payload (WI-467; unhandled, it surfaces as
//! `EvalError::Raised` — see `eval_test::m3_int_division_by_zero`). The static
//! guard changes only the inferred row, never runtime behavior. These tests pin
//! the STATIC threading and its discharge.

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

/// A literal NON-ZERO divisor refutes the guard `eq(2, 0)` by ground evaluation,
/// so `div(n, 2)` contributes NO effect and `half` is pure — it loads clean with
/// an EMPTY effect row. (Pre-WI-479 this was an `undeclared effect` load error;
/// the migration to the guarded effect makes it pure.)
#[test]
fn int_div_literal_nonzero_divisor_is_pure() {
    let errs = try_load(
        r#"
namespace test.wi066.literal
  import anthill.prelude.Int64.{div}
  operation half(n: Int64) -> Int64 = div(n, 2)
end
"#,
    );
    assert!(
        errs.is_empty(),
        "div(n, 2) has a literal non-zero divisor: the guard eq(2, 0) is refuted, \
         so half/1 is pure and needs no effect row. got:\n{}",
        errors_text(&errs)
    );
}

/// A literal ZERO divisor does NOT refute the guard — `eq(0, 0)` HOLDS — so the
/// effect stays conservatively present. An op that omits the effect row must
/// fail to load (drop only on a positive proof of `¬guard`, never because a
/// guard "looks dischargeable").
#[test]
fn int_div_literal_zero_divisor_carries_effect() {
    let errs = try_load(
        r#"
namespace test.wi066.zero
  import anthill.prelude.Int64.{div}
  operation half(n: Int64) -> Int64 = div(n, 0)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "div(n, 0) has a literal-zero divisor: the guard eq(0, 0) holds, so \
         Error[DivisionByZero] is present and an undeclared use must fail"
    );
    let text = errors_text(&errs);
    assert!(
        text.contains("undeclared effect") && text.contains("DivisionByZero"),
        "error should name the undeclared Error[DivisionByZero]; got:\n{text}"
    );
}

/// An enclosing `if neq(d, 0)` narrows the local interpretation environment Γ in
/// the THEN branch, so `div(n, d)` there refutes its guard `eq(d, 0)` from Γ and
/// the effect drops. The whole body is then pure and loads clean (WI-067
/// flow-fact discharge, now over the migrated stdlib `div`).
#[test]
fn int_div_guarded_branch_is_pure() {
    let errs = try_load(
        r#"
namespace test.wi066.guarded
  import anthill.prelude.Int64.{div}
  operation safe(n: Int64, d: Int64) -> Int64 =
    if neq(d, 0) then div(n, d) else 0
end
"#,
    );
    assert!(
        errs.is_empty(),
        "if neq(d, 0) then div(n, d) narrows Γ so the then-branch div discharges \
         Error[DivisionByZero]; the body is pure. got:\n{}",
        errors_text(&errs)
    );
}

/// A SYMBOLIC divisor cannot refute the guard: `eq(d, 0)` is non-ground, so
/// `neq(d, 0)` flounders (open-world — `d` could be 0 at runtime) and the effect
/// stays conservatively present. An op that omits the effect row must fail.
#[test]
fn int_div_unknown_divisor_carries_effect() {
    let errs = try_load(
        r#"
namespace test.wi066.unknown
  import anthill.prelude.Int64.{div}
  operation half(n: Int64, d: Int64) -> Int64 = div(n, d)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "div(n, d) with a symbolic divisor keeps Error[DivisionByZero]; an \
         undeclared use must fail"
    );
    assert!(
        errors_text(&errs).contains("undeclared effect"),
        "got:\n{}",
        errors_text(&errs)
    );
}

/// The conservative path is unchanged: declaring `effects Error[DivisionByZero]`
/// subsumes the (undischarged) guarded effect of a symbolic-divisor `div`, so
/// the op loads clean.
#[test]
fn int_div_unknown_divisor_with_declared_effect_loads() {
    let errs = try_load(
        r#"
namespace test.wi066.declared
  import anthill.prelude.Int64.{div}
  -- Error and DivisionByZero resolve via the implicit prelude (WI-066:
  -- DivisionByZero is in IMPLICIT_PRELUDE_EFFECTS alongside MatchFailed), so no
  -- explicit import is needed — mirroring how Error[MatchFailed] is referenced.
  operation half(n: Int64, d: Int64) -> Int64 effects Error[DivisionByZero] = div(n, d)
end
"#,
    );
    assert!(
        errs.is_empty(),
        "expected clean load with the effect declared over a symbolic divisor; got:\n{}",
        errors_text(&errs)
    );
}

/// `mod` carries the same guarded effect (the `/`-family is uniform): a
/// symbolic-divisor use that omits the effect row is a load error.
#[test]
fn int_mod_unknown_divisor_carries_effect() {
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
        "mod(a, b) with a symbolic divisor incurs Error[DivisionByZero]; an \
         undeclared use must not load"
    );
    assert!(
        errors_text(&errs).contains("undeclared effect"),
        "got:\n{}",
        errors_text(&errs)
    );
}
