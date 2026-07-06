//! WI-592 (WI-502 / WI-573 prerequisite): a guarded-effect guard over a
//! nullary-CONSTRUCTOR argument now DISCHARGES (or is correctly kept).
//!
//! Before WI-592, a bare-identifier argument that resolves to a constructor
//! (`risky(Green)`) was lowered for a Γ goal as `var_ref(name: Green)` — the same
//! shape a genuine variable binder gets — so the Γ floundering gate treated the
//! constructor as an open-world variable and `neq(Green, Red)` *floundered*
//! instead of being decided. The guarded effect was therefore conservatively
//! kept even when the guard was statically refutable. WI-592 lowers a
//! constructor `var_ref` to a ground `Ref` at the goal-lowering boundary
//! (`try_occurrence_to_term`), so the resolver decides it.
//!
//! This is the constructor-argument analog of `wi067_guard_discharge_test`
//! (which only exercised Int64 *literal* arguments, never a constructor). The
//! carrier here uses the STRUCTURAL `Eq` builtin (it only `provides Eq`, with no
//! override): dispatching a guard whose predicate is a carrier's *custom* spec-op
//! override is the separate WI-573 work.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Identical harness to `wi067_guard_discharge_test::load_result`.
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
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

/// The undeclared-effect diagnostic is `…effects: …got undeclared effect: Boom`
/// (typing.rs). Match BOTH fragments — not just `"Boom"` (which the sort name
/// alone would satisfy from any unrelated failure that happens to mention it).
fn is_undeclared_boom(errs: &[String]) -> bool {
    errs.iter()
        .any(|e| e.contains("undeclared effect") && e.contains("Boom"))
}

/// `Color` is a 2-constructor sort with STRUCTURAL `Eq` (only `provides Eq`, no
/// `eq` override). `risky(c)` raises `Boom` only when `c = Red`.
const COLOR_PRELUDE: &str = r#"
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}

  sort Boom
    entity Bang
  end

  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
  end

  operation risky(c: Color) -> Int64
    effects { Boom :- eq(c, Red) }
"#;

#[test]
fn nonmatching_constructor_arg_discharges() {
    // `risky(Green)` — `eq(Green, Red)` is structurally false, so `neq(Green, Red)`
    // is provable and `Boom` DROPS. Before WI-592 `Green` floundered as a
    // `var_ref`, so this caller wrongly required `effects Boom`. (This is the lone
    // `is_ok` case — it FAILS if the fix regresses, since the effect reappears.)
    let src = format!(
        r#"
namespace anthill.test.wi592drop
{COLOR_PRELUDE}
  operation caller() -> Int64 =
    risky(Green)
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "a non-matching constructor argument (`risky(Green)`, guard `eq(c, Red)`) \
         must refute the guard and drop `Boom`; got: {:#?}",
        res.err()
    );
}

#[test]
fn matching_constructor_arg_keeps_effect() {
    // `risky(Red)` — `eq(Red, Red)` HOLDS, so `Boom` must NOT discharge. This is
    // the soundness floor: drop only on a positive proof of `¬guard`.
    let src = format!(
        r#"
namespace anthill.test.wi592keep
{COLOR_PRELUDE}
  operation caller() -> Int64 =
    risky(Red)
end
"#
    );
    let errs = load_result(&src).expect_err(
        "a matching constructor argument (`risky(Red)`) keeps the guarded `Boom`; \
         omitting `effects Boom` must fail",
    );
    assert!(
        is_undeclared_boom(&errs),
        "expected the un-discharged `Boom` to surface as undeclared; got: {errs:#?}"
    );
}

#[test]
fn symbolic_constructor_arg_keeps_effect() {
    // `risky(c)` with `c` an unconstrained `Color` parameter: `eq(c, Red)` cannot
    // be decided (a real binder, kind `Param`, stays `var_ref` and flounders), so
    // `Boom` is conservatively kept — the WI-592 fix must NOT convert a genuine
    // binder to a ground `Ref` (only a constructor `var_ref`).
    let src = format!(
        r#"
namespace anthill.test.wi592sym
{COLOR_PRELUDE}
  operation caller(c: Color) -> Int64 =
    risky(c)
end
"#
    );
    let errs = load_result(&src).expect_err(
        "a symbolic `Color` parameter cannot refute `eq(c, Red)`, so `Boom` is \
         conservatively present; omitting it must fail",
    );
    assert!(
        is_undeclared_boom(&errs),
        "expected the conservatively-present `Boom` to surface as undeclared; \
         got: {errs:#?}"
    );
}

/// SOUNDNESS of the var_ref→Ref lowering: the guard must be decided by ACTUAL
/// structural equality of the constructors, not merely "is the argument a
/// constructor at all". With the guard `eq(c, Green)`:
///   * `risky(Red)`   → `eq(Red, Green)` is false → guard refuted → `Boom` DROPS;
///   * `risky(Green)` → `eq(Green, Green)` holds  → guard kept     → `Boom` STAYS.
/// The DROP half is the discriminating case: it fails if the argument did not
/// lower to a ground `Ref` distinct from `Green` (a `var_ref(Red)` would flounder
/// and wrongly keep), and it also fails a blanket "discharge every constructor"
/// bug (the KEEP half catches that one). This replaces an earlier same-guard,
/// same-arg test that was inert (it passed whether the fix was present or not,
/// because both `Ref(Green)=Ref(Green)` and a floundering `var_ref` keep `Boom`).
const ALT_GUARD_PRELUDE: &str = r#"
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}

  sort Boom
    entity Bang
  end

  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
  end

  operation risky(c: Color) -> Int64
    effects { Boom :- eq(c, Green) }
"#;

#[test]
fn discharge_distinguishes_constructors() {
    // DROP half — `risky(Red)` against guard `eq(c, Green)`.
    let drop_src = format!(
        r#"
namespace anthill.test.wi592altdrop
{ALT_GUARD_PRELUDE}
  operation caller() -> Int64 =
    risky(Red)
end
"#
    );
    let res = load_result(&drop_src);
    assert!(
        res.is_ok(),
        "guard `eq(c, Green)` at `risky(Red)` is false → must drop `Boom` (proves \
         the constructor arg lowered to a ground `Ref` distinct from `Green`); \
         got: {:#?}",
        res.err()
    );

    // KEEP half — `risky(Green)` against guard `eq(c, Green)` (guard holds).
    let keep_src = format!(
        r#"
namespace anthill.test.wi592altkeep
{ALT_GUARD_PRELUDE}
  operation caller() -> Int64 =
    risky(Green)
end
"#
    );
    let errs = load_result(&keep_src).expect_err(
        "guard `eq(c, Green)` at `risky(Green)` HOLDS → `Boom` must be kept; \
         omitting it must fail (guards against a blanket discharge-every-constructor)",
    );
    assert!(
        is_undeclared_boom(&errs),
        "expected the kept `Boom` to surface as undeclared; got: {errs:#?}"
    );
}
