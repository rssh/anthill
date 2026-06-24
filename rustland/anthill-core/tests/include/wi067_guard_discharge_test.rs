//! WI-067 (proposal 048 §"Typer delta" / 050 consumer 2): guarded effect
//! DISCHARGE at a call site. The dual of `wi478_guarded_effect_test`: where
//! WI-478 proves a guarded atom is *conservatively present* (no discharge), this
//! proves the typer now *drops* the guarded effect when it can CONSTRUCTIVELY
//! REFUTE the guard from the local interpretation environment Γ (proposal 050) +
//! ground evaluation + KB — and ONLY then (an unrefutable guard stays present,
//! the soundness default: drop only on a positive proof of ¬guard, never NAF).
//!
//! `risky(b)` carries `effects { Boom :- eq(b, 0) }`. Discharge fires iff
//! `neq(b, 0)` is provable at the call:
//!   * a NON-zero literal divisor (`risky(5)`) — refuted by ground evaluation;
//!   * a `b` narrowed non-zero by an enclosing `if neq(b, 0)` — refuted from Γ;
//!   * a `b` narrowed non-zero by an earlier `match` arm (`case 0 -> …`) — Γ;
//! and does NOT fire (effect stays present) for:
//!   * a symbolic divisor (`risky(b)`, `b` unknown) — `neq(b, 0)` flounders;
//!   * a literal ZERO divisor (`risky(0)`) — the guard genuinely holds.
//!
//! Each case is asserted at LOAD time (the effect check runs during loading): a
//! discharged call lets the caller omit `effects Boom` and load clean; an
//! undischarged one surfaces the conservatively-present `Boom` as an undeclared
//! effect — exactly the WI-478 harness, read in reverse.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load stdlib + user source together and surface load errors as strings.
/// Identical harness to `wi478_guarded_effect_test::load_result`.
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

/// The shared callee: `risky` carries a guarded `Boom`. It returns `Int64` so a
/// non-discharging branch can fall through to a plain `0` (the `Unit` literal is
/// awkward in expression position). The caller body varies per test; only the
/// bodies that establish `neq(b, 0)` may omit `effects Boom`.
const RISKY_PRELUDE: &str = r#"
  import anthill.prelude.{Int64}

  sort Boom
    entity Bang
  end

  operation risky(b: Int64) -> Int64
    effects { Boom :- eq(b, 0) }
"#;

#[test]
fn nonzero_literal_divisor_discharges() {
    // `risky(5)` — a non-zero literal. σ maps `b ↦ 5`, the guard becomes the
    // ground `eq(5, 0)`, and `refute_guard` proves `neq(5, 0)` by evaluation, so
    // `Boom` is DROPPED. The caller may omit `effects Boom` and still load clean.
    let src = format!(
        r#"
namespace anthill.test.wi067lit
{RISKY_PRELUDE}
  operation caller() -> Int64 =
    risky(5)
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "a non-zero literal divisor must refute the guard `eq(5, 0)` and drop \
         `Boom`, so the caller need not declare it; got: {:#?}",
        res.err()
    );
}

#[test]
fn zero_literal_divisor_keeps_effect() {
    // `risky(0)` — the guard `eq(0, 0)` HOLDS (`neq(0, 0)` is false), so the
    // effect must NOT be discharged. The undeclared `Boom` must surface (drop
    // only on a positive proof of ¬guard — never because a guard "looks
    // dischargeable").
    let src = format!(
        r#"
namespace anthill.test.wi067zero
{RISKY_PRELUDE}
  operation caller() -> Int64 =
    risky(0)
end
"#
    );
    let errs = load_result(&src).expect_err(
        "a literal-zero divisor keeps the guarded `Boom` (the guard holds); \
         omitting `effects Boom` must fail",
    );
    assert!(
        errs.iter().any(|e| e.contains("Boom")),
        "expected the un-discharged `Boom` to surface as an undeclared effect; \
         got: {errs:#?}"
    );
}

#[test]
fn if_branch_narrowed_divisor_discharges() {
    // `if neq(b, 0) then risky(b) else 0`. In the THEN branch Γ carries the
    // condition `neq(b, 0)` (the 050 if-fork narrowing), so the guard `eq(b, 0)`
    // is refuted straight from Γ and `Boom` drops; the else branch raises nothing.
    // The whole body is pure, so `caller` need not declare `Boom`.
    let src = format!(
        r#"
namespace anthill.test.wi067if
{RISKY_PRELUDE}
  operation caller(b: Int64) -> Int64 =
    if neq(b, 0) then risky(b) else 0
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "an `if neq(b, 0)` guard must narrow Γ so `risky(b)` in the then-branch \
         discharges `Boom`; the caller body is then pure. got: {:#?}",
        res.err()
    );
}

#[test]
fn symbolic_divisor_keeps_effect() {
    // `risky(b)` with `b` an unconstrained parameter: `neq(b, 0)` flounders
    // (open-world — the symbolic `b` could be 0 at runtime), so the guard is NOT
    // refuted and `Boom` stays conservatively present. Omitting `effects Boom`
    // must fail — the guard against over-discharge (NAF would wrongly drop here).
    let src = format!(
        r#"
namespace anthill.test.wi067sym
{RISKY_PRELUDE}
  operation caller(b: Int64) -> Int64 =
    risky(b)
end
"#
    );
    let errs = load_result(&src).expect_err(
        "a symbolic divisor cannot refute `eq(b, 0)`, so `Boom` is conservatively \
         present; omitting `effects Boom` must fail",
    );
    assert!(
        errs.iter().any(|e| e.contains("Boom")),
        "expected the conservatively-present `Boom` to surface as undeclared; \
         got: {errs:#?}"
    );

    // Declaring the effect at the caller loads clean — the conservative path is
    // unchanged from WI-478.
    let declared = format!(
        r#"
namespace anthill.test.wi067sym2
{RISKY_PRELUDE}
  operation caller(b: Int64) -> Int64
    effects Boom =
    risky(b)
end
"#
    );
    assert!(
        load_result(&declared).is_ok(),
        "declaring `Boom` at the caller subsumes the conservatively-present \
         guarded effect and loads clean"
    );
}

#[test]
fn refuted_guard_keeps_same_label_unconditional_effect() {
    // A row may carry the SAME label both UNCONDITIONALLY and guarded:
    // `{ Boom, Boom :- eq(b, 0) }` (the unreduced disjunction the 048 merge keeps).
    // Discharging the guarded `Boom` at a literal-divisor call must drop ONLY the
    // guarded twin and leave the unconditional `Boom` present — a blanket
    // label-removal would unsoundly lose the unconditional effect.
    let src = r#"
namespace anthill.test.wi067dup
  import anthill.prelude.{Int64}

  sort Boom
    entity Bang
  end

  operation risky2(b: Int64) -> Int64
    effects { Boom, Boom :- eq(b, 0) }

  operation caller() -> Int64 =
    risky2(5)
end
"#;
    let errs = load_result(src).expect_err(
        "the UNCONDITIONAL `Boom` survives discharge of the guarded twin, so a \
         caller omitting `effects Boom` must still fail",
    );
    assert!(
        errs.iter().any(|e| e.contains("Boom")),
        "expected the surviving unconditional `Boom` to surface as undeclared; \
         got: {errs:#?}"
    );

    // Declaring `Boom` loads clean — only the guarded twin discharged.
    let declared = r#"
namespace anthill.test.wi067dup2
  import anthill.prelude.{Int64}

  sort Boom
    entity Bang
  end

  operation risky2(b: Int64) -> Int64
    effects { Boom, Boom :- eq(b, 0) }

  operation caller() -> Int64
    effects Boom =
    risky2(5)
end
"#;
    assert!(
        load_result(declared).is_ok(),
        "declaring the surviving unconditional `Boom` must load clean"
    );
}

#[test]
fn match_arm_narrowed_divisor_discharges() {
    // `match b with case 0 -> 0 ; case _ -> risky(b)`. The earlier GROUND arm
    // `case 0` narrows the later arm's Γ with `neq(b, 0)` (the 050 match rule —
    // the canonical "past `case 0`" discharge), so `risky(b)` in the wildcard arm
    // refutes its guard and drops `Boom`. The caller is then pure.
    let src = format!(
        r#"
namespace anthill.test.wi067match
{RISKY_PRELUDE}
  operation caller(b: Int64) -> Int64 =
    match b
      case 0 -> 0
      case _ -> risky(b)
    end
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "an earlier `case 0` arm must narrow Γ with `neq(b, 0)` so the wildcard \
         arm's `risky(b)` discharges `Boom`; the caller is then pure. got: {:#?}",
        res.err()
    );
}

#[test]
fn denoted_modify_label_guard_discharges_and_keeps() {
    // A guarded effect whose LABEL is denoted (`Modify[c]`, value-parameterized)
    // rides the occurrence carrier (WI-478 `make_guarded_occ`), storing its guard
    // as a `Value::Entity` cons list. Discharge must read that carrier too — a
    // conditional `Modify` ("modifies c only when b = 0") is as first-class as a
    // conditional `Error`. At `maybe_modify(c, 5)` the guard `eq(5, 0)` refutes, so
    // `Modify[c]` DROPS and the caller need not declare it.
    let discharged = r#"
namespace anthill.test.wi067mod
  import anthill.prelude.{Unit, Cell, Int64}

  operation maybe_modify(c: Cell, b: Int64) -> Unit
    effects { Modify[c] :- eq(b, 0) }

  operation caller(c: Cell) -> Unit =
    maybe_modify(c, 5)
end
"#;
    assert!(
        load_result(discharged).is_ok(),
        "a literal-refutable guard on a DENOTED `Modify[c]` label must discharge \
         (read off its Value::Entity guard list), exactly like a ground label; \
         got: {:#?}",
        load_result(discharged).err()
    );

    // Symbolic `b` keeps `Modify[c]` — same soundness floor as the ground case.
    let kept = r#"
namespace anthill.test.wi067mod2
  import anthill.prelude.{Unit, Cell, Int64}

  operation maybe_modify(c: Cell, b: Int64) -> Unit
    effects { Modify[c] :- eq(b, 0) }

  operation caller(c: Cell, b: Int64) -> Unit =
    maybe_modify(c, b)
end
"#;
    let errs = load_result(kept).expect_err(
        "a symbolic `b` cannot refute the denoted-label guard, so `Modify[c]` is \
         conservatively present; omitting it must fail",
    );
    assert!(
        errs.iter().any(|e| e.contains("Modify")),
        "expected the conservatively-present `Modify[c]` to surface as undeclared; \
         got: {errs:#?}"
    );
}
