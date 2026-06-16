//! WI-347 — operation-override refinement (Phase 1: effects-⊆).
//!
//! A carrier's own operation that implements/overrides a spec operation
//! (own-op-beats-inherited, §8.7) must REFINE it. This phase checks the
//! effect row: each override effect must be covered by some spec effect under
//! `<:` (the `spec-instance-dispatch.md §"Effect compatibility"` rule). An
//! override that widens the effect row — raising an effect the spec doesn't
//! cover — is rejected, because a caller programming against the spec's
//! contract has no handler for it.
//!
//! Enforced only for ground effect rows (fail-open on parametric `effects E` /
//! denoted `Modify[c]`), so the stdlib's polymorphic-effect providers are
//! unaffected — see the matching stdlib-stays-green assertions in the
//! wi343/wi345 suites.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extra: &str) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

// ── widening the effect row is rejected ─────────────────────────────────

#[test]
fn override_widening_effect_rejected() {
    // `Sp.op` declares `effects Eff1`; `Carrier` provides `Sp` and its override
    // `op` declares `effects Eff2`, an unrelated effect not covered by `Eff1`.
    // A caller of `Sp.op` set up handlers for `Eff1`, so the `Eff2`-raising
    // override is unsound → rejected.
    let src = r#"
        namespace wi347.widen
          import anthill.prelude.{Effect, Int64}
          sort Eff1 end
          sort Eff2 end
          fact Effect[T = Eff1]
          fact Effect[T = Eff2]
          sort Sp
            sort T = ?
            operation op(x: T) -> T effects Eff1
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier effects Eff2 = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e|
            e.contains("wi347.widen.Carrier") && e.contains("op") && e.contains("Eff2")),
        "expected an IncompatibleOverride naming Carrier, op, and the uncovered Eff2; got: {errs:?}");
}

// ── matching effect row loads clean ─────────────────────────────────────

#[test]
fn override_matching_effect_loads() {
    // The override declares exactly the spec's effect (`Eff1`) — equal rows are
    // trivially a subset, so it loads.
    let src = r#"
        namespace wi347.match
          import anthill.prelude.{Effect, Int64}
          sort Eff1 end
          fact Effect[T = Eff1]
          sort Sp
            sort T = ?
            operation op(x: T) -> T effects Eff1
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier effects Eff1 = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(errs.is_empty(),
        "override declaring the spec's own effect should load clean; got: {errs:?}");
}

// ── a pure override (no effects) is fine ────────────────────────────────

#[test]
fn override_pure_op_loads() {
    // Neither the spec op nor the override declares effects — nothing to widen.
    let src = r#"
        namespace wi347.pure
          import anthill.prelude.{Int64}
          sort Sp
            sort T = ?
            operation op(x: T) -> T
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(errs.is_empty(),
        "a pure override of a pure spec op should load clean; got: {errs:?}");
}

// ── dropping a spec effect (narrowing) loads clean ──────────────────────

#[test]
fn override_dropping_effect_loads() {
    // The spec op declares `effects Eff1`, but the override is pure (raises
    // nothing). Narrowing the row is sound — the override simply never uses an
    // effect the spec permits — so it loads. (Empty ⊆ {Eff1}.)
    let src = r#"
        namespace wi347.narrow
          import anthill.prelude.{Effect, Int64}
          sort Eff1 end
          fact Effect[T = Eff1]
          sort Sp
            sort T = ?
            operation op(x: T) -> T effects Eff1
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(errs.is_empty(),
        "an override that drops a spec effect (narrows the row) should load clean; got: {errs:?}");
}

// ── strengthening the precondition is rejected ──────────────────────────

#[test]
fn override_strengthening_precondition_rejected() {
    // Spec `op` has no precondition; the override adds `requires gt(x, 0)`,
    // demanding more of callers than the spec promised. A caller that satisfied
    // the spec's (empty) precondition could now violate the override's — unsound.
    let src = r#"
        namespace wi347.pre_strong
          import anthill.prelude.{Int64}
          import anthill.prelude.Ordered.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> T
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier requires gt(x, 0) = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e|
            e.contains("wi347.pre_strong.Carrier") && e.contains("op") && e.contains("precondition")),
        "expected IncompatibleOverride: the override strengthens the precondition; got: {errs:?}");
}

// ── weakening the postcondition is rejected ─────────────────────────────

#[test]
fn override_weakening_postcondition_rejected() {
    // Spec `op` promises `ensures gt(x, 0)`; the override drops it, promising
    // less than the spec — a caller relying on the postcondition is unsound.
    let src = r#"
        namespace wi347.post_weak
          import anthill.prelude.{Int64}
          import anthill.prelude.Ordered.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> T ensures gt(x, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e|
            e.contains("wi347.post_weak.Carrier") && e.contains("op") && e.contains("postcondition")),
        "expected IncompatibleOverride: the override weakens the postcondition; got: {errs:?}");
}

// ── matching contract loads clean (param-alignment) ─────────────────────

#[test]
fn override_matching_contract_loads() {
    // The override declares exactly the spec's precondition and postcondition.
    // Equal contracts (modulo the positional param rename) trivially refine, so
    // it loads — pins that the check does not false-positive on a faithful impl.
    let src = r#"
        namespace wi347.contract_ok
          import anthill.prelude.{Int64}
          import anthill.prelude.Ordered.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> T requires gt(x, 0) ensures gt(x, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier requires gt(x, 0) ensures gt(x, 0) = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(errs.is_empty(),
        "matching precondition/postcondition on spec and override should load clean; got: {errs:?}");
}
