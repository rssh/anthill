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

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

fn load_errors(extra: &str) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
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
    assert!(
        errs.is_empty(),
        "override declaring the spec's own effect should load clean; got: {errs:?}"
    );
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
    assert!(
        errs.is_empty(),
        "a pure override of a pure spec op should load clean; got: {errs:?}"
    );
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
    assert!(
        errs.is_empty(),
        "an override that drops a spec effect (narrows the row) should load clean; got: {errs:?}"
    );
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
          import anthill.prelude.Ord.{gt}
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
        errs.iter().any(|e| e.contains("wi347.pre_strong.Carrier")
            && e.contains("op")
            && e.contains("precondition")),
        "expected IncompatibleOverride: the override strengthens the precondition; got: {errs:?}"
    );
}

// ── weakening the postcondition is rejected ─────────────────────────────

#[test]
fn override_weakening_postcondition_rejected() {
    // Spec `op` promises `ensures gt(x, 0)`; the override drops it, promising
    // less than the spec — a caller relying on the postcondition is unsound.
    let src = r#"
        namespace wi347.post_weak
          import anthill.prelude.{Int64}
          import anthill.prelude.Ord.{gt}
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
        errs.iter().any(|e| e.contains("wi347.post_weak.Carrier")
            && e.contains("op")
            && e.contains("postcondition")),
        "expected IncompatibleOverride: the override weakens the postcondition; got: {errs:?}"
    );
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
          import anthill.prelude.Ord.{gt}
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
    assert!(
        errs.is_empty(),
        "matching precondition/postcondition on spec and override should load clean; got: {errs:?}"
    );
}

// ── result-binder alignment (the C8 fix) ────────────────────────────────
//
// `result` is defined per operation as `<op>.result` (proposal 041), so the
// spec's binder and the override's are DIFFERENT symbols. The contract legs
// compare clauses structurally, so before the alignment landed no clause
// mentioning `result` could ever match — and a spec operation carrying ANY
// `ensures` therefore had NO POSSIBLE PROVIDER, even one restating the
// postcondition verbatim.
//
// WHICH TESTS FAIL IF THE ALIGNMENT IS BACKED OUT: only the first of the three
// below. `override_matching_result_postcondition_loads` goes red; the other two
// pass either way BY DESIGN and are here to stop the first from being satisfied
// by an alignment that merely disabled the leg in the result position — one
// pins that a genuinely different postcondition is still refused, the other
// that a mismatched return type is still refused. The pre-existing
// `override_matching_contract_loads` above passes either way too: its clauses
// range over a PARAMETER, which the parameter zip already aligned.

#[test]
fn override_matching_result_postcondition_loads() {
    // THE C8 CASE. Verbatim restatement of a `result`-mentioning postcondition.
    // Fails when the result-binder alignment is removed.
    let src = r#"
        namespace wi347.result_ok
          import anthill.prelude.{Int64}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> T ensures gt(result, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier ensures gt(result, 0) = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "an override restating the spec's `result` postcondition verbatim must load; got: {errs:?}"
    );
}

#[test]
fn override_weaker_result_postcondition_is_refused() {
    // CONTROL for the above: the alignment must not turn the postcondition leg
    // into a no-op in the result position. A DIFFERENT clause over `result` is
    // still a weakening.
    let src = r#"
        namespace wi347.result_weak
          import anthill.prelude.{Int64}
          import anthill.prelude.Ord.{gt, lt}
          sort Sp
            sort T = ?
            operation op(x: T) -> T ensures gt(result, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier ensures lt(result, 0) = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("weakens the postcondition")),
        "a different `result` postcondition must still be refused; got: {errs:?}"
    );
}

// ── σ has TWO readers, and the effects leg is the other one (WI-20260822-59CDQ) ──
//
// The σ re-key below the provision walk was made for the return-type guard, but the
// effects leg reads the same σ. Its `confident` gate demands a GROUND σ-substituted
// spec row; while σ was keyed on the raw binding copy the substitution no-opped, a
// spec row naming a spec type parameter stayed parametric, and the leg fail-opened.
// It now grounds, so the leg actually runs there. Found by /code-review, which was
// right that the change had one measured reader and two real ones.

#[test]
fn a_sigma_bound_effect_row_is_compared() {
    // The spec op's effect row names the spec's own parameter `E`; the provision binds
    // `E = Eff1`; the override raises the unrelated `Eff2`. MEASURED: this loaded with
    // ZERO errors before σ was keyed on the resolved spec-param symbol.
    //
    // BACK-OUT A (σ keyed on the raw provision binding key) makes it load clean again.
    let src = r#"
        namespace wi347.eff_sigma
          import anthill.prelude.{Effect, Int64}
          sort Eff1 end
          sort Eff2 end
          fact Effect[T = Eff1]
          fact Effect[T = Eff2]
          sort Sp
            sort T = ?
            sort E = ?
            operation op(x: T) -> T effects E
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier, E = Eff1]
            operation op(x: Carrier) -> Carrier effects Eff2 = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("wi347.eff_sigma.Carrier")
            && e.contains("Eff2")
            && e.contains("effects must not widen")),
        "a σ-bound spec effect row must be compared, not fail open; got: {errs:?}"
    );
}

#[test]
fn a_sigma_bound_effect_row_that_matches_still_loads() {
    // CONTROL, and it PASSES EITHER WAY BY DESIGN — before the re-key the leg was
    // skipped, after it the row is covered, and both admit the program. It is here so
    // the test above cannot be satisfied by a σ that grounds the spec row to something
    // no override could ever match.
    let src = r#"
        namespace wi347.eff_sigma_ok
          import anthill.prelude.{Effect, Int64}
          sort Eff1 end
          fact Effect[T = Eff1]
          sort Sp
            sort T = ?
            sort E = ?
            operation op(x: T) -> T effects E
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier, E = Eff1]
            operation op(x: Carrier) -> Carrier effects Eff1 = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "an override declaring exactly the σ-bound spec effect must load; got: {errs:?}"
    );
}

// ── the return type behind a `result` clause (WI-20260822-59CDQ) ────────
//
// MEASURED BACK-OUTS. Each line is a mutation actually applied to
// `check_override_refinement` and re-run, not a prediction:
//
//   A  σ keyed on the raw provision binding key, as it was
//        → `result_ret_mismatch_survives_sigma` AND
//          `a_sigma_bound_effect_row_is_compared` — σ has TWO readers  (2)
//   B  the return-type guard skipped entirely
//        → `result_ret_mismatch_survives_sigma`,
//          `result_alignment_requires_the_return_types_to_agree`, and
//          `a_return_type_refusal_does_not_hide_an_independent_contract_defect`  (3)
//   C  the guard's condition weakened from "the alignment DISCHARGES a clause"
//      to "a clause MENTIONS the binder"
//        → `a_weakening_is_reported_as_one_even_when_the_return_types_also_differ` (1)
//   C₂ that same condition widened to "mentions any ALIGNED symbol" (params too)
//        → C's test, plus `a_mismatched_return_type_no_clause_reads_…`  (2)
//   D  `wants_result_alignment` widened (raw `requires`, plus the impl's `ensures`)
//        → NOTHING alone. With C as well it adds
//          `an_impl_only_ensures_over_result_…`, which is the honest statement:
//          the discharge test is what protects that case today and the gate is a
//          second, currently redundant guard on it. The gate's other job is a COST
//          one — reading the raw `requires` list opens it for every override with an
//          effect-row variable, because the loader injects an `EffectsRuntime` clause
//          there — and nothing here measures that.
//   H  the contract-name check's dedup keyed on the functor alone
//        → `one_misspelling_in_both_clause_lists_is_reported_twice`      (1)
//   F  the return-type test spelled as structural equality, not `<:`
//        → `a_covariant_return_type_still_discharges_the_result_clause`  (1)
//   B₂ the return-type refusal `continue`ing past the contract legs
//        → `a_return_type_refusal_does_not_hide_an_independent_contract_defect` (1)
//   G  "cannot decide" treated as "differs" (the ground gate dropped)
//        → NOTHING alone: σ grounds every case these fixtures reach, so the ground
//          gate is inert here on its own. With A as well it takes THREE —
//          `a_parametric_return_type_still_loads`, `result_ret_mismatch_survives_sigma`,
//          `override_matching_result_postcondition_loads` and
//          `a_sigma_bound_effect_row_is_compared` — i.e. the C8 bug back.
//          That pair is the only evidence the ground gate has, and it is why the
//          gate is not deleted as dead.

#[test]
fn result_alignment_requires_the_return_types_to_agree() {
    // THE SOUNDNESS SIDE (WI-20260822-59CDQ). Nothing else on this pass compares
    // return types (kernel-language.md §8.7 — a provision certifies that a member
    // of that NAME exists, not that it fits), so aligning the binders
    // unconditionally lets an IDENTICAL `ensures P(result)` match across two
    // different return types, discharging a postcondition about a value of the
    // wrong type.
    //
    // BOTH RETURN TYPES ARE GROUND HERE. The parametric case — a spec that returns
    // its own type parameter — is the sibling test below, and it is the one that
    // actually loaded clean before this landed.
    //
    // BACK-OUT B (see the block above) makes this and
    // `result_ret_mismatch_survives_sigma` load clean; nothing else moves.
    let src = r#"
        namespace wi347.result_ret_mismatch
          import anthill.prelude.{Int64, Bool}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64 ensures gt(result, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Bool ensures gt(result, 0) = true
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("wi347.result_ret_mismatch.Carrier")
            && e.contains("returns `Bool`")
            && e.contains("returns `Int64`")),
        "the refusal must NAME BOTH return types, not report a weakened postcondition; got: {errs:?}"
    );
}

#[test]
fn result_ret_mismatch_survives_sigma() {
    // THE CASE THAT ACTUALLY LOADED CLEAN (WI-20260822-59CDQ). The spec returns its
    // own type PARAMETER, which the provision binds to `Carrier` — so the honest
    // comparison is `Int64` (what the override returns) against `Carrier` (what the
    // spec promises here), and it is a mismatch.
    //
    // It only became decidable once σ was keyed on the RESOLVED spec-param symbol.
    // Before that the binding key was a different `Symbol` copy,
    // `substitute_impl_params_alloc` matched nothing, the spec's return type stayed
    // the un-substituted `T`, and the ground gate skipped the comparison entirely.
    // MEASURED: this program loaded with ZERO errors.
    //
    // BACK-OUT A takes this one and ONLY this one:
    // `result_alignment_requires_the_return_types_to_agree` above has a ground spec
    // return type and never needed σ. It is also one of the three A+G takes.
    let src = r#"
        namespace wi347.result_ret_sigma
          import anthill.prelude.{Int64}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> T ensures gt(result, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Int64 ensures gt(result, 0) = 1
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("wi347.result_ret_sigma.Carrier")
            && e.contains("returns `Int64`")
            && e.contains("returns `Carrier`")),
        "a spec returning its own parameter must be σ-grounded before the comparison; got: {errs:?}"
    );
}

#[test]
fn a_parametric_return_type_still_loads() {
    // THE CONTROL FOR BOTH OF THE ABOVE, and the one that stops the guard from
    // becoming the C8 bug one case narrower. The spec returns `T`, the provision
    // binds `T = Carrier`, and the override returns `Carrier` — so σ grounds the
    // spec's return type to exactly what the override returns and the `result`
    // clause is discharged.
    //
    // IT PASSED BEFORE THIS TICKET TOO, for the opposite reason — σ was inert, so
    // the comparison was skipped — which is why it cannot stand in for
    // `result_ret_mismatch_survives_sigma`. What it does pin is measured: it is one
    // of the three tests BACK-OUT A+G takes, the pair that turns "cannot decide"
    // into "differs" over a spec return type σ can no longer ground. Neither A nor
    // G alone moves it.
    let src = r#"
        namespace wi347.result_ret_parametric
          import anthill.prelude.{Int64}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> T ensures gt(result, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier ensures gt(result, 0) = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "the ordinary parametric provider must still load; got: {errs:?}"
    );
}

#[test]
fn a_return_type_refusal_does_not_hide_an_independent_contract_defect() {
    // The return-type refusal is reported BESIDE the contract legs, not instead of
    // them. This override does two independent wrong things — it returns `Bool` where
    // the spec returns `Int64` under a discharged `result` postcondition, AND it
    // strengthens the precondition with a `requires` the spec does not state. Both
    // must be named on one load; an author who fixes the return type and reloads must
    // not then discover a second error that was always there.
    //
    // FAILS IF the return-type refusal `continue`s past the contract legs, which is
    // what the first cut did. Found by /code-review.
    let src = r#"
        namespace wi347.two_defects
          import anthill.prelude.{Int64, Bool}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64 ensures gt(result, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Bool requires gt(x, 0) ensures gt(result, 0) = true
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("returns `Bool`") && e.contains("returns `Int64`")),
        "the return-type mismatch must be reported; got: {errs:?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("strengthens the precondition")),
        "the independent precondition defect must be reported on the SAME load; got: {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("weakens the postcondition")),
        "the `result` postcondition IS restated verbatim and must not also be reported \
         as weakened — that double-report is what the return-type error replaces; got: {errs:?}"
    );
}

#[test]
fn a_covariant_return_type_still_discharges_the_result_clause() {
    // THE COMPARISON IS `impl_ret <: spec_ret`, NOT EQUALITY. An override may return
    // a SUBTYPE of what the spec declares, and a predicate about a value of the
    // subtype is the same proposition — so the `result` clause is still discharged.
    // `Carrier` provides `Base`, which is what makes `Carrier <: Base` hold
    // (`sort_provides_admissibly`).
    //
    // BACK-OUT F takes it, and only it — the refusal then reads as a weakened
    // postcondition on a faithful override.
    let src = r#"
        namespace wi347.result_ret_covariant
          import anthill.prelude.{Int64}
          import anthill.prelude.Ord.{gt}
          sort Base
            sort B = ?
          end
          sort Sp
            sort T = ?
            operation op(x: T) -> Base ensures gt(result, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Base[B = Carrier]
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Carrier ensures gt(result, 0) = x
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "a covariant (subtype) return type must still discharge the clause; got: {errs:?}"
    );
}

#[test]
fn a_mismatched_return_type_no_clause_reads_is_not_this_passs_business() {
    // SCOPE CONTROL. The return types differ, but neither contract clause mentions
    // `result` — so the alignment reaches nothing and no comparison here depends on
    // the return types. Refusing it would be the general signature-conformance check
    // this pass deliberately does not do (kernel-language.md §8.7 / WI-935; enforcing it is WI-20260822-1MAGR), and
    // silently widening into that scope is what this test exists to catch.
    //
    // BACK-OUT C₂ takes it — a guard that fires when the alignment rewrites ANY
    // symbol rather than the result binder specifically, which the parameter zip
    // makes true of `gt(x, 0)` on every override. C alone does not.
    let src = r#"
        namespace wi347.ret_mismatch_no_result
          import anthill.prelude.{Int64, Bool}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64 ensures gt(x, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Bool ensures gt(x, 0) = true
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "a return-type mismatch no contract clause reads is not this check's scope; got: {errs:?}"
    );
}

#[test]
fn a_weakening_is_reported_as_one_even_when_the_return_types_also_differ() {
    // THIRD SCOPE CONTROL, and the reason the guard's condition is the DISCHARGE and
    // not "a clause mentions `result`". Here the override's postcondition matches the
    // spec's under NEITHER alignment — the spec promises something about its
    // parameter, the override about its result — so the binder discharges nothing and
    // the genuine defect is the weakening. The return types also differ, and naming
    // them would send the author to a line whose repair would not make this load.
    //
    // BACK-OUT C takes it, and only it.
    let src = r#"
        namespace wi347.weaken_and_ret
          import anthill.prelude.{Int64, Bool}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64 ensures gt(x, 0)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Bool ensures gt(result, 0) = true
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("weakens the postcondition")),
        "the defect here is the weakening, and that is what must be named; got: {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("returns `Bool`")),
        "the return types decide nothing here and must not be reported; got: {errs:?}"
    );
}

#[test]
fn an_impl_only_ensures_over_result_is_not_this_passs_business() {
    // SECOND SCOPE CONTROL, and the one that caught a real over-refusal in the
    // first cut of this guard. The spec declares NO postcondition, so the
    // postcondition leg never runs and nothing is discharged — the override is
    // simply promising more than it was asked to, which is a refinement. What it
    // returns is then the general signature question (§8.7 / WI-935, owned by WI-20260822-1MAGR), not this
    // pass's, even though its `ensures` does mention `result`.
    //
    // MEASURED, AND THE ONE CASE THAT NEEDS TWO BACK-OUTS: neither C nor D moves it
    // alone — the discharge test finds no spec clause to match against, and that
    // alone is enough. It falls under C+D together. So `wants_result_alignment` is
    // a redundant second guard here today, kept because it is also the cheap gate
    // that keeps two qualified-name lookups off every op pair in the stdlib.
    let src = r#"
        namespace wi347.impl_only_ensures
          import anthill.prelude.{Int64, Bool}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Bool ensures gt(result, 0) = true
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "an override adding its own `result` postcondition discharges nothing; got: {errs:?}"
    );
}

// ── contract clauses resolve their predicate names (WI-20260822-59CDQ) ──
//
// A `requires` / `ensures` clause is a goal written on a DECLARATION, so neither
// §5.3 name check reached it: the operation-body one walks bodies, WI-1034/WI-1058
// walk rule bodies. MEASURED before the fix: replacing a real `ensures` predicate
// with an invented one loaded byte-identically, so the refinement check above was
// comparing spellings that denote nothing.
//
// BACK-OUT E (the pass's errors dropped on the floor) takes exactly the three
// tests below that assert a refusal; `a_declared_contract_predicate_still_loads`
// passes either way BY DESIGN and is the control against a pass that refuses
// everything.
//
// THE POPULATION WAS NOT EMPTY, and the census that said it was could not see it:
// zero undefined contract names across stdlib and every `.anthill` project, but the
// full suite then found one — `wi618_bare_arrow_logic_test`'s `mentions`, a
// placeholder in a fixture written inline in Rust. It now carries a rule, and that
// file says why.

#[test]
fn an_ensures_naming_nothing_is_a_load_error() {
    let src = r#"
        namespace wi347.bogus_ensures
          import anthill.prelude.{Int64}
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64 ensures totally_bogus_predicate(result)
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("totally_bogus_predicate")
            && e.contains("wi347.bogus_ensures.Sp.op")
            && e.contains("ensures")),
        "an `ensures` naming an undeclared predicate must be refused; got: {errs:?}"
    );
}

#[test]
fn a_requires_naming_nothing_is_a_load_error_inside_a_multi_goal_clause() {
    // The conjunct position matters: the loader lowers `a, b` as one
    // `conjunction(a, b)` term, so a walk that tested the clause's head instead of
    // splitting it would miss BOTH conjuncts and report `conjunction` instead.
    // `gt` here is declared and must NOT be reported.
    let src = r#"
        namespace wi347.bogus_requires
          import anthill.prelude.{Int64}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64 requires bogus_precondition(x), gt(x, 0)
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("bogus_precondition")
            && e.contains("wi347.bogus_requires.Sp.op")
            && e.contains("requires")),
        "a `requires` conjunct naming an undeclared predicate must be refused; got: {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("conjunction")),
        "the multi-goal wrapper must be split, never reported as the goal; got: {errs:?}"
    );
}

#[test]
fn the_contract_name_check_reaches_every_operation_shape() {
    // POPULATION CONTROL. The pass's population is `op_decl_sites`, one entry per
    // `Item::Operation` the phase converts — a different set from the
    // `OperationInfo` facts the census that measured this gap walked. If it covered
    // only one declaration shape the two positive tests above would still pass while
    // the check silently missed most of the tree, so drive all three shapes at once:
    // a NAMESPACE-level operation, a spec member (body-less), and a carrier member
    // WITH a body. Each carries its own distinctly-spelled bogus predicate, so the
    // assertion cannot be satisfied by one of them three times.
    let src = r#"
        namespace wi347.every_shape
          import anthill.prelude.{Int64}
          operation free_op(x: Int64) -> Int64 ensures bogus_at_namespace(result) = x
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64 ensures bogus_at_spec(result)
          end
          sort Carrier
            entity c(id: Int64)
            fact Sp[T = Carrier]
            operation op(x: Carrier) -> Int64 ensures bogus_at_carrier(result) = 1
          end
        end
    "#;
    let errs = load_errors(src);
    for (shape, functor) in [
        ("namespace-level", "bogus_at_namespace"),
        ("spec member", "bogus_at_spec"),
        ("carrier member with a body", "bogus_at_carrier"),
    ] {
        assert!(
            errs.iter().any(|e| e.contains(functor)),
            "the check must reach a {shape} operation ({functor}); got: {errs:?}"
        );
    }
}

#[test]
fn one_misspelling_in_both_clause_lists_is_reported_twice() {
    // One misspelling is one edit PER PLACE IT IS WRITTEN. The same undeclared name in
    // an operation's `requires` and in its `ensures` is two lines to fix, and both
    // report at the same declaration span — so the clause kind is the only thing
    // distinguishing them and the dedup must be keyed on it.
    //
    // FAILS IF the dedup is keyed on the functor alone, which is what the first cut
    // did: the `ensures` occurrence stayed silent until the `requires` one was fixed
    // and the file reloaded. Found by /code-review.
    let src = r#"
        namespace wi347.both_lists
          import anthill.prelude.{Int64}
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64 requires same_bogus_name(x) ensures same_bogus_name(result)
          end
        end
    "#;
    let errs = load_errors(src);
    let hits: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("same_bogus_name") && e.contains("wi347.both_lists.Sp.op"))
        .collect();
    assert_eq!(
        hits.len(),
        2,
        "both the `requires` and the `ensures` occurrence must be named; got: {errs:?}"
    );
    assert!(
        hits.iter().any(|e| e.contains("`requires` clause"))
            && hits.iter().any(|e| e.contains("`ensures` clause")),
        "the two must be distinguished by clause kind; got: {hits:?}"
    );
}

#[test]
fn a_declared_contract_predicate_still_loads() {
    // CONTROL for the two above: the check must not refuse the ordinary case.
    // Distinct from `override_matching_contract_loads` — that one exercises the
    // refinement legs, this one exercises the NAME check on a spec op with no
    // provider at all, so a regression that refused every contract clause would be
    // caught here even if the refinement legs never ran.
    let src = r#"
        namespace wi347.contract_names_ok
          import anthill.prelude.{Int64}
          import anthill.prelude.Ord.{gt}
          sort Sp
            sort T = ?
            operation op(x: T) -> Int64 requires gt(x, 0) ensures gt(result, 0)
          end
        end
    "#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "declared contract predicates must load clean; got: {errs:?}"
    );
}
