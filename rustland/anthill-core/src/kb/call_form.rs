//! WI-801 — THE single owner of the spread-vs-whole decision at a function-value
//! application.
//!
//! Three sites have to agree on how many values a callable is handed, and before
//! this module they each derived it from a DIFFERENT quantity:
//!
//!   * the TYPER's argument check (`positional_arg_expectations`, kb/typing.rs)
//!     pivoted on `A`'s COMPONENT COUNT at a `Function[A, B, E]` slot;
//!   * the TYPER's conformance check (`arrow_function_compatible`) read neither —
//!     it skipped arity entirely, on the true-but-incomplete ground that a
//!     `Function` states none;
//!   * EVAL (`spread_eta_args` / `gather_closure_arg`, eval/eval.rs) pivoted on
//!     the CALLEE's OWN arity (`params.len()` / [`Pattern::binder_arity`]).
//!
//! They coincide only when the callback's arity is one the slot can actually
//! reach, and nothing established that: a 3-binder lambda at a 2-component `A`
//! LOADED CLEAN and trapped `ArityMismatch { expected: 3, got: 2 }` at eval — the
//! load-clean-then-trap class WI-782/791/792/788 exist to remove. (The OPERATION
//! spelling of the same program was already refused at load, because an op's
//! parameter list is a CONCRETE tuple type that fails the param comparison; an
//! unannotated lambda ADOPTS `A` as its param type (kb/typing.rs, `Expr::Lambda`),
//! so its param matches trivially and only its arity disagrees.)
//!
//! [`Pattern::binder_arity`] (kb/node_occurrence.rs) owns the count of binders a
//! pattern WRITES. This module owns what that count MEANS at an application.
//!
//! [`Pattern::binder_arity`]: crate::kb::node_occurrence::Pattern::binder_arity

/// How the values presented at ONE application relate to the callee's own
/// parameter arity. TOTAL over the two counts, so every combination is a named
/// outcome rather than an anonymous fallthrough.
///
/// FIELDLESS deliberately. Every variant's "payload" would be one of
/// [`classify_application`]'s own two arguments, so a consumer could learn
/// nothing from it that it did not already have in scope — and carrying them
/// invited exactly that misreading: two call sites destructured a payload into a
/// binding that SHADOWED the identical value they had just computed, reading as
/// if the classifier had told them something new.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallForm {
    /// The counts already agree — hand the values over as written.
    AsWritten,
    /// ONE value stands for the callee's whole parameter list, so it must be
    /// spread across it. Carries a DYNAMIC obligation the classifier cannot
    /// discharge on counts alone: that one value must really have `arity`
    /// components. Eval checks it against the value (`spread_eta_args`); the
    /// typer checks it against `A` ([`arity_admitted_at_function_slot`]).
    Spread,
    /// The callee takes ONE parameter and was handed several values, so they are
    /// that parameter's components and must be gathered into it.
    ///
    /// Only the TYPER can act on this, and that asymmetry is the point: gathering
    /// needs the component LABELS, which live in `A` and are erased by the time
    /// eval runs. The typer normalizes such a call into a whole-`A` tuple at the
    /// call site; eval reaching this arm means no static type said what the
    /// labels were, so it raises rather than guessing a positional spelling.
    Gather,
    /// Neither reading applies.
    Mismatch,
}

/// Relate a callable's own parameter `arity` to the number of values `supplied`
/// at one application.
///
/// The order of the arms is load-bearing. Equal counts are `AsWritten` FIRST, so
/// the degenerate `arity == supplied == 1` is a pass-through rather than a
/// vacuous spread or gather; only then do the two adapting readings apply, and
/// they cannot both fire because each demands the OTHER count be 1.
pub fn classify_application(arity: usize, supplied: usize) -> CallForm {
    if arity == supplied {
        CallForm::AsWritten
    } else if supplied == 1 {
        CallForm::Spread
    } else if arity == 1 {
        CallForm::Gather
    } else {
        CallForm::Mismatch
    }
}

/// WI-801: may a callable of `arity` parameters stand where a
/// `Function[A, B, E]` is declared?
///
/// `a_components` is `Some(n)` when `A` is a TUPLE type with `n` components, and
/// `None` when `A` is a known NON-tuple — one indivisible value. The caller must
/// pass no verdict at all (skip the check) when `A` is not yet known, so a
/// generic `Function[A = T, B]` stays unconstrained.
///
/// The rule is the spec's (docs/kernel-language.md §"the equivalence is not
/// exact"): a `Function[(A, B), R]` "accepts either" a single-tuple-argument
/// callback OR a two-parameter one, so exactly TWO call counts are reachable at
/// the slot — ONE whole `A` (WI-775) and `A`'s components spread (WI-784). A
/// callable that stands here will meet both, so it must handle both; anything
/// else typechecks and then traps.
///
/// Stated THROUGH [`classify_application`] rather than as the equivalent
/// `arity == 1 || Some(arity) == a_components`, deliberately: the admissible
/// arities are a CONSEQUENCE of what the call forms do, not an independent fact,
/// and spelling them independently is exactly how this site and eval came to
/// disagree.
///
/// ONE `supplied` suffices, though the slot admits two call counts. Asking the
/// classifier about both is redundant, not thorough: `supplied = 1` and
/// `supplied = |A|` provably yield the same verdict for every input (each reduces
/// to `arity == 1 || arity == |A|`), so the second question can only ever repeat
/// the first's answer. The SPREAD count is the one asked, because it is the count
/// whose `Spread` obligation is discharged below.
///
/// That obligation is what makes this more than an arity equality: `Spread` is
/// admissible only when `A` really HAS `arity` components, which is what keeps a
/// 2-binder callback out of a scalar `Function[A = Int64, B]` slot — `A`
/// contributes no components to spread, so only arity 1 can take it.
pub fn arity_admitted_at_function_slot(a_components: Option<usize>, arity: usize) -> bool {
    match classify_application(arity, a_components.unwrap_or(1)) {
        CallForm::AsWritten | CallForm::Gather => true,
        CallForm::Spread => a_components == Some(arity),
        CallForm::Mismatch => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classification_is_total_and_unambiguous() {
        assert_eq!(classify_application(2, 2), CallForm::AsWritten);
        assert_eq!(classify_application(1, 1), CallForm::AsWritten);
        assert_eq!(classify_application(0, 0), CallForm::AsWritten);
        assert_eq!(classify_application(2, 1), CallForm::Spread);
        assert_eq!(classify_application(1, 3), CallForm::Gather);
        assert_eq!(classify_application(3, 2), CallForm::Mismatch);
    }

    /// The equivalence [`arity_admitted_at_function_slot`]'s doc asserts, checked
    /// rather than claimed — both that the routed form matches the direct rule,
    /// and that the `supplied` it drops could not have changed the verdict.
    #[test]
    fn the_admitted_set_is_exactly_one_or_the_component_count() {
        for components in (0..8).map(Some).chain(std::iter::once(None)) {
            for arity in 0..8 {
                let direct = arity == 1 || Some(arity) == components;
                assert_eq!(
                    arity_admitted_at_function_slot(components, arity),
                    direct,
                    "components={components:?} arity={arity}",
                );
            }
        }
    }

    /// THE WI-801 defect, at the level of the rule: a 3-binder callback at a
    /// 2-component `A` fits neither reading.
    #[test]
    fn a_callback_fitting_neither_reading_is_refused() {
        assert!(!arity_admitted_at_function_slot(Some(2), 3));
        assert!(!arity_admitted_at_function_slot(Some(2), 0));
        assert!(!arity_admitted_at_function_slot(Some(3), 2));
    }

    /// Both readings the spec names stay admitted — this is what forbids the
    /// ticket's broader "binder count differs from A's arity" phrasing. Arity ONE
    /// is the CANONICAL inhabitant of `Function[A = (X, Y), B]`: `lambda t ->
    /// t._1` simply IS an `(X, Y) -> B`.
    #[test]
    fn both_admissible_readings_survive() {
        assert!(arity_admitted_at_function_slot(Some(2), 1));
        assert!(arity_admitted_at_function_slot(Some(2), 2));
        assert!(arity_admitted_at_function_slot(Some(3), 1));
        assert!(arity_admitted_at_function_slot(Some(3), 3));
        assert!(arity_admitted_at_function_slot(Some(1), 1));
    }

    /// The unit slot: `Function[A = (), B]` forced as `f()`. Arity 0 is admitted
    /// because it EQUALS the component count, not because 0 is special — the
    /// nullary thunk (`prelude/delay.anthill`) rides this arm.
    #[test]
    fn a_nullary_thunk_is_admitted_at_a_unit_slot() {
        assert!(arity_admitted_at_function_slot(Some(0), 0));
        assert!(arity_admitted_at_function_slot(Some(0), 1));
    }

    /// A NON-tuple `A` is one indivisible value, so only arity 1 can take it.
    /// Without `Spread`'s obligation being discharged against `A`, a 2-binder
    /// callback would slip in here: `classify_application(2, 1)` is a `Spread`,
    /// and it is admissible ONLY because `A` really has 2 components.
    #[test]
    fn a_scalar_slot_admits_only_arity_one() {
        assert!(arity_admitted_at_function_slot(None, 1));
        assert!(!arity_admitted_at_function_slot(None, 2));
        assert!(!arity_admitted_at_function_slot(None, 0));
    }
}
