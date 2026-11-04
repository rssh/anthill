//! How a callable takes the tuple an application hands it — the one owner of the questions
//! the typer and eval must answer alike (kernel-language §4.4, "Every arrow is a `Function`").
//!
//! An application of a function value hands its callable ONE argument: the tuple `A` the
//! typer gathered the written arguments into (`f(7, 1)` over `(x: Int64, y: Int64) -> R` is
//! `f((x: 7, y: 1))`), or the one value of a non-tuple `A`. What the callable does with it is
//! its own: an operation of several parameters takes them from the components — by label where
//! its parameter names are `A`'s labels, by position otherwise ([`meets_slot_by_label`]) — a
//! lambda hands the tuple to its pattern, and a callable of one parameter takes it whole.
//!
//! [`classify_application`] relates the values a HOST call hands a callable (a builtin applying
//! a closure to two arguments) to the callable's own count; the typer's own applications are
//! already in the one-tuple form.
//!
//! [`Pattern::binder_arity`] (kb/node_occurrence.rs) owns the count of binders a pattern
//! WRITES.
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
    /// typer checks it against `A` (the application match).
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

/// Rule 6 of proposal 002 (kernel-language §4.4, "A callable where a function type is
/// expected"): does a callable of several parameters meet a slot's `A` BY LABEL? It does when
/// the two tuples carry the same labels — the callable's parameter names are `A`'s component
/// labels, in any order — and otherwise the components meet the parameters BY POSITION, the
/// first to the first. A positional `A` (`_1.._n`) carries no labels of its own to agree on,
/// and a lambda's tuple has none either.
///
/// THE ONE OWNER, read by the typer where it re-expresses the callable at the slot and by eval
/// where an operation value takes the tuple (`spread_eta_args`), so the two cannot map one call
/// differently. Labels are compared by SHORT name, as `TupleComponents::by_label_index` reads a
/// tuple's components.
pub fn meets_slot_by_label(own: &[&str], slot: &[&str]) -> bool {
    own.len() == slot.len()
        && !own.is_empty()
        && own.iter().all(|o| slot.contains(o))
        && slot.iter().all(|l| own.contains(l))
}

/// For each of a callable's parameters, the index of the slot's `A` component it takes — by
/// label where [`meets_slot_by_label`] holds, by position otherwise. `None` when the counts
/// differ: two arguments do not meet three components (the application match).
pub fn slot_components_of_params(own: &[&str], slot: &[&str]) -> Option<Vec<usize>> {
    if own.len() != slot.len() {
        return None;
    }
    if meets_slot_by_label(own, slot) {
        own.iter().map(|o| slot.iter().position(|l| l == o)).collect()
    } else {
        Some((0..own.len()).collect())
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

    /// Rule 6: the same labels in another order meet by label; any other labels, a lambda's
    /// positional tuple, or a positional slot, by position; different counts not at all.
    #[test]
    fn a_callable_meets_a_slot_by_label_or_by_position() {
        assert_eq!(slot_components_of_params(&["y", "x"], &["x", "y"]), Some(vec![1, 0]));
        assert_eq!(slot_components_of_params(&["z", "x"], &["x", "y"]), Some(vec![0, 1]));
        assert_eq!(slot_components_of_params(&["a", "b"], &["_1", "_2"]), Some(vec![0, 1]));
        assert_eq!(slot_components_of_params(&["_1", "_2"], &["acc", "x"]), Some(vec![0, 1]));
        assert_eq!(slot_components_of_params(&["a", "b", "c"], &["_1", "_2"]), None);
        assert_eq!(slot_components_of_params(&[], &[]), Some(vec![]));
        assert!(!meets_slot_by_label(&["x", "x"], &["x", "y"]));
    }
}
