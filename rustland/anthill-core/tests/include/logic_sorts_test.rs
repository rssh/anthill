//! Logic.Minimal / Logic.Constructive / Logic.Classical land in the
//! stdlib and form a `requires` chain.

use crate::common::load_stdlib_kb as load_stdlib;

#[test]
fn logic_sorts_are_in_stdlib() {
    let kb = load_stdlib();
    for qn in [
        "anthill.logic.Minimal.Minimal",
        "anthill.logic.Constructive.Constructive",
        "anthill.logic.Classical.Classical",
    ] {
        assert!(
            kb.try_resolve_symbol(qn).is_some(),
            "expected stdlib sort `{qn}` to be defined"
        );
    }
}

#[test]
fn classical_axioms_are_present() {
    let kb = load_stdlib();
    for rule in [
        "anthill.logic.Classical.Classical.excluded_middle",
        "anthill.logic.Classical.Classical.contradiction",
        "anthill.logic.Classical.Classical.double_negation",
    ] {
        assert!(
            kb.try_resolve_symbol(rule).is_some(),
            "expected Classical rule `{rule}` to be defined"
        );
    }
}

#[test]
fn constructive_axioms_are_present() {
    let kb = load_stdlib();
    for rule in [
        "anthill.logic.Constructive.Constructive.identity",
        "anthill.logic.Constructive.Constructive.modus_ponens",
        "anthill.logic.Constructive.Constructive.conjunction_intro",
        "anthill.logic.Constructive.Constructive.ex_falso",
    ] {
        assert!(
            kb.try_resolve_symbol(rule).is_some(),
            "expected Constructive rule `{rule}` to be defined"
        );
    }
}
