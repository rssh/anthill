//! Logic.Minimal / Logic.Constructive / Logic.Classical land in the
//! stdlib and form a `requires` chain.

mod common;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_stdlib() -> KnowledgeBase {
    let stdlib = common::stdlib_dir();
    let files = common::collect_anthill_files(&stdlib);
    let parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p).unwrap();
        parse::parse(&src).unwrap()
    }).collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

#[test]
fn logic_sorts_are_in_stdlib() {
    let kb = load_stdlib();
    for qn in [
        "anthill.logic.Minimal.Minimal",
        "anthill.logic.Constructive.Constructive",
        "anthill.logic.Classical.Classical",
    ] {
        assert!(kb.try_resolve_symbol(qn).is_some(),
            "expected stdlib sort `{qn}` to be defined");
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
        assert!(kb.try_resolve_symbol(rule).is_some(),
            "expected Classical rule `{rule}` to be defined");
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
        assert!(kb.try_resolve_symbol(rule).is_some(),
            "expected Constructive rule `{rule}` to be defined");
    }
}
