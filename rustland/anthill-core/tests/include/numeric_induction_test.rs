//! Built-in `Int.induction(?P, ?lo, ?hi)` and `BigInt.induction(?P)`
//! rules from the prelude. WI-107.
//!
//! These are the kernel-emitted/hand-authored numeric induction
//! principles required by the lf1 reachability lift. Since neither
//! Int nor BigInt is a sort with constructors, the rules can't
//! come from emit_induction_rule (proposal 025); they're authored
//! as plain anthill in stdlib/anthill/prelude/{int,bigint}.anthill.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::{Term, TermId};
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

fn load_stdlib() -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p).unwrap();
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

fn rule_body_for(kb: &KnowledgeBase, qn: &str) -> Vec<TermId> {
    let sym = kb.try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not in KB"));
    let rid = kb.by_functor(sym).first().copied()
        .unwrap_or_else(|| panic!("no rule for {qn}"));
    kb.rule_body(rid).to_vec()
}

#[test]
fn int_induction_loads_with_base_and_step() {
    let kb = load_stdlib();
    let body = rule_body_for(&kb, "anthill.prelude.Int.induction");
    assert_eq!(body.len(), 2,
        "Int.induction should have 2 body goals (base + step), got {}", body.len());

    // The step goal must be forall_impl carrying the IH.
    let printer = TermPrinter::new(&kb);
    let step = body.iter().copied().find(|&g| {
        matches!(kb.get_term(g),
            Term::Fn { functor, .. } if kb.resolve_sym(*functor) == "forall_impl")
    }).unwrap_or_else(|| {
        let dump: Vec<_> = body.iter().map(|&t| printer.print_term(t)).collect();
        panic!("no forall_impl in Int.induction body: {dump:?}")
    });

    let printed = printer.print_term(step);
    assert!(printed.contains("(forall("), "missing forall: {printed}");
    assert!(printed.contains(" -: "), "missing -: : {printed}");
    assert!(printed.contains("ho_apply"), "step must apply ?P: {printed}");
    assert!(printed.contains("add"), "step must reach n+1 via add: {printed}");
}

#[test]
fn bigint_induction_loads_with_base_and_step() {
    let kb = load_stdlib();
    let body = rule_body_for(&kb, "anthill.prelude.BigInt.induction");
    assert_eq!(body.len(), 2,
        "BigInt.induction should have 2 body goals, got {}", body.len());

    let printer = TermPrinter::new(&kb);
    let step = body.iter().copied().find(|&g| {
        matches!(kb.get_term(g),
            Term::Fn { functor, .. } if kb.resolve_sym(*functor) == "forall_impl")
    }).unwrap_or_else(|| {
        let dump: Vec<_> = body.iter().map(|&t| printer.print_term(t)).collect();
        panic!("no forall_impl in BigInt.induction body: {dump:?}")
    });

    let printed = printer.print_term(step);
    assert!(printed.contains("(forall("), "missing forall: {printed}");
    assert!(printed.contains(" -: "), "missing -: : {printed}");
    // Strong induction: predecessor (sub n 1) appears in the antecedent IH.
    assert!(printed.contains("sub"), "strong-induction step must reference sub: {printed}");
}
