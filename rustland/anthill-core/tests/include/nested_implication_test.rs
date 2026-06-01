//! Body-level nested implication `(forall(?h, ?rest), Q -: P)` (WI-105).
//!
//! Acceptance: hand-written rule with `(forall(?x), Q(?x) -: P(?x))`
//! parses, loads, and round-trips. Used by auto-generated induction
//! principles for the inductive-step case (WI-106 follow-up).


use std::rc::Rc;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p).unwrap();
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

fn rule_body_for(kb: &KnowledgeBase, qn: &str) -> Vec<Rc<NodeOccurrence>> {
    let sym = kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("symbol {qn} not found"));
    let rid = kb.rules_by_functor(sym).first().copied()
        .unwrap_or_else(|| panic!("no rule for {qn}"));
    kb.rule_body_nodes(rid).to_vec()
}

#[test]
fn nested_impl_in_rule_body_parses_and_loads() {
    let src = r#"
        namespace test.nested.parse
          export Step
          sort Step
            entity step_root
          end

          rule step_witness(?P)
            :- ho_apply(?P, step_root),
               (forall(?h, ?rest), ho_apply(?P, ?rest) -: ho_apply(?P, ?h))
        end
    "#;
    let kb = load_with(src);
    let body = rule_body_for(&kb, "test.nested.parse.step_witness");
    assert_eq!(body.len(), 2, "expected 2 body goals");

    // Second goal should be a forall_impl occurrence
    let goal = &body[1];
    match goal.as_expr() {
        Some(Expr::Apply { functor, pos_args, named_args, .. }) => {
            assert_eq!(kb.resolve_sym(*functor), "forall_impl",
                "second goal should be forall_impl");
            assert_eq!(pos_args.len(), 3, "forall_impl takes (binders, ants, cons)");
            assert!(named_args.is_empty());
        }
        other => panic!("expected forall_impl Apply, got {other:?}"),
    }
}

#[test]
fn nested_impl_round_trips_through_printer() {
    let src = r#"
        namespace test.nested.print
          export S
          sort S
            entity s_root
          end

          rule s_r(?P)
            :- (forall(?x), ho_apply(?P, ?x) -: ho_apply(?P, s_root))
        end
    "#;
    let kb = load_with(src);
    let body = rule_body_for(&kb, "test.nested.print.s_r");
    let printer = TermPrinter::new(&kb);
    let printed = printer.print_occurrence(&body[0]);
    assert!(printed.contains("(forall("), "missing forall opener: {printed}");
    assert!(printed.contains(" -: "), "missing -: separator: {printed}");
    assert!(printed.contains("ho_apply"), "missing ho_apply: {printed}");
}

#[test]
fn nested_impl_multi_binder_multi_antecedent() {
    let src = r#"
        namespace test.nested.multi
          export M
          sort M
            entity m_root
          end

          rule m_complex(?P)
            :- (forall(?a, ?b, ?c),
                ho_apply(?P, ?a), ho_apply(?P, ?b)
                -: ho_apply(?P, ?c))
        end
    "#;
    let kb = load_with(src);
    let body = rule_body_for(&kb, "test.nested.multi.m_complex");
    let goal = &body[0];

    let pos: Vec<Rc<NodeOccurrence>> = match goal.as_expr() {
        Some(Expr::Apply { pos_args, .. }) => pos_args.clone(),
        other => panic!("expected forall_impl Apply, got {other:?}"),
    };

    // binders tuple should have 3 elements
    let binders = match pos[0].as_expr() {
        Some(Expr::Apply { pos_args, .. }) => pos_args.len(),
        _ => 0,
    };
    assert_eq!(binders, 3, "expected 3 binders");

    // antecedents tuple should have 2 elements
    let ants = match pos[1].as_expr() {
        Some(Expr::Apply { pos_args, .. }) => pos_args.len(),
        _ => 0,
    };
    assert_eq!(ants, 2, "expected 2 antecedents");

    // consequent tuple should have 1 element
    let cons = match pos[2].as_expr() {
        Some(Expr::Apply { pos_args, .. }) => pos_args.len(),
        _ => 0,
    };
    assert_eq!(cons, 1, "expected 1 consequent");
}
