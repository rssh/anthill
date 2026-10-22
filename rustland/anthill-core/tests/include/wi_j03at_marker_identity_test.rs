//! WI-20260827-J03AT — the resolver's markers are kernel SYMBOLS, not names.
//!
//! `forall_impl` / `forall_in` / `some_in` (the converter's discharge and bounded
//! quantifiers), `__pop_assumption` (the resolver's scope discharge) and
//! `__within_requirements` (the marker a citation's root goal rides in) were recognised by
//! their SHORT NAME. So a user predicate of one of those names was read as the marker —
//! its data arguments as goals, its wrong-arity call never refused — and, worse, the
//! parser's own mint resolved through scope like a written name, so in a namespace that
//! declared a `forall_impl` the discharge itself was the user's symbol, read as a
//! discharge only because its short name matched. The markers are minted at kernel
//! addresses now (`..anthill.kernel.forall_impl`, …), which no identifier can spell, and
//! every reader keys on the builtin tag bootstrap registers on them.
//!
//! BACK-OUT (this file run against the parent commit, which has the short-name readers
//! and the short mints): every row here fails except
//! `a_renamed_head_is_refused_at_its_arity`, the control of the separating pair, and
//! `a_genuine_discharge_in_a_query_declares_its_hypothesis`, which holds either way by
//! design — the two say the change is about the KEYING, not the arity check or the
//! discharge's own walk.
//!
//! Five readers have no row of their own, and cannot: `step_init`'s `is_forall_impl` /
//! `bounded_quant_kind` / `pop_assumption_arg` run only behind `is_scoping_marker`, and the
//! query walk's discharge skip and the typer's `GoalCommit` discharge test act on a node's
//! goal slots, which `goal_slot_readings` gives no symbol but the markers. They are keyed
//! on the tag so no reader of a marker reads a name.

use std::rc::Rc;

use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{load_errors_of, load_kb_with, pattern_hits, query_pattern_term};

fn rule_body(kb: &KnowledgeBase, qn: &str) -> Vec<Rc<NodeOccurrence>> {
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not found"));
    let rid = kb
        .rules_by_functor(sym)
        .first()
        .copied()
        .unwrap_or_else(|| panic!("no rule for {qn}"));
    kb.rule_body_nodes(rid).to_vec()
}

fn functor_qn(kb: &KnowledgeBase, goal: &NodeOccurrence) -> String {
    match goal.as_expr() {
        Some(Expr::Apply { functor, .. } | Expr::Constructor { name: functor, .. }) => {
            kb.qualified_name_of(*functor).to_string()
        }
        other => panic!("expected an application, got {other:?}"),
    }
}

/// The ticket's separating pair, per marker name: a user predicate named like a marker,
/// called at another arity, is refused exactly as the same program with the head renamed.
/// Before, the marker-named program loaded clean and answered a bogus solution.
#[test]
fn a_user_predicate_named_like_a_marker_is_refused_at_its_arity() {
    for name in ["forall_impl", "forall_in", "some_in"] {
        let ns = format!("test.j03at.arity_{name}");
        let src = format!(
            "namespace {ns}\n  fact p9(1)\n  fact q9(2)\n  rule {name}(?x) :- p9(?x)\n\
             \x20 rule r9(?x) :- {name}(p9(?x), q9(?x), p9(?x))\nend\n"
        );
        let errors = load_errors_of(&src);
        let expected = format!(
            "expected a term a clause of `{ns}.{name}` can match (1 positional), got 3 positional"
        );
        assert!(
            errors.iter().any(|e| e.contains(&expected)),
            "`{name}` must be the user's own predicate, refused at its arity: {errors:?}"
        );
    }
}

/// The CONTROL of the pair: passes with or without the change.
#[test]
fn a_renamed_head_is_refused_at_its_arity() {
    let errors = load_errors_of(
        "namespace test.j03at.ctl\n  fact p9(1)\n  fact q9(2)\n  rule zzz(?x) :- p9(?x)\n\
         \x20 rule r9(?x) :- zzz(p9(?x), q9(?x), p9(?x))\nend\n",
    );
    assert!(
        errors.iter().any(|e| e.contains(
            "expected a term a clause of `test.j03at.ctl.zzz` can match (1 positional), got 3 positional"
        )),
        "{errors:?}"
    );
}

/// A namespace declaring its own `forall_impl` keeps BOTH: its discharge is the kernel
/// marker, and its predicate answers as itself. Before, the discharge's functor was the
/// user's `forall_impl`, and a query of the user's predicate was a vacuous discharge —
/// `forall_impl(2, 5, 6)` answered although no clause matches it.
#[test]
fn a_namespace_declaring_forall_impl_keeps_its_discharge_and_its_predicate() {
    for decl in [
        "rule forall_impl(?a, ?b, ?c) :- p9(?a)",
        "fact forall_impl(1, 5, 6)",
    ] {
        let src = format!(
            "namespace test.j03at.own\n  fact p9(1)\n  fact q9(2)\n  {decl}\n\
             \x20 rule base(?x) :- p9(?x)\n\
             \x20 rule disc(?y) :- q9(?y), (forall(?z), base(?z) -: base(?z))\n\
             \x20 rule undischarged(?y) :- q9(?y), (forall(?z), base(?z) -: q9(?z))\nend\n"
        );
        let mut kb = load_kb_with(&src);
        let body = rule_body(&kb, "test.j03at.own.disc");
        assert_eq!(
            functor_qn(&kb, &body[1]),
            "anthill.kernel.forall_impl",
            "{decl}: the discharge must be the kernel marker, not the user's name"
        );
        assert_eq!(pattern_hits(&mut kb, "test.j03at.own.disc(2)"), 1, "{decl}");
        assert_eq!(pattern_hits(&mut kb, "test.j03at.own.undischarged(2)"), 0, "{decl}");
        assert_eq!(pattern_hits(&mut kb, "test.j03at.own.forall_impl(1, 5, 6)"), 1, "{decl}");
        assert_eq!(
            pattern_hits(&mut kb, "test.j03at.own.forall_impl(2, 5, 6)"),
            0,
            "{decl}: the user's predicate answers by its clauses, not as a discharge"
        );
    }
}

/// The bounded quantifiers' half of the row above.
#[test]
fn a_namespace_declaring_forall_in_and_some_in_keeps_its_quantifiers_and_its_facts() {
    let src = "namespace test.j03at.quant\n  fact p9(1)\n  fact q9(2)\n\
               \x20 fact forall_in(1, 2, 3)\n  fact some_in(1, 2, 3)\n\
               \x20 rule every(?y) :- q9(?y), (forall ?e in [1, 1]: p9(?e))\n\
               \x20 rule any(?y) :- q9(?y), (some ?e in [2, 1]: p9(?e))\n\
               \x20 rule none(?y) :- q9(?y), (forall ?e in [2, 1]: p9(?e))\nend\n";
    let mut kb = load_kb_with(src);
    for (rule, marker) in [
        ("test.j03at.quant.every", "anthill.kernel.forall_in"),
        ("test.j03at.quant.any", "anthill.kernel.some_in"),
    ] {
        let body = rule_body(&kb, rule);
        assert_eq!(functor_qn(&kb, &body[1]), marker, "{rule}");
    }
    assert_eq!(pattern_hits(&mut kb, "test.j03at.quant.every(2)"), 1);
    assert_eq!(pattern_hits(&mut kb, "test.j03at.quant.any(2)"), 1);
    assert_eq!(pattern_hits(&mut kb, "test.j03at.quant.none(2)"), 0);
    for name in ["forall_in", "some_in"] {
        assert_eq!(pattern_hits(&mut kb, &format!("test.j03at.quant.{name}(1, 2, 3)")), 1);
        assert_eq!(
            pattern_hits(&mut kb, &format!("test.j03at.quant.{name}(9, [1], 9)")),
            0,
            "`{name}` is the user's fact, not a quantifier over `[1]`"
        );
    }
}

/// A user's `forall_impl` called at ITS arity from a rule body is a call on the user's
/// fact. Before, its constant arguments were read as goals and the load was refused
/// ("constant `9` in a rule-body GOAL position").
#[test]
fn a_user_forall_impl_call_reads_the_users_clauses() {
    let mut kb = load_kb_with(
        "namespace test.j03at.call\n  fact forall_impl(7, 8, 9)\n\
         \x20 rule r9(?x) :- forall_impl(?x, 8, 9)\nend\n",
    );
    assert_eq!(pattern_hits(&mut kb, "test.j03at.call.r9(7)"), 1);
    assert_eq!(pattern_hits(&mut kb, "test.j03at.call.r9(8)"), 0);
}

/// A bare `forall_impl(…)` nobody declared names nothing: no written spelling means the
/// marker. Before, it was the marker — the bare intern the converter also minted.
#[test]
fn a_bare_marker_name_in_a_rule_body_names_nothing() {
    let errors = load_errors_of(
        "namespace test.j03at.bare\n  fact p9(1)\n\
         \x20 rule w(?x) :- p9(?x), forall_impl(tuple(?z), tuple(p9(?z)), tuple(p9(?z)))\nend\n",
    );
    assert!(
        errors.iter().any(|e| e.contains("rule-body goal `forall_impl` names nothing")),
        "{errors:?}"
    );
}

/// The query walk (`undefined_query_goal_functors`): a bare `forall_impl(…)` in a pattern
/// is an undefined functor, not a discharge whose interior the walk skips. Before, the
/// marker exemption and the discharge skip both answered for the short name.
#[test]
fn a_bare_marker_name_in_a_query_is_an_undefined_functor() {
    let mut kb = load_kb_with("namespace test.j03at.q\n  fact seed(1)\nend\n");
    let qt = query_pattern_term(
        &mut kb,
        "not(forall_impl(tuple(?h), tuple(hyp(?h)), tuple(hyp(?h))))",
    );
    let undefined: Vec<String> = kb
        .undefined_query_goal_functors(&qt)
        .iter()
        .map(|s| kb.qualified_name_of(*s).to_string())
        .collect();
    assert!(undefined.iter().any(|n| n == "forall_impl"), "{undefined:?}");
}

/// The discharge's own skip, unchanged: its antecedent declares `hyp`, so the query walk
/// does not refuse it. Passes either way by design.
#[test]
fn a_genuine_discharge_in_a_query_declares_its_hypothesis() {
    let mut kb = load_kb_with("namespace test.j03at.q2\n  fact seed(1)\nend\n");
    let qt = query_pattern_term(&mut kb, "not((forall(?h), hyp(?h) -: hyp(?h)))");
    assert!(kb.undefined_query_goal_functors(&qt).is_empty());
}

/// The printer asks the QUALIFIED name: a user's `forall_impl(tuple(…), …)` prints as the
/// call it is, a discharge as its surface form. Before, the first printed as a discharge.
#[test]
fn the_printer_renders_only_the_kernel_marker_as_a_discharge() {
    let mut kb = load_kb_with("namespace test.j03at.print\n  fact seed(1)\nend\n");
    let written = query_pattern_term(&mut kb, "forall_impl(tuple(?h), tuple(1), tuple(2))");
    let printed = TermPrinter::new(&kb).print_occurrence(&written);
    assert!(printed.starts_with("forall_impl("), "{printed}");
    let discharge = query_pattern_term(&mut kb, "(forall(?h), seed(?h) -: seed(?h))");
    let printed = TermPrinter::new(&kb).print_occurrence(&discharge);
    assert!(printed.starts_with("(forall("), "{printed}");
    for (pattern, surface) in [
        ("(forall ?x in [1]: seed(?x))", "(forall "),
        ("(some ?x in [1]: seed(?x))", "(some "),
    ] {
        let q = query_pattern_term(&mut kb, pattern);
        let printed = TermPrinter::new(&kb).print_occurrence(&q);
        assert!(printed.starts_with(surface), "{pattern}: {printed}");
    }
}

/// `__pop_assumption`, the resolver's own marker: a user predicate of that name called
/// inside a discharge's consequent is the user's call. Before, it was read as the marker
/// and popped the assumption the next goal needed, so `kept` answered nothing.
#[test]
fn a_user_pop_assumption_is_not_the_resolvers_marker() {
    let mut kb = load_kb_with(
        "namespace test.j03at.pop\n  fact p9(1)\n  rule __pop_assumption(?n) :- p9(?n)\n\
         \x20 rule kept(?y) :- p9(?y), (forall(?z), p9(?z) -: __pop_assumption(1), p9(?z))\nend\n",
    );
    assert_eq!(pattern_hits(&mut kb, "test.j03at.pop.kept(1)"), 1);
}

/// The printer's PARSE view: a parsed file reports the minted name verbatim, so the
/// marked address is what `is_control` matches there, and a written `forall_impl(…)` is
/// still printed as the call it is.
#[test]
fn the_parse_view_printer_renders_the_minted_markers_as_surface_forms() {
    use anthill_core::parse::{self, ir::Item};
    let parsed = parse::parse(
        "rule r(?y) :- (forall(?z), p(?z) -: p(?z)), (forall ?e in [1]: p(?e)), \
         (some ?e in [1]: p(?e)), forall_impl(tuple(?z), tuple(1), tuple(2))",
    )
    .expect("parse");
    let body = parsed
        .items
        .iter()
        .find_map(|i| match i {
            Item::Rule(r) => r.body.clone(),
            _ => None,
        })
        .expect("a rule body");
    let printer = TermPrinter::over(&parsed);
    let printed: Vec<String> = body.iter().map(|g| printer.print_term(*g)).collect();
    for (goal, surface) in printed.iter().zip(["(forall(", "(forall ", "(some ", "forall_impl("]) {
        assert!(goal.starts_with(surface), "{surface}: {printed:?}");
    }
}

/// A marker symbol in a shape the resolver does not mint — reachable only by naming the
/// kernel address — is an ERROR when it runs, not a silent miss: `execute_builtin`
/// refuses it, and the search reports the fault.
#[test]
fn a_kernel_marker_in_another_shape_is_an_error_when_it_runs() {
    let src = "namespace test.j03at.shape\n  fact seed(1)\nend\n";
    for pattern in [
        "anthill.kernel.forall_impl(1)",
        "anthill.kernel.some_in(1, 2)",
        "anthill.kernel.__pop_assumption(x)",
        "anthill.kernel.__within_requirements(1)",
    ] {
        let (_, messages) = crate::common::resolve_with_messages(src, pattern);
        assert!(
            messages.iter().any(|m| m.contains("is a resolver marker")),
            "{pattern}: {messages:?}"
        );
    }
}

/// `__within_requirements`, the citation marker: a user predicate of that name answers by
/// its own clauses. Before, its first argument was unwrapped and resolved as the cited goal,
/// so `__within_requirements(1, 1)` answered nothing although its clause holds.
#[test]
fn a_user_within_requirements_is_not_the_citation_marker() {
    let mut kb = load_kb_with(
        "namespace test.j03at.within\n  fact p9(1)\n\
         \x20 rule __within_requirements(?g, ?r) :- p9(?g), p9(?r)\n\
         \x20 rule r(?x) :- p9(?x), __within_requirements(?x, 1)\nend\n",
    );
    assert_eq!(pattern_hits(&mut kb, "test.j03at.within.__within_requirements(1, 1)"), 1);
    assert_eq!(pattern_hits(&mut kb, "test.j03at.within.r(1)"), 1);
}
