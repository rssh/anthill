//! WI-20260821-6WVJB — ONE NAME, ONE ARITY. The clauses of a predicate, and the clauses
//! written under an operation, all have one arity — positional and named arguments
//! counted together — and a declaration states it. Arity is not part of a name: a bare
//! name is a value with no arity to choose by. Refused as
//! `LoadError::ClausesOfDifferentArity`, naming every arity and where it is written.
//!
//! And a predicate's named arguments are matched in any key order: a goal written
//! `r(b: ?y, a: ?x)` answers `fact r(a: 3, b: 4)`, and the two spellings of one fact are
//! one row.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ─────────────────────────────
//!
//! Removing `check_one_arity_per_name` from the load pipeline fails every `*_is_refused`
//! row but `a_row_asserted_at_run_time_of_another_arity_is_refused`, which fails when
//! `check_fact_mutation_target` stops asking `established_arity`. Clearing
//! `predicate_declarations` at each load's start, as `op_decl_sites` is, fails
//! `a_clause_against_an_earlier_loads_declaration_is_refused`, and the unit row
//! `a_later_load_does_not_report_an_earlier_loads_declarations` (in `kb/load.rs`), which
//! also fails when every declared predicate is asked at every load. Walking named keys in
//! stored order again (`discrim::walk_named_keys` returning `named_keys` as held) fails
//! `a_rule_body_goal_matches_in_any_key_order`, `a_query_matches_in_any_key_order` and
//! `a_head_written_in_another_order_answers`.
//! Storing a fact head as written again (`predicate_head_in_key_order` returning its
//! argument) fails `one_fact_in_two_key_orders_is_one_row`. The controls pass either way
//! BY DESIGN: they are what the refusals and the matches must disagree with —
//! `clauses_of_one_arity_are_one_predicate`, `a_positional_and_a_named_head_of_one_count_load`,
//! `one_name_in_two_scopes_is_two_predicates`, `the_functional_relation_view_stays_legal`,
//! `an_entity_fact_with_an_omitted_field_loads`, `constraint_rows_are_outside_the_rule`
//! and `a_named_tuple_keeps_its_order`.

use crate::common::{
    definite_unary, load_kb_with, resolve_with_messages, unrendered_load_errors_of,
};
use anthill_core::eval::Value;
use anthill_core::kb::load::{ArityGroup, LoadError};
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::term_view::{TermView, ViewHead};
use smallvec::SmallVec;

/// The one error `src` loads with, which must be this refusal: its name and its arity
/// groups. Every other error fails the row, so a fixture refused for another reason
/// cannot pass on this one's account.
fn refusal(src: &str) -> (String, &'static str, Vec<ArityGroup>) {
    let errors = unrendered_load_errors_of(src);
    match errors.as_slice() {
        [LoadError::ClausesOfDifferentArity {
            name,
            kind,
            arities,
        }] => (name.clone(), *kind, arities.clone()),
        other => panic!("expected exactly the one-arity refusal, got {other:#?}"),
    }
}

/// `(arity, declared?, clauses)` of each group, in the order the refusal tells them.
fn shape(arities: &[ArityGroup]) -> Vec<(usize, bool, usize)> {
    arities
        .iter()
        .map(|g| (g.arity, g.declared_at.is_some(), g.clauses))
        .collect()
}

fn answers(src: &str, pattern: &str) -> usize {
    let (sols, faults) = resolve_with_messages(src, pattern);
    assert!(faults.is_empty(), "{pattern}: the search faulted: {faults:?}");
    sols.len()
}

// ── refusals ────────────────────────────────────────────────────────────

#[test]
fn two_arities_of_one_predicate_is_refused() {
    let src = "namespace ar1\n  fact p(1)\n  fact p(1, 2)\n  fact p(7)\nend\n";
    let (name, kind, arities) = refusal(src);
    assert_eq!((name.as_str(), kind), ("ar1.p", "predicate"));
    assert_eq!(shape(&arities), vec![(1, false, 2), (2, false, 1)]);
    // Each arity is told by its first clause, so the message names both lines (an inline
    // source has no path, so a site is its `line:col`).
    let at: Vec<&str> = arities
        .iter()
        .map(|g| g.first_clause_at.as_deref().expect("a clause at each arity"))
        .collect();
    assert_eq!(at, vec!["2:8", "3:8"]);
}

#[test]
fn named_arguments_count_toward_the_arity_is_refused() {
    let src = "namespace ar2\n  fact q(a: 1)\n  fact q(a: 1, b: 2)\nend\n";
    let (name, _, arities) = refusal(src);
    assert_eq!(name, "ar2.q");
    assert_eq!(shape(&arities), vec![(1, false, 1), (2, false, 1)]);
}

#[test]
fn a_bare_head_is_arity_zero_is_refused() {
    let src = "namespace ar3\n  fact z\n  fact z(1)\nend\n";
    let (_, _, arities) = refusal(src);
    assert_eq!(shape(&arities), vec![(0, false, 1), (1, false, 1)]);
}

#[test]
fn a_rule_beside_a_fact_of_another_arity_is_refused() {
    let src = "namespace ar4\n  fact p(1)\n  rule p(?x, ?y) :- p(?x), p(?y)\nend\n";
    let (_, _, arities) = refusal(src);
    assert_eq!(shape(&arities), vec![(1, false, 1), (2, false, 1)]);
}

/// A declaration states the arity: a clause of another one is refused even though it is
/// the predicate's only clause.
#[test]
fn a_clause_against_its_declaration_is_refused() {
    let src = "namespace ar5\n  rule t(?x, ?y)\n  fact t(1)\nend\n";
    let (_, _, arities) = refusal(src);
    assert_eq!(shape(&arities), vec![(2, true, 0), (1, false, 1)]);
}

#[test]
fn two_declarations_of_different_arity_is_refused() {
    let src = "namespace ar6\n  rule t(?x)\n  rule t(?x, ?y)\nend\n";
    let (_, _, arities) = refusal(src);
    assert_eq!(shape(&arities), vec![(1, true, 0), (2, true, 0)]);
}

/// A head that resolves through an import is a clause of the imported predicate, so it is
/// held to that predicate's declaration and clauses. Before this ticket `a.p` answered at
/// both arities.
#[test]
fn an_imported_predicates_clause_of_another_arity_is_refused() {
    let src = r#"
namespace ar7a
  rule p(?x)
  fact p(1)
end
namespace ar7b
  import ar7a.p
  fact p(1, 2)
end
"#;
    let (name, _, arities) = refusal(src);
    assert_eq!(name, "ar7a.p");
    assert_eq!(shape(&arities), vec![(1, true, 1), (2, false, 1)]);
}

/// Clauses written under an operation are held to it as well. `f` is body-less, so no
/// other check reaches a clause under it; before this ticket `S.f(?x, ?y, ?z)` answered.
#[test]
fn clauses_under_an_operation_at_two_arities_is_refused() {
    let src = r#"
namespace ar8
  import anthill.prelude.{Int64}
  sort S
    entity s(n: Int64)
    operation f(x: Int64) -> Int64
  end
  fact S.f(1, 2, 3)
  fact S.f(5)
end
"#;
    let (name, kind, arities) = refusal(src);
    assert_eq!((name.as_str(), kind), ("ar8.S.f", "operation"));
    assert_eq!(shape(&arities), vec![(3, false, 1), (1, false, 1)]);
}

/// A later load is held to an earlier load's clauses: `anthill.reflect.feed.reaches` has
/// its two-argument clauses in the stdlib. WHICH RECIPE MEASURES WHAT: the shared base and
/// two steps load the stdlib first and seal it, so they measure the LATER load this row is
/// named for; the fresh recipe is one call over both, and measures that the refusal is
/// the same within one load — which needs the plain `import …reaches` to resolve in the
/// load that introduces it (WI-20261022-JBHQC; before it, `UnresolvedImport` there). The
/// groups are told in load order, the stdlib's first under all three: the fresh recipe
/// hands the stdlib's files to the one call before the program's.
#[test]
fn a_clause_against_an_earlier_loads_clauses_is_refused() {
    let src = r#"
namespace ar9
  import anthill.reflect.feed.reaches
  fact reaches(1)
end
"#;
    let (name, _, arities) = refusal(src);
    assert_eq!(name, "anthill.reflect.feed.reaches");
    assert_eq!(arities.len(), 2);
    assert_eq!((arities[0].arity, arities[1].arity), (2, 1));
    assert_eq!(arities[1].clauses, 1);
}

/// A later load is held to an earlier load's DECLARATION, which keeps its arity across
/// loads though it stores no clause: `Constructive.identity` is declared in the stdlib at
/// one argument and has no clause. The one-argument clause is the control.
#[test]
fn a_clause_against_an_earlier_loads_declaration_is_refused() {
    let program = |fact: &str| {
        format!(
            "namespace ar10\n  import anthill.logic.Constructive.Constructive.identity\n  \
             {fact}\nend\n"
        )
    };
    let (name, _, arities) = refusal(&program("fact identity(1, 2)"));
    assert_eq!(name, "anthill.logic.Constructive.Constructive.identity");
    assert_eq!(shape(&arities), vec![(1, true, 0), (2, false, 1)]);
    let kb = load_kb_with(&program("fact identity(1)"));
    assert_eq!(
        kb.rule_ids_by_qn("anthill.logic.Constructive.Constructive.identity").len(),
        1
    );
}

/// A row written at run time is held to the arity the load established: `KB.assert`, a
/// store's persist and its update all pass `check_fact_mutation_target`. The row at the
/// established arity is the control, and it is stored.
#[test]
fn a_row_asserted_at_run_time_of_another_arity_is_refused() {
    let mut kb = load_kb_with("namespace rt6\n  fact p(1)\nend\n");
    let p = kb.resolve_symbol("rt6.p");
    let domain = Some(kb.resolve_symbol("rt6"));
    let row = |kb: &mut anthill_core::kb::KnowledgeBase, ints: &[i64]| {
        let args: Vec<_> = ints
            .iter()
            .map(|&i| kb.alloc(Term::Const(Literal::Int(i))))
            .collect();
        Value::term(kb.alloc(Term::Fn {
            functor: p,
            pos_args: SmallVec::from_slice(&args),
            named_args: SmallVec::new(),
        }))
    };
    let two = row(&mut kb, &[1, 2]);
    match kb.assert_checked_persistent(two, domain) {
        Err(e) => assert!(e.to_string().contains("second arity"), "{e}"),
        Ok(_) => panic!("a two-argument row under the one-argument `p` must be refused"),
    }
    let one = row(&mut kb, &[5]);
    kb.assert_checked_persistent(one, domain)
        .expect("a row at the established arity is written");
    assert_eq!(kb.rule_ids_by_qn("rt6.p").len(), 2);
}

// ── controls: what the refusals must disagree with ──────────────────────

#[test]
fn clauses_of_one_arity_are_one_predicate() {
    let src = r#"
namespace c1
  fact p(1)
  fact p(7)
  fact q(9)
  rule p(?x) :- q(?x)
end
"#;
    assert_eq!(answers(src, "c1.p(?x)"), 3);
}

/// One count, two spellings: arity counts positional and named arguments together, so
/// these load. They are not one relation's rows — each goal answers its own.
#[test]
fn a_positional_and_a_named_head_of_one_count_load() {
    let src = "namespace c2\n  fact r(1, 2)\n  fact r(a: 3, b: 4)\nend\n";
    assert_eq!(answers(src, "c2.r(?x, ?y)"), 1);
    assert_eq!(answers(src, "c2.r(a: ?x, b: ?y)"), 1);
}

#[test]
fn one_name_in_two_scopes_is_two_predicates() {
    let src = "namespace c3a\n  fact p(1)\nend\nnamespace c3b\n  fact p(1, 2)\nend\n";
    assert_eq!(answers(src, "c3a.p(?x)"), 1);
    assert_eq!(answers(src, "c3b.p(?x, ?y)"), 1);
}

/// An operation of arity 1 read as a relation at arity 2 is a reading of the goal, no
/// stored clause, so it is not a second arity of `inc`.
#[test]
fn the_functional_relation_view_stays_legal() {
    let src = r#"
namespace c4
  import anthill.prelude.{Int64}
  operation inc(x: Int64) -> Int64 = x + 1
  fact mark(1)
  rule r(?v) :- mark(?m), inc(41, ?v)
end
"#;
    let mut kb = load_kb_with(src);
    assert!(matches!(definite_unary(&mut kb, "c4.r").as_slice(), [Value::Int(42)]));
}

/// An entity's fact head takes the constructor's arity, the omitted field filled.
#[test]
fn an_entity_fact_with_an_omitted_field_loads() {
    let src = r#"
namespace c5
  import anthill.prelude.{Int64}
  sort E
    entity e(a: Int64, b: Int64)
  end
  fact e(a: 1)
  fact e(a: 1, b: 2)
end
"#;
    assert_eq!(answers(src, "c5.E.e(a: ?x, b: ?y)"), 2);
}

/// The kernel's `Constraint` rows take a shape per constraint form — `head` and `guard`
/// for a guarded denial, `guard` alone for a quantified one — and the rule leaves them
/// alone: this program holds both arities and loads. The quantified one still guards:
/// `tag(5)` breaks it.
#[test]
fn constraint_rows_are_outside_the_rule() {
    let program = |extra: &str| {
        format!(
            r#"
namespace c6
  import anthill.prelude.{{PartialOrd}}
  fact tag(1)
  {extra}
  constraint no_big: no ?x: tag(?x) -: PartialOrd.gt(?x, 1)
  constraint stated: tag(?n) :- PartialOrd.gt(?n, 100)
end
"#
        )
    };
    let kb = load_kb_with(&program(""));
    let rows = kb.rule_ids_by_qn("Constraint");
    let mut arities: Vec<usize> = rows
        .iter()
        .map(|&rid| match kb.rule_head_value(rid).head(&kb) {
            ViewHead::Functor {
                pos_arity,
                named_arity,
                ..
            } => pos_arity + named_arity,
            other => panic!("a Constraint row is an application: {other:?}"),
        })
        .collect();
    arities.sort_unstable();
    arities.dedup();
    assert_eq!(arities, vec![1, 2], "both shapes are stored, and the load is clean");
    let violated = unrendered_load_errors_of(&program("fact tag(5)"));
    assert!(
        matches!(violated.as_slice(), [LoadError::ConstraintViolated { .. }]),
        "{violated:#?}"
    );
}

// ── key order ───────────────────────────────────────────────────────────

#[test]
fn a_rule_body_goal_matches_in_any_key_order() {
    let src = r#"
namespace k1
  fact r(a: 3, b: 4)
  rule s(?x, ?y) :- r(a: ?x, b: ?y)
  rule t(?x, ?y) :- r(b: ?y, a: ?x)
end
"#;
    assert_eq!(answers(src, "k1.s(?x, ?y)"), 1, "the written order, the control");
    assert_eq!(answers(src, "k1.t(?x, ?y)"), 1);
}

#[test]
fn a_query_matches_in_any_key_order() {
    let src = "namespace k2\n  fact r(a: 3, b: 4)\nend\n";
    assert_eq!(answers(src, "k2.r(b: ?y, a: ?x)"), 1);
}

/// A bodied head, which is stored as written: only the walk order reaches it. (A fact
/// head is also stored in key order, `one_fact_in_two_key_orders_is_one_row`.)
#[test]
fn a_head_written_in_another_order_answers() {
    let src = r#"
namespace k3
  fact q(3, 4)
  rule r(b: ?y, a: ?x) :- q(?x, ?y)
  rule s(?x, ?y) :- r(a: ?x, b: ?y)
end
"#;
    assert_eq!(answers(src, "k3.s(?x, ?y)"), 1);
}

#[test]
fn one_fact_in_two_key_orders_is_one_row() {
    let src = "namespace k4\n  fact r(a: 3, b: 4)\n  fact r(b: 4, a: 3)\nend\n";
    let kb = load_kb_with(src);
    assert_eq!(kb.rule_ids_by_qn("k4.r").len(), 1);
}

/// A named tuple's component order is its identity: `(y: 2, x: 1)` is another value.
#[test]
fn a_named_tuple_keeps_its_order() {
    let src = r#"
namespace k5
  fact at(pos: (x: 1, y: 2))
  rule same :- at(pos: (x: 1, y: 2))
  rule swapped :- at(pos: (y: 2, x: 1))
end
"#;
    assert_eq!(answers(src, "k5.same"), 1);
    assert_eq!(answers(src, "k5.swapped"), 0);
}
