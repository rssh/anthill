//! WI-20261011-BVG8M — WHAT A PROOF IS OWED FOR A `requires` OF ITS SCOPE: THE CLAUSE,
//! AND THE LAWS OF THE SPEC IT REQUIRES.
//!
//! The record of a `requires <SE>` clause (proposal 030, α.6) states the conjunction of
//! `SE`'s laws at the clause's bindings, and a proof in the clause's scope is owed them
//! as hypotheses. `anthill prove` handed a proof the RECORDS and lowered each as a cited
//! rule is lowered — by lifting the rule of that name — and a record is no rule, so a
//! `by z3` proof in a scope that has a `requires` was refused for standing there. Two
//! readers make the lowering a read of the KB:
//!
//! * `load::requires_clauses_of` — the `requires` clauses of the scopes named, read off
//!   the declarations, each with the SORT its spec is of. A requirement's record is a
//!   scope axiom — it holds because the declaration has the clause — so the clause is
//!   what is read; the last row holds the records and the clauses to each other.
//! * `KnowledgeBase::spec_laws` — a law is a clause of a `rule` or a `constraint` item
//!   WRITTEN in the spec's sort, and an equation written `fact`. Not an operation's
//!   default body, which a carrier may replace; not any other fact; not a rule that
//!   declares its predicate and asserts nothing; not a clause the loader derived there.
//!   The spec's own, not those of what it requires in turn. Decided with the user,
//!   2026-10-12.
//!
//! No law is LOWERED yet — that is proposal 030's γ.4, decided and not built — so what
//! `anthill prove` does with these is name the laws a proof is not given
//! (`prove::s8cyd_implicit_cite_tests`, and the CLI's `wi_bvg8m_requirement_cite_test`).
//!
//! WHAT FAILS WHEN A PART IS BACKED OUT is measured, row by row, in
//! `docs/measurements/test-infrastructure/requirement-cites-2026-10-12.txt` §5.

use std::collections::BTreeSet;

use anthill_core::kb::load::{requires_clauses_of, RequiresClause};
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::{ClauseKind, KnowledgeBase};

use crate::common::{load_kb_with, load_stdlib_kb, named_field_term, proof_record_heads};

/// A spec with one clause of each kind a sort's body can hold, and a scope that
/// requires it — and `Eq`, at another of its parameters.
const SRC: &str = r#"
namespace test.bvg8m.laws
  import anthill.prelude.{Int64}
  import anthill.prelude.PartialOrd.{gte, gt}
  import anthill.prelude.PartialEq.{eq}

  sort Measured
    sort T = ?

    operation {
      weight(a: T) -> Int64 = 0
      heavier(a: T, b: T) -> Bool = gt(weight(a), weight(b))
    }

    entity Sample(n: Int64)
    fact Sample(n: 1)

    rule weight_nonneg: gte(weight(?a), 0) <=> true
    rule heavier(?a, ?a) <=> false
    rule weight_bound: gte(?w, 0)
      :- eq(?w, weight(?a))
    rule weight_then: eq(?w, weight(?a)) -: gte(?w, 0)
    rule two_heads: gte(weight(?a), 0), gte(weight(?a), -1) :- eq(?a, ?a)
    fact gte(weight(?a), -5) <=> true
    constraint weight_sane: gte(weight(?a), 0) :- eq(?a, ?a)
    rule declared(?p)
  end

  sort Scope
    sort T = ?
    sort U = ?
    requires Measured[T = T]
    requires anthill.prelude.Eq[T = U]
  end

  sort Bare
    sort T = ?
  end
end
"#;

/// The laws of the sort `spec_qn`, each as `<label or ->  <kind>  <equation or clause>`.
fn laws(kb: &KnowledgeBase, spec_qn: &str) -> Vec<String> {
    let spec = kb
        .try_resolve_symbol(spec_qn)
        .unwrap_or_else(|| panic!("`{spec_qn}` is a sort of the KB"));
    kb.spec_laws(spec)
        .iter()
        .map(|law| {
            let label = law
                .label
                .map_or("-", |label| kb.qualified_name_of(label).rsplit('.').next().unwrap());
            let kind = match law.clause.clause_kind {
                ClauseKind::Rule => "rule",
                ClauseKind::Fact => "fact",
                ClauseKind::Constraint => "constraint",
                other => panic!("a law is no {other:?}"),
            };
            let shape = if law.is_equation { "equation" } else { "clause" };
            format!("{label} {kind} {shape}")
        })
        .collect()
}

/// How many laws the sort has, and the labels of those cited by one.
fn count_and_labels(kb: &KnowledgeBase, spec_qn: &str) -> (usize, Vec<String>) {
    let laws = laws(kb, spec_qn);
    let labels = laws
        .iter()
        .filter_map(|law| law.split(' ').next().filter(|label| *label != "-"))
        .map(str::to_owned)
        .collect();
    (laws.len(), labels)
}

/// Eight clauses of `Measured` are laws: the labelled equation; the equation with no
/// label; the rule written `head :- body` and the rule written `body -: head` — one
/// stored form, the two; the rule of two heads, which is two clauses under one label;
/// the equation written `fact`; and the constraint. Four things in the same sort are
/// not: the default body of `heavier` (stored there as the equation
/// `heavier(a, b) = gt(…)`), the fact `Sample(n: 1)`, the declaration `declared(?p)`,
/// and the `domain` rule the loader derives for a sort that has an entity.
#[test]
fn a_law_is_a_rule_or_a_constraint_written_in_the_spec() {
    let kb = load_kb_with(SRC);
    let mut of_measured = laws(&kb, "test.bvg8m.laws.Measured");
    // The rules are in the order the source has them. A `fact` and a `constraint` are
    // loaded with their own kinds, so where each stands among the rules is the
    // loader's; the row holds which clauses are laws, and sorts them.
    let rules: Vec<&str> = of_measured
        .iter()
        .filter(|law| law.contains(" rule "))
        .map(String::as_str)
        .collect();
    assert_eq!(
        rules,
        [
            "weight_nonneg rule equation",
            "- rule equation",
            "weight_bound rule clause",
            "weight_then rule clause",
            "two_heads rule clause",
            "two_heads rule clause",
        ]
    );
    of_measured.retain(|law| !law.contains(" rule "));
    of_measured.sort();
    assert_eq!(of_measured, ["- constraint clause", "- fact equation"]);

    // A sort that requires a spec has none of the spec's laws for its own.
    assert_eq!(laws(&kb, "test.bvg8m.laws.Scope"), Vec::<String>::new());
}

/// The library's specs, for the shapes they hold. THE COUNTS ARE THE LIBRARY'S, on
/// 2026-10-12, and move when a law is written or taken out — what the row holds is
/// which clauses of each sort were counted:
///
/// * `PartialOrd` — four operations with default bodies, and no law;
/// * `WeakOrd` — eight equations and a constraint, beside two default bodies;
/// * `PartialEq` — one equation, with no label; `Eq` — one, labelled;
/// * `Constructive` — eight declarations, which assert nothing;
/// * `EffectsRuntime` — a fact that is no equation, and no law.
#[test]
fn the_librarys_laws_are_not_its_default_bodies() {
    let kb = load_stdlib_kb();
    let prelude = |name: &str| format!("anthill.prelude.{name}");
    let labels = |names: &[&str]| names.iter().map(|n| (*n).to_owned()).collect::<Vec<_>>();

    assert_eq!(count_and_labels(&kb, &prelude("PartialOrd")), (0, labels(&[])));
    assert_eq!(
        count_and_labels(&kb, &prelude("WeakOrd")),
        (9, labels(&["compare_antisym", "compare_refl"]))
    );
    assert_eq!(count_and_labels(&kb, &prelude("PartialEq")), (1, labels(&[])));
    assert_eq!(count_and_labels(&kb, &prelude("Eq")), (1, labels(&["eq_refl"])));
    assert_eq!(
        count_and_labels(&kb, "anthill.logic.Constructive.Constructive"),
        (0, labels(&[]))
    );
    assert_eq!(count_and_labels(&kb, &prelude("EffectsRuntime")), (0, labels(&[])));
}

/// The clauses of the scopes named, as `(scope, the sort the spec is of, <SE>)`.
fn clauses(kb: &KnowledgeBase, scopes: &[&str]) -> Vec<(String, String, String)> {
    requires_clauses_of(kb, scopes)
        .expect("the relation is read")
        .into_iter()
        .map(|RequiresClause { scope_qn, spec, spec_text }| {
            (scope_qn, kb.qualified_name_of(spec).to_owned(), spec_text)
        })
        .collect()
}

/// `Scope` requires `Measured` at its `T` and `Eq` at its `U`: two clauses, in the
/// order the source has them, each with the sort its spec is of. A scope that requires
/// nothing has none, and neither has a name that is no sort; and a scope that was not
/// named is not read — `Scope`'s clauses are no clauses of `WeakOrd`.
#[test]
fn the_clauses_of_a_scope_are_read_off_its_declaration() {
    let kb = load_kb_with(SRC);
    let scope = "test.bvg8m.laws.Scope";
    let of_scope = vec![
        (
            scope.to_owned(),
            "test.bvg8m.laws.Measured".to_owned(),
            "test.bvg8m.laws.Measured[T = test.bvg8m.laws.Scope.T]".to_owned(),
        ),
        (
            scope.to_owned(),
            "anthill.prelude.Eq".to_owned(),
            "anthill.prelude.Eq[T = test.bvg8m.laws.Scope.U]".to_owned(),
        ),
    ];
    assert_eq!(clauses(&kb, &[scope]), of_scope);

    for none in [
        &["test.bvg8m.laws.Bare"][..],
        &["test.bvg8m.laws.Absent"],
        &["test.bvg8m.laws"],
        &[],
    ] {
        assert_eq!(clauses(&kb, none), Vec::new(), "{none:?} has no `requires`");
    }

    // Several scopes: the clauses of each, and of no other.
    let weak_ord = "anthill.prelude.WeakOrd";
    let of_weak_ord: Vec<(String, String)> = clauses(&kb, &[weak_ord])
        .into_iter()
        .map(|(scope, spec, _)| (scope, spec))
        .collect();
    assert_eq!(
        of_weak_ord,
        [
            (weak_ord.to_owned(), "anthill.prelude.Eq".to_owned()),
            (weak_ord.to_owned(), "anthill.prelude.PartialOrd".to_owned()),
        ]
    );
    let both: BTreeSet<_> = clauses(&kb, &[scope, "test.bvg8m.laws.Bare", weak_ord])
        .into_iter()
        .map(|(scope, _, _)| scope)
        .collect();
    assert_eq!(both, BTreeSet::from([scope.to_owned(), weak_ord.to_owned()]));
    assert_eq!(clauses(&kb, &[scope, "test.bvg8m.laws.Bare", weak_ord]).len(), 4);
}

/// THE RECORDS AND THE CLAUSES ARE ONE SET: every record the loader writes for a
/// `requires` clause is a clause read back by its name — `<scope>.requires.<SE>` — and
/// every clause of those scopes has its record. In the library, and with a program
/// loaded after it. This is what lets `anthill prove` read a scope's clauses where
/// proposal 030 says a proof is handed the scope's records.
#[test]
fn the_requirement_records_are_the_clauses() {
    let kb = load_kb_with(SRC);
    let text = |term, key: &str| match kb.get_term(named_field_term(&kb, term, key)?) {
        Term::Const(Literal::String(s)) => Some(s.clone()),
        _ => None,
    };

    let mut recorded: BTreeSet<String> = BTreeSet::new();
    let mut scopes: BTreeSet<String> = BTreeSet::new();
    for head in proof_record_heads(&kb) {
        let witness = named_field_term(&kb, head, "witness").expect("a record has a witness");
        let (Some(scope_qn), Some(aspect)) = (text(witness, "scope_qn"), text(witness, "aspect"))
        else {
            continue; // not a scope axiom
        };
        if !aspect.starts_with("requires.") {
            continue; // an induction principle
        }
        recorded.insert(text(head, "rule").expect("a record has a name"));
        scopes.insert(scope_qn);
    }
    // The library's requirements and `Scope`'s two: the walk did not come back empty.
    assert!(recorded.len() > 2, "the registry holds requirement records: {}", recorded.len());

    let scope_names: Vec<&str> = scopes.iter().map(String::as_str).collect();
    let read: BTreeSet<String> = requires_clauses_of(&kb, &scope_names)
        .expect("the relation is read")
        .into_iter()
        .map(|clause| format!("{}.requires.{}", clause.scope_qn, clause.spec_text))
        .collect();
    assert_eq!(read, recorded);
}
