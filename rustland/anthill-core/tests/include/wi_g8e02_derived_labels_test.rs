//! WI-20261121-G8E02 — EVERY CLAUSE THE LOADER STORES HAS A LABEL, a derived one included
//! (proposal 075 §6, *Labels for derived clauses*; kernel-language.md §4.1). Before: the
//! loader labeled a clause written in source (WI-20261121-MVQP8) and the `<op>__defeq`
//! rule, and nothing it derived — measured on bba5bb704, 6 063 of the standard library's
//! 6 306 clauses had no label, among them every `<Sort>.induction` axiom, every case of
//! every sort domain and every reflect row.
//!
//! Where a clause's label comes from is said where it is stored: every entry point that
//! stores one takes a `ClauseLabel` — `Written` (the source's, or the converter's),
//! `Derived` (named by the derivation: `IntList.induction`, `IntList.domain-i_cons`),
//! `Content` (a bodyless clause its derivation does not name — a reflect row, a
//! provision, an operation's equation — labeled by what it stores, as a written fact is,
//! under the declaration it is about) or `Runtime` (a fact a program asserts while it
//! runs, which stays unlabeled, §7 question 2). A label the loader mints is a symbol of
//! the clause's own, listed in no name table.
//!
//! BACK-OUTS: measured, at each row and listed at the end of this file.

use std::collections::{HashMap, HashSet};

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::{ClauseKind, ClauseOrigin, KnowledgeBase, RuleId};
use smallvec::SmallVec;

use crate::common::{load_kb_with, load_stdlib_kb};
use crate::wi_mvqp8_generated_label_test::is_generated;

const PROGRAM: &str = r#"
namespace g8e02
  import anthill.prelude.Int64

  enum IntList
    entity i_nil
    entity i_cons(head: Int64, tail: IntList)
  end

  entity Reading(value: Int64)

  fact prop_holds(i_nil)
  rule prop_holds(i_cons(head: ?_h, tail: ?t)) :- prop_holds(?t)

  operation double(x: Int64) -> Int64 = x + x

  fact p(1)
  rule both: twin_a(?x), twin_b(?x) :- p(?x)
  constraint positive: forall ?x: p(?x) -: ?x > 0
end
"#;

/// The qualified name of the predicate `rid`'s head states.
fn head_name(kb: &KnowledgeBase, rid: RuleId) -> String {
    match kb.rule_head_value(rid) {
        Value::Term { id, .. } => match kb.get_term(*id) {
            Term::Fn { functor, .. } | Term::Ref(functor) => {
                kb.qualified_name_of(*functor).to_owned()
            }
            other => format!("{other:?}"),
        },
        Value::Entity { functor, .. } => kb.qualified_name_of(*functor).to_owned(),
        other => other.type_name().to_owned(),
    }
}

/// Every live clause with no label, as `kind head` — what a row below expects empty.
fn unlabeled(kb: &KnowledgeBase) -> Vec<String> {
    kb.live_rule_ids_iter()
        .filter(|&rid| kb.rule_label(rid).is_none())
        .map(|rid| format!("{} {}", kb.rule_clause_kind(rid), head_name(kb, rid)))
        .collect()
}

fn label_qn(kb: &KnowledgeBase, rid: RuleId) -> String {
    let label = kb
        .rule_label(rid)
        .unwrap_or_else(|| panic!("{rid:?} has no label"));
    kb.qualified_name_of(label).to_owned()
}

fn assert_all_labeled(kb: &KnowledgeBase, what: &str) {
    let missing = unlabeled(kb);
    assert!(
        missing.is_empty(),
        "{} of the {} clauses {what} stored have no label, e.g. {:#?}",
        missing.len(),
        kb.live_rule_ids_iter().count(),
        &missing[..missing.len().min(12)],
    );
}

// ── every clause ────────────────────────────────────────────────

/// The acceptance's row: after the standard library's load every clause the loader
/// stored has a label.
///
/// BACKED OUT, any derivation stored with `Runtime` (B1 the induction axiom, B2 the
/// domain cases, B3 the `MemberInfo` rows, B13 an operation's equation): FAILS.
#[test]
fn every_clause_the_standard_library_load_stores_has_a_label() {
    assert_all_labeled(&load_stdlib_kb(), "the standard library's load");
}

/// …and after a program's load on top of it: the program's written clauses, its sorts'
/// induction axioms and domains, its operation's equation, its reflect rows, its
/// constraint's two clauses.
///
/// BACKED OUT as the row above (B1, B2, B3, B13): FAILS.
#[test]
fn every_clause_a_program_load_stores_has_a_label() {
    let library = load_stdlib_kb().live_rule_ids_iter().count();
    let kb = load_kb_with(PROGRAM);
    let total = kb.live_rule_ids_iter().count();
    assert!(
        total > library + 20,
        "the program stores clauses of its own: {library} before it, {total} after"
    );
    assert_all_labeled(&kb, "the library's and the program's loads");
}

/// The documented exception (§7, question 2): a fact a program asserts while it runs —
/// here through `KB.assert`'s door, `assert_checked_persistent` — is not the loader's,
/// and has no label. It is the one clause of the KB that has none.
///
/// BACKED OUT, the run-time row labeled (B4, `Content` at that door): FAILS — and so does
/// any back-out that leaves a loader clause unlabeled (B1, B2, B3, B13), at its last line.
#[test]
fn a_fact_a_program_asserts_while_it_runs_has_no_label() {
    let mut kb = load_kb_with(PROGRAM);
    let before: HashSet<RuleId> = kb.live_rule_ids_iter().collect();
    let reading = kb.resolve_symbol("g8e02.Reading");
    let value = kb.intern("value");
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let row = Value::term(kb.make_entity_term(
        reading,
        SmallVec::new(),
        SmallVec::from_slice(&[(value, seven)]),
    ));
    kb.assert_checked_persistent(row, None)
        .unwrap_or_else(|e| panic!("a `Reading` row asserts: {e:?}"))
        .expect("no guard is declared on `Reading`");
    let added: Vec<RuleId> = kb
        .live_rule_ids_iter()
        .filter(|r| !before.contains(r))
        .collect();
    assert_eq!(added.len(), 1, "one row stored: {added:?}");
    assert_eq!(
        kb.rule_label(added[0]),
        None,
        "a run-time fact has no label"
    );
    assert_eq!(unlabeled(&kb), vec!["Fact g8e02.Reading".to_string()]);
}

// ── derived clauses, by their derivation ────────────────────────

/// `<Sort>.induction` is one clause, and its label is the principle's own name — the
/// predicate's symbol itself, not a second symbol of its qualified name (a name resolves
/// to one symbol). A citation of the name reaches that clause and no other, and the
/// clause is the axiom the resolver proves an induction with.
///
/// BACKED OUT, the axiom stored with `Runtime` (B1): FAILS.
#[test]
fn the_induction_principle_is_labeled_by_its_own_name() {
    let mut kb = load_kb_with(PROGRAM);
    let induction = kb.resolve_symbol("g8e02.IntList.induction");
    let clauses = kb.rules_by_functor(induction);
    assert_eq!(clauses.len(), 1, "one axiom clause: {clauses:?}");
    assert_eq!(kb.rule_label(clauses[0]), Some(induction));
    assert_eq!(label_qn(&kb, clauses[0]), "g8e02.IntList.induction");
    assert_eq!(kb.rule_ids_by_qn("g8e02.IntList.induction"), clauses);
    assert_eq!(kb.clause_origin(clauses[0]), ClauseOrigin::Derived);

    let prop_holds = kb.resolve_symbol("g8e02.prop_holds");
    let prop = kb.alloc(Term::Ref(prop_holds));
    let goal = kb.alloc(Term::Fn {
        functor: induction,
        pos_args: SmallVec::from_elem(prop, 1),
        named_args: SmallVec::new(),
    });
    assert!(
        !kb.resolve(&[goal], &ResolveConfig::default()).is_empty(),
        "the labeled axiom proves `IntList.induction(prop_holds)`",
    );
}

/// The constructor a domain case `__fill(<ctor>(…))` is the case of.
fn case_constructor(kb: &KnowledgeBase, rid: RuleId) -> String {
    let Term::Fn { pos_args, .. } = kb.get_term(kb.rule_head(rid)) else {
        panic!("a case's head is `__fill(<constructor>)`");
    };
    match kb.get_term(pos_args[0]) {
        Term::Ref(c) | Term::Fn { functor: c, .. } => kb.local_name_of(*c).to_owned(),
        other => panic!("a case's argument is its constructor: {other:?}"),
    }
}

/// A sort's domain is one clause of `fill` per constructor, each labeled by the domain
/// and the constructor (`IntList.domain-i_cons`), and its value face is one clause
/// labeled by its own name. Each label cites its case and no other. A minted label is
/// listed in no name table (`SymbolTable::define_unlisted`): no name resolves to it, and
/// the label cites its clause through its symbol.
///
/// BACKED OUT: the cases stored with `Runtime` (B2), named without their constructor
/// (B5), one label shared by a sort's cases with the store's refusal taken out (B11+B12),
/// or each label made a local of the sort's scope (B10): FAILS.
#[test]
fn each_case_of_a_sort_domain_is_labeled_by_its_constructor() {
    let mut kb = load_kb_with(PROGRAM);
    let fill = kb.resolve_symbol("g8e02.IntList.__fill");
    let mut cases: Vec<(String, String, RuleId)> = kb
        .rules_by_functor(fill)
        .into_iter()
        .map(|rid| (case_constructor(&kb, rid), label_qn(&kb, rid), rid))
        .collect();
    cases.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
    let named: Vec<(&str, &str)> = cases
        .iter()
        .map(|(c, l, _)| (c.as_str(), l.as_str()))
        .collect();
    assert_eq!(
        named,
        vec![
            ("i_cons", "g8e02.IntList.domain-i_cons"),
            ("i_nil", "g8e02.IntList.domain-i_nil"),
        ],
    );
    for (_, label, rid) in &cases {
        let symbol = kb.rule_label(*rid).expect("labeled");
        assert_eq!(
            kb.clause_ids_of(symbol),
            vec![*rid],
            "`{label}` cites its case alone"
        );
        assert_eq!(
            kb.try_resolve_symbol(label),
            None,
            "`{label}` is listed in no name table"
        );
    }

    let face = kb.resolve_symbol("g8e02.IntList.domain");
    let faces = kb.rules_by_functor(face);
    assert_eq!(faces.len(), 1, "{faces:?}");
    assert_eq!(kb.rule_label(faces[0]), Some(face));

    // The labeled cases are the domain's: a member is checked through them.
    let i_nil = kb.resolve_symbol("g8e02.IntList.i_nil");
    let i_cons = kb.resolve_symbol("g8e02.IntList.i_cons");
    let (head, tail) = (kb.intern("head"), kb.intern("tail"));
    let three = kb.alloc(Term::Const(Literal::Int(3)));
    let nil = kb.alloc(Term::Ref(i_nil));
    let list = kb.make_entity_term(
        i_cons,
        SmallVec::new(),
        SmallVec::from_slice(&[(head, three), (tail, nil)]),
    );
    let goal = kb.alloc(Term::Fn {
        functor: face,
        pos_args: SmallVec::from_elem(list, 1),
        named_args: SmallVec::new(),
    });
    assert!(
        !kb.resolve(&[goal], &ResolveConfig::default()).is_empty(),
        "`IntList.domain(i_cons(head: 3, tail: i_nil))` holds through the labeled cases",
    );
}

/// No label names two clauses but a written rule's, whose heads are its clauses (here
/// `both`, the exception exercised); a label the loader derives names one clause — two
/// derivations never share one. Over the library and the program.
///
/// BACKED OUT, one label shared by a sort's cases (B11) with the store's refusal of a
/// derived label that labels another clause taken out (B12), or the constraint's goals
/// clause given the constraint's own label (B7): FAILS. With the refusal in place, B11
/// stops the library's load: `a derived label names exactly one clause`.
#[test]
fn no_derived_label_names_two_clauses() {
    let kb = load_kb_with(PROGRAM);
    let mut by_label: HashMap<Symbol, Vec<RuleId>> = HashMap::new();
    for rid in kb.live_rule_ids_iter() {
        by_label
            .entry(kb.rule_label(rid).expect("every clause is labeled"))
            .or_default()
            .push(rid);
    }
    let shared: Vec<(Symbol, &Vec<RuleId>)> = by_label
        .iter()
        .filter(|(_, ids)| ids.len() > 1)
        .map(|(l, ids)| (*l, ids))
        .collect();
    for (label, ids) in &shared {
        assert!(
            ids.iter()
                .all(|&rid| kb.clause_origin(rid) == ClauseOrigin::Source),
            "`{}` labels {} clauses and one of them is derived: {:?}",
            kb.qualified_name_of(*label),
            ids.len(),
            ids.iter()
                .map(|&rid| head_name(&kb, rid))
                .collect::<Vec<_>>(),
        );
    }
    assert!(
        shared
            .iter()
            .any(|(label, ids)| kb.qualified_name_of(*label) == "g8e02.both" && ids.len() == 2),
        "the written two-headed rule shares its label between its two clauses",
    );
}

// ── derived clauses, by their content ───────────────────────────

/// The SortInfo row the loader derives for `g8e02.IntList` in a load of `src`, by label.
fn sort_info_label(src: &str) -> String {
    let kb = load_kb_with(src);
    let int_list = kb.resolve_symbol("g8e02.IntList");
    let sort_info = kb.resolve_symbol("anthill.reflect.SortInfo");
    let rows: Vec<RuleId> = kb
        .rules_by_functor(sort_info)
        .into_iter()
        .filter(|&rid| {
            let named = kb.fact_head_named_args(rid).unwrap_or_default();
            named.iter().any(|&(field, value)| {
                kb.local_name_of(field) == "name"
                    && matches!(kb.get_term(value), Term::Ref(s) | Term::Fn { functor: s, .. } if *s == int_list)
            })
        })
        .collect();
    assert_eq!(rows.len(), 1, "one SortInfo row of IntList: {rows:?}");
    label_qn(&kb, rows[0])
}

/// A reflect row is labeled by what it stores, as a written fact is: the relation's
/// name, `-`, a hash of the row — a name under the declaration the row is about
/// (`g8e02.IntList.SortInfo-…`), as every derived label is a name of what derived it.
/// The label is a function of the row alone — a load that interns other names first, so
/// that every symbol of the program has another number, gives the row the same label —
/// and a different row has a different one.
///
/// BACKED OUT, the hash over a functor's symbol NUMBER where it reads its qualified name
/// (B6): FAILS at the renumbered load.
#[test]
fn a_derived_row_is_labeled_by_what_it_stores() {
    let label = sort_info_label(PROGRAM);
    assert!(is_generated(&label, "g8e02.IntList.SortInfo"), "{label}");
    let renumbered = PROGRAM.replace(
        "  enum IntList",
        "  entity Earlier(a: Int64, b: Int64)\n  entity Earlier2(c: Int64)\n  enum IntList",
    );
    assert_eq!(
        sort_info_label(&renumbered),
        label,
        "the label reads no symbol's number"
    );
    let other = PROGRAM.replace(
        "    entity i_nil\n",
        "    entity i_nil\n    entity i_one(v: Int64)\n",
    );
    assert_ne!(sort_info_label(&other), label, "another row, another label");
}

/// An operation's equation is labeled as the equation written `rule double(?x) <=> …`
/// would be: the operation's name and a hash of the clause.
///
/// BACKED OUT, the equation stored with `Runtime` (B13): FAILS.
#[test]
fn an_operations_equation_is_labeled_by_its_operation() {
    let kb = load_kb_with(PROGRAM);
    let double = kb.resolve_symbol("g8e02.double");
    let equations: Vec<RuleId> = kb
        .rules_by_functor(kb.resolve_symbol("anthill.prelude.PartialEq.eq"))
        .into_iter()
        .filter(|&rid| match kb.get_term(kb.rule_head(rid)) {
            Term::Fn { pos_args, .. } => matches!(
                kb.get_term(pos_args[0]),
                Term::Fn { functor, .. } if *functor == double
            ),
            _ => false,
        })
        .collect();
    assert_eq!(equations.len(), 1, "{equations:?}");
    let label = label_qn(&kb, equations[0]);
    assert!(is_generated(&label, "g8e02.double"), "{label}");
}

/// A constraint stores two clauses: its reflection row, which the source wrote and
/// which carries the constraint's label, and the clause of its goals, derived, which
/// carries `<label>-goals`. Each label cites its clause alone.
///
/// BACKED OUT, the goals clause given the constraint's own label (B7): FAILS.
#[test]
fn a_constraints_two_clauses_have_two_labels() {
    let kb = load_kb_with(PROGRAM);
    let row = kb.rule_ids_by_qn("g8e02.positive");
    assert_eq!(row.len(), 1, "{row:?}");
    assert_eq!(kb.rule_clause_kind(row[0]), ClauseKind::Constraint);
    assert!(
        kb.is_fact(row[0]),
        "the reflection row `Constraint(guard(…))`"
    );
    assert_eq!(kb.clause_origin(row[0]), ClauseOrigin::Source);
    let goals: Vec<RuleId> = kb
        .live_rule_ids_iter()
        .filter(|&rid| {
            kb.rule_label(rid)
                .is_some_and(|l| kb.qualified_name_of(l) == "g8e02.positive-goals")
        })
        .collect();
    assert_eq!(goals.len(), 1, "{goals:?}");
    let label = kb.rule_label(goals[0]).expect("labeled");
    assert_eq!(
        kb.clause_ids_of(label),
        goals,
        "the label cites the goals clause alone"
    );
    assert_eq!(kb.rule_clause_kind(goals[0]), ClauseKind::Constraint);
    assert!(!kb.is_fact(goals[0]), "`⊥ :- p(?x), ?x > 0`");
    assert_eq!(kb.clause_origin(goals[0]), ClauseOrigin::Derived);
}

// ── BACK-OUTS ───────────────────────────────────────────────────
//
// MEASURED 2026-11-21, each change made alone and reverted, on a selected run of this file
// (`scripts/test.sh -p anthill-core --test wi_tests -- wi_g8e02`) and of the suite named:
//
// * B1 — `emit_induction_rule` stores the axiom with `ClauseLabel::Runtime`: 5 rows fail
//   (both every-clause rows, the run-time row, the induction row, the no-shared-label row).
// * B2 — `emit_fill_clauses` stores the cases with `Runtime`: 5 fail (both every-clause
//   rows, the run-time row, the domain row, the no-shared-label row).
// * B3 — `emit_member_fact` stores the `MemberInfo` rows with `Runtime`: 4 fail (both
//   every-clause rows, the run-time row, the no-shared-label row).
// * B4 — `assert_checked_persistent` stores the row with `Content`: the run-time row fails.
// * B5 — a case is labeled `domain`, without its constructor: the domain row fails.
// * B6 — the content hash reads a functor's symbol number: the content row fails.
// * B7 — the constraint's goals clause takes the constraint's label: the constraint row
//   and the no-shared-label row fail.
// * B8 — `KB.layer_symbols` lists the derived labels: 7 rows of `guardians_test` fail, the
//   gate refusing a well-formed candidate for "declaring" the labels of the flow facts a
//   later load derives about the library's `List.foldLeft` / `foldRight`.
// * B9 — the induction axiom is stored again for a sort declared, or presented, again:
//   7 rows of `wi_4zrtg_sealed_library_test` and 3 idempotence rows of `induction_tests`
//   fail, the store refusing the axiom's label for its second clause.
// * B10 — a minted label is a local of its scope (`SymbolTable::define`): the domain row
//   (its name resolves) and `wi_rmzqz_host_block_rule_label_test` (a type alias with a
//   `SortAlias` row "declared both as a type alias and with members of its own") fail.
// * B11 — a sort's cases share the first case's label: the library's load stops at the
//   store's refusal, every row fails. B11 with B12 (the refusal taken out): the domain row
//   and the no-shared-label row fail.
// * B13 — `emit_operation_equation` stores the equation with `Runtime`: 5 fail (both
//   every-clause rows, the run-time row, the no-shared-label row, the equation row).
//
// Every row fails under one of them; none passes them all.
