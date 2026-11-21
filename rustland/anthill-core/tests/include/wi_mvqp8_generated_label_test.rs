//! WI-20261121-MVQP8 — A RULE, FACT OR CONSTRAINT WRITTEN WITHOUT A LABEL GETS ONE: its
//! head's name, `-`, and a hash of its content (`pos-K3M9Q2XA`), decided with the user
//! 2026-11-21. Nothing after the converter tells it from a written label: it is defined
//! in its scope, it is the target of the clause's descriptions, `describe` and `using`
//! reach it by name, and a constraint's report names it — located now, and with the
//! constraint's descriptions.
//!
//! Before: two violated unlabeled constraints printed two identical lines, `integrity
//! constraint is violated by the loaded facts`; a written label was reported with no
//! location; a `{< … >}` block before a `fact`, an unlabeled bodied rule or an unlabeled
//! constraint was refused ("has no stable target", WI-20261115-S6CWK rows 1-3).
//!
//! The hash is of the clause's CANONICAL form — its kind, then its tokens with comments
//! and descriptions left out and each variable renamed by its first occurrence — so the
//! label is a function of the clause alone: another clause of the scope never moves it,
//! renaming a variable or reformatting leaves it, and changing what it says changes it.
//!
//! BACK-OUTS: measured, listed at the end of this file.

use anthill_core::kb::load::{LoadError, ReportedConstraint};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::KnowledgeBase;

use crate::common::{
    load_errors_of, load_kb_with, load_outcome, query_pattern_term, unrendered_load_errors_of,
};
use crate::wi1070_operation_description_test::descriptions_of;

/// The constraints a load reports violated: each one's label, site and descriptions.
fn violated(src: &str) -> Vec<(String, String, Vec<String>)> {
    unrendered_load_errors_of(src)
        .into_iter()
        .filter_map(|e| match e {
            LoadError::ConstraintViolated {
                constraint: Some(ReportedConstraint { label, site }),
                descriptions,
            } => Some((label, site, descriptions)),
            _ => None,
        })
        .collect()
}

/// Is `label` `name-` and an 8-character base-32 hash?
pub(crate) fn is_generated(label: &str, name: &str) -> bool {
    label.strip_prefix(name).and_then(|rest| rest.strip_prefix('-')).is_some_and(|hash| {
        hash.len() == 8 && hash.chars().all(|c| c.is_ascii_digit() || c.is_ascii_uppercase())
    })
}

/// The qualified target of the one description whose content is `content`.
pub(crate) fn target_of(kb: &KnowledgeBase, content: &str) -> String {
    let desc = kb.resolve_symbol("anthill.reflect.DescriptionInfo");
    for fid in kb.rules_by_functor(desc) {
        let Term::Fn { named_args, .. } = kb.get_term(kb.fact_term(fid)) else {
            continue;
        };
        let field = |f: &str| {
            named_args
                .iter()
                .find(|(n, _)| kb.local_name_of(*n) == f)
                .map(|&(_, t)| t)
        };
        let text = field("content").map(|t| kb.get_term(t));
        if text == Some(&Term::Const(Literal::String(content.to_owned()))) {
            if let Some(Term::Ref(s)) = field("target").map(|t| kb.get_term(t)) {
                return kb.qualified_name_of(*s).to_owned();
            }
        }
    }
    panic!("no description `{content}`");
}

// ── reports ─────────────────────────────────────────────────────

const ROW1: &str = r#"
namespace mvqp8.row1
  import anthill.prelude.Int64
  fact p(1)
  fact q(1)
  rule big(?x) :- ?x > 5
  rule small(?x) :- ?x < 0
  constraint forall ?x: p(?x) -: big(?x)
  constraint forall ?x: q(?x) -: small(?x)
end
"#;

/// The ticket's row 1: two violated unlabeled constraints are two different lines, each
/// naming its constraint by its label and saying where it is written.
#[test]
fn two_unlabeled_violations_are_told_apart_and_located() {
    let reports = violated(ROW1);
    assert_eq!(reports.len(), 2, "{reports:?}");
    assert!(is_generated(&reports[0].0, "big"), "{reports:?}");
    assert!(is_generated(&reports[1].0, "small"), "{reports:?}");
    assert!(
        reports[0].1.starts_with("8:") && reports[1].1.starts_with("9:"),
        "each report is located at its own constraint: {reports:?}",
    );
    let lines = load_errors_of(ROW1);
    assert_eq!(lines.len(), 2, "{lines:#?}");
    assert_ne!(lines[0], lines[1], "the two lines differ: {lines:#?}");
    assert!(lines[0].contains("integrity constraint 'big-"), "{lines:#?}");
}

/// The ticket's row 2: a written label is reported as it always was, located now.
#[test]
fn a_written_label_is_reported_as_written() {
    let reports = violated(
        r#"
namespace mvqp8.row2
  import anthill.prelude.Int64
  fact p(1)
  rule small(?x) :- ?x < 0
  constraint labeled_one: forall ?x: p(?x) -: small(?x)
end
"#,
    );
    assert_eq!(reports.len(), 1, "{reports:?}");
    assert_eq!(reports[0].0, "labeled_one");
    assert!(reports[0].1.starts_with("6:"), "located at the constraint: {reports:?}");
}

const ROW3: &str = r#"
namespace mvqp8.row3
  import anthill.prelude.Int64
  fact p(1)
  rule big(?x) :- ?x > 5
  {< every p is big >}
  constraint forall ?x: p(?x) -: big(?x)
end
"#;

/// The ticket's row 3: a description before an unlabeled constraint loads, names its
/// label, and the violation report carries it.
#[test]
fn an_unlabeled_constraints_description_is_stored_and_reported() {
    let (kb, errors) = load_outcome(ROW3).kb_and_errors();
    let target = target_of(&kb, "every p is big");
    let reported: Vec<(&String, &Vec<String>)> = errors
        .iter()
        .filter_map(|e| match e {
            LoadError::ConstraintViolated {
                constraint: Some(ReportedConstraint { label, .. }),
                descriptions,
            } => Some((label, descriptions)),
            _ => None,
        })
        .collect();
    assert_eq!(reported.len(), 1, "{errors:#?}");
    assert_eq!(
        target,
        format!("mvqp8.row3.{}", reported[0].0),
        "the block's target is the label the report names",
    );
    assert_eq!(reported[0].1, &vec!["every p is big".to_string()]);
    let lines = load_errors_of(ROW3);
    assert!(
        lines.iter().any(|l| l.ends_with("— every p is big")),
        "the report shows the description: {lines:#?}"
    );
}

// ── the label ───────────────────────────────────────────────────

/// S6CWK rows 1-3, and the names a label starts with: a fact's and a rule's head, an
/// equation's subject, a bare-name head, and a constraint whose consequent names no
/// predicate (an operator), which is named by its kind.
#[test]
fn every_unlabeled_clause_is_described_under_its_label() {
    let kb = load_kb_with(
        r#"
namespace mvqp8.s6
  import anthill.prelude.Int64
  {< a fact about one >}
  fact n(1)
  {< every n is positive >}
  rule pos(?x) :- n(?x), ?x > 0
  {< it holds >}
  fact holds
  {< no n is huge >}
  constraint no ?x: n(?x) -: ?x > 1000
  {< an equation's own intent >}
  rule twice(?x) <=> ?x + ?x
end
"#,
    );
    for (text, name) in [
        ("a fact about one", "mvqp8.s6.n"),
        ("every n is positive", "mvqp8.s6.pos"),
        ("it holds", "mvqp8.s6.holds"),
        ("no n is huge", "mvqp8.s6.constraint"),
        ("an equation's own intent", "mvqp8.s6.twice"),
    ] {
        let target = target_of(&kb, text);
        assert!(is_generated(&target, name), "{text}: {target}");
        assert_eq!(descriptions_of(&kb, &target), vec![(0, text.to_string())]);
    }
}

/// The label is a function of the clause ALONE. Another clause of the same head, added
/// beside it, leaves it; so do renaming a variable and reformatting. Changing what the
/// clause says changes it.
#[test]
fn a_label_is_a_function_of_its_clause_alone() {
    let label = |clause: &str, neighbour: &str| {
        target_of(
            &load_kb_with(&format!(
                r#"
namespace mvqp8.stable
  import anthill.prelude.Int64
  fact n(1)
  {neighbour}
  {{< this one >}}
  {clause}
end
"#
            )),
            "this one",
        )
    };
    let alone = label("rule pos(?x) :- n(?x), ?x > 0", "");
    assert!(is_generated(&alone, "mvqp8.stable.pos"), "{alone}");
    assert_eq!(alone, label("rule pos(?x) :- n(?x), ?x > 0", "rule pos(?x) :- n(?x), ?x > 100"));
    assert_eq!(alone, label("rule pos(?y) :- n(?y),\n      ?y > 0", ""));
    assert_ne!(alone, label("rule pos(?x) :- n(?x), ?x > 1", ""));
}

/// A fact and `rule … :- true` are one clause (§6.1), so they share one label; a rule and
/// a constraint written alike are two declarations, so they do not.
#[test]
fn one_clause_has_one_label_and_a_constraint_is_not_a_rule() {
    let kb = load_kb_with(
        r#"
namespace mvqp8.kind
  import anthill.prelude.Int64
  {< as a fact >}
  fact p(1)
  {< as a rule >}
  rule p(1) :- true
  {< a rule >}
  rule big(?x) :- p(?x)
  {< a constraint >}
  constraint big(?x) :- p(?x)
end
"#,
    );
    assert_eq!(target_of(&kb, "as a fact"), target_of(&kb, "as a rule"));
    assert_ne!(target_of(&kb, "a rule"), target_of(&kb, "a constraint"));
}

/// A generated label is a name like a written one: `describe` reaches it from elsewhere,
/// and a rule written with several heads and no label loads under it, as a labeled one
/// does — both measured refused before.
#[test]
fn a_generated_label_is_a_name_like_a_written_one() {
    const CLAUSE: &str = "rule pos(?x) :- n(?x), ?x > 0";
    let label = {
        let kb = load_kb_with(&format!(
            "namespace mvqp8.name\n  import anthill.prelude.Int64\n  fact n(1)\n  {{< inline >}}\n  {CLAUSE}\nend\n"
        ));
        let target = target_of(&kb, "inline");
        target.rsplit('.').next().unwrap().to_owned()
    };
    let kb = load_kb_with(&format!(
        "namespace mvqp8.name\n  import anthill.prelude.Int64\n  fact n(1)\n  {CLAUSE}\n  describe {label} {{< from a describe >}}\nend\n"
    ));
    assert_eq!(
        descriptions_of(&kb, &format!("mvqp8.name.{label}")),
        vec![(0, "from a describe".to_string())],
    );

    let mut kb = load_kb_with(
        r#"
namespace mvqp8.heads
  fact n(1)
  rule a(?x), b(?x) :- n(?x)
end
"#,
    );
    let goal = query_pattern_term(&mut kb, "mvqp8.heads.b(?x)");
    let (sols, _) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert_eq!(sols.len(), 1, "the second head of an unlabeled multi-head rule answers");
}

/// A fact's label is a symbol of its scope whether or not it is described, as a
/// written label is.
#[test]
fn an_undescribed_facts_label_is_a_symbol() {
    let with = load_kb_with("namespace mvqp8.quiet\n  {< x >}\n  fact n(1)\nend\n");
    let label = target_of(&with, "x");
    let without = load_kb_with("namespace mvqp8.quiet\n  fact n(1)\nend\n");
    assert!(without.try_resolve_symbol(&label).is_some(), "{label}");
}

/// A fact written in a host `provides … language … end` block is described under its
/// label at the block's target sort, the scope its clause loads in. Found by
/// `/code-review`: pass 1 defined no fact label there, and the load was refused,
/// "unresolved name 'tag_note-…' in scope 'mvqp8.pb.Tag'".
#[test]
fn a_fact_in_a_host_block_is_described() {
    let kb = load_kb_with(
        r#"
namespace mvqp8.pb
  sort Tag
    entity tag
  end
  provides Tag language rust
    {< described fact >}
    fact tag_note(1)
  end
end
"#,
    );
    let target = target_of(&kb, "described fact");
    assert!(is_generated(&target, "mvqp8.pb.Tag.tag_note"), "{target}");
}

/// A query's pattern is carried as `fact <pattern>`, and its generated label names
/// nothing: a query declares nothing. Found by `/code-review`: the pattern defined its
/// label in the global scope of the KB it asked.
#[test]
fn a_query_pattern_defines_no_label() {
    let parsed = anthill_core::parse::parse("fact mvqp8.q.n(1)").expect("parses");
    let anthill_core::parse::ir::Item::Fact(f) = &parsed.items[0] else {
        panic!("a fact");
    };
    let label = parsed.symbols.local_name(f.label.segments[0]).to_owned();
    let mut kb = load_kb_with("namespace mvqp8.q\n  fact n(1)\nend\n");
    let _ = query_pattern_term(&mut kb, "mvqp8.q.n(1)");
    assert!(kb.try_resolve_symbol(&label).is_none(), "{label}");
}

// BACK-OUTS, each measured on its own on the selected binary, over this file, wi1072 and
// wi_vfakk (23 rows):
//   * one fixed name generated for every clause (no head, no hash) — 8 red: the row-1
//     reports (one line), `every_unlabeled_clause_is_described_under_its_label`,
//     `a_label_is_a_function_of_its_clause_alone`,
//     `one_clause_has_one_label_and_a_constraint_is_not_a_rule`, wi1072's anonymous row and
//     vfakk's three generated-label rows. The rows that only need A label — the row-3
//     report, `describe`, the multi-head rule, the undescribed fact's symbol — pass, by
//     design;
//   * the canonical form's variable renaming dropped — 1 red:
//     `a_label_is_a_function_of_its_clause_alone`;
//   * the kind dropped from a constraint's canonical form — 1 red:
//     `one_clause_has_one_label_and_a_constraint_is_not_a_rule`;
//   * the site dropped from a report — 2 red: the row-1 and row-2 report rows;
//   * the descriptions dropped from a violation — 1 red: the row-3 row;
//   * the converter's refusal of a block on a fact, an unlabeled bodied rule and an
//     unlabeled constraint restored — 9 red: every row that writes one.
// The vfakk and wi1072 controls pass under every one of these, by design.
