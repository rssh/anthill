//! WI-023: parse/load integration for quantified constraints. A `no/lone/…`
//! constraint lowers to a `LogicalQuery` guard (carrier-agnostic `add_guard`),
//! and the post-load `check_all_guards` pass enforces it; aggregation constraints
//! are reported as not-yet-enforced.
//!
//! The constraints here use CROSS-ATOM variable sharing (`?x` shared between the
//! quantifier's condition and body, each atom itself linear). Intra-atom repeated
//! variables (`edge(from: ?n, to: ?n)`) are deliberately avoided: the resolver's
//! discrim-query-as-unifier does not yet enforce non-linear (repeated-variable)
//! consistency within a single atom — a separate resolver limitation, not the
//! constraint-wiring this WI delivers.

use crate::common::try_load_kb_with;

const GRAPH: &str = r#"
namespace test.wi023
  sort Node
    entity a
    entity b
    entity c
  end
  sort Rel
    entity edge(from: Node, to: Node)
  end
"#;

/// `no ?x: a→x -: x→a` (no 2-cycle through `a`). With edges a→b, b→c there is no
/// such cycle, so the constraint holds and the file loads; the guard registers.
#[test]
fn quantified_no_constraint_satisfied_loads() {
    let source = format!(
        "{GRAPH}\n  constraint no_two_cycle: no ?x: edge(from: a, to: ?x) -: edge(from: ?x, to: a)\n  fact edge(from: a, to: b)\n  fact edge(from: b, to: c)\nend\n"
    );
    let kb = try_load_kb_with(&source).unwrap_or_else(|errs| {
        panic!("expected load to succeed, got: {errs:?}");
    });
    assert_eq!(kb.guard_count(), 1, "the quantified constraint should register one guard");
}

/// With edges a→b, b→a there IS a 2-cycle through `a` (x = b), so the constraint
/// is violated and the load is blocked with a labeled ConstraintViolated error.
#[test]
fn quantified_no_constraint_violated_fails() {
    let source = format!(
        "{GRAPH}\n  constraint no_two_cycle: no ?x: edge(from: a, to: ?x) -: edge(from: ?x, to: a)\n  fact edge(from: a, to: b)\n  fact edge(from: b, to: a)\nend\n"
    );
    let errs = match try_load_kb_with(&source) {
        Ok(_) => panic!("a 2-cycle through `a` must violate the constraint, but load succeeded"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains("violated") && e.contains("no_two_cycle")),
        "expected a ConstraintViolated error mentioning the label, got: {errs:?}"
    );
}

/// A `some` constraint drives eval_count_guard with max = usize::MAX; it must
/// load without overflow (the saturating_add fix) when satisfied. With a 2-cycle
/// a→b→a present, `some ?x: a→x -: x→a` holds.
#[test]
fn some_quantified_constraint_loads_without_overflow() {
    let source = format!(
        "{GRAPH}\n  constraint has_two_cycle: some ?x: edge(from: a, to: ?x) -: edge(from: ?x, to: a)\n  fact edge(from: a, to: b)\n  fact edge(from: b, to: a)\nend\n"
    );
    let kb = try_load_kb_with(&source).unwrap_or_else(|errs| {
        panic!("a satisfied `some` constraint should load, got: {errs:?}");
    });
    assert_eq!(kb.guard_count(), 1);
}

/// A single-atom `forall` body is correctly negated and enforced. With edges
/// a→b, b→a, `forall ?x: a→x -: x→a` holds (every x reachable from a links back).
#[test]
fn forall_single_atom_body_loads() {
    let source = format!(
        "{GRAPH}\n  constraint all_link_back: forall ?x: edge(from: a, to: ?x) -: edge(from: ?x, to: a)\n  fact edge(from: a, to: b)\n  fact edge(from: b, to: a)\nend\n"
    );
    let kb = try_load_kb_with(&source).unwrap_or_else(|errs| {
        panic!("a satisfied single-atom forall should load, got: {errs:?}");
    });
    assert_eq!(kb.guard_count(), 1);
}

/// A: a `forall` with a multi-atom `-:` body cannot be negated correctly
/// (¬(Q1∧Q2) ≠ ¬Q1∧¬Q2), so it is rejected loudly rather than mis-evaluated.
#[test]
fn forall_multi_atom_body_rejected() {
    let source = format!(
        "{GRAPH}\n  constraint bad: forall ?x: edge(from: a, to: ?x) -: edge(from: ?x, to: a), edge(from: ?x, to: b)\nend\n"
    );
    let errs = match try_load_kb_with(&source) {
        Ok(_) => panic!("multi-atom forall body must be rejected, but load succeeded"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains("unsupported form") && e.contains("forall") && e.contains("bad")),
        "expected an UnsupportedConstraintForm error, got: {errs:?}"
    );
}

/// B: the top-level `head -: conclusion` implication form is rejected loudly at
/// parse time rather than silently dropping the conclusion.
#[test]
fn top_level_conclusion_form_rejected_at_parse() {
    let src = "namespace t\n  constraint c: foo(x: a) -: bar(y: a)\nend\n";
    assert!(
        anthill_core::parse::parse(src).is_err(),
        "top-level `head -: conclusion` constraint must be a loud parse error"
    );
}

/// B: a `:- guard` on a quantifier body is rejected loudly at parse time.
#[test]
fn quantifier_body_guard_rejected_at_parse() {
    let src = "namespace t\n  constraint c: forall ?x -: p(v: ?x) :- q(v: ?x)\nend\n";
    assert!(
        anthill_core::parse::parse(src).is_err(),
        "a `:- guard` on a quantifier body must be a loud parse error"
    );
}

/// An aggregation constraint is parsed but reported as not-yet-enforced (loud),
/// rather than silently registering a vacuously-true guard.
#[test]
fn aggregation_constraint_reports_unsupported() {
    let source = format!(
        "{GRAPH}\n  constraint few_edges: count(?x: edge(from: a, to: ?x) -: edge(from: a, to: ?x)) <= 10\nend\n"
    );
    let errs = match try_load_kb_with(&source) {
        Ok(_) => panic!("aggregation is not yet enforced, but load succeeded"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains("aggregation") && e.contains("few_edges")),
        "expected an AggregationConstraintUnsupported error, got: {errs:?}"
    );
}
