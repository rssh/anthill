//! WI-20261029-50361 — a rule head named like a namespace it reaches introduces its own
//! predicate, as its declaration does, and a clause is never stored under a namespace
//! (kernel-language.md §5.3).
//!
//! A. THE TICKET'S SHAPES. Inside `namespace probe.zed` a bare `zed` reaches the namespace
//!    through the enclosing `probe`, and a head introduces only when its name resolves to
//!    nothing, so `rule zed :- …` introduced nothing and its clause was stored under the
//!    namespace: `probe.zed.zed` named nothing, `import probe.zed.{zed}` was refused, and the
//!    declared twin (`rule zed(?x)` above the clause) answered through `probe.zed.zed`. A
//!    namespace is no answer to the head's ladder now (`load::rule_head_ladder_answer`).
//! B. THE SAME RULE ELSEWHERE: a namespace reached deeper, through an `import`, from a body,
//!    and a qualified path through the name the head now takes, which is loud as it is under
//!    the declaration.
//! C. NO PREDICATE CAN BE INTRODUCED, so the clause is refused: a head in the scope that
//!    declares the namespace, a qualified head, a namespace-less file naming `anthill`
//!    (`ClauseHeadNamesNoRelation`, beside the const refusal it widens); the body-less
//!    declaration there no longer advises `:- true`; and an ambiguous head is reported once.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build, over this
//! file and the whole `wi_tests` binary:
//!
//!   * the namespace arm of `rule_head_ladder_answer` → every row of A and B but the control
//!     (seven), and outside this file four rows whose fixtures name a rule as the last segment
//!     of its namespace by accident — `wi_c7anm_…::a_non_parameter_named_arg_keeps_its_key`,
//!     `wi_p7vp4_…::a_goal_at_its_declared_arity_is_woven_only_for_the_bool_view`,
//!     `wi_s8cbv_…::two_projected_requires_bind_two_dictionaries_at_their_own_roots`,
//!     `wi_wf14z_…::a_refused_loads_clause_does_not_refuse_its_corrected_retry` — whose heads
//!     land on the namespace again and are refused by the arm below;
//!   * the namespace arm of `not_a_relation` → [`a_clause_that_would_land_on_a_namespace_is_refused`]
//!     and [`the_declaration_in_the_parent_does_not_advise_a_clause`], whose repair reads it;
//!   * the declaration's repair advising `:- true` again, in its detail or in the closing
//!     sentence (`BodylessRuleDeclaresNothing::clause_can_stand`) → the second alone;
//!   * the stop at a head reported ambiguous (`Loader::reported_ambiguity_since`) →
//!     [`an_ambiguous_head_is_reported_once`].
//!
//!   PASS EITHER WAY, by design: [`the_declared_entity_and_the_declared_predicate_were_already_their_own`],
//!   the control. Outside this binary, `anthill-cli`'s
//!   `wi_kf2sd_several_clauses_test::a_proof_naming_a_namespace_is_of_no_rule` holds the
//!   clause-kind filter in `anthill-smt-gen`'s `stated_clauses`, which this file's defect was
//!   the first case of.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, query_unary};

/// Definite answers of `pattern`.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// The `Int64` answers of `qn(?r)`, each definite.
fn ints(kb: &mut KnowledgeBase, qn: &str) -> Vec<i64> {
    query_unary(kb, qn)
        .into_iter()
        .map(|(v, definite)| match (v, definite) {
            (Value::Int(i), true) => i,
            other => panic!("`{qn}`: expected a definite Int64, got {other:?}"),
        })
        .collect()
}

// ── A. The ticket's shapes ──────────────────────────────────────────────────

/// `rule zed :- …` and `fact zed`, each read from another namespace through the import the
/// ticket found refused (`unresolved import 'probe.zed.zed'`).
#[test]
fn a_nullary_head_introduces_and_is_imported() {
    for (label, clause) in [
        ("rule", "rule zed :- Link(from: 1, to: 2)"),
        ("fact", "fact zed"),
    ] {
        let mut kb = load_kb_with(&format!(
            "namespace test.n50361a.zed\n  entity Link(from: Int64, to: Int64)\n  fact \
             Link(from: 1, to: 2)\n  {clause}\nend\nnamespace test.n50361a.use\n  import \
             test.n50361a.zed.{{zed}}\n  fact one(1)\n  rule seen(?r) :- zed, one(?r)\nend\n"
        ));
        assert_eq!(answers(&mut kb, "test.n50361a.zed.zed"), 1, "{label}: its own name");
        assert_eq!(ints(&mut kb, "test.n50361a.use.seen"), [1], "{label}: through the import");
    }
}

/// `rule zed(?x) :- …`: the predicate answers under its own name, and the namespace holds
/// nothing at that arity — before, `probe.zed(?x)` answered `3`.
#[test]
fn a_unary_head_answers_under_its_own_name_and_not_the_namespaces() {
    let mut kb = load_kb_with(
        "namespace test.n50361b.zed\n  entity Item(v: Int64)\n  fact Item(v: 3)\n  rule \
         zed(?x) :- Item(v: ?x)\nend\n",
    );
    assert_eq!(ints(&mut kb, "test.n50361b.zed.zed"), [3]);
    assert_eq!(answers(&mut kb, "test.n50361b.zed(?x)"), 0);
}

/// `rule zed` beside `fact zed(2)` is one predicate written at two arities, refused as any
/// other is — before, both clauses were stored under the namespace and the load was clean.
#[test]
fn two_arities_are_one_predicates_refusal() {
    let errs = load_errors_of(
        "namespace test.n50361c.zed\n  entity Link(from: Int64, to: Int64)\n  fact Link(from: \
         1, to: 2)\n  rule zed :- Link(from: 1, to: 2)\n  fact zed(2)\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["predicate 'test.n50361c.zed.zed' is written at more than one arity"],
        "two arities",
    );
}

/// CONTROLS, passing either way: a declared entity of the name, and the declared twin of the
/// ticket's rule — what the undeclared head now agrees with.
#[test]
fn the_declared_entity_and_the_declared_predicate_were_already_their_own() {
    let mut kb = load_kb_with(
        "namespace test.n50361d.zed\n  entity zed(x: Int64)\n  fact zed(x: 1)\nend\n",
    );
    assert_eq!(answers(&mut kb, "test.n50361d.zed.zed(x: 1)"), 1);
    let mut kb = load_kb_with(
        "namespace test.n50361e.zed\n  rule zed(?x)\n  rule zed(1) :- true\nend\n",
    );
    assert_eq!(ints(&mut kb, "test.n50361e.zed.zed"), [1]);
}

// ── B. The same rule elsewhere ──────────────────────────────────────────────

/// Reached from a deeper namespace, through an `import` of the namespace, and by one head of
/// a labeled multi-head rule: each introduces where it is written.
#[test]
fn a_namespace_reached_any_other_way_is_no_answer_either() {
    let mut kb = load_kb_with(
        "namespace test.n50361f.zed.inner\n  rule zed(1) :- true\nend\n\
         namespace test.n50361f.sib\n  import test.n50361f.zed\n  rule zed(2) :- true\nend\n",
    );
    assert_eq!(ints(&mut kb, "test.n50361f.zed.inner.zed"), [1], "deeper");
    assert_eq!(ints(&mut kb, "test.n50361f.sib.zed"), [2], "through an import");
    let mut kb = load_kb_with(
        "namespace test.n50361g.zed\n  entity Item(v: Int64)\n  fact Item(v: 3)\n  rule both: \
         zed(?x), other(?x) :- Item(v: ?x)\nend\n",
    );
    assert_eq!(ints(&mut kb, "test.n50361g.zed.zed"), [3], "a multi-head rule's head");
    assert_eq!(ints(&mut kb, "test.n50361g.zed.other"), [3], "and its other head");
}

/// Two scopes that see each other each introducing the name — the namespace and one nested
/// in it — is refused as it is for any other name, now that neither head is a clause of the
/// namespace. Before, both clauses were stored under it.
#[test]
fn two_scopes_introducing_the_name_are_refused_as_any_name_is() {
    let errs = load_errors_of(
        "namespace test.n50361h.zed.inner\n  rule zed(1) :- true\nend\n\
         namespace test.n50361h.zed\n  rule zed(2) :- true\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["the rule head `zed` introduces that name at 2 scopes", "test.n50361h.zed.inner"],
        "two scopes",
    );
}

/// A body goal in the namespace reads the predicate the head introduced.
#[test]
fn a_body_in_the_namespace_reads_the_new_predicate() {
    let mut kb = load_kb_with(
        "namespace test.n50361m.zed\n  fact zed(4)\n  rule q(?x) :- zed(?x)\nend\n",
    );
    assert_eq!(ints(&mut kb, "test.n50361m.zed.q"), [4]);
}

/// The head takes the name in its scope, so a qualified path through the namespace's name
/// there names nothing, loudly — as it does under the declaration `rule zed(?x)`. Before, the
/// clause sat on the namespace and the path read through it.
#[test]
fn a_path_through_the_name_the_head_takes_is_loud() {
    let errs = load_errors_of(
        "namespace test.n50361n.zed\n  entity Link(from: Int64, to: Int64)\n  fact Link(from: \
         1, to: 2)\n  rule zed(1) :- true\n  rule q :- zed.Link(from: 1, to: 2)\nend\n",
    );
    assert_refused_naming(&errs, &["`zed.Link` names nothing"], "the path");
}

// ── C. No predicate can be introduced ──────────────────────────────────────

const REFUSAL: &str = "a namespace is not a relation and holds no clauses";

/// In the scope that declares the namespace a predicate of its own would take the
/// namespace's qualified name, so the clause is refused, in either spelling — as is a
/// qualified head written anywhere, and a namespace-less file's head naming a top-level
/// namespace. Before, each loaded clean with its clause under the namespace.
#[test]
fn a_clause_that_would_land_on_a_namespace_is_refused() {
    let child = "namespace test.n50361i.zed\n  entity X(v: Int64)\nend\n";
    for (label, src, ns) in [
        (
            "rule in the parent",
            format!("namespace test.n50361i\n  rule zed(1) :- true\nend\n{child}"),
            "test.n50361i.zed",
        ),
        (
            "fact in the parent",
            format!("namespace test.n50361i\n  fact zed(1)\nend\n{child}"),
            "test.n50361i.zed",
        ),
        (
            "qualified head",
            format!("namespace test.n50361j\n  rule test.n50361i.zed(1) :- true\nend\n{child}"),
            "test.n50361i.zed",
        ),
        (
            "namespace-less file",
            "rule anthill(1) :- true\n".to_owned(),
            "anthill",
        ),
    ] {
        let errs = load_errors_of(&src);
        assert_refused_naming(
            &errs,
            &[&format!("head names the namespace `{ns}`"), REFUSAL],
            label,
        );
    }
}

/// The body-less declaration there is refused as before, and no longer advises `:- true` —
/// which wrote the clause the refusal above now refuses — nor does the one beside a const.
#[test]
fn the_declaration_in_the_parent_does_not_advise_a_clause() {
    for (label, src, kind) in [
        (
            "namespace",
            "namespace test.n50361k\n  rule zed(?x)\nend\nnamespace test.n50361k.zed\n  entity \
             X(v: Int64)\nend\n",
            "Namespace",
        ),
        (
            "const",
            "namespace test.n50361l\n  const zed: Int64 = 1\n  rule zed(?x)\nend\n",
            "Const",
        ),
    ] {
        let errs = load_errors_of(src);
        assert_refused_naming(
            &errs,
            &[
                &format!("already declared in this scope as a {kind}"),
                "no clause can be written of it",
            ],
            label,
        );
        assert!(
            !errs.iter().any(|e| e.contains(":- true")),
            "{label}: no advice to write a clause of it: {errs:#?}"
        );
    }
}


/// A head whose name is ambiguous gets one report: the namespace its recovery stands on is
/// not a name the author wrote. Before the guard, `fact M719.tgt` was refused a second time,
/// as naming `zz50361.a.M719`.
#[test]
fn an_ambiguous_head_is_reported_once() {
    let roots = "namespace zz50361.a\n  namespace M719\n    rule tgt :- true\n  end\nend\n\
                 namespace zz50361.b\n  namespace M719\n    rule tgt :- true\n  end\nend\n";
    for mark in ["", "()"] {
        let errs = load_errors_of(&format!(
            "{roots}namespace zz50361.use\n  import zz50361.a.*\n  import zz50361.b.*\n  sort \
             S\n    fact M719.tgt{mark}\n  end\nend\n"
        ));
        assert_eq!(errs.len(), 1, "`{mark}`: one head, one report: {errs:#?}");
        assert!(errs[0].contains("ambiguous symbol 'M719.tgt'"), "{errs:#?}");
    }
}


