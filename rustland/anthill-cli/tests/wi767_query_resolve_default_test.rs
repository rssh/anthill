//! WI-767 — the default `anthill query` RESOLVES; it does not head-match.
//!
//! The pre-fix default was `kb.query` — discrimination-tree HEAD matching. On
//! ground facts that is indistinguishable from resolution, but on a rule it
//! unified the pattern with the rule head opened at fresh variables and
//! reported the match as an answer: `loc(?#0)  [?n = ?#0]` — "1 result(s)",
//! `?n` UNBOUND. That reads exactly like a floundered SLD answer, so a correct
//! rule looked broken while the same goal through `KnowledgeBase::resolve`
//! answered `?n = "a"` definitively. The default is now SLD resolution; the
//! old structural browse moved behind `--match`.
//!
//! The review of the fix added three loudness pins of the same
//! silent-wrong-answer class: a depth-truncated search must not read as a
//! refutation, a capped answer set must not read as a complete enumeration,
//! and a strategy flag must not be silently dropped under a listing mode.

mod common;

use std::rc::Rc;

use anthill_core::eval::value::Value;
use anthill_core::kb::load::{self, FileSourceResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

use common::{anthill, fixtures_dir};

fn fixture() -> std::path::PathBuf {
    fixtures_dir("query").join("enumerating-rule.anthill")
}

/// The API-side answer: definite bindings of `?n` in `probe.wi767.loc(?n)`
/// over the same fixture the CLI loads. The goal is built directly as a
/// `Value::Entity` (the known-good `kb.resolve` shape from
/// `wi760_realization_rule_test`), NOT via the CLI's parse-a-pattern path, so
/// the two sides construct their goals independently and must agree.
fn api_definite_bindings() -> Vec<String> {
    let source = std::fs::read_to_string(fixture()).expect("read fixture");
    let parsed = parse::parse(&source).expect("fixture parses");
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &[&parsed], &FileSourceResolver::new(Vec::new()))
        .expect("fixture loads");

    let functor = kb.try_resolve_symbol("probe.wi767.loc").expect("rule loaded");
    let n_sym = kb.intern("n");
    let vid = kb.fresh_var(n_sym);
    let goal = Value::Entity {
        functor,
        pos: Rc::from(vec![Value::Var(Var::Global(vid))]),
        named: Rc::from(Vec::new()),
    };
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    sols.iter()
        .filter(|s| s.residual.is_empty())
        .map(|s| match s.subst.resolve_as_value(vid) {
            Some(Value::Str(v)) => v.clone(),
            Some(Value::Term { id, .. }) => match kb.get_term(*id) {
                Term::Const(Literal::String(v)) => v.clone(),
                other => panic!("?n bound to a non-string term: {other:?}"),
            },
            other => panic!("?n unbound in a definite solution: {other:?}"),
        })
        .collect()
}

/// The acceptance pin: the CLI's DEFAULT invocation returns the same definite
/// bindings as `kb.resolve` — nothing unbound, nothing floundered.
#[test]
fn default_query_agrees_with_kb_resolve_on_an_enumerating_rule() {
    let api = api_definite_bindings();
    assert_eq!(api, vec!["a".to_string()],
               "API baseline moved — fixture or resolver changed");

    let fx = fixture();
    let out = anthill(&["query", "-p", fx.to_str().unwrap(), "probe.wi767.loc(?n)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    for value in &api {
        assert!(out.stdout.contains(&format!("?n = {value:?}")),
                "CLI must bind ?n = {value:?} like kb.resolve; got stdout:\n{}", out.stdout);
    }
    assert!(out.has_stdout_line(&format!("{} solution(s)", api.len())),
            "CLI must report exactly the definite solutions; got stdout:\n{}", out.stdout);
    assert!(!out.stdout.contains("residual"),
            "no goal flounders here; got stdout:\n{}", out.stdout);
}

/// `--match` keeps the old structural browse, made honest: a bodied rule's
/// head match renders as `head :- body` — visibly a rule, not an answer whose
/// variables failed to ground — and the count says `result`, not `solution`.
#[test]
fn match_mode_lists_the_rule_head_without_evaluating() {
    let fx = fixture();
    let out = anthill(&["query", "--match", "-p", fx.to_str().unwrap(), "probe.wi767.loc(?n)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(out.has_stdout_line("1 result(s)"),
            "one head match expected; got stdout:\n{}", out.stdout);
    assert!(out.stdout.contains(" :- "),
            "a bodied rule must show its body; got stdout:\n{}", out.stdout);
    assert!(!out.stdout.contains("?n = \"a\""),
            "--match must not evaluate the rule body; got stdout:\n{}", out.stdout);
}

/// `--match` on a fact pattern echoes the stored fact itself — the browse view
/// (and the CLI suite's only pin of head rendering, per the WI-767 review).
#[test]
fn match_mode_echoes_fact_heads() {
    let fx = fixture();
    let out = anthill(&["query", "--match", "-p", fx.to_str().unwrap(),
                        "probe.wi767.LocalSort.Local(name: ?n, val: ?v)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(out.stdout.contains("name: \"a\"") && out.stdout.contains("val: \"one\""),
            "the stored fact must be echoed with its fields; got stdout:\n{}", out.stdout);
    assert!(out.has_stdout_line("2 result(s)"),
            "both Local facts match; got stdout:\n{}", out.stdout);
}

/// `--resolve` predates the default flip; it stays accepted and identical.
#[test]
fn resolve_flag_is_still_accepted() {
    let fx = fixture();
    let out = anthill(&["query", "--resolve", "-p", fx.to_str().unwrap(), "probe.wi767.loc(?n)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(out.stdout.contains("?n = \"a\"") && out.has_stdout_line("1 solution(s)"),
            "--resolve must answer like the default; got stdout:\n{}", out.stdout);
}

/// `--match` and `--resolve` contradict each other; clap refuses the combo.
#[test]
fn match_conflicts_with_resolve() {
    let fx = fixture();
    let out = anthill(&["query", "--match", "--resolve", "-p", fx.to_str().unwrap(),
                        "probe.wi767.loc(?n)"]);
    assert_ne!(out.code, 0, "conflicting flags must be refused; stdout:\n{}", out.stdout);
    assert!(out.stderr.contains("cannot be used with"),
            "the refusal must come from the declared conflict, not an unrelated failure; stderr:\n{}",
            out.stderr);
}

/// A depth-truncated search abandoned branches, so its "no solutions" is
/// UNDECIDED — without the caveat a correct rule reads as refuted, the exact
/// silent-wrong-answer class WI-767 was filed about, on the depth axis.
#[test]
fn depth_truncated_search_is_flagged_undecided() {
    let fx = fixture();
    let out = anthill(&["query", "--max-depth", "1", "-p", fx.to_str().unwrap(),
                        "probe.wi767.loc(?n)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(out.stdout.contains("no solutions"),
            "depth 1 cannot reach the rule body; got stdout:\n{}", out.stdout);
    assert!(out.stdout.contains("truncated at --max-depth"),
            "a truncated search must carry the UNDECIDED caveat; got stdout:\n{}", out.stdout);
}

/// Hitting --max-results must say so: the resolver is asked for one solution
/// PAST the cap, so the summary can flag the cut instead of passing a capped
/// count off as a complete enumeration.
#[test]
fn hitting_the_result_cap_is_flagged() {
    let fx = fixture();
    let out = anthill(&["query", "--max-results", "1", "-p", fx.to_str().unwrap(),
                        "probe.wi767.LocalSort.Local(name: ?n, val: ?v)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(out.has_stdout_line("1 solution(s) shown — more exist, raise --max-results"),
            "two Local facts behind a cap of 1 must flag the cut; got stdout:\n{}", out.stdout);
}

/// `--max-depth` budgets RESOLUTION; under `--match` (or a listing mode) it
/// used to be accepted and silently inert.
#[test]
fn max_depth_under_match_is_refused() {
    let fx = fixture();
    let out = anthill(&["query", "--match", "--max-depth", "3", "-p", fx.to_str().unwrap(),
                        "probe.wi767.loc(?n)"]);
    assert_eq!(out.code, 1,
               "--max-depth under --match must be refused, not ignored; stdout:\n{}", out.stdout);
    assert!(out.stderr.contains("--max-depth applies only to resolution"),
            "the refusal must name the flag; got stderr:\n{}", out.stderr);
}

/// `--match` (and `--resolve`) select the PATTERN answering strategy; under a
/// listing mode they used to be accepted and silently dropped.
#[test]
fn match_under_a_listing_mode_is_refused() {
    let fx = fixture();
    let out = anthill(&["query", "--match", "--mode", "sort", "-p", fx.to_str().unwrap(),
                        "probe.wi767.LocalSort"]);
    assert_eq!(out.code, 1,
               "--match under --mode sort must be refused, not ignored; stdout:\n{}", out.stdout);
    assert!(out.stderr.contains("--mode pattern"),
            "the refusal must say which mode accepts the flag; got stderr:\n{}", out.stderr);
}
