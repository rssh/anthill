/// Integration test: load examples/github-todo + stdlib, resolve workflow queries.
///
/// Validates the full pipeline: parse → sugar desugar → load → SLD resolution
/// using the github-todo example (domain, project, tools, workitems, rules, feedback).

mod common;

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::persistence::print::TermPrinter;

use smallvec::SmallVec;

// ── KB loader ───────────────────────────────────────────────────

fn load_github_todo_kb() -> KnowledgeBase {
    let stdlib_dir = common::stdlib_dir();
    let example_dir = common::examples_dir().join("github-todo");

    let mut files = common::collect_anthill_files(&stdlib_dir);
    files.extend(common::collect_anthill_files(&example_dir));

    let parsed: Vec<_> = files.iter()
        .map(|path| {
            let source = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            parse::parse(&source)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", path.display()))
        })
        .collect();

    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let result = load::load_all(&mut kb, &refs, &NullResolver);
    if let Err(errs) = &result {
        for e in errs {
            eprintln!("Load warning: {e}");
        }
    }
    kb
}

fn resolve_config() -> ResolveConfig {
    ResolveConfig { max_solutions: 20, ..ResolveConfig::default() }
}

fn make_var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

/// Build a query term: functor(?arg1, ?arg2), resolving functor by qualified name.
fn make_query2(kb: &mut KnowledgeBase, qualified_functor: &str, arg1: &str, arg2: &str) -> TermId {
    let sym = kb.try_resolve_symbol(qualified_functor)
        .unwrap_or_else(|| panic!("symbol '{}' not found in KB", qualified_functor));
    let v1 = make_var(kb, arg1);
    let v2 = make_var(kb, arg2);
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(&[v1, v2]),
        named_args: SmallVec::new(),
    })
}

/// Extract a string binding from a solution.
fn extract_string(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    match kb.get_term(term) {
        Term::Const(anthill_core::kb::term::Literal::String(s)) => Some(s.clone()),
        _ => None,
    }
}

// ── Tests ───────────────────────────────────────────────────────

#[test]
fn loads_successfully() {
    let kb = load_github_todo_kb();
    assert!(kb.fact_count() > 100, "should load many facts from stdlib + example");
    assert!(kb.rule_count() > 0, "should load rules from rules.anthill");
}

#[test]
fn workitems_loaded() {
    let kb = load_github_todo_kb();
    let wi_sym = kb.try_resolve_symbol("anthill.stage0.WorkItem")
        .expect("WorkItem should be resolved");
    let results = kb.by_functor(wi_sym);
    // 4 work items + 1 entity definition = at least 4 facts with WorkItem functor
    assert!(results.len() >= 4, "expected at least 4 WorkItem facts, got {}", results.len());
}

#[test]
fn project_loaded() {
    let kb = load_github_todo_kb();
    let proj_sym = kb.try_resolve_symbol("anthill.stage0.Project")
        .expect("Project should be resolved");
    let results = kb.by_functor(proj_sym);
    assert!(results.len() >= 1, "expected at least 1 Project fact");
}

#[test]
fn open_item_resolves_all_four() {
    let mut kb = load_github_todo_kb();
    let query = make_query2(&mut kb, "anthill.stage0.workflow.open_item", "id", "desc");
    let solutions = kb.resolve(&[query], &resolve_config());
    assert_eq!(solutions.len(), 4, "all 4 work items are Open");
}

#[test]
fn claimable_resolves_only_wi_auth_001() {
    let mut kb = load_github_todo_kb();
    let query = make_query2(&mut kb, "anthill.stage0.workflow.claimable", "id", "desc");
    let solutions = kb.resolve(&[query], &resolve_config());
    assert_eq!(solutions.len(), 1, "only WI-AUTH-001 has no dependencies");

    // Verify it's WI-AUTH-001
    let sol = &solutions[0];
    let query_vars = kb.collect_vars(query);
    let id_var = query_vars.iter().find(|v| kb.resolve_sym(v.name()) == "id").unwrap();
    let id_val = sol.subst.resolve(*id_var)
        .and_then(|t| extract_string(&kb, t));
    assert_eq!(id_val.as_deref(), Some("WI-AUTH-001"));
}

#[test]
fn blocked_resolves_three() {
    let mut kb = load_github_todo_kb();
    let query = make_query2(&mut kb, "anthill.stage0.workflow.blocked", "id", "desc");
    let solutions = kb.resolve(&[query], &resolve_config());
    assert_eq!(solutions.len(), 3, "3 items have unverified dependencies");

    let query_vars = kb.collect_vars(query);
    let id_var = query_vars.iter().find(|v| kb.resolve_sym(v.name()) == "id").unwrap();
    let mut ids: Vec<String> = solutions.iter()
        .filter_map(|sol| sol.subst.resolve(*id_var).and_then(|t| extract_string(&kb, t)))
        .collect();
    ids.sort();
    assert_eq!(ids, vec!["WI-AUTH-002", "WI-AUTH-003", "WI-AUTH-004"]);
}

#[test]
fn feedback_loaded() {
    let kb = load_github_todo_kb();
    let fb_sym = kb.try_resolve_symbol("anthill.stage0.Feedback")
        .expect("Feedback should be resolved");
    let results = kb.by_functor(fb_sym);
    assert!(results.len() >= 2, "expected at least 2 Feedback facts, got {}", results.len());
}

#[test]
fn tooldef_loaded() {
    let kb = load_github_todo_kb();
    let tool_sym = kb.try_resolve_symbol("anthill.stage0.ToolDef")
        .expect("ToolDef should be resolved");
    let results = kb.by_functor(tool_sym);
    // project.anthill imports cargo-build, cargo-test, cargo-clippy + tools.anthill defines lint-all
    assert!(results.len() >= 1, "expected at least 1 ToolDef fact, got {}", results.len());
}
