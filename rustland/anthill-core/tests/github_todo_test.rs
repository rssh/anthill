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

/// Load stdlib + github-todo example + an extra inline source (additional
/// `anthill.stage0` facts). Used by the WI-433 coverage test to add a dependent
/// whose deps are Verified without mutating the shared example fixture.
fn load_github_todo_kb_with_extra(extra: &str) -> KnowledgeBase {
    let stdlib_dir = common::stdlib_dir();
    let example_dir = common::examples_dir().join("github-todo");

    let mut files = common::collect_anthill_files(&stdlib_dir);
    files.extend(common::collect_anthill_files(&example_dir));

    let mut parsed: Vec<_> = files.iter()
        .map(|path| {
            let source = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            parse::parse(&source)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", path.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra source"));

    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|errs| {
            for e in &errs { eprintln!("Load error: {e}"); }
            panic!("load failed with {} errors", errs.len());
        });
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

/// Resolve a named query var's binding in one solution to its term, loudly.
fn binding_term(
    kb: &KnowledgeBase,
    query: TermId,
    sol: &anthill_core::kb::resolve::Solution,
    var_name: &str,
) -> TermId {
    let query_vars = kb.collect_vars(query);
    let var = query_vars.iter().find(|v| kb.resolve_sym(v.name()) == var_name)
        .unwrap_or_else(|| panic!("query has no var ?{var_name}"));
    sol.subst.resolve_as_value(*var).map(|v| v.expect_term())
        .unwrap_or_else(|| panic!("?{var_name} unbound in solution"))
}

/// Collect the `?id` bindings of every solution, sorted. Loud: a solution
/// whose `?id` is unbound or not a String literal panics rather than being
/// silently dropped from the comparison.
fn sorted_ids(kb: &KnowledgeBase, query: TermId, solutions: &[anthill_core::kb::resolve::Solution]) -> Vec<String> {
    let mut ids: Vec<String> = solutions.iter()
        .map(|sol| {
            let t = binding_term(kb, query, sol, "id");
            extract_string(kb, t).unwrap_or_else(|| panic!("?id is not a String literal"))
        })
        .collect();
    ids.sort();
    ids
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
    let results = kb.rules_by_functor(wi_sym);
    // 4 work items + 1 entity definition = at least 4 facts with WorkItem functor
    assert!(results.len() >= 4, "expected at least 4 WorkItem facts, got {}", results.len());
}

#[test]
fn project_loaded() {
    let kb = load_github_todo_kb();
    let proj_sym = kb.try_resolve_symbol("anthill.stage0.Project")
        .expect("Project should be resolved");
    let results = kb.rules_by_functor(proj_sym);
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
    assert_eq!(
        sorted_ids(&kb, query, &solutions),
        vec!["WI-AUTH-001"],
        "only WI-AUTH-001 has no dependencies",
    );
}

/// WI-433 coverage hole: the example only had claimable items with EMPTY deps,
/// so the positional-vs-named never-match (a dependent with VERIFIED deps wrongly
/// rejected) was invisible. Add a Verified dep + a dependent and assert the
/// dependent is claimable. The dep's status is written POSITIONALLY
/// (`Verified("…")`) to exercise the WI-433 desugar against the named
/// `Verified(at: ?)` rule pattern.
#[test]
fn wi433_claimable_with_verified_deps() {
    let extra = r#"
namespace anthill.stage0
  fact WorkItem(id: "WI-DEP-V", description: "a verified dependency",
                depends_on: [], status: Verified("2026-06-17"))
  fact WorkItem(id: "WI-CHILD", description: "depends on a verified item",
                depends_on: ["WI-DEP-V"], status: Open)
end
"#;
    let mut kb = load_github_todo_kb_with_extra(extra);
    let query = make_query2(&mut kb, "anthill.stage0.workflow.claimable", "id", "desc");
    let solutions = kb.resolve(&[query], &resolve_config());
    let ids = sorted_ids(&kb, query, &solutions);

    assert!(
        ids.contains(&"WI-CHILD".to_string()),
        "a dependent whose deps are all Verified must be claimable; claimable = {ids:?}",
    );
    // The dep is itself Verified (not Open), so it is NOT claimable.
    assert!(
        !ids.contains(&"WI-DEP-V".to_string()),
        "a Verified item is not claimable; claimable = {ids:?}",
    );
}

#[test]
fn blocked_resolves_three() {
    let mut kb = load_github_todo_kb();
    let query = make_query2(&mut kb, "anthill.stage0.workflow.blocked", "id", "desc");
    let solutions = kb.resolve(&[query], &resolve_config());
    assert_eq!(
        sorted_ids(&kb, query, &solutions),
        vec!["WI-AUTH-002", "WI-AUTH-003", "WI-AUTH-004"],
        "3 items have unverified dependencies",
    );
}

/// WI-717: an omitted OPTIONAL entity field is stored as `none()` (WI-716),
/// so the workflow rules must give it the none() reading — an omitted
/// `depends_on` means "no dependencies", an omitted `description` leaves the
/// item listed (with `none` as its description) — instead of dropping the
/// item from every view because none() matches neither the `nil()`/`cons(…)`
/// nor the `some(?)` shapes.
///
/// The exact-set assertions also pin the WI-716 none()-fill itself for facts
/// whose entity is declared in ANOTHER file: a var-filled optional would
/// unify BOTH `description_view` cases (and both deps rules) and duplicate
/// the item's solutions.
const WI717_OMITTED_OPTIONALS: &str = r#"
namespace anthill.stage0
  fact WorkItem(id: "WI-NODEPS", description: "omits depends_on entirely",
                acceptance: [], status: Open)
  fact WorkItem(id: "WI-NODESC", acceptance: [], depends_on: [], status: Open)
  fact WorkItem(id: "WI-DELIV-NODESC", acceptance: [], depends_on: [],
                status: Delivered(agent: "claude", at: "2026-07-15"))
end
"#;

#[test]
fn wi717_omitted_optionals_stay_claimable() {
    let mut kb = load_github_todo_kb_with_extra(WI717_OMITTED_OPTIONALS);
    let query = make_query2(&mut kb, "anthill.stage0.workflow.claimable", "id", "desc");
    let solutions = kb.resolve(&[query], &resolve_config());
    assert_eq!(
        sorted_ids(&kb, query, &solutions),
        vec!["WI-AUTH-001", "WI-NODEPS", "WI-NODESC"],
        "an item omitting depends_on (WI-NODEPS) or description (WI-NODESC) \
         must be claimable exactly once, alongside the baseline WI-AUTH-001",
    );
}

#[test]
fn wi717_omitted_description_still_open_with_none_desc() {
    let mut kb = load_github_todo_kb_with_extra(WI717_OMITTED_OPTIONALS);
    let query = make_query2(&mut kb, "anthill.stage0.workflow.open_item", "id", "desc");
    let solutions = kb.resolve(&[query], &resolve_config());
    assert_eq!(
        sorted_ids(&kb, query, &solutions),
        vec!["WI-AUTH-001", "WI-AUTH-002", "WI-AUTH-003", "WI-AUTH-004",
             "WI-NODEPS", "WI-NODESC"],
        "the 4 example items + WI-NODEPS + WI-NODESC, each exactly once",
    );

    // An omitted description surfaces as the ground `none`, never an unbound
    // var; a present one unwraps to its term (pins the some-case of
    // description_view's nonlinear head, not just the ground none-case).
    let find = |id: &str| {
        solutions.iter()
            .find(|sol| {
                let t = binding_term(&kb, query, sol, "id");
                extract_string(&kb, t).as_deref() == Some(id)
            })
            .unwrap_or_else(|| panic!("no solution for {id}"))
    };
    let nodesc_desc = binding_term(&kb, query, find("WI-NODESC"), "desc");
    assert_eq!(
        TermPrinter::new(&kb).print_term(nodesc_desc), "none",
        "an omitted description surfaces as none(), not a leaked var",
    );
    let nodeps_desc = binding_term(&kb, query, find("WI-NODEPS"), "desc");
    assert_eq!(
        extract_string(&kb, nodeps_desc).as_deref(),
        Some("omits depends_on entirely"),
        "a present description unwraps to its term",
    );
}

#[test]
fn wi717_needs_review_lists_omitted_description() {
    let mut kb = load_github_todo_kb_with_extra(WI717_OMITTED_OPTIONALS);
    let query = make_query2(&mut kb, "anthill.stage0.workflow.needs_review", "id", "desc");
    let solutions = kb.resolve(&[query], &resolve_config());
    assert_eq!(
        sorted_ids(&kb, query, &solutions),
        vec!["WI-DELIV-NODESC"],
        "a Delivered item whose description is omitted still shows up for review",
    );
}

#[test]
fn wi717_omitted_optionals_are_not_blocked() {
    let mut kb = load_github_todo_kb_with_extra(WI717_OMITTED_OPTIONALS);
    let query = make_query2(&mut kb, "anthill.stage0.workflow.blocked", "id", "desc");
    let solutions = kb.resolve(&[query], &resolve_config());
    assert_eq!(
        sorted_ids(&kb, query, &solutions),
        vec!["WI-AUTH-002", "WI-AUTH-003", "WI-AUTH-004"],
        "items with omitted optionals have no unmet deps — blocked stays the \
         3 example items with real unverified dependencies",
    );
}

#[test]
fn feedback_loaded() {
    let kb = load_github_todo_kb();
    let fb_sym = kb.try_resolve_symbol("anthill.stage0.Feedback")
        .expect("Feedback should be resolved");
    let results = kb.rules_by_functor(fb_sym);
    assert!(results.len() >= 2, "expected at least 2 Feedback facts, got {}", results.len());
}

#[test]
fn tooldef_loaded() {
    let kb = load_github_todo_kb();
    let tool_sym = kb.try_resolve_symbol("anthill.stage0.ToolDef")
        .expect("ToolDef should be resolved");
    let results = kb.rules_by_functor(tool_sym);
    // project.anthill imports cargo-build, cargo-test, cargo-clippy + tools.anthill defines lint-all
    assert!(results.len() >= 1, "expected at least 1 ToolDef fact, got {}", results.len());
}

/// WI-501: a fact serialized to a persisted store (TOML) and reloaded must
/// hash-cons-match the SAME fact loaded from .anthill source. The serializer is
/// lossy without types (it strips `some(value: x)` → `x`, drops `none()`, and
/// renders nullary entities like `Open` as bare strings); the type-directed
/// deserializer rebuilds each field from its declared type so the round-trip is
/// faithful. Uses a fact with all fields explicitly valued. (When this test was
/// written an omitted field meant a fresh var with a distinct VarId, which could
/// never hash-cons-match; since WI-716 an omitted OPTIONAL fills with ground
/// none() — only omitted REQUIRED fields still var-fill.)
#[test]
fn wi501_workitem_round_trips_through_store() {
    use anthill_core::persistence::term_ser;
    let extra = r#"
namespace anthill.stage0
  fact WorkItem(id: "WI-RT", description: some(value: "round trip"),
                context: none, acceptance: [], depends_on: none,
                generates: none, requires_capability: none, status: Open)
end
"#;
    let mut kb = load_github_todo_kb_with_extra(extra);
    let wi = kb.try_resolve_symbol("anthill.stage0.WorkItem").unwrap();

    let printer = TermPrinter::new(&kb);
    let before: Vec<_> = kb.rules_by_functor(wi).to_vec();
    let src_rid = *before.iter()
        .find(|r| printer.print_term(kb.rule_head(**r)).contains("WI-RT"))
        .expect("source WI-RT fact present");
    let src_head = kb.rule_head(src_rid);
    drop(printer);

    // Serialize just this fact, then reload it into the same KB.
    let toml = term_ser::serialize_toml(&kb, "anthill.stage0.WorkItem", &[src_rid])
        .expect("serialize");
    let domain = kb.make_name_term("store");
    let n = term_ser::load_toml(&mut kb, &toml, domain).expect("reload");
    assert_eq!(n, 1);

    let after: Vec<_> = kb.rules_by_functor(wi).to_vec();
    let de_rid = *after.iter().find(|r| !before.contains(*r)).expect("reloaded fact");
    let de_head = kb.rule_head(de_rid);

    let printer = TermPrinter::new(&kb);
    assert_eq!(
        src_head, de_head,
        "reloaded fact must hash-cons-match the source-loaded form (WI-501).\n\
         source:   {}\n  reloaded: {}",
        printer.print_term(src_head),
        printer.print_term(de_head),
    );
}

/// WI-501: a persisted entity missing a REQUIRED (non-Option) field is store
/// corruption — the deserializer fails loudly rather than building a silent
/// partial fact. (An absent Option field is fine — restored to none().)
#[test]
fn wi501_missing_required_field_errors_loudly() {
    use anthill_core::persistence::term_ser;
    let mut kb = load_github_todo_kb();
    let domain = kb.make_name_term("store");
    // Omit the required `id` field; acceptance + status present, options omitted.
    let toml_src = r#"
[meta]
entity = "anthill.stage0.WorkItem"

[data]
acceptance = []
status = "Open"
"#;
    let errs = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect_err("missing required field must error");
    assert!(
        errs.iter().any(|e| matches!(e, term_ser::SerError::MissingField { field, .. } if field == "id")),
        "expected MissingField for 'id', got: {errs:?}"
    );
}
