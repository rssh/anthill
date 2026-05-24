/// Integration tests for term serialization (TOML/JSON ↔ KB terms).

use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, FileSourceResolver};
use anthill_core::parse;
use anthill_core::persistence::term_ser;
use anthill_core::persistence::print::TermPrinter;

use smallvec::SmallVec;

// ── Helpers ─────────────────────────────────────────────────────

/// Build a KB with a simple entity definition for testing.
/// Defines: sort Status { entity Open, entity Closed }
///          sort Task { entity Task(id: String, status: Status, tags: List) }
fn build_test_kb() -> KnowledgeBase {
    let source = r#"
namespace test

sort Status {
    entity Open
    entity Closed
    entity InProgress
}

sort Acceptance {
    entity ToolPasses(tool: String)
    entity Compiles(path: String)
    entity Verified(at: String, by: String)
}

sort Task {
    entity Task(id: String, description: String, status: Status, tags: List[String])
}

sort Project {
    entity Project(name: String, language: String)
}
end
"#;

    let parsed = parse::parse(source).expect("test source should parse");
    let mut kb = KnowledgeBase::new();
    let resolver = FileSourceResolver::new(vec![
        std::path::PathBuf::from("../../stdlib"),
    ]);
    let refs = vec![&parsed];
    let _ = load::load_all(&mut kb, &refs, &resolver);
    kb
}

// ── Primitive tests ─────────────────────────────────────────────

#[test]
fn load_toml_primitives() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[meta]
entity = "test.Project"

[data]
name = "my-app"
language = "rust"
"#;

    let count = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect("load_toml should succeed");
    assert_eq!(count, 1);

    // Query by functor
    let project_sym = kb.try_resolve_symbol("test.Project")
        .expect("Project should be resolved");
    let results = kb.by_functor(project_sym);
    assert_eq!(results.len(), 1);

    let head = kb.rule_head(results[0]);
    let printer = TermPrinter::new(&kb);
    let text = printer.print_term(head);
    assert!(text.contains("my-app"), "expected 'my-app' in: {text}");
}

#[test]
fn load_json_primitives() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let json_src = r#"{
        "meta": { "entity": "test.Project" },
        "data": { "name": "my-app", "language": "rust" }
    }"#;

    let count = term_ser::load_json(&mut kb, json_src, domain)
        .expect("load_json should succeed");
    assert_eq!(count, 1);
}

#[test]
fn load_toml_int_float_bool() {
    let mut kb = KnowledgeBase::new();

    // Register a simple entity with numeric fields
    let src = r#"
namespace test
sort Nums { entity Nums(x: Int, y: Float, flag: Bool) }
end
"#;
    let parsed = parse::parse(src).expect("parse");
    let resolver = load::NullResolver;
    let _ = load::load_all(&mut kb, &[&parsed], &resolver);

    let domain = kb.make_name_term("test_domain");
    let toml_src = r#"
[meta]
entity = "test.Nums"

[data]
x = 42
y = 3.14
flag = true
"#;

    let count = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect("load int/float/bool");
    assert_eq!(count, 1);

    let nums_sym = kb.try_resolve_symbol("test.Nums")
        .expect("Nums should be resolved");
    let results = kb.by_functor(nums_sym);
    assert_eq!(results.len(), 1);
}

// ── List tests ──────────────────────────────────────────────────

#[test]
fn load_toml_list() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[meta]
entity = "test.Task"

[data]
id = "T-001"
description = "Test task"
status = "Open"
tags = ["rust", "core"]
"#;

    let count = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect("load_toml with list should succeed");
    assert_eq!(count, 1);

    let task_sym = kb.try_resolve_symbol("test.Task")
        .expect("Task should be resolved");
    let results = kb.by_functor(task_sym);
    assert_eq!(results.len(), 1);

    let printer = TermPrinter::new(&kb);
    let text = printer.print_term(kb.rule_head(results[0]));
    assert!(text.contains("cons"), "expected cons-list in: {text}");
}

// ── Multiple entries ────────────────────────────────────────────

#[test]
fn load_toml_multiple_entries() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[meta]
entity = "test.Task"

[[data]]
id = "T-001"
description = "First"
status = "Open"
tags = []

[[data]]
id = "T-002"
description = "Second"
status = "Closed"
tags = ["urgent"]
"#;

    let count = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect("load multiple entries");
    assert_eq!(count, 2);

    let task_sym = kb.try_resolve_symbol("test.Task")
        .expect("Task should be resolved");
    let results = kb.by_functor(task_sym);
    assert_eq!(results.len(), 2);
}

// ── Constructors with fields ────────────────────────────────────

#[test]
fn load_toml_constructor_with_fields() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[meta]
entity = "test.Task"

[data]
id = "T-001"
description = "Test"
status = "Open"
tags = [{ ToolPasses = "cargo-test" }, { Compiles = "src" }]
"#;

    let count = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect("load with constructors");
    assert_eq!(count, 1);
}

// ── Variable handling ───────────────────────────────────────────

#[test]
fn load_toml_variables() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[meta]
entity = "test.Task"

[data]
id = "?task_id"
description = "?desc"
status = "?s"
tags = []
"#;

    let count = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect("load with variables");
    assert_eq!(count, 1);

    let task_sym = kb.try_resolve_symbol("test.Task")
        .expect("Task resolved");
    let results = kb.by_functor(task_sym);
    assert_eq!(results.len(), 1);

    let head = kb.rule_head(results[0]);
    let printer = TermPrinter::new(&kb);
    let text = printer.print_term(head);
    assert!(text.contains("?task_id"), "expected variable in: {text}");
}

#[test]
fn load_toml_escaped_variable() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[meta]
entity = "test.Project"

[data]
name = "\\?not-a-variable"
language = "rust"
"#;

    let count = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect("load escaped variable");
    assert_eq!(count, 1);

    let project_sym = kb.try_resolve_symbol("test.Project")
        .expect("Project resolved");
    let results = kb.by_functor(project_sym);
    assert_eq!(results.len(), 1);

    let head = kb.rule_head(results[0]);
    let printer = TermPrinter::new(&kb);
    let text = printer.print_term(head);
    // Should contain the literal "?not-a-variable" as a string, not a logic variable
    assert!(text.contains("\"?not-a-variable\""), "expected quoted escaped string in: {text}");
}

// ── JSON tests ──────────────────────────────────────────────────

#[test]
fn load_json_full_envelope() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let json_src = r#"{
        "meta": { "entity": "test.Task" },
        "data": [
            {
                "id": "T-001",
                "description": "First task",
                "status": "Open",
                "tags": ["rust"]
            },
            {
                "id": "T-002",
                "description": "Second task",
                "status": "Closed",
                "tags": []
            }
        ]
    }"#;

    let count = term_ser::load_json(&mut kb, json_src, domain)
        .expect("load JSON envelope");
    assert_eq!(count, 2);
}

// ── Multi-section tests ─────────────────────────────────────────

#[test]
fn load_toml_multi_section() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[project.meta]
entity = "test.Project"

[project.data]
name = "my-app"
language = "rust"

[tasks.meta]
entity = "test.Task"

[[tasks.data]]
id = "T-001"
description = "Do stuff"
status = "Open"
tags = []
"#;

    let count = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect("load multi-section");
    assert_eq!(count, 2, "should load 1 project + 1 task");

    let project_sym = kb.try_resolve_symbol("test.Project")
        .expect("Project resolved");
    let task_sym = kb.try_resolve_symbol("test.Task")
        .expect("Task resolved");
    assert_eq!(kb.by_functor(project_sym).len(), 1);
    assert_eq!(kb.by_functor(task_sym).len(), 1);
}

// ── Serializer tests ────────────────────────────────────────────

/// Build a Project("my-app", "rust") fact and return its RuleId.
fn assert_project_fact(kb: &mut KnowledgeBase, domain: TermId) -> anthill_core::kb::RuleId {
    let project_sym = kb.try_resolve_symbol("test.Project")
        .expect("Project resolved");
    let name_sym = kb.intern("name");
    let lang_sym = kb.intern("language");
    let name_val = kb.alloc(Term::Const(Literal::String("my-app".into())));
    let lang_val = kb.alloc(Term::Const(Literal::String("rust".into())));

    let mut named_args: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    named_args.push((name_sym, name_val));
    named_args.push((lang_sym, lang_val));
    named_args.sort_by_key(|&(sym, _)| sym.index());

    let term = kb.alloc(Term::Fn {
        functor: project_sym,
        pos_args: SmallVec::new(),
        named_args,
    });

    let sort = kb.make_name_term("Fact");
    kb.assert_fact(term, sort, domain, None)
}

#[test]
fn serialize_simple_facts_toml() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");
    let rid = assert_project_fact(&mut kb, domain);

    let toml_str = term_ser::serialize_toml(&kb, "test.Project", &[rid])
        .expect("serialize_toml should succeed");
    assert!(toml_str.contains("my-app"), "expected 'my-app' in: {toml_str}");
    assert!(toml_str.contains("rust"), "expected 'rust' in: {toml_str}");
    assert!(toml_str.contains("[meta]"), "expected [meta] in: {toml_str}");
}

#[test]
fn serialize_simple_facts_json() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");
    let rid = assert_project_fact(&mut kb, domain);

    let json_str = term_ser::serialize_json(&kb, "test.Project", &[rid])
        .expect("serialize_json should succeed");
    assert!(json_str.contains("my-app"), "expected 'my-app' in: {json_str}");
    assert!(json_str.contains("\"meta\""), "expected 'meta' in: {json_str}");
}

// ── Round-trip tests ────────────────────────────────────────────

#[test]
fn round_trip_toml() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[meta]
entity = "test.Project"

[data]
name = "my-app"
language = "rust"
"#;

    let count = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect("initial load");
    assert_eq!(count, 1);

    // Find the fact
    let project_sym = kb.try_resolve_symbol("test.Project")
        .expect("Project resolved");
    let facts = kb.by_functor(project_sym);
    assert_eq!(facts.len(), 1);

    // Serialize
    let toml_out = term_ser::serialize_toml(&kb, "test.Project", &facts)
        .expect("serialize");

    // Reload into fresh KB
    let mut kb2 = build_test_kb();
    let domain2 = kb2.make_name_term("test_domain2");
    let count2 = term_ser::load_toml(&mut kb2, &toml_out, domain2)
        .expect("reload");
    assert_eq!(count2, 1);

    let project_sym2 = kb2.try_resolve_symbol("test.Project")
        .expect("Project resolved in kb2");
    let facts2 = kb2.by_functor(project_sym2);
    assert_eq!(facts2.len(), 1);
}

#[test]
fn round_trip_json() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let json_src = r#"{
        "meta": { "entity": "test.Project" },
        "data": { "name": "round-trip", "language": "anthill" }
    }"#;

    let count = term_ser::load_json(&mut kb, json_src, domain)
        .expect("initial load");
    assert_eq!(count, 1);

    let project_sym = kb.try_resolve_symbol("test.Project")
        .expect("Project resolved");
    let facts = kb.by_functor(project_sym);

    let json_out = term_ser::serialize_json(&kb, "test.Project", &facts)
        .expect("serialize");

    let mut kb2 = build_test_kb();
    let domain2 = kb2.make_name_term("test_domain2");
    let count2 = term_ser::load_json(&mut kb2, &json_out, domain2)
        .expect("reload");
    assert_eq!(count2, 1);
}

// ── Error cases ─────────────────────────────────────────────────

#[test]
fn load_toml_missing_meta() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[data]
name = "oops"
"#;

    let result = term_ser::load_toml(&mut kb, toml_src, domain);
    assert!(result.is_err(), "should fail without meta");
}

#[test]
fn load_toml_unknown_entity() {
    let mut kb = build_test_kb();
    let domain = kb.make_name_term("test_domain");

    let toml_src = r#"
[meta]
entity = "totally.bogus.XyzzyFoo42"

[data]
x = 1
"#;

    let result = term_ser::load_toml(&mut kb, toml_src, domain);
    assert!(result.is_err(), "should fail with unknown entity");
}
