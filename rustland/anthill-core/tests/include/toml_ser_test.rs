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
    let results = kb.rules_by_functor(project_sym);
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
sort Nums { entity Nums(x: Int64, y: Float, flag: Bool) }
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
    let results = kb.rules_by_functor(nums_sym);
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
    let results = kb.rules_by_functor(task_sym);
    assert_eq!(results.len(), 1);

    let printer = TermPrinter::new(&kb);
    let text = printer.print_term(kb.rule_head(results[0]));
    // Ground cons/nil spines print as list literals (the round-trippable
    // form — a bare `nil`/`cons` print reloads as a name reference that
    // no longer unifies with list patterns; see TermPrinter).
    assert!(text.contains("[\"rust\", \"core\"]"), "expected list literal in: {text}");
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
    let results = kb.rules_by_functor(task_sym);
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
    let results = kb.rules_by_functor(task_sym);
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
    let results = kb.rules_by_functor(project_sym);
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
    assert_eq!(kb.rules_by_functor(project_sym).len(), 1);
    assert_eq!(kb.rules_by_functor(task_sym).len(), 1);
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

#[test]
fn serialize_json_list_field_has_no_trailing_nil() {
    // WI-511: a nullary `nil` list terminator is the canonical `Ref(nil)`.
    // `cons_to_json_array` must recognize it as the spine end, not append the
    // bare `nil` cell as a stray final array element (which it did when it
    // only matched the `Fn{nil}` form).
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
    term_ser::load_toml(&mut kb, toml_src, domain).expect("load_toml");
    let task_sym = kb.try_resolve_symbol("test.Task").expect("Task resolved");
    let facts = kb.rules_by_functor(task_sym);
    assert_eq!(facts.len(), 1);

    let json_str = term_ser::serialize_json(&kb, "test.Task", &facts)
        .expect("serialize_json should succeed");
    // The fixture's strings ("T-001", "Test task", "Open", "rust", "core")
    // contain no "nil"; a stray terminator element would surface as one.
    assert!(json_str.contains("rust") && json_str.contains("core"),
        "expected the list elements in: {json_str}");
    assert!(!json_str.contains("nil"),
        "tags array must end at the `nil` terminator, not append it as an \
         element; got: {json_str}");
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
    let facts = kb.rules_by_functor(project_sym);
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
    let facts2 = kb2.rules_by_functor(project_sym2);
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
    let facts = kb.rules_by_functor(project_sym);

    let json_out = term_ser::serialize_json(&kb, "test.Project", &facts)
        .expect("serialize");

    let mut kb2 = build_test_kb();
    let domain2 = kb2.make_name_term("test_domain2");
    let count2 = term_ser::load_json(&mut kb2, &json_out, domain2)
        .expect("reload");
    assert_eq!(count2, 1);
}

// ── WI-498: canonicalization across the persistence boundary ────

/// A fact reloaded from a persisted store must hash-cons-match the SAME fact
/// loaded from .anthill source, even when the entity's declared field order
/// differs from symbol interning order. The loader canonicalizes source facts
/// to declared field order and the discrim matcher descends named keys
/// positionally, so the deserializer must canonicalize the same way (via the
/// `make_entity_term` funnel) — not sort by `Symbol::index()`.
#[test]
fn wi498_deserialized_entity_matches_source_loaded_form() {
    // Top-level entities (like the github-todo `anthill.stage0` domain) so the
    // qualified entity name resolves to a functor carrying registered field
    // names — the deserializer's `entity_field_names` lookup then sees declared
    // order. `aafield` is interned first (in `Pre`), so it gets a LOWER symbol
    // index than `zzfield` (first seen in `Rec`); but `Rec` DECLARES `zzfield`
    // first, so declared order [zzfield, aafield] is the REVERSE of index order
    // [aafield, zzfield] — the same shape as the real `WorkItem` entity, whose
    // `id` is declared first but interned after `description`/`status`.
    let src = r#"
namespace test
entity Pre(aafield: String)
entity Rec(zzfield: String, aafield: String)
fact Rec(zzfield: "z", aafield: "a")
end
"#;
    let parsed = parse::parse(src).expect("parse");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &[&parsed], &load::NullResolver);

    let rec_sym = kb.try_resolve_symbol("test.Rec").expect("Rec resolved");

    // Precondition: the fixture must actually exercise the bug — declared field
    // order must differ from interning order, else the test is a silent no-op.
    let declared = kb
        .entity_field_names(rec_sym)
        .expect("Rec has declared fields")
        .to_vec();
    assert_eq!(declared.len(), 2);
    assert!(
        declared[0].index() > declared[1].index(),
        "fixture must produce interning order != declared order to exercise \
         WI-498 (declared[0]={}, declared[1]={}); adjust field names if \
         interning changed",
        declared[0].index(),
        declared[1].index(),
    );

    // The source-loaded data fact `Rec(zzfield:"z", aafield:"a")`, canonicalized
    // to declared field order by the loader. (Located by its "z" payload; since
    // WI-515 `rules_by_functor` returns only data facts — the entity SCHEMA fact
    // that used to ride along is no longer asserted.)
    let printer = TermPrinter::new(&kb);
    let before = kb.rules_by_functor(rec_sym);
    let source_rid = *before
        .iter()
        .find(|r| printer.print_term(kb.rule_head(**r)).contains("\"z\""))
        .expect("source data fact present");
    let source_head = kb.rule_head(source_rid);
    // Confirm the loader canonicalized the source fact to DECLARED order
    // (zzfield before aafield) — otherwise the comparison below would pass
    // vacuously (both sides in index order).
    let printed = printer.print_term(source_head);
    assert!(
        printed.find("zzfield") < printed.find("aafield"),
        "source fact must be in declared order zzfield-then-aafield: {printed}"
    );
    drop(printer);

    // Deserialize the SAME entity from a persisted (TOML) store, with the
    // fields written in NON-declared order to stress the canonicalization.
    let domain = kb.make_name_term("persisted");
    let toml_src = r#"
[meta]
entity = "test.Rec"

[data]
aafield = "a"
zzfield = "z"
"#;
    let count = term_ser::load_toml(&mut kb, toml_src, domain).expect("reload from store");
    assert_eq!(count, 1);

    let after = kb.rules_by_functor(rec_sym);
    let deser_rid = *after
        .iter()
        .find(|r| !before.contains(*r))
        .expect("deserialized fact present");
    let deser_head = kb.rule_head(deser_rid);

    // Hash-consing means structurally identical terms share one TermId; with
    // the WI-498 fix the deserialized term canonicalizes to declared order and
    // is the SAME term as the source-loaded fact. Before the fix it sorted by
    // index order and produced a DISTINCT, non-matching term.
    assert_eq!(
        source_head, deser_head,
        "reloaded term must hash-cons-match the source-loaded form (WI-498)"
    );
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

// ── WI-503: residual round-trip gaps left by WI-501 ─────────────

/// Load `src` (referencing the stdlib) into a fresh KB. Helper for the WI-503
/// fixtures, which need custom sorts plus the prelude `Option`/`List`.
fn load_kb_with_stdlib(src: &str) -> KnowledgeBase {
    let parsed = parse::parse(src).expect("test source should parse");
    let mut kb = KnowledgeBase::new();
    let resolver = FileSourceResolver::new(vec![std::path::PathBuf::from("../../stdlib")]);
    let _ = load::load_all(&mut kb, &[&parsed], &resolver);
    kb
}

/// WI-503 gap (1): `some(none())` — a present-but-empty `Option[T = Option[U]]` —
/// cannot be represented in the flattened TOML/JSON format. The inner `none`
/// serializes to JSON null, the field is dropped, and reload restores `none()`
/// (absent), silently losing the present/absent distinction. The serializer must
/// error loudly rather than round-trip to the wrong value.
#[test]
fn serialize_nested_option_some_none_errors_loudly() {
    let mut kb = load_kb_with_stdlib(r#"
namespace test
sort Box { entity Box(inner: Option[T = Option[T = Int]]) }
end
"#);

    // Build `inner = some(value: none())` directly (the lossy shape).
    let none_sym = kb.try_resolve_symbol("anthill.prelude.Option.none").expect("Option.none");
    let some_sym = kb.try_resolve_symbol("anthill.prelude.Option.some").expect("Option.some");
    let value_sym = kb.intern("value");
    let none_t = kb.alloc(Term::Ref(none_sym));
    let mut some_named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    some_named.push((value_sym, none_t));
    let some_none = kb.alloc(Term::Fn {
        functor: some_sym,
        pos_args: SmallVec::new(),
        named_args: some_named,
    });

    let box_sym = kb.try_resolve_symbol("test.Box").expect("Box resolved");
    let inner_sym = kb.intern("inner");
    let mut box_named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    box_named.push((inner_sym, some_none));
    let box_term = kb.alloc(Term::Fn {
        functor: box_sym,
        pos_args: SmallVec::new(),
        named_args: box_named,
    });
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("d");
    let rid = kb.assert_fact(box_term, sort, domain, None);

    let err = term_ser::serialize_json(&kb, "test.Box", &[rid])
        .expect_err("some(none()) must error loudly, not silently collapse");
    assert!(
        matches!(err, term_ser::SerError::InvalidValue(_)),
        "expected InvalidValue for nested-Option collapse, got: {err:?}"
    );
}

/// WI-503 gap (2): the serializer detects prelude `List`/`Option` by QUALIFIED
/// name. A user entity literally named `cons` in another namespace is NOT a list;
/// the old short-name check flattened it to an empty array, silently dropping its
/// fields. It must serialize as an ordinary entity instead.
#[test]
fn serialize_user_entity_named_cons_is_not_flattened_as_list() {
    let mut kb = load_kb_with_stdlib(r#"
namespace test
sort Holder { entity Holder(c: Pair, tags: List[Int]) }
sort Pair { entity cons(x: Int, y: Int) }
end
"#);

    let cons_sym = kb.try_resolve_symbol("test.Pair.cons").expect("test.Pair.cons resolved");
    assert_ne!(
        kb.qualified_name_of(cons_sym), "anthill.prelude.List.cons",
        "fixture must use a DISTINCT user `cons`, not the prelude one",
    );

    let x_sym = kb.intern("x");
    let y_sym = kb.intern("y");
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let two = kb.alloc(Term::Const(Literal::Int(2)));
    let mut cons_named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    cons_named.push((x_sym, one));
    cons_named.push((y_sym, two));
    cons_named.sort_by_key(|&(s, _)| s.index());
    let cons_term = kb.alloc(Term::Fn {
        functor: cons_sym,
        pos_args: SmallVec::new(),
        named_args: cons_named,
    });

    let holder_sym = kb.try_resolve_symbol("test.Holder").expect("Holder resolved");
    let c_sym = kb.intern("c");
    let mut holder_named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    holder_named.push((c_sym, cons_term));
    let holder_term = kb.alloc(Term::Fn {
        functor: holder_sym,
        pos_args: SmallVec::new(),
        named_args: holder_named,
    });
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("d");
    let rid = kb.assert_fact(holder_term, sort, domain, None);

    let json = term_ser::serialize_json(&kb, "test.Holder", &[rid]).expect("serialize");
    assert!(
        json.contains("\"cons\""),
        "user `cons` entity must keep its name (not be flattened as a list), got: {json}"
    );
    assert!(
        json.contains("\"x\"") && json.contains("\"y\"") && json.contains('1') && json.contains('2'),
        "user `cons` fields must survive serialization, got: {json}"
    );
}

/// WI-503 gap (3): a multi-field constructor given a non-object scalar payload
/// (a foreign / hand-authored store — our serializer never emits this) cannot
/// fill its named fields. The old positional fallback built a `Term::Fn` that
/// never discrim-matched the named pattern; the deserializer must error loudly.
#[test]
fn deserialize_multifield_ctor_scalar_payload_errors_loudly() {
    let mut kb = load_kb_with_stdlib(r#"
namespace test
sort Rec { entity Rec(outcome: Outcome) }
sort Outcome { entity Verified(at: String, by: String)  entity Pending }
end
"#);

    let domain = kb.make_name_term("d");
    // `Verified` needs `at` + `by`; a bare scalar can't supply them.
    let json_src = r#"{
        "meta": { "entity": "test.Rec" },
        "data": { "outcome": { "Verified": "2027-01-01" } }
    }"#;
    let errs = term_ser::load_json(&mut kb, json_src, domain)
        .expect_err("multi-field ctor with a scalar payload must error loudly");
    assert!(
        errs.iter().any(|e| matches!(e, term_ser::SerError::InvalidValue(_))),
        "expected InvalidValue for foreign positional payload, got: {errs:?}"
    );
}
