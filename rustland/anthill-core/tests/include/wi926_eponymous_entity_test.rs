//! WI-926 / §6.3 — a sort's constructor that carries THE SORT'S OWN NAME *is* the
//! sort, so `sort Project { entity Project(…) }` declares ONE symbol.
//!
//! It used to declare two. The sort took the plain qualified name `test.Project`
//! and the constructor the nested `test.Project.Project`, and only the nested one
//! carried a field schema — while every reader of a `Project(…)` FACT HEAD looked
//! at the plain one. Measured before the fix, on
//! `sort Project { entity Project(name: String, language: String) }`:
//!
//! ```text
//! test.Project          kind=Sort   fields=None      <- what a fact head resolves to
//! test.Project.Project  kind=Entity fields=Some(2)   <- where the schema lived
//! ```
//!
//! §6.3 states the sugar `entity Account(…)` and the desugaring
//! `sort Account { entity Account(…) }` are the same declaration. They were not:
//! the sugar produced one symbol WITH a schema, the desugaring two with the schema
//! on the unreachable one. These tests pin the equivalence.

use anthill_core::kb::load::{self, FileSourceResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::persistence::term_ser;

fn load_src(source: &str) -> KnowledgeBase {
    let parsed = parse::parse(source).expect("test source should parse");
    let mut kb = KnowledgeBase::new();
    let resolver = FileSourceResolver::new(vec![std::path::PathBuf::from("../../stdlib")]);
    let _ = load::load_all(&mut kb, &[&parsed], &resolver);
    kb
}

const SRC: &str = r#"
namespace test.wi926
  import anthill.prelude.{String}

  sort Status
    entity Open
    entity Closed
  end

  sort Project
    entity Project(name: String, language: String)
  end

  sort Task
    entity Task(id: String, status: Status)
  end

  sort Person
    entity mk(name: String)
  end

  entity Standalone(a: String)

  fact Task(id: "T-1", status: Open)
end
"#;

// ── The symbol shape ────────────────────────────────────────────

#[test]
fn an_eponymous_constructor_is_the_sort_itself() {
    let kb = load_src(SRC);

    let project = kb
        .try_resolve_symbol("test.wi926.Project")
        .expect("the sort name resolves");
    let fields = kb
        .entity_field_names(project)
        .expect("the eponymous sort carries the entity's field schema");
    let names: Vec<&str> = fields.iter().map(|f| kb.resolve_sym(*f)).collect();
    assert_eq!(names, vec!["name", "language"], "declared field order");

    assert!(
        kb.try_resolve_symbol("test.wi926.Project.Project").is_none(),
        "the nested constructor name must not exist — one written name, one symbol",
    );
}

#[test]
fn a_differently_named_variant_keeps_its_nested_symbol() {
    // The collapse is keyed on the NAME matching, not on being a lone variant:
    // `sort Person { entity mk(…) }` has one constructor under a different name,
    // and it stays a child symbol with the schema on it.
    let kb = load_src(SRC);

    let person = kb.try_resolve_symbol("test.wi926.Person").expect("Person resolves");
    assert!(
        kb.entity_field_names(person).is_none(),
        "a sort whose constructor is named differently carries no schema itself",
    );
    let mk = kb
        .try_resolve_symbol("test.wi926.Person.mk")
        .expect("the differently-named constructor keeps its nested symbol");
    assert_eq!(kb.entity_field_names(mk).map(<[_]>::len), Some(1));
    assert_eq!(kb.constructor_parent_sort(mk), Some(person));

    // Same for a multi-variant sort.
    let status = kb.try_resolve_symbol("test.wi926.Status").expect("Status resolves");
    assert!(kb.try_resolve_symbol("test.wi926.Status.Open").is_some());
    assert!(kb.entity_field_names(status).is_none());
}

#[test]
fn the_sugar_and_the_desugaring_agree() {
    // §6.3's equivalence, as a direct comparison: a free-standing `entity E(…)`
    // and an eponymous `sort E { entity E(…) }` must present the same way — one
    // symbol, carrying the field schema, with no parent sort and no nested twin.
    let kb = load_src(SRC);

    for name in ["test.wi926.Standalone", "test.wi926.Project"] {
        let sym = kb.try_resolve_symbol(name).unwrap_or_else(|| panic!("{name} resolves"));
        assert!(
            kb.entity_field_names(sym).is_some(),
            "{name}: the declaration's schema is on the name that was written",
        );
        assert_eq!(
            kb.constructor_parent_sort(sym),
            None,
            "{name}: an entity that is its own type has no parent sort",
        );
        assert!(
            kb.try_resolve_symbol(&format!("{name}.{}", kb.resolve_sym(sym))).is_none(),
            "{name}: no nested twin",
        );
        assert!(
            kb.is_entity_constructor(sym),
            "{name}: an application of it constructs",
        );
    }
}

#[test]
fn an_eponymous_data_sort_is_not_an_abstract_spec() {
    // `sort_has_constructors` scans for direct CHILD symbols of kind Entity, and
    // an eponymous constructor is not a child. Left alone it would answer `false`
    // and the provider-info loader (WI-407) would read a data sort as a spec.
    let kb = load_src(SRC);
    let project = kb.try_resolve_symbol("test.wi926.Project").expect("Project resolves");
    assert!(
        kb.sort_has_constructors(project),
        "an eponymous sort is constructor-shaped DATA, not an abstract spec",
    );
}

// ── The persistence half: what the split actually broke ─────────

/// THE CONTROL. A row loaded from a persisted store must hash-cons-match the SAME
/// row loaded from `.anthill` source — WI-498's principle, here on the shape
/// WI-498's own test could not use (it reached for a free-standing `entity`
/// precisely because the sort-body form carried no schema).
///
/// Before WI-926 this failed on the VALUES, not the functor: the section's schema
/// lookup missed, `unwrap_or_default()` handed `load_entry` an EMPTY field list,
/// and WI-501's type-directed reconstruction was skipped entirely — so
/// `status = "Open"` came back as the bare String `"Open"` where the source fact
/// holds the entity `Open`. Measured, same KB:
///
/// ```text
/// source:      Task(id: "T-1", status: Open)
/// persistence: Task(id: "T-2", status: "Open")
/// ```
///
/// Two terms for one datum, and the persisted one never discrim-matches a
/// `Task(status: Open)` pattern.
#[test]
fn a_persisted_row_is_the_same_term_as_its_source_twin() {
    let mut kb = load_src(SRC);
    let task = kb.try_resolve_symbol("test.wi926.Task").expect("Task resolves");

    let before = kb.rules_by_functor(task);
    assert_eq!(before.len(), 1, "the source `fact Task(…)` is the only row so far");
    let source_head = kb.rule_head(before[0]);

    // The SAME datum, through the persistence loader.
    let domain = kb.intern("persisted");
    let toml_src = r#"
[meta]
entity = "test.wi926.Task"

[data]
id = "T-1"
status = "Open"
"#;
    let count = term_ser::load_toml(&mut kb, toml_src, domain).expect("load_toml");
    assert_eq!(count, 1);

    let after = kb.rules_by_functor(task);
    let deser_rid = *after
        .iter()
        .find(|r| !before.contains(*r))
        .expect("the deserialized row is present");
    let deser_head = kb.rule_head(deser_rid);

    // Hash-consing: structurally identical terms share one TermId.
    assert_eq!(
        source_head,
        deser_head,
        "a persisted row must reconstruct to the SAME term as its source twin \
         (source: {}, persisted: {})",
        anthill_core::persistence::print::TermPrinter::new(&kb).print_term(source_head),
        anthill_core::persistence::print::TermPrinter::new(&kb).print_term(deser_head),
    );
}

/// A section naming something with no field schema is a LOUD error. The old
/// `unwrap_or_default()` made it an EMPTY schema instead — which is not a
/// degraded reconstruction but a different one, and it read as "handled".
#[test]
fn a_section_without_a_field_schema_is_refused() {
    let mut kb = load_src(SRC);
    let domain = kb.intern("persisted");

    // A multi-constructor sort has no single row shape to deserialize against.
    let toml_src = r#"
[meta]
entity = "test.wi926.Status"

[data]
whatever = "x"
"#;
    let errs = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect_err("a schema-less section must be refused, not loaded against an empty schema");
    assert!(
        errs.iter().any(|e| matches!(e, term_ser::SerError::NoFieldSchema { .. })),
        "expected NoFieldSchema, got: {errs:?}",
    );
    // The diagnostic names the constructors, so the remedy is readable off it.
    let text = errs.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n");
    assert!(
        text.contains("test.wi926.Status.Open") && text.contains("test.wi926.Status.Closed"),
        "the error must name the constructors to pick from; got:\n{text}",
    );

    // Nothing was asserted.
    let status = kb.try_resolve_symbol("test.wi926.Status").expect("Status resolves");
    assert!(kb.rules_by_functor(status).is_empty(), "a refused section asserts nothing");
}

/// With a real schema in hand, an unknown key in a row is reported. It could not
/// be while the schema was empty: the check was guarded on `!fields.is_empty()`,
/// so every key passed.
#[test]
fn an_unknown_field_in_a_persisted_row_is_reported() {
    let mut kb = load_src(SRC);
    let domain = kb.intern("persisted");
    let toml_src = r#"
[meta]
entity = "test.wi926.Project"

[data]
name = "my-app"
langauge = "rust"
"#;
    let errs = term_ser::load_toml(&mut kb, toml_src, domain)
        .expect_err("a misspelled field must be reported");
    assert!(
        errs.iter().any(|e| matches!(
            e,
            term_ser::SerError::UnknownField { field, .. } if field == "langauge"
        )),
        "expected UnknownField for 'langauge', got: {errs:?}",
    );
}
