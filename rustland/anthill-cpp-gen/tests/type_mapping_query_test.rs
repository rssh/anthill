//! WI-089: the keyed-TypeMapping discrim query that replaces the hardcoded
//! prim_lower / param_lower tables. Isolates the query from codegen
//! integration so a matching bug is distinguishable from an emission bug.

use super::common;

use anthill_cpp_gen::cpp_base_host_type;
use common::load_kb_with;

#[test]
fn base_renames_resolve_via_query() {
    // The cpp_std base renames ship in the stdlib; no user types needed.
    let mut kb = load_kb_with("namespace test.empty end");

    // WI-833: `cpp_base_host_type` takes `&mut` now — it RESOLVES the TypeMapping
    // candidates (`read_facts_resolved`) so a guarded overlay is evaluated. Plain
    // facts resolve, so `.unwrap()`.
    let mut base = |ty: &str| cpp_base_host_type(&mut kb, ty).unwrap();

    // Primitives → leaf host type.
    assert_eq!(base("anthill.prelude.Int64").as_deref(), Some("int64_t"));
    assert_eq!(base("anthill.prelude.Float").as_deref(), Some("double"));
    assert_eq!(
        base("anthill.prelude.String").as_deref(),
        Some("std::string")
    );
    assert_eq!(base("anthill.prelude.Bool").as_deref(), Some("bool"));
    assert_eq!(base("anthill.prelude.Unit").as_deref(), Some("void"));

    // Parameterized stdlib sorts → a template over their parameters (K6WFS).
    assert_eq!(
        base("anthill.prelude.List").as_deref(),
        Some("std::vector<$T>")
    );
    assert_eq!(
        base("anthill.prelude.Option").as_deref(),
        Some("std::optional<$T>")
    );
    assert_eq!(
        base("anthill.prelude.Result").as_deref(),
        Some("anthill::runtime::Result<$T, $E>")
    );

    // A sort is looked up by its qualified name only (K6WFS): the short name finds
    // nothing, as an unknown type does.
    assert_eq!(base("Int64"), None);
    assert_eq!(base("NoSuchType"), None);
}

/// WI-833: a BODIED TypeMapping rule is now EVALUATED, not refused. WI-089's
/// guarded-overlay direction finally works: the query resolves the candidate
/// (`read_facts_resolved`), so the mapping participates iff its guard holds.
/// Pre-WI-833 (`read_facts(Refuse)`) this same rule was refused loudly because
/// the read could not evaluate the guard; the fuller passing/failing-guard and
/// ambiguity coverage lives in `wi833_resolve_aggregation_test`.
#[test]
fn guarded_type_mapping_is_evaluated_not_refused() {
    let base = |fast_math: bool| {
        let toggle = if fast_math {
            "fact FastMath(on: true)"
        } else {
            "fact FastMath(on: false)"
        };
        let source = format!(
            r#"
            namespace test.bodiedguard
              import anthill.realization.{{TypeMapping}}
              import anthill.prelude.{{Bool}}
              import anthill.prelude.Option.{{some, none}}

              sort Money end
              entity FastMath(on: Bool)
              {toggle}

              rule TypeMapping(lang: some("cpp"), key: none, anthill_type: "test.bodiedguard.Money",
                               host_type: "float", lift: none, lower: none)
                :- FastMath(on: true)
            end
        "#
        );
        let mut kb = load_kb_with(&source);
        cpp_base_host_type(&mut kb, "test.bodiedguard.Money")
            .expect("a guarded TypeMapping is resolved, not refused")
    };

    // Guard holds → the overlay's host type is emitted.
    assert_eq!(
        base(true).as_deref(),
        Some("float"),
        "passing guard → mapping applies"
    );
    // Guard fails → no mapping (the rule contributed no row).
    assert_eq!(base(false), None, "failing guard → no mapping resolves");
}

#[test]
fn project_fact_participates_in_query() {
    // A project asserting its own keyed entry is picked up by the same
    // query — "configure the type mapping as ordinary language usage", no
    // Rust recompile. A fresh anthill type avoids any ambiguity with the
    // stdlib base renames.
    let source = r#"
        namespace test.project
          import anthill.realization.{TypeMapping}
          import anthill.prelude.Option.{some, none}
          sort Money end
          fact TypeMapping(lang: some("cpp"), anthill_type: "test.project.Money", host_type: "::cents::Cents")
        end
    "#;
    let mut kb = load_kb_with(source);

    assert_eq!(
        cpp_base_host_type(&mut kb, "test.project.Money")
            .unwrap()
            .as_deref(),
        Some("::cents::Cents")
    );
}

/// K6WFS: what every cpp `TypeMapping` is held to before any is used — `anthill_type`
/// names a sort by its qualified name, and `host_type` places each of the sort's
/// parameters exactly once. Each malformed entry is refused naming itself, where it
/// used to be either never matched (a short name under the qualified-only lookup) or
/// wrapped in an order the host does not have. FAILS with `check_type_mappings`
/// backed out, as do `wi847`'s and `wi848`'s refusal rows; the well-formed twins pass
/// either way.
#[test]
fn a_malformed_type_mapping_is_refused_naming_it() {
    let refusal = |anthill_type: &str, host_type: &str| {
        let source = format!(
            r#"
            namespace test.malformed
              import anthill.realization.{{TypeMapping}}
              import anthill.prelude.Option.{{some, none}}
              sort Money end
              sort Box
                sort K = ?
                sort V = ?
              end
              fact TypeMapping(lang: some("cpp"), key: none, anthill_type: "{anthill_type}",
                               host_type: "{host_type}", lift: none, lower: none)
            end
        "#
        );
        let mut kb = load_kb_with(&source);
        cpp_base_host_type(&mut kb, "anthill.prelude.Int64")
            .expect_err("a malformed entry is refused at the first lookup")
            .message
    };
    // The well-formed twins resolve.
    for (anthill_type, host_type) in [
        ("test.malformed.Money", "cents"),
        ("test.malformed.Box", "box<$V, $K>"),
    ] {
        let source = format!(
            r#"
            namespace test.malformed
              import anthill.realization.{{TypeMapping}}
              import anthill.prelude.Option.{{some, none}}
              sort Money end
              sort Box
                sort K = ?
                sort V = ?
              end
              fact TypeMapping(lang: some("cpp"), key: none, anthill_type: "{anthill_type}",
                               host_type: "{host_type}", lift: none, lower: none)
            end
        "#
        );
        let mut kb = load_kb_with(&source);
        assert_eq!(
            cpp_base_host_type(&mut kb, anthill_type)
                .unwrap()
                .as_deref(),
            Some(host_type)
        );
    }

    let short = refusal("Money", "cents");
    assert!(
        short.contains("names no sort by its qualified name"),
        "{short}"
    );
    let unknown = refusal("test.malformed.Nothing", "cents");
    assert!(
        unknown.contains("names no sort by its qualified name"),
        "{unknown}"
    );
    let stray = refusal("test.malformed.Box", "box<$K, $W>");
    assert!(
        stray.contains("`$W` is no type parameter of the sort"),
        "{stray}"
    );
    let twice = refusal("test.malformed.Box", "box<$K, $K, $V>");
    assert!(twice.contains("`$K` is written twice"), "{twice}");
    let missing = refusal("test.malformed.Box", "box<$K>");
    assert!(
        missing.contains("type parameter `V` has no `$V`"),
        "{missing}"
    );
    let bare = refusal("test.malformed.Box", "box");
    assert!(bare.contains("type parameter `K` has no `$K`"), "{bare}");
    let scalar = refusal("test.malformed.Money", "cents<$T>");
    assert!(
        scalar.contains("`$T` is no type parameter of the sort"),
        "{scalar}"
    );
}
