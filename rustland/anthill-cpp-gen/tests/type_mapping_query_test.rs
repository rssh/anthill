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
    assert_eq!(base("Int64").as_deref(), Some("int64_t"));
    assert_eq!(base("Float").as_deref(), Some("double"));
    assert_eq!(base("String").as_deref(), Some("std::string"));
    assert_eq!(base("Bool").as_deref(), Some("bool"));
    assert_eq!(base("Unit").as_deref(), Some("void"));

    // Parameterized stdlib containers → bare template name.
    assert_eq!(base("List").as_deref(), Some("std::vector"));
    assert_eq!(base("Option").as_deref(), Some("std::optional"));

    // No mapping for an unknown type.
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

              entity FastMath(on: Bool)
              {toggle}

              rule TypeMapping(lang: some("cpp"), key: none, anthill_type: "Money", host_type: "float",
                               lift: none, lower: none)
                :- FastMath(on: true)
            end
        "#
        );
        let mut kb = load_kb_with(&source);
        cpp_base_host_type(&mut kb, "Money")
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
          fact TypeMapping(lang: some("cpp"), anthill_type: "Money", host_type: "::cents::Cents")
        end
    "#;
    let mut kb = load_kb_with(source);

    assert_eq!(
        cpp_base_host_type(&mut kb, "Money").unwrap().as_deref(),
        Some("::cents::Cents")
    );
}
