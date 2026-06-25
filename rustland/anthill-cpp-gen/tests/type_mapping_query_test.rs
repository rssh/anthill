//! WI-089: the keyed-TypeMapping discrim query that replaces the hardcoded
//! prim_lower / param_lower tables. Isolates the query from codegen
//! integration so a matching bug is distinguishable from an emission bug.

use super::common;

use anthill_cpp_gen::cpp_base_host_type;
use common::load_kb_with;

#[test]
fn base_renames_resolve_via_query() {
    // The cpp_std base renames ship in the stdlib; no user types needed.
    let kb = load_kb_with("namespace test.empty end");

    // Primitives → leaf host type.
    assert_eq!(cpp_base_host_type(&kb, "Int64").as_deref(), Some("int64_t"));
    assert_eq!(cpp_base_host_type(&kb, "Float").as_deref(), Some("double"));
    assert_eq!(
        cpp_base_host_type(&kb, "String").as_deref(),
        Some("std::string")
    );
    assert_eq!(cpp_base_host_type(&kb, "Bool").as_deref(), Some("bool"));
    assert_eq!(cpp_base_host_type(&kb, "Unit").as_deref(), Some("void"));

    // Parameterized stdlib containers → bare template name.
    assert_eq!(
        cpp_base_host_type(&kb, "List").as_deref(),
        Some("std::vector")
    );
    assert_eq!(
        cpp_base_host_type(&kb, "Option").as_deref(),
        Some("std::optional")
    );

    // No mapping for an unknown type.
    assert_eq!(cpp_base_host_type(&kb, "NoSuchType"), None);
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
    let kb = load_kb_with(source);

    assert_eq!(
        cpp_base_host_type(&kb, "Money").as_deref(),
        Some("::cents::Cents")
    );
}
