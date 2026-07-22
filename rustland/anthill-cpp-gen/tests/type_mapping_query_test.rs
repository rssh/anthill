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

    // WI-810: `cpp_base_host_type` returns `Result` now (it can refuse a bodied
    // TypeMapping through `read_facts(Refuse)`); plain facts resolve, so `.unwrap()`.
    let base = |ty: &str| cpp_base_host_type(&kb, ty).unwrap();

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

/// WI-770 / WI-810: a BODIED TypeMapping rule must never be silently head-matched
/// — the query reads facts only and cannot evaluate the guard, so an author
/// following WI-089's guarded-overlay direction would otherwise get the guard's
/// host type emitted unconditionally with no diagnostic. WI-810 moved this reader
/// onto `read_facts(Refuse)`, so the refusal now surfaces GRACEFULLY through
/// `CppCodegenError` (rendered `error: {msg}`, exit 1) instead of the WI-770
/// `assert!`-abort (exit 101) — but it is still LOUD, naming the offending rule.
#[test]
fn bodied_type_mapping_rule_is_refused_not_head_matched() {
    let source = r#"
        namespace test.bodiedguard
          import anthill.realization.{TypeMapping}
          import anthill.prelude.Option.{some, none}

          sort Toggle
            entity fast_math_on
          end

          rule TypeMapping(lang: some("cpp"), anthill_type: "Money", host_type: "float")
            :- fast_math_on()
        end
    "#;
    let kb = load_kb_with(source);
    let err = cpp_base_host_type(&kb, "Money")
        .expect_err("a bodied TypeMapping rule must be refused, never head-matched");
    // The refusal renders the offending rule (`head :- body`) and names the functor.
    assert!(err.message.contains(":-"), "refusal renders the rule: {}", err.message);
    assert!(
        err.message.contains("TypeMapping"),
        "refusal names the functor: {}",
        err.message
    );
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
        cpp_base_host_type(&kb, "Money").unwrap().as_deref(),
        Some("::cents::Cents")
    );
}
