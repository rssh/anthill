//! `fact Generated(source: ..., artifact: ..., language: ..., kind:
//! ..., profile: some("..."))` is the spec-side declaration of a
//! codegen target — what `anthill codegen cpp-project` reads to
//! decide which sorts get scaffolded into per-controller folders.
//!
//! Distinct from `Implementation` (which adapts external code into
//! anthill); `Generated` declares anthill is the *source* and the
//! host artifact is the *output*.

use super::common::load_kb_with;

#[test]
fn generated_facts_are_extracted_with_source_artifact_and_kind() {
    let source = r#"
        namespace test.gen_facts
          import anthill.prelude.{Option}
          import anthill.realization.{Generated}

          sort Calc
            operation tick() -> Bool = true
          end

          fact Generated(
            source:      "test.gen_facts.Calc",
            artifact:    "controllers/Calc",
            language:    "cpp",
            profile:     some("cpp20-stl"),
            kind:        "controller",
            description: some("a test controller")
          )
        end
    "#;
    let kb = load_kb_with(source);

    let targets = anthill_cpp_gen::generated_targets(&kb);
    let calc = targets.iter()
        .find(|t| t.source == "test.gen_facts.Calc")
        .expect("expected Generated fact for Calc");
    assert_eq!(calc.artifact, "controllers/Calc");
    assert_eq!(calc.language, "cpp");
    assert_eq!(calc.kind, "controller");
    assert_eq!(calc.profile.as_deref(), Some("cpp20-stl"));
    assert_eq!(calc.description.as_deref(), Some("a test controller"));
}

#[test]
fn generated_facts_with_none_profile_resolve_to_none() {
    let source = r#"
        namespace test.gen_no_profile
          import anthill.prelude.{Option}
          import anthill.realization.{Generated}

          sort Calc
            operation tick() -> Bool = true
          end

          fact Generated(
            source:      "test.gen_no_profile.Calc",
            artifact:    "out/Calc",
            language:    "cpp",
            profile:     none,
            kind:        "library",
            description: none
          )
        end
    "#;
    let kb = load_kb_with(source);
    let t = anthill_cpp_gen::generated_targets(&kb)
        .into_iter()
        .find(|t| t.source == "test.gen_no_profile.Calc")
        .expect("expected target");
    assert!(t.profile.is_none(), "profile=none should map to None: {:?}", t.profile);
    assert!(t.description.is_none());
    assert_eq!(t.kind, "library");
}

#[test]
fn no_facts_yields_empty_list() {
    let source = r#"
        namespace test.gen_empty
          import anthill.prelude.{Bool}
          sort Calc
            operation tick() -> Bool = true
          end
        end
    "#;
    let kb = load_kb_with(source);
    // Stdlib also has no Generated facts (yet), so the result is
    // empty rather than just "no test-namespace targets".
    let targets = anthill_cpp_gen::generated_targets(&kb);
    let in_namespace: Vec<_> = targets.iter()
        .filter(|t| t.source.starts_with("test.gen_empty."))
        .collect();
    assert!(in_namespace.is_empty(), "no Generated facts in test namespace");
}
