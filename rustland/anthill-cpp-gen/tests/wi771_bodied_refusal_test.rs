//! WI-771: cpp-gen's realization fact readers refuse a BODIED rule loudly —
//! through `CppCodegenError` (rendered as `error: {msg}`, exit 1), not the
//! WI-770 `assert!` abort — instead of head-matching it with its guard silently
//! skipped. The three siblings that had NO `is_fact` guard before WI-771 read
//! through the values-first `read_facts(Refuse)` accessor (WI-773/057):
//! `Implementation` (`CarrierTable::from_kb`), `OperationImpl`
//! (`OpImplTable::from_kb`), and `Generated` (`generated_targets`). All three
//! share the identical accessor call + `expect_term_head` narrowing; the two
//! user-authorable realization facts (`Generated`, `Implementation`) exercise it
//! end-to-end here, and the blanket single-pass `Refuse` policy is pinned
//! generically by `kb::extent`'s unit tests.
//!
//! Before WI-771 a guarded `Implementation` bound carrier / host_type / binding
//! unconditionally (wrong C++ type + include), and a guarded `Generated` emitted
//! the artifact / selected the profile overlay unconditionally — the exact
//! silent-wrong-answer class this test now forbids.

use super::common;

use anthill_cpp_gen::CarrierTable;
use common::load_kb_with;

#[test]
fn bodied_generated_rule_is_refused_loudly() {
    // A `Generated` overlay written as a GUARDED rule rather than a fact — the
    // latent trap WI-770 named for `generated_targets`.
    let source = r#"
        namespace test.wi771_gen
          import anthill.prelude.{String, Option, Bool}
          import anthill.realization.Generated

          entity Toggle(on: Bool)
          fact Toggle(on: true)

          rule Generated(
                source:      "test.wi771_gen.Widget",
                artifact:    "widget.hpp",
                language:    "cpp",
                profile:     none,
                kind:        "controller",
                description: none)
            :- Toggle(on: true)
        end
    "#;
    let kb = load_kb_with(source);
    let err = anthill_cpp_gen::generated_targets(&kb)
        .expect_err("a bodied Generated rule must be refused, never head-matched");
    // The refusal renders the offending rule (`head :- body`), so the message
    // names the offender — not merely "a bodied rule exists".
    assert!(err.message.contains(":-"), "refusal renders the rule: {}", err.message);
    assert!(
        err.message.contains("Generated"),
        "refusal names the functor: {}",
        err.message
    );
}

#[test]
fn bodied_implementation_rule_is_refused_loudly() {
    // An `Implementation` carrier binding written as a GUARDED rule rather than a
    // fact — the trap WI-771 closes for `CarrierTable::from_kb`.
    let source = r#"
        namespace test.wi771_impl
          import anthill.prelude.{String, Option, Bool}
          import anthill.realization.{Implementation, CarrierBinding}

          sort Money
          end

          entity Toggle(on: Bool)
          fact Toggle(on: true)

          rule Implementation(
                target:        "test.wi771_impl.Money",
                artifact:      "cents/cents.hpp",
                language:      "cpp",
                profile:       none,
                description:   none,
                carrier:       [CarrierBinding(sort_name: "Money", host_type: "::cents::Cents")],
                namespace_map: [],
                binding:       none)
            :- Toggle(on: true)
        end
    "#;
    let kb = load_kb_with(source);
    // `.err().expect(..)` rather than `.expect_err(..)`: `CarrierTable` is not
    // `Debug`, and the Ok value is irrelevant to this assertion anyway.
    let err = CarrierTable::from_kb(&kb)
        .err()
        .expect("a bodied Implementation rule must be refused, never head-matched");
    assert!(err.message.contains(":-"), "refusal renders the rule: {}", err.message);
    assert!(
        err.message.contains("Implementation"),
        "refusal names the functor: {}",
        err.message
    );
}

#[test]
fn plain_generated_and_implementation_facts_still_read() {
    // The dual of the refusals: ordinary FACTS (the stdlib + project norm) read
    // exactly as before — the accessor only refuses BODIED candidates.
    let source = r#"
        namespace test.wi771_ok
          import anthill.prelude.{String, Option}
          import anthill.realization.{Generated, Implementation, CarrierBinding}

          sort Money
          end

          fact Implementation(
            target:        "test.wi771_ok.Money",
            artifact:      "cents/cents.hpp",
            language:      "cpp",
            profile:       none,
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Money", host_type: "::cents::Cents")],
            namespace_map: [],
            binding:       none)

          fact Generated(
            source:      "test.wi771_ok.Money",
            artifact:    "money.hpp",
            language:    "cpp",
            profile:     none,
            kind:        "library",
            description: none)
        end
    "#;
    let kb = load_kb_with(source);
    let table = CarrierTable::from_kb(&kb).expect("plain Implementation facts read");
    assert_eq!(table.lookup("test.wi771_ok.Money"), Some("::cents::Cents"));
    let targets = anthill_cpp_gen::generated_targets(&kb).expect("plain Generated facts read");
    assert!(targets.iter().any(|t| t.source == "test.wi771_ok.Money"));
}
