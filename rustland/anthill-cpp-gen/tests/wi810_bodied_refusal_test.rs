//! WI-810: cpp-gen's TYPE-LOWERING-path realization readers refuse a BODIED rule
//! loudly — through `CppCodegenError` (rendered `error: {msg}`, exit 1), not the
//! WI-770 `assert!`-abort — instead of head-matching it with its guard silently
//! skipped. WI-810 moved the three former `query_realization_facts` callers onto
//! the values-first `read_facts(Refuse)` accessor (WI-773/057) via
//! `read_realization_facts`:
//!   - `TypeMapping`     (`cpp_base_host_type` / `resolve_type_mapping`) — pinned
//!     in `type_mapping_query_test::bodied_type_mapping_rule_is_refused_not_head_matched`
//!   - `IncludeMapping`  (`Includes::from_kb`, the namespace-header include scan)
//!   - `NamingConvention` (`cpp_method_name`, the carrier-dispatch method spelling)
//!
//! The latter two ride deeper codegen paths (a namespace-header emit, a
//! carrier-dispatch body synthesis), so they are exercised end-to-end here
//! through the public `emit_*` entry points. The blanket single-pass `Refuse`
//! policy itself is pinned generically by `kb::extent`'s unit tests; before
//! WI-810 a guarded `IncludeMapping` / `NamingConvention` was head-matched, its
//! guard skipped — the exact silent-wrong-answer class this test now forbids.

use super::common;

use anthill_cpp_gen::{emit_namespace_header, emit_traits_struct};
use common::load_kb_with;

#[test]
fn bodied_include_mapping_rule_is_refused_loudly() {
    // An `IncludeMapping` probe written as a GUARDED rule rather than a fact —
    // the trap WI-810 closes for `Includes::from_kb` (the include scan run while
    // rendering a namespace header). The stdlib ships plain cpp IncludeMapping
    // facts; this bodied candidate under the same functor poisons the read.
    let source = r##"
        namespace test.wi810_inc
          import anthill.prelude.{Int64, Bool}
          import anthill.realization.IncludeMapping

          entity Widget(size: Int64)

          entity Toggle(on: Bool)
          fact Toggle(on: true)

          rule IncludeMapping(lang: "cpp", host_type: "::widget::W", include: "#include <widget.hpp>")
            :- Toggle(on: true)
        end
    "##;
    let mut kb = load_kb_with(source);
    let err = emit_namespace_header(&mut kb, "test.wi810_inc")
        .expect_err("a bodied IncludeMapping rule must be refused, never head-matched");
    // The refusal renders the offending rule (`head :- body`) and names the functor.
    assert!(err.message.contains(":-"), "refusal renders the rule: {}", err.message);
    assert!(
        err.message.contains("IncludeMapping"),
        "refusal names the functor: {}",
        err.message
    );
}

#[test]
fn bodied_naming_convention_rule_is_refused_loudly() {
    // A `NamingConvention` overlay written as a GUARDED rule rather than a fact —
    // the trap WI-810 closes for `cpp_method_name`, reached when synthesising a
    // carrier-dispatch method body (`self->pascalCase()`). The `Sensor` carrier
    // binding lets the `self: Sensor` param lower to a host type so emission
    // reaches body synthesis; the bodied `NamingConvention` then poisons the read.
    let source = r#"
        namespace test.wi810_naming
          import anthill.prelude.{String, Unit, Option, Bool}
          import anthill.realization.{Implementation, CarrierBinding, NamingConvention}

          sort Sensor
            operation ping(self: Sensor) -> Unit
          end

          entity Toggle(on: Bool)
          fact Toggle(on: true)

          fact Implementation(
            target:        "test.wi810_naming.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       none,
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor", host_type: "::vendor::Sensor *")],
            namespace_map: [],
            binding:       none)

          rule NamingConvention(language: "cpp", method_case: "PascalCase", source_case: "snake_case")
            :- Toggle(on: true)
        end
    "#;
    let mut kb = load_kb_with(source);
    let err = emit_traits_struct(&mut kb, "test.wi810_naming.Sensor")
        .expect_err("a bodied NamingConvention rule must be refused, never head-matched");
    assert!(err.message.contains(":-"), "refusal renders the rule: {}", err.message);
    assert!(
        err.message.contains("NamingConvention"),
        "refusal names the functor: {}",
        err.message
    );
}

#[test]
fn plain_include_and_naming_facts_still_read() {
    // The dual of the refusals: ordinary FACTS (the stdlib norm) read exactly as
    // before. A plain namespace header emits with its include block, and a
    // carrier-dispatch body gets its camelCase method spelling — the accessor
    // only refuses BODIED candidates.
    let source = r#"
        namespace test.wi810_ok
          import anthill.prelude.{Unit, Option, Bool}
          import anthill.realization.{Implementation, CarrierBinding}

          entity Widget(size: Int64)

          sort Sensor
            operation ping(self: Sensor) -> Unit
          end

          fact Implementation(
            target:        "test.wi810_ok.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       none,
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor", host_type: "::vendor::Sensor *")],
            namespace_map: [],
            binding:       none)
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi810_ok")
        .expect("plain IncludeMapping facts read: namespace header emits");
    assert!(header.contains("struct Widget"), "entity struct emitted:\n{header}");
    let traits = emit_traits_struct(&mut kb, "test.wi810_ok.Sensor")
        .expect("plain NamingConvention facts read: carrier dispatch body synthesises");
    // snake_case `ping` stays `ping` (identity under camelCase); the point is the
    // NamingConvention read succeeded and produced a dispatch call.
    assert!(traits.contains("self->ping()"), "carrier dispatch body emitted:\n{traits}");
}
