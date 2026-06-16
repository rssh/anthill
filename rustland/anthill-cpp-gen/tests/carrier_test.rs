//! Tests for `Implementation` / `CarrierBinding` consumption.
//!
//! Verifies that an anthill sort with a `CarrierBinding` lowers to the
//! declared host type (instead of the hardcoded primitive fallback or
//! a fresh emitted struct).

use super::common;

use anthill_cpp_gen::{emit_entity_struct, emit_namespace_header, CarrierTable};
use common::{collect_anthill_files, load_kb_with, load_kb_with_extras, rustland_root};

#[test]
fn carrier_table_picks_up_implementation_facts() {
    // Plain sort + Implementation fact assigning it a C++ carrier.
    // No fields on Money — it's a foreign type webots-wise.
    let source = r#"
        namespace test.carriers
          import anthill.prelude.{String, Option}
          import anthill.realization.{Implementation, CarrierBinding}

          sort Money
          end

          fact Implementation(
            target:        "test.carriers.Money",
            artifact:      "cents/cents.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Money",
                                           host_type: "::cents::Cents")],
            namespace_map: []
          )
        end
    "#;

    let kb = load_kb_with(source);
    let table = CarrierTable::from_kb(&kb);

    assert!(!table.is_empty(), "expected at least one carrier from the Money fact");
    assert_eq!(
        table.lookup("test.carriers.Money"),
        Some("::cents::Cents"),
        "Money should map to ::cents::Cents",
    );
    assert!(
        table.lookup("test.carriers.Money").is_some(),
        "Money should be flagged as carrier-bound",
    );
}

#[test]
fn entity_field_uses_carrier_type() {
    // An entity with a field typed at a carrier-bound sort should
    // emit the host type, not the anthill name (and not error).
    let source = r#"
        namespace test.carriers
          import anthill.prelude.{String, Option}
          import anthill.realization.{Implementation, CarrierBinding}

          sort Money
          end

          fact Implementation(
            target:        "test.carriers.Money",
            artifact:      "cents/cents.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Money",
                                           host_type: "::cents::Cents")],
            namespace_map: []
          )

          entity Account(name: String, balance: Money)
        end
    "#;

    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "test.carriers.Account").expect("emit Account");
    let expected = "\
struct Account {
    std::string name;
    ::cents::Cents balance;
};
";
    assert_eq!(cpp, expected, "Account emission with carrier-bound Money:\n{cpp}");
}

#[test]
fn carrier_bound_sort_skipped_in_namespace_emission() {
    // The Money sort is carrier-bound; it must NOT appear as an
    // emitted struct in the namespace's header (or we'd shadow the
    // user's existing ::cents::Cents type). Account, which has
    // fields, is emitted as expected.
    let source = r#"
        namespace test.carriers
          import anthill.prelude.{String, Option}
          import anthill.realization.{Implementation, CarrierBinding}

          sort Money
          end

          fact Implementation(
            target:        "test.carriers.Money",
            artifact:      "cents/cents.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Money",
                                           host_type: "::cents::Cents")],
            namespace_map: []
          )

          entity Account(name: String, balance: Money)
        end
    "#;

    let kb = load_kb_with(source);
    let header = emit_namespace_header(&kb, "test.carriers")
        .expect("emit test.carriers namespace");

    assert!(header.contains("struct Account"), "expected Account struct:\n{header}");
    assert!(
        !header.contains("struct Money"),
        "Money is carrier-bound and must not be emitted as a struct:\n{header}"
    );
    // Money's host type must show up at Account.balance's field type.
    assert!(
        header.contains("::cents::Cents balance"),
        "expected balance field with carrier type:\n{header}"
    );
}

#[test]
fn carrier_overrides_primitive_default() {
    // Override the default Int64 → int64_t mapping with a carrier.
    // (This is mostly a probe — production specs are unlikely to
    // override primitives, but the precedence is documented.)
    let source = r#"
        namespace test.carriers
          import anthill.prelude.{Int64, Option}
          import anthill.realization.{Implementation, CarrierBinding}

          sort SmallInt
          end

          fact Implementation(
            target:        "test.carriers.SmallInt",
            artifact:      "small_int.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "SmallInt",
                                           host_type: "int32_t")],
            namespace_map: []
          )

          entity Counter(value: SmallInt, total: Int64)
        end
    "#;

    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "test.carriers.Counter").expect("emit Counter");
    // `value: SmallInt` → carrier int32_t; `total: Int64` → primitive int64_t.
    assert!(cpp.contains("int32_t value"), "expected int32_t for SmallInt:\n{cpp}");
    assert!(cpp.contains("int64_t total"), "expected int64_t for Int64:\n{cpp}");
}

#[test]
fn lf1_carriers_loaded_from_realization_facts() {
    // Loading the lf1 webots dir should populate the carrier table
    // with all 7 webots binding sorts. This is the integration check
    // against actual project files.
    let lf1 = rustland_root().join("examples/webots-modelling/lf1/webots");
    let kb = load_kb_with_extras("namespace test.lf1_carriers end", &collect_anthill_files(&lf1));

    let table = CarrierTable::from_kb(&kb);

    // The lf1 realization.anthill declares these (as of the carrier slice).
    let expected = [
        ("anthill.examples.lf1.webots.Robot",        "webots::Robot"),
        ("anthill.examples.lf1.webots.GPS",          "webots::GPS *"),
        ("anthill.examples.lf1.webots.Gyro",         "webots::Gyro *"),
        ("anthill.examples.lf1.webots.InertialUnit", "webots::InertialUnit *"),
        ("anthill.examples.lf1.webots.Motor",        "webots::Motor *"),
        ("anthill.examples.lf1.webots.Emitter",      "webots::Emitter *"),
        ("anthill.examples.lf1.webots.Receiver",     "webots::Receiver *"),
        ("anthill.examples.lf1.webots.SimulationRuntime", "webots::Robot"),
    ];
    for (sort_name, host_type) in expected {
        assert_eq!(
            table.lookup(sort_name),
            Some(host_type),
            "{sort_name} should carrier-bind to {host_type}",
        );
    }
}
