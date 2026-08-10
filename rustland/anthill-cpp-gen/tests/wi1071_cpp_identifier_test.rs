//! WI-1071: Anthill identifiers containing `-` must cross the C++ boundary as
//! legal identifiers, and the resulting many-to-one mapping must reject
//! ambiguous declarations before emitting a header.

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_namespace_header, header_filename_for_namespace, CarrierTable};
use common::{find_cxx, load_kb_with, scratch_dir};

#[test]
fn hyphenated_identifiers_emit_and_compile_as_underscores() {
    let source = r#"
        namespace test.hy-phen
          import anthill.prelude.{Int64}

          entity my-entity(zero-val: Int64)

          sort my-widget
            entity widget-value(item-val: Int64)
          end

          sort Calc
            sort T = ?
            operation zero-val(my-arg: T) -> T
          end
        end
    "#;

    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.hy-phen").expect("emit normalized header");

    // BACKOUT CONTROL: without WI-1071 every assertion below sees the source
    // hyphen unchanged, and the compiler then rejects the generated header at
    // the namespace declaration before any driven type/member use can compile.
    assert!(
        header.contains("namespace test::hy_phen {"),
        "namespace segment was not normalized:\n{header}"
    );
    assert!(
        header.contains("struct my_entity"),
        "entity name was not normalized:\n{header}"
    );
    assert!(
        header.contains("int64_t zero_val;"),
        "field name was not normalized:\n{header}"
    );
    assert!(
        header.contains("struct widget_value"),
        "variant/entity name was not normalized:\n{header}"
    );
    assert!(
        header.contains("using my_widget = std::variant<widget_value>;"),
        "sum-sort name or constructor reference was not normalized:\n{header}"
    );
    assert!(
        header.contains("static T zero_val(T my_arg);"),
        "operation or parameter name was not normalized:\n{header}"
    );
    assert_eq!(
        header_filename_for_namespace("test.hy-phen"),
        "test_hy_phen.hpp",
        "header filenames use the same per-segment normalization"
    );

    let Some(cxx) = find_cxx() else {
        eprintln!("no C++ compiler available — skipping compile check");
        return;
    };
    let dir = scratch_dir("wi1071_cpp_identifiers");
    let header_path = dir.join(header_filename_for_namespace("test.hy-phen"));
    std::fs::write(&header_path, &header).expect("write generated header");
    let driver = format!(
        r#"#include "{}"

int main() {{
    test::hy_phen::my_entity entity{{42}};
    test::hy_phen::widget_value choice{{7}};
    test::hy_phen::my_widget sum = choice;
    auto operation = &test::hy_phen::Calc<int64_t>::zero_val;
    return entity.zero_val + std::get<test::hy_phen::widget_value>(sum).item_val
        + (operation != nullptr ? 0 : 1);
}}
"#,
        header_path.display()
    );
    let driver_path = dir.join("driver.cpp");
    std::fs::write(&driver_path, &driver).expect("write C++ driver");

    let output = Command::new(cxx)
        .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Wextra"])
        .arg(&driver_path)
        .output()
        .expect("invoke C++ compiler");
    if !output.status.success() {
        panic!(
            "generated WI-1071 header did not compile with {cxx}\n\
             ── header ──\n{header}\n\
             ── driver ──\n{driver}\n\
             ── stderr ──\n{}\n\
             ── stdout ──\n{}",
            String::from_utf8_lossy(&output.stderr),
            String::from_utf8_lossy(&output.stdout),
        );
    }
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn normalized_identifier_collision_is_refused_before_emission() {
    let mut kb = load_kb_with(
        r#"
        namespace test.wi1071_collision
          import anthill.prelude.{Int64}
          entity foo-bar(value: Int64)
          entity foo_bar(value: Int64)
        end
        "#,
    );

    // BACKOUT CONTROL: without WI-1071 collision validation this returns Ok
    // and emits two declarations of `foo_bar`; the source language distinction
    // has already been lost by the time a C++ compiler diagnoses redefinition.
    let error = emit_namespace_header(&mut kb, "test.wi1071_collision")
        .expect_err("foo-bar and foo_bar must not share one C++ identifier");
    assert!(
        error.message.contains("foo-bar")
            && error.message.contains("foo_bar")
            && error.message.contains("collision"),
        "collision diagnostic must name both source spellings and the problem: {}",
        error.message
    );
}

#[test]
fn carrier_lookup_keeps_anthill_spelling_while_emission_normalizes() {
    let mut kb = load_kb_with(
        r#"
        namespace test.hy-lookup
          import anthill.prelude.{Int64, Option, String}
          import anthill.realization.{Implementation, CarrierBinding}

          sort host-sort
          end

          fact Implementation(
            target:        "test.hy-lookup.host-sort",
            artifact:      "vendor/host.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "host-sort",
                                           host_type: "::vendor::Host")],
            namespace_map: []
          )

          entity holder(payload: host-sort)
        end
        "#,
    );

    // BACKOUT CONTROL: this lookup passed before WI-1071 and must keep passing;
    // normalizing either realization key would silently lose the carrier. The
    // header assertion fails if the matching emission side remains verbatim.
    let carriers = CarrierTable::from_kb(&kb).expect("read carrier facts");
    assert_eq!(
        carriers.lookup("test.hy-lookup.host-sort"),
        Some("::vendor::Host")
    );
    assert_eq!(
        carriers.lookup("test.hy_lookup.host_sort"),
        None,
        "realization keys remain exact Anthill spellings"
    );

    let header = emit_namespace_header(&mut kb, "test.hy-lookup").expect("emit holder header");
    assert!(header.contains("namespace test::hy_lookup {"), "{header}");
    assert!(header.contains("::vendor::Host payload;"), "{header}");
    assert!(!header.contains("struct host_sort"), "{header}");
}
