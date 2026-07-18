//! WI-533 — C++ codegen for term-level constants (proposal 039 / WI-084).
//!
//! A `const NAME: T = <value>` declared in a sort body becomes a
//! `static constexpr` member of the carrier's traits class; declared at
//! namespace level it becomes an `inline constexpr`. The value is lowered
//! from the const's anthill body (reusing operation-body lowering), and a
//! bodyless host const reference (WI-532 `infinity`/`nan`) lowers to the
//! corresponding C++ IEEE expression.

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_namespace_header, emit_traits_struct};
use common::{
    collect_anthill_files, find_cxx, load_kb_with, load_kb_with_extras, rustland_root, scratch_dir,
};

#[test]
fn sort_body_const_emits_static_constexpr_member() {
    // The const becomes a static constexpr member, emitted before the methods
    // (matching source order, where the sentinel precedes the operations).
    let source = r#"
        namespace test.wi533
          import anthill.prelude.{Int64, Bool, String}
          import anthill.realization.{Implementation, CarrierBinding}
          sort Emitter
            const BROADCAST_CHANNEL: Int64 = -1
            operation send(self: Emitter, payload: String) -> Bool
          end
          fact Implementation(
            target:        "test.wi533.Emitter",
            artifact:      "emitter.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Emitter",
                                           host_type: "::wi533::Emitter")],
            namespace_map: []
          )
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.wi533.Emitter").expect("emit Emitter");
    assert!(
        cpp.contains("static constexpr int64_t BROADCAST_CHANNEL = -1;"),
        "expected the const as a static constexpr member:\n{cpp}"
    );
}

#[test]
fn lf1_emitter_emits_broadcast_channel_const() {
    // The real driver: lf1 webots `Emitter::BROADCAST_CHANNEL` reaches C++.
    let lf1_webots = rustland_root().join("examples/webots-modelling/lf1/webots");
    let lf1_files = collect_anthill_files(&lf1_webots);
    assert!(!lf1_files.is_empty(), "expected lf1 webots sources");
    let mut kb = load_kb_with_extras("namespace test.lf1_const end", &lf1_files);
    let cpp = emit_traits_struct(&mut kb, "anthill.examples.lf1.webots.Emitter")
        .expect("emit lf1 Emitter");
    assert!(
        cpp.contains("static constexpr int64_t BROADCAST_CHANNEL = -1;"),
        "lf1 Emitter must emit BROADCAST_CHANNEL as a constant:\n{cpp}"
    );
}

#[test]
fn namespace_const_emits_inline_constexpr_and_compiles() {
    // A namespace-level const → `inline constexpr`, emitted before the structs.
    let source = r#"
        namespace test.wi533ns
          import anthill.prelude.{Int64}
          const MAX_RETRIES: Int64 = 5
          entity Packet(size: Int64)
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi533ns").expect("emit ns header");
    assert!(
        header.contains("inline constexpr int64_t MAX_RETRIES = 5;"),
        "expected a namespace-level inline constexpr:\n{header}"
    );
    compile_header(&header, "wi533ns", "test::wi533ns::Packet p{1};\n    (void)p;");
}

#[test]
fn const_referencing_infinity_lowers_to_numeric_limits_and_compiles() {
    // The motor velocity-mode sentinel shape (WI-532 driver): a const whose body
    // is the host const `infinity` lowers to the C++ IEEE expression and pulls
    // in <limits>.
    let source = r#"
        namespace test.wi533inf
          import anthill.prelude.{Float}
          import anthill.prelude.Float.{infinity}
          const VELOCITY_MODE_POSITION: Float = infinity
          entity Dummy(x: Float)
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi533inf").expect("emit ns header");
    assert!(
        header.contains(
            "inline constexpr double VELOCITY_MODE_POSITION = \
             std::numeric_limits<double>::infinity();"
        ),
        "infinity const must lower to a numeric_limits expression:\n{header}"
    );
    assert!(
        header.contains("#include <limits>"),
        "emitting numeric_limits must pull in <limits>:\n{header}"
    );
    compile_header(&header, "wi533inf", "test::wi533inf::Dummy d{0.0};\n    (void)d;");
}

#[test]
fn string_const_emits_string_view_and_compiles() {
    // A String const cannot be `constexpr std::string` (not a literal type in
    // C++17); it lowers to `std::string_view`, which pulls in <string_view>.
    let source = r#"
        namespace test.wi533str
          import anthill.prelude.{String, Int64}
          const GREETING: String = "hi"
          entity Box(n: Int64)
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi533str").expect("emit ns header");
    assert!(
        header.contains("inline constexpr std::string_view GREETING = \"hi\";"),
        "String const must lower to string_view:\n{header}"
    );
    assert!(
        header.contains("#include <string_view>"),
        "string_view const must pull <string_view>:\n{header}"
    );
    compile_header(&header, "wi533str", "test::wi533str::Box b{1};\n    (void)b;");
}

#[test]
fn const_only_sort_emits_struct_member_and_compiles() {
    // A sort with only a const (no operations) is still discovered and emitted
    // as a struct of static constexpr members — not silently dropped.
    let source = r#"
        namespace test.wi533only
          import anthill.prelude.{Int64}
          sort Channels
            const BROADCAST: Int64 = -1
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi533only").expect("emit ns header");
    assert!(header.contains("struct Channels"), "const-only sort must emit a struct:\n{header}");
    assert!(
        header.contains("static constexpr int64_t BROADCAST = -1;"),
        "const-only sort must carry its const:\n{header}"
    );
    compile_header(&header, "wi533only", "(void)test::wi533only::Channels::BROADCAST;");
}

#[test]
fn namespace_and_sort_body_consts_do_not_collide() {
    // A namespace-level const and a sort-body const in the same namespace each
    // emit exactly once in their own scope — the namespace scan and the struct
    // scan must not double-count.
    let source = r#"
        namespace test.wi533mix
          import anthill.prelude.{Int64}
          const NS_LEVEL: Int64 = 7
          sort Channels
            const BROADCAST: Int64 = -1
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi533mix").expect("emit ns header");
    assert!(
        header.contains("inline constexpr int64_t NS_LEVEL = 7;"),
        "namespace const at namespace scope:\n{header}"
    );
    assert!(
        header.contains("static constexpr int64_t BROADCAST = -1;"),
        "sort-body const as a struct member:\n{header}"
    );
    assert_eq!(header.matches("NS_LEVEL").count(), 1, "NS_LEVEL must appear once:\n{header}");
    assert_eq!(header.matches("BROADCAST").count(), 1, "BROADCAST must appear once:\n{header}");
    assert!(
        !header.contains("inline constexpr int64_t BROADCAST"),
        "the sort-body const must not also emit at namespace scope:\n{header}"
    );
}

/// Write `header` to a scratch dir and compile a driver that includes it and
/// runs `body`. Skips (with a note) when no C++ compiler is available.
fn compile_header(header: &str, tag: &str, body: &str) {
    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping {tag} compile check");
            return;
        }
    };
    let dir = scratch_dir(tag);
    let header_path = dir.join(format!("{tag}.hpp"));
    std::fs::write(&header_path, header).expect("write header");
    let driver = format!(
        "#include \"{}\"\n\nint main() {{\n    {body}\n    return 0;\n}}\n",
        header_path.display()
    );
    let driver_path = dir.join("driver.cpp");
    std::fs::write(&driver_path, &driver).expect("write driver");

    let output = Command::new(cxx)
        .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Wextra"])
        .arg(&driver_path)
        .output()
        .expect("invoke compiler");
    assert!(
        output.status.success(),
        "{tag} header failed to compile (compiler: {cxx})\n\
         ── header ───────────\n{header}\n\
         ── stderr ───────────\n{}",
        String::from_utf8_lossy(&output.stderr),
    );
    let _ = std::fs::remove_dir_all(&dir);
}
