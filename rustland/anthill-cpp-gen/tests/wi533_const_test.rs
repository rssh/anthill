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
          import anthill.prelude.Option.{none, some}
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
    compile_header(
        &header,
        "wi533ns",
        "test::wi533ns::Packet p{1};\n    (void)p;",
    );
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
    compile_header(
        &header,
        "wi533inf",
        "test::wi533inf::Dummy d{0.0};\n    (void)d;",
    );
}

/// WI-889 — all THREE Float IEEE specials lower from the cpp `const_map` (the
/// `HostConstTable` that replaced the hand-written `render_as_float_special`), not just
/// `infinity`. Each is a bodyless host const with no C++ literal spelling; the binding's
/// `const_map` names the `std::numeric_limits` expression, and `<limits>` rides the
/// include probe. Compiling the header proves the emitted expressions are real C++.
#[test]
fn all_three_float_ieee_specials_lower_from_const_map_and_compile() {
    let source = r#"
        namespace test.wi889cpp
          import anthill.prelude.{Float}
          import anthill.prelude.Float.{infinity, negativeInfinity, nan}
          const POS_INF: Float = infinity
          const NEG_INF: Float = negativeInfinity
          const NOT_A_NUM: Float = nan
          entity Dummy(x: Float)
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi889cpp").expect("emit ns header");
    for (name, expr) in [
        ("POS_INF", "std::numeric_limits<double>::infinity()"),
        ("NEG_INF", "-std::numeric_limits<double>::infinity()"),
        ("NOT_A_NUM", "std::numeric_limits<double>::quiet_NaN()"),
    ] {
        assert!(
            header.contains(&format!("inline constexpr double {name} = {expr};")),
            "{name} must lower to its const_map expression `{expr}`:\n{header}"
        );
    }
    assert!(
        header.contains("#include <limits>"),
        "the numeric_limits expressions must pull in <limits>:\n{header}"
    );
    compile_header(
        &header,
        "wi889cpp",
        "test::wi889cpp::Dummy d{0.0};\n    (void)d;",
    );
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
    compile_header(
        &header,
        "wi533str",
        "test::wi533str::Box b{1};\n    (void)b;",
    );
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
    assert!(
        header.contains("struct Channels"),
        "const-only sort must emit a struct:\n{header}"
    );
    assert!(
        header.contains("static constexpr int64_t BROADCAST = -1;"),
        "const-only sort must carry its const:\n{header}"
    );
    compile_header(
        &header,
        "wi533only",
        "(void)test::wi533only::Channels::BROADCAST;",
    );
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
    assert_eq!(
        header.matches("NS_LEVEL").count(),
        1,
        "NS_LEVEL must appear once:\n{header}"
    );
    assert_eq!(
        header.matches("BROADCAST").count(),
        1,
        "BROADCAST must appear once:\n{header}"
    );
    assert!(
        !header.contains("inline constexpr int64_t BROADCAST"),
        "the sort-body const must not also emit at namespace scope:\n{header}"
    );
}

/// Write `header` to a scratch dir and compile a driver that includes it and
/// runs `body`. Skips (with a note) when no C++ compiler is available.
/// WI-20261011-2QZ3F — a const's value is lowered as it was TYPED: a call an equation
/// defines is the equation's right-hand side by then. Lowered as written it named a
/// body-less operation with no C++ realization, and the header was refused (measured
/// with the const's typed value not stored: "`test.wi2qz3fcpp.dbl` has no body and no
/// C++ realization").
#[test]
fn a_const_over_an_equation_defined_call_lowers_the_typed_value_and_compiles() {
    let source = r#"
        namespace test.wi2qz3fcpp
          import anthill.prelude.{Int64}
          operation dbl(n: Int64) -> Int64
          rule dbl(?n) <=> ?n + ?n @[simp]
          const EIGHT: Int64 = dbl(4)
          entity Dummy(x: Int64)
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi2qz3fcpp").expect("emit ns header");
    assert!(
        header.contains("inline constexpr int64_t EIGHT = (4 + 4);"),
        "the const lowers the equation's right-hand side:\n{header}"
    );
    compile_header(
        &header,
        "wi2qz3fcpp",
        "static_assert(test::wi2qz3fcpp::EIGHT == 8);\n    test::wi2qz3fcpp::Dummy d{1};\n    (void)d;",
    );
}

/// A const whose value reads a sort's member const needs that sort's struct declared.
/// Every namespace const was emitted above the structs, so `D = (S::c + 1)` stood above
/// `struct S` and the header did not compile.
///
/// FAILS with `consts_below_the_structs` answering `false` for every const — this row
/// on the order it asserts, the entity-typed row below at the compiler. MEASURED.
#[test]
fn a_const_that_names_a_sorts_const_stands_below_its_struct() {
    let source = r#"
        namespace test.wi2qz3fbelow
          import anthill.prelude.{Int64}
          sort S
            const c: Int64 = 5
          end
          const D: Int64 = S.c + 1
          const FIRST: Int64 = 7
          entity Dummy(x: Int64)
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi2qz3fbelow").expect("emit ns header");
    let at = |needle: &str| {
        header
            .find(needle)
            .unwrap_or_else(|| panic!("`{needle}` is in the header:\n{header}"))
    };
    assert!(
        at("struct S") < at("inline constexpr int64_t D = (S::c + 1);"),
        "the const that names `S::c` is below `struct S`:\n{header}"
    );
    // A const that names no struct keeps its place above them, where a struct or a
    // method body that names it sees it declared.
    assert!(
        at("inline constexpr int64_t FIRST = 7;") < at("struct Dummy"),
        "a const that needs no struct stays first:\n{header}"
    );
    compile_header(
        &header,
        "wi2qz3fbelow",
        "static_assert(test::wi2qz3fbelow::D == 6);\n    test::wi2qz3fbelow::Dummy d{1};\n    (void)d;",
    );
}

/// A const of an entity type needs its struct for its own type, and a const that reads
/// a field of it follows it.
#[test]
fn a_const_of_an_entity_type_stands_below_its_struct() {
    let source = r#"
        namespace test.wi2qz3fent
          import anthill.prelude.{Int64}
          entity P(x: Int64, y: Int64)
          const origin: P = P(3, 4)
          const ox: Int64 = origin.x
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi2qz3fent").expect("emit ns header");
    compile_header(
        &header,
        "wi2qz3fent",
        "static_assert(test::wi2qz3fent::ox == 3);\n    static_assert(test::wi2qz3fent::origin.y == 4);",
    );
}

/// A string that SPELLS a struct's name, or another const's, depends on neither: the
/// lowered value is scanned for the names it uses in its code, not in its text.
///
/// FAILS with the scan reading string text (`code_outside_literals` returning its
/// argument): the header is refused for `A` and `B`, a "const dependency cycle", as it
/// was before `consts_below_the_structs` existed. `GREETING`'s half was measured apart,
/// without those two: it is taken to need `struct S` and emitted below it, where `S`'s
/// own member cannot see it — "'GREETING' was not declared in this scope".
#[test]
fn a_string_that_spells_a_name_is_not_a_reference_to_it() {
    let source = r#"
        namespace test.wi2qz3fstr
          import anthill.prelude.{Int64, String}
          const GREETING: String = "an S is a sort"
          const A: String = "see B"
          const B: String = "see A"
          sort S
            const label: String = GREETING
          end
          entity Dummy(x: Int64)
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi2qz3fstr").expect("emit ns header");
    compile_header(
        &header,
        "wi2qz3fstr",
        "static_assert(test::wi2qz3fstr::S::label == test::wi2qz3fstr::GREETING);\n    test::wi2qz3fstr::Dummy d{1};\n    (void)d;",
    );
}

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
