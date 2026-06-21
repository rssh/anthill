//! WI-536 — term-level consts in carrier-bound sorts reach generated C++, and
//! const references resolve to named constants.
//!
//! A carrier-bound sort is excluded from struct emission (the carrier owns the
//! type), so a const declared inside one has nowhere to live. WI-536 emits it
//! as a namespace-scope companion `Sort_NAME` (`inline constexpr`), and a
//! reference to any const lowers to its named constant — the companion for a
//! carrier-bound sort, the `Sort::NAME` struct member for an emitted sort —
//! rather than the bare short name (which would not be in scope at the C++ use
//! site).

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_namespace_header, emit_traits_struct};
use common::{find_cxx, load_kb_with, scratch_dir};

const EMITTER_CARRIER: &str = r#"
          fact Implementation(
            target:        "test.wi536.Emitter",
            artifact:      "webots/Emitter.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Emitter",
                                           host_type: "::webots::Emitter *")],
            namespace_map: []
          )
"#;

#[test]
fn carrier_bound_sort_const_emits_namespace_companion_and_compiles() {
    // Emitter is carrier-bound → no struct emitted, but its const surfaces as a
    // namespace-scope companion `Emitter_BROADCAST_CHANNEL`.
    let source = format!(
        r#"
        namespace test.wi536
          import anthill.prelude.{{Int64}}
          import anthill.realization.{{Implementation, CarrierBinding}}
          sort Emitter
            const BROADCAST_CHANNEL: Int64 = -1
            operation get_channel(self: Emitter) -> Int64
          end
          {EMITTER_CARRIER}
          entity Marker(n: Int64)
        end
    "#
    );
    let kb = load_kb_with(&source);
    let header = emit_namespace_header(&kb, "test.wi536").expect("emit ns header");
    assert!(
        header.contains("inline constexpr int64_t Emitter_BROADCAST_CHANNEL = -1;"),
        "carrier-bound sort const must emit a namespace companion:\n{header}"
    );
    assert!(
        !header.contains("struct Emitter"),
        "the carrier-bound sort itself must not emit a struct:\n{header}"
    );
    compile_header(
        &header,
        "wi536",
        "test::wi536::Marker m{1}; (void)m;\n    static_assert(test::wi536::Emitter_BROADCAST_CHANNEL == -1);",
    );
}

#[test]
fn const_reference_in_body_lowers_to_companion() {
    // An op body that references the carrier-bound sort's own const lowers the
    // reference to the companion name (here fully qualified — emit_traits_struct
    // has no enclosing-namespace context).
    let source = format!(
        r#"
        namespace test.wi536
          import anthill.prelude.{{Int64}}
          import anthill.realization.{{Implementation, CarrierBinding}}
          sort Emitter
            const BROADCAST_CHANNEL: Int64 = -1
            operation default_channel(self: Emitter) -> Int64 = BROADCAST_CHANNEL
          end
          {EMITTER_CARRIER}
        end
    "#
    );
    let kb = load_kb_with(&source);
    let cpp = emit_traits_struct(&kb, "test.wi536.Emitter").expect("emit Emitter");
    assert!(
        cpp.contains("Emitter_BROADCAST_CHANNEL"),
        "a const reference must lower to the companion, not the bare name:\n{cpp}"
    );
    assert!(
        !cpp.contains("return BROADCAST_CHANNEL;"),
        "the bare const name must not leak into the body:\n{cpp}"
    );
}

#[test]
fn non_carrier_sort_const_reference_uses_struct_member_and_compiles() {
    // A const in an EMITTED (non-carrier) sort is a struct member, so a
    // reference resolves to `Sort::NAME`.
    let source = r#"
        namespace test.wi536nc
          import anthill.prelude.{Int64}
          sort Config
            const LIMIT: Int64 = 42
            operation get_limit() -> Int64 = LIMIT
          end
        end
    "#;
    let kb = load_kb_with(source);
    let header = emit_namespace_header(&kb, "test.wi536nc").expect("emit ns header");
    assert!(
        header.contains("static constexpr int64_t LIMIT = 42;"),
        "non-carrier sort const stays a struct member:\n{header}"
    );
    assert!(
        header.contains("return Config::LIMIT;"),
        "a reference to a struct-member const must qualify as Config::LIMIT:\n{header}"
    );
    compile_header(
        &header,
        "wi536nc",
        "static_assert(test::wi536nc::Config::LIMIT == 42);\n    \
         if (test::wi536nc::Config::get_limit() != 42) return 1;",
    );
}

#[test]
fn const_reference_across_namespaces_is_fully_qualified_and_compiles() {
    // A const declared in one namespace, referenced from another, is fully
    // qualified and pulls in the declaring namespace's header.
    let source = r#"
        namespace test.wi536def
          import anthill.prelude.{Int64}
          sort Config
            const LIMIT: Int64 = 7
            operation get_limit() -> Int64 = LIMIT
          end
        end

        namespace test.wi536use
          import anthill.prelude.{Int64}
          import test.wi536def.Config.{LIMIT}
          sort Reader
            operation read() -> Int64 = LIMIT
          end
        end
    "#;
    let kb = load_kb_with(source);
    let def_header = emit_namespace_header(&kb, "test.wi536def").expect("emit def header");
    let use_header = emit_namespace_header(&kb, "test.wi536use").expect("emit use header");
    assert!(
        use_header.contains("::test::wi536def::Config::LIMIT"),
        "cross-namespace const reference must be fully qualified:\n{use_header}"
    );
    assert!(
        use_header.contains("#include \"test_wi536def.hpp\""),
        "cross-namespace reference must pull in the declaring namespace header:\n{use_header}"
    );

    // Compile both headers together — proves the producer (`def`) and consumer
    // (`use`) agree on the include filename and the fully-qualified path.
    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler — skipping wi536 cross-namespace compile check");
            return;
        }
    };
    let dir = scratch_dir("wi536xns");
    std::fs::write(dir.join("test_wi536def.hpp"), &def_header).expect("write def");
    let use_path = dir.join("test_wi536use.hpp");
    std::fs::write(&use_path, &use_header).expect("write use");
    let driver = format!(
        "#include \"{}\"\n\nint main() {{\n    \
         if (test::wi536use::Reader::read() != 7) return 1;\n    return 0;\n}}\n",
        use_path.display()
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
        "cross-namespace headers failed to compile (compiler: {cxx})\n\
         ── def ───────────\n{def_header}\n── use ───────────\n{use_header}\n\
         ── stderr ───────────\n{}",
        String::from_utf8_lossy(&output.stderr),
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn const_referencing_another_const_emits_in_dependency_order_and_compiles() {
    // ALPHA references ZEBRA; emitted alphabetically ALPHA would precede ZEBRA,
    // but the topo-sort emits the dependency (ZEBRA) first so the constexpr
    // initializer names an already-declared constant. (Without the sort this is
    // a C++ use-before-declaration error.)
    let source = r#"
        namespace test.wi536topo
          import anthill.prelude.{Int64}
          const ZEBRA: Int64 = 1
          const ALPHA: Int64 = ZEBRA
          entity Marker(n: Int64)
        end
    "#;
    let kb = load_kb_with(source);
    let header = emit_namespace_header(&kb, "test.wi536topo").expect("emit ns header");
    let z = header.find("int64_t ZEBRA =").expect("ZEBRA declaration");
    let a = header.find("int64_t ALPHA =").expect("ALPHA declaration");
    assert!(
        z < a,
        "the dependency ZEBRA must be declared before ALPHA:\n{header}"
    );
    compile_header(
        &header,
        "wi536topo",
        "test::wi536topo::Marker m{1}; (void)m;\n    static_assert(test::wi536topo::ALPHA == 1);",
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
