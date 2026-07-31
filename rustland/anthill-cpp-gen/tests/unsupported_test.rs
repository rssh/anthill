//! Negative tests for the cpp17-stl profile's "unsupported feature"
//! error pass.
//!
//! Two classes of features cannot be lowered to RAII-only C++:
//!   1. Self-referential anonymous lambdas — `let f = lambda(?x) -> f(...)`.
//!      The emitted `[=](auto x){ return body; }` has no name in scope
//!      for `f`, and "fixing" it (Y-combinator or `std::function`) either
//!      bloats the call site or introduces refcounted heap closures.
//!   2. Runtime use of `anthill.reflect.*` / `anthill.persistence.*`
//!      sorts. Both rely on a hash-consed term store, which has no host
//!      counterpart in cpp17-stl.
//!
//! These tests assert that codegen rejects these inputs with a clear
//! error message, rather than emitting non-compilable C++.

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_runtime_header, emit_traits_struct};
use common::{find_cxx, load_kb_with, load_kb_with_lenient, scratch_dir};

/// Compile `driver` (which may `#include "anthill_runtime.hpp"`) at C++17 with
/// `-fsyntax-only`, returning `Some((succeeded, stderr))`. `None` means no C++
/// compiler is installed — the caller skips, matching the other compile tests.
/// The runtime header is written beside the driver so a template degrade's
/// `::anthill::runtime::dependent_false_v` resolves.
fn try_compile(test_name: &str, driver: &str) -> Option<(bool, String)> {
    let cxx = find_cxx()?;
    let dir = scratch_dir(test_name);
    std::fs::write(dir.join("anthill_runtime.hpp"), emit_runtime_header())
        .expect("write runtime header");
    let driver_path = dir.join("driver.cpp");
    std::fs::write(&driver_path, driver).expect("write driver");
    let output = Command::new(cxx)
        .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Wextra"])
        .arg(&driver_path)
        .output()
        .expect("invoke compiler");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let _ = std::fs::remove_dir_all(&dir);
    Some((output.status.success(), stderr))
}

#[test]
fn recursive_anonymous_lambda_rejected() {
    // `let f = lambda(?x) -> f(x)` — the lambda body refers to its own
    // binder. The IIFE lowering would emit
    //   auto f = [=](auto x){ return f(x); };
    // which doesn't compile (the inner `f` shadows nothing and the
    // outer `f` isn't visible inside its own initializer).
    //
    // WI-891: `synthesise_body_for` degrades this capability gap into a
    // build-breaking `static_assert` carrying the diagnostic — NOT the old
    // `// TODO … return {};`, which COMPILED and answered a zero-initialized
    // value. `Calc` is a non-generic sort, so the emitted method is not a
    // template and the assert is a plain `static_assert(false, …)`.
    let source = r#"
        namespace test.unsupported
          import anthill.prelude.{Int64}
          sort Calc
            operation lam(n: Int64) -> Int64 =
              let f = lambda x -> f(x)
              n
          end
        end
    "#;
    let mut kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&mut kb, "test.unsupported.Calc")
        .expect("emit_traits_struct degrades unsupported features to a static_assert");

    // The diagnostic rides a build-breaking `static_assert(false, …)`, and the
    // silently-wrong `return {};` is gone.
    assert!(
        cpp.contains("static_assert(false,"),
        "degrade must be a non-compiling static_assert, got:\n{cpp}"
    );
    assert!(
        cpp.contains("recursive anonymous lambda not supported"),
        "expected unsupported-recursive-lambda diagnostic in the assert, got:\n{cpp}"
    );
    assert!(
        cpp.contains("named operation"),
        "diagnostic should suggest lifting to a named operation:\n{cpp}"
    );
    assert!(
        !cpp.contains("return {};"),
        "the compiling zero-init degrade must be gone:\n{cpp}"
    );

    // And it actually fails the C++ build, carrying the message. A non-generic
    // sort's method is not a template, so `static_assert(false, …)` fires at the
    // definition — no instantiation needed.
    let driver = format!("#include <cstdint>\n{cpp}\nint main() {{ return 0; }}\n");
    if let Some((ok, stderr)) = try_compile("wi891_nontemplate", &driver) {
        assert!(!ok, "unlowerable non-template body must NOT compile:\n{driver}");
        assert!(
            stderr.contains("recursive anonymous lambda not supported in cpp17-stl"),
            "compiler diagnostic must carry the codegen-time message:\n{stderr}"
        );
    }
}

#[test]
fn degrade_inside_higher_kinded_sort_falls_back_to_plain_static_assert() {
    // WI-891 regression: `innermost_type_param` must SKIP a higher-kinded (template-
    // template) param. Its C++ decl is `template<typename...> class F`, so F is NOT a
    // type and `dependent_false_v<F>` is ill-formed — it would replace the codegen
    // diagnostic with a cryptic "template template parameter requires arguments" and
    // hard-fail the whole header (the exact failure WI-891 exists to remove). With only
    // an HK param in scope, the degrade must fall back to `static_assert(false, …)`,
    // which still carries the message.
    let source = r#"
        namespace test.wi891_hk
          import anthill.prelude.{Int64}
          sort Box[F[T]]
            operation weird(n: Int64) -> Int64 =
              let g = lambda x -> g(x)
              n
          end
        end
    "#;
    let mut kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&mut kb, "test.wi891_hk.Box").expect("emit Box");

    assert!(
        cpp.contains("template<template<typename...> class F>"),
        "F must be an HK template-template parameter:\n{cpp}"
    );
    assert!(
        !cpp.contains("dependent_false_v<F>"),
        "must NOT key dependent_false on the template-template param (ill-formed):\n{cpp}"
    );
    assert!(
        cpp.contains("static_assert(false,") && cpp.contains("recursive anonymous lambda not supported"),
        "HK-only scope must fall back to static_assert(false) carrying the message:\n{cpp}"
    );

    // Compiling it must never produce the ill-formed template-template kind error; if it
    // fails (clang/gcc fire `static_assert(false)` in a template member), it must fail
    // carrying the codegen message — not a cryptic kind error.
    let driver = format!("#include <cstdint>\n{cpp}\nint main() {{ return 0; }}\n");
    if let Some((ok, stderr)) = try_compile("wi891_hk", &driver) {
        assert!(
            !stderr.contains("template template parameter"),
            "must not emit the ill-formed dependent_false_v<F> kind error:\n{stderr}"
        );
        if !ok {
            assert!(
                stderr.contains("recursive anonymous lambda not supported in cpp17-stl"),
                "the failing diagnostic must carry the codegen message:\n{stderr}"
            );
        }
    }
}

#[test]
fn recursive_anonymous_lambda_in_template_struct_uses_dependent_false() {
    // WI-891 WATCH: the same degrade inside a TEMPLATE member cannot use a bare
    // `static_assert(false, …)` — that is ill-formed, no diagnostic required, in an
    // uninstantiated template (a conforming compiler may accept it and miscompile).
    // A generic sort makes the method a class-template member, so cpp-gen keys the
    // assert on the in-scope template parameter via `dependent_false_v<T>`: it fires
    // with a required diagnostic exactly when the member is instantiated, never eagerly.
    let source = r#"
        namespace test.unsupported_tmpl
          import anthill.prelude.{Int64}
          sort Calc
            sort T = ?
            operation lam(n: Int64) -> Int64 =
              let f = lambda x -> f(x)
              n
          end
        end
    "#;
    let mut kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&mut kb, "test.unsupported_tmpl.Calc")
        .expect("emit generic Calc traits");

    assert!(
        cpp.contains("template<typename T>"),
        "generic sort must emit a class template:\n{cpp}"
    );
    assert!(
        cpp.contains("static_assert(::anthill::runtime::dependent_false_v<T>,"),
        "a template member's degrade must depend on the template parameter:\n{cpp}"
    );
    assert!(
        !cpp.contains("static_assert(false"),
        "must NOT use the IFNDR-prone bare static_assert inside a template:\n{cpp}"
    );

    // Uninstantiated, the dependent assert does NOT fire: the header compiles clean.
    let base = format!("#include <cstdint>\n#include \"anthill_runtime.hpp\"\n{cpp}\n");
    if let Some((ok, stderr)) = try_compile(
        "wi891_template_uninstantiated",
        &format!("{base}int main() {{ return 0; }}\n"),
    ) {
        assert!(
            ok,
            "uninstantiated template degrade must compile (dependent-false, no eager \
             misfire):\n{stderr}"
        );
    }

    // Instantiated, it fires — the build fails carrying the codegen-time message.
    if let Some((ok, stderr)) = try_compile(
        "wi891_template_instantiated",
        &format!("{base}int main() {{ (void)Calc<int>::lam(0); return 0; }}\n"),
    ) {
        assert!(!ok, "instantiating the unlowerable template member must NOT compile");
        assert!(
            stderr.contains("recursive anonymous lambda not supported in cpp17-stl"),
            "compiler diagnostic must carry the codegen-time message:\n{stderr}"
        );
    }
}

#[test]
fn non_recursive_let_lambda_still_works() {
    // Sanity check: a `let f = lambda(?x) -> add(x, 1)` (no self-ref)
    // must still lower successfully. The detector keys on the binder
    // name appearing inside the lambda body — when it doesn't, the
    // existing IIFE + generic-lambda emission applies unchanged.
    let source = r#"
        namespace test.unsupported_ok
          import anthill.prelude.{Int64}
          sort Calc
            operation lam(n: Int64) -> Int64 =
              let g = lambda x -> add(x, 1)
              n
          end
        end
    "#;
    let mut kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&mut kb, "test.unsupported_ok.Calc")
        .expect("non-recursive lambda must still lower");
    assert!(
        cpp.contains("[=](auto x) { return (x + 1); }"),
        "non-recursive lambda body should lower normally:\n{cpp}"
    );
}

#[test]
fn reflect_sort_in_signature_rejected() {
    // An operation whose return type is `TermRepr` (from anthill.reflect)
    // requires the host language to have a hash-consed term store. The
    // cpp17-stl profile has none, so codegen must refuse.
    let source = r#"
        namespace test.unsupported_reflect
          import anthill.reflect.{TermRepr}
          sort Inspector
            operation peek() -> TermRepr
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let err = emit_traits_struct(&mut kb, "test.unsupported_reflect.Inspector")
        .expect_err("reflect sort in op signature must be rejected");

    let msg = err.to_string();
    assert!(
        msg.contains("does not support runtime reflection"),
        "expected reflection-unsupported diagnostic, got: {msg}"
    );
    assert!(
        msg.contains("anthill.reflect.TermRepr"),
        "diagnostic should name the offending sort: {msg}"
    );
}

#[test]
fn persistence_sort_in_signature_rejected() {
    // Same idea for `anthill.persistence.Store`: a host with no
    // serialization story for live anthill terms cannot honor the
    // operation surface, so codegen refuses up front.
    let source = r#"
        namespace test.unsupported_persistence
          import anthill.persistence.{Store}
          import anthill.prelude.{Unit}
          sort Bridge
            operation tell(s: Store) -> Unit
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let err = emit_traits_struct(&mut kb, "test.unsupported_persistence.Bridge")
        .expect_err("persistence sort in op signature must be rejected");

    let msg = err.to_string();
    assert!(
        msg.contains("does not support runtime persistence"),
        "expected persistence-unsupported diagnostic, got: {msg}"
    );
    assert!(
        msg.contains("anthill.persistence.Store"),
        "diagnostic should name the offending sort: {msg}"
    );
}
