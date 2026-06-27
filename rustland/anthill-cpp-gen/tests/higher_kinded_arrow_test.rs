//! WI-575 (proposal 002, the (e)+(f) tail split out of WI-095): C++ codegen
//! for arrow-sorted operation params and higher-kinded sort carriers.
//!
//! Covers:
//! - an arrow-typed op param `f: (A) -> F[T = B]` lowers to
//!   `std::function<F<B>(A)>` (effects erased)
//! - a higher-kinded sort carrier `sort Spec[F[T]]` emits a C++
//!   template-template parameter `template<typename...> class F`
//! - a use of the carrier `F[T = A]` lowers to `F<A>`
//! - a multi-param / effectful arrow still lowers (params → arg list,
//!   effects dropped)

use super::common;

use std::process::Command;

use anthill_cpp_gen::emit_traits_struct;
use common::{find_cxx, load_kb_with_lenient, scratch_dir};

#[test]
fn hk_monad_traits_lowers_arrow_and_template_template() {
    // `Monad[F[T], A, B]`: F is the higher-kinded carrier; A and B are
    // first-order element params (kept at sort level so the test stays
    // about codegen, not per-operation generics).
    let source = r#"
        namespace test.hk_monad
          sort Monad[F[T], A, B]
            operation flatMap(fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.hk_monad.Monad").expect("emit Monad");

    // (f) higher-kinded carrier → template-template parameter; first-order
    // params stay `typename`.
    assert!(
        cpp.contains("template<template<typename...> class F, typename A, typename B>"),
        "HK carrier should emit a template-template parameter:\n{cpp}"
    );
    // (f) carrier use `F[T = A]` / `F[T = B]` → `F<A>` / `F<B>`.
    assert!(
        cpp.contains("F<A> fa"),
        "carrier use `F[T = A]` should lower to `F<A>`:\n{cpp}"
    );
    // (e) arrow param `(A) -> F[T = B]` → `std::function<F<B>(A)>`.
    assert!(
        cpp.contains("std::function<F<B>(A)> f"),
        "arrow param should lower to std::function:\n{cpp}"
    );
    // Return type `F[T = B]` → `F<B>`.
    assert!(
        cpp.contains("static F<B> flatMap("),
        "return type should lower to `F<B>`:\n{cpp}"
    );
}

#[test]
fn pure_arrow_param_lowers_to_std_function() {
    // First-order `map`: the arrow callback is pure `(A) -> B`.
    let source = r#"
        namespace test.fmap
          sort Functor[F[T], A, B]
            operation map(fa: F[T = A], f: (A) -> B) -> F[T = B]
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.fmap.Functor").expect("emit Functor");

    assert!(
        cpp.contains("std::function<B(A)> f"),
        "pure arrow `(A) -> B` should lower to `std::function<B(A)>`:\n{cpp}"
    );
}

#[test]
fn multi_param_and_effectful_arrow_lower() {
    // A binary arrow with an effect annotation: params become the arg list,
    // the effect row is erased at the C++ type level.
    let source = r#"
        namespace test.binop
          import anthill.prelude.{Int64, String}
          sort Calc
            operation run(f: (Int64, String) -> Int64 @ {Modify[Calc]}) -> Int64
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.binop.Calc").expect("emit Calc");

    assert!(
        cpp.contains("std::function<int64_t(int64_t, std::string)> f"),
        "multi-param effectful arrow should lower with effects erased:\n{cpp}"
    );
}

#[test]
fn non_hk_param_stays_typename() {
    // Regression: a plain first-order sort param must keep `typename T`
    // (the higher-kinded path is only for carriers with nested params).
    let source = r#"
        namespace test.box1
          sort Box
            sort T = ?
            operation unwrap(b: ?T) -> ?T = b
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.box1.Box").expect("emit Box");

    assert!(
        cpp.contains("template<typename T>"),
        "first-order param should stay `typename T`:\n{cpp}"
    );
    assert!(
        !cpp.contains("template<typename...> class T"),
        "first-order param must NOT become a template-template parameter:\n{cpp}"
    );
}

#[test]
fn first_order_param_applied_is_a_loud_error() {
    // Guard: a FIRST-ORDER param `T` used in application position (`T[X = ?]`,
    // a kind error) must NOT lower to `T<…>` against a `typename T` slot.
    // `lower_parameterized` only treats a genuinely higher-kinded base as a
    // template-template application; a first-order base falls through to the
    // loud "no C++ mapping" error rather than silently emitting invalid C++.
    let source = r#"
        namespace test.kind_err
          sort Bad
            sort T = ?
            sort X = ?
            operation oops(v: T[X = ?X]) -> Int64
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let result = emit_traits_struct(&kb, "test.kind_err.Bad");
    match result {
        Err(e) => assert!(
            e.message.contains("no C++ mapping"),
            "expected a loud 'no C++ mapping' error for an applied first-order \
             param, got: {}",
            e.message
        ),
        Ok(cpp) => assert!(
            !cpp.contains("T<"),
            "a first-order param applied as `T[X = ?X]` must not lower to `T<…>`:\n{cpp}"
        ),
    }
}

#[test]
fn hk_monad_traits_compiles() {
    // The emitted traits struct must be syntactically valid C++. The
    // template is declaration-only (never instantiated), so a syntax-only
    // pass validates the template-template parameter, the dependent `F<…>`
    // uses, and the `std::function` callback all parse.
    let source = r#"
        namespace test.hk_compile
          sort Monad[F[T], A, B]
            operation flatMap(fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let traits = emit_traits_struct(&kb, "test.hk_compile.Monad").expect("emit Monad");

    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping compile check");
            return;
        }
    };

    // `emit_traits_struct` returns just the struct; supply the includes the
    // standalone entry point doesn't gather (`<functional>` for the arrow).
    let header = format!("#pragma once\n#include <functional>\n\n{traits}\n");
    let dir = scratch_dir("hk_monad_compile");
    let header_path = dir.join("monad.hpp");
    std::fs::write(&header_path, &header).expect("write header");

    let driver = format!("#include \"{}\"\nint main() {{ return 0; }}\n", header_path.display());
    let driver_path = dir.join("driver.cpp");
    std::fs::write(&driver_path, &driver).expect("write driver");

    let output = Command::new(cxx)
        .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Wextra"])
        .arg(&driver_path)
        .output()
        .expect("invoke compiler");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!(
            "C++ compile failed (compiler: {cxx})\n\
             ── header.hpp ───────────────────────\n{header}\n\
             ── stderr ───────────────────────────\n{stderr}"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
