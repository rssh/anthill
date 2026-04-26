//! Phase C expression-body lowering tests: `let` chains and
//! `lambda` expressions.
//!
//! Phase B handled if-then-else and field access. Phase C adds:
//!   - let-chain    → C++ IIFE `[&]() { auto x = ...; return ...; }()`
//!     with chain flattening so nested lets share one IIFE
//!   - lambda       → C++ generic lambda `[=](auto x) { return ...; }`
//!
//! Out of scope (later phases): match, constructor literals, list
//! literals, typeclass operator dispatch.

use super::common;

use std::process::Command;

use anthill_cpp_gen::emit_traits_struct;
use common::{find_cxx, load_kb_with, load_kb_with_lenient, scratch_dir};

#[test]
fn single_let_emits_iife() {
    let source = r#"
        namespace test.expr_c
          import anthill.prelude.{Int}
          export Calc
          sort Calc
            operation step(n: Int) -> Int =
              let x = add(n, 1)
              add(x, x)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_c.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("[&]() { auto x = (n + 1); return (x + x); }()"),
        "single let should compile to flat IIFE:\n{cpp}"
    );
}

#[test]
fn nested_let_chain_flattened() {
    // Two lets in sequence — should produce one IIFE with both
    // bindings, not nested IIFEs (which would be ugly and slower
    // for the optimizer to inline).
    let source = r#"
        namespace test.expr_c
          import anthill.prelude.{Int}
          export Calc
          sort Calc
            operation chain(n: Int) -> Int =
              let a = add(n, 1)
              let b = add(a, 2)
              add(a, b)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_c.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("[&]() { auto a = (n + 1); auto b = (a + 2); return (a + b); }()"),
        "nested let should flatten into one IIFE:\n{cpp}"
    );
}

#[test]
fn let_with_if_in_body() {
    // The body of the let is itself an if-then-else — phases B and C
    // compose naturally because lower_expr is fully recursive.
    let source = r#"
        namespace test.expr_c
          import anthill.prelude.{Int, Bool}
          export Calc
          sort Calc
            operation pick(n: Int, b: Bool) -> Int =
              let x = add(n, 1)
              if b then x else 0
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_c.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("[&]() { auto x = (n + 1); return (b ? x : 0); }()"),
        "let with if body missing or wrong:\n{cpp}"
    );
}

#[test]
fn lambda_emits_generic_lambda() {
    // `lambda x -> add(x, n)` becomes `[=](auto x) { return add(x, n); }`.
    // We use generic-lambda + by-value capture so the result composes
    // with std::function or `auto`-typed callables without needing
    // a declared signature.
    //
    // The type checker rejects "lambda as return value of Int op", so
    // we use the lenient loader — the lowering itself is what we test.
    let source = r#"
        namespace test.expr_c
          import anthill.prelude.{Int}
          export Calc
          sort Calc
            operation lam(n: Int) -> Int = lambda x -> add(x, n)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.expr_c.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("[=](auto x) { return (x + n); }"),
        "lambda body missing or wrong:\n{cpp}"
    );
}

#[test]
fn let_iife_compiles() {
    // End-to-end: emit a let-bodied op and verify clang accepts the
    // resulting IIFE syntax under -std=c++17.
    let source = r#"
        namespace test.expr_c_compile
          import anthill.prelude.{Int}
          export Calc
          sort Calc
            operation forty_two() -> Int =
              let x = 21
              let y = 21
              add(x, y)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.expr_c_compile.Calc")
        .expect("emit Calc");

    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler — skipping let-IIFE compile check");
            return;
        }
    };
    let dir = scratch_dir("expr_c_let");
    let driver = format!(
        r#"#include <cstdint>

namespace test::expr_c_compile {{

inline int64_t add(int64_t a, int64_t b) {{ return a + b; }}

{traits}
}}

int main() {{
    auto v = test::expr_c_compile::Calc::forty_two();
    (void)v;
    return 0;
}}
"#
    );
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
            "let-IIFE compile failed (compiler: {cxx})\n\
             ── traits ───────────\n{traits}\n\
             ── driver ───────────\n{driver}\n\
             ── stderr ───────────\n{stderr}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
