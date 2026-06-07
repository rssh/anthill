//! Phase A expression-body lowering tests.
//!
//! Covers: literal returns, parameter-reference returns, simple
//! function-call returns. Out of scope (later phases): if-then-else,
//! let, lambda, match, typeclass operator dispatch (`add` → `+`),
//! constructor literals (`Vec3{x: 1, ...}`).

use super::common;

use std::process::Command;

use anthill_cpp_gen::emit_traits_struct;
use common::{find_cxx, load_kb_with, scratch_dir};

#[test]
fn literal_int_body() {
    let source = r#"
        namespace test.expr_a
          import anthill.prelude.{Int64}
          export Calc
          sort Calc
            operation forty_two() -> Int64 = 42
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_a.Calc")
        .expect("emit Calc traits");

    assert!(
        cpp.contains("static int64_t forty_two() {\n        return 42;\n    }"),
        "literal int body missing or wrong:\n{cpp}"
    );
}

#[test]
fn literal_float_and_string_bodies() {
    let source = r#"
        namespace test.expr_a
          import anthill.prelude.{Float, String}
          export Constants
          sort Constants
            operation pi()    -> Float  = 3.14
            operation hello() -> String = "world"
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_a.Constants")
        .expect("emit Constants");

    assert!(
        cpp.contains("static double pi() {\n        return 3.14;\n    }"),
        "pi body missing:\n{cpp}"
    );
    assert!(
        cpp.contains("static std::string hello() {\n        return \"world\";\n    }"),
        "hello body missing:\n{cpp}"
    );
}

#[test]
fn parameter_reference_body() {
    // `id(x: Int64) -> Int64 = x` — body is just a variable reference,
    // emits the parameter name.
    let source = r#"
        namespace test.expr_a
          import anthill.prelude.{Int64}
          export Identity
          sort Identity
            operation id(x: Int64) -> Int64 = x
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_a.Identity")
        .expect("emit Identity");

    assert!(
        cpp.contains("static int64_t id(int64_t x) {\n        return x;\n    }"),
        "param-ref body missing or wrong:\n{cpp}"
    );
}

#[test]
fn simple_function_call_body() {
    // A user-defined op in the same sort emits as a plain call — no
    // operator rewrite kicks in because the QN doesn't match the
    // prelude typeclass dispatch table.
    let source = r#"
        namespace test.expr_a
          import anthill.prelude.{Int64}
          export Counter
          sort Counter
            operation step(x: Int64) -> Int64 = x
            operation use(x: Int64) -> Int64 = step(x)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_a.Counter")
        .expect("emit Counter");

    assert!(
        cpp.contains("static int64_t use(int64_t x) {\n        return step(x);\n    }"),
        "simple-call body missing or wrong:\n{cpp}"
    );
}

#[test]
fn nested_call_body() {
    // `triple_inc(x: Int64) -> Int64 = inc(inc(inc(x)))` — recursive call
    // lowering, exercises lower_expr's recursion on Term::Fn args.
    let source = r#"
        namespace test.expr_a
          import anthill.prelude.{Int64}
          export NestedCalls
          sort NestedCalls
            operation inc(x: Int64) -> Int64 = x
            operation triple_inc(x: Int64) -> Int64 = inc(inc(inc(x)))
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_a.NestedCalls")
        .expect("emit NestedCalls");

    assert!(
        cpp.contains("static int64_t triple_inc(int64_t x) {\n        return inc(inc(inc(x)));\n    }"),
        "nested-call body missing or wrong:\n{cpp}"
    );
}

#[test]
fn expression_body_takes_precedence_over_carrier_dispatch() {
    // If an op has BOTH a carrier (so dispatch is possible) AND an
    // expression body, the expression body wins. This protects the
    // user's explicit override against being silently replaced by
    // the auto-dispatch path.
    let source = r#"
        namespace test.expr_a
          import anthill.prelude.{Int64}
          import anthill.realization.{Implementation, CarrierBinding}
          export Calc
          sort Calc
            operation get(self: Calc) -> Int64 = 99
          end
          fact Implementation(
            target:        "test.expr_a.Calc",
            artifact:      "calc.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Calc",
                                           host_type: "::vendor::Calc *")],
            namespace_map: []
          )
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_a.Calc")
        .expect("emit Calc");

    // Body is the literal 99 (expression body wins) — not self->get().
    assert!(
        cpp.contains("static int64_t get(::vendor::Calc * self) {\n        return 99;\n    }"),
        "expression body should override carrier dispatch:\n{cpp}"
    );
    assert!(
        !cpp.contains("self->get()"),
        "should not have fallen through to carrier dispatch:\n{cpp}"
    );
}

#[test]
fn literal_int_body_compiles() {
    // End-to-end: emit a literal-bodied op and verify it compiles.
    let source = r#"
        namespace test.expr_a_compile
          import anthill.prelude.{Int64}
          export Calc
          sort Calc
            operation forty_two() -> Int64 = 42
          end
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.expr_a_compile.Calc")
        .expect("emit Calc");

    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler — skipping expr-body compile check");
            return;
        }
    };
    let dir = scratch_dir("expr_a_literal");
    let driver = format!(
        r#"#include <cstdint>

namespace test::expr_a_compile {{

{traits}
}}

int main() {{
    auto v = test::expr_a_compile::Calc::forty_two();
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
            "literal-body compile failed (compiler: {cxx})\n\
             ── traits ───────────\n{traits}\n\
             ── driver ───────────\n{driver}\n\
             ── stderr ───────────\n{stderr}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
