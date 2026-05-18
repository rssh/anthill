//! Phase E: typeclass operator dispatch.
//!
//! Calls to prelude typeclass methods get rewritten to their C++
//! operator equivalents:
//!   - Numeric.{add, sub, mul} → + - *
//!   - Int.div / Float.div / Int.mod → / / %
//!   - Ordered.{gt, lt, gte, lte} → > < >= <=
//!   - Eq.{eq, neq} → == !=
//!   - Bool.{and, or, not} → && || !
//!   - Int.neg / Float.neg → unary -
//!
//! User-defined functions with the same short name don't dispatch
//! (the rewrite keys on the full qualified name).
//!
//! Out of scope (later phases): effect-aware return wrapping
//! (`tl::expected<T, Error>`), do-blocks, statement-position lowering.

use super::common;

use std::process::Command;

use anthill_cpp_gen::emit_traits_struct;
use common::{find_cxx, load_kb_with, scratch_dir};

#[test]
fn numeric_add_emits_plus() {
    let source = r#"
        namespace test.expr_e_add
          import anthill.prelude.{Int}
          export Calc
          sort Calc
            operation inc(x: Int) -> Int = add(x, 1)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_e_add.Calc")
        .expect("emit Calc");
    assert!(
        cpp.contains("return (x + 1);"),
        "add(x, 1) should become (x + 1):\n{cpp}"
    );
}

#[test]
fn numeric_sub_mul_emit_operators() {
    let source = r#"
        namespace test.expr_e_arith
          import anthill.prelude.{Int}
          export Calc
          sort Calc
            operation diff(a: Int, b: Int) -> Int = sub(a, b)
            operation prod(a: Int, b: Int) -> Int = mul(a, b)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_e_arith.Calc")
        .expect("emit Calc");
    assert!(cpp.contains("return (a - b);"), "sub:\n{cpp}");
    assert!(cpp.contains("return (a * b);"), "mul:\n{cpp}");
}

#[test]
fn ordered_comparators_emit_relational_ops() {
    let source = r#"
        namespace test.expr_e_cmp
          import anthill.prelude.{Int, Bool}
          export Calc
          sort Calc
            operation g(a: Int, b: Int)  -> Bool = gt(a, b)
            operation l(a: Int, b: Int)  -> Bool = lt(a, b)
            operation ge(a: Int, b: Int) -> Bool = gte(a, b)
            operation le(a: Int, b: Int) -> Bool = lte(a, b)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_e_cmp.Calc")
        .expect("emit Calc");
    assert!(cpp.contains("return (a > b);"),  "gt:\n{cpp}");
    assert!(cpp.contains("return (a < b);"),  "lt:\n{cpp}");
    assert!(cpp.contains("return (a >= b);"), "gte:\n{cpp}");
    assert!(cpp.contains("return (a <= b);"), "lte:\n{cpp}");
}

#[test]
fn eq_neq_emit_double_equals() {
    let source = r#"
        namespace test.expr_e_eq
          import anthill.prelude.{Int, Bool}
          import anthill.prelude.Eq.{eq, neq}
          export Calc
          sort Calc
            operation same(a: Int, b: Int) -> Bool = eq(a, b)
            operation diff(a: Int, b: Int) -> Bool = neq(a, b)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_e_eq.Calc")
        .expect("emit Calc");
    assert!(cpp.contains("return (a == b);"), "eq:\n{cpp}");
    assert!(cpp.contains("return (a != b);"), "neq:\n{cpp}");
}

#[test]
fn bool_logical_ops_emit_and_or_not() {
    let source = r#"
        namespace test.expr_e_bool
          import anthill.prelude.{Bool}
          import anthill.prelude.Bool.{and, or, not}
          export Calc
          sort Calc
            operation both(a: Bool, b: Bool) -> Bool = and(a, b)
            operation any(a: Bool, b: Bool)  -> Bool = or(a, b)
            operation flip(a: Bool)          -> Bool = not(a)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_e_bool.Calc")
        .expect("emit Calc");
    assert!(cpp.contains("return (a && b);"), "and:\n{cpp}");
    assert!(cpp.contains("return (a || b);"), "or:\n{cpp}");
    assert!(cpp.contains("return (!a);"),     "not:\n{cpp}");
}

#[test]
fn user_named_add_does_not_get_rewritten() {
    // A user op named `add` (in the user's namespace, not Numeric)
    // should NOT be rewritten — the operator-dispatch table keys on
    // the full qualified name, so user code passes through as a
    // plain function call.
    let source = r#"
        namespace test.expr_e_user
          import anthill.prelude.{Int}
          export Calc
          sort Calc
            operation add(a: Int, b: Int) -> Int = a
            operation use(a: Int, b: Int) -> Int = add(a, b)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_e_user.Calc")
        .expect("emit Calc");
    assert!(
        cpp.contains("return add(a, b);"),
        "user-defined `add` should stay as a function call:\n{cpp}"
    );
}

#[test]
fn arithmetic_in_if_compiles() {
    // End-to-end: clang accepts the operator-rewritten code.
    let source = r#"
        namespace test.expr_e_compile
          import anthill.prelude.{Int}
          export Calc
          sort Calc
            operation abs(n: Int) -> Int = if gt(n, 0) then n else sub(0, n)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.expr_e_compile.Calc")
        .expect("emit Calc");

    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler — skipping arithmetic compile check");
            return;
        }
    };
    let dir = scratch_dir("expr_e_arith");
    let driver = format!(
        r#"#include <cstdint>

namespace test::expr_e_compile {{

{traits}
}}

int main() {{
    auto v = test::expr_e_compile::Calc::abs(-3);
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
            "Phase E compile failed (compiler: {cxx})\n\
             ── traits ───────────\n{traits}\n\
             ── driver ───────────\n{driver}\n\
             ── stderr ───────────\n{stderr}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
