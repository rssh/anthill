//! Phase D expression-body lowering tests: match expressions,
//! constructor literals, and collection literals.
//!
//! Phase C handled let chains and lambdas. Phase D adds:
//!   - match (over sum-sort variants) → chained
//!     `std::holds_alternative<T>(s) ? body : next` ternary
//!   - constructor literals             → `EntityName{val0, val1, …}`
//!     ordered by entity field declaration
//!   - list / tuple / set literals      → uniform brace-init `{…}`
//!
//! Out of scope (later phases): match patterns that bind values
//! (`case Pose(x: ?vx) ->`), guards, wildcards mixed with literals,
//! typeclass operator dispatch, effect-aware return wrapping.

use super::common;

use std::process::Command;

use anthill_cpp_gen::emit_traits_struct;
use common::{find_cxx, load_kb_with_lenient, scratch_dir};

#[test]
fn entity_constructor_literal_emits_brace_init() {
    let source = r#"
        namespace test.expr_d
          import anthill.prelude.{Int64}
          entity Pose(x: Int64, y: Int64)
          sort Calc
            operation make_pose(x: Int64) -> Pose = Pose(x: x, y: 0)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.expr_d.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("return Pose{x, 0};"),
        "constructor literal should emit Pose{{x, 0}}:\n{cpp}"
    );
}

#[test]
fn entity_constructor_named_args_reorder_to_field_order() {
    // Source uses named args in reverse declaration order; the
    // emitted brace-init must reorder values to the field-declaration
    // order so the resulting C++ matches the struct layout.
    let source = r#"
        namespace test.expr_d_reorder
          import anthill.prelude.{Int64}
          entity Pose(x: Int64, y: Int64)
          sort Calc
            operation make_pose(a: Int64, b: Int64) -> Pose = Pose(y: b, x: a)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.expr_d_reorder.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("return Pose{a, b};"),
        "named-arg reorder failed (expected Pose{{a, b}}):\n{cpp}"
    );
}

#[test]
fn list_literal_emits_brace_init() {
    let source = r#"
        namespace test.expr_d_list
          import anthill.prelude.{Int64, List}
          sort Calc
            operation triple(x: Int64) -> List[T = Int64] = [x, 1, 2]
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.expr_d_list.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("return {x, 1, 2};"),
        "list literal should emit `{{x, 1, 2}}`:\n{cpp}"
    );
}

#[test]
fn match_over_nullary_sum_emits_holds_alternative_chain() {
    // `Color = Red | Green | Blue` (each nullary) ⇒ Color carrier is
    // `std::variant<Red, Green, Blue>`. Match dispatches on the
    // active alternative via `std::holds_alternative<…>`.
    let source = r#"
        namespace test.expr_d_match
          import anthill.prelude.{Int64}
          enum Color
            entity Red
            entity Green
            entity Blue
          end
          sort Calc
            operation tag(c: Color) -> Int64 =
              match c
                case Red -> 0
                case Green -> 1
                case Blue -> 2
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.expr_d_match.Calc")
        .expect("emit Calc");

    // The last branch falls through unconditionally — innermost arm
    // is just `2`, the previous two test their tags.
    assert!(
        cpp.contains(
            "(std::holds_alternative<Red>(c) ? 0 : \
             (std::holds_alternative<Green>(c) ? 1 : 2))"
        ),
        "match over nullary sum should emit holds_alternative chain:\n{cpp}"
    );
}

#[test]
fn match_with_let_in_branch_body() {
    // Phase C and Phase D compose: a `let` body inside a match arm
    // should keep its IIFE shape inside the ternary.
    let source = r#"
        namespace test.expr_d_compose
          import anthill.prelude.{Int64}
          enum Sign
            entity Pos
            entity Neg
          end
          sort Calc
            operation pick(s: Sign, n: Int64) -> Int64 =
              match s
                case Pos ->
                  let k = add(n, 1)
                  add(k, k)
                case Neg -> 0
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.expr_d_compose.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("std::holds_alternative<Pos>(s)"),
        "match dispatch missing:\n{cpp}"
    );
    assert!(
        cpp.contains("[&]() { auto k = (n + 1); return (k + k); }()"),
        "let-IIFE in match branch missing:\n{cpp}"
    );
}

#[test]
fn entity_constructor_literal_compiles() {
    // End-to-end: brace-init compiles against the entity struct emitted
    // by `emit_entity_struct`.
    let source = r#"
        namespace test.expr_d_compile
          import anthill.prelude.{Int64}
          entity Pose(x: Int64, y: Int64)
          sort Calc
            operation origin() -> Pose = Pose(x: 0, y: 0)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let traits = emit_traits_struct(&kb, "test.expr_d_compile.Calc")
        .expect("emit Calc");

    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler — skipping constructor-literal compile check");
            return;
        }
    };
    let dir = scratch_dir("expr_d_ctor");
    let driver = format!(
        r#"#include <cstdint>

namespace test::expr_d_compile {{

struct Pose {{
    int64_t x;
    int64_t y;
}};

{traits}
}}

int main() {{
    auto p = test::expr_d_compile::Calc::origin();
    (void)p;
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
            "constructor literal compile failed (compiler: {cxx})\n\
             ── traits ───────────\n{traits}\n\
             ── driver ───────────\n{driver}\n\
             ── stderr ───────────\n{stderr}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
