//! Phase B expression-body lowering tests: `if-then-else` and field
//! access (`obj.field`).
//!
//! Phase A handled literals, parameter references, and function
//! calls. Phase B adds:
//!   - if-then-else  → C++ ternary `(cond ? then : else)`
//!   - field access  → C++ dot-projection `obj.field`
//!
//! Out of scope (later phases): let, lambda, match, constructor
//! literals, typeclass operator dispatch.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::{load_kb_with, load_kb_with_lenient};

#[test]
fn if_then_else_literal_branches() {
    // The simplest form: condition is a function call returning Bool,
    // both branches are literals. Lowered as C++ ternary so the body
    // can be emitted as a single `return` expression.
    let source = r#"
        namespace test.expr_b
          import anthill.prelude.{Int64, Bool}
          export Calc
          sort Calc
            operation pick(b: Bool) -> Int64 = if b then 1 else 0
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_b.Calc")
        .expect("emit Calc traits");

    assert!(
        cpp.contains("static int64_t pick(bool b) {\n        return (b ? 1 : 0);\n    }"),
        "if-then-else with literal branches missing or wrong:\n{cpp}"
    );
}

#[test]
fn if_then_else_with_call_in_condition() {
    // Condition is a typeclass function call (`gt(n, 0)`) and the
    // then-branch is a parameter reference. Phase A's call lowering
    // is reused for the condition.
    let source = r#"
        namespace test.expr_b
          import anthill.prelude.{Int64, Bool}
          export Calc
          sort Calc
            operation abs(n: Int64) -> Int64 = if gt(n, 0) then n else 0
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_b.Calc")
        .expect("emit Calc");

    // Phase E rewrites `gt(n, 0)` to `(n > 0)` because gt is the
    // anthill.prelude.Ordered.gt typeclass operation.
    assert!(
        cpp.contains("static int64_t abs(int64_t n) {\n        return ((n > 0) ? n : 0);\n    }"),
        "if-then-else with call condition missing:\n{cpp}"
    );
}

#[test]
fn nested_if_then_else() {
    // The else-branch is itself an if-expression. The outer recursion
    // in lower_expr should lower the nested if without trouble.
    let source = r#"
        namespace test.expr_b
          import anthill.prelude.{Int64, Bool}
          export Calc
          sort Calc
            operation sign(b1: Bool, b2: Bool) -> Int64 =
              if b1 then 1 else if b2 then 0 else (-1)
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_traits_struct(&kb, "test.expr_b.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("(b1 ? 1 : (b2 ? 0 : -1))"),
        "nested if-then-else missing or wrong:\n{cpp}"
    );
}

#[test]
fn field_access_emits_dot_syntax() {
    // `(p).x` is a value-receiver field access: the loader re-routes it to a
    // zero-arg `DotApply` (WI-280) and the typer's field fallback rewrites it
    // to `field_access(p, "x")` once it resolves `x` against `Pose` — which,
    // as a free-standing entity, is its own constructor (WI-490). The lowering
    // recognises the `field_access` functor and emits dot syntax.
    //
    // The lenient loader is retained so the test is robust to unrelated load
    // diagnostics; the field access itself now type-checks cleanly.
    let source = r#"
        namespace test.expr_b_field
          import anthill.prelude.{Float}
          export Pose, Calc
          entity Pose(x: Float, y: Float)
          sort Calc
            operation pos_x(p: Pose) -> Float = (p).x
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.expr_b_field.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("return p.x;"),
        "field access should emit `p.x`, got:\n{cpp}"
    );
}

#[test]
fn field_access_in_expression_position() {
    // Field access used inside a call: the field_access desugaring
    // should still emit dot syntax even when the result feeds a
    // surrounding expression.
    let source = r#"
        namespace test.expr_b_field2
          import anthill.prelude.{Float}
          export Pose, Calc
          entity Pose(x: Float, y: Float)
          sort Calc
            operation sum_xy(p: Pose) -> Float = add((p).x, (p).y)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.expr_b_field2.Calc")
        .expect("emit Calc");

    // Phase E rewrites `add(p.x, p.y)` to `(p.x + p.y)` since add is
    // the anthill.prelude.Numeric.add typeclass method.
    assert!(
        cpp.contains("return (p.x + p.y);"),
        "nested field access in arithmetic should produce (p.x + p.y):\n{cpp}"
    );
}
