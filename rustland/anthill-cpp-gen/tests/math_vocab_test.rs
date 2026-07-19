//! `anthill.prelude.Float.{sin, cos, atan2, hypot, log10, fmod, abs,
//! sqrt, pi, e, tau, ...}` lower to the corresponding `std::` functions
//! and `<cmath>` is added to the namespace header's include block.
//!
//! Math constants (`pi`, `e`, `tau`) used as bare values lower to
//! numeric literals (works in C++17 without needing `<numbers>`).

use super::common;

use anthill_cpp_gen::{emit_namespace_header, emit_traits_struct};
use common::load_kb_with;

#[test]
fn float_trig_calls_lower_to_std() {
    let source = r#"
        namespace test.math_trig
          import anthill.prelude.{Float}
          import anthill.prelude.Float.{sin, cos, atan2}
          sort Calc
            operation s(x: Float) -> Float = sin(x)
            operation c(x: Float) -> Float = cos(x)
            operation a(y: Float, x: Float) -> Float = atan2(y, x)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.math_trig.Calc")
        .expect("emit Calc");
    assert!(cpp.contains("return std::sin(x);"),       "sin:\n{cpp}");
    assert!(cpp.contains("return std::cos(x);"),       "cos:\n{cpp}");
    assert!(cpp.contains("return std::atan2(y, x);"),  "atan2:\n{cpp}");
}

#[test]
fn float_misc_math_calls_lower_to_std() {
    let source = r#"
        namespace test.math_misc
          import anthill.prelude.{Float}
          import anthill.prelude.Float.{sqrt, hypot, log10, fmod}
          sort Calc
            operation r(x: Float) -> Float = sqrt(x)
            operation h(a: Float, b: Float) -> Float = hypot(a, b)
            operation l(x: Float) -> Float = log10(x)
            operation m(a: Float, b: Float) -> Float = fmod(a, b)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.math_misc.Calc")
        .expect("emit Calc");
    assert!(cpp.contains("return std::sqrt(x);"),       "sqrt:\n{cpp}");
    assert!(cpp.contains("return std::hypot(a, b);"),   "hypot:\n{cpp}");
    assert!(cpp.contains("return std::log10(x);"),      "log10:\n{cpp}");
    assert!(cpp.contains("return std::fmod(a, b);"),    "fmod:\n{cpp}");
}

#[test]
fn pi_constant_lowers_to_literal() {
    let source = r#"
        namespace test.math_pi
          import anthill.prelude.{Float}
          import anthill.prelude.Float.{pi}
          sort Calc
            operation p() -> Float = pi
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.math_pi.Calc")
        .expect("emit Calc");
    assert!(
        cpp.contains("return 3.141592653589793;"),
        "pi as bare value should lower to a literal:\n{cpp}"
    );
}

#[test]
fn cmath_include_added_to_header() {
    // The header writer should see `std::sin` in the emitted body and
    // request `<cmath>` via the runtime-collected includes set.
    let source = r#"
        namespace test.math_inc
          import anthill.prelude.{Float}
          import anthill.prelude.Float.{sin}
          sort Calc
            operation rotated(x: Float) -> Float = sin(x)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_namespace_header(&mut kb, "test.math_inc")
        .expect("emit header");
    assert!(
        cpp.contains("#include <cmath>"),
        "namespace header missing <cmath> include:\n{cpp}"
    );
    assert!(
        cpp.contains("std::sin(x)"),
        "sin call missing in header:\n{cpp}"
    );
}
