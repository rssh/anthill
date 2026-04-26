//! Stdlib Option/wrapper-constructor lowering: `some(x)` →
//! `std::make_optional(x)`, `none` → `std::nullopt`.
//!
//! Plain entity constructors continue to lower to brace-init —
//! Option's special case is keyed on the qualified name, not on the
//! entity-table presence.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::load_kb_with_lenient;

#[test]
fn option_some_lowers_to_make_optional() {
    let source = r#"
        namespace test.opt_some
          import anthill.prelude.{Int, Option}
          import anthill.prelude.Option.{some}
          export Calc
          sort Calc
            operation lift(x: Int) -> Option[T = Int] = some(x)
          end
        end
    "#;
    // Lenient loader: typer rejects `some(x): Option[T = Int]`
    // because the bare-Option-vs-Option[T = Int] check is overstrict.
    // The lowering itself is what we test here.
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.opt_some.Calc")
        .expect("emit Calc");
    assert!(
        cpp.contains("return std::make_optional(x);"),
        "Option.some should lower to std::make_optional:\n{cpp}"
    );
}

#[test]
fn option_none_lowers_to_nullopt() {
    let source = r#"
        namespace test.opt_none
          import anthill.prelude.{Int, Option}
          import anthill.prelude.Option.{none}
          export Calc
          sort Calc
            operation empty() -> Option[T = Int] = none
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.opt_none.Calc")
        .expect("emit Calc");
    assert!(
        cpp.contains("return std::nullopt;"),
        "Option.none should lower to std::nullopt:\n{cpp}"
    );
}
