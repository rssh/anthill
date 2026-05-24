//! Slice 2: match patterns that bind values from constructor fields.
//!
//! `case some(?w) -> body` binds `?w` to `o.value()` for an Option;
//! `case some(?w) -> ...` over a generic sum sort would bind `?w` to
//! `std::get<some>(o).value`. The body is wrapped in an IIFE so the
//! local `auto w = …;` declaration lives in scope while the
//! surrounding ternary still produces a value.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::load_kb_with_lenient;

#[test]
fn option_some_binding_lowers_to_value_iife() {
    let source = r#"
        namespace test.mb_opt
          import anthill.prelude.{Int, Option}
          export Calc
          sort Calc
            operation unwrap(o: Option[T = Int]) -> Int =
              match o
                case some(w) -> w
                case none     -> 0
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.mb_opt.Calc")
        .expect("emit Calc");

    // tag check on the some-arm uses has_value()
    assert!(
        cpp.contains("(o.has_value() ? ["),
        "Option.some pattern should use has_value() tag check:\n{cpp}"
    );
    // binding `?w` is materialised as `auto w = o.value();`
    assert!(
        cpp.contains("auto w = o.value();"),
        "binding `?w` should declare local from o.value():\n{cpp}"
    );
    // none-arm is the catch-all (no holds_alternative or has_value on the inner)
    assert!(
        cpp.contains(": 0)"),
        "none branch should emit 0 as the catch-all:\n{cpp}"
    );
}

#[test]
fn variant_constructor_pattern_binds_fields() {
    // A generic sum sort with a fielded constructor — pattern bindings
    // become `std::get<Ctor>(s).<field>` accesses, in declaration order.
    let source = r#"
        namespace test.mb_var
          import anthill.prelude.{Int}
          export Shape, Circle, Square, Calc
          enum Shape
            entity Circle(radius: Int)
            entity Square(side: Int)
          end
          sort Calc
            operation perimeter(s: Shape) -> Int =
              match s
                case Circle(r) -> r
                case Square(w) -> w
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.mb_var.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("std::holds_alternative<Circle>(s)"),
        "Circle tag check missing:\n{cpp}"
    );
    assert!(
        cpp.contains("auto r = std::get<Circle>(s).radius;"),
        "Circle.radius binding missing:\n{cpp}"
    );
    assert!(
        cpp.contains("auto w = std::get<Square>(s).side;"),
        "Square.side binding missing:\n{cpp}"
    );
}

#[test]
fn nested_let_inside_branch_body_works() {
    // The IIFE machinery composes with existing let-chain lowering —
    // a binding-pattern branch's body can itself contain a let.
    let source = r#"
        namespace test.mb_nested
          import anthill.prelude.{Int, Option}
          export Calc
          sort Calc
            operation double_or_zero(o: Option[T = Int]) -> Int =
              match o
                case some(w) ->
                  let twice = add(w, w)
                  twice
                case none -> 0
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.mb_nested.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("auto w = o.value();"),
        "binding missing:\n{cpp}"
    );
    // The let inside the body becomes another IIFE — `(w + w)` after
    // operator rewrite of add.
    assert!(
        cpp.contains("auto twice = (w + w);"),
        "let inside binding-pattern branch should compose:\n{cpp}"
    );
}

#[test]
fn wildcard_branch_after_constructor_works() {
    // Trailing `_` catch-all should be the last arm and not have a
    // tag check. Using a constructor pattern before it ensures the
    // match isn't trivially short-circuited.
    let source = r#"
        namespace test.mb_wild
          import anthill.prelude.{Int, Option}
          export Calc
          sort Calc
            operation safe(o: Option[T = Int]) -> Int =
              match o
                case some(w) -> w
                case _        -> 0
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.mb_wild.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("o.has_value()"),
        "some branch should still tag-check:\n{cpp}"
    );
    assert!(
        cpp.contains(": 0)"),
        "wildcard catch-all should emit `0` directly:\n{cpp}"
    );
}
