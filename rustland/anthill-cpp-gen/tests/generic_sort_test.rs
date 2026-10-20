//! Slice 1 of generic-sort support: first-order (non-higher-kinded)
//! type parameters on sorts.
//!
//! Covers:
//! - entity inside a parameterised sort emits `template<typename T> struct …`
//! - traits-class for a parameterised sort emits a template prefix and
//!   substitutes `?T` references in operation parameter / return types
//! - multi-param sorts emit `template<typename A, typename B>`
//! - non-generic sorts continue to emit without a template prefix
//! - keyword clashes get suffixed (`?class` → `class0`)
//!
//! Out of scope (later slices):
//! - higher-kinded params (`F[T = ?]` where F itself is a parameter)
//! - generic sum sorts (`enum Tree { entity Leaf(value: ?T); ... }`)

use super::common;

use anthill_cpp_gen::{emit_entity_struct, emit_traits_struct};
use common::load_kb_with;

#[test]
fn generic_entity_emits_template_prefix() {
    let source = r#"
        namespace test.gen_box
          sort Box
            sort T = ?
            entity Box(value: ?T)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.gen_box.Box").expect("emit Box");

    assert!(
        cpp.contains("template<typename T>\nstruct Box {\n    T value;\n};"),
        "generic entity should emit template prefix:\n{cpp}"
    );
}

#[test]
fn multi_param_entity_emits_template_with_two_args() {
    let source = r#"
        namespace test.gen_pair
          sort Pair
            sort A = ?
            sort B = ?
            entity Pair(first: ?A, second: ?B)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.gen_pair.Pair").expect("emit Pair");

    assert!(
        cpp.contains("template<typename A, typename B>"),
        "multi-param prefix missing:\n{cpp}"
    );
    assert!(
        cpp.contains("A first;") && cpp.contains("B second;"),
        "field types should reference template params:\n{cpp}"
    );
}

#[test]
fn non_generic_entity_keeps_no_prefix() {
    // Sanity: a plain entity-with-fields emits without `template<…>`.
    let source = r#"
        namespace test.plain
          import anthill.prelude.{Int64}
          entity Pose(x: Int64, y: Int64)
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.plain.Pose").expect("emit Pose");

    assert!(
        !cpp.contains("template<"),
        "non-generic entity should not emit a template prefix:\n{cpp}"
    );
    assert!(cpp.contains("struct Pose {"), "struct missing:\n{cpp}");
}

#[test]
fn generic_traits_class_emits_template_prefix() {
    // The traits class for a generic sort emits `template<typename T>`
    // and substitutes the sort's `T` in operation parameter / return types.
    //
    // A VARIABLE `?T` IN THE SIGNATURE IS NOT THE SORT'S `T` (§5.4, proposal 070): it is
    // the operation's own type parameter, so `pass2` is a template of its own. This row
    // wrote `pass(x: ?T)` and read the class's `T` back by the coincidence of the name.
    let source = r#"
        namespace test.gen_id
          sort Identity
            sort T = ?
            operation pass(x: T) -> T = x
            operation pass2(x: ?T) -> ?T = x
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.gen_id.Identity").expect("emit Identity");

    assert!(
        cpp.contains("template<typename T>\nstruct Identity {"),
        "generic traits class should emit template prefix:\n{cpp}"
    );
    assert!(
        cpp.contains("static T pass(T x)"),
        "operation signature should use template parameter T:\n{cpp}"
    );
    assert!(
        cpp.contains("template<typename T0>\n    static T0 pass2(T0 x)"),
        "a variable written in the signature is the operation's own template parameter:\n{cpp}"
    );
}

/// WI-20260911-VNQTR — a variable a signature writes in a parameter type is a template
/// parameter of the operation's own, apart from a bracket's or the sort's parameter of the
/// same name and from a value parameter of its name. Held in the frame by its name, `?U`
/// took the bracket `U`'s place and `?T` the sort's `T` — every `U` lowered to the
/// variable's parameter, which no call can deduce — and `keep(x: ?x)` named its template
/// parameter like its value parameter, which C++ refuses (MEASURED, g++).
#[test]
fn an_inline_variable_is_a_template_parameter_of_its_own() {
    let source = r#"
        namespace test.gen_inline
          sort Identity
            sort T = ?
            operation pass4[U](a: U, b: ?U) -> U = a
            operation mix(a: T, b: ?T) -> T = a
            operation keep(x: ?x) -> ?x = x
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.gen_inline.Identity").expect("emit Identity");
    assert!(
        cpp.contains("template<typename U, typename U0>\n    static U pass4(U a, U0 b)"),
        "a bracket and a variable of one name are two template parameters:\n{cpp}"
    );
    assert!(
        cpp.contains("template<typename T0>\n    static T mix(T a, T0 b)"),
        "the sort's `T` stays the class's beside a variable `?T`:\n{cpp}"
    );
    assert!(
        cpp.contains("template<typename x0>\n    static x0 keep(x0 x)"),
        "a template parameter is not named like a value parameter:\n{cpp}"
    );
}

#[test]
fn keyword_clash_gets_suffixed() {
    // A type parameter named `class` would collide with the C++
    // keyword — the canonicaliser appends a `0` (or higher) suffix
    // so the emitted template stays valid.
    let source = r#"
        namespace test.gen_kw
          sort Holder
            sort class = ?
            entity Holder(value: ?class)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.gen_kw.Holder").expect("emit Holder");

    assert!(
        cpp.contains("template<typename class0>"),
        "keyword param should be suffixed to 'class0':\n{cpp}"
    );
    assert!(
        cpp.contains("class0 value;"),
        "field type should use suffixed name:\n{cpp}"
    );
}
