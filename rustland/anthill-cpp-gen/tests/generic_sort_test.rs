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
use common::{load_kb_with, load_kb_with_lenient};

#[test]
fn generic_entity_emits_template_prefix() {
    let source = r#"
        namespace test.gen_box
          export Box
          sort Box
            sort T = ?
            entity Box(value: ?T)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_entity_struct(&kb, "test.gen_box.Box.Box")
        .expect("emit Box");

    assert!(
        cpp.contains("template<typename T>\nstruct Box {\n    T value;\n};"),
        "generic entity should emit template prefix:\n{cpp}"
    );
}

#[test]
fn multi_param_entity_emits_template_with_two_args() {
    let source = r#"
        namespace test.gen_pair
          export Pair
          sort Pair
            sort A = ?
            sort B = ?
            entity Pair(first: ?A, second: ?B)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_entity_struct(&kb, "test.gen_pair.Pair.Pair")
        .expect("emit Pair");

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
          import anthill.prelude.{Int}
          export Pose
          entity Pose(x: Int, y: Int)
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "test.plain.Pose")
        .expect("emit Pose");

    assert!(
        !cpp.contains("template<"),
        "non-generic entity should not emit a template prefix:\n{cpp}"
    );
    assert!(cpp.contains("struct Pose {"), "struct missing:\n{cpp}");
}

#[test]
fn generic_traits_class_emits_template_prefix() {
    // The traits class for a generic sort emits `template<typename T>`
    // and substitutes `?T` in operation parameter / return types.
    let source = r#"
        namespace test.gen_id
          export Identity
          sort Identity
            sort T = ?
            operation pass(x: ?T) -> ?T = x
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.gen_id.Identity")
        .expect("emit Identity");

    assert!(
        cpp.contains("template<typename T>\nstruct Identity {"),
        "generic traits class should emit template prefix:\n{cpp}"
    );
    assert!(
        cpp.contains("static T pass(T x)"),
        "operation signature should use template parameter T:\n{cpp}"
    );
}

#[test]
fn keyword_clash_gets_suffixed() {
    // A type parameter named `class` would collide with the C++
    // keyword — the canonicaliser appends a `0` (or higher) suffix
    // so the emitted template stays valid.
    let source = r#"
        namespace test.gen_kw
          export Holder
          sort Holder
            sort class = ?
            entity Holder(value: ?class)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_entity_struct(&kb, "test.gen_kw.Holder.Holder")
        .expect("emit Holder");

    assert!(
        cpp.contains("template<typename class0>"),
        "keyword param should be suffixed to 'class0':\n{cpp}"
    );
    assert!(
        cpp.contains("class0 value;"),
        "field type should use suffixed name:\n{cpp}"
    );
}
