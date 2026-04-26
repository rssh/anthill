//! `emit_namespace_header` includes traits classes for sorts that
//! have operations declared directly under the namespace, not just
//! flat entities and sum sorts. Data items emit before traits items
//! so traits-class method declarations referencing entity types
//! don't need forward declarations.

use super::common;

use anthill_cpp_gen::emit_namespace_header;
use common::load_kb_with;

#[test]
fn namespace_header_includes_traits_class() {
    let source = r#"
        namespace test.ns_traits
          import anthill.prelude.{Int}
          export Pose, Calc
          entity Pose(x: Int, y: Int)
          sort Calc
            operation pos_x(p: Pose) -> Int = 0
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_namespace_header(&kb, "test.ns_traits")
        .expect("emit namespace header");

    assert!(
        cpp.contains("struct Pose {"),
        "entity Pose should be emitted:\n{cpp}"
    );
    assert!(
        cpp.contains("struct Calc {"),
        "traits class Calc should be emitted alongside entities:\n{cpp}"
    );
    assert!(
        cpp.contains("static int64_t pos_x(Pose p)"),
        "Calc's operation should appear as a static method:\n{cpp}"
    );

    // Pose comes before Calc — entities (data band) precede traits
    // classes so static-method signatures referencing entity types
    // compile without forward declarations.
    let pose_pos = cpp.find("struct Pose").expect("Pose present");
    let calc_pos = cpp.find("struct Calc").expect("Calc present");
    assert!(
        pose_pos < calc_pos,
        "data types must precede traits classes:\n{cpp}"
    );
}

#[test]
fn data_band_topologically_sorted_by_field_deps() {
    // `Outer` has a field of type `Inner` — even though `Inner`
    // sorts after `Outer` alphabetically, the topo pass must place
    // `Inner` first so the C++ compiles without forward declarations.
    let source = r#"
        namespace test.topo
          import anthill.prelude.{Int}
          export Outer, Inner
          entity Inner(value: Int)
          entity Outer(inner: Inner, n: Int)
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_namespace_header(&kb, "test.topo")
        .expect("emit header");

    let inner_pos = cpp.find("struct Inner").expect("Inner present");
    let outer_pos = cpp.find("struct Outer").expect("Outer present");
    assert!(
        inner_pos < outer_pos,
        "Inner must precede Outer because Outer has an Inner field:\n{cpp}"
    );
}

#[test]
fn data_band_chains_three_levels() {
    // A → B → C dependency chain (A holds B, B holds C). The topo
    // pass should produce C, B, A in that order regardless of
    // alphabetical position.
    let source = r#"
        namespace test.chain
          import anthill.prelude.{Int}
          export A, B, C
          entity C(v: Int)
          entity B(c: C)
          entity A(b: B)
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_namespace_header(&kb, "test.chain")
        .expect("emit header");

    let c_pos = cpp.find("struct C").expect("C present");
    let b_pos = cpp.find("struct B").expect("B present");
    let a_pos = cpp.find("struct A").expect("A present");
    assert!(c_pos < b_pos && b_pos < a_pos, "topo chain wrong:\n{cpp}");
}

#[test]
fn namespace_with_only_traits_emits_traits() {
    // Sanity: a namespace with no flat entities or sum sorts still
    // emits a traits class for the lone sort-with-operations.
    let source = r#"
        namespace test.ns_traits_only
          import anthill.prelude.{Int}
          export Calc
          sort Calc
            operation forty_two() -> Int = 42
          end
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_namespace_header(&kb, "test.ns_traits_only")
        .expect("emit traits-only namespace header");

    assert!(
        cpp.contains("struct Calc {"),
        "traits class missing in traits-only namespace:\n{cpp}"
    );
    assert!(
        cpp.contains("static int64_t forty_two()"),
        "operation should be emitted:\n{cpp}"
    );
}
