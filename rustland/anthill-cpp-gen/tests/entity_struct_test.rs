//! Integration tests for emit_entity_struct.

use super::common;

use anthill_cpp_gen::emit_entity_struct;
use common::load_kb_with;

#[test]
fn vec3_entity_emits_cpp_struct() {
    // Smallest useful sanity check. Vec3's field order (x, y, z)
    // happens to coincide with alphabetical order; EulerAngles in
    // the lf1 smoke test exercises declaration-order emission where
    // the two diverge.
    let source = r#"
        namespace test.geom
          import anthill.prelude.{Float}
          entity Vec3(x: Float, y: Float, z: Float)
        end
    "#;

    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.geom.Vec3").expect("emit Vec3 struct");

    let expected = "\
struct Vec3 {
    double x;
    double y;
    double z;
};
";
    assert_eq!(
        cpp, expected,
        "C++ struct mismatch:\nexpected:\n{expected}\nactual:\n{cpp}"
    );
}

#[test]
fn entity_with_int_and_string_fields() {
    // Mixed primitive types — verifies the Int64 → int64_t and
    // String → std::string mappings.
    let source = r#"
        namespace test.account
          import anthill.prelude.{Int64, String}
          entity Account(id: Int64, name: String)
        end
    "#;

    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.account.Account").expect("emit Account struct");

    let expected = "\
struct Account {
    int64_t id;
    std::string name;
};
";
    assert_eq!(cpp, expected, "C++ struct mismatch");
}

#[test]
fn missing_entity_returns_error() {
    let mut kb = load_kb_with("namespace test.empty end");
    let result = emit_entity_struct(&mut kb, "DoesNotExist");
    assert!(result.is_err(), "expected error for missing entity");
}

/// A field whose type holds a value has no C++ spelling, and is refused by name. It
/// was dropped from the struct in silence: the entity below emitted `struct Slot {
/// int64_t id; };`.
///
/// BACKED OUT (the field filtered out where its type is no term): this test FAILS,
/// the struct is emitted without `data`.
#[test]
fn a_field_whose_type_holds_a_value_is_refused_by_name() {
    let source = r#"
        namespace test.slot
          import anthill.prelude.{Int64}
          sort Buf
            sort T = ?
            sort N = ?
            entity buf(v: T)
          end
          entity Slot(id: Int64, data: Buf[T = Int64, N = 3])
        end
    "#;

    let mut kb = load_kb_with(source);
    let err = emit_entity_struct(&mut kb, "test.slot.Slot")
        .expect_err("a field whose type holds a value has no C++ struct member");
    assert!(
        err.message.contains("entity 'test.slot.Slot' field 'data'")
            && err.message.contains("holds a value"),
        "{}",
        err.message
    );
}
