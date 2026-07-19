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
    assert_eq!(cpp, expected, "C++ struct mismatch:\nexpected:\n{expected}\nactual:\n{cpp}");
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
