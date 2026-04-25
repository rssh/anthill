//! Integration tests for emit_entity_struct.

mod common;

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
          export Vec3
          entity Vec3(x: Float, y: Float, z: Float)
        end
    "#;

    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "Vec3").expect("emit Vec3 struct");

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
    // Mixed primitive types — verifies the Int → int64_t and
    // String → std::string mappings.
    let source = r#"
        namespace test.account
          import anthill.prelude.{Int, String}
          export Account
          entity Account(id: Int, name: String)
        end
    "#;

    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "Account").expect("emit Account struct");

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
    let kb = load_kb_with("namespace test.empty end");
    let result = emit_entity_struct(&kb, "DoesNotExist");
    assert!(result.is_err(), "expected error for missing entity");
}
