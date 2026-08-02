//! WI-931 — ONE SYMBOL, ONE STRUCT: an eponymous sort that carries BOTH fields
//! and operations reaches C++ as a single type.
//!
//! §6.3 / WI-926 make `sort Vec3 { entity Vec3(…); operation vec_add(…) = … }`
//! ONE symbol and one declaration — the sugar `entity Vec3(…)` and this long form
//! denote the same thing. cpp-gen found it TWICE: `classify_namespace` builds the
//! data band from the entity-field registry and the traits band from
//! `OperationInfo` parents, and one symbol satisfies both. Each band then emitted
//! a full `struct Vec3 { … };`, and a header holding both is a C++ REDEFINITION
//! ERROR — measured, on a header this generator produced.
//!
//! The fix is at the classification and the by-symbol emitter, not at the
//! namespace walk, because the walk is only one of three callers: the crate's
//! public `emit_entity_struct` / `emit_traits_struct` by-name API would otherwise
//! keep handing out half a type under the type's own name, and
//! `traits_classes_in_namespace` (which the CLI's `codegen cpp-project` uses to
//! scaffold one controller per traits class) would offer a DATA TYPE as a
//! controller target.
//!
//! The fixture is local rather than the stdlib's `Vec3`. When WI-931 wrote it that
//! was a necessity — the tree shipped no sort of this shape, because WI-931 had
//! just withdrawn the `VectorSpace` provision that motivated giving `Vec3`
//! operations. WI-935 restored it, so `anthill.geometry.Vec3` IS now an eponymous
//! sort with fields and operations. The local fixture stays anyway: it pins the
//! rule at a shape this suite controls, so a future edit to stdlib geometry cannot
//! quietly remove the only example the rule is measured against.

use super::common;

use std::process::Command;

use anthill_cpp_gen::{
    emit_entity_struct, emit_namespace_header, emit_traits_struct, traits_classes_in_namespace,
};
use common::{find_cxx, load_kb_with, scratch_dir};

/// An eponymous sort with fields AND operations, beside a plain entity (which
/// must be unaffected) and a genuine operations-only traits sort (which must
/// still emit as one).
const SRC: &str = r#"
namespace test.wi931
  import anthill.prelude.{Float}

  sort Point {
    entity Point(x: Float, y: Float)
    operation origin() -> Point = Point(x: 0.0, y: 0.0)
    operation shift(p: Point, dx: Float) -> Point = Point(x: p.x + dx, y: p.y)
  }

  entity Plain(a: Float)

  sort Calc
    operation twice(v: Float) -> Float = v + v
  end
end
"#;

const EXPECTED_POINT: &str = "\
struct Point {
    double x;
    double y;
    static Point origin() {
        return Point{0.0, 0.0};
    }
    static Point shift(Point p, double dx) {
        return Point{(p.x + dx), p.y};
    }
};
";

/// SUBJECT — the namespace header holds ONE `struct Point`, so it compiles.
/// Counting is the assertion: a `contains` check passes just as happily on a
/// header with two definitions, which is the bug.
#[test]
fn the_namespace_header_defines_the_eponymous_sort_once() {
    let mut kb = load_kb_with(SRC);
    let header = emit_namespace_header(&mut kb, "test.wi931").expect("emit header");
    assert_eq!(
        header.matches("struct Point").count(),
        1,
        "exactly one `struct Point` definition:\n{header}",
    );
    assert!(header.contains(EXPECTED_POINT), "fields then operations:\n{header}");
    // The neighbours are untouched — the merge is not a blanket rewrite.
    assert_eq!(header.matches("struct Plain").count(), 1, "{header}");
    assert_eq!(header.matches("struct Calc").count(), 1, "{header}");
}

/// SUBJECT — and it actually compiles, which is the property the redefinition
/// broke. Constructing a `Point` and calling both members exercises the merged
/// struct rather than merely parsing it.
#[test]
fn the_emitted_header_compiles() {
    let mut kb = load_kb_with(SRC);
    let header = emit_namespace_header(&mut kb, "test.wi931").expect("emit header");

    let Some(cxx) = find_cxx() else {
        eprintln!("no C++ compiler available — skipping compile check");
        return;
    };
    let dir = scratch_dir("wi931_eponymous");
    let header_path = dir.join("wi931.hpp");
    std::fs::write(&header_path, &header).expect("write header");
    let driver = format!(
        r#"#include "{}"

int main() {{
    test::wi931::Point p = test::wi931::Point::origin();
    test::wi931::Point q = test::wi931::Point::shift(p, 2.0);
    return q.x > 1.0 ? 0 : 1;
}}
"#,
        header_path.display()
    );
    let driver_path = dir.join("driver.cpp");
    std::fs::write(&driver_path, &driver).expect("write driver");
    let out = Command::new(cxx)
        .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Wextra"])
        .arg(&driver_path)
        .output()
        .expect("invoke compiler");
    assert!(
        out.status.success(),
        "merged struct must compile\n── header ──\n{header}\n── stderr ──\n{}",
        String::from_utf8_lossy(&out.stderr),
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// SUBJECT — BOTH public by-name entry points answer with the whole type. This is
/// the half the namespace walk cannot cover: these bypass it entirely, and before
/// WI-931 they returned the two halves that could not coexist in one header.
#[test]
fn both_by_name_entry_points_answer_with_the_whole_type() {
    let mut kb = load_kb_with(SRC);
    let as_entity = emit_entity_struct(&mut kb, "test.wi931.Point").expect("emit Point");
    let as_traits = emit_traits_struct(&mut kb, "test.wi931.Point").expect("emit Point traits");
    assert_eq!(as_entity, EXPECTED_POINT, "entity entry point:\n{as_entity}");
    assert_eq!(as_traits, EXPECTED_POINT, "traits entry point:\n{as_traits}");
}

/// SUBJECT — an eponymous sort is NOT a traits class, so the CLI's
/// `codegen cpp-project` fallback does not scaffold a controller for a data type.
/// `Calc` is the control: a real operations-only sort still IS one, so the filter
/// is about the overlap and not about having operations.
#[test]
fn an_eponymous_sort_is_not_offered_as_a_traits_class() {
    let mut kb = load_kb_with(SRC);
    let classes = traits_classes_in_namespace(&mut kb, "test.wi931").expect("classify");
    assert!(
        !classes.iter().any(|c| c == "Point"),
        "a data type must not be offered as a controller target: {classes:?}",
    );
    assert!(
        classes.iter().any(|c| c == "Calc"),
        "an operations-only sort is still a traits class: {classes:?}",
    );
}

/// CONTROL — a plain entity with no operations emits exactly what it always did,
/// and asking for its traits struct is still the loud error it always was. Without
/// this pair, an emitter that merged unconditionally would satisfy every test
/// above.
#[test]
fn control_a_plain_entity_is_unchanged_and_has_no_traits_struct() {
    let mut kb = load_kb_with(SRC);
    let plain = emit_entity_struct(&mut kb, "test.wi931.Plain").expect("emit Plain");
    assert_eq!(plain, "struct Plain {\n    double a;\n};\n", "{plain}");

    let err = emit_traits_struct(&mut kb, "test.wi931.Plain")
        .expect_err("an entity with no operations has no traits struct");
    assert!(
        err.message.contains("no operations or constants"),
        "the empty-traits-class refusal must survive the merge: {}",
        err.message,
    );
}
