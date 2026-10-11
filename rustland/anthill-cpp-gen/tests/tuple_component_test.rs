//! A field read off a tuple is read by its place.
//!
//! A tuple type lowers to `std::tuple`, whose components have no names, so `p._1` and
//! `p.y` have no C++ spelling as members: `operation fstof(p: (Int64, Int64)) -> Int64 =
//! p._1` was emitted `return p._1;`, which does not compile. The component is read with
//! `std::get`, at the place its label has in the receiver's type.
//!
//! CONTROLS — measured with the reading backed out of the `field_access` arm: three rows
//! FAIL, `a_component_is_read_by_its_place` and `a_lambdas_binder_is_read_by_its_place`
//! on the text and `the_generated_reads_compile_and_run` in the compiler. A field of an
//! entity is still a member read (`a_field_of_an_entity_is_still_a_member`), and passes
//! either way.
//!
//! Found while delivering WI-20261011-3HN0N.

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_namespace_header, emit_traits_struct};
use common::{find_cxx, load_kb_with, scratch_dir};

const SOURCE: &str = r#"
    namespace test.tuplecomp
      import anthill.prelude.Int64
      sort Calc
        operation fstof(p: (Int64, Int64)) -> Int64 = p._1
        operation sndof(p: (Int64, Int64)) -> Int64 = p._2
        operation yof(p: (x: Int64, y: Int64)) -> Int64 = p.y
        operation inner(p: ((Int64, Int64), Int64)) -> Int64 = p._1._2
        operation both(a: Int64) -> (Int64, Int64) = (a, a + 1)
        operation go() -> Int64 = fstof(both(4)) + both(5)._2
        operation aliased(p: Pair) -> Int64 = p._2
        operation generic[T](p: (T, T)) -> T = p._1
      end
      sort Pair = (Int64, Int64)
    end
"#;

#[test]
fn a_component_is_read_by_its_place() {
    let mut kb = load_kb_with(SOURCE);
    let cpp = emit_traits_struct(&mut kb, "test.tuplecomp.Calc").expect("emit Calc");
    for expected in [
        "return std::get<0>(p);",
        "return std::get<1>(p);",
        "return std::get<1>(std::get<0>(p));",
        "std::get<1>(both(5))",
    ] {
        assert!(cpp.contains(expected), "expected `{expected}` in:\n{cpp}");
    }
    assert!(!cpp.contains("p._1") && !cpp.contains("p.y"), "{cpp}");
}

/// The header compiles, and each read gives the component its label names.
#[test]
fn the_generated_reads_compile_and_run() {
    let mut kb = load_kb_with(SOURCE);
    let header = emit_namespace_header(&mut kb, "test.tuplecomp").expect("emit header");
    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping compile check");
            return;
        }
    };
    let dir = scratch_dir("tuple_component");
    let header_path = dir.join("test_tuplecomp.hpp");
    std::fs::write(&header_path, &header).expect("write header");
    let driver = format!(
        r#"#include "{}"

int main() {{
    using test::tuplecomp::Calc;
    if (Calc::fstof({{7, 8}}) != 7) return 1;
    if (Calc::sndof({{7, 8}}) != 8) return 2;
    if (Calc::yof({{7, 8}}) != 8) return 3;
    if (Calc::inner({{{{1, 2}}, 3}}) != 2) return 4;
    if (Calc::go() != 10) return 5;
    if (Calc::aliased({{7, 8}}) != 8) return 6;
    if (Calc::generic(std::tuple<int64_t, int64_t>{{7, 8}}) != 7) return 7;
    return 0;
}}
"#,
        header_path.display()
    );
    let driver_path = dir.join("driver.cpp");
    std::fs::write(&driver_path, &driver).expect("write driver");
    let binary = dir.join("driver");
    let output = Command::new(cxx)
        .args(["-std=c++17", "-Wall", "-Wextra", "-o"])
        .arg(&binary)
        .arg(&driver_path)
        .output()
        .expect("invoke compiler");
    assert!(
        output.status.success(),
        "C++ compile failed (compiler: {cxx})\n{header}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let status = Command::new(&binary).status().expect("run the driver");
    assert_eq!(status.code(), Some(0), "the driver names the read that is wrong:\n{header}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A binder of a lambda is a receiver as a parameter is. Read off the text alone: the
/// tuple the lambda is handed is written as a brace list, which a generic lambda cannot
/// take, so this body does not compile for a reason that is not the read's.
#[test]
fn a_lambdas_binder_is_read_by_its_place() {
    let mut kb = load_kb_with(
        r#"
        namespace test.tuplecomplam
          import anthill.prelude.Int64
          sort Calc
            operation vialam(a: Int64) -> Int64 =
              let f = lambda (q: (Int64, Int64)) -> q._2
              f((a, 7))
          end
        end
    "#,
    );
    let cpp = emit_traits_struct(&mut kb, "test.tuplecomplam.Calc").expect("emit Calc");
    assert!(cpp.contains("return std::get<1>(q);"), "{cpp}");
}

#[test]
fn a_field_of_an_entity_is_still_a_member() {
    let mut kb = load_kb_with(
        r#"
        namespace test.tuplecompent
          import anthill.prelude.Int64
          entity Pose(x: Int64, y: Int64)
          sort Calc
            operation yof(p: Pose) -> Int64 = p.y
          end
        end
    "#,
    );
    let cpp = emit_traits_struct(&mut kb, "test.tuplecompent.Calc").expect("emit Calc");
    assert!(cpp.contains("return p.y;"), "{cpp}");
}
