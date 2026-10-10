//! WI-20261009-AN6CQ — anthill-todo loads the standard library FIRST, on its own, seals
//! that load, and loads its program — the embedded bundle and the project's files — in
//! a later one.
//!
//! Driven through the built binary, as `anthill-cli`'s rows of the same name drive the
//! CLI: a project file that supplies the equality of the library's `List` is refused
//! (`docs/kernel-language.md` §8.3), where one load of everything let it replace the
//! derived one; and one that declares a library operation again is refused as the
//! second declaration it is, where a library loaded first and not sealed let its body
//! replace the library's.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! * `anthill-todo/src/main.rs` made to hand `load_program` the library and the
//!   program as ONE program: `a_project_file_may_not_supply_the_librarys_equality`
//!   FAILS, the command succeeding. The `…_declare_a_library_operation_again` row
//!   passes, one call refusing that as well.
//! * `load::load_program` made not to seal the library's load: `a_project_file_may_not_
//!   declare_a_library_operation_again` FAILS, the command succeeding, and the equality
//!   row passes — that rule is the order's, not the seal's.
//! * `a_project_with_no_such_file_still_lists` passes either way BY DESIGN: it is the
//!   control that the project loads at all, so that the refusals are about the file.

use std::process::Command;

use crate::common::setup_project;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// What `setup_project` writes as the project's `workitems.anthill`.
const AN_EQ_FOR_THE_LIBRARYS_LIST: &str = r#"
namespace test.an6cq.todo
  import anthill.prelude.{Eq, PartialEq, List, Bool}
  sort EqList
    sort A = ?
    requires Eq[T = A]
    provides PartialEq[T = List[T = A]]
    provides Eq[T = List[T = A]]
    operation eq(x: List[T = A], y: List[T = A]) -> Bool = true
  end
end
"#;

fn list(workitems: &str) -> (bool, String) {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, workitems);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(), "list"])
        .output()
        .expect("run anthill-todo");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

#[test]
fn a_project_file_may_not_supply_the_librarys_equality() {
    let (ok, stderr) = list(AN_EQ_FOR_THE_LIBRARYS_LIST);
    assert!(
        !ok && stderr.contains("the equality of 'anthill.prelude.List' is closed"),
        "a project is a later load than the standard library; succeeded: {ok}, stderr:\n{stderr}"
    );
}

/// What `setup_project` writes as the project's `workitems.anthill`: a second
/// declaration of an operation the library declares, with another body.
const A_LIBRARY_OPERATION_AGAIN: &str =
    "namespace anthill.prelude.Option\n  operation isEmpty(o: Self) -> Bool = true\nend\n";

#[test]
fn a_project_file_may_not_declare_a_library_operation_again() {
    let (ok, stderr) = list(A_LIBRARY_OPERATION_AGAIN);
    assert!(
        !ok && stderr
            .contains("operation 'anthill.prelude.Option.isEmpty' is declared more than once"),
        "the library's load is sealed, and the project's declaration is a second one; \
         succeeded: {ok}, stderr:\n{stderr}"
    );
}

#[test]
fn a_project_with_no_such_file_still_lists() {
    let (ok, stderr) = list("");
    assert!(ok, "the control: an ordinary project loads; stderr:\n{stderr}");
}
