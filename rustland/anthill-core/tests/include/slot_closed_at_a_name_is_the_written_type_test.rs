//! A SLOT CLOSED AT A NAME IS THE TYPE THE AUTHOR CAN WRITE (`kernel-language.md` §5.4): `let o
//! = none()` binds `o` at `Option[T = Nothing]`, the same type as `let o: Option[T = Nothing] =
//! none()`, so a raise of `o` is declared by the row that names that type. The typer-filled slot
//! was another term: its key the parameter's qualified symbol (`anthill.prelude.Option.T`)
//! where a written type keys the bare label `T`, and its bottom `TypeExtractor.Nothing` where a
//! written one is the sort `anthill.prelude.Nothing`. The two render alike, and the op-effects
//! check, which compares the labels structurally, refused the raise: "expected declared:
//! [Error[T = Option[T = nothing]]], got undeclared effect: Error[T = Option[T = nothing]]".
//! Found answering proposal 071's open question 3, 2026-10-27.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ── measured 2026-10-27, each alone ──
//!
//! * The filled slot keyed by the bare label (`rigidify_unwritten_sort_params`): every row of
//!   `a_bottom_closed_at_a_name_is_declared_by_the_written_row`.
//! * The bottom built as the declared sort (`KnowledgeBase::make_nothing_type`): the same.
//!
//! PASS EITHER WAY BY DESIGN: `the_annotated_twin_is_declared_by_the_same_row`, whose slot is
//! written.

use anthill_core::eval::Value;

fn program(decl: &str) -> String {
    format!(
        r#"
namespace test.closedslot
  import anthill.prelude.{{Int64, List, Option, Error, Nothing}}
  import anthill.prelude.Option.{{none}}
  import anthill.prelude.Result.{{ok, err}}

{decl}

  operation caught() -> Int64 =
    match Error.reify(lambda () -> raises())
      case ok(_) -> 1
      case err(_) -> 2
end
"#
    )
}

/// The slot closed at the bottom where the value is bound — a `let`, a match binder, a
/// destructured tuple, a slot nested in the bound type — raised under a row that writes the
/// type.
#[test]
fn a_bottom_closed_at_a_name_is_declared_by_the_written_row() {
    for (shape, decl) in [
        (
            "Option",
            "  operation raises() -> Int64 effects {Error[Option[T = Nothing]]} =
    let o = none()
    Error.raise(o)",
        ),
        (
            "List",
            "  operation raises() -> Int64 effects {Error[List[T = Nothing]]} =
    let xs = []
    Error.raise(xs)",
        ),
        (
            "match binder",
            "  operation raises() -> Int64 effects {Error[Option[T = Nothing]]} =
    match none()
      case o -> Error.raise(o)",
        ),
        (
            "destructured tuple",
            "  operation raises() -> Int64 effects {Error[Option[T = Nothing]]} =
    let (a, b) = (none(), 1)
    Error.raise(a)",
        ),
        (
            "nested in a list",
            "  operation raises() -> Int64 effects {Error[List[T = Option[T = Nothing]]]} =
    let xs = [none()]
    Error.raise(xs)",
        ),
        (
            "nested in an option",
            "  operation raises() -> Int64 effects {Error[Option[T = List[T = Nothing]]]} =
    let o = Option.some([])
    Error.raise(o)",
        ),
    ] {
        let src = program(decl);
        assert_eq!(crate::common::load_errors_of(&src), Vec::<String>::new(), "{shape}");
        let mut interp = crate::common::interp_for(&src);
        let v = interp.call("test.closedslot.caught", &[]).expect("runs");
        assert!(matches!(v, Value::Int(2)), "{shape}: the raise is caught; got {v:?}");
    }
}

/// The control: the slot written by an annotation.
#[test]
fn the_annotated_twin_is_declared_by_the_same_row() {
    let src = program(
        "  operation raises() -> Int64 effects {Error[Option[T = Nothing]]} =
    let o: Option[T = Nothing] = none()
    Error.raise(o)",
    );
    let mut interp = crate::common::interp_for(&src);
    let v = interp.call("test.closedslot.caught", &[]).expect("runs");
    assert!(matches!(v, Value::Int(2)), "the raise is caught; got {v:?}");
}
