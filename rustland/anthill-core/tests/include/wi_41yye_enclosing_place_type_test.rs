//! WI-41YYE: enclosing value places participate in conformance and type joins.
//! Four enclosing-parameter regressions fail with the predicate fix backed out;
//! Error twins, the let-local refusal and execution controls pass either way.
//! Callback binders keep alignment.
use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

const HEADER: &str = r#"
namespace enclosing
  import anthill.prelude.{Int64, Cell, Modify, Error, String}
  sort Walk
    sort C = ?
    effects E = ?
    operation run(c: C, x: Int64) -> Int64 effects E
  end
  sort Box
    import anthill.prelude.Int64
    import enclosing.Walk
    effects BE = ?
    entity box(f: (x: Int64) -> Int64 @ {BE})
    provides Walk[C = Self, E = BE]
    operation run(b: Self, x: Int64) -> Int64 effects {BE} = match b case box(f) -> f(x)
  end
  import enclosing.Box.box
  operation runPure(b: Box[BE = {}], x: Int64) -> Int64 = match b case box(f) -> f(x)
  operation runAt(j: Cell[V = Int64], b: Box[BE = {Modify[j]}], x: Int64) -> Int64 effects {Modify[j]} = match b case box(f) -> f(x)
  operation second[A](x: A, y: A) -> A = y
  operation bump(k: Cell[V = Int64], x: Int64) -> Int64 effects {Modify[k]} =
    let u = Cell.set(k, Cell.get(k) + x)
    x
"#;

fn source(body: &str) -> String {
    format!("{HEADER}\n{body}\nend")
}

#[test]
fn enclosing_cell_cannot_enter_pure_box_parameter() {
    let src = source(
        "operation use(k: Cell[V = Int64], b: Box[BE = {Modify[k]}]) -> Int64 = runPure(b, 5)",
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            "runPure.b (op-arg)",
            "expected Box[BE = {}]",
            "Modify[T = k]",
        ],
        "enclosing cell is determined",
    );
}

#[test]
fn enclosing_cells_compare_by_identity() {
    let src = source("operation use(k: Cell[V = Int64], j: Cell[V = Int64], b: Box[BE = {Modify[k]}]) -> Int64 effects {Modify[j]} = runAt(j, b, 5)");
    assert_refused_naming(
        &load_errors_of(&src),
        &["runAt.b (op-arg)", "Modify[T = j]", "Modify[T = k]"],
        "another cell is not the declared cell",
    );
}

#[test]
fn enclosing_cell_participates_in_repeated_parameter_join() {
    let src = source("operation use(k: Cell[V = Int64], p: Box[BE = {}], w: Box[BE = {Modify[k]}]) -> Int64 = Walk.run(second(p, w), 5)");
    assert_refused_naming(
        &load_errors_of(&src),
        &["no common type", "second", "Modify[T = k]"],
        "cell row must contribute to the join",
    );
}

#[test]
fn ground_error_controls_are_refused() {
    for body in [
        "operation use(b: Box[BE = {Error[String]}]) -> Int64 = runPure(b, 5)",
        "operation use(p: Box[BE = {}], w: Box[BE = {Error[String]}]) -> Int64 = Walk.run(second(p, w), 5)",
    ] {
        assert_refused_naming(&load_errors_of(&source(body)), &["Error[T = String]"], "ground twin");
    }
}

#[test]
fn matching_enclosing_cell_executes_write_and_join() {
    for body in ["runAt(k, b, 5)", "Walk.run(second(b, b), 5)"] {
        let src = source(&format!(
            r#"
  operation use(k: Cell[V = Int64], b: Box[BE = {{Modify[k]}}]) -> Int64 effects {{Modify[k]}} = {body}
  operation build(k: Cell[V = Int64]) -> Int64 effects {{Modify[k]}} =
    let b: Box[BE = {{Modify[k]}}] = box(lambda (x: Int64) -> bump(k, x))
    use(k, b)
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let n = build(k)
    n * 100 + Cell.get(k)
"#
        ));
        let mut interp = interp_for(&src);
        crate::common::register_modify_handler(&mut interp);
        let result = interp.call("enclosing.main", &[]);
        assert!(matches!(result, Ok(Value::Int(505))), "{body}: {result:?}");
    }
}

#[test]
fn callback_own_binders_still_align_and_execute() {
    let src = source(
        r#"
  operation apply(k: Cell[V = Int64], f: (a: Cell[V = Int64], x: Int64) -> Int64 @ {Modify[a]}) -> Int64 effects {Modify[k]} = f(k, 5)
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let n = apply(k, bump)
    n * 100 + Cell.get(k)
"#,
    );
    let mut interp = interp_for(&src);
    crate::common::register_modify_handler(&mut interp);
    let result = interp.call("enclosing.main", &[]);
    assert!(matches!(result, Ok(Value::Int(505))), "{result:?}");
}

fn stream_source(row: &str, declared: &str, entry: &str) -> String {
    format!(
        r#"
namespace enclosingStream
  import anthill.prelude.{{Int64, Cell, Modify, Error, String, Stream, Option, Pair}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.pair
  sort Cnt
    import anthill.prelude.{{Int64, Option, Pair, Stream}}
    import anthill.prelude.Option.{{some, none}}
    import anthill.prelude.Pair.pair
    sort T = ?
    effects EC = ?
    entity cnt(f: (x: Int64) -> T @ {{EC}})
    provides Stream[T = T, E = {{EC}}]
    operation splitFirst(c: Self) -> Option[Pair[A = T, B = Stream[T = T, E = {{EC}}]]] effects {{EC}} =
      match c case cnt(f) -> some(pair(f(5), c))
  end
  import enclosingStream.Cnt.cnt
  operation consume(s: Stream[T = Int64, E = {{}}]) -> Int64 =
    match Stream.splitFirst(s)
      case none() -> 0
      case some(pair(x, _)) -> x
  operation use(k: Cell[V = Int64], s: Cnt[T = Int64, EC = {{{row}}}]) -> Int64 effects {{{declared}}} = consume(s)
  {entry}
end
"#
    )
}

#[test]
fn stream_provider_cannot_hide_enclosing_cell_row() {
    for row in ["Modify[k]", "Error[String]"] {
        let src = stream_source(row, "", "");
        assert_refused_naming(
            &load_errors_of(&src),
            &[
                "consume.s (op-arg)",
                "expected Stream[T = Int64, E = {}]",
                "got Cnt",
            ],
            "provider row is checked",
        );
    }
}

#[test]
fn pure_stream_provider_executes_control() {
    let src = stream_source(
        "",
        "",
        r#"
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    use(k, cnt(lambda (x: Int64) -> x))
"#,
    );
    let mut interp = interp_for(&src);
    let result = interp.call("enclosingStream.main", &[]);
    assert!(matches!(result, Ok(Value::Int(5))), "{result:?}");
}

#[test]
fn let_local_cell_is_checked() {
    let src = source(
        r#"
  operation use() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let b: Box[BE = {Modify[k]}] = box(lambda (x: Int64) -> bump(k, x))
    runPure(b, 5)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["runPure.b (op-arg)", "Modify[T = k]"],
        "let local place is a determined identity",
    );
}
