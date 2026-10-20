//! WI-20260911-VNQTR, found by its review — A MEMBER'S TYPE PARAMETERS ARE THE SPEC
//! OPERATION'S WHERE THEY STAND, AND A RESTATEMENT IS READ CONJUNCT BY CONJUNCT.
//!
//! The record lists an operation's type parameters by family — the bracket's, the member
//! sugar's, then the variables the signature writes, in the order first written — and the
//! member's were paired with the spec operation's by position on it. Once the record listed
//! the written variables, a position crossed families and spellings: a member `d[B](x: ?a, y:
//! B)` beside `d(x: ?a, y: ?b)` paired its `?a` with the spec's `?b`, so a strengthening
//! `requires` read as a restatement and the member answered at another parameter's type; and
//! two sides writing different numbers of variables paired nothing at all, so providers that
//! ran were refused. A declared parameter is paired by position, where the two declare as
//! many; a variable by where it stands in the two signatures, read as types (an application's
//! arguments by key).
//!
//! BACK-OUT, a temporary switch in one build, over the whole `wi_tests` binary (7552 rows) —
//! the record's lists zipped by position, as before: **3 red**, every row here, and nothing
//! else.

use crate::common::{assert_refused_naming, load_errors_of};
use crate::wi_vnqtr_inline_param_forward_test::answers;

const HEAD: &str = r#"
  import anthill.prelude.{Cell, Int64, String, Type, List, Pair}
  import anthill.prelude.Pair.{pair}
  import anthill.reflect.{TypeValue}
  operation tyOf[X](x: X) -> Type requires TypeValue[T = X] = Cell[V = X]
  sort Box[V]
    entity box(v: V)
  end
"#;

fn program(ns: &str, spec_op: &str, member: &str, call: &str) -> String {
    format!(
        "namespace test.vnqtr.pair.{ns}\n{HEAD}\n  sort Desc\n    sort T = ?\n    {spec_op}\n  end\n  sort Leaf\n    entity leaf(n: Int64)\n    provides Desc[T = Leaf]\n    {member}\n  end\n  operation go() -> Type = {call}\nend\n"
    )
}

/// A member that requires evidence about ANOTHER parameter than the spec operation does is
/// a strengthening, whatever the spellings: refused. Paired by position on the record, the
/// member's `?a` (the type of `x`) was the spec's `?b` (the type of `y`), the clause read as
/// a restatement, and `tyOf(x)` at `5` answered `Cell(V: String)` (MEASURED).
#[test]
fn a_strengthening_member_in_another_spelling_is_refused() {
    for (ns, spec_op, member) in [
        (
            "bracket",
            "operation d(x: T, y: ?a, z: ?b) -> Type requires TypeValue[T = ?b]",
            "operation d[B](x: Leaf, y: ?a, z: B) -> Type requires TypeValue[T = ?a] = tyOf(y)",
        ),
        (
            "inline",
            "operation d[B](x: T, y: ?a, z: B) -> Type requires TypeValue[T = B]",
            "operation d(x: Leaf, y: ?p, z: ?q) -> Type requires TypeValue[T = ?p] = tyOf(y)",
        ),
    ] {
        let src = program(ns, spec_op, member, "Desc.d(leaf(n: 1), 5, \"s\")");
        assert_refused_naming(
            &load_errors_of(&src),
            &["strengthens the precondition"],
            &format!("{ns}: the member requires evidence about another parameter"),
        );
    }
}

/// A member restating the spec operation's requirement in another spelling answers: a
/// bracket opposite a variable, either way round, and a variable at a named argument written
/// in the other order. Each was refused as a strengthening.
#[test]
fn a_restatement_in_another_spelling_answers() {
    for (ns, spec_op, member, call, answer) in [
        (
            "brvar",
            "operation d[U](x: T, y: U) -> Type requires TypeValue[T = U]",
            "operation d(x: Leaf, y: ?t) -> Type requires TypeValue[T = ?t] = tyOf(y)",
            "Desc.d(leaf(n: 1), 5)",
            "Cell(V: Int64)",
        ),
        (
            "varbr",
            "operation d(x: T, y: ?t) -> Type requires TypeValue[T = ?t]",
            "operation d[U](x: Leaf, y: U) -> Type requires TypeValue[T = U] = tyOf(y)",
            "Desc.d(leaf(n: 1), \"s\")",
            "Cell(V: String)",
        ),
        (
            "mixed",
            "operation d(x: T, y: ?a, z: ?b) -> Type requires TypeValue[T = ?b]",
            "operation d[B](x: Leaf, y: ?a, z: B) -> Type requires TypeValue[T = B] = tyOf(z)",
            "Desc.d(leaf(n: 1), 5, \"s\")",
            "Cell(V: String)",
        ),
        (
            "keys",
            "operation d(x: T, y: Pair[A = ?a, B = ?b]) -> Type requires TypeValue[T = ?b]",
            "operation d(x: Leaf, y: Pair[B = ?p, A = ?q]) -> Type requires TypeValue[T = ?p] = ?p",
            "Desc.d(leaf(n: 1), pair(5, \"s\"))",
            "String",
        ),
    ] {
        let src = program(ns, spec_op, member, call);
        assert_eq!(load_errors_of(&src), Vec::<String>::new(), "{ns}");
        assert_eq!(answers(&src, &[&format!("test.vnqtr.pair.{ns}.go")]), [answer], "{ns}");
    }
}

/// CONTROL for the variables' reading: where the two sides write different numbers of
/// variables, the declared parameters are still paired by position — a member writing a slot
/// as a variable the spec operation leaves out (`b: Box[V = ?v]` beside `b: Box`), or the
/// member sugar beside one. Paired by position across the whole record, nothing was paired,
/// and the restatement was refused as a strengthening (MEASURED: both ran before the record
/// listed the variables).
#[test]
fn a_member_writing_another_number_of_variables_restates_the_declared_ones() {
    let src = program(
        "count",
        "operation d[U](x: T, y: U, b: Box) -> Type requires TypeValue[T = U]",
        "operation d[U](x: Leaf, y: U, b: Box[V = ?v]) -> Type requires TypeValue[T = U] = tyOf(y)",
        "Desc.d(leaf(n: 1), 5, box(v: \"s\"))",
    );
    assert_eq!(answers(&src, &["test.vnqtr.pair.count.go"]), ["Cell(V: Int64)"]);
}
