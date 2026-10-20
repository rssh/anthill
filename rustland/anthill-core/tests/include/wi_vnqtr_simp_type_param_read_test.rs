//! WI-20260911-VNQTR, found by its review — A READ OF A TYPE PARAMETER THAT A REWRITE MOVES
//! INTO A TYPE POSITION IS THE PARAMETER THERE.
//!
//! Under `requires TypeValue[T = K]` a body's `K` read as a value is the slot dispatch that
//! answers it (`TypeValue.type_value[T = K]()`, proposal 065). A `@[simp]` rule fires on a
//! redex whose arguments the typer has typed, so `mkq(K)` under `rule mkq(?k) <=> Map[K = ?k,
//! V = Int64].empty()` put the dispatch where a type goes: `put.key: expected bottom`. It ran
//! without the clause, the read left a type; and once the record listed a variable the
//! signature writes, `?k` was such a read too, so the inline spelling that ran was refused as
//! well (MEASURED). A dispatch synthesized for a read denotes the parameter it reads where a
//! type is wanted, and stays the dispatch where a value is.
//!
//! BACK-OUT, a temporary switch in one build, over the whole `wi_tests` binary (7552 rows) —
//! a lowered read denoting no type: **1 red**,
//! [`a_read_moved_into_a_type_position_is_the_parameter`], and nothing else.

use crate::common::load_errors_of;
use crate::wi_vnqtr_inline_param_forward_test::answers;

const HEAD: &str = r#"
  import anthill.prelude.{Map, Int64, String, Cell, Type}
  import anthill.prelude.Map.{put, size}
  import anthill.reflect.{TypeValue}
  rule mkq(?k) <=> Map[K = ?k, V = Int64].empty() @[simp]
  operation idt(x: Type) -> Type
  rule idt(?x) <=> ?x @[simp]
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace test.vnqtr.simpread.{ns}\n{HEAD}\n{body}\nend\n")
}

/// Moved into a type position — a map's key type — the read is the parameter: the map is at
/// the caller's key type and takes a key of it. A bracket's `K` and a signature's `?k` alike.
#[test]
fn a_read_moved_into_a_type_position_is_the_parameter() {
    let src = program(
        "typepos",
        r#"  operation dqb[K](x: K) -> Int64 requires TypeValue[T = K] = size(put(mkq(K), x, 1))
  operation dqi(x: ?k) -> Int64 requires TypeValue[T = ?k] = size(put(mkq(?k), x, 1))
  operation b() -> Int64 = dqb("a")
  operation i() -> Int64 = dqi("a")"#,
    );
    assert_eq!(load_errors_of(&src), Vec::<String>::new());
    assert_eq!(
        answers(&src, &["test.vnqtr.simpread.typepos.b", "test.vnqtr.simpread.typepos.i"]),
        ["1", "1"]
    );
}

/// CONTROL: kept in a value position, the read is still the dispatch, and answers the type it
/// reads.
#[test]
fn a_read_kept_in_a_value_position_is_the_dispatch() {
    let src = program(
        "valuepos",
        r#"  operation rb[K](x: K) -> Type requires TypeValue[T = K] = idt(K)
  operation ri(x: ?k) -> Type requires TypeValue[T = ?k] = idt(?k)
  operation b() -> Type = rb("a")
  operation i() -> Type = ri(1)"#,
    );
    assert_eq!(load_errors_of(&src), Vec::<String>::new());
    assert_eq!(
        answers(&src, &["test.vnqtr.simpread.valuepos.b", "test.vnqtr.simpread.valuepos.i"]),
        ["String", "Int64"]
    );
}
