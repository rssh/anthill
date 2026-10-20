//! WI-20260911-VNQTR, found on the way — A FORWARD OF A SLOT THE CALLER'S SIGNATURE LEAVES
//! UNWRITTEN IS REFUSED, AS A FORWARD OF A PARAMETER IS.
//!
//! §5.4 quantifies a slot left out of a parameter's type, or written `?`, as it does a
//! variable written there. `relayA(xs: List) -> Type = tyOfL(xs)`, over `tyOfL[B](xs: List[T =
//! B]) requires TypeValue[T = B]`, hands the slot to an operation that demands evidence about
//! it; it loaded and died at run time, "requirement param `__req_typevalue` not bound". Now:
//!
//! * a slot at the top of a parameter's type is checked as the projection `xs.T`, which a
//!   clause can name, and the refusal prints `requires TypeValue[T = xs.T]` — wherever the
//!   slot stands in what the call passes, the whole argument or a part of an application;
//! * so is a slot an alias leaves open at the top of a parameter's type, which the body reads
//!   by the same path;
//! * a slot NESTED inside one (`List[T = Box]`, `Box[V = ?]`) has no name a clause could
//!   write, and the refusal says to write a variable for it first.
//!
//! BACK-OUTS, each a temporary switch in one build, over the whole `wi_tests` binary (7552
//! rows):
//!
//! * **slots not read by the forward refusal**: **5 red** here — every row but
//!   [`a_slot_named_by_a_variable_is_refused_as_its_parameter`], the record's — and 7 across
//!   the binary (`an_anonymous_variable_in_the_carrier_is_the_slot_it_stands_in`,
//!   `a_requirement_at_one_slot_covers_no_other`).
//! * **a slot inside an application read as ground**: **1 red** here,
//!   [`a_slot_inside_an_application_is_named_by_its_path`] (2 across the binary).
//! * **a nested slot printed `?V`**: **1 red**, [`a_nested_slot_is_named_first`].
//! * **an alias's slot opened to a rigid of its own**: **1 red**,
//!   [`an_aliases_slot_at_the_top_is_named_by_its_path`].

use crate::common::replace_in_fixture;
use crate::wi_vnqtr_inline_param_forward_test::{answers, the_one_refusal, with_printed_repair};

const HEAD: &str = r#"
  import anthill.prelude.{Bool, Cell, Int64, Type, List, cons, nil}
  import anthill.reflect.{TypeValue}
  sort Box[V]
    entity box(v: V)
  end
  sort Two[A, C]
    entity two(a: A, c: C)
  end
  operation tyOf[X](x: X) -> Type requires TypeValue[T = X] = Cell[V = X]
  operation tyOfL[B](xs: List[T = B]) -> Type requires TypeValue[T = B] = Cell[V = B]
  operation tyOfLB[B](xs: List[T = Box[V = B]]) -> Type requires TypeValue[T = B] = Cell[V = B]
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace test.vnqtr.slot.{ns}\n{HEAD}\n{body}\nend\n")
}

/// A slot left out at the top of a parameter's type, and one written `?` there, are its path
/// `xs.T`; the printed clause repairs the forward, and the `nil` that carried no element type
/// answers.
#[test]
fn a_top_level_slot_is_named_by_its_path() {
    for (ns, ty) in [("omitted", "List"), ("anon", "List[T = ?]")] {
        let src = program(
            ns,
            &format!(
                "  operation relayA(xs: {ty}) -> Type = tyOfL(xs)\n  operation empty() -> Type =\n    let xs: List[T = Int64] = nil\n    relayA(xs)"
            ),
        );
        the_one_refusal(
            &src,
            &[
                "its carrier is `xs.T`, a slot the signature of the CALLING operation",
                "leaves unwritten in the type of its parameter `xs`",
                "Declare `requires anthill.reflect.TypeValue[T = xs.T]`",
            ],
        );
        let repaired = with_printed_repair(
            &src,
            &format!("operation relayA(xs: {ty}) -> Type"),
            &format!("test.vnqtr.slot.{ns}.relayA"),
        );
        assert_eq!(
            answers(&repaired, &[&format!("test.vnqtr.slot.{ns}.empty")]),
            ["Cell(V: Int64)"],
            "{ns}"
        );
    }
}

/// A slot that stands INSIDE what the call passes is the same slot: `tyOf(xs)` passes `List[T =
/// xs.T]`, and `tyOf(two(a: h, c: 1))` passes `Two[A = xs.T, C = Int64]` for an `h` of `xs`.
/// Each is refused naming `xs.T` and printing the clause that answers — and alike whether a
/// parameter of the caller's stands beside the slot or a ground type does. A slot is a
/// projection, which counts as ground, so the whole was taken for a concrete type: refused as
/// a call at a type no row of `TypeValue` may be written for, and the slot named only where a
/// parameter of the caller's stood beside it (MEASURED).
#[test]
fn a_slot_inside_an_application_is_named_by_its_path() {
    for (ns, op, body, call, answer) in [
        ("whole", "operation m(xs: List) -> Type", "tyOf(xs)", "m(xs)", "Cell[V = List[T = Int64]]"),
        (
            "part",
            "operation m(xs: List) -> Type",
            "match xs\n      case cons(h, t) -> tyOf(two(a: h, c: 1))\n      case nil() -> Int64",
            "m(cons(5, xs))",
            "Cell[V = Two[A = Int64, C = Int64]]",
        ),
        (
            "beside",
            "operation m[U](xs: List, u: U) -> Type requires TypeValue[T = U]",
            "match xs\n      case cons(h, t) -> tyOf(two(a: h, c: u))\n      case nil() -> Int64",
            "m(cons(5, xs), \"s\")",
            "Cell[V = Two[A = Int64, C = String]]",
        ),
    ] {
        // The answer compared with a written type: a type's printed bindings follow no
        // declared order.
        let src = program(
            ns,
            &format!(
                "  {op} =\n    {body}\n  operation go() -> Bool =\n    let xs: List[T = Int64] = nil\n    {call} = {answer}"
            ),
        );
        let e = the_one_refusal(
            &src,
            &[
                "holds `xs.T`, a slot the signature of the CALLING operation",
                "Declare `requires anthill.reflect.TypeValue[T = xs.T]`",
            ],
        );
        assert!(!e.contains("none may be written"), "{ns}: {e}");
        let repaired = replace_in_fixture(
            &src,
            &format!("{op} ="),
            &format!(
                "{op}{} TypeValue[T = xs.T] =",
                if op.contains("requires") { "," } else { " requires" }
            ),
        );
        assert_eq!(answers(&repaired, &[&format!("test.vnqtr.slot.{ns}.go")]), ["true"], "{ns}");
    }
}

/// A slot nested in a parameter's type has no name: the refusal prints no clause and says to
/// write a variable for it. Written so, with the clause over the variable, the call answers.
#[test]
fn a_nested_slot_is_named_first() {
    for (ns, ty) in [("nested", "List[T = Box]"), ("nestedanon", "List[T = Box[V = ?]]")] {
        let src = program(
            ns,
            &format!(
                "  operation relayN(xs: {ty}) -> Type = tyOfLB(xs)\n  operation one() -> Type = relayN(cons(box(v: 1), nil))"
            ),
        );
        let e = the_one_refusal(
            &src,
            &["its carrier is `Box.V`, an unknown the signature of the CALLING operation", "Write a variable in that slot"],
        );
        assert!(!e.contains("Declare `requires"), "no clause can name the slot: {e}");
        let named = replace_in_fixture(
            &src,
            &format!("operation relayN(xs: {ty}) -> Type = tyOfLB(xs)"),
            "operation relayN(xs: List[T = Box[V = ?v]]) -> Type requires TypeValue[T = ?v] = tyOfLB(xs)",
        );
        assert_eq!(
            answers(&named, &[&format!("test.vnqtr.slot.{ns}.one")]),
            ["Cell(V: Int64)"],
            "{ns}"
        );
    }
}

/// A slot an alias leaves open at the top of a parameter's type is read by its path as a slot
/// left out is: `y: LT` over `sort LT = List[T = ?a]` is checked as `y: List[T = y.T]`. The
/// forward is refused naming `y.T`, and the clause it prints answers. Opened to a rigid of
/// its own, no clause could name the slot: the refusal advised writing a variable the alias
/// does not take, and `requires TypeValue[T = y.T]` did not cover it (MEASURED).
#[test]
fn an_aliases_slot_at_the_top_is_named_by_its_path() {
    let src = program(
        "alias",
        "  sort LT = List[T = ?a]\n  operation m(y: LT) -> Type = tyOfL(y)\n  operation empty() -> Type =\n    let xs: List[T = Int64] = nil\n    m(xs)",
    );
    the_one_refusal(
        &src,
        &["its carrier is `y.T`", "Declare `requires anthill.reflect.TypeValue[T = y.T]`"],
    );
    let repaired = with_printed_repair(&src, "operation m(y: LT) -> Type", "test.vnqtr.slot.alias.m");
    assert_eq!(answers(&repaired, &["test.vnqtr.slot.alias.empty"]), ["Cell(V: Int64)"]);
}

/// A slot an alias leaves open INSIDE an argument has no path, and is named first, as a
/// nested slot the signature leaves out is.
#[test]
fn an_aliases_slot_inside_an_argument_is_named_first() {
    let src = program(
        "aliasnested",
        "  sort LB = List[T = Box[V = ?a]]\n  operation m(y: LB) -> Type = tyOfLB(y)",
    );
    let e = the_one_refusal(&src, &["`?a`, an unknown the signature of the CALLING operation"]);
    assert!(!e.contains("Declare `requires"), "no clause can name the alias's slot: {e}");
}

/// A slot the author names with a variable is a parameter of the caller's, refused and
/// repaired as one. It loaded at HEAD, the variable on no record of the operation's: this is
/// the record's row, not the slot reading's.
#[test]
fn a_slot_named_by_a_variable_is_refused_as_its_parameter() {
    let src = program(
        "named",
        "  operation relayV(xs: List[T = ?e]) -> Type = tyOfL(xs)\n  operation empty() -> Type =\n    let xs: List[T = Int64] = nil\n    relayV(xs)",
    );
    the_one_refusal(&src, &["Declare `requires anthill.reflect.TypeValue[T = ?e]`"]);
    let repaired = with_printed_repair(
        &src,
        "operation relayV(xs: List[T = ?e]) -> Type",
        "test.vnqtr.slot.named.relayV",
    );
    assert_eq!(answers(&repaired, &["test.vnqtr.slot.named.empty"]), ["Cell(V: Int64)"]);
}
