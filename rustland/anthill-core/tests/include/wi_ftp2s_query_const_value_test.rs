//! WI-20261120-FTP2S — A QUERY HOLDS A COMPUTED CONST'S VALUE (kernel-language §5.9, "A query
//! pattern is the exception to the table"). A query converts against a loaded program, so a
//! const with no load-time value is evaluated where a query names it, and the slot holds what
//! it computes: a literal, or the term of a value with one (an entity, a list, an option, a
//! tuple; `load::query_slot_const`). A const the slot can hold nothing of is refused, naming
//! it: a function, and one the evaluator cannot compute (a dictionary since 24ZZ0, in
//! `wi_2ksaa_dictionary_instance_test`).
//!
//! MEASURED before, on e2fce05e: the query kept the name of a value that is no literal, so
//! `at(p: origin)` answered NO beside `fact at(p: pt(x: 4))` (likewise a list and an option),
//! `?r <=> origin` answered `origin`, `getX(origin)` and `len(xs)` were undecided, and written
//! dotted the argument stayed a `field_access` chain. A closure const handed to an operation
//! was undecided; a host const with no binding answered no.
//!
//! ## What fails with the change backed out
//!
//! Measured 2026-11-20 with a temporary switch per part, then removed, over the whole of
//! `wi_tests` (9687 rows) in one optimized build; the control, no switch, 0 failed.
//!
//! * A value that is no literal kept out of the slot, its name kept as before (the switch
//!   stood before the value's term was asked for, so a function's refusal went too): 3,
//!   [`a_query_holds_a_computed_consts_value`], [`a_call_in_a_query_is_handed_the_value`] and
//!   [`a_const_the_slot_holds_nothing_of_is_refused`].
//! * The refusals of a function and of a const not evaluated off, the name kept silently (a
//!   dictionary's left on): 1, [`a_const_the_slot_holds_nothing_of_is_refused`].
//! * A dictionary inside the value let through (the `/code-review` fix, measured on this file,
//!   `wi_2ksaa` and `wi_kdmqs`, 53 rows): 1, [`a_const_the_slot_holds_nothing_of_is_refused`].
//! * [`a_literal_or_scalar_const_reads_as_before`] passes either way, by design.

use crate::common::{load_kb_with, pattern_answer_counts, query_pattern_refusals};

const PROGRAM: &str = r#"
namespace p.ftp
  import anthill.prelude.{Int64, String, List, Option, Bool}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Additive
  import anthill.realization.runtime.Dictionary
  sort P
    entity pt(x: Int64)
    operation getX(p: P) -> Int64 = match p
      case pt(x) -> x
  end
  sort H
    entity at(p: P)
    entity hasXs(l: List[T = Int64])
    entity hasO(o: Option[T = Int64])
    entity hasT(t: (a: Int64, b: String))
    entity hasN(n: Int64)
  end
  const origin: P = pt(x: 4)
  const xs: List[T = Int64] = [1, 2]
  const some3: Option[T = Int64] = some(3)
  const tup: (a: Int64, b: String) = (a: 1, b: "x")
  const things: List = [1, 2]
  const two: Int64 = 2
  const sum: Int64 = 2 + 3
  const yes: Bool = 1 < 2
  const f: (x: Int64) -> Int64 = lambda (x: Int64) -> x + 1
  const hosted: Int64
  const od: Option[T = Additive[T = Int64]] = some(Dictionary.instance[Additive[T = Int64]]())
  operation len(l: List[T = Int64]) -> Int64 = l.length()
  operation apply1(g: (x: Int64) -> Int64) -> Int64 = g(1)
  fact at(p: pt(x: 4))
  fact hasXs(l: [1, 2])
  fact hasO(o: some(3))
  fact hasT(t: (a: 1, b: "x"))
  fact hasN(n: 5)
end
"#;

fn holds(pattern: &str) -> (usize, usize) {
    let mut kb = load_kb_with(PROGRAM);
    pattern_answer_counts(&mut kb, pattern)
}

/// A fact holding a computed const's value is found through the const's name: an entity, a
/// list, an option, a tuple, and a list declared with its element unwritten (§5.9: a slot the
/// declared type leaves out). The const's value meets itself under `<=>`. Each control, a
/// value no fact holds, answers nothing.
#[test]
fn a_query_holds_a_computed_consts_value() {
    for (pattern, want) in [
        ("p.ftp.H.at(p: p.ftp.origin)", (1, 1)),
        ("p.ftp.H.hasXs(l: p.ftp.xs)", (1, 1)),
        ("p.ftp.H.hasO(o: p.ftp.some3)", (1, 1)),
        ("p.ftp.H.hasT(t: p.ftp.tup)", (1, 1)),
        ("p.ftp.H.hasXs(l: p.ftp.things)", (1, 1)),
        ("p.ftp.P.pt(x: 4) <=> p.ftp.origin", (1, 1)),
        ("p.ftp.P.pt(x: 5) <=> p.ftp.origin", (0, 0)),
        ("p.ftp.H.at(p: p.ftp.P.pt(x: 5))", (0, 0)),
        ("p.ftp.H.at(p: p.ftp.P.pt(x: 4))", (1, 1)),
    ] {
        assert_eq!(holds(pattern), want, "{pattern}");
    }
}

/// A call in a query is handed the const's value, the const named bare-qualified or through
/// its sort: `getX(origin)` is 4 and `len(xs)` 2, definitely.
#[test]
fn a_call_in_a_query_is_handed_the_value() {
    for (pattern, want) in [
        ("4 <=> p.ftp.P.getX(p.ftp.origin)", (1, 1)),
        ("5 <=> p.ftp.P.getX(p.ftp.origin)", (0, 0)),
        ("2 <=> p.ftp.len(p.ftp.xs)", (1, 1)),
        ("3 <=> p.ftp.len(p.ftp.xs)", (0, 0)),
    ] {
        assert_eq!(holds(pattern), want, "{pattern}");
    }
}

/// What the slot can hold nothing of is refused, naming the const: a function, alone or
/// handed to an operation (undecided before), a dictionary inside the value (proposal 074
/// §2; the name before, its value with the splice alone), and a host const this runtime binds
/// no value to (a silent NO before).
#[test]
fn a_const_the_slot_holds_nothing_of_is_refused() {
    let mut kb = load_kb_with(PROGRAM);
    for (pattern, text) in [
        ("?r <=> p.ftp.f", "the const `p.ftp.f` holds a function, which has no term"),
        ("2 <=> p.ftp.apply1(p.ftp.f)", "the const `p.ftp.f` holds a function"),
        (
            "?r <=> p.ftp.od",
            "the const `p.ftp.od` holds a dictionary inside its value, and a dictionary has no value",
        ),
        (
            "p.ftp.H.hasN(n: p.ftp.hosted)",
            "the const `p.ftp.hosted` is evaluated where a query names it, and could not be",
        ),
    ] {
        let refusals = query_pattern_refusals(&mut kb, pattern);
        assert!(refusals.iter().any(|e| e.contains(text)), "{pattern}: {refusals:?}");
    }
}

/// A literal const, a computed scalar, and a computed `Bool` at a goal read as before. Passes
/// either way, by design.
#[test]
fn a_literal_or_scalar_const_reads_as_before() {
    for (pattern, want) in [
        ("3 <=> p.ftp.len([p.ftp.two, p.ftp.two, p.ftp.two])", (1, 1)),
        ("p.ftp.H.hasN(n: p.ftp.sum)", (1, 1)),
        ("p.ftp.yes", (1, 1)),
    ] {
        assert_eq!(holds(pattern), want, "{pattern}");
    }
}
