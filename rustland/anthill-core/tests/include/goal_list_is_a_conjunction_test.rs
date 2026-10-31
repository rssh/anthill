//! A parenthesized goal list is the conjunction of its goals (kernel-language.md §5.3).
//!
//! THE RULE. At a goal position — a body goal, an `|` / `&` branch, a negand, a component of
//! a quantifier's body or of a discharge's consequent, the body of a mirror-form rule —
//! `(g₁, …, gₙ)` is `g₁ & … & gₙ`. In a value position it is the tuple it is: a goal's
//! argument, an operand of `<=>`, a fact's column.
//!
//! BEFORE (measured 2026-10-31 on 10767b15): the list was the tuple at every position. A tuple
//! heads no clause, so as a goal it failed with no diagnostic — `p(?x) :- (a(?x), b(?x))`
//! answered nothing — and under `not` it held, whether the goals did or not.
//!
//! EVERY ROW HAS ITS OWN SOURCE. CONTROLS at each row.

use anthill_core::eval::Value;

use crate::common::{load_kb_with, query_unary};

/// `test.<name>`: `a` holds at 1 and 2, `b` at 2 and 3, so their conjunction holds at 2 alone;
/// `c` holds at 1, 2 and 3.
fn ns(name: &str, body: &str) -> String {
    format!(
        "namespace test.{name}\n  import anthill.prelude.{{Int64}}\n  \
         fact a(1)\n  fact a(2)\n  fact b(2)\n  fact b(3)\n  \
         fact c(1)\n  fact c(2)\n  fact c(3)\n{body}\nend\n"
    )
}

/// The `Int64` answers of `test.<name>.value(?r)` over `body`, sorted; every one definite.
#[track_caller]
fn ints(name: &str, body: &str) -> Vec<i64> {
    let mut kb = load_kb_with(&ns(name, body));
    let mut out: Vec<i64> = query_unary(&mut kb, &format!("test.{name}.value"))
        .into_iter()
        .map(|(v, definite)| match (v, definite) {
            (Value::Int(n), true) => n,
            other => panic!("{name}: expected a definite Int64, got {other:?}"),
        })
        .collect();
    out.sort();
    out
}

/// EVERY GOAL POSITION reads the list as the conjunction: each spelling answers 2, where `a`
/// and `b` both hold. FAILS with the list read as a tuple (`is_written_goal_list` answering
/// `false`): every spelling but the flat one answers nothing. The flat spelling passes either
/// way by design.
#[test]
fn a_goal_list_is_a_conjunction_at_every_goal_position() {
    for (name, body) in [
        ("gl.flat", "  rule value(?r) :- a(?r), b(?r)"),
        ("gl.top", "  rule value(?r) :- (a(?r), b(?r))"),
        ("gl.later", "  rule value(?r) :- c(?r), (a(?r), b(?r))"),
        ("gl.branch", "  rule value(?r) :- (a(?r), b(?r)) | false"),
        ("gl.nested", "  rule value(?r) :- ((a(?r), c(?r)), b(?r))"),
        (
            "gl.quantified",
            "  rule value(?r) :- c(?r), (forall ?z in [1]: (a(?r), b(?r)))",
        ),
        (
            "gl.inquantifier",
            "  rule value(?r) :- c(?r), (forall ?z in [1]: c(?r), (a(?r), b(?r)))",
        ),
        ("gl.mirror", "  rule (a(?r), b(?r)) -: value(?r)"),
    ] {
        assert_eq!(ints(name, body), [2], "{name}");
    }
}

/// A NEGATED LIST IS THE NEGATED CONJUNCTION: `not((a, b))` and `not(a, b)` hold at 1 and 3,
/// where the two goals do not both hold, and fail at 2. FAILS with the list read as a tuple:
/// both answer 1, 2 and 3, the tuple's failure read as a disproof.
#[test]
fn a_negated_goal_list_is_the_negated_conjunction() {
    for (name, body) in [
        ("gl.negated", "  rule value(?r) :- c(?r), not((a(?r), b(?r)))"),
        ("gl.negtwo", "  rule value(?r) :- c(?r), not(a(?r), b(?r))"),
    ] {
        assert_eq!(ints(name, body), [1, 3], "{name}");
    }
}

/// IN A VALUE POSITION THE LIST IS A TUPLE: a fact's column, a goal's argument and an operand
/// of `<=>` hold `(1, 2)`, which `(?r, 2)` takes apart to 1. Passes either way by design: it is
/// the half of the rule the change leaves as it was.
#[test]
fn a_parenthesized_list_in_a_value_position_is_a_tuple() {
    for (name, body) in [
        ("gl.argument", "  fact pair((1, 2))\n  rule value(?r) :- pair((?r, 2))"),
        ("gl.column", "  fact pair((1, 2))\n  rule value(?r) :- pair(?t), ?t <=> (?r, 2)"),
        ("gl.operand", "  rule value(?r) :- ?t <=> (1, 2), ?t <=> (?r, 2)"),
    ] {
        assert_eq!(ints(name, body), [1], "{name}");
    }
}
