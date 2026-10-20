//! WI-20260911-VNQTR, found by its review — TWO SLOT PATHS ARE TWO TYPES WHERE A REQUIREMENT
//! IS MATCHED.
//!
//! A requirement the caller holds covers a call's requirement where the two are at one type,
//! and two types that are no structure of parts were compared by their heads once the
//! subtype test refused them. Every projection has the one head, so a requirement at `xs.T`
//! covered a call at `ys.T`: under `m(xs: List, ys: List) requires Stamp[T = xs.T], Stamp[T =
//! ys.T]`, a call at an element of `ys` was handed `xs`'s provider, and the clauses the forward
//! refusal prints for two slots, written as printed, answered with one provider for both.
//! The deeper cover (`wi_vnqtr_transitive_cover_test`) reached the same match through a
//! chain. A projection is related by its path alone, as a value in a type position is by its
//! value.
//!
//! BACK-OUT, a temporary switch in one build, over the whole `wi_tests` binary (7552 rows) —
//! projections compared by their head again: **2 red**, both rows here, and nothing else.

use crate::common::load_errors_of;
use crate::wi_vnqtr_inline_param_forward_test::{answers, the_one_refusal};

const HEAD: &str = r#"
  import anthill.prelude.{Int64, List, cons, nil}
  sort Stamp
    sort T = ?
    operation stamp() -> Int64
  end
  sort Mid
    sort T = ?
    requires Stamp[T = T]
    operation mid() -> Int64
  end
  sort Leaf
    entity leaf(n: Int64)
    provides Stamp[T = Leaf]
    provides Mid[T = Leaf]
    operation stamp() -> Int64 = 7
    operation mid() -> Int64 = 70
  end
  sort Twig
    entity twig(n: Int64)
    provides Stamp[T = Twig]
    provides Mid[T = Twig]
    operation stamp() -> Int64 = 9
    operation mid() -> Int64 = 90
  end
  operation stampOf[B](x: B) -> Int64 requires Stamp[T = B] = Stamp.stamp[T = B]()
  operation stampOfL[B](xs: List[T = B]) -> Int64 requires Stamp[T = B] = Stamp.stamp[T = B]()
"#;

fn program(ns: &str, body: &str) -> String {
    format!(
        "namespace test.vnqtr.paths.{ns}\n{HEAD}\n{body}\n  operation go() -> Int64 = m(cons(leaf(n: 1), nil), cons(twig(n: 2), nil))\nend\n"
    )
}

/// Each slot's requirement answers for its own slot, whichever clause comes first: `ys`'s
/// element is a twig, 9, and both lists read alike, `79`. One provider answered for both,
/// `7` and `77` (MEASURED).
#[test]
fn each_slot_is_answered_by_its_own_requirement() {
    for (ns, clauses, body, answer) in [
        (
            "element",
            "Stamp[T = xs.T], Stamp[T = ys.T]",
            "match ys\n      case cons(h, r) -> stampOf(h)\n      case nil() -> 0",
            "9",
        ),
        ("lists", "Stamp[T = xs.T], Stamp[T = ys.T]", "stampOfL(xs) * 10 + stampOfL(ys)", "79"),
        (
            "through",
            "Mid[T = xs.T], Mid[T = ys.T]",
            "match ys\n      case cons(h, r) -> stampOf(h)\n      case nil() -> 0",
            "9",
        ),
    ] {
        let src = program(ns, &format!("  operation m(xs: List, ys: List) -> Int64 requires {clauses} =\n    {body}"));
        assert_eq!(load_errors_of(&src), Vec::<String>::new(), "{ns}");
        assert_eq!(answers(&src, &[&format!("test.vnqtr.paths.{ns}.go")]), [answer], "{ns}");
    }
}

/// A requirement at one slot covers no call at another: the call at `ys`'s element is
/// refused naming `ys.T`, where `xs`'s provider answered it.
#[test]
fn a_requirement_at_one_slot_covers_no_other() {
    let src = program(
        "other",
        "  operation m(xs: List, ys: List) -> Int64 requires Stamp[T = xs.T] =\n    match ys\n      case cons(h, r) -> stampOf(h)\n      case nil() -> 0",
    );
    the_one_refusal(&src, &["`test.vnqtr.paths.other.Stamp[T = ys.T]`", "holds nothing for `ys.T`"]);
}
