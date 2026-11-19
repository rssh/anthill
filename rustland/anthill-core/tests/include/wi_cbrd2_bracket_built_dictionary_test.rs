//! A CALL WHOSE BRACKET FIXES ITS INSTANCE AT A CONCRETE TYPE (WI-20261105-CBRD2). A rule-body
//! call written through a receiver bracket that writes the spec's carrier at a concrete type,
//! `FiniteCollection[C = List[T = String]].size(?ls, ?n)`, is at that instance whatever its
//! arguments are, as a call with an argument at that type is. Where the bracket leaves some of
//! the spec's parameters unwritten (`Element`, `E` here), the typer leaves the call's
//! dictionary to the clause, and the clause's weave gave the call a read of its own. That read
//! carries no bracket, and found the provider from the values of the call's arguments when it
//! ran (`resolve::value_reads_by_this_thread`).
//!
//! The dictionary is now built where the clause is woven, from the provisions at the
//! bracket's types (`fetch_at_goal`, the query's concrete route), and the call carries it.
//! Where the provisions build none the call is refused there; no row reaches that, since a
//! bracket at a carrier nothing provides the spec at is refused by the typer first
//! (`FiniteCollection[C = Int64].size(…)`, measured).
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch restoring the read, then removed. The control is the
//! switch unset: every row passes.
//!
//! * [`a_bracketed_call_reads_no_value`] fails on the reads (two, one per box); its lengths
//!   stand.
//! * [`a_bracket_writing_every_parameter_is_the_typers`] passes either way: the control. A
//!   bracket that writes all of the spec's parameters is built by the typer, which leaves the
//!   clause nothing to weave.

use anthill_core::kb::resolve::value_reads_by_this_thread;

use crate::common::{load_kb_with, load_stdlib_kb, pattern_last_ints};

/// `f`'s result and the reads for a call it answered from a value, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = value_reads_by_this_thread();
    let r = f();
    (r, value_reads_by_this_thread() - before)
}

fn program(tail: &str) -> String {
    format!(
        r#"
namespace test.cbrd2.bracket
  import anthill.prelude.{{Int64, List, String, FiniteCollection}}
  import anthill.prelude.FiniteCollection.{{size}}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort ListShow
    import test.cbrd2.bracket.Show
    sort E = ?
    requires Show[T = E]
    provides Show[T = List[T = E]]
    operation show(x: List[T = E]) -> Int64 = match x case nil -> 100 case cons(h, t) -> Show.show(h) + 10
  end
  sort Box
    entity Box(items: List[T = String])
  end
  fact Box(items: ["a", "b"])
  fact Box(items: [])
  rule sized(?ls, ?n) :- FiniteCollection[C = List[T = String]].size(?ls, ?n)
  rule boxSizes(?n) :- Box(items: ?ls), sized(?ls, ?n)
  fact src([1, 2])
  fact src([])
  rule shown(?x, ?t) :- Show[T = List[T = Int64]].show(?x, ?t)
  rule srcShown(?t) :- src(?x), shown(?x, ?t)
{tail}end
namespace anthill.prelude.Int64
  import test.cbrd2.bracket.Show
  provides Show[T = Int64]
  operation show(x: Int64) -> Int64 = 1
end
"#
    )
}

/// Each box's length, through the bracket's `FiniteCollection` at `List[T = String]`, and
/// nothing read from the lists.
#[test]
fn a_bracketed_call_reads_no_value() {
    let mut kb = load_kb_with(&program(""));
    let (lengths, reads) = counting(|| pattern_last_ints(&mut kb, "test.cbrd2.bracket.boxSizes(?n)"));
    assert_eq!(lengths, vec![0, 2]);
    assert_eq!(reads, 0, "a dictionary read off the values");
}

/// `Show[T = List[T = Int64]]` is `ListShow` over `Int64`'s `Show`, built at load by the
/// typer: `[1, 2]` shows `11` and `[]` `100`, though nothing in `[]` says its element. Passes
/// with the change backed out (the module doc).
#[test]
fn a_bracket_writing_every_parameter_is_the_typers() {
    let mut kb = load_kb_with(&program(""));
    let (shown, reads) = counting(|| pattern_last_ints(&mut kb, "test.cbrd2.bracket.srcShown(?t)"));
    assert_eq!(shown, vec![11, 100]);
    assert_eq!(reads, 0, "a dictionary read off the values");
}
