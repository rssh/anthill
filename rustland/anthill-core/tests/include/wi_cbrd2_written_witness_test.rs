//! A WITNESS WRITTEN IN A COLUMN'S TYPE (WI-20261105-CBRD2). A clause whose column writes a named
//! requirement slot at a witness, `rule cmpV(?p: Pair2[T = ?v, U = ?v, O = Down], ?c) :- ?p <=>
//! pr(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)` over `sort Pair2 { sort T = ?  sort U = ?
//! requires O: WeakOrd[T = T]  entity pr(a: T, b: U) }`, makes the call's read `O`'s: `Down` at
//! the type the citation fixes `?v` to (060.1 §8.2, kernel-language §5.4: "filled from that slot
//! as the citation fixes it"). Two things kept it from being read:
//!
//! * the citation's reading of a slot took one held by a variable of the clause's typing only,
//!   and skipped a slot the clause writes (`carried_slot_reading`);
//! * a rule goal's citation read a construction written in it (`pr(a: 4, b: 5)`) at no type,
//!   so the column stayed at its own bound and `?v` open (`rule_goal_edge`).
//!
//! The read was left unrouted and found its provider from the value when the call ran:
//! `Int64`'s own, `-1` for `(4, 5)`, where `Down` gives `1`. At a concrete `T` the call is no
//! read of the slot (§5.4: "a read at another type … is not the slot's"): it is pinned to
//! `Int64`'s own at load, as the same call in an operation is.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every row
//! passes.
//!
//! * The written witness skipped: [`a_witness_written_in_a_column_is_read_at_the_citations_type`]
//!   fails, `-1` and a read per goal; [`a_written_witness_that_does_not_answer_is_refused`]
//!   fails, the goal loading.
//! * The construction at no type: the witness is checked at an open `T`, and `viaV` itself is
//!   refused, "Down provides … but not at the bindings"; the two rows that load the program
//!   fail on it, and [`a_written_witness_that_does_not_answer_is_refused`] passes, refused for
//!   that.
//! * [`at_a_concrete_type_the_call_is_not_the_slots`] passes with the written witness skipped:
//!   the control.

use anthill_core::kb::resolve::value_reads_by_this_thread;

use crate::common::{interp_for, load_errors_of, load_kb_with, load_stdlib_kb, pattern_last_ints};

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
namespace test.cbrd2.ww
  import anthill.prelude.{{Int64, String, WeakOrd, Ord}}
  import anthill.prelude.Numeric.{{sub}}
  sort Pair2
    sort T = ?
    sort U = ?
    requires O: WeakOrd[T = T]
    entity pr(a: T, b: U)
  end
  sort Down
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  operation opConcrete(p: Pair2[T = Int64, U = Int64, O = Down]) -> Int64 =
    match p case pr(a, b) -> WeakOrd.compare(a, b)
  operation callOp() -> Int64 = opConcrete(pr(a: 4, b: 5))
  rule cmpE(?p: Pair2[T = Int64, U = Int64, O = Down], ?c) :- ?p <=> pr(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
  rule viaE(?c) :- cmpE(pr(a: 4, b: 5), ?c)
  rule cmpV(?p: Pair2[T = ?v, U = ?v, O = Down], ?c) :- ?p <=> pr(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
  rule viaV(?c) :- cmpV(pr(a: 4, b: 5), ?c)
{tail}end
"#
    )
}

/// `Down` at `?v = Int64`, the type `pr(a: 4, b: 5)` fixes: `compare(4, 5)` is `1`, through a
/// rule goal and asked as a query, nothing read from the values.
#[test]
fn a_witness_written_in_a_column_is_read_at_the_citations_type() {
    let mut kb = load_kb_with(&program(""));
    for query in ["test.cbrd2.ww.viaV(?c)", "test.cbrd2.ww.cmpV(test.cbrd2.ww.Pair2.pr(a: 4, b: 5), ?c)"] {
        let (answers, reads) = counting(|| pattern_last_ints(&mut kb, query));
        assert_eq!(answers, vec![1], "{query}: `Down`'s order");
        assert_eq!(reads, 0, "{query}: a dictionary read off the values");
    }
}

/// `Down` provides no order at `String`: a goal citing `cmpV` at `pr(a: "x", b: "y")` is refused
/// at load, naming it, where it answered `String`'s own order from the values.
#[test]
fn a_written_witness_that_does_not_answer_is_refused() {
    let errors = load_errors_of(&program("  rule viaS(?c) :- cmpV(pr(a: \"x\", b: \"y\"), ?c)\n"));
    assert!(
        errors.iter().any(|e| e.contains("Down provides anthill.prelude.WeakOrd, but not at the bindings")),
        "refused, naming `Down`: {errors:?}"
    );
}

/// At `T = Int64` the call is at a concrete type, not the slot's: `Int64`'s own, `-1`, in the
/// rule as in the operation. Passes either way (the module doc).
#[test]
fn at_a_concrete_type_the_call_is_not_the_slots() {
    let mut kb = load_kb_with(&program(""));
    let (answers, reads) = counting(|| pattern_last_ints(&mut kb, "test.cbrd2.ww.viaE(?c)"));
    assert_eq!(answers, vec![-1]);
    assert_eq!(reads, 0);
    let mut interp = interp_for(&program(""));
    let got = interp.call("test.cbrd2.ww.callOp", &anthill_core::eval::HostValue::all(&[])).map(|h| h.value);
    assert!(matches!(got, Ok(anthill_core::eval::Value::Int(-1))), "{got:?}");
}
