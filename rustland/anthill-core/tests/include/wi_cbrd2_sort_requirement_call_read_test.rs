//! A SORT'S REQUIREMENT REACHES A CLAUSE'S CALL (WI-20261105-CBRD2). A rule of a sort declares
//! no requirement its sort states (060.1 §8.2); a call in it at the sort's parameter —
//! `rule direct(?x: T, ?t) :- Marker.tag(?x, ?t)` in `sort Holder` with `requires Marker[T = T]`
//! — reads that requirement. Two places read it from the value instead:
//!
//! * a goal of another clause of the sort, `rule d2(?x: T, ?t) :- direct(?x, ?t)`, passed
//!   `direct`'s read nothing, and the read found `Marker`'s provider from the value of `?x`:
//!   `Holder[T = Int64].d2(?x, ?t)` waited on it. The citing clause now reads the requirement
//!   and passes it, as it does for a guard (`call_read_at_goal`), and where it reads it for a
//!   call of its own, it passes that read;
//! * a citation of `direct` filled its read from the provisions at the receiver's type alone,
//!   which leaves `Conv[A = Int64]` to two providers in `sort Two2` with `requires Conv[A = T,
//!   B = U]`: `Two2[T = Int64, U = Bool].direct(1, ?r)` waited. It now reads the sort's
//!   requirement at the types the citation fixes (`call_read_is_the_sorts_requirement`).
//!
//! The read a clause takes for its goal is the requirement as the sort states it, every
//! parameter it binds included: a callee that names only `A` is handed `Conv[A = T, B = U]`,
//! which the citation decides.
//!
//! The answers with a bound argument are the ones the values gave, so the rows measure the
//! reading (`resolve::value_reads_by_this_thread`, which counts the reads for a call answered
//! with no dictionary passed in) beside them.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * No read handed on for a callee's call: [`a_goal_passes_the_sorts_requirement_to_a_call`]
//!   fails on the reads, and [`a_citation_reads_the_requirement_as_the_sort_states_it`] at
//!   `viaCall`.
//! * The citation's read of a call at the receiver's type alone:
//!   [`a_citation_reads_the_requirement_as_the_sort_states_it`] fails at `direct`.
//! * The read handed on at what the callee names (`Conv[A = T]`), not as the sort states it:
//!   [`a_citation_reads_the_requirement_as_the_sort_states_it`] fails, the program refused at
//!   load.
//! * Two requirements stated with no name taken as the first:
//!   [`two_requirements_the_goal_both_fits_are_refused`] fails, its goal loading clean and
//!   `viaBoth` answering `1`.
//! * The clause's own read for a call not handed on: no row here fails; the clause takes a
//!   second read of the requirement, which `anthill-cli`'s
//!   `wi_fheek_inlined_names_test::an_own_variable_of_a_declared_sort_is_declared_at_it`
//!   measures as one more name of its frame.

use anthill_core::kb::resolve::value_reads_by_this_thread;

use crate::common::{load_errors_of, load_kb_with, load_stdlib_kb, pattern_answer_counts, pattern_last_ints};

/// `f`'s result and the reads for a call it answered from a value, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = value_reads_by_this_thread();
    let r = f();
    (r, value_reads_by_this_thread() - before)
}

const HOLDER: &str = r#"
namespace test.cbrd2.call.h
  import anthill.prelude.{Int64, Bool}
  sort Marker
    sort T = ?
    operation tag(x: T) -> Int64
    operation big(x: T) -> Bool
  end
  sort IntMarker
    provides Marker[T = Int64]
    operation tag(x: Int64) -> Int64 = 1
    operation big(x: Int64) -> Bool = x > 2
  end
  sort BoolMarker
    provides Marker[T = Bool]
    operation tag(x: Bool) -> Int64 = 2
    operation big(x: Bool) -> Bool = x
  end
  fact pool(1)
  fact pool(5)
  sort Holder
    sort T = ?
    requires Marker[T = T]
    rule direct(?x: T, ?t) :- Marker.tag(?x, ?t)
    rule bigOne(?x: T) :- Marker.big(?x)
    rule d2(?x: T, ?t) :- direct(?x, ?t)
    rule d3(?x: T, ?t) :- d2(?x, ?t)
    rule dnot(?x: T, ?t) :- not(bigOne(?x)), ?t <=> 9
    rule dor(?x: T, ?t) :- direct(?x, ?t) | ?t <=> 0
    rule both(?x: T, ?t) :- direct(?x, ?t), bigOne(?x)
  end
  rule atInt(?t) :- Holder[T = Int64].d2(1, ?t)
  rule atBool(?t) :- Holder[T = Bool].d3(true, ?t)
  rule notBig(?t) :- Holder[T = Int64].dnot(1, ?t)
  rule notBig5(?t) :- Holder[T = Int64].dnot(5, ?t)
  rule branched(?t) :- Holder[T = Bool].dor(true, ?t)
  rule pooled(?t) :- pool(?x), Holder[T = Int64].both(?x, ?t)
  rule unbound(?t) :- Holder[T = Int64].d2(?x, ?t)
end
"#;

/// A goal of another clause of the sort passes `direct`'s read the sort's `Marker`: through a
/// chain of clauses, under `not`, in a branch of `|`, beside another goal, and from a query,
/// whose types fix `T`. With `?x` unbound the answer is `Int64`'s `1`, its column's domain left.
#[test]
fn a_goal_passes_the_sorts_requirement_to_a_call() {
    let ns = "test.cbrd2.call.h";
    for (pattern, want) in [
        ("atInt(?t)", vec![1]),
        ("atBool(?t)", vec![2]),
        ("notBig(?t)", vec![9]),
        ("notBig5(?t)", vec![]),
        ("branched(?t)", vec![0, 2]),
        ("pooled(?t)", vec![1]),
        ("Holder.d2(1, ?t)", vec![1]),
    ] {
        let mut kb = load_kb_with(HOLDER);
        let (got, reads) = counting(|| pattern_last_ints(&mut kb, &format!("{ns}.{pattern}")));
        assert_eq!(reads, 0, "`{pattern}` read a provider from a value");
        assert_eq!(got, want, "`{pattern}`");
    }
    let mut kb = load_kb_with(HOLDER);
    let ((_, total), reads) = counting(|| pattern_answer_counts(&mut kb, &format!("{ns}.unbound(?t)")));
    assert_eq!((total, reads), (1, 0), "`unbound(?t)`: one answer, no read from a value");
}

/// `Two2[T = Int64, U = Bool]` reads `Conv[A = Int64, B = Bool]`, `IntBool`'s, through the
/// clause's own call, a goal of another clause's call, and a goal of a rule guarding `Conv[A =
/// X]`, whose instance leaves `B` to the sort.
#[test]
fn a_citation_reads_the_requirement_as_the_sort_states_it() {
    let ns = "test.cbrd2.call.c";
    let program = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(x: A) -> Int64
  end
  sort IntInt
    provides Conv[A = Int64, B = Int64]
    operation conv(x: Int64) -> Int64 = 1
  end
  sort IntBool
    provides Conv[A = Int64, B = Bool]
    operation conv(x: Int64) -> Int64 = 2
  end
  rule ckA[X](?x: X, ?r) :- Conv[A = X], Conv.conv(?x, ?r)
  sort Two2
    sort T = ?
    sort U = ?
    requires Conv[A = T, B = U]
    rule direct(?x: T, ?r) :- Conv.conv(?x, ?r)
    rule viaCall(?x: T, ?r) :- direct(?x, ?r)
    rule viaGuard(?x: T, ?r) :- ckA(?x, ?r)
  end
  rule cDirect(?r) :- Two2[T = Int64, U = Bool].direct(1, ?r)
  rule cViaCall(?r) :- Two2[T = Int64, U = Bool].viaCall(1, ?r)
  rule cViaGuard(?r) :- Two2[T = Int64, U = Bool].viaGuard(1, ?r)
  rule cAtInt(?r) :- Two2[T = Int64, U = Int64].viaCall(1, ?r)
end
"#
    );
    let mut kb = load_kb_with(&program);
    for (pattern, want) in [("cDirect(?r)", 2), ("cViaCall(?r)", 2), ("cViaGuard(?r)", 2), ("cAtInt(?r)", 1)] {
        assert_eq!(pattern_last_ints(&mut kb, &format!("{ns}.{pattern}")), vec![want], "`{pattern}`");
    }
}

/// A sort stating `Conv` twice with no name, `[A = T, B = Int64]` and `[A = T, B = Bool]`, holds
/// two dictionaries the goal of a rule guarding `Conv[A = X]` both fits: refused at the goal,
/// naming both, not handed the first. A goal of a clause calling `Conv.conv` is left undecided,
/// as the call itself is.
#[test]
fn two_requirements_the_goal_both_fits_are_refused() {
    let ns = "test.cbrd2.call.t";
    let program = |extra: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(x: A) -> Int64
  end
  sort IntInt
    provides Conv[A = Int64, B = Int64]
    operation conv(x: Int64) -> Int64 = 1
  end
  sort IntBool
    provides Conv[A = Int64, B = Bool]
    operation conv(x: Int64) -> Int64 = 2
  end
  rule ckA[X](?x: X, ?r) :- Conv[A = X], Conv.conv(?x, ?r)
  sort Both
    sort T = ?
    requires Conv[A = T, B = Int64]
    requires Conv[A = T, B = Bool]
    rule direct(?x: T, ?r) :- Conv.conv(?x, ?r)
    rule viaCall(?x: T, ?r) :- direct(?x, ?r)
{extra}
  end
  rule viaBoth(?r) :- Both[T = Int64].viaCall(1, ?r)
end
"#
        )
    };
    let errs = load_errors_of(&program("    rule viaGuard(?x: T, ?r) :- ckA(?x, ?r)"));
    assert!(
        errs.len() == 1
            && errs[0].contains("the sort states two the goal fits")
            && errs[0].contains("B = anthill.prelude.Int64")
            && errs[0].contains("B = anthill.prelude.Bool"),
        "{errs:?}"
    );
    let mut kb = load_kb_with(&program(""));
    assert_eq!(
        pattern_answer_counts(&mut kb, &format!("{ns}.viaBoth(?r)")),
        (0, 1),
        "`viaBoth(?r)`: undecided, not one of the two"
    );
}
