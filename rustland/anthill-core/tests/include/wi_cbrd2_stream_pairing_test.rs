//! A VALUE AT `Stream` IS PAIRED WHERE ITS SORT IS KNOWN, NOT FROM THE VALUE (WI-20261105-CBRD2;
//! the user, 2026-11-20, proposal 073 §1, §2). After the guards at a call
//! (`wi_cbrd2_guard_instance_at_call_test`), the gate's resolver bridge still paired 37 values
//! with a dictionary found from their own sort (`Interpreter::pair_by_own_sort`,
//! `resolve::value_pairings_by_this_thread`), in two shapes.
//!
//! **A result fed to the next call** (22, `wi_shed7_reads_wait_test`'s solver):
//!
//! ```anthill
//! rule second(vs: List[T = Int64], ?x, ?rest)
//!   :- Stream.splitFirst(vs)  <=> some(pair(fst: ?,  snd: ?r1)),
//!      Stream.splitFirst(?r1) <=> some(pair(fst: ?x, snd: ?rest))
//! ```
//!
//! typed `?r1` at the spec's result, `Stream`, whose values are instances, so nothing paired
//! the second call's argument at load; at run time `?r1` held the plain list `List.splitFirst`
//! returned. Decided with the user: a call at a receiver the clause types at a concrete carrier
//! is that carrier's member, and its result is the member's (§1; kernel-language §5.3, the
//! paragraph "A call whose arguments' types are known at load"): `?r1` is a `List[T = Int64]`
//! (`rule_constraints::narrow_pattern_at`, `carriers_member_result`), paired at load where the
//! next call takes it, and `?rest` is the list `[3]`, as it was. So is a variable a `<=>` binds
//! to the result (`?t <=> Stream.tail(d)` at a carrier whose own `tail` returns itself), and
//! what a variable that took the result is matched against (`?o <=> Stream.splitFirst(vs), ?o
//! <=> some(pair(fst: ?, snd: ?r1))`), in whatever order the steps are written. Not the goal
//! form, `Stream.splitFirst(vs, ?o)`: the call's check types its result column, and what that is
//! matched against, at the spec's declared return, so the next step's receiver is paired from
//! its value there, as before. Where the clause knows no
//! carrier, a receiver at `Stream` itself, the value is the instance the citation made, and so
//! is the result (§2): that already held, and [`a_receiver_at_the_abstract_sort_keeps_its_instance`]
//! pins it.
//!
//! **A spec's member that is a default of `Stream`** (13: `guard_chain`, `dqd5w`, `j9ssg`):
//! `Iterable.isEmpty(c: C)` at `C = List` is answered by `Stream.isEmpty(s: Self)`, which reads
//! its receiver as an instance. A body's call through the dictionary pairs the receiver with
//! it (`positions_to_pair`); the bridge's entry through the dictionary did not
//! (`Interpreter::call_op_bridged`), and the host entry paired it from the list. The bridge
//! pairs it as a body does now.
//!
//! The two left (`ycz0j`, `x5sb4`) were a guard goal `Iterable.isEmpty(nil)` the typer left
//! with no member, which the interpreter dispatched from the value; such a goal is read at its
//! member since (`wi_cbrd2_contract_member_goal_test`'s
//! `a_guard_naming_a_default_body_is_read_at_its_member`).
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every row
//! passes.
//!
//! * The carrier's member not read: [`a_result_is_typed_at_the_carrier`] fails, 1 pairing at
//!   `secondOf`; the answers stand. [`a_called_value_is_typed_at_the_carrier`] fails too, and on
//!   its answer: `?t` typed `Stream` holds the plain `down(n: 4)`, and the next step waits on a
//!   value at `Self` that is no instance — undecided, where it answers `3`.
//! * The narrowing read once, in the order the clause writes it: [`a_result_is_typed_at_the_carrier`]
//!   fails at `thirdRevOf`.
//! * A `<=>` with a variable not read at the carrier: [`a_called_value_is_typed_at_the_carrier`]
//!   fails, as with the member not read, and [`a_result_is_typed_at_the_carrier`] at
//!   `secondViaOf`.
//! * A variable's member result not handed to what it is matched against:
//!   [`a_result_is_typed_at_the_carrier`] fails at `secondViaOf`.
//! * The bridge's receiver not paired through the dictionary: [`a_default_member_takes_the_dictionarys_instance`]
//!   fails at its first query, 2 pairings (`wi_dqd5w_spec_op_relational_view_test`'s
//!   constraint rows paired 7 before the change).
//! * [`the_carriers_result_is_its_value`] and [`a_receiver_at_the_abstract_sort_keeps_its_instance`]
//!   pass either way: the first pins that B left the value a list, the second that A was
//!   already so.

use anthill_core::kb::resolve::value_pairings_by_this_thread;

use crate::common::{load_errors_of, load_kb_with, load_stdlib_kb, pattern_last_ints, query_unary};

/// `f`'s result and the pairings from a value's own sort during it, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = value_pairings_by_this_thread();
    let r = f();
    (r, value_pairings_by_this_thread() - before)
}

const SRC: &str = r#"
namespace test.cbrd2.sp
  import anthill.prelude.{Int64, List, Option, Pair, Stream}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  rule second(vs: List[T = Int64], ?x, ?rest)
    :- Stream.splitFirst(vs)  <=> some(pair(fst: ?,  snd: ?r1)),
       Stream.splitFirst(?r1) <=> some(pair(fst: ?x, snd: ?rest))
  rule third(vs: List[T = Int64], ?x)
    :- Stream.splitFirst(vs)  <=> some(pair(fst: ?,  snd: ?r1)),
       Stream.splitFirst(?r1) <=> some(pair(fst: ?,  snd: ?r2)),
       Stream.splitFirst(?r2) <=> some(pair(fst: ?x, snd: ?r3)),
       Stream.splitFirst(?r3) <=> none()
  -- the steps written the other way round
  rule thirdRev(vs: List[T = Int64], ?x)
    :- Stream.splitFirst(?r2) <=> some(pair(fst: ?x, snd: ?)),
       Stream.splitFirst(?r1) <=> some(pair(fst: ?,  snd: ?r2)),
       Stream.splitFirst(vs)  <=> some(pair(fst: ?,  snd: ?r1))
  -- the result bound to a variable, then matched
  rule secondVia(vs: List[T = Int64], ?x)
    :- ?o <=> Stream.splitFirst(vs), ?o <=> some(pair(fst: ?, snd: ?r1)),
       Stream.splitFirst(?r1) <=> some(pair(fst: ?x, snd: ?))
  rule secondOf(?x) :- second([1, 2, 3], ?x, ?)
  rule thirdRevOf(?x) :- thirdRev([1, 2, 3], ?x)
  rule secondViaOf(?x) :- secondVia([1, 2, 3], ?x)
  rule thirdOf(?x)  :- third([1, 2, 3], ?x)
  rule restIs(1)    :- second([1, 2, 3], ?, ?rest), ?rest <=> [3]
  -- the receiver at `Stream` itself: its carrier is whatever built the value
  rule secondAny(?s: Stream[T = Int64, E = {}], ?x)
    :- Stream.splitFirst(?s) <=> some(pair(fst: ?, snd: ?r)),
       Stream.splitFirst(?r) <=> some(pair(fst: ?x, snd: ?))
  rule tailAny(?s: Stream[T = Int64, E = {}], ?r)
    :- Stream.splitFirst(?s) <=> some(pair(fst: ?, snd: ?r))
  rule secondOfAny(?x) :- secondAny([1, 2, 3], ?x)
  rule tailOfAny(?r)   :- tailAny([1, 2, 3], ?r)
end
"#;

/// Each step's tail is a `List`, paired at load where the next step takes it: `secondOf`
/// answers `2`, `thirdOf` `3`, `thirdRevOf`, its steps written the other way round, `3`, and
/// `secondViaOf`, the result bound to `?o` and matched after, `2`, nothing found from a value.
#[test]
fn a_result_is_typed_at_the_carrier() {
    let mut kb = load_kb_with(SRC);
    for (query, want) in [
        ("test.cbrd2.sp.secondOf(?x)", 2),
        ("test.cbrd2.sp.thirdOf(?x)", 3),
        ("test.cbrd2.sp.thirdRevOf(?x)", 3),
        ("test.cbrd2.sp.secondViaOf(?x)", 2),
    ] {
        let (answers, pairings) = counting(|| pattern_last_ints(&mut kb, query));
        assert_eq!(answers, vec![want], "{query}");
        assert_eq!(pairings, 0, "{query}: a tail paired from the list it is");
    }
}

/// A carrier whose own `tail` is itself: `?t <=> Stream.tail(d)` at `d: Down` is a `Down`, as
/// the pattern of a `splitFirst` is (`afterTwoOf` answers `3`, nothing found from a value).
#[test]
fn a_called_value_is_typed_at_the_carrier() {
    let src = r#"
namespace test.cbrd2.spd
  import anthill.prelude.{Int64, Option, Pair, Stream, PartialEq, Numeric}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  sort Down
    entity down(n: Int64)
    provides Stream[T = Int64, E = {}]
    operation splitFirst(d: Self) -> Option[Pair[A = Int64, B = Down]] =
      match d
        case down(n) -> if PartialEq.eq(n, 0) then none else some(pair(fst: n, snd: down(n: Numeric.sub(n, 1))))
    operation tail(d: Self) -> Down = match d case down(n) -> down(n: Numeric.sub(n, 1))
  end
  rule afterTwo(d: Down, ?x)
    :- ?t <=> Stream.tail(d), ?u <=> Stream.tail(?t),
       Stream.splitFirst(?u) <=> some(pair(fst: ?x, snd: ?))
  rule afterTwoOf(?x) :- afterTwo(down(n: 5), ?x)
end
"#;
    let mut kb = load_kb_with(src);
    let (answers, pairings) = counting(|| pattern_last_ints(&mut kb, "test.cbrd2.spd.afterTwoOf(?x)"));
    assert_eq!(answers, vec![3]);
    assert_eq!(pairings, 0, "a `Down` paired from its own sort");
}

/// The tail is the list it is: `?rest <=> [3]` holds. Passes either way.
#[test]
fn the_carriers_result_is_its_value() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(pattern_last_ints(&mut kb, "test.cbrd2.sp.restIs(?x)"), vec![1]);
}

/// A receiver at `Stream` itself is the instance the citation made of `[1, 2, 3]`, and the tail
/// its member returns is an instance too: `secondOfAny` answers `2` with nothing found from a
/// value, and `tailOfAny`'s answer is `Instance(<List's Stream>, [2, 3])`. Passes either way.
#[test]
fn a_receiver_at_the_abstract_sort_keeps_its_instance() {
    let mut kb = load_kb_with(SRC);
    let (second, pairings) = counting(|| pattern_last_ints(&mut kb, "test.cbrd2.sp.secondOfAny(?x)"));
    assert_eq!(second, vec![2]);
    assert_eq!(pairings, 0, "a tail paired from the list it holds");
    let rows = query_unary(&mut kb, "test.cbrd2.sp.tailOfAny");
    let [(anthill_core::eval::Value::Entity { functor, pos, .. }, true)] = rows.as_slice() else {
        panic!("one definite answer, an entity: {rows:?}");
    };
    assert_eq!(kb.qualified_name_of(*functor), "anthill.realization.runtime.Instance");
    let held = anthill_core::kb::typing::type_display_name_value(&kb, &pos[1]);
    assert_eq!(held, "cons[head = 2, tail = cons[head = 3, tail = nil]]");
}

const ITER: &str = r#"
namespace test.cbrd2.spi
  import anthill.prelude.{Int64, Bool, String, List, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}
  import anthill.prelude.Iterable.{isEmpty, nonEmpty}
  rule emp[C](?ls: C, ?b) :- FiniteCollection[C = C], isEmpty(?ls, ?b)
  sort Box
    entity Box(items: List[T = String])
  end
  fact Box(items: ["a", "b"])
  fact Box(items: [])
  rule emptyLen(?n) :- Box(items: ?ls), emp(?ls, true), size(?ls, ?n)
  rule fullLen(?n)  :- Box(items: ?ls), emp(?ls, false), size(?ls, ?n)
end
"#;

/// `Iterable.isEmpty` at `List` runs `Stream.isEmpty`, whose receiver is the instance the
/// dictionary makes: through a guard's dictionary (`emp`), and in a constraint over a column
/// (`nonEmpty(?ls)`, holding over `["a"]` and violated by `[]`), nothing found from a value.
#[test]
fn a_default_member_takes_the_dictionarys_instance() {
    let mut kb = load_kb_with(ITER);
    for (query, want) in [("test.cbrd2.spi.emptyLen(?n)", vec![0]), ("test.cbrd2.spi.fullLen(?n)", vec![2])] {
        let (answers, pairings) = counting(|| pattern_last_ints(&mut kb, query));
        assert_eq!(answers, want, "{query}");
        assert_eq!(pairings, 0, "{query}: a list paired from its own sort");
    }
    let constraint = |facts: &str| {
        format!(
            "namespace test.cbrd2.spc\n  import anthill.prelude.{{String, List}}\n  import anthill.prelude.Iterable.{{nonEmpty}}\n  sort Box\n    entity Box(items: List[T = String])\n  end\n{facts}  constraint full: forall ?ls: Box(items: ?ls) -: nonEmpty(?ls)\nend\n"
        )
    };
    let (held, pairings) = counting(|| load_errors_of(&constraint("  fact Box(items: [\"a\"])\n")));
    assert_eq!(held, Vec::<String>::new());
    assert_eq!(pairings, 0, "the constraint's list paired from its own sort");
    let (violated, pairings) = counting(|| load_errors_of(&constraint("  fact Box(items: [])\n")));
    assert!(
        violated.iter().any(|e| e.contains("integrity constraint 'full' is violated")),
        "`[]` violates it: {violated:?}"
    );
    assert_eq!(pairings, 0, "the constraint's list paired from its own sort");
}
