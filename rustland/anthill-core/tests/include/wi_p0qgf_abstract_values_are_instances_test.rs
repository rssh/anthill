//! WI-20261105-P0QGF — proposal 073 stage 3: A VALUE OF AN ABSTRACT TYPE IS AN INSTANCE OF ITS
//! SORT (073 §2, §3, §6.4; `docs/design/instance-values.md`).
//!
//! A value typed at a sort that receives on itself and has no constructors of its own
//! (`Stream`, `FiniteStream`, a user's `Mergeable`) is the pair of the dictionary of the sort that built it and that sort's value, made where the
//! value meets the abstract type. A call on it runs the member the pair's dictionary names, and
//! nothing at run time reads the value to choose an operation or a dictionary: the
//! interpreter's steps that did (the carrier override and the dispatch on the argument's sort)
//! are taken only under a caller with no types — a host entry, a rule body, a reflected form —
//! which are stage 4's (WI-20261105-CBRD2).
//!
//! THE CONTROL IS THE CENSUS, NOT THESE ROWS ALONE. Three rows FAIL on the tree before
//! (590f4272, measured with this file in a worktree there), each saying why at its site:
//! `a_defaulted_operation_at_a_known_type_passes_its_instance`,
//! `a_combinator_chain_over_a_relation` and `a_recursion_whose_instance_grows_at_each_turn`.
//! The other five answer the same there, by the value routes, and hold the answers with those
//! routes gone from typed code. That they are
//! gone is measured by a trace at each route over `wi_tests` (instance-values.md §6): no route
//! that reads a value is reached from a typed caller.

use anthill_core::eval::{Interpreter, Value};

use crate::common::{interp_for, one_definite_int, show_value};

fn int(interp: &mut Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{op}`: expected an Int64, got {other:?}"),
    }
}

fn shown(interp: &mut Interpreter, op: &str) -> String {
    match interp.call(op, &[]) {
        Ok(v) => show_value(interp.kb(), &v),
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

const PEOPLE: &str = r#"
namespace p0qgf.rel
  import anthill.prelude.{Int64, String, List, Error, Relation}
  import anthill.prelude.List.{length}
  sort People
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)
  fact person(name: "carol", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  const people: Relation[T = (name: String, age: Int64)] = person_row
  const rows: Relation[T = (name: String, age: Int64), E = {Error}] = person_row
  operation three() -> Int64 effects Error = length(people.takeN(3))
  operation olds() -> Int64 effects Error =
    length(rows.filter(lambda r -> r.age > 26).map(lambda r -> r.age).takeN(5))
end
"#;

/// 073's program: `Stream.takeN`'s default body calls `splitFirst(s)` on the `Relation`, then
/// on the `LogicalStream` its `splitFirst` returns as the rest, each the instance the previous
/// member built.
#[test]
fn three_rows_of_a_relation() {
    assert_eq!(int(&mut interp_for(PEOPLE), "p0qgf.rel.three"), 3);
}

/// A combinator chain over a `Relation`: each combinator answers an instance of the stream it
/// builds, and `takeN` runs on the last. FAILS on the tree before, where the run time chose
/// `FilteredStream.splitFirst` from the value and entered it with nothing in its frame:
/// "`__req_iterable` not bound in caller frame". The relation's row is written: with `E` left
/// open (`people`) the chain is refused at load on both trees, "undeclared effect: ?E", where
/// `takeN` alone loads — not this ticket's.
#[test]
fn a_combinator_chain_over_a_relation() {
    assert_eq!(int(&mut interp_for(PEOPLE), "p0qgf.rel.olds"), 2);
}

/// A data structure of instances holds one per element: `[xs, xs.map(twice)]` at
/// `List[T = Stream[…]]` runs `List`'s operations on the first element and the mapped
/// stream's on the second.
#[test]
fn a_list_of_streams_holds_one_instance_per_element() {
    let mut interp = interp_for(
        r#"
namespace p0qgf.two
  import anthill.prelude.{Int64, List, Stream}
  import anthill.prelude.Stream.{takeN}
  operation twice(x: Int64) -> Int64 = x * 2
  operation streams(xs: List[T = Int64]) -> List[T = Stream[T = Int64, E = {}]] =
    [xs, xs.map(twice)]
  operation firsts(ss: List[T = Stream[T = Int64, E = {}]]) -> List[T = List[T = Int64]] =
    ss.map(lambda s -> takeN(s, 1)).collect()
  operation go() -> List[T = List[T = Int64]] = firsts(streams([1, 2, 3]))
end
"#,
    );
    assert_eq!(shown(&mut interp, "p0qgf.two.go"), "[[1], [2]]");
}

/// `Map.iterator` answers the `List` it builds at `Stream[…]`, an instance of `List`.
#[test]
fn a_maps_iterator_is_an_instance_of_the_list_it_returns() {
    let mut interp = interp_for(
        r#"
namespace p0qgf.mi
  import anthill.prelude.{Int64, List, Stream, Map, String}
  import anthill.prelude.Stream.{takeN}
  import anthill.prelude.List.{length}
  operation m() -> Map[K = Int64, V = String] = Map.put(Map.put(Map.empty(), 1, "a"), 2, "b")
  operation go() -> Int64 = length(takeN(Map.iterator(m()), 5))
end
"#,
    );
    assert_eq!(int(&mut interp, "p0qgf.mi.go"), 2);
}

/// A recursion whose instance grows at each turn passes the instance the previous turn built:
/// a `MappedStream` over a `MappedStream` over a `List`. FAILS on the tree before: the run time
/// reached `Iterable.iterator` in a frame no caller had supplied, "the requirement it reads
/// pins no provider" (`UnpinnedRequirement`).
#[test]
fn a_recursion_whose_instance_grows_at_each_turn() {
    let mut interp = interp_for(
        r#"
namespace p0qgf.grow
  import anthill.prelude.{Int64, List, Stream}
  import anthill.prelude.Stream.{takeN}
  operation twice(x: Int64) -> Int64 = x * 2
  operation first(s: Stream[T = Int64, E = {}]) -> Int64 =
    match takeN(s, 1) case cons(h, _) -> h case _ -> 0
  operation deep(n: Int64, s: Stream[T = Int64, E = {}]) -> Int64 =
    if n > 0 then deep(n - 1, s.map(twice)) else first(s)
  operation go() -> Int64 = deep(3, [1, 2])
end
"#,
    );
    assert_eq!(int(&mut interp, "p0qgf.grow.go"), 8);
}

/// Two operands at the abstract type, over two carriers (073 §2): the receiver's instance
/// answers, and the other operand is passed as the instance it is — `Bag.merge` adds the
/// `Tally`'s size by `Tally`'s member, and the reverse.
#[test]
fn two_operands_at_the_abstract_type() {
    let mut interp = interp_for(
        r#"
namespace p0qgf.mrg
  import anthill.prelude.{Int64, List}
  sort Mergeable
    operation size(a: Self) -> Int64
    operation merge(a: Self, b: Self) -> Self
  end
  sort Bag
    entity bag(n: Int64)
    provides Mergeable
    operation size(a: Bag) -> Int64 = match a case bag(n) -> n
    operation merge(a: Bag, b: Mergeable) -> Bag = match a case bag(n) -> bag(n + Mergeable.size(b))
  end
  sort Tally
    entity tally(k: Int64)
    provides Mergeable
    operation size(a: Tally) -> Int64 = match a case tally(k) -> k * 100
    operation merge(a: Tally, b: Mergeable) -> Tally = match a case tally(n) -> tally(n + Mergeable.size(b))
  end
  operation two(x: Mergeable, y: Mergeable) -> Int64 = Mergeable.size(Mergeable.merge(x, y))
  operation ab() -> Int64 = two(bag(1), tally(2))
  operation ba() -> Int64 = two(tally(2), bag(1))
  operation ms() -> List[T = Mergeable] = [bag(1), tally(2)]
  operation viaList() -> List[T = Int64] =
    match ms() case cons(a, cons(b, nil)) -> [two(a, b), two(b, a)] case _ -> []
end
"#,
    );
    assert_eq!(int(&mut interp, "p0qgf.mrg.ab"), 201);
    assert_eq!(int(&mut interp, "p0qgf.mrg.ba"), 300);
    assert_eq!(shown(&mut interp, "p0qgf.mrg.viaList"), "[201, 300]");
}

/// A defaulted spec operation at a fully known type passes the instance the call selects to
/// its default body (073 §3): `Holder.size2(box(v: some(1)))` is a call at `Box[V =
/// Option[T = Int64]]`, `OptIntBoxH`'s, and the body's `size(c)` reads that instance. FAILS on
/// the tree before: the body's call was dispatched on the head `Box` and found two suppliers,
/// "ambiguous dispatch of `Holder.size`".
#[test]
fn a_defaulted_operation_at_a_known_type_passes_its_instance() {
    let mut interp = interp_for(
        r#"
namespace p0qgf.hold
  import anthill.prelude.{Int64, Option, String}
  import anthill.prelude.Option.{some, none}
  sort Holder
    sort C = ?
    operation size(c: C) -> Int64
    operation size2(c: C) -> Int64 = size(c)
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort OptIntBoxH
    provides Holder[C = Box[V = Option[T = Int64]]]
    operation size(c: Box[V = Option[T = Int64]]) -> Int64 = 42
  end
  sort OptStrBoxH
    provides Holder[C = Box[V = Option[T = String]]]
    operation size(c: Box[V = Option[T = String]]) -> Int64 = 7
  end
  operation go() -> Int64 = Holder.size2(box(v: some(1)))
  operation go1() -> Int64 = Holder.size(box(v: some(1)))
  operation goStr() -> Int64 = Holder.size2(box(v: some("s")))
end
"#,
    );
    assert_eq!(int(&mut interp, "p0qgf.hold.go"), 42);
    assert_eq!(int(&mut interp, "p0qgf.hold.go1"), 42);
    assert_eq!(int(&mut interp, "p0qgf.hold.goStr"), 7);
}

/// `collect` on a value typed `FiniteStream` runs the member of the instance `fs()` returns,
/// `List`'s, from an operation body and from a rule.
#[test]
fn collect_on_a_finite_stream_runs_its_instances_member() {
    let mut interp = interp_for(
        r#"
namespace p0qgf.vc
  import anthill.prelude.{List, Int64, FiniteStream, FiniteCollection}
  import anthill.prelude.FiniteCollection.{collect}
  operation fs() -> FiniteStream[T = Int64, E = {}] = [1, 2, 3]
  operation viaCollect() -> Int64 = List.length(collect(fs()))
  rule rv(?n) :- viaCollect(?n)
end
"#,
    );
    assert_eq!(int(&mut interp, "p0qgf.vc.viaCollect"), 3);
    assert_eq!(one_definite_int(interp.kb_mut(), "p0qgf.vc.rv"), Some(3));
}

/// A call at a goal no sort heads, all of it values, is refused at load where no provision
/// answers it: `Sized[N = 4].width()` beside the one provision at `N = 3`, naming the goal.
/// FAILS on the tree before, where it loaded and the call answered nothing. The twin at
/// `N = 3` answers 10.
#[test]
fn a_value_goal_no_provision_answers_is_refused_at_load() {
    const PROGRAM: &str = r#"
namespace p0qgf.sz
  import anthill.prelude.{Int64}
  sort Sized
    sort N = ?
    operation width() -> Int64
  end
  sort CS
    import p0qgf.sz.Sized
    provides Sized[N = 3]
    operation width() -> Int64 = 10
  end
  operation go() -> Int64 = Sized[N = AT].width()
end
"#;
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&PROGRAM.replace("AT", "4")),
        &["Sized.width.dispatch", "unresolved: p0qgf.sz.Sized[N = 4]"],
        "a value goal no provision answers",
    );
    assert_eq!(int(&mut interp_for(&PROGRAM.replace("AT", "3")), "p0qgf.sz.go"), 10);
}
