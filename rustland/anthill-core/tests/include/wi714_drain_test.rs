//! WI-714 (proposal 052) — CONSUMPTION: a relation folds/collects as a stream.
//!
//! This is the WI-713 `query_id_set` pattern, which motivated 052: run a 1-arg
//! workflow predicate by NAME and accumulate the satisfying ids into a set. Today
//! (`anthill-todo/anthill/main.anthill:2719`) that is hand-rolled against the raw
//! reflect API — `fresh_var[Term]("id")` + `make_fn(<string>, …)` + `execute` +
//! `collect_id_set`, a hand-written `Stream[Solution]` walk that reads `?id` off a
//! raw `Substitution` BY STRING KEY via `extract_string_field`. Here the same set
//! falls out of naming the rule: the reference IS a `Relation[String]`, so the
//! solution materializes as a TYPED row and the walk is an ordinary stream drain.
//!
//! THE DRAIN IS BOUNDED, and that is the honest shape — not a concession:
//!
//! * A relation is MAYBE-INFINITE (a recursive rule enumerates unboundedly), so it
//!   provides `LogicalStream`/`Stream`, never `FiniteCollection`. The eager drains
//!   (`collect`/`size`/`foldLeft`/`foldRight`) live on `FiniteCollection` precisely
//!   because they walk to the end and so diverge on a maybe-infinite carrier
//!   (`stream.anthill:63-68`, WI-589 / proposal library/003 Phase C). Providing
//!   `collect` IS the finiteness guarantee (`finite_collection.anthill:27-29`), and
//!   a Relation cannot honor it — so `r.collect()` / `r.toList` DO NOT exist, by
//!   design rather than by omission. `Relation`'s provision closure is exactly
//!   {LogicalStream, Stream, Iterable}.
//! * `takeN` is the bounded drain: body-backed over `splitFirst` (so eval-reachable,
//!   unlike the rule-backed `head`/`headOption`), and it returns a `List` — which
//!   DOES provide `FiniteCollection` (`list.anthill:168`), so the fold is the
//!   ordinary one. Bound → List → fold: the finiteness enters where it is real.
//! * The bound is not new. WI-713's own walk is already capped (`collect_id_set(…,
//!   100000)`, `main.anthill:2725` — "a runaway guard; the predicate yields one
//!   solution per matching WorkItem, far fewer"). So this expresses the SAME
//!   semantics the consumer has today, with the boilerplate deleted.

use crate::common::interp_for;
use anthill_core::eval::Value;

const SRC: &str = r#"
namespace test.wi714drain
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool, Map}
  import anthill.prelude.Map.{empty, put, get, size}
  import anthill.prelude.List.{foldLeft, length}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)
  fact person(name: "carol", age: 30)

  -- One free head var → Relation[String] (1-collapse), the `dep_satisfied(?id)`
  -- shape exactly: a 1-arg predicate cited BY NAME.
  rule person_name(?name) :- person(name: ?name, age: ?)

  -- A repeated-id relation: clause 1 yields the two age-30 people (alice, carol),
  -- clause 2 yields all three — so every name recurs and the SET collapses them
  -- (put dedups) while the LIST keeps the bag multiplicity (OQ6).
  rule dup_name(?name) :- person(name: ?name, age: 30)
  rule dup_name(?name) :- person(name: ?name, age: ?)

  -- The accumulator step — `put(acc, id, true)`, exactly collect_id_set's body
  -- minus the Substitution/string-key read (the row IS already a typed String).
  operation add_name(acc: Map[String, Bool], n: String) -> Map[String, Bool] =
    put(acc, n, true)

  -- THE PATTERN: query_id_set, as a relation drain. Compare main.anthill:2719.
  operation nameSet() -> Map[String, Bool] effects Error =
    let r = person_name
    foldLeft(r.takeN(100000), empty(), add_name)

  operation nameSetSize() -> Int64 effects Error = size(nameSet())

  -- The set collapses duplicate ids (put dedups), as collect_id_set's Map.put does.
  operation dupNameSetSize() -> Int64 effects Error =
    let r = dup_name
    size(foldLeft(r.takeN(100000), empty(), add_name))

  -- ...while the bounded drain itself keeps the bag (OQ6): 2 + 3 = 5 rows, 3 distinct.
  operation dupNameCount() -> Int64 effects Error =
    let r = dup_name
    length(r.takeN(100000))

  -- Membership of the collected set — the `list` view's blocked/ready split reads
  -- exactly this way (`get(satisfied_set, id)`).
  operation aliceIsSatisfied() -> Option[Bool] effects Error =
    get(nameSet(), "alice")

  operation zedIsSatisfied() -> Option[Bool] effects Error =
    get(nameSet(), "zed")

  -- The drain COMPOSES with the algebra: fold the result of a `where` filter.
  operation filteredSetSize() -> Int64 effects Error =
    let r = person_row.where(lambda c -> eq(c.age, 30))
    let names = r.(name)
    size(foldLeft(names.takeN(100000), empty(), add_name))

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
end
"#;

/// The WI-713 `query_id_set` pattern, end-to-end: a 1-arg rule cited by name drains
/// as a stream and folds into a set. Three people → three names in the set.
#[test]
fn wi714_relation_folds_into_a_set() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714drain.nameSet", &[])
        .expect("nameSet() drains the relation and folds it into a Map set");
    assert!(
        matches!(r, Value::Map(_)),
        "nameSet() yields a Map value, got {r:?}"
    );
    // Read the set back through `size` rather than destructuring Map's internals.
    let n = interp
        .call("test.wi714drain.nameSetSize", &[])
        .expect("nameSetSize() runs");
    assert_eq!(
        n.as_int(),
        Some(3),
        "three people → the drained+folded set holds {{alice, bob, carol}}"
    );
}

/// `put` dedups: a relation yielding "alice" twice collapses to ONE set entry,
/// while the bounded drain itself keeps the bag multiplicity (OQ6).
#[test]
fn wi714_set_dedups_while_the_drain_keeps_the_bag() {
    let mut interp = interp_for(SRC);
    let rows = interp
        .call("test.wi714drain.dupNameCount", &[])
        .expect("dupNameCount() runs");
    assert_eq!(
        rows.as_int(),
        Some(5),
        "the drain is a BAG: clause 1 yields alice+carol (age 30), clause 2 yields all three"
    );
    let distinct = interp
        .call("test.wi714drain.dupNameSetSize", &[])
        .expect("dupNameSetSize() runs");
    assert_eq!(
        distinct.as_int(),
        Some(3),
        "...but `put` dedups: the SET holds only {{alice, bob, carol}}"
    );
}

/// The collected set answers membership — the shape `list`'s blocked/ready split
/// uses (`get(satisfied_set, id)`).
#[test]
fn wi714_collected_set_answers_membership() {
    let mut interp = interp_for(SRC);
    let hit = interp
        .call("test.wi714drain.aliceIsSatisfied", &[])
        .expect("aliceIsSatisfied() runs");
    let miss = interp
        .call("test.wi714drain.zedIsSatisfied", &[])
        .expect("zedIsSatisfied() runs");
    // `some(x)`'s payload rides positionally OR as the single named field,
    // depending on how the producer built it — `get` builds it named.
    let payload = match &hit {
        Value::Entity { pos, .. } if !pos.is_empty() => pos[0].clone(),
        Value::Entity { named, .. } if !named.is_empty() => named[0].1.clone(),
        other => panic!("alice IS in the collected set → some(true), got {other:?}"),
    };
    assert_eq!(
        payload.as_bool(),
        Some(true),
        "alice's entry in the collected set is `true`"
    );
    assert!(
        matches!(&miss, Value::Entity { pos, named, .. } if pos.is_empty() && named.is_empty()),
        "zed is NOT in the collected set → none, got {miss:?}"
    );
}

/// The drain COMPOSES with the relational algebra: `where` filters the query, the
/// distribute-dot projects a column, and the result still drains+folds as a stream.
/// This is the whole 052 shape in one line — compose the QUERY, materialize once.
#[test]
fn wi714_drain_composes_with_the_algebra() {
    let mut interp = interp_for(SRC);
    let n = interp
        .call("test.wi714drain.filteredSetSize", &[])
        .expect("filteredSetSize() runs the where+project pipeline and folds it");
    assert_eq!(
        n.as_int(),
        Some(2),
        "where(age=30).(name) drains+folds to the 2-name set {{alice, carol}}"
    );
}
