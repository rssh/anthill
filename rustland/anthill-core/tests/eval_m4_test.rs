//! Integration tests for the M4 `LogicalStream` + `splitFirst` milestone
//! (WI-048). Covers `eval::stream::{StreamArena, StreamSource}`, the
//! arena-refcounted `StreamHandle`, and the evaluator builtins
//! `anthill.prelude.LogicalStream.splitFirst` / `anthill.reflect.KB.execute`.
//!
//! Acceptance (per WI-048): an anthill program queries an ancestor
//! relation and drives the resulting stream through `splitFirst`. Yielded
//! substitutions are represented as `Value::Unit` placeholders for v1 — a
//! future milestone introduces an inspectable `Substitution` handle.

mod common;

use anthill_core::eval::Value;
use anthill_core::eval::stream::StreamSource;

use common::interp_for;

#[test]
fn m4_empty_stream_yields_none() {
    // StreamSource::Empty — immediate exhaustion. Drives the Rust-side
    // pump directly, confirming the arena + Empty arm.
    let mut interp = interp_for("namespace test.m4_empty end\n");
    let h = interp.alloc_stream(StreamSource::Empty);
    assert!(interp.stream_split_first(&h).unwrap().is_none());
}

#[test]
fn m4_pure_stream_yields_once_then_empty() {
    // StreamSource::Pure(v) — single-shot stream. First pump yields the
    // value; second pump yields none. Confirms in-place mutation of the
    // arena slot from Pure → Empty.
    let mut interp = interp_for("namespace test.m4_pure end\n");
    let payload = Value::Int(42);
    let h = interp.alloc_stream(StreamSource::Pure(Some(payload.clone())));
    let (v, rest) = interp.stream_split_first(&h).unwrap().expect("first pump yields");
    assert_eq!(v.as_int(), Some(42));
    assert!(interp.stream_split_first(&rest).unwrap().is_none(), "second pump yields none");
}

#[test]
fn m4_resolver_stream_iterates_ancestor_query() {
    // Acceptance test. Load a user KB with an `ancestor` relation, build
    // `pattern_query(ancestor(...))` from the Rust side, wrap the resulting
    // `SearchStream` as a `Value::Stream`, then drive it through
    // `splitFirst` from an anthill program.
    let source = r#"
namespace test.m4_ancestor
  import anthill.prelude.{LogicalStream}
  import anthill.prelude.LogicalStream.{splitFirst}
  import anthill.prelude.Pair.{pair}

  sort Person
    entity alice
    entity bob
    entity carol
  end

  sort Family
    entity ancestor(parent: Person, child: Person)
  end
  fact ancestor(parent: alice, child: bob)
  fact ancestor(parent: bob, child: carol)

  operation drain(s: LogicalStream) -> Int =
    match splitFirst(s)
      case some(pair(_, rest)) -> 1 + drain(rest)
      case none() -> 0
end
"#;
    let mut interp = interp_for(source);

    // Build the LogicalQuery from the Rust side. We query
    // `ancestor(parent: ?p, child: bob)` — expect one solution (p=alice).
    // Field names on an entity are scoped to the entity; resolve qualified
    // so the discrim tree sees the same Symbol the loader used.
    let kb = interp.kb_mut();
    let ancestor_sym = kb.try_resolve_symbol("test.m4_ancestor.Family.ancestor")
        .expect("ancestor symbol");
    let bob_sym = kb.try_resolve_symbol("test.m4_ancestor.Person.bob").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
        .expect("pattern_query");
    // The loader's `reintern` path (load.rs:1867) creates unqualified
    // short-name symbols for named-arg keys in a fact head, so the query
    // pattern must use the same short-name Symbol to hash-cons equal
    // to the stored fact. Using the qualified entity-field Symbol (from
    // scan_definitions) gives a *different* Symbol and the discrim tree
    // won't match.
    let parent_field = kb.intern("parent");
    let child_field = kb.intern("child");
    let term_field = kb.intern("term");
    let p_name = kb.intern("p");
    let vid = kb.fresh_var(p_name);
    use anthill_core::kb::term::{Term, Var};
    let var_p = kb.alloc(Term::Var(Var::Global(vid)));
    // Nullary constructors in fact position are stored as `Term::Ref`, not
    // `Term::Fn` with empty args — the loader resolves bare identifiers
    // to Refs when they're known symbols. Match that shape so the discrim
    // tree sees a structural match.
    let bob_term = kb.alloc(Term::Ref(bob_sym));

    // pattern_query( ancestor(parent: ?p, child: bob) )
    let ancestor_pattern = Value::Entity {
        functor: ancestor_sym,
        pos: Vec::new(),
        named: vec![
            (parent_field, Value::Term(var_p)),
            (child_field, Value::Term(bob_term)),
        ],
    };
    let query = Value::Entity {
        functor: pattern_query_sym,
        pos: Vec::new(),
        named: vec![(term_field, ancestor_pattern)],
    };

    // Lower + wrap as a Value::Stream on the Rust side (since we can't
    // construct a `KB` value from anthill code cleanly yet).
    let search = interp.kb_mut().execute_logical_query(&query).expect("execute lowered");
    let stream_handle = interp.alloc_stream(StreamSource::Resolver(Some(search)));
    let stream_val = Value::Stream(stream_handle);

    let count = interp.call("test.m4_ancestor.drain", &[stream_val])
        .expect("drain runs end-to-end");
    assert_eq!(count.as_int(), Some(1), "drain count for single-match query");
}

#[test]
fn m4_resolver_stream_iterates_multiple_solutions() {
    // Same as the single-solution test but the query has an unbound
    // `child`, so both facts match — we expect 2 yields before none.
    let source = r#"
namespace test.m4_multi
  import anthill.prelude.{LogicalStream}
  import anthill.prelude.LogicalStream.{splitFirst}
  import anthill.prelude.Pair.{pair}

  sort Person
    entity alice
    entity bob
    entity carol
  end

  sort Family
    entity ancestor(parent: Person, child: Person)
  end
  fact ancestor(parent: alice, child: bob)
  fact ancestor(parent: bob, child: carol)

  operation drain(s: LogicalStream) -> Int =
    match splitFirst(s)
      case some(pair(_, rest)) -> 1 + drain(rest)
      case none() -> 0
end
"#;
    let mut interp = interp_for(source);

    let kb = interp.kb_mut();
    let ancestor_sym = kb.try_resolve_symbol("test.m4_multi.Family.ancestor").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let parent_field = kb.intern("parent");
    let child_field = kb.intern("child");
    let term_field = kb.intern("term");
    let p = kb.intern("p");
    let c = kb.intern("c");
    let vp = kb.fresh_var(p);
    let vc = kb.fresh_var(c);
    use anthill_core::kb::term::{Term, Var};
    let var_p = kb.alloc(Term::Var(Var::Global(vp)));
    let var_c = kb.alloc(Term::Var(Var::Global(vc)));

    let ancestor_pattern = Value::Entity {
        functor: ancestor_sym,
        pos: Vec::new(),
        named: vec![
            (parent_field, Value::Term(var_p)),
            (child_field, Value::Term(var_c)),
        ],
    };
    let query = Value::Entity {
        functor: pattern_query_sym,
        pos: Vec::new(),
        named: vec![(term_field, ancestor_pattern)],
    };

    let search = interp.kb_mut().execute_logical_query(&query).expect("execute lowered");
    let stream_handle = interp.alloc_stream(StreamSource::Resolver(Some(search)));
    let stream_val = Value::Stream(stream_handle);

    let count = interp.call("test.m4_multi.drain", &[stream_val])
        .expect("drain runs");
    // A fully-unbound query matches both user facts plus the synthetic
    // per-entity "declaration fact" the loader asserts from
    // `entity ancestor(parent: Person, child: Person)` (load.rs:2950,
    // asserted with sort=Entity, functor=ancestor). We count structural
    // matches regardless of sort, hence 3 rather than 2. The single-
    // match test pins `child: bob` and avoids this by excluding the
    // declaration fact.
    assert_eq!(count.as_int(), Some(3), "drain count for fully-unbound query");
}

#[test]
fn m4_take_n_on_infinite_native_stream() {
    // Infinite producer (Native closure emits 1, 2, 3, …) paired with a
    // bounded consumer. Confirms:
    //   - splitFirst is pulled exactly N times (the closure's counter
    //     reports its final value),
    //   - takeN returns N on early termination,
    //   - the arena slot is reclaimed when the stream handle drops, even
    //     though the underlying producer could have kept emitting.
    let src = r#"
namespace test.m4_take
  import anthill.prelude.{LogicalStream}
  import anthill.prelude.LogicalStream.{splitFirst}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.Ordered.{gt}

  operation takeN(s: LogicalStream, n: Int) -> Int =
    if gt(n, 0) then
      match splitFirst(s)
        case some(pair(_, rest)) -> 1 + takeN(rest, n - 1)
        case none() -> 0
    else 0
end
"#;
    let mut interp = interp_for(src);

    // Counter captured by-move into the producer closure. Each pump bumps
    // the counter and yields it — unbounded source, no None return path.
    let pulls = std::rc::Rc::new(std::cell::Cell::new(0i64));
    let pulls_for_closure = pulls.clone();
    let producer = Box::new(move || {
        let n = pulls_for_closure.get() + 1;
        pulls_for_closure.set(n);
        Some(Value::Int(n))
    });
    let handle = interp.alloc_stream(StreamSource::Native(producer));
    assert_eq!(interp.stream_arena_live_count(), 1);

    let count = interp.call("test.m4_take.takeN", &[
        Value::Stream(handle),
        Value::Int(5),
    ]).expect("takeN runs");
    assert_eq!(count.as_int(), Some(5), "takeN returns 5");

    // Producer was pumped exactly 5 times — confirms laziness: we didn't
    // drain ahead of the consumer.
    assert_eq!(pulls.get(), 5, "producer was pulled once per solution");

    // The handle we passed into takeN was moved — takeN's locals dropped
    // on return. Arena slot must be reclaimed.
    assert_eq!(interp.stream_arena_live_count(), 0, "slot reclaimed after early termination");
}

#[test]
fn m4_mplus_finite_then_infinite() {
    // MPlus{finite, infinite}: the consumer first sees everything the
    // finite (left) side produces, then transitions to the infinite
    // (right) side. Pumping N > |finite| values confirms:
    //   - Ordering: left drains before right — left's element comes first.
    //   - Right is not pulled until left exhausts — infinite's counter
    //     shows only (N - |finite|) pulls.
    //   - After left exhausts, the continuation handle points at right
    //     directly (the MPlus wrapper is collapsed), so pulling more
    //     from that handle doesn't re-traverse the exhausted left.
    let mut interp = interp_for("namespace test.m4_mplus end\n");

    let left = interp.alloc_stream(StreamSource::Pure(Some(Value::Int(99))));

    let pulls = std::rc::Rc::new(std::cell::Cell::new(0i64));
    let pulls_for_closure = pulls.clone();
    let producer = Box::new(move || {
        let n = pulls_for_closure.get() + 1;
        pulls_for_closure.set(n);
        Some(Value::Int(n))
    });
    let right = interp.alloc_stream(StreamSource::Native(producer));

    let mut stream = interp.alloc_stream(StreamSource::MPlus { left, right });
    assert_eq!(interp.stream_arena_live_count(), 3);

    let mut values = Vec::new();
    for _ in 0..4 {
        let (v, rest) = interp.stream_split_first(&stream).unwrap().expect("more");
        values.push(v);
        stream = rest;
    }

    let ints: Vec<i64> = values.iter().filter_map(|v| v.as_int()).collect();
    assert_eq!(ints, vec![99, 1, 2, 3], "left drains before right, in order");
    assert_eq!(pulls.get(), 3, "infinite was pulled exactly (N - |finite|) times");

    drop(stream);
    assert_eq!(interp.stream_arena_live_count(), 0, "all arena slots reclaimed");
}

#[test]
fn m4_mplus_finite_then_empty() {
    // MPlus{finite, empty}: consumer sees the left side's elements and
    // then `none` — the right-empty arm must terminate cleanly rather
    // than looping forever or producing a spurious extra yield.
    let mut interp = interp_for("namespace test.m4_mplus_fe end\n");
    let left = interp.alloc_stream(StreamSource::Pure(Some(Value::Int(42))));
    let right = interp.alloc_stream(StreamSource::Empty);
    let stream = interp.alloc_stream(StreamSource::MPlus { left, right });

    let (v, rest) = interp.stream_split_first(&stream).unwrap().expect("first yields");
    assert_eq!(v.as_int(), Some(42));
    assert!(interp.stream_split_first(&rest).unwrap().is_none(), "then exhausted");

    drop(rest);
    drop(stream);
    assert_eq!(interp.stream_arena_live_count(), 0);
}

#[test]
fn m4_mplus_empty_then_finite() {
    // MPlus{empty, finite}: left yields none on the first pump, so the
    // resolver recurses into right immediately. The continuation handle
    // the caller gets back points at `right` directly — the MPlus
    // wrapper is effectively collapsed after left exhausts.
    let mut interp = interp_for("namespace test.m4_mplus_ef end\n");
    let left = interp.alloc_stream(StreamSource::Empty);
    let right = interp.alloc_stream(StreamSource::Pure(Some(Value::Int(7))));
    let stream = interp.alloc_stream(StreamSource::MPlus { left, right });

    let (v, rest) = interp.stream_split_first(&stream).unwrap().expect("first yields");
    assert_eq!(v.as_int(), Some(7), "right's element surfaces when left is empty");
    assert!(interp.stream_split_first(&rest).unwrap().is_none());

    drop(rest);
    drop(stream);
    assert_eq!(interp.stream_arena_live_count(), 0);
}

#[test]
fn m4_stream_handle_reclaimed_after_exhaustion() {
    // Pump a Pure stream to exhaustion, drop all handles — the arena slot
    // must be reclaimed. Confirms refcount + Drop cascade.
    let mut interp = interp_for("namespace test.m4_rc end\n");
    let h = interp.alloc_stream(StreamSource::Pure(Some(Value::Int(1))));
    assert_eq!(interp.stream_arena_live_count(), 1);
    let _ = interp.stream_split_first(&h).unwrap();
    let _ = interp.stream_split_first(&h).unwrap();
    drop(h);
    assert_eq!(interp.stream_arena_live_count(), 0, "slot reclaimed");
}
