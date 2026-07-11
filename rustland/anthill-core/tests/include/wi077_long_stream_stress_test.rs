//! WI-077 — long-stream stress test for `execute_logical_query` /
//! `SearchStream` driven through the `StreamSource::Resolver` arena path.
//!
//! Prior Resolver coverage (eval_test.rs `m4_resolver_stream_*`) tops out at
//! 3 solutions, and the infinite-stream tests only exercise
//! `StreamSource::Native`. This file pushes the *resolver* path to N >= 1000
//! solutions and asserts:
//!   (a) all N solutions surface (exact count — no drops, no duplicates),
//!   (b) the stream arena slot is reclaimed once its handles drop
//!       (`stream_arena_live_count()` returns to 0),
//!   (c) memory does not blow up with N — each per-solution `Solution` value
//!       carries a `Value::Substitution` whose arena slot is freed as the
//!       value drops, so `subst_arena_live_count()` is flat (0) at the end
//!       rather than O(N).
//!
//! The second test reuses the same harness over an `MPlus` of two long
//! resolver branches, which is the coverage WI-075 (disjunction) needs:
//! concatenating two N-solution streams must surface all 2N and reclaim
//! every arena slot.
//!
//! Determinism: each `item` fact carries a literal `group` discriminator,
//! so a query that pins `group` to a concrete `Value::Int` matches exactly
//! the number of facts in that group. (WI-515: the synthetic per-entity
//! declaration fact this pin also used to exclude is no longer asserted.)

use anthill_core::eval::stream::StreamSource;
use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::resolve::SearchStream;
use anthill_core::kb::term::{Term, Var};
use crate::common::interp_for;

/// Number of facts per group. The ticket requires N >= 1000.
const N: i64 = 1000;

/// Build an interpreter whose KB holds `groups * N` facts of the form
/// `item(group: g, key: k)` for `g in 0..groups`, `k in 0..N`. The `group`
/// field is a literal discriminator (see the module comment).
fn item_interp(groups: i64) -> Interpreter {
    let mut src = String::from(
        r#"namespace test.wi077
  sort Item
    entity item(group: Int64, key: Int64)
  end
"#,
    );
    for g in 0..groups {
        for k in 0..N {
            src.push_str(&format!("  fact item(group: {g}, key: {k})\n"));
        }
    }
    src.push_str("end\n");
    interp_for(&src)
}

/// Build the reified query `pattern_query(item(group: <group>, key: ?k))`
/// and execute it, returning the resolver `SearchStream`. `group` is pinned
/// to a literal so only that group's N facts match.
fn group_query(interp: &mut Interpreter, group: i64) -> SearchStream {
    let kb = interp.kb_mut();
    let item_sym = kb
        .try_resolve_symbol("test.wi077.Item.item")
        .expect("item functor symbol");
    let pattern_query_sym = kb
        .try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
        .expect("pattern_query symbol");

    // Short-name field keys: the loader's reintern path stores named-arg
    // keys in a fact head under their short name, so the query pattern must
    // intern the same short Symbol to hash-cons equal (see m4 tests).
    let group_field = kb.intern("group");
    let key_field = kb.intern("key");
    let term_field = kb.intern("term");

    let k_name = kb.intern("k");
    let vk = kb.fresh_var(k_name);
    let var_k = kb.alloc(Term::Var(Var::Global(vk)));

    // item(group: <literal>, key: ?k)
    let pattern = Value::Entity {
        functor: item_sym,
        pos: Vec::new().into(),
        named: vec![
            (group_field, Value::Int(group)),
            (key_field, Value::term(var_k)),
        ]
        .into(),
    };
    let query = Value::Entity {
        functor: pattern_query_sym,
        pos: Vec::new().into(),
        named: vec![(term_field, pattern)].into(),
    };

    kb.execute_logical_query(&query).expect("execute lowered query")
}

#[test]
fn wi077_resolver_long_stream_surfaces_all_n_solutions() {
    let mut interp = item_interp(1);

    let search = group_query(&mut interp, 0);
    let handle = interp.alloc_stream(StreamSource::Resolver(Some(search)));
    assert_eq!(interp.stream_arena_live_count(), 1, "one resolver slot");
    assert_eq!(interp.subst_arena_live_count(), 0, "no substitutions yet");

    // Drive splitFirst to exhaustion. For a Resolver the continuation is the
    // same slot advanced in place, so pumping `&handle` repeatedly walks the
    // whole stream; `rest` is just a clone of `handle` and drops each turn.
    let mut count = 0i64;
    while let Some((v, _rest)) = interp.stream_split_first(&handle).expect("pump ok") {
        // WI-531: each resolver yield is now a `Solution` entity that CARRIES
        // its `Value::Substitution` (the `subst` field) into the per-interp
        // subst arena; dropping `v` at the end of this iteration frees that
        // slot, which is what keeps memory flat across N.
        let carries_subst = matches!(&v, Value::Entity { named, .. }
            if named.iter().any(|(_, fv)| matches!(fv, Value::Substitution(_))));
        assert!(carries_subst, "resolver yields a Solution carrying a Substitution, got {v:?}");
        count += 1;
    }

    // (a) all N solutions surface — exactly N.
    assert_eq!(count, N, "all N resolver solutions surface");

    // (c) no per-solution leak: every yielded substitution was freed as its
    // Value dropped, so the subst arena is back to empty — O(1), not O(N).
    assert_eq!(
        interp.subst_arena_live_count(),
        0,
        "substitution arena flat after draining N solutions"
    );

    // (b) the resolver slot is reclaimed once its only handle drops.
    assert_eq!(interp.stream_arena_live_count(), 1, "slot live until handle drops");
    drop(handle);
    assert_eq!(interp.stream_arena_live_count(), 0, "resolver slot reclaimed");
}

#[test]
fn wi077_mplus_over_long_branches_surfaces_all_solutions() {
    // WI-075 gate: the long-stream harness must also hold up when two long
    // resolver branches are concatenated via MPlus. Build two groups of N
    // facts each; MPlus{ Resolver(group 0), Resolver(group 1) } must surface
    // all 2N solutions (left fully before right) and reclaim every slot.
    let mut interp = item_interp(2);

    let left_search = group_query(&mut interp, 0);
    let left = interp.alloc_stream(StreamSource::Resolver(Some(left_search)));
    let right_search = group_query(&mut interp, 1);
    let right = interp.alloc_stream(StreamSource::Resolver(Some(right_search)));
    let mut stream = interp.alloc_stream(StreamSource::MPlus { left, right });
    assert_eq!(interp.stream_arena_live_count(), 3, "mplus + two branches");

    // MPlus hands back a *different* continuation handle when the left branch
    // exhausts (it collapses to the right child), so track `stream = rest`.
    let mut count = 0i64;
    loop {
        match interp.stream_split_first(&stream).expect("pump ok") {
            Some((_v, rest)) => {
                count += 1;
                stream = rest;
            }
            None => break,
        }
    }

    assert_eq!(count, 2 * N, "MPlus surfaces both long branches");
    assert_eq!(
        interp.subst_arena_live_count(),
        0,
        "substitution arena flat after draining MPlus"
    );

    // Dropping the final continuation cascades through the MPlus tree and
    // reclaims every slot (mplus + both branches).
    drop(stream);
    assert_eq!(interp.stream_arena_live_count(), 0, "all MPlus arena slots reclaimed");
}
