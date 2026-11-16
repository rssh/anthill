//! WI-20261115-0WT09 — DEPTH IS NESTING, AND FUEL IS A SEPARATE COUNTER.
//!
//! `max_depth` bounded the number of steps taken on ONE branch: one counter per frame, every
//! step adding 1 to it, so the goals of a conjunction added up and a long finite computation
//! was cut as an infinite one is (WI-20261115-YR3N7: a typed column's check of a two-product,
//! two-order state needed 107, past the default 100, the sum of its parts). Decided with the
//! user (2026-11-15): "Depth is depth. If we need step-count (like fuel), then better have
//! other counter for this". A goal's depth is now its NESTING — a clause body is one deeper
//! than the goal the clause answers, every other goal keeps its own — and `max_steps` is the
//! fuel: the steps of the whole search, a negation's sub-search included.
//!
//! BACK-OUT, measured 2026-11-16 one part at a time over this file and
//! `wi_p9qbf_lazy_truncation_test` (17 rows, all green on the change; re-measured after
//! `/code-review`):
//!  * [D] depth counting steps again, EMULATED — every step bumps every goal of the top frame
//!    by one, which charges a clause resolution about twice what the old frame counter did —
//!    6 fail: `siblings_do_not_add_their_depths` and `a_typed_columns_check_is_as_deep_as_its_
//!    value` (the sum of two conjuncts decides the depth, not the deeper one), the two fuel rows
//!    (the counted steps pass the depth limit before the fuel runs out), and two rows whose
//!    fixtures are sized by depth: `an_infinite_descent_is_still_cut_by_depth`'s count — one
//!    answer per level is the nesting reading — and p9qbf's `split_first_reports_the_cut_at_
//!    its_end` at depth 7;
//!  * [F] the fuel check in `SearchStream::step` removed — 3 fail: `a_shallow_exponential_
//!    search_is_cut_by_fuel` (the doubling search finds its proof), `a_negations_steps_are_
//!    the_searchs_fuel` and `a_negation_out_of_fuel_keeps_its_fault` (the sub-search finishes);
//!  * [C] a negation's sub-search on fuel of its own, not charged back — 2 fail:
//!    `a_negations_steps_are_the_searchs_fuel` (the outer search ends with fuel to spare) and
//!    `a_negation_out_of_fuel_keeps_its_fault` (the sub-search finishes on its own fuel);
//!  * [E] the stop on the sub-search's fuel BEFORE its faults are folded in (the first cut,
//!    found by `/code-review`) — 1 fails: `a_negation_out_of_fuel_keeps_its_fault`.
//! CONTROL for all four: `the_payload_names_the_limit` (it reads the raise, not the search);
//! `an_infinite_descent_is_still_cut_by_depth` passes under [F], [C] and [E].

use crate::common::{interp_for, load_kb_with, query_pattern_term, supply_invocation_imports};
use anthill_core::eval::{EvalError, Value};
use anthill_core::kb::resolve::{ResolveConfig, SearchFailure, SearchLimit};
use anthill_core::kb::KnowledgeBase;

const SRC: &str = r#"
namespace wi0wt09
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{cons}
  import anthill.kernel.{not}

  enum OrderStatus
    entity CREATED
    entity PAID
  end
  entity Product(id: Int64, price: Int64)
  entity Order(id: Int64, status: OrderStatus, total: Int64)
  entity S(products: List[T = Product], orders: List[T = Order])
  rule only_s(?s: S) :- true

  fact walk(z)
  rule walk(s(p: ?t)) :- walk(?t)
  rule both(?a, ?b) :- walk(?a), walk(?b)

  sort N
    entity z
    entity s(p: N)
  end
  rule loopy :- loopy
  rule notLoopy :- not(loopy)
  fact nat(z)
  rule nat(s(p: ?x)) :- nat(?x)
  fact tree(z)
  rule tree(s(p: ?n)) :- tree(?n), tree(?n)
  rule notTree(?n) :- not(tree(?n))

  operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k
  rule faulty(?r) :- guardExhaustible(0, ?r)
  rule faulty(?r) :- tree(s(p: s(p: s(p: s(p: s(p: s(p: s(p: s(p: s(p: s(p: s(p: s(p: s(p: s(p: s(p: s(p: z))))))))))))))))), ?r <=> 1
  rule notFaulty :- not(faulty(1))
end
"#;

fn kb() -> KnowledgeBase {
    let mut kb = load_kb_with(SRC);
    supply_invocation_imports(&mut kb, &["wi0wt09.*"]);
    kb
}

/// `s(p: s(p: … z))`, `n` deep.
fn nat(n: usize) -> String {
    (0..n).fold("z".to_string(), |inner, _| format!("s(p: {inner})"))
}

/// Does `pattern` hold DEFINITELY at `config`?
fn holds(kb: &mut KnowledgeBase, pattern: &str, config: &ResolveConfig) -> bool {
    let goal = query_pattern_term(kb, pattern);
    let (solutions, _) = kb.resolve_with_stats(&[goal], config);
    solutions.iter().any(|s| s.is_definite())
}

/// The smallest `max_depth` at which `pattern` holds definitely — the depth its proof needs.
fn depth_needed(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    (0..=400)
        .find(|&d| {
            holds(
                kb,
                pattern,
                &ResolveConfig {
                    max_depth: d,
                    ..ResolveConfig::default()
                },
            )
        })
        .unwrap_or_else(|| panic!("`{pattern}` does not hold at any depth up to 400"))
}

/// TWO CONJUNCTS ARE AS DEEP AS THE DEEPER ONE. `both(a, b)` walks `a`, then `b`: the second
/// walk's goals sit beside the first's finished proof, not below it, so walking an
/// eight-step chain twice needs the depth of walking it once — and `walk(s^8(z))` itself
/// needs one level per step.
///
/// OVER `N`, NOT A LIST: `walk`'s column at a `List` is `List[T = ?t]`, which the typer gives
/// `both` as a checked bound, and the check of an `Int64` element sits one level below the
/// deepest cell — the first cut of this row measured 10 for `both(l8, [])`, not 9. `N` has
/// no parameter, so `both`'s columns carry no check and the row is about the conjunction.
///
/// FAILS UNDER [D]: with the frame counting every step, `both(s^8(z), s^8(z))` needs the two
/// walks' steps added (about twice `both(s^8(z), z)`'s).
#[test]
fn siblings_do_not_add_their_depths() {
    let mut kb = kb();
    let n8 = nat(8);
    let one = depth_needed(&mut kb, &format!("walk({n8})"));
    let alone = depth_needed(&mut kb, &format!("both({n8}, z)"));
    let twice = depth_needed(&mut kb, &format!("both({n8}, {n8})"));
    assert_eq!(one, 8, "one level per step: `walk(z)` is asked 8 deep");
    assert_eq!(alone, one + 1, "`both`'s clause is one level above the walks");
    assert_eq!(
        twice, alone,
        "the second walk adds nothing to the depth: {alone} for one chain, {twice} for two"
    );
}

/// A TYPED COLUMN'S CHECK IS AS DEEP AS ITS VALUE, not as long as it — the case that found
/// this (WI-20261115-YR3N7). `S`'s two lists are siblings, so eight orders beside eight
/// products need no more depth than eight products alone; and a longer list nests one level
/// per cell, where its steps — the check's per-element work — went into the depth before
/// and go into the fuel now.
///
/// FAILS UNDER [D]: eight orders beside eight products add their whole check's steps, and
/// each further product adds its check's steps, not one level.
#[test]
fn a_typed_columns_check_is_as_deep_as_its_value() {
    let mut kb = kb();
    let products = |n: usize| -> String {
        let items: Vec<String> = (1..=n).map(|i| format!("Product({i}, 10)")).collect();
        format!("[{}]", items.join(", "))
    };
    let orders = |n: usize| -> String {
        let items: Vec<String> = (1..=n).map(|i| format!("Order({i}, PAID, 5)")).collect();
        format!("[{}]", items.join(", "))
    };
    let state = |p: usize, o: usize| format!("only_s(S(products: {}, orders: {}))", products(p), orders(o));
    let p8 = depth_needed(&mut kb, &state(8, 0));
    let p8o8 = depth_needed(&mut kb, &state(8, 8));
    let p4 = depth_needed(&mut kb, &state(4, 0));
    assert_eq!(p8o8, p8, "eight orders beside eight products add no depth: {p8} alone, {p8o8} with them");
    assert!(
        p8 - p4 <= 4,
        "four more products nest four more cells, at most a level each: {p4} for four, {p8} for eight"
    );
    assert!(
        p8 <= ResolveConfig::default().max_depth,
        "the state YR3N7 could not check at the default depth now fits it: needs {p8}"
    );
}

/// AN INFINITE DESCENT IS STILL CUT BY DEPTH, truncated and never refuted: depth alone bounds
/// every chain of clause openings, so a left recursion and an unbounded enumeration stop at
/// `max_depth` with no fuel spent past it.
///
/// CONTROL under [F] and [C] — the depth is what cuts these. Under [D]'s emulation the
/// enumeration's count fails: one answer per level is the nesting reading (see the header).
#[test]
fn an_infinite_descent_is_still_cut_by_depth() {
    let mut kb = kb();
    let config = ResolveConfig::default();
    let goal = query_pattern_term(&mut kb, "loopy");
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(solutions.is_empty(), "`loopy` has no proof");
    assert!(stats.truncated && !stats.out_of_fuel, "cut by depth, not by fuel: {stats:?}");
    assert!(stats.steps < 10_000, "a depth-cut descent is cheap: {} steps", stats.steps);

    let goal = query_pattern_term(&mut kb, "notLoopy");
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(
        solutions.iter().all(|s| !s.is_definite()) && stats.truncated,
        "`not(loopy)` is undecided over a cut search, never a refutation of `loopy`"
    );

    let goal = query_pattern_term(&mut kb, "nat(?y)");
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(stats.truncated && !stats.out_of_fuel, "the enumeration is cut by depth: {stats:?}");
    assert_eq!(
        solutions.len(),
        config.max_depth + 1,
        "one answer per level, `z` through `s^{}(z)`",
        config.max_depth
    );
}

/// A SHALLOW EXPONENTIAL SEARCH IS CUT BY FUEL. `tree(s(n))` calls `tree(n)` twice, so its
/// proof is 17 levels deep for `s^16(z)` and takes some hundred thousand steps: no depth
/// limit stops it, and the step-counting depth used to cut it at 100. The fuel does, and the
/// end names it: `SearchLimit::Steps`. With fuel to spare the same rule proves `s^5(z)`.
///
/// FAILS UNDER [F]: the search runs to its end (a definite proof), out of no fuel. Under [D]
/// as well: the counted steps pass the depth limit before the fuel runs out (measured on
/// scaland's twin row).
#[test]
fn a_shallow_exponential_search_is_cut_by_fuel() {
    let mut kb = kb();
    let config = ResolveConfig {
        max_steps: 10_000,
        ..ResolveConfig::default()
    };
    assert!(holds(&mut kb, &format!("tree({})", nat(5)), &config), "`s^5(z)` fits the fuel");

    let pattern = format!("tree({})", nat(16));
    let goal = query_pattern_term(&mut kb, &pattern);
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(solutions.is_empty(), "no proof is found within 10 000 steps");
    assert!(stats.truncated && stats.out_of_fuel, "cut by fuel: {stats:?}");
    assert!(stats.steps <= 10_000, "the fuel is the limit: {} steps", stats.steps);

    let goal = query_pattern_term(&mut kb, &pattern);
    let stream = kb.resolve_lazy(&[goal], &config);
    match stream.split_first(&mut kb) {
        Err(SearchFailure::Truncated {
            limit: SearchLimit::Steps { max_steps: 10_000 },
        }) => {}
        Err(other) => panic!("the lazy end names the fuel, got {other}"),
        Ok(other) => panic!(
            "the lazy end names the fuel, got {}",
            if other.is_some() { "an answer" } else { "a complete end" }
        ),
    }
}

/// A NEGATION'S STEPS ARE THE SEARCH'S FUEL. `not(tree(s^16(z)))` sub-resolves `tree(…)` on
/// what is left of the outer search's fuel, and its steps are charged back: the outer search
/// runs out with it, and `not(…)` is not decided by a sub-search cut short.
///
/// FAILS UNDER [C]: the sub-search runs on fuel of its own and is not charged back, so the
/// outer search ends in a handful of steps with fuel to spare. Under [F] and [D] too: no fuel
/// runs out at all, or the counted steps cut the sub-search at its depth first.
#[test]
fn a_negations_steps_are_the_searchs_fuel() {
    let mut kb = kb();
    let config = ResolveConfig {
        max_steps: 10_000,
        ..ResolveConfig::default()
    };
    let goal = query_pattern_term(&mut kb, &format!("notTree({})", nat(16)));
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(
        solutions.iter().all(|s| !s.is_definite()),
        "a negation over a search cut by fuel is not decided"
    );
    assert!(stats.out_of_fuel, "the outer search ran out with its negation: {stats:?}");
}

/// A NEGATION OUT OF FUEL KEEPS ITS SUB-SEARCH'S FAULT. `not(faulty(1))`: `faulty`'s first
/// clause raises in a bridged call — a fault (WI-20260911-0V0F7) — and its second runs the
/// doubling `tree(s^16(z))`, some hundred thousand steps, out of the fuel. (A recursion with
/// no base case is no such fixture: its first conjunct is cut at the depth limit and the whole
/// chain fails back in a few hundred steps — the first cut of this row, which then passed
/// without the fuel ever running out.) The outer search stops with it, and its end is the
/// FAULT, which outranks the truncation: the sub-search's faults are folded in before the stop
/// (`/code-review` found the stop first, and the fault lost).
///
/// FAILS with the stop before the fold — [E]: the end is `Truncated { Steps }`, the fault
/// gone. Under [F] and [C] too: with fuel to spare the sub-search finds `tree`'s proof and
/// `not(…)` fails definitely. CONTROL under [D]: the counted steps cut the sub-search at its
/// depth first, and its fault is promoted as an undecided one's.
#[test]
fn a_negation_out_of_fuel_keeps_its_fault() {
    let mut kb = kb();
    let config = ResolveConfig {
        max_steps: 10_000,
        ..ResolveConfig::default()
    };
    let goal = query_pattern_term(&mut kb, "notFaulty");
    let stream = kb.resolve_lazy(&[goal], &config);
    match stream.split_first(&mut kb) {
        Err(SearchFailure::Faulted(_)) => {}
        Err(other) => panic!("the fault outranks the truncation, got: {other}"),
        Ok(other) => panic!(
            "`not(faulty(1))` is not decided; got {}",
            if other.is_some() { "an answer" } else { "a complete end" }
        ),
    }
}

/// THE PAYLOAD NAMES THE LIMIT: `search_truncated(limit: depth(max_depth: d))` and
/// `search_truncated(limit: steps(max_steps: n))`, the program-facing twin of
/// `SearchLimit`. A program matches the nested limit — `wi_p9qbf_lazy_truncation_test`'s
/// `caughtDepth` catches `search_truncated(depth(d))` from a cut relation.
///
/// CONTROL for [D], [F] and [C] — it reads the raise, not the search.
#[test]
fn the_payload_names_the_limit() {
    let mut interp = interp_for(SRC);
    for (limit, ctor, field, n) in [
        (SearchLimit::Depth { max_depth: 7 }, "anthill.reflect.SearchLimit.depth", "max_depth", 7),
        (SearchLimit::Steps { max_steps: 9 }, "anthill.reflect.SearchLimit.steps", "max_steps", 9),
    ] {
        let raised = interp.raise_search_truncated(limit);
        let EvalError::Raised { payload, .. } = raised else {
            panic!("`search_truncated` is raised as an `Error`, got {raised:?}")
        };
        let Value::Entity { functor, named, .. } = &payload else {
            panic!("the payload is an entity, got {payload:?}")
        };
        assert_eq!(
            interp.kb().qualified_name_of(*functor),
            "anthill.reflect.ResolveStreamFailure.search_truncated"
        );
        let limit_value = named
            .iter()
            .find(|(k, _)| interp.kb().local_name_of(*k) == "limit")
            .map(|(_, v)| v.clone())
            .expect("a `limit` field");
        let Value::Entity { functor, named, .. } = &limit_value else {
            panic!("`limit` is a SearchLimit entity, got {limit_value:?}")
        };
        assert_eq!(interp.kb().qualified_name_of(*functor), ctor);
        let held = named
            .iter()
            .find(|(k, _)| interp.kb().local_name_of(*k) == field)
            .map(|(_, v)| v.clone());
        assert!(matches!(held, Some(Value::Int(m)) if m == n), "`{field}` is {n}, got {held:?}");
    }
}
