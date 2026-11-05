//! WI-20261013-DEY66 — proposal 068 §8 step 3: the per-consumer reductions retire. A call a
//! rule evaluates is run by the interpreter and nothing else; the narrowing reads a `match`
//! on a tuple of the arguments; and a dot written in a query pattern is dispatched as the
//! same text is in a clause (068 §6).
//!
//! * `reduce_op_value`'s call-by-name fold is gone: it inlined a bodied operation's body
//!   over the call's arguments and reduced the result structurally, one level per nested
//!   call, bridging a nested call that reads requirement slots on its own with the folded
//!   arguments as values. An operation body's `[1, 2]` reached that bridge as the node
//!   eval presents as `ListLiteral(1, 2)`, which no arm of a `match` takes
//!   (WI-20261102-989Z0). Every call now runs whole in the interpreter.
//! * The fold had covered for the interpreter: a dispatched call landing on a member of a
//!   THIRD sort — neither the spec nor the provider — whose sort `requires` something was
//!   handed the provider's dictionary, which carries nothing for that sort, and died
//!   `Internal` (WI-20261102-6GAS1). The typer now gives such a call the dictionary the
//!   direct call of the member builds (`typing::build::third_sort_member_dict`).
//! * `body_specialize::reduce` stays the narrowing's one step (decided with the user: the
//!   narrowing needs each arm's residual as code, which a strict run does not return). It
//!   reads a `match` on a tuple component by component (`split_tuple_scrutinee`), and a
//!   tuple pattern against the `TupleLiteral` node an operation body stores, which it read
//!   as a definite non-match — the prover was handed `pick(x, y) = 20` for
//!   `match (x, y) case (0, _) -> 10 case _ -> 20`.
//! * A query's dot is typed where the pattern is converted, by the typer's own dot
//!   dispatch, and a dot on a query variable is refused (decided with the user: a dot is
//!   decided by its receiver's type, never by a value). Every such dot was the data
//!   `dot_apply(…)`, bound as a definite answer.
//!
//! ## Back-out
//!
//! MEASURED, each part backed out on its own (temporary switches, one build), against this
//! module:
//!   * the whole change (HEAD `fd640523`, a worktree) — every row but the CONTROLS;
//!   * the 6GAS1 typer arm (`third_sort_member_dict` answering `None`) — the three
//!     `a_dispatch_to_a_third_sorts_member_*` rows (an `Internal` evaluator error);
//!   * the tuple split (`split_tuple_scrutinee` answering `None`) — the three
//!     `a_match_on_a_tuple_*` / `an_arm_*` / `a_recursive_*` rows;
//!   * the tuple pattern's reading of the stored tuple (the `TupleLiteral` constructor read
//!     as a non-tuple again) — `a_tuple_pattern_reads_the_operation_bodys_tuple`;
//!   * the query dot (`query_dot_expression` answering `None`) — the four query-dot rows;
//!   * the variable check reading only the outermost dot (`dot_on_a_query_variable`) —
//!     `a_dot_on_a_query_variable_is_refused` (its nested spellings get the typer's
//!     unresolved-receiver text instead).
//!
//! The CONTROL rows pass either way, by design, and each says why at its site.

use anthill_core::eval;
use anthill_core::kb::load::QueryPattern;
use anthill_core::kb::op_info::all_operation_params;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// `(solutions, definite solutions, fault messages, truncated)` of the query `pattern`.
fn ask(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize, Vec<String>, bool) {
    let goal: QueryPattern = crate::common::query_pattern_term(kb, pattern);
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let definite = sols.iter().filter(|s| s.is_definite()).count();
    let faults = stats.errors.iter().map(|e| e.message.clone()).collect();
    (sols.len(), definite, faults, stats.truncated)
}

/// The query `pattern` holds once, definitely, with nothing faulted or cut.
fn holds(kb: &mut KnowledgeBase, pattern: &str) -> bool {
    ask(kb, pattern) == (1, 1, Vec::new(), false)
}

/// The query `pattern` has no answer, and the search is complete.
fn refuted(kb: &mut KnowledgeBase, pattern: &str) -> bool {
    ask(kb, pattern) == (0, 0, Vec::new(), false)
}

// ── 989Z0: the interpreter runs a call whole ──────────────────────────────────────────────

const CALLS: &str = r#"
namespace test.dey66.calls
  import anthill.prelude.{Int64, List, Option}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Option.{some, none}

  sort Pc
    sort C = ?
    sort Element = ?
    operation emp() -> C
    operation ins(c: C, elem: Element) -> C
    operation len(xs: List[T = Element]) -> Int64 = match xs
      case nil() -> 0
      case cons(x, rest) -> 1
    operation tlen(p: (Element, Element)) -> Int64 = match p
      case (a, b) -> 2
    operation olen(o: Option[T = List[T = Element]]) -> Int64 = match o
      case some(cons(x, rest)) -> 1
      case some(nil) -> 0
      case none -> 5
  end

  sort Bx
    entity bnil
    entity badd(e: Int64, rest: Bx)
    provides Pc[C = Bx, Element = Int64]
    operation emp() -> Bx = bnil()
    operation ins(c: Bx, elem: Int64) -> Bx = badd(e: elem, rest: c)
  end

  operation q() -> Int64 = Pc[C = Bx].len([1, 2, 3])
  operation qt() -> Int64 = Pc[C = Bx].tlen((1, 2))
  operation qo() -> Int64 = Pc[C = Bx].olen(some([1, 2]))
  rule r(?x) :- ?x <=> q()
  rule rt(?x) :- ?x <=> qt()
  rule ro(?x) :- ?x <=> qo()
end
"#;

/// WI-20261102-989Z0's row: `q`'s body passes a list literal to a default body that reads
/// its sort's slots (`Pc.len`'s parameter names `Element`). Before: `?x = 1`, beside the
/// warning that `Pc.len` raised `match_failed` on `ListLiteral(1, 2, 3)` and an INCOMPLETE
/// search — the fold bridged the inner call with `q`'s literal unevaluated.
#[test]
fn a_call_reached_through_an_operation_body_runs_whole() {
    let mut kb = crate::common::load_kb_with(CALLS);
    assert!(holds(&mut kb, "test.dey66.calls.r(1)"));
    assert!(refuted(&mut kb, "test.dey66.calls.r(0)"));
}

/// The literal nested in a constructor, `some([1, 2])`: the same fault before.
#[test]
fn a_literal_nested_in_a_constructor_runs_whole() {
    let mut kb = crate::common::load_kb_with(CALLS);
    assert!(holds(&mut kb, "test.dey66.calls.ro(1)"));
    assert!(refuted(&mut kb, "test.dey66.calls.ro(5)"));
}

/// CONTROL: a tuple literal answered 2 before as well — a tuple pattern takes eval's tuple.
#[test]
fn control_a_tuple_literal_ran_before_too() {
    let mut kb = crate::common::load_kb_with(CALLS);
    assert!(holds(&mut kb, "test.dey66.calls.rt(2)"));
}

// ── 6GAS1: a dispatch to a member of a third sort ────────────────────────────────────────

const THIRD: &str = r#"
namespace test.dey66.third
  import anthill.prelude.{Int64, List}
  import anthill.prelude.List.{cons, nil}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
    operation describeAll(x: T, xs: List[T = Int64]) -> Int64
  end

  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end

  sort Leaf
    entity leaf
    provides Tag[G = Leaf]
    operation tagval(x: Leaf) -> Int64 = 7
  end

  sort LeafDesc
    sort L = ?
    requires Tag[G = L]
    operation describeLeaf(x: L) -> Int64 = Tag.tagval(x)
    operation describeLeafAll(x: L, xs: List[T = Int64]) -> Int64 = match xs
      case nil -> Tag.tagval(x)
      case cons(h, r) -> Tag.tagval(x) + h
  end

  namespace Leaf
    provides Desc[T = Leaf, describe = LeafDesc.describeLeaf, describeAll = LeafDesc.describeLeafAll]
  end

  operation one() -> List[T = Int64] = [1, 2]
  operation probe() -> Int64 = Desc.describe(leaf())
  operation probeAll() -> Int64 = Desc.describeAll(leaf(), [1, 2])
  operation probeOne() -> Int64 = Desc.describeAll(leaf(), one())
  operation direct() -> Int64 = LeafDesc.describeLeaf(leaf())
  rule answer(?r) :- probe(?r)
  rule answerAll(?r) :- probeAll(?r)
  rule answerOne(?r) :- probeOne(?r)
end
"#;

fn call(entry: &str) -> Result<eval::Value, eval::EvalError> {
    let mut interp = crate::common::interp_for(THIRD);
    interp.call(&format!("test.dey66.third.{entry}"), &[])
}

/// WI-20261102-6GAS1's row: `Desc.describe(leaf())` dispatches to `LeafDesc.describeLeaf`,
/// whose sort requires `Tag[G = L]`. Before: `Internal("deferred dispatch frame-push: …
/// whose parent `LeafDesc` is neither the spec nor the provider of the dictionary …")`.
#[test]
fn a_dispatch_to_a_third_sorts_member_runs_in_the_interpreter() {
    assert!(matches!(call("probe"), Ok(eval::Value::Int(7))), "{:?}", call("probe"));
}

/// The same with a list argument the member matches on, written in place and through an
/// operation. Before: the same `Internal` error; from a rule, a panic.
#[test]
fn a_dispatch_to_a_third_sorts_member_with_a_list_argument() {
    assert!(matches!(call("probeAll"), Ok(eval::Value::Int(8))), "{:?}", call("probeAll"));
    assert!(matches!(call("probeOne"), Ok(eval::Value::Int(8))), "{:?}", call("probeOne"));
}

/// The rule spellings, now that a rule's call is run by the interpreter whole.
#[test]
fn a_dispatch_to_a_third_sorts_member_from_a_rule() {
    let mut kb = crate::common::load_kb_with(THIRD);
    assert!(holds(&mut kb, "test.dey66.third.answer(7)"));
    assert!(holds(&mut kb, "test.dey66.third.answerAll(8)"));
    assert!(holds(&mut kb, "test.dey66.third.answerOne(8)"));
}

/// CONTROL: the direct call of the member built its own sort's dictionary before.
#[test]
fn control_the_direct_call_of_the_member() {
    assert!(matches!(call("direct"), Ok(eval::Value::Int(7))), "{:?}", call("direct"));
}

// ── the narrowing reads a tuple ──────────────────────────────────────────────────────────

const TUPLES: &str = r#"
namespace test.dey66.tuple
  import anthill.prelude.{Int64, List}
  import anthill.prelude.List.{cons, nil}

  operation firstof(xs: List[T = Int64], d: Int64) -> Int64 = match (xs, d)
    case (cons(h, t), _) -> h
    case (nil, dd) -> dd
  operation firstm(xs: List[T = Int64], d: Int64) -> Int64 = match xs
    case cons(h, t) -> h
    case nil -> d
  operation drops(xs: List[T = Int64], d: Int64) -> Int64 = match (xs, d)
    case (cons(h, t), 0) -> h
    case (nil, dd) -> dd
  operation overlap(xs: List[T = Int64], d: Int64) -> Int64 = match (xs, d)
    case (cons(h, t), _) -> h
    case (_, dd) -> dd
  operation appT(xs: List[T = Int64], ys: List[T = Int64]) -> List[T = Int64] = match (xs, ys)
    case (nil, zs) -> zs
    case (cons(h, t), zs) -> cons(h, appT(t, zs))
  operation pick(x: Int64, y: Int64) -> Int64 = match (x, y)
    case (0, _) -> 10
    case _ -> 20

  rule value(?r) :- firstof(?xs, 9) = 9, ?r <=> ?xs
  rule valuem(?r) :- firstm(?xs, 9) = 9, ?r <=> ?xs
  rule dropped(?r) :- drops(?xs, 9) = 9, ?r <=> ?xs
  rule overlapping(?r) :- overlap(?xs, 9) = 9, ?r <=> ?xs
  rule appended(?a) :- appT(?a, [3]) = [1, 3]
end
"#;

fn tuple_rows(kb: &mut KnowledgeBase, rel: &str) -> Vec<(String, bool)> {
    crate::common::shown_rows(kb, &format!("test.dey66.tuple.{rel}"))
}

/// 3HN0N's row (DSEXA's 2026-10-11 note): the `match (xs, d)` spelling answers the two
/// definite rows its `match xs` twin does. Before: one conditional row, residual
/// `eq(firstof(?_, 9), 9)`.
#[test]
fn a_match_on_a_tuple_narrows_the_component_it_tests() {
    let mut kb = crate::common::load_kb_with(TUPLES);
    let rows = tuple_rows(&mut kb, "value");
    assert_eq!(rows, tuple_rows(&mut kb, "valuem"));
    assert_eq!(rows.len(), 2, "{rows:?}");
    assert!(rows.iter().all(|(_, definite)| *definite), "{rows:?}");
}

/// The known component's pattern drops an arm it cannot match: `drops(cons(…), 9)` matches
/// no arm, so only `nil` narrows. Before: one conditional row.
#[test]
fn an_arm_the_known_component_refutes_is_dropped() {
    let mut kb = crate::common::load_kb_with(TUPLES);
    assert_eq!(tuple_rows(&mut kb, "dropped"), vec![("nil".to_string(), true)]);
}

/// A recursive tuple match narrows as its `match xs` twin, `List.append`, does: the
/// arm's residual is unified with OTHER first, so it terminates. Before: one conditional row.
#[test]
fn a_recursive_tuple_match_narrows_as_its_twin() {
    let mut kb = crate::common::load_kb_with(TUPLES);
    assert_eq!(
        tuple_rows(&mut kb, "appended"),
        vec![("cons(head: 1, tail: nil)".to_string(), true)]
    );
}

/// CONTROL: overlapping arms (`_` beside `cons`) are not narrowed, as at a `match xs` with
/// a catch-all: the answer stays conditional.
#[test]
fn control_overlapping_arms_are_not_narrowed() {
    let mut kb = crate::common::load_kb_with(TUPLES);
    let rows = tuple_rows(&mut kb, "overlapping");
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert!(!rows[0].1, "{rows:?}");
}

/// The reducer read a tuple pattern against the `TupleLiteral` node an operation body
/// stores as a known non-tuple, a definite non-match, and took the `_` arm: the prover was
/// handed the one unconditional equation `pick(x, y) = 20`. A `match` on parameters has no
/// defining equations, so it declines now.
#[test]
fn a_tuple_pattern_reads_the_operation_bodys_tuple() {
    let mut kb = crate::common::load_kb_with(TUPLES);
    let pick = all_operation_params(&kb)
        .into_iter()
        .map(|(s, _)| s)
        .find(|s| kb.qualified_name_of(*s) == "test.dey66.tuple.pick")
        .expect("pick is an operation");
    assert!(kb.op_defining_equations(pick).is_none());
}

// ── a dot in a query ─────────────────────────────────────────────────────────────────────

const DOTS: &str = r#"
namespace test.dey66.dot
  import anthill.prelude.{Int64}
  sort Box[V]
    entity box(v: Int64)
    operation tag() -> Int64 = 7
    operation peek(b: Self) -> Int64 = b.v
    operation bump(n: Int64) -> Int64 = n + 1
  end
  operation mk() -> Box = box(v: 3)
  operation seven() -> Int64 = 7
  operation inc(n: Int64) -> Int64 = n + 1
  fact p(4)
end
"#;

/// A3FY2's row (DSEXA's 2026-10-11 note): a dot on a sort, on a construction and on a
/// call is dispatched. Before: each was the data `dot_apply(…)`, so `= 7` had no answer.
#[test]
fn a_dot_in_a_query_is_dispatched_as_in_a_clause() {
    let mut kb = crate::common::load_kb_with(DOTS);
    assert!(holds(&mut kb, "(test.dey66.dot.Box).tag() = 7"));
    assert!(refuted(&mut kb, "(test.dey66.dot.Box).tag() = 8"));
    assert!(holds(&mut kb, "test.dey66.dot.Box.box(v: 4).peek() = 4"));
    assert!(holds(&mut kb, "test.dey66.dot.mk().peek() = 3"));
    assert!(holds(&mut kb, "test.dey66.dot.Box.box(v: 4).v = 4"));
    // A dot in another dot's argument is dispatched with it.
    assert!(holds(&mut kb, "(test.dey66.dot.Box).bump(test.dey66.dot.Box.box(v: 4).peek()) = 5"));
}

/// The dispatched call is a goal's argument, and NAF over it is decided. Before: `p(…)`
/// had no answer and `not(… = 5)` was conditional.
#[test]
fn a_dot_in_a_query_goal_argument() {
    let mut kb = crate::common::load_kb_with(DOTS);
    assert!(holds(&mut kb, "test.dey66.dot.p(test.dey66.dot.Box.box(v: 4).peek())"));
    assert!(refuted(&mut kb, "test.dey66.dot.p(test.dey66.dot.Box.box(v: 5).peek())"));
    assert!(holds(&mut kb, "not(test.dey66.dot.Box.box(v: 4).peek() = 5)"));
}

/// A query's variable has no type for a dot to be dispatched by, written alone, in another
/// dot's argument or as its receiver. Before: the dot was bound as data.
#[test]
fn a_dot_on_a_query_variable_is_refused() {
    let mut kb = crate::common::load_kb_with(DOTS);
    for pattern in [
        "?x <=> ?b.peek()",
        "?x <=> (test.dey66.dot.Box).bump(?b.peek())",
        "?x <=> (?b.peek()).bump()",
    ] {
        let refusals = crate::common::query_pattern_refusals(&mut kb, pattern);
        assert!(
            refusals.iter().any(|r| r.contains("`?b.peek` cannot be dispatched in a query")),
            "{pattern}: {refusals:?}"
        );
    }
}

/// A member the receiver's sort does not declare is refused as in a clause. Before: data.
#[test]
fn a_dot_naming_no_member_is_refused() {
    let mut kb = crate::common::load_kb_with(DOTS);
    let refusals = crate::common::query_pattern_refusals(&mut kb, "?x <=> (test.dey66.dot.Box).nope()");
    assert!(refusals.iter().any(|r| r.contains("no such member")), "{refusals:?}");
}

/// CONTROL: A3FY2's nullary rows, which answer since 2S5FP / CZJ2N, and the qualified call.
#[test]
fn control_a_nullary_call_and_a_qualified_call_in_a_query() {
    let mut kb = crate::common::load_kb_with(DOTS);
    assert!(holds(&mut kb, "test.dey66.dot.seven() = 7"));
    assert!(holds(&mut kb, "test.dey66.dot.inc(test.dey66.dot.seven()) = 8"));
    assert!(holds(&mut kb, "test.dey66.dot.Box.tag() = 7"));
    assert!(holds(&mut kb, "test.dey66.dot.Box.peek(test.dey66.dot.Box.box(v: 4)) = 4"));
}
