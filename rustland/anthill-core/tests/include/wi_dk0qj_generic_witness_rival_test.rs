//! WI-20260923-DK0QJ — A SET BUILT WITH A GENERIC WITNESS IS NOT ANSWERED BY A MORE SPECIFIC
//! RIVAL, on any route.
//!
//! The fixture is `wi_ee0ep_param_dictionary_test::specificity_does_not_choose_a_type_carried_slot`'s
//! (WI-20260922-ATFGH): three providers of `WeakOrd[T = Pair[A = String, B = String]]` — the
//! stdlib's `Pair` (lexicographic), `Flat` (generic over any pair of ordered components,
//! calling every pair equal) and `PairNe` (at exactly `Pair[String, String]`, calling no pair
//! equal: the most specific head). A set `{pair("a", "z")}` built at `O = Flat`, and one whose
//! witness has a named slot of its own, `O = ByInner[OI = Flat]` over `Boxed[E = Pair[…]]`.
//! Asked whether the set holds its own element, `Flat` and `Pair` say yes and `PairNe` alone
//! says no, so `false` is the rival's answer and nothing else's.
//!
//! Two routes answered `false`, in silence:
//!
//! * A WRITTEN QUERY, `Driver.flat(0, ?s), MySet.contains(?s, pair("a", "z"), ?r)`. The
//!   query's typing collected its goals' constraints and never settled the positions a clause
//!   reads after its walk, `flat`'s result column among them, so `?s` was at what `contains`'
//!   parameter says, `MySet[T = …, O = ?]`, the call's `O` was inferred by the ladder (058
//!   §3.4) and `PairNe` won it, with no dictionary built from a value. A query's late
//!   positions are now settled as a rule body's are (`ClauseSite::Query`).
//! * A GOAL BUILT AT RUN TIME, typed by no load — a call no typer reads (kernel-language
//!   §5.2). The SLD bridge built the call's dictionary from the values and answered a named
//!   slot at `Withhold`, which lets the most specific provider win: the carrier's own slot,
//!   `MySet`'s `O` (the ticket's half (b)), and — below a sole `ByInner` — the witness's own
//!   `OI` (half (a), the nested slot, which the sub-goal recursion re-derived at `Withhold`).
//!   Each named slot on that route is now answered by a sole provider only, at every depth,
//!   and the goal delays on a tie, as §5.2 says.
//!
//! A typed host call and a rule body answered by `Flat` before this ticket and after it.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, each alone, then removed:
//!
//! * the query's late positions left unsettled: [`a_written_query_reads_the_slot_its_calls_result_writes`]
//!   fails on both shapes (`false` definite), and on the `<=>` spelling measured alone (`true`
//!   answers nothing);
//! * the bridge answering a non-type-carried named slot at `Withhold`:
//!   [`a_run_time_goal_takes_no_rival_for_the_carriers_own_slot`] fails (`false` definite), and
//!   so does [`a_run_time_goal_takes_no_rival_for_a_witness_own_slot`], whose sub-slot is then
//!   derived below a withheld goal;
//! * a chosen provider's named slot re-derived at `Withhold` below an unranked goal:
//!   [`a_run_time_goal_takes_no_rival_for_a_witness_own_slot`] fails; the carrier's-own-slot
//!   row passes.
//!
//! [`the_typed_routes_answer_by_the_witness_the_set_was_built_with`] and
//! [`a_sole_provider_still_answers_a_run_time_goal`] pass either way by design: the first is
//! the answer the others are held to, the second a slot with one provider, which no ranking
//! changes.

use anthill_core::eval::{HostValue, Interpreter, Value};
use anthill_core::kb::resolve::{bridge_derivations_by_this_thread, ResolveConfig};
use anthill_core::kb::KnowledgeBase;

const SRC: &str = r#"
namespace dk0qj
  import anthill.prelude.{WeakOrd, String, Int64, Bool, Pair}
  import anthill.prelude.Pair.{pair}
  sort Flat
    sort A = ?
    sort B = ?
    provides WeakOrd[T = Pair[A = A, B = B]] :- WeakOrd[A], WeakOrd[B]
    operation compare(a: Pair[A = A, B = B], b: Pair[A = A, B = B]) -> Int64 = 0
  end
  sort PairNe
    provides WeakOrd[T = Pair[A = String, B = String]]
    operation compare(a: Pair[A = String, B = String], b: Pair[A = String, B = String]) -> Int64 = 1
  end
  enum MySet
    import anthill.prelude.PartialOrd.{lt, gt}
    sort T = ?
    requires O: WeakOrd[T]
    entity nothing
    entity node(elem: T, rest: MySet[T = T, O = O])
    operation contains(s: MySet[T = T, O = O], x: T) -> Bool =
      match s
        case nothing() -> false
        case node(y, r) ->
          let c = WeakOrd.compare(x, y)
          if lt(c, 0) then false
          else if gt(c, 0) then contains(r, x)
          else true
    operation empty() -> MySet[T = T, O = O] = nothing()
    operation insert(s: MySet[T = T, O = O], x: T) -> MySet[T = T, O = O] = node(x, s)
  end
  enum Boxed
    import anthill.prelude.{PartialEq, Eq}
    sort E = ?
    requires Eq[T = E]
    entity boxed(v: E)
    provides PartialEq[T = Self]
    provides Eq[T = Self]
    operation eq(a: Self, b: Self) -> Bool =
      match a
        case boxed(av) ->
          match b
            case boxed(bv) -> PartialEq.eq(av, bv)
  end
  sort ByInner
    import anthill.prelude.{WeakOrd, PartialOrd}
    sort E = ?
    requires OI: WeakOrd[T = E]
    provides PartialOrd[T = Boxed[E = E]]
    provides WeakOrd[T = Boxed[E = E]]
    operation compare(a: Boxed[E = E], b: Boxed[E = E]) -> Int64 =
      match a
        case boxed(av) ->
          match b
            case boxed(bv) -> WeakOrd.compare(av, bv)
  end
  sort Driver
    operation flat(n: Int64) -> MySet[T = Pair[A = String, B = String], O = Flat] =
      MySet.insert(MySet.empty[T = Pair[A = String, B = String], O = Flat](), pair("a", "z"))
    operation nested(n: Int64) -> MySet[T = Boxed[E = Pair[A = String, B = String]], O = ByInner[OI = Flat]] =
      MySet.insert(MySet.empty[T = Boxed[E = Pair[A = String, B = String]], O = ByInner[OI = Flat]](), boxed(v: pair("a", "z")))
    operation ints(n: Int64) -> MySet[T = Int64] = MySet.insert(MySet.empty[T = Int64](), 5)
    operation nestedInts(n: Int64) -> MySet[T = Boxed[E = Int64], O = ByInner] =
      MySet.insert(MySet.empty[T = Boxed[E = Int64], O = ByInner](), boxed(v: 5))
    operation hostFlat(n: Int64) -> Bool = MySet.contains(flat(n), pair("a", "z"))
    operation hostNested(n: Int64) -> Bool = MySet.contains(nested(n), boxed(v: pair("a", "z")))
  end
  rule byResult(?x: Pair[A = String, B = String], ?r) :- Driver.flat(0, ?s), MySet.contains(?s, ?x, ?r)
  rule byEquation(?x: Pair[A = String, B = String], ?r) :- ?s <=> Driver.flat(0), MySet.contains(?s, ?x, ?r)
end
"#;

/// The set's own element, which only `PairNe` says it does not hold.
const ELEMENT: &str = "anthill.prelude.Pair.pair(\"a\", \"z\")";
const BOXED: &str = "dk0qj.Boxed.boxed(v: anthill.prelude.Pair.pair(\"a\", \"z\"))";

/// PINNED TO ONE LOAD, BY NAME (WI-20261010-9BKZ4), as the ATFGH row is: `PairNe` provides the
/// stdlib's `WeakOrd` at the stdlib's `Pair[A = String, B = String]`, more specifically than
/// `Pair` itself, so it changes who answers an unselected dispatch there — for the stdlib's
/// bodies as for these — and loaded after the stdlib sealed it is a load error
/// (`ChangesSealedCode`). That most specific rival is the fixture's point.
fn one_load() -> KnowledgeBase {
    let (kb, _) = crate::common::expect_loaded(crate::common::recipe_load(
        &[SRC],
        None,
        anthill_core::kb::load::LoadOptions::default(),
        crate::common::LoadRecipe::OneShot,
        |_| {},
    ));
    kb
}

/// What `contains(set, x)` answers over goals built by `goals` from `[make(0, ?s), contains(?s, x,
/// <literal>)]`: per literal, the definite answers and all of them, and the dictionaries built
/// from values while they ran.
#[derive(Debug, PartialEq)]
struct Answers {
    true_definite: usize,
    true_all: usize,
    false_definite: usize,
    false_all: usize,
    derived: usize,
}

fn answers(
    make: &str,
    x: &str,
    goals: fn(&mut KnowledgeBase, &[&str]) -> Vec<anthill_core::kb::load::QueryPattern>,
) -> Answers {
    let mut counts = [(0, 0); 2];
    let mut derived = 0;
    for (at, literal) in ["true", "false"].into_iter().enumerate() {
        let mut kb = one_load();
        let patterns = [
            format!("dk0qj.Driver.{make}(0, ?s)"),
            format!("dk0qj.MySet.contains(?s, {x}, {literal})"),
        ];
        let patterns: Vec<&str> = patterns.iter().map(String::as_str).collect();
        let goals = goals(&mut kb, &patterns);
        let before = bridge_derivations_by_this_thread();
        let (sols, stats) = kb.resolve_with_stats(&goals, &ResolveConfig::default());
        derived += bridge_derivations_by_this_thread() - before;
        assert!(!stats.truncated && stats.errors.is_empty(), "{patterns:?}: a complete search: {stats:?}");
        counts[at] = (sols.iter().filter(|s| s.is_definite()).count(), sols.len());
    }
    Answers {
        true_definite: counts[0].0,
        true_all: counts[0].1,
        false_definite: counts[1].0,
        false_all: counts[1].1,
        derived,
    }
}

/// A written query is typed where it is read, as a rule body is: `?s` is at `flat`'s result
/// type, `O = Flat` written there, and the call reads it — `true`, nothing built from a value.
/// The nested set's `OI = Flat` is read off the same type. FAILS with the query's late
/// positions left unsettled: `false` definite on both shapes, `PairNe`'s answer.
#[test]
fn a_written_query_reads_the_slot_its_calls_result_writes() {
    for (make, x) in [("flat", ELEMENT), ("nested", BOXED)] {
        let got = answers(make, x, crate::common::query_goals);
        assert_eq!(
            got,
            Answers { true_definite: 1, true_all: 1, false_definite: 0, false_all: 0, derived: 0 },
            "{make}: the query answers by the witness the set was built with"
        );
    }
    // The `<=>` spelling, read by the late position a clause reads it by (`CalledValue`).
    let mut kb = one_load();
    for (literal, expected) in [("true", 1), ("false", 0)] {
        let patterns = [
            "?s <=> dk0qj.Driver.flat(0)".to_string(),
            format!("dk0qj.MySet.contains(?s, {ELEMENT}, {literal})"),
        ];
        let patterns: Vec<&str> = patterns.iter().map(String::as_str).collect();
        let goals = crate::common::query_goals(&mut kb, &patterns);
        let sols = kb.resolve(&goals, &ResolveConfig::default());
        assert_eq!(
            (sols.iter().filter(|s| s.is_definite()).count(), sols.len()),
            (expected, expected),
            "{patterns:?}"
        );
    }
}

/// HALF (b): a goal no load typed holds the set's value and not its type, so `MySet`'s own `O`
/// is built from the value — and the value chose `Flat` and does not say so. Three providers
/// match, none is the one, and the goal is left undecided, neither answer definite. FAILS with
/// the bridge answering the slot at `Withhold`: `false` definite, `PairNe`'s.
#[test]
fn a_run_time_goal_takes_no_rival_for_the_carriers_own_slot() {
    let got = answers("flat", ELEMENT, crate::common::run_time_goals);
    assert_eq!(
        got,
        Answers { true_definite: 0, true_all: 1, false_definite: 0, false_all: 1, derived: 2 },
        "undecided at either answer, the dictionary derived from the value each time"
    );
}

/// HALF (a), THE NESTED SLOT: the top slot has one provider, `ByInner`, which is exact; its own
/// `OI` is chosen by the same construction and carried no more than `O` is, so it is not
/// ranked either, and the goal is undecided. FAILS with a chosen provider's named slot
/// re-derived at `Withhold` below the unranked goal: `false` definite, `PairNe`'s.
#[test]
fn a_run_time_goal_takes_no_rival_for_a_witness_own_slot() {
    let got = answers("nested", BOXED, crate::common::run_time_goals);
    assert_eq!(
        got,
        Answers { true_definite: 0, true_all: 1, false_definite: 0, false_all: 1, derived: 2 },
        "undecided at either answer, the dictionary derived from the value each time"
    );
}

/// CONTROL: where each slot has ONE provider — `Int64`'s own ordering, and `ByInner` over
/// `Boxed[E = Int64]` with `Int64`'s below it — the run-time goal answers definitely: the
/// provider is exact, the route is not refused. Passes either way by design.
#[test]
fn a_sole_provider_still_answers_a_run_time_goal() {
    for (make, x) in [("ints", "5"), ("nestedInts", "dk0qj.Boxed.boxed(v: 5)")] {
        let got = answers(make, x, crate::common::run_time_goals);
        assert_eq!(
            got,
            Answers { true_definite: 1, true_all: 1, false_definite: 0, false_all: 0, derived: 2 },
            "{make}: a sole provider answers, its dictionary derived from the value each time"
        );
    }
}

/// CONTROL, the answer the routes above are held to: a typed host call and a rule body read
/// `O = Flat` (and `OI = Flat`) off the set's type, `true`. Passes either way by design.
#[test]
fn the_typed_routes_answer_by_the_witness_the_set_was_built_with() {
    let mut interp = Interpreter::new(one_load());
    anthill_core::eval::builtins::register_standard_builtins(&mut interp);
    for op in ["dk0qj.Driver.hostFlat", "dk0qj.Driver.hostNested"] {
        let got = interp.call(op, &HostValue::all(&[Value::Int(0)])).map(|h| h.value);
        assert!(matches!(got, Ok(Value::Bool(true))), "{op}: {got:?}");
    }
    let mut kb = one_load();
    for rule in ["byResult", "byEquation"] {
        for (literal, expected) in [("true", 1), ("false", 0)] {
            let pattern = format!("dk0qj.{rule}({ELEMENT}, {literal})");
            let goals = crate::common::query_goals(&mut kb, &[pattern.as_str()]);
            let sols = kb.resolve(&goals, &ResolveConfig::default());
            assert_eq!(
                (sols.iter().filter(|s| s.is_definite()).count(), sols.len()),
                (expected, expected),
                "{pattern}"
            );
        }
    }
}
