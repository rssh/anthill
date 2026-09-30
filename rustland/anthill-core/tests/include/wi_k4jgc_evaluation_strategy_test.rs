//! WI-20260926-K4JGC — proposal 068 §1.1–1.2: an operation application written in a rule
//! body denotes its VALUE at any depth, and every consumer reads it by ONE evaluation
//! strategy (`kb/resolve/evaluate.rs`) — evaluate until a variable or a stuck call is left,
//! then work structurally.
//!
//! Before it, each consumer reduced to its own depth: `=` / `===` the top of an operand,
//! `<=>` the node its walk was at (a bind stored the rest unvisited), head matching nothing.
//! One call answered true, false or nothing by where it was written, a stuck call was bound
//! as DATA and reported as a definite answer, and `not(...)` over a wrong refutation proved
//! a falsehood. Every row below is the ticket's (and 068's problem section's), driven by
//! value.
//!
//! ## Back-out
//!
//! MEASURED against this module alone (`scripts/test.sh -p anthill-core --test wi_tests --
//! wi_k4jgc`), each back-out on its own:
//!   * the whole change (the tree before this ticket) — every row but the three CONTROLS and
//!     the two EDGE rows (`a_deep_value_is_walked_to_its_end`,
//!     `a_goal_passed_as_data_stays_the_term`), which pin what the new walk must not break
//!     and pass without it by design;
//!   * goal arguments not evaluated before candidate selection (`evaluate_goal_arguments`
//!     answering `None`) — `a_goal_argument_is_evaluated_before_head_matching`,
//!     `arithmetic_in_a_goal_argument_computes` and the WI-670 row;
//!   * WI-670's open-time refutation judging an atom that holds a call —
//!     `wi670_does_not_refute_an_atom_holding_a_call` (`q` is empty);
//!   * every hole pending, reached or not — `identical_stuck_calls_unify_by_reflexivity`
//!     (a conditional row);
//!   * body-less spec operations not dispatched in a value slot (`reduce_op_value`'s
//!     `dispatch_body_less` false in `evaluate_call`) —
//!     `a_body_less_spec_operation_dispatches_in_a_value_slot`;
//!   * the fold cap counted per DATA level (`evaluate_child` passing `depth + 1`) —
//!     `a_deep_value_is_walked_to_its_end` (a panic);
//!   * a builtin's failure over numbers read as "not run" —
//!     `a_call_with_no_value_fails_where_it_is_read`;
//!   * a goal-only builtin classified like any call — `a_goal_passed_as_data_stays_the_term`.
//!
//! The CONTROL rows pass either way, by design, and each says why at its site.

use anthill_core::kb::resolve::{ResolveConfig, UnknownCause};
use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// `C.tag` is a bodied `match` (`tag(red()) = 1`); `String.contains` is host-mapped; `p`
/// has one fact, `p(n: 1)`.
const SRC: &str = r#"
namespace k4jgc
  import anthill.prelude.{Int64, String, Bool, WeakOrd, PartialEq, Set, List}
  import anthill.prelude.Set.{union, intersection}

  sort C
    entity red
    entity green
    operation tag(c: C) -> Int64 =
      match c
        case red() -> 1
        case green() -> 2
  end
  sort Box
    entity box(v: Int64)
  end
  sort BB
    entity bb(v: Bool)
  end
  sort Pair
    entity pair(a: C, b: Box)
  end
  sort P
    entity p(n: Int64)
    entity num(n: Int64)
  end
  fact p(n: 1)
  fact p(n: 3)
  fact num(n: 2)

  -- `=`, `===` and `<=>` over a call under a constructor
  rule hostUnder(1) :- bb(v: String.contains("abc", "b")) = bb(v: true)
  rule bodiedUnder(1) :- box(v: C.tag(red())) = box(v: 1)
  rule structUnder(1) :- box(v: C.tag(red())) === box(v: 1)
  rule bound(?v) :- ?v <=> box(v: C.tag(red()))
  rule boundThenTested(1) :- ?v <=> box(v: C.tag(red())), ?v = box(v: 1)

  -- a goal's argument
  rule argument(1) :- p(n: C.tag(red()))
  rule notArgument(1) :- not(p(n: C.tag(red())))

  -- a call that cannot run yet
  rule pending(?v) :- ?v <=> box(v: C.tag(?c))
  rule pendingThenBound(?v) :- ?v <=> box(v: C.tag(?c)), ?c <=> red()
  rule withinOneGoal(?v) :- pair(a: ?c, b: box(v: C.tag(?c))) <=> pair(a: red(), b: ?v)
  rule reflexive(1) :- box(v: C.tag(?c)) <=> box(v: C.tag(?c))

  -- a call no implementation will ever run
  rule noImpl(1) :- intersection({1, 2}, {2}) = {2}
  rule notNoImpl(1) :- not(intersection({1, 2}, {2}) = {2})
  rule noImplUnion(1) :- union({1}, {2}) = {1, 2}

  -- a body-less spec operation in a value slot
  rule compared(1) :- WeakOrd.compare(1, 5) = -1
  rule below(?a, ?b) :- PartialEq.eq(WeakOrd.compare(?a, ?b), -1)
  rule isBelow(1) :- below(1, 5)
  rule notBelow(1) :- not(below(1, 5))
  rule compareRelation(?r) :- WeakOrd.compare(1, 5, ?r)
  rule compareBound(?r) :- ?r <=> WeakOrd.compare(1, 5)

  -- arithmetic (a resolver builtin) in a value slot
  rule sumBound(?r) :- ?r <=> 1 + 2
  rule sumTested(1) :- 3 = 1 + 2
  rule sumArgument(1) :- p(n: 1 + 2)

  -- WI-670's open-time refutation: `r` opens with `?x` unbound in `q`
  rule r(?x) :- anthill.reflect.ground(?x), p(n: Int64.add(?x, 1))
  rule q(?x) :- r(?x), num(n: ?x)
  rule q2(?x) :- num(n: ?x), r(?x)

  -- review rows: deep data, a call with no value, a goal passed as data
  rule divBound(?r) :- ?r <=> Int64.div(1, 0)
  rule divTested(1) :- Int64.div(1, 0) = 3
  rule divNot(1) :- not(Int64.div(1, 0) = 3)
  rule divArgument(1) :- p(n: Int64.div(1, 0))
  rule divRelation(?r) :- Int64.div(1, 0, ?r)
  rule takes(?g) :- anthill.reflect.nonvar(?g)
  rule goalAsData(1) :- takes(PartialEq.eq(?x, 1))

  -- CONTROLS
  rule controlVar(?n) :- box(v: ?n) <=> box(v: C.tag(red()))
  rule controlWhole(?v) :- ?v <=> C.tag(?c)
  rule controlNarrow(?a) :- List.append(?a, [3]) = [1, 3]
end
"#;

fn kb() -> KnowledgeBase {
    crate::common::load_kb_with(SRC)
}

/// The rows of `k4jgc.<rel>`, rendered, each with whether it is definite.
fn rows(kb: &mut KnowledgeBase, rel: &str) -> Vec<(String, bool)> {
    crate::common::shown_rows(kb, &format!("k4jgc.{rel}"))
}

/// The one DEFINITE answer of `k4jgc.<rel>`, if it is `box(v: n)`: `Some(n)`.
fn one_box(kb: &mut KnowledgeBase, rel: &str) -> Option<i64> {
    let rows = crate::common::query_unary(kb, &format!("k4jgc.{rel}"));
    let [(v, true)] = rows.as_slice() else {
        panic!("{rel}: one definite row; got {rows:?}");
    };
    let functor = crate::common::entity_functor(kb, v).map(|f| kb.local_name_of(f).to_string());
    if functor.as_deref() != Some("box") {
        return None;
    }
    let field = crate::common::entity_field(kb, v, "v", 0);
    crate::common::scalar_int(kb, &field)
}

/// `[("1", true)]` — the relation holds, definitely, once.
fn holds(kb: &mut KnowledgeBase, rel: &str) -> bool {
    rows(kb, rel) == vec![("1".to_string(), true)]
}

/// The undecided causes of each answer of `k4jgc.<rel>(?r)` — what the drain reports for a
/// goal that has no answer, as opposed to one that floundered.
fn undecided_causes(kb: &mut KnowledgeBase, rel: &str) -> Vec<Vec<UnknownCause>> {
    let sym = kb
        .try_resolve_symbol(&format!("k4jgc.{rel}"))
        .unwrap_or_else(|| panic!("`k4jgc.{rel}` does not resolve"));
    let r_sym = kb.intern("r");
    let r_vid = kb.fresh_var(r_sym);
    let r_var = kb.alloc(Term::Var(Var::Global(r_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_elem(r_var, 1),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .map(|sol| sol.undecided.iter().map(|(_, cause)| *cause).collect())
        .collect()
}

// ── one strategy for `=`, `===` and `<=>` ─────────────────────────────────────────────────

/// A call under an entity constructor is evaluated by `=` — host-mapped and bodied alike.
/// Before: both (0, 0), definite refutations, the unevaluated call compared as data.
#[test]
fn a_call_under_a_constructor_is_evaluated_by_eq() {
    let mut kb = kb();
    assert!(holds(&mut kb, "hostUnder"), "{:?}", rows(&mut kb, "hostUnder"));
    assert!(holds(&mut kb, "bodiedUnder"), "{:?}", rows(&mut kb, "bodiedUnder"));
}

/// `===` compares the VALUES of its operands at every depth (068 §5). Before: (0, 0).
#[test]
fn struct_eq_compares_the_values_of_its_operands() {
    let mut kb = kb();
    assert!(holds(&mut kb, "structUnder"), "{:?}", rows(&mut kb, "structUnder"));
}

/// `<=>` binds the call's VALUE: `box(v: 1)`, definite. Before: a definite answer binding
/// `?v` to `box(v: tag(red))` — the call as data — and `?v = box(v: 1)` after it then
/// refuted the equation the other spelling proves.
#[test]
fn unify_binds_the_value_not_the_call() {
    let mut kb = kb();
    assert_eq!(one_box(&mut kb, "bound"), Some(1));
    assert!(holds(&mut kb, "boundThenTested"), "{:?}", rows(&mut kb, "boundThenTested"));
}

// ── a goal's arguments ────────────────────────────────────────────────────────────────────

/// Design D3: a goal's arguments are evaluated before candidate selection, so
/// `p(n: C.tag(red()))` meets `fact p(n: 1)` as `p(n: 1)`. Before: (0, 0), and `not(...)`
/// over it PROVED A FALSEHOOD — `notArgument` answered 1.
#[test]
fn a_goal_argument_is_evaluated_before_head_matching() {
    let mut kb = kb();
    assert!(holds(&mut kb, "argument"), "{:?}", rows(&mut kb, "argument"));
    assert_eq!(rows(&mut kb, "notArgument"), Vec::<(String, bool)>::new());
}

// ── a call that cannot run yet: a pending equation, never data (068 §1.2) ──────────────────

/// `?v <=> box(v: C.tag(?c))`: `?c` is never bound, so the answer is CONDITIONAL on the
/// pending `unify(?t, tag(?c))` — and `?v` holds a variable where the call stood, never the
/// call. Once `?c <=> red()` follows, the pending equation evaluates: `box(v: 1)`,
/// definite. Before: `pending` was a DEFINITE `box(v: tag(?_))`, and `pendingThenBound` a
/// definite `box(v: tag(red))`.
#[test]
fn a_stuck_call_is_a_pending_equation_not_data() {
    let mut kb = kb();
    let pending = rows(&mut kb, "pending");
    assert!(
        pending.len() == 1 && !pending[0].1 && !pending[0].0.contains("tag"),
        "one conditional row whose value holds no call; got {pending:?}",
    );
    assert_eq!(one_box(&mut kb, "pendingThenBound"), Some(1));
}

/// 068 §1.1 step 4: a bind in the same `<=>` that binds a pending call's blocker lets it
/// evaluate within the derivation — `?c` is unbound when evaluation reaches `C.tag(?c)`, and
/// bound by the same unification. Before: a definite `box(v: tag(red))`.
#[test]
fn a_binding_in_the_same_unification_evaluates_the_pending_call() {
    let mut kb = kb();
    assert_eq!(one_box(&mut kb, "withinOneGoal"), Some(1));
}

/// Two IDENTICAL stuck calls share one hole and unify by reflexivity: a pure operation
/// applied to the same arguments has the same value, whatever it is — so the hole pends
/// nothing and the answer is definite. FAILS with every hole kept pending: one conditional
/// row — which is also what it answered before this ticket, `<=>` delaying the whole goal
/// on the call.
#[test]
fn identical_stuck_calls_unify_by_reflexivity() {
    let mut kb = kb();
    assert!(holds(&mut kb, "reflexive"), "{:?}", rows(&mut kb, "reflexive"));
}

// ── a call no implementation will ever run (068 §2) ───────────────────────────────────────

/// `Set.intersection` / `union` have no body, no host mapping and no provider: their calls
/// are UNREDUCED, so a comparison over one is UNDECIDED — a conditional answer whose cause is
/// named `Unreduced`, not a flounder — and `not(...)` over it is undecided too, never a
/// proof. Before: `noImpl` and `noImplUnion` were definite refutations, and `notNoImpl`
/// PROVED A FALSEHOOD, definitely.
#[test]
fn an_unreduced_call_is_undecided_not_false() {
    let mut kb = kb();
    for rel in ["noImpl", "noImplUnion"] {
        assert_eq!(rows(&mut kb, rel), vec![("1".to_string(), false)], "{rel}");
        assert_eq!(
            undecided_causes(&mut kb, rel),
            vec![vec![UnknownCause::Unreduced]],
            "{rel}: undecided because the call is unreduced, not floundered",
        );
    }
    let neg = rows(&mut kb, "notNoImpl");
    assert!(
        neg.iter().all(|(_, definite)| !definite),
        "`not` over an undecided comparison proves nothing; got {neg:?}",
    );
}

// ── a body-less spec operation in a value slot (PRVA2's rows) ─────────────────────────────

/// `WeakOrd.compare` has no body; `Int64` supplies it. A ground carrier DISPATCHES in a value
/// slot (068 §1), so `compare(1, 5)` is `-1` wherever it is written. Before: `compared` and
/// `isBelow` were (0, 0), `notBelow` PROVED A FALSEHOOD, and `compareBound` bound `?r` to the
/// unreduced `compare(1, 5)` as a DEFINITE answer. `compareRelation`, the functional-relation
/// form, answered `-1` all along — a CONTROL, passing either way by design.
#[test]
fn a_body_less_spec_operation_dispatches_in_a_value_slot() {
    let mut kb = kb();
    assert!(holds(&mut kb, "compared"), "{:?}", rows(&mut kb, "compared"));
    assert!(holds(&mut kb, "isBelow"), "{:?}", rows(&mut kb, "isBelow"));
    assert_eq!(rows(&mut kb, "notBelow"), Vec::<(String, bool)>::new());
    assert_eq!(crate::common::one_definite_int(&mut kb, "k4jgc.compareRelation"), Some(-1));
    assert_eq!(crate::common::one_definite_int(&mut kb, "k4jgc.compareBound"), Some(-1));
}

// ── arithmetic in a value slot ────────────────────────────────────────────────────────────

/// `1 + 2` is `Int64.add`, a resolver builtin: it computes through its result column
/// (`add(1, 2, ?r)`) wherever it is written. Before: `sumBound` and `sumTested` were
/// conditional residuals (`unify(?_, add(1, 2))`, `eq(3, add(1, 2))`) and `sumArgument`
/// (0, 0).
#[test]
fn arithmetic_in_a_value_slot_computes() {
    let mut kb = kb();
    assert_eq!(crate::common::one_definite_int(&mut kb, "k4jgc.sumBound"), Some(3));
    assert!(holds(&mut kb, "sumTested"), "{:?}", rows(&mut kb, "sumTested"));
}

/// The same, as a goal's argument: `p(n: 1 + 2)` meets `fact p(n: 3)`.
#[test]
fn arithmetic_in_a_goal_argument_computes() {
    let mut kb = kb();
    assert!(holds(&mut kb, "sumArgument"), "{:?}", rows(&mut kb, "sumArgument"));
}

// ── WI-670's open-time refutation (PRVA2's row) ───────────────────────────────────────────

/// `r` opens in `q` with `?x` unbound, and WI-670's pre-check delays the clause on its
/// `ground(?x)` — after asking whether another conjunct refutes it regardless. It judged
/// `p(n: Int64.add(?x, 1))` by its discrimination candidates, keying the call as data, and
/// found none: `q` answered nothing where `q2`, the swapped conjunction, answers 2. An atom
/// holding a call is no longer judged. FAILS with that judgement restored: `q` is empty.
/// `q2` is a CONTROL for the conjunction order and needs D3 alone.
#[test]
fn wi670_does_not_refute_an_atom_holding_a_call() {
    let mut kb = kb();
    assert_eq!(crate::common::one_definite_int(&mut kb, "k4jgc.q"), Some(2));
    assert_eq!(crate::common::one_definite_int(&mut kb, "k4jgc.q2"), Some(2));
}

// ── the evaluation walk's edges (found by /code-review) ───────────────────────────────────

/// DATA of any depth is walked: a 70-element list through `<=>` and `=`. The fold cap
/// counts re-evaluations of a call's value, never the depth of a value — counted per data
/// level it made the walk give up at 64 and PANIC in `<=>`'s hole mode. An EDGE row: it
/// passes with the whole ticket backed out, where there was no walk.
#[test]
fn a_deep_value_is_walked_to_its_end() {
    let list: Vec<String> = (1..=70).map(|i| i.to_string()).collect();
    let list = list.join(", ");
    let src = SRC.replace(
        "  -- CONTROLS\n",
        &format!("  rule longUnify(1) :- ?l <=> [{list}], ?l = [{list}]\n  -- CONTROLS\n"),
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert!(holds(&mut kb, "longUnify"), "{:?}", rows(&mut kb, "longUnify"));
}

/// A call that RAN and has NO value — `div(1, 0)` — fails whatever reads it, exactly as its
/// relation `div(1, 0, ?r)` fails (the CONTROL here, answering nothing either way): `<=>`,
/// `=` and a goal argument all answer nothing, and `not(... = 3)` holds. FAILS with the
/// builtin's failure read as "not run": each of the three is a conditional residual and
/// `divNot` is undecided.
#[test]
fn a_call_with_no_value_fails_where_it_is_read() {
    let mut kb = kb();
    for rel in ["divBound", "divTested", "divArgument", "divRelation"] {
        assert_eq!(rows(&mut kb, rel), Vec::<(String, bool)>::new(), "{rel}");
    }
    assert!(holds(&mut kb, "divNot"), "{:?}", rows(&mut kb, "divNot"));
}

/// A GOAL-ONLY builtin (`eq`) passed as DATA to a relation is not a value computation: it
/// stays the term, so `takes(PartialEq.eq(?x, 1))` holds. FAILS with such a builtin
/// classified like a call that cannot run yet: it becomes a hole, `takes` holds of the
/// hole, and the pending `unify(?t, eq(?x, 1))` never discharges — one conditional row. An
/// EDGE row: it passes with the whole ticket backed out, where goal arguments were not
/// evaluated.
#[test]
fn a_goal_passed_as_data_stays_the_term() {
    let mut kb = kb();
    assert!(holds(&mut kb, "goalAsData"), "{:?}", rows(&mut kb, "goalAsData"));
}

// ── CONTROLS ──────────────────────────────────────────────────────────────────────────────

/// CONTROL — passes either way, BY DESIGN: `<=>` recursed into the constructor and reduced
/// the call at the node it reached before this ticket, and does after.
#[test]
fn control_a_variable_against_a_call_binds_its_value() {
    let mut kb = kb();
    assert_eq!(crate::common::one_definite_int(&mut kb, "k4jgc.controlVar"), Some(1));
}

/// CONTROL — passes either way, BY DESIGN: a WHOLE side that is a stuck call is the pending
/// equation itself, so the goal waits for `?c` and ends a conditional answer, as it always
/// did — the new strategy must not bind `?v` to a hole that restates it.
#[test]
fn control_a_whole_stuck_side_waits() {
    let mut kb = kb();
    let rows = rows(&mut kb, "controlWhole");
    assert!(rows.len() == 1 && !rows[0].1, "one conditional row; got {rows:?}");
}

/// CONTROL — passes either way, BY DESIGN: the WI-580 unfold still NARROWS a call on a flex
/// argument (`append(?a, [3]) = [1, 3]` solves `?a = [1]`); it runs before `=` evaluates.
#[test]
fn control_the_unfold_still_narrows() {
    let mut kb = kb();
    assert_eq!(
        rows(&mut kb, "controlNarrow"),
        vec![("cons(head: 1, tail: nil)".to_string(), true)],
        "`?a = [1]`, definite",
    );
}
