//! WI-20260926-CYNPE — proposal 068 §2.2, the run-time half: a goal that cannot be answered
//! YET waits on its blockers and is not asked again until one is bound; a goal that can NEVER
//! be answered is parked with its cause; and a functional-relation call that did not run
//! waits instead of answering nothing.
//!
//! Before it, a delayed goal was asked again from scratch every time a sibling made progress
//! (an evaluation that can include a bridge run), an UNREDUCED goal was rotated exactly as a
//! delay was, and the WI-938 hook sent a call that did not run to candidate selection, where
//! no clause is written for `f/n+1` — so an unbound argument, no supplier and a supplier tie
//! all answered NOTHING, silently (WI-20260924-35E14, WI-20260925-PRVA2's `Conv.tag` row).
//!
//! ## Back-out
//!
//! MEASURED against this module alone (`scripts/test.sh -p anthill-core --test wi_tests --
//! wi_cynpe`), each back-out on its own:
//!   * the WI-938 hook as it was (an UNWOVEN call that did not run goes to candidate
//!     selection) — `a_bodied_call_waits_for_its_argument`,
//!     `a_call_that_never_gets_its_argument_is_a_conditional_answer`,
//!     `an_unreduced_call_is_an_undecided_residual_naming_its_cause` (each: no solutions);
//!     outside this module, the rows this ticket moved from "no solutions" to UNDECIDED —
//!     `nar1x_carrier_less_spec_op_test::the_same_clause_without_the_require_has_no_definite_answer`,
//!     `wi1043_bodyless_rule_body_test::an_unground_body_less_goal_binds_no_residual`,
//!     `wi_s8cbv_projection_requirement_test::a_rule_with_no_require_has_no_dictionary_at_all`,
//!     `wi_96ztm_two_dictionaries_test::the_control_without_either_require_neither_call_answers`;
//!   * a waiting goal asked on every turn (`pass_over_waiting_goal` never passing one over)
//!     — `a_suspended_goal_is_asked_once` and `a_parked_goal_is_never_asked_again` (each
//!     goal asked 4 times: once, then again after each sibling's progress);
//!   * an UNREDUCED goal parked though a call in it still waits on a variable (the
//!     `unbound_vars_in_goal_calls` test in `schedule_unanswerable_goal`) —
//!     `a_call_waiting_beside_an_unreduced_one_can_still_refute` (one undecided row);
//!   * an UNREDUCED goal suspended on all its variables instead of parked —
//!     `a_parked_goal_is_never_asked_again` (asked 2 times: again once `?c` is bound);
//!   * the WI-938 hook delaying a call that did not run even where a HYPOTHESIS matches the
//!     goal — `a_hypothesis_still_answers_a_stuck_call` (a conditional row where the
//!     assumption answers it; the tree before this ticket passes it, by the fall-through);
//!   * an UNREDUCED goal residualized on the spot instead of rotated behind its siblings —
//!     `a_failing_sibling_still_refutes_a_parked_goal` and
//!     `a_call_waiting_beside_an_unreduced_one_can_still_refute` (an undecided row where the
//!     clause is false) and `a_parked_goal_is_never_asked_again` (the clause residualizes
//!     before its siblings run).
//!
//! The CONTROLS pass either way, by design, and each says why at its site. The ticket's two
//! controls outside this module pass unchanged: `wi519_residual_honesty_test` (every residual
//! row) and `classic_mini_test` (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6) —
//! whose waiting goals are now passed over instead of asked again, with the same answers.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::{ResolveConfig, ResolveStats, Solution, UnknownCause};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;

/// `Colour.score` is an ordinary BODIED operation (35E14's population: P7VP4 weaves only spec
/// operations). `Conv.tag(b: B)` stands at `B`, so nothing in `?s <=> "km", Conv.tag(?s, ?r)`
/// grounds `Conv`'s carrier `A`: no provider supplies the call (PRVA2's row).
const SRC: &str = r#"
namespace wicynpe
  import anthill.prelude.{Int64, String}

  sort Colour
    entity red
    entity green
    entity blue
    operation score(x: Colour) -> Int64 =
      match x
        case red() -> 1
        case green() -> 2
        case blue() -> 3
  end

  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A, b: B) -> Int64
    operation tag(b: B) -> Int64
  end
  sort Meters
    entity m(v: Int64)
    provides Conv[A = Meters, B = String]
    operation conv(a: Meters, b: String) -> Int64 = 7
    operation tag(b: String) -> Int64 = 3
  end

  -- 35E14: the typed head's generator runs AFTER the call
  rule late(x: Colour) :- Colour.score(x, 3)
  rule unbound(?r) :- Colour.score(?v, ?r)

  -- PRVA2: a call no provider supplies
  rule convTag(?r) :- ?s <=> "km", Conv.tag(?s, ?r)
  rule convTagFails(?r) :- ?s <=> "km", Conv.tag(?s, ?r), 1 = 2

  -- a goal waiting on `?z`, which nothing binds, among siblings that make progress one
  -- at a time; and the same siblings without it
  rule chain(?a) :- Int64.gt(?z, 0), ?a <=> ?b + 1, ?b <=> ?c + 1, ?c <=> 1
  rule chainBare(?a) :- ?a <=> ?b + 1, ?b <=> ?c + 1, ?c <=> 1

  -- a PARKED goal whose own variable `?c` a sibling binds; and the same without it
  rule parked(?a) :- ?s <=> "km", ?c <=> Conv.tag(?s), ?a <=> ?b + 1, ?b <=> ?c + 1, ?c <=> 1
  rule parkedBare(?a) :- ?s <=> "km", ?a <=> ?b + 1, ?b <=> ?c + 1, ?c <=> 1

  -- an UNREDUCED comparison beside a call that waits on `?z`: bound to `0`, it has no value
  rule absent(1) :- ?s <=> "km", Int64.div(1, ?z) = Conv.tag(?s), ?z <=> 0
  rule absentLater(1) :- ?s <=> "km", Int64.div(1, ?z) = Conv.tag(?s), ?z <=> 1

  -- a hypothesis about a call stuck on an eigenvariable
  rule hypo(1) :- (forall(?c), Colour.score(?c, 3) -: Colour.score(?c, 3))

  -- CONTROLS
  rule early(?x) :- ?x <=> blue(), Colour.score(?x, 3)
  rule lateEq(x: Colour) :- Colour.score(x) = 3
  rule convTagReq(?r) :- require[Conv[A = Meters, B = String]], Conv.tag("km", ?r)
end
"#;

fn kb() -> KnowledgeBase {
    crate::common::load_kb_with(SRC)
}

fn rows(kb: &mut KnowledgeBase, rel: &str) -> Vec<(String, bool)> {
    crate::common::shown_rows(kb, &format!("wicynpe.{rel}"))
}

/// Resolve `wicynpe.<rel>(?r)`: its solutions and the search's telemetry.
fn resolve(kb: &mut KnowledgeBase, rel: &str) -> (Vec<Solution>, ResolveStats) {
    let goal = crate::common::query_pattern_term(kb, &format!("wicynpe.{rel}(?r)"));
    kb.resolve_with_stats(&[goal], &ResolveConfig::default())
}

/// How many goals the search of `wicynpe.<rel>(?r)` ASKED.
fn asked(kb: &mut KnowledgeBase, rel: &str) -> u64 {
    resolve(kb, rel).1.goals_asked
}

/// Does some residual goal of `sol` hold a call to `name`, at any depth?
fn residual_holds_call(kb: &KnowledgeBase, sol: &Solution, name: &str) -> bool {
    fn holds(kb: &KnowledgeBase, v: &Value, name: &str) -> bool {
        let ViewHead::Functor {
            functor, pos_arity, ..
        } = v.head(kb)
        else {
            return false;
        };
        functor.is_some_and(|f| kb.local_name_of(f) == name)
            || (0..pos_arity).any(|i| v.pos_arg(kb, i).is_some_and(|c| holds(kb, &c.to_value(), name)))
            || v.named_keys(kb)
                .into_iter()
                .any(|k| v.named_arg(kb, k).is_some_and(|c| holds(kb, &c.to_value(), name)))
    }
    sol.residual.iter().any(|g| holds(kb, g, name))
}

// ── the WI-938 hook: a call that did not run waits ────────────────────────────────────────

/// 35E14's `late`: `Colour.score(x, 3)` runs before the typed head's generator binds `x`. The
/// call is SUSPENDED on `x`, is asked again once the generator binds it, and the clause
/// answers `blue`, definitely. Before: no solutions — the hook sent the call to candidate
/// selection, which has no clause for `score/2`.
#[test]
fn a_bodied_call_waits_for_its_argument() {
    let mut kb = kb();
    assert_eq!(rows(&mut kb, "late"), vec![("blue".to_string(), true)]);
}

/// 35E14's `unbound`: nothing ever binds `?v`, so the call never runs and the answer is
/// CONDITIONAL, carrying the call in its residual — not "no solutions".
#[test]
fn a_call_that_never_gets_its_argument_is_a_conditional_answer() {
    let mut kb = kb();
    let (sols, stats) = resolve(&mut kb, "unbound");
    assert_eq!(sols.len(), 1, "one conditional answer");
    assert!(!sols[0].is_definite(), "the call never ran: the answer is conditional");
    assert!(residual_holds_call(&kb, &sols[0], "score"), "the residual carries the call");
    assert!(
        sols[0].undecided.is_empty(),
        "a call waiting on a variable is SUSPENDED, not undecided; got {:?}",
        sols[0].undecided
    );
    assert!(stats.errors.is_empty(), "nothing faulted; got {:?}", stats.errors);
}

/// PRVA2's row, the run-time half: no provider supplies `Conv.tag("km")`, so the call is
/// UNREDUCED — an undecided residual that NAMES its cause, never an empty answer. Before: no
/// solutions, silently.
#[test]
fn an_unreduced_call_is_an_undecided_residual_naming_its_cause() {
    let mut kb = kb();
    let (sols, _) = resolve(&mut kb, "convTag");
    assert_eq!(sols.len(), 1, "one undecided answer; got {} solutions", sols.len());
    let sol = &sols[0];
    assert!(!sol.is_definite());
    let causes: Vec<UnknownCause> = sol.undecided.iter().map(|(_, c)| *c).collect();
    assert_eq!(causes, vec![UnknownCause::Unreduced], "the cause is named");
    assert!(residual_holds_call(&kb, sol, "tag"), "the residual carries the call");
}

/// A PARKED goal keeps its place behind its siblings, so a sibling that fails still refutes
/// the clause: 0 answers, and the search is complete — a refutation, not an undecided answer.
/// Passes against the tree before this ticket too (the hook FAILED the goal); fails if a
/// parked goal residualizes on the spot instead of rotating.
#[test]
fn a_failing_sibling_still_refutes_a_parked_goal() {
    let mut kb = kb();
    let (sols, stats) = resolve(&mut kb, "convTagFails");
    assert!(sols.is_empty(), "`1 = 2` refutes the clause; got {} answers", sols.len());
    assert!(!stats.truncated, "and the search is complete: the answer is 0, definitely");
}

/// A `forall_impl` antecedent is a hypothesis about the call's VALUE, and the consequent's
/// call is stuck on the eigenvariable `c`: the hypothesis answers it, definitely, as candidate
/// selection answered it before the hook waited. Delayed regardless, it waits on a
/// call that can never run and the tautology comes back conditional.
#[test]
fn a_hypothesis_still_answers_a_stuck_call() {
    let mut kb = kb();
    assert_eq!(crate::common::one_definite_int(&mut kb, "wicynpe.hypo"), Some(1));
}

/// An UNREDUCED comparison is not parked while a call beside it still waits on a variable:
/// `Int64.div(1, ?z) = Conv.tag("km")` is undecided until `?z` is bound — to `0` the division
/// has no value (ABSENT), which outranks UNREDUCED, and the clause is REFUTED: 0 answers, the
/// search complete. Parked on the spot, it was never asked again and the clause came back
/// undecided. The control: bound to `1`, the comparison stays undecided.
#[test]
fn a_call_waiting_beside_an_unreduced_one_can_still_refute() {
    let mut kb = kb();
    let (sols, stats) = resolve(&mut kb, "absent");
    assert!(sols.is_empty(), "`div(1, 0)` has no value; got {} answers", sols.len());
    assert!(!stats.truncated, "and the search is complete: the answer is 0, definitely");
    assert_eq!(
        crate::common::undecided_causes(&mut kb, "wicynpe.absentLater"),
        vec![vec![UnknownCause::Unreduced]],
    );
}

// ── a waiting goal is not asked again ─────────────────────────────────────────────────────

/// `Int64.gt(?z, 0)` waits on `?z`, which nothing binds, while its three siblings make
/// progress one at a time — each binds what the next one waits on. It is asked ONCE: the
/// difference between the clause with it and without it. Counted, not timed. Asked from
/// scratch on every turn, it was asked 4 times — once, then again after each sibling's
/// progress. The answers are the control: `chainBare` binds `?a = 3`, and `chain` is
/// conditional on the goal that never ran.
#[test]
fn a_suspended_goal_is_asked_once() {
    let mut kb = kb();
    assert_eq!(crate::common::one_definite_int(&mut kb, "wicynpe.chainBare"), Some(3));
    let (sols, _) = resolve(&mut kb, "chain");
    assert_eq!(sols.len(), 1);
    assert!(!sols[0].is_definite(), "`?z` is never bound");
    let with = asked(&mut kb, "chain");
    let without = asked(&mut kb, "chainBare");
    assert_eq!(with, without + 1, "asked {with} vs {without}: the waiting goal is asked once");
}

/// An UNREDUCED goal is never asked again — not even once a sibling binds a variable it
/// holds (`?c`): no binding makes an implementation reachable. Suspended on its variables
/// instead, it was asked a second time when `?c` was bound.
#[test]
fn a_parked_goal_is_never_asked_again() {
    let mut kb = kb();
    assert_eq!(crate::common::one_definite_int(&mut kb, "wicynpe.parkedBare"), Some(3));
    let (sols, _) = resolve(&mut kb, "parked");
    assert_eq!(sols.len(), 1);
    let causes: Vec<UnknownCause> = sols[0].undecided.iter().map(|(_, c)| *c).collect();
    assert_eq!(causes, vec![UnknownCause::Unreduced]);
    let with = asked(&mut kb, "parked");
    let without = asked(&mut kb, "parkedBare");
    assert_eq!(with, without + 1, "asked {with} vs {without}: the parked goal is asked once");
}

// ── CONTROLS ──────────────────────────────────────────────────────────────────────────────

/// The call's argument is bound before it runs: `blue`, before this ticket and after.
#[test]
fn control_a_call_whose_argument_is_bound_first() {
    let mut kb = kb();
    assert_eq!(rows(&mut kb, "early"), vec![("blue".to_string(), true)]);
}

/// `Colour.score(x) = 3` delayed through `=`'s own path before this ticket: `blue` either way.
#[test]
fn control_the_value_form_of_the_same_call() {
    let mut kb = kb();
    assert_eq!(rows(&mut kb, "lateEq"), vec![("blue".to_string(), true)]);
}

/// With the instance named, the call runs: `3` either way.
#[test]
fn control_a_supplied_call_runs() {
    let mut kb = kb();
    assert_eq!(crate::common::one_definite_int(&mut kb, "wicynpe.convTagReq"), Some(3));
}
