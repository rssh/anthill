//! WI-20260826-VPEWK — A HOST-IMPLEMENTED OPERATION REDUCES IN A RULE BODY.
//!
//! Before this ticket a host-backed operation reduced in an OPERATION BODY and
//! nowhere in a RULE — neither at a goal nor at an operand — and the two headline
//! facts of the ticket that measured it were each half right:
//!
//!   * `:- Bool.and(true, true)` DID answer 1, so the ticket read the goal position
//!     as working. It answers through the CONNECTIVE reading, not a host call:
//!     `Bool.and` at goal arity 2 is position-directed to `anthill.kernel.and`
//!     (`kb/mod.rs`'s `POSITION_DIRECTED_BOOLEANS`) and resolved by `push_and`, which
//!     splices two GOALS into the frame. No host function runs. Measured: that row
//!     answers 1 with this ticket's change backed out.
//!   * `:- Bool.and(true, true) = true` answered NOTHING, which the ticket diagnosed
//!     as an OPERAND-vs-GOAL split. It is not that either. The separator is which
//!     REGISTRY holds the host function — see the two rows in
//!     `a_migrated_registration_is_visible_to_the_gate` below (named
//!     `a_hardcoded_registration_is_still_invisible_to_the_gate` until WI-880 migrated
//!     the eight it pinned; its rows now carry the flipped values).
//!
//! WHAT THE DEFECT ACTUALLY WAS. WI-20260822-J38JE widened the goal-side ENTRY gate
//! (`op_reducible_in_rule_body` = a body OR `is_interpreter_mapped_op`) so a host op
//! could take the WI-580/WI-938 relational view. But that view is IMPLEMENTED by
//! routing the goal to `eq(f(args), true)` — i.e. into the OPERAND path — and that
//! path still asked `reduce_op_value(.., dispatch_body_less: false)`, "a body and
//! nothing else". So J38JE's widening admitted host ops through a door that opened
//! onto a wall, and was INERT for every host op that is not one of the three
//! position-directed connectives. `String.contains` is the witness: it is
//! `operation_map`ped, so the widened entry gate accepts it, and it answered NOTHING
//! at BOTH positions until `reduce_op_value` gained its own host arm.
//!
//! CONTROLS — TWO SEPARABLE BACK-OUTS, because the change has two halves and one
//! back-out cannot measure both. Each was RUN, not reasoned about.
//!
//!   1. THE HOST ARM in `reduce_op_value` (`None if self.host_op_reducible_at_a_value(op)`),
//!      disabled as `None if false && …`. FAILS: `a_host_backed_bool_op_reduces_at_an_operand`
//!      (all three positive rows drop to 0), `a_mapped_host_op_answers_at_both_positions`
//!      (`goalT` AND `opT` both drop to 0 — the row that says the defect was never
//!      operand-vs-goal), `an_unground_host_operand_suspends_rather_than_answering`
//!      (`gnd` drops to 0), the `pure` row of the effect test, and
//!      `a_migrated_registration_is_visible_to_the_gate` — which, when this control was
//!      run, reached that file through its `has` CONTROL row alone (the mapped sibling
//!      that must answer), its other rows being about ops the arm never reached. Since
//!      WI-880 migrated those ops the whole test reaches the arm. Measured: 5 of the 6
//!      tests fail.
//!      PASSES EITHER WAY: `symbolic_algebra_at_an_operand_is_still_left_as_data`
//!      ALONE, and by design — every row in it pins what the arm must NOT reach, so
//!      there is nothing in it for a back-out to break. That is what makes it a
//!      control rather than a measurement.
//!   2. THE EFFECT CLAUSE inside `host_op_reducible_at_a_value` (the `sig.effects.is_empty()`
//!      conjunct). FAILS: only `an_effectful_host_op_does_not_run_at_an_operand`, whose
//!      `fx` row answers 1 instead of 0. Every other test in this file passes with the
//!      clause gone, which is exactly why that test exists — the whole-arm back-out above
//!      cannot see this half at all.
//!
//! A third back-out, the host leg of `is_unreduced_op_call`, is measured at its own site
//! rather than here: without it the unground row answers `no solutions` (a decided FALSE)
//! instead of suspending, which `an_unground_host_operand_suspends_rather_than_answering`
//! catches on its `total` assertion and nothing else in the workspace does.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// DEFINITE solutions only — `.len()` counts FLOUNDERED ones too, and for a
/// CONDITION a suspension is the one answer that must not read as success. Same
/// counter, and the same reason, as `wi_j38je_boolean_goal_test`'s.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// TOTAL solutions, definite + floundered. Paired with [`answers`] it separates
/// "decided false" from "suspended", which is the whole of the unground row below.
fn total(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The ticket's own table: a host-backed `Bool` operation at an OPERAND.
///
/// BOTH POLARITIES on every row, so each measures the COMPUTATION and not merely
/// that something reduced. A row that only asserted `and(true, true) = true` answers
/// 1 would pass equally if the arm reduced every call to `true`.
#[test]
fn a_host_backed_bool_op_reduces_at_an_operand() {
    let mut kb = crate::common::load_kb_with(
        "namespace vpewka\n  import anthill.prelude.{Bool}\n  \
         rule andT(1)  :- Bool.and(true, true) = true\n  \
         rule andF(1)  :- Bool.and(true, false) = true\n  \
         rule orT(1)   :- Bool.or(false, true) = true\n  \
         rule orF(1)   :- Bool.or(false, false) = true\n  \
         rule notT(1)  :- Bool.not(false) = true\n  \
         rule notF(1)  :- Bool.not(true) = true\nend\n",
    );
    for (pred, want) in [
        ("andT", 1),
        ("andF", 0),
        ("orT", 1),
        ("orF", 0),
        ("notT", 1),
        ("notF", 0),
    ] {
        assert_eq!(
            answers(&mut kb, &format!("vpewka.{pred}(1)")),
            want,
            "`{pred}`: a host-backed Bool op at an operand must DECIDE. Every row \
             here answered 0 before the `host_op_reducible_at_a_value` arm — including \
             the ones that must answer 0, which is why both polarities are asserted"
        );
    }
}

/// THE CONTROL THAT SAYS THE GATE IS NOT "DISPATCH BODY-LESS OPS TOO".
///
/// `reduce_op_value`'s `dispatch_body_less` flag protects SYMBOLIC ALGEBRA: an
/// operand is a term a RULE WROTE, and a body-less spec op there may be data rather
/// than a computation. `anthill.prelude.Set`'s `insert` / `empty` are the named
/// case — parametric parent, no body, a real signature, and the terms the membership
/// rules resolve over; reducing them would destroy the data (the five wi616
/// regressions `is_unreduced_op_call` records, through the other door).
///
/// The host arm cannot reach them: `Set` has no `operation_map` and no hardcoded
/// registration, so `is_interpreter_mapped_op` answers FALSE and the flag's own arm
/// still owns every op it owned before.
///
/// PASSES EITHER WAY BY DESIGN — that is the point of a control. It is here to fail
/// if a future widening replaces the predicate with "body-less", which is the one
/// change that would look like a simplification and would silently reduce data.
#[test]
fn symbolic_algebra_at_an_operand_is_still_left_as_data() {
    let mut kb = crate::common::load_kb_with(
        "namespace vpewkb\n  import anthill.prelude.{Set, Int64}\n  \
         rule same(1) :- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1)\n  \
         rule diff(1) :- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 2)\nend\n",
    );
    assert_eq!(
        answers(&mut kb, "vpewkb.same(1)"),
        1,
        "two structurally identical `Set.insert` terms are EQUAL AS DATA — the \
         operand path must not dispatch them"
    );
    assert_eq!(
        answers(&mut kb, "vpewkb.diff(1)"),
        0,
        "…and different data is not equal: the row above is not vacuous"
    );
}

/// THE ROUTE J38JE OPENED, NOW REACHABLE. `String.contains` is `operation_map`ped
/// (`rustland/anthill-stl/anthill/string.anthill`), Bool-returning, rule-less and
/// effect-free — every clause `bare_bodied_bool_relation` asks — so J38JE's widened
/// entry gate admits it to the relational view. The view routes the goal to
/// `eq(f(args), true)`, so before this ticket the GOAL row answered nothing too.
///
/// This is the row that separates this ticket's diagnosis from the one the ticket
/// was filed with: it is not an operand-vs-goal split, because BOTH positions were
/// broken for this op and both are fixed by one arm in the operand path.
#[test]
fn a_mapped_host_op_answers_at_both_positions() {
    let mut kb = crate::common::load_kb_with(
        "namespace vpewkc\n  import anthill.prelude.{String, Bool}\n  \
         rule goalT(1) :- String.contains(\"abc\", \"b\")\n  \
         rule goalF(1) :- String.contains(\"abc\", \"z\")\n  \
         rule opT(1)   :- String.contains(\"abc\", \"b\") = true\n  \
         rule opF(1)   :- String.contains(\"abc\", \"z\") = true\nend\n",
    );
    for (pred, want) in [("goalT", 1), ("goalF", 0), ("opT", 1), ("opF", 0)] {
        assert_eq!(
            answers(&mut kb, &format!("vpewkc.{pred}(1)")),
            want,
            "`{pred}`: a MAPPED host op decides at both positions. MEASURED with the \
             arm backed out: `goalT` and `opT` both answered 0, which is what says \
             J38JE's entry widening was inert without this"
        );
    }
}

/// AN UNGROUND OPERAND SUSPENDS. It does not answer, and it does not silently
/// vanish: the call residualizes (`bridge_op_to_eval` returns `None` on a non-ground
/// argument, and `unwrap_or(v)` puts the ORIGINAL call back), the `eq` delays, and
/// the search flounders. `total` sees the floundered solution, `answers` does not.
///
/// This is the WI-519 residual discipline, and it is the reason the host arm is safe
/// to admit at any depth: an argument the bridge cannot ground never produces a
/// confident wrong answer, only a suspension.
#[test]
fn an_unground_host_operand_suspends_rather_than_answering() {
    let mut kb = crate::common::load_kb_with(
        "namespace vpewkd\n  import anthill.prelude.{Bool}\n  \
         rule ung(?b)  :- Bool.and(?b, true) = true\n  \
         rule gnd(1)   :- Bool.and(true, true) = true\nend\n",
    );
    assert_eq!(
        answers(&mut kb, "vpewkd.ung(?b)"),
        0,
        "an unground operand decides NOTHING — `=` is `PartialEq.eq`, a test that \
         never binds (§8.3), so `?b` is not solved for"
    );
    assert!(
        total(&mut kb, "vpewkd.ung(?b)") > 0,
        "…and it SUSPENDS rather than failing: the floundered solution is present, \
         which is what distinguishes a delay from a decided `false`. This is the \
         half a `.len()`-based counter would have blessed as an answer"
    );
    assert_eq!(
        answers(&mut kb, "vpewkd.gnd(1)"),
        1,
        "CONTROL: the same call GROUND decides, so the row above measures \
         groundness and not a dead rule"
    );
}

/// THE UNSOUNDNESS THIS FILE PINNED IS GONE, AND WHAT REMAINS IS A SUSPENSION.
///
/// VPEWK wrote this test "to FAIL when either lands, which is the intent", and WI-880
/// landed the first: `String.concat` / `length` / `startsWith` / … are `operation_map`
/// entries now, so `op_is_interpretable` sees them and they reduce. The rows below are
/// the SAME rows with the flipped values, kept rather than deleted because the pairing
/// is what says which of the two remainders moved.
///
/// WHAT THE ROW USED TO SAY, and it was the whole reason WI-880 was a correctness item:
/// WI-884 split the host surface in two, `String.contains` named by an `operation_map`
/// clause and `String.concat` registered by hardcoded qualified name in
/// `eval/builtins.rs`. `is_unreduced_op_call` did not recognize the hardcoded half, so
/// `eq` compared the CALL to `"ab"` STRUCTURALLY and committed — `String.concat("a","b")
/// = "ab"` was DECIDED FALSE, and `not(…)` over it answered **1 DEFINITE**, a positive
/// answer out of a call that never ran. The WI-738 soundness floor, missing for this
/// class. MEASURED both ways here: `cat` 0 -> 1, `ncat` 1 -> 0, `len` 0 -> 1.
///
/// WHAT IS STILL NOT REDUCED — A HOST CALL NESTED IN A HOST CALL'S ARGUMENT.
/// `reduce_op_value` σ-walks each argument to a `Value` but does not REDUCE an argument
/// that is itself an op-call, so the bridge sees a `Value::Node` and its ground check
/// declines. (A host call nested in a BODIED op's body DOES reduce — that path recurses
/// through `reduce_op_value` at `depth + 1` — which is the `deep` row.) This one is a
/// SUSPENSION and always was: the residual is present (`total > 0`) and its negation
/// suspends too, which is why every row asserts `total` beside `answers` — the two
/// remainders were never the same kind, and an earlier draft of this doc said they were.
///
/// `has` IS STILL THE CONTROL and now passes for a reason it shares with its siblings
/// rather than against them: it was the MAPPED sibling that answered while the hardcoded
/// ones did not, and the separator it isolated — the REGISTRY, not the sort, not the
/// position — is exactly what WI-880 removed by putting the whole surface in one
/// registry. It keeps its row so a REGRESSION that un-migrated the eight would show up
/// as the old split rather than as a uniform failure.
#[test]
fn a_migrated_registration_is_visible_to_the_gate() {
    let mut kb = crate::common::load_kb_with(
        "namespace vpewke\n  import anthill.prelude.{Bool, String, Int64}\n  \
         operation inner() -> Bool = Bool.or(false, true)\n  \
         rule cat(1)   :- String.concat(\"a\", \"b\") = \"ab\"\n  \
         rule ncat(1)  :- not(String.concat(\"a\", \"b\") = \"ab\")\n  \
         rule len(1)   :- String.length(\"abc\") = 3\n  \
         rule has(1)   :- String.contains(\"abc\", \"b\") = true\n  \
         rule nest(1)  :- Bool.and(Bool.not(false), true) = true\n  \
         rule deep(1)  :- inner() = true\nend\n",
    );
    assert_eq!(
        answers(&mut kb, "vpewke.cat(1)"),
        1,
        "`String.concat` rides an `operation_map` clause since WI-880, so \
         `is_interpreter_mapped_op` sees it and the call REDUCES. It answered 0 under \
         WI-884's split — back the eight mappings out and this returns to 0"
    );
    assert_eq!(
        total(&mut kb, "vpewke.cat(1)"),
        1,
        "…the one answer is DEFINITE, with no residual beside it. The pairing is what \
         separates 'reduced and true' from 'suspended', which `answers` alone cannot"
    );
    assert_eq!(
        answers(&mut kb, "vpewke.ncat(1)"),
        0,
        "AND THE UNSOUNDNESS IS GONE. This row answered 1 DEFINITE — a positive answer \
         out of a call that never ran, because `eq` compared the un-reduced CALL to \
         \"ab\" structurally and committed. The call runs now, so its negation is false"
    );
    assert_eq!(
        answers(&mut kb, "vpewke.len(1)"),
        1,
        "…and so does `String.length`, the second of the migrated eight"
    );
    assert_eq!(
        answers(&mut kb, "vpewke.has(1)"),
        1,
        "CONTROL, and the row that makes the two above mean something: the MAPPED \
         sibling in the same file answers. The separator is the registry, not the \
         sort, not the position, and not `String`"
    );
    assert_eq!(
        answers(&mut kb, "vpewke.nest(1)"),
        0,
        "a host call in a host call's ARGUMENT is not reduced — the argument is \
         σ-walked, never reduced, so the bridge's ground check declines and the call \
         residualizes"
    );
    assert!(
        total(&mut kb, "vpewke.nest(1)") > 0,
        "…and unlike `cat` it genuinely SUSPENDS — the residual is present. This is \
         the row that makes the two remainders distinguishable rather than both \
         reading as `0`"
    );
    assert_eq!(
        answers(&mut kb, "vpewke.deep(1)"),
        1,
        "CONTROL: the same nesting through a BODIED op DOES reduce — \
         `reduce_op_value` recurses over the folded body at `depth + 1`. So the row \
         above is about argument reduction, not about depth"
    );
}

/// AN EFFECTFUL HOST OPERATION DOES NOT RUN IN A RULE BODY — the clause
/// WI-20260822-ZJZS7 item 2 asked to have confirmed, and it did NOT hold for free.
///
/// The GOAL side has always stated it (`bare_bodied_bool_relation`: "an effectful body
/// is not a logical relation, and the eval bridge's empty effect registry would suspend
/// on one anyway"). The second half of that reason does not carry over to a HOST
/// function: a bodied op RAISES its effect while the bridge evaluates the body, so the
/// bridge's `Err(_) => None` arm catches it — but a host function is opaque Rust that
/// simply runs, raises nothing, and its declared `effects` row is the only thing between
/// a rule body and a real side effect.
///
/// THE FIXTURE MAPS BOTH OPERATIONS TO THE SAME HOST FUNCTION, so the ONLY difference
/// between the two rows is the `effects` row. A fixture that gave them different host
/// functions would confound "the effect row was read" with "that function behaves
/// differently". MEASURED before the effect clause: BOTH answered 1 — the row was inert.
///
/// WHY `Error` AND NOT A STATE EFFECT. A `Modify[p]` operation cannot be reached from a
/// rule body with a literal argument at all — the typer refuses the CALL at load ("expected
/// an argument naming a PLACE … got a literal"), so the state-effect hazard is already
/// guarded one rung up and there is no row to drive here. `Error` is the effect a rule body
/// can actually reach, which makes it the one this gate is really about.
///
/// AND IT IS THE ROW MOST LIKELY TO CHANGE. USER DIRECTION 2026-08-27: "error effect we can
/// allow (and handle error by erroring rule)" — i.e. `Error` is a FAILURE CHANNEL, not a
/// state effect, and refusing it here is conservative rather than principled. Deliberately
/// not done in this ticket (deciding what "erroring rule" means for SLD — fail the clause,
/// or propagate — is a semantics question, not a gate tweak) and filed as
/// WI-20260827-NFXPZ, which also has to answer what an erroring operand under
/// `not(...)` means: under a fail reading it SUCCEEDS, turning a host error into a
/// positive answer.
/// This row is written to FAIL when that lands, which is the intent: the gate becomes
/// "no effects EXCEPT `Error`" and the assertion below becomes 1.
#[test]
fn an_effectful_host_op_does_not_run_at_an_operand() {
    let mut kb = crate::common::load_kb_with(
        "namespace vpewkf\n  import anthill.prelude.{String}\n  \
         sort MyS\n    \
           operation trimIt(s: String) -> String\n    \
           operation trimFx(s: String) -> String\n      effects {Error}\n  end\n  \
         provides MyS language rust\n    artifact \"scratch\"\n    \
           carrier { MyS: \"String\" }\n    \
           operation_map {\n      trimIt: \"string_trim\",\n      trimFx: \"string_trim\"\n    }\n  end\n  \
         rule pure(1) :- MyS.trimIt(\"  a  \") = \"a\"\n  \
         rule fx(1)   :- MyS.trimFx(\"  a  \") = \"a\"\nend\n",
    );
    assert_eq!(
        answers(&mut kb, "vpewkf.pure(1)"),
        1,
        "CONTROL: the PURE operation runs its host function at an operand. Without \
         this row the one below would pass on a fixture that simply never worked"
    );
    assert_eq!(
        answers(&mut kb, "vpewkf.fx(1)"),
        0,
        "…and the SAME host function behind an operation declared `effects {{Error}}` \
         does NOT run. The only difference between the two rules is the effect row"
    );
}

/// ONE EQUATION MUST NOT HAVE TWO VERDICTS DEPENDING ON OPERAND ORDER.
///
/// Found by /code-review on this ticket's own diff, and the whole workspace was green
/// with the defect in — nothing else covers it. `is_unreduced_op_call` gained a HOST leg
/// (right for the DELAY question `eq` asks) and `op_call_as_occ`'s `Value::Node` arm
/// DELEGATES to that predicate to pick `unfold_eq_operand`'s case-split SUBJECT — a
/// different question, which needs a body to unfold. So a host operand was chosen as the
/// subject, `folded_call_match` bailed at its own `op_has_runnable_body`, and the whole
/// unfold returned `None`, ABANDONING the split the OTHER operand would have served.
/// Literally the WI-1040 defect that arm's own comment records, reached one door over.
///
/// MEASURED with the guard removed from that arm:
///   `String.contains(..) = Colour.isRed(?c)`  →  1 solution, CONDITIONAL
///   `Colour.isRed(?c) = String.contains(..)`  →  1 solution, DEFINITE
/// The asymmetry IS the bug: `eq` is symmetric, so the two rows must agree.
#[test]
fn an_eq_between_a_host_call_and_a_bodied_call_does_not_depend_on_operand_order() {
    let mut kb = crate::common::load_kb_with(
        "namespace vpewkg\n  import anthill.prelude.{String, Bool}\n  \
         sort Colour\n    entity red\n    entity green\n    \
           operation isRed(c: Colour) -> Bool =\n      match c\n        \
             case red() -> true\n        case green() -> false\n  end\n  \
         rule hostFirst(?c)   :- String.contains(\"abc\", \"b\") = Colour.isRed(?c)\n  \
         rule bodiedFirst(?c) :- Colour.isRed(?c) = String.contains(\"abc\", \"b\")\nend\n",
    );
    let (hf, bf) = (
        answers(&mut kb, "vpewkg.hostFirst(?c)"),
        answers(&mut kb, "vpewkg.bodiedFirst(?c)"),
    );
    assert_eq!(
        hf, bf,
        "`eq` is SYMMETRIC: writing the host call first must not change the verdict. \
         Asserted as an EQUALITY rather than against a literal, because what is wrong \
         when this fails is the DISAGREEMENT — pinning either side to a number would \
         also fail if both moved together for an unrelated reason, and would say the \
         wrong thing about why"
    );
    assert_eq!(
        hf, 1,
        "…and both DECIDE rather than both suspending, which is what says the rows \
         agree because the unfold ran and not because it was abandoned twice"
    );
}
