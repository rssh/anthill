//! WI-1043 — a RULE BODY naming a BODY-LESS spec op must be decided like the same call
//! in an operation body: pinned to the implementation the carrier supplies, and REFUSED
//! at load when two texts supply one (058 §3.7 / §4.9, WI-1027's half).
//!
//! WI-1026 admitted only the DEFAULTED half to the rule-body dispatch walk, on the
//! reasoning that a body-less op "has no default to shadow, so `reduce_op_value` leaves
//! it un-ground and the goal residualizes rather than answering wrongly". Residualizing
//! IS the wrong answer, and the row that said otherwise was fixture contamination: the
//! REFUSED that `wi1035`'s table claimed for this shape came from the `wi1027` probe
//! OPERATION sitting in the same program, not from the rule.
//!
//! MEASURED before any code changed, every supply shape, one rule body
//! (`rule answer(?r) :- Desc.describe(leaf(), ?r)`) and its operation-body twin:
//!
//! | suppliers | rule body | operation body | | after |
//! |---|---|---|---|---|
//! | own member + provision | `[]` | `7` | → | `7` / unchanged |
//! | witness sort alone | `[]` (qualified) / **refused** (dot) | `9` | → | `9` / unchanged |
//! | instance fact alone | `[]` | `9` | → | `9` — closed by **WI-1057**, below |
//! | own member + instance fact | `[]` | REFUSED | → | **REFUSED** / unchanged |
//! | own member + witness | `[]` | REFUSED | → | **REFUSED** / unchanged |
//! | own member, NO provision | `[]` | loads, `OperationBodyMissing` at the CALL | → | **REFUSED at load** |
//!
//! Row 2's dot column is not a typo and is the second defect this ticket found: that
//! spelling has been typed since WI-282, so it already reached the rule-body requirement
//! check and was REFUSED — a legal program, whose operation-body twin answers 9. See
//! `a_witness_supplied_carrier_answers_through_both_spellings`.
//!
//! ## The three pieces, and what each is for
//!
//! * **The walk gate** (`call_dispatch_shape` → `spec_op_call_parent`) admits the
//!   body-less half, so the call reaches `check_apply_iter`'s WI-210 block and the
//!   WI-1027 supplier-tie guard that lives above its outcome arms. That is the whole of
//!   the LOAD face.
//! * **The goal shape** (`dispatched_relation_arity`) reads the typer's PIN. Without it
//!   the pin is written, carried and never consulted: `functional_relation_arity` asks
//!   "has a runnable body?" of the SPELLED functor, and a body-less spec op has none, so
//!   the goal `f(a…, ?r)` never became the call `f(a…)` that `reduce_op_value` folds.
//!   Row 1 answers `[]` with the pin present and `7` with this line.
//! * **The witness escape** (`carrier_provided_by_witness`) keeps the newly-typed
//!   arguments from feeding the rule-body requirement check a question it answers wrongly
//!   — `sort_provides` walks the CARRIER's own out-edges and a witness provision is filed
//!   under the witness. This one FIXES A PRE-EXISTING REFUSAL as well as preventing a new
//!   one; see row 2.
//!
//! ## What this ticket did NOT report — and what WI-1056 then did
//!
//! An `=` goal loads as a call on `PartialEq.eq`, so body-less spec ops are what rule
//! bodies are largely MADE of: the gate newly decides **133** call sites on a whole-corpus
//! load (28 on stdlib + host bindings alone). Rule bodies had never been type-checked, and
//! typing those atoms surfaced **19 leaf errors**, rendering as 7 load errors in 4 files —
//! **none of them a dispatch verdict**, all of them programs that loaded and ran. THIS
//! ticket therefore reported only the two TIES from this shape, and only for the call it
//! was deciding.
//!
//! **WI-1056 has since decided all 7 and widened the policy**, so a body-less atom now
//! reports every failure its type-check finds: two were typer gaps (an eponymous /
//! free-standing entity CONSTRUCTOR applied in a rule body; a same-base PARTIAL type
//! application refused against a fuller one), one was a source error in
//! `stdlib/anthill/prelude/bigint.anthill`, and the rest are the standing WI-282
//! unresolved-receiver exemption. See `wi1056_rule_body_type_check_test` and
//! `dispatch_calls_in_occ`'s doc. What remains narrowed is the general `Expr::Apply`
//! (**WI-1058**).
//!
//! ## What fails if this is backed out — MEASURED per piece, one revert each, four runs
//!
//! | test | gate | goal shape | witness escape | recursion |
//! |---|---|---|---|---|
//! | `a_body_less_rule_body_tie_is_refused_at_load` | **FAILS** (loads clean, `[]`) | ok | ok | ok |
//! | `a_witness_rival_tie_carries_the_witness_repair` | **FAILS** | ok | **FAILS** | ok |
//! | `the_rule_body_refusal_shares_the_operation_bodys_message` | **FAILS** | ok | ok | ok |
//! | `one_supplier_answers_the_supplied_impl_in_a_rule_body` | **FAILS** (`[]`) | **FAILS** (`[]`) | ok | ok |
//! | `a_witness_supplied_carrier_answers_through_both_spellings` | **FAILS** | **FAILS** | **FAILS** | ok |
//! | `a_carrier_with_no_instance_is_refused_at_load` | **FAILS** (loads clean) | ok | ok | ok |
//! | `the_walk_gate_is_exactly_the_two_halves` | ok | ok | ok | ok |
//! | `a_tie_nested_in_an_eq_goal_is_reported_once` | **FAILS** (the qualified arm loads clean) | ok | ok | ok |
//! | `wi282…::rule_body_dot_no_such_member_errors` | ok | ok | ok | **FAILS** |
//! | `wi557…::rule_body_definite_precondition_violation_is_rejected` | ok | ok | ok | **FAILS** |
//!
//! The four columns are the four pieces: the walk GATE (`call_dispatch_shape`'s Apply arm
//! back to the defaulted half), the GOAL SHAPE (`dispatched_relation_arity` back to
//! `functional_relation_arity`), the WITNESS ESCAPE (the third filter clause), and the
//! RECURSION (`CallDispatch::BodyLessSpecOp` walking into its own children).
//!
//! `the_walk_gate_is_exactly_the_two_halves` is ok in every column BY DESIGN, and the
//! first version of this table predicted otherwise — it pins the GATE FUNCTION, not any
//! reader of it, so reverting a reader cannot move it. What does: a clause added to
//! `spec_op_call_parent` that neither half has. That is the drift it exists for.
//!
//! The last two rows are not this file's tests — they are the delivered rule-body
//! diagnostics (a member-not-found on a KNOWN receiver, WI-282; a definite value-
//! precondition violation, WI-602) that the gate's FIRST cut SWALLOWED, by handing the
//! whole `eq(?v, ?p.bogus)` atom to `type_check_node` under a tie-only error policy.
//! MEASURED as two full-suite failures, which is how the recursion clause was found.
//!
//! ## WI-1057 — the fourth row, and why it needed a different mechanism
//!
//! The table above has four columns because WI-1043's four pieces all turn on the
//! typer's PIN. Row 3 has no pin: `dispatch_spec_op_cached` does not read a WI-431
//! instance fact's op-binding, so an implementation supplied only that way is
//! discoverable BY VALUE, at eval. WI-1057 closed it with four more pieces, each
//! keyed to one early return, and its two tests state their own controls at their
//! sites (they are not columns here — reverting any WI-1043 piece leaves both alone):
//!
//! * **the goal shape** (`body_less_relation_arity`) admits a body-less spec op on the
//!   SPELLED functor, since there is no pin to redirect to. Kept OFF
//!   `functional_relation_arity`, which also gates WI-1040's dictionary weave.
//! * **the reduction** (`reduce_op_value`) stops bailing on a body-less op and runs it
//!   through the eval bridge instead.
//! * **the host entry** (`invoke_op_with_requirements`) gains the value-directed
//!   escape the in-body path had at its step 3b — the bridge calls the host entry, so
//!   without this the rule body asked the one crossing that could not answer.
//! * **the hook's guard** (`reduction_left_body_less_call`) keeps an UNDECIDED call
//!   from being `unify`d with the result variable. This is the piece that makes the
//!   naive widening safe, and it is deliberately NOT a clause in
//!   `is_unreduced_op_call` — folding the two broke 5 `wi616_semantic_eq_test` cases,
//!   because `Set.insert`/`Set.empty` are body-less spec ops that are symbolic ALGEBRA.
//!
//! WI-1057 ALSO lowered `BRIDGE_REENTRY_CAP` (32 → 16). Not housekeeping: the host
//! entry sits on the eval↔SLD bridge path, and at 32 that recursion already consumed
//! essentially ALL of libtest's default 2 MiB thread stack. Deepening each crossing
//! did not fail a test — it ABORTED the whole `wi_tests` binary with a native stack
//! overflow, reporting 2463 tests as nothing. See the constant's own doc.
//!
//! WI-1057's own back-out table — MEASURED, one revert each, five runs:
//!
//! | test | goal shape | reduction | host entry | hook guard | cap |
//! |---|---|---|---|---|---|
//! | `a_fact_route_supplier_answers_from_a_rule_body` | **FAILS** | **FAILS** | **FAILS** | ok | ok |
//! | `an_unground_body_less_goal_binds_no_residual` | ok | ok | ok | **FAILS** | ok |
//! | `wi625…::eval_undecidable_instance_fact_eq_is_loud_not_false` | ok | ok | ok | ok | **ABORTS** |
//!
//! Re-driven after this ticket's /code-review moved three of the five (the reduction
//! behind `reduce_dispatched_goal_call`, the rule-less clause into
//! `body_less_dispatchable`, the woven bypass under the same guard): same five cells.
//!
//! The first three columns are the three early returns between the goal and the
//! implementation, so the headline test cannot separate them — each alone is fatal to
//! it. The hook guard is the one piece it CANNOT see (there the bridge answers, so no
//! undecided call ever reaches the guard), which is why the second test exists. Every
//! WI-1043 column above leaves both of these alone, and these five leave every
//! WI-1043 row alone.
//!
//! REFERENCE: WI-1027; WI-1026; WI-1035; WI-1012; WI-1010; WI-444; WI-450; WI-1056;
//! WI-1057; WI-431; WI-625; WI-842; WI-938; `docs/design/058-implementation.md` §3.7,
//! §14, §21, §23.

use anthill_core::intern::Symbol;
use anthill_core::kb::op_info::all_operation_params;
use anthill_core::kb::typing::{
    defaulted_spec_op_parent, lookup_spec_op_dispatch, spec_op_call_parent,
};
use anthill_core::kb::KnowledgeBase;

/// SIBLING-MODULE REUSE, the house pattern in this cluster: the BODY-LESS builder is
/// `wi1035`'s (whose subject is the same program's DOT spelling), the two-supplier
/// constants are `wi1026`'s and `wi1027`'s, and the load-refusal / answer helpers are
/// `wi1012`'s and `wi1026`'s. Copying any of them would let this file's fixture drift
/// away from the one whose measurements this file's header cites.
use crate::wi1010_defaulted_op_instance_fact_test::probe;
use crate::wi1012_static_supplier_tie_test::{located, refusal};
use crate::wi1026_rule_body_spec_op_dispatch_test::{
    answer, TWO_LEAF as OWN, TWO_SUPPLY as RIVAL_FACT,
};
use crate::wi1027_bodyless_supplier_tie_test::{assert_supplier_tie, RIVAL_WITNESS};
use crate::wi1035_dot_member_supplier_tie_test::body_less;

/// THE CALL SITES. The qualified rule body is this ticket's subject; the operation body
/// is the face it must agree with, and the dot is the third spelling WI-1035 closed.
const QUAL_RULE: &str = "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n";
const QUAL_OP: &str = "  operation probe() -> Int64 = Desc.describe(leaf())\n";
const DOT_RULE: &str = "  rule answer(?r) :- leaf().describe(?r)\n";

/// `Leaf` declares its own runnable member and NO provision — so nothing makes it an
/// instance of `Desc`. Distinct from [`OWN`], which carries `provides Desc[T = Leaf]`.
const OWN_NO_PROVISION: &str = "    operation describe(x: Leaf) -> Int64 = 7\n";

/// `Leaf` declares NOTHING: no member and no provision of its own, so every supplier in
/// the fixture comes from the `supply` slot. Not `wi1035`'s `NO_OWN` (`provides Desc[T =
/// Leaf]` with no member), which the WI-818 backing check refuses on a BODY-LESS spec op
/// — a provision with no default and no own member backs nothing.
const NO_SUPPLIER_LEAF: &str = "";

/// THE HEADLINE. Two suppliers of a BODY-LESS spec op, reached from a rule body with no
/// operation anywhere in the program — the subtraction that makes this measure the rule
/// and not a probe (the contamination that put a REFUSED in `wi1035`'s table for a row
/// that answered `[]`).
///
/// Asserted as a LOAD refusal, not by re-driving: once refused there is no KB to query,
/// and "the query returns nothing" is the symptom this ticket exists to stop.
#[test]
fn a_body_less_rule_body_tie_is_refused_at_load() {
    let ns = "test.wi1043.tie";
    let msg = refusal(&body_less(ns, OWN, RIVAL_FACT, QUAL_RULE));
    assert_supplier_tie(
        &msg,
        ns,
        &format!("an instance fact binding `describe = {ns}.otherDescribe`"),
    );
}

/// ROUTE 3 through a rule body, and the only shape that reaches
/// `SupplierTieRepair::NameableWitness` here: a body-less op HAS the dispatch slot a
/// `[Desc = Rival]` bracket binds, so the repair must say so rather than inherit "keep
/// exactly one" — carried from the candidates, not assumed at the raising site.
#[test]
fn a_witness_rival_tie_carries_the_witness_repair() {
    let ns = "test.wi1043.witnesstie";
    let msg = refusal(&body_less(ns, OWN_NO_PROVISION, RIVAL_WITNESS, QUAL_RULE));
    assert_supplier_tie(&msg, ns, &format!("witness sort '{ns}.Rival'"));
    assert!(
        msg.contains("route the call through an operation that can write `[Spec = Witness]`"),
        "a witness rival on a BODY-LESS op is nameable at a bracket-capable call: {msg}",
    );
    // ONE refusal, not the tie plus a spurious second. The first cut of the witness
    // escape was absent and this program reported `missing requires Desc[T = …]`
    // alongside the tie — the same false positive `a_witness_supplied_carrier_…` drives
    // in its one-supplier form, where it is the difference between refusing a legal
    // program and running it.
    assert_eq!(
        msg.lines().count(),
        1,
        "the rule-body face must raise the tie and nothing else: {msg}",
    );
}

/// ONE REFUSAL, TWO FACES. The rule body and the operation body must produce the same
/// message body, each located at ITS OWN call — the invariant WI-1026 made for the
/// defaulted half, on the half it left.
#[test]
fn the_rule_body_refusal_shares_the_operation_bodys_message() {
    // One namespace for both, so the qualified names inside match and any difference
    // left is a difference of WORDING.
    let ns = "test.wi1043.faces";
    let rule_msg = refusal(&body_less(ns, OWN, RIVAL_FACT, QUAL_RULE));
    let op_msg = refusal(&body_less(ns, OWN, RIVAL_FACT, QUAL_OP));
    let (rule_loc, rule_body) = located(&rule_msg);
    let (op_loc, op_body) = located(&op_msg);
    assert_eq!(
        rule_body, op_body,
        "one refusal, one message body — two faces must not drift",
    );
    assert_ne!(
        rule_loc, op_loc,
        "the two fixtures put the call on different lines; equal locations would mean \
         the location is not really being read off the call",
    );
}

/// THE OTHER HALF OF THE TICKET, and the one that needs both the gate and the goal
/// shape: with ONE supplier the rule body must ANSWER the supplied implementation, as
/// the operation body does. `Leaf` provides `Desc` and declares its own `describe`, so
/// the typer pins the call; the pin then has to survive into the resolver's goal-shape
/// decision, which asks about the SPELLED functor and finds a body-less op.
#[test]
fn one_supplier_answers_the_supplied_impl_in_a_rule_body() {
    let ns = "test.wi1043.one";
    let src = body_less(ns, OWN, "", QUAL_RULE);
    assert_eq!(
        answer(ns, &src),
        7,
        "one supplier: the rule body must reach the carrier's implementation, not \
         residualize — `[]` is what this ticket exists to stop",
    );
    // The face it must agree with, on the same program text.
    assert_eq!(
        probe(ns, &body_less(ns, OWN, "", QUAL_OP)),
        7,
        "the operation-body face"
    );
}

/// THE WITNESS ROUTE, BOTH SPELLINGS — and the PRE-EXISTING refusal this ticket had to
/// fix before it could widen anything.
///
/// `sort Rival provides Desc[T = Leaf]` makes `Leaf` an instance of `Desc` without `Leaf`
/// declaring anything, and `sort_provides` — which walks the CARRIER's own out-edges —
/// cannot see it (WI-450's carrier-as-artifact limit, 058 §12). The rule-body requirement
/// check asks exactly that question of every ground carrier argument it can read, so this
/// legal program was refused with "missing `requires Desc[T = …]`" through the DOT
/// spelling, which the WI-282 walk has always typed. MEASURED on both sides: the
/// operation-body twin loads and answers 9.
///
/// The widening would have extended that refusal to the qualified spelling, because what
/// feeds the check is the argument's `inferred_type` and only a typed atom has one. Both
/// spellings now answer.
#[test]
fn a_witness_supplied_carrier_answers_through_both_spellings() {
    let ns = "test.wi1043.witness";
    assert_eq!(
        answer(ns, &body_less(ns, "", RIVAL_WITNESS, QUAL_RULE)),
        9,
        "the witness sort supplies the only implementation and the qualified rule body \
         must reach it",
    );
    assert_eq!(
        answer(ns, &body_less(ns, "", RIVAL_WITNESS, DOT_RULE)),
        9,
        "and the dot spelling, which was REFUSED before this ticket — a legal program, \
         on a check that cannot see a witness provision",
    );
    assert_eq!(
        probe(ns, &body_less(ns, "", RIVAL_WITNESS, QUAL_OP)),
        9,
        "the face both must agree with",
    );
}

/// THE TRUE POSITIVE THE WITNESS ESCAPE MUST NOT SWALLOW, and the one row where the rule
/// body is now STRICTER than the operation body rather than merely equal to it.
///
/// `Leaf` declares a `describe` member and NO provision, so nothing makes it an instance
/// of `Desc`: there is no dictionary and no dispatch. MEASURED on the operation-body
/// twin: it LOADS CLEAN and fails at the CALL with `OperationBodyMissing` — WI-1012's
/// cost (1), `anthill check` passing on a program the interpreter refuses. The rule-body
/// face says so at LOAD.
///
/// An own member is NOT a provision, which is the distinction that makes the escape safe:
/// widening it to "the carrier has a supplier of this op by any route" would admit route
/// 1 here and put this program back to loading clean.
#[test]
fn a_carrier_with_no_instance_is_refused_at_load() {
    let ns = "test.wi1043.noinstance";
    let msg = refusal(&body_less(ns, OWN_NO_PROVISION, "", QUAL_RULE));
    assert!(
        msg.contains("requires") && msg.contains("Desc"),
        "a call on a carrier that provides no instance must be refused, naming the \
         requirement: {msg}",
    );
    // The operation-body twin, so the asymmetry is a measurement and not an assumption:
    // it loads, and the failure arrives only when the call runs.
    let ns_op = "test.wi1043.noinstanceop";
    let interp_err = crate::common::interp_for(&body_less(ns_op, OWN_NO_PROVISION, "", QUAL_OP))
        .call(&format!("{ns_op}.probe"), &[])
        .expect_err("no instance: the operation-body call has nothing to dispatch to");
    assert!(
        format!("{interp_err:?}").contains("OperationBodyMissing"),
        "the operation body's face is a RUNTIME failure: {interp_err:?}",
    );
}

/// THE GATE ITSELF, over a real corpus load: [`spec_op_call_parent`] is exactly the union
/// of the two halves it was built from, with no third reading of its own.
///
/// The oracle discipline `wi1042_defaulted_gate_test` established: compare the shipped
/// gate against an INDEPENDENT construction out of the two owners, so the assertion is
/// between two spellings rather than a function with itself. Non-vacuity is asserted on
/// BOTH halves — a union whose body-less side is empty would pass the agreement while
/// measuring only WI-1026's population.
///
/// CONTROL: add any clause to [`spec_op_call_parent`] that neither half has, or drop its
/// `OperationInfo` probe (which is what keeps an entity constructor declared inside a
/// parametric sort — `anthill.prelude.Option.some` — out of the walk), and this fails.
#[test]
fn the_walk_gate_is_exactly_the_two_halves() {
    let kb: KnowledgeBase = crate::common::load_kb_with("namespace wi1043.probe\nend\n");
    let oracle = |op: Symbol| -> Option<Symbol> {
        defaulted_spec_op_parent(&kb, op).or_else(|| lookup_spec_op_dispatch(&kb, op))
    };
    let (mut defaulted, mut body_less_count) = (0usize, 0usize);
    for (op, _) in all_operation_params(&kb) {
        assert_eq!(
            spec_op_call_parent(&kb, op),
            oracle(op),
            "the walk gate and the union of its two halves disagree on `{}`",
            kb.qualified_name_of(op),
        );
        if defaulted_spec_op_parent(&kb, op).is_some() {
            defaulted += 1;
        } else if lookup_spec_op_dispatch(&kb, op).is_some() {
            body_less_count += 1;
        }
    }
    assert!(
        defaulted >= 10 && body_less_count >= 10,
        "both halves must be populated for the agreement above to measure anything — \
         defaulted {defaulted}, body-less {body_less_count}",
    );
    // The one symbol whose answer the two body tests genuinely disagree about
    // (WI-1042): an entity constructor declared INSIDE a parametric sort. It is not an
    // operation, so it is in neither half — and admitting it here is what fired the
    // rule-body walk on entity-constructor calls in 14 tests.
    let some = kb
        .try_resolve_symbol("anthill.prelude.Option.some")
        .expect("the stdlib declares Option.some");
    assert_eq!(
        spec_op_call_parent(&kb, some),
        None,
        "`Option.some` is an entity constructor, not a spec op",
    );
}

/// THE GAP THIS TICKET DID NOT CLOSE, and **WI-1057** did. Kept here, where WI-1043's
/// own table pointed, rather than moved to a new file: it is one more row of the supply
/// matrix this file measures, and the row it contradicts is three screens up.
///
/// A body-less spec op supplied ONLY by a retroactive instance fact has no typer pin —
/// `dispatch_spec_op_cached` does not read instance-fact op-bindings (WI-431 inc 2), so
/// the implementation is discoverable only BY VALUE, at eval. WI-1043 gave every OTHER
/// route its goal shape by reading that pin (`dispatched_relation_arity`); this route
/// has no pin to read, so WI-1057 admits the shape on the spelled functor itself
/// (`body_less_relation_arity`) and lets the eval bridge decide the supplier from the
/// argument VALUES, exactly as the operation-body face does.
///
/// Both spellings, which is what says the fix is not spelling-keyed.
#[test]
fn a_fact_route_supplier_answers_from_a_rule_body() {
    let ns = "test.wi1043.factonly";
    for (tail, spelling) in [(QUAL_RULE, "qualified"), (DOT_RULE, "dot")] {
        assert_eq!(
            answer(ns, &body_less(ns, NO_SUPPLIER_LEAF, RIVAL_FACT, tail)),
            9,
            "WI-1057: the {spelling} rule body must reach the fact-route supplier of a \
             body-less spec op — `[]` in both spellings is what this closed",
        );
    }
    assert_eq!(
        probe(ns, &body_less(ns, NO_SUPPLIER_LEAF, RIVAL_FACT, QUAL_OP)),
        9,
        "the operation-body face, which is the one the rule body has to agree with",
    );
}

/// THE TRAP WI-1057 EXISTS TO AVOID, driven — and the reason the naive widening was
/// measured and rejected before any code was written.
///
/// Admitting a body-less spec op to the functional-relation view is only half a fix.
/// The other half is that its call may not REDUCE: with the carrier argument still
/// unbound there is no value to dispatch on, the eval bridge's ground gate declines,
/// and `reduce_op_value` hands back the ORIGINAL call. Routing `unify(?r, <that call>)`
/// then BINDS `?r` to the call term and reports it as a definite answer — a wrong
/// answer where there had merely been a missing one.
///
/// `reduction_left_body_less_call` is what stops it, and this drives that: the goal
/// must answer NOTHING (the pre-WI-1057 outcome for this shape) rather than one
/// solution binding `?r` to a `describe(...)` node. Answering nothing rather than
/// DELAYING is the WI-938 hook's own standing open half, recorded at its site; this
/// test pins only that no residual is bound.
///
/// CONTROL: drop `reduction_left_body_less_call` from the hook's `undecided` and this
/// test fails with one solution, while
/// `a_fact_route_supplier_answers_from_a_rule_body` still passes — there the bridge
/// DOES answer, so the guard is never consulted. That asymmetry is the point: it is
/// the only one of WI-1057's four pieces this test can see.
#[test]
fn an_unground_body_less_goal_binds_no_residual() {
    let ns = "test.wi1043.unground";
    // `?x` is never bound by any earlier goal, so the call reaching the goal shape has
    // a free carrier argument — the one thing the WI-938 hook must not decide.
    let unground_rule = "  rule answer(?r) :- Desc.describe(?x, ?r)\n";
    let mut kb =
        crate::common::load_kb_with(&body_less(ns, NO_SUPPLIER_LEAF, RIVAL_FACT, unground_rule));
    let answers = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
    assert!(
        answers.is_empty(),
        "an un-ground body-less spec-op goal must not bind `?r` to the un-reduced call: \
         got {answers:?}",
    );
}

/// ONE CALL, ONE REFUSAL — the tie'd call NESTED inside an `=` goal, which is the common
/// spelling and the one this ticket's first cut printed TWICE.
///
/// An `=` goal loads as a call on the body-less `PartialEq.eq`, so the outer atom is
/// itself an admitted shape: this frame recurses into the child (which decides the tie
/// and reports it) and then types the whole atom, which re-derives the same refusal at
/// the same span. Reported from both, it printed twice — and for the DOT spelling that is
/// a regression against pre-WI-1043 behaviour, where the child reported it exactly once.
/// Found by this ticket's /code-review, driven here.
///
/// CONTROL: drop the duplicate guard — WI-1043's `own_call_tie` `(op, span)` identity,
/// and since WI-1056 the `already_reported` key that replaced it — and both arms report 2
/// lines. The flat-case assertion in `a_witness_rival_tie_carries_the_witness_repair`
/// cannot see it: there the tie IS the atom's own call.
#[test]
fn a_tie_nested_in_an_eq_goal_is_reported_once() {
    let ns = "test.wi1043.nested";
    for (tail, spelling) in [
        (
            "  rule answer(?r) :- eq(?r, Desc.describe(leaf()))\n",
            "qualified",
        ),
        ("  rule answer(?r) :- eq(?r, leaf().describe())\n", "dot"),
    ] {
        let msg = refusal(&body_less(ns, OWN, RIVAL_FACT, tail));
        assert!(
            msg.contains("ambiguous dispatch") && msg.contains("Desc.describe"),
            "the {spelling} nested call must still refuse: {msg}",
        );
        assert_eq!(
            msg.lines().count(),
            1,
            "the {spelling} nested tie must be reported ONCE — the enclosing `eq` atom \
             re-derives it, and the child already said it: {msg}",
        );
    }
}
