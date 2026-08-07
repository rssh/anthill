//! WI-1027 — the BODY-LESS half of WI-1012's load refusal: a statically concrete
//! carrier with TWO suppliers of a body-less spec op is refused at LOAD.
//!
//! WI-1012 gave the refusal a load face for the DEFAULTED half only — its arm sits
//! inside `check_apply_iter`'s `lookup_spec_op_dispatch(..).is_none()` block, covering
//! exactly the ops eval's `resolve_carrier_override_by_value` serves. The BODY-LESS
//! half (eval's `resolve_spec_op_target_by_value`, the reader WI-842 built) had none.
//!
//! THE TICKET ASKED FOR A FIXTURE FIRST, because the reading was structural and NOT
//! driven: reaching two suppliers there needs route 1 — the carrier's OWN member,
//! registered by `build_sort_ops_table` pass 1 regardless of any provision — to
//! disagree with the provision count, which is precisely what `DispatchOutcome::
//! Ambiguous` cannot see. It reproduces, and driving it found MORE than the ticket
//! described. One program, three supply shapes, all three MEASURED before the guard:
//!
//! | `Leaf`'s own `describe` | rival | before | which arm |
//! |---|---|---|---|
//! | declared, NO body | `fact Desc[T = Leaf, describe = otherDescribe]` | loads clean, `AmbiguousSpecOpDispatch` at the CALL | `Unique`, pin guard false |
//! | `= 7` | the same fact | **answers 7** | `Unique`, PINS route 1 |
//! | `= 7` | `sort Rival { fact Desc[T = Leaf]; operation describe = 9 }` | **answers 9** | `Unique`, PINS the witness |
//!
//! (Row 3 was RE-MEASURED, not carried over, after `Rival` lost its `entity` — see
//! `RIVAL_WITNESS` for why it had to. Same answer, 9.)
//!
//! Only the first is the decline the ticket predicted. The other two are the same
//! first-match defect one layer down: `Unique` resolves through `sort_ops_lookup(impl_
//! sort, op_short)`, a first-match read over ONE sort's table, which sees the rival
//! routes no better than the provision walk sees route 1 — so it SELECTS silently,
//! which is what 058 §4.9 forbids and what WI-1010 closed for the defaulted half. Row 2
//! is WI-1010's own defect verbatim: a `describe = otherDescribe` binding the loader had
//! already certified (`check_instance_fact_op_signatures`) meant nothing.
//!
//! **THE TICKET'S CONDITION — "two suppliers" — IS FALSE AT THE TYPER.** A ≥2-count
//! guard, the obvious reading of 058 §4.9 and what the ticket describes, refused SIX
//! delivered programs (wi817 ×1, wi843 ×2, wi857 ×2, wi858 ×1). The count is sound for
//! eval's `resolve_spec_op_target_by_value` precisely because that read is BRACKET-LESS
//! BY CONSTRUCTION; a call site has two ways to arbitrate that the count cannot see —
//! tier 1's explicit `f[Spec = W](…)`, and tier 2's specificity, which WI-843 pinned as
//! deliberate (`a_specificity_ordered_pair_silently_takes_the_more_specific`) and
//! recorded that making loud "amounts to a new coherence rule". So the guard refuses only
//! what the arbitration could not SEE: a group holding a route-1 (`Own`) or route-2
//! (`Fact`) supplier, neither of which `resolve_inner` can weigh. That rule has a name —
//! `refuse_unarbitrated_supplier_tie` — and its doc carries the full argument, the
//! per-route mechanism (`SupplyRoute::weighed_by_provision_arbitration`), the two excluded
//! outcomes (`Ambiguous` / `NoMatch`, which raise on their own account) and the corpus
//! measurement: 0 tied pairs across `stdlib` + `anthill-stl`, so the corpus reaches the
//! guard only through those six fixtures.
//!
//! NOT ESTABLISHED, and the guard's placement is what makes it not matter: whether a tie
//! can reach the OTHER two declining arms the ticket named — the concrete `NoCandidates`
//! pass-through and `Deferred`-with-no-slot. One construction was tried for
//! `NoCandidates` (a second spec param bound away from the call's goal, so the provision
//! keys to `Leaf` while `collect_provides_candidates` matches nothing) and it was refused
//! by an ordinary return-type mismatch before reaching the arm; none was tried for
//! `Deferred`. Guarding above the `match` covers them by construction, so their
//! reachability changes nothing here — which is the argument for placing it there rather
//! than writing three arms of which two would have no test.
//!
//! WHAT FAILS IF THIS IS BACKED OUT — MEASURED, three separate runs, one revert each,
//! not predicted, and RE-MEASURED after review restructured the guard into a named
//! function. The guard has TWO narrowing clauses beside the count — tier 1 (`!pinned_spec`)
//! and the route clause (`weighed_by_provision_arbitration`) — and each is driven by a
//! DIFFERENT delivered test, which is why they were reverted one at a time.
//!
//! | test | guard deleted | tier-1 clause dropped | route clause dropped |
//! |---|---|---|---|
//! | `an_unrunnable_member_beside_a_fact_binding_is_refused_at_load` | **FAILS** | ok | ok |
//! | `a_runnable_member_no_longer_silently_outranks_a_fact_binding` | **FAILS** | ok | ok |
//! | `a_witness_supplier_no_longer_silently_outranks_the_carriers_member` | **FAILS** | ok | ok |
//! | `a_rule_reaching_the_tie_through_an_operation_is_refused` | **FAILS** | ok | ok |
//! | `a_provision_tie_is_still_reported_as_a_provider_tie` | **FAILS** | ok | ok |
//! | `a_bracket_selecting_the_witness_still_loads_and_runs` | ok | **FAILS** | ok |
//! | `one_fact_supplier_still_dispatches` | ok | ok | ok |
//! | `an_own_member_alone_still_dispatches` | ok | ok | ok |
//! | `a_rule_over_one_supplier_still_answers` | ok | ok | ok |
//! | `wi857…::a_chain_free_witness_provider_still_runs` | ok | **FAILS** | ok |
//! | `wi843…::a_specificity_ordered_pair_silently_takes_the_more_specific` | ok | ok | **FAILS** |
//!
//! Two rows deserve their reading stated. `a_provision_tie_is_still_reported_as_a_
//! provider_tie` fails in column 1 not for its headline claim — the `Ambiguous` exclusion
//! holds either way — but for its FIXTURE GUARD, which asserts that dropping the
//! self-provision turns the same program into the supplier tie; without a guard there is
//! no tie to turn into, and a test that only asserted the exclusion would have passed
//! while measuring nothing. And the last three ok-either-way rows are the controls an
//! over-firing guard consumes first: the 1-supplier answer on each side of the tie, and
//! the SLD path over one supplier.
//!
//! The eval face's control is elsewhere and must stay green —
//! `wi842_bracketless_readers_test::a_two_provider_value_directed_dispatch_names_both_
//! candidates`, whose carrier is a type param (`Holder.probe(x: HT)`), so no static
//! carrier exists for this guard to read and the refusal stays at the read.
//!
//! REFERENCE: WI-1012; WI-1010; WI-842; WI-876; `docs/design/058-implementation.md` §14.

/// The three contract-carrying helpers of this cluster, imported rather than copied —
/// the discipline `wi1010::program`'s own doc states ("a copy there would let the shape
/// drift under the successor's feet"). `refusal`'s panic text is what stops "loaded
/// clean" reading as a pass; `probe`'s absent load-clean assertion is argued at its
/// definition (WI-966); `located` pins the ONE `line:col: message` rendering.
use anthill_core::eval::Value;

use crate::wi1010_defaulted_op_instance_fact_test::probe;
use crate::wi1012_static_supplier_tie_test::{located, refusal};

/// A BODY-LESS `Desc.describe` — the half WI-1012 did not cover. `leaf_body` writes the
/// carrier's own member (route 1), `supply` the rival (route 2 or 3), `tail` extra items.
///
/// THE ONE THING NOT SHARED with `wi1010_defaulted_op_instance_fact_test::program`, which
/// this file otherwise borrows from: the two templates differ by exactly ` = 1` on the
/// spec op. That token is the whole discriminator — with it the call takes
/// `check_apply_iter`'s DEFAULTED block and WI-1012's arm, without it the body-less block
/// and this ticket's guard. Parameterizing one builder over it would let a fixture named
/// for one half emit programs for the other, and would hide at each call site which half
/// is under test. It is the same factoring the source keeps for the same reason:
/// `carrier_override_suppliers` and `spec_op_suppliers_for_carrier` are two functions over
/// one walk, because the two halves must be able to answer differently.
fn program(ns: &str, leaf_body: &str, supply: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
{leaf_body}  end
{supply}
  operation probe() -> Int64 = Desc.describe(leaf())
{tail}end
"#
    )
}

/// Route 1 present but NOT runnable — declared only. The `Unique` arm's pin guard reads
/// `op_has_runnable_body`, so this is the flavour the ticket predicted: no pin, and the
/// concrete carrier goes to eval.
const OWN_UNRUNNABLE: &str = "    operation describe(x: Leaf) -> Int64\n";
/// Route 1 present AND runnable — the `Unique` arm PINS it, silently.
const OWN_RUNNABLE: &str = "    operation describe(x: Leaf) -> Int64 = 7\n";
/// [`OWN_RUNNABLE`] with the carrier's OWN provision of the spec beside it. One constant
/// and one spelling, because inside a sort body `fact Desc[…]` and `provides Desc[…]`
/// emit the SAME `SortProvidesInfo` (WI-449) — so writing them differently in two tests
/// with opposite outcomes points a reader at a difference that decides nothing. What
/// decides is which rival is supplied.
const SELF_PROVIDED_OWN_RUNNABLE: &str =
    "    fact Desc[T = Leaf]\n    operation describe(x: Leaf) -> Int64 = 7\n";

/// ROUTE 2 — a retroactive instance fact's op-valued binding. Has no name (058 §4.3).
const RIVAL_FACT: &str = "\n  operation otherDescribe(x: Leaf) -> Int64 = 9\n\n  \
                          fact Desc[T = Leaf, describe = otherDescribe]\n";
/// ROUTE 3 — a WITNESS sort supplying `Leaf`'s `describe`. Nameable, hence the other
/// repair.
///
/// It declares NO entity on purpose: a CONCRETE provider is refused an explicit
/// `[Desc = Rival]` bracket ("its values carry their own sort, so the dispatch is already
/// directed by the value" — WI-855), which would make the tier-1 control below untestable.
/// `wi857`'s `Descending` is spelled the same way for the same reason.
pub(crate) const RIVAL_WITNESS: &str = "\n  sort Rival\n    import anthill.prelude.Int64\n    \
                             fact Desc[T = Leaf]\n    \
                             operation describe(x: Leaf) -> Int64 = 9\n  end\n";

/// Assert the refusal is the SUPPLIER tie and names both routes.
pub(crate) fn assert_supplier_tie(msg: &str, ns: &str, route_two: &str) {
    assert!(msg.contains(&format!("{ns}.Desc.describe")), "the spec op must be named: {msg}");
    assert!(msg.contains(&format!("carrier `{ns}.Leaf`")), "the carrier must be named: {msg}");
    assert!(
        msg.contains(&format!("the carrier's own member '{ns}.Leaf.describe'")),
        "route 1 must be named BY ROUTE: {msg}",
    );
    assert!(msg.contains(route_two), "the rival must be named by ITS route: {msg}");
    // The span is what raising at the typer buys over raising at the call: it locates
    // the CALL, not the declarations, which are individually legal. Asserted through
    // `located`, which additionally hands back the BODY — so this pins that the message
    // STARTS after the prefix rather than merely containing the phrase somewhere.
    let (_, body) = located(msg);
    assert!(body.starts_with("ambiguous dispatch of `"), "{msg}");
}

/// THE ARM THE TICKET PREDICTED. `Leaf.describe` is DECLARED with no body, so the
/// `Unique` arm's `op_has_runnable_body` leg is false and the call is left as the spec
/// op for eval — with two suppliers waiting there.
///
/// MEASURED before the guard: this program LOADED CLEAN and the call returned
/// `EvalError::AmbiguousSpecOpDispatch`. That is WI-1012's cost (1) — `anthill check`
/// passing on a program the interpreter refuses — on the half it did not cover.
///
/// Note the rival's own significance: `spec_op_suppliers_for_carrier`, unlike the
/// defaulted half's `carrier_override_suppliers`, does NOT filter unrunnable candidates,
/// and must not — that filter is backend-relative (WI-886) and this is a coherence
/// question. So the unrunnable member counts as the second supplier here and would not
/// there, which is why the guard reads the wider list.
#[test]
fn an_unrunnable_member_beside_a_fact_binding_is_refused_at_load() {
    let ns = "test.wi1027.unrunnable";
    let msg = refusal(&program(ns, OWN_UNRUNNABLE, RIVAL_FACT, ""));
    assert_supplier_tie(
        &msg,
        ns,
        &format!("an instance fact binding `describe = {ns}.otherDescribe`"),
    );
}

/// THE ARM DRIVING FOUND, AND THE WORSE ONE. The identical program with the member given
/// a body: the `Unique` arm PINS route 1 and the fact's binding is silently inert.
///
/// MEASURED before the guard: **answered 7**. Not a deferral, not a diagnostic — a wrong
/// answer to a question with two written answers, which is WI-1010's defect statement
/// word for word ("a silent wrong answer, not a missing feature") on the other half.
#[test]
fn a_runnable_member_no_longer_silently_outranks_a_fact_binding() {
    let ns = "test.wi1027.runnable";
    let msg = refusal(&program(ns, OWN_RUNNABLE, RIVAL_FACT, ""));
    assert_supplier_tie(
        &msg,
        ns,
        &format!("an instance fact binding `describe = {ns}.otherDescribe`"),
    );
    // A defaulted op's tie can only ever be `KeepOne` (no dispatch slot to bind), so
    // WI-1012's arm asks and always gets it. A BODY-LESS op HAS the slot, and neither
    // rival here is nameable, so this arm must still answer `KeepOne` — the discriminator
    // is the RIVAL's kind, not the site's.
    assert!(
        msg.contains("No bracket names any of them"),
        "an own-member-vs-instance-fact tie has no nameable rival: {msg}",
    );
}

/// ROUTE 3, and the FIRST TIME THE TYPER REACHES `SupplierTieRepair::NameableWitness`.
/// WI-1012 recorded that its arm "is body-less-gated shut and so always answers
/// `KeepOne`, but it asks anyway" — this is the site that makes asking pay: a body-less
/// op HAS the `Dispatch` requirement slot a `[Desc = Rival]` bracket binds, and `Rival`
/// is a nameable provider distinct from the carrier.
///
/// MEASURED before the guard: **answered 9** — the witness, with `Leaf`'s own `describe`
/// (7) silently losing. Same first-match read, opposite winner, which is the tell that
/// route order was deciding rather than anything the author wrote.
#[test]
fn a_witness_supplier_no_longer_silently_outranks_the_carriers_member() {
    let ns = "test.wi1027.witness";
    let msg = refusal(&program(ns, OWN_RUNNABLE, RIVAL_WITNESS, ""));
    assert_supplier_tie(
        &msg,
        ns,
        &format!("witness sort '{ns}.Rival' (supplying '{ns}.Rival.describe')"),
    );
    assert!(
        msg.contains("route the call through an operation that can write `[Spec = Witness]`"),
        "a witness rival on a BODY-LESS op is nameable at a bracket-capable call, and \
         the repair must say so rather than inherit `keep exactly one`: {msg}",
    );
}

/// WI-1012's COST (3), the reason that ticket existed, on this half: a rule reaching the
/// tie through an operation. `bridge_op_to_eval` residualizes every non-`Suspended` eval
/// error to `None` (WI-483), so the refusal degraded to SILENCE — the rule reported the
/// ambiguity by not answering.
///
/// MEASURED before the guard, on the unrunnable-member fixture (the only flavour that
/// reached the eval refusal at all): the program loaded clean and `answer(?r)` returned
/// **0 solutions**. The other two flavours were worse still — they answered DEFINITELY,
/// with the losing supplier invisible.
///
/// Asserted as a LOAD refusal rather than by re-driving the rule: once the program is
/// refused there is no KB to query, and "the query returns nothing" is precisely the
/// symptom that must stop being how this reports.
#[test]
fn a_rule_reaching_the_tie_through_an_operation_is_refused() {
    let ns = "test.wi1027.rule";
    let msg = refusal(&program(ns, OWN_UNRUNNABLE, RIVAL_FACT, "\n  rule answer(?r) :- probe(?r)\n"));
    assert!(
        msg.contains("ambiguous dispatch") && msg.contains("Desc.describe"),
        "the operation the rule bridges into must report the tie at load: {msg}",
    );
}

/// THE EXCLUSION, DRIVEN. Add the carrier's OWN provision (`provides Desc[T = Leaf]`) to
/// the witness fixture and the goal now matches TWO provisions, so `dispatch_spec_op_
/// cached` answers `DispatchOutcome::Ambiguous` — an outcome that raises on its own
/// account, with `InstanceTie`'s provider symbols and its own `TieRepair`. The guard
/// skips it deliberately; this test is what fails if that skip is dropped.
///
/// This file originally RECORDED a bad rendering here rather than fixing it: swap the
/// witness for the instance fact and the same `Ambiguous` arm printed the carrier TWICE
/// (`Leaf, Leaf`) with `TieRepair::ValueDirected`. **WI-1032 closed it**, and not where
/// this note expected — the two provisions AGREE as provisions, so the collector now
/// collapses them and the conflict reaches the supplier guard above. Driving it also
/// turned up the worse half: the same pair WITHOUT the op binding is one dictionary
/// written twice, and it was REFUSED. See `wi1032_provision_dedup_test`. What survives
/// here is the exclusion itself, which this test still pins: `Rival` is a distinct
/// provider, so the tie is a real PROVIDER tie and `DispatchAmbiguous` owns it.
#[test]
fn a_provision_tie_is_still_reported_as_a_provider_tie() {
    let ns = "test.wi1027.provisiontie";
    let msg = refusal(&program(ns, SELF_PROVIDED_OWN_RUNNABLE, RIVAL_WITNESS, ""));
    assert!(
        msg.contains("instances provide"),
        "two PROVISIONS matching the goal are `DispatchAmbiguous`'s tie, not the supplier \
         tie — the guard must not pre-empt an outcome that already refuses: {msg}",
    );
    assert!(
        !msg.contains("the carrier's own member"),
        "the supplier tie's route rendering must not appear here: {msg}",
    );
    // The self-provision is what moves it: the same program without it is the supplier
    // tie above. Asserted so this test cannot pass by the fixture drifting into a shape
    // that never had two provisions.
    assert!(
        refusal(&program(ns, OWN_RUNNABLE, RIVAL_WITNESS, "")).contains("the carrier's own member"),
        "fixture guard: dropping the self-provision must give the SUPPLIER tie",
    );
}

/// CONTROL, AND THE CLAUSE THAT NARROWED THE GUARD. The same two-supplier program with
/// a `[Desc = Rival]` bracket LOADS and RUNS. 058 §4.1 tier 1: the author named a
/// provider, so nothing here is unselected, and the same reasoning that stops the bracket
/// being swallowed by `dispatch_spec_op_cached`'s defer trigger (WI-841) stops it being
/// swallowed by this refusal.
///
/// Not hypothetical — it is `wi857_dictionary_layout_test::a_chain_free_witness_provider_
/// still_runs` in miniature (`Ord.compare[Ord = Descending](7, 3)` over `Int64`,
/// whose own `compare` is the second supplier). A ≥2-count guard with no tier-1 clause
/// refused that delivered program; this test is the local copy so the clause has a
/// failure of its own rather than only a distant one.
#[test]
fn a_bracket_selecting_the_witness_still_loads_and_runs() {
    let ns = "test.wi1027.selected";
    let src = program(ns, OWN_RUNNABLE, RIVAL_WITNESS, "")
        .replace("Desc.describe(leaf())", "Desc.describe[Desc = Rival](leaf())");
    assert!(src.contains("[Desc = Rival]"), "fixture guard: the bracket must be written");
    assert_eq!(
        probe(ns, &src),
        9,
        "the bracket names `Rival`, so its `describe` runs — and the value proves the \
         selection rather than a fallthrough, since the carrier's own member answers 7",
    );
}

/// CONTROL — ONE supplier, by the fact route, still dispatches to it. This is WI-1010's
/// rule on the body-less half and it must be untouched: the fact's binding wins because
/// it is the only thing supplied, not because a count reached 2.
#[test]
fn one_fact_supplier_still_dispatches() {
    let ns = "test.wi1027.factonly";
    assert_eq!(
        probe(ns, &program(ns, "", RIVAL_FACT, "")),
        9,
        "the fact's `describe = otherDescribe` binding is the carrier's ONLY \
         implementation and must still be dispatched to",
    );
}

/// CONTROL — the carrier's OWN member alone, the overwhelmingly common shape (every
/// body-less spec-op call in the tree). An over-firing guard consumes this first.
#[test]
fn an_own_member_alone_still_dispatches() {
    let ns = "test.wi1027.ownonly";
    let src = program(ns, SELF_PROVIDED_OWN_RUNNABLE, "", "");
    assert_eq!(probe(ns, &src), 7, "one supplier, the carrier's own member");
}

/// CONTROL — a rule body over the one-supplier program still ANSWERS. The refusal test
/// above asserts a load error, which would also be produced by the fixture failing to
/// load for an unrelated reason; this pins that the same shape minus the second supplier
/// resolves end to end through the SLD→eval bridge.
#[test]
fn a_rule_over_one_supplier_still_answers() {
    let ns = "test.wi1027.ruleok";
    let src = program(ns, "", RIVAL_FACT, "\n  rule answer(?r) :- probe(?r)\n");
    let mut kb = crate::common::load_kb_with(&src);
    // `matches!` rather than `assert_eq!`: `Value` has no `PartialEq` (it carries
    // closures), which is why `query_unary` hands back raw values for the caller to
    // pattern-match.
    let answers = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
    assert!(
        matches!(answers.as_slice(), [(Value::Int(9), true)]),
        "one supplier: the rule must DEFINITELY answer the fact-bound impl's 9 — the \
         EMPTY result a tie gives here is the silence WI-1012 named as cost (3); got \
         {answers:?}",
    );
}
