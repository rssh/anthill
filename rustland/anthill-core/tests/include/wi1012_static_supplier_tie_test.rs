//! WI-1012 — a supplier TIE on a STATICALLY CONCRETE carrier is refused at LOAD,
//! not only at the call.
//!
//! WI-1010 made a SECOND supplier of a DEFAULTED spec op loud (058 §4.9) rather than
//! letting route order decide silently, and raised it at eval as
//! `EvalError::AmbiguousSpecOpDispatch`. But the TYPER already holds the span, the
//! carrier and the route-rendered candidate list at the moment it declines to pin, so
//! deferring was a fallback rather than a deferral. It cost three things:
//!
//!   1. `anthill check` passed on a program the interpreter refuses;
//!   2. a tie in code that never RUNS never reported;
//!   3. on the SLD path the refusal DEGRADED TO SILENCE — `bridge_op_to_eval`
//!      residualizes every non-`Suspended` eval error to `None` (WI-483), so a rule
//!      reaching a 2-supplier defaulted op answered NOTHING.
//!
//! (3) is the reason the ticket exists, and it was MEASURED before any code changed:
//! `a_rule_reaching_the_tie_through_an_operation_is_refused`'s program loaded CLEAN
//! and `query_unary` on its rule returned `[]`.
//!
//! THE EVAL SITE STAYS. The typer's WI-444 block fires only on a statically concrete
//! carrier, so an abstract-spec receiver still needs the late refusal —
//! `a_tie_on_an_abstract_carrier_is_still_refused_at_the_call` drives it. That is an
//! argument for SHARING one message body between the two faces, which
//! `both_faces_render_one_message_body` pins.
//!
//! WHY A NEW `TypeError` VARIANT. `DispatchAmbiguous` cannot carry this tie: its
//! `InstanceTie` holds PROVIDER symbols, and for a route-1-vs-route-2 tie both
//! canonicalize to the SAME carrier — `render_instance_tie` would print `Leaf, Leaf`
//! and, both being concrete, pick `TieRepair::ValueDirected`, whose message ("each is
//! a CONCRETE provider … pin the carrier through the call's receiver") describes a
//! different failure. `a_route_1_vs_2_tie_is_not_a_provider_tie` pins the distinction
//! at the message the author actually reads.
//!
//! ## Two limits, both MEASURED, neither closed here
//!
//! **A rule body that names the spec op DIRECTLY was not covered** — three spellings,
//! three silent answers, measured on this file's tie fixture and on the same program
//! with ONE (fact-route) supplier. **CLOSED BY WI-1026**; the table is kept because
//! this is where it was measured, with what WI-1026 changed it to:
//!
//! | rule body | 1 supplier | 2 suppliers | | WI-1026 |
//! |---|---|---|---|---|
//! | `Desc.describe(leaf(), ?r)` | `1` — the DEFAULT, binding invisible | `1` — tie ignored | → | `7` / REFUSED |
//! | `describe(leaf(), ?r)` | `[]` | `[]` | → | unchanged — WI-1034 |
//! | `leaf().describe(?r)` | `1` — the DEFAULT | `7` — route 1, first match | → | `7` / `7` — WI-1035 |
//! | via an operation body | `7` ✓ WI-1010 | REFUSED ✓ WI-1012 | → | unchanged |
//!
//! TWO CLAIMS ABOVE WERE WRONG, and WI-1026 refuted both by driving them.
//! "The typer never sees it, since `type_rule_bodies` reaches `check_apply_iter` only
//! for a DOT" — the DOT row IS reached, and the WI-444 block DID pin it; the pin was
//! lost in the De Bruijn open / head-match rename, because `rebuilt_expr` carried the
//! `inferred_type` and not the `CallClass` beside it. And the tie shown here as `7 —
//! route 1, first match` is not a rule-body defect at all: the same dot in an
//! OPERATION body also answers `7` (this file's own control used the QUALIFIED
//! spelling, so it measured the path and attributed to it what is keyed on the
//! spelling). See `wi1026_rule_body_spec_op_dispatch_test`.
//!
//! **The refusal cannot fire for a SELF-RECEIVER spec** (`head(s: Stream)`) — the
//! stdlib's largest defaulted-op family. `provision_carrier_sort` files every
//! provision under the spec's FIRST TYPE PARAM, so no route-2/3 supplier reaches such
//! a carrier and the arm never sees two candidates. WI-450's carrier-as-artifact
//! limit (058 §12); recorded at the arm so closing it there is a decision, not a side
//! effect that silently widens a LOAD refusal.
//!
//! WHAT FAILS IF THIS IS BACKED OUT (back out = the typer's `[_, _, ..]` arm falls
//! through instead of raising, which is WI-1010's behaviour) — MEASURED, all rows:
//!
//! | test | backed out |
//! |---|---|
//! | `a_concrete_carrier_tie_is_refused_at_load` | **FAILS** |
//! | `a_rule_reaching_the_tie_through_an_operation_is_refused` | **FAILS** |
//! | `a_tie_in_a_branch_that_never_runs_is_refused` | **FAILS** |
//! | `a_route_1_vs_2_tie_is_not_a_provider_tie` | **FAILS** |
//! | `both_faces_render_one_message_body` | **FAILS** (the load half) |
//! | `a_tie_on_an_abstract_carrier_is_still_refused_at_the_call` | ok — **by design** |
//!
//! The last row is the control the refusal must NOT consume: the eval face is what
//! this ticket deliberately keeps. The other two controls a `[_, _, ..]` arm must
//! leave alone — the 1-supplier and 0-supplier arms, the latter being every defaulted
//! spec-op call in the tree — are NOT copied here: they are
//! `the_carriers_own_member_still_beats_the_default` and
//! `a_carrier_with_no_supplier_still_runs_the_default` in
//! `wi1010_defaulted_op_instance_fact_test`, over the same fixture builder, and both
//! fail if this arm over-fires.
//!
//! REFERENCE: WI-1010; WI-842; WI-843; `docs/design/058-implementation.md` §12–§13.

use anthill_core::eval::EvalError;

/// WI-1010's fixture builder, not a copy of it: this ticket refuses the very program
/// that one drives, so the two must not drift. `tail` appends extra namespace items.
use crate::wi1010_defaulted_op_instance_fact_test::program;

/// The carrier's OWN member beside a fact binding a DIFFERENT operation — two runnable
/// implementations of one defaulted op for one carrier.
const TWO_SUPPLIERS_LEAF: &str =
    "    provides Desc[T = Leaf]\n    operation describe(x: Leaf) -> Int64 = 7\n";
const TWO_SUPPLIERS_TAIL: &str = "\n  operation otherDescribe(x: Leaf) -> Int64 = 9\n\n  \
     fact Desc[T = Leaf, describe = otherDescribe]\n";

fn two_suppliers(ns: &str, tail: &str) -> String {
    program(ns, TWO_SUPPLIERS_LEAF, TWO_SUPPLIERS_TAIL, tail)
}

/// The load errors of `src`, joined — panics if it loads CLEAN, which is the pre-fix
/// behaviour and must never read as a pass.
///
/// `pub(crate)` for WI-1027, the body-less half of this same refusal: the panic text IS
/// the contract ("loaded clean" must never read as a pass), and two copies of it can be
/// relaxed independently. Sibling-module reuse is the house pattern in this cluster —
/// this file already imports wi1010's fixture builder for the same reason.
pub(crate) fn refusal(src: &str) -> String {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal; the program loaded clean:\n{src}"))
        .join("\n")
}

/// Split a load error's `line:col: ` prefix from its message body. `pub(crate)` with
/// [`refusal`], so the ONE rendering (`load.rs`'s `line:col: message`) has ONE parser. Panics unless the
/// prefix is really a location — the span is half of what raising at the typer buys,
/// so a locationless rendering must fail rather than be silently accepted as the body.
pub(crate) fn located(msg: &str) -> (&str, &str) {
    let (loc, body) = msg
        .split_once(": ")
        .unwrap_or_else(|| panic!("expected a `line:col: message` rendering, got: {msg}"));
    let (line, col) = loc
        .split_once(':')
        .unwrap_or_else(|| panic!("expected `line:col`, got `{loc}` in: {msg}"));
    assert!(
        line.parse::<u32>().is_ok() && col.parse::<u32>().is_ok(),
        "expected numeric `line:col`, got `{loc}` in: {msg}",
    );
    (loc, body)
}

/// THE HEADLINE. Two suppliers, a concrete `Leaf`, refused at LOAD — naming the op,
/// the carrier, and each candidate BY ITS SUPPLY ROUTE, since the three routes are
/// written in three syntaxes and the author has to know which text to delete.
#[test]
fn a_concrete_carrier_tie_is_refused_at_load() {
    let ns = "test.wi1012.load";
    let msg = refusal(&two_suppliers(ns, ""));
    assert!(msg.contains("ambiguous dispatch"), "{msg}");
    assert!(
        msg.contains("Desc.describe"),
        "the spec op must be named: {msg}"
    );
    assert!(
        msg.contains("carrier `test.wi1012.load.Leaf`"),
        "the carrier must be named: {msg}"
    );
    assert!(
        msg.contains("the carrier's own member 'test.wi1012.load.Leaf.describe'"),
        "route 1 by route: {msg}",
    );
    assert!(
        msg.contains("an instance fact binding `describe = test.wi1012.load.otherDescribe`"),
        "route 2 quoted by the BINDING the author wrote (a fact has no name): {msg}",
    );
    // The span is half of what raising at the typer buys — it holds the CALL's span at
    // the moment it declines to pin, so the refusal renders `line:col` at the call and
    // not at the declarations, which are legal.
    let (_, body) = located(&msg);
    assert!(body.starts_with("ambiguous dispatch of `"), "{msg}");
}

/// COST (3), THE REASON THIS TICKET EXISTS — and the measurement that found it.
/// MEASURED BEFORE THE FIX: this exact program loaded CLEAN and `query_unary` on
/// `answer` returned `[]`. The rule reported the tie by not answering, because
/// `bridge_op_to_eval` residualizes every non-`Suspended` eval error to `None` (WI-483
/// substitution transparency) — inherited family policy, documented in
/// `docs/kernel-language.md` §"Where the ambiguity error is raised", and exactly the
/// "prefer a loud error over a silent skip" case.
///
/// WHAT THIS DOES AND DOES NOT DRIVE, stated because the assertion cannot tell them
/// apart. The refusal is raised on `probe`'s OPERATION body; the rule reaches the tie
/// only by CALLING `probe`, which is the route that residualized. So this pins that
/// the SLD-reachable program is now refused — but it would still pass if rule-body
/// typing were deleted outright. A rule body naming `Desc.describe` DIRECTLY is a
/// different program and is driven in `wi1026_rule_body_spec_op_dispatch_test`, which
/// removes THIS file's `probe` so the refusal cannot fire on the operation body and
/// mask what the rule does.
///
/// Asserted as a LOAD refusal rather than by re-driving the rule: once the program is
/// refused there is no KB to query, and "the query returns nothing" is precisely the
/// symptom that must stop being how this reports.
#[test]
fn a_rule_reaching_the_tie_through_an_operation_is_refused() {
    let ns = "test.wi1012.rule";
    let msg = refusal(&two_suppliers(ns, "\n  rule answer(?r) :- probe(?r)\n"));
    assert!(
        msg.contains("ambiguous dispatch") && msg.contains("Desc.describe"),
        "the operation the rule bridges into must report the tie at load: {msg}",
    );
}

/// COSTS (1) AND (2) — `anthill check` passing on a program the interpreter refuses,
/// and a tie that never reports because its code never RUNS. This fixture is the
/// second one: `probe` is called and answers, but the tie sits in the branch the
/// condition never takes. MEASURED with the refusal backed out: the program loads
/// clean and `probe()` answers 0, so no site ever raises. A refusal that only fires
/// where the interpreter happens to step is not a refusal of the program.
///
/// Distinct from `a_concrete_carrier_tie_is_refused_at_load` in exactly that: there the
/// call is on the ONLY path through `probe`, here it is on a path with no execution.
#[test]
fn a_tie_in_a_branch_that_never_runs_is_refused() {
    let ns = "test.wi1012.dead";
    let src = two_suppliers(ns, "")
        // `gt(1, 0)` is true, so the `else` arm never evaluates — but the typer types both
        // arms to join them, which is why the tie is visible to it and to nothing else.
        .replace(
            "operation probe() -> Int64 = Desc.describe(leaf())",
            "operation probe() -> Int64 = if gt(1, 0) then 0 else Desc.describe(leaf())",
        );
    assert!(
        src.contains("if gt(1, 0) then"),
        "fixture guard: the rewrite must have applied"
    );
    let msg = refusal(&src);
    assert!(
        msg.contains("ambiguous dispatch"),
        "a dead branch's tie must report: {msg}"
    );
}

/// THE EVAL FACE, KEPT ON PURPOSE — the control the load refusal must NOT consume.
/// `via_spec` takes an abstract-spec `Shape`, which `carrier_is_abstract_spec` makes
/// the typer defer on, so no static pin is possible and only the runtime value names
/// `Leaf`. The program LOADS (that is the assertion `interp_for` makes by not
/// panicking) and the CALL is refused.
#[test]
fn a_tie_on_an_abstract_carrier_is_still_refused_at_the_call() {
    let ns = "test.wi1012.abstract";
    let err = crate::common::interp_for(&abstract_carrier_program(ns))
        .call(&format!("{ns}.probe"), &[])
        .expect_err("two implementations, a carrier the typer cannot pin — refuse at the call");
    let EvalError::AmbiguousSpecOpDispatch {
        carrier,
        candidates,
        ..
    } = &err
    else {
        panic!("expected AmbiguousSpecOpDispatch, got {err:?}");
    };
    assert!(
        carrier.ends_with(".Leaf"),
        "the tie is per CARRIER: {carrier}"
    );
    assert_eq!(candidates.len(), 2, "both routes: {candidates:?}");
}

/// THE SHARED MESSAGE BODY. The same tie, twice: `Leaf` pinned statically (refused at
/// LOAD) and `Leaf` behind an abstract `Shape` (refused at the CALL). One sentence,
/// one owner — `kb::typing::ambiguous_spec_op_dispatch_message` — so the two faces of
/// one refusal cannot drift, the `unselected_instance_message` / `macro_rejection_message`
/// discipline.
///
/// Compared on the SENTENCE, with the namespace-dependent names removed, since the
/// load face prefixes `line:col` and names one namespace while the eval face names the
/// other. Both halves are asserted non-empty first, so a helper that silently returned
/// `""` could not pass this.
#[test]
fn both_faces_render_one_message_body() {
    let load_ns = "test.wi1012.same.load";
    let eval_ns = "test.wi1012.same.eval";
    let load_msg = refusal(&two_suppliers(load_ns, ""));
    let eval_err = crate::common::interp_for(&abstract_carrier_program(eval_ns))
        .call(&format!("{eval_ns}.probe"), &[])
        .expect_err("the eval face must still refuse");
    let eval_msg = eval_err.to_string();

    // Checked on the LOAD face only: the equality below makes the same six assertions
    // on the eval face redundant, and asserting them twice reads as two independent
    // checks when the second could never fail alone. These localize a wording change
    // to the clause that moved before the equality reports a whole-string diff.
    for phrase in [
        "ambiguous dispatch of `",
        "2 implementations are supplied for that carrier",
        "and nothing here selects one — keep exactly one and delete the rest",
        "No bracket names any of them",
        "the carrier's own member '",
        "an instance fact binding `describe = ",
    ] {
        assert!(
            load_msg.contains(phrase),
            "load face is missing `{phrase}`:\n{load_msg}"
        );
    }
    // The load face additionally carries `line:col: `, which the eval face has no source
    // text to resolve — strip exactly that prefix and the rest must be EQUAL, not merely
    // similar. `refusal` and `expect_err` already guarantee both sides are non-empty.
    let (_, load_body) = located(&load_msg);
    assert_eq!(
        load_body.replace(load_ns, "NS"),
        eval_msg.replace(eval_ns, "NS"),
        "the two faces must render ONE message body",
    );
}

/// WHY A NEW VARIANT rather than `TypeError::DispatchAmbiguous`, pinned at the text the
/// author reads. `DispatchAmbiguous` renders through `render_instance_tie`, which lists
/// PROVIDER symbols; here both routes are supplied FOR `Leaf` and canonicalize to it,
/// so that rendering would print the same name twice and — both being concrete — reach
/// `TieRepair::ValueDirected`, whose repair ("pin the carrier through the call's
/// receiver or its expected result type") cannot fix this: the carrier IS pinned, and
/// pinning it harder changes nothing.
#[test]
fn a_route_1_vs_2_tie_is_not_a_provider_tie() {
    let ns = "test.wi1012.notprovider";
    let msg = refusal(&two_suppliers(ns, ""));
    assert!(
        !msg.contains("each is a CONCRETE provider"),
        "the `TieRepair::ValueDirected` wording describes a different tie: {msg}",
    );
    assert!(
        !msg.contains("instances provide"),
        "`unselected_instance_message`'s provider framing does not apply: {msg}",
    );
    assert!(
        msg.matches("test.wi1012.notprovider.Leaf`").count() == 1,
        "the carrier is named ONCE, not listed twice as two providers would be: {msg}",
    );
    assert!(
        msg.contains("keep exactly one and delete the rest"),
        "the repair is deleting a TEXT, not writing a bracket: {msg}",
    );
}

/// The tie behind an ABSTRACT-SPEC receiver: `via_spec` takes a `Shape`, so the typer
/// cannot pin, and the runtime value's own sort is what reaches the two suppliers.
fn abstract_carrier_program(ns: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Shape
    sort E = ?
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Shape[E = Int64]
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  operation otherDescribe(x: Leaf) -> Int64 = 9

  fact Desc[T = Leaf, describe = otherDescribe]

  operation via_spec(s: Shape) -> Int64 = Desc.describe(s)
  operation probe() -> Int64 = via_spec(leaf())
end
"#
    )
}
