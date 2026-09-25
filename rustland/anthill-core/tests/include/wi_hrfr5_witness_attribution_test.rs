//! WI-20260917-HRFR5 — THE WRITTEN BRACKET CHOOSES A WITNESS, so two `require`s on one
//! spec are admitted however they were grounded.
//!
//! Before this, they were admitted only where every one was grounded by a TYPED HEAD
//! ANCHOR, because the anchor path was the only place the bracket was READ: reading it is
//! what chose the head binding. A witness was picked by SCAN ORDER, so two `require`s both
//! landed on the first call and nothing said which dictionary was which. The direct scan
//! now lets the bracket choose among candidate calls by their carrier argument's STATIC
//! sort, and `GroundedRequirement::anchored` is spelled `bracket_attributed` because
//! "an anchor grounded it" was only ever a proxy for "the bracket chose it".
//!
//! ## What is readable at LOAD is the whole boundary
//!
//! A witness goal carries its arguments and the carrier decision happens at FIRE time —
//! that is the design, and it is why `Desc.describe(?a, ?r)` at an ordinary variable can
//! be attributed to no bracket at all. Two argument shapes do name a sort at load: a
//! ground CONSTRUCTOR, and a TYPED head parameter (through the clause's own `bounds`, the
//! channel the anchor path already reads). Those two are this ticket's population, and
//! [`untyped_carriers_are_still_refused`] is the row that keeps the boundary honest.
//!
//! ## Why EXACTLY ONE match
//!
//! Two candidate calls at ONE carrier are two calls the same dictionary covers, and
//! choosing between them would be scan order wearing the bracket's name — so a bracket
//! that matches more than one candidate chooses nothing
//! ([`two_calls_at_one_carrier_are_still_refused`]).
//!
//! ## What was built and MEASURED AWAY: narrowing the weave
//!
//! A first cut also filtered what a bracket-chosen `require` COVERS to the calls whose
//! carrier it names, on the argument that two dictionaries would otherwise be woven into
//! each other's calls. Backing that out failed ZERO rows — including the acceptance — and
//! [`a_call_at_a_carrier_the_bracket_does_not_name_still_answers`] is why: the filter can
//! only engage where a carrier argument is READABLE, and exactly there the call is
//! VALUE-DIRECTED, so which dictionary it carries decides nothing. The weave decides
//! dispatch only for a CARRIER-LESS op (WI-20260909-NAR1X), which exposes no carrier
//! argument to select on. Deleted rather than shipped undriven.
//!
//! WI-20260911-5G28A S2 CHANGED THAT PREMISE, not the finding. A rule citation can now hand
//! a clause the dictionary its CALLER chose, which the argument cannot name, so the weave
//! covers a carrier-bearing body-less call too — AT ITS DICTIONARY'S CARRIER, narrowed by
//! the witness's carrier ARGUMENT rather than by the bracket's sort
//! (`collect_covered_calls`). [`a_typed_head_carrier_is_readable_too`] is what drives that
//! narrowing: with it backed out, each call is covered by both `require`s and the clause
//! is REFUSED by the one-dictionary-per-call check.
//!
//! ## Back-out
//!
//! With the selection backed out (the `chosen` computation forced to `None`) the two
//! acceptance rows fail: both `require`s go unattributed and the pair is refused, which is
//! exactly the behaviour this ticket lifts. The refusal rows pass either way BY DESIGN —
//! they are what says the lift did not become "admit two `require`s whenever a witness
//! grounds them", and the full workspace measured EXACTLY ONE row moving when this
//! landed: `wi_96ztm…::a_witness_grounded_pair_is_refused_whatever_the_bracket_says`,
//! whose message assertion was re-aimed at the new sentence and whose two shapes still
//! refuse.

use anthill_core::eval::Value;

/// `Thing` answers 7 through `Desc` and `Gadget` answers 9. `describe` is BODY-LESS in the
/// spec, so an absent dictionary is observable as no answer rather than as a default.
fn fixture(ns: &str, clause: &str, query: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Thing
    import anthill.prelude.Int64
    entity thing
    provides Desc[T = Thing]
    operation describe(x: Thing) -> Int64 = 7
  end

  sort Gadget
    import anthill.prelude.Int64
    entity gadget
    provides Desc[T = Gadget]
    operation describe(x: Gadget) -> Int64 = 9
  end

{clause}  rule answer(?r) :- {query}
end
"#
    )
}

fn answer(ns: &str, clause: &str, query: &str) -> Option<i64> {
    let mut kb = crate::common::load_kb_with(&fixture(ns, clause, query));
    match crate::common::query_unary(&mut kb, &format!("{ns}.answer")).as_slice() {
        [(Value::Int(i), true)] => Some(*i),
        _ => None,
    }
}

fn refusal(ns: &str, clause: &str, query: &str) -> String {
    crate::common::try_load_kb_with(&fixture(ns, clause, query))
        .err()
        .unwrap_or_else(|| panic!("expected a refusal; it loaded clean"))
        .join("\n")
}

/// Two `require`s, two calls, GROUND carriers — one clause answers both carriers' numbers.
const GROUND: &str = "  rule two(?r1, ?r2) :- ?d1 = require[Desc[T = Thing]], \
     ?d2 = require[Desc[T = Gadget]], Desc.describe(thing(), ?r1), \
     Desc.describe(gadget(), ?r2)\n";

/// The same pair with TYPED HEAD PARAMETERS as the carriers — read through the clause's
/// `bounds`. The witness scans run BEFORE the anchor, so these `require`s are
/// witness-grounded even though the head is typed; that is what made this shape the
/// gate's own population.
const TYPED: &str = "  rule two(a: Thing, b: Gadget, ?r1, ?r2) :- \
     ?d1 = require[Desc[T = Thing]], ?d2 = require[Desc[T = Gadget]], \
     Desc.describe(a, ?r1), Desc.describe(b, ?r2)\n";

/// THE ACCEPTANCE — a witness-grounded pair LOADS and each call dispatches through the
/// dictionary its own carrier names, asserted BY VALUE.
///
/// `describe` is body-less and each answer comes from a different provider, so 7 and 9
/// can only have arrived through two different dictionaries. Both slots are read, because
/// a single number would be satisfied by either dictionary reaching either call.
///
/// FAILS WITH THE SELECTION BACKED OUT — both `require`s go unattributed and the clause is
/// refused, which is the behaviour this ticket lifts.
#[test]
fn a_witness_grounded_pair_is_admitted_when_the_bracket_names_each_carrier() {
    assert_eq!(answer("test.hrfr5.g1", GROUND, "two(?r, ?)"), Some(7));
    assert_eq!(answer("test.hrfr5.g2", GROUND, "two(?, ?r)"), Some(9));
}

/// THE SAME PAIR THROUGH TYPED HEAD PARAMETERS, which is the shape the gate actually
/// guarded: a typed head does NOT make these `require`s anchor-grounded, because the
/// witness scans run first and a covered call is present.
#[test]
fn a_typed_head_carrier_is_readable_too() {
    assert_eq!(answer("test.hrfr5.t1", TYPED, "two(thing(), gadget(), ?r, ?)"), Some(7));
    assert_eq!(answer("test.hrfr5.t2", TYPED, "two(thing(), gadget(), ?, ?r)"), Some(9));
}

/// UNTYPED CARRIERS ARE STILL REFUSED — the boundary of what load-time attribution can
/// see, and the row that says this lift did not become "admit two `require`s whenever a
/// witness grounds them".
///
/// `?a` and `?b` are ordinary variables: their sorts are a run-time fact, so neither
/// bracket can name a call and admitting the pair would bind them by scan order. PASSES
/// EITHER WAY BY DESIGN — before this ticket the same clause was refused because nothing
/// was anchored.
#[test]
fn untyped_carriers_are_still_refused() {
    let errs = refusal(
        "test.hrfr5.u",
        "  rule two(?a, ?b, ?r1, ?r2) :- ?d1 = require[Desc[T = Thing]], \
         ?d2 = require[Desc[T = Gadget]], Desc.describe(?a, ?r1), Desc.describe(?b, ?r2)\n",
        "two(thing(), gadget(), ?r, ?)",
    );
    assert!(
        errs.contains("unless the WRITTEN BRACKET says which carrier each one means"),
        "got:\n{errs}"
    );
}

/// TWO CALLS AT ONE CARRIER ARE STILL REFUSED — "exactly one match", not "the first
/// match".
///
/// Both calls carry `thing()`, so `require[Desc[T = Thing]]` names both and choosing
/// between them would be scan order again. The second `require` names a carrier no call
/// has, so it is chosen by nothing either. PASSES EITHER WAY BY DESIGN.
#[test]
fn two_calls_at_one_carrier_are_still_refused() {
    let errs = refusal(
        "test.hrfr5.s",
        "  rule two(?r1, ?r2) :- ?d1 = require[Desc[T = Thing]], \
         ?d2 = require[Desc[T = Gadget]], Desc.describe(thing(), ?r1), \
         Desc.describe(thing(), ?r2)\n",
        "two(?r, ?)",
    );
    assert!(
        errs.contains("unless the WRITTEN BRACKET says which carrier each one means"),
        "got:\n{errs}"
    );
}

/// ONE `require` STILL COVERS EVERY CALL IT COVERED — one `require[Desc[T = Thing]]` and
/// two calls at `thing()`, both answering 7.
///
/// PASSES EITHER WAY BY DESIGN; it is the regression this change had to avoid, not
/// evidence for it. It is also what a narrowing filter would have had to keep true, and
/// checking that is how the filter came to be measured at all.
#[test]
fn one_require_still_covers_every_call_it_covered() {
    assert_eq!(
        answer(
            "test.hrfr5.c1",
            "  rule two(?r1, ?r2) :- ?d = require[Desc[T = Thing]], \
             Desc.describe(thing(), ?r1), Desc.describe(thing(), ?r2)\n",
            "two(?r, ?)",
        ),
        Some(7),
    );
    assert_eq!(
        answer(
            "test.hrfr5.c2",
            "  rule two(?r1, ?r2) :- ?d = require[Desc[T = Thing]], \
             Desc.describe(thing(), ?r1), Desc.describe(thing(), ?r2)\n",
            "two(?, ?r)",
        ),
        Some(7),
    );
}


/// A CALL AT A CARRIER THE BRACKET DOES NOT NAME STILL ANSWERS, and correctly — the row
/// that says narrowing the weave would have bought nothing.
///
/// One `require[Desc[T = Thing]]` beside calls at BOTH `thing()` and `gadget()`: the
/// second answers 9, its own carrier's number, though the only dictionary in the clause
/// is `Thing`'s. A carrier-bearing spec op is VALUE-DIRECTED — it dispatches on its
/// argument — so the dictionary woven into it does not decide its answer. That is the
/// whole reason the first cut's filter was unmeasurable, and it is measured here rather
/// than argued.
///
/// PASSES EITHER WAY BY DESIGN: it answered 7 and 9 before this ticket too. Its job is to
/// pin WHY the shipped change is smaller than it first was.
#[test]
fn a_call_at_a_carrier_the_bracket_does_not_name_still_answers() {
    const MIXED: &str = "  rule two(?r1, ?r2) :- ?d = require[Desc[T = Thing]], \
         Desc.describe(thing(), ?r1), Desc.describe(gadget(), ?r2)\n";
    assert_eq!(answer("test.hrfr5.m1", MIXED, "two(?r, ?)"), Some(7));
    assert_eq!(
        answer("test.hrfr5.m2", MIXED, "two(?, ?r)"),
        Some(9),
        "the `gadget()` call answers its OWN carrier's number with only `Thing`'s \
         dictionary in scope — value direction, not the weave"
    );
}
