//! WI-1035 — a DOT-spelled call must consult the supplier set, exactly as the
//! qualified spelling does. `leaf().describe(…)` resolved `describe` on the receiver's
//! sort BY NAME, took the carrier's own member, and never asked which spec that member
//! backs — so both load refusals built for this question (WI-1012's defaulted half,
//! WI-1027's body-less half) were unreachable through a dot.
//!
//! MEASURED before any code changed, on WI-1010's fixture with two suppliers, and the
//! last column is what makes it a defect rather than a spelling preference:
//!
//! | spec op | rival | site | `leaf().describe()` | `Desc.describe(leaf())` |
//! |---|---|---|---|---|
//! | defaulted (`= 1`) | instance fact | operation body | **7** | REFUSED |
//! | defaulted (`= 1`) | instance fact | rule body | **7** | REFUSED |
//! | body-less | instance fact | operation body | **7** | REFUSED |
//! | body-less | instance fact | rule body | **7** | REFUSED |
//! | body-less | witness sort | operation body | **7** | REFUSED |
//!
//! Row 5 is the loudest: the qualified spelling of that program answers 9 without the
//! WI-1027 guard and is REFUSED with it, while the dot answered 7 either way — the same
//! two texts, three different outcomes, decided by which spelling the author reached for.
//!
//! ## Which layer this is, since the mechanism looks like a name question
//!
//! It is not the §8.6 name ladder (WI-907/908/914). That ladder decides which NAME a
//! member resolves to and ends at an ambiguity; this is one layer down — given the
//! name, which of the texts SUPPLYING an implementation for this carrier wins — and
//! 058 §3.7 answers it identically for every reader: a read that selects goes loud on
//! the second candidate, never first-match. The carrier's own member is route 1 of that
//! set, not a rung.
//!
//! The call is still dispatched to the member, and the tempting reason for that is WRONG:
//! "rerouting re-types every `xs.map(f)` in the tree" is false by this ticket's own
//! number — `xs.map(f)` never reaches the guard, it resolves at the NEXT rung, which
//! already synthesizes the spec op. The real reason is that `find_spec_op_for_provided_-
//! sort` matches by SHORT NAME. That is the language's own notion of backing, and it is
//! sound for REFUSING (a same-named member beside a provision-supplied one IS the tie) and
//! unsound for CALLING: rerouting would invoke a different operation against the spec's
//! signature on the strength of a name match. Refusing costs a correct program a
//! diagnostic; rerouting would silently run something else.
//!
//! ## BLAST RADIUS — MEASURED, not predicted
//!
//! ZERO sites in the corpus. Counted at the guard itself over four cumulative loads
//! (stdlib + `anthill-stl`, then + `examples/`, + `anthill-todo/`, + `anthill-testcases/`):
//! 115 dots typed, 102 with a resolved receiver sort, and **0** of them resolving the
//! receiver's OWN member — so the guard's precondition never holds and nothing downstream
//! of it can fire. The full workspace suite agrees: on the first run after the guard
//! landed, 29 binaries and one failure — the row WI-1026 pinned for this ticket to flip.
//!
//! **COST IS UNEXERCISED, NOT MEASURED, and saying otherwise would be the wrong
//! measurement.** An A/B over the heaviest binary (`wi_tests`, guard live vs. env-gated
//! off in ONE build) gave 101.35 / 100.95 s vs. 101.76 / 101.24 s — but with 0 own-member
//! hits the guard body never executes on either side, so that pair compares two identical
//! runs and can only say the RESTRUCTURE is free. What it does not price is the change
//! the design makes deliberately: `find_spec_op_for_provided_sort` used to be paid on
//! own-member MISSES only (an `.or_else` the hit short-circuited) and is now paid on every
//! dot with a resolved receiver sort. That is the first-match blindness being removed, not
//! a defect — and it is real for a program that writes such dots, which the corpus does
//! not (`map.anthill` documents `m.size()` as exactly this shape; no source calls it).
//! The memo that would fix it is `WI-1011`'s, unforced by this site.
//!
//! ## What fails if this is backed out — MEASURED per piece, one revert each
//!
//! | test | dot guard | respan | both |
//! |---|---|---|---|
//! | `a_dot_spelled_operation_body_tie_is_refused_at_load` | **FAILS** | ok | **FAILS** |
//! | `a_dot_spelled_rule_body_tie_is_refused_at_load` | **FAILS** | ok | **FAILS** |
//! | `a_body_less_dot_tie_with_a_fact_rival_is_refused` | **FAILS** | ok | **FAILS** |
//! | `a_body_less_dot_tie_with_a_witness_rival_carries_the_witness_repair` | **FAILS** | ok | **FAILS** |
//! | `a_dot_on_a_provision_tie_refuses_as_a_supplier_tie` | **FAILS** | ok | **FAILS** |
//! | `the_dot_refusal_is_located_and_shares_the_qualified_spellings_body` | **FAILS** | **FAILS** | **FAILS** |
//! | `an_abstract_spec_receiver_is_not_refused` | ok | ok | ok |
//! | `one_supplier_through_a_dot_still_reaches_the_own_member` | ok | ok | ok |
//! | `one_fact_supplier_through_a_dot_still_reaches_the_binding` | ok | ok | ok |
//! | `a_carrier_with_no_supplier_still_runs_the_default_through_a_dot` | ok | ok | ok |
//! | `wi1026…::a_dot_spelled_operation_body_ties_exactly_as_the_rule_body_does` | **FAILS** | ok | **FAILS** |
//!
//! The four ok-either-way rows are the controls an over-firing guard consumes first, and
//! each is a different way of having ONE answer: the own member alone, a fact binding
//! alone, no supplier at all (the default, which is what makes a default a default), and
//! a receiver whose carrier is not statically pinned. The last is also the only test of
//! the WI-608 abstract-spec gate, which is otherwise invisible, and the pin for the
//! residual that gate leaves (**WI-1038**) — see it for both.
//!
//! ## The two conditions, and which one is actually exercised here
//!
//! The guard asks the DEFAULTED half's question with a bare count (nothing arbitrates a
//! defaulted op — its own block argues that at length) and delegates the BODY-LESS half
//! to `refuse_unarbitrated_supplier_tie`, whose extra route clause exists because
//! `dispatch_spec_op_cached` CAN weigh provisions. Stated plainly: at this call site that
//! clause is not known to be reachable. The guard runs only when the dot resolved an own
//! member, and an own member is a `SupplyRoute::Own` candidate, which is never
//! `weighed_by_provision_arbitration` — so the clause is satisfied whenever the count is.
//! It is not PROVABLY inert (`carrier_own_op` reads `sort_ops_lookup` while the dot reads
//! `find_operation_in_scope`, and the WI-616 doc records a shape where those differ), and
//! delegating keeps one owner for the condition either way. No test here drives it, and
//! this paragraph is instead of a control that would only look like one.
//!
//! The DEFAULTED half is NOT delegated — it repeats WI-1012's three-line condition,
//! because extracting it would make that arm's `[only]` pin walk the suppliers twice or
//! leave it matching an arm it can no longer reach. That creates a coupling nothing
//! enforces: a narrowing clause added to either count must be written at both. It is said
//! at the guard, and here, and in no third place.
//!
//! Tier 1 cannot apply at all: `Expr::DotApply` carries no `type_args`, so a dot is
//! bracket-less by construction — the same reason eval's bracket-less readers take the
//! bare count (WI-842). And an author-written `[simp]` dot rule is not pre-empted: it
//! fires earlier in the same frame and never reaches the guard, which is unchanged and
//! is not a silent first-match — a rewrite declared in the receiver's sort is a text
//! written for this receiver.
//!
//! ## The span, which was a second defect and not a polish
//!
//! The rule-body arms first refused at `1:1` — a WRONG location, not a missing one, and
//! the qualified spelling of the same program refuses at the call. `build_body_atom_-
//! occurrence` falls back to `materialize_from_handle` for reflect forms, and a rule-body
//! term has no `term_spans` entry, so the atom came back at offset 0 of source 0. Its own
//! doc has recorded that loss since WI-246. `respan_root` gives the materialized atom the
//! parse span the loader is already holding one line above. WI-1026 made "a rule-body
//! refusal is LOCATED" an invariant with a test; this keeps it true for the new arm.
//!
//! Reach is the ROOT only — a reflect form's interior, hence the inner dot of a chained
//! `a.b().c()`, still renders `1:1`. WI-246's "later work" note names no ticket and
//! WI-246 is delivered, so **WI-1039** now owns it.
//!
//! REFERENCE: WI-1026; WI-1012; WI-1027; WI-1010; WI-444; WI-246; WI-608; WI-1038; WI-1039;
//! `docs/design/058-implementation.md` §3.7, §4.9.

/// SIBLING-MODULE REUSE, the house pattern in this cluster (`wi1012` imports `wi1010`'s
/// builder; `wi1027` imports both). Every helper below was written here first and then
/// found to be BYTE-IDENTICAL to a sibling's, which is the drift `wi1012::refusal`'s doc
/// warns about — "two copies of it can be relaxed independently" — so they are imported
/// rather than kept. Aliased where this file's subject wants a different name:
///
///   * `defaulted` is `wi1026::program`, the DEFAULTED (`= 1`) builder with a free tail;
///   * `OWN` / `RIVAL_FACT` are `wi1026::TWO_LEAF` / `TWO_SUPPLY`, so `defaulted(ns, OWN,
///     RIVAL_FACT, tail)` IS `wi1026::two_suppliers(ns, tail)` — the same program its
///     row measured, which is what makes "the same tie, a different spelling" a fact
///     about one text rather than about two that happen to look alike.
///
/// [`body_less`] stays LOCAL and is the one thing not shared: WI-1027's own doc argues
/// that the ` = 1` token is the whole discriminator between the two guards, so a builder
/// that could emit either half would hide at each call site which half is under test.
/// (`wi1027::program` is that half but hardwires a QUALIFIED `probe`, which is the
/// spelling this file exists to contrast with.)
use crate::wi1010_defaulted_op_instance_fact_test::probe;
use crate::wi1012_static_supplier_tie_test::{located, refusal};
use crate::wi1026_rule_body_spec_op_dispatch_test::{
    answer, program as defaulted, TWO_LEAF as OWN, TWO_SUPPLY as RIVAL_FACT,
};
use crate::wi1027_bodyless_supplier_tie_test::{assert_supplier_tie, RIVAL_WITNESS};

/// A `describe` with NO default body — WI-1027's half. See the import block for why this
/// one is not shared.
fn body_less(ns: &str, leaf_body: &str, supply: &str, tail: &str) -> String {
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
{tail}end
"#
    )
}

/// ROUTE 1 ABSENT — the carrier declares the provision and no member, so the dot has no
/// own member to take and resolves through the provided spec instead. The only fixture
/// constant this file owns; `OWN` / `RIVAL_FACT` / `RIVAL_WITNESS` are imported above.
const NO_OWN: &str = "    provides Desc[T = Leaf]\n";

/// The DOT-spelled call sites. Both faces of every tie are asserted, because a test on
/// one alone would pass equally if the defect were the OTHER path's — which is exactly
/// how WI-1026 mis-attributed this one.
const DOT_OP: &str = "  operation probe() -> Int64 = leaf().describe()\n";
const DOT_RULE: &str = "  rule answer(?r) :- leaf().describe(?r)\n";

/// THE HEADLINE, defaulted half, operation body. This is the arm WI-1026 measured and
/// left: it answered 7 while the qualified spelling of the identical program was refused.
#[test]
fn a_dot_spelled_operation_body_tie_is_refused_at_load() {
    let ns = "test.wi1035.dotop";
    let msg = refusal(&defaulted(ns, OWN, RIVAL_FACT, DOT_OP));
    assert_supplier_tie(
        &msg,
        ns,
        &format!("an instance fact binding `describe = {ns}.otherDescribe`"),
    );
}

/// THE HEADLINE, defaulted half, rule body — the SAME dot one site over. Asserted
/// separately because WI-1026's control turned on exactly this pair agreeing: a test on
/// the rule-body arm alone would pass equally if this were a rule-body defect, and would
/// license closing it in the wrong place.
///
/// Asserted as a LOAD refusal, not by re-driving the rule: once refused there is no KB to
/// query, and "the query returns nothing" is the symptom that must stop being how this
/// reports (WI-1012's cost 3).
#[test]
fn a_dot_spelled_rule_body_tie_is_refused_at_load() {
    let ns = "test.wi1035.dotrule";
    let msg = refusal(&defaulted(ns, OWN, RIVAL_FACT, DOT_RULE));
    assert_supplier_tie(
        &msg,
        ns,
        &format!("an instance fact binding `describe = {ns}.otherDescribe`"),
    );
}

/// THE BODY-LESS HALF, which the ticket did not name and driving found. The dot bypassed
/// WI-1027's guard for the same reason it bypassed WI-1012's — the member is taken before
/// any spec is identified — so ONE fix closes both, and the condition each half is judged
/// by is delegated to the guard that owns it rather than re-derived here.
#[test]
fn a_body_less_dot_tie_with_a_fact_rival_is_refused() {
    let ns = "test.wi1035.blfact";
    let msg = refusal(&body_less(ns, OWN, RIVAL_FACT, DOT_OP));
    assert_supplier_tie(
        &msg,
        ns,
        &format!("an instance fact binding `describe = {ns}.otherDescribe`"),
    );
    // A body-less op HAS the dispatch slot a bracket binds, but neither rival here is
    // nameable, so the repair must still be `KeepOne` — the discriminator is the RIVAL's
    // kind, not the site's (WI-1027).
    assert!(
        msg.contains("No bracket names any of them"),
        "an own-member-vs-instance-fact tie has no nameable rival: {msg}",
    );
}

/// THE WORST ROW MEASURED. Through the dot this answered 7; the qualified spelling of the
/// same program answered 9 before WI-1027 and is refused after it. Two texts, three
/// outcomes, chosen by spelling.
///
/// It is also the only shape here that reaches `SupplierTieRepair::NameableWitness`, so it
/// pins that the repair is CARRIED from the candidates rather than assumed at the raising
/// site — the mistake WI-1012's own first cut made.
#[test]
fn a_body_less_dot_tie_with_a_witness_rival_carries_the_witness_repair() {
    let ns = "test.wi1035.blwitness";
    let own_no_provision = "    operation describe(x: Leaf) -> Int64 = 7\n";
    let msg = refusal(&body_less(ns, own_no_provision, RIVAL_WITNESS, DOT_OP));
    assert_supplier_tie(&msg, ns, &format!("witness sort '{ns}.Rival'"));
    assert!(
        msg.contains("route the call through an operation that can write `[Spec = Witness]`"),
        "a witness rival on a BODY-LESS op is nameable at a bracket-capable call, and the \
         repair must say so rather than inherit `keep exactly one`: {msg}",
    );
}

/// The `line:col` at which `needle` really occurs in `src` — 1-based on both axes,
/// which is the rendering `load.rs` produces. ASCII fixtures, so a byte offset within
/// the line IS its column. Panics when the needle is absent, so a fixture that drifts
/// away from the call this test is about fails rather than measuring the wrong line.
fn call_site(src: &str, needle: &str) -> String {
    let (i, line) = src
        .lines()
        .enumerate()
        .find(|(_, l)| l.contains(needle))
        .unwrap_or_else(|| panic!("fixture guard: {needle:?} is not in:\n{src}"));
    format!("{}:{}", i + 1, line.find(needle).expect("just matched") + 1)
}

/// ONE REFUSAL, THREE SPELLINGS. The dot in an operation body, the dot in a rule body and
/// the QUALIFIED call must produce the same message body — and each must be located AT
/// ITS OWN CALL.
///
/// Both halves are load-bearing and each is measured directly. Byte equality after
/// stripping `line:col` is what stops a fourth raising site from growing a fourth wording
/// (the `ambiguous_spec_op_dispatch_message` discipline WI-1012 built and WI-1026
/// extended). The location is compared against the offset the needle really has in the
/// fixture, NOT merely asserted to be numeric or to differ between fixtures: with
/// `respan_root` backed out the rule-body arm renders `1:1`, which is numeric, and which
/// differs from the other two — MEASURED, a first cut of this test asserted exactly those
/// two weaker things and passed with the respan gone.
#[test]
fn the_dot_refusal_is_located_and_shares_the_qualified_spellings_body() {
    // One namespace for all three, so the qualified names inside the message match and any
    // difference left is a difference of WORDING.
    let ns = "test.wi1035.faces";
    let split = |tail: &str, needle: &str| -> (String, String) {
        let src = defaulted(ns, OWN, RIVAL_FACT, tail);
        let msg = refusal(&src);
        let (loc, body) = located(&msg);
        assert_eq!(
            loc,
            call_site(&src, needle),
            "the refusal must be located at the CALL:\n{msg}",
        );
        (loc.to_string(), body.to_string())
    };
    let (dot_op_loc, dot_op_body) = split(DOT_OP, "leaf().describe()");
    let (dot_rule_loc, dot_rule_body) = split(DOT_RULE, "leaf().describe(?r)");
    let (_, qual_body) = split(
        "  operation probe() -> Int64 = Desc.describe(leaf())\n",
        "Desc.describe(leaf())",
    );

    assert_eq!(dot_op_body, qual_body, "one refusal, one message body — the spelling must not drift it");
    assert_eq!(dot_rule_body, qual_body, "and the rule-body face must not drift either");
    assert_ne!(
        dot_op_loc, dot_rule_loc,
        "fixture guard: the two dot fixtures must not sit at the same offset, or the \
         per-site check above would be one assertion made twice",
    );
}

/// THE STATED DIVERGENCE, PINNED SO IT IS A DECISION AND NOT A DRIFT. Add the carrier's
/// own provision beside a witness rival and the QUALIFIED spelling reports the PROVIDER
/// tie — `DispatchOutcome::Ambiguous`, which raises on its own account and which
/// `refuse_unarbitrated_supplier_tie`'s caller therefore excludes. The dot ran no dispatch
/// at all, so it has no outcome to yield to and reports the SUPPLIER tie instead.
///
/// Both refuse the same program at load and name the same two texts; only the sentence
/// differs. Asserted from both ends — the dot's wording AND the qualified spelling's on
/// the identical source — so a future change that unified them has to come here and say so
/// rather than flip one silently.
#[test]
fn a_dot_on_a_provision_tie_refuses_as_a_supplier_tie() {
    let ns = "test.wi1035.provisiontie";
    let dot = refusal(&body_less(ns, OWN, RIVAL_WITNESS, DOT_OP));
    assert!(
        dot.contains("the carrier's own member"),
        "the dot reports the SUPPLIER tie, by route: {dot}",
    );
    let qualified = refusal(&body_less(
        ns,
        OWN,
        RIVAL_WITNESS,
        "  operation probe() -> Int64 = Desc.describe(leaf())\n",
    ));
    assert!(
        qualified.contains("instances provide"),
        "fixture guard: the qualified spelling of THIS program must be the provider tie, \
         which is what makes the two sentences differ: {qualified}",
    );
}

/// CONTROL, and the only test of the WI-608 abstract-spec gate. `Coll` has no entity of
/// its own and `Leaf` provides it, so a `Coll`-typed receiver is not a static pin — its
/// runtime value is some concrete provider, and the suppliers of the SPEC sort are not
/// the suppliers of the value. `Coll` DOES resolve an own member here (a spec declaring
/// its own defaulted members is ordinary), and there are two suppliers for it, so without
/// the gate this program is refused at LOAD — which is the wrong half of the answer, since
/// WI-1012 deliberately leaves an abstract carrier to the CALL.
///
/// AND IT PINS A RESIDUAL — **WI-1038**, whose fixture this is. The dot answers `7`
/// silently while the QUALIFIED spelling of the identical program is refused at the call.
/// Both spellings are asserted here so the divergence is a recorded decision rather than a
/// silence: closing WI-1038 must come here and flip the first half. It is unchanged by
/// WI-1035 — the guard returns early on this receiver either way — and closing it needs
/// the dot to REACH the value-directed reader, which is the reroute this ticket declined
/// to take wholesale.
#[test]
fn an_abstract_spec_receiver_is_not_refused() {
    let ns = "test.wi1035.abstract";
    let program = |call: &str| {
        format!(
            r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Coll
    import anthill.prelude.Int64
    sort E = ?
    provides Desc[T = Coll]
    operation describe(x: Coll) -> Int64 = 7
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Coll[E = Int64]
  end

  operation otherDescribe(x: Coll) -> Int64 = 9

  fact Desc[T = Coll, describe = otherDescribe]

  operation viaSpec(c: Coll) -> Int64 = {call}
  operation probe() -> Int64 = viaSpec(leaf())
end
"#
        )
    };
    assert_eq!(
        probe(ns, &program("c.describe()")),
        7,
        "an abstract-spec receiver pins no carrier statically, so this load must not \
         refuse — the value-directed reader owns the question. The 7 is the statically \
         resolved own member RUNNING, not a verdict on which supplier should win (WI-1038)",
    );
    // The other spelling, on the same source, so the residual is measured and not assumed.
    // Asserted at the CALL: it loads clean (`interp_for` goes through `expect_loaded`), and
    // the refusal WI-1012 left to eval is what the dot does not reach.
    let err = crate::common::interp_for(&program("Desc.describe(c)"))
        .call(&format!("{ns}.probe"), &[])
        .expect_err("WI-1038: the qualified spelling must still refuse this tie at the call");
    assert!(
        format!("{err:?}").contains("AmbiguousSpecOpDispatch"),
        "WI-1038: the two spellings disagree — the dot answers 7 where this refuses. \
         Closing WI-1038 flips the FIRST assertion, not this one: {err:?}",
    );
}

/// CONTROL — the carrier's own member ALONE still reaches it through the dot. This is
/// every backed dot in the tree and an over-firing guard consumes it first.
#[test]
fn one_supplier_through_a_dot_still_reaches_the_own_member() {
    let ns = "test.wi1035.ownonly";
    assert_eq!(probe(ns, &defaulted(ns, OWN, "", DOT_OP)), 7, "one supplier, the own member");
    assert_eq!(
        answer(ns, &defaulted(ns, OWN, "", DOT_RULE)),
        7,
        "and through the rule-body dot, which is WI-1026's delivered pin",
    );
}

/// CONTROL — the OTHER side of the tie alone. With no own member the dot never reaches
/// this guard at all: it resolves through the provided spec, and WI-1010's rule decides
/// it. Pinned here because the guard must not disturb the ladder's second rung.
#[test]
fn one_fact_supplier_through_a_dot_still_reaches_the_binding() {
    let ns = "test.wi1035.factonly";
    assert_eq!(
        probe(ns, &defaulted(ns, NO_OWN, RIVAL_FACT, DOT_OP)),
        9,
        "the fact's `describe = otherDescribe` binding is the carrier's ONLY \
         implementation and must still be dispatched to",
    );
}

/// CONTROL — no supplier at all: the gap a default exists to fill. This is what makes a
/// default a default and it must not move.
#[test]
fn a_carrier_with_no_supplier_still_runs_the_default_through_a_dot() {
    let ns = "test.wi1035.gap";
    assert_eq!(
        probe(ns, &defaulted(ns, NO_OWN, "", DOT_OP)),
        1,
        "no supplier — the spec's default must still run",
    );
}
