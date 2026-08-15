//! WI-861 (proposal 058 §3.2 rung 2a, §3.6; phase 8c) — an UNSELECTED dispatch takes
//! the DEFAULT among the tied most-specific candidates.
//!
//! WI-860 built the relations and the index and left them with NO consumer. This is the
//! consumer, and it is one predicate — [`kb::defaults::default_among`] — asked at the two
//! populations a bracket-less dispatch can tie over:
//!
//!   * PROVISIONS, at `resolve_inner`'s `pick_most_specific` tie. Every classified
//!     dispatch, every requirement DICTIONARY the call site constructs
//!     (`build_dep_projection` Strategy 3) and every value-directed bridge
//!     (`resolve_bridge_requirements`) reads that one arbitration.
//!   * SUPPLIERS, at the three faces of `AmbiguousSpecOpDispatch` — eval's
//!     value-directed read and the two typer guards, which must agree or a program is
//!     refused at load and answered at run time.
//!
//! WHAT THE RUNG IS NOT: a ranking. **Specificity ranks first** (058 §3.2) — a strictly
//! more specific candidate wins silently and a default never displaces it — and the rung
//! fires only where the ladder had nothing left, i.e. exactly where tier 3 used to
//! refuse. Everything it decides was previously a loud error, so no program that
//! ANSWERED before answers differently: the flips are refusals becoming values.
//!
//! THE FLIP INVENTORY the ticket wrote before implementation lives partly elsewhere,
//! because a flip is asserted where its program already is:
//!
//!   * `wi844_sorted_set_driver_test::a_bare_compare_takes_the_hosts_own_ordering` —
//!     bracket-less `WeakOrd.compare` on a `String` beside two loadable witnesses;
//!   * `wi858_pair_orderings_test::a_bracketless_compare_takes_the_prelude_ordering` —
//!     the same over the prelude's `Pair`, which is the SHIPPED-LIBRARY reason this rung
//!     exists (WI-858: without it there is no spelling that reaches `Pair`'s canonical
//!     order once a program declares a rival, because §3.5 check 3 refuses `[Ord =
//!     Pair]`);
//!   * `wi1027_bodyless_supplier_tie_test::a_self_providing_carrier_now_answers_the_
//!     bracketless_call` and `wi1035_dot_member_supplier_tie_test::the_two_spellings_
//!     agree_when_a_default_answers` — the self-provider-plus-witness pair, whose old
//!     REFUSALS those two files owned, so the flip is asserted where the refusal was;
//!   * `wi842_bracketless_readers_test` and `wi855_ambiguous_requirement_test` moved
//!     their loud pins onto WITNESS-ONLY ties (a carrier providing nothing itself), which
//!     is what a tie no default answers now looks like — they are the controls;
//!   * `wi837_witness_eq_dispatch_test` — the `Eq` family, UNTOUCHED (flip 4 is that
//!     there is no flip); `a_marked_default_does_not_reopen_the_coherent_family` below
//!     asserts it from this side.
//!
//! AND ONE CLAUSE IS DRIVEN ENTIRELY ELSEWHERE, so it is named here rather than left to
//! be rediscovered: `default_among`'s *exactly one, never the first* is what keeps
//! `wi1027::a_runnable_member_no_longer_silently_outranks_a_fact_binding` refusing — its
//! two suppliers are the carrier's own member and the carrier's own instance fact, so
//! BOTH map to the carrier and a first-hit reading would take route order and load the
//! program. Measured as back-out 5.
//!
//! Reference: proposal 058 §3.2, §3.6; `docs/design/058-implementation.md` §3, §8 phase
//! 8c, §19 (the substrate).

use anthill_core::eval::{EvalError, Value};

// ── Fixture ──────────────────────────────────────────────────────────
//
// A local `Desc` spec with a depth-coded answer, so a WRONG provider shows up as a
// different number rather than as an error: `describe(leaf())` is 1 for the carrier's
// own implementation, 7 for `Rival`, 9 for `Other`, and `describe(wrapⁿ(…))` multiplies
// by ten and adds two per level — the `common::DESC_INSTANCES` coding, spelled locally
// because this file needs `Leaf` in BOTH the self-providing and the bare shape and the
// shared constant is only the first.

/// `Leaf` PROVIDES `Desc` itself — so 058 §3.6 infers `default_provider(Desc, Leaf,
/// Leaf)` and silence prefers its own implementation.
const LEAF_SELF: &str = r#"
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
"#;

/// `Leaf` with the SAME member and NO provision — no inferred row, so only a written
/// `DefaultProvider` mark can break a tie at this carrier. The "Money shape" of the
/// ticket's flip (5): a carrier whose orderings are all supplied from outside.
const LEAF_BARE: &str = r#"
  sort Leaf
    entity leaf
    operation describe(x: Leaf) -> Int64 = 1
  end
"#;

/// A WITNESS for `Leaf` — nameable, so it may coexist (058 §3.1).
const RIVAL: &str = r#"
  sort Rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
"#;

/// A SECOND witness, so a tie can be made that contains no self-provision at all.
const OTHER: &str = r#"
  sort Other
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 9
  end
"#;

/// The conditional provider whose BODY READS ITS DICTIONARY. `Holder.probe(wrap(leaf()))`
/// resolves `Desc[Wrap[Leaf]]` to this, whose own `Desc[T = E]` sub-goal is the tie —
/// so an answer here is evidence that a DICTIONARY was built, not merely that a dispatch
/// picked a symbol.
const WRAP: &str = r#"
  sort Wrap
    sort A = ?
    entity wrap(inner: A)
  end

  sort WrapDesc
    sort E = ?
    requires Desc[T = E]
    provides Desc[T = Wrap[A = E]]
    operation describe(w: Wrap[A = E]) -> Int64 =
      add(mul(10, Desc.describe(w.inner)), 2)
  end
"#;

/// A SORT-level `requires`, so the caller's dictionary is constructed at the CALL SITE
/// (`build_dep_projection` Strategy 3) — the sixth consumer WI-1091's measurement found,
/// and the one that answers `None` on a tie and leaves the callee's slot absent.
const HOLDER_SORT: &str = r#"
  sort Holder
    sort HT = ?
    requires Desc[T = HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
"#;

/// An OP-scoped `requires`, which (WI-562) is served by VALUE DIRECTION instead — the
/// route eval's `AmbiguousSpecOpDispatch` / `AmbiguousRequirement` reads guard.
const HOLDER_OP: &str = r#"
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
"#;

const MARK_RIVAL: &str = "  fact DefaultProvider(spec: Desc, provider: Rival)\n";

fn program(ns: &str, parts: &[&str]) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  import anthill.reflect.typing.DefaultProvider

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
{}
end
"#,
        parts.concat()
    )
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

/// Run `entry(0)` on a FRESH interpreter — a trapped call poisons later calls on a
/// shared one. `interp_for` panics on a dirty load, so a value assertion is also a
/// clean-load assertion.
fn eval_fresh(src: &str, entry: &str) -> Result<Value, EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    match eval_fresh(src, entry) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}\n{src}"),
    }
}

/// Enter `Holder.probe` FROM THE HOST with a `leaf()` value — no call site at all, so
/// the dispatch is value-directed and nothing could have selected.
fn probe_leaf_from_host(src: &str, ns: &str) -> Result<Value, EvalError> {
    let mut interp = crate::common::interp_for(src);
    let leaf_sym = interp.kb().resolve_symbol(&format!("{ns}.Leaf.leaf"));
    let leaf = Value::Entity {
        functor: leaf_sym,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
    interp.call(&format!("{ns}.Holder.probe"), &[leaf])
}

/// `Driver.drive(0)` calling `Holder.probe(arg)` — a typer-classified call site, which
/// is what makes the caller construct the dictionary.
fn driver(arg: &str) -> String {
    format!(
        "  sort Driver\n    operation drive(n: Int64) -> Int64 = Holder.probe({arg})\n  end\n"
    )
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage: an unknown sort must still fail to load, so every clean
/// load below is a real assertion and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    load_errs(&program(
        "wi861.control",
        &["  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end\n"],
    ));
}

// ── The rung itself, at the PROVISION tie ────────────────────────────

/// THE HEADLINE. A bracket-less call whose carrier PROVIDES the spec itself answers the
/// carrier's own implementation, with a nameable rival loaded beside it.
///
/// Backed out (delete the `.or_else(default_among_candidates)` in `resolve_inner`) this
/// is `LoadError::UnselectedInstance` — the tier-3 refusal — which is what the file's
/// own control below asserts by DELETING the provision instead.
#[test]
fn a_self_providing_carrier_answers_a_bracketless_call_beside_a_rival() {
    let ns = "wi861.own";
    let src = program(ns, &[LEAF_SELF, RIVAL, HOLDER_SORT, &driver("leaf()")]);
    assert_eq!(
        eval_int(&src, &format!("{ns}.Driver.drive"), "the tie must resolve"),
        1,
        "058 §3.6: the carrier's own provision is its default, so silence takes `Leaf`'s \
         own `describe` (1) and `Rival` stays opt-in"
    );
}

/// …AND IT IS THE DEFAULT DOING IT, NOT ROUTE ORDER. The identical program with the
/// RIVAL marked answers 7. This is the control that separates rung 2a from the
/// first-match reading WI-842 deleted — first match answers 1 either way.
///
/// The mark is legal here only because `Leaf` does NOT provide `Desc` in this arm:
/// marking a rival against a self-providing carrier is refused by `one_default`
/// (no-displacement, WI-860), which the next test asserts.
#[test]
fn a_marked_witness_answers_where_the_carrier_provides_nothing() {
    let ns = "wi861.marked";
    let src = program(
        ns,
        &[LEAF_BARE, RIVAL, OTHER, MARK_RIVAL, HOLDER_SORT, &driver("leaf()")],
    );
    assert_eq!(
        eval_int(&src, &format!("{ns}.Driver.drive"), "the mark must break the tie"),
        7,
        "the Money shape (058 §3.6): a carrier with no provision of its own, two \
         witnesses, and the application naming which one silence takes"
    );
}

/// …and UNMARKING restores the tier-3 refusal — the same program minus one line. Without
/// this arm the test above would pass equally if ties had simply stopped being refused.
#[test]
fn unmarking_the_witness_restores_the_tier_3_refusal() {
    let ns = "wi861.unmarked";
    let src = program(
        ns,
        &[LEAF_BARE, RIVAL, OTHER, HOLDER_SORT, &driver("leaf()")],
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("is ambiguous among providers")
                && e.contains("wi861.unmarked.Rival")
                && e.contains("wi861.unmarked.Other")
        }),
        "with no default row the tie must still be a loud error naming BOTH witnesses: \
         {errs:?}"
    );
}

/// SPECIFICITY RANKS FIRST (058 §3.2): a strictly more-specific candidate wins silently
/// and a marked default never displaces it. The mark names the PARAMETRIC provider; the
/// call is at the GROUND carrier, where a more specific provision exists, and it wins.
///
/// The control is the same program with the ground provision deleted: the mark then
/// decides, so this test measures the ORDER of the two rungs and not merely that the
/// ground provider works.
#[test]
fn a_more_specific_candidate_beats_a_marked_default() {
    const BOX: &str = r#"
  sort Box
    sort B = ?
    entity box(inner: B)
  end

  sort GenBox
    sort E = ?
    provides Desc[T = Box[B = E]]
    operation describe(b: Box[B = E]) -> Int64 = 5
  end
"#;
    const INT_BOX: &str = r#"
  sort IntBox
    provides Desc[T = Box[B = Int64]]
    operation describe(b: Box[B = Int64]) -> Int64 = 8
  end
"#;
    const MARK_GEN: &str = "  fact DefaultProvider(spec: Desc, provider: GenBox)\n";
    let call = "  sort Driver\n    \
                operation drive(n: Int64) -> Int64 = Holder.probe(box(inner: 3))\n  end\n";

    let ns = "wi861.specific";
    let both = program(ns, &[BOX, INT_BOX, MARK_GEN, HOLDER_SORT, call]);
    assert_eq!(
        eval_int(&both, &format!("{ns}.Driver.drive"), "specificity must rank first"),
        8,
        "`IntBox`'s ground `Desc[Box[Int64]]` is strictly more specific than the marked \
         `GenBox`'s `Desc[Box[E]]` — a default is a FALLBACK, not a competitor, so it \
         may not displace a candidate that outranks it"
    );

    let ns = "wi861.specific.only";
    let general_only = program(ns, &[BOX, MARK_GEN, HOLDER_SORT, call]);
    assert_eq!(
        eval_int(
            &general_only,
            &format!("{ns}.Driver.drive"),
            "the parametric provider must be reachable at all"
        ),
        5,
        "THE CONTROL: with the ground rival deleted the parametric provider answers, so \
         the 8 above is specificity winning and not `GenBox` being unusable"
    );
}

// ── Consumer 6: the requirement DICTIONARY, not merely a dispatch ─────

/// THE SIXTH CONSUMER (WI-1091's measurement): `build_dep_projection` Strategy 3 answers
/// `None` on an `Ambiguous` resolution and leaves the callee's requirement slot ABSENT —
/// silently, since that producer is best-effort. So the rung has to be read by the
/// CONSTRUCTION and not only by the classifier's verdict.
///
/// Asserted as a VALUE that only a built dictionary can produce: `WrapDesc.describe`
/// reads its own `Desc[T = E]` slot, and its answer is depth-coded, so 12 = 10·1 + 2 is
/// evidence that the slot was filled with `Leaf`'s instance. A dispatch that merely
/// "chose" and left the slot empty dies `DeferToRequirement: … not bound`.
#[test]
fn a_tied_sub_goal_with_a_default_builds_the_dictionary() {
    let ns = "wi861.dict";
    let src = program(
        ns,
        &[LEAF_SELF, RIVAL, WRAP, HOLDER_SORT, &driver("wrap(inner: leaf())")],
    );
    assert_eq!(
        eval_int(&src, &format!("{ns}.Driver.drive"), "the dictionary must be built"),
        12,
        "10·describe(leaf) + 2 — the conditional provider's `Desc[T = Leaf]` slot tied \
         and the default filled it; an absent slot raises instead of answering"
    );
}

/// …and the dictionary carries the DEFAULT'S provider rather than a first match: with
/// the rival marked (and `Leaf` bare, so the mark is legal) the same call answers 72.
#[test]
fn the_built_dictionary_carries_the_marked_provider() {
    let ns = "wi861.dict.marked";
    let src = program(
        ns,
        &[
            LEAF_BARE,
            RIVAL,
            OTHER,
            MARK_RIVAL,
            WRAP,
            HOLDER_SORT,
            &driver("wrap(inner: leaf())"),
        ],
    );
    assert_eq!(
        eval_int(&src, &format!("{ns}.Driver.drive"), "the mark must reach the slot"),
        72,
        "10·7 + 2 — the sub-goal's dictionary is `Rival`'s because the mark says so; a \
         12 here would mean the slot was filled by route order"
    );
}

// ── Consumer 3: the value-directed reads ─────────────────────────────

/// FLIP (3), eval's `AmbiguousSpecOpDispatch`: a value-directed dispatch whose tied
/// suppliers include the CARRIER'S OWN takes it, because the carrier's own provision is
/// its inferred default. Entered from the HOST, so no call site could have selected.
#[test]
fn a_value_directed_tie_takes_the_carriers_own_supplier() {
    let ns = "wi861.vd.own";
    let src = program(ns, &[LEAF_SELF, RIVAL, HOLDER_OP]);
    assert!(
        matches!(probe_leaf_from_host(&src, ns), Ok(Value::Int(1))),
        "the carrier's own member answers; got {:?}",
        probe_leaf_from_host(&src, ns)
    );
}

/// …the MARKED twin, so the answer is attributable to the default and not to route
/// order (which put the carrier's own member first and would answer 1 here too).
#[test]
fn a_value_directed_tie_takes_the_marked_witness() {
    let ns = "wi861.vd.marked";
    let src = program(ns, &[LEAF_BARE, RIVAL, OTHER, MARK_RIVAL, HOLDER_OP]);
    assert!(
        matches!(probe_leaf_from_host(&src, ns), Ok(Value::Int(7))),
        "the marked witness answers; got {:?}",
        probe_leaf_from_host(&src, ns)
    );
}

/// THE CONTROL FLIP (3) NAMES: a WITNESS-ONLY tie with no default keeps the diagnostic.
/// This is what makes the two tests above evidence of a rung rather than of the refusal
/// having been weakened.
///
/// **WI-1091 MOVED WHICH DIAGNOSTIC, not whether there is one.** `Holder.probe`'s
/// requirement is OP-SCOPED, and WI-1091 widened the placement so its body's
/// `Desc.describe(x)` reads the slot that licence names instead of being served by
/// value-direction. The question the runtime asks therefore changed from "which SUPPLIER
/// of `describe` for `Leaf`?" (`AmbiguousSpecOpDispatch`) to "which `Desc[Leaf]`
/// INSTANCE?" (`AmbiguousRequirement`) — one step earlier, at the dictionary this call
/// could not build. Both name `Rival` and `Other`, which is what this control is for; the
/// supplier-tie rendering is still pinned by the sibling
/// [`a_bodyless_own_member_beside_a_marked_witness_takes_the_default`]'s unmarked control
/// and by wi1012/wi1027's load refusals.
///
/// BACKED OUT (WI-1091's widening reverted): `AmbiguousSpecOpDispatch` naming the same
/// two witnesses — so this row measures the rung either way, and only the error's NAME
/// moves with the placement.
#[test]
fn a_witness_only_value_directed_tie_stays_loud() {
    let ns = "wi861.vd.loud";
    let src = program(ns, &[LEAF_BARE, RIVAL, OTHER, HOLDER_OP]);
    let err = probe_leaf_from_host(&src, ns).unwrap_err();
    let EvalError::AmbiguousRequirement {
        requirement,
        candidates,
        ..
    } = &err
    else {
        panic!("expected the tie to stay loud with no default row; got {err:?}")
    };
    assert!(
        requirement.contains("Desc") && requirement.contains("Leaf"),
        "the tie must name the REQUIREMENT that could not be built (`Desc[T = Leaf]`); \
         got `{requirement}`"
    );
    assert!(
        candidates.iter().any(|c| c.contains("Rival"))
            && candidates.iter().any(|c| c.contains("Other")),
        "both witnesses must still be named: {candidates:?}"
    );
}

// ── The two typer guards read the SAME arbitration ───────────────────

/// THE BODY-LESS GUARD (`refuse_unarbitrated_supplier_tie`, WI-1027) declines when the
/// rung answers — and this is the test that makes its licence MEASURED rather than
/// argued, because that guard selects nothing: it refuses or steps aside, and the
/// dispatch is then made by `resolve_inner`. The value asserts the two agreed.
///
/// The shape: `Leaf` has an own `describe` and NO provision (so it is a supplier the
/// provision arbitration cannot weigh — the guard's whole condition), `Rival` provides
/// and is MARKED. The rung names `Rival`, `resolve_inner` resolves `Unique(Rival)`, and
/// 7 is both answers agreeing.
#[test]
fn a_bodyless_own_member_beside_a_marked_witness_takes_the_default() {
    let ns = "wi861.guard";
    let call = "  sort Use\n    \
                operation use(x: Leaf) -> Int64 = Desc.describe(x)\n  end\n  \
                sort Driver\n    \
                operation drive(n: Int64) -> Int64 = Use.use(leaf())\n  end\n";
    let src = program(ns, &[LEAF_BARE, RIVAL, MARK_RIVAL, call]);
    assert_eq!(
        eval_int(&src, &format!("{ns}.Driver.drive"), "the guard must step aside"),
        7,
        "the guard declined and the dispatch landed on the same provider the rung named \
         — a 1 here would mean the carrier's unweighed own member won anyway"
    );

    // THE CONTROL: unmarked, the guard refuses, naming both supply ROUTES.
    let unmarked = program(ns, &[LEAF_BARE, RIVAL, call]);
    let errs = load_errs(&unmarked);
    assert!(
        errs.iter()
            .any(|e| e.contains("own member") && e.contains("witness sort")),
        "with no default the body-less guard must still refuse, naming both routes: \
         {errs:?}"
    );
}

/// THE DOT SPELLING agrees with the qualified one on the BODY-LESS half too — the half
/// the first cut of this ticket got wrong, and the reason `dot_takes_or_reroutes` is one
/// owner rather than a test in each branch.
///
/// MEASURED on this exact program before the fix (found by /code-review, not by the
/// suite): `Desc.describe(x)` answered 7 while `x.describe()` answered 1, because the
/// body-less branch consulted the rung — its guard had learned to decline — and then
/// returned `Take` regardless, calling the very member the default did NOT name. Before
/// WI-861 the program was refused at load, so the divergence was new: the spelling-keyed
/// silence WI-1035 exists to close, re-created by its own successor.
#[test]
fn the_dot_spelling_reads_the_same_arbitration_on_a_bodyless_op() {
    let ns = "wi861.dot.bodyless";
    let call = "  sort Driver\n    \
                operation dotted(n: Int64) -> Int64 = leaf().describe()\n    \
                operation qualified(n: Int64) -> Int64 = Desc.describe(leaf())\n  end\n";
    let src = program(ns, &[LEAF_BARE, RIVAL, MARK_RIVAL, call]);
    let dotted = eval_int(&src, &format!("{ns}.Driver.dotted"), "the dot must dispatch");
    let qualified = eval_int(
        &src,
        &format!("{ns}.Driver.qualified"),
        "the qualified spelling must dispatch",
    );
    assert_eq!(
        (dotted, qualified),
        (7, 7),
        "the mark names `Rival`, so NEITHER spelling may take `Leaf`'s own member (1)"
    );
}

/// …and the SOLE-supplier control for the same owner: `chosen` is `Some` for one supplier
/// too, so a reroute that did not gate on a TIE would change what an ordinary dot calls.
///
/// The shape that makes it reachable is `carrier_override_suppliers`' interpretability
/// filter: `Leaf` DECLARES `describe2` with no body, so it is dropped from the supplier
/// set and the witness is the only one left — one supplier whose target is not the member
/// the dot resolved. `Take` is the answer, as it was before this ticket; measured 7 (the
/// witness, reached through the ordinary defaulted path) only if the reroute over-fires.
#[test]
fn a_sole_supplier_dot_still_takes_its_member() {
    let ns = "wi861.dot.sole";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Desc2
    sort T = ?
    operation describe2(x: T) -> Int64 = 1
  end

  sort Leaf
    entity leaf
    operation describe2(x: Leaf) -> Int64
  end

  sort Rival2
    provides Desc2[T = Leaf]
    operation describe2(x: Leaf) -> Int64 = 7
  end

  sort Driver
    operation dotted(n: Int64) -> Int64 = leaf().describe2()
  end
end
"#
    );
    // No default row exists at all here (`Leaf` provides nothing, nothing is marked), so
    // the rung never speaks — and the dot must behave exactly as it did before WI-861.
    // Backed out (drop the `cands.len() >= 2` gate) this answers the witness instead.
    let got = eval_fresh(&src, &format!("{ns}.Driver.dotted"));
    assert!(
        !matches!(got, Ok(Value::Int(7))),
        "a SOLE supplier is not a tie and must not reroute the dot: got {got:?}"
    );
}

/// THE DEFAULTED half of the same rule (WI-1035's population), where the default names a
/// WITNESS — the case a `DotMember::Take` cannot express, since taking the receiver's own
/// member would answer 3 where `Desc2.describe2(x)` answers 7.
#[test]
fn the_dot_spelling_reads_the_same_arbitration() {
    let ns = "wi861.dot";
    // A DEFAULTED spec op, which is the population the dot's guard covers.
    let defaulted = r#"
  sort Desc2
    sort T = ?
    operation describe2(x: T) -> Int64 = 1
  end
"#;
    let leaf = r#"
  sort Leaf
    entity leaf
    operation describe2(x: Leaf) -> Int64 = 3
  end
"#;
    let rival = r#"
  sort Rival2
    provides Desc2[T = Leaf]
    operation describe2(x: Leaf) -> Int64 = 7
  end
"#;
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  import anthill.reflect.typing.DefaultProvider
{defaulted}{leaf}{rival}  fact DefaultProvider(spec: Desc2, provider: Rival2)
  sort Driver
    operation dotted(n: Int64) -> Int64 = leaf().describe2()
    operation qualified(n: Int64) -> Int64 = Desc2.describe2(leaf())
  end
end
"#
    );
    let dotted = eval_int(&src, &format!("{ns}.Driver.dotted"), "the dot must dispatch");
    let qualified = eval_int(
        &src,
        &format!("{ns}.Driver.qualified"),
        "the qualified spelling must dispatch",
    );
    assert_eq!(
        (dotted, qualified),
        (7, 7),
        "both spellings read one arbitration: the mark names `Rival2`, so the dot may \
         not keep the receiver's own member (3) while the qualified spelling takes 7"
    );
}

// ── Flip (4): the coherent family is UNTOUCHED ───────────────────────

/// FLIP (4) IS THAT THERE IS NO FLIP. The `Eq` family dispatches from UNIFICATION, where
/// no call site exists to select (058 §3.7), so two suppliers for one carrier are
/// refused at LOAD by `EqDispatchIndex` — before any rung is reached and regardless of
/// what a `DefaultProvider` row says. A default that silently re-opened the coherent
/// family would make `eq` mean two things in one program.
#[test]
fn a_marked_default_does_not_reopen_the_coherent_family() {
    let src = r#"
namespace wi861.coherent
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.reflect.typing.DefaultProvider

  sort Coin
    entity heads
    entity tails
    operation eq(a: Coin, b: Coin) -> Bool = true
  end

  sort CoinEqB
    provides PartialEq[T = Coin]
    operation eq(a: Coin, b: Coin) -> Bool = false
  end

  fact DefaultProvider(spec: PartialEq, provider: CoinEqB)
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("ambiguous") && e.contains("eq")),
        "the coherent family's LOAD refusal must stand with the mark present — a rung \
         consulted here would let one program answer `eq` two ways: {errs:?}"
    );
    // THE CONTROL: the same program with the carrier's own `eq` deleted loads, so the
    // refusal above is the two suppliers and not the mark itself being rejected.
    let one = src.replace(
        "    operation eq(a: Coin, b: Coin) -> Bool = true\n",
        "",
    );
    assert!(
        crate::common::try_load_kb_with(&one).is_ok(),
        "one supplier plus the mark must load: {:?}",
        crate::common::try_load_kb_with(&one).err()
    );
}
