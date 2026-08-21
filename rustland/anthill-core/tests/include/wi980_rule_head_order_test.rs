//! WI-980 / proposal 059 R6 — A RULE HEAD'S BINDING DOES NOT DEPEND ON DECLARATION
//! ORDER.
//!
//! THE POLICY IS NOT IN QUESTION HERE. §"A rule head functor is resolved, not declared"
//! (WI-896) already says it: the functor runs the ordinary ladder and the rule
//! contributes a clause to whatever it lands on; only where the ladder finds NOTHING
//! does the rule introduce the name, scoped where written. What was undefined is WHEN
//! "the ladder finds nothing" is evaluated — and it was evaluated against a half-built
//! name table, so textual order decided:
//!
//! ```text
//!   namespace s2                      namespace s1
//!     rule p(1)                         sort Rec
//!     sort Rec                            entity rec(n: Int64)
//!       entity rec(n: Int64)              rule p(2)
//!       rule p(2)                       end
//!     end                               rule p(1)
//!   end                               end
//!
//!   s2.p(2)=1   s2.Rec.p=<no symbol>    s1.p(2)=0   s1.Rec.p(2)=1
//! ```
//!
//! Same pair, opposite order, two different programs: ONE predicate with two clauses
//! versus TWO predicates with one clause each. It silently decides whether a rule
//! EXTENDS someone else's predicate, and extension is non-monotone — a true statement
//! becomes false and the proofs discharged from it were verified against a knowledge
//! base that no longer exists.
//!
//! Every row drives the GOAL. A rule head that binds nowhere still loads clean, so
//! "it loads" would keep passing through exactly the regression this suite exists for.
//!
//! ── WHAT THE ROWS ARE, AND WHICH ONES MEASURE THE FIX ────────────────────────
//!
//! FOUR CHANNELS, each in BOTH orders — because a pair that agrees in only one order
//! measures nothing:
//!
//! | channel | rule-first | rule-second |
//! |---|---|---|
//! | a sort body | control | **measures the fix** |
//! | a nested ordinary namespace | control | **measures the fix** |
//! | two FILES at one address | control | **measures the fix** |
//! | a `requires` parent | **measures the fix** | **measures the fix** |
//!
//! THE BACK-OUTS, all run, all present-but-wrong rather than deleted so the rule-first
//! rows cannot pass by accident. Each names the line, not the idea:
//!
//! * THE OWNERSHIP GUARD — in sub-pass 3's decision loop, gate on
//!   `name_denotes_for_rule_head(kb, head.name, head.scope)` instead of
//!   `decision.verdict(…)`, which is the pre-WI-980 guard: a table read while the same
//!   loop is filling it. VERIFIED, 11 rows fail — all three `*_rule_written_second`,
//!   BOTH `requires` rows, `mutual_visibility_…`, and five of the rows below. The three
//!   `*_rule_written_first` CONTROLS still pass, which is the point of having them.
//!   (Taking `Owned::Here` unconditionally is a DIFFERENT back-out and a blunter one —
//!   18 rows, controls included — because it also stops heads joining where they should.)
//! * `<global>`'s TWO ROLES — drop the `s == global` test from the overlay closure in
//!   [`Ownership::reach`], fusing "may own a name written at it" with "may be yielded
//!   to". VERIFIED, exactly 3 rows fail: [`a_global_head_is_never_yielded_to`] with its
//!   stdlib row emptied onto the user's predicate,
//!   [`a_global_head_absorbs_nothing_beside_a_cycle_or_a_nesting`], and
//!   [`a_top_level_head_beside_an_import_reports_rather_than_aborting`].
//! * THE ASKING FILE — `set_asking_file(None)` in place of `set_asking_file(Some(file))`
//!   in [`Ownership::reach`]. VERIFIED, 4 rows fail; named at
//!   [`a_head_binds_through_its_own_files_import`].
//! * THE SCC SCOPE — `let component = undecided.clone()` in place of
//!   `Self::sink_component(…)`, breaking a tie across everything still undecided rather
//!   than inside one strongly-connected component. VERIFIED, exactly 2 rows fail:
//!   [`a_cycle_does_not_reach_a_bystander`] and
//!   [`a_chain_deeper_than_any_recursion_loads`].
//!
//! Two recipes here used to name code that does not exist (`owners.owns(…)`, an
//! `Ownership::decide` overlay). This repo treats a stated back-out AS the measurement,
//! so a recipe that cannot be followed leaves its row asserting only "it loads".
//!
//! The three `*_rule_written_first` rows PASS EITHER WAY, by design — they are the
//! control, and without them a "fix" that made every inner head bind would look
//! correct. [`an_unmatched_inner_head_still_introduces`] is the other half of that
//! control: the fix must not make a genuinely-new inner name join something.
//!
//! THE THIRD CHANNEL IS NOT DECORATION. The per-file walk is what made the binding
//! order-dependent, so a fix that only reordered WITHIN a file would pass the first two
//! channels and leave the defect intact across files.
//!
//! THE FOURTH CHANNEL IS WHY THE GUARD WALKS `parents` AND NOT AN ADDRESS. A `requires`
//! parent sits at no particular address, so any key derived from the qualified NAME
//! answers it by text order — measured, an earlier attempt keyed on address depth left
//! [`requires_same_depth`] split in one order and joined in the other, and made
//! [`requires_target_deeper`] WORSE than before it. Both rows fail under that key and
//! pass under this one, which is what shows the guard asks about the same reach a
//! reference gets.
//!
//! AND `<global>` PLAYS ONE ROLE OF THE TWO — [`a_global_head_is_never_yielded_to`],
//! with [`the_documented_top_level_form_loads`] as the bound on it.
//!
//! ── WHY THE SECOND CHANNEL IS A NESTED NAMESPACE AND NOT A SECONDARY ENTRY ───
//!
//! WI-980 asks for the sort body and a proposal-059 SECONDARY ENTRY (`namespace Rec …
//! end` at the address of a sort). That spelling no longer loads: WI-1000 shipped 059
//! R3, which refuses every `rule` in a secondary entry outright.
//! [`a_rule_in_a_secondary_entry_is_still_refused`] pins that refusal, so the
//! substitution below is recorded rather than silent.
//!
//! The nested ORDINARY namespace is the right stand-in, and not a weaker one: R6 is a
//! claim about the ENCLOSING CHAIN, not about sorts, and 059's Definitions make an
//! ordinary namespace — an address with no main entry — the case "nothing in R3 or R4
//! reaches". It is also the overwhelmingly common shape. Two channels that differ in
//! what the inner scope IS, agreeing, is what shows the binding is keyed on the chain.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// How many solutions `pattern` has — the ticket's own instrument ("resolving the goal
/// after load; counts are answers"). Goes through the shipped query-pattern path, so a
/// pattern whose functor lands on a different symbol resolves against that symbol's
/// clauses, exactly as `anthill query` would.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The clauses stored under the symbol `qn` names, or `None` when nothing is named
/// `qn` at all — the PREDICATE IDENTITY half of the claim, which the answer counts
/// alone do not pin: a `Rec.p` that exists but is never reached would leave every
/// count unchanged.
fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

/// The whole claim, for one loaded program: `p` is ONE predicate with TWO clauses at
/// the namespace, the inner scope introduced NOTHING, and the goal the inner clause
/// answers is reachable through the namespace predicate.
///
/// `inner_qn` is asserted ABSENT rather than merely unreached, because that is the
/// difference between the two readings: the split program has a real `Rec.p` symbol
/// carrying the clause the namespace predicate then never sees.
fn assert_joined(kb: &mut KnowledgeBase, ns: &str, inner_qn: &str) {
    assert_eq!(
        clauses(kb, &format!("{ns}.p")),
        Some(2),
        "`{ns}.p` must be ONE predicate carrying BOTH clauses"
    );
    assert_eq!(
        clauses(kb, inner_qn),
        None,
        "`{inner_qn}` must not exist — in the finished program `p` resolves from \
         inside the inner scope, so the inner head introduces nothing (059 R6)"
    );
    // The inner clause's own answer, reached through the NAMESPACE predicate. This is
    // the row that reads 0 in the split program.
    assert_eq!(answers(kb, &format!("{ns}.p(2)")), 1, "{ns}.p(2)");
    assert_eq!(answers(kb, &format!("{ns}.p(1)")), 1, "{ns}.p(1)");
}

// ── Channel 1: a sort body ──────────────────────────────────────────────────

fn sort_body(ns: &str, rule_first: bool) -> String {
    let outer = "  rule p(1)\n";
    let inner = "  sort Rec\n    entity rec(n: Int64)\n    rule p(2)\n  end\n";
    let body = if rule_first {
        format!("{outer}{inner}")
    } else {
        format!("{inner}{outer}")
    };
    format!("namespace {ns}\n{body}end\n")
}

#[test]
fn sort_body_rule_written_first() {
    // CONTROL — PASSES EITHER WAY, BY DESIGN. The enclosing head is decided first
    // whether the order comes from the text or from the depth sort, so this row cannot
    // distinguish them. It is here so that the pair below means "the orders agree"
    // rather than "the second order happens to answer 1".
    let mut kb = crate::common::load_kb_with(&sort_body("wi980.body1", true));
    assert_joined(&mut kb, "wi980.body1", "wi980.body1.Rec.p");
}

#[test]
fn sort_body_rule_written_second() {
    // MEASURES THE FIX. BACKED OUT: `wi980.body2.Rec.p` exists with one clause,
    // `wi980.body2.p` has one, and `wi980.body2.p(2)` answers 0.
    //
    // This is also the ticket's "WATCH FOR" case — an inner and an outer head that
    // would EACH introduce, with nothing else declaring the name. Outermost-first is
    // what makes the inner one see the outer and join.
    let mut kb = crate::common::load_kb_with(&sort_body("wi980.body2", false));
    assert_joined(&mut kb, "wi980.body2", "wi980.body2.Rec.p");
}

// ── Channel 2: a nested ordinary namespace ──────────────────────────────────

fn nested_ns(ns: &str, rule_first: bool) -> String {
    let outer = "  rule p(1)\n";
    let inner = "  namespace inner\n    rule p(2)\n  end\n";
    let body = if rule_first {
        format!("{outer}{inner}")
    } else {
        format!("{inner}{outer}")
    };
    format!("namespace {ns}\n{body}end\n")
}

#[test]
fn nested_namespace_rule_written_first() {
    // CONTROL — passes either way, by design (see above).
    let mut kb = crate::common::load_kb_with(&nested_ns("wi980.nest1", true));
    assert_joined(&mut kb, "wi980.nest1", "wi980.nest1.inner.p");
}

#[test]
fn nested_namespace_rule_written_second() {
    // MEASURES THE FIX. BACKED OUT: `wi980.nest2.inner.p` exists and
    // `wi980.nest2.p(2)` answers 0. The inner scope is NOT a sort here, which is the
    // point — the guard walks resolution parents, not sort-ness.
    let mut kb = crate::common::load_kb_with(&nested_ns("wi980.nest2", false));
    assert_joined(&mut kb, "wi980.nest2", "wi980.nest2.inner.p");
}

// ── Channel 3: two FILES at one address ─────────────────────────────────────

const OUTER_FILE: &str = "namespace wi980.split\n  rule p(1)\nend\n";
const INNER_FILE: &str =
    "namespace wi980.split\n  sort Rec\n    entity rec(n: Int64)\n    rule p(2)\n  end\nend\n";

#[test]
fn cross_file_rule_written_first() {
    // CONTROL — passes either way, by design.
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        OUTER_FILE, INNER_FILE,
    ]));
    assert_joined(&mut kb, "wi980.split", "wi980.split.Rec.p");
}

#[test]
fn cross_file_rule_written_second() {
    // MEASURES THE FIX, and it is the row a within-file reordering would not reach:
    // sub-pass 3 used to decide each file's heads before looking at the next, so the
    // file the loader happens to read first decided the program. BACKED OUT:
    // `wi980.split.Rec.p` exists and `wi980.split.p(2)` answers 0.
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        INNER_FILE, OUTER_FILE,
    ]));
    assert_joined(&mut kb, "wi980.split", "wi980.split.Rec.p");
}

// ── What OWNERSHIP buys over "a head is written there" ──────────────────────

#[test]
fn a_head_that_binds_is_not_an_owner() {
    // THE ROW THAT MEASURES THE RECURSION, and without it nothing does — every other row
    // in this file passes with the overlay degraded to "a head is WRITTEN in that scope".
    //
    // `zdemo` WRITES a head named `q`, and does not OWN it: its head reaches `zlib.q`
    // through `zdemo`'s own `import zlib.*`, so nothing named `q` is created at `zdemo`.
    // The import is FILE-LOCAL (WI-995), so the third file cannot use it either — which
    // is why `Rec` must introduce its own `q` rather than yield to a scope holding
    // nothing. Reading the text instead of resolving it gets this exactly backwards.
    //
    // BACKED OUT (overlay reports `heads.contains_key(&(s, name))` instead of
    // `owns(s, name)`): this row FAILS — the whole program is refused, `Rec` having
    // yielded to a name that resolves nowhere for it. Every other row still passes.
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        "namespace zlib\n  rule q(1)\nend\n",
        "namespace zdemo\n  import zlib.*\n  rule q(2)\nend\n",
        "namespace zdemo\n  sort Rec\n    entity rec(n: Int64)\n    rule q(3)\n  end\nend\n",
    ]));
    assert_eq!(
        clauses(&kb, "zlib.q"),
        Some(2),
        "the importing file's head is a clause of the imported predicate"
    );
    assert_eq!(
        clauses(&kb, "zdemo.q"),
        None,
        "`zdemo` writes a head of that name and holds nothing under it"
    );
    assert_eq!(
        clauses(&kb, "zdemo.Rec.q"),
        Some(1),
        "so the sibling file's inner head introduces its own"
    );
    // DRIVEN both ways: each predicate answers its own clauses and not the other's.
    assert_eq!(answers(&mut kb, "zlib.q(2)"), 1);
    assert_eq!(answers(&mut kb, "zlib.q(3)"), 0);
    assert_eq!(answers(&mut kb, "zdemo.Rec.q(3)"), 1);
}

// ── The one shape ownership cannot decide ───────────────────────────────────

#[test]
fn mutual_visibility_introduces_separately_in_either_order() {
    // TWO SCOPES THAT CAN EACH SEE THE OTHER, one head name between them. Neither is
    // outermost, so no fact in the program names an owner — and each therefore
    // introduces its OWN.
    //
    // WHAT A *USE* THEN SEES, driven below rather than asserted in prose. A bare `p`
    // written in `mA` resolves to `mA`'s OWN `p` and stops: `resolve_in_scope` reads a
    // scope's `locals` and returns before it ever consults an import or a parent, so the
    // name each scope just introduced SHADOWS the wildcard import that made the cycle.
    // `mA.usesp(2)` therefore answers 0 — `mA`'s `import mB.*` is dead for `p`, silently.
    //
    // AN EARLIER VERSION OF THIS COMMENT CLAIMED THE OPPOSITE — that a bare `p` is
    // "reported by the ordinary resolver as `ambiguous symbol`, which is the right place
    // for it: the ambiguity is at the USE". That is structurally impossible for the
    // reason just given, it was never driven, and the row asserted only clause counts,
    // which are equally true of the silent shadow. It is corrected here rather than
    // quietly dropped because the claim was the whole justification for the design.
    //
    // WHETHER THE SHADOW IS RIGHT IS AN OPEN QUESTION, NOT A SETTLED ONE
    // (WI-20260821-E85J5). It is consistent with the rest of the language — a local beats
    // an import everywhere — but 059 R4 clause 3 refuses exactly this capture for
    // DECLARATIONS, and before WI-980 the cycle collapsed to one predicate so `p(2)` WAS
    // reachable from `mA`. This row pins the behaviour so that a change to it is visible;
    // it does not argue that the behaviour is correct.
    //
    // ORDER-FREE IS THE OTHER CLAIM. MEASURED under the demand-driven recursion this
    // replaced: `mA.p=2, mB.p=None` in one file order and the mirror in the other,
    // because the provisional answer the cycle re-entry handed back was memoised into
    // whichever arm was asked first.
    //
    // BACKED OUT (`let component = undecided.clone()` in place of `Self::sink_component`):
    // this test still passes — the cycle IS the whole undecided set here, so the two
    // agree. [`a_cycle_does_not_reach_a_bystander`] is the row that separates them, and
    // it is named here because this row alone would let that distinction go unmeasured.
    const A: &str = "namespace mA\n  import mB.*\n  rule p(1)\nend\n";
    const B: &str = "namespace mB\n  import mA.*\n  rule p(2)\nend\n";
    for files in [[A, B], [B, A]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&files));
        assert_eq!(
            clauses(&kb, "mA.p"),
            Some(1),
            "each scope keeps its own clause"
        );
        assert_eq!(clauses(&kb, "mB.p"), Some(1));
    }
    // DRIVE THE USE. Clause counts alone cannot tell the shadow from the alternative.
    const A_USES: &str =
        "namespace mA\n  import mB.*\n  rule p(1)\n  rule usesp(?x) :- p(?x)\nend\n";
    let mut kb =
        crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[A_USES, B]));
    assert_eq!(answers(&mut kb, "mA.usesp(1)"), 1, "its own clause is reached");
    assert_eq!(
        answers(&mut kb, "mA.usesp(2)"),
        0,
        "and the imported one is NOT — the local shadows the import that made the cycle"
    );
    // CONTROL — the same import, with nothing local to shadow it. This is what shows the
    // 0 above is the shadow and not a broken import.
    const A_NO_OWN: &str = "namespace mA\n  import mB.*\n  rule usesp(?x) :- p(?x)\nend\n";
    let mut ctrl =
        crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[A_NO_OWN, B]));
    assert_eq!(answers(&mut ctrl, "mA.usesp(2)"), 1, "CONTROL: the import works");
    assert_eq!(answers(&mut ctrl, "mA.usesp(1)"), 0, "CONTROL: nothing local exists");
}

#[test]
fn a_global_head_absorbs_nothing_beside_a_cycle_or_a_nesting() {
    // The `<global>` rule lives in `Ownership`'s overlay, which the DECISION consults.
    // Two shapes reach `<global>` by another route and must not absorb through it: a
    // mutual-import cycle (whose members introduce separately, so the trailing hole check
    // re-asks the ordinary ladder — and that ladder has no `<global>` rule), and an
    // ordinary enclosing join happening beside a top-level head of the same name.
    //
    // PASSES EITHER WAY TODAY, and is here because it did not always: the shape was
    // reachable while a cycle produced a "nobody owns it" verdict, and the per-site split
    // removed that verdict rather than the route. Nothing else pins the route.
    const G: &str = "rule p(0)\n";
    const A: &str = "namespace mA\n  import mB.*\n  rule p(1)\nend\n";
    const B: &str = "namespace mB\n  import mA.*\n  rule p(2)\nend\n";
    for files in [[G, A, B], [A, B, G]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&files));
        assert_eq!(
            clauses(&kb, "p"),
            Some(1),
            "the global head keeps its own clause"
        );
        assert_eq!(clauses(&kb, "mA.p"), Some(1));
        assert_eq!(clauses(&kb, "mB.p"), Some(1));
    }
    const N: &str =
        "namespace outer\n  rule p(1)\n  sort Rec\n    entity r(n: Int64)\n    rule p(2)\n  end\nend\n";
    for files in [[G, N], [N, G]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&files));
        assert_eq!(clauses(&kb, "p"), Some(1));
        assert_eq!(
            clauses(&kb, "outer.p"),
            Some(2),
            "the enclosing join is unaffected"
        );
        assert_eq!(clauses(&kb, "outer.Rec.p"), None);
    }
}

#[test]
fn a_cycle_does_not_reach_a_bystander() {
    // A SCOPE THAT MERELY REACHES A CYCLE IS NOT IN IT. `mA` and `mB` import each other;
    // `mC` imports `mA` and writes the same head name. The cycle is `mA`/`mB`'s business,
    // and what `mC` does must be decided the way it would be with no cycle at all: `mC`
    // imports a scope that OWNS `p`, so `mC`'s head is a CLAUSE of `mA.p`.
    //
    // THE CONTROL IS THE POINT, and this row did not have one. It used to assert
    // `mA.p`=1/`mB.p`=1/`mC.p`=1 — three predicates — which is the bystander being SPLIT
    // OFF by a cycle it is not in, pinned as if it were correct. The `NO_CYCLE` arm below
    // is what shows the difference: without the cycle all three join, so a `mC` that
    // stops joining the moment `mA` gains an import is the defect, not the requirement.
    //
    // BACKED OUT (break the tie across the whole undecided set instead of inside one
    // strongly-connected component): this test FAILS — `mC` is swept into the tie-break
    // with `mA`/`mB`, introduces its own `p`, and the two arms below disagree.
    const A: &str = "namespace mA\n  import mB.*\n  rule p(1)\nend\n";
    const NO_CYCLE: &str = "namespace mA\n  rule p(1)\nend\n";
    const B: &str = "namespace mB\n  import mA.*\n  rule p(2)\nend\n";
    const C: &str = "namespace mC\n  import mA.*\n  rule p(3)\nend\n";

    // CONTROL — no cycle. Everything joins `mA`, which is what an import MEANS.
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        NO_CYCLE, B, C,
    ]));
    assert_eq!(clauses(&kb, "mA.p"), Some(3), "CONTROL: all three join");
    assert_eq!(clauses(&kb, "mB.p"), None, "CONTROL");
    assert_eq!(clauses(&kb, "mC.p"), None, "CONTROL");

    // THE ROW. `mA`/`mB` tie and each introduces its own; `mC` is untouched by that and
    // still joins the scope it imports.
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[A, B, C]));
    assert_eq!(
        clauses(&kb, "mA.p"),
        Some(2),
        "`mA` owns its own clause and the bystander's"
    );
    assert_eq!(clauses(&kb, "mB.p"), Some(1), "the other cycle member owns its own");
    assert_eq!(
        clauses(&kb, "mC.p"),
        None,
        "the bystander introduces NOTHING — it imports a scope that owns `p`"
    );
}

#[test]
fn a_facade_importing_its_own_submodule_still_joins() {
    // ONE DOWNWARD WILDCARD IMPORT IS NOT A CYCLE, though the graph says otherwise: `fa`
    // sees `inner` through the import and `inner` sees `fa` through the ENCLOSING edge.
    // §"outermost-first" already names the winner between those two, so a facade
    // re-exporting its own submodule — an ordinary idiom — must keep joining.
    //
    // MEASURED before the tie-break: this program was REFUSED with two
    // `RuleHeadOwnedByNoScope` errors, while the identical program with distinct head
    // names, and the identical program without the import, both loaded.
    //
    // BACKED OUT (drop `encloses_a_cycle_member`, so an enclosure-related cycle is
    // treated as ambiguous): this test FAILS — `fa.p` and `fa.inner.p` split, one clause
    // each, where the enclosing join is the whole of WI-980's core case.
    let kb = crate::common::load_kb_with(
        "namespace fa\n  import fa.inner.*\n  rule p(1)\n  namespace inner\n    rule p(2)\n  end\nend\n",
    );
    assert_eq!(
        clauses(&kb, "fa.p"),
        Some(2),
        "the enclosing scope owns both clauses"
    );
    assert_eq!(clauses(&kb, "fa.inner.p"), None);
}

#[test]
fn a_chain_deeper_than_any_recursion_loads() {
    // NO BOUND, BECAUSE NO RECURSION. The first version of `Ownership` answered
    // `owns(scope, name)` by recursing through the resolver, nesting a whole walk per
    // link of the visible-scope chain — so its depth was proportional to that chain, and
    // MEASURED, 700 chained scopes sharing one head name ABORTED THE PROCESS (`thread …
    // has overflowed its stack`, SIGABRT) while the same 700 with DISTINCT head names
    // loaded clean. That forced an arbitrary `OWNERSHIP_MAX_DEPTH`, which bought a
    // located error at the price of refusing chains that used to load.
    //
    // The round-based fixpoint has no recursion to overflow: each round is a loop, and
    // `sink_component` closes over the undecided set iteratively. So the honest test is
    // no longer "the bound reports" but "the chain LOADS", and it drives the answer
    // rather than the loading.
    //
    // BACKED OUT (`let component = undecided.clone()` in place of `Self::sink_component`):
    // this test FAILS — settling every undecided scope at once collapses the chain
    // instead of walking it link by link. VERIFIED at this depth, not inherited from the
    // deeper version this row used to run at.
    //
    // WHAT THIS ROW DOES NOT MEASURE, said rather than implied. It does not reproduce the
    // stack overflow that forced the old `OWNERSHIP_MAX_DEPTH`, and no back-out available
    // in this tree can: that bound guarded a RECURSION which no longer exists, so there
    // is nothing left to restore it against. Reproducing the overflow needed ~700 links,
    // which is why the depth was cut. What is left is worth keeping on its own terms: a
    // chain far past any depth the recursive version could reach is decided, and decided
    // CORRECTLY, which is the claim a reader of this row needs.
    //
    // THE COST OF DECIDING A CHAIN IS SUPER-QUADRATIC — MEASURED, not reasoned. Marginal
    // ownership time (a shared head name minus a distinct-name control, so parse and
    // stdlib cost cancel), min of 3 in-process runs:
    //
    //     n = 200 -> 0.68s     n = 300 -> 2.33s     n = 400 -> 7.63s
    //
    // which is an exponent of 3.1 over 200->300 and 4.1 over 300->400. An earlier version
    // of this comment asserted QUADRATIC from the resolver-walk count alone; that is the
    // wrong term. One component settles per round, so there are O(n) rounds, and each
    // round costs O(n) resolver walks (rule 2 re-asks every undecided scope) plus O(n²)
    // for `sink_component`'s transitive closure. Anyone sizing a limit from the old
    // "quadratic" would have been wrong at scale. The optimistic reach — which does not
    // depend on `owners` — has since been hoisted out of the round loop, removing one
    // factor of n from the walk count; the closure is still per-round and is where the
    // remaining exponent lives.
    //
    // THE QUADRATIC COST IS TEMPORARY BY DESIGN. Every scope here is deciding something
    // its author could simply have said, which is proposal 061's whole argument: under an
    // explicit declaration this pass takes no decision, and both the machinery and this
    // row go with it.
    let n = PAST_THE_OLD_LIMIT;
    let mut files: Vec<String> = (0..n)
        .map(|i| {
            format!(
                "namespace deep{i}\n  import deep{}.*\n  rule p({i})\nend\n",
                i + 1
            )
        })
        .collect();
    files.push(format!("namespace deep{n}\n  rule p({n})\nend\n"));
    let refs: Vec<&str> = files.iter().map(|s| s.as_str()).collect();
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&refs));
    // THE CHAIN ALTERNATES, and that is correct rather than a wart: a WILDCARD IMPORT IS
    // NOT TRANSITIVE. `deep{n}` alone sees nothing, so it owns; `deep{n-1}` imports it
    // and joins; `deep{n-2}` imports `deep{n-1}`, which now owns NOTHING, and
    // `import deep{n-1}.*` does not re-export what `deep{n-1}` itself imported — so it
    // sees nothing and owns in its turn. (Measured independently at
    // [`nobody_yields_to_a_scope_that_mints_nothing`], where `sib` importing `fb` does
    // not reach the `ext` that `fb` imported.) Every EVEN index owns a pair.
    //
    // Asserting the STRUCTURE, not just the load: a chain that loaded while splitting
    // into 701 separate predicates, or collapsing into one, would pass a bare "it loads"
    // and both are the defects this row exists for.
    assert_eq!(clauses(&kb, &format!("deep{n}.p")), Some(2), "the far end owns a pair");
    assert_eq!(
        clauses(&kb, &format!("deep{}.p", n - 1)),
        None,
        "its importer joined it"
    );
    assert_eq!(
        clauses(&kb, &format!("deep{}.p", n - 2)),
        Some(2),
        "and the next link owns its own pair, the import being non-transitive"
    );
    // `deep0` is the head of the chain and nothing imports it, so its pair is a single.
    assert_eq!(clauses(&kb, "deep0.p"), Some(1), "the near end owns only its own");
    let total: usize = (0..=n)
        .filter_map(|i| clauses(&kb, &format!("deep{i}.p")))
        .sum();
    assert_eq!(total, n + 1, "every clause is accounted for, none on a bare intern");
}

/// Past the old `OWNERSHIP_MAX_DEPTH` (200) — deep enough that the recursive version
/// could not have decided this chain at all. EVEN, because the chain alternates
/// owner/yielder and the assertions read fixed indices off both ends.
const PAST_THE_OLD_LIMIT: usize = 260;

// ── The controls that bound the fix ─────────────────────────────────────────

#[test]
fn an_unmatched_inner_head_still_introduces() {
    // PASSES EITHER WAY, BY DESIGN — and it is why the rows above are evidence of a
    // BINDING rule rather than of a blanket one. Nothing named `q` encloses the sort,
    // so the inner head still introduces, still scoped where written (WI-894), and its
    // clause is still reachable there. A fix that made every inner head join an
    // enclosing scope would break this row and leave all six above green.
    let mut kb = crate::common::load_kb_with(
        "namespace wi980.fresh\n  rule p(1)\n  sort Rec\n    entity rec(n: Int64)\n    \
         rule q(2)\n  end\nend\n",
    );
    assert_eq!(clauses(&kb, "wi980.fresh.Rec.q"), Some(1));
    assert_eq!(clauses(&kb, "wi980.fresh.q"), None);
    assert_eq!(answers(&mut kb, "wi980.fresh.Rec.q(2)"), 1);
}

#[test]
fn a_rule_in_a_secondary_entry_is_still_refused() {
    // WI-980 asks for the SECONDARY-ENTRY spelling as the second channel. It does not
    // load: WI-1000 shipped 059 R3 after this ticket was written. Pinned here so the
    // substitution ([`nested_namespace_rule_written_second`]) is recorded rather than
    // silent — if R3's blanket ban is ever narrowed (WI-1001), this row fails and the
    // spelling the ticket actually named becomes available as a fourth channel.
    //
    // PASSES EITHER WAY, BY DESIGN: sub-pass 1b refuses before sub-pass 3 runs at all.
    for order in [
        "  rule p(1)\n  sort Rec\n    entity rec(n: Int64)\n  end\n  \
         namespace Rec\n    rule p(2)\n  end\n",
        "  sort Rec\n    entity rec(n: Int64)\n  end\n  namespace Rec\n    \
         rule p(2)\n  end\n  rule p(1)\n",
    ] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with(&format!("namespace wi980.sec\n{order}end\n")),
            &["`rule` is not allowed in a secondary entry of sort 'wi980.sec.Rec'"],
        );
    }
}

// ── The decision is taken ON BEHALF OF the file the head is written in ──────

/// A head that binds through a WILDCARD IMPORT, written in a file that is not the last
/// one scanned. Phase 2 runs outside the per-file loop, and an import resolves only in
/// the file that lists it (WI-995) — so the decision has to re-declare which file is
/// asking, or every head after the first file's is judged with some other file's
/// imports in scope.
///
/// The importing scope is DEEPER than the imported one on purpose, and a third file is
/// scanned LAST, so a stale asking-file is a DIFFERENT file's and the row cannot pass by
/// the two coinciding.
///
/// BACKED OUT (`Ownership::reach` asks with no file rather than the head's —
/// `set_asking_file(None)` in place of `set_asking_file(Some(file))`): this test FAILS,
/// along with THREE others — [`a_chain_deeper_than_any_recursion_loads`] (701 clauses
/// collapse to 1), [`a_cycle_does_not_reach_a_bystander`] and
/// [`a_head_that_binds_is_not_an_owner`]. With no file asking, every wildcard import is
/// filtered out, so `q` reaches nothing in `b` and the head mints
/// `wi980.viaimport.b.q`, splitting the predicate exactly as the order defect did.
///
/// AN EARLIER VERSION OF THIS NOTE NAMED THE WRONG LINE — sub-pass 3's PHASE 2
/// `set_asking_file` — and claimed this row was the only failure in the binary. Backing
/// that line out changes nothing: `reach` re-declares the asking file per site, so the
/// decision reaches the same verdict whatever phase 2 asked. The claim was never
/// measured; it is here as a reminder that a stated back-out is only worth what running
/// it is worth.
#[test]
fn a_head_binds_through_its_own_files_import() {
    const LIB: &str = "namespace wi980_lib\n  rule q(1)\nend\n";
    const IMPORTER: &str = "namespace wi980.viaimport.b\n  import wi980_lib.*\n  rule q(2)\nend\n";
    // A third file, scanned LAST, so a stale asking-file is a DIFFERENT file's and the
    // row cannot pass by the two coinciding.
    const TRAILING: &str = "namespace wi980.viaimport.z\n  rule unrelated(3)\nend\n";

    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        LIB, IMPORTER, TRAILING,
    ]));
    assert_eq!(
        clauses(&kb, "wi980_lib.q"),
        Some(2),
        "the importing file's head must join the imported predicate"
    );
    assert_eq!(
        clauses(&kb, "wi980.viaimport.b.q"),
        None,
        "`q` denotes in `b` through `b`'s OWN import, so the head introduces nothing"
    );
    assert_eq!(answers(&mut kb, "wi980_lib.q(2)"), 1);
}

// ── The three regressions found by review, each pinned ──────────────────────

#[test]
fn a_top_level_head_beside_an_import_reports_rather_than_aborting() {
    // A HEAD CAN REACH TWO OWNERS, and until this was fixed that ABORTED THE PROCESS.
    // The decision asks the ladder through an overlay that EXCLUDES `<global>` (a head
    // inside a namespace never yields to a name every file shares), while the loader's
    // own resolver of course still sees it. So `nb`'s head was decided "a clause of
    // `nd.p`" and then, once minted, found BOTH — a genuine ambiguity.
    //
    // MEASURED before the fix: `debug_assert_eq!` at kb/mod.rs — "head functor … is a
    // non-canonical same-FQN copy of resolved symbol" — aborted the test binary in every
    // file order, because `push_ambiguous_symbol` answered with `intern(name)` and for a
    // TOP-LEVEL candidate the short name IS the qualified name. In release, where the
    // assert is compiled out, the clause was stored under a divergent functor that (in
    // that assert's own words) "silently no-matches in both rule-firing indexes".
    //
    // BACKED OUT (`push_ambiguous_symbol` returns `self.kb.symbols.intern(name)` again):
    // this test does not fail — it ABORTS the whole test binary.
    const G: &str = "rule p(0)\n";
    const D: &str = "namespace nd\n  rule p(5)\nend\n";
    const B: &str = "namespace nb\n  import nd.*\n  rule p(93)\nend\n";
    for order in [[G, D, B], [D, B, G], [B, G, D]] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with_files(&order),
            &["ambiguous symbol 'p' in scope 'nb'"],
        );
    }
}

#[test]
fn a_facade_still_joins_one_level_deeper() {
    // THE SHIPPED FACADE ROW IS WRITTEN AT THE ONE DEPTH THAT USED TO WORK.
    // [`a_facade_importing_its_own_submodule_still_joins`] nests twice; MEASURED, adding
    // a THIRD level turned the same idiom into a three-error refusal, because the
    // tie-break scanned every head-writing scope by ADDRESS PREFIX instead of the actual
    // cycle's members. This row is that depth, and it is the control on the fix rather
    // than a repetition: the two-level row passes either way.
    //
    // BACKED OUT (`encloses_a_cycle_member`'s `scope_display_name(..).strip_prefix(..)`
    // scan over `self.heads.keys()` in place of `sink_component` + `SymbolTable::encloses`):
    // this test FAILS with "no scope introduces the rule head `p`", three times.
    let kb = crate::common::load_kb_with(
        "namespace fa\n  import fa.inner.*\n  rule p(1)\n  namespace inner\n    \
         rule p(2)\n    namespace deep\n      rule p(3)\n    end\n  end\nend\n",
    );
    assert_eq!(
        clauses(&kb, "fa.p"),
        Some(3),
        "the facade owns all three, at any nesting depth"
    );
    assert_eq!(clauses(&kb, "fa.inner.p"), None);
    assert_eq!(clauses(&kb, "fa.inner.deep.p"), None);
}

#[test]
fn nobody_yields_to_a_scope_that_mints_nothing() {
    // A HEAD MUST NEVER YIELD TO A PREDICATE THAT WILL NOT EXIST. `fb` imports its own
    // submodule AND `ext`; it yields to `ext`, so `fb.p` is never minted. `sib`, which
    // imports `fb`, must therefore NOT yield to `fb`.
    //
    // MEASURED before the fix: REFUSED — "no scope introduces the rule head 'p' written
    // in 'sib' … it yields to 'fb', which does not introduce it either". The tie-break
    // had memoised `owns(fb, p) = true` as a POLICY, discarding the value the loop
    // computed, so the overlay advertised an owner the mint loop never created.
    //
    // THE CONTROL IS THE SAME PROGRAM WITHOUT `import fb.inner.*` — one line, and it is
    // what shows the refusal was never about `sib`: it loaded clean before and must give
    // the IDENTICAL answer now.
    //
    // BACKED OUT (`owners_for`'s rule 2 admits a scope that reaches any CANDIDATE rather
    // than a settled OWNER): this test FAILS — `sib` yields into the hole again.
    const EXT: &str = "namespace ext\n  rule p(9)\nend\n";
    const FB: &str = "namespace fb\n  import fb.inner.*\n  import ext.*\n  rule p(1)\n  \
                      namespace inner\n    rule p(2)\n  end\nend\n";
    const FB_CONTROL: &str = "namespace fb\n  import ext.*\n  rule p(1)\n  \
                              namespace inner\n    rule p(2)\n  end\nend\n";
    const SIB: &str = "namespace sib\n  import fb.*\n  rule p(3)\nend\n";

    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[EXT, FB, SIB]));
    assert_eq!(clauses(&kb, "ext.p"), Some(3), "ext owns its own and both of fb's");
    assert_eq!(clauses(&kb, "fb.p"), None, "fb yields to ext, so it mints nothing");
    assert_eq!(clauses(&kb, "sib.p"), Some(1), "sib cannot see ext, so it introduces");

    let ctrl = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        EXT,
        FB_CONTROL,
        SIB,
    ]));
    assert_eq!(clauses(&ctrl, "ext.p"), Some(3), "CONTROL: identical without the import");
    assert_eq!(clauses(&ctrl, "fb.p"), None, "CONTROL");
    assert_eq!(clauses(&ctrl, "sib.p"), Some(1), "CONTROL");
}

#[test]
fn a_mutual_cycle_is_decided_the_same_in_every_file_order() {
    // THE TICKET'S OWN INVARIANT, over a shape that used to break it. Two mutually
    // importing namespaces and a nested scope under one of them: MEASURED before the
    // fix, four of the six file orders gave `nA.p` = 3 clauses with `nB.p` ABSENT and
    // the other two gave 2 and 1 — because a verdict computed under a provisional cycle
    // break was memoised and then read by a site outside the cycle.
    //
    // ALL SIX ORDERS, not two: the defect was invisible in four of them.
    //
    // BACKED OUT (memoise `reach` under the optimistic overlay and reuse it once owners
    // are settled): this test FAILS — the orders disagree again.
    const A: &str = "namespace nA\n  import nB.*\n  rule p(1)\nend\n";
    const B: &str = "namespace nB\n  import nA.*\n  rule p(2)\nend\n";
    const S: &str = "namespace nA.sub\n  rule p(3)\nend\n";
    for order in [[A, B, S], [A, S, B], [B, A, S], [B, S, A], [S, A, B], [S, B, A]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&order));
        assert_eq!(clauses(&kb, "nA.p"), Some(2), "nA.p, order {order:?}");
        assert_eq!(clauses(&kb, "nB.p"), Some(1), "nB.p, order {order:?}");
        assert_eq!(clauses(&kb, "nA.sub.p"), None, "nA.sub.p, order {order:?}");
    }
    // CONTROL — the nested scope writing a DIFFERENT name. One clause each, every order,
    // and it passes with or without the fix: without it the rows above would be
    // satisfied by any change that stopped the cycle members joining at all.
    const S2: &str = "namespace nA.sub\n  rule qq(3)\nend\n";
    for order in [[A, B, S2], [S2, A, B]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&order));
        assert_eq!(clauses(&kb, "nA.p"), Some(1), "CONTROL nA.p");
        assert_eq!(clauses(&kb, "nB.p"), Some(1), "CONTROL nB.p");
    }
}

// ── Channel 4: a `requires` parent ──────────────────────────────────────────
//
// NOT AN ENCLOSING SCOPE, and that is the whole reason these rows exist. `A requires
// Spec` puts `Spec`'s scope on `A`'s `parents` list, so a name written as a head in
// `Spec` is visible from `A` exactly as an enclosing scope's would be — but `Spec` sits
// at whatever address its author gave it, which may be shallower than `A`, deeper, or
// the same. Any guard keyed on the qualified NAME answers these by text order; only one
// that walks `parents` answers them at all.

/// `A requires Spec`, `p` written as a head in each. `nest_spec` puts `Spec` one
/// namespace deeper than `A`; `spec_first` is the text order. Returns
/// `(Spec.p clauses, A.p clauses)`.
fn requires_pair(
    ns: &str,
    spec_first: bool,
    nest_spec: bool,
) -> (Option<usize>, Option<usize>, usize) {
    let (spec, spec_qn) = if nest_spec {
        (
            "  namespace mid\n    sort Spec\n      rule p(2)\n    end\n  end\n".to_owned(),
            format!("{ns}.mid.Spec"),
        )
    } else {
        (
            "  sort Spec\n    rule p(2)\n  end\n".to_owned(),
            format!("{ns}.Spec"),
        )
    };
    let a =
        format!("  sort A\n    requires {spec_qn}\n    entity a(n: Int64)\n    rule p(1)\n  end\n");
    let body = if spec_first {
        format!("{spec}{a}")
    } else {
        format!("{a}{spec}")
    };
    let mut kb = crate::common::load_kb_with(&format!("namespace {ns}\n{body}end\n"));
    // THE GOAL IS DRIVEN, like every other channel. `A`'s clause reached through the
    // SPEC's predicate is the whole claim; a clause indexed under `Spec.p` but
    // unreachable by resolution would leave the counts alone and say nothing.
    let reached = answers(&mut kb, &format!("{spec_qn}.p(1)"));
    (
        clauses(&kb, &format!("{spec_qn}.p")),
        clauses(&kb, &format!("{ns}.A.p")),
        reached,
    )
}

#[test]
fn requires_same_depth() {
    // BOTH ORDERS MEASURE THE FIX, and they must AGREE. BACKED OUT, the
    // requirer-written-first order splits into 1 + 1 while the other joins — the same
    // silent flip the enclosing-chain rows show, on an edge address depth cannot see.
    //
    // The third element is `Spec.p(1)` DRIVEN: `A`'s clause is reachable through the
    // spec's predicate, which is what "joined" has to mean.
    assert_eq!(requires_pair("wi980.rq1", true, false), (Some(2), None, 1));
    assert_eq!(requires_pair("wi980.rq2", false, false), (Some(2), None, 1));
}

#[test]
fn requires_target_deeper() {
    // THE REQUIRED SORT NESTED DEEPER THAN ITS REQUIRER, in BOTH text orders — the
    // header's own rule, that a pair agreeing in only one order measures nothing.
    //
    // An address-derived key gets this exactly backwards: it decides the shallower `A`
    // first, so `Spec` never sees it and the pair SPLITS where plain text order had
    // joined them. Walking the resolution parents makes the direction of the `requires`
    // edge the only thing that matters, and the two orders agree.
    assert_eq!(requires_pair("wi980.rq3", true, true), (Some(2), None, 1));
    assert_eq!(requires_pair("wi980.rq4", false, true), (Some(2), None, 1));
}

// ── `<global>`'s two roles ──────────────────────────────────────────────────

#[test]
fn a_global_head_is_never_yielded_to() {
    // `<global>` HAS TWO ROLES AND THEY ARE NOT THE SAME. It may OWN a name written at
    // it — a namespace-less file is the language's own first form, taught by
    // kernel-language.md's `**Forms:**` block and by `examples/classic-mini/ancestor` —
    // and it must never be YIELDED TO, because it is the one scope every file in the
    // program shares and nobody opts into.
    //
    // MEASURED with the two fused: a one-line `rule modus_ponens(7, 8)` in a file with no
    // namespace made `anthill.logic.Constructive.Constructive.modus_ponens` CEASE TO
    // EXIST and put the stdlib's own axiom under the user's predicate, loading clean.
    // Fused the other way, a top-level head introduced NOTHING and fell to the WI-476
    // bare intern, silently.
    //
    // BACKED OUT (drop the `s != self.global` guard in `Ownership`'s overlay): the
    // stdlib row FAILS — its axiom's predicate is emptied onto the user's.
    let mut kb = crate::common::load_kb_with("rule modus_ponens(7, 8)\n");
    assert_eq!(
        clauses(&kb, "anthill.logic.Constructive.Constructive.modus_ponens"),
        Some(1),
        "the stdlib axiom keeps its own predicate"
    );
    assert_eq!(
        clauses(&kb, "modus_ponens"),
        Some(1),
        "and the top-level head owns the name it wrote, at `<global>`"
    );
    assert_ne!(
        kb.try_resolve_symbol("modus_ponens"),
        kb.try_resolve_symbol("anthill.logic.Constructive.Constructive.modus_ponens"),
        "two names, two symbols"
    );
    // THE CLAUSE COUNTS ARE THE MEASUREMENT, not a goal, and that is a limit of this
    // row rather than an omission. The stdlib axiom is GENERAL — its head has variables
    // — so it matches any pair a query could carry, and a goal cannot tell "answered by
    // its own clause" from "answered by the user's". `Some(1)` / `Some(1)` is what
    // discriminates: with the two roles fused it read `None` / `Some(2)`.
    assert_eq!(answers(&mut kb, "modus_ponens(7, 8)"), 1);
}

#[test]
fn the_documented_top_level_form_loads() {
    // kernel-language.md's `**Forms:**` block and `examples/classic-mini/ancestor/
    // README.md` both teach a namespace-less program. PASSES EITHER WAY today; it is
    // here because an earlier attempt at the row above REFUSED this shape, and five
    // documentation sites teach it.
    let mut kb = crate::common::load_kb_with(
        "rule parent(\"alice\", \"bob\")\nrule ancestor(?x, ?z) :- parent(?x, ?z)\n",
    );
    assert_eq!(clauses(&kb, "parent"), Some(1));
    assert_eq!(clauses(&kb, "ancestor"), Some(1));
    assert_eq!(answers(&mut kb, "ancestor(\"alice\", \"bob\")"), 1);
}

#[test]
fn the_captured_stdlib_predicate_survives() {
    // THE CONTROL FOR THE YIELD RULE — PASSES EITHER WAY, BY DESIGN, and it is here to
    // bound that rule rather than to measure it. The same short name, written inside a
    // namespace, must still be an ordinary new predicate: the stdlib axiom keeps its own
    // qualified name and its one clause, and the user gets one of their own. A guard
    // keyed on the NAME rather than on the SCOPE would break this row and leave
    // [`a_global_head_is_never_yielded_to`] green — which is what makes the pair a pair.
    //
    // NOTHING HERE IS REFUSED, and an earlier version of this comment said otherwise —
    // it described the capture's program as "now refused" and this section as "the shape
    // that is refused rather than decided". There is no such refusal: WI-980 replaced it
    // with the two-roles rule, and BOTH rows in this section load through
    // `load_kb_with`, which panics on any load error. The guard that actually stands
    // behind them is the `s == global` test in `Ownership::reach`'s overlay closure,
    // named here because the stale wording left it unattributed. The capture itself is
    // what [`a_global_head_is_never_yielded_to`] measures, from a KB that loads.
    let kb = crate::common::load_kb_with("namespace wi980.ok\n  rule modus_ponens(7, 8)\nend\n");
    assert_eq!(
        clauses(&kb, "anthill.logic.Constructive.Constructive.modus_ponens"),
        Some(1),
        "the stdlib axiom keeps its own predicate"
    );
    assert_eq!(clauses(&kb, "wi980.ok.modus_ponens"), Some(1));
}
