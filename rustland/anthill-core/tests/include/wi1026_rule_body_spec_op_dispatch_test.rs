//! WI-1026 — a RULE BODY that names a defaulted spec op must dispatch like an
//! operation body does: to the implementation the carrier SUPPLIES (WI-444 /
//! WI-1010), and loudly when two texts supply one (WI-1012 / 058 §3.7).
//!
//! WI-1012 measured the gap and filed it: three rule-body spellings, three silent
//! answers, none of them the operation body's. RE-MEASURED HERE before any code
//! changed, on WI-1010's fixture MINUS its `probe` operation — because leaving
//! `probe` in makes WI-1012's refusal fire on IT, which masks whatever the rule
//! body does. (WI-1026's own ticket text carries the contaminated numbers: it
//! reports the 2-supplier rows as answering silently, which is what they do only
//! once the operation-body call is out of the program.)
//!
//! | rule body | 1 supplier | 2 suppliers | | after |
//! |---|---|---|---|---|
//! | `Desc.describe(leaf(), ?r)` | `1` — the DEFAULT | `1` — tie ignored | → | `7` / **REFUSED** |
//! | `leaf().describe(?r)` | `1` — the DEFAULT | `7` | → | `7` / `7` (see below) |
//! | `describe(leaf(), ?r)` | `[]` | `[]` | → | `[]` — left, reason below |
//! | via an operation body (control) | `7` | REFUSED | → | unchanged |
//!
//! (Row 2's `7` in the 2-supplier column is what this ticket left and **WI-1035**
//! closed; it is a load REFUSAL now, at both sites. The row is written as it was
//! measured HERE, because the reason it was left is this ticket's own attribution.)
//!
//! ## Three defects wore one ticket, and the ticket's diagnosis named neither
//!
//! WI-1026 says "neither WI-444 site is on the SLD goal path". MEASURED FALSE for
//! the dot spelling: `type_rule_bodies` DOES dispatch a rule-body dot through
//! `check_apply_iter`, and the WI-444 block DID pin it — the stored body carried
//! `PinNow{impl_op = leafDescribe}` while the rule answered `1`.
//!
//!   * **The pin was dropped in transit.** `rebuilt_expr` — the owner WI-502 built
//!     so a rebuild does not lose the typer's stamp — carried `inferred_type` and
//!     not the `CallClass` written beside it. `with_fresh_vars` opens the body's
//!     De Bruijn vars and `body_rename` substitutes the head match, so by the time
//!     `reduce_op_value` folded the call the classification was `None` and it
//!     folded `op_body_node(Desc.describe)`, the SPEC'S OWN DEFAULT. One
//!     invariant, two fields, separated by exactly one bug — now
//!     `carry_typer_stamps_from`, and the resolver reads it through the same
//!     `classified_apply_target` eval reads.
//!   * **The qualified spelling was never typed at all.** `type_rule_bodies` walked
//!     only bodies containing a DOT, so a direct `Desc.describe(leaf(), ?r)` reached
//!     no dispatch decision and no tie check. `occ_needs_call_dispatch` now also
//!     triggers on a defaulted spec-op head.
//!   * **The dot's 2-supplier row is NOT a rule-body defect** — see below.
//!
//! ## The row deliberately left: `leaf().describe(?r)` with two suppliers — CLOSED
//!
//! It answered `7` (the carrier's own member) where the qualified spelling is now
//! refused. That was not this ticket's path, and the CONTROL is what proved it:
//! `a_dot_spelled_operation_body_ties_exactly_as_the_rule_body_does` puts the SAME dot
//! in an OPERATION body — the path WI-1010/WI-1012 own — and it answered `7` too.
//! WI-1026's ticket asserted the opposite ("the same tie through an operation body … a
//! load refusal with two, so the defect is the PATH and not the fixture"); its control
//! used the QUALIFIED spelling and so measured the path while attributing to it what
//! is really keyed on the SPELLING. The dot resolves `describe` on `Leaf` BY NAME to
//! the carrier's own member, so `check_apply_iter` is reached with `fn_sym =
//! Leaf.describe` — not a spec op at all — and no supplier set was ever consulted.
//! Fixing it meant changing dot member resolution, which changes operation bodies too.
//!
//! **WI-1035 delivered it**, and driving found MORE than this row measured: the same
//! dot bypassed WI-1027's BODY-LESS guard identically, so one fix closes both halves
//! of the spec-op population. The test above now asserts the refusal at both sites and
//! keeps the PAIRING it was written for; the fix's own coverage — both halves, the
//! controls, the zero-site blast radius — is `wi1035_dot_member_supplier_tie_test`.
//!
//! ## The row deliberately left: `describe(leaf(), ?r)` answering `[]`
//!
//! `describe` is not in scope at the namespace top level, so it interns to a symbol
//! with no clauses, no operation record and no builtin — a goal that can match
//! nothing. It never reaches dispatch, so it is not an 058 question at all; WI-1026's
//! own ordering note predicted exactly this ("a resolution failure prior to any 058
//! question"). Making such a goal loud is a corpus-wide change, MEASURED: 20 dangling
//! rule-body goals in stdlib alone (25 with examples), over 5 distinct names, and at
//! least two categories are LEGITIMATE and would be false positives —
//! `anthill.reflect.typing.DefaultProvider` is an entity whose facts the loader
//! asserts after this check would run, and `forall_impl` is a resolver scoping marker
//! that has no clauses by design. Filed as **WI-1034**.
//!
//! ## What fails if this is backed out — MEASURED per half, not predicted
//!
//! | test | stamp carry | rule-body typing | both |
//! |---|---|---|---|
//! | `a_dot_spelled_rule_body_reaches_the_supplied_impl` | **FAILS** | ok | **FAILS** |
//! | `a_qualified_rule_body_reaches_the_supplied_impl` | **FAILS** | **FAILS** | **FAILS** |
//! | `a_qualified_rule_body_tie_is_refused_at_load` | ok | **FAILS** | **FAILS** |
//! | `the_rule_body_refusal_is_located_and_shares_one_body` | ok | **FAILS** | **FAILS** |
//! | `a_carrier_with_no_supplier_still_runs_the_default_in_a_rule_body` | ok | ok | ok |
//! | `a_dot_spelled_operation_body_ties_exactly_as_the_rule_body_does` | ok | ok | ok |
//! | `a_bare_goal_naming_nothing_still_answers_nothing` | ok | ok | ok |
//!
//! The last three pass EITHER WAY **by design**, and each is here for a different
//! reason: the gap case is what makes a default a default and must not move; the
//! other two PIN the two rows this ticket deliberately leaves, so that closing
//! WI-1034 or WI-1035 has to come here and say so. WI-1035 did — the dot row's test
//! now asserts a refusal instead of `7`, and still passes either way here, because
//! what it measures is the two SITES agreeing, not which verdict they agree on.
//!
//! Note the second row: `a_qualified_rule_body_reaches_the_supplied_impl` needs BOTH
//! halves, which is why they ship together. Typing the call writes the pin; carrying
//! the stamp is what lets the resolver see it. Either alone leaves the rule answering
//! the default.
//!
//! Two SMALLER pieces inside those halves were measured separately, because each
//! could plausibly have been dead code and neither is:
//!
//!   * the resolver's WI-938 functional-relation rebuild going through
//!     `goal_occ.rebuilt_expr(..)` rather than a bare `new_expr` — that hook builds
//!     a FRESH `f(a₁…aₙ)` occurrence from the goal `f(a₁…aₙ, ?r)`, a new node no
//!     other carry ever sees. Reverted to `new_expr` ALONE: both
//!     `*_reaches_the_supplied_impl` tests FAIL.
//!   * the `sources` tagging in `type_rule_bodies` — backed out ALONE:
//!     `the_rule_body_refusal_is_located_and_shares_one_body` FAILS (the refusal
//!     renders with no `line:col`), and nothing else moves.
//!
//! ## One thing the resolver deliberately does NOT honour
//!
//! `classified_apply_target` answers for `CallClass::PinNow` only. The WI-444 block
//! writes `ConcreteApplyWithin` instead whenever the supplied impl's own sort
//! declares `requires`, and that class means the callee needs a dictionary in its
//! frame — which the structural fold has none of. Eval's copy of this read (the one
//! this ticket lifted onto `NodeOccurrence`) DID name that variant, harmlessly,
//! because eval matches it three arms earlier and routes it to the start that
//! installs the dict; the branch was dead there, and its deadness is what hid the
//! hazard from the lift. So a rule body reaching such an impl still runs the
//! default — narrower than the gap this ticket closed, and filed as **WI-1037**.
//!
//! REFERENCE: WI-1012; WI-1010; WI-444; WI-502; WI-938;
//! `docs/design/058-implementation.md` §3.1, §3.7, §13.

use anthill_core::eval::Value;

/// WI-1010's program shape MINUS the `probe` operation — see the header for why
/// that subtraction is the whole point. `tail` appends namespace items (the rule
/// under test, or a `probe` when the operation-body CONTROL is what is wanted).
///
/// Not `wi1010::program` with an empty tail: that builder hardwires `operation
/// probe() -> Int64 = Desc.describe(leaf())`, and this file's subject is the path
/// that has no such operation in it.
pub(crate) fn program(ns: &str, leaf_body: &str, supply: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
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

/// ONE supplier, by the WI-431 instance-fact route — the route WI-1010 made beat the
/// default, and the one a rule body could not see. `Leaf` writes no member of its own.
const ONE_LEAF: &str = "";
const ONE_SUPPLY: &str = "\n  operation leafDescribe(x: Leaf) -> Int64 = 7\n\n  \
                          fact Desc[T = Leaf, describe = leafDescribe]\n";

/// TWO suppliers — the carrier's own member (7) beside a fact binding a different
/// operation (9). WI-1012's tie, reachable without an operation body.
pub(crate) const TWO_LEAF: &str = "    provides Desc[T = Leaf]\n    operation describe(x: Leaf) -> Int64 = 7\n";
pub(crate) const TWO_SUPPLY: &str = "\n  operation otherDescribe(x: Leaf) -> Int64 = 9\n\n  \
                          fact Desc[T = Leaf, describe = otherDescribe]\n";

fn one_supplier(ns: &str, tail: &str) -> String {
    program(ns, ONE_LEAF, ONE_SUPPLY, tail)
}
fn two_suppliers(ns: &str, tail: &str) -> String {
    program(ns, TWO_LEAF, TWO_SUPPLY, tail)
}

/// The single Int answer of `{ns}.answer`, driven as an SLD GOAL — the path under
/// test. Panics on any other shape, including `[]`: "the query returned nothing" is
/// the symptom this ticket exists to stop, so it must never read as a pass.
pub(crate) fn answer(ns: &str, src: &str) -> i64 {
    let mut kb = crate::common::load_kb_with(src);
    let qn = format!("{ns}.answer");
    match crate::common::query_unary(&mut kb, &qn).as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("`{qn}` must answer exactly one definite Int, got {other:?}\n{src}"),
    }
}

/// THE HEADLINE, qualified spelling. The carrier's only implementation is a WI-431
/// instance fact's binding, and the rule body names the SPEC op directly. Before
/// this ticket it answered `1` — the spec's default, with the binding invisible —
/// which is WI-1010's own rule ("defaults fill GAPS, they do not SHADOW") absent
/// from the SLD path.
#[test]
fn a_qualified_rule_body_reaches_the_supplied_impl() {
    let ns = "test.wi1026.qualified";
    let src = one_supplier(ns, "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n");
    assert_eq!(
        answer(ns, &src),
        7,
        "a rule body naming the spec op directly must reach the fact-bound impl, \
         not the spec's default",
    );
}

/// THE HEADLINE, dot spelling — and the one the ticket's diagnosis got wrong. The
/// typer ALREADY pinned this call; what was missing is that the pin did not survive
/// the De Bruijn open and head-match rename into the resolver. Distinct from the
/// qualified test because it fails for a different reason and is fixed by a
/// different half: back out the stamp carry alone and this one fails while the
/// tie refusal still passes.
#[test]
fn a_dot_spelled_rule_body_reaches_the_supplied_impl() {
    let ns = "test.wi1026.dot";
    let src = one_supplier(ns, "  rule answer(?r) :- leaf().describe(?r)\n");
    assert_eq!(
        answer(ns, &src),
        7,
        "the typer pins this call; the resolver must fold the PINNED op, not the \
         spec's default body",
    );
}

/// WI-1012's refusal, now reachable from a rule body with no operation in the
/// program. Asserted as a LOAD refusal, not by re-driving: once refused there is no
/// KB to query, and "the query returns nothing" is the symptom that must stop being
/// how this reports.
#[test]
fn a_qualified_rule_body_tie_is_refused_at_load() {
    let ns = "test.wi1026.tie";
    let src = two_suppliers(ns, "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n");
    let msg = crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal; the program loaded clean:\n{src}"))
        .join("\n");
    assert!(msg.contains("ambiguous dispatch"), "{msg}");
    assert!(msg.contains("Desc.describe"), "the spec op must be named: {msg}");
    assert!(msg.contains("carrier `test.wi1026.tie.Leaf`"), "the carrier must be named: {msg}");
    assert!(
        msg.contains("the carrier's own member 'test.wi1026.tie.Leaf.describe'"),
        "route 1 named by its route: {msg}",
    );
    assert!(
        msg.contains("an instance fact binding `describe = test.wi1026.tie.otherDescribe`"),
        "route 2 quoted by the BINDING the author wrote: {msg}",
    );
}

/// The refusal raised from a RULE BODY must be located, and must be the SAME message
/// body as the one raised from an operation body.
///
/// Both halves are load-bearing and neither was free. WI-1012 put the refusal at the
/// typer rather than at eval precisely BECAUSE the typer holds the span; a rule-body
/// copy that rendered a bare byte offset would be the fallback that ticket removed —
/// and it did, until `type_rule_bodies` was given the `sources` channel every other
/// typer pass already uses (WI-745). The shared body is `render_suppliers` /
/// `supplier_tie_repair` / `ambiguous_spec_op_dispatch_message`; asserting byte
/// equality after stripping the `line:col` is what stops a fourth raising site from
/// growing a fourth wording.
#[test]
fn the_rule_body_refusal_is_located_and_shares_one_body() {
    let split = |src: &str| -> (String, String) {
        let msg = crate::common::try_load_kb_with(src)
            .err()
            .unwrap_or_else(|| panic!("expected a load refusal:\n{src}"))
            .join("\n");
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
        (loc.to_string(), body.to_string())
    };

    // Same namespace name in both, so the qualified names inside the message match
    // and any difference left is a difference of WORDING.
    let ns = "test.wi1026.faces";
    let (rule_loc, rule_body) =
        split(&two_suppliers(ns, "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n"));
    let (op_loc, op_body) =
        split(&two_suppliers(ns, "  operation probe() -> Int64 = Desc.describe(leaf())\n"));
    assert_eq!(rule_body, op_body, "one refusal, one message body — two faces must not drift");
    assert_ne!(
        rule_loc, op_loc,
        "the two fixtures put the call on different lines; equal locations would mean \
         the location is not really being read off the call",
    );
}

/// THE CONTROL THIS REFUSAL MUST NOT CONSUME, driven through the rule-body path
/// specifically: a carrier with NO supplier still runs the spec's default. This is
/// every defaulted spec-op call in the tree, and it is what makes a default a
/// default. Passes with the change backed out, by design.
#[test]
fn a_carrier_with_no_supplier_still_runs_the_default_in_a_rule_body() {
    let ns = "test.wi1026.gap";
    let src = program(
        ns,
        "    provides Desc[T = Leaf]\n",
        "",
        "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n",
    );
    assert_eq!(answer(ns, &src), 1, "no supplier — the spec's default must still run");
}

/// THE ROW THIS TICKET DELIBERATELY LEFT, NOW CLOSED BY **WI-1035** — kept here,
/// re-aimed, because what it measures is this ticket's own attribution and not
/// WI-1035's fix. Before WI-1035 both arms answered `7`; both are now refused at load.
///
/// The reading is unchanged and is why the pair is asserted TOGETHER: the dot in a rule
/// body and the identical dot in an OPERATION body — the path WI-1010/WI-1012 own —
/// behave alike, so the silence was keyed on the SPELLING and not on the rule body.
/// `leaf().describe(…)` resolved `describe` on `Leaf` by NAME to the carrier's own
/// member, and `check_apply_iter` never saw the spec op whose suppliers would be
/// compared. That measurement refutes WI-1026's own stated control, which used the
/// QUALIFIED spelling in the operation body and so concluded the defect was the path.
///
/// A test on the rule-body arm alone would have passed equally if the dot HAD been a
/// rule-body defect, and would have licensed closing WI-1035 in the wrong place —
/// which is the whole reason this test asserts both arms rather than one.
///
/// WI-1035's own coverage (both halves of the spec-op population, the controls, the
/// blast radius) is in `wi1035_dot_member_supplier_tie_test`; what stays here is the
/// PAIRING.
#[test]
fn a_dot_spelled_operation_body_ties_exactly_as_the_rule_body_does() {
    // `refusal` / `located` rather than local closures: they are this cluster's shared
    // owners of "loaded clean must never read as a pass" and of the `line:col: message`
    // parse, and `refusal`'s own doc gives that as the reason it is `pub(crate)`.
    let expect_tie = |ns: &str, tail: &str| {
        let msg = crate::wi1012_static_supplier_tie_test::refusal(&two_suppliers(ns, tail));
        assert!(
            msg.contains("ambiguous dispatch") && msg.contains("Desc.describe"),
            "WI-1035: `{tail}` must refuse the 2-supplier tie: {msg}",
        );
        msg
    };
    let op = expect_tie("test.wi1026.dottie", "  operation probe() -> Int64 = leaf().describe()\n");
    let rule = expect_tie("test.wi1026.dottie", "  rule answer(?r) :- leaf().describe(?r)\n");
    // Same namespace in both, so the qualified names inside match: the two SITES agree
    // on the verdict, which is the claim this test exists to make. Compared after the
    // `line:col` prefix, since the two fixtures put the call in different places.
    assert_eq!(
        crate::wi1012_static_supplier_tie_test::located(&op).1,
        crate::wi1012_static_supplier_tie_test::located(&rule).1,
        "the two sites must give ONE verdict — a difference here would mean the dot's \
         silence really was keyed on the rule body after all",
    );
}

/// PINS THE OTHER ROW DELIBERATELY LEFT (WI-1034). `describe` unqualified names
/// nothing at the namespace top level: no clause, no operation record, no builtin.
/// The goal matches nothing and the rule answers `[]` — with ONE unambiguous
/// supplier present, so this is a name-resolution silence and not a dispatch verdict.
///
/// Driven with one supplier deliberately: if it were a dispatch question, the single
/// supplier would decide it, and the row would answer 7.
#[test]
fn a_bare_goal_naming_nothing_still_answers_nothing() {
    let ns = "test.wi1026.bare";
    let src = one_supplier(ns, "  rule answer(?r) :- describe(leaf(), ?r)\n");
    let mut kb = crate::common::load_kb_with(&src);
    assert!(
        crate::common::query_unary(&mut kb, &format!("{ns}.answer")).is_empty(),
        "WI-1034: a goal whose functor names nothing answers nothing, silently — \
         unchanged here, and a corpus-wide question (20 such goals in stdlib alone)",
    );
}
