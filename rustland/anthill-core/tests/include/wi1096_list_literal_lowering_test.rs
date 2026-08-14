//! WI-1096: a `[…]` LIST LITERAL LOWERS TO THE `cons`/`nil` SPINE IN EVERY POSITION,
//! not only where a declared field type happens to say `List`.
//!
//! THE DEFECT. `List.contains([7], 9)` as a rule-body goal ANSWERED — 9 is not in
//! `[7]`. Silently, with no diagnostic: the literal stayed a flat
//! `Fn{anthill.reflect.ListLiteral, [7]}`, which `contains`' body cannot destructure,
//! so the derived relational reading (`eq(contains([7], 9), true)`, WI-580) never
//! discharged and rode out as an undischarged RESIDUAL — and a conditional solution
//! is still a solution to whatever asked. A membership test that answers for
//! everything makes every rule filtering on it unsound, and `not contains(…)` then
//! fails where it should succeed.
//!
//! WHY THE DEFAULT WAS THE BUG, not the coverage. WI-007 made the desugaring
//! context-keyed and WI-936 made that context LOAD-ORDER INDEPENDENT — but both work
//! the `entity_field_types` channel, and that channel does not reach, and cannot be
//! made to reach, a position with no declared field: an operation-call argument, a
//! rule head, a plain relation's fact head, a bare `?xs = [1, 2]`. There is no field
//! type there to lower earlier. `expected == None` therefore meant two different
//! things at one branch — "this position declares a NON-List collection" and "nobody
//! declares anything here" — and the branch answered the first for both.
//!
//! MEASURED BEFORE THE FIX, one probe per position, each beside its own
//! correct-answering `cons`-spelled twin:
//!
//! | position                                        | literal | cons-spelled twin |
//! |-------------------------------------------------|---------|-------------------|
//! | op-call argument as a GOAL (`contains(l, 9)`)    | 1 cond. |  0  (correct)     |
//! | op-call argument for its VALUE (`length(l)`)     | 1 cond. |  1  (correct)     |
//! | rule head (`rule pass([1, 2, 3])`)               |    0    |  1  (correct)     |
//! | plain relation's fact head (`fact stored([…])`)  |    0    |  1  (correct)     |
//! | bare `?xs = [1, 2]`, then `?xs = cons(…)`        | 1 cond. |  1 cond.          |
//! | entity field declared `List[T = Int64]`          |    1    |  1  (correct)     |
//! | entity field declared `Set[T = Int64]`           |    0    |  0  (by design)   |
//! | entity field declared a TYPE PARAMETER (`v: T`)  | 1 cond. |  1  (correct)     |
//!
//! Row 5 is the one position that does NOT discriminate on the answer: a `?xs = […]`
//! chain residualizes either way, because two delayed `eq`s in a row suspend on the
//! unbound `?xs` (WI-519) before the spine shape matters. It was measured on the
//! stored rule body instead — `eq(?_, [1, 2])` before, `eq(?_, cons(head: 1, tail:
//! cons(head: 2, tail: nil)))` after — and is DRIVEN here in the form that grounds
//! it, through a rule head ([`a_literal_reached_through_a_head_or_a_fact_is_a_list`]).
//!
//! ONE UNDECLARED POSITION WAS ALREADY CORRECT and stays so — a bounded quantifier's
//! collection slot, `(forall ?x in [1, 2]: …)`. Its row passes with the change backed
//! out, which is the measurement
//! ([`a_bounded_quantifier_over_a_literal_was_already_correct`]). It is the
//! exception that names the general rule: its reader (`bounded_list_elements`) is
//! CARRIER-NEUTRAL and has an explicit `ListLiteral` arm beside its `cons` one, so it
//! never depended on the lowering. That arm must not be deleted as dead — a literal in
//! a `Set`-declared slot, and every reflect-built `ListLiteral` term, still reach it.
//!
//! Two further positions share the one conversion site and were checked by READING,
//! not driven, each for a stated reason: a CONSTRAINT body (the kernel has no runtime
//! constraint checker — spec §1 records the execution boundary as narrower than the
//! logical reading, and `anthill check` is a scaffold) and a PROOF obligation (its
//! goals convert through the same `convert_term_with_expected`; nothing about a proof
//! reaches the literal branch differently). Both are covered by the site, not by a
//! second rule.
//!
//! THE FIX IS AT THE ONE PLACE A LIST LITERAL IS LOWERED — the `ListLiteral` branch
//! of `Loader::convert_term_with_expected` — and it changes the DEFAULT, not the
//! coverage: a declared List-shaped type still supplies the element hint, a declared
//! type naming another collection still declines, and an ABSENT declaration now means
//! `List` rather than "leave it as written". No special case in the goal path, and
//! nothing added to any other conversion site.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! Restore `expected.and_then(|e| Self::find_list_element_type(self.kb, e))` and
//! exactly SIX of the fourteen rows here fail, MEASURED by doing it (8 passed;
//! 6 failed): [`a_rule_body_goal_over_a_literal_decides_membership`],
//! [`negation_over_a_literal_holds_when_the_element_is_absent`],
//! [`a_longer_literal_and_an_empty_literal_both_decide`],
//! [`a_literal_reached_through_a_head_or_a_fact_is_a_list`],
//! [`an_operation_call_argument_reduces_for_its_value`], and
//! [`a_type_parameter_typed_field_is_not_a_rival_collection`]. Outside this file,
//! `wi939_contains_rename_test::list_contains_over_a_literal_as_a_rule_body_goal` and
//! `wi936_field_type_load_order_test::an_untyped_list_literal_lowers_in_either_order`
//! fail too — the latter is WI-936's own control, RE-KEYED by this ticket onto the
//! case WI-007 actually protects (a declared NON-List collection type); see its note.
//!
//! PASS EITHER WAY, BY DESIGN — the attribution controls:
//! [`the_cons_spelled_twin_still_decides`] (the spelling that was always correct),
//! [`an_operation_body_still_evaluates_a_literal`] (the eval path, never affected — an
//! operation body's `[…]` is an `Expr::ListLit` OCCURRENCE, a different carrier from
//! the term this ticket lowers),
//! [`a_bounded_quantifier_over_a_literal_was_already_correct`] (a carrier-neutral
//! reader), [`a_declared_list_field_still_destructures`] and
//! [`an_option_wrapped_list_field_still_desugars_and_wraps`] (WI-007/WI-408/WI-936's
//! covered positions), and the two rows that stop the fix from being "desugar
//! unconditionally": [`a_declared_non_list_collection_still_keeps_the_literal_flat`]
//! and [`a_declared_collection_of_lists_keeps_its_literal_flat`]. The named-arg row
//! [`a_list_literal_written_by_name_with_named_args_is_not_lowered`] passes either way
//! against THIS back-out — it guards a regression the default change introduced on its
//! own, which the guard fixes. Backing out the `named_args.is_empty()` test instead
//! fails exactly that one row and nothing else (measured: 13 passed, 1 failed).
//!
//! The query row [`a_query_pattern_matches_the_shape_the_loader_stored`] is pinned by
//! its OWN back-out: drop the `list_literal_lowering` call in `convert_query_term` and
//! it is the only row that fails (measured: 14 passed, 1 failed).
//!
//! ACROSS THE WHOLE WORKSPACE the change moves exactly ONE pre-existing test:
//! `wi936_field_type_load_order_test`'s control, re-keyed here. All 29 test binaries
//! were run with the fix in and that was the only failure.
//!
//! ── WHAT A REVIEW PASS ADDED, AND WHY IT IS THE SAME DEFECT ───────────────────
//!
//! The first version of this fix keyed the declining branch on "the declared type is
//! not List-shaped", which is still ONE NAME FOR TWO QUESTIONS — it declines both for
//! a type that NAMES another collection and for one that names nothing in particular.
//! Three rows here came from finding that: the type-parameter row (the WI-1096 residual
//! reappearing one field deep), the collection-of-lists row (the wrapper descent
//! entering a `Set`'s bindings and lowering a literal that meant the set), and the
//! named-arg row (a `ListLiteral(elements: …)` collapsing to `nil`). The lesson is the
//! one the defect started from: an absent commitment is not a contrary one.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

/// Every fixture binds its head variable from `fact mark(1)` BEFORE the goal under
/// test, rather than from the ticket's trailing `?m = 1`. MEASURED reason: that
/// trailing `eq` suspends as a delayed goal of its own, so a SUCCEEDING row reports
/// "1 conditional" whether the `contains` decided or merely residualized — collapsing
/// the very distinction this ticket turns on. Bound from a fact, the goal under test
/// is the only thing that can suspend: a surviving solution is DEFINITE, and a goal
/// that never decides shows up as a conditional one.
const MARK: &str = "  fact mark(1)\n";

/// The DEFINITE solutions of a unary rule. A conditional solution is not an answer to
/// a membership question — it is an undischarged goal — so it does not count here.
fn decided(kb: &mut KnowledgeBase, qn: &str) -> usize {
    crate::common::query_unary(kb, qn)
        .iter()
        .filter(|(_, definite)| *definite)
        .count()
}

/// Total solutions, conditional ones included — what the pre-fix defect produced and
/// what a `.len()`-only assertion would have called an answer.
fn any(kb: &mut KnowledgeBase, qn: &str) -> usize {
    crate::common::query_unary(kb, qn).len()
}

fn kb_of(body: &str) -> KnowledgeBase {
    crate::common::load_kb_with(&format!(
        "namespace wi1096\n  \
         import anthill.prelude.{{List, Int64, Bool, Set}}\n  \
         import anthill.prelude.List.{{cons, nil, contains, length}}\n{MARK}{body}\nend\n"
    ))
}

/// THE HEADLINE — a bare `contains` goal over a `[…]` literal DECIDES the membership
/// question, both ways. A predicate answering for everything fails the second row; one
/// answering for nothing fails the first.
#[test]
fn a_rule_body_goal_over_a_literal_decides_membership() {
    let mut kb = kb_of(
        "  rule yes(?m) :- mark(?m), contains([7], 7)\n  \
           rule no(?m)  :- mark(?m), contains([7], 9)\n",
    );
    assert_eq!(
        any(&mut kb, "wi1096.no"),
        0,
        "9 is NOT in [7] — before the fix this answered ONE (conditional), which is \
         the shape the ticket reported",
    );
    assert_eq!(
        decided(&mut kb, "wi1096.yes"),
        1,
        "7 IS in [7], and DEFINITELY — before the fix this too came back as one \
         solution, but an undischarged residual, so a count alone would have called \
         the defect fixed",
    );
}

/// CONTROL — the `cons`-spelled twin, correct before and after. It is what makes the
/// row above attributable to the LITERAL and nothing else: the two fixtures differ
/// only in how the one-element list is written.
#[test]
fn the_cons_spelled_twin_still_decides() {
    let mut kb = kb_of(
        "  rule yes(?m) :- mark(?m), contains(cons(head: 7, tail: nil), 7)\n  \
           rule no(?m)  :- mark(?m), contains(cons(head: 7, tail: nil), 9)\n",
    );
    assert_eq!(decided(&mut kb, "wi1096.yes"), 1);
    assert_eq!(any(&mut kb, "wi1096.no"), 0);
}

/// CONTROL — the eval path, which was never broken. An operation body's `[…]` is an
/// `Expr::ListLit` OCCURRENCE built by the body loader, not the hash-consed term this
/// ticket lowers; the ticket recorded it measured-correct, and it must stay so — a fix
/// that "worked" by changing eval would have been fixing the wrong carrier.
#[test]
fn an_operation_body_still_evaluates_a_literal() {
    let src = r#"
namespace wi1096.eval
  import anthill.prelude.{List, Int64, Bool}
  operation yes() -> Bool = List.contains([7], 7)
  operation no()  -> Bool = List.contains([7], 9)
end
"#;
    let mut interp = crate::common::interp_for(src);
    let bool_of = |v: Value| match v {
        Value::Bool(b) => b,
        other => panic!("expected Bool, got {}", other.type_name()),
    };
    assert!(bool_of(
        interp.call("wi1096.eval.yes", &[]).expect("yes runs")
    ));
    assert!(!bool_of(
        interp.call("wi1096.eval.no", &[]).expect("no runs")
    ));
}

/// NEGATION — where a spurious success flips a rule's meaning the OTHER way. Before
/// the fix `contains([1, 2, 3], 9)` never discharged, so negation-as-failure had no
/// failure to read; `present` is the mirror, so a `not` that simply always held would
/// fail there.
#[test]
fn negation_over_a_literal_holds_when_the_element_is_absent() {
    let mut kb = kb_of(
        "  rule absent(?m)  :- mark(?m), not contains([1, 2, 3], 9)\n  \
           rule present(?m) :- mark(?m), not contains([1, 2, 3], 2)\n",
    );
    assert_eq!(
        decided(&mut kb, "wi1096.absent"),
        1,
        "9 is not in the list, so the negation HOLDS",
    );
    assert_eq!(
        any(&mut kb, "wi1096.present"),
        0,
        "2 IS in the list, so the negation must not hold — the row that stops a \
         vacuously-true `not` from passing the one above",
    );
}

/// A literal of length > 1 and the EMPTY literal `[]`, since a one-element literal
/// could be a special case at either end of the spine build.
#[test]
fn a_longer_literal_and_an_empty_literal_both_decide() {
    let mut kb = kb_of(
        "  rule three_has(?m)   :- mark(?m), contains([1, 2, 3], 2)\n  \
           rule three_lacks(?m) :- mark(?m), contains([1, 2, 3], 9)\n  \
           rule empty_lacks(?m) :- mark(?m), contains([], 1)\n  \
           fact empty_fact([])\n  \
           rule empty_is_nil(?m)   :- mark(?m), empty_fact(nil())\n  \
           rule empty_not_cons(?m) :- mark(?m), empty_fact(cons(head: ?, tail: ?))\n",
    );
    assert_eq!(decided(&mut kb, "wi1096.three_has"), 1);
    assert_eq!(any(&mut kb, "wi1096.three_lacks"), 0);
    assert_eq!(
        any(&mut kb, "wi1096.empty_lacks"),
        0,
        "nothing is a member of the empty list",
    );
    assert_eq!(
        decided(&mut kb, "wi1096.empty_is_nil"),
        1,
        "`[]` IS `nil()` — the empty literal lowers to the terminator, not to a \
         zero-argument `ListLiteral()`",
    );
    assert_eq!(
        any(&mut kb, "wi1096.empty_not_cons"),
        0,
        "…and it is not a `cons`: the row above is about the SHAPE, not about `nil` \
         matching anything",
    );
}

/// THE OTHER UNDECLARED POSITIONS — a RULE HEAD and a plain relation's FACT HEAD.
/// Neither declares argument types at all, so no expected-type channel could ever have
/// reached them; both answered ZERO before the fix, where the `cons`-spelled twin
/// answered one. Driving through `contains` on the variable the head bound also
/// settles the `?xs = […]` reading in its grounded form.
#[test]
fn a_literal_reached_through_a_head_or_a_fact_is_a_list() {
    let mut kb = kb_of(
        "  rule pass([1, 2, 3])\n  \
           rule head_has(?m)   :- mark(?m), pass(?xs), contains(?xs, 2)\n  \
           rule head_lacks(?m) :- mark(?m), pass(?xs), contains(?xs, 9)\n  \
           fact stored([1, 2, 3])\n  \
           rule fact_has(?m)   :- mark(?m), stored(?xs), contains(?xs, 2)\n  \
           rule fact_lacks(?m) :- mark(?m), stored(?xs), contains(?xs, 9)\n",
    );
    assert_eq!(decided(&mut kb, "wi1096.head_has"), 1);
    assert_eq!(any(&mut kb, "wi1096.head_lacks"), 0);
    assert_eq!(decided(&mut kb, "wi1096.fact_has"), 1);
    assert_eq!(any(&mut kb, "wi1096.fact_lacks"), 0);
}

/// The op-call argument in its OTHER reading — read for the call's VALUE rather than
/// as a goal. `length([1, 2])` could not reduce over a flat literal either, so the
/// comparison stayed residual whichever number it was compared against.
#[test]
fn an_operation_call_argument_reduces_for_its_value() {
    let mut kb = kb_of(
        "  rule len_two(?m)   :- mark(?m), eq(length([1, 2]), 2)\n  \
           rule len_three(?m) :- mark(?m), eq(length([1, 2]), 3)\n",
    );
    assert_eq!(decided(&mut kb, "wi1096.len_two"), 1);
    assert_eq!(
        any(&mut kb, "wi1096.len_three"),
        0,
        "the wrong length must REFUTE — before the fix both compares residualized, \
         so both 'answered'",
    );
}

/// CONTROL — the one undeclared position that was ALREADY correct, and why. A bounded
/// quantifier's collection slot reads its spine through `bounded_list_elements`, which
/// is carrier-neutral and carries an explicit `ListLiteral` arm beside its `cons` one,
/// so it decided both spellings before this ticket and decides both after. Keeping the
/// row says the lowering did not become that reader's precondition, and keeps the arm
/// from reading as dead code.
#[test]
fn a_bounded_quantifier_over_a_literal_was_already_correct() {
    let mut kb = kb_of(
        "  rule all_pos(?m) :- mark(?m), (forall ?x in [1, 2]: gt(?x, 0))\n  \
           rule all_big(?m) :- mark(?m), (forall ?x in [1, 2]: gt(?x, 1))\n",
    );
    assert_eq!(decided(&mut kb, "wi1096.all_pos"), 1);
    assert_eq!(any(&mut kb, "wi1096.all_big"), 0);
}

/// THE FOURTH TERM POSITION — a QUERY pattern, which must build what the loader
/// STORED or it cannot match it. Found by a second review pass, and it was a live
/// regression: the loader started lowering an undeclared literal while
/// `convert_query_term` still built the flat one, so `anthill query 'stored(?x)'`
/// printed `?x = [1, 2, 3]` and feeding that exact answer back as `stored([1, 2, 3])`
/// found NOTHING. Both spellings print as `[…]`, so nothing showed.
///
/// MEASURED at the commit that introduced it: `stored([1, 2, 3])` → 0,
/// `held(Holder(xs: [1, 2]))` → 0, `tagged(Tagged(tags: [1, 2]))` → 1. The middle row
/// is older than WI-1096 — a DECLARED `List` field has been unmatchable by a literal
/// query since WI-007 — and routing both converters through one decision function
/// closes that too.
///
/// The two rows that keep this honest: the wrong literal must NOT match (or "matches
/// anything" would pass), and the `Set`-declared field must STILL match, since there
/// both sides decline together.
#[test]
fn a_query_pattern_matches_the_shape_the_loader_stored() {
    let src = r#"
namespace wi1096.query
  import anthill.prelude.{List, Int64, Set}
  fact stored([1, 2, 3])
  entity Holder(xs: List[T = Int64])
  fact held(Holder(xs: [1, 2]))
  entity Tagged(tags: Set[T = Int64])
  fact tagged(Tagged(tags: [1, 2]))
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    // The namespace in query scope, the way `anthill query -i wi1096.query.*` puts it
    // there — a program file's own imports are file-local and do not reach a query.
    crate::common::supply_invocation_imports(&mut kb, &["wi1096.query.*"]);
    // Through the SHIPPED query path — `fact <pattern>`, `scan_definitions`, then
    // `load::convert_query_term` — which is what `anthill query --pattern` takes, so
    // this exercises the converter that was out of step and not a private helper.
    fn hits(kb: &mut KnowledgeBase, pattern: &str) -> usize {
        use anthill_core::kb::resolve::ResolveConfig;
        let goal = crate::common::query_pattern_term(kb, pattern);
        kb.resolve(&[goal], &ResolveConfig::default()).len()
    }
    assert_eq!(
        hits(&mut kb, "stored([1, 2, 3])"),
        1,
        "the literal a query prints must be the literal a query matches",
    );
    assert_eq!(
        hits(&mut kb, "stored([1, 2, 9])"),
        0,
        "…and a DIFFERENT literal must not — the row that stops 'matches anything'",
    );
    assert_eq!(
        hits(&mut kb, "held(Holder(xs: [1, 2]))"),
        1,
        "a DECLARED `List` field too — unmatchable by a literal query since WI-007",
    );
    assert_eq!(
        hits(&mut kb, "tagged(Tagged(tags: [1, 2]))"),
        1,
        "a `Set`-declared field still matches by literal: both sides decline together",
    );
}

/// ONLY THE BRACKET SURFACE IS THE LIST LITERAL — `[a, b]` lowers, a written
/// `ListLiteral(a, b)` does not. The two build the identical term once the name
/// resolves, so a parse-level mark is the only thing that separates them (WI-1099, on
/// the WI-927 `Box[T = Int64]` vs `Box(value: 1)` model).
///
/// This was NOT a theoretical distinction. The first version of the query-side fix
/// lowered both, and `wi040_reserved_vocab_test::query_pattern_bare_list_literal_
/// resolves_qualified` — which pins `ListLiteral(?x)` resolving to
/// `anthill.reflect.ListLiteral` — went red, because the pattern had become a `cons`
/// spine. That test is the sibling driver on the QUERY side; this row is the loader
/// side, and the `[…]` half beside it is what says the mark did not simply disable
/// the lowering.
#[test]
fn only_the_bracket_surface_is_the_list_literal() {
    let src = r#"
namespace wi1096.surface
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{cons, nil}
  fact mark(1)
  fact bracket([1, 2])
  fact by_name(ListLiteral(1, 2))
  rule bracket_is_a_list(?m) :- mark(?m), bracket(cons(head: 1, tail: ?))
  rule by_name_is_not(?m)    :- mark(?m), by_name(cons(head: 1, tail: ?))
  rule by_name_is_entity(?m) :- mark(?m), by_name(ListLiteral(1, 2))
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        decided(&mut kb, "wi1096.surface.bracket_is_a_list"),
        1,
        "`[1, 2]` is the List literal",
    );
    assert_eq!(
        any(&mut kb, "wi1096.surface.by_name_is_not"),
        0,
        "…and `ListLiteral(1, 2)` written by name is NOT — it is the reflect entity",
    );
    assert_eq!(
        decided(&mut kb, "wi1096.surface.by_name_is_entity"),
        1,
        "…which is still matchable AS that entity, by the same spelling",
    );
}

/// CONTROL — the position WI-007 and WI-936 already covered: an entity field DECLARED
/// `List[T = …]`. It answered correctly before this ticket and must keep answering,
/// which is what says the change moved the DEFAULT and left the declared channel
/// alone.
#[test]
fn a_declared_list_field_still_destructures() {
    let mut kb = kb_of(
        "  entity Holder(xs: List[T = Int64])\n  \
           fact held(Holder(xs: [1, 2]))\n  \
           rule first(?m) :- mark(?m), held(Holder(xs: cons(head: 1, tail: ?)))\n",
    );
    assert_eq!(decided(&mut kb, "wi1096.first"), 1);
}

/// THE SAME DEFECT ONE FIELD DEEP — found by review after the default landed. A field
/// declared with a bare TYPE PARAMETER (`entity Box(v: T)`, and `Option.some(value: T)`
/// which every top-level `some(…)` goes through) is not a rival collection: a `T` says
/// the position is generic, which is what an ABSENT declaration says too. Reading it as
/// "some non-List type" left the literal flat and reproduced the WI-1096 residual
/// verbatim.
///
/// Measured before this second fix, with the first one already in: `tvar_lacks` answered
/// 1 conditional carrying `residual: eq(contains([1, 2, 3], 9), true)`, `tvar_head` and
/// `some_head` answered 0, while the un-wrapped `plain_head` answered 1.
#[test]
fn a_type_parameter_typed_field_is_not_a_rival_collection() {
    let src = r#"
namespace wi1096.tvar
  import anthill.prelude.{List, Int64, Bool, Option}
  import anthill.prelude.List.{cons, nil, contains}
  import anthill.prelude.Option.{some}

  fact mark(1)

  sort Boxed
    sort T = ?
    entity Box(v: T)
  end

  fact boxed(Box(v: [1, 2, 3]))
  rule tvar_has(?m)   :- mark(?m), boxed(Box(v: ?l)), contains(?l, 2)
  rule tvar_lacks(?m) :- mark(?m), boxed(Box(v: ?l)), contains(?l, 9)
  rule tvar_head(?m)  :- mark(?m), boxed(Box(v: cons(head: 1, tail: ?)))

  fact wrapped(some([1, 2, 3]))
  rule some_head(?m) :- mark(?m), wrapped(some(cons(head: 1, tail: ?)))

  fact plain([1, 2, 3])
  rule plain_head(?m) :- mark(?m), plain(cons(head: 1, tail: ?))
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(decided(&mut kb, "wi1096.tvar.tvar_has"), 1);
    assert_eq!(
        any(&mut kb, "wi1096.tvar.tvar_lacks"),
        0,
        "9 is not in the list — a `T`-typed field must not resurrect the residual",
    );
    assert_eq!(decided(&mut kb, "wi1096.tvar.tvar_head"), 1);
    assert_eq!(
        decided(&mut kb, "wi1096.tvar.some_head"),
        1,
        "`some(value: T)` is a generic slot, not a rival collection",
    );
    assert_eq!(
        decided(&mut kb, "wi1096.tvar.plain_head"),
        1,
        "the un-wrapped control — it answered before the wrapped ones did, which is \
         what made the wrapper the difference",
    );
}

/// CONTROL FOR THAT FIX — an `Option[T = List[…]]` field still lowers its payload AND
/// still gets the WI-408 `some(…)` wrap. The recursion into a wrapper's payload and
/// that wrap are two halves of one decision, so narrowing the recursion (below) must
/// not cost this.
#[test]
fn an_option_wrapped_list_field_still_desugars_and_wraps() {
    let src = r#"
namespace wi1096.optwrap
  import anthill.prelude.{List, Int64, String, Option}
  import anthill.prelude.List.{cons}
  import anthill.prelude.Option.{some}
  fact mark(1)
  entity Item(name: String, deps: Option[T = List[T = String]])
  fact it(Item(name: "a", deps: ["x", "y"]))
  rule opt_head(?m) :- mark(?m), it(Item(name: ?, deps: some(cons(head: "x", tail: ?))))
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(decided(&mut kb, "wi1096.optwrap.opt_head"), 1);
}

/// A COLLECTION OF LISTS IS STILL THAT COLLECTION — found by review. The wrapper
/// descent used to enter ANY parameterized type's bindings, so a `Set[T = List[T =
/// Int64]]`-declared field lowered its `[1, 2]` to a `cons` spine (measured: the `cons`
/// pattern matched) and was then NOT wrapped, because the `some(…)` half correctly saw
/// a non-`Option`. The two halves now key on the same predicate.
///
/// This row is what the spec sentence "a position declared `Set[T = X]` keeps its
/// literal as written" actually costs; without it that sentence was false for a set OF
/// lists.
#[test]
fn a_declared_collection_of_lists_keeps_its_literal_flat() {
    let src = r#"
namespace wi1096.setoflists
  import anthill.prelude.{List, Int64, Set}
  import anthill.prelude.List.{cons}
  fact mark(1)
  entity Wrap(inner: Set[T = List[T = Int64]])
  fact w(Wrap(inner: [1, 2]))
  rule wrap_head(?m)  :- mark(?m), w(Wrap(inner: cons(head: 1, tail: ?)))
  rule wrap_whole(?m) :- mark(?m), w(Wrap(inner: ?))
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        any(&mut kb, "wi1096.setoflists.wrap_head"),
        0,
        "the literal names the SET, not one of its element lists",
    );
    assert_eq!(
        decided(&mut kb, "wi1096.setoflists.wrap_whole"),
        1,
        "…and the fact is there",
    );
}

/// A `ListLiteral` CARRYING NAMED ARGS IS NOT THIS SURFACE, so it is not lowered —
/// found by review. `[…]` parses to positional children only (the `[h | t]` tail form
/// was removed, WI-560), so the named spelling `ListLiteral(elements: …)` is the
/// reflect ENTITY written by name (it appears in `docs/proposals/typing_pass_spec.
/// anthill`). Lowering reads `pos_args` alone, so it silently dropped the payload:
/// measured, this fact loaded as `nil` and `named(nil())` matched it.
///
/// Asserted on the FACT side, which is what the default change reached. In a RULE BODY
/// the named arg is dropped further downstream by the term→occurrence build (`Expr::
/// ListLit` is a flat vector by WI-560's decision) — pre-existing, unchanged here, and
/// deliberately not claimed.
#[test]
fn a_list_literal_written_by_name_with_named_args_is_not_lowered() {
    let src = r#"
namespace wi1096.namedargs
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{cons, nil}
  fact mark(1)
  fact named(ListLiteral(elements: 1))
  rule is_nil(?m) :- mark(?m), named(nil())
"#
    .to_owned()
        + "end\n";
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(
        any(&mut kb, "wi1096.namedargs.is_nil"),
        0,
        "a named-arg `ListLiteral` is not the empty list — it kept its payload",
    );
}

/// CONTROL, AND THE GUARD ON THE FIX'S SHAPE — a field whose DECLARED type is another
/// collection keeps the literal flat. This is the case WI-007 installed the "leave it
/// alone" branch for, and the only case that branch was ever right about. Were the fix
/// "desugar unconditionally", `set_head` would start answering.
#[test]
fn a_declared_non_list_collection_still_keeps_the_literal_flat() {
    let mut kb = kb_of(
        "  entity Tagged(tags: Set[T = Int64])\n  \
           fact tagged(Tagged(tags: [1, 2]))\n  \
           rule set_head(?m)  :- mark(?m), tagged(Tagged(tags: cons(head: 1, tail: ?)))\n  \
           rule set_whole(?m) :- mark(?m), tagged(Tagged(tags: ?))\n",
    );
    assert_eq!(
        any(&mut kb, "wi1096.set_head"),
        0,
        "a `Set`-declared field keeps its literal flat — a `cons` pattern matches \
         nothing, exactly as before this ticket",
    );
    assert_eq!(
        decided(&mut kb, "wi1096.set_whole"),
        1,
        "…and the fact is there: the zero above is about the SHAPE, not a missing fact",
    );
}
