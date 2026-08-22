//! WI-20260822-J38JE — A BOOLEAN CONSTANT IN GOAL POSITION IS A SEARCH: `true` succeeds,
//! `false` fails.
//!
//! USER DECISION (2026-08-22): "`x :- true` should be a successful search, `x :- false`
//! unsuccessful." So `false` is legal-and-DEAD rather than refused, and both readings
//! hold at EVERY goal position — which is what §6.6 already requires of the boolean
//! OPERATORS ("at every GOAL position: the body's atoms, and the goal slots of the
//! connectives above them").
//!
//! ── WHAT WAS WRONG, MEASURED ─────────────────────────────────────────────────
//!
//! Nothing gave a constant a reading, so a boolean literal in goal position became NO
//! GOAL AT ALL: it resolved to no clause and no builtin, and WI-1034's "rule-body goal
//! names nothing" refusal cannot reach it because a CONSTANT NAMES NO NAME. `false`
//! therefore gave the right answer for the wrong reason and `true` gave the wrong one:
//!
//! | body | logic | before | now |
//! |---|---|---|---|
//! | `:- true` | 1 | 1 (the loader strip) | 1 |
//! | `:- false` | 0 | 0 — BY ACCIDENT | 0 |
//! | `:- not(true)` | 0 | **1** | 0 |
//! | `:- not(false)` | 1 | 1 | 1 |
//! | `:- base(9) \| true` | 1 | **0** | 1 |
//!
//! The two wrong rows share one cause, and 061 is half of it: `:- true` got its meaning
//! from a strip over the body's TOP-LEVEL goal list, which by construction cannot reach a
//! goal nested under `not` or `|`. Before 061 both positions answered the same (wrongly);
//! after it, one spelling had two readings decided by DEPTH. The reading now lives in
//! `SearchStream::step_init`, where every goal passes.
//!
//! ── THE BACK-OUTS ────────────────────────────────────────────────────────────
//!
//! * **THE GOAL READING** — gate off the `ViewHead::Const(Literal::Bool(b))` arm in
//!   `step_init` (kb/resolve.rs). VERIFIED over this file plus `wi_fqc85` and `wi980`,
//!   **exactly 1 row fails**: [`the_reading_holds_at_every_goal_position`]. An earlier
//!   draft of this list predicted 2, adding
//!   [`a_false_goal_fails_by_the_rule_not_by_accident`] — running it says otherwise, and
//!   the reason is the point of that row's own comment: `false` answers 0 under BOTH
//!   readings, by the rule now and by resolving-to-nothing before, so no count of its
//!   own can separate them. `not(true)` is what separates them, and it lives in the row
//!   that does fail. The top-level rows pass either way (the loader strip answers
//!   `true`, and `false` fails by accident) — which is why the nested ones are here.
//! * **THE LOADER STRIP** — gate off `is_empty_conjunction_goal` in `load_rule`'s body
//!   loop (kb/load.rs, 061). VERIFIED over the same 44 rows, **exactly 1 fails**:
//!   [`a_top_level_true_is_still_erased_at_load`]. Everything else passes, INCLUDING all
//!   of `wi_fqc85`, because the resolver arm now answers the goal the strip would have
//!   removed. That is a guard absorbing a neighbour's domain: when 061 shipped, this
//!   same back-out felled 24 rows. It is the reason this row asserts the BODY and not an
//!   answer count, and `wi_fqc85`'s own back-out list has been corrected to say so.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// One namespace carrying every shape, so the rows below differ only in the goal they
/// drive. `base` has the single clause `base(7)`, so `base(9)` is a goal that FAILS —
/// which is what makes the disjunction rows measure the other branch.
const SRC: &str = r#"
namespace j38je
  import anthill.prelude.{Int64, Bool}
  rule base(7) :- true

  rule ptrue(1)    :- true
  rule pfalse(1)   :- false
  rule nottrue(1)  :- not(true)
  rule notfalse(1) :- not(false)
  rule andtrue(1)  :- base(7), true
  rule andfalse(1) :- base(7), false
  rule ortrue(1)   :- base(9) | true
  rule orfalse(1)  :- base(9) | false
  rule orlive(1)   :- base(7) | false

  rule gtlive(1)   :- Int64.gt(2, 1)
  rule gtdead(1)   :- Int64.gt(1, 2)
end
"#;

#[test]
fn a_boolean_constant_goal_is_a_search_that_succeeds_or_fails() {
    // THE DECISION ITSELF, at the top level. PASSES EITHER WAY under the goal-reading
    // back-out (061's loader strip answers `true` there, and `false` fails by accident),
    // which is why it is not the row that measures the fix — it is the row that says
    // what the fix must not change.
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(answers(&mut kb, "j38je.ptrue(1)"), 1, "`:- true` is a successful search");
    assert_eq!(answers(&mut kb, "j38je.pfalse(1)"), 0, "`:- false` is an unsuccessful one");
}

#[test]
fn the_reading_holds_at_every_goal_position() {
    // THE ROW THAT MEASURES THE FIX, and the one no top-level test can stand in for. A
    // goal nested under `not` or `|` never reaches the loader's top-level strip, so
    // before this it kept the old non-reading: `not(true)` SUCCEEDED and a disjunction
    // whose live branch was `true` FAILED.
    //
    // BACKED OUT (delete the `ViewHead::Const(Literal::Bool(b))` arm from `step_init`):
    // this row FAILS on `nottrue` (1, not 0) and on `ortrue` (0, not 1).
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(answers(&mut kb, "j38je.nottrue(1)"), 0, "not(true) FAILS");
    assert_eq!(answers(&mut kb, "j38je.notfalse(1)"), 1, "not(false) succeeds");
    assert_eq!(answers(&mut kb, "j38je.ortrue(1)"), 1, "a dead branch beside `true`");
    assert_eq!(answers(&mut kb, "j38je.orfalse(1)"), 0, "two dead branches");
    assert_eq!(
        answers(&mut kb, "j38je.orlive(1)"),
        1,
        "CONTROL: a live branch beside `false` — `false` must not poison the disjunction"
    );
}

#[test]
fn a_false_goal_fails_by_the_rule_not_by_accident() {
    // `false` ANSWERED 0 BEFORE THIS TOO, and that is the trap the row exists for: it
    // failed because a `Term::Const` resolves to no clause and no builtin, the same way
    // a TYPO fails — WI-1034's "names nothing" refusal cannot reach a constant, which
    // names no name. The answer count alone cannot tell the two apart, so the row drives
    // the composition: under the accident `not(false)` also succeeds (a dead goal
    // negated), while `false` at the tail of a conjunction is indistinguishable either
    // way. What separates them is `not(true)` — measured in the row above — and the
    // conjunction rows here, which pin that a `false` reached mid-body kills the clause
    // rather than being skipped like `true`.
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(answers(&mut kb, "j38je.andtrue(1)"), 1, "`true` mid-body skips");
    assert_eq!(answers(&mut kb, "j38je.andfalse(1)"), 0, "`false` mid-body kills");
}

#[test]
fn a_top_level_true_is_still_erased_at_load() {
    // THE TWO READINGS DO NOT OVERLAP, and this row is the seam. §6.1 reads `fact H` as
    // `H :- true`, and only an EMPTY body makes that the same clause `fact` stores —
    // `is_equation` and WI-624's ground-fact fast path both read body-emptiness, so a
    // clause carrying one always-succeeding goal is a DIFFERENT clause with the same
    // answers. The resolver arm cannot supply that; the loader strip must stay.
    //
    // Asserts the BODY, not an answer count, because the answers agree under both
    // readings — which is precisely why this is the only row the loader-strip back-out
    // fells.
    let kb = crate::common::load_kb_with(
        "namespace j38jeb\n  rule viatrue(1) :- true\n  fact viafact(1)\nend\n",
    );
    let sym = kb
        .try_resolve_symbol("j38jeb.viatrue")
        .expect("the rule head is scoped where it is written");
    let rules = kb.rules_by_functor(sym);
    assert_eq!(rules.len(), 1, "one clause");
    assert!(
        kb.rule_body_nodes(rules[0]).is_empty(),
        "`:- true` IS the empty body — the `true` contributed no goal"
    );
}

#[test]
fn what_this_decision_does_not_reach() {
    // THE BOUND ON THE READING, pinned so that widening it is visible. Two neighbouring
    // populations keep today's behaviour:
    //
    //  * A NON-BOOL CONSTANT GOAL is still silently dead — no reading, no diagnostic.
    //    That is WI-20260822-J38JE item 4, which wants a located error rather than a
    //    third meaning for constants, and it is NOT what "true succeeds, false fails"
    //    decided. This row will fail when that lands, which is the intent.
    //  * A BOOL-RETURNING OPERATION CALL in goal position already evaluates, through
    //    WI-938's derived relational view at the operation's own arity — a different
    //    mechanism from this one, and the reason item 1 (is a general boolean EXPRESSION
    //    a condition?) is still open.
    let mut kb = crate::common::load_kb_with(
        "namespace j38jec\n  import anthill.prelude.{Int64, Bool, String}\n  \
         rule pint(1) :- 42\n  rule pstr(1) :- \"hello\"\n  \
         sort Box\n    entity box(n: Int64)\n    \
         operation isbig(b: Box) -> Bool = Int64.gt(1, 0)\n    \
         operation issmall(b: Box) -> Bool = Int64.gt(0, 1)\n  end\n  \
         rule pop(1) :- Box.isbig(box(n: 5))\n  \
         rule pop2(1) :- Box.issmall(box(n: 5))\nend\n",
    );
    assert_eq!(answers(&mut kb, "j38jec.pint(1)"), 0, "a non-Bool constant goal: item 4");
    assert_eq!(answers(&mut kb, "j38jec.pstr(1)"), 0, "…and it loads clean, which is the gap");
    assert_eq!(answers(&mut kb, "j38jec.pop(1)"), 1, "a Bool operation call ALREADY evaluates");
    assert_eq!(answers(&mut kb, "j38jec.pop2(1)"), 0, "…and is not vacuous");
}
