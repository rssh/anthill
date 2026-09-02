//! WI-20260902-VNWAW — A DOTTED PAREN-LESS GOAL TAKES THE NAME'S TWO READINGS, NOT JUST
//! ITS SYMBOL.
//!
//! WI-20260901-719FJ decided WHICH SYMBOL a dotted paren-less citation spells in a goal:
//! `zz.inner.flag` is the qualified NAME, not a `field_access` projection. It answered
//! that by returning the bare `Ref`/`Ident` leaf. WI-20260902-CZJ2N then decided what a
//! NAME MEANS in a goal, and gave the one-segment arms of the same walk two readings the
//! dotted branch never got — a fielded ENTITY is §8.3's all-fields-fresh pattern, and a
//! nullary OPERATION is its own call (a predicate goal is answered by MATCHING, an
//! operation goal by REDUCING).
//!
//! ── MEASURED ON THE DELIVERED CZJ2N TREE (this file's own fixtures, run with the
//!    change backed out) ──────────────────────────────────────────────────────
//!
//! | goal                       | unqualified | dotted, before | dotted, after |
//! |---|---|---|---|
//! | `:- flag`  (op, `= true`)  | 1 | **0** — silently empty | 1 |
//! | `:- flag()`                | 1 | 1 | 1 |
//! | `:- not(flag)`             | 0 | **1** — WRONG ANSWER  | 0 |
//! | `:- acct` (2 facts)        | 1 | **0** — silently empty | 1 |
//! | `:- not(acct)`             | 0 | **1** — WRONG ANSWER  | 0 |
//! | `:- not(empt)` (no facts)  | 0 | **1** — disagreed with its own applied twin | 0 |
//!
//! The `not` rows are the same free proof 719FJ removed for the dotted predicate and
//! CZJ2N removed for the one-segment op: negation-as-failure reading a goal that CANNOT
//! RUN as a disproof. §6.6 says resolution is "by syntactic position"; this was it being
//! false for one qualification, twice.
//!
//! ── THE OTHER FOUR LOGICAL POSITIONS ALREADY HAD IT ──────────────────────────
//!
//! CZJ2N put §8.3's expansion at all five, and the dotted spelling reaches four of them
//! through code that was already shared: `Loader::convert_subject_term` (the rule head,
//! the fact head, the sort-body pre-scan and the proof step) calls
//! `expand_bare_entity_subject` on ITS dotted branch, and `convert_query_term` calls
//! `expand_bare_entity_pattern` on its own. Only the rule-body GOAL arm forked, because
//! there the dotted branch `return`s an occurrence of its own before reaching the
//! one-segment `Term::Ref` / `Term::Ident` arms that grew the readings. The fix is a FORWARDING to
//! those arms, in their order, not a third reading.
//!
//! ── THE CORPUS CENSUS: ZERO ──────────────────────────────────────────────────
//!
//! Instrumented at the branch and run over every `.anthill` file in the tree (stdlib,
//! examples, anthill-testcases, testdata, rustland, docs, anthill-todo — 234 files) and
//! over `anthill-todo`'s 1 292 `.anthill.md` documents (197 items loaded): **zero
//! dotted paren-less goal citations of any kind**, with a positive control that fired
//! all three arms. So the population this moves is new code only, and the whole
//! `cargo test` suite is unchanged by it — 6 333 rows over 36 binaries, of which the 5
//! new ones are this file's; every back-out below fells only rows written here.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! TWO AXES, both at the one site (`build_body_atom_occurrence_inner`'s dotted `at_goal`
//! branch), each backed out PRESENT-BUT-WRONG and run over the whole 4 041-row
//! `wi_tests` binary:
//!
//! **1 — THE ENTITY READING.** Guard the `bare_entity_goal_occurrence` call out of the
//! dotted branch (keeping `nullary_op_call_or_ref`). **EXACTLY 2 ROWS FAIL** of 4 041:
//! [`a_dotted_bare_entity_goal_is_the_all_fields_fresh_pattern`] (its `Two`, `NotTwo` and
//! `NotNone` cells) and [`a_goal_connective_branch_reads_alike_for_every_spelling`] — the
//! latter on its `dOrEnt` row, which I had NOT predicted and which is what says that row
//! MEASURES the entity reading inside a connective branch rather than merely controlling
//! for it.
//!
//! **2 — THE OPERATION READING.** Replace `self.nullary_op_call_or_ref(sym, parse_id)`
//! with a bare `Expr::Ref(sym)`. **EXACTLY 3 ROWS FAIL:**
//! [`the_ticket_table_answers_one_one_zero_in_both_columns`] (its `dotBare` / `dotNot`
//! rows), [`a_dotted_nullary_op_goal_answers_by_the_operation_s_value`] (its `dOn` /
//! `dNotOn` rows), and the connective test again — this time on its `dAtom` row.
//!
//! Both back-outs were APPLIED AND RUN over the WHOLE `wi_tests` binary (4 041 rows, 3
//! more `#[ignore]`d), so each list is EXHAUSTIVE over that population: every row not
//! named passed. The two axes are SEPARABLE — neither fells any of the other's rows, and
//! where they meet (the connective test) they fell different assertions in it — which is
//! what says this is two readings at one site rather than one change with two names.
//!
//! CONTROLS THAT PASS EITHER WAY, BY DESIGN, each stated at its site:
//! [`a_data_slot_keeps_the_dotted_reference_on_both_sides_of_a_match`] (the position split
//! is the point — a data slot holds a term whose spelling is its identity), and the `off`
//! / `dNone` / `dTwoP` / applied-dotted rows inside the tests above, which are what say
//! the goal RUNS rather than merely succeeding.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;

/// DEFINITE solutions only — a `.len()` counts a FLOUNDERED one as an answer
/// (WI-20260822-WZX6B). It matters here because several rows negate a goal whose entity
/// pattern is NON-GROUND (`not(acct)`, all fields fresh), which is the shape that
/// residualizes rather than failing.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// Assert a whole table of `<goal> -> <count>` rows against one KB, so a regression shows
/// up as the SPELLINGS DISAGREEING rather than as an absolute nobody can rank.
fn assert_table(kb: &mut KnowledgeBase, rows: &[(&str, usize, &str)]) {
    for &(goal, want, why) in rows {
        assert_eq!(
            answers(kb, &format!("{goal}(?x)")),
            want,
            "{goal}: {why}"
        );
    }
}

/// **A — THE TICKET'S OWN 3×2**, which read `1 1 0 / 0 1 1` and must read `1 1 0` twice.
///
/// `flag` is body-BACKED and rule-LESS, which is WI-580's relational-view gate — the same
/// shape CZJ2N used, so the two columns differ in NOTHING but the qualification.
#[test]
fn the_ticket_table_answers_one_one_zero_in_both_columns() {
    const SRC: &str = "\
namespace zzvw.inner
  import anthill.prelude.Bool
  operation flag() -> Bool = true
  rule ctrlBare(1)  :- flag
  rule ctrlParen(1) :- flag()
  rule ctrlNot(1)   :- not(flag)
end
namespace zzvw.outer
  rule dotBare(1)  :- zzvw.inner.flag
  rule dotParen(1) :- zzvw.inner.flag()
  rule dotNot(1)   :- not(zzvw.inner.flag)
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_table(
        &mut kb,
        &[
            // THE UNQUALIFIED COLUMN — CZJ2N's rows, unchanged here and the yardstick
            // the dotted column is read against. Green either way.
            ("zzvw.inner.ctrlBare", 1, "the one-segment bare goal runs the operation"),
            ("zzvw.inner.ctrlParen", 1, "…and so does its applied twin"),
            ("zzvw.inner.ctrlNot", 0, "…so its negation fails"),
            // THE DOTTED COLUMN — the two that moved, and the applied control between
            // them.
            (
                "zzvw.outer.dotBare",
                1,
                "the DOTTED bare goal must run the same operation — it answered 0, \
                 silently, because the dotted branch returned the bare `Ref` leaf and \
                 `reduce_op_value` hands anything but an `Apply` straight back",
            ),
            (
                "zzvw.outer.dotParen",
                1,
                "…as the applied dotted spelling already did — the CONTROL, green either \
                 way, and what says a dotted goal can reach the operation at all",
            ),
            (
                "zzvw.outer.dotNot",
                0,
                "`not(zzvw.inner.flag)` must FAIL: it ANSWERED 1 before, negation-as-\
                 failure laundering a goal that could not run into a proof",
            ),
        ],
    );
}

/// **B — THE ANSWER TRACKS THE OPERATION'S VALUE**, which is what separates "the goal
/// now runs" from "the goal now succeeds".
///
/// The `offx` pair is GREEN EITHER WAY and is the point of the test: before the change
/// `dOff` answered 0 and `dNotOff` answered 1 for the wrong reason (the goal could not
/// run at all), and after it they answer the same for the right one. A repair that made
/// every dotted op goal succeed would pass `dOn` and fail `dOff`; one that broke NAF
/// would pass `dNotOn` and fail `dNotOff`. Neither `on` row alone can rank those.
#[test]
fn a_dotted_nullary_op_goal_answers_by_the_operation_s_value() {
    const SRC: &str = "\
namespace zzvv.inner
  import anthill.prelude.Bool
  operation onx() -> Bool = true
  operation offx() -> Bool = false
end
namespace zzvv.outer
  rule dOn(1)     :- zzvv.inner.onx
  rule dNotOn(1)  :- not(zzvv.inner.onx)
  rule dOff(1)    :- zzvv.inner.offx
  rule dNotOff(1) :- not(zzvv.inner.offx)
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_table(
        &mut kb,
        &[
            ("zzvv.outer.dOn", 1, "a `true` body proves the goal — it answered 0"),
            ("zzvv.outer.dNotOn", 0, "…so its negation fails — it answered 1"),
            (
                "zzvv.outer.dOff",
                0,
                "a `false` body does NOT prove it — green either way, and it is what \
                 says the fix RUNS the operation rather than making the goal succeed",
            ),
            (
                "zzvv.outer.dNotOff",
                1,
                "…and its negation holds — green either way, the row a broken NAF \
                 would fail",
            ),
        ],
    );
}

/// **C — A DOTTED BARE FIELDED ENTITY GOAL IS §8.3's ALL-FIELDS-FRESH PATTERN.**
///
/// EIGHT ROWS IN EACH COLUMN, and the assertion is that the two columns are EQUAL: the
/// dotted spelling of a program must answer exactly what the one-segment spelling of the
/// same program answers, cell for cell. Written that way rather than as six absolutes
/// because two of the cells (`sNotNone` / `dNotNone`) are 0 for a reason that is NOT this
/// ticket's — NAF over a non-ground entity pattern does not succeed here, for ANY
/// spelling — and an absolute row would either bake that in as intended or fail for the
/// wrong reason. What this ticket owns is that the columns AGREE; before it they
/// disagreed in three cells, and the dotted `not(empt)` even disagreed with its own
/// applied twin.
///
/// `empt` — a declared entity with NO facts — is the row that says `dTwo` is not vacuous
/// truth: an expansion that produced a goal matching anything would answer 1 there.
#[test]
fn a_dotted_bare_entity_goal_is_the_all_fields_fresh_pattern() {
    const SRC: &str = "\
namespace zzve.inner
  import anthill.prelude.Int64
  entity acct(n: Int64)
  fact acct(n: 1)
  fact acct(n: 2)
  entity empt(n: Int64)
  rule sTwo(1)      :- acct
  rule sTwoP(1)     :- acct()
  rule sNotTwo(1)   :- not(acct)
  rule sNotTwoP(1)  :- not(acct())
  rule sNone(1)     :- empt
  rule sNoneP(1)    :- empt()
  rule sNotNone(1)  :- not(empt)
  rule sNotNoneP(1) :- not(empt())
end
namespace zzve.outer
  rule dTwo(1)      :- zzve.inner.acct
  rule dTwoP(1)     :- zzve.inner.acct()
  rule dNotTwo(1)   :- not(zzve.inner.acct)
  rule dNotTwoP(1)  :- not(zzve.inner.acct())
  rule dNone(1)     :- zzve.inner.empt
  rule dNoneP(1)    :- zzve.inner.empt()
  rule dNotNone(1)  :- not(zzve.inner.empt)
  rule dNotNoneP(1) :- not(zzve.inner.empt())
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    // The one-segment column is read first and becomes the expectation for the dotted
    // one — so this is a PAIRING and not two independent absolutes.
    let cells = [
        ("Two", "the entity HOLDS (two facts), so a bare goal proves"),
        ("TwoP", "…and so does the applied spelling — the control"),
        ("NotTwo", "…so the negation of a holding entity must fail"),
        ("NotTwoP", "…as the applied negation already did — the control"),
        ("None", "an entity with NO facts proves nothing"),
        ("NoneP", "…nor does its applied spelling — the control"),
        ("NotNone", "NAF over a non-ground pattern, whatever it answers"),
        ("NotNoneP", "…and the applied spelling must answer the same"),
    ];
    for (cell, why) in cells {
        let one = answers(&mut kb, &format!("zzve.inner.s{cell}(?x)"));
        let dot = answers(&mut kb, &format!("zzve.outer.d{cell}(?x)"));
        assert_eq!(
            dot, one,
            "d{cell} must answer what s{cell} answers ({why}); the qualification decides \
             NOTHING about a goal's reading. Before this ticket the dotted column read \
             `0 1 1 0 0 0 1 0` against the one-segment `1 1 0 0 0 0 0 0`."
        );
    }
    // AND THE ABSOLUTE VALUES OF THE TWO THAT CARRY CONTENT, so the pairing above cannot
    // be satisfied by both columns breaking together (a `nullary_canon` regression would
    // do exactly that).
    assert_eq!(
        answers(&mut kb, "zzve.outer.dTwo(?x)"),
        1,
        "…and the value is 1, not merely equal to a jointly-broken twin"
    );
    assert_eq!(
        answers(&mut kb, "zzve.outer.dNone(?x)"),
        0,
        "…while the FACT-LESS entity still answers 0 — the row that says the expansion \
         is a search and not a pattern that matches anything"
    );
}

/// **THE DATA-SLOT CONTROL — GREEN BEFORE AND AFTER, AND THE POINT OF THE POSITION
/// SPLIT.** §8.3's expansion is the one reading that could leak out of the goal
/// position: `acct` in a DATA slot must stay the REFERENCE — the sort-as-value
/// `facts_of(kb(), acct)` reads, and `typing::check_bare_ref`'s free-standing-entity arm
/// — and if it expanded on ONE of the walks that spell a stored term, the fact and the
/// goal that searches for it would stop being one term and the match would break in
/// SILENCE (WI-756; the regression WI-20260825-P9Y67 measured from the other side). A
/// fixture that drove only the goal position would pass with that broken, which is why
/// this row exists.
///
/// TWO ASSERTIONS, and the second is the one with content:
///  * the three walks still agree — the `fact`'s slot, the query pattern's, and the rule
///    body's (the walk this ticket edits) — so the stored term is still findable; and
///  * the bound value carries NO ARGUMENTS, i.e. it is not `acct(n: ?fresh)`. That is
///    the expansion's absence stated positively; a count-only row would be green with it
///    running, since the expanded pattern also produces exactly one definite answer.
///
/// WHAT THE SLOT ACTUALLY BINDS, measured rather than assumed: the NAME, not the
/// `field_access` chain — `Fn{acct, [], []}` for an entity and `Ref(f)` for a predicate,
/// an operation or a namespace. 719FJ's own data-slot row (`fact holds(nsx.tgt)`) is
/// about the FACT-head walk (`convert_term`); a rule-body value slot is the OCCURRENCE
/// walk, where proposal 052 §6.7 / WI-714 already read a dotted citation as the name it
/// spells. Both readings are UNMOVED by this ticket: with the change backed out this
/// fixture binds the identical shape.
#[test]
fn a_data_slot_keeps_the_dotted_reference_on_both_sides_of_a_match() {
    const SRC: &str = "\
namespace zzvd.inner
  import anthill.prelude.Int64
  entity acct(n: Int64)
  fact acct(n: 1)
end
fact holdsVd(zzvd.inner.acct)
rule viaVd(1) :- holdsVd(zzvd.inner.acct)
rule slotVd(?t) :- ?t <=> zzvd.inner.acct
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        answers(&mut kb, "holdsVd(zzvd.inner.acct)"),
        1,
        "a QUERY's data slot spells the same term the fact's does"
    );
    assert_eq!(
        answers(&mut kb, "viaVd(?x)"),
        1,
        "…and so does a RULE BODY's — the third walk, and the one this ticket edits"
    );

    let mut bound = crate::common::definite_unary(&mut kb, "slotVd");
    assert_eq!(bound.len(), 1, "`slotVd` binds exactly once; got {bound:?}");
    let bound = bound.pop().expect("checked above");
    // Read the shape through `TermView`, not by matching a `Value` variant: one term
    // reaches a test on three carriers and an enum match reads the first and panics on
    // the other two.
    let (pos, named) = match bound.head(&kb) {
        ViewHead::Functor {
            pos_arity,
            named_arity,
            ..
        } => (pos_arity, named_arity),
        // A `Ref` leaf carries no arguments either, and that is equally not the
        // expansion — the assertion below is about the arguments, so a leaf passes it.
        _ => (0, 0),
    };
    assert_eq!(
        (pos, named),
        (0, 0),
        "a bare fielded entity in a DATA slot is the REFERENCE, so it carries no field \
         arguments — §8.3's all-fields-fresh expansion belongs to the LOGICAL positions \
         only. Got {pos} positional / {named} named in {bound:?}"
    );
}

/// **A MEASURED NON-GOAL, recorded so the next reader does not mistake it for this
/// ticket's defect.** A nullary Bool OPERATION written as a branch of a GOAL CONNECTIVE
/// (`|` / `&`) answers nothing — in ALL FOUR spellings, one-segment or dotted, bare or
/// applied — while the same goal as a plain body atom answers, and while an ENTITY
/// branch answers in every spelling. So the connective, not the qualification, is what
/// drops it: WI-580's relational view is reached from a body atom and from `not(…)`, and
/// not from `kernel.or` / `kernel.and`'s branch slots.
///
/// GREEN BEFORE AND AFTER, and that is the assertion: this ticket makes the dotted column
/// EQUAL the one-segment column here too, at 0, rather than fixing either. Filed as
/// WI-20260902-VZC2C.
#[test]
fn a_goal_connective_branch_reads_alike_for_every_spelling() {
    const SRC: &str = "\
namespace zzvc.inner
  import anthill.prelude.{Bool, Int64}
  operation onx() -> Bool = true
  entity acct(n: Int64)
  fact acct(n: 1)
end
namespace zzvc.one
  import anthill.prelude.Bool
  operation onx2() -> Bool = true
  fact pbVc(1)
  rule sOr(1)    :- pbVc(999) | onx2
  rule sOrP(1)   :- pbVc(999) | onx2()
  rule sAnd(1)   :- pbVc(1) & onx2
  rule sAtom(1)  :- onx2
end
namespace zzvc.outer
  fact pbVc2(1)
  rule dOr(1)    :- pbVc2(999) | zzvc.inner.onx
  rule dOrP(1)   :- pbVc2(999) | zzvc.inner.onx()
  rule dAnd(1)   :- pbVc2(1) & zzvc.inner.onx
  rule dAtom(1)  :- zzvc.inner.onx
  rule dOrEnt(1) :- pbVc2(999) | zzvc.inner.acct
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_table(
        &mut kb,
        &[
            ("zzvc.one.sAtom", 1, "a body ATOM reaches the relational view"),
            ("zzvc.outer.dAtom", 1, "…in the dotted spelling too — this ticket's row"),
            ("zzvc.one.sOr", 0, "a `|` BRANCH does not, one-segment and bare"),
            ("zzvc.one.sOrP", 0, "…nor applied — so it is not a spelling question"),
            ("zzvc.outer.dOr", 0, "…nor dotted and bare — EQUAL to the column above"),
            ("zzvc.outer.dOrP", 0, "…nor dotted and applied"),
            ("zzvc.one.sAnd", 0, "`&` drops it too, one-segment"),
            ("zzvc.outer.dAnd", 0, "…and dotted — the same 0"),
            (
                "zzvc.outer.dOrEnt",
                1,
                "…while an ENTITY branch DOES answer under the same connective, which is \
                 what says the gap is the operation's relational view and not `or` \
                 itself (WI-20260902-VZC2C)",
            ),
        ],
    );
}

