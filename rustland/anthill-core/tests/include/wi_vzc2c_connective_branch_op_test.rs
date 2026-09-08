//! WI-20260902-VZC2C — a NULLARY BOOL OPERATION is read as its relational view wherever
//! the goal reaches the resolver, not only where the loader hands over its own occurrence.
//!
//! THE DEFECT, as the ticket measured it: `rule s(1) :- onx` answered 1 and
//! `rule s(1) :- p(999) | onx` answered 0, in every spelling — bare, applied, one-segment
//! and dotted — with `&` dropping it the same way. Exit 0, no diagnostic.
//!
//! THE CAUSE IS ONE SHAPE, AND IT IS NOT `or`. The storage canon
//! (`KnowledgeBase::nullary_canon`) makes `Fn{f}` and `Ref(f)` ONE TERM, so any occurrence
//! rebuilt FROM a term comes back as the bare `Expr::Ref` leaf — and `reduce_op_value`
//! hands anything but an `Apply` straight back un-reduced, so WI-580's `eq(f(), true)`
//! rewrite builds a goal that cannot decide. The loader already knew this and elaborates a
//! bare nullary op to an `Expr::Apply` at the source walk (`nullary_op_call_or_ref`,
//! WI-20260902-CZJ2N / VNWAW); it is the OTHER producers of a goal occurrence that could
//! not.
//!
//! THREE OF THEM, and the ticket named one. Each is driven below by its own test:
//!   1. A `|` / `&` BRANCH ([`a_connective_branch_runs_a_nullary_bool_operation`]).
//!      `kernel.or` / `kernel.and` are stdlib RULES over `push_choice` / `push_and`, so a
//!      branch is bound by a HEAD MATCH — and `KnowledgeBase::with_fresh_vars` reifies
//!      every non-`Term` head-match binding to a term (WI-636), which for a nullary call
//!      is the canon's bare name. `kernel.not` has no such rule — it is a builtin that
//!      reads its negand off the goal's own view — which is exactly why `not(onx)` reached
//!      the view when a branch did not.
//!   2. A TOP-LEVEL QUERY ([`a_top_level_query_of_a_nullary_bool_operation_answers`]) —
//!      `load::nullary_query_canon` builds the transient carrier's `Expr::Ref`
//!      deliberately, to keep the two carriers' canons one test. Not in the ticket; found
//!      by asking what else is rebuilt from a term.
//!   3. A CONSTRAINT GUARD ([`a_constraint_guard_runs_a_nullary_bool_operation`]) —
//!      WI-20260830-DQD5W's population one shape in, and the one that is a WRONG answer
//!      rather than a missing one: the guard body could never hold, so `no … -: flag`
//!      held vacuously over every row.
//!
//! AND ONE CARRIER QUESTION UNDER THEM ([`a_spliced_symbol_ref_goal_takes_the_same_reading`]),
//! which is not a fourth producer but the same reading asked of a fourth SPELLING:
//! `term_view.rs`'s own head list says a bare nullary name arrives as `Term::Ref(f)`,
//! `Value::SymbolRef(f)`, `Expr::Ref(f)` or a stored nullary application, and only the last
//! can be reduced. Raised by `/code-review`.
//!
//! THE REPAIR IS AT THE CONSUMER the three converge on: `resolve.rs::step_init`'s WI-580
//! hook, which materializes the goal's `Ref` leaf back into `Apply{f}` before wrapping it
//! in `eq(…, true)`. It is the only site with the reading that licenses the elaboration —
//! a bare nullary op in an arrow-typed slot is §5.4's unapplied function value, and none
//! of the three producers (nor `reduce_op_value`) has an expected type to consult, while
//! reaching this hook already MEANS "the relational view of `f` at its declared arity".
//!
//! ── THE CORPUS CENSUS: ZERO ──────────────────────────────────────────────────
//!
//! `operation <name>()` over every `.anthill` file in the tree (stdlib, examples,
//! anthill-todo's own program, rustland, docs) finds **55 nullary operations, of which
//! exactly one returns `Bool`** — `anthill.kernel.cut`, which is a resolver BUILTIN and a
//! body-less declaration, so `bare_bodied_bool_relation` excludes it twice over and it
//! never took this reading. The corpus population this moves is therefore **zero**: it is
//! new code only, exactly as VNWAW's census found for the dotted spelling. The back-out
//! list below is the same fact from the other side — the only rows that move are the ones
//! written for it.
//!
//! WHAT FAILS WHEN IT IS BACKED OUT — TWO COMPONENTS, ONE BACK-OUT EACH, both applied
//! present-but-wrong and run over the WHOLE `wi_tests` binary (4 276 rows, 3 more
//! `#[ignore]`d), so each list is EXHAUSTIVE over that population: every row not named
//! passed. The first was also run over the whole workspace (30 binaries,
//! `rustland/scripts/test.sh`) with the same six and nothing else.
//!
//! **1 — THE REPAIR** (make the arm inert; the operand goes in exactly as it arrives).
//! **EXACTLY 6 TESTS FAIL** — all five here plus the VNWAW fixture:
//!   * [`a_connective_branch_runs_a_nullary_bool_operation`] — its 8 `on` rows
//!     (`sOr`/`sOrP`/`sAnd`/`sAndP` and their four dotted twins) go 1 → 0, and its two
//!     `sOrNotOn`/`dOrNotOn` rows go 0 → 1, which is the NAF-laundering face: a goal that
//!     could not run read as a disproof.
//!   * [`a_nested_connective_branch_runs_it_too`] — both rows, 1 → 0.
//!   * [`a_top_level_query_of_a_nullary_bool_operation_answers`] — its two `on` rows,
//!     1 → 0.
//!   * [`a_constraint_guard_runs_a_nullary_bool_operation`] — its two `ong` rows, the
//!     constraint stops firing.
//!   * [`a_spliced_symbol_ref_goal_takes_the_same_reading`] — its `on` row, 1 → 0.
//!   * `wi_vnwaw_dotted_goal_readings_test::
//!     a_goal_connective_branch_reads_alike_for_every_spelling`, whose six `0` rows this
//!     ticket turned into `1`s — the standing fixture the ticket named.
//!
//! **2 — THE WIDENING** from "is this an `Expr::Ref`?" to "is this already an
//! application?", which is what reaches the `Value::SymbolRef` carrier (restore the narrow
//! `Expr::Ref` test and drop the synthesized arm). **EXACTLY 1 TEST FAILS**:
//! [`a_spliced_symbol_ref_goal_takes_the_same_reading`]. The two components are therefore
//! SEPARABLE — the widening fells nothing the repair alone already covers — which is what
//! says this is one repair with a carrier question inside it and not two changes sharing a
//! name.
//!
//! ONE BACK-OUT FELLS BOTH CONNECTIVES, and that is the measurement rather than a gap in
//! it. The ticket asked for `&` to be backed out separately from `|` because a repair
//! written AT a connective would leave the other exactly as broken. This one is written at
//! neither: `push_choice` builds a CONTINUATION candidate in a new frame and `push_and`
//! SPLICES both conjuncts into the current one, so the two rows travel different routes to
//! the same hook — and a future repair that reached only one of them still fails the other
//! four rows here.
//!
//! CONTROLS THAT PASS EITHER WAY, BY DESIGN, each stated at its site: the `off` twins (a
//! `false`-bodied operation, so the row measures the operation's VALUE and not mere
//! success), the ENTITY branch and the arity-1 PREDICATE branch (which say the connective's
//! slot was always a goal position), the plain body ATOM (WI-580/VNWAW's own route,
//! untouched), and `not(off…)` inside a branch (so a repair that simply broke NAF fails
//! beside the `not(on…)` rows it would otherwise pass).

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// Assert a whole table of `<rule> -> <count>` rows against one KB, so a regression shows
/// up as the SPELLINGS DISAGREEING rather than as an absolute nobody can rank.
///
/// [`crate::common::definite_unary`] and not a `.len()` over `query_unary`: an unreduced
/// op call RESIDUALIZES, which is the exact outcome this ticket is about, and a floundered
/// solution counted as an answer would have made every broken row here read as green
/// (WI-20260822-WZX6B).
fn assert_table(kb: &mut KnowledgeBase, rows: &[(&str, usize, &str)]) {
    for &(rule, want, why) in rows {
        assert_eq!(
            crate::common::definite_unary(kb, rule).len(),
            want,
            "{rule}: {why}"
        );
    }
}

/// `onx` / `offx` are body-BACKED and rule-LESS — WI-580's relational-view gate, the same
/// shape CZJ2N and VNWAW used, so the columns below differ in NOTHING but the position and
/// the qualification.
const SRC: &str = "\
namespace zzvc.inner
  import anthill.prelude.{Bool, Int64}
  operation onx() -> Bool = true
  operation offx() -> Bool = false
  entity acct(n: Int64)
  fact acct(n: 1)
end
namespace zzvc.one
  import anthill.prelude.Bool
  operation onx2() -> Bool = true
  operation offx2() -> Bool = false
  fact pbVc(1)
  rule sAtom(1)      :- onx2
  rule sNot(1)       :- not(onx2)
  rule sPredOr(1)    :- pbVc(999) | pbVc(1)
  rule sOr(1)        :- pbVc(999) | onx2
  rule sOrP(1)       :- pbVc(999) | onx2()
  rule sAnd(1)       :- pbVc(1) & onx2
  rule sAndP(1)      :- pbVc(1) & onx2()
  rule sOrOff(1)     :- pbVc(999) | offx2
  rule sOrOffP(1)    :- pbVc(999) | offx2()
  rule sAndOff(1)    :- pbVc(1) & offx2
  rule sOrNotOn(1)   :- pbVc(999) | not(onx2)
  rule sOrNotOff(1)  :- pbVc(999) | not(offx2)
  rule sAndNotOff(1) :- pbVc(1) & not(offx2)
  rule sNestOr(1)    :- pbVc(999) | (pbVc(998) | onx2)
  rule sOrAnd(1)     :- pbVc(999) | (pbVc(1) & onx2)
end
namespace zzvc.outer
  fact pbVc2(1)
  rule dAtom(1)     :- zzvc.inner.onx
  rule dOrEnt(1)    :- pbVc2(999) | zzvc.inner.acct
  rule dOr(1)       :- pbVc2(999) | zzvc.inner.onx
  rule dOrP(1)      :- pbVc2(999) | zzvc.inner.onx()
  rule dAnd(1)      :- pbVc2(1) & zzvc.inner.onx
  rule dAndP(1)     :- pbVc2(1) & zzvc.inner.onx()
  rule dOrOff(1)    :- pbVc2(999) | zzvc.inner.offx
  rule dOrOffP(1)   :- pbVc2(999) | zzvc.inner.offx()
  rule dAndOff(1)   :- pbVc2(1) & zzvc.inner.offx
  rule dOrNotOn(1)  :- pbVc2(999) | not(zzvc.inner.onx)
  rule dOrNotOff(1) :- pbVc2(999) | not(zzvc.inner.offx)
end
";

/// **THE TICKET'S OWN TABLE**, both connectives × both qualifications × both nullary
/// spellings, with the value control beside each.
///
/// The `on` rows are the ones that MOVE (0 → 1) and the `off` rows are what says they moved
/// for the right reason: a repair that made every nullary op branch SUCCEED would pass the
/// eight `on` rows and fail the six `off` ones.
#[test]
fn a_connective_branch_runs_a_nullary_bool_operation() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_table(
        &mut kb,
        &[
            // ── CONTROLS: the connective's slot was ALWAYS a goal position, and the body
            // ATOM route always worked. Green either way; without them the eight rows
            // below cannot be attributed to the OPERATION's reading rather than to `or`.
            ("zzvc.one.sAtom", 1, "a body ATOM reaches the relational view — WI-580/VNWAW's route, untouched"),
            ("zzvc.outer.dAtom", 1, "…in the dotted spelling too — VNWAW's row"),
            ("zzvc.one.sPredOr", 1, "an arity-1 PREDICATE branch answers, so `|` itself works"),
            ("zzvc.outer.dOrEnt", 1, "…and so does an ENTITY branch, so the branch IS a goal position"),
            ("zzvc.one.sNot", 0, "`not` over a true operation fails — NAF reads the view from its negand"),
            // ── THE EIGHT ROWS THIS TICKET MOVES: 0 → 1.
            ("zzvc.one.sOr", 1, "a `|` BRANCH must run the operation — it answered 0, silently, because the branch is bound by a head match and comes back as the canon's bare `Ref` leaf, which `reduce_op_value` cannot open"),
            ("zzvc.one.sOrP", 1, "…and the applied spelling with it — the two are ONE term (CZJ2N), so no repair can move only one"),
            ("zzvc.outer.dOr", 1, "…dotted and bare"),
            ("zzvc.outer.dOrP", 1, "…dotted and applied"),
            ("zzvc.one.sAnd", 1, "`&` too — `push_and` SPLICES its conjuncts where `push_choice` builds a continuation, so this is a second route to the same hook, not a restatement"),
            ("zzvc.one.sAndP", 1, "…applied"),
            ("zzvc.outer.dAnd", 1, "…dotted and bare"),
            ("zzvc.outer.dAndP", 1, "…dotted and applied"),
            // ── THE VALUE CONTROL: same rows over a `false`-bodied operation. Green either
            // way BY DESIGN — before the change they answered 0 because the goal could not
            // run, and after it because the operation is false.
            ("zzvc.one.sOrOff", 0, "a false-bodied operation must still FAIL its branch"),
            ("zzvc.one.sOrOffP", 0, "…applied"),
            ("zzvc.one.sAndOff", 0, "…under `&`"),
            ("zzvc.outer.dOrOff", 0, "…dotted and bare"),
            ("zzvc.outer.dOrOffP", 0, "…dotted and applied"),
            ("zzvc.outer.dAndOff", 0, "…dotted, under `&`"),
            // ── THE WRONG ANSWER, REMOVED: 1 → 0. This is the face that is worse than a
            // missing answer — negation-as-failure reading a goal that COULD NOT RUN as a
            // disproof, inside a connective.
            ("zzvc.one.sOrNotOn", 0, "`not(onx2)` in a branch must FAIL: it ANSWERED 1 before, NAF laundering an unrunnable goal into a proof"),
            ("zzvc.outer.dOrNotOn", 0, "…dotted, the same laundering"),
            // ── …and its partner, green either way, so a repair that simply BROKE NAF
            // fails here while passing the two rows above.
            ("zzvc.one.sOrNotOff", 1, "`not(offx2)` in a branch must still SUCCEED"),
            ("zzvc.one.sAndNotOff", 1, "…under `&` as well"),
            ("zzvc.outer.dOrNotOff", 1, "…dotted"),
        ],
    );
}

/// A branch nested INSIDE another connective — the recursive case, which the flat rows
/// cannot rank because the inner goal is reached through a second head match.
#[test]
fn a_nested_connective_branch_runs_it_too() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_table(
        &mut kb,
        &[
            ("zzvc.one.sNestOr", 1, "`p | (q | onx2)` — the inner `|`'s branch, two head matches from the source occurrence"),
            ("zzvc.one.sOrAnd", 1, "`p | (q & onx2)` — a conjunct inside a disjunct, so the two routes compose"),
        ],
    );
}

/// **PRODUCER 2 — THE TRANSIENT QUERY CARRIER**, which the ticket did not name.
///
/// `load::convert_query_term` (the CLI's own query path — `anthill-cli/src/main.rs`) builds
/// its occurrence through `nullary_query_canon`, which returns `Expr::Ref` for a nullary
/// name ON PURPOSE, so that the transient carrier and the interned one canonicalize by one
/// shared test. The consequence was that a nullary Bool operation could not be queried AT
/// ALL: `onq` and `onq()` both answered 0.
#[test]
fn a_top_level_query_of_a_nullary_bool_operation_answers() {
    const QSRC: &str = "\
namespace zzvq.one
  import anthill.prelude.Bool
  operation onq() -> Bool = true
  operation offq() -> Bool = false
end
";
    // NOT `definite_unary`, which builds a unary goal from a symbol: the carrier under
    // test IS the query pattern, so the goal has to come through `convert_query_term` —
    // the path `anthill-cli`'s `--pattern` uses — and at arity ZERO, which is where
    // `nullary_query_canon` fires.
    let answers = |kb: &mut KnowledgeBase, pattern: &str| -> usize {
        let goal = crate::common::query_pattern_term(kb, pattern);
        kb.resolve(&[goal], &ResolveConfig::default())
            .iter()
            .filter(|s| s.is_definite())
            .count()
    };
    let mut kb = crate::common::load_kb_with(QSRC);
    for (goal, want, why) in [
        ("zzvq.one.onq", 1, "a bare nullary Bool op is queryable — it answered 0"),
        ("zzvq.one.onq()", 1, "…and so is its applied twin, which answered 0 too: the canon collapses them, so the defect was never a spelling"),
        ("zzvq.one.offq", 0, "the CONTROL — a false-bodied op must answer 0, or the two rows above measure success rather than the value"),
        ("zzvq.one.offq()", 0, "…applied"),
    ] {
        assert_eq!(answers(&mut kb, goal), want, "{goal}: {why}");
    }
}

/// **PRODUCER 3 — THE CONSTRAINT GUARD**, WI-20260830-DQD5W's population one shape in, and
/// the only face here that is a WRONG ANSWER rather than a missing one.
///
/// `lower_query` hands the resolver a hash-consed `Value::Term`; DQD5W taught the hook to
/// materialize it, but the materialization of a nullary call is the canon's `Ref` leaf, so
/// the guard body could never hold and `no ?n: Box(n: ?n) -: flag` held VACUOUSLY over every
/// row — a constraint that never fires, indistinguishable from one that is satisfied.
///
/// Both polarities, so a guard that fired on everything (or nothing) fails either way.
#[test]
fn a_constraint_guard_runs_a_nullary_bool_operation() {
    let case = |goal: &str| {
        format!(
            "\
namespace zzvg.one
  import anthill.prelude.{{Bool, Int64}}
  operation ong() -> Bool = true
  operation offg() -> Bool = false
  entity Box(n: Int64)
  fact Box(n: 1)
  constraint none_bad:
    no ?n: Box(n: ?n) -: {goal}
end
"
        )
    };
    for (goal, must_fire, why) in [
        ("ong", true, "the guard holds for the one Box row, so the `no` must REFUSE the load — it held vacuously instead"),
        ("ong()", true, "…and the applied spelling with it"),
        ("offg", false, "the CONTROL — a false-bodied guard must let the load through, or the rows above measure a guard that fires on everything"),
        ("offg()", false, "…applied"),
    ] {
        let errs = crate::common::try_load_kb_with(&case(goal))
            .err()
            .unwrap_or_default();
        let fired = errs.iter().any(|e| e.contains("none_bad"));
        assert_eq!(
            fired,
            must_fire,
            "{goal}: {why} — got {errs:?}",
        );
    }
}

/// **THE OPERAND'S SPELLING, not only its producer** — raised by `/code-review`, which
/// found that the repair's first form tested for `Expr::Ref` and would have left a second
/// bare-nullary spelling unrepaired.
///
/// A bare nullary name has more than one occurrence spelling that heads as
/// `ViewHead::nullary(f)`: the `Expr::Ref(f)` all three producers above deliver, and
/// `Expr::Spliced(Value::SymbolRef(f))`, which heads THROUGH its carried value
/// (`term_view.rs`'s `Spliced` arm — "a value carrying an occurrence views through to the
/// occurrence, so an occurrence carrying a value views through to the value"). Both mean
/// "call `f`" at a goal, and neither can be reduced as it stands.
///
/// The goal is BUILT HERE rather than loaded, because no loader path spells it — the
/// `Spliced`/`SymbolRef` mints are dictionary `impl` slots, `OpRef.op` and reflect argument
/// reads. That is exactly why it is driven: the repair asks "is this already an
/// application?" instead of "is this an `Expr::Ref`?", and without this row that widening
/// would rest on an argument rather than on a measurement. Back out the widening (restore
/// the `Expr::Ref` test) and both `on` rows here go 1 → 0 while every other row in this
/// file stays green.
#[test]
fn a_spliced_symbol_ref_goal_takes_the_same_reading() {
    use anthill_core::eval::value::Value;
    use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
    use anthill_core::span::{SourceId, SourceSpan};

    const SSRC: &str = "\
namespace zzvs.one
  import anthill.prelude.Bool
  operation ons() -> Bool = true
  operation offs() -> Bool = false
end
";
    let mut kb = crate::common::load_kb_with(SSRC);
    let span = SourceSpan::new(SourceId::from_raw(0), 0, 4);
    for (name, want, why) in [
        ("zzvs.one.ons", 1, "a `Spliced(SymbolRef)` goal is the same bare nullary name, so it must run the operation"),
        ("zzvs.one.offs", 0, "the CONTROL — a false-bodied op must answer 0, or the row above measures success rather than the value"),
    ] {
        let sym = kb.resolve_symbol(name);
        let goal = Value::Node(NodeOccurrence::new_expr(
            Expr::Spliced(Value::SymbolRef(sym)),
            span,
            None,
        ));
        let n = kb
            .resolve(&[goal], &ResolveConfig::default())
            .iter()
            .filter(|s| s.is_definite())
            .count();
        assert_eq!(n, want, "{name}: {why}");
    }
}
