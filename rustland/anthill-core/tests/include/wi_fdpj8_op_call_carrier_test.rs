//! **WI-20260910-FDPJ8 — AN UNEVALUATED OP CALL REACHED eq/cmp/arith AS DATA ON THE
//! `Term` AND `Entity` CARRIERS, AND THE VERDICT WAS WRONG.**
//!
//! `reduce_op_value` folded only a `Value::Node` (`let occ = match &v { Value::Node(o)
//! => …, _ => return v }`) and its partner `is_unreduced_op_call` — the WI-738
//! soundness floor that makes an unfolded call DELAY instead of being compared — opened
//! with the same match. The pair was internally consistent; the consequence was one
//! level up. On the other two carriers a bodied op call was NEITHER REDUCED NOR
//! DELAYED, so it entered `sem_eq_values`' ladder as DATA — and every arm of that
//! ladder asks about a CARRIER (reflexivity, a head `Eq` override, a Float, a partial
//! carrier), which an operation application matches none of. It fell out the structural
//! tail.
//!
//! # The defect, as measured at HEAD before the fix
//!
//! Over `operation dbl(n: Int64) -> Int64 = add(n, n)` and `fact Box(w: 2)`, one
//! program with two readings decided only by WHERE THE GOAL WAS WRITTEN:
//!
//! | goal | truth | rule body (`Node`) | term-carried | entity-carried |
//! |---|---|---|---|---|
//! | `neq(dbl(2), 4)` | 0 | 0 | **1 — WRONG VERDICT** | **1 — WRONG VERDICT** |
//! | `eq(dbl(2), 4)`  | 1 | 1 | **0 — lost answer**   | **0 — lost answer** |
//! | `Int64.lt(dbl(2), 5)` | 1 | 1 | **0 — lost, loudly** | **0 — lost, loudly** |
//!
//! The `lt` rows came back through WI-879's `[wi879] … has no order for this operand
//! pair (dbl and Int64) — the goal is UNDECIDED` diagnostic: loud rather than silent,
//! and still the wrong answer for a well-formed program.
//!
//! AND IT WAS REACHABLE FROM SOURCE, not only from a hand-built `kb.resolve`: a
//! CONSTRAINT GUARD is term-carried (`lower_query`), which is WI-20260830-DQD5W's own
//! population. `no ?v: Box(w: ?v) -: neq(dbl(?v), 4)` over `fact Box(w: 2)` — where
//! `dbl(2)` IS 4, so no witness exists — reported `integrity constraint 'none_bad' is
//! violated by the loaded facts`, and it reported the same for `Box(w: 3)`, which
//! genuinely violates it. A guard that refuses both is a guard enforcing nothing.
//!
//! # The repair, and why it is two changes in this order
//!
//!  1. **`reduce_op_value` materializes a non-`Node` call** through
//!     [`node_occurrence::value_as_occurrence`] (WI-20260906-7YPGM added it for the two
//!     relational-view hooks) behind the cost gate `op_call_occurrence_to_reduce`, so a
//!     call is REDUCED on every carrier.
//!  2. **`is_unreduced_op_call` reads `TermView::head`**, so a call that reduction left
//!     standing DELAYS on every carrier.
//!
//! Widening (2) alone is wrong and is why this was not fixed when it was found: nothing
//! else reduces such an operand, so it would delay for ever — a never-answer traded for
//! a sometimes-wrong one. The CARRIER is widened, never the DISPATCH: `reduce_operand`
//! still passes `dispatch_body_less: false` (WI-1057's `reduce_dispatched_goal_call`
//! split), so `anthill.prelude.Set`'s body-less `insert`/`empty` — SYMBOLIC ALGEBRA
//! that `eq` must keep comparing structurally — are as un-reduced on a term as they
//! were on an occurrence. That is the trap this door has been walked through before:
//! WI-1057 widened `is_unreduced_op_call` to admit body-less spec ops and broke 5
//! `wi616_semantic_eq_test` cases, turning definite FAILURES into residual successes
//! (`eq({1,2},{1,3})` and even `{1,2} === {2,1}` answering 1 where they must answer 0).
//! `resolve_tests` — which is where those 5 rows live — is green here, and is named as
//! the row set this widening is measured against.
//!
//! # What each row measures, and what fails when the change is backed out
//!
//! MEASURED by mutating each shipped change one at a time and re-running, not
//! predicted. The back-outs are:
//!
//!  * **(R)** `reduce_op_value`'s non-`Node` arm restored to `_ => return v`.
//!  * **(D)** `is_unreduced_op_call` restored to `let Value::Node(occ) = v else {
//!    return false }`.
//!  * **(A)** the `pos_arity + named_arity > 0` test dropped from that predicate's view
//!    arm.
//!  * **(U)** `unify_terms` mapping `TermUnification::Undecided` back onto `NoUnifier`.
//!  * **(E)** a `matches!(v, Value::Entity { .. }) => false` guard ahead of that
//!    predicate's view arm — not a back-out of anything shipped, but the CARRIER PROBE
//!    that says which rows ride `Entity` rather than merely saying so in their name.
//!
//! | back out | red rows |
//! |---|---|
//! | (R) | [`an_op_call_operand_decides_on_the_term_carrier`], [`an_op_call_operand_decides_on_the_entity_carrier`], [`a_constraint_guard_over_an_op_call_decides_both_ways`] |
//! | (D) | [`an_unreducible_term_carried_op_call_still_delays`], [`an_unreducible_entity_carried_op_call_still_delays`] |
//! | (A) | [`a_bare_nullary_op_name_is_still_data`] |
//! | (U) | [`an_undecidable_pair_is_not_reported_as_non_unifiable`] |
//! | (E) | [`an_unreducible_entity_carried_op_call_still_delays`] alone |
//! | (R) **and** (D) | all of the above, plus the `neq` column of the first two |
//!
//! Each was run on its own and left EXACTLY the rows above red, at exactly the
//! assertions named there — (R) at the `eq` row of each carrier and at the `Box(w: 3)`
//! polarity of the guard, (D) with `1` where `0` is required in both delay rows.
//!
//! **(E) IS IN THE TABLE BECAUSE ITS FIRST ANSWER WAS THAT NOTHING RODE `Entity`.** The
//! first cut of the entity delay row left all six rows green under (E) — it measured
//! the `Term` carrier twice — and that row's own doc records the fixture change.
//! `an_op_call_operand_decides_on_the_entity_carrier` and the constraint guard ride
//! `Entity` through the REDUCTION gate (they go red under (E)'s reduce-side twin), and
//! the delay row rides it through the predicate.
//!
//! **The same arity test in the REDUCTION's own gate (`op_call_occurrence_to_reduce`)
//! drives NO row**, measured the same way: dropping it leaves every row here green,
//! because `value_as_occurrence` materializes a nullary `Term` / `SymbolRef` head as an
//! `Expr::Ref` LEAF, which `reduce_op_value` hands straight back. Its reason is
//! recorded at that function and is alignment with the driven half, not a fixture.
//!
//! # What `/code-review` found after the first cut, and what it corrected
//!
//! Four of its five findings are fixed above and each has a row or a named doc
//! correction: `unify_terms`' Delay→`None` collapse (U), the reduce gate not being a
//! superset of its delay partner (`op_call_occurrence_to_reduce`'s union leg), the
//! entity row that did not ride `Entity` (E), and a "cost gate" headline that was a
//! behavioural narrowing on one carrier.
//!
//! The fifth — that this ticket makes `unify` / `===` "dispatch" where they are
//! documented not to — is a MIS-ATTRIBUTION, and
//! [`a_folding_operand_is_not_new_under_unify_or_struct_eq`] is the control that says
//! so: both fold on the `Node` carrier at HEAD. The docs claiming otherwise were
//! corrected (kernel.anthill's `unify` and `struct_eq` declarations, `BuiltinTag::Eq` /
//! `Unify`, `builtin_unify`) rather than the code reverted — "never dispatches" is
//! true of the COMPARISON (no carrier's `Eq` member is selected) and was never true of
//! the OPERANDS.
//!
//! **THE `neq(dbl(2), 4)` COLUMN — THE TICKET'S HEADLINE WRONG ANSWER — IS GREEN UNDER
//! EITHER BACK-OUT ALONE**, and is said here rather than left for a reader to discover
//! from a back-out that changes nothing. Two repairs are each SUFFICIENT for it: (R)
//! computes `dbl(2) = 4` and `neq(4, 4)` is false, and (D) delays instead of deciding,
//! which also yields no definite solution. It is the `eq` / `lt` columns beside it that
//! attribute (R), because a delay cannot produce the answer they require.
//!
//! CONTROLS — each passes with (R) and (D) backed out:
//!
//!  * **The rule-body twin** beside every carrier row (`body_neq` / `body_eq` /
//!    `body_lt`), asserted in the same test. Rule bodies carry OCCURRENCES (WI-246), so
//!    that column was correct before this ticket and must stay correct after it. It is
//!    what attributes each failure to the CARRIER rather than to the fixture.
//!  * `resolve_tests::wi616_semantic_eq_test` (10 rows) and
//!    `wi738_operand_call_delay_test` — the domain of `eq` and the `Node`/`Term` faces
//!    of the delay predicate. Green under both back-outs, which is what says these arms
//!    were ADDED and not moved.

use anthill_core::eval::value::Value;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use smallvec::SmallVec;

use crate::common::{definite_unary, try_load_kb_with};

// ── Term-goal plumbing (the same shape `wi_7ypgm_goal_walk_flatness_test` uses) ──
//
// Every carrier row here builds its goals as hash-consed TERMS and calls `kb.resolve`
// directly, because that is the carrier the ticket is about: a rule body carries
// OCCURRENCES (WI-246), so only a direct `kb.resolve(&[Value::term(..)])`,
// `execute_logical_query`, a constraint guard (`lower_query`) or the reflect
// `execute(and(..))` reaches the `Value::Term` goal walk at all — and a PRECEDING goal
// that binds a variable is what moves the next one onto the `Value::Entity` carrier
// (`reify_value_transient`, WI-20260906-7YPGM).

/// A fresh logic variable as a term.
fn var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let s = kb.intern(name);
    let v = kb.fresh_var(s);
    kb.alloc(Term::Var(Var::Global(v)))
}

/// `qn(args…)` as a hash-consed application term.
fn call(kb: &mut KnowledgeBase, qn: &str, args: &[TermId]) -> TermId {
    let f = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("`{qn}` must resolve"));
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

/// Resolve a term conjunction, keeping only DEFINITE solutions — the WI-519 decision
/// boundary, so a floundered residual cannot be counted as a proof.
///
/// FILTERED, not `definite_only: true`: that flag PRUNES the search as well as the
/// answers, and the WI-580 case-split reaches solutions through branches it drops.
fn definite(kb: &mut KnowledgeBase, goals: &[TermId]) -> usize {
    let gs: Vec<Value> = goals.iter().map(|&t| Value::term(t)).collect();
    kb.resolve(&gs, &ResolveConfig::default())
        .into_iter()
        .filter(anthill_core::kb::resolve::Solution::is_definite)
        .count()
}

/// The stdlib **and the Rust bindings** plus the fixture: the primitive spec FACTS
/// (`fact Numeric[Int64]` and friends) live in the binding files, and without them
/// `dbl` has no arithmetic to bridge to — the rows would answer nothing for a reason
/// that has nothing to do with this ticket.
fn load_with_stdlib(extra: &str) -> KnowledgeBase {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).unwrap_or_else(|e| panic!("parse extra: {e:?}")));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver).unwrap_or_else(|e| panic!("load: {e:?}"));
    kb
}

/// `dbl` is BODIED and its body is ARITHMETIC, so the structural fold cannot collapse
/// it and the reduction is `bridge_op_to_eval`'s — the "COMPLEX body" arm, which is the
/// one a carrier could hide. `tau` is the nullary control's callee.
const SRC: &str = r#"
namespace fdpj8
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Numeric.{add}
  import anthill.prelude.PartialEq.{eq, neq}
  import anthill.prelude.Int64.{lt}
  import anthill.kernel.{unify, struct_eq}

  entity Box(w: Int64)
  fact Box(w: 2)
  rule box(?v) :- Box(w: ?v)

  operation dbl(n: Int64) -> Int64 = add(n, n)
  operation tau() -> Int64 = 7

  -- THE CONTROL COLUMN: the identical goals written in a rule BODY, which carries
  -- occurrences (WI-246) and answered correctly before this ticket.
  rule body_neq(?v) :- Box(w: ?v), neq(dbl(?v), 4)
  rule body_eq(?v)  :- Box(w: ?v), eq(dbl(?v), 4)
  rule body_lt(?v)  :- Box(w: ?v), lt(dbl(?v), 5)

  -- The `unify` / `===` faces of the same operand pipeline, on the NODE carrier —
  -- green at HEAD and here, which is what says this ticket widened the CARRIER and
  -- not the DISPATCH (see `a_folding_operand_is_not_new_under_unify_or_struct_eq`).
  rule node_unify_val(?v)  :- Box(w: ?v), unify(dbl(?v), 4)
  rule node_streq_val(?v)  :- Box(w: ?v), struct_eq(dbl(?v), 4)
end
"#;

/// The rule-body column of the table, asserted once and called by both carrier rows —
/// so a carrier row cannot pass while its own control has silently moved.
fn assert_rule_body_control(kb: &mut KnowledgeBase) {
    for (qn, want) in [
        ("fdpj8.body_neq", 0),
        ("fdpj8.body_eq", 1),
        ("fdpj8.body_lt", 1),
    ] {
        let got = definite_unary(kb, qn);
        assert_eq!(
            got.len(),
            want,
            "CONTROL `{qn}`: the same goal in a rule BODY rides the `Value::Node` \
             carrier and answered correctly before this ticket. If it moved, the \
             carrier rows below measure something other than the carrier. Got {got:?}",
        );
    }
}

/// THE TABLE, term-carried. `dbl(2)` IS 4, so `neq` is false, `eq` is true and
/// `lt(.., 5)` is true — whatever carrier the goal was written on.
#[test]
fn an_op_call_operand_decides_on_the_term_carrier() {
    let mut kb = load_with_stdlib(SRC);
    assert_rule_body_control(&mut kb);

    let two = kb.alloc(Term::Const(Literal::Int(2)));
    let four = kb.alloc(Term::Const(Literal::Int(4)));
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let dbl2 = call(&mut kb, "fdpj8.dbl", &[two]);

    for (qn, arg, want, why) in [
        (
            "anthill.prelude.PartialEq.neq",
            four,
            0,
            "`neq(dbl(2), 4)` must NOT be proved — `dbl(2)` is 4. A definite solution \
             is the structural lie WI-738's floor exists to stop, reached one carrier \
             over",
        ),
        (
            "anthill.prelude.PartialEq.eq",
            four,
            1,
            "`eq(dbl(2), 4)` must be proved — a delay cannot produce this answer, so \
             it is what attributes the row to the REDUCTION and not to the delay",
        ),
        (
            "anthill.prelude.Int64.lt",
            five,
            1,
            "`lt(dbl(2), 5)` must be proved — 0 here is WI-879's `no order for this \
             operand pair (dbl and Int64)`, the cmp face of the same hole",
        ),
    ] {
        let g = call(&mut kb, qn, &[dbl2, arg]);
        assert_eq!(definite(&mut kb, &[g]), want, "{why}");
    }
}

/// The same table, ENTITY-carried: a preceding goal binds `?v`, so the goal walk
/// σ-moves the call OFF the hash-consed store (`reify_value_transient`) and the operand
/// arrives as an `Entity` spine rather than a `Term`.
#[test]
fn an_op_call_operand_decides_on_the_entity_carrier() {
    let mut kb = load_with_stdlib(SRC);
    assert_rule_body_control(&mut kb);

    let four = kb.alloc(Term::Const(Literal::Int(4)));
    let five = kb.alloc(Term::Const(Literal::Int(5)));

    for (qn, arg, want) in [
        ("anthill.prelude.PartialEq.neq", four, 0),
        ("anthill.prelude.PartialEq.eq", four, 1),
        ("anthill.prelude.Int64.lt", five, 1),
    ] {
        let x = var(&mut kb, "x");
        let bind = call(&mut kb, "fdpj8.box", &[x]);
        assert_eq!(
            definite(&mut kb, &[bind]),
            1,
            "the binding goal must answer, or the conjunction below falls through \
             before reaching the operand at all",
        );
        let dblx = call(&mut kb, "fdpj8.dbl", &[x]);
        let g = call(&mut kb, qn, &[dblx, arg]);
        assert_eq!(
            definite(&mut kb, &[bind, g]),
            want,
            "`[box(?x), {qn}(dbl(?x), …)]` must answer {want} times: `?x` is 2 and \
             `dbl(2)` is 4. The operand is `Entity`-carried here because a preceding \
             goal bound `?x`",
        );
    }
}

/// **THE DELAY HALF.** A call the reduction CANNOT decide — `dbl(?x)` with `?x` free,
/// where `bridge_op_to_eval` declines a non-ground argument and hands the ORIGINAL call
/// back — must still DELAY on a term carrier, not be compared as data.
///
/// FAILS when `is_unreduced_op_call` is narrowed back to `Value::Node`: the operand
/// reads as ordinary DATA, `neq` compares the term `dbl(?x)` to `4` structurally, the
/// heads differ, and the goal is PROVED. WI-738's "silently, unconditionally TRUE",
/// verbatim, on the carrier the reduction now reaches but the delay did not.
#[test]
fn an_unreducible_term_carried_op_call_still_delays() {
    let mut kb = load_with_stdlib(SRC);
    let four = kb.alloc(Term::Const(Literal::Int(4)));
    let x = var(&mut kb, "x");
    let dblx = call(&mut kb, "fdpj8.dbl", &[x]);
    let g = call(&mut kb, "anthill.prelude.PartialEq.neq", &[dblx, four]);
    assert_eq!(
        definite(&mut kb, &[g]),
        0,
        "`neq(dbl(?x), 4)` with `?x` free must NOT be proved: nothing has decided what \
         `dbl(?x)` is, so no verdict may be committed over it",
    );
}

/// The same delay, ENTITY-carried — and the CALL ITSELF must hold the bound variable,
/// which is what the first cut of this row got wrong.
///
/// **A ROW THAT NAMED A CARRIER WITHOUT RIDING IT, found by `/code-review` and
/// recorded because the mistake is invisible from the assertion.** That cut was
/// `[box(?v), neq(dbl(?y), ?v)]` — `?v` bound, `?y` free. σ rebuilds only the nodes it
/// MOVES, and `reify_on` hands back the shared `Value::term(t)` for an untouched
/// subterm, so the operand `dbl(?y)`, which contains no bound var, arrived as a
/// `Value::Term`: a second copy of the row above it, asserting the same 0 for the same
/// reason. MEASURED — blinding `is_unreduced_op_call`'s view arm to `Value::Entity`
/// left ALL SIX shipped rows green.
///
/// `dbl(add(?v, ?y))` fixes it by putting the bound `?v` INSIDE the call: σ must
/// rebuild the spine, so the operand is `Entity`-carried, while the free `?y` keeps the
/// reduction undecidable so it reaches the delay rather than a value. MEASURED: 1 with
/// that blind in place, 0 without it — the wrong answer and the right one.
#[test]
fn an_unreducible_entity_carried_op_call_still_delays() {
    let mut kb = load_with_stdlib(SRC);
    let four = kb.alloc(Term::Const(Literal::Int(4)));
    let v = var(&mut kb, "v");
    let y = var(&mut kb, "y");
    let bind = call(&mut kb, "fdpj8.box", &[v]);
    let inner = call(&mut kb, "anthill.prelude.Int64.add", &[v, y]);
    let d = call(&mut kb, "fdpj8.dbl", &[inner]);
    let g = call(&mut kb, "anthill.prelude.PartialEq.neq", &[d, four]);
    assert_eq!(
        definite(&mut kb, &[bind, g]),
        0,
        "`[box(?v), neq(dbl(add(?v, ?y)), 4)]` must NOT be proved: `?v` is 2 — which \
         is what moves the operand onto the `Entity` carrier — but `?y` is free, so \
         `dbl(add(2, ?y))` is undecided and no verdict may be committed over it",
    );
}

/// **`unify` AND `===` ALREADY FOLDED AN OP-CALL OPERAND, on the `Node` carrier, before
/// this ticket** — the control for a `/code-review` finding that read this ticket's
/// carrier widening as a new DISPATCH under two builtins documented "never dispatches
/// — structural only".
///
/// They share ONE operand pipeline with `eq`/`cmp`/`arith` (`reduce_operand`, reached
/// from `eq_operands` and `unify_values` alike), and it has reduced op-call operands
/// since WI-483/WI-738. So the claim to check is not whether folding is right — that
/// decision is years old — but whether this ticket introduced it. It did not: both rows
/// answer 1 at HEAD and here. What the ticket changed is that the `Term` and `Entity`
/// spellings now agree with this one.
///
/// Green under every back-out in the table above; the stale doc lines these rows
/// falsify were corrected on `kernel.anthill`'s two declarations and on `BuiltinTag`.
#[test]
fn a_folding_operand_is_not_new_under_unify_or_struct_eq() {
    let mut kb = load_with_stdlib(SRC);
    for qn in ["fdpj8.node_unify_val", "fdpj8.node_streq_val"] {
        let got = definite_unary(&mut kb, qn);
        assert_eq!(
            got.len(),
            1,
            "`{qn}` folds `dbl(2)` to 4 and succeeds — at HEAD as well as here. A 0 \
             would mean this ticket changed what these two builtins DO, rather than \
             which carriers they do it on. Got {got:?}",
        );
    }
}

/// **AN UNDECIDABLE PAIR IS NOT "THESE TERMS DO NOT UNIFY".** `KnowledgeBase::unify_terms`
/// returned `Option<Substitution>` and mapped the delay onto `None`, ring-fenced by a
/// doc claim this ticket falsifies — "a delaying op-call operand (only reachable from
/// occurrence-carried inputs) reads as non-unifiable here". Once the delay predicate
/// reads every carrier, a TERM-carried op call reaches it, and `reflect.unify` handed
/// the program `none()` for two terms that plainly unify structurally.
///
/// The three rows are the three answers, so a return that collapsed any two of them
/// fails here. FAILS when `unify_terms` maps `Undecided` back onto `NoUnifier`: the
/// first row reports a definite "no unifier" for `dbl(?x)` vs `dbl(?y)`.
/// Found by `/code-review`.
#[test]
fn an_undecidable_pair_is_not_reported_as_non_unifiable() {
    use anthill_core::kb::resolve::TermUnification;
    let mut kb = load_with_stdlib(SRC);
    let two = kb.alloc(Term::Const(Literal::Int(2)));
    let four = kb.alloc(Term::Const(Literal::Int(4)));
    let x = var(&mut kb, "x");
    let y = var(&mut kb, "y");

    let dx = call(&mut kb, "fdpj8.dbl", &[x]);
    let dy = call(&mut kb, "fdpj8.dbl", &[y]);
    assert!(
        matches!(kb.unify_terms(dx, dy), TermUnification::Undecided),
        "`unify_terms(dbl(?x), dbl(?y))` is UNDECIDED — nothing has said what either \
         call is. `NoUnifier` here is a definite claim the walk never earned, and it \
         is what `reflect.unify` hands out as `none()`",
    );

    let d2 = call(&mut kb, "fdpj8.dbl", &[two]);
    assert!(
        matches!(kb.unify_terms(d2, four), TermUnification::Unifier(_)),
        "`unify_terms(dbl(2), 4)`: `dbl(2)` IS 4, so the pair unifies with an empty σ",
    );
    let d4 = call(&mut kb, "fdpj8.dbl", &[four]);
    assert!(
        matches!(kb.unify_terms(d4, four), TermUnification::NoUnifier),
        "THE THIRD ANSWER, and the polarity that says the row above is not just \
         reporting success for everything: `dbl(4)` is 8, which does not unify with 4",
    );
}

/// **A BARE NULLARY OP NAME IS DATA, NOT A CALL** — the `pos + named > 0` test both new
/// reads carry, and the one place the carrier-neutral view is WIDER than the shape it
/// is standing in for. The storage canon collapses `Fn{tau}` to `Ref(tau)` (WI-436), so
/// on every carrier but `Node` a bare name and a nullary call are ONE term; opening it
/// as a call is the reading WI-20260902-VZC2C explicitly refused at `reduce_op_value`
/// ("a bare nullary op in an ARROW-typed slot is §5.4's unapplied function value").
///
/// `eq(tau, tau)` holds by reflexivity over one shared `TermId`. MEASURED red when the
/// arity test is dropped from `is_unreduced_op_call`'s view arm (back-out (A)): both
/// operands report un-reduced, the goal delays, and the answer is LOST — 0 where 1 is
/// required — rather than refused. It is green under (R) and under (D), so it is a
/// control for those two and the measurement of the third.
#[test]
fn a_bare_nullary_op_name_is_still_data() {
    let mut kb = load_with_stdlib(SRC);
    let tau = kb
        .try_resolve_symbol("fdpj8.tau")
        .expect("`fdpj8.tau` must resolve");
    let bare = kb.alloc(Term::Ref(tau));
    let g = call(&mut kb, "anthill.prelude.PartialEq.eq", &[bare, bare]);
    assert_eq!(
        definite(&mut kb, &[g]),
        1,
        "`eq(tau, tau)` over a BARE nullary op name must hold by reflexivity: a bare \
         name in operand position is §5.4's unapplied function value — DATA — and \
         delaying on it loses an answer rather than refusing one",
    );
}

/// **THE SOURCE-REACHABLE FACE.** A constraint guard is term-carried (`lower_query`),
/// so this program needs no hand-built `kb.resolve` at all: `no ?v: Box(w: ?v) -:
/// neq(dbl(?v), 4)` asks whether any row has `dbl(?v) ≠ 4`.
///
/// BOTH POLARITIES, so a guard that answers a constant fails whichever way it is wrong:
/// `Box(w: 2)` has `dbl(2) = 4` and must LOAD; `Box(w: 3)` has `dbl(3) = 6` and must be
/// REFUSED naming the constraint. At HEAD both were refused — the guard enforced
/// nothing, and said so only about the corpus that was fine.
///
/// FAILS when the reduction is narrowed back to `Value::Node`: with the delay half
/// alone the guard finds no DEFINITE witness for either row, so `Box(w: 3)` loads and
/// the second half goes red. That is what makes this row attribute the REDUCTION.
#[test]
fn a_constraint_guard_over_an_op_call_decides_both_ways() {
    let corpus = |w: i64| {
        format!(
            r#"
namespace fdpj8_c
  import anthill.prelude.{{Int64, Bool}}
  import anthill.prelude.Numeric.{{add}}
  import anthill.prelude.PartialEq.{{neq}}

  entity Box(w: Int64)
  operation dbl(n: Int64) -> Int64 = add(n, n)

  constraint none_bad:
    no ?v: Box(w: ?v) -: neq(dbl(?v), 4)

  fact Box(w: {w})
end
"#
        )
    };
    let ok = try_load_kb_with(&corpus(2));
    assert!(
        ok.is_ok(),
        "`dbl(2)` IS 4, so no row witnesses `neq(dbl(?v), 4)` and the corpus must \
         load. A refusal here is the guard reporting a violation of nothing: {:?}",
        ok.err(),
    );
    let errs = try_load_kb_with(&corpus(3)).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("none_bad")),
        "THE CONTROL POLARITY: `dbl(3)` is 6, so this corpus DOES violate the \
         constraint and must be refused NAMING it — otherwise the row above is \
         passing over a guard that enforces nothing. Got {errs:?}"
    );
}
