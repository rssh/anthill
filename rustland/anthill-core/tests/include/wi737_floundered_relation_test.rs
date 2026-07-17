//! WI-737 — a FLOUNDERED relation drain RAISES; it never presents an answer the
//! search did not DECIDE as a definite row.
//!
//! A `Relation[T]` (proposal 052) promises rows of `T`, and `T` has no room for a
//! third "undecided" outcome. `materialize_solution` used to read every column
//! through the answer substitution without ever consulting `sol.is_definite()`, so
//! a floundered solution — one whose residual holds goals that delayed on variables
//! that never got bound — materialized anyway, in two distinct lies:
//!
//!   1. A VAR-BEARING ROW. `distinct_pair` is typed `Relation[(x: Int64, y: Int64)]`
//!      yet drained to ONE row holding `(x: Var(Global(1232)), y: Var(Global(1233)))`
//!      — a logic variable sitting in a column the schema types `Int64`. A type-level
//!      lie in the very face built to REPLACE raw `Substitution` walking with typed
//!      rows.
//!   2. SPURIOUS MEMBERSHIP. A relation over an undecidable body drained NON-EMPTY,
//!      so a floundered residual read as a positive membership answer — including
//!      the 0-column case, which returned `unit` from the early return before any
//!      column was even inspected.
//!
//! The rest of the codebase already got this right, which is what made the gap a
//! REGRESSION rather than a missing feature: `make_solution_value` reifies
//! `definite` vs `undecided` precisely so consumers can inspect what stayed pending;
//! `relation_negate` refuses a free-column operand rather than risk exactly this;
//! anthill-todo's hand-written walk skips `case undecided(_, _)`. The typed face
//! built to RETIRE that boilerplate had silently lost the residual honesty (WI-519)
//! the boilerplate had. The existing wi714 suites missed it because they all query
//! ground facts, which only ever yield definite solutions — so the controls at the
//! bottom of this file are load-bearing, not ceremony.
//!
//! THE SPLIT: the RAW reflect / LogicalStream face keeps undecidedness as DATA
//! (`execute` yields `undecided(subst, residual)`, never raised on its `E` channel,
//! so WI-010's self-hosted resolver can inspect it); the TYPED Relation face raises.
//! `E ⊇ {Error}` on every relation already, so the raise needed no signature change.

use crate::common::interp_for;
use anthill_core::eval::{EvalError, Value};

const SRC: &str = r#"
namespace test.wi737
  import anthill.prelude.{Int64, List, Unit, Bool}
  import anthill.prelude.List.{length}

  sort Num
    entity num(v: Int64)
  end
  fact num(v: 1)
  fact num(v: 2)
  fact num(v: 3)

  -- SYMPTOM 1: both head vars free, so the comparison guard flounders in mode
  -- (out, out) (WI-739) — the whole rule delays and never decides.
  rule distinct_pair(?x, ?y) :- num(v: ?x), num(v: ?y), neq(?x, ?y)
  operation pairCount() -> Int64 effects Error = length(distinct_pair.takeN(10))

  -- SYMPTOM 2: `?y` is body-local and NO goal ever binds it, so `neq(?y, ?x)`
  -- delays forever. `num(v: ?x)` still binds `?x`, so this drained THREE rows
  -- with perfectly bound columns — the residual was the only evidence the body
  -- was never decided, and materialization threw it away.
  rule floundered_member(?x) :- num(v: ?x), neq(?y, ?x)
  operation memberCount() -> Int64 effects Error = length(floundered_member.takeN(10))

  -- SYMPTOM 2b: the 0-COLUMN membership relation — the path that returned `unit`
  -- from the early return, before any column was inspected. This is why the gate
  -- sits BEFORE the `columns.is_empty()` return, not inside the column loop.
  rule flounders() :- neq(?y, 1)
  operation membershipCount() -> Int64 effects Error = length(flounders.takeN(10))

  -- CONTROL: the SAME two free columns as `distinct_pair`, minus the guard —
  -- a plain fact join, which decides. Isolates the raise to the FLOUNDER, not to
  -- "the relation has free columns" (which `negate`'s guard keys on) nor to arity.
  rule pair_any(?x, ?y) :- num(v: ?x), num(v: ?y)
  operation pairAnyCount() -> Int64 effects Error = length(pair_any.takeN(20))

  -- CONTROL, the sharpest: the SAME body and the SAME `neq` guard as
  -- `distinct_pair`, but `?x` / `?y` are BODY-LOCAL rather than head params — so
  -- they are not CALLER vars, the rule-level pre-check does not delay, `num` binds
  -- both before `neq` runs, and the guard DECIDES. Same guard, opposite verdict:
  -- the flounder is a property of the MODE, and the gate reads the RESIDUAL — not
  -- the guard's presence, not the rule's shape.
  rule distinct_local() :- num(v: ?x), num(v: ?y), neq(?x, ?y)
  operation distinctLocalCount() -> Int64 effects Error =
    length(distinct_local.takeN(20))

  -- CONTROL: a definite 0-column membership relation still yields its `unit` row.
  rule has_one() :- num(v: 1)
  operation hasOneCount() -> Int64 effects Error = length(has_one.takeN(10))

  -- MIXED: clause 1 decides (3 rows), clause 2 flounders. The raise is LAZY —
  -- it fires only if the drain actually pumps that far.
  rule mixed(?x) :- num(v: ?x)
  rule mixed(?x) :- num(v: ?x), neq(?y, ?x)
  operation mixedBounded() -> Int64 effects Error = length(mixed.takeN(3))
  operation mixedFull() -> Int64 effects Error = length(mixed.takeN(10))
end
"#;

/// Resolve a CANONICAL name to its Symbol. Constructor identity is compared by
/// canonical symbol, never by short name — a last-segment match is unsound (WI-672
/// deleted `same_symbol` for exactly this) and would let any other sort's `cons` /
/// `nil` / `relation_floundered` satisfy these assertions. Field LABELS below are
/// still name-compared: a label is not a qualified identity (cf. `same_label`).
fn canonical(interp: &anthill_core::eval::Interpreter, qname: &str) -> anthill_core::intern::Symbol {
    interp
        .kb()
        .try_resolve_symbol(qname)
        .unwrap_or_else(|| panic!("`{qname}` must be in scope"))
}

/// Assert `err` is the WI-737 raise, and return the number of residual goals its
/// payload names. Mirrors `eval_test::m3_int_division_by_zero`'s idiom: unhandled,
/// a routed `Error` effect surfaces as `Raised` carrying the payload entity.
fn assert_floundered(interp: &anthill_core::eval::Interpreter, err: EvalError) -> usize {
    let payload = match err {
        EvalError::Raised { payload } => payload,
        other => panic!(
            "a floundered drain must RAISE on the Error channel (E ⊇ {{Error}} already), \
             got {other:?}"
        ),
    };
    let (functor, named) = match &payload {
        Value::Entity { functor, named, .. } => (*functor, named),
        other => panic!("expected a relation_floundered(goals:) entity payload, got {other:?}"),
    };
    assert_eq!(
        functor,
        canonical(interp, "anthill.prelude.RelationFloundered.relation_floundered"),
        "the payload is the RelationFloundered witness, not some other Error payload"
    );
    let goals = named
        .iter()
        .find(|(k, _)| interp.kb().resolve_sym(*k) == "goals")
        .map(|(_, v)| v)
        .unwrap_or_else(|| panic!("payload carries a `goals` field; got {payload:?}"));
    // Walk the cons/nil spine. The goals ride carrier-faithfully (WI-348): a goal
    // that came from source keeps its `Value::Node` occurrence, one built as a term
    // is a `Value::Term` — this suite exercises BOTH, so count the spine rather
    // than matching either carrier.
    let cons = canonical(interp, "anthill.prelude.List.cons");
    let nil = canonical(interp, "anthill.prelude.List.nil");
    let mut n = 0usize;
    let mut cur = goals;
    loop {
        let (functor, named) = match cur {
            Value::Entity { functor, named, .. } => (*functor, named),
            other => panic!("goals is a List spine (cons/nil), found {other:?}"),
        };
        if functor == nil {
            break;
        }
        assert_eq!(functor, cons, "goals is a List spine (cons/nil)");
        n += 1;
        cur = named
            .iter()
            .find(|(k, _)| interp.kb().resolve_sym(*k) == "tail")
            .map(|(_, v)| v)
            .expect("a cons cell has a tail");
    }
    n
}

/// SYMPTOM 1: the var-bearing row. `distinct_pair` is typed
/// `Relation[(x: Int64, y: Int64)]`; it used to drain to one row whose BOTH columns
/// held unbound logic variables. Now the drain raises and names the pending goal.
#[test]
fn wi737_var_bearing_row_raises_instead_of_materializing() {
    let mut interp = interp_for(SRC);
    let err = interp
        .call("test.wi737.pairCount", &[])
        .expect_err("an undecided body must not drain to a row of logic variables");
    let goals = assert_floundered(&interp, err);
    assert!(
        goals >= 1,
        "the raise NAMES the undischarged goals — it carried {goals}"
    );
}

/// SYMPTOM 2: spurious membership. The columns here are BOUND (1, 2, 3), so the
/// row looked perfectly well-typed — only the residual showed the body was never
/// decided. Pins that the gate reads `is_definite()`, not "does a column hold a Var".
#[test]
fn wi737_spurious_membership_over_undecidable_body_raises() {
    let mut interp = interp_for(SRC);
    let err = interp
        .call("test.wi737.memberCount", &[])
        .expect_err("an undecided body must not report rows, even with bound columns");
    let goals = assert_floundered(&interp, err);
    assert!(goals >= 1, "the raise names the undischarged goals");
}

/// SYMPTOM 2b: the 0-column membership relation — the `Value::Unit` early return.
/// Pins the gate's PLACEMENT: before the `columns.is_empty()` return, since that
/// path never inspects a column and so could never notice the residual.
#[test]
fn wi737_zero_column_membership_raises_rather_than_yielding_unit() {
    let mut interp = interp_for(SRC);
    let err = interp
        .call("test.wi737.membershipCount", &[])
        .expect_err("a floundered 0-column membership must not read as `unit` = provable");
    let goals = assert_floundered(&interp, err);
    assert!(goals >= 1, "the raise names the undischarged goals");
}

/// CONTROL: definite relations are unaffected. Same two free columns as
/// `distinct_pair`, minus the floundering guard — so the raise is attributable to the
/// FLOUNDER, not to free columns (what `negate`'s guard keys on) or to arity.
#[test]
fn wi737_definite_relation_still_drains() {
    let mut interp = interp_for(SRC);
    let n = interp
        .call("test.wi737.pairAnyCount", &[])
        .expect("a DEFINITE relation drains unchanged — the gate is on the residual");
    assert_eq!(n.as_int(), Some(9), "3 nums x 3 nums, no guard to flounder on");
}

/// CONTROL, the sharpest: the SAME `neq` guard that makes `distinct_pair` raise
/// DECIDES here, because its vars are body-local rather than caller vars — so `num`
/// binds them before the guard runs. Same guard, opposite verdict: the gate reads
/// the RESIDUAL, not the guard's presence.
#[test]
fn wi737_same_guard_drains_when_its_vars_are_not_caller_vars() {
    let mut interp = interp_for(SRC);
    let n = interp
        .call("test.wi737.distinctLocalCount", &[])
        .expect("a decidable `neq` must NOT raise — the guard is not the trigger");
    assert_eq!(
        n.as_int(),
        Some(6),
        "the 6 ordered pairs of distinct nums, each proving the membership once"
    );
}

/// CONTROL: a definite 0-column membership relation still yields its `unit` row —
/// the early return is gated, not removed.
#[test]
fn wi737_definite_membership_still_yields_unit() {
    let mut interp = interp_for(SRC);
    let n = interp
        .call("test.wi737.hasOneCount", &[])
        .expect("a definite membership relation still drains");
    assert_eq!(n.as_int(), Some(1), "num(v: 1) is provable exactly once");
}

/// The gate is PER-SOLUTION and lazy, not per-relation: a relation whose definite
/// answers precede a floundered one still drains its definite prefix, and raises only
/// if the consumer actually pumps into the undecided region. So `takeN(3)` succeeds on
/// the very relation `takeN(10)` raises on — which is the honest reading of a bounded
/// drain over a maybe-infinite carrier, not an inconsistency: the bound is what decides
/// how much search you asked for, and you are only told about undecidedness you reached.
#[test]
fn wi737_definite_prefix_drains_and_the_raise_is_lazy() {
    let mut interp = interp_for(SRC);
    let bounded = interp
        .call("test.wi737.mixedBounded", &[])
        .expect("the 3 definite rows drain — the drain never reaches the floundered clause");
    assert_eq!(bounded.as_int(), Some(3), "clause 1's three definite rows");

    let err = interp
        .call("test.wi737.mixedFull", &[])
        .expect_err("pumping past them reaches the floundered clause, which raises");
    let goals = assert_floundered(&interp, err);
    assert!(goals >= 1, "the raise names the undischarged goals");
}
