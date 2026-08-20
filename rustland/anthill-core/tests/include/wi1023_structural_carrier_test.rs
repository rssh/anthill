//! WI-1023 — the three questions the four hand-written carrier lists were all
//! trying to answer, each driven per admitted carrier.
//!
//! "Is this carrier structurally equivalent to its term twin" was asked at four
//! sites, answered by four `matches!` lists, and they had drifted. The lists are
//! gone; three NAMED predicates took their place, and they are not one predicate
//! because they are not one question:
//!
//!  - [`ViewHead::is_opaque`] — "does this carrier present a SHAPE?" — answer
//!    dedup (`SearchStream::is_duplicate_answer`, named `is_duplicate_projection`
//!    when this file was written).
//!  - `Value::lowers_to_leaf_term` — "does it lower to a LEAF term, losslessly
//!    and infallibly?" — the `Term`-vs-`Entity` carrier choice (`fn_value`).
//!  - the `ViewHead::Ref` read in `MapKey::try_from_value` — "is it the same
//!    NAME?" — covered by that module's own unit tests.
//!
//! Two of the three move in a direction where being wrong LOSES data — an
//! over-eager dedup DROPS an answer, a re-routed head splits one logical fact
//! across two disjoint key spaces — so every test here states, MEASURED, what it
//! reports when the change under it is backed out, and which of them pass either
//! way BY DESIGN (they guard the losing direction and must never have been red).

use std::rc::Rc;

use smallvec::SmallVec;

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::{ClauseKind, KnowledgeBase};
use anthill_core::span::{SourceId, SourceSpan};

// ── (A) `is_duplicate_answer` — one σ-injection gadget, every carrier ────────
//
// `resolve_sort_instantiation_param(SortView(T: <v>), T, ?out)` binds `?out` to
// the `SortView`'s `T` slot **in that value's own carrier** (`finish_result_value`,
// WI-1015) — the route the WI-1016 dedup test already drives, and the one the
// ticket names for `Value::Requirement` via `Dictionary.sub`. Splicing an
// arbitrary `Value` into that slot puts an arbitrary carrier into σ, so ONE
// fixture drives every carrier the widened predicate admits.
//
// The two routes are alternatives for ONE goal. That was FORCED when this file
// was written — dedup fingerprinted the NEAREST ancestor ChoicePoint's goal, so a
// disjunction in a rule BODY measured nothing (WI-1016's lesson) — and is merely
// the cleanest shape now that WI-FFPGD projects onto the QUERY's goals. Two rules
// with builtin-only bodies satisfy it: a builtin pushes no ChoicePoint and adds no
// intermediate goal, so `p(?x)` is both the head goal and the whole query.

/// A KB with `wi1023_p(?v) :- rsip(SortView(T: <slot>), T, ?v)` for each
/// `slot`, and the goal `wi1023_p(?x)`. Returns the number of SURVIVING
/// solutions — the whole measurement of answer dedup.
///
/// `build` mints the alternatives INSIDE the fixture's own KB, and that is not a
/// convenience: a `Symbol` is an index into one KB's symbol table and a `TermId`
/// into one KB's term store, so a value built in a second KB names something
/// else entirely. The first draft of this file did exactly that and reported 2
/// for every row — a green-looking `assert_ne!` on carriers that were not the
/// pair they claimed to be.
fn solutions_for(build: impl FnOnce(&mut KnowledgeBase) -> Vec<Value>) -> usize {
    solutions_for_rows(|kb| build(kb).into_iter().map(|s| vec![s]).collect())
}

/// Assert every row of a carrier table at once. A per-row `assert_eq!` stops at
/// the first failure, which would name ONE carrier when a change is backed out and
/// hide the rest — and "each carrier gets its own control" is the claim these
/// tables make.
fn expect_all(got: Vec<(&str, usize)>, want: usize, msg: &str) {
    let bad: Vec<&(&str, usize)> = got.iter().filter(|(_, n)| *n != want).collect();
    assert!(bad.is_empty(), "{msg}; got {bad:?}");
}

/// As [`solutions_for`], but each alternative injects a LIST of values: the last
/// one lands in `?v` (the head var, so it is goal-reachable) and the earlier ones
/// in rule-local vars the goal never mentions. That difference is the whole
/// domain distinction between the two guards.
fn solutions_for_rows(build: impl FnOnce(&mut KnowledgeBase) -> Vec<Vec<Value>>) -> usize {
    let (mut kb, goal) = fixture(build);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

fn fixture(build: impl FnOnce(&mut KnowledgeBase) -> Vec<Vec<Value>>) -> (KnowledgeBase, TermId) {
    let (kb, _q, goal) = crate::common::one_goal_carrier_fixture("wi1023_p", build);
    (kb, goal)
}

/// PREMISE of every (A) test below, asserted rather than assumed: the gadget
/// really does put the raw carrier into σ. Without this, a `1` from
/// [`solutions_for`] would be indistinguishable from a fixture that never
/// produced the carrier at all — the WI-1016 mistake, which measured dedup twice
/// and the carrier never.
#[test]
fn the_injection_gadget_puts_the_raw_carrier_into_sigma() {
    for probe in [Value::Int(1), Value::Str("s".into()), Value::Bool(true)] {
        let p = probe.clone();
        let (mut kb, goal) = fixture(move |_| vec![vec![p]]);
        let sols = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(sols.len(), 1, "one alternative answers once");
        assert!(
            sols[0].subst.iter().any(|(_, b)| b.scalar_eq(&probe)),
            "premise: σ carries {probe:?} on its own carrier, not a lowered twin",
        );
    }
}

/// EVERY carrier the widened predicate admits, driven in the direction the
/// widening MOVES: two alternatives that reach ONE answer, one on the value
/// carrier and one on the hash-consed term twin, collapse to a single solution.
///
/// Before WI-1023 the σ scan was `matches!(v, Term | Node | SymbolRef)`, so a
/// binding on any of these carriers switched answer dedup OFF entirely — fail
/// open, which is why the whole class went unnoticed. `Requirement` / `OpRef`
/// had been structural since WI-1019 (the commit before WI-1016 added the fifth
/// arm) and `Value::Var` fingerprints as a `Var` token; the scalars were never
/// re-examined after WI-348 made the key carrier-agnostic.
///
/// CONTROL, MEASURED by restoring that `matches!`: seven of the eight rows report
/// 2 — `Int`, `Bool`, `Str`, `Float`, `BigInt`, `Var`, `Entity`. `SymbolRef` is
/// the eighth and passes EITHER WAY BY DESIGN: WI-1016 admitted it already, and it
/// is in the table so the row that motivated the audit stays pinned.
#[test]
fn a_structural_binding_keeps_answer_dedup_on() {
    // Each row NAMES a carrier and mints it in the fixture's KB; the term twin is
    // built there too, by `alloc_from_value` — the one owner of every carrier's
    // lowering, so the pair is by construction two spellings of one child rather
    // than a hand-copy that could drift. Two rule bodies holding genuinely
    // different values that fingerprint the SAME is what makes one answer a
    // duplicate.
    type Mint = fn(&mut KnowledgeBase) -> Value;
    let rows: Vec<(&str, Mint)> = vec![
        ("Int", |_| Value::Int(7)),
        ("Bool", |_| Value::Bool(true)),
        ("Str", |_| Value::Str("k".into())),
        ("Float", |_| Value::Float(1.5)),
        ("BigInt", |_| Value::BigInt(num_bigint::BigInt::from(9))),
        ("SymbolRef", |kb| Value::SymbolRef(kb.intern("wi1023_c"))),
        ("Var", |kb| {
            let n = kb.intern("wi1023_r");
            Value::Var(Var::Rigid(kb.fresh_var(n)))
        }),
        // `Entity` has a term twin too, but reaches it through
        // `alloc_from_value`'s RECURSION rather than a leaf arm — a different
        // path to the same claim, so it is a row and not a separate test.
        ("Entity", |kb| {
            let c = kb.intern("wi1023_e");
            entity_of(c, Value::Int(3))
        }),
    ];
    let got: Vec<(&str, usize)> = rows
        .into_iter()
        .map(|(name, mint)| {
            let n = solutions_for(move |kb| {
                let carrier = mint(kb);
                let twin = Value::term(
                    kb.alloc_from_value(&carrier)
                        .unwrap_or_else(|e| panic!("{name}: {e:?}")),
                );
                assert_ne!(
                    std::mem::discriminant(&carrier),
                    std::mem::discriminant(&twin),
                    "{name}: premise — the two routes really are different carriers",
                );
                vec![carrier, twin]
            });
            (name, n)
        })
        .collect();
    expect_all(
        got,
        1,
        "two carriers of one answer are one answer; still separate",
    );
}

/// The direction where being wrong LOSES data, and the reason each admitted
/// carrier needs its own control: two alternatives that are genuinely DIFFERENT
/// must both survive. A widened predicate that admitted a carrier the fingerprint
/// cannot actually tell apart would show up here as a `1`.
///
/// PASSES EITHER WAY BY DESIGN — before WI-1023 these carriers switched dedup off
/// wholesale, which also yields 2. It is a guard on the losing direction, not a
/// measurement of the change; its value is that it can only ever go red.
#[test]
fn two_genuinely_different_bindings_are_two_answers() {
    type MintPair = fn(&mut KnowledgeBase) -> (Value, Value);
    let rows: Vec<(&str, MintPair)> = vec![
        ("Int", |_| (Value::Int(1), Value::Int(2))),
        ("Bool", |_| (Value::Bool(true), Value::Bool(false))),
        ("Str", |_| (Value::Str("a".into()), Value::Str("b".into()))),
        ("Float", |_| (Value::Float(1.0), Value::Float(2.0))),
        ("BigInt", |_| {
            (
                Value::BigInt(num_bigint::BigInt::from(1)),
                Value::BigInt(num_bigint::BigInt::from(2)),
            )
        }),
        ("SymbolRef", |kb| {
            (
                Value::SymbolRef(kb.intern("wi1023_c")),
                Value::SymbolRef(kb.intern("wi1023_d")),
            )
        }),
        ("Var", |kb| {
            let n = kb.intern("wi1023_r");
            (
                Value::Var(Var::Rigid(kb.fresh_var(n))),
                Value::Var(Var::Rigid(kb.fresh_var(n))),
            )
        }),
        ("Entity", |kb| {
            let c = kb.intern("wi1023_e");
            (entity_of(c, Value::Int(1)), entity_of(c, Value::Int(2)))
        }),
        ("Tuple", |_| {
            (tuple_of(Value::Int(1)), tuple_of(Value::Int(2)))
        }),
    ];
    let got: Vec<(&str, usize)> = rows
        .into_iter()
        .map(|(name, mint)| {
            let n = solutions_for(move |kb| {
                let (a, b) = mint(kb);
                vec![a, b]
            });
            (name, n)
        })
        .collect();
    expect_all(got, 2, "two answers must stay two; collapsed");
}

/// The **transitive** guard, and the ONLY test that drives it: a structural
/// carrier holding an OPAQUE child. `Value::Tuple{pos: [Closure]}` heads as
/// `Functor{None, 1, 0}` — so the σ-wide shallow scan sees a shape and lets it
/// through — while its key is `[Open(None,1,0), Opaque]` for BOTH closures. Two
/// genuinely distinct answers, one key.
///
/// The old by-carrier list covered this by accident, by excluding every compound
/// non-`Node` carrier outright; widening the shallow test to "presents a shape"
/// removes that accident, and `TermView::bears_opaque` recursing is what replaces
/// it.
///
/// CONTROL, RE-MEASURED under WI-FFPGD, AND THE ORIGINAL CLAIM WAS WRONG. It read
/// "deleting the `if !key.is_opaque_free() { return false }` arm: 1 solution where
/// 2 is right", crediting the KEY-side guard. Dropping that guard changes NOTHING
/// here — measured — because the tuple lands in the head var, so it is in σ, and
/// the σ-wide scan stops dedup first. The claim was true of a SHALLOW σ scan and
/// went stale when `bears_opaque` became transitive; it named the wrong guard from
/// then on. What this test actually measures is the σ-wide scan's TRANSITIVITY,
/// same as [`an_opaque_nested_under_a_local_var_disables_dedup`] — deleting the σ
/// scan reports 1, and so does making it shallow (`v.head(kb)` matched against
/// `ViewHead::Opaque`).
///
/// THE KEY-SIDE GUARD HAS NO WITNESS IN THE WORKSPACE, stated rather than credited
/// to this test: dropping `key.iter().all(GoalKey::is_opaque_free)` from
/// `is_duplicate_answer` reddens not one test in the crate. Its domain is real but
/// unreached — an `Opaque` the key picks up from the GOAL with nothing in σ to
/// scan, which since WI-FFPGD means a query goal that is an occurrence region
/// `occ_head` declines to decompose (any var inside it keys as one `Opaque`, so two
/// answers binding that var differently collapse), or a duplicate-label goal, whose
/// repeated key `fingerprint_into` marks `Opaque` for the same reason. Neither has
/// a producer a test can currently build. The guard stays — it fails OPEN, and
/// deleting an unwitnessed guard in the answer-DROPPING direction is the trade
/// WI-1023's header warns about.
#[test]
fn an_opaque_child_inside_a_structural_carrier_disables_dedup() {
    let interp = crate::common::interp_for("namespace test.wi1023_op\nend\n");
    let (a, b) = (
        tuple_of(opaque_value(&interp, 1)),
        tuple_of(opaque_value(&interp, 2)),
    );
    let n = solutions_for(move |kb| {
        // PREMISE, asserted: the CHILD is opaque and the PARENT is not. If the
        // parent headed `Opaque` the σ-wide scan would already stop dedup and this
        // would be the other test; if the child did not, there would be nothing to
        // guard. `Cell` needs no KB, so the two carriers cross KBs safely here —
        // unlike a `Symbol`/`TermId`, an arena handle names the same slot anywhere.
        assert!(
            matches!(a.head(kb), ViewHead::Functor { functor: None, .. }),
            "premise: a Tuple presents a shape to the shallow scan",
        );
        let Value::Tuple { pos, .. } = &a else {
            unreachable!()
        };
        assert!(
            matches!(pos[0].head(kb), ViewHead::Opaque),
            "premise: the child presents none"
        );
        vec![a, b]
    });
    assert_eq!(
        n, 2,
        "an opaque child makes the key non-injective — dedup must stand down"
    );
}

/// The two guards' domains INTERSECT, and the intersection is the case that
/// makes the σ scan transitive rather than a head test: an opaque nested inside a
/// structural carrier, bound to a rule-LOCAL var the goal never mentions.
///
/// A shallow σ scan passes it (`Value::Tuple` heads `Functor{None,1,0}`) and the
/// key never sees it (not goal-reachable), so BOTH guards would wave it through
/// and the second answer would be dropped. This is a hole the WI-1023 widening
/// INTRODUCED — the list it replaced excluded `Tuple` wholesale — and it is why
/// `TermView::bears_opaque` recurses instead of reading one head.
///
/// CONTROL, MEASURED by making the σ scan shallow again (`v.head(kb)` matched
/// against `ViewHead::Opaque`): 1 solution where 2 is right.
#[test]
fn an_opaque_nested_under_a_local_var_disables_dedup() {
    let interp = crate::common::interp_for("namespace test.wi1023_nested\nend\n");
    let (c1, c2) = (opaque_value(&interp, 1), opaque_value(&interp, 2));
    let n = solutions_for_rows(move |_| {
        vec![
            vec![tuple_of(c1), Value::Int(1)],
            vec![tuple_of(c2), Value::Int(1)],
        ]
    });
    assert_eq!(n, 2, "an opaque under a local var is still an external row");
}

/// The **σ-wide** guard's own domain, the half a key-side check cannot reach: an
/// opaque binding on a rule-LOCAL var the goal never mentions. Both alternatives
/// project to the same `wi1023_p(1)`, so the fingerprint is identical and
/// `is_opaque_free` answers `true` — the key has no idea the two solutions differ.
///
/// This is proposal 026.1 §"Lineage-preserving bindings"' external row, and the
/// reason WI-1023 kept the scan over ALL of σ rather than replacing it with the
/// key-side guard alone.
///
/// CONTROL, MEASURED by deleting the σ scan (leaving the key-side guard, which
/// cannot see this): 1 solution where 2 is right — the second answer,
/// distinguished only by a binding outside the goal, is DROPPED.
#[test]
fn an_opaque_binding_outside_the_goal_disables_dedup() {
    let interp = crate::common::interp_for("namespace test.wi1023_ext\nend\n");
    let (c1, c2) = (opaque_value(&interp, 1), opaque_value(&interp, 2));
    let n = solutions_for_rows(move |_| vec![vec![c1, Value::Int(1)], vec![c2, Value::Int(1)]]);
    assert_eq!(
        n, 2,
        "two external rows, one projection — the rows are the answers"
    );
}

// ── (B) `fn_value` — one logical fact, one stored fact, per leaf carrier ─────

/// `f(<leaf>)` is ONE fact whichever carrier the leaf child arrives on.
///
/// `assert_fact_carrier` routes through `fn_value`, whose all-leaf test decides
/// the head carrier: a `Value::Entity` head keys `value_fact_dedup` (a `GoalKey`)
/// and a `Value::Term` head keys `fact_dedup` (a `TermId`), and the two key spaces
/// are DISJOINT (WI-815). WI-1016 closed that for `SymbolRef`; the same argument
/// applies verbatim to every other leaf `alloc_from_value` lowers, and the
/// hand-written `Value::Term | SymbolRef` list admitted none of them.
///
/// CONTROL, MEASURED by restoring that list: six of the seven rows report two
/// different `RuleId`s and a `Value::Entity` head — `Int`, `Bool`, `Str`, `Float`,
/// `BigInt`, `Var`. `SymbolRef` passes EITHER WAY BY DESIGN (WI-1016 admitted it),
/// and is kept as the pinned precedent.
///
/// THE CORPUS POPULATION IS ZERO — instrumenting `fn_value` across the whole
/// workspace recorded not one re-routed child, from either caller
/// (`assert_fact_carrier`'s four callers all pass `Value::term(..)`, and no σ in
/// the suite binds a scalar under a reified `Term::Fn`). Per WI-815, a count over
/// an empty population cannot see a wrong key, so this is a driven control, not a
/// measurement of the corpus.
#[test]
fn a_leaf_child_stores_one_fact_whichever_carrier_it_rides() {
    let mut kb = KnowledgeBase::new();
    let f = kb.intern("wi1023_f");
    let domain = kb.intern("test");
    let payload = kb.intern("wi1023_payload");
    let vid = kb.fresh_var(payload);
    // Every leaf `alloc_from_value` lowers, scalar and non-scalar alike. The term
    // twin is built BY that same function, so the pair is by construction the two
    // spellings of one child and not two hand-written shapes that could differ.
    let rows: Vec<(&str, Value)> = vec![
        ("Int", Value::Int(7)),
        ("Bool", Value::Bool(true)),
        ("Str", Value::Str("k".into())),
        ("Float", Value::Float(1.5)),
        ("BigInt", Value::BigInt(num_bigint::BigInt::from(9))),
        ("SymbolRef", Value::SymbolRef(payload)),
        ("Var", Value::Var(Var::Rigid(vid))),
    ];
    // COLLECTED for the same reason as the (A) tables: a per-row `assert_eq!`
    // would name only the first carrier when the change is backed out.
    let bad: Vec<&str> = rows
        .into_iter()
        .filter(|(name, carrier)| {
            let twin = Value::term(
                kb.alloc_from_value(carrier)
                    .unwrap_or_else(|e| panic!("{name}: {e:?}")),
            );
            let via_carrier = kb.assert_fact_carrier(
                f,
                vec![carrier.clone()],
                vec![],
                ClauseKind::Fact,
                domain,
                None,
            );
            let via_term =
                kb.assert_fact_carrier(f, vec![twin], vec![], ClauseKind::Fact, domain, None);
            via_carrier != via_term
                || !matches!(kb.rule_head_value(via_carrier), Value::Term { .. })
        })
        .map(|(name, _)| name)
        .collect();
    assert!(
        bad.is_empty(),
        "one logical fact, one RuleId on the hash-consed carrier; split for {bad:?}",
    );
}

/// Where the leaf set STOPS, asserted so a later widening has to face it: a
/// `Value::Entity` child keeps the whole application on the value-fact carrier.
///
/// It lowers, and losslessly — but to an APPLICATION, not a leaf, and admitting
/// it would make `fn_value`'s `Err` reachable (`OverArityConstructor`), demoting
/// a broken-invariant panic to a real failure mode.
///
/// PASSES EITHER WAY BY DESIGN against the WI-1023 widening (the old list
/// excluded `Entity` too); it goes red only if someone widens the predicate
/// past leaves.
#[test]
fn a_compound_child_still_takes_the_value_fact_carrier() {
    let mut kb = KnowledgeBase::new();
    let f = kb.intern("wi1023_g");
    let c = kb.intern("wi1023_c");
    let domain = kb.intern("test");
    let rid = kb.assert_fact_carrier(
        f,
        vec![entity_of(c, Value::Int(1))],
        vec![],
        ClauseKind::Fact,
        domain,
        None,
    );
    assert!(
        matches!(kb.rule_head_value(rid), Value::Entity { .. }),
        "an Entity child is not a leaf — the head stays a value fact",
    );
}

// ── helpers ─────────────────────────────────────────────────────────────────

/// A value that presents NO shape — a `Cell` arena handle. Distinct calls give
/// distinct cells, which `opaque_carrier_eq` never reports equal, so two of them
/// are two genuinely different answers with one `StructToken::Opaque` key.
fn opaque_value(interp: &anthill_core::eval::Interpreter, seed: i64) -> Value {
    Value::Cell(interp.alloc_cell(Value::Int(seed)))
}

fn entity_of(functor: Symbol, child: Value) -> Value {
    Value::Entity {
        functor,
        pos: Rc::from(vec![child]),
        named: Rc::from(Vec::<(Symbol, Value)>::new()),
    }
}

fn tuple_of(child: Value) -> Value {
    Value::Tuple {
        pos: Rc::from(vec![child]),
        named: Rc::from(Vec::<(Symbol, Value)>::new()),
    }
}
