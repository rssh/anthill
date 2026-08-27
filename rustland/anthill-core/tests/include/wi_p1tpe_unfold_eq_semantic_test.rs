//! WI-20260827-P1TPE — THE WI-580 UNFOLD COMPARED STRUCTURALLY WHERE THE GOAL IS
//! SEMANTIC, so a case-split over a carrier with a declared `Eq` DROPPED REAL SOLUTIONS.
//!
//! `unfold_eq_operand` expands a `SemEq` goal whose operand is an unground bodied
//! op-call into one continuation per `match` arm, and each arm asserts
//! `unify(residualᵢ, OTHER)`. `unify` is structural by construction (proposal 049's
//! Invariant, stated at `builtin_unify`: "carrier-agnostic and structural-only — it
//! never dispatches"), while the goal being expanded is `eq`, which DISPATCHES to the
//! carrier's declared equality (kernel-language.md §8.3). Where the two disagree the arm
//! FAILS, and when every arm does the goal is DECIDED FALSE — not a lost answer but a
//! definite refutation, which NAF concludes from.
//!
//! THE FIX declines the unfold when an arm's RESIDUAL reaches a carrier whose `eq` is
//! not structural AND the OTHER operand reaches one too — the SAME two predicates
//! `sem_eq_values` asks of an `eq` operand before it will commit to a structural verdict:
//! `value_reaches_eq_override` (a declared override, outcomes 4/5) and
//! `value_reaches_partial_carrier` (WI-664's unshielded `Float`, asked one step earlier).
//! Both legs are needed and each has a driven row: the override leg drops solutions, the
//! Float leg PROVES a falsehood.
//!
//! BOTH HALVES ARE LOAD-BEARING and each was driven. The RESIDUAL half is what OTHER's
//! structure and the declared RETURN TYPE could not see (below). The OTHER half is what
//! keeps the GENERATOR shape working: `C.pick(?c) = ?v` and `C.fpick(?c) = wrap(v: ?v)`
//! enumerate 2 DEFINITE answers because `unify` BINDS a flex operand rather than
//! comparing it, and a residual-only key took both to a suspension. `unify` can only
//! wrongly refute where BOTH sides are concrete.
//!
//! WHAT THIS DOES NOT REACH, said here because WI-20260827-XBHX3 depends on it: an OTHER
//! that is an UN-REDUCED CALL reduces to a value neither half can see, so `w` below is
//! invisible to this decline. It is sound today only because the neighbouring
//! `value_has_bodied_op_call` gate declines it first, for a reason that has nothing to do
//! with equality — and it goes (0, 0) the moment that gate is neutralized. XBHX3 must add
//! an "OTHER still carries an unevaluated computation" test to this decline when it
//! removes that gate; `the_masked_row_still_rests_on_its_neighbour` is the row that
//! measures it. A disjunct on that same predicate was written HERE and removed: the gate
//! shadows it completely, so it was unreachable and untestable.
//!
//! THE TWO KEYS THAT WERE PROTOTYPED FIRST AND EACH LEFT THE DEFECT LIVE:
//!   * OTHER's structure — `C.mk(red())`'s head is `mk`, and `AE` occurs nowhere in it,
//!     so `w` below stayed (0, 0) under it;
//!   * the operation's declared RETURN TYPE — it has no children beyond its own
//!     bindings, so `-> Wrap` over a `wrap(v: AE)` entity reaches nothing (`fld` stayed
//!     (0, 0)) — and it also DECLINED MORE than it had to, costing `cost` below.
//!
//! WHY READING STRUCTURE IS SOUND ON THE RESIDUAL SIDE, where it is not on OTHER's:
//! `anf_flatten` has already hoisted every op-call out of the residual into its own `eq`
//! goal, decided SEMANTICALLY, and `unify_values` returns `Delay` on any un-reduced call
//! it still meets. A carrier this scan cannot see can therefore only make the goal
//! SUSPEND, never wrongly refute.
//!
//! WHY THE `tag` FIELD IS THE POINT, AND WHY A TIDIER FIXTURE MEASURES NOTHING.
//! `AE`'s declared `eq` reads field `k` and IGNORES field `tag`, so `ae(k: 1, tag: 8)`
//! and `ae(k: 1, tag: 9)` are declared-EQUAL and structurally DIFFERENT. On a carrier
//! whose values agree structurally the two relations are the SAME relation: every arm
//! answers identically with the decline and without it, and this whole file would be
//! green either way for a reason unrelated to the question. The operands must also be
//! DISTINCT — `sem_eq_values` answers reflexivity BEFORE any dispatch, so structurally
//! identical operands never consult the carrier's `eq` at all. `C.mk` returns
//! `ae(k: …, tag: 9)` for the same reason: an earlier draft delegated to `C.pick`, which
//! made its reduced value structurally EQUAL to the matching arm's, and the `w` row was
//! then green in every state.
//!
//! THE FOUR STATES, MEASURED. This site's decline is the `value_reaches_eq_override` on
//! `result_occ`; its neighbour is `value_has_bodied_op_call`, which WI-20260827-XBHX3
//! removes.
//!
//! ```text
//!                 neighbour ON     neighbour ON    neighbour OFF    neighbour OFF
//!                 this OFF         this ON         this ON          this OFF
//!                 (today)          (THIS CHANGE)   (after XBHX3)    (XBHX3 alone)
//!   wd            (0, 0) WRONG     (1, 0)          (1, 0)           (0, 0) WRONG
//!   wd0 wd0Naf    (0,0) (1,1) WRONG  (1,0) (1,0)   (1,0) (1,0)      (0,0) (1,1) WRONG
//!   bur           (0, 0) WRONG     (1, 0)          (1, 0)           (0, 0) WRONG
//!   fld           (0, 0) WRONG     (1, 0)          (1, 0)           (0, 0) WRONG
//!   w             (1, 0)           (1, 0)          (0, 0) WRONG     (0, 0) WRONG
//!                 — NOT reached by this decline; the neighbour is what declines it
//!   bodyNest      (1, 0)           (1, 0)          (1, 1) ?c = red  (1, 1) ?c = red
//!   nanr          (1, 1) WRONG     (1, 0)          (1, 0)           (1, 1) WRONG
//!   genp          (1, 1)           (1, 0)          (1, 0)           (1, 1)
//!   fok           (1, 1)           (1, 0)          (1, 0)           (1, 1)
//!                 — THE TWO COSTS: `genp`'s (1,1) was 1 of 2 solutions, `fok`'s was a
//!                   Float compare where structural and IEEE happen to agree
//!   nanrg fokg fgen  (0, 0) (1, 1) (2, 2) — unmoved in all four
//!   gen genw genb (2, 2) each      — unmoved in all four
//!   cost costg    (1, 1) each      — unmoved in all four
//!   g wg burg     (1, 1) (1, 1) (1, 0)   — unmoved in all four
//!   fldg plain tagr  (1, 0) (1, 1) (1, 1) — unmoved in all four
//! ```
//!
//! Read the two right-hand columns together: `bodyNest` is the answer XBHX3 measured the
//! neighbour COSTING and this key does not take it back, while `w` is the row XBHX3 still
//! owes a clause for.
//!
//! ONE SHAPE THAT LOOKS LIKE THIS DEFECT AND IS NOT, so the next reader does not read it
//! as a miss of this key: an arm residual that puts a PARAMETER UNDER A CONSTRUCTOR —
//! `case red() -> some(x)` — answers (0, 0) in all four states, and so does its `Int64`
//! twin, where no carrier overrides anything. The cause is a positional constructor
//! argument in an operation body building a value nothing matches; it refutes even the
//! GROUND call, with no unfold and no `eq` override involved. WI-20260827-T2470 owns it,
//! with the isolated five-row fixture.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// `(total, definite)`. Both halves are needed and every claim here turns on telling
/// them apart: a SUSPENSION is `total > 0, definite 0`, a DECIDED-FALSE is `total 0`,
/// and this ticket is precisely about the second appearing where the first is correct.
fn counts(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize) {
    let goal = crate::common::query_pattern_term(kb, pattern);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let def = sols.iter().filter(|s| s.is_definite()).count();
    (sols.len(), def)
}

/// The head symbol names of a unary predicate's DEFINITE answers, in order — so a test
/// asserting that a case-split still decides can name the value, not only the count.
fn definite_names(kb: &mut KnowledgeBase, qn: &str) -> Vec<String> {
    crate::common::query_unary(kb, qn)
        .into_iter()
        .filter(|(_, d)| *d)
        .map(|(v, _)| match kb.value_head_symbol(&v) {
            Some(s) => kb.local_name_of(s).to_string(),
            None => format!("{v:?}"),
        })
        .collect()
}

/// `AE` declares an `eq` that compares field `k` and IGNORES field `tag` — the whole
/// point of the fixture (see the module doc). `Box` is its CONTROL carrier: same shape,
/// no `eq` member, so structural equality IS its instance. `Wrap` reaches `AE` through a
/// nominal FIELD, `Option[T = AE]` through a type BINDING — the two ways an override is
/// buried, and the residual scan must find both.
///
/// `C.bpick` / `C.tag` return no `AE` at all and are declared in the SAME sort as
/// `C.pick`, so a key that fired on the owning sort, or on "this KB has an override
/// somewhere", would take them down too.
const SRC: &str = r#"
namespace p1tpe
  import anthill.prelude.{Int64, Bool, Eq, PartialEq, Option, Float}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Float.{nan}
  sort AE
    entity ae(k: Int64, tag: Int64)
    operation aeq(a: AE, b: AE) -> Bool = eq(a.k, b.k)
    provides PartialEq[T = AE, eq = aeq]
    provides Eq[T = AE]
  end
  sort Box
    entity box(v: Int64)
  end
  sort Wrap
    entity wrap(v: AE)
  end
  -- WI-664's carrier: `Float` is the OTHER way a structural verdict is the wrong
  -- relation, and it fails in the opposite direction — a definite PROOF
  sort P
    entity p(f: Float)
  end
  sort C
    entity red
    entity green
    operation pick(c: C) -> AE =
      match c
        case red() -> ae(k: 1, tag: 8)
        case green() -> ae(k: 2, tag: 0)
    -- `tag: 9` deliberately DISAGREES with every arm of `pick` while `k` agrees with
    -- one: `mk(red())` is declared-equal to `pick(red())` and structurally different.
    operation mk(c: C) -> AE = ae(k: C.tag(c), tag: 9)
    -- the override one TYPE BINDING down
    operation opick(c: C) -> Option[T = AE] =
      match c
        case red() -> some(ae(k: 1, tag: 8))
        case green() -> none
    -- the override one NOMINAL FIELD down: `Wrap` itself overrides nothing
    operation fpick(c: C) -> Wrap =
      match c
        case red() -> wrap(v: ae(k: 1, tag: 8))
        case green() -> wrap(v: ae(k: 2, tag: 0))
    operation bpick(c: C) -> Box =
      match c
        case red() -> box(v: 1)
        case green() -> box(v: 2)
    operation tag(c: C) -> Int64 =
      match c
        case red() -> 1
        case green() -> 2
    -- arm bodies are the op's own PARAMETERS, so each arm's residual ANF-hoists to a
    -- bare var + its own `eq` goal: the deciding compare is already SEMANTIC and this
    -- key must NOT decline it. See `a_residual_that_hoists_its_call_still_decides`.
    operation fnan(c: C) -> P =
      match c
        case red() -> p(f: nan)
        case green() -> p(f: 1.5)
    operation fplain(c: C) -> P =
      match c
        case red() -> p(f: 2.5)
        case green() -> p(f: 1.5)
    operation cpick(c: C, x: AE, y: AE) -> AE =
      match c
        case red() -> x
        case green() -> y
  end
  rule wd(?c)       :- C.pick(?c) = ae(k: 1, tag: 9)
  rule g(1)         :- C.pick(red()) = ae(k: 1, tag: 9)
  rule wdNaf(1)     :- not(C.pick(?c) = ae(k: 1, tag: 9))
  rule wd0()        :- C.pick(?c) = ae(k: 1, tag: 9)
  rule wd0Naf(1)    :- not(wd0())
  rule bur(?c)      :- C.opick(?c) = some(ae(k: 1, tag: 9))
  rule burg(1)      :- C.opick(red()) = some(ae(k: 1, tag: 9))
  rule fld(?c)      :- C.fpick(?c) = wrap(v: ae(k: 1, tag: 9))
  rule fldg(1)      :- C.fpick(red()) = wrap(v: ae(k: 1, tag: 9))
  rule w(?c)        :- C.pick(?c) = C.mk(red())
  rule wg(1)        :- C.pick(red()) = C.mk(red())
  rule plain(?c)    :- C.bpick(?c) = box(v: 1)
  rule tagr(?c)     :- C.tag(?c) = 1
  rule bodyNest(?c) :- C.bpick(?c) = box(v: C.tag(red()))
  rule gen(?c, ?v)  :- C.pick(?c) = ?v
  rule genw(?c, ?v) :- C.fpick(?c) = wrap(v: ?v)
  rule genp(?c, ?k) :- C.pick(?c) = ae(k: ?k, tag: 8)
  rule genb(?c, ?v) :- C.bpick(?c) = ?v
  rule genpRed()    :- C.pick(red()) = ae(k: 1, tag: 8)
  rule genpGreen()  :- C.pick(green()) = ae(k: 2, tag: 8)
  rule nanr(?c)     :- C.fnan(?c) = p(f: nan)
  rule nanrg(1)     :- C.fnan(red()) = p(f: nan)
  rule fok(?c)      :- C.fplain(?c) = p(f: 2.5)
  rule fokg(1)      :- C.fplain(red()) = p(f: 2.5)
  rule fgen(?c, ?v) :- C.fplain(?c) = ?v
  rule cost(?c)     :- C.cpick(?c, ae(k: 1, tag: 8), ae(k: 2, tag: 0)) = ae(k: 1, tag: 9)
  rule costg(1)     :- C.cpick(red(), ae(k: 1, tag: 8), ae(k: 2, tag: 0)) = ae(k: 1, tag: 9)
end
"#;

/// THE HEADLINE ROW, with NO call anywhere in the equation.
///
/// `C.pick(?c) = ae(k: 1, tag: 9)` case-split into `unify(ae(k: 1, tag: 8), ae(k: 1,
/// tag: 9))` and `unify(ae(k: 2, tag: 0), …)`. Both fail STRUCTURALLY; under the declared
/// `eq` the first HOLDS (same `k`). Every arm gone ⇒ the goal was decided FALSE.
///
/// `g` is the whole argument, asserted beside it: the SAME equation with the scrutinee
/// GROUND takes the declared-`Eq` path and answers 1 DEFINITE. So `?c = red` IS a
/// solution and `wd` at 0 total was dropping it.
///
/// BACK OUT the residual decline and this test goes RED at `wd`: (1, 0) → (0, 0). `g`
/// passes either way, by design — it never reaches the unfold.
#[test]
fn a_case_split_over_a_custom_eq_carrier_no_longer_decides_false() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "p1tpe.g(1)"),
        (1, 1),
        "CONTROL, and the reason the row below is a DROPPED solution rather than an \
         absent one: ground, the same equation dispatches to `aeq`, which compares only \
         `k`, and answers DEFINITELY. Unmoved by this change"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.wd(?c)"),
        (1, 0),
        "the unground twin must NOT decide. Back the decline out and this is (0, 0) — a \
         definite refutation of an equation the row above proves has a witness"
    );
    assert!(
        definite_names(&mut kb, "p1tpe.wd").is_empty(),
        "a suspension asserts nothing about `?c`; the guard against an arm committing"
    );
}

/// THE POLARITY THAT MAKES IT UNSOUND RATHER THAN MERELY INCOMPLETE — and the spelling
/// that reaches it, which is not the obvious one.
///
/// `not(C.pick(?c) = ae(k: 1, tag: 9))` written DIRECTLY is (1, 0) in all four states:
/// its inner goal has a free `?c`, so NAF flounders before the unfold's verdict can
/// matter. It measures nothing and is asserted below only so the next reader does not
/// take its greenness for coverage.
///
/// The refutation reaches NAF through a NULLARY wrapper instead: `wd0()` keeps `?c`
/// local, so `not(wd0())` is a ground NAF goal over a predicate the unfold had decided
/// FALSE. MEASURED: (1, 1) with the decline backed out — `not` PROVED, definitely, from
/// an empty search over a goal that has a witness — and (1, 0) with it. THIS TEST GOES
/// RED on a back-out.
#[test]
fn naf_over_the_refutation_no_longer_proves_a_falsehood() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "p1tpe.wd0()"),
        (1, 0),
        "the nullary wrapper suspends. (0, 0) with the decline backed out"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.wd0Naf(1)"),
        (1, 0),
        "so NAF over it suspends too. (1, 1) with the decline backed out — a DEFINITE \
         `not`, which is the unsoundness rather than an incompleteness"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.wdNaf(1)"),
        (1, 0),
        "and the DIRECT NAF spelling measures nothing: free `?c` in the inner goal makes \
         NAF flounder, so this row is (1, 0) in all four states"
    );
}

/// THE OVERRIDE BURIED UNDER STRUCTURE, reached BOTH ways — and the pair of rows that
/// chose the residual over the declared return type.
///
/// `C.opick` returns `Option[T = AE]`: `Option` overrides nothing, `AE` does, one TYPE
/// BINDING down. `C.fpick` returns `Wrap`, a `wrap(v: AE)` entity: same override, one
/// NOMINAL FIELD down. Both are the WI-573/WI-616 "buried override" shape, which
/// `sem_eq_values` SUSPENDS on rather than deciding structurally (outcome 5); the unfold
/// was deciding both FALSE.
///
/// A RETURN-TYPE KEY FINDS THE FIRST AND NOT THE SECOND — a declared `Wrap` has no
/// children, so nothing in the type mentions `AE` — and that asymmetry is why the
/// delivered key reads the RESIDUAL, which carries the actual `wrap(v: ae(…))` value.
///
/// Both ground twins SUSPEND rather than answering (a buried override is delayed, not
/// dispatched), so the claim for each unground row is "not decided false", exactly what
/// the ground reading of the same equation is willing to say.
///
/// BACK OUT the decline and this goes RED at BOTH `bur` and `fld`: (1, 0) → (0, 0). The
/// two `…g` rows are (1, 0) either way.
#[test]
fn an_override_buried_under_structure_declines_both_ways_down() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "p1tpe.burg(1)"),
        (1, 0),
        "the ground twin SUSPENDS. So the strongest sound answer for the unground row is \
         a suspension too, never a refutation. Unmoved by this change"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.bur(?c)"),
        (1, 0),
        "override one TYPE BINDING down. Back the decline out and this is (0, 0)"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.fldg(1)"),
        (1, 0),
        "the same, for the nominal-field carrier: the ground twin suspends"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.fld(?c)"),
        (1, 0),
        "override one NOMINAL FIELD down. Back the decline out and this is (0, 0) — and \
         this is the row a return-type key could not see, since `Wrap` has no children"
    );
}

/// THE CONTROL THAT BOUNDS THE KEY: a case-split over a carrier with NO custom `eq`
/// still decides, in the same KB and the same sort where an overriding carrier exists.
///
/// This is what separates the delivered key from the ticket's direction (c) — "decline
/// the unfold entirely for a carrier with a declared `Eq`" — and from any key reading
/// `has_eq_dispatch_entries()`: both would take these two rows down with them. `bpick`
/// returns `Box`, whose structural equality IS its instance; `tag` returns `Int64` and is
/// declared beside `pick`, so a key reading the OWNING SORT would decline it.
///
/// BOTH PASS WITH THE DECLINE BACKED OUT, by design — they exist to show the change
/// costs nothing, so they must be green on both sides.
#[test]
fn a_carrier_with_no_custom_eq_still_case_splits() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        (
            counts(&mut kb, "p1tpe.plain(?c)"),
            definite_names(&mut kb, "p1tpe.plain")
        ),
        ((1, 1), vec!["red".to_string()]),
        "a `Box`-returning case-split still answers DEFINITELY, and answers `red` — \
         asserted on the VALUE, since a count alone would also pass if the unfold \
         started answering `green`"
    );
    assert_eq!(
        (
            counts(&mut kb, "p1tpe.tagr(?c)"),
            definite_names(&mut kb, "p1tpe.tagr")
        ),
        ((1, 1), vec!["red".to_string()]),
        "…and so does an `Int64`-returning one declared in the same sort as `pick`: the \
         key reads the RESIDUAL, not the owning sort and not whether the KB has any \
         override at all"
    );
}

/// THE GENERATOR SHAPE, and the reason the decline asks about OTHER as well as the
/// residual.
///
/// `C.pick(?c) = ?v` and `C.fpick(?c) = wrap(v: ?v)` use a case-splitting operation to
/// ENUMERATE: each arm's `unify(residualᵢ, OTHER)` meets a flex var, which BINDS rather
/// than comparing, so both arms succeed and the answer set is 2 DEFINITE and COMPLETE.
/// `unify` can only wrongly refute where BOTH sides are concrete, so there is nothing
/// here for the structural/semantic disagreement to bite on.
///
/// AN INTERMEDIATE VERSION OF THIS CHANGE — keyed on the residual ALONE — took both rows
/// to (1, 0), and /code-review caught it. That is why the decline's second half asks
/// whether OTHER can meet the override with something concrete. `genb` is the `Box`
/// control: no override anywhere, (2, 2) throughout, so it cannot distinguish the two
/// versions and is not evidence on its own.
///
/// ALL THREE PASS WITH THE DECLINE BACKED OUT, by design — they are here to show the
/// delivered key costs these rows nothing.
#[test]
fn a_generator_over_an_overriding_carrier_still_enumerates() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "p1tpe.gen(?c, ?v)"),
        (2, 2),
        "`C.pick(?c) = ?v` still enumerates BOTH arms definitely: OTHER is a flex var, so          each arm's `unify` binds it. A residual-only key made this (1, 0)"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.genw(?c, ?v)"),
        (2, 2),
        "…and so does a generator whose flex var sits UNDER a constructor: `wrap` matches          `wrap` structurally, which is sound (`Wrap` overrides nothing), and the `AE`          position meets `?v`. A residual-only key made this (1, 0) too"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.genb(?c, ?v)"),
        (2, 2),
        "CONTROL with no override anywhere — green under every version of this change,          so it measures nothing by itself and is asserted to say so"
    );
}

/// THE ONE ANSWER THIS DECLINE COSTS — and what that answer was worth.
///
/// `C.pick(?c) = ae(k: ?k, tag: 8)` is declined: OTHER is concrete at the `AE` position
/// (its head IS `ae`), so this is the shape where structural and semantic equality can
/// disagree, and they do. Before the decline it answered 1 DEFINITE, `?c = red, ?k = 1`.
///
/// THAT ANSWER SET WAS INCOMPLETE, WHICH IS THE POINT: `?c = green, ?k = 2` is a solution
/// too — asserted below on its ground twin, because `pick(green())` is `ae(k: 2, tag: 0)`
/// and `aeq` compares only `k`. The structural `unify` dropped it on `tag` 0 vs 8. So the
/// trade is a DEFINITE set that silently omits half its solutions (which NAF concludes
/// from) for a suspension that omits nothing.
///
/// BACK OUT the decline and `genp` returns to (1, 1). Both ground twins are 1 DEFINITE
/// either way.
#[test]
fn the_one_answer_the_decline_costs_was_half_an_answer_set() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "p1tpe.genpRed()"),
        (1, 1),
        "ground twin 1: `?c = red, ?k = 1` holds"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.genpGreen()"),
        (1, 1),
        "ground twin 2: `?c = green, ?k = 2` holds too — `aeq` ignores `tag`. THIS is the          solution the pre-change (1, 1) was missing"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.genp(?c, ?k)"),
        (1, 0),
        "so the unground row suspends rather than reporting 1 of its 2 solutions as if          that were all of them. (1, 1) with the decline backed out"
    );
}

/// AT AN OVERRIDING CARRIER AND STILL NOT DECLINED, because this residual's compare is
/// ALREADY SEMANTIC. The row that says the key is keyed on the right thing.
///
/// `C.cpick`'s arm bodies are its own PARAMETERS, so `anf_flatten` hoists each arm's
/// residual to a BARE VAR plus its own `eq` goal, and the arm's goals are
/// `[unify(?c, redᵢ), unify(?fᵢ, OTHER), eq(argᵢ, ?fᵢ)]`. The structural `unify` only
/// BINDS a fresh var; the `eq` decides, and it dispatches. So the arm answers correctly
/// and the scan — which sees a bare var and no override — lets it through.
///
/// A KEY ON THE DECLARED RETURN TYPE DECLINED THIS ROW, turning a correct 1 DEFINITE
/// `?c = red` into a suspension; the residual key does not, because the residual is a
/// bare var and reaches no override at all. MEASURED (1, 1) `?c = red` in ALL FOUR gate
/// states. Green with the decline backed out too, by design.
#[test]
fn a_residual_that_hoists_its_call_still_decides() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "p1tpe.costg(1)"),
        (1, 1),
        "the ground twin decides, as the witness that `?c = red` is the true answer"
    );
    assert_eq!(
        (
            counts(&mut kb, "p1tpe.cost(?c)"),
            definite_names(&mut kb, "p1tpe.cost")
        ),
        ((1, 1), vec!["red".to_string()]),
        "and the unground row still finds it — the value asserted, not just the count. \
         Unmoved in all four gate states"
    );
}

/// THE ROW WI-20260827-XBHX3 IS BLOCKED ON — AND THIS TICKET DOES NOT UNBLOCK IT ON ITS
/// OWN. Stated as a fact rather than as a hope, because the ticket's plan assumed it would.
///
/// `C.pick(?c) = C.mk(red())` is the same unsoundness reached through a REDUCED call.
/// `C.mk(red())` reduces to `ae(k: 1, tag: 9)`: declared-equal to arm `red`'s
/// `ae(k: 1, tag: 8)`, structurally different from it and from arm `green`'s too, so both
/// arms fail structurally. Neither half of this decline can see it: the arm's residual
/// does reach `AE`, but OTHER is an un-reduced `Expr::Apply` whose head is `mk`, and `AE`
/// occurs nowhere in it until it reduces — which happens inside `unify_values`, long
/// after this decision.
///
/// SO IT IS SOUND TODAY FOR THE NEIGHBOUR'S REASON, NOT FOR THIS ONE.
/// `unfold_eq_operand` also declines whenever OTHER carries a bodied op-call
/// (`value_has_bodied_op_call`), and `C.mk(red())` is one. MEASURED with that gate
/// neutralized — the state XBHX3 will land: `w` is (0, 0), DECIDED FALSE, while `wg`
/// stays 1 DEFINITE as the witness that `?c = red` exists. THIS IS THE ROW XBHX3 MUST
/// MEASURE ITS REPLACEMENT WITH.
///
/// A DISJUNCT FOR IT WAS WRITTEN HERE AND REMOVED. Adding
/// `|| value_has_bodied_op_call(&other)` to the decline's OTHER half makes `w` safe on
/// paper, and /code-review showed the clause is UNREACHABLE: the standalone gate above
/// declines every value that would satisfy it, proved by an assert that never fired
/// across the suite. An untestable branch whose first execution is someone else's diff is
/// worse than an honest gap, so the gap is written down instead.
///
/// AND THE ANSWER XBHX3 MEASURED THE NEIGHBOUR COSTING IS NOT COLLATERAL OF THIS KEY:
/// in that same neutralized state `bodyNest` — `C.bpick(?c) = box(v: C.tag(red()))`, a
/// `Box` with no custom `Eq` — reaches 1 DEFINITE `?c = red`. Its (1, 0) here is the
/// neighbour's doing, not this decline's.
#[test]
fn the_masked_row_still_rests_on_its_neighbour() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "p1tpe.wg(1)"),
        (1, 1),
        "CONTROL: ground, the same equation answers 1 DEFINITE, so `?c = red` is a \
         witness for the row below"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.w(?c)"),
        (1, 0),
        "a suspension — and green with THIS decline backed out too, because the \
         neighbouring gate is what declines it. Neutralize that gate and it is (0, 0): \
         see this test's doc"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.bodyNest(?c)"),
        (1, 0),
        "the neighbour still declines this one, and THIS decline does not: with the \
         neighbour neutralized it is (1, 1) `?c = red`, the answer XBHX3 keeps"
    );
}

/// THE THIRD LEG, AND IT FAILS THE OTHER WAY: an unshielded `Float` makes the per-arm
/// structural `unify` PROVE a falsehood, where the override legs above only dropped one.
///
/// `unify` reads two `nan`s as equal (`OrderedFloat` is reflexive); IEEE `eq` does not
/// (`nan != nan` — the `NonEq` witness `anthill.prelude.Float` exhibits). So the `red` arm
/// of `C.fnan(?c) = p(f: nan)` succeeded structurally and the goal was answered 1 DEFINITE
/// `?c = red` — a proof of a relation that is FALSE, which is why `nanrg`, the ground
/// twin, correctly answers 0. Same equation, opposite verdicts, decided by whether the
/// scrutinee was bound.
///
/// This is why the decline asks `value_reaches_partial_carrier` beside
/// `value_reaches_eq_override` — the two predicates `sem_eq_values` itself consults
/// before committing to a structural verdict, so the unfold and the builtin cannot
/// disagree about which values need the semantic path.
///
/// BACK OUT the decline and `nanr` goes back to (1, 1). `nanrg` is (0, 0) either way —
/// it never reaches the unfold, and it is the control that says (1, 1) was wrong rather
/// than merely different.
#[test]
fn a_float_leaf_no_longer_proves_an_equation_that_is_false() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "p1tpe.nanrg(1)"),
        (0, 0),
        "CONTROL: ground, `p(f: nan) = p(f: nan)` is REFUTED — IEEE `nan != nan`. \
         Unmoved by this change"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.nanr(?c)"),
        (1, 0),
        "so the unground twin must not PROVE it. Back the decline out and this is \
         (1, 1) `?c = red` — a definite proof of a false equation, worse than the \
         dropped solutions the override legs fix"
    );
}

/// WHAT THE FLOAT LEG COSTS, driven beside what it buys.
///
/// The leg is CARRIER-level, not value-level: it asks "does a `Float` occur here", the
/// same trigger `sem_eq_values` uses to switch to its field-wise IEEE compare. So it also
/// declines a Float compare where structural and IEEE happen to AGREE — `C.fplain(?c) =
/// p(f: 2.5)` was 1 DEFINITE `?c = red` and is now a suspension.
///
/// Taking the over-approximation is deliberate: a value-level rule ("only decline when a
/// NaN or a signed zero is present") would make the unfold and the builtin disagree about
/// which values need the semantic path, and this file's whole subject is what happens when
/// two readers of one equation use different relations.
///
/// `fgen` is the generator control — OTHER is a flex var, so no arm compares anything and
/// the leg does not fire. (2, 2) in all four states.
#[test]
fn the_float_leg_over_approximates_and_the_generator_survives_it() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "p1tpe.fokg(1)"),
        (1, 1),
        "ground twin: `2.5 = 2.5` under IEEE too, so the row below has a true answer"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.fok(?c)"),
        (1, 0),
        "…and it is now a suspension. (1, 1) `?c = red` with the decline backed out — \
         the cost of asking the carrier rather than the value"
    );
    assert_eq!(
        counts(&mut kb, "p1tpe.fgen(?c, ?v)"),
        (2, 2),
        "the generator is untouched: a flex OTHER binds, so no Float is ever compared"
    );
}
