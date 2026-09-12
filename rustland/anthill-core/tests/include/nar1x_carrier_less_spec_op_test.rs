//! WI-20260909-NAR1X — a rule clause's requirement dictionary reaches a
//! **CARRIER-LESS** spec op (`Monoid.unit()`, `Zeroable.zero()`), and the impl it
//! selects is entered with that dictionary's own subtree in its frame.
//!
//! Design: `docs/design/op-to-rule-requirement-channel.md` (crossing 3, §5.2);
//! surface: proposal 060 §1/§3; the dictionary mechanics are WI-1040's
//! (`wi1040_require_clause_dictionary_test`), which this extends in one place each.
//!
//! ## What a CARRIER-LESS spec op is, and why it has no other route
//!
//! `op_has_spec_carrier_param` asks whether an operation exposes a parameter typed
//! at the spec's carrier. `Desc.describe(x: T)` does; `Zeroable.zero() -> Int64`
//! does not, and neither does an all-content op. Every OTHER way the system picks an
//! implementation reads a carried type off a VALUE:
//!
//!  * the typer's call-site pin needs an argument whose type it knows;
//!  * `classify_unstamped_spec_op_call` (WI-1044) reads the operands at run time;
//!  * `resolve_bridge_requirements` pins the callee's `requires` chain **from the
//!    argument types and nothing else**.
//!
//! A carrier-less call has no operand to read, so all three answer nothing, and the
//! clause's own `require[X]` dictionary is the ONLY thing in the program that says
//! which instance the call means. That is why the weave is not an optimisation here:
//! it is the whole dispatch.
//!
//! ## THE TWO HALVES, AND WHAT EACH BACK-OUT FAILS — MEASURED, not reasoned
//!
//!  * **WEAVE** — `collect_covered_calls` (typing.rs) admits a carrier-less body-less
//!    spec op, so the call is rewritten to `Expr::ApplyWithin` and the clause's
//!    dictionary selects the member;
//!  * **DICT** — `WovenDispatch` (resolve.rs) carries that dictionary one hop past
//!    the member into `call_op_bridged` (eval/mod.rs), which expands it into the
//!    frame instead of pinning from argument types there are none of.
//!
//!  * **VIEW** — that dictionary is read through `Dictionary::from_view`
//!    (`eval/dictionary.rs`), carrier-neutrally, because which of the three carriers
//!    it rides depends on whether it was derived in this clause or supplied through a
//!    rule head.
//!
//! | row | WEAVE out | DICT out | VIEW out (`from_value`) |
//! |---|---|---|---|
//! | [`the_carrier_less_call_answers_the_carriers_own_number`] | FAILS — `[]` | ok | ok |
//! | [`the_carrier_less_call_at_operand_position_answers_the_same`] | FAILS — an un-reduced call term | ok | ok |
//! | [`a_polymorphic_operation_entering_a_rule_reaches_the_carrier_less_op`] | FAILS — `0` on the two rows whose truth is `1`, a WRONG answer | ok | ok |
//! | [`the_selected_impls_own_requirement_is_filled_from_the_dictionary`] | FAILS — `[]` | FAILS — a residual | ok |
//! | [`the_filled_requirement_follows_the_element_and_is_not_a_constant`] | FAILS — `[]` | FAILS — a residual | ok |
//! | [`a_dictionary_crossing_a_rule_head_is_read_on_its_own_carrier`] | FAILS — `[]` | FAILS — a residual | **FAILS — a residual** |
//! | [`the_same_clause_without_the_require_answers_nothing`] | ok | ok | ok |
//! | [`a_carrier_bearing_call_answers_the_same_number_either_way`] | ok | ok | ok |
//! | [`a_builtin_backed_spec_op_is_still_not_woven`] | ok | ok | ok |
//!
//! DICT is DOWNSTREAM of WEAVE and VIEW is downstream of DICT — nothing reaches the
//! hand-off unless the call was woven, and nothing hands over a dictionary it could
//! not read — so the lower rows fail under more than one arm, and they fail
//! DIFFERENTLY (`[]` versus a residual), which is what says these are three things
//! and not one credited three times. Only the last row separates VIEW, and it is the
//! only one whose dictionary crosses a HEAD; that is not a coincidence, it is the
//! condition that puts a dictionary on the occurrence carrier at all.
//!
//! **NO ROW OUTSIDE THIS FILE MOVES UNDER ANY OF THE THREE**, measured over
//! `wi1040_require_clause_dictionary_test` and `wi_96ztm_two_dictionaries_test`, the
//! two suites that drive this machinery — which is what says the three arms measure
//! THIS ticket rather than the requirement channel at large. (They did move once,
//! during the build: gating the member SELECTION on the whole-tree dictionary read
//! took four of their rows from `7`/`9` to a residual. The handle is optional for
//! that reason, and the reason is written at the site.)
//!
//! The last three rows pass under every arm **BY DESIGN** and each says so at its own
//! site; they are what makes the rest mean "this change" rather than "something about
//! this program".
//!
//! ## What this does NOT deliver
//!
//! The design's steps 1, 2 and 4 — a predicate's implicit-parameter SEQUENCE, the
//! rule→rule push, and the `Value::Relation` capture for a GENERATIVE citation — are
//! untouched. NAR1X's own boundary rules the generative edge out in as many words
//! ("a generative `p(?out)` from an operation body does not traverse this edge at
//! all"), and `060-typedomains-implementation.md` §5 records that edge as still
//! nobody's.
//!
//! **AND THE TICKET'S OWN DIAGNOSIS WAS WRONG ABOUT WHERE.** It says the op→rule
//! crossing "DROPS THE SLOT" — `prove_rule_predicate` taking a predicate and ground
//! args from a frame that holds `frame.requirements` — and proposes a `ResolveConfig`
//! field seeded from that frame. MEASURED before building: the rule DERIVES its own
//! dictionary locally from the ground operand (the witness/anchor path, WI-1040 +
//! WI-20260909-QMFC5), so nothing is missing at that crossing; what failed was the
//! rule→op call one goal later, whose callee no value can name. The design note
//! reaches the same verdict from the other side ("NAR1X's row is crossing 3's").
//! So there is no `ResolveConfig` field here, and the ticket's stated control —
//! "with the ResolveConfig field dropped" — is spelled as the two back-outs above.

use anthill_core::eval::Value;

// ── the fixture ─────────────────────────────────────────────────────────────

/// A spec with BOTH shapes side by side, which is what lets every row below have a
/// control drawn from the same program:
///
///  * `zero() -> Int64` — body-less and **nullary**: carrier-less, the subject;
///  * `tag(x: T) -> Int64 = 0` — defaulted and carrier-BEARING: the witness that
///    grounds the clause's `require`, and the control call that needs no dictionary.
///
/// Two carriers answering DIFFERENT numbers on both operations, so no assertion here
/// can be satisfied by the spec's default or by the other carrier's supply.
fn two_carriers(tail: &str) -> String {
    format!(
        r#"namespace test.nar1x
  import anthill.prelude.Int64

  sort Zeroable
    sort T = ?
    operation zero() -> Int64
    operation tag(x: T) -> Int64 = 0
  end

  sort Sum
    import anthill.prelude.Int64
    entity sum
    provides Zeroable[T = Sum]
    operation zero() -> Int64 = 3
    operation tag(x: Sum) -> Int64 = 1
  end

  sort Prod
    import anthill.prelude.Int64
    entity prod
    provides Zeroable[T = Prod]
    operation zero() -> Int64 = 5
    operation tag(x: Prod) -> Int64 = 2
  end

{tail}end
"#
    )
}

/// Every solution of `test.nar1x.answer(?r)`, definiteness included — the rows below
/// distinguish "no answer" from "one answer that is a residual", and collapsing the
/// two is how a delay reads as a pass.
fn answers(src: &str) -> Vec<(Value, bool)> {
    let mut kb = crate::common::load_kb_with(src);
    crate::common::query_unary(&mut kb, "test.nar1x.answer")
}

/// The single definite `Int` of `test.nar1x.answer`. Panics on anything else,
/// `[]` included.
fn answer(src: &str) -> i64 {
    match answers(src).as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("expected exactly one definite Int, got {other:?}\n{src}"),
    }
}

// ── the headline ────────────────────────────────────────────────────────────

/// THE HEADLINE. One polymorphic clause, two carriers, two numbers — and the number
/// is the carrier's own `zero()`, which nothing at the call site names.
///
/// The clause's `require[Zeroable[T]]` is grounded by the witness call
/// `Zeroable.tag(?x, ?t)` (WI-300's transitive tier), so the dictionary is `Sum`'s or
/// `Prod`'s according to what `?x` carries; `Zeroable.zero(?r)` names no carrier at
/// all and dispatches through that dictionary.
///
/// BACK-OUT: with `collect_covered_calls`' carrier-less admission removed, both rows
/// answer `[]` — the call is not woven, the goal reaches the eval bridge on the SPEC
/// op, and eval has no implementation to run.
#[test]
fn the_carrier_less_call_answers_the_carriers_own_number() {
    for (ctor, expected) in [("sum()", 3), ("prod()", 5)] {
        let src = two_carriers(&format!(
            "  rule via(?x, ?r) :- require[Zeroable[T]], Zeroable.tag(?x, ?t), \
                Zeroable.zero(?r)\n  \
             rule answer(?r) :- via({ctor}, ?r)\n"
        ));
        assert_eq!(
            answer(&src),
            expected,
            "`Zeroable.zero()` must reach {ctor}'s own implementation through the \
             clause dictionary",
        );
    }
}

/// THE CONTROL FOR THE HEADLINE, and it is a live one rather than a formality: it
/// says the DICTIONARY is what answers, not the resolver's value-directed
/// classification (WI-1044), which is what carries the equivalent carrier-BEARING
/// row below.
///
/// Delete the `require` and the identical clause answers NOTHING — because
/// value-direction reads the operands' carried types and a nullary call has none.
#[test]
fn the_same_clause_without_the_require_answers_nothing() {
    let src = two_carriers(
        "  rule via(?x, ?r) :- Zeroable.tag(?x, ?t), Zeroable.zero(?r)\n  \
           rule answer(?r) :- via(sum(), ?r)\n",
    );
    let got = answers(&src);
    assert!(
        got.is_empty(),
        "without the clause dictionary nothing can name an implementation of a \
         nullary spec op; got {got:?}",
    );
}

/// The same call at OPERAND position rather than at GOAL position — `?r <=> zero()`
/// instead of `zero(?r)`.
///
/// A separate row because the two reach `reduce_op_value` through different doors:
/// the goal shape goes through `step_init`'s woven-head arm (WI-1040's reader,
/// widened to a body-less callee by `body_less_relation_arity`), the operand through
/// `unify`'s own reduction. Both must dispatch through the dictionary or one spelling
/// of one program answers differently from the other — the WI-20260910-FDPJ8 shape.
///
/// BACK-OUT: the operand stays an UN-REDUCED call term (a definite solution whose
/// value is the call itself), which is the WI-483 leave-uninterpreted outcome.
#[test]
fn the_carrier_less_call_at_operand_position_answers_the_same() {
    let src = two_carriers(
        "  rule via(?x, ?r) :- require[Zeroable[T]], Zeroable.tag(?x, ?t), \
            ?r <=> Zeroable.zero()\n  \
           rule answer(?r) :- via(sum(), ?r)\n",
    );
    assert_eq!(answer(&src), 3, "the operand position must dispatch too");
}

// ── the two "either way" controls ───────────────────────────────────────────

/// PASSES EITHER WAY BY DESIGN, and that is what it is for: it says the change
/// serves ONLY the carrier-less call.
///
/// `Zeroable.tag(?x, ?r)` carries its carrier in an argument, so it was already
/// decided — by the weave (it is bodied, so `functional_relation_arity` admitted it
/// before this ticket) and, with the `require` deleted, by value-direction. Both
/// spellings answer the carrier's own number, before and after.
#[test]
fn a_carrier_bearing_call_answers_the_same_number_either_way() {
    for (ctor, expected) in [("sum()", 1), ("prod()", 2)] {
        let with = two_carriers(&format!(
            "  rule via(?x, ?r) :- require[Zeroable[T]], Zeroable.tag(?x, ?r)\n  \
             rule answer(?r) :- via({ctor}, ?r)\n"
        ));
        let without = two_carriers(&format!(
            "  rule via(?x, ?r) :- Zeroable.tag(?x, ?r)\n  \
             rule answer(?r) :- via({ctor}, ?r)\n"
        ));
        assert_eq!(answer(&with), expected);
        assert_eq!(
            answer(&without),
            expected,
            "a carrier-BEARING call is decided by the value either way — the \
             carrier-less admission must not be what makes this row work",
        );
    }
}

/// PASSES EITHER WAY BY DESIGN — WI-1040's MEASURED REGRESSION, kept as a guard.
///
/// That ticket recorded weaving a body-less spec op taking `require[PartialEq[T]],
/// eq(?x, ?y)` from ONE solution to ZERO, because `eq` is ALSO builtin-tagged and an
/// `Expr::ApplyWithin` at goal position is `ViewHead::Opaque` to builtin dispatch.
/// The admission added here cannot reach it: `body_less_relation_arity` bails on
/// `self.builtins.get(&f).is_some()`, so a builtin-backed callee is refused by the
/// reader test before the carrier test is even asked.
#[test]
fn a_builtin_backed_spec_op_is_still_not_woven() {
    let src = r#"namespace test.nar1x
  import anthill.prelude.Int64
  import anthill.prelude.PartialEq
  import anthill.prelude.PartialEq.{eq}
  rule via(?x, ?y, ?r) :- require[PartialEq[T]], eq(?x, ?y), ?r <=> 1
  rule answer(?r) :- via(1, 1, ?r)
end
"#;
    assert_eq!(
        answer(src),
        1,
        "`eq` must keep the check-only behaviour WI-1040 left it with",
    );
}

// ── the dictionary's SUBTREE crosses into the impl's own frame ──────────────

/// A CONDITIONAL provider, whose implementation reads its ELEMENT's dictionary.
///
/// `Wrap provides Zeroable[T = Wrap] :- Zeroable[E]`, and `Wrap.zero() =
/// Zeroable.zero() + 100` reads the element's slot out of its own frame. Selecting
/// `Wrap.zero` is not enough to RUN it: the only thing in the system that says the
/// element is `Sum` is `sub(0)` of the dictionary the clause holds
/// (`060-typedomains-implementation.md` §4.1 — "the components' types live in the
/// subtree, so the subtree is what must cross"), and the bridge's usual answer
/// — pin the chain from the argument types — has no argument to read.
///
/// BACK-OUTS, and they are DIFFERENT: with the dictionary hand-off removed this row
/// answers ONE INDEFINITE solution (the impl is selected, its own slot is not filled,
/// and the bridge suspends); with the carrier-less admission removed it answers `[]`
/// (nothing selects the impl at all).
#[test]
fn the_selected_impls_own_requirement_is_filled_from_the_dictionary() {
    let src = r#"namespace test.nar1x
  import anthill.prelude.Int64
  sort Zeroable
    sort T = ?
    operation zero() -> Int64
    operation tag(x: T) -> Int64 = 0
  end
  sort Sum
    import anthill.prelude.Int64
    entity sum
    provides Zeroable[T = Sum]
    operation zero() -> Int64 = 3
    operation tag(x: Sum) -> Int64 = 1
  end
  sort Prod
    import anthill.prelude.Int64
    entity prod
    provides Zeroable[T = Prod]
    operation zero() -> Int64 = 5
    operation tag(x: Prod) -> Int64 = 2
  end
  sort Wrap
    import anthill.prelude.Int64
    sort E = ?
    entity wrap(inner: E)
    provides Zeroable[T = Wrap] :- Zeroable[E]
    operation zero() -> Int64 = Int64.add(Zeroable.zero(), 100)
    operation tag(x: Wrap) -> Int64 = 9
  end
  rule via(?x, ?r) :- require[Zeroable[T]], Zeroable.tag(?x, ?t), Zeroable.zero(?r)
  rule answer(?r) :- via(wrap(inner: sum()), ?r)
end
"#;
    assert_eq!(
        answer(src),
        103,
        "`Wrap.zero()` must read the ELEMENT's dictionary — `sub(0)` of the one the \
         clause holds — and reach `Sum`'s 3, not `Prod`'s 5 and not a residual",
    );
}

/// THE CONTROL FOR THE ROW ABOVE: `103` must be the ELEMENT's number and not a
/// constant. The same program at the other element answers `105`.
///
/// Without this the row above passes on a `Wrap.zero()` that ignored its slot and
/// still happened to be entered with `Sum`'s dictionary — which is exactly what a
/// sole-provider completion inside `resolve_bridge_requirements` would have produced.
#[test]
fn the_filled_requirement_follows_the_element_and_is_not_a_constant() {
    let src = |elem: &str| {
        format!(
            r#"namespace test.nar1x
  import anthill.prelude.Int64
  sort Zeroable
    sort T = ?
    operation zero() -> Int64
    operation tag(x: T) -> Int64 = 0
  end
  sort Sum
    import anthill.prelude.Int64
    entity sum
    provides Zeroable[T = Sum]
    operation zero() -> Int64 = 3
    operation tag(x: Sum) -> Int64 = 1
  end
  sort Prod
    import anthill.prelude.Int64
    entity prod
    provides Zeroable[T = Prod]
    operation zero() -> Int64 = 5
    operation tag(x: Prod) -> Int64 = 2
  end
  sort Wrap
    import anthill.prelude.Int64
    sort E = ?
    entity wrap(inner: E)
    provides Zeroable[T = Wrap] :- Zeroable[E]
    operation zero() -> Int64 = Int64.add(Zeroable.zero(), 100)
    operation tag(x: Wrap) -> Int64 = 9
  end
  rule via(?x, ?r) :- require[Zeroable[T]], Zeroable.tag(?x, ?t), Zeroable.zero(?r)
  rule answer(?r) :- via(wrap(inner: {elem}), ?r)
end
"#
        )
    };
    assert_eq!(answer(&src("sum()")), 103);
    assert_eq!(
        answer(&src("prod()")),
        105,
        "the element decides; two elements must not answer one number",
    );
}

// ── NAR1X's own acceptance: the op→rule ground-test entry ───────────────────

/// NAR1X'S ACCEPTANCE ROW — a rule whose requirement is at a carrier-less spec op,
/// entered as a GROUND TEST from a POLYMORPHIC operation, answers BY VALUE, and two
/// suppliers give different numbers.
///
/// `Holder.same[HT](a, b) requires PartialEq[T = HT]` defers its `eq` to the frame's
/// dictionary; the carrier's `ceq` is defined by RULES, so the eq bridge hands the
/// goal to the resolver (`prove_rule_predicate`, WI-1092's route). That clause holds
/// `require[Zeroable[T]]` and asks the carrier-less `Zeroable.zero(?z)` for a number,
/// which it then matches against the operand's own field. So `same(sum(v: 3), _)`
/// holds and `same(sum(v: 5), _)` does not, while `Prod` is the other way round —
/// the two carriers' `zero()`s, `3` and `5`, read off the outcome.
///
/// The second operand is `99` in every row, so the pair is structurally UNEQUAL and
/// `ceq` is what decides it. (Comparing a value with itself is how a fixture like
/// this comes to measure nothing — WI-1092's own note.)
///
/// BACK-OUT: with the carrier-less admission removed, ALL FOUR rows answer `0` —
/// including the two whose truth is `1`. That is a WRONG ANSWER and not a missing
/// one: `ceq` IS defined, its clause simply cannot run the call, so the proof is
/// `Refuted` and every caller renders that as `false`.
#[test]
fn a_polymorphic_operation_entering_a_rule_reaches_the_carrier_less_op() {
    let src = r#"namespace test.nar1x.entry
  import anthill.prelude.{Bool, Int64, Eq, PartialEq}

  sort Zeroable
    sort T = ?
    operation zero() -> Int64
    operation tag(x: T) -> Int64 = 0
  end

  sort Sum
    import anthill.prelude.{Bool, Int64}
    entity sum(v: Int64)
    provides Zeroable[T = Sum]
    operation zero() -> Int64 = 3
    operation tag(x: Sum) -> Int64 = 1
    operation ceq(a: Sum, b: Sum) -> Bool
    rule ceq(?a, ?b) :- require[Zeroable[T]], Zeroable.tag(?a, ?t),
                        Zeroable.zero(?z), ?a <=> sum(v: ?z)
    provides PartialEq[T = Sum, eq = ceq]
    provides Eq[T = Sum]
  end

  sort Prod
    import anthill.prelude.{Bool, Int64}
    entity prod(v: Int64)
    provides Zeroable[T = Prod]
    operation zero() -> Int64 = 5
    operation tag(x: Prod) -> Int64 = 2
    operation ceq(a: Prod, b: Prod) -> Bool
    rule ceq(?a, ?b) :- require[Zeroable[T]], Zeroable.tag(?a, ?t),
                        Zeroable.zero(?z), ?a <=> prod(v: ?z)
    provides PartialEq[T = Prod, eq = ceq]
    provides Eq[T = Prod]
  end

  sort Holder
    sort HT = ?
    requires PartialEq[T = HT]
    operation same(a: HT, b: HT) -> Bool = PartialEq.eq(a, b)
  end

  sort Driver
    import anthill.prelude.Int64
    operation drive_sum(n: Int64) -> Int64 =
      if Holder.same(Sum.sum(v: n), Sum.sum(v: 99)) then 1 else 0
    operation drive_prod(n: Int64) -> Int64 =
      if Holder.same(Prod.prod(v: n), Prod.prod(v: 99)) then 1 else 0
  end
end
"#;
    let mut interp = crate::common::interp_for(src);
    // `Sum.zero()` is 3 and `Prod.zero()` is 5 — read off which operand each
    // carrier's rule accepts.
    for (op, n, expected) in [
        ("drive_sum", 3, 1),
        ("drive_sum", 5, 0),
        ("drive_prod", 3, 0),
        ("drive_prod", 5, 1),
    ] {
        let got = interp
            .call(&format!("test.nar1x.entry.Driver.{op}"), &[Value::Int(n)])
            .unwrap_or_else(|e| panic!("{op}({n}): {e:?}"));
        assert_eq!(
            crate::common::scalar_int(interp.kb(), &got),
            Some(expected),
            "{op}({n}) must be {expected}: the rule reads its carrier's own \
             `Zeroable.zero()` through the clause dictionary",
        );
    }
}

/// THE THIRD AXIS — the dictionary crosses a rule HEAD, which is what decides WHICH
/// CARRIER it arrives on.
///
/// One dictionary has three carriers (`requirement-channel.md` §9): a `TermId`, a
/// `Value::Entity`, and a `NodeOccurrence` (`Expr::Dictionary`). Every row above
/// derives its dictionary in the SAME clause that uses it, so it arrives as the
/// `Value::Entity` `fetch_dictionary` built. Supply it through a HEAD instead — `get`
/// binds it, `use` receives it — and the goal walk materializes it into the
/// occurrence carrier on the way.
///
/// So this row measures the READ, not the hand-off: `Dictionary::from_view` (the
/// carrier-neutral one) against `Dictionary::from_value` (which matches the
/// `Value::Entity` shape structurally). BACK-OUT, measured: with `from_value` at that
/// site this answers ONE INDEFINITE solution, because the handle is `None`, no
/// `WovenDispatch` is built, and `Wrap.zero()`'s own element slot is never filled.
///
/// It needs the CONDITIONAL provider to discriminate at all: on a leaf impl the
/// handle is unused, so both readers answer `3` and the axis would be invisible.
/// A dictionary that only has to SELECT a member is read through `TermView` by
/// `dictionary_dispatch_target`'s impl lookup, which was carrier-neutral before this
/// ticket and is why WI-1040's own crossing rows never needed this.
#[test]
fn a_dictionary_crossing_a_rule_head_is_read_on_its_own_carrier() {
    let src = r#"namespace test.nar1x
  import anthill.prelude.Int64
  sort Zeroable
    sort T = ?
    operation zero() -> Int64
    operation tag(x: T) -> Int64 = 0
  end
  sort Sum
    import anthill.prelude.Int64
    entity sum
    provides Zeroable[T = Sum]
    operation zero() -> Int64 = 3
    operation tag(x: Sum) -> Int64 = 1
  end
  sort Prod
    import anthill.prelude.Int64
    entity prod
    provides Zeroable[T = Prod]
    operation zero() -> Int64 = 5
    operation tag(x: Prod) -> Int64 = 2
  end
  sort Wrap
    import anthill.prelude.Int64
    sort E = ?
    entity wrap(inner: E)
    provides Zeroable[T = Wrap] :- Zeroable[E]
    operation zero() -> Int64 = Int64.add(Zeroable.zero(), 100)
    operation tag(x: Wrap) -> Int64 = 9
  end
  rule get(?x, ?d) :- ?d = require[Zeroable[T]], Zeroable.tag(?x, ?t)
  rule use(?x, ?d, ?r) :- ?d = require[Zeroable[T]], Zeroable.tag(?x, ?u), Zeroable.zero(?r)
  rule answer(?r) :- get(wrap(inner: {elem}), ?d), use(wrap(inner: {elem}), ?d, ?r)
end
"#;
    // Both elements, so the row cannot pass on a constant — the same control the
    // locally-derived twin above carries.
    assert_eq!(answer(&src.replace("{elem}", "sum()")), 103);
    assert_eq!(answer(&src.replace("{elem}", "prod()")), 105);
}
