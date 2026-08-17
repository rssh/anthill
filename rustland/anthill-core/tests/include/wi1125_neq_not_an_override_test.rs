//! WI-1125 (WI-502 consumer) — a carrier may not supply its own `neq`.
//!
//! THE DECISION, because the ticket posed it as two opposite arms. `neq` is NOT an
//! override point: `neq(a, b) <=> not(eq(a, b))` (kernel-language.md §8.3,
//! `stdlib/anthill/prelude/eq.anthill`) makes it DERIVED, §8.3 already said in as
//! many words that "an own `neq` member is never consulted", and every evaluator
//! implements exactly that — the resolver's `sem_eq_core` runs one `sem_eq_values`
//! with the verdict inverted, `eval::builtins`' `builtin_neq` is `!semantic_equal`,
//! and the C++ codegen maps `PartialEq.neq` to `!=`. So the declaration was accepted,
//! documented as an override (WI-1098/WI-999), and honoured nowhere. WI-1125 makes it
//! a LOAD ERROR (`LoadError::CarrierSuppliesNeq`, raised by `build_eq_dispatch_index`
//! via `neq_supplier_refusals`) rather than teaching four evaluators to dispatch a
//! member the language defines as derived.
//!
//! WHAT WAS SILENTLY WRONG, in two shapes that failed differently:
//!
//!   1. `neq` and NO `eq` — nothing keys the eq-dispatch index, so `sem_eq_values`
//!      fell through to its STRUCTURAL verdict, against the carrier's own
//!      inequality. WI-755 held a typer-side floor over the guard-REFUTATION route
//!      alone (`guard_conjunct_reaches_undispatchable_neq` + its value scan, depth
//!      cap and three-route supply probe — ~175 lines, all deleted by this ticket).
//!      The three other `prove_from_gamma` consumers (call-site `requires`, contract
//!      `ensures`, in-body `proof`) and the interpreter had no floor at all and
//!      answered structurally. That is the half this ticket owns, and the sections
//!      below drive each consumer with a program shaped for it.
//!   2. `neq` BESIDE an `eq` — the `eq` is dispatched and is RIGHT (it is the
//!      authority the law names, and `wi573_eq_override_discharge_test::
//!      custom_eq_override_dispatches_and_drops` pins that dispatch on the eq-only
//!      carrier). The `neq` is then dead text that can only disagree with the
//!      equality that decides, and nothing checked the two for coherence. Nothing
//!      CAN: `∀a,b. neq(a,b) = not(eq(a,b))` is not decidable at load. Refusing the
//!      member makes the contradiction unrepresentable rather than partially checked
//!      — which is why the refusal is total and not narrowed to the neq-only shape.
//!
//! CONTROLS. MEASURED, not predicted — back the refusal out by MUTATION rather than
//! deletion (leave the `neq_supplier_refusals` call in `build_eq_dispatch_index`,
//! discard its result), so the sweep still runs and only the verdict changes, and run
//! all 3042 `anthill-core` tests. EXACTLY SEVEN fail and nothing else:
//!
//!   * the six `*_is_refused` rows here — `a_carrier_own_neq_member`,
//!     `a_fact_bound_neq`, `a_witness_supplied_neq`,
//!     `a_carrier_supplying_both_members`, `contradictory_members_are_refused_by_the_
//!     same_rule` and `every_consumer_of_a_neq_only_carrier` — each because its
//!     fixture loads clean again;
//!   * `wi1098_derive_eq_total_test::declaring_neq_on_a_derived_carrier_is_not_a_
//!     capture_but_is_still_refused`.
//!
//! That nothing ELSE moves is half the measurement: it says the refusal reaches only
//! programs that supply a `neq`, which no stdlib carrier and no other fixture does.
//!
//! The other five rows here pass either way, and each says so at its own site. Three
//! are LOAD-CLEAN controls that a refusal cannot flip — `the_same_carrier_without_the_
//! neq_member_loads`, `an_abstract_spec_declaring_the_family_is_not_a_carrier_override`
//! (which has its own back-out below) and `every_consumer_shape_loads_clean_without_
//! the_member`; two are the `*_spelling_*` repair rows, which never mention a `neq`
//! member. That is by design, and the last of them is worth naming:
//!   * `every_consumer_shape_loads_clean_without_the_member` does NOT fail — it is
//!     the same five programs with no equality member, i.e. the structural answer
//!     the accepted `neq`-only program was silently giving, and it passes either way
//!     BY DESIGN. It is the measurement of the DEFECT and the control on the fixtures
//!     (a refusal raised in the load pass would be satisfied by a program too
//!     malformed to reach its consumer). Beside it sit the two `*_spelling_*` rows,
//!     which take the same meaning written as an `eq` and reach the OPPOSITE verdict
//!     through the `requires` consumer and through eval. Together they make "refused"
//!     a repair rather than a removal: the carrier can still say what it meant.
//!
//! A SECOND, INDEPENDENT BACK-OUT covers the other half of the detection: make
//! `member_operands_are_the_carrier` return `true` unconditionally, i.e. refuse
//! any own member named `neq`. MEASURED over the same 3042 tests, exactly ONE fails
//! — `an_abstract_spec_declaring_the_family_is_not_a_carrier_override` — and it is
//! the row that has to: a spec declaring `neq(a: T, b: T)` for its own type parameter
//! is not overriding anything for itself, and refusing it would reject a shape the
//! corpus already has (`map_eq_error_test`'s `MyEq`) with a message its author could
//! not act on. TWO back-outs because there are two axes — WHETHER a supplied `neq` is
//! refused, and WHICH members count as supplying one — and one of them would have
//! measured only the first.
//!
//! The rows this ticket MOVED live where the behaviour moved: the three
//! `*_keeps_effect` rows and `carrier_supplying_both_members_dispatches_its_eq` in
//! `wi573_eq_override_discharge_test` were about a floor that no longer exists and
//! are replaced by the refusal rows here; `wi1098_derive_eq_total_test::
//! declaring_neq_on_a_derived_carrier_is_an_override_not_a_capture` flipped from
//! "loads clean" to "refused, and NOT by the capture check".

use anthill_core::eval::Interpreter;

/// The one shape every row varies: a two-constructor `Color` whose equality is
/// stated by MEMBERS, plus whatever the row needs around it. `members` is spliced
/// into the sort body.
fn color_program(ns: &str, members: &str, rest: &str) -> String {
    format!(
        r#"
namespace wi1125.{ns}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq}}
  import anthill.prelude.PartialEq.{{eq, neq}}

  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
{members}
  end
{rest}
end
"#
    )
}

/// Load `src` and return the rendered load errors (empty on a clean load).
fn load_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

/// Assert `src` is refused by THIS ticket's refusal and no other. Matching the
/// leading phrase alone would also pass on any unrelated error that happened to
/// name `neq`, so both the verdict and the reason are pinned; `no_eq` says which of
/// the two repairs the message must offer, which is the half a narrowed refusal
/// would get wrong.
fn expect_neq_refusal(src: &str, no_eq: bool) -> Vec<String> {
    let errs = load_errors(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("`neq` is not an override point")),
        "expected the WI-1125 refusal; got: {errs:#?}"
    );
    let repair = if no_eq {
        "Supply the `eq` instead"
    } else {
        "Delete the `neq`"
    };
    assert!(
        errs.iter().any(|e| e.contains(repair)),
        "expected the message to offer the repair {repair:?}; got: {errs:#?}"
    );
    errs
}

// ── The three supply routes ──────────────────────────────────────────────────
// Asked in the eq-dispatch index's own vocabulary (`EqDispatchIndex::build_neq`),
// so the refusal covers exactly the routes an `eq` is collected from. This is not
// belt-and-braces: WI-755's floor asked the same question a second way and had to
// be told, by review, that its route-1-only read let a `fact PartialEq(T: Color,
// neq: colorNeq)` binding through.

#[test]
fn a_carrier_own_neq_member_is_refused() {
    // ROUTE 1. `neq = false` — nothing is unequal, so under this carrier's own
    // inequality EVERYTHING is equal, the exact opposite of the structural verdict
    // on `Green`/`Red`. Before WI-1125 this loaded and every evaluator answered
    // structurally against it.
    let src = color_program(
        "ownmember",
        "    operation neq(a: Color, b: Color) -> Bool = false",
        "",
    );
    let errs = expect_neq_refusal(&src, true);
    assert!(
        errs.iter().any(|e| e.contains("the carrier's own member")),
        "the message must name the ROUTE, since the three are written in three \
         syntaxes and the author must know which text to change; got: {errs:#?}"
    );
    // ONE error, not two. `eq_dispatch_carrier_domain` unions two sources and
    // deduplicates CANONICALLY precisely because a carrier visited twice reports
    // itself twice — its own doc says so about `AmbiguousEqDispatch`, and this
    // refusal rides the same walk. A row asserting only `any(...)` would not see a
    // duplicate.
    assert_eq!(
        errs.len(),
        1,
        "the refusal must be reported ONCE per carrier; got: {errs:#?}"
    );
}

#[test]
fn a_fact_bound_neq_is_refused() {
    // ROUTE 2 — a retroactive instance fact's op binding. The carrier declares no
    // member at all, so a route-1-only reader sees nothing; it is just as
    // undispatchable, and `wi573_eq_override_discharge_test` measured a route-1-only
    // detection dropping a real effect over exactly this shape.
    let src = r#"
namespace wi1125.factbound
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}

  sort Color
    entity Red
    entity Green
  end

  operation colorNeq(a: Color, b: Color) -> Bool = false
  fact PartialEq(T: Color, neq: colorNeq)
end
"#;
    let errs = expect_neq_refusal(src, true);
    assert!(
        errs.iter().any(|e| e.contains("an instance fact binding")),
        "the message must name the FACT route; got: {errs:#?}"
    );
}

#[test]
fn a_witness_supplied_neq_is_refused() {
    // ROUTE 3 — a witness sort providing `PartialEq[T = Color]` and supplying the
    // member. The third route the eq index collects, and the one WI-837 added; a
    // refusal that covered only the two written inside the carrier would leave the
    // hole open for the one spelling that is written outside it.
    let src = r#"
namespace wi1125.witness
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Color
    entity Red
    entity Green
  end

  sort ColorNeq
    provides PartialEq[T = Color]
    operation neq(a: Color, b: Color) -> Bool = false
  end
end
"#;
    let errs = expect_neq_refusal(src, true);
    assert!(
        errs.iter().any(|e| e.contains("witness sort")),
        "the message must name the WITNESS route; got: {errs:#?}"
    );
}

// ── Both members: the arm that made the refusal TOTAL ─────────────────────────

#[test]
fn a_carrier_supplying_both_members_is_refused() {
    // SUB-CASE 2 — the two members CONSISTENT (`eq = false`, `neq = true` satisfy
    // `neq <=> not(eq)`). The `eq` was dispatched and was right, so nothing here was
    // ever answered wrongly; what is refused is the DEAD member beside it, and the
    // reason is sub-case 3 below, which this shape is one token away from.
    //
    // The behaviour this used to guard — the WI-755 dispatch not being blocked by
    // the mere presence of an own `neq` — is not lost with the row: it is pinned by
    // `wi573_eq_override_discharge_test::custom_eq_override_dispatches_and_drops` on
    // the eq-ONLY carrier, and by `the_same_carrier_without_the_neq_member_loads`
    // below on this very program.
    let src = color_program(
        "bothmembers",
        "    operation eq(a: Color, b: Color) -> Bool = false\n    \
         operation neq(a: Color, b: Color) -> Bool = true",
        "",
    );
    let errs = expect_neq_refusal(&src, false);
    assert!(
        errs.iter().any(|e| e.contains("beside its `eq`")),
        "with an `eq` present the message must say so — that is what makes \
         'delete the `neq`' the right repair rather than 'supply an `eq`'; \
         got: {errs:#?}"
    );
}

#[test]
fn contradictory_members_are_refused_by_the_same_rule() {
    // SUB-CASE 3 — `eq = false` AND `neq = false`: the carrier states something
    // `neq <=> not(eq)` forbids. Before WI-1125 the resolver answered via the `eq`
    // and NOTHING checked the pair — not `check_eq_noneq_exclusive` (that is
    // `Eq` vs `NonEq`), not `AmbiguousEqDispatch` (that is two `eq` suppliers).
    //
    // It is refused by the SAME rule as the consistent pair above, and deliberately:
    // a load-time check of `∀a,b. neq(a,b) = not(eq(a,b))` is not decidable, so any
    // check would be a syntactic approximation that this fixture happens to fall
    // inside. Refusing the member makes the contradiction unrepresentable, which is
    // total. That the two rows differ in one token and get the same verdict IS the
    // measurement.
    let src = color_program(
        "contradictory",
        "    operation eq(a: Color, b: Color) -> Bool = false\n    \
         operation neq(a: Color, b: Color) -> Bool = false",
        "",
    );
    expect_neq_refusal(&src, false);
}

#[test]
fn the_same_carrier_without_the_neq_member_loads() {
    // THE CONTROL for both rows above: identical program, `neq` member deleted. It
    // must load — otherwise "refused" would be measuring the `eq` member, the
    // `provides` lines, or the fixture being malformed, and every row in this file
    // would prove nothing.
    let src = color_program(
        "bothminusneq",
        "    operation eq(a: Color, b: Color) -> Bool = false",
        "",
    );
    assert!(
        load_errors(&src).is_empty(),
        "a carrier supplying only `eq` must still load: {:#?}",
        load_errors(&src)
    );
}

#[test]
fn an_abstract_spec_declaring_the_family_is_not_a_carrier_override() {
    // THE ROUTE-1 FILTER, and the row that fails if it is dropped. A spec DECLARES
    // `eq`/`neq` over its own type parameter for its providers to implement; it is
    // not overriding equality for its own values, and `carrier_own_op` cannot tell
    // the two apart on the name alone (`MyEq.neq` is parented by `MyEq` and is not
    // `PartialEq.neq`, so it passes both of that predicate's filters).
    // `member_operands_are_the_carrier` separates them by asking whose values
    // the member compares — `T`, not `MyEq`.
    //
    // The same false positive `typing::carrier_has_unbacked_eq_override` had to
    // exclude for `eq`, and the same shape `map_eq_error_test::
    // abstract_spec_redeclaring_eq_loads_clean` already carries — that row's `MyEq`
    // spells the second member `neq2` to stay clear of the eq family, so this one
    // spells it `neq` and is the row that actually stands on the filter.
    let src = r#"
namespace wi1125.userspec
  import anthill.reflect.{not}
  import anthill.prelude.Bool
  sort MyEq
    sort T = ?
    operation {
      eq(a: T, b: T) -> Bool
      neq(a: T, b: T) -> Bool
    }
  end
end
"#;
    assert!(
        load_errors(src).is_empty(),
        "a spec declaring the eq family for its own parameter is a DECLARATION, not \
         a carrier override, and must load: {:#?}",
        load_errors(src)
    );
}

// ── What is NOT the carrier's `neq` — the three review findings ──────────────
// A refusal is only as good as its boundary, and this ticket's first cut got the
// boundary wrong three ways. Each was reproduced by review against a program that
// had loaded clean before; each row below is that program.

#[test]
fn a_nullary_member_named_neq_is_not_this_spec_op() {
    // FINDING 1 — and it was a PANIC, not a wrong verdict. The first cut read the
    // member's first parameter and `debug_assert!`ed the binary arity, on the premise
    // that `PartialEq.neq` is binary. That is a fact about the SPEC's declaration, not
    // about an arbitrary member a carrier happens to name `neq` — and `operation
    // neq() -> Bool` is ordinary parsable source, so every debug build (which is every
    // test binary, and a debug `anthill check`) aborted instead of diagnosing.
    //
    // The verdict is `false`, and not as a fallback: a 0-ary member is not
    // `PartialEq.neq` under any reading, so it supplies nothing and the program is
    // fine. Backing the fix out replaces this row's clean load with a process abort.
    let src = color_program("nullary", "    operation neq() -> Bool = true", "");
    assert!(
        load_errors(&src).is_empty(),
        "a 0-ary member named `neq` is not the binary spec op and must neither be \
         refused nor asserted on: {:#?}",
        load_errors(&src)
    );
}

#[test]
fn an_unrelated_neq_on_a_witness_sort_does_not_refuse_its_carrier() {
    // FINDING 2. The witness route reads `carrier_own_op(witness, …)` FIRST — a match
    // on the short name, one sort over — before the provision's own `neq = f` binding.
    // So a witness that legitimately supplies `Color`'s `eq` and also happens to
    // declare an `Int64` helper called `neq` was read as supplying `Color`'s `neq`,
    // and the message told its author to delete a member with nothing to do with
    // equality. MEASURED before the fix: refused, naming
    // `witness sort 'ColorEq' (supplying 'ColorEq.neq')`.
    //
    // Its control is the row below: the same witness route DOES refuse when the
    // member really compares `Color`s, so this row is not just "witnesses are exempt".
    let src = r#"
namespace wi1125.witnessunrelated
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Color
    entity Red
    entity Green
  end

  sort ColorEq
    provides PartialEq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = true
    operation neq(a: Int64, b: Int64) -> Bool = false
  end
end
"#;
    assert!(
        load_errors(src).is_empty(),
        "a witness member named `neq` that compares Int64s supplies nothing of \
         `Color`'s equality: {:#?}",
        load_errors(src)
    );
}

#[test]
fn a_written_neq_binding_on_a_witness_is_refused_as_written() {
    // THE OTHER EDGE of finding 2, and what keeps the fix from being an exemption. A
    // provision that WRITES `neq = f` is a deliberate claim about this carrier's
    // inequality however `f` is typed, so nothing has to be established about `f` —
    // the author named the slot. Only the name-matched leg is filtered.
    let src = r#"
namespace wi1125.witnessbound
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Color
    entity Red
    entity Green
  end

  operation colorNeq(a: Color, b: Color) -> Bool = false

  sort ColorNeqW
    provides PartialEq[T = Color, neq = colorNeq]
  end
end
"#;
    expect_neq_refusal(src, true);
}

#[test]
fn a_carrier_that_claims_no_equality_is_refused_too() {
    // FINDING 3, answered rather than excused. Review proposed gating the refusal on
    // the carrier SELF-PROVIDING `Eq`/`PartialEq`, the way
    // `typing::carrier_has_unbacked_eq_override` gates its own `eq` probe. That gate
    // cannot be asked here and must not be: `build_eq_dispatch_index` runs BEFORE
    // WI-1098's `derive_total_eq`, so a total composite provides nothing YET — and
    // this fixture is `wi1098_derive_eq_total_test`'s own shape with different names.
    // Gating on provisions would have excused the ticket's headline case by an
    // accident of pass order.
    //
    // So the criterion is the member's shape, and the consequence is stated here
    // rather than left to be discovered: a sort that never wrote `provides` is
    // refused too. It is the same silent hole — nothing dispatches the member, a
    // `neq(m, n)` call takes the builtin and answers structurally — and the repair is
    // the same one member over.
    let src = r#"
namespace wi1125.noclaim
  import anthill.prelude.Bool

  sort Matrix
    entity mk(n: Bool)
    operation neq(a: Matrix, b: Matrix) -> Bool = true
  end
end
"#;
    expect_neq_refusal(src, true);
}

// ── The consumers: every reader that was silently structural ─────────────────
// The refusal is ONE load-time check, upstream of all of them — which is the whole
// argument for putting it there, and is exactly the claim that has to be driven
// rather than inferred. Each entry below is a program shaped for one consumer, in
// the shape that reached that consumer with a wrong answer.
//
// TWO ROWS OVER THE TABLE, and neither is worth anything without the other. The
// first asserts every shape is REFUSED once the carrier declares `neq`. The second
// loads the SAME five shapes with no equality member at all and asserts they are
// CLEAN — without it, "refused" would be satisfied by a fixture too malformed to
// reach its consumer, since this ticket's error is raised in the load pass and does
// not care whether the body below it type-checks. Clean-without-the-member is also
// what the accepted `neq`-only program was silently answering: the structural
// verdict, identical to having written nothing.

/// `(consumer, source tail)` — one program shape per `prove_from_gamma` consumer,
/// plus eval. `Boom` is declared inside each shape that needs it so the tails stay
/// independent.
const CONSUMER_SHAPES: &[(&str, &str)] = &[
    // 1 — `conjunct_refuted` → `refute_guard`. The one route WI-755 floored: with the
    // floor the effect was KEPT (suspended), with it removed the effect DROPPED, a
    // silent wrong answer. Neither now.
    (
        "guard",
        r#"
  operation risky(c: Color) -> Int64
    effects { Boom :- eq(c, Red) }

  operation caller() -> Int64 =
    risky(Green)

  sort Boom
    entity Bang
  end
"#,
    ),
    // 2 — `precondition_proved`. THE row this ticket owns: measured on HEAD BEFORE
    // WI-755, `requires neq(c, Red)` at `needy(Green)` PROVED, though a carrier whose
    // own `neq` is `false` calls every colour equal. WI-756 covered the proof paths
    // but every one of its fixtures uses an `eq` override, so none reached this shape.
    (
        "requires",
        r#"
  operation needy(c: Color) -> Int64
    requires neq(c, Red)
  =
    1

  operation caller() -> Int64 =
    needy(Green)
"#,
    ),
    // 3 — `proof_verify::discharge_contract_proof`, the contract `ensures` site.
    (
        "ensures",
        r#"
  operation pick() -> Color
    ensures neq(result, Red)
  =
    Green
"#,
    ),
    // 4 — WI-538's in-body `proof … by derivation conclude`.
    (
        "inbodyproof",
        r#"
  operation claim() -> Int64 =
    proof h by derivation conclude neq(Green, Red) end
    1
"#,
    ),
    // 5 — eval. `builtin_neq` is `!semantic_equal`, and `semantic_equal` probes the
    // same eq-keyed index, so the interpreter answered a `neq`-only carrier
    // structurally too. Driven for real by
    // `the_eq_spelling_of_the_same_carrier_is_answered_semantically`.
    ("eval", "\n  operation same() -> Bool = neq(Green, Red)\n"),
];

#[test]
fn every_consumer_of_a_neq_only_carrier_is_refused() {
    for (consumer, tail) in CONSUMER_SHAPES {
        let src = color_program(
            consumer,
            "    operation neq(a: Color, b: Color) -> Bool = false",
            tail,
        );
        let errs = expect_neq_refusal(&src, true);
        assert!(
            !errs.is_empty(),
            "consumer {consumer}: expected the WI-1125 refusal"
        );
    }
}

#[test]
fn every_consumer_shape_loads_clean_without_the_member() {
    // THE CONTROL for the row above, and the one that makes it a statement about the
    // `neq` member rather than about five fixtures. Same five programs, no equality
    // member: the carrier has none of its own, the structural verdict IS its
    // instance, and every shape resolves — the guard refutes and drops `Boom`, the
    // `requires`/`ensures`/`conclude` all hold since `Green` and `Red` are
    // structurally distinct, and the `neq` call evaluates.
    //
    // It is ALSO the defect, stated: this clean load is exactly the answer the
    // ACCEPTED `neq`-only program was giving on every one of these shapes — the
    // verdict reached by ignoring a member that said the opposite. So the row passes
    // either way BY DESIGN (backing this ticket out does not touch it) and is here
    // for the contrast, not as a measurement of the refusal.
    for (consumer, tail) in CONSUMER_SHAPES {
        let src = color_program(&format!("{consumer}bare"), "", tail);
        assert!(
            load_errors(&src).is_empty(),
            "consumer {consumer}: a carrier with no equality of its own is decided \
             structurally and every shape must load: {:#?}",
            load_errors(&src)
        );
    }
}

// ── The repair works: the same meaning, spelled as an `eq` ───────────────────
// A refusal is only a repair if the carrier can still say what it meant.
// `operation neq(a, b) = false` says "nothing is unequal"; `neq <=> not(eq)` makes
// that exactly `operation eq(a, b) = true`. These rows drive the eq spelling through
// the two consumers above that can be observed from a test, and each lands on the
// verdict the `neq` spelling was silently NOT producing.

const EVERYTHING_EQUAL_VIA_EQ: &str = "    operation eq(a: Color, b: Color) -> Bool = true";

#[test]
fn the_eq_spelling_of_the_same_carrier_is_proved_semantically() {
    // CONSUMER 2, repaired. `eq = true` ⇒ everything is equal ⇒ `neq(Green, Red)` is
    // FALSE, so `requires neq(c, Red)` at `needy(Green)` must NOT prove and the call
    // is refused as an unsatisfied precondition. That refusal is the SEMANTIC answer:
    // the structural verdict (`Green ≠ Red`) would have proved it, and did, on every
    // spelling before this ticket.
    let src = color_program(
        "requiresrepair",
        EVERYTHING_EQUAL_VIA_EQ,
        r#"
  operation needy(c: Color) -> Int64
    requires neq(c, Red)
  =
    1

  operation caller() -> Int64 =
    needy(Green)
"#,
    );
    let errs = load_errors(&src);
    assert!(
        !errs
            .iter()
            .any(|e| e.contains("`neq` is not an override point")),
        "the eq spelling must not trip this ticket's refusal; got: {errs:#?}"
    );
    assert!(
        !errs.is_empty(),
        "`Color.eq(Green, Red)` is TRUE, so `neq(Green, Red)` is FALSE and the \
         precondition must NOT prove — the call must be refused. A clean load here \
         means the carrier's equality was ignored and the structural verdict \
         answered, which is the defect this ticket removes."
    );
}

#[test]
fn the_eq_spelling_of_the_same_carrier_is_answered_semantically() {
    // CONSUMER 5, repaired, and the row that DRIVES the interpreter rather than
    // inferring it: `neq(Green, Red)` must be FALSE under `eq = true`. Structurally
    // it is TRUE (two distinct constructors), so this row fails outright if eval
    // stops consulting the carrier.
    let src = color_program(
        "evalrepair",
        EVERYTHING_EQUAL_VIA_EQ,
        "\n  operation same() -> Bool = neq(Green, Red)\n  \
         operation both() -> Bool = eq(Green, Red)\n",
    );
    assert!(load_errors(&src).is_empty(), "{:#?}", load_errors(&src));
    let mut i: Interpreter = crate::common::interp_for(&src);
    let call = |i: &mut Interpreter, op: &str| -> bool {
        i.call(op, &[])
            .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
            .as_bool()
            .unwrap_or_else(|| panic!("call {op}: not a Bool"))
    };
    assert!(
        call(&mut i, "wi1125.evalrepair.both"),
        "the carrier's own `eq` says every colour is equal, so `eq(Green, Red)` is \
         TRUE — the structural verdict is FALSE"
    );
    assert!(
        !call(&mut i, "wi1125.evalrepair.same"),
        "`neq` is the negation of that dispatched `eq`, so `neq(Green, Red)` is \
         FALSE — the structural verdict is TRUE"
    );
}

