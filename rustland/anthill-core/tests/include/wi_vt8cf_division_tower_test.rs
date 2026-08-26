//! WI-20260824-VT8CF — `/` and `%` are CARRIER-AGNOSTIC, because their tier targets are
//! spec operations on parametric carriers.
//!
//! ## What changed, and why it is a library change rather than a guard
//!
//! `/` mints a bare `div` and `%` a bare `mod`, and the implicit tier
//! (`PRELUDE_QUALIFIED`, kb/load.rs) maps each short name to exactly ONE qualified name.
//! Those two entries pointed at `anthill.prelude.Int64.{div,mod}` — a NON-parametric
//! carrier — and everything this file pins follows from that one fact:
//!
//!   * a minted `/` meant the `Int64` operation whatever its operands were, so
//!     `10.0 / 4.0` was `type mismatch in div.a (op-arg): expected Int64, got Float`
//!     unless the file wrote `import anthill.prelude.Float.{div}` — which every float
//!     site in the corpus did, and which is a wart nobody had connected to the gap;
//!   * `typing::spec_op_parent_sort` answers `None` for a non-parametric carrier, so
//!     `check_rival_spec_operations` stood down and a namespace-level
//!     `operation mod(a, b) = 99` CAPTURED a minted `7 % 2`, silently.
//!
//! Both are the same defect — a tier entry is resolved by SCOPE, and scope is
//! shadowable — so both close by repointing the entries at spec operations:
//! `Divisible.div` and `EuclideanDomain.mod` (`stdlib/anthill/prelude/division.anthill`).
//! The refusal half is measured next door, in
//! `wi_kd9sw_minted_operator_address_test::a_free_standing_spec_op_name_is_legal_again`
//! — which INVERTS it: WI-20260825-KD9SW made a minted `%` name
//! `..anthill.prelude.EuclideanDomain.mod` outright, so a free-standing `mod` can no
//! longer silence anything and is legal again, while `7 % 2` still answers 1. This file
//! measures the DISPATCH half — that the operator reaches each carrier's own operation —
//! and that half is unchanged by the mint, since the address names the SPEC op.
//!
//! ## The back-out these rows are stated against
//!
//! Repoint `PRELUDE_QUALIFIED`'s two entries at `anthill.prelude.Int64.{div,mod}` and
//! move the `BuiltinTag::Div`/`Mod` registrations back with them. Every row here that
//! names a non-`Int64` carrier fails; the `Int64` rows pass either way BY DESIGN and are
//! here to pin that the repair changed nothing for the carrier that already worked.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_stdlib_kb, sort_provisions};

/// Call `qn` in a stdlib-backed interpreter and render the result.
fn drive(src: &str, qn: &str) -> String {
    let mut interp = interp_for(src);
    let got = interp
        .call(qn, &[])
        .unwrap_or_else(|e| panic!("{qn} must evaluate: {e:?}"));
    format!("{got:?}")
}

/// THE WART, CLOSED — and the row that fails hardest on a back-out.
///
/// No `import anthill.prelude.Float.{div}` anywhere: a minted `/` resolves to
/// `Divisible.div`, and `Float` provides it (through `Field`), so the typer dispatches to
/// `Float.div`. Backed out, this is a LOAD error naming `Int64`, not a wrong number —
/// which is why it is asserted through a value rather than through "it loads".
#[test]
fn float_division_needs_no_import() {
    let src = r#"
namespace test.vt8cf.fdiv
  import anthill.prelude.{Float}
  operation drive() -> Float = 10.0 / 4.0
end
"#;
    assert_eq!(
        drive(src, "test.vt8cf.fdiv.drive"),
        "Float(2.5)",
        "`10.0 / 4.0` must reach `Float.div` with no import written"
    );
}

/// IEEE division is still IEEE — `1.0 / 0.0` is +Infinity and NOT the
/// `Error[DivisionByZero]` the spec operation declares. The carrier NARROWS the spec's
/// guarded effect to nothing, which is what makes one `div` able to serve both carriers;
/// declaring no effect on `Divisible.div` instead made four carriers a load error
/// ("effects must not widen"), so this row is where that decision is pinned behaviourally.
#[test]
fn float_division_by_zero_is_still_infinity_not_an_effect() {
    let src = r#"
namespace test.vt8cf.finf
  import anthill.prelude.{Float, Bool}
  operation drive() -> Bool = Float.isInfinite(1.0 / 0.0)
end
"#;
    assert_eq!(
        drive(src, "test.vt8cf.finf.drive"),
        "Bool(true)",
        "`Float.div` is total; the spec's guarded effect is narrowed away, not inherited"
    );
}

/// `Int64` UNCHANGED — passes both ways by design. `div` truncates toward zero and `mod`
/// is Euclidean, exactly as before, so the repair is a widening and not a re-definition.
/// The negative row is the one that would catch a silent switch to floored division.
#[test]
fn int_division_and_modulo_are_unchanged() {
    let src = r#"
namespace test.vt8cf.idiv
  import anthill.prelude.{Int64}
  operation q() -> Int64 = 7 / 2
  operation qn() -> Int64 = -7 / 2
  operation m() -> Int64 = 7 % 2
  operation mn() -> Int64 = -7 % 2
end
"#;
    for (op, want) in [
        ("q", "Int(3)"),
        ("qn", "Int(-3)"),
        ("m", "Int(1)"),
        ("mn", "Int(1)"),
    ] {
        assert_eq!(
            drive(src, &format!("test.vt8cf.idiv.{op}")),
            want,
            "`{op}` must be {want}: `div` truncates toward zero, `mod` is Euclidean"
        );
    }
}

/// A CAPABILITY THAT DID NOT EXIST — `BigInt` declared no division at all before this
/// ticket (eighteen ordering and conversion operations and not one of `div`/`mod`/`rem`),
/// so a minted `/` over BigInt operands had nothing to reach. The RESOLVER computed both
/// all along (the BigInt slots of `BuiltinTag::Div`/`Mod`), which is what made the hole
/// invisible: a rule-body division answered while the same division in an operation body
/// had no operation to dispatch to.
#[test]
fn bigint_division_now_exists() {
    let src = r#"
namespace test.vt8cf.bdiv
  import anthill.prelude.{Int64, BigInt, Option}
  import anthill.prelude.PartialEq.{eq}
  -- The divisor is a COMPUTED expression, not a literal, so `eq(b, 0)` cannot be
  -- refuted and the guarded effect stays conservatively present — WI-478's rule, not
  -- anything specific to BigInt. The `Int64` rows above need no declaration because
  -- their divisors are literals that refute it by ground evaluation.
  operation q() -> Option[T = Int64] effects Error[DivisionByZero] =
    BigInt.to_int(BigInt.to_bigint(100) / BigInt.to_bigint(7))
  operation m() -> Option[T = Int64] effects Error[DivisionByZero] =
    BigInt.to_int(BigInt.to_bigint(100) % BigInt.to_bigint(7))
  operation mn() -> Option[T = Int64] effects Error[DivisionByZero] =
    BigInt.to_int(BigInt.to_bigint(-100) % BigInt.to_bigint(7))
end
"#;
    // MATCH THE PAYLOAD, NOT A SUBSTRING OF THE RENDERING. `drive` returns the `Debug`
    // of an `Option[Int64]`, which is
    // `Entity { functor: Symbol(37), pos: [], named: [(Symbol(171), Int(14))] }` — so a
    // bare `contains("2")` is satisfiable by a digit of an INTERNING ID and would pass
    // for a wrong answer under a different symbol numbering. `Int({want})` can only be
    // the payload. Found by `/code-review`; the ids above are this load's, and depending
    // on them is exactly what this avoids.
    for (op, want) in [("q", 14), ("m", 2), ("mn", 5)] {
        let got = drive(src, &format!("test.vt8cf.bdiv.{op}"));
        assert!(
            got.contains(&format!("Int({want})")),
            "BigInt `{op}` must be some({want}); got {got}. `mn` is the Euclidean row: \
             -100 rem 7 is -2, and `mod` lifts it to 5"
        );
    }
}

/// THE POLYMORPHISM ITSELF, and the row an `Int64`-only reading of this change cannot
/// produce: ONE generic body, `requires EuclideanDomain[T]`, run over TWO carriers
/// through a runtime dictionary. Nothing in the body names a carrier.
///
/// This is what "carrier-agnostic" means operationally, and it is unavailable in
/// principle when the tier points at a concrete carrier's operation — there is no spec
/// to `requires`.
#[test]
fn one_generic_body_divides_over_two_carriers() {
    let src = r#"
namespace test.vt8cf.generic
  import anthill.prelude.{Int64, BigInt, Option, EuclideanDomain}

  -- The divisor is a PARAMETER, so the guard is symbolic and the effect is threaded
  -- rather than discharged — which is itself the generic case working: one declaration
  -- covers both carriers, because both narrow the SAME spec-level guarded row.
  operation halve[T](x: T, two: T) -> T requires EuclideanDomain[T]
    effects Error[DivisionByZero] = x / two

  operation on_int() -> Int64 effects Error[DivisionByZero] = halve(7, 2)
  operation on_big() -> Option[T = Int64] effects Error[DivisionByZero] =
    BigInt.to_int(halve(BigInt.to_bigint(100), BigInt.to_bigint(7)))
end
"#;
    assert_eq!(
        drive(src, "test.vt8cf.generic.on_int"),
        "Int(3)",
        "the generic body dispatched to `Int64.div`"
    );
    let big = drive(src, "test.vt8cf.generic.on_big");
    assert!(
        big.contains("Int(14)"),
        "…and the SAME body dispatched to `BigInt.div` for a BigInt argument; got {big}. \
         `Int(14)` and not `14`, for the interning-id reason `bigint_division_now_exists` \
         states"
    );
}

/// THE DESIGN DECISION, PINNED BEHAVIOURALLY: `EuclideanDomain`'s division identity
/// `b * div(a, b) + rem(a, b) = a` pairs `div` with `rem` and NOT with `mod`, because the
/// library's `div` truncates while its `mod` is Euclidean — two different conventions, so
/// that pair satisfies no identity at all.
///
/// The row is written as the disagreement rather than as the law, so it cannot pass by
/// both sides being equal: if a later change makes `div` floored to "tidy up" the pair,
/// `with_mod` becomes -7 and this fails, which is the intended alarm — that change is a
/// deliberate flip of `-7 / 2` from -3 to -4 and needs its own decision.
#[test]
fn the_division_identity_holds_for_rem_and_not_for_mod() {
    let src = r#"
namespace test.vt8cf.euclid
  import anthill.prelude.{Int64}
  import anthill.prelude.Int64.{rem}
  operation with_rem() -> Int64 = 2 * (-7 / 2) + rem(-7, 2)
  operation with_mod() -> Int64 = 2 * (-7 / 2) + (-7 % 2)
end
"#;
    assert_eq!(
        drive(src, "test.vt8cf.euclid.with_rem"),
        "Int(-7)",
        "`b * div(a, b) + rem(a, b)` recovers `a` — the identity `euclid_div` states"
    );
    assert_eq!(
        drive(src, "test.vt8cf.euclid.with_mod"),
        "Int(-5)",
        "…and the `mod` pair does NOT, which is why the law is not written over it"
    );
}

/// THE PROVISION GRAPH, read off the loaded KB rather than off the source files: each
/// branch provides the base, so a carrier writes ONE row and cannot state the two
/// inconsistently, and `Float` is deliberately NOT a `EuclideanDomain` though every field
/// mathematically is one — that structure is degenerate (remainder identically 0) and is
/// not what `Float.fmod` computes.
#[test]
fn the_tower_is_wired_as_two_branches_over_one_base() {
    let kb = load_stdlib_kb();
    let provisions = sort_provisions(&kb);
    let has = |provider: &str, spec: &str| {
        provisions
            .iter()
            .any(|(p, s)| p.ends_with(provider) && s.ends_with(spec))
    };

    assert!(
        has("EuclideanDomain", "Divisible"),
        "`EuclideanDomain provides Divisible` — the chain that makes one carrier row \
         enough; got {provisions:?}"
    );
    assert!(
        has("Field", "Divisible"),
        "`Field provides Divisible` — the same, for the exact-division branch; got \
         {provisions:?}"
    );
    assert!(
        !has("Field", "EuclideanDomain"),
        "`Field` must NOT provide `EuclideanDomain`: the implication is true and useless \
         (remainder identically 0), and asserting it would owe every field a `mod` that \
         contradicts `Float.fmod`"
    );
}

/// `%` OVER FLOATS IS UNAVAILABLE, and WHEN you find out is a DIVERGENCE THIS TICKET
/// MOVED — recorded here rather than left to be rediscovered.
///
/// `Float` provides `Field`, not `EuclideanDomain`, so `mod` is not part of its surface
/// and `7.5 % 2.0` has no implementation to reach. It used to be a LOAD error
/// (`type mismatch in mod.a (op-arg): expected Int64, got Float`, because the tier
/// pointed at `Int64.mod`); it is now a RUN-TIME raise naming the missing operation.
///
/// THE CAUSE IS NOT IN THIS TICKET'S CODE. A spec-op call whose carrier binds CONCRETELY
/// and finds no provider is a deliberate pass-through — WI-325's `NoCandidates` arm,
/// "legitimate pass-through — host builtin / spec-derived rule may resolve at runtime" —
/// and it is what `Numeric` does too: a carrier providing `Numeric` without declaring
/// `mul` also loads clean and dies at run time. Narrowing that arm is a change to a
/// general typer mechanism with its own census to run, so this row PINS the behaviour
/// instead of hiding it, and the message it asserts is the loud one.
///
/// FAILS IF `mod` IS EVER MOVED DOWN TO `Divisible`, which would make this dispatch to a
/// member `Float` has no implementation for — the same death, one level less explicably.
#[test]
fn float_has_no_minted_modulo_but_does_have_fmod() {
    let bad = r#"
namespace test.vt8cf.fmodgap
  import anthill.prelude.{Float}
  operation drive() -> Float effects Error[DivisionByZero] = 7.5 % 2.0
end
"#;
    assert!(
        crate::common::try_load_kb_with(bad).is_ok(),
        "RECORDING THE DIVERGENCE: this LOADS today (WI-325 concrete pass-through), where \
         before this ticket it was a load error naming Int64"
    );
    let mut interp = interp_for(bad);
    let err = interp
        .call("test.vt8cf.fmodgap.drive", &[])
        .expect_err("…and it must RAISE rather than answer a number");
    let text = format!("{err:?}");
    assert!(
        text.contains("EuclideanDomain.mod"),
        "…naming the operation nothing implements for this carrier, so the author can \
         see that `Float` is not a Euclidean domain; got {text}"
    );

    let good = r#"
namespace test.vt8cf.ffmod
  import anthill.prelude.{Float}
  import anthill.prelude.Float.{fmod}
  operation drive() -> Float = fmod(7.5, 2.0)
end
"#;
    assert_eq!(
        drive(good, "test.vt8cf.ffmod.drive"),
        "Float(1.5)",
        "…and the IEEE remainder is reachable by its own name"
    );
}

/// THE GUARD-DISCHARGE σ IS PAIRED BY THE **SPEC** OP'S LABELS, NOT THE IMPL'S — a
/// correctness row for the `dispatched_impl_effects` half of this ticket's discharge fix,
/// found by `/code-review` after the first cut got it wrong.
///
/// The caller writes the SPEC operation's parameter names (it was matched against the
/// spec op), while the impl's guard names the IMPL's parameters — and an override may
/// RENAME them; parameters align positionally, not by name. So σ must pair impl param `i`
/// with the argument at position `i`, or, for a NAMED call, with the argument labelled
/// `spec_params[i]`. `dispatched_impl_effects`' own doc says exactly this, one line above
/// the loop.
///
/// The first cut called `build_call_guard_sigma(kb, &impl_op.params, …)`, which matches a
/// named argument's LABEL against the params it is handed — right where the call was
/// matched against those params, wrong here. Below, the impl renames `(a, b)` to `(x, y)`
/// and the call is written with the spec's labels, so no label matches an impl param: σ
/// comes out EMPTY, `eq(y, 0)` never grounds, and the literal `2` that plainly refutes it
/// keeps a spurious `Error[DivisionByZero]`.
///
/// BACKED OUT — swap `spec_params.get(i)` for `impl_op.params.get(i)` in that σ block —
/// this row fails with exactly that: "type mismatch in named_call.effects (op-effects):
/// expected declared: [], got undeclared effect: Error[T = DivisionByZero]". MEASURED,
/// not argued.
///
/// THE OTHER DIRECTION IS UNSOUND and is why this is a correctness row rather than a
/// precision one: with the impl's parameters PERMUTED rather than renamed, label-matching
/// binds the guard to the WRONG OPERAND, so a refutable literal on the wrong side DROPS an
/// effect that is really incurred. The rename case is the one that can be written as a
/// loading program, so it is the one driven here.
#[test]
fn the_guard_sigma_pairs_by_the_spec_ops_labels() {
    let src = r#"
namespace test.vt8cf.rename
  import anthill.prelude.{Int64}
  import anthill.prelude.PartialEq.{eq}

  sort Halver
    sort T = ?
    operation slice(a: T, b: Int64) -> T effects { Error[DivisionByZero] :- eq(b, 0) }
  end

  sort Box
    entity Box(v: Int64)
    -- The impl RENAMES both parameters, and its guard names its own `y`.
    operation slice(x: Box, y: Int64) -> Box
      effects { Error[DivisionByZero] :- eq(y, 0) } = Box(v: 1)
  end
  fact Halver[T = Box]

  -- A NAMED call, carrying the SPEC op's labels, with a literal second operand that
  -- refutes `eq(b, 0)` by ground evaluation. `named_call` declares NO effects, so the
  -- discharge is what makes it load.
  operation named_call() -> Box = Halver.slice(a: Box(v: 7), b: 2)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "a literal `b: 2` refutes the guard, so the dispatched impl's effect must be \
         DISCHARGED even though the impl renamed the parameter it names; got {errs:?}"
    );
}

/// A USER CARRIER GETS `+` FROM ONE `fact`, AND CANNOT YET GET `/` AT ALL — the
/// extensibility claim, driven from both sides, because the stdlib carriers cannot test
/// it: they are host-backed and exempt from checks a user sort must pass.
///
/// THE ADDITIVE HALF WORKS. `Money` declares its own `add` and asserts
/// `fact Numeric[T = Money]`; a minted `+` then reaches `Money.add` by the short-name
/// join, with no `operation_map` entry and no host registration. `700 + 25 = 725` off the
/// carrier's OWN field, so a dispatch that had fallen through to the host `numeric_add`
/// would type-error on an `Entity` rather than answer. Since WI-20260825-1WBZT the join
/// runs one hop further — `+` names `Additive.add` and `Numeric provides Additive[T = T]`
/// — and this row is unchanged in what it asserts, which is the point: the bundle still
/// bundles.
///
/// THE DIVISION HALF DOES NOT, and this row RECORDS that rather than leaving it to be
/// discovered. A user carrier cannot provide `EuclideanDomain` when its implementation
/// divides, because the effect declaration is a PINCER — measured, all four spellings:
///
///   effects Error[DivisionByZero]                      "must not widen" (unguarded is
///                                                       wider than the spec's guarded row)
///   effects { … :- eq(b, zero()) }                     "must not widen"
///   effects { … :- eq(b, zero) }                       "must not widen"
///   effects { … :- eq(b, Money(cents: 0)) }            "must not widen"
///   (no effects row at all)                            "undeclared effect" from the body
///
/// The coverage check compares the guard STRUCTURALLY against `Divisible.div`'s
/// `eq(b, 0)`, whose `0` is an `Int64` literal — and no spelling over a `Money` operand
/// can match it. So the tower is stdlib-only in practice: `Int64`, `BigInt` and `Float`
/// reach it because they are host carriers, not because a carrier in general can.
/// `each_branch_reaches_the_base_and_neither_reaches_the_other` below exercises only
/// those three, and this row is why that is not the same claim.
///
/// NOTHING REGRESSED — a user carrier could not divide before this ticket either, when
/// `/` meant `Int64.div` outright. What is new is that the tower now LOOKS extensible,
/// so the gap needs saying.
#[test]
fn a_user_carrier_gets_plus_but_cannot_yet_provide_the_division_tower() {
    let money_ops = r#"
    operation add(a: Money, b: Money) -> Money = Money(cents: a.cents + b.cents)
    operation sub(a: Money, b: Money) -> Money = Money(cents: a.cents - b.cents)
    -- MEANINGLESS, AND DECLARED ANYWAY — cents times cents is cents-SQUARED, which is
    -- not money. It is here because this fixture claims the WHOLE BUNDLE
    -- (`fact Numeric[T = Money]`), which is `Additive` + `Multiplicative` + a comparison
    -- surface: ten operations for one operator. That was the only way to get `+` until
    -- WI-20260825-1WBZT gave each operator its own syntax category — a carrier that only
    -- adds now writes `fact Additive[T = Money]` and owes four
    -- (`wi_1wbzt_syntax_category_test`). This row keeps the bundle spelling on purpose:
    -- it is the control that a carrier may STILL claim everything, so the split is a new
    -- option rather than a replacement, and the `plus` assertion below measures the
    -- dispatch through it either way.
    operation mul(a: Money, b: Money) -> Money = Money(cents: a.cents * b.cents)
    operation neg(a: Money) -> Money = Money(cents: 0 - a.cents)
    -- `zero` / `one` — the two identities the bundle's categories declare. `zero` was
    -- spelled `zero-val` until WI-20260825-1WBZT, which settled the additive identity on
    -- ONE name (`algebra.Ring` carried the other, `zero`); `one` had no `Numeric`
    -- counterpart before the split and is `Multiplicative`'s.
    operation zero() -> Money = Money(cents: 0)
    operation one() -> Money = Money(cents: 1)
    operation gt(a: Money, b: Money) -> Bool  = a.cents > b.cents
    operation gte(a: Money, b: Money) -> Bool = a.cents >= b.cents
    operation lt(a: Money, b: Money) -> Bool  = a.cents < b.cents
    operation lte(a: Money, b: Money) -> Bool = a.cents <= b.cents"#;

    let additive = format!(
        r#"
namespace test.vt8cf.money
  import anthill.prelude.{{Int64, Numeric, PartialOrd}}
  sort Money
    entity Money(cents: Int64){money_ops}
  end
  fact PartialOrd[T = Money]
  fact Numeric[T = Money]
  operation plus() -> Int64 = (Money(cents: 700) + Money(cents: 25)).cents
end
"#
    );
    assert_eq!(
        drive(&additive, "test.vt8cf.money.plus"),
        "Int(725)",
        "a minted `+` must reach the CARRIER's own `add` — 725 is `700 + 25` off its \
         field, where a fall-through to the host builtin would type-error on an Entity"
    );

    // …and every way of declaring the division half is refused. Each arm differs from the
    // others ONLY in the effects row, so the pincer is the measurement rather than one
    // unlucky spelling.
    for effects in [
        "effects Error[DivisionByZero]",
        "effects { Error[DivisionByZero] :- eq(b, zero()) }",
        "effects { Error[DivisionByZero] :- eq(b, Money(cents: 0)) }",
        "",
    ] {
        let src = format!(
            r#"
namespace test.vt8cf.moneydiv
  import anthill.prelude.{{Int64, Numeric, PartialOrd, EuclideanDomain}}
  sort Money
    entity Money(cents: Int64){money_ops}
    operation div(a: Money, b: Money) -> Money {effects} = Money(cents: a.cents / b.cents)
    operation mod(a: Money, b: Money) -> Money {effects} = Money(cents: a.cents % b.cents)
    operation rem(a: Money, b: Money) -> Money {effects} = Money(cents: Int64.rem(a.cents, b.cents))
  end
  fact PartialOrd[T = Money]
  fact Numeric[T = Money]
  fact EuclideanDomain[T = Money]
end
"#
        );
        let errs = crate::common::try_load_kb_with(&src).err().unwrap_or_default();
        assert!(
            !errs.is_empty(),
            "RECORDING THE GAP: a user carrier cannot provide `EuclideanDomain` under \
             `effects {effects:?}` either — if this now LOADS, the pincer is closed and \
             this row should become the positive test it wants to be"
        );
    }
}

/// THE TOWER AS A SEPARATING MATRIX — six programs, one `requires` clause apart, driven
/// through REQUIREMENT DISCHARGE rather than read off the provision facts.
///
/// This is the row that shows the shape is a tower and not three unrelated specs: both
/// branches reach the base, and NEITHER reaches the other.
///
///                    Int64      Float
///     Divisible      loads      loads       <- the `/` slot, reached through either branch
///     EuclideanDomain loads     REFUSED     <- Float has no `mod`; it is not one
///     Field          REFUSED    loads       <- truncated division has no inverse
///
/// The two refusals are what make it evidence. A `provides` chain that leaked in either
/// direction — or a `requires` that discharged by symbol rather than over the call's
/// carrier — turns one of them green, and the four positive rows alone would not notice:
/// they pass just as well if `Divisible` is provided by everything.
///
/// Stronger than `the_tower_is_wired_as_two_branches_over_one_base` below, which reads
/// the `SortProvidesInfo` facts. That one asserts what the library WROTE; this one asserts
/// what the typer DOES with it, which is the question a caller actually asks.
#[test]
fn each_branch_reaches_the_base_and_neither_reaches_the_other() {
    let program = |spec: &str, ty: &str, a: &str, b: &str| {
        format!(
            r#"
namespace test.vt8cf.matrix
  import anthill.prelude.{{Int64, Float, Divisible, Field, EuclideanDomain}}
  operation via[T](x: T, y: T) -> T requires {spec}[T]
    effects Error[DivisionByZero] = x / y
  operation drive() -> {ty} effects Error[DivisionByZero] = via({a}, {b})
end
"#
        )
    };
    let loads = |spec: &str, ty: &str, a: &str, b: &str| {
        crate::common::try_load_kb_with(&program(spec, ty, a, b)).is_ok()
    };

    for (spec, ty, a, b) in [
        ("Divisible", "Int64", "7", "2"),
        ("EuclideanDomain", "Int64", "7", "2"),
        ("Divisible", "Float", "10.0", "4.0"),
        ("Field", "Float", "10.0", "4.0"),
    ] {
        assert!(
            loads(spec, ty, a, b),
            "`requires {spec}[T]` must discharge over {ty} — the branch, or the base it \
             provides"
        );
    }
    assert!(
        !loads("Field", "Int64", "7", "2"),
        "`Field[Int64]` must NOT discharge: truncated division has no multiplicative \
         inverse, and this is half of what makes the four rows above evidence"
    );
    assert!(
        !loads("EuclideanDomain", "Float", "10.0", "4.0"),
        "`EuclideanDomain[Float]` must NOT discharge: Float has no `mod`, and every field \
         being trivially Euclidean is exactly the implication the library declines to write"
    );
}

/// THE PRICE OF ONE `div` SERVING TWO CARRIERS, pinned rather than left to surprise the
/// first person who writes `a / b` over floats.
///
/// The guarded `Error[DivisionByZero]` has to live on `Divisible.div`: an override may
/// NARROW a spec operation's effect row and never WIDEN it, so with no row on the spec
/// the four carriers that declare one are load errors. `Float.div` then narrows it to
/// nothing — which is why `1.0 / 0.0` is `+Infinity` and not a raise.
///
/// BUT THE NARROWING DOES NOT REACH THE CALL'S ROW. A dispatched call MERGES the impl's
/// effects into the spec op's rather than replacing them, so with a SYMBOLIC divisor —
/// where the guard `eq(b, 0)` cannot be refuted — a bare `a / b` over floats carries an
/// effect IEEE division can never raise, while the same division written `Float.div(a, b)`
/// is pure. Sound (an over-approximation), imprecise, and NOT specific to division: it is
/// how every dispatched spec op with a guarded effect behaves. Whether a resolved call
/// should take the impl's row or the union is a typer question with its own census to
/// run, so this row states the current answer instead of asserting the one we would
/// prefer.
///
/// A LITERAL DIVISOR IS UNAFFECTED, which is the second half and the reason this is a
/// wart and not a wall: `1.0 / 0.0` and `n / 2` both discharge.
#[test]
fn a_bare_float_division_over_approximates_its_effect_row() {
    let symbolic = r#"
namespace test.vt8cf.feff
  import anthill.prelude.{Float}
  operation bare(a: Float, b: Float) -> Float = a / b
end
"#;
    let errs = crate::common::try_load_kb_with(symbolic)
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("DivisionByZero")),
        "RECORDING THE OVER-APPROXIMATION: a bare `/` over floats takes the SPEC op's \
         guarded row, which a symbolic divisor cannot refute; got {errs:?}"
    );

    let qualified = r#"
namespace test.vt8cf.feffq
  import anthill.prelude.{Float}
  operation named(a: Float, b: Float) -> Float = Float.div(a, b)
end
"#;
    assert!(
        crate::common::try_load_kb_with(qualified).is_ok(),
        "…and naming the carrier's operation is pure, which is the separating row: the \
         difference is the SPELLING, not the arithmetic"
    );
}

/// The tier's two entries really are the spec operations — read off `load.rs`'s own
/// table rather than restated, so a future edit that repoints them cannot leave this
/// file's rows passing for the wrong reason. Guards the mechanism the whole ticket rests
/// on.
#[test]
fn the_implicit_tier_points_at_the_spec_operations() {
    let kb = load_stdlib_kb();
    assert!(
        anthill_core::kb::load::implicit_target_orphans(&kb).is_empty(),
        "every implicit target must be declared by the standard load"
    );
    let spec_names = anthill_core::kb::load::spec_operation_short_names(&kb);
    for name in ["div", "mod"] {
        assert!(
            spec_names.contains(name),
            "`{name}` must be a SPEC operation now — that is what puts it inside \
             `check_rival_spec_operations` with nothing added to that pass"
        );
    }
    // …and the control: `rem` is a member of the same spec, so it comes along; `fmod`
    // is `Float`'s alone and must NOT, or the tower would have absorbed an operation
    // that has no second carrier.
    assert!(
        spec_names.contains("rem"),
        "`rem` is an `EuclideanDomain` member and is a spec operation too"
    );
    assert!(
        !spec_names.contains("fmod"),
        "`fmod` stays `Float`'s own — no spec owns it, and inventing one for a single \
         carrier would assert a structure nothing satisfies"
    );
    let _ = Value::Int(0);
}
