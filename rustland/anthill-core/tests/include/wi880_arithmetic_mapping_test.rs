//! WI-880 — the ARITHMETIC families are keyed per carrier, and a host-realized
//! carrier owes each operation individually.
//!
//! WI-876 proved the mechanism on the ordering family and deliberately stopped there.
//! The hole was the same one family over: `eval/builtins.rs` registered
//! `anthill.prelude.Additive.add`/`sub`/`neg` and `Multiplicative.mul` by SPEC-OP
//! qualified name, so ONE host implementation was the backing for every carrier that
//! never wrote its own — and that implementation then had to TEST ITS OPERANDS to
//! discover which arithmetic it was being asked for.
//!
//! THE PRE-FIX MEASUREMENT, reproduced before the change on [`MONEY`] — a structural
//! `Numeric` carrier writing `add`, `neg`, `zero`, `mul`, `one` and the comparisons,
//! and no `sub`:
//!
//!   Additive.add(cents(700), cents(25))    ->  Ok(725)   -- its own member wins
//!   Additive.sub(cents(700), cents(25))    ->  Err(TypeMismatch { expected:
//!                        "matching Int, BigInt, or Float", got: "Entity" })
//!   Multiplicative.mul(cents(7), cents(5)) ->  Ok(35)
//!   Additive.neg(cents(700))               ->  Ok(-700)
//!
//! The program LOADED CLEAN — `op_backed`'s `kb.is_builtin` leg reads `sub`'s resolver
//! tag and certifies the spec op as backed for every provider — and then died in the
//! host scalar arithmetic. That is WI-876's defect A stated for arithmetic, and
//! `stdlib/anthill/prelude/arithmetic.anthill`'s own header had recorded it as live.
//!
//! WHAT THE FIX IS, in three parts:
//!
//!   1. `Int64` / `Float` / `BigInt` DECLARE `add`/`sub`/`mul` (and `BigInt` `neg`),
//!      body-less, because a host implementation must have a carrier to be keyed to;
//!      each binding block's `operation_map` names its own host function.
//!   2. `Additive.sub` gains the DEFAULT BODY `add(a, neg(b))` — the `sub_def` law,
//!      which could not be a body while a spec-op builtin shadowed it (measured:
//!      writing it changed nothing, the builtin still won).
//!   3. `check_provider_operations`' wholesale host-carrier skip is narrowed to a
//!      PER-OPERATION question, so an operation no host realizes is refused at load
//!      even on a carrier a host artifact backs.
//!
//! Reference: WI-876 (the mechanism), `docs/design/058-implementation.md` §10,
//! `stdlib/anthill/prelude/arithmetic.anthill`, `rustland/anthill-stl/anthill/*.anthill`.

use anthill_core::eval::Value;

/// A STRUCTURAL `Numeric` carrier. It writes every operation the spec cannot derive
/// and NOT ONE MORE — in particular no `sub`, which is the acceptance: the surface
/// has to come from the spec's own derivation over this carrier's `add` and `neg`.
///
/// `mul`/`one` are here because `Numeric` bundles `Multiplicative` and a
/// multiplicative monoid has an identity (`numeric.anthill`'s header). The four
/// comparisons are `PartialOrd`'s, which `Numeric` requires.
const MONEY: &str = r#"
namespace wi880.money
  import anthill.prelude.{Int64, Bool, Numeric, Additive, Multiplicative, PartialOrd, PartialEq}

  sort Money
    import anthill.prelude.{Int64, Bool, Numeric, Additive, Multiplicative, PartialOrd, PartialEq}
    entity cents(v: Int64)

    provides PartialEq[Money]
    provides PartialOrd[Money]
    provides Numeric[Money]

    operation eq(a: Money, b: Money) -> Bool =
      match a
        case cents(x) -> match b
          case cents(y) -> PartialEq.eq(x, y)
    operation gt(a: Money, b: Money) -> Bool =
      match a
        case cents(x) -> match b
          case cents(y) -> PartialOrd.gt(x, y)
    operation gte(a: Money, b: Money) -> Bool =
      match a
        case cents(x) -> match b
          case cents(y) -> PartialOrd.gte(x, y)
    operation lt(a: Money, b: Money) -> Bool =
      match a
        case cents(x) -> match b
          case cents(y) -> PartialOrd.lt(x, y)
    operation lte(a: Money, b: Money) -> Bool =
      match a
        case cents(x) -> match b
          case cents(y) -> PartialOrd.lte(x, y)

    -- The primitives, and only these. NO `sub`.
    operation add(a: Money, b: Money) -> Money =
      match a
        case cents(x) -> match b
          case cents(y) -> cents(Additive.add(x, y))
    operation neg(a: Money) -> Money =
      match a
        case cents(x) -> cents(Additive.neg(x))
    operation zero() -> Money = cents(0)
    operation mul(a: Money, b: Money) -> Money =
      match a
        case cents(x) -> match b
          case cents(y) -> cents(Multiplicative.mul(x, y))
    operation one() -> Money = cents(1)
  end

  sort Driver
    import anthill.prelude.{Int64, Additive, Multiplicative}
    import wi880.money.Money.{cents}
    operation addV(n: Int64) -> Int64 =
      match Additive.add(cents(700), cents(25))
        case cents(v) -> v
    -- THE ACCEPTANCE: `Money` has no `sub`, so this is `Additive.sub`'s default body
    -- running `Money.add` over `Money.neg`.
    operation subV(n: Int64) -> Int64 =
      match Additive.sub(cents(700), cents(25))
        case cents(v) -> v
    operation mulV(n: Int64) -> Int64 =
      match Multiplicative.mul(cents(7), cents(5))
        case cents(v) -> v
    operation negV(n: Int64) -> Int64 =
      match Additive.neg(cents(700))
        case cents(v) -> v
  end
end
"#;

/// Call several entries on ONE interpreter (the `wi876_operation_mapping_test` recipe:
/// each `interp_for` is a full stdlib parse-and-load, and every call here succeeds so
/// none can poison a later one).
fn eval_all(src: &str, entries: &[&str]) -> Vec<Value> {
    let mut interp = crate::common::interp_for(src);
    entries
        .iter()
        .map(|e| {
            interp
                .call(e, &[Value::Int(0)])
                .unwrap_or_else(|err| panic!("call {e}: {err:?}"))
        })
        .collect()
}

fn eval_one(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

fn as_int(v: &Value, why: &str) -> i64 {
    match v {
        Value::Int(n) => *n,
        other => panic!("{why}; got {other:?}"),
    }
}

fn as_bool(v: &Value, why: &str) -> bool {
    match v {
        Value::Bool(b) => *b,
        other => panic!("{why}; got {other:?}"),
    }
}

fn as_float(v: &Value, why: &str) -> f64 {
    match v {
        Value::Float(f) => *f,
        other => panic!("{why}; got {other:?}"),
    }
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

fn loads_clean(src: &str, why: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{why}; got load errors: {errs:?}");
    }
}

/// The harness reports breakage: an unknown sort must still fail to load, so
/// [`loads_clean`] below is a real assertion and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    load_errs(
        "\nnamespace wi880.control\n  \
         sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end\nend\n",
    );
}

// ── The acceptance ───────────────────────────────────────────────────

/// THE ACCEPTANCE: a structural `Numeric` carrier gets a working arithmetic surface
/// from its OWN primitives, with no per-carrier boilerplate beyond what the spec
/// cannot derive.
///
/// `subV` is the arm that measures the change — it is the one operation `Money` does
/// not write. Back the migration out (restore the four `register_if_present` lines on
/// `Additive`/`Multiplicative`) and it returns to the `TypeMismatch` in this file's
/// header, whether or not `Additive.sub` keeps its body: a spec-op builtin beats a
/// spec default body, which is why the body could not be written before.
///
/// The other three arms pass EITHER WAY and are here to bound the claim — they went
/// through `Money`'s own members before the change and go through them now, so a
/// reader does not credit the fix with more than the one row it moved.
#[test]
fn the_additive_surface_works_from_add_and_neg() {
    let v = eval_all(
        MONEY,
        &[
            "wi880.money.Driver.addV",
            "wi880.money.Driver.subV",
            "wi880.money.Driver.mulV",
            "wi880.money.Driver.negV",
        ],
    );
    assert_eq!(as_int(&v[0], "add, the carrier's own member"), 725);
    assert_eq!(
        as_int(&v[1], "sub, DERIVED by `Additive.sub`'s default body"),
        675
    );
    assert_eq!(as_int(&v[2], "mul, the carrier's own member"), 35);
    assert_eq!(as_int(&v[3], "neg, the carrier's own member"), -700);
}

/// A CARRIER'S OWN `sub` BEATS THE DERIVATION — the arm without which
/// [`the_additive_surface_works_from_add_and_neg`] cannot say which of two paths
/// answered.
///
/// `add(a, neg(b))` and an ordinary `sub` agree at every value, so a carrier that
/// writes a NORMAL `sub` separates nothing: both routes return the same number and the
/// test is green either way. [`SATURATING`]'s member disagrees on purpose — it clamps
/// at zero — so `Additive.sub(tally(3), tally(10))` answers `0` if the member ran and
/// `-7` if the spec's default body ran. Both values are asserted, from ONE fixture, so
/// the pair also shows the carrier's `add`/`neg` are reachable at all.
///
/// This matters beyond the fixture: the three SCALAR carriers each map their own `sub`,
/// and if the default body shadowed a carrier member then every `a - b` in the language
/// would cost an interpreter frame plus a `neg` where the host answers in one call —
/// the regression WI-876 avoided by mapping `Ord.max`/`min` per carrier rather than
/// letting the derivation stand. It cannot be measured ON `Int64` (nothing there can
/// disagree with itself), which is why the rule is driven on a carrier that can.
const SATURATING: &str = r#"
namespace wi880.saturating
  import anthill.prelude.{Int64, Bool, Numeric, Additive, Multiplicative, PartialOrd, PartialEq}

  sort Tally
    import anthill.prelude.{Int64, Bool, Numeric, Additive, Multiplicative, PartialOrd, PartialEq}
    entity tally(v: Int64)

    provides PartialEq[Tally]
    provides PartialOrd[Tally]
    provides Numeric[Tally]

    operation eq(a: Tally, b: Tally) -> Bool =
      match a
        case tally(x) -> match b
          case tally(y) -> PartialEq.eq(x, y)
    operation gt(a: Tally, b: Tally) -> Bool =
      match a
        case tally(x) -> match b
          case tally(y) -> PartialOrd.gt(x, y)
    operation gte(a: Tally, b: Tally) -> Bool =
      match a
        case tally(x) -> match b
          case tally(y) -> PartialOrd.gte(x, y)
    operation lt(a: Tally, b: Tally) -> Bool =
      match a
        case tally(x) -> match b
          case tally(y) -> PartialOrd.lt(x, y)
    operation lte(a: Tally, b: Tally) -> Bool =
      match a
        case tally(x) -> match b
          case tally(y) -> PartialOrd.lte(x, y)

    operation add(a: Tally, b: Tally) -> Tally =
      match a
        case tally(x) -> match b
          case tally(y) -> tally(Additive.add(x, y))
    operation neg(a: Tally) -> Tally =
      match a
        case tally(x) -> tally(Additive.neg(x))
    operation zero() -> Tally = tally(0)
    operation mul(a: Tally, b: Tally) -> Tally =
      match a
        case tally(x) -> match b
          case tally(y) -> tally(Multiplicative.mul(x, y))
    operation one() -> Tally = tally(1)

    -- DELIBERATELY NOT `add(a, neg(b))`: it clamps at zero. That disagreement is the
    -- whole instrument — the spec's default would answer -7 where this answers 0.
    operation sub(a: Tally, b: Tally) -> Tally =
      match a
        case tally(x) -> match b
          case tally(y) ->
            if PartialOrd.gte(x, y) then tally(Additive.sub(x, y)) else tally(0)
  end

  sort Drive
    import anthill.prelude.{Int64, Additive}
    import wi880.saturating.Tally.{tally}
    -- 3 - 10: the member clamps to 0, the derivation would answer -7.
    operation clamped(n: Int64) -> Int64 =
      match Additive.sub(tally(3), tally(10))
        case tally(v) -> v
    -- 10 - 3: both routes answer 7, so this row says the carrier is not simply broken.
    operation ordinary(n: Int64) -> Int64 =
      match Additive.sub(tally(10), tally(3))
        case tally(v) -> v
  end
end
"#;

#[test]
fn a_carriers_own_sub_beats_the_spec_derivation() {
    let v = eval_all(
        SATURATING,
        &[
            "wi880.saturating.Drive.clamped",
            "wi880.saturating.Drive.ordinary",
        ],
    );
    assert_eq!(
        as_int(&v[0], "3 - 10 through the CARRIER's own clamping `sub`"),
        0,
        "the carrier's own member must win; `Additive.sub`'s default body would \
         answer -7 here, which is what makes this row an instrument and not a tautology",
    );
    assert_eq!(
        as_int(&v[1], "10 - 3, where the two routes agree"),
        7,
        "the control: this value is the same either way, so it says the carrier works \
         and says nothing about which route ran",
    );
}

// ── The mechanism: one key per (carrier, operation) ──────────────────

/// The arithmetic reaches the runtime as `anthill.realization.OperationMapping` facts,
/// one per (carrier, operation) — and the SPEC ops carry none.
///
/// Asserted on the facts and not on "the arithmetic works", because the arithmetic
/// would also work if the registrations had quietly stayed on the spec op. That is
/// the defect, and it is invisible from the answers.
#[test]
fn the_arithmetic_is_mapped_per_carrier_and_the_spec_ops_are_not() {
    let kb = crate::common::load_kb_with("\nnamespace wi880.facts\n  sort S\n  end\nend\n");
    let host_fn = |op_qn: &str| -> String {
        kb.host_op_mappings()
            .iter()
            .find(|m| m.op_qn == op_qn && m.lang == "rust")
            .unwrap_or_else(|| panic!("no rust mapping for {op_qn}"))
            .host_fn
            .clone()
    };
    // THREE CARRIERS, THREE FUNCTIONS, per operation. A table that had collapsed to
    // one entry per operation would show the same `host_fn` down a column.
    assert_eq!(host_fn("anthill.prelude.Int64.add"), "int_add");
    assert_eq!(host_fn("anthill.prelude.Float.add"), "float_add");
    assert_eq!(host_fn("anthill.prelude.BigInt.add"), "bigint_add");
    assert_eq!(host_fn("anthill.prelude.Int64.sub"), "int_sub");
    assert_eq!(host_fn("anthill.prelude.Float.sub"), "float_sub");
    assert_eq!(host_fn("anthill.prelude.BigInt.sub"), "bigint_sub");
    assert_eq!(host_fn("anthill.prelude.Int64.mul"), "int_mul");
    assert_eq!(host_fn("anthill.prelude.Float.mul"), "float_mul");
    assert_eq!(host_fn("anthill.prelude.BigInt.mul"), "bigint_mul");
    // `neg` was already carrier-keyed for `Int64`/`Float` — by a HARDCODED qualified
    // name, which is WI-884's split. It rides the same channel as its siblings now,
    // and `BigInt` gains the member it never had (`numeric_neg` on the spec op used
    // to cover it by testing the operand).
    assert_eq!(host_fn("anthill.prelude.Int64.neg"), "int_neg");
    assert_eq!(host_fn("anthill.prelude.Float.neg"), "float_neg");
    assert_eq!(host_fn("anthill.prelude.BigInt.neg"), "bigint_neg");

    let sym = |qn: &str| {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("no symbol {qn}"))
    };
    for spec_op in [
        "anthill.prelude.Additive.add",
        "anthill.prelude.Additive.sub",
        "anthill.prelude.Additive.neg",
        "anthill.prelude.Multiplicative.mul",
    ] {
        assert!(
            !kb.is_host_mapped_op(sym(spec_op)),
            "{spec_op} carries no host implementation — that keying IS the defect",
        );
    }
}

/// THE THREE CARRIERS ARE THREE DIFFERENT OPERATIONS, and the overflow column is
/// where they stop agreeing. This is the argument for keying them apart rather than
/// branching on the operand carrier inside one function, driven rather than asserted.
///
/// `Int64` RAISES, `Float` SATURATES to an infinity, `BigInt` cannot overflow. Under
/// the old shared registration all three were reached through one `numeric_add`, and
/// the arm it took was chosen by testing the values.
#[test]
fn the_three_carriers_disagree_at_the_boundary() {
    const BOUNDARY: &str = r#"
namespace wi880.boundary
  sort Probe
    import anthill.prelude.{Int64, Float, BigInt, Bool}
    import anthill.prelude.Int64.{maxValue}
    -- i64::MAX + 1: the checked arithmetic has no answer.
    operation intOverflow(n: Int64) -> Int64 = Int64.add(Int64.maxValue(), 1)
    -- The same sum in an unbounded carrier: an answer, and the right one.
    operation bigOk(n: Int64) -> Bool =
      BigInt.gt(BigInt.add(BigInt.to_bigint(Int64.maxValue()), BigInt.to_bigint(1)),
                BigInt.to_bigint(Int64.maxValue()))
    -- IEEE: 1e308 + 1e308 overflows f64 and SATURATES rather than raising. Built with
    -- `pow` because the grammar has no exponent literal.
    operation floatSaturates(n: Int64) -> Bool =
      Float.isInfinite(Float.add(Float.pow(10.0, 308.0), Float.pow(10.0, 308.0)))
  end
end
"#;
    // THE OP NAME IS ASSERTED, not just the variant. `Err(Overflow { .. })` passes
    // whatever the label says, and the label is half of what the per-carrier split buys
    // — the wrappers delegated to the shared arithmetic with no label at first, so this
    // raised `op: "Numeric.add"`, naming a spec operation the ticket had just stopped
    // implementing. /code-review found it; a variant-only assertion could not.
    let overflow = eval_one(BOUNDARY, "wi880.boundary.Probe.intOverflow");
    assert!(
        matches!(
            overflow,
            Err(anthill_core::eval::EvalError::Overflow { op: "Int64.add" })
        ),
        "`Int64.add` is CHECKED — i64::MAX + 1 raises, naming Int64's own operation; \
         got {overflow:?}",
    );
    let v = eval_all(
        BOUNDARY,
        &[
            "wi880.boundary.Probe.bigOk",
            "wi880.boundary.Probe.floatSaturates",
        ],
    );
    assert!(
        as_bool(&v[0], "BigInt.add answers"),
        "`BigInt.add` is UNBOUNDED — the same sum has an answer",
    );
    assert!(
        as_bool(&v[1], "Float.add answers"),
        "`Float.add` is IEEE — it saturates to an infinity rather than raising",
    );
}

/// THE SCALAR CONTROL: the arithmetic every program in the tree already used still
/// answers, through all three carriers and through both the minted operator and the
/// qualified call. Every one of these moved from a spec-op registration to a
/// per-carrier one, so a carrier left behind would die or take the wrong route.
#[test]
fn the_scalar_arithmetic_is_unchanged() {
    const SCALARS: &str = r#"
namespace wi880.scalars
  sort Probe
    import anthill.prelude.{Int64, Float, BigInt, Bool, PartialEq}
    operation intPlus(n: Int64) -> Int64 = 40 + 2
    operation intMinus(n: Int64) -> Int64 = 50 - 8
    operation intTimes(n: Int64) -> Int64 = 6 * 7
    operation intNeg(n: Int64) -> Int64 = Int64.neg(42)
    operation floatPlus(n: Int64) -> Float = 1.5 + 2.25
    operation floatTimes(n: Int64) -> Float = 1.5 * 2.0
    operation bigPlus(n: Int64) -> Bool =
      PartialEq.eq(BigInt.add(BigInt.to_bigint(40), BigInt.to_bigint(2)),
                   BigInt.to_bigint(42))
    operation bigNeg(n: Int64) -> Bool =
      PartialEq.eq(BigInt.neg(BigInt.to_bigint(42)),
                   BigInt.sub(BigInt.to_bigint(0), BigInt.to_bigint(42)))
  end
end
"#;
    let v = eval_all(
        SCALARS,
        &[
            "wi880.scalars.Probe.intPlus",
            "wi880.scalars.Probe.intMinus",
            "wi880.scalars.Probe.intTimes",
            "wi880.scalars.Probe.intNeg",
            "wi880.scalars.Probe.floatPlus",
            "wi880.scalars.Probe.floatTimes",
            "wi880.scalars.Probe.bigPlus",
            "wi880.scalars.Probe.bigNeg",
        ],
    );
    assert_eq!(as_int(&v[0], "40 + 2"), 42);
    assert_eq!(as_int(&v[1], "50 - 8"), 42);
    assert_eq!(as_int(&v[2], "6 * 7"), 42);
    assert_eq!(as_int(&v[3], "Int64.neg(42)"), -42);
    assert_eq!(as_float(&v[4], "1.5 + 2.25"), 3.75);
    assert_eq!(as_float(&v[5], "1.5 * 2.0"), 3.0);
    assert!(as_bool(&v[6], "BigInt addition"));
    assert!(as_bool(&v[7], "BigInt negation"));
}

// ── The load check: backing is a per-OPERATION question ──────────────

/// A carrier a host artifact realizes still owes each operation INDIVIDUALLY.
///
/// `check_provider_operations` used to skip a carrier that is any
/// `Implementation.target` WHOLESALE — "it is a host carrier, so assume every
/// operation is backed", which is a claim about the CARRIER answering a question
/// asked about an OPERATION. MEASURED before the narrowing: this program LOADED
/// CLEAN, with `compare` body-less, unmapped and implemented nowhere. So
/// `op_is_executable`'s host-mapping leg was correct by construction and reached by
/// nothing, and `docs/kernel-language.md` said as much.
///
/// BACK THE NARROWING OUT (restore the `host_targets.contains` early `continue`) and
/// this test fails while [`a_host_carrier_owes_only_what_no_host_realizes`] still
/// passes — the pair separates the two directions.
#[test]
fn a_host_carrier_still_owes_an_operation_no_host_realizes() {
    let errs = load_errs(&unbacked_widget(""));
    assert!(
        errs.iter()
            .any(|e| e.contains("backs no operation") && e.contains("compare")),
        "the unmapped, body-less `compare` is refused; got {errs:?}",
    );
}

/// …AND OWES NOTHING MORE. The same carrier with the SAME body-less `compare`, given
/// an `operation_map` entry, loads clean — the operation is realized, the load check
/// can see it, and this is the path `op_is_executable`'s mapping leg was written for.
///
/// This is the control for the arm above: it holds the carrier, the provisions and
/// the body-less declaration fixed and varies ONLY the mapping, so a refusal that had
/// really been about (say) the entity or the `Ord` chain would fail here too.
#[test]
fn a_host_carrier_owes_only_what_no_host_realizes() {
    loads_clean(
        &unbacked_widget("operation_map { compare: \"ordered_compare\" }"),
        "a MAPPED body-less operation is backed",
    );
}

/// The same program built two ways — `clause` is the binding block's body beyond its
/// artifact. Shared so the two arms above cannot drift apart into measuring different
/// programs.
fn unbacked_widget(clause: &str) -> String {
    format!(
        r#"
namespace wi880.widget
  import anthill.prelude.{{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}}

  sort Widget
    import anthill.prelude.{{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}}
    entity widget(v: Int64)

    provides PartialEq[Widget]
    provides Eq[Widget]
    provides PartialOrd[Widget]
    provides Ord[Widget]

    operation eq(a: Widget, b: Widget) -> Bool =
      match a
        case widget(x) -> match b
          case widget(y) -> PartialEq.eq(x, y)

    -- Declared and body-less. Whether anything implements it is exactly the question.
    operation compare(a: Widget, b: Widget) -> Int64
  end

  provides Widget language rust
    artifact "rustland/anthill-stl/src/prelude/int.rs"
    {clause}
  end
end
"#
    )
}

/// A SPEC-LEVEL mapping backs a host-realized carrier, and no other.
///
/// The two rules meet here. `op_backed` refuses a host mapping on the SPEC's own
/// member in general (WI-931): `is_host_mapped_op` is a flat set with no carrier
/// dimension, so counting it would certify every carrier of the spec the moment one
/// `operation_map` named the member — WI-876's defect A. But the wholesale skip this
/// ticket narrowed was doing exactly that job for the genuinely polymorphic case, and
/// dropping it outright loses it: `anthill.persistence.filesystem.FileStore` and its
/// two siblings map `retract`/`update`/`retrieve` ONCE on the spec, because each is
/// one rust function that resolves the store VALUE to its registered mirror and there
/// is no per-backend function to name.
///
/// `host_realized` IS the missing carrier dimension — an `Implementation` fact naming
/// this carrier — so the leg is offered to `FileStore` and withheld from a carrier
/// that merely claims the spec. MEASURED on the first cut of the narrowing: with the
/// leg absent, the three filesystem backends produce seven `UnbackedProviderOperation`
/// errors and the stdlib stops loading.
#[test]
fn a_spec_level_mapping_backs_a_host_realized_carrier_and_no_other() {
    // The shipped backends load — the leg is live.
    loads_clean(
        "\nnamespace wi880.stores\n  sort S\n  end\nend\n",
        "the filesystem stores' spec-level mappings back them",
    );
    // …and an arbitrary entity claiming the same spec does NOT get them. This is
    // WI-931's own measurement, which the narrowing must not undo.
    let errs = load_errs(
        r#"
namespace wi880.notastore
  import anthill.prelude.{Int64}
  import anthill.persistence.{NonMonotonicStore}
  sort ZzNotAStore
    import anthill.prelude.{Int64}
    entity zzNotAStore(v: Int64)
  end
  fact NonMonotonicStore[ZzNotAStore]
end
"#,
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("backs no operation") && e.contains("retract")),
        "an entity with no `Implementation` fact is not offered the spec mapping; \
         got {errs:?}",
    );
}
