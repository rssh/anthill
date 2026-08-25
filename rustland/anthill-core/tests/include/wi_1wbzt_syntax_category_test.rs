//! WI-20260825-1WBZT — EVERY OPERATOR NAMES ITS OWN SYNTAX CATEGORY: a spec owning
//! exactly the operation that operator mints.
//!
//! ## What changed, and why it is a library change rather than a guard
//!
//! `+` minted a bare `add`, and the implicit tier (`PRELUDE_QUALIFIED`, kb/load.rs) maps
//! one short name to exactly ONE qualified name — which was `anthill.prelude.Numeric.add`.
//! `Numeric` is a BUNDLE: it declared `add`, `sub`, `mul`, `neg`, `zero-val` and
//! `requires PartialOrd[T]`, which declares four comparisons. So a carrier that only
//! ADDS had to claim nine operations to get one operator, and for `Money(cents: Int64)`
//! one of them is a lie — cents times cents is cents-squared, which is not money. The
//! author's two options were both bad, and both were driven: implement the lie, or omit
//! `mul`, which loads and runs clean and then dies at run time on `Money * Money`.
//!
//! `stdlib/anthill/prelude/arithmetic.anthill` splits the categories out and `Numeric`
//! reaches them by `provides`, which is what makes the third option — claim `Additive`
//! alone — expressible:
//!
//!   Additive        add, sub, neg, zero;  add_comm / add_assoc / add_identity /
//!                                          sub_def / neg_def
//!   Multiplicative  mul, one;             mul_assoc / mul_identity
//!     `-- Numeric       provides both;  + requires PartialOrd[T];  declares NOTHING
//!     `-- algebra.Ring  provides both;  + mul_comm / distrib;      declares NOTHING
//!
//! ## The back-out these rows are stated against
//!
//! Restore `numeric.anthill`'s five declarations and `algebra.Ring`'s five, delete
//! `arithmetic.anthill`, and repoint `PRELUDE_QUALIFIED` / `register_builtin_tags` /
//! `register_stdlib_scopes` at `Numeric.{add,sub,mul,neg}`. Every row here that names
//! `Additive` or `Multiplicative` fails. `the_bundle_still_bundles` passes either way BY
//! DESIGN and is here for exactly that reason: it is what says the split ADDED an option
//! rather than moving the cost around.

use crate::common::{interp_for, load_stdlib_kb, sort_provisions, try_load_kb_with};

/// The `Money` carrier the ticket was measured on, in its HONEST spelling: it adds,
/// subtracts and negates, it has a zero, and it says nothing about multiplication or
/// order. Four operations, one `fact`.
const MONEY_ADDITIVE: &str = r#"
namespace test.wbzt.money
  import anthill.prelude.{Int64, Additive}
  sort Money
    entity Money(cents: Int64)
    operation add(a: Money, b: Money) -> Money = Money(cents: a.cents + b.cents)
    operation sub(a: Money, b: Money) -> Money = Money(cents: a.cents - b.cents)
    operation neg(a: Money) -> Money = Money(cents: 0 - a.cents)
    operation zero() -> Money = Money(cents: 0)
  end
  fact Additive[T = Money]
  operation plus() -> Int64 = (Money(cents: 700) + Money(cents: 25)).cents
  operation minus() -> Int64 = (Money(cents: 700) - Money(cents: 25)).cents
end
"#;

/// Call `qn` in a stdlib-backed interpreter and render the result.
fn drive(src: &str, qn: &str) -> String {
    let mut interp = interp_for(src);
    let got = interp
        .call(qn, &[])
        .unwrap_or_else(|e| panic!("{qn} must evaluate: {e:?}"));
    format!("{got:?}")
}

/// THE TICKET'S CONTROL, AND THE ROW THAT COULD NOT PASS BEFORE IT.
///
/// A carrier that claims `Additive` and NOTHING else gets a working minted `+` and `-`.
/// Backed out, `fact Additive[T = Money]` names nothing — `Additive` does not exist —
/// and the only way to the operator is `fact Numeric[T = Money]`, which drags in `mul`
/// and, through `requires PartialOrd[T]`, four comparisons.
///
/// Driven through VALUES rather than through "it loads": 725 and 675 are computed off the
/// carrier's OWN `cents` field, so a dispatch that fell through to the host `numeric_add`
/// would answer "expected matching Int, BigInt, or Float, got Entity" instead of a number.
#[test]
fn a_carrier_that_only_adds_gets_plus_from_one_fact() {
    assert_eq!(
        drive(MONEY_ADDITIVE, "test.wbzt.money.plus"),
        "Int(725)",
        "a minted `+` must reach the CARRIER's own `add` off one `fact Additive`"
    );
    assert_eq!(
        drive(MONEY_ADDITIVE, "test.wbzt.money.minus"),
        "Int(675)",
        "and `-` the carrier's own `sub` — the same category, so one claim buys both"
    );
}

/// AND IT CLAIMS NOTHING IT DOES NOT MEAN. The same carrier declares no `mul`, no
/// comparison, and asserts no `Numeric` — measured off the provision facts rather than
/// off the source text, because the question is what the KB believes.
///
/// This is the half that makes the row above worth having. Without it, "a carrier gets
/// `+`" is satisfied just as well by the old bundle.
#[test]
fn and_the_carrier_claims_nothing_else() {
    let (kb, _) = crate::common::load_stdlib_kb_with_source(MONEY_ADDITIVE);
    let mine: Vec<String> = sort_provisions(&kb)
        .into_iter()
        .filter(|(carrier, _)| carrier == "test.wbzt.money.Money")
        .map(|(_, spec)| spec)
        .collect();
    assert!(
        mine.contains(&"anthill.prelude.Additive".to_string()),
        "the carrier must provide `Additive`; got {mine:?}"
    );
    for unclaimed in [
        "anthill.prelude.Numeric",
        "anthill.prelude.Multiplicative",
        "anthill.prelude.PartialOrd",
    ] {
        assert!(
            !mine.contains(&unclaimed.to_string()),
            "claiming `Additive` must NOT drag in {unclaimed} — that is the bundle this \
             ticket split; got {mine:?}"
        );
    }
}

/// WHAT THE CARRIER OWES, EXACTLY — measured by omitting one operation at a time, because
/// "four operations" is a claim about the LOADER and not about the declaration list.
///
/// Two of the four are demanded and two are not, and the split is NOT a property of the
/// operations: `add` and `sub` carry resolver builtins (`BuiltinTag::Add` / `Sub`) and
/// the backing check reads a builtin as backing. That is WI-876's finding on
/// `gt`/`lt`/`gte`/`lte`, still live for arithmetic until WI-880 moves the arithmetic
/// families into each carrier's `operation_map`. Recorded here so the four-operation
/// claim is not read as four load-time demands.
///
/// FAILS IF `Additive` gains or loses a bodyless member: the demanded set moves and this
/// row names which. It is also what would catch a default body added to `sub` — the
/// `sub` line would stay "loads" for the wrong reason, but `arithmetic.anthill`'s note
/// says why that body cannot run yet.
#[test]
fn the_loader_demands_the_two_operations_no_builtin_backs() {
    let carrier = |omit: &str| {
        let member = |name: &str, decl: &str| {
            if name == omit {
                String::new()
            } else {
                format!("    {decl}\n")
            }
        };
        format!(
            r#"
namespace test.wbzt.omit
  import anthill.prelude.{{Int64, Additive}}
  sort Money
    entity Money(cents: Int64)
{}{}{}{}  end
  fact Additive[T = Money]
end
"#,
            member(
                "add",
                "operation add(a: Money, b: Money) -> Money = Money(cents: a.cents + b.cents)"
            ),
            member(
                "sub",
                "operation sub(a: Money, b: Money) -> Money = Money(cents: a.cents - b.cents)"
            ),
            member("neg", "operation neg(a: Money) -> Money = Money(cents: 0 - a.cents)"),
            member("zero", "operation zero() -> Money = Money(cents: 0)"),
        )
    };
    for (omit, demanded) in [
        ("neg", true),
        ("zero", true),
        ("add", false),
        ("sub", false),
        ("", false), // the all-four control: it must load CLEAN, or the four rows
                     // above are measuring some unrelated defect in the fixture
    ] {
        let errs = try_load_kb_with(&carrier(omit))
            .map(|_| Vec::new())
            .unwrap_or_else(|e| e);
        if demanded {
            assert!(
                errs.iter().any(|e| e
                    .contains(&format!("backs no operation 'anthill.prelude.Additive.{omit}'"))),
                "omitting `{omit}` must be a LOAD error NAMING it — the message is the \
                 assertion, because a load error for any other reason would read as this \
                 one; got {errs:?}"
            );
        } else {
            // NOT "no error mentioning `{omit}`": the whole load must be clean, or
            // `add`/`sub` could be silently demanded under a different sentence.
            assert!(
                errs.is_empty(),
                "omitting `{omit}` must load CLEAN — `add` and `sub` carry resolver \
                 builtins, which the backing check reads as backing; got {errs:?}"
            );
        }
    }
}

/// THE BUNDLE STILL BUNDLES — the second control, and it passes BOTH WAYS by design.
///
/// `Int64` keeps its single `provides Numeric[T = Int64]` in
/// `anthill-stl/anthill/int64.anthill` — no row anywhere names `Additive` or
/// `Multiplicative` for it — and every operator still answers. That is the `provides`
/// direction working: a conversion in the chain, so the four existing providers
/// (`anthill-stl` int64 / bigint / float, `anthill-cpp-gen` int64) needed no edit.
///
/// It is here because the rows above would be satisfied by a split that BROKE the
/// bundle, and that is the failure this change could plausibly have.
#[test]
fn the_bundle_still_bundles() {
    let src = r#"
namespace test.wbzt.bundle
  import anthill.prelude.{Int64, Float, Bool}
  operation a() -> Int64 = 1 + 2
  operation s() -> Int64 = 7 - 2
  operation m() -> Int64 = 6 * 7
  operation d() -> Int64 = 7 / 2
  operation r() -> Int64 = 7 % 2
  operation c() -> Bool  = 1 < 2
  operation f() -> Float = 10.0 / 4.0
end
"#;
    for (op, want) in [
        ("a", "Int(3)"),
        ("s", "Int(5)"),
        ("m", "Int(42)"),
        ("d", "Int(3)"),
        ("r", "Int(1)"),
        ("c", "Bool(true)"),
        ("f", "Float(2.5)"),
    ] {
        assert_eq!(
            drive(src, &format!("test.wbzt.bundle.{op}")),
            want,
            "`{op}` must still be {want}: one `provides Numeric[T = Int64]` reaches \
             every category through the chain"
        );
    }
}

/// ONE DECLARATION PER SHORT NAME — the half of the rule that is a RESOLUTION constraint
/// rather than a taste, asserted at the addresses themselves.
///
/// `Numeric.add` and `algebra.Ring.add` were two DIFFERENT operations under one spelling;
/// the additive identity was worse, carried as `Numeric.zero-val` and `Ring.zero`, which
/// do not collide and so were never diagnosed. The tier maps one short name to one
/// qualified name, and a carrier providing two specs that both declare `add` gets two
/// `sort_ops` entries whose winner is HashMap-iteration order.
///
/// The ABSENCE half is what makes this a test: without it the row passes on a KB where
/// the old declarations are back beside the new ones, which is the state a careless
/// merge restores.
#[test]
fn each_arithmetic_short_name_is_declared_exactly_once() {
    let kb = load_stdlib_kb();
    for declared in [
        "anthill.prelude.Additive.add",
        "anthill.prelude.Additive.sub",
        "anthill.prelude.Additive.neg",
        "anthill.prelude.Additive.zero",
        "anthill.prelude.Multiplicative.mul",
        "anthill.prelude.Multiplicative.one",
    ] {
        assert!(
            kb.try_resolve_symbol(declared).is_some(),
            "the category must DECLARE {declared}"
        );
    }
    for gone in [
        "anthill.prelude.Numeric.add",
        "anthill.prelude.Numeric.sub",
        "anthill.prelude.Numeric.mul",
        "anthill.prelude.Numeric.neg",
        "anthill.prelude.Numeric.zero-val",
        "anthill.prelude.algebra.Ring.add",
        "anthill.prelude.algebra.Ring.sub",
        "anthill.prelude.algebra.Ring.mul",
        "anthill.prelude.algebra.Ring.zero",
        "anthill.prelude.algebra.Ring.one",
    ] {
        assert!(
            kb.try_resolve_symbol(gone).is_none(),
            "{gone} must NOT be a second declaration of a name a category owns — the \
             bundles reach it by `provides`"
        );
    }
}

/// THE TIER'S TARGETS ARE ALL LIVE, and the four arithmetic names are still SPEC
/// operations after the move.
///
/// A tier entry whose target is not loaded resolves to nothing and the name silently
/// stops resolving (`implicit_target_orphans`, WI-900) — a rename of a stdlib operation
/// does not fail loudly, it makes a rule head spelled that way start INTRODUCING the name
/// instead of referencing it. So this is the row that would have caught repointing
/// `PRELUDE_QUALIFIED` at `Additive` without the stdlib declaring it, or the reverse.
///
/// `spec_operation_short_names` is the second half: `add`/`sub`/`mul`/`neg` must still be
/// SPEC operations, which is what keeps them inside `check_rival_spec_operations` — the
/// refusal `wi_bfb9a_rival_spec_operation_test` counts. The move was between two
/// PARAMETRIC carriers, so nothing there had to change, and this row is what says so.
#[test]
fn the_implicit_tier_points_at_the_syntax_categories() {
    let kb = load_stdlib_kb();
    assert!(
        anthill_core::kb::load::implicit_target_orphans(&kb).is_empty(),
        "no tier target may be an orphan — an orphaned entry stops resolving SILENTLY"
    );
    let spec_names = anthill_core::kb::load::spec_operation_short_names(&kb);
    for name in ["add", "sub", "mul", "neg"] {
        assert!(
            spec_names.contains(name),
            "`{name}` must still be a SPEC operation after moving to its category — that \
             is what keeps it inside `check_rival_spec_operations`"
        );
    }
    // …and the control: `zero` and `one` are members of the same two specs, so they come
    // along as spec operations too, while `pow` — `Float`'s alone, with no category by
    // WI-20260824-VT8CF's decision — must NOT.
    for name in ["zero", "one"] {
        assert!(
            spec_names.contains(name),
            "`{name}` is a category member and is a spec operation too"
        );
    }
    assert!(
        !spec_names.contains("pow"),
        "`pow` stays `Float`'s own — `^` gets no category, because the rule is a category \
         per operator that HAS one, not a spec invented so the table looks uniform"
    );
}

/// THE CHAIN IS THE WIRING, driven through REQUIREMENT DISCHARGE rather than read off the
/// provision facts — the shape `wi_vt8cf_division_tower_test` uses for the division tower.
///
///                            Int64      Money (Additive only)
///     requires Additive       loads      loads     <- Int64 reaches it ONLY through Numeric
///     requires Multiplicative loads      REFUSED   <- Money declares no `mul` and claims none
///     requires Numeric        loads      REFUSED   <- and no comparison surface either
///
/// THE BODY HAS TO USE THE CATEGORY'S OPERATOR or the row measures nothing: with a body
/// of `= x` all six cells LOAD, because a requirement nothing reads is never asked at the
/// call site. Measured — that was this test's first shape and it was green in every cell.
///
/// THE ROWS THEREFORE DO NOT SHARE ONE BODY, since `Additive` and `Multiplicative` have no
/// operation in common, and a matrix whose cells differ in two places cannot attribute a
/// verdict. THE SEPARATOR IS THE FOURTH ROW: `requires Numeric[T]` with the body `x + y`
/// — byte for byte the `Additive` row's body, so `Money` can supply everything the body
/// READS — and it is REFUSED. That isolates the `requires` clause as the cause and leaves
/// the body out of it.
///
/// The refusals are what make this evidence. A `provides` chain that leaked, or a
/// `requires` that discharged by symbol rather than over the call's carrier, turns them
/// green, and the positive cells alone would not notice — they pass just as well if
/// everything provides everything.
#[test]
fn the_chain_discharges_for_int64_and_stops_at_the_category_money_claimed() {
    const MONEY_DECL: &str = r#"
  sort Money
    entity Money(cents: Int64)
    operation add(a: Money, b: Money) -> Money = Money(cents: a.cents + b.cents)
    operation sub(a: Money, b: Money) -> Money = Money(cents: a.cents - b.cents)
    operation neg(a: Money) -> Money = Money(cents: 0 - a.cents)
    operation zero() -> Money = Money(cents: 0)
  end
  fact Additive[T = Money]"#;
    let loads = |spec: &str, body: &str, money: bool| {
        let (decl, ty, arg) = if money {
            (MONEY_DECL, "Money", "Money(cents: 1)")
        } else {
            ("", "Int64", "1")
        };
        let src = format!(
            r#"
namespace test.wbzt.matrix
  import anthill.prelude.{{Int64, Additive, Multiplicative, Numeric}}
{decl}
  operation via[T](x: T, y: T) -> T requires {spec}[T] = {body}
  operation drive() -> {ty} = via({arg}, {arg})
end
"#
        );
        try_load_kb_with(&src).is_ok()
    };

    for (spec, body) in [
        ("Additive", "x + y"),
        ("Multiplicative", "x * y"),
        ("Numeric", "x * y"),
        ("Numeric", "x + y"),
    ] {
        assert!(
            loads(spec, body, false),
            "`Int64` must discharge `requires {spec}[T]` (body `{body}`) off its single \
             `provides Numeric[T = Int64]` — no row anywhere names the categories for it, \
             so the chain is what carries it"
        );
    }
    assert!(
        loads("Additive", "x + y", true),
        "`Money` claims `Additive`, so `requires Additive[T]` discharges and `+` reaches \
         its own `add`"
    );
    for (spec, body) in [
        ("Multiplicative", "x * y"),
        ("Numeric", "x * y"),
        ("Numeric", "x + y"),
    ] {
        assert!(
            !loads(spec, body, true),
            "`Money` claims ONLY `Additive`, so `requires {spec}[T]` (body `{body}`) must \
             be REFUSED — and the `x + y` row is the separator: same body as the passing \
             `Additive` cell, so only the `requires` clause differs"
        );
    }
}

/// SOURCE COMPATIBILITY, MEASURED. `import anthill.prelude.Numeric.{{add, sub, mul, neg}}`
/// still resolves — through the `provides` chain, exactly as `import
/// anthill.prelude.Eq.{{eq}}` reaches the inherited `PartialEq.eq` — so the ~43 sites in
/// the corpus and the examples that write it were not touched by this change.
///
/// THE OTHER SPELLING DOES NOT, and that asymmetry is recorded rather than left to be
/// discovered: a QUALIFIED `Numeric.add(a, b)` in an operation body is "unknown functor".
/// It is not new and it is not this ticket's — `Eq.eq(a, b)` and `Field.div(a, b)` have
/// both been in that state since their declarations moved (WI-1110, WI-20260824-VT8CF) —
/// but this ticket put two more addresses in the population, so it is pinned here and
/// filed as WI-20260825-X9RRN.
#[test]
fn the_member_import_still_reaches_the_moved_declaration() {
    let via_import = r#"
namespace test.wbzt.compat
  import anthill.prelude.Numeric.{add, sub, mul, neg}
  import anthill.prelude.{Int64}
  operation drive() -> Int64 = add(1, mul(sub(4, 2), 3))
end
"#;
    assert_eq!(
        drive(via_import, "test.wbzt.compat.drive"),
        "Int(7)",
        "`import anthill.prelude.Numeric.{{add, …}}` must still reach the declaration \
         `Additive`/`Multiplicative` now own, and compute"
    );

    let via_qualified = r#"
namespace test.wbzt.qualified
  import anthill.prelude.{Int64, Numeric}
  operation drive(a: Int64, b: Int64) -> Int64 = Numeric.add(a, b)
end
"#;
    let errs = try_load_kb_with(via_qualified)
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e);
    assert!(
        errs.iter().any(|e| e.contains("Numeric.add") && e.contains("unknown functor")),
        "RECORDING THE ASYMMETRY (WI-20260825-X9RRN): the qualified call does NOT walk \
         the chain — if this now loads, that ticket landed and this half should become \
         the positive row it wants to be; got {errs:?}"
    );
}

/// THE LAWS SIT WITH THE OPERATION THAT DECLARES THEM — the ticket's third acceptance
/// clause, asserted where a reader can see the split rather than in prose.
///
/// `add_comm` / `add_assoc` / `add_identity` / `neg_def` came off `Numeric`;
/// `mul_assoc` / `mul_identity` came off `algebra.Ring`. What stayed on `Ring` is what no
/// single category can state: `distrib` reads BOTH operations, and `mul_comm` is a claim
/// about multiplication that is false in general and true of the COMMUTATIVE ring.
#[test]
fn the_additive_laws_moved_to_the_sort_that_declares_add() {
    let kb = load_stdlib_kb();
    for (rule, owner) in [
        ("anthill.prelude.Additive.add_comm", "Additive"),
        ("anthill.prelude.Additive.add_assoc", "Additive"),
        ("anthill.prelude.Additive.add_identity", "Additive"),
        ("anthill.prelude.Additive.sub_def", "Additive"),
        ("anthill.prelude.Additive.neg_def", "Additive"),
        ("anthill.prelude.Multiplicative.mul_assoc", "Multiplicative"),
        ("anthill.prelude.Multiplicative.mul_identity", "Multiplicative"),
        ("anthill.prelude.algebra.Ring.mul_comm", "Ring"),
        ("anthill.prelude.algebra.Ring.distrib", "Ring"),
    ] {
        assert!(
            kb.try_resolve_symbol(rule).is_some(),
            "{rule} must live on {owner}"
        );
    }
    for gone in [
        "anthill.prelude.Numeric.add_comm",
        "anthill.prelude.Numeric.add_assoc",
        "anthill.prelude.Numeric.add_identity",
        "anthill.prelude.Numeric.neg_def",
        "anthill.prelude.algebra.Ring.add_comm",
        "anthill.prelude.algebra.Ring.add_identity",
        "anthill.prelude.algebra.Ring.mul_identity",
    ] {
        assert!(
            kb.try_resolve_symbol(gone).is_none(),
            "{gone} must NOT still be stated where the operation no longer is — two \
             copies of one law drift"
        );
    }
}

/// THE DIAMOND, AND THAT IT IS THE BENIGN ONE. `Float` reaches `Additive` by TWO routes —
/// `provides Numeric[T = Float]` and `provides Ring[Float]`, both written in
/// `anthill-stl/anthill/float.anthill` — and the base declares each operation ONCE, so
/// implementation stays CARRIER-directed: both routes resolve to `Float`'s own member by
/// the short-name join and there is no "which parent's method" question.
///
/// READ OUT OF THE INTERPRETER'S KB, not `load_stdlib_kb()`'s. The two `Float` rows live
/// in the RUST BINDING (`anthill-stl/anthill/`), which the stdlib-directory walk does not
/// read — a provisions query there answers `[]` for `Float`, which would have made this
/// row assert nothing while looking like it asserted the diamond.
///
/// Driven as well as read: `2.5 + 2.5` answers. What keeps the shape benign is the
/// declare-once discipline, which is enforced NOWHERE — WI-20260825-EBMG8 owns that gap,
/// and this row is the shape it has to keep safe.
#[test]
fn float_reaches_the_category_by_two_routes_and_still_adds() {
    let src = r#"
namespace test.wbzt.diamond
  import anthill.prelude.{Float}
  operation drive() -> Float = 2.5 + 2.5
end
"#;
    let mut interp = interp_for(src);
    let float_rows: Vec<String> = sort_provisions(interp.kb())
        .into_iter()
        .filter(|(carrier, _)| carrier == "anthill.prelude.Float")
        .map(|(_, spec)| spec)
        .collect();
    for both in ["anthill.prelude.Numeric", "anthill.prelude.algebra.Ring"] {
        assert!(
            float_rows.contains(&both.to_string()),
            "the diamond needs both routes present, or this row measures nothing; \
             {both} missing from {float_rows:?}"
        );
    }
    // …and both of those specs reach ONE `Additive`, which is the other half of the
    // diamond and the half this ticket built.
    let spec_to_spec = sort_provisions(interp.kb());
    for provider in ["anthill.prelude.Numeric", "anthill.prelude.algebra.Ring"] {
        assert!(
            spec_to_spec
                .iter()
                .any(|(p, s)| p == provider && s == "anthill.prelude.Additive"),
            "`{provider} provides Additive` is the edge that closes the diamond; got \
             {spec_to_spec:?}"
        );
    }
    let got = interp
        .call("test.wbzt.diamond.drive", &[])
        .expect("two routes to one declaration must still dispatch");
    assert_eq!(
        format!("{got:?}"),
        "Float(5.0)",
        "two routes to one declaration must still dispatch to the carrier's own `add`"
    );
}

/// THE FIVE ADDRESSES `algebra.VectorSpace`'s LAWS NAME ARE LIVE, and the five they used
/// to name are not — driven through the GUARDED position, because the position the laws
/// actually sit in checks nothing.
///
/// THIS ROW EXISTS BECAUSE THE CHANGE SHIPPED WRONG ONCE. `Ring` stopped declaring
/// `add`/`sub`/`mul`/`zero`/`one`, and `VectorSpace`'s `vec_sub_def`, `vec_scale_identity`,
/// `vec_scale_assoc` and `vec_scale_distrib_s` went on writing `Ring.sub(Ring.zero,
/// Ring.one)` and friends — five addresses that then named NOTHING. The full stdlib load
/// stayed clean and both workspaces stayed green, because an equational law's HEAD and RHS
/// are unchecked: `rule r: f(?a) <=> Bogus.nope(?a)` loads byte-identically. Found by
/// `/code-review`; the missing guard is WI-20260825-6RRVA.
///
/// SO THE ASSERTION IS MADE SOMEWHERE ELSE. A rule-body GOAL over the same name IS checked
/// (WI-1034), so each address goes there instead:
///
///   `Additive.add` / `.sub` / `Multiplicative.mul`   load
///   `Additive.zero` / `Multiplicative.one`           "ambiguous dispatch of …" — which is
///                                                    PROOF the name resolved: five
///                                                    providers were found and a nullary
///                                                    call cannot pick one
///   every `Ring.*` spelling                          "names nothing"
///
/// The `Ring.*` half is what makes it a measurement rather than a smoke test: without it
/// the row passes on a tree where BOTH spellings resolve, which is exactly the state
/// before the split — so it would not have caught the regression it exists for.
#[test]
fn the_scalar_side_law_addresses_are_live_and_the_ring_ones_are_not() {
    // `?r = N(?a, ?a)` for the binary ones, `?r = N()` for the identities — the arity the
    // declaration gives, so an arity complaint cannot be mistaken for a naming one.
    let goal = |name: &str, nullary: bool| {
        let call = if nullary {
            format!("{name}()")
        } else {
            format!("{name}(?a, ?a)")
        };
        format!(
            r#"
namespace test.wbzt.lawaddr
  import anthill.prelude.{{Int64, Additive, Multiplicative}}
  import anthill.prelude.algebra.{{Ring}}
  rule g(?a, ?r) :- ?r = {call}
end
"#
        )
    };
    let errs_for = |name: &str, nullary: bool| {
        try_load_kb_with(&goal(name, nullary))
            .map(|_| Vec::new())
            .unwrap_or_else(|e| e)
    };

    // The two BINARY category ops the laws name: the address resolves and the goal loads.
    for name in ["Additive.add", "Additive.sub", "Multiplicative.mul"] {
        assert!(
            errs_for(name, false).is_empty(),
            "`{name}` is what `VectorSpace`'s laws must name — the goal position must \
             accept it: {:?}",
            errs_for(name, false)
        );
    }
    // The two IDENTITIES: a nullary call cannot select a provider, and the complaint NAMES
    // the resolved operation — which is the proof the address is live. Asserting the
    // sentence rather than "some error" is the point: "names nothing" would also be an
    // error, and it is the opposite verdict.
    for name in ["Additive.zero", "Multiplicative.one"] {
        let errs = errs_for(name, true);
        assert!(
            errs.iter().any(|e| e.contains("ambiguous dispatch of")
                && e.contains(&format!("anthill.prelude.{name}"))),
            "`{name}` must RESOLVE — the nullary ambiguity names it, which is the \
             evidence; got {errs:?}"
        );
    }
    // …and the five `Ring.*` spellings the laws USED to carry name nothing at all.
    for (name, nullary) in [
        ("Ring.add", false),
        ("Ring.sub", false),
        ("Ring.mul", false),
        ("Ring.zero", true),
        ("Ring.one", true),
    ] {
        let errs = errs_for(name, nullary);
        assert!(
            errs.iter()
                .any(|e| e.contains(name) && e.contains("names nothing")),
            "`{name}` must name NOTHING — `Ring` reaches its operations by `provides` and \
             declares none, so a law still spelled this way is a typo the loader cannot \
             see (WI-20260825-6RRVA); got {errs:?}"
        );
    }
}

/// THE HOST-OP TABLES FOLLOW THE DECLARATION, and the reason this is a row rather than a
/// grep is that every one of them is keyed by QUALIFIED NAME and fails SILENTLY when the
/// key goes stale: `register_if_present` skips a name that does not resolve, `SMT_BUILTINS`
/// lowers an unknown functor as uninterpreted, `render_as_operator` falls through to a
/// call. None of the three errors.
///
/// The eval half is what this row can drive in-process: the interpreter answers `1 + 2`
/// from `numeric_add`, so a `register_if_present` still pointed at
/// `anthill.prelude.Numeric.add` would have registered NOTHING and the call would fail.
#[test]
fn the_host_arithmetic_is_still_registered_at_the_moved_address() {
    let kb = load_stdlib_kb();
    for qn in [
        "anthill.prelude.Additive.add",
        "anthill.prelude.Additive.sub",
        "anthill.prelude.Additive.neg",
        "anthill.prelude.Multiplicative.mul",
    ] {
        assert!(
            kb.try_resolve_symbol(qn).is_some(),
            "{qn} must resolve, or `register_if_present` silently registers nothing"
        );
    }
    let src = r#"
namespace test.wbzt.host
  import anthill.prelude.{Int64}
  operation drive() -> Int64 = 1 + 2
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(
        format!(
            "{:?}",
            interp
                .call("test.wbzt.host.drive", &[])
                .expect("the host `add` must be registered at the category's address")
        ),
        "Int(3)"
    );
}
