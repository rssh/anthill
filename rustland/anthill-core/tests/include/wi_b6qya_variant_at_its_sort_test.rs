//! A PARAMETRIC VARIANT IS ITS SORT AT THE SAME ARGUMENTS — found while probing
//! WI-20261009-B6QYA, and fixed with it.
//!
//! THE RULE. A constructor's type arguments are its sort's (spec §8.2), so a value typed
//! `Option.some[T = Int64]` is an `Option[T = Int64]` wherever another type than the
//! variant itself is asked for, as a value typed by the bare variant `Colour.red` is a
//! `Colour`. Two such variants join at their sort, and what the subtype relation reads of
//! a parameter — its variance, whether a slot may be left out — it reads of the sort's.
//!
//! BEFORE. `operation pass(x: Option.some[T = Int64]) -> Int64 = unwrap(x)` over
//! `unwrap(o: Option[T = Int64])` was refused, `expected Option[T = Int64], got
//! some[T = Int64]`: the bases conformed, and the expected `T` was then looked for in a
//! provision of the constructor's, which has none. `takes(if c then x else y)` over a
//! `some[…]` and a `none[…]` was refused, an application having no parent to climb to.
//! And `some[T = cat]` was no `some[T = Animal]`, the variance being asked of `some`.
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   the subtype relation's reading of a variant at its sort (the `variant_at_its_sort`
//!   leg of `parameterized_compatible_view`) — FAIL, every row but the fence:
//!     a_parametric_variant_is_its_sort_at_the_same_arguments
//!     the_same_variant_is_compared_as_its_sort_is
//!     a_sort_s_own_operation_takes_a_variant_typed_value
//!     two_parametric_variants_join_at_their_sort
//!   the join's (`widen_value` climbing a bare variant only) — FAIL:
//!     two_parametric_variants_join_at_their_sort (its two-variant half)
//!   the variance read at the sort (`declared_variance` asked of the constructor) — FAIL:
//!     two_parametric_variants_join_at_their_sort (its one-variant half)
//!   a variant-typed receiver's carrier read as its sort (`concrete_receiver_carrier`
//!   keeping the constructor) — FAIL:
//!     a_sort_s_own_operation_takes_a_variant_typed_value
//!     the_same_variant_is_compared_as_its_sort_is (its `Pair.fst` half)
//!   a provision matched against the goal's variant as written
//!   (`match_candidate_against_goal` without its `variant_at_its_sort` leg) — FAIL:
//!     a_spec_call_at_a_variant_typed_carrier_is_answered_by_its_sort
//!   a requirement's other elements read off the variant and not its sort
//!   (`bind_clause_params_at_carrier` without its `variant_type_at_its_sort` leg) — FAIL:
//!     a_spec_call_at_a_variant_typed_carrier_is_answered_by_its_sort (its chain row)
//!
//!   PASS UNDER EVERY BACK-OUT, by design — the fence:
//!     a_bare_variant_and_a_sort_are_as_they_were

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// The declarations the rows are about, indented for a namespace body.
const DECLS: &str = r#"
  sort Animal
    entity cat
    entity dog
    operation legs(a: Animal) -> Int64 = 4
  end
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
    operation shade(c: Colour) -> Int64 = match c
      case red(v) -> v
      case blue(v) -> v
  end
  sort Pair[L, R]
    entity pair(l: L, r: R)
    entity left(l: L)
    operation fst(p: Self) -> L = match p
      case pair(l, r) -> l
      case left(l) -> l
  end
  operation unwrap(o: Option[T = Int64]) -> Int64 = match o
    case some(v) -> v
    case none -> 0
  operation count[U](o: Option[T = U]) -> Int64 = match o
    case some(v) -> 1
    case none -> 0
  operation legsOf(o: Option[T = Animal]) -> Int64 = match o
    case some(a) -> Animal.legs(a)
    case none -> 0
  operation someCat(c: Animal.cat) -> Option.some[T = Animal.cat] = some(c)
  operation someDog(d: Animal.dog) -> Option.some[T = Animal.dog] = some(d)
  operation optCat(c: Animal.cat) -> Option[T = Animal.cat] = some(c)
"#;

fn source(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Type, Bool, Option}}\n  import anthill.prelude.Option.{{some, none}}\n{DECLS}\n{body}\nend\n"
    )
}

/// Load, call `test.<ns>.go()`, and hand back its integer as text.
fn run(ns: &str, body: &str) -> String {
    let mut interp = interp_for(&source(ns, body));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => n.to_string(),
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, body: &str) -> String {
    let errs = try_load_kb_with(&source(ns, body))
        .err()
        .unwrap_or_else(|| panic!("{ns}: must be refused, and loaded clean"));
    format!("{errs:?}")
}

/// A value typed by a parametric variant is taken where its sort is asked for: by a
/// parameter, a parameter generic in the argument, a return, an annotated `let`, a field.
#[test]
fn a_parametric_variant_is_its_sort_at_the_same_arguments() {
    for (ns, pass) in [
        ("vsarg", "  operation pass(x: Option.some[T = Int64]) -> Int64 = unwrap(x)"),
        ("vsgen", "  operation pass(x: Option.some[T = Int64]) -> Int64 = count(x) + unwrap(x) - 1"),
        (
            "vsret",
            "  operation up(x: Option.some[T = Int64]) -> Option[T = Int64] = x\n  operation pass(x: Option.some[T = Int64]) -> Int64 = unwrap(up(x))",
        ),
        (
            "vslet",
            "  operation pass(x: Option.some[T = Int64]) -> Int64 =\n    let o: Option[T = Int64] = x\n    unwrap(o)",
        ),
        (
            "vsfield",
            "  sort Holder\n    entity holder(o: Option[T = Int64])\n    operation held(h: Holder) -> Int64 = unwrap(h.o)\n  end\n  operation pass(x: Option.some[T = Int64]) -> Int64 = Holder.held(holder(x))",
        ),
    ] {
        let body = format!("{pass}\n  operation go() -> Int64 = pass(some(5))");
        assert_eq!(run(ns, &body), "5", "{ns}");
    }
    // Its arguments are still the ones compared, and a sibling variant is still another.
    for (ns, body, site) in [
        (
            "vsargbad",
            "  operation pass(x: Option.some[T = String]) -> Int64 = unwrap(x)",
            "unwrap.o (op-arg): expected Option[T = Int64], got some[T = String]",
        ),
        (
            "vssibling",
            "  operation onlyNone(o: Option.none[T = Int64]) -> Int64 = 0\n  operation pass(x: Option.some[T = Int64]) -> Int64 = onlyNone(x)",
            "onlyNone.o (op-arg): expected none[T = Int64], got some[T = Int64]",
        ),
        (
            "vsretbad",
            "  operation up(x: Option.some[T = Int64]) -> Option[T = String] = x",
            "up.return (op-return): expected Option[T = String], got some[T = Int64]",
        ),
    ] {
        let rendered = refusal(ns, body);
        assert!(rendered.contains(site), "{ns}: {rendered}");
    }
}

/// One variant on both sides is compared as its sort is: by the sort's variance, and with
/// a slot left out standing for any type.
#[test]
fn the_same_variant_is_compared_as_its_sort_is() {
    let ns = "vscov";
    let body = "  operation someLegs(o: Option.some[T = Animal]) -> Int64 = legsOf(o)\n  operation pass(x: Option.some[T = Animal.cat]) -> Int64 = someLegs(x)\n  operation go() -> Int64 = pass(someCat(cat))";
    assert_eq!(run(ns, body), "4");
    let rendered = refusal(
        "vscovback",
        "  operation onlyCats(o: Option.some[T = Animal.cat]) -> Int64 = 1\n  operation pass(x: Option.some[T = Animal]) -> Int64 = onlyCats(x)",
    );
    assert!(
        rendered.contains("onlyCats.o (op-arg): expected some[T = cat], got some[T = Animal]"),
        "{rendered}"
    );

    let ns = "vspartial";
    let body = "  operation full(p: Pair.left[L = Int64, R = String]) -> Int64 = Pair.fst(p)\n  operation pass(x: Pair.left[L = Int64]) -> Int64 = full(x)\n  operation go() -> Int64 = pass(left(7))";
    assert_eq!(run(ns, body), "7");
    let rendered = refusal(
        "vspartialbad",
        "  operation full(p: Pair.left[L = Int64, R = String]) -> Int64 = Pair.fst(p)\n  operation pass(x: Pair.left[L = String]) -> Int64 = full(x)",
    );
    assert!(
        rendered.contains("full.p (op-arg): expected left[L = Int64, R = String], got left[L = String]"),
        "{rendered}"
    );
}

/// The sort's own operations take a value typed by one of its parametric variants, by
/// the sort's name and by a dot, and read its instance. Before, the receiver's carrier was
/// read as the constructor, which provides nothing: "Pair.fst.dispatch: … no impl provides
/// Pair".
#[test]
fn a_sort_s_own_operation_takes_a_variant_typed_value() {
    for (ns, call) in [("vsown", "Pair.fst(x)"), ("vsowndot", "x.fst()")] {
        let body = format!(
            "  operation pass(x: Pair.left[L = Int64, R = String]) -> Int64 = {call}\n  operation go() -> Int64 = pass(left(7))"
        );
        assert_eq!(run(ns, &body), "7", "{ns}");
    }
    let rendered = refusal(
        "vsownbad",
        "  operation pass(x: Pair.left[L = Int64, R = String]) -> String = Pair.fst(x)",
    );
    assert!(
        rendered.contains("pass.return (op-return): expected String, got Int64"),
        "{rendered}"
    );
}

/// A spec called at a carrier typed by a parametric variant is answered by the provision
/// of its sort — written on the sort, or read through the spec's own `requires` — as at a
/// carrier typed by the sort. A provision written at one variant still answers at that
/// variant and at no other instance. Before, "`Both.one` provides no `Desc`".
#[test]
fn a_spec_call_at_a_variant_typed_carrier_is_answered_by_its_sort() {
    let specs = |ns: &str, body: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{List, FiniteCollection}}\n\
             \x20 import anthill.prelude.List.{{cons, nil}}\n\
             \x20 sort Desc[T]\n\
             \x20   operation describe(x: T) -> Int64\n\
             \x20 end\n\
             \x20 sort Both[V]\n\
             \x20   entity one(v: V)\n\
             \x20   entity two(v: V)\n\
             \x20   provides Desc[T = Both[V = V]]\n\
             \x20   operation describe(x: Both[V = V]) -> Int64 = 9\n\
             \x20 end\n\
             \x20 sort Only[V]\n\
             \x20   entity wrap(v: V)\n\
             \x20   entity bare\n\
             \x20   provides Desc[T = Only.wrap[V = Int64]]\n\
             \x20   operation describe(x: Only.wrap[V = Int64]) -> Int64 = 5\n\
             \x20 end\n\
             \x20 sort Plain[V]\n\
             \x20   entity mk(v: V)\n\
             \x20 end\n\
             {body}\n\
             end\n"
        )
    };
    let answer = |ns: &str, body: &str| -> String {
        let mut interp = interp_for(&specs(ns, body));
        match interp.call(&format!("test.{ns}.go"), &[]) {
            Ok(Value::Int(n)) => n.to_string(),
            other => panic!("{ns}: expected an Int64, got {other:?}"),
        }
    };
    for (ns, body, want) in [
        (
            "vsspec",
            "  operation at(x: Both.one[V = Int64]) -> Int64 = Desc.describe(x)\n  operation go() -> Int64 = at(one(1))",
            "9",
        ),
        (
            "vsspecchain",
            "  operation at(xs: List.cons[T = Int64]) -> Int64 = FiniteCollection.size(xs)\n  operation go() -> Int64 = at(cons(head: 7, tail: cons(head: 8, tail: nil)))",
            "2",
        ),
        (
            "vsspecown",
            "  operation at(x: Only.wrap[V = Int64]) -> Int64 = Desc.describe(x)\n  operation go() -> Int64 = at(wrap(1))",
            "5",
        ),
    ] {
        assert_eq!(answer(ns, body), want, "{ns}");
    }
    for (ns, body, carrier) in [
        (
            "vsspecother",
            "  operation at(x: Only.wrap[V = String]) -> Int64 = Desc.describe(x)",
            "Only.wrap[V = anthill.prelude.String]",
        ),
        (
            "vsspecnone",
            "  operation at(x: Plain.mk[V = Int64]) -> Int64 = Desc.describe(x)",
            "Plain.mk[V = anthill.prelude.Int64]",
        ),
    ] {
        let errs = try_load_kb_with(&specs(ns, body))
            .err()
            .unwrap_or_else(|| panic!("{ns}: must be refused, and loaded clean"));
        let rendered = format!("{errs:?}");
        assert!(
            rendered.contains("describe.requires") && rendered.contains(carrier),
            "{ns}: {rendered}"
        );
    }
}

/// Two branches typed by parametric variants join at their sort — two variants of it, or
/// one variant at two arguments the sort's variance joins.
#[test]
fn two_parametric_variants_join_at_their_sort() {
    let ns = "vsjoin";
    let body = "  operation pick(c: Bool, x: Option.some[T = Int64], y: Option.none[T = Int64]) -> Int64 = unwrap(if c then x else y)\n  operation go() -> Int64 = pick(true, some(5), none) + pick(false, some(5), none)";
    assert_eq!(run(ns, body), "5");
    let rendered = refusal(
        "vsjoinbad",
        "  operation pick(c: Bool, x: Option.some[T = Int64], y: Option.none[T = String]) -> Int64 = unwrap(if c then x else y)",
    );
    assert!(rendered.contains("expected some[T = Int64], got none[T = String]"), "{rendered}");

    let ns = "vsjoincov";
    let body = "  operation pick(c: Bool, x: Option.some[T = Animal.cat], y: Option.some[T = Animal.dog]) -> Int64 = legsOf(if c then x else y)\n  operation go() -> Int64 = pick(true, someCat(cat), someDog(dog))";
    assert_eq!(run(ns, body), "4");
}

/// The fence: a bare variant is its sort, and a sort is compared by its variance, as both
/// were.
#[test]
fn a_bare_variant_and_a_sort_are_as_they_were() {
    let ns = "vsbare";
    let body = "  operation pass(x: Colour.red) -> Int64 = Colour.shade(x)\n  operation go() -> Int64 = pass(red(3))";
    assert_eq!(run(ns, body), "3");
    let ns = "vssort";
    let body = "  operation pass(x: Option[T = Animal.cat]) -> Int64 = legsOf(x)\n  operation go() -> Int64 = pass(optCat(cat))";
    assert_eq!(run(ns, body), "4");
    let rendered = refusal(
        "vssortbad",
        "  operation pass(x: Option[T = String]) -> Int64 = unwrap(x)",
    );
    assert!(
        rendered.contains("unwrap.o (op-arg): expected Option[T = Int64], got Option[T = String]"),
        "{rendered}"
    );
}
