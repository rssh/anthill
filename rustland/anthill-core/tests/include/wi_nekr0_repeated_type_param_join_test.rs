//! WI-20260926-NEKR0 — A TYPE PARAMETER BOUND BY SEVERAL ARGUMENTS TAKES THEIR JOIN
//! (kernel-language §8.1, *A type parameter bound by several arguments takes their join*).
//!
//! `cmp2[A](x: A, y: A)` used to take `A` from its FIRST argument, so with `Circle provides
//! Shape` the call `cmp2(s, c)` loaded at `A = Shape` and `cmp2(c, s)` was refused ("expected
//! Circle, got Shape") — a call's typing depended on the order of its arguments. Each argument
//! at a COVARIANT occurrence of `A` (bare, under a `Covariant` sort parameter, in an arrow's
//! result) now contributes its type, and `A` is their join — the `if`/`match` arm join and the
//! collection-literal one (WI-20260829-WBXGX). The other occurrences contribute nothing and are
//! checked against it.
//!
//! ## Back-out
//!
//! With the pre-pass (`join_repeated_type_params`) removed from all four sites, these FAIL:
//! `both_orders_answer_in_an_operation_body`, `both_orders_answer_through_a_citation`,
//! `a_covariant_slot_contributes_in_either_order`, `no_join_is_refused_naming_the_parameter`
//! (the old per-argument mismatch is reported instead), `a_callback_parameter_refuses_the_join`
//! (the callback, written first, pins `A = Circle` and `x` is blamed), and PRVA2's
//! `the_other_order_loads_and_routes_as_the_typer_instantiates`.
//! PASS EITHER WAY, by design (controls): `a_callback_parameter_contributes_nothing` and
//! `an_invariant_slot_still_demands_one_type` — they pin what the join must NOT widen.
//! `an_invariant_slot_fixes_the_parameter` FAILS backed out (the reverse order `putLast(c, b)`
//! let `c` pin `A = Circle` and refused the box) AND with only the join's invariant arm removed
//! (the covariant `Circle` alone then decides `A` and refuses the box in BOTH orders) — the
//! regression `/code-review` found in the first cut. `a_provided_sort_leaves_the_parameter_to_-
//! the_call` passes backed out AND after; it FAILS only with the join's OPAQUE veto removed (the
//! lone `Circle` then decides `A` before the `List`→`Stream` provision is read). All measured.
//! `a_conversion_is_not_joined` FAILS backed out, BY DESIGN — the some-coercion used to admit
//! `same(some(1), 5)` in that order only; the join does not read conversions, so both orders are
//! refused (§8.1).

use anthill_core::eval::value::Value;

/// `Circle provides Shape`; `Circle`'s own `Cmp` answers `1`, `ShapeCmp`'s `2`. So an answer
/// of `2` says `A = Shape` was instantiated and its dictionary chosen.
const BASE: &str = r#"
namespace winekr0
  import anthill.prelude.{Int64, String, List, Stream, Error, EmptyStream, Relation}

  sort Cmp
    sort T = ?
    operation cmp(a: T, b: T) -> Int64
  end

  sort Shape
  end

  sort Circle
    provides Shape
    entity circle
    provides Cmp[T = Circle]
    operation cmp(a: Circle, b: Circle) -> Int64 = 1
  end

  sort ShapeCmp
    provides Cmp[T = Shape]
    operation cmp(a: Shape, b: Shape) -> Int64 = 2
  end

  sort Util
    operation cmp2[A](x: A, y: A) -> Int64 requires Cmp[T = A] = Cmp.cmp(x, y)
  end

  rule via(?a, ?b, ?c) :- Util.cmp2(?a, ?b, ?c)
end
"#;

fn extended(rules: &str) -> String {
    let body = BASE.trim_end().strip_suffix("end").expect("the fixture ends its namespace");
    format!("{body}{rules}end\n")
}

fn drive_int(src: &str, entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// THE CASE. Both orders load at `A = Shape` and answer `ShapeCmp`'s `2`. FAILS backed out:
/// `bodyCS` is refused, "type mismatch in cmp2.y (op-arg): expected Circle, got Shape".
#[test]
fn both_orders_answer_in_an_operation_body() {
    let src = extended(
        "  sort Driver\n    \
         operation bodySC(c: Circle, s: Shape) -> Int64 = Util.cmp2(s, c)\n    \
         operation bodyCS(c: Circle, s: Shape) -> Int64 = Util.cmp2(c, s)\n    \
         operation goSC() -> Int64 = bodySC(circle(), circle())\n    \
         operation goCS() -> Int64 = bodyCS(circle(), circle())\n  \
         end\n",
    );
    assert_eq!(
        (drive_int(&src, "winekr0.Driver.goSC"), drive_int(&src, "winekr0.Driver.goCS")),
        (2, 2),
    );
}

/// The same call through a CITATION of a rule calling it, from a caller holding
/// `Cmp[T = Shape]`: the column typing and the slot route instantiate as the typer does, in both
/// orders. FAILS backed out: `citeCS` is refused, "argument binding column `b` has an
/// incompatible type".
#[test]
fn both_orders_answer_through_a_citation() {
    let src = extended(
        "  sort Driver\n    \
         operation citeSC(c: Circle, s: Shape) -> Int64 effects {Error, Error[EmptyStream]}\n      \
         requires Cmp[T = Shape] = via(s, c).head.c\n    \
         operation citeCS(c: Circle, s: Shape) -> Int64 effects {Error, Error[EmptyStream]}\n      \
         requires Cmp[T = Shape] = via(c, s).head.c\n    \
         operation goSC() -> Int64 effects {Error, Error[EmptyStream]} = citeSC(circle(), circle())\n    \
         operation goCS() -> Int64 effects {Error, Error[EmptyStream]} = citeCS(circle(), circle())\n  \
         end\n",
    );
    assert_eq!(
        (drive_int(&src, "winekr0.Driver.goSC"), drive_int(&src, "winekr0.Driver.goCS")),
        (2, 2),
    );
}

/// A COVARIANT SLOT contributes too: `List.T` is declared `Covariant`, so `xs: List[T = A]`
/// given a `List[T = Circle]` contributes `Circle`, joined with `y`'s `Shape`, whichever
/// parameter is written first. FAILS backed out: `addFirst(cs, s)` is refused (the list pins
/// `A = Circle` first).
#[test]
fn a_covariant_slot_contributes_in_either_order() {
    let src = extended(
        "  sort Util2\n    \
         operation addFirst[A](xs: List[T = A], y: A) -> Int64 requires Cmp[T = A] = Cmp.cmp(y, y)\n    \
         operation addLast[A](y: A, xs: List[T = A]) -> Int64 requires Cmp[T = A] = Cmp.cmp(y, y)\n  \
         end\n  \
         sort Driver\n    \
         operation first(cs: List[T = Circle], s: Shape) -> Int64 = Util2.addFirst(cs, s)\n    \
         operation last(cs: List[T = Circle], s: Shape) -> Int64 = Util2.addLast(s, cs)\n    \
         operation goFirst() -> Int64 = first([circle()], circle())\n    \
         operation goLast() -> Int64 = last([circle()], circle())\n  \
         end\n",
    );
    assert_eq!(
        (drive_int(&src, "winekr0.Driver.goFirst"), drive_int(&src, "winekr0.Driver.goLast")),
        (2, 2),
    );
}

/// NO JOIN — `Int64` and `String` have no common type — is refused, naming the parameter and
/// both contributions. FAILS backed out: the refusal is the per-argument "expected Int64, got
/// String" instead.
#[test]
fn no_join_is_refused_naming_the_parameter() {
    let src = extended(
        "  sort Util3\n    \
         operation same[A](x: A, y: A) -> Int64 = 0\n  \
         end\n  \
         sort Driver\n    \
         operation bad() -> Int64 = Util3.same(1, \"a\")\n  \
         end\n",
    );
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&src),
        &["no common type for type parameter `A` of `same`: Int64 (x), String (y)"],
    );
}

/// CONTROL, passes either way: a callback's PARAMETER is contravariant, so it contributes
/// nothing — `A` comes from `x` alone (`Circle`), and a `Shape`-taking callback accepts it.
#[test]
fn a_callback_parameter_contributes_nothing() {
    let src = extended(
        "  sort Util4\n    \
         operation apply2[A](f: (v: A) -> Int64, x: A) -> Int64 = f(x)\n  \
         end\n  \
         sort Driver\n    \
         operation onShape(v: Shape) -> Int64 = 7\n    \
         operation go() -> Int64 = Util4.apply2(onShape, circle())\n  \
         end\n",
    );
    assert_eq!(drive_int(&src, "winekr0.Driver.go"), 7);
}

/// The join is CHECKED against a callback parameter, never widened by it — `A = Shape` from
/// `x`, and a `Circle`-only callback cannot take every `Shape`, so `f` is refused. FAILS backed
/// out: the callback, written first, pinned `A = Circle` and the refusal blamed `x`.
#[test]
fn a_callback_parameter_refuses_the_join() {
    let src = extended(
        "  sort Util4\n    \
         operation apply2[A](f: (v: A) -> Int64, x: A) -> Int64 = f(x)\n  \
         end\n  \
         sort Driver\n    \
         operation onCircle(v: Circle) -> Int64 = 7\n    \
         operation bad(s: Shape) -> Int64 = Util4.apply2(onCircle, s)\n  \
         end\n",
    );
    crate::common::expect_load_errors(crate::common::try_load_kb_with(&src), &["apply2.f"]);
}

/// CONTROL, passes either way: a sort parameter with NO declared variance is invariant, so it
/// contributes nothing and still demands one type — `Box[T = Circle]` is no `Box[T = Shape]`.
#[test]
fn an_invariant_slot_still_demands_one_type() {
    let src = extended(
        "  sort Box\n    \
         sort T = ?\n    \
         entity box(v: T)\n  \
         end\n  \
         sort Util5\n    \
         operation put[A](b: Box[T = A], y: A) -> Int64 = 0\n  \
         end\n  \
         sort Driver\n    \
         operation bad(b: Box[T = Circle], s: Shape) -> Int64 = Util5.put(b, s)\n  \
         end\n",
    );
    crate::common::expect_load_errors(crate::common::try_load_kb_with(&src), &["put."]);
}

/// AN INVARIANT OCCURRENCE FIXES THE PARAMETER, and the covariant argument is checked against
/// it: `Box[T = Shape]` makes `A = Shape`, which the `Circle` conforms to. `put(b, c)` loaded
/// before the join existed (the box came first and pinned `A`) and `putLast(c, b)` did not; the
/// join over the covariant arguments ALONE takes `A = Circle` and refuses the box in both —
/// "expected Box[T = Circle], got Box[T = Shape]".
#[test]
fn an_invariant_slot_fixes_the_parameter() {
    let src = extended(
        "  sort Box\n    \
         sort T = ?\n    \
         entity box(v: T)\n  \
         end\n  \
         sort Util5\n    \
         operation put[A](b: Box[T = A], y: A) -> Int64 requires Cmp[T = A] = Cmp.cmp(y, y)\n    \
         operation putLast[A](y: A, b: Box[T = A]) -> Int64 requires Cmp[T = A] = Cmp.cmp(y, y)\n  \
         end\n  \
         sort Driver\n    \
         operation first(b: Box[T = Shape], c: Circle) -> Int64 = Util5.put(b, c)\n    \
         operation last(b: Box[T = Shape], c: Circle) -> Int64 = Util5.putLast(c, b)\n    \
         operation shapeBox(s: Shape) -> Box[T = Shape] = box(v: s)\n    \
         operation goFirst() -> Int64 = first(shapeBox(circle()), circle())\n    \
         operation goLast() -> Int64 = last(shapeBox(circle()), circle())\n  \
         end\n",
    );
    assert_eq!(
        (drive_int(&src, "winekr0.Driver.goFirst"), drive_int(&src, "winekr0.Driver.goLast")),
        (2, 2),
        "`A = Shape`, fixed by the box, and `ShapeCmp` chosen",
    );
}

/// AN ARGUMENT THE JOIN CANNOT READ LEAVES THE PARAMETER TO THE CALL. `s: Stream[T = A]` given
/// a `List[T = Shape]` relates through `List provides Stream` — not a head the join decomposes —
/// so `A` is not instantiated from the `Circle` beside it alone: the call pins it through the
/// provision (`A = Shape`) as it always did, and the `Circle` conforms.
#[test]
fn a_provided_sort_leaves_the_parameter_to_the_call() {
    let src = extended(
        "  sort Util6\n    \
         operation push[A](s: Stream[T = A], x: A) -> Int64 requires Cmp[T = A] = Cmp.cmp(x, x)\n  \
         end\n  \
         sort Driver\n    \
         operation viaList(xs: List[T = Shape], c: Circle) -> Int64 = Util6.push(xs, c)\n    \
         operation shapes(s: Shape) -> List[T = Shape] = [s]\n    \
         operation go() -> Int64 = viaList(shapes(circle()), circle())\n  \
         end\n",
    );
    assert_eq!(drive_int(&src, "winekr0.Driver.go"), 2, "`A = Shape`, through the provision");
}

/// The join does not read CONVERSIONS: `Option[T = Int64]` and `Int64` have no join, so
/// `same(some(1), 5)` is refused in BOTH orders. It used to load in the first — `some(1)` pinned
/// `A = Option[T = Int64]` and the `5` was some-coerced — and be refused in the second: the same
/// order-dependence, from a conversion.
#[test]
fn a_conversion_is_not_joined() {
    let src = extended(
        "  sort Util3\n    \
         operation same[A](x: A, y: A) -> Int64 = 0\n  \
         end\n  \
         sort Driver\n    \
         operation someFirst() -> Int64 = Util3.same(anthill.prelude.Option.some(1), 5)\n    \
         operation someLast() -> Int64 = Util3.same(5, anthill.prelude.Option.some(1))\n  \
         end\n",
    );
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&src),
        &[
            "no common type for type parameter `A` of `same`: Option[T = Int64] (x), Int64 (y)",
            "no common type for type parameter `A` of `same`: Int64 (x), Option[T = Int64] (y)",
        ],
    );
}
