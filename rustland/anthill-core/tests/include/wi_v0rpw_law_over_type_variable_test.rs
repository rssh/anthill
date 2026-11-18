//! A LAW OVER A TYPE VARIABLE IS A LEMMA, USED AT A TYPE THAT PROVIDES ITS SORT
//! (WI-20261117-V0RPW, user decisions 2026-11-17). A guarded `=` law is a premise of the
//! typer's proofs (§5.3): a guard is refuted by proving the swapped comparison, and a law
//! whose left side matches the comparison's operand answers it. The library's arithmetic laws
//! named no type, so they held at every carrier whose division shares `div`, `mul` and `rem`,
//! with the `Int64` literal `0` for zero — MEASURED, each refuted the guard of a call that
//! raises (rows below). They are written over their type variable now, `rule euclid_div:
//! add[A](mul(?b: A, …), …) = ?a :- EuclideanDomain[T = A], Additive[T = A], neq(?b, zero)`;
//! using one instantiates `A` at the type of what `?b` matches, passes each guard as the
//! typer's instance there, and reads `zero` through `Additive[T = A]`. Where nothing provides
//! the sort the lemma is not used; and `Float` provides `Divisible`, not `Field`.
//!
//! ## What fails with the change backed out
//!
//! Measured one at a time, each with the rest of the change in place (2026-11-17):
//!
//! * The loader refusing a bound on a guarded `=` law again (WI-582), or a call with no
//!   argument no longer resolved through the one instance the clause holds: every row fails —
//!   the stdlib's laws do not load.
//! * That resolution without its one-type-variable condition:
//!   [`a_call_with_no_argument_reads_the_instance_of_a_one_variable_clause`] (the two-variable
//!   clause loads).
//! * The law not instantiated at the match, or its guard's instance not passed:
//!   [`euclid_div_is_used_at_a_euclidean_domain_and_not_at_a_zero_divisor`] and
//!   [`the_field_laws_are_used_at_a_field`] (the lemma is used nowhere).
//! * `euclid_div` written as before, `add(mul(?b, div(?a, ?b)), rem(?a, ?b)) = ?a :- neq(?b,
//!   0)`: the `euclid_div` row (the `0n` divisor's guard refuted).
//! * `Field`'s first law written as before: [`the_field_laws_are_not_used_where_the_type_is_no_field`]
//!   and [`the_field_laws_are_used_at_a_field`] (its `0` is no `F5`).
//! * `Float` providing `Field` again: [`float_divides_and_is_no_field`], the not-a-field row,
//!   and `wi_vt8cf`'s and `wi_m8qwj`'s rows that say so.
//!
//! Dropping a lemma at a type that does not provide its sort when it is instantiated FAILS NO
//! ROW, by design: the law's own read of that instance, a goal of its body, holds it back too.
//! The drop is the earlier of two stops that agree.

use crate::common::{load_errors_of, run_int64};

/// A program declaring the effect `Boom`, with `risky` guarded by `guard` over parameters of
/// type `ty`, and `c` calling it as `call`.
fn guarded(ns: &str, ty: &str, guard: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Float, BigInt, Bool, PartialEq, Effect, EuclideanDomain}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  operation risky(a: {ty}, b: {ty}) -> {ty} effects {{ Boom :- {guard} }} = a
  operation c(x: {ty}) -> {ty} = {call}
end
"#
    )
}

fn owes_boom(src: &str) -> bool {
    load_errors_of(src)
        .iter()
        .any(|e| e.contains("c.effects") && e.contains("undeclared effect: Boom"))
}

const EUCLID: &str = "neq(b * (a / b) + EuclideanDomain.rem(a, b), a)";
const INVERSE: &str = "neq((a / b) * b, a)";

/// `euclid_div` refutes the guard at a non-zero divisor of an `Int64` or a `BigInt` — a
/// Euclidean domain each — and at a zero one it is not used: `neq(0n, zero)` is false, `zero`
/// being `BigInt`'s. The `0n` row is the defect: `neq(0n, 0)` held, so the guard was refuted
/// at a call whose division raises.
#[test]
fn euclid_div_is_used_at_a_euclidean_domain_and_not_at_a_zero_divisor() {
    for (i, (ty, call, owes)) in [
        ("Int64", "risky(x, 2)", false),
        ("BigInt", "risky(x, 2n)", false),
        ("Int64", "risky(x, 0)", true),
        ("BigInt", "risky(x, 0n)", true),
    ]
    .iter()
    .enumerate()
    {
        let src = guarded(&format!("test.v0rpw.euclid{i}"), ty, EUCLID, call);
        assert_eq!(
            owes_boom(&src),
            *owes,
            "{ty} {call}: {:?}",
            load_errors_of(&src)
        );
    }
}

/// `Field`'s `mul(div(?a, ?b), ?b) = ?a` holds at a field, and no carrier here is one: an
/// `Int64` and a `BigInt` divide rounding toward zero, a `Float` rounds. It refuted the guard
/// at each of these calls, every one of which raises for some `x` (`(7 / 2) * 2` is 6, `(1.0 /
/// 49.0) * 49.0` is 0.9999999999999999). A ground call is evaluated, and stays decided.
#[test]
fn the_field_laws_are_not_used_where_the_type_is_no_field() {
    for (i, (ty, call)) in [
        ("Int64", "risky(x, 2)"),
        ("BigInt", "risky(x, 2n)"),
        ("Float", "risky(x, 0.0)"),
        ("Float", "risky(x, 49.0)"),
        // Passes either way by design: a ground call is evaluated, not proved by a law.
        ("Float", "risky(1.0, 49.0)"),
    ]
    .iter()
    .enumerate()
    {
        let src = guarded(&format!("test.v0rpw.inverse{i}"), ty, INVERSE, call);
        assert!(owes_boom(&src), "{ty} {call}: {:?}", load_errors_of(&src));
    }
    // CONTROL: a ground call whose guard evaluates false owes nothing.
    let src = guarded("test.v0rpw.inverse_ground", "Int64", INVERSE, "risky(6, 2)");
    assert!(!owes_boom(&src), "{:?}", load_errors_of(&src));
}

/// `Float` is `Divisible` and not a `Field`: `/` still reaches `Float.div` (10.0 / 4.0 is
/// 2.5), and a requirement of `Field` at `Float` is unmet.
#[test]
fn float_divides_and_is_no_field() {
    assert_eq!(
        run_int64(
            "namespace test.v0rpw.fdiv\n  import anthill.prelude.{Int64, Float}\n  \
             operation q() -> Int64 = Float.floor(10.0 / 4.0 * 10.0)\nend\n",
            "test.v0rpw.fdiv.q",
        ),
        Ok(25)
    );
    let errs = load_errors_of(
        "namespace test.v0rpw.ffield\n  \
         import anthill.prelude.{Float, Field, Error, DivisionByZero}\n  \
         operation inv[T](a: T) -> T effects {Error[T = DivisionByZero]} requires Field[T = T] = Field.recip(a)\n  \
         operation q() -> Float effects {Error[T = DivisionByZero]} = inv(4.0)\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("anthill.prelude.Field[T = anthill.prelude.Float]")),
        "`Float` provides no `Field`: {errs:?}"
    );
}

/// At a carrier that IS a field the law is used: `F5`, the integers mod 5, where `(a / b) * b`
/// is `a` for every `b` but zero. `zero` is `F5`'s, `f5(v: 0)`, read through `Additive[T =
/// F5]`. The controls the rows above measure the other way.
#[test]
fn the_field_laws_are_used_at_a_field() {
    let program = |ns: &str, divisor: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, PartialEq, Field, Effect, Error, DivisionByZero}}
  import anthill.prelude.algebra.{{Ring}}
  import anthill.prelude.PartialEq.{{neq}}
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  sort F5
    entity f5(v: Int64)
    operation add(a: F5, b: F5) -> F5 = f5(v: Int64.mod(Int64.add(a.v, b.v), 5))
    operation neg(a: F5) -> F5        = f5(v: Int64.mod(Int64.sub(5, a.v), 5))
    operation zero() -> F5            = f5(v: 0)
    operation mul(a: F5, b: F5) -> F5 = f5(v: Int64.mod(Int64.mul(a.v, b.v), 5))
    operation one() -> F5             = f5(v: 1)
    operation eq(a: F5, b: F5) -> Bool = a.v = b.v
    operation recip(a: F5) -> F5 effects {{ Error[DivisionByZero] }} =
      f5(v: Int64.mod(Int64.mul(Int64.mul(a.v, a.v), a.v), 5))
    operation div(a: F5, b: F5) -> F5 effects {{ Error[DivisionByZero] }} = mul(a, recip(b))
    provides PartialEq[T = F5]
    provides Ring[F5]
    provides Field[T = F5]
  end
  operation risky(a: F5, b: F5) -> F5 effects {{ Error[DivisionByZero], Boom :- {INVERSE} }} = a
  operation c(x: F5) -> F5 effects {{ Error[DivisionByZero] }} = risky(x, {divisor})
end
"#
        )
    };
    let used = load_errors_of(&program("test.v0rpw.fivefield.two", "f5(v: 2)"));
    assert!(used.is_empty(), "the law refutes the guard at a non-zero divisor: {used:?}");
    let src = program("test.v0rpw.fivefield.zero", "f5(v: 0)");
    assert!(owes_boom(&src), "not at a zero one: {:?}", load_errors_of(&src));
}

/// A call written with no argument (`zero`) reads the one instance a clause over ONE type
/// variable holds — `Additive[T = A]`'s, at `A`. Over two, a rule's type variables still unify
/// while its body is typed, so `zero` would read `A`'s instance compared with a `B`: it is
/// refused as before, an ambiguous dispatch.
#[test]
fn a_call_with_no_argument_reads_the_instance_of_a_one_variable_clause() {
    let clause = |ns: &str, rule: &str| {
        format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64, Additive, PartialOrd, PartialEq}}\n  \
             import anthill.prelude.PartialEq.{{neq}}\n  import anthill.prelude.Additive.{{zero}}\n  \
             {rule}\nend\n"
        )
    };
    let one = load_errors_of(&clause(
        "test.v0rpw.onevar",
        "rule s[A](?a: A, ?b: A) :- Additive[T = A], PartialEq[T = A], neq(?b, zero)",
    ));
    assert!(one.is_empty(), "{one:?}");
    let two = load_errors_of(&clause(
        "test.v0rpw.twovar",
        "rule r[A, B](?a: A, ?b: B) :- Additive[T = A], PartialOrd[T = B], neq(?b, zero)",
    ));
    assert!(
        two.iter().any(|e| e.contains("ambiguous dispatch of `anthill.prelude.Additive.zero`")),
        "{two:?}"
    );
}
