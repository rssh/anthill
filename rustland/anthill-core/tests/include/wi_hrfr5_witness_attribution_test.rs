//! WI-20260917-HRFR5 — THE WRITTEN BRACKET CHOSE A WITNESS, so two `require`s on one spec
//! were admitted however they were grounded: the direct scan let a `require[Desc[T = Thing]]`
//! choose among candidate calls by their carrier argument's STATIC sort, a ground
//! constructor or a typed head parameter, and refused the pair where it could not — untyped
//! carriers, or two calls at one carrier.
//!
//! ## Since proposal 060.1 §5
//!
//! `require[X]` is removed, and the requirements this file attributed were at CONCRETE
//! carriers, which a call at a concrete type does not need: `Desc.describe(thing(), ?r1),
//! Desc.describe(gadget(), ?r2)` answers 7 and 9 by type. What the bracket did — tell two
//! requirements of one spec apart by the carrier each is at — the head's introducer does,
//! two type parameters each with its guard, `two[A, B](a: A, b: B, …) :- Desc[T = A],
//! Desc[T = B]`, each call covered by the guard at its own argument's parameter
//! (`collect_covered_calls`, narrowed by the call's carrier argument). And two guards at ONE
//! parameter are two requirements, as an operation's two equal `requires` lines are two
//! slots (060.1 §8.5): the refusals of untyped carriers and of two calls at one carrier are
//! lifted, a call covered by both reading the first.
//!
//! ## Back-out
//!
//! With HRFR5's selection backed out (the `chosen` computation forced to `None`) its two
//! acceptance rows failed — measured on `require[X]`, whose scan the guard does not use. With
//! the weave's narrowing backed out (the carrier check of `collect_covered_calls` skipped),
//! [`a_typed_head_carrier_is_readable_too`] fails, measured on the guard: each call is covered
//! by both guards and the clause is refused by the one-dictionary-per-call check ("covered by
//! distinct carrier requirements"), as the written pair was. Its `describe` is body-less, so
//! skipping the check for a bodied call alone leaves it passing.

use anthill_core::eval::Value;

/// `Thing` answers 7 through `Desc` and `Gadget` answers 9. `describe` is BODY-LESS in the
/// spec, so an absent dictionary is observable as no answer rather than as a default.
fn fixture(ns: &str, clause: &str, query: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Thing
    import anthill.prelude.Int64
    entity thing
    provides Desc[T = Thing]
    operation describe(x: Thing) -> Int64 = 7
  end

  sort Gadget
    import anthill.prelude.Int64
    entity gadget
    provides Desc[T = Gadget]
    operation describe(x: Gadget) -> Int64 = 9
  end

{clause}  rule answer(?r) :- {query}
end
"#
    )
}

fn answer(ns: &str, clause: &str, query: &str) -> Option<i64> {
    let mut kb = crate::common::load_kb_with(&fixture(ns, clause, query));
    match crate::common::query_unary(&mut kb, &format!("{ns}.answer")).as_slice() {
        [(Value::Int(i), true)] => Some(*i),
        _ => None,
    }
}

/// Two calls at GROUND carriers, no requirement written: each is dispatched by its type.
const GROUND: &str = "  rule two(?r1, ?r2) :- Desc.describe(thing(), ?r1), Desc.describe(gadget(), ?r2)\n";

/// Two type parameters, each with its guard, and a call at each — the introducer's
/// attribution of two requirements of one spec.
const TYPED: &str = "  rule two[A, B](a: A, b: B, ?r1, ?r2) :- Desc[T = A], Desc[T = B], \
     Desc.describe(a, ?r1), Desc.describe(b, ?r2)\n";

/// Calls at ground carriers answer each its own carrier's number, asserted BY VALUE —
/// `describe` is body-less and each answer comes from a different provider. The row was
/// HRFR5's acceptance, a witness-grounded pair `?d1 = require[Desc[T = Thing]], ?d2 =
/// require[Desc[T = Gadget]]` before the same calls, admitted when the bracket named each
/// carrier; the calls need neither. PASSES EITHER WAY now.
#[test]
fn a_witness_grounded_pair_is_admitted_when_the_bracket_names_each_carrier() {
    assert_eq!(answer("test.hrfr5.g1", GROUND, "two(?r, ?)"), Some(7));
    assert_eq!(answer("test.hrfr5.g2", GROUND, "two(?, ?r)"), Some(9));
}

/// TWO REQUIREMENTS OF ONE SPEC, told apart by the parameters they are at: `A` and `B`, each
/// with its guard, cited at `thing()` and `gadget()`, answer `Thing`'s 7 and `Gadget`'s 9.
/// The row was the same pair through TYPED HEAD PARAMETERS (`a: Thing, b: Gadget`) and
/// `require[Desc[T = Thing]]`, `require[Desc[T = Gadget]]`.
#[test]
fn a_typed_head_carrier_is_readable_too() {
    assert_eq!(answer("test.hrfr5.t1", TYPED, "two(thing(), gadget(), ?r, ?)"), Some(7));
    assert_eq!(answer("test.hrfr5.t2", TYPED, "two(thing(), gadget(), ?, ?r)"), Some(9));
}

/// TWO GUARDS AT ONE PARAMETER ARE TWO REQUIREMENTS (060.1 §8.5), and the calls both cover
/// read the first: `two[A](?a: A, ?b: A, …) :- Desc[T = A], Desc[T = A]` answers 7 at two
/// `thing()`s, and nothing at `thing()` and `gadget()` — one `A` is not both. The row was the
/// refusal of a pair over UNTYPED carriers, which no bracket could attribute; the introducer
/// types them, and the refusal is lifted.
#[test]
fn untyped_carriers_are_still_refused() {
    let one = "  rule two[A](?a: A, ?b: A, ?r1, ?r2) :- Desc[T = A], Desc[T = A], \
               Desc.describe(?a, ?r1), Desc.describe(?b, ?r2)\n";
    assert_eq!(answer("test.hrfr5.u1", one, "two(thing(), thing(), ?, ?r)"), Some(7));
    assert_eq!(answer("test.hrfr5.u2", one, "two(thing(), gadget(), ?r, ?)"), None);
}

/// TWO CALLS AT ONE CARRIER UNDER TWO GUARDS AT ONE PARAMETER read the first (060.1 §8.5):
/// 7 for each. The row was the refusal of `require[Desc[T = Thing]]` and
/// `require[Desc[T = Gadget]]` beside two calls at `thing()` — "exactly one match", not
/// "the first match"; two requirements of one spec at one parameter are the operation's two
/// equal `requires` lines now.
#[test]
fn two_calls_at_one_carrier_are_still_refused() {
    let two = "  rule two[A](?a: A, ?r1, ?r2) :- Desc[T = A], Desc[T = A], \
               Desc.describe(?a, ?r1), Desc.describe(?a, ?r2)\n";
    assert_eq!(answer("test.hrfr5.s1", two, "two(thing(), ?r, ?)"), Some(7));
    assert_eq!(answer("test.hrfr5.s2", two, "two(thing(), ?, ?r)"), Some(7));
}

/// ONE GUARD STILL COVERS EVERY CALL AT ITS PARAMETER — two calls at `?a: A`, both answering
/// 7 at `thing()`. PASSES EITHER WAY BY DESIGN (it was one `require[Desc[T = Thing]]` and two
/// calls at `thing()`); it is the regression a narrowing of the weave would have to avoid.
#[test]
fn one_require_still_covers_every_call_it_covered() {
    let one = "  rule two[A](?a: A, ?r1, ?r2) :- Desc[T = A], \
               Desc.describe(?a, ?r1), Desc.describe(?a, ?r2)\n";
    assert_eq!(answer("test.hrfr5.c1", one, "two(thing(), ?r, ?)"), Some(7));
    assert_eq!(answer("test.hrfr5.c2", one, "two(thing(), ?, ?r)"), Some(7));
}

/// A CALL AT A CARRIER THE GUARD IS NOT AT STILL ANSWERS, and correctly: one guard at `A`,
/// cited at `thing()`, beside calls at `?a` and at `gadget()` — the second answers 9, its own
/// carrier's number, dispatched by its type and not covered by the guard. PASSES EITHER WAY BY
/// DESIGN: the row was one `require[Desc[T = Thing]]` beside the two calls, answering 7 and 9.
#[test]
fn a_call_at_a_carrier_the_bracket_does_not_name_still_answers() {
    const MIXED: &str = "  rule two[A](?a: A, ?r1, ?r2) :- Desc[T = A], \
         Desc.describe(?a, ?r1), Desc.describe(gadget(), ?r2)\n";
    assert_eq!(answer("test.hrfr5.m1", MIXED, "two(thing(), ?r, ?)"), Some(7));
    assert_eq!(
        answer("test.hrfr5.m2", MIXED, "two(thing(), ?, ?r)"),
        Some(9),
        "the `gadget()` call answers its OWN carrier's number"
    );
}
