//! WI-734 — the binary-type-constructor family's ABSTRACT-OPERAND rule, settled once for
//! `Concat` (WI-714) / `Without` (WI-727) and any future member (a `Project[T, keep]`,
//! WI-732; a `FieldOf`, WI-759).
//!
//! THE RULE: an operand that is NOT YET KNOWN — a logic variable (the `Var::Rigid` skolem a
//! generic op's `[S]` becomes, or an unsolved inference var), or an unreduced residual one
//! level down — leaves the ctor SYMBOLIC, to reduce later once the operand grounds. An
//! operand that IS known but cannot be merged (a name collision, a 1-collapse / scalar
//! schema) stays a LOUD error.
//!
//! Before this, both cases were handed to the reducer, so an un-instantiated type parameter
//! was reported with the CONCRETE-malformation message ("operand must be a named-tuple type
//! … a 1-collapse / membership schema is not supported") — a diagnostic blaming a shape the
//! user never wrote. "Cannot reduce yet" and "cannot reduce ever" are different answers.
//!
//! CONFLUENCE: a residual can only exist over an un-instantiated operand, so a fully
//! concrete type is always fully reduced — there are never two comparable forms of one
//! concrete type.

use crate::common::try_load_kb_with;

/// A bodyless `merge` whose schema lives purely in its signature, plus a GENERIC wrapper
/// whose own operands are abstract — so `merge`'s return inside it is a residual `Concat`.
const GENERIC: &str = r#"
  import anthill.prelude.{String, Int64, Bool, Relation}
  import anthill.prelude.Relation.{Concat}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "a", age: 1)
  sort Membership
    entity member(who: String, dept: String)
  end
  fact member(who: "a", dept: "eng")

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  rule member_row(?who, ?dept) :- member(who: ?who, dept: ?dept)

  operation merge[L, R](a: Relation[T = L], b: Relation[T = R])
    -> Relation[T = Concat[A = L, B = R]]

  operation mergeWrap[L2, R2](a: Relation[T = L2], b: Relation[T = R2])
    -> Relation[T = Concat[A = L2, B = R2]] = merge(a, b)
"#;

/// DIRECTION 1 (`Concat`) — an abstract operand stays SYMBOLIC. `merge(a, b)` inside the
/// generic wrapper cannot reduce (`L2` / `R2` are un-instantiated), and the residual must
/// conform to the wrapper's own declared return rather than raise.
#[test]
fn wi734_concat_abstract_operand_stays_symbolic() {
    let src = format!("namespace test.wi734sym\n{GENERIC}\nend\n");
    assert!(
        try_load_kb_with(&src).is_ok(),
        "a Concat over abstract operands must stay symbolic, not raise the \
         concrete-malformation error"
    );
}

/// A residual REDUCES once its operands ground. Selecting a column from EACH side
/// (`name` from `a`, `dept` from `b`) only resolves against the MERGED schema — were the
/// residual to escape unreduced, both would fail dot dispatch.
#[test]
fn wi734_residual_reduces_when_operands_ground() {
    let src = format!(
        r#"
namespace test.wi734ground
{GENERIC}
  operation useIt() -> Bool effects Error =
    let m = mergeWrap(person_row, member_row)
    let picked = m.(name, dept)
    picked.isEmpty
end
"#
    );
    assert!(
        try_load_kb_with(&src).is_ok(),
        "grounding a residual Concat must yield the merged schema, so a column from \
         each operand resolves"
    );
}

/// NEGATIVE CONTROL — the residual must not have become permissive. A column in NEITHER
/// operand is still rejected once the schema grounds.
#[test]
fn wi734_grounded_residual_still_rejects_unknown_column() {
    let src = format!(
        r#"
namespace test.wi734unknowncol
{GENERIC}
  operation useIt() -> Bool effects Error =
    let m = mergeWrap(person_row, member_row)
    let picked = m.(name, nosuchcolumn)
    picked.isEmpty
end
"#
    );
    assert!(
        try_load_kb_with(&src).is_err(),
        "a column in neither operand must still be rejected after the residual reduces"
    );
}

/// DIRECTION 2 (`Concat`) — a CONCRETE but unmergeable pair stays LOUD, reached through
/// the SAME generic wrapper as the symbolic case: only the groundness of the operands
/// differs, and that alone decides symbolic-vs-error. Both rows expose `name`.
#[test]
fn wi734_concat_concrete_collision_is_still_loud() {
    let src = format!(
        r#"
namespace test.wi734collide
{GENERIC}
  rule other_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation useIt() -> Bool effects Error =
    let m = mergeWrap(person_row, other_row)
    let picked = m.(name, age)
    picked.isEmpty
end
"#
    );
    match try_load_kb_with(&src) {
        Err(errs) => assert!(
            errs.iter().any(|e| e.contains("disjoint") || e.contains("share the field name")),
            "expected the disjoint-field-name Concat error, got: {errs:?}"
        ),
        Ok(_) => panic!("a concrete colliding merge must stay a loud error"),
    }
}

/// The SECOND not-yet-known shape: an operand that is itself an UNREDUCED ctor. Each ctor
/// reduces in its own pass, so during the `Concat` pass the inner `Without` (whose `T` is
/// abstract) is still a residual — the outer `Concat` must defer on it rather than trip its
/// concrete-operand check. Guards the branch a bare-variable test cannot reach.
#[test]
fn wi734_nested_residual_operand_stays_symbolic() {
    const SRC: &str = r#"
namespace test.wi734nest
  import anthill.prelude.{String, Int64, Bool, Relation}
  import anthill.prelude.Relation.{Concat, Without}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "a", age: 1)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation nest[S, D, B2](p: Relation[T = S], q: Relation[T = B2])
    -> Relation[T = Concat[A = Without[T = S, Drop = D], B = B2]]
  operation nestWrap[S2, D2, B3](p: Relation[T = S2], q: Relation[T = B3])
    -> Relation[T = Concat[A = Without[T = S2, Drop = D2], B = B3]] = nest(p, q)
end
"#;
    assert!(
        try_load_kb_with(SRC).is_ok(),
        "a Concat whose operand is an unreduced Without residual must also stay symbolic"
    );
}

/// A DENOTED operand — a value standing in the type-argument position — is NOT
/// "not yet known": a value can never become a named tuple, so this is "cannot reduce
/// ever" and stays LOUD. Pins that the not-yet-known test did not over-broaden into
/// swallowing genuinely unreducible operands.
#[test]
fn wi734_denoted_operand_is_still_loud() {
    const SRC: &str = r#"
namespace test.wi734den
  import anthill.prelude.{String, Int64, Bool, Relation}
  import anthill.prelude.Relation.{Concat}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "a", age: 1)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation den[R](p: Relation[T = R], c: Int64) -> Relation[T = Concat[A = c, B = R]]
  operation useDen() -> Bool effects Error =
    let m = den(person_row, 1)
    m.isEmpty
end
"#;
    match try_load_kb_with(SRC) {
        Err(errs) => assert!(
            errs.iter().any(|e| e.contains("named-tuple type")),
            "expected the concrete non-named-tuple error for a value operand, got: {errs:?}"
        ),
        Ok(_) => panic!("a denoted value operand can never merge and must stay loud"),
    }
}

/// DIRECTION 1 (`Without`) — the family rule holds for the DUAL too, via the real `fix`
/// path: the receiver's schema `S` is abstract, so `Without[T = S, Drop = …]` cannot
/// reduce and must stay symbolic. (`Without`'s concrete-operand loud errors are pinned by
/// the WI-727 `fix` tests.)
#[test]
fn wi734_without_abstract_operand_stays_symbolic() {
    const SRC: &str = r#"
namespace test.wi734without
  import anthill.prelude.{String, Int64, Bool, Relation}
  import anthill.prelude.Relation.{fix}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "a", age: 1)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation wrapFix[S](p: Relation[T = S]) -> Relation = p.fix(name: "a")
end
"#;
    assert!(
        try_load_kb_with(SRC).is_ok(),
        "a Without over an abstract receiver schema must stay symbolic"
    );
}
