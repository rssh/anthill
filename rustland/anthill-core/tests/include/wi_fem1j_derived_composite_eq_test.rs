//! WI-20261109-FEM1J (proposal 051 Phase 2, 3 of 4) — a composite's derived `eq` compares
//! field by field, each field through the `eq` its type supplies.
//!
//! Before, the derivation recorded the provision only, and the structural compare of the
//! host did the comparing: measured on 4067661d, with `Pt`'s `eq` comparing `x` alone,
//! `PartialEq.eq(box(p: pt(1, 2)), box(p: pt(1, 9)))` was `false` in an operation body and
//! undecided in a rule body, and so was the same pair under `some`.
//!
//! Now (1) every composite given `PartialEq` by the derivation is also given the `eq` member
//! a program would write for it (`eq_derive::derived_eq_member_source`, loaded by
//! `load::load_derived_eq_members` before the typer): it compares the constructors and then
//! each field through `PartialEq.eq`, which the typer pins at the field's type or reads
//! through the parameter's dictionary; a composite whose every field compares by structure
//! is compared by `===`. (2) The derivation decides a composite's equality where every
//! field's is decided: a composite holding a `Float` derives `PartialEq` as any other does,
//! and `NonEq` only beside it; a field of an opaque handle, of a type that leaves a
//! parameter open, of a sort whose `eq` is declared and unimplemented (`Map`), or of a type
//! whose sort's own `requires` fail at its arguments, decides nothing. (3) A carrier whose
//! `Eq` is conditional (`provides Eq[Option] :- Eq[T]`) has no law read at its member's
//! entry; two identical operands are equal by the law where every value inside them is of
//! a lawful carrier (`some(7)`, not `some(nan)`). (4) The value-directed field-wise walks
//! are gone; a tuple, which no member compares, has its components compared; the equation
//! unfold's override scan looks inside a derived member.
//!
//! ## Back-out
//!
//! Measured 2026-11-09, one part at a time by a temporary switch, over the whole
//! `anthill-core` crate:
//!
//! - the members out (`load_derived_eq_members` not run): 22 rows — every row of this file
//!   that compares a composite (all but the two that refuse or load), wi664's three NaN
//!   rows, wi_ckd4j's two, wi_p1tpe's float-leaf and buried-override rows, the wi625 rows
//!   that reach an override inside `Option`, wi_5bp39's composite row, and the rows that
//!   list a sort's operations or count its typed bodies (wi1008, wi_gmg6n, wi_9bkz4,
//!   wi_papx0);
//! - the `Partial` half as it was (`PartialEq` for every composite reaching a `Float`): the
//!   stdlib does not load (`anthill.reflect.Expr`'s member compares a `NodeOccurrence`) —
//!   9 630 rows;
//! - a conditional `Eq` read as lawful at the member's entry: `a_float_field_follows_ieee`
//!   and wi_ckd4j's two NaN rows, `some(nan)` against itself answering `true`;
//! - the lawful-values reading of identical operands out: wi738's `eq(some(7), some(7))`
//!   and the wi625 eval row (identical sets under `some`), each left undecided;
//! - the tuple compare out: wi_7g99a's `(nan, 1) = (nan, 1)`;
//! - the unfold's scan stopping at a derived member: 8 narrowing rows (push_choice ×2,
//!   wi_k4jgc, wi_dey66, wi_p1tpe ×2, wi_7ypgm, wi_t2470);
//! - the field type's `requires` not read: wi_7ab56 and wi_swphb, a member refused at
//!   `Set[T = P.Key]`;
//! - an unimplemented `eq` read as decided: wi644 ×4, wi835, wi_2nxac and wi_tj3g4, a member
//!   refused at a `Map` field;
//! - a field with no sort head read as decided: wi429 and wi_p7vp4;
//! - an open parameter read as decided: `a_field_that_leaves_a_parameter_open_derives_no_member`.
//!
//! PASS EITHER WAY, BY DESIGN: the removal of the field-wise walks moves no row — a typed
//! call reaches the member before any value is read — and whether a member compares by `===`
//! or field by field, which give one answer.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::node_occurrence::{for_each_child, ApplyDispatch, Expr, NodeOccurrence};
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

use crate::common::{interp_for, load_errors_of, load_kb_with, query_unary};

const NS: &str = "test.fem1j";

/// `Pt`'s `eq` compares `x` alone, so `pt(1, 2)` equals `pt(1, 9)` and only a member that
/// reads `Pt.eq` says so.
const PT: &str = r#"
  sort Pt
    entity pt(x: Int64, y: Int64)
    operation eq(a: Self, b: Self) -> Bool =
      match a
        case pt(ax, _) ->
          match b
            case pt(bx, _) -> PartialEq.eq(ax, bx)
    provides PartialEq[Self]
    provides Eq[Self]
  end
"#;

fn program(body: &str) -> String {
    format!(
        r#"namespace {NS}
  import anthill.prelude.{{Int64, Bool, Float, PartialEq, Eq, Option, Pair, List, TotalFloat}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}
  import anthill.prelude.Float.{{nan}}
{PT}
{body}
end
"#
    )
}

fn call_bool(interp: &mut Interpreter, op: &str) -> bool {
    match interp.call(&format!("{NS}.{op}"), &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("`{op}`: expected a Bool, got {other:?}"),
    }
}

/// The one definite `Bool` the unary relation answers.
fn rule_bool(interp: &mut Interpreter, rule: &str) -> bool {
    match query_unary(interp.kb_mut(), &format!("{NS}.{rule}")).as_slice() {
        [(Value::Bool(b), true)] => *b,
        other => panic!("`{rule}`: expected one definite Bool, got {other:?}"),
    }
}

/// Does the unary relation hold, definitely, once?
fn rule_holds(interp: &mut Interpreter, rule: &str) -> bool {
    match query_unary(interp.kb_mut(), &format!("{NS}.{rule}")).as_slice() {
        [] => false,
        [(_, true)] => true,
        other => panic!("`{rule}`: expected no answer or one definite one, got {other:?}"),
    }
}

/// The operation each call of `PartialEq.eq` in `op`'s body was pinned to.
fn pins(kb: &KnowledgeBase, op: &str) -> Vec<String> {
    let sym = kb.try_resolve_symbol(&format!("{NS}.{op}")).expect("the operation resolves");
    let body = kb.op_body_node(sym).expect("the operation has a body");
    let mut out = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(body)];
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        if let Expr::Apply { functor, .. } = expr {
            if kb.qualified_name_of(*functor) == "anthill.prelude.PartialEq.eq" {
                out.push(match o.apply_dispatch() {
                    ApplyDispatch::Pin(t) | ApplyDispatch::NeedsDict(t) => {
                        kb.qualified_name_of(t).to_string()
                    }
                    ApplyDispatch::Unclassified => "unclassified".to_string(),
                });
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    out
}

/// A field of a sort with its own `eq` is compared by that `eq`, in an operation body, a rule
/// goal and through `=` / `!=`; the typed call is the call of the composite's member. FAILS
/// with the members out: the pin is `PartialEq.eq` and every equal pair answers `false`.
#[test]
fn a_field_compares_by_its_types_eq() {
    let src = program(
        r#"
  sort Box
    entity box(p: Pt)
  end
  operation same() -> Bool = PartialEq.eq(box(p: pt(1, 2)), box(p: pt(1, 9)))
  operation apart() -> Bool = PartialEq.eq(box(p: pt(1, 2)), box(p: pt(2, 2)))
  operation viaEq() -> Bool = box(p: pt(1, 2)) = box(p: pt(1, 9))
  operation viaNeq() -> Bool = box(p: pt(1, 2)) != box(p: pt(1, 9))
  rule sameGoal(?r) :- PartialEq.eq(box(p: pt(1, 2)), box(p: pt(1, 9)), ?r)
  rule apartGoal(?r) :- PartialEq.eq(box(p: pt(1, 2)), box(p: pt(2, 2)), ?r)
  rule viaEqGoal(?r) :- ?r <=> 1, box(p: pt(1, 2)) = box(p: pt(1, 9))
  rule viaNeqGoal(?r) :- ?r <=> 1, box(p: pt(1, 2)) != box(p: pt(1, 9))
"#,
    );
    let mut interp = interp_for(&src);
    assert_eq!(pins(interp.kb(), "same"), vec![format!("{NS}.Box.eq")]);
    assert!(call_bool(&mut interp, "same"));
    assert!(!call_bool(&mut interp, "apart"));
    assert!(call_bool(&mut interp, "viaEq"));
    assert!(!call_bool(&mut interp, "viaNeq"));
    assert!(rule_bool(&mut interp, "sameGoal"));
    assert!(!rule_bool(&mut interp, "apartGoal"));
    assert!(rule_holds(&mut interp, "viaEqGoal"));
    assert!(!rule_holds(&mut interp, "viaNeqGoal"));
}

/// A field typed by a parameter is compared through the parameter's `eq`: `some(v)` through
/// `T`'s, a `List[T = Pt]` element by element, and a generic caller under `requires
/// PartialEq[T = A]` reaches the same member. FAILS with the members out.
#[test]
fn a_parameter_field_compares_by_the_parameters_eq() {
    let src = program(
        r#"
  sort Box
    entity box(p: Pt)
  end
  operation same[A](x: A, y: A) -> Bool requires PartialEq[T = A] = PartialEq.eq(x, y)
  operation someSame() -> Bool = PartialEq.eq(some(pt(1, 2)), some(pt(1, 9)))
  operation someApart() -> Bool = PartialEq.eq(some(pt(1, 2)), none)
  operation listSame() -> Bool = PartialEq.eq([pt(1, 2), pt(3, 4)], [pt(1, 0), pt(3, 0)])
  operation listApart() -> Bool = PartialEq.eq([pt(1, 2), pt(3, 4)], [pt(1, 0), pt(4, 0)])
  operation listShorter() -> Bool = PartialEq.eq([pt(1, 2)], [pt(1, 0), pt(3, 0)])
  operation genericBox() -> Bool = same(box(p: pt(1, 2)), box(p: pt(1, 9)))
  operation genericSome() -> Bool = same(some(pt(1, 2)), some(pt(1, 9)))
  rule someGoal(?r) :- PartialEq.eq(some(pt(1, 2)), some(pt(1, 9)), ?r)
  rule listGoal(?r) :- PartialEq.eq([pt(1, 2), pt(3, 4)], [pt(1, 0), pt(3, 0)], ?r)
  rule someTest(?r) :- ?r <=> 1, some(pt(1, 2)) = some(pt(1, 9))
"#,
    );
    let mut interp = interp_for(&src);
    assert_eq!(pins(interp.kb(), "someSame"), vec!["anthill.prelude.Option.eq".to_string()]);
    assert!(call_bool(&mut interp, "someSame"));
    assert!(!call_bool(&mut interp, "someApart"));
    assert!(call_bool(&mut interp, "listSame"));
    assert!(!call_bool(&mut interp, "listApart"));
    assert!(!call_bool(&mut interp, "listShorter"));
    assert!(call_bool(&mut interp, "genericBox"));
    assert!(call_bool(&mut interp, "genericSome"));
    assert!(rule_bool(&mut interp, "someGoal"));
    assert!(rule_bool(&mut interp, "listGoal"));
    assert!(rule_holds(&mut interp, "someTest"));
}

/// A recursive composite's member calls itself. FAILS with the members out.
#[test]
fn a_recursive_composite_calls_its_own_member() {
    let src = program(
        r#"
  sort Tree
    entity leaf(v: Pt)
    entity node(l: Tree, r: Tree)
  end
  operation same() -> Bool =
    PartialEq.eq(node(leaf(pt(1, 2)), leaf(pt(3, 4))), node(leaf(pt(1, 0)), leaf(pt(3, 0))))
  operation apart() -> Bool =
    PartialEq.eq(node(leaf(pt(1, 2)), leaf(pt(3, 4))), node(leaf(pt(1, 0)), leaf(pt(4, 0))))
  operation shape() -> Bool = PartialEq.eq(node(leaf(pt(1, 2)), leaf(pt(3, 4))), leaf(pt(1, 2)))
  rule sameGoal(?r) :-
    PartialEq.eq(node(leaf(pt(1, 2)), leaf(pt(3, 4))), node(leaf(pt(1, 0)), leaf(pt(3, 0))), ?r)
"#,
    );
    let mut interp = interp_for(&src);
    assert!(call_bool(&mut interp, "same"));
    assert!(!call_bool(&mut interp, "apart"));
    assert!(!call_bool(&mut interp, "shape"));
    assert!(rule_bool(&mut interp, "sameGoal"));
}

/// `Pair` writes its own member, which compares its components through `PartialEq.eq`, and
/// reads a derived member there as any other. FAILS with the members out.
#[test]
fn a_pair_holding_a_composite_reads_the_members() {
    let src = program(
        r#"
  sort Box
    entity box(p: Pt)
  end
  operation same() -> Bool =
    PartialEq.eq(pair(fst: box(p: pt(1, 2)), snd: 0), pair(fst: box(p: pt(1, 9)), snd: 0))
  operation apart() -> Bool =
    PartialEq.eq(pair(fst: box(p: pt(1, 2)), snd: 0), pair(fst: box(p: pt(1, 9)), snd: 1))
  rule sameGoal(?r) :-
    PartialEq.eq(pair(fst: box(p: pt(1, 2)), snd: 0), pair(fst: box(p: pt(1, 9)), snd: 0), ?r)
"#,
    );
    let mut interp = interp_for(&src);
    assert!(call_bool(&mut interp, "same"));
    assert!(!call_bool(&mut interp, "apart"));
    assert!(rule_bool(&mut interp, "sameGoal"));
}

/// A `Float` field follows IEEE through `Float.eq`: `some(nan)` is apart from itself in both
/// bodies, as a pair holding `nan` is, while `TotalFloat`'s own `eq` makes `some(TotalFloat(nan))`
/// equal to itself. FAILS with a conditional `Eq` read as lawful at the member's entry:
/// `someNan` and `pairNan` answer `true`.
#[test]
fn a_float_field_follows_ieee() {
    let src = program(
        r#"
  sort Reading
    entity reading(v: Float)
  end
  operation someNan() -> Bool = PartialEq.eq(some(nan), some(nan))
  operation pairNan() -> Bool = PartialEq.eq(pair(fst: nan, snd: 1), pair(fst: nan, snd: 1))
  operation readingNan() -> Bool = PartialEq.eq(reading(nan), reading(nan))
  operation readingSame() -> Bool = PartialEq.eq(reading(1.5), reading(1.5))
  operation someTotal() -> Bool = PartialEq.eq(some(TotalFloat(nan)), some(TotalFloat(nan)))
  operation someInt() -> Bool = PartialEq.eq(some(1), some(1))
  rule someNanGoal(?r) :- PartialEq.eq(some(nan), some(nan), ?r)
  rule someTotalGoal(?r) :- PartialEq.eq(some(TotalFloat(nan)), some(TotalFloat(nan)), ?r)
"#,
    );
    let mut interp = interp_for(&src);
    assert!(!call_bool(&mut interp, "someNan"), "IEEE: nan is apart from itself");
    assert!(!call_bool(&mut interp, "pairNan"), "IEEE: nan is apart from itself");
    assert!(!call_bool(&mut interp, "readingNan"), "IEEE: nan is apart from itself");
    assert!(call_bool(&mut interp, "readingSame"));
    assert!(call_bool(&mut interp, "someTotal"), "TotalFloat's eq is total");
    assert!(call_bool(&mut interp, "someInt"));
    assert!(!rule_bool(&mut interp, "someNanGoal"));
    assert!(rule_bool(&mut interp, "someTotalGoal"));
}

/// A composite holding a `Float` and a field whose equality nothing decides (a function)
/// derives no equality: a call asking for it is refused where it is written. FAILS with the
/// `Partial` half as it was — the stdlib does not load.
#[test]
fn a_field_nothing_decides_derives_no_equality() {
    let src = program(
        r#"
  sort Tagged
    entity tagged(f: (Int64) -> Int64, v: Float)
  end
  operation inc(n: Int64) -> Int64 = n
  operation same[A](x: A, y: A) -> Bool requires PartialEq[T = A] = PartialEq.eq(x, y)
  operation cmp() -> Bool = same(tagged(f: inc, v: 1.5), tagged(f: inc, v: 1.5))
"#,
    );
    let errs = load_errors_of(&src);
    crate::common::assert_refused_naming(
        &errs,
        &["PartialEq", "Tagged"],
        "a composite with a function field derives no `PartialEq`",
    );
}

/// A field whose type leaves a parameter of its sort open — `Strm[T = Int64]` beside an
/// unwritten `E`, a bare `Box` — is of a fresh instance per value (kernel-language §5.2), so
/// two values' fields are of two instances and nothing decides an equality between them:
/// the composite derives none, and is given no member. FAILS with that rule backed out: the
/// member of `H` is refused, its two binders' `E` being two instances.
#[test]
fn a_field_that_leaves_a_parameter_open_derives_no_member() {
    let src = program(
        r#"
  sort Strm
    sort T = ?
    sort E = ?
    entity s(v: T)
  end
  sort H
    entity h(st: Strm[T = Int64])
  end
  sort Chain
    sort T = ?
    entity link(v: T)
    entity hop(next: Chain[T = ?])
  end
"#,
    );
    let kb = load_kb_with(&src);
    for sort in ["H", "Chain"] {
        assert!(
            kb.try_resolve_symbol(&format!("{NS}.{sort}.eq")).is_none(),
            "`{sort}` is given no `eq`"
        );
    }
    assert!(kb.try_resolve_symbol(&format!("{NS}.Strm.eq")).is_some(), "`Strm` is");
}
