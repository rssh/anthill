//! WI-664 — composite `Eq`/`NonEq`: field-wise SEMANTIC equality for a
//! Float-containing composite (entity / named tuple), so the interpreter and the
//! resolver AGREE with the field-wise C++ `operator==` on a nested `NaN`
//! (`eq(Point(nan,_), Point(nan,_)) = false`), and the derived `NonEq`
//! classification that makes a user `provides Eq` over such a composite a load
//! error. `TotalFloat` (a Float wrapper declaring its own total `eq`) is a lawful
//! boundary — it stays reflexively `Eq`, and shields a composite that wraps it.
//! `===` (`struct_eq`) stays structural throughout (hash-consing intact).

use anthill_core::eval::Interpreter;
use anthill_core::intern::Symbol;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

fn interp(src: &str) -> Interpreter {
    crate::common::interp_for(src)
}

fn call_bool(i: &mut Interpreter, op: &str) -> bool {
    i.call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
        .as_bool()
        .unwrap_or_else(|| panic!("call {op}: not a Bool"))
}

const SRC: &str = r#"
namespace test.wi664
  import anthill.prelude.{Bool, Int64, Float, TotalFloat}
  import anthill.prelude.TotalFloat.{TotalFloat}
  import anthill.prelude.Float.{nan}
  import anthill.prelude.PartialEq.{eq, neq}

  sort Point
    entity point(x: Float, y: Float)
  end

  sort Pair
    entity pair(a: Int64, b: Int64)
  end

  sort Line
    entity line(from: Point, to: Point)
  end

  -- A composite wrapping the lawful TotalFloat boundary: NOT a partial carrier.
  sort WrapTF
    entity wrapTF(v: TotalFloat)
  end

  -- NaN-containing composite: field-wise eq is FALSE (nan != nan, IEEE).
  operation p_nan_eq()  -> Bool = eq(point(x: nan, y: 0.0), point(x: nan, y: 0.0))
  operation p_nan_neq() -> Bool = neq(point(x: nan, y: 0.0), point(x: nan, y: 0.0))
  -- No NaN: field-wise eq is TRUE / discriminating.
  operation p_eq()      -> Bool = eq(point(x: 1.0, y: 2.0), point(x: 1.0, y: 2.0))
  operation p_ne()      -> Bool = eq(point(x: 1.0, y: 2.0), point(x: 1.0, y: 3.0))
  -- === stays STRUCTURAL: nan === nan is true (hash-consing / dedup).
  operation p_seq_nan() -> Bool = point(x: nan, y: 0.0) === point(x: nan, y: 0.0)

  -- All-Eq composite (no Float): unaffected, structural eq is lawful.
  operation pair_eq()   -> Bool = eq(pair(a: 1, b: 2), pair(a: 1, b: 2))
  operation pair_ne()   -> Bool = eq(pair(a: 1, b: 2), pair(a: 1, b: 9))

  -- Nested: a Float buried one level deeper still follows IEEE.
  operation line_nan_eq() -> Bool =
    eq(line(from: point(x: nan, y: 0.0), to: point(x: 1.0, y: 1.0)),
       line(from: point(x: nan, y: 0.0), to: point(x: 1.0, y: 1.0)))
  operation line_eq()     -> Bool =
    eq(line(from: point(x: 1.0, y: 0.0), to: point(x: 1.0, y: 1.0)),
       line(from: point(x: 1.0, y: 0.0), to: point(x: 1.0, y: 1.0)))

  -- TotalFloat (own eq, a boundary): eq stays TRUE on nan — the lawful wrapper.
  operation tf_nan_eq() -> Bool = eq(TotalFloat(raw: nan), TotalFloat(raw: nan))
  -- A composite wrapping TotalFloat: the boundary shields the inner Float, so the
  -- structural reflexivity shortcut applies and nan-in-TotalFloat stays equal.
  operation wtf_nan_eq() -> Bool =
    eq(wrapTF(v: TotalFloat(raw: nan)), wrapTF(v: TotalFloat(raw: nan)))
end
"#;

// ── AXIS 2: interpreter (eval) field-wise semantic equality ──────────────────

/// The headline acceptance: `eq(Point(nan,_), Point(nan,_)) = false` in the
/// interpreter, AGREEING with the field-wise C++ `operator==` (the WI-645
/// divergence, one level up through composition). `neq` is its negation.
#[test]
fn point_with_nan_field_is_not_equal() {
    let mut i = interp(SRC);
    assert!(!call_bool(&mut i, "test.wi664.p_nan_eq"),
        "eq(Point(nan,0), Point(nan,0)) must be false — field-wise eq propagates IEEE nan != nan");
    assert!(call_bool(&mut i, "test.wi664.p_nan_neq"),
        "neq(Point(nan,0), Point(nan,0)) must be true");
}

/// A Float-containing composite with NO NaN behaves as an ordinary product: equal
/// iff every field is equal.
#[test]
fn point_without_nan_is_field_wise_equal() {
    let mut i = interp(SRC);
    assert!(call_bool(&mut i, "test.wi664.p_eq"),
        "eq(Point(1.0,2.0), Point(1.0,2.0)) must be true");
    assert!(!call_bool(&mut i, "test.wi664.p_ne"),
        "eq(Point(1.0,2.0), Point(1.0,3.0)) must be false (y differs)");
}

/// `===` / `struct_eq` stays STRUCTURAL — `Point(nan,_) === Point(nan,_)` is true
/// (nan === nan structural identity), unchanged by the semantic field-wise fix.
/// This is the must-not-regress half (hash-consing / dedup depend on it).
#[test]
fn struct_eq_on_composite_nan_stays_structural() {
    let mut i = interp(SRC);
    assert!(call_bool(&mut i, "test.wi664.p_seq_nan"),
        "Point(nan,_) === Point(nan,_) must stay true — struct_eq is structural");
}

/// An all-`Eq` composite (only `Int` fields) is unaffected — structural equality
/// IS its lawful equality.
#[test]
fn all_eq_composite_unaffected() {
    let mut i = interp(SRC);
    assert!(call_bool(&mut i, "test.wi664.pair_eq"), "eq(Pair(1,2), Pair(1,2)) must be true");
    assert!(!call_bool(&mut i, "test.wi664.pair_ne"), "eq(Pair(1,2), Pair(1,9)) must be false");
}

/// Nested: a `Float` two levels down (`Line(Point(nan,_), _)`) still follows IEEE
/// — the field-wise descent recurses.
#[test]
fn nested_composite_nan_recurses() {
    let mut i = interp(SRC);
    assert!(!call_bool(&mut i, "test.wi664.line_nan_eq"),
        "eq over a Line with a nested Point(nan,_) must be false");
    assert!(call_bool(&mut i, "test.wi664.line_eq"),
        "eq over two identical NaN-free Lines must be true");
}

/// `TotalFloat` is the lawful boundary: `eq(TotalFloat(nan), TotalFloat(nan))`
/// stays TRUE (its own `eq` is total/structural), and a composite WRAPPING a
/// `TotalFloat` is shielded — the inner Float is not re-laundered field-wise.
#[test]
fn totalfloat_boundary_stays_reflexive() {
    let mut i = interp(SRC);
    assert!(call_bool(&mut i, "test.wi664.tf_nan_eq"),
        "eq(TotalFloat(nan), TotalFloat(nan)) must stay true (lawful boundary)");
    assert!(call_bool(&mut i, "test.wi664.wtf_nan_eq"),
        "eq(WrapTF(TotalFloat(nan)), …) must be true — TotalFloat shields the inner Float");
}

// ── AXIS 2: resolver (SLD) field-wise semantic equality ──────────────────────

/// A `point(x, y)` term with real Float LITERAL leaves. In a rule body `nan` is a
/// symbolic const the resolver never folds, so `value_f64` can't see it; a
/// `Literal::Float` IS unwrapped, so this is what actually exercises the resolver's
/// field-wise IEEE path (the pre-existing const-folding gap is orthogonal).
fn point_term(kb: &mut KnowledgeBase, ctor: Symbol, x: Symbol, y: Symbol, xv: f64, yv: f64) -> TermId {
    use anthill_core::kb::term::Literal;
    let xt = kb.alloc(Term::Const(Literal::Float(xv.into())));
    let yt = kb.alloc(Term::Const(Literal::Float(yv.into())));
    kb.make_entity_term(ctor, SmallVec::new(), SmallVec::from_slice(&[(x, xt), (y, yt)]))
}

fn eq_goal(kb: &mut KnowledgeBase, eq_sym: Symbol, a: TermId, b: TermId) -> TermId {
    kb.alloc(Term::Fn { functor: eq_sym, pos_args: SmallVec::from_slice(&[a, b]), named_args: SmallVec::new() })
}

/// The resolver mirror (`sem_eq_core` → field-wise): resolving `eq(point(nan,0),
/// point(nan,0))` yields 0 solutions (false), while a NaN-free equal pair yields 1
/// and a field-differing pair yields 0. Keeps resolver == interpreter == codegen
/// (the WI-616/645 discipline) for Float-containing composites.
#[test]
fn resolver_field_wise_eq_agrees() {
    let mut kb = crate::common::load_kb_with(SRC);
    let cfg = ResolveConfig::default();
    let eq_sym = kb.try_resolve_symbol("anthill.prelude.PartialEq.eq").expect("PartialEq.eq");
    // The `point` constructor's functor — scanned by short name over the
    // entity registry (WI-632 retired `resolve_entity_functor`; this test just
    // needs the unique `point` ctor of its own fixture).
    let ctor = {
        let funcs: Vec<_> = kb.entity_field_type_functors().copied().collect();
        funcs.into_iter().find(|&f| kb.resolve_sym(f) == "point").expect("point constructor")
    };
    let fields = kb.entity_field_names(ctor).expect("point fields").to_vec();
    let (x, y) = (fields[0], fields[1]);

    let pnan = point_term(&mut kb, ctor, x, y, f64::NAN, 0.0);
    let g_nan = eq_goal(&mut kb, eq_sym, pnan, pnan);
    assert_eq!(kb.resolve(&[g_nan], &cfg).len(), 0,
        "eq(point(nan,0), point(nan,0)) must be false in SLD (field-wise IEEE), matching eval");

    let p12 = point_term(&mut kb, ctor, x, y, 1.0, 2.0);
    let g_eq = eq_goal(&mut kb, eq_sym, p12, p12);
    assert_eq!(kb.resolve(&[g_eq], &cfg).len(), 1,
        "eq(point(1,2), point(1,2)) must resolve (field-wise all-equal)");

    let p13 = point_term(&mut kb, ctor, x, y, 1.0, 3.0);
    let g_ne = eq_goal(&mut kb, eq_sym, p12, p13);
    assert_eq!(kb.resolve(&[g_ne], &cfg).len(), 0,
        "eq(point(1,2), point(1,3)) must not resolve (y differs)");
}

// ── AXIS 1: derived NonEq classification (load-time rejection) ───────────────

/// A user `provides Eq` over a composite with a `Float` (NonEq) field is a LOAD
/// ERROR: the composite derives `NonEq` (its field-wise eq is non-reflexive), and
/// `Eq` ⊥ `NonEq` (the WI-658 check) rejects it. The user must use `TotalFloat`
/// or give the composite its own `eq`.
#[test]
fn provides_eq_over_float_composite_is_load_error() {
    let src = r#"
namespace test.wi664.badeq
  import anthill.prelude.{Float, Eq, PartialEq}
  sort P
    entity P(x: Float)
    provides PartialEq[T = P]
    provides Eq[T = P]
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("provides both") && e.contains("NonEq") && e.contains("P")),
        "expected an Eq⊥NonEq conflict for P (a Float-containing composite); got:\n{}",
        errs.join("\n"),
    );
}

/// Review (fixpoint) — a MUTUALLY-RECURSIVE sort that reaches a `Float` through the
/// recursion is still classified `NonEq`, regardless of the (nondeterministic)
/// sort-classification order. A truncating DFS would order-dependently miss it
/// (the cycle guard poisoning its memo); the sound fixpoint does not. `Forest`
/// reaches `Float` only via `fcons.head: Tree` → `node.weight: Float`.
#[test]
fn mutually_recursive_float_sort_derives_noneq() {
    let src = r#"
namespace test.wi664.mutrec
  import anthill.prelude.{Float, Eq, PartialEq}
  sort Tree
    entity node(kids: Forest, weight: Float)
  end
  sort Forest
    entity fnil
    entity fcons(head: Tree, tail: Forest)
    provides PartialEq[T = Forest]
    provides Eq[T = Forest]
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("provides both") && e.contains("NonEq") && e.contains("Forest")),
        "Forest transitively reaches a Float through the Tree↔Forest recursion; \
         provides Eq[Forest] must be rejected (sound fixpoint); got:\n{}",
        errs.join("\n"),
    );
}

/// Review (authoritative boundary) — a Float-containing carrier whose lawful `eq`
/// is supplied by an OP-BINDING (`provides PartialEq[T=W, eq=weq]`), not a declared
/// `operation eq`, is a boundary via the SAME signal the eq-dispatch index uses, so
/// it is NOT field-wise-derived `NonEq` and `provides Eq[W]` loads clean rather than
/// false-conflicting.
#[test]
fn op_bound_eq_is_a_lawful_boundary() {
    let src = r#"
namespace test.wi664.opbound
  import anthill.prelude.{Float, Eq, PartialEq}
  sort W
    entity w(v: Float)
    operation weq(a: W, b: W) -> Bool
    rule weq(?a, ?b) :- ?a === ?b
    provides PartialEq[T = W, eq = weq]
    provides Eq[T = W]
  end
end
"#;
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("op-bound-eq carrier W must load (a lawful boundary), not false-derive NonEq; got:\n{}",
            errs.join("\n"));
    }
}

/// The dual: a user `provides Eq` over an all-`Eq` composite (no partial field)
/// is FINE — it derives `Eq`, not `NonEq`, so there is no conflict.
#[test]
fn provides_eq_over_all_eq_composite_loads_clean() {
    let src = r#"
namespace test.wi664.goodeq
  import anthill.prelude.{Int64, Eq, PartialEq}
  sort Q
    entity Q(a: Int64)
    provides PartialEq[T = Q]
    provides Eq[T = Q]
  end
end
"#;
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("expected a clean load for an all-Eq composite Q; got:\n{}", errs.join("\n"));
    }
}
