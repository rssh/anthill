//! WI-283 — type-directed, guard-aware `[simp]` firing in the typer.
//!
//! A `[simp]` rule scoped to a parametric (spec) sort — e.g.
//! `Magma.op2(?a, ?b) = ?a` on `sort Magma[T] requires Eq[T]` — carries
//! that sort's `requires` implicitly. Its law holds only for carriers that
//! *satisfy* the sort, so the engine fires it only where the receiver's
//! type provides the spec (`simp_fire_guard_holds` → `min_sort` +
//! `sort_provides`). These tests load such a rule from source and pin both
//! sides of the guard:
//!   - it fires on a receiver whose type provides the spec (`Int64`); and
//!   - it does **not** fire on a receiver whose type does not (`Bool`) —
//!     guard-free firing there would erase an unsatisfied call (unsound).
//!
//! Loading a `[simp]` rule from source also exercises the canonical-`eq`
//! lookup (`KnowledgeBase::eq_functor`): loaded equations are headed by
//! `anthill.prelude.Eq.eq`, not a bare `eq`, so the firing index must key
//! on the former — the synthetic `wi283_typer_firing_test` rules can't
//! catch a regression there.

use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::term::{Literal, Term};
use smallvec::SmallVec;

/// A parametric spec sort `Magma[T] requires Eq[T]` with a `[simp]`
/// identity, `fact Magma[T = Int64]`, and two call sites: one over `Int64`
/// (provides Magma) and one over `Bool` (does not).
const SRC: &str = r#"
namespace test.wi283guard
  import anthill.prelude.{Int64, Bool, Eq}
  import test.wi283guard.Magma.{op2}

  sort Magma
    sort T = ?
    requires Eq[T]
    operation {
      op2(a: T, b: T) -> T
    }
    rule {
      op2_id: op2(?a, ?b) = ?a [simp]
    }
  end

  fact Magma[T = Int64]

  sort IntUser
    operation use_int(a: Int64, b: Int64) -> Int64 = op2(a, b)
  end

  sort BoolUser
    operation use_bool(a: Bool, b: Bool) -> Bool = op2(a, b)
  end
end
"#;

#[test]
fn simp_rule_fires_where_receiver_provides_the_spec() {
    let kb = crate::common::load_kb_with(SRC);
    let op = kb
        .try_resolve_symbol("test.wi283guard.IntUser.use_int")
        .expect("use_int symbol");
    let body = kb.op_body_node(op).expect("use_int has a body");
    // op2(a, b) over Int64 (Int64 provides Magma) → rewritten to its first
    // argument `a`, a parameter reference. The redex is gone.
    assert!(
        matches!(body.as_expr(), Some(Expr::VarRef { .. })),
        "op2_id must fire over Int64 (Int64 provides Magma): op2(a,b) → a; got {:?}",
        body.as_expr(),
    );
}

#[test]
fn simp_rule_does_not_fire_where_receiver_lacks_the_spec() {
    let kb = crate::common::load_kb_with(SRC);
    let op = kb
        .try_resolve_symbol("test.wi283guard.BoolUser.use_bool")
        .expect("use_bool symbol");
    let body = kb.op_body_node(op).expect("use_bool has a body");
    // op2(a, b) over Bool (Bool does NOT provide Magma) → the guard blocks
    // firing; the call stays an Apply of the spec op. Firing here would
    // erase a call whose `requires Eq[T]` / `Magma[T = Bool]` is unmet.
    match body.as_expr() {
        Some(Expr::Apply { functor, .. }) => {
            let qn = kb.qualified_name_of(*functor);
            assert!(
                qn.ends_with("Magma.op2"),
                "expected the unfired op2 apply, got functor {qn}",
            );
        }
        other => panic!("op2_id must NOT fire over Bool; expected op2 apply, got {other:?}"),
    }
}

// ── carrier is not the leading argument ──────────────────────────────
//
// The guard must test the *carrier* argument(s) — those declared with the
// spec sort's type-parameter — not a positional shortcut. Here `Box.wrap`'s
// carrier `x: T` is the SECOND parameter; the first, `tag: Int64`, is a
// non-carrier whose type (`Int64`) happens to provide `Box`. A guard keyed on
// arg 0 would read `tag`'s sort, find `Int64` provides `Box`, and wrongly fire
// regardless of the real carrier `x` — erasing a call where `x`'s type does
// not satisfy `Box`.
const SRC_CARRIER: &str = r#"
namespace test.wi283carrier
  import anthill.prelude.{Int64, Bool, Eq}
  import test.wi283carrier.Box.{wrap}

  sort Box
    sort T = ?
    requires Eq[T]
    operation {
      wrap(tag: Int64, x: T) -> T
    }
    rule {
      wrap_id: wrap(?tag, ?x) = ?x [simp]
    }
  end

  fact Box[T = Int64]

  sort GoodUser
    operation use_int(x: Int64) -> Int64 = wrap(5, x)
  end

  sort BadUser
    operation use_bool(x: Bool) -> Bool = wrap(5, x)
  end
end
"#;

#[test]
fn guard_tests_the_carrier_arg_not_arg0_positive() {
    // Carrier `x` (arg 1) is Int64, which provides Box → fires to `x`, even
    // though the carrier is not the leading argument.
    let kb = crate::common::load_kb_with(SRC_CARRIER);
    let op = kb
        .try_resolve_symbol("test.wi283carrier.GoodUser.use_int")
        .expect("use_int symbol");
    let body = kb.op_body_node(op).expect("use_int has a body");
    assert!(
        matches!(body.as_expr(), Some(Expr::VarRef { .. })),
        "wrap_id must fire when the carrier arg (x: Int64, arg 1) provides Box: \
         wrap(5, x) → x; got {:?}",
        body.as_expr(),
    );
}

#[test]
fn guard_tests_the_carrier_arg_not_arg0_negative() {
    // Carrier `x` (arg 1) is Bool, which does NOT provide Box → must NOT
    // fire, even though arg 0 (`tag: Int64`) is a type that DOES provide Box.
    // This is the unsoundness an arg-0 guard would introduce.
    let kb = crate::common::load_kb_with(SRC_CARRIER);
    let op = kb
        .try_resolve_symbol("test.wi283carrier.BadUser.use_bool")
        .expect("use_bool symbol");
    let body = kb.op_body_node(op).expect("use_bool has a body");
    match body.as_expr() {
        Some(Expr::Apply { functor, .. }) => {
            let qn = kb.qualified_name_of(*functor);
            assert!(
                qn.ends_with("Box.wrap"),
                "expected the unfired wrap apply, got functor {qn}",
            );
        }
        other => panic!(
            "wrap_id must NOT fire when the carrier x: Bool lacks Box, even though \
             arg 0 (Int64) provides it; got {other:?}",
        ),
    }
}

// ── resolver side: requires-guarded rules fire via the carried type ───
//
// WI-292: the resolver's equational fallback (`simplify`/`apply_eq_rules`)
// now reads the redex's CARRIED type (the WI-578 typed-value substrate,
// `value_type_term`) to honor a sort's `requires`. A requires-guarded
// spec-op rule fires exactly where the carrier arguments' carried types
// provide the spec, and is skipped (the redex left intact) where they don't
// — never NAF-deciding an undecided guard (WI-067). `op2(5, 7)` over `Int64`
// (which provides Magma via `fact Magma[T = Int64]`) rewrites to its first
// argument; `op2(true, false)` over `Bool` (no such fact) is left untouched.

#[test]
fn resolver_fires_requires_guarded_equation_when_carrier_provides_spec() {
    let mut kb = crate::common::load_kb_with(SRC);
    let op2 = kb
        .try_resolve_symbol("test.wi283guard.Magma.op2")
        .expect("op2 symbol");
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let term = kb.alloc(Term::Fn {
        functor: op2,
        pos_args: SmallVec::from_slice(&[five, seven]),
        named_args: SmallVec::new(),
    });
    // op2(5, 7) → 5: Int64 provides Magma, so the carried-type guard holds and
    // op2_id fires. Compare by VALUE — the instantiated RHS (WI-584) carries the
    // matched `5`, which need not be the same TermId the test allocated.
    let result = kb.simplify(term);
    assert_eq!(
        kb.get_term(result),
        &Term::Const(Literal::Int(5)),
        "the resolver must fire the requires-guarded op2_id over Int64 (which \
         provides Magma): op2(5, 7) → 5; got {:?}",
        kb.get_term(result),
    );
}

#[test]
fn resolver_does_not_fire_requires_guarded_equation_when_carrier_lacks_spec() {
    let mut kb = crate::common::load_kb_with(SRC);
    let op2 = kb
        .try_resolve_symbol("test.wi283guard.Magma.op2")
        .expect("op2 symbol");
    let t = kb.alloc(Term::Const(Literal::Bool(true)));
    let f = kb.alloc(Term::Const(Literal::Bool(false)));
    let term = kb.alloc(Term::Fn {
        functor: op2,
        pos_args: SmallVec::from_slice(&[t, f]),
        named_args: SmallVec::new(),
    });
    // op2(true, false): Bool does NOT provide Magma (no `fact Magma[T = Bool]`),
    // so the carried-type guard fails and op2_id does NOT fire — the term is left
    // intact. Firing here would erase a call whose `requires Eq[T]` is unmet.
    assert_eq!(
        kb.simplify(term),
        term,
        "the resolver must NOT fire the requires-guarded op2_id over Bool \
         (which does not provide Magma): op2(true, false) is left intact",
    );
}

// ── resolver side: a NON-[simp] requires-guarded law must NOT fire ────
//
// WI-292 termination guard. `apply_eq_rules` fires via the discrimination tree,
// which RETAINS equational rules that load `unindex_functor`s for lacking a
// `[simp]`/`[unfold]` tag (the tag is cleared only from `rules_by_functor`). A
// plain LAW in a requires-bearing spec sort — here commutativity
// `flip(?a, ?b) = flip(?b, ?a)` — is a candidate AND its carrier (Int64) provides
// the spec, so the type guard alone would fire it; firing a non-reducing law
// directionally ping-pongs to fuel exhaustion. The directional-rewrite gate
// (`equation_is_directional_rewrite`) is what leaves it intact — the same gate
// the typer's `simp_rewrite` applies, now mirrored in the resolver.
const SRC_NONSIMP: &str = r#"
namespace test.wi292nonsimp
  import anthill.prelude.{Int64, Eq}
  import test.wi292nonsimp.Flippy.{flip}

  sort Flippy
    sort T = ?
    requires Eq[T]
    operation {
      flip(a: T, b: T) -> T
    }
    rule {
      flip_comm: flip(?a, ?b) = flip(?b, ?a)
    }
  end

  fact Flippy[T = Int64]
end
"#;

#[test]
fn resolver_does_not_fire_non_simp_requires_guarded_law() {
    let mut kb = crate::common::load_kb_with(SRC_NONSIMP);
    let flip = kb
        .try_resolve_symbol("test.wi292nonsimp.Flippy.flip")
        .expect("flip symbol");
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let term = kb.alloc(Term::Fn {
        functor: flip,
        pos_args: SmallVec::from_slice(&[five, seven]),
        named_args: SmallVec::new(),
    });
    // flip_comm is requires-guarded (Flippy requires Eq) and Int64 provides Flippy,
    // so the type guard would pass — but it is NOT [simp]-tagged, so it is a
    // non-directional law that must not fire. `apply_eq_rules` must report NO
    // changes (firing commutativity would ping-pong to the 100-fuel cap).
    let (result, changes) =
        kb.apply_eq_rules(term, 100, &anthill_core::kb::subst::Substitution::new());
    assert!(
        changes.is_empty(),
        "non-[simp] requires-guarded flip_comm must NOT fire (firing it would loop); \
         got {} change(s)",
        changes.len(),
    );
    assert_eq!(result, term, "the term must be left intact");
}
