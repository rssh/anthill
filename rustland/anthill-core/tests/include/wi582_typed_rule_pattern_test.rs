//! WI-582 — explicit typed rule patterns (`?x: T`).
//!
//! The EXPLICIT surface for type-directed rules: a `: T` annotation on a rule
//! LHS pattern variable. Distinct from the IMPLICIT path (WI-292), where a
//! `[simp]` rule inherits its enclosing sort's `requires`. Here the rule is a
//! bare top-level relation in NO requires-sort, so the implicit guard is
//! inapplicable — the explicit `?x: Summable` bound is the deciding guard.
//!
//! Semantics (the desugaring): `keep(?x: Summable, ?y) = ?x` MEANS
//! `keep(?x, ?y) = ?x :- conforms(typeof(?x), Summable)`. The loader STRIPS the
//! annotation from the head (so the discrimination tree indexes `keep(?x, ?y)`
//! identically to the untyped form — carrier-neutral, M1) and installs the bound
//! as a per-variable `Type` constraint keyed by the variable's DeBruijn index
//! (`install_rule_type_bounds`). At fire, `apply_eq_rules` reads each matched
//! value's CARRIED type (WI-578, `value_type_term`) and checks it conforms —
//! firing where it does, suspending (leaving the redex) where it does not or the
//! type is under-determined (never NAF-deciding an undecided guard; WI-067).

use anthill_core::kb::term::{Literal, Term};
use smallvec::SmallVec;

/// A parametric spec sort `Summable` that `Int64` provides (`fact
/// Summable[T = Int64]`) and `Bool` does not, plus an operation `keep[A]` in a
/// PLAIN sort (`Lib`, no `requires`) with a `[simp]` rule carrying an explicit
/// typed pattern `keep(?x: Summable, ?y) = ?x`. Because `Lib` declares no
/// `requires`, the IMPLICIT guard (WI-292) is inapplicable: only the EXPLICIT
/// per-variable bound `?x: Summable` gates firing. The annotation is stripped
/// from the head before the typer sees it, so it does not collide with the
/// signature's `x: A`.
const SRC: &str = r#"
namespace test.wi582
  import anthill.prelude.{Int64, Bool, Eq}
  import test.wi582.Lib.{keep}

  sort Summable
    sort T = ?
    requires Eq[T]
  end

  fact Summable[T = Int64]

  sort Lib
    sort A = ?
    operation {
      keep(x: A, y: A) -> A
    }
    rule {
      keep_id: keep(?x: Summable, ?y) = ?x [simp]
    }
  end
end
"#;

#[test]
fn typed_pattern_bound_installed_on_rule() {
    let kb = crate::common::load_kb_with(SRC);
    // The explicit `?x: Summable` bound is stripped from the head and recorded
    // as a per-variable Type bound, keyed by the variable's DeBruijn index.
    // The rule's head functor is `Eq.eq` (it is an equation), so look it up by
    // its citation label `keep_id`, not by the `keep` operation symbol.
    let rid = kb
        .rule_id_by_qn("test.wi582.Lib.keep_id")
        .expect("keep_id rule loaded");
    let bounds = kb.rule_type_bounds(rid);
    assert_eq!(
        bounds.len(),
        1,
        "keep must carry exactly one typed-pattern bound (?x: Summable); got {bounds:?}",
    );
    // ?x is the FIRST head variable (globals[0]); the DeBruijn convention is
    // reversed (index = arity - 1 - position), so for the 2-var head keep(?x, ?y)
    // ?x's DeBruijn index is 1, not 0. (Storing the raw position 0 was the bug the
    // mixed-type firing test guards.)
    assert_eq!(bounds[0].0, 1, "the bound must key ?x's DeBruijn index (arity-1-0 = 1)");
}

#[test]
fn typed_pattern_fires_when_carrier_provides_the_bound() {
    let mut kb = crate::common::load_kb_with(SRC);
    let keep = kb
        .try_resolve_symbol("test.wi582.Lib.keep")
        .expect("keep symbol");
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let term = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[five, seven]),
        named_args: SmallVec::new(),
    });
    // keep(5, 7): ?x = 5, carried type Int64, which provides Summable → the
    // explicit bound holds → the rule fires → 5. Compare by VALUE (the
    // instantiated RHS carries the matched 5; WI-584).
    let result = kb.simplify(term);
    assert_eq!(
        kb.get_term(result),
        &Term::Const(Literal::Int(5)),
        "keep must fire over Int64 (which provides Summable): keep(5, 7) → 5; got {:?}",
        kb.get_term(result),
    );
}

#[test]
fn typed_pattern_suspends_when_carrier_lacks_the_bound() {
    let mut kb = crate::common::load_kb_with(SRC);
    let keep = kb
        .try_resolve_symbol("test.wi582.Lib.keep")
        .expect("keep symbol");
    let t = kb.alloc(Term::Const(Literal::Bool(true)));
    let f = kb.alloc(Term::Const(Literal::Bool(false)));
    let term = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[t, f]),
        named_args: SmallVec::new(),
    });
    // keep(true, false): ?x = true, carried type Bool, which does NOT provide
    // Summable → the explicit bound fails → the rule does NOT fire (the redex is
    // left intact). Firing here would erase a call whose `?x: Summable` is unmet.
    assert_eq!(
        kb.simplify(term),
        term,
        "keep must NOT fire over Bool (which lacks Summable): keep(true, false) is left intact",
    );
}

#[test]
fn typed_pattern_checks_the_annotated_variable_not_a_sibling() {
    // MIXED-type arguments: the bound is on ?x (the first arg). A wrong-variable
    // bug — e.g. a DeBruijn-index mismatch that reads ?y instead of ?x — would
    // invert both assertions. Same-typed args (5,7 / true,false) cannot catch it.
    let mut kb = crate::common::load_kb_with(SRC);
    let keep = kb
        .try_resolve_symbol("test.wi582.Lib.keep")
        .expect("keep symbol");
    // keep(5, true): ?x = 5 (Int64 provides Summable) → FIRES to 5, regardless of
    // ?y = true (Bool, which does NOT provide Summable). The guard is on ?x only.
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let tru = kb.alloc(Term::Const(Literal::Bool(true)));
    let fire = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[five, tru]),
        named_args: SmallVec::new(),
    });
    let fire_res = kb.simplify(fire);
    assert_eq!(
        kb.get_term(fire_res),
        &Term::Const(Literal::Int(5)),
        "guard is on ?x: keep(5, true) must fire on ?x=Int64 (ignoring ?y=Bool); got {:?}",
        kb.get_term(fire_res),
    );
    // keep(true, 5): ?x = true (Bool lacks Summable) → SUSPENDS, even though
    // ?y = 5 (Int64) provides it. A bug reading ?y would wrongly fire here.
    let tru2 = kb.alloc(Term::Const(Literal::Bool(true)));
    let five2 = kb.alloc(Term::Const(Literal::Int(5)));
    let susp = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[tru2, five2]),
        named_args: SmallVec::new(),
    });
    assert_eq!(
        kb.simplify(susp),
        susp,
        "guard is on ?x: keep(true, 5) must suspend on ?x=Bool (ignoring ?y=Int64)",
    );
}

/// The `[T]` type-variable-introducer form `keep[T](?x: T, ?y) = ?x :- Summable[T]`
/// — the verbose spelling of the inline `keep(?x: Summable, ?y) = ?x`. The loader
/// desugars it: the head introduces `T`, the guard `:- Summable[T]` bounds it, and
/// `?x: T` folds to the bound `Summable`. It must load and fire identically.
const SRC_TP: &str = r#"
namespace test.wi582tp
  import anthill.prelude.{Int64, Bool, Eq}
  import test.wi582tp.Lib.{keep}

  sort Summable
    sort T = ?
    requires Eq[T]
  end

  fact Summable[T = Int64]

  sort Lib
    sort A = ?
    operation {
      keep(x: A, y: A) -> A
    }
    rule {
      keep_id: keep[T](?x: T, ?y) = ?x :- Summable[T] [simp]
    }
  end
end
"#;

#[test]
fn tparam_form_folds_guard_into_bound_and_fires() {
    let mut kb = crate::common::load_kb_with(SRC_TP);
    // Desugared: the head-introduced `T` bounded by `:- Summable[T]` folds into
    // `?x: Summable`, installed as the single per-variable bound.
    let rid = kb
        .rule_id_by_qn("test.wi582tp.Lib.keep_id")
        .expect("keep_id rule loaded");
    let bounds = kb.rule_type_bounds(rid);
    assert_eq!(
        bounds.len(),
        1,
        "the [T] form must install one folded bound (?x: Summable); got {bounds:?}",
    );
    // ?x's DeBruijn index in the 2-var head keep(?x, ?y) is arity-1-0 = 1.
    assert_eq!(bounds[0].0, 1, "the bound must key ?x's DeBruijn index (1)");

    let keep = kb
        .try_resolve_symbol("test.wi582tp.Lib.keep")
        .expect("keep symbol");
    // Fires over Int64 (provides Summable).
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let pos = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[five, seven]),
        named_args: SmallVec::new(),
    });
    let pos_res = kb.simplify(pos);
    assert_eq!(
        kb.get_term(pos_res),
        &Term::Const(Literal::Int(5)),
        "[T] form must fire over Int64: keep(5, 7) → 5; got {:?}",
        kb.get_term(pos_res),
    );
    // Suspends over Bool (does not provide Summable).
    let t = kb.alloc(Term::Const(Literal::Bool(true)));
    let f = kb.alloc(Term::Const(Literal::Bool(false)));
    let neg = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[t, f]),
        named_args: SmallVec::new(),
    });
    assert_eq!(
        kb.simplify(neg),
        neg,
        "[T] form must NOT fire over Bool: keep(true, false) left intact",
    );
}
