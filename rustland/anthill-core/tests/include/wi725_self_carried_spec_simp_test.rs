//! WI-725 — a MACRO-headed `[simp]` rule is a definitional LOWERING, not a
//! conditional typeclass law, so it fires WITHOUT the spec-op carrier guard.
//!
//! The `[simp]` firing guard (`simp_fire_guard_holds`) gates a spec-op law on the
//! carrier PROVIDING the spec — sound for an algebraic law (`get(put(m,k,v),k) <=>
//! some(v)` holds only for a real Map). But `sort_provides` is not reflexive, so a
//! value typed DIRECTLY at a constructor-less abstract self-carrier sort (a rule
//! reference `Relation[schema]` — the WI-714 `where` receiver) never satisfies the
//! guard for a law on its OWN sort: `sort_provides(Relation, Relation)` is false.
//! Making the guard reflexive would ALSO fire the Map/Set reducing laws on abstract
//! carriers, whose value RHS then breaks at eval (the WI-611 catch-22).
//!
//! The fix keys on the RHS: a rule whose RHS is a MACRO (`where <=> guarded_of`) is a
//! compile-time syntax→syntax lowering — the macro is its own validity check, so it
//! bypasses the carrier guard; a value-RHS law stays gated. This test uses a self-
//! carrier spec `Widget` whose body-less op `flip` has a macro-RHS lowering; the
//! consumer `use_flip(w: Widget) = flip(w)` rewrites at compile time to the macro's
//! output `noted(w)`. WITHOUT the bypass the guard leaves `flip` — a body-less spec
//! op with no Widget provider — dormant, and the load fails (a MissingRequires on the
//! undischarged self-sort); the sibling `map_builtins_test::proposal_acceptance_fixture`
//! pins the dual (a value-RHS Map law still does NOT fire on an abstract carrier).

use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::KnowledgeBase;

const SRC: &str = r#"
namespace test.wi725
  import anthill.prelude.{Int64}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{NodeOccurrence, make_apply}
  import test.wi725.Widget.{flip}

  -- A constructor-less ABSTRACT self-carrier spec (carrier = Widget itself), like
  -- Relation/Stream: `flip` is a body-less SPEC OP whose carrier `w: Widget` is the
  -- sort. The [simp] firing guard would demand sort_provides(Widget, Widget) (false).
  sort Widget
    sort T = ?
    operation flip(w: Widget) -> Int64
    -- MACRO-RHS lowering: bypasses the carrier guard (WI-725).
    rule flip(?w) <=> flip_macro(?w) [simp]
  end

  -- The macro (occurrence→occurrence): builds `noted(w)`, reusing the arg occurrence.
  operation flip_macro(w: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi725.noted", cons(w, nil()), w)

  -- The macro's concrete output target — an ordinary (non-spec) op, so calling it on
  -- an abstract Widget carries no spec obligation.
  operation noted(w: Widget) -> Int64 = 7

  -- Consumer: `flip(w)` with `w` typed at the abstract self-carrier Widget. Its stored
  -- body rewrites to `noted(w)` at compile time IFF the macro-RHS bypass fires.
  operation use_flip(w: Widget) -> Int64 = flip(w)
end
"#;

fn sym(kb: &KnowledgeBase, qn: &str) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("resolve {qn}"))
}

/// `use_flip(w: Widget) = flip(w)` — `flip` is a body-less spec op on the abstract
/// self-carrier `Widget`, and its `[simp]` rule has a MACRO RHS, so the WI-725 bypass
/// fires it at compile time: the stored body becomes the macro output `noted(w)`, NOT
/// a dormant `flip` apply. Without the bypass the guard blocks it (`sort_provides(
/// Widget, Widget)` is false) and the load fails, so a successful load + a `noted`
/// head is the proof.
#[test]
fn macro_rhs_lowering_fires_on_abstract_self_carrier() {
    let kb = crate::common::load_kb_with(SRC);
    let op = sym(&kb, "test.wi725.use_flip");
    let body = kb.op_body_node(op).expect("use_flip has a body");
    let flip = sym(&kb, "test.wi725.Widget.flip");
    let noted = sym(&kb, "test.wi725.noted");
    match body.as_expr() {
        Some(Expr::Apply { functor, .. }) => {
            assert_ne!(*functor, flip, "the flip redex must be lowered, not left dormant");
            assert_eq!(
                *functor, noted,
                "the macro-RHS lowering must rewrite `flip(w)` to its output `noted(w)` (WI-725)",
            );
        }
        other => panic!("expected `noted(w)` apply, got {other:?}"),
    }
}
