//! WI-20260929-QA700 — `BoundedLattice`'s `less_bottom` / `less_top` are LAWS
//! (`less(bottom, ?a) <=> true`), not clauses of `Lattice.less`.
//!
//! Written `less(bottom, ?a) :- true`, each was a clause of the spec operation itself.
//! A body-less spec operation with a clause of its own resolves through its clauses and
//! is never dispatched (`body_less_dispatchable`, "rules win while both exist"), so a
//! `Lattice.less` goal never reached a carrier's `less`, and the two clauses matched only
//! the unevaluated term `bottom` / `top`. Since K4JGC a goal's arguments are evaluated
//! before its head is matched, so `bottom()` reached them as the carrier's value and they
//! stopped matching even that. An equation resolves no goal; the verifier reads it as a
//! law (`wi_zz7ph_law_lowering_test`'s `BoundedLattice` row: 16 laws lowered of 16).
//!
//! A carrier that supplies no `less` is not a case: it is refused at load ("backs no
//! operation … no default on `Lattice`"), so the decision has no default body to write.
//!
//! ## Back-out
//!
//! MEASURED with `prelude/lattice.anthill`'s two laws written as clauses again
//! (`:- true`), this module alone: `a_lattice_goal_reaches_the_carriers_less`,
//! `naf_over_a_true_less_fails`, `bottom_is_read_as_its_value`, `top_is_read_as_its_value`
//! and `an_open_side_is_not_bound_to_the_term_top` fail. The
//! rows that pass either way, by design: `a_false_less_is_refuted` (the shadowed goal
//! answered nothing, which happens to be the truth there) and the CONTROL
//! `the_carriers_own_less_answers_either_way`.

use anthill_core::kb::KnowledgeBase;

/// A two-point lattice, `lo ≤ hi`. `less` is a `match`, so it is the carrier's own and
/// nothing else answers for it; `bottom()` is `lo()` and `top()` is `hi()`.
const SRC: &str = r#"
namespace qa700
  import anthill.prelude.{Lattice, BoundedLattice, PartialEq, Eq}
  import qa700.Lv.{lo, hi}

  sort Lv
    entity lo
    entity hi
    provides PartialEq[T = Lv]
    provides Eq[T = Lv]
    provides Lattice[T = Lv]
    provides BoundedLattice[T = Lv]
    operation lub(a: Lv, b: Lv) -> Lv =
      match a
        case lo() -> b
        case hi() -> hi()
    operation glb(a: Lv, b: Lv) -> Lv =
      match a
        case lo() -> lo()
        case hi() -> b
    operation less(a: Lv, b: Lv) -> Bool =
      match a
        case lo() -> true
        case hi() -> b === hi()
    operation top() -> Lv = hi()
    operation bottom() -> Lv = lo()
  end

  rule loHi(1) :- Lattice.less(lo(), hi())
  rule hiHi(1) :- Lattice.less(hi(), hi())
  rule hiLo(1) :- Lattice.less(hi(), lo())
  rule notLoHi(1) :- not(Lattice.less(lo(), hi()))
  rule notHiLo(1) :- not(Lattice.less(hi(), lo()))

  rule bottomHi(1) :- Lattice.less(BoundedLattice[T = Lv].bottom(), hi())
  rule hiTop(1) :- Lattice.less(hi(), BoundedLattice[T = Lv].top())
  rule overLo(?x) :- Lattice.less(lo(), ?x)

  -- CONTROL
  rule own(1) :- Lv.less(lo(), hi())
end
"#;

fn kb() -> KnowledgeBase {
    crate::common::load_kb_with(SRC)
}

/// The rows of `qa700.<rel>`, rendered, each with whether it is definite.
fn rows(kb: &mut KnowledgeBase, rel: &str) -> Vec<(String, bool)> {
    crate::common::shown_rows(kb, &format!("qa700.{rel}"))
}

/// `[("1", true)]` — the relation holds, definitely, once.
fn holds(kb: &mut KnowledgeBase, rel: &str) -> bool {
    rows(kb, rel) == vec![("1".to_string(), true)]
}

/// `lo ≤ hi` and `hi ≤ hi` are the carrier's `less`, reached through `Lattice.less`.
/// Before: both (0, 0) — the goal resolved through the two clauses alone.
#[test]
fn a_lattice_goal_reaches_the_carriers_less() {
    let mut kb = kb();
    assert!(holds(&mut kb, "loHi"), "{:?}", rows(&mut kb, "loHi"));
    assert!(holds(&mut kb, "hiHi"), "{:?}", rows(&mut kb, "hiHi"));
}

/// `not(less(lo, hi))` fails. Before: it held — negation as failure over the shadowed
/// goal proved a falsehood.
#[test]
fn naf_over_a_true_less_fails() {
    let mut kb = kb();
    assert_eq!(rows(&mut kb, "notLoHi"), Vec::<(String, bool)>::new());
}

/// `hi ≤ lo` is false: no answer, and `not(...)` over it holds. Passes either way, by
/// design — the shadowed goal answered nothing, which is the truth here; the row pins that
/// reaching the carrier did not make a false `less` hold.
#[test]
fn a_false_less_is_refuted() {
    let mut kb = kb();
    assert_eq!(rows(&mut kb, "hiLo"), Vec::<(String, bool)>::new());
    assert!(holds(&mut kb, "notHiLo"), "{:?}", rows(&mut kb, "notHiLo"));
}

/// `bottom()` is evaluated before the goal is matched (K4JGC) and the carrier's `less`
/// answers over its value. Before: (0, 0) — `less_bottom` matched only the unevaluated
/// term, which the evaluated argument no longer is.
#[test]
fn bottom_is_read_as_its_value() {
    let mut kb = kb();
    assert!(holds(&mut kb, "bottomHi"), "{:?}", rows(&mut kb, "bottomHi"));
}

/// `top()` likewise, on the right. Before: (0, 0), through `less_top`.
#[test]
fn top_is_read_as_its_value() {
    let mut kb = kb();
    assert!(holds(&mut kb, "hiTop"), "{:?}", rows(&mut kb, "hiTop"));
}

/// No answer binds the open side to the TERM `top`. Before: one definite answer, `?x =
/// top` — `less_top` matched `?x` against its head and bound it to the unevaluated
/// application, which is no value of `Lv`. The carrier's `less` holds of `lo` and any `b`,
/// so it answers without binding `?x`.
#[test]
fn an_open_side_is_not_bound_to_the_term_top() {
    let mut kb = kb();
    let got = rows(&mut kb, "overLo");
    assert!(!got.is_empty(), "lo is below everything: {got:?}");
    assert!(got.iter().all(|(v, _)| v != "top"), "{got:?}");
}

/// CONTROL: the carrier's own `less`, called directly, never met the clauses. Passes either
/// way, by design.
#[test]
fn the_carriers_own_less_answers_either_way() {
    let mut kb = kb();
    assert!(holds(&mut kb, "own"), "{:?}", rows(&mut kb, "own"));
}
