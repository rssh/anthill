//! WI-596 — type-directed `[simp]` firing for SELF-REPRESENTING container sorts
//! (`Set` / `Map`), the phase-2 companion to the phase-1 carrier-parameter case
//! (`Magma`, wi283_type_directed_guard_test.rs).
//!
//! A container spec names its carrier by the SORT ITSELF (`insert(s: Set, x: T)`,
//! `get(m: Map, …)`) and its type-parameters (`T`, `K`/`V`) are CONTENT (element /
//! key / value), constrained by the sort's `requires` (`Eq[T]`) — NOT required to
//! provide the sort. The phase-1 guard (`simp_guard_holds_core`) required EVERY
//! type-param-typed argument to `provides` the sort, which left every container law
//! dormant: `member`'s element `x: T` does not provide `Set`. Phase-2 detects the
//! self-representing shape and keys the guard on the CARRIER (sort-typed) argument,
//! ignoring content arguments — a carrier that `provides Set[T = …]` has already
//! discharged the sort's `requires` on its element (WI-343).
//!
//! These tests exercise the mechanism over a REAL provider (a concrete carrier that
//! `provides` the spec) — we do NOT lean on "nothing provides Set/Map today":
//! the guarantee is that a law fires exactly over a carrier that genuinely provides
//! the sort, and the algebraic laws hold for any valid instance, so firing there is
//! correct, not merely harmless. The final test pins that the stdlib `Set`/`Map`
//! reducing laws are now `[simp]`-tagged.

use anthill_core::kb::load::{is_equational_head, meta_has_flag};
use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// A self-representing container spec `Bag` (carrier = `Bag`, element `T`,
/// `requires Eq[T]`), a concrete carrier `IntBag` that `provides Bag[T = Int64]`,
/// and a `Plain` sort that does not. `peek` has ONLY the carrier argument;
/// `holds` additionally takes an element `x: T` the guard must IGNORE.
const SRC: &str = r#"
namespace test.wi596
  import anthill.prelude.{Int64, Bool, Eq}
  import test.wi596.Bag.{peek, holds}

  sort Bag
    sort T = ?
    requires Eq[T]
    operation {
      peek(s: Bag) -> Bool
      holds(x: T, s: Bag) -> Bool
    }
    rule {
      peek_id:  peek(?s) <=> true [simp]
      holds_id: holds(?x, ?s) <=> true [simp]
    }
  end

  sort IntBag
    entity ibag
    provides Bag[T = Int64]
  end

  sort Plain
    entity plain
  end

  sort BagUser
    operation use_peek(s: IntBag) -> Bool = peek(s)
  end
end
"#;

fn sym(kb: &KnowledgeBase, qn: &str) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("resolve {qn}"))
}

/// A nullary constructor term `f()` (`Fn { f, [], [] }`).
fn nullary(kb: &mut KnowledgeBase, qn: &str) -> anthill_core::kb::term::TermId {
    let f = sym(kb, qn);
    kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::new(), named_args: SmallVec::new() })
}

// ── resolver side: carrier-keyed firing over a real provider ──────────

#[test]
fn container_law_fires_when_carrier_provides_spec() {
    let mut kb = crate::common::load_kb_with(SRC);
    let peek = sym(&kb, "test.wi596.Bag.peek");
    let ibag = nullary(&mut kb, "test.wi596.IntBag.ibag");
    // peek(ibag()): the carrier arg's type (IntBag) provides Bag, so the
    // requires-guard holds and peek_id fires. The redex is rewritten (leaves
    // `peek`).
    let term = kb.alloc(Term::Fn {
        functor: peek,
        pos_args: SmallVec::from_slice(&[ibag]),
        named_args: SmallVec::new(),
    });
    let result = kb.simplify(term);
    assert_ne!(
        result, term,
        "peek_id must fire over a carrier that provides Bag (IntBag): peek(ibag) rewrites",
    );
    // And it must no longer be a `peek` application.
    assert!(
        !matches!(kb.get_term(result), Term::Fn { functor, .. } if *functor == peek),
        "peek(ibag) must rewrite away the peek apply, got {:?}",
        kb.get_term(result),
    );
}

#[test]
fn container_law_does_not_fire_when_carrier_lacks_spec() {
    let mut kb = crate::common::load_kb_with(SRC);
    let peek = sym(&kb, "test.wi596.Bag.peek");
    let plain = nullary(&mut kb, "test.wi596.Plain.plain");
    // peek(plain()): Plain does NOT provide Bag, so the guard fails and peek_id
    // does not fire — the redex is left intact (suspend, never NAF-decide).
    let term = kb.alloc(Term::Fn {
        functor: peek,
        pos_args: SmallVec::from_slice(&[plain]),
        named_args: SmallVec::new(),
    });
    assert_eq!(
        kb.simplify(term),
        term,
        "peek_id must NOT fire over a carrier that lacks Bag (Plain): peek(plain) is left intact",
    );
}

#[test]
fn content_argument_is_not_required_to_provide_the_sort() {
    // The discriminator between phase-2 and the naive "every type-param arg
    // provides the sort": `holds(x: T, s: Bag)`'s element `x` is `Int64`, which
    // does NOT provide Bag — only the carrier `s` does. The guard must key on the
    // carrier and IGNORE the element, so `holds(5, ibag())` FIRES. Under the
    // phase-1 rule it would (wrongly) demand `Int64` provide Bag and stay dormant.
    let mut kb = crate::common::load_kb_with(SRC);
    let holds = sym(&kb, "test.wi596.Bag.holds");
    let ibag = nullary(&mut kb, "test.wi596.IntBag.ibag");
    let five = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(5)));
    let term = kb.alloc(Term::Fn {
        functor: holds,
        pos_args: SmallVec::from_slice(&[five, ibag]),
        named_args: SmallVec::new(),
    });
    let result = kb.simplify(term);
    assert_ne!(
        result, term,
        "holds_id must fire on the carrier alone (Int64 element need not provide Bag): \
         holds(5, ibag) rewrites",
    );
    assert!(
        !matches!(kb.get_term(result), Term::Fn { functor, .. } if *functor == holds),
        "holds(5, ibag) must rewrite away the holds apply, got {:?}",
        kb.get_term(result),
    );
}

// ── typer side: op-body simplification over a provider ────────────────

#[test]
fn container_law_fires_in_typer_over_provider_body() {
    // Mirrors phase-1's typer path: `use_peek(s: IntBag) = peek(s)` — the typer's
    // `simp_fire_guard_holds` reads the carrier occurrence's type (IntBag),
    // finds it provides Bag, and rewrites the body away from a `peek` apply.
    let kb = crate::common::load_kb_with(SRC);
    let op = sym(&kb, "test.wi596.BagUser.use_peek");
    let body = kb.op_body_node(op).expect("use_peek has a body");
    let peek = sym(&kb, "test.wi596.Bag.peek");
    match body.as_expr() {
        Some(Expr::Apply { functor, .. }) => assert_ne!(
            *functor, peek,
            "peek(s) over IntBag must fire in the typer, not stay a peek apply",
        ),
        _ => { /* fired to a non-apply (the `true` literal) — as expected */ }
    }
}

// FIRING BOUNDARY (not tested here — documents why): the stdlib Set/Map laws are
// NESTED — `member(?x, insert(?s, ?x))`, `union(?s, empty())`, `get(put(?m,?k,?v),?k)`
// — so the redex's carrier argument is a spec-op subterm (`insert`/`put`/`empty`)
// whose DECLARED return is the ABSTRACT sort. On a freestanding redex that subterm's
// `value_type_term` reads abstract (`sort_provides(Set, Set)` is not reflexive), so
// the guard SUSPENDS — sound, never NAF-decides. These laws therefore fire only when
// the carrier's CONCRETE provider type flows in from context (a typer occurrence type,
// or a frame variable bound to a concrete carrier), and there is a genuine catch-22
// for the nested form: keeping the spec functor (so the law's inner pattern matches)
// vs. overriding the op to refine its return (which changes the functor). Closing
// that — carrier-aware refinement of a spec op's SELF return without changing its
// functor — is typer machinery separate from this guard, so it is not exercised here;
// the flat `peek(carrier)` / `holds(elem, carrier)` tests above verify the guard
// mechanism itself (carrier-keyed, element-ignored) over a real provider.

// ── stdlib: the reducing Set/Map laws are now [simp]-tagged ────────────

/// Does some equational rule whose LHS outer functor is `op_qn` carry `[simp]`?
fn simp_law_present(kb: &mut KnowledgeBase, op_qn: &str) -> bool {
    let op_sym = sym(kb, op_qn);
    let rule_sort = kb.make_name_term("Rule");
    let rules = kb.by_sort(rule_sort);
    for rid in rules {
        let head = kb.rule_head(rid);
        if !is_equational_head(kb, head) {
            continue;
        }
        // An equation head is `Fn { eq/unify, [lhs, rhs] }`; the LHS is arg 0.
        let lhs = match kb.get_term(head) {
            Term::Fn { pos_args, .. } if !pos_args.is_empty() => pos_args[0],
            _ => continue,
        };
        let lhs_functor = match kb.get_term(lhs) {
            Term::Fn { functor, .. } => *functor,
            _ => continue,
        };
        if lhs_functor == op_sym && meta_has_flag(kb, kb.rule_meta(rid), "simp") {
            return true;
        }
    }
    false
}

#[test]
fn stdlib_set_and_map_reducing_laws_are_simp_tagged() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert!(
        simp_law_present(&mut kb, "anthill.prelude.Set.member"),
        "the stdlib Set.member reducing law must be [simp]-tagged (WI-596 part A)",
    );
    assert!(
        simp_law_present(&mut kb, "anthill.prelude.Set.union"),
        "the stdlib Set.union reducing law must be [simp]-tagged (WI-596 part A)",
    );
    assert!(
        simp_law_present(&mut kb, "anthill.prelude.Map.get"),
        "the stdlib Map.get reducing law must be [simp]-tagged (WI-596 part A)",
    );
    assert!(
        simp_law_present(&mut kb, "anthill.prelude.Map.size"),
        "the stdlib Map.size reducing law must be [simp]-tagged (WI-596 part A)",
    );
}
