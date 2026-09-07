//! **WI-20260904-02ERR — A PER-SITE TYPE VARIABLE IS NOT INTERNED.**
//!
//! `TypeChild::Interned` held a `TermId`, so a variable reaching a type slot had to be
//! laundered through the term store: `Value::term(type_param_var_term(kb, Var::Global(vid)))`.
//! `kb.fresh_var` mints a brand-new `VarId` every time, so that term hash-consed with
//! nothing and nothing released it — one pinned `TermStore` slot per un-annotated binder
//! PER LOAD, unbounded in a process that loads repeatedly, against CLAUDE.md's rule that
//! transient terms are deliberately NOT interned.
//!
//! THE ARM WENT ON `TypeNode`, NOT `TypeChild`, and that placement is the ticket's
//! content. A third `TypeChild` arm would have broken an invariant argued across four
//! sites, one a live `unreachable!("a param type is Term or Node")`: a type is minted as a
//! term OR as an occurrence, THERE IS NO THIRD. `TypeNode::Var` keeps it — a variable
//! rides `TypeChild::Node(occ)` whose kind is `TypeNode::Var`, so it IS an occurrence.
//! What it costs instead is stated at the site: `TypeNode`'s membership rule was "a form
//! gets an arm iff it can TRANSITIVELY CONTAIN a `denoted`", and a variable is a LEAF, so
//! the rule widened to "…OR needs an identity of its own" — WI-20260904-DTY3B's carrier
//! rule, that a subtree is interned when it is WORTH SHARING and not merely CAPABLE of it.
//!
//! WHAT DRIVES WHAT, because "it loads clean" is not evidence here:
//!
//!   * [`an_unannotated_binder_interns_no_type_variable`] is THE ticket's property, and it
//!     measures the KIND (`interned_global_var_count`) rather than the store's total
//!     length, so unrelated vocabulary the program interns cannot mask or fake it.
//!   * [`the_binder_is_still_inferred`] is the CONTROL that keeps the property honest: a
//!     carrier that stopped interning by dropping the variable on the floor would pass the
//!     row above and fail this one.
//!   * The occurs-check, groundness and substitution rows below drive the three walks that
//!     had to learn the new arm, each with a value asserted rather than a shape.
//!
//! BACK-OUT. Restore rung 3 / the `?pat` fallback to `Value::term(type_param_var_term(..))`
//! and `an_unannotated_binder_interns_no_type_variable` fails with a non-zero count (2 for
//! this program), while every other row here PASSES — they assert behaviour that must not
//! move, which is exactly why they are the control. Remove instead the `TypeNode::Var` arm
//! in `node_occurrence::map_type_child` (the σ hook) and
//! [`a_bound_type_variable_still_substitutes`] fails while the interning row still passes:
//! the two halves are independently pinned.
//!
//! WHAT IS NOT CLOSED. `value_to_type_child` mints with the ZERO SPAN — that seam takes a
//! bare `Value` with no span to inherit — so a variable that reaches a type slot through
//! it carries no provenance. The two known producers hand their own span in; a third one
//! appearing would silently get the zero span, which is why the gap is written at the site
//! rather than left to be rediscovered.

// WI-20260827-14EV6: `literal_int64` is a `TermView` method — the carrier-neutral scalar
// read that replaced `Value::as_int`.
use anthill_core::kb::term_view::TermView;
use anthill_core::kb::KnowledgeBase;

/// A `Function`-typed ENTITY FIELD to put a lambda in — THE ONE SLOT SHAPE `data_slot_arg_hints`
/// DOES NOT HINT, so a row built on it reaches rung 3 and measures the mint and nothing else.
///
/// This fixture is the whole reason the first version of this file measured nothing: written
/// against `apply1(lambda x -> x + 1, 2)`, WI-20260904-50B2K part (b) reaches that slot with
/// the callee's declared `Function[A = Int64, B = Int64]`, the binder is typed at RUNG 2, and
/// rung 3 is never asked — so backing the mint out changed no count and every row still
/// passed. Measured, not reasoned: that is what the back-out run reported.
fn holder_src(ns: &str, body: &str) -> String {
    format!(
        "\
namespace {ns}
  import anthill.prelude.{{Int64, Function}}
  sort Holder
    entity holder(f: Function[A = Int64, B = Int64])
  end
  operation runit(h: Holder, n: Int64) -> Int64 =
    match h
      case holder(f) -> f(n)
{body}end
"
    )
}

fn load(ns: &str, body: &str) -> KnowledgeBase {
    crate::common::try_load_kb_with(&holder_src(ns, body)).unwrap_or_else(|errs| {
        panic!("{ns}: must load; got {} error(s):\n{}", errs.len(), errs.join("\n"))
    })
}

/// The one definite Int64 answer of a unary goal — the VALUE, not "something answered".
fn only_int(kb: &mut KnowledgeBase, qn: &str) -> i64 {
    let mut vs = crate::common::definite_unary(kb, qn);
    assert_eq!(vs.len(), 1, "{qn}: expected exactly one answer, got {vs:?}");
    let v = vs.pop().unwrap();
    // WI-20260827-14EV6: the carrier-neutral scalar read. `Value::as_int` is gone — a
    // scalar is read for what it DENOTES, on whatever carrier it rides.
    v.literal_int64(kb)
        .unwrap_or_else(|| panic!("{qn}: expected an Int64 answer, got {v:?}"))
}

/// An un-annotated binder in the un-hinted slot: rung 3 mints for it.
const INFERRED: &str = "  rule value(?r) :- ?r <=> runit(holder(f: lambda x -> x + 1), 2)\n";
/// The ANNOTATED twin: rung 1 wins, so nothing is minted.
const WRITTEN: &str =
    "  rule value(?r) :- ?r <=> runit(holder(f: lambda (x: Int64) -> x + 1), 2)\n";

/// **THE TICKET'S PROPERTY.** Rung 3's inference variable does not enter the hash-consed
/// store.
///
/// Measured against the ANNOTATED twin rather than against zero: the program interns
/// `Global` vars of its own, so the absolute count is not the claim — the claim is that
/// writing the annotation out, which skips the mint entirely, changes NOTHING.
///
/// CONTROL, MEASURED: restore rung 3 to `Value::term(type_param_var_term(..))` and this row
/// fails, `inferred` exceeding `written` by 1. Every other row in this file passes under
/// that back-out BY DESIGN — they assert behaviour that must not move.
#[test]
fn an_unannotated_binder_interns_no_type_variable() {
    let inferred = load("zz02err.a", INFERRED);
    let written = load("zz02err.b", WRITTEN);

    let inferred_vars = inferred.interned_global_var_count();
    let written_vars = written.interned_global_var_count();

    assert_eq!(
        inferred_vars, written_vars,
        "an un-annotated binder interned {} `Term::Var(Global)` more than its annotated \
         twin — rung 3's inference variable is being laundered through the term store \
         again (WI-20260904-02ERR)",
        inferred_vars as i64 - written_vars as i64,
    );
}

/// **THE CONTROL.** Not interning is only interesting if the binder is still INFERRED — a
/// carrier that dropped the variable on the floor would pass the row above and fail here.
/// `x + 1` pins the binder through `Additive.add`'s signature, and before WI-20260904-50B2K
/// this same program was REFUSED with "ambiguous dispatch of `Additive.add`: 3 instances".
#[test]
fn the_binder_is_still_inferred() {
    let mut kb = load("zz02err.c", INFERRED);
    assert_eq!(only_int(&mut kb, "zz02err.c.value"), 3);
}

/// **THE σ HOOK.** A bound inference variable must still substitute. Before the arm in
/// `node_occurrence::map_type_child` the occurrence carrier had no way to answer σ — the
/// walk recursed into a leaf, found no children and returned it unchanged, so a bound `?T`
/// silently stayed a variable. This program can only answer if the binder's type resolved
/// to `Int64` and `Additive` dispatched on it.
#[test]
fn a_bound_type_variable_still_substitutes() {
    let mut kb = load(
        "zz02err.d",
        "  rule value(?r) :- ?r <=> runit(holder(f: lambda y -> y + 2), 5)\n",
    );
    assert_eq!(only_int(&mut kb, "zz02err.d.value"), 7);
}

/// The annotated twin is UNMOVED — it never reaches rung 3, so it is the row that would
/// catch the change leaking into the path that was already correct.
#[test]
fn the_annotated_twin_is_unmoved() {
    let mut kb = load("zz02err.e", WRITTEN);
    assert_eq!(only_int(&mut kb, "zz02err.e.value"), 3);
}

/// **THE VAR-TO-VAR CHAIN**, which `/code-review` found the rows above cannot reach.
///
/// `SubstTypeRewrite::var` answers a bound variable with the type its binding DENOTES, and
/// `type_denoted_by`'s own `Value::Var` arm `alloc_from_value`s a `Term::Var` — so a
/// binding `?T ↦ ?U`, which unification produces routinely, re-interned the very per-site
/// global this ticket removes, while every row above stayed green. The arm now keeps the
/// occurrence carrier for a var-to-var answer.
///
/// An ALIAS is the shape that produces the chain: `g` is `f`, so `g`'s type variable is
/// bound to `f`'s rather than to a concrete type.
#[test]
fn an_alias_of_an_inferred_lambda_interns_no_type_variable() {
    const ALIASED: &str = "  \
       rule value(?r) :- ?r <=> runit(holder(f: lambda x -> x + 1), 2)\n  \
       rule aliased(?r) :- ?r <=> runit(holder(f: lambda z -> z + 1), 3)\n";
    const ALIASED_ANN: &str = "  \
       rule value(?r) :- ?r <=> runit(holder(f: lambda (x: Int64) -> x + 1), 2)\n  \
       rule aliased(?r) :- ?r <=> runit(holder(f: lambda (z: Int64) -> z + 1), 3)\n";
    let inferred = load("zz02err.h", ALIASED);
    let written = load("zz02err.i", ALIASED_ANN);
    assert_eq!(
        inferred.interned_global_var_count(),
        written.interned_global_var_count(),
        "an inferred binder chain interned more `Term::Var(Global)` than its annotated twin",
    );

    let mut kb = load("zz02err.j", ALIASED);
    assert_eq!(only_int(&mut kb, "zz02err.j.aliased"), 4, "the second binder must infer too");
}
