//! WI-664 — composite `Eq`/`NonEq` derivation (proposal 004 / library, WI-644).
//!
//! Equality lawfulness PROPAGATES from a composite's fields, mirroring Rust's
//! `derive`: an entity / named-tuple is a lawful `Eq` iff every field is `Eq`, and
//! is `NonEq` (partial) if any field is `NonEq` (reaches an IEEE `Float`). The two
//! coupled halves this module owns:
//!
//! * **Classification** ([`run`]) — a sort is PARTIAL iff it (transitively) reaches
//!   an IEEE `Float` leaf (a `NonEq` provider) through composite fields, WITHOUT
//!   crossing a lawful-Eq BOUNDARY. Computed as a monotone FIXPOINT over the
//!   field-reference graph (not a truncating DFS), so it is sound for recursive and
//!   mutually-recursive sorts. A boundary is a sort whose `eq` is its OWN — a
//!   declared `operation eq` OR an op-bound provision (`fact PartialEq[T=X, eq=…]`)
//!   — the SAME authoritative signal the eq-dispatch index uses
//!   (`build_sort_ops_table` pass 3), so the classifier's boundary is exactly the
//!   resolver's dispatch boundary. That is what keeps `TotalFloat` (a `Float`
//!   wrapper that declares its own total `eq`) lawfully `Eq` — and shields a
//!   composite that wraps it — while a plain `Point(x: Float, y: Float)` becomes
//!   `NonEq`.
//!
//! * **Behavior wiring** — [`KnowledgeBase::field_wise_noneq_carriers`] (the
//!   constructor functors of `Partial` sorts) is what the resolver's `sem_eq_core`
//!   and the interpreter's `semantic_equal` read (via
//!   [`KnowledgeBase::value_reaches_partial_carrier`]) to compare such a value
//!   FIELD-WISE instead of taking the structural reflexivity shortcut — so
//!   `eq(Point(nan,_), Point(nan,_))` reduces to `eq(nan,nan) ∧ … = false`,
//!   agreeing with the field-wise C++ `operator==`.
//!
//! [`run`] also asserts the derived `NonEq`+`PartialEq` provision facts for each
//! `Partial` composite so a user `provides Eq[Point]` conflicts with the derived
//! `NonEq[Point]` at load (the WI-658 `check_eq_noneq_exclusive` route — "composes
//! automatically"). It runs AFTER the provider-coverage checks (so a derived
//! `NonEq`'s witness `nonEqRefl` is not held to op-backing: it is a propagated
//! classification, witnessed by the partial field, not a hand-declared primitive)
//! and BEFORE `check_eq_noneq_exclusive`.
//!
//! SCOPE (proposal 004 / WI-664): entities + named tuples with CONCRETE fields. A
//! partial leaf reached only THROUGH a parametric container (`Option[Float]`,
//! `List[Float]`, `Set`/`Map` over `Float`) is the documented "parametric-container
//! propagation" follow-up — `sort_functor_of_view` resolves a field's type to its
//! BASE sort (`Option`), whose element param is abstract, so the concrete `Float`
//! argument is not seen and such a composite classifies non-partial. It is left
//! non-partial (conservative: structural eq, no derived `NonEq`), NOT silently
//! claimed handled.

use std::collections::HashSet;

use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::Symbol;
use crate::kb::term::{Literal, Term};
use crate::kb::term_view::{TermView, ViewHead};
use crate::kb::KnowledgeBase;

/// WI-664 entry point (a post-load pass). See the module header for placement.
pub(crate) fn run(kb: &mut KnowledgeBase) {
    let noneq_sym = kb.try_resolve_symbol("anthill.prelude.NonEq");
    let partialeq_sym = kb.try_resolve_symbol("anthill.prelude.PartialEq");
    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq");
    let eq_spec = kb.try_resolve_symbol("anthill.prelude.PartialEq.eq");
    let eq_short = kb.intern("eq");

    // Every composite carrier sort: data sorts (with variant constructors) plus
    // free-standing entities (their own sort).
    let sorts = composite_sorts(kb);

    // Lawful-Eq BOUNDARIES (canonical), by the authoritative eq-dispatch signal.
    let boundary: HashSet<Symbol> = sorts
        .iter()
        .filter(|&&s| is_eq_boundary(kb, s, eq_spec, eq_short, partialeq_sym, eq_sym))
        .map(|&s| kb.canonical_sort_sym(s))
        .collect();

    // Each composite's field sorts (canonical), computed once for the fixpoint.
    let field_sorts: Vec<(Symbol, Vec<Symbol>)> = sorts
        .iter()
        .map(|&s| {
            let fs = composite_field_sorts(kb, s)
                .into_iter()
                .map(|f| kb.canonical_sort_sym(f))
                .collect();
            (kb.canonical_sort_sym(s), fs)
        })
        .collect();

    // PARTIAL set (canonical), seeded with the pre-existing `NonEq` leaves (`Float`)
    // and grown to a monotone fixpoint: a NON-BOUNDARY composite becomes Partial
    // once any of its field sorts is Partial. A boundary sort is never added and
    // blocks propagation through it (`WrapTF(v: TotalFloat)` stays non-partial).
    let mut partial: HashSet<Symbol> = noneq_provider_sorts(kb, noneq_sym)
        .into_iter()
        .map(|s| kb.canonical_sort_sym(s))
        .collect();
    loop {
        let mut changed = false;
        for (cs, fsorts) in &field_sorts {
            if boundary.contains(cs) || partial.contains(cs) {
                continue;
            }
            if fsorts.iter().any(|f| partial.contains(f)) {
                partial.insert(*cs);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Build the field-wise carrier set + derive `NonEq`/`PartialEq` for each Partial
    // composite. (Leaf `NonEq` providers like `Float` are in `partial` but not in
    // `sorts`, so they neither add constructors nor re-derive.)
    let mut field_wise: HashSet<Symbol> = HashSet::new();
    let mut derive: Vec<Symbol> = Vec::new();
    for &s in &sorts {
        if partial.contains(&kb.canonical_sort_sym(s)) {
            for ctor in kb.field_constructors_of_sort(s) {
                field_wise.insert(ctor);
            }
            derive.push(s);
        }
    }
    kb.field_wise_noneq_carriers = field_wise;

    for s in derive {
        if let Some(ne) = noneq_sym {
            if !super::typing::sort_provides(kb, s, ne) {
                assert_provides(kb, s, ne);
            }
        }
        if let Some(pe) = partialeq_sym {
            if !super::typing::sort_provides(kb, s, pe) {
                assert_provides(kb, s, pe);
            }
        }
    }
}

/// Every composite carrier sort: data sorts (with variant constructors) plus
/// free-standing entities (their own sort). Derived from the entity-field-type
/// registry — one entry per constructor that carries a field schema — mapping each
/// constructor to its owning sort.
fn composite_sorts(kb: &KnowledgeBase) -> Vec<Symbol> {
    let mut sorts: Vec<Symbol> = Vec::new();
    let mut seen: HashSet<Symbol> = HashSet::new();
    let ctor_functors: Vec<Symbol> = kb.entity_field_type_functors().copied().collect();
    for ctor in ctor_functors {
        // A variant maps to its parent sort; a free-standing entity is its own sort.
        // `constructor_parent_sort` yields the parent as a term — always a sort
        // reference (`Fn`/`Ref`/`Ident`); the `_` arm cannot occur for a registered
        // parent, and degrading to the ctor (free-standing) is the safe reading.
        let sort = match kb.constructor_parent_sort(ctor) {
            Some(parent) => match kb.get_term(parent) {
                Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => *functor,
                _ => ctor,
            },
            None => ctor,
        };
        if seen.insert(sort) {
            sorts.push(sort);
        }
    }
    sorts
}

/// Is `sort` a lawful-Eq boundary — its `eq` is its OWN, so its equality is
/// dispatched, never field-wise-derived? The SAME check `build_sort_ops_table` pass
/// 3 uses to populate the eq-dispatch index (`carrier_own_op` for a declared
/// `operation eq`, else `instance_fact_op_binding` for the op-bound spelling `fact
/// PartialEq/Eq[T=sort, eq=…]`), so the classifier boundary == the resolver's
/// dispatch boundary and a carrier that dispatches its own `eq` is neither
/// field-wise'd nor false-derived `NonEq` against its own `Eq`.
fn is_eq_boundary(
    kb: &KnowledgeBase,
    sort: Symbol,
    eq_spec: Option<Symbol>,
    eq_short: Symbol,
    partialeq_sym: Option<Symbol>,
    eq_sym: Option<Symbol>,
) -> bool {
    if let Some(spec) = eq_spec {
        if super::typing::carrier_own_op(kb, sort, spec, eq_short).is_some() {
            return true;
        }
    }
    let bound = |spec: Option<Symbol>| {
        spec.and_then(|s| super::typing::instance_fact_op_binding(kb, sort, s, "eq")).is_some()
    };
    bound(partialeq_sym) || bound(eq_sym)
}

/// The sorts that ALREADY provide `NonEq` — the partial leaves the fixpoint seeds
/// from (the non-parametric `Float`, plus any hand-written `NonEq`). Scans the
/// `SortProvidesInfo` facts for a `NonEq` spec; runs BEFORE this pass derives any,
/// so it never reads its own output.
fn noneq_provider_sorts(kb: &KnowledgeBase, noneq_sym: Option<Symbol>) -> Vec<Symbol> {
    let (Some(provides_sym), Some(noneq)) = (
        kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo"),
        noneq_sym,
    ) else {
        return Vec::new();
    };
    let noneq_canon = kb.canonical_sort_sym(noneq);
    let mut out: Vec<Symbol> = Vec::new();
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = super::typing::get_named_arg(kb, &named, "sort_ref") else { continue };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else { continue };
        let Some(spec_view) = super::typing::get_named_arg(kb, &named, "spec") else { continue };
        let Some(spec_base) = super::load::provides_spec_base_sym(kb, spec_view) else { continue };
        if kb.canonical_sort_sym(spec_base) == noneq_canon {
            out.push(carrier);
        }
    }
    out
}

/// The sorts of every field of `sort`'s constructors — the fixpoint's out-edges.
/// A fieldless variant (`entity red`) contributes nothing (its `entity_field_types`
/// is absent/empty — correctly Total-neutral). A field whose type head is not a
/// sort (an arrow / effect / `denoted`, or a parametric container's abstract
/// element param) yields no edge: it carries no structural equality of its own, and
/// the parametric-container-of-Float case is the documented follow-up (module
/// header), left non-partial rather than falsely claimed handled.
fn composite_field_sorts(kb: &KnowledgeBase, sort: Symbol) -> Vec<Symbol> {
    let mut out: Vec<Symbol> = Vec::new();
    for ctor in kb.field_constructors_of_sort(sort) {
        let Some(fields) = kb.entity_field_types(ctor) else { continue };
        let fields: Vec<(Symbol, Value)> = fields.to_vec();
        for (_name, ftype) in &fields {
            if let Some(fsort) = super::typing::sort_functor_of_view(kb, ftype) {
                out.push(fsort);
            }
        }
    }
    out
}

/// Assert a derived `SortProvidesInfo(sort_ref = carrier, spec = SortView(spec, <T>
/// = carrier))` fact — byte-identical in shape to `Float`'s `fact NonEq[T = Float]`
/// (the loader's `maybe_emit_fact_provides_info`, load.rs), so every provides-fact
/// reader (`check_eq_noneq_exclusive`, `sort_provides`, …) reads it unchanged.
fn assert_provides(kb: &mut KnowledgeBase, carrier: Symbol, spec: Symbol) {
    let provides_sym = kb.resolve_symbol("anthill.reflect.SortProvidesInfo");
    let sort_view_sym = kb.resolve_symbol("anthill.reflect.SortView");
    let sort_ref_key = kb.intern("sort_ref");
    let spec_key = kb.intern("spec");
    // The spec's carrier parameter name (`T` for `PartialEq`/`NonEq`); cosmetic to
    // the exclusion check (which keys on the carrier), but kept faithful.
    let t_param = {
        let name = kb
            .type_params_of_sort(spec)
            .into_iter()
            .next()
            .unwrap_or_else(|| "T".to_string());
        kb.intern(&name)
    };
    // spec = SortView(spec, <T> = carrier), all-ground → a hash-consed `Term::Fn`.
    // The spec base rides as a name term (`Fn{spec}`, the loader's spelling), but
    // the carrier BINDING must be a bona-fide type value: a bare sort is `Ref(S)`
    // (WI-361), which the WI-391/449 extractability check reads as a Nominal — a
    // bare `Fn{carrier}` name term would extract as `Error`.
    let spec_name = kb.make_name_term_from_sym(spec);
    let carrier_binding = kb.make_sort_ref(carrier);
    let spec_view = kb.alloc(Term::Fn {
        functor: sort_view_sym,
        pos_args: SmallVec::from_elem(spec_name, 1),
        named_args: SmallVec::from_elem((t_param, carrier_binding), 1),
    });
    let sort_ref_term = kb.make_name_term_from_sym(carrier);
    kb.register_entity_fields(provides_sym, vec![sort_ref_key, spec_key]);
    let provides_sort = kb.make_name_term("Requirement");
    kb.assert_fact_carrier(
        provides_sym,
        Vec::new(),
        vec![
            (sort_ref_key, Value::term(sort_ref_term)),
            (spec_key, Value::term(spec_view)),
        ],
        provides_sort,
        sort_ref_term, // domain = the carrier name term
        None,
    );
}

/// WI-664 — the outcome of decomposing two operands for a FIELD-WISE semantic
/// equality compare ([`KnowledgeBase::same_shape_child_pairs`]).
pub(crate) enum FieldPairs {
    /// Either operand is not functor-headed ⇒ not applicable; the caller keeps its
    /// structural verdict.
    NotComposite,
    /// Same-kind composites of DIFFERENT shape (functor / arity / named-key set) ⇒
    /// definitively not equal.
    Mismatch,
    /// Same-shape composites: the matching child-value pairs to compare AND-wise.
    Pairs(Vec<(Value, Value)>),
}

impl KnowledgeBase {
    /// WI-664 — decompose two operands for a field-wise compare into their matching
    /// child pairs. The single shape-walk shared by eval's `composite_field_wise_eq`
    /// and the resolver's `composite_field_wise_sem_eq` (only the per-field
    /// recursion leaf differs: a `bool` vs a three-way `BuiltinResult`), so the
    /// decomposition — which must agree with [`views_structurally_equal`]'s
    /// `Functor` arm and the field-wise C++ `operator==` — lives in ONE place.
    /// Children are materialized as owned [`Value`]s, releasing the borrow before
    /// the caller's (possibly `&mut self`) recursion.
    pub(crate) fn same_shape_child_pairs(&self, a: &Value, b: &Value) -> FieldPairs {
        let (pa, na) = match (a.head(self), b.head(self)) {
            (
                ViewHead::Functor { functor: fa, pos_arity: pa, named_arity: na },
                ViewHead::Functor { functor: fb, pos_arity: pb, named_arity: nb },
            ) => {
                if fa != fb || pa != pb || na != nb {
                    return FieldPairs::Mismatch;
                }
                (pa, na)
            }
            _ => return FieldPairs::NotComposite,
        };
        let mut pairs = Vec::with_capacity(pa + na);
        for i in 0..pa {
            match (a.pos_arg(self, i), b.pos_arg(self, i)) {
                (Some(ca), Some(cb)) => pairs.push((ca.to_value(), cb.to_value())),
                _ => return FieldPairs::Mismatch,
            }
        }
        for key in a.named_keys(self) {
            match (a.named_arg(self, key), b.named_arg(self, key)) {
                (Some(ca), Some(cb)) => pairs.push((ca.to_value(), cb.to_value())),
                _ => return FieldPairs::Mismatch,
            }
        }
        FieldPairs::Pairs(pairs)
    }

    /// WI-664 — does `v` reach an UNSHIELDED partial (non-reflexive) carrier — a
    /// `Float` leaf NOT behind a lawful-Eq own-`eq` boundary — so its SEMANTIC
    /// equality must be computed FIELD-WISE rather than by the structural
    /// reflexivity shortcut? `true` for a bare `Float`, for an entity whose
    /// constructor is a derived `NonEq` carrier
    /// ([`Self::field_wise_noneq_carriers`]), and for a tuple any of whose fields
    /// reaches one. `false` for a lawful-Eq boundary (`TotalFloat`/`Set`/`Map` —
    /// own `eq`, so NOT in the set), an all-`Eq` composite, and every scalar. An
    /// entity reads the precomputed per-constructor classification in O(1) — which
    /// already stopped at boundaries, so there is no descent into a `TotalFloat`
    /// field; only tuples (no sort to key on) walk structurally.
    pub(crate) fn value_reaches_partial_carrier(&self, v: &Value) -> bool {
        match v {
            Value::Float(_) => true,
            Value::Tuple { pos, named, .. } => {
                pos.iter().any(|c| self.value_reaches_partial_carrier(c))
                    || named.iter().any(|(_, c)| self.value_reaches_partial_carrier(c))
            }
            _ => {
                let head = v.head(self);
                if matches!(head, ViewHead::Const(Literal::Float(_))) {
                    return true;
                }
                match head.functor_sym() {
                    Some(f) => self.field_wise_noneq_carriers.contains(&f),
                    None => false,
                }
            }
        }
    }
}
