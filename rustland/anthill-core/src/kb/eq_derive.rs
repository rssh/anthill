//! WI-664 / WI-1098 — composite `Eq`/`NonEq` derivation (proposal 004 / library,
//! WI-644).
//!
//! Equality lawfulness PROPAGATES from a composite's fields, mirroring Rust's
//! `derive`: an entity / named-tuple is a lawful `Eq` iff every field is `Eq`, and
//! is `NonEq` (partial) if any field is `NonEq` (reaches an IEEE `Float`). The parts
//! this module owns:
//!
//! * **Classification** ([`classify`]) — ONE fixpoint pair over the field-reference
//!   graph (not a truncating DFS), so it is sound for recursive and mutually-recursive
//!   sorts. A sort is PARTIAL iff it (transitively) reaches an IEEE `Float` leaf (a
//!   `NonEq` provider) through composite fields, WITHOUT crossing a lawful-Eq
//!   BOUNDARY — a LEAST fixpoint, since partiality grows from a known-partial leaf.
//!   A sort is TOTAL iff every field is `Eq` — a GREATEST one, since totality must
//!   hold for ALL fields and so shrinks from an optimistic seed ([`total_composites`]).
//!   A boundary is a sort whose `eq` is DISPATCHED — a declared `operation eq`, an
//!   op-bound provision (`fact PartialEq[T=X, eq=…]`), or (WI-837) a WITNESS SORT's
//!   `eq` — read through the very predicate the eq-dispatch index uses
//!   (`load::EqDispatchIndex`, built by `load::build_eq_dispatch_index`), so the
//!   classifier's boundary is exactly the resolver's dispatch boundary. Since WI-856
//!   the composite half of the DOMAIN is shared as well ([`composite_sorts`]). That is
//!   what keeps `TotalFloat` (a `Float` wrapper that declares its own total `eq`)
//!   lawfully `Eq` — and shields a composite that wraps it — while a plain
//!   `Point(x: Float, y: Float)` becomes `NonEq`.
//!
//! * **Behavior wiring** — [`KnowledgeBase::field_wise_noneq_carriers`] (the
//!   constructor functors of `Partial` sorts) is what the resolver's `sem_eq_core`
//!   and the interpreter's `semantic_equal` read (via
//!   [`KnowledgeBase::value_reaches_partial_carrier`]) to compare such a value
//!   FIELD-WISE instead of taking the structural reflexivity shortcut — so
//!   `eq(Point(nan,_), Point(nan,_))` reduces to `eq(nan,nan) ∧ … = false`,
//!   agreeing with the field-wise C++ `operator==`.
//!
//! * **Provision assertion, at TWO points in the pipeline.** [`run`] asserts the
//!   derived `NonEq`+`PartialEq` for each `Partial` composite so a user
//!   `provides Eq[Point]` conflicts with the derived `NonEq[Point]` at load (the
//!   WI-658 `check_eq_noneq_exclusive` route — "composes automatically"). It runs
//!   AFTER the provider-coverage checks (so a derived `NonEq`'s witness `nonEqRefl`
//!   is not held to op-backing: it is a propagated classification, witnessed by the
//!   partial field, not a hand-declared primitive) and BEFORE
//!   `check_eq_noneq_exclusive`. The CONDITIONAL `NonEq` mirror
//!   ([`derive_conditional_noneq`], WI-20260919-9KYPA) rides in the same pass for the
//!   same two reasons. [`derive_total_eq`] asserts the derived
//!   `Eq`+`PartialEq` for each `Total` composite, and must run BEFORE the typer AND
//!   have its rows reach the sort-ops table (its call site refreshes that table for
//!   exactly this reason) — that function's doc carries why, and why the `NonEq`
//!   half cannot join it.
//!
//! SCOPE (proposal 004 / WI-664): entities + named tuples. A partial leaf reached only
//! THROUGH a parametric container (`Option[Float]`, `List[Float]`, `Pair[Float, …]`) was
//! the "parametric-container propagation" follow-up — `sort_functor_of_view` resolved a
//! field's type to its BASE sort, so the concrete `Float` argument was not seen. Since
//! WI-20260918-CKD4J a field contributes the sorts its type's ARGUMENTS name too
//! ([`composite_field_sorts`]), and such a composite classifies `Partial`. WI-1098 meets the SAME boundary from the other side, where being
//! wrong would be a false CLAIM rather than a missed refusal: a composite with a
//! parametric field, and a parametric sort itself, derive no UNCONDITIONAL `Eq` — their
//! lawful equality is conditional on their arguments' (`provides Eq[Pair] :- Eq[A],
//! Eq[B]`). WI-20260918-CKD4J derives exactly that conditional form
//! ([`derive_conditional_eq`]), reading a field's full TYPE rather than its head sort; and
//! mirrors it for the `NonEq` half: a composite reaching `Float` through a parametric
//! field's ARGUMENTS classifies `Partial` ([`composite_field_sorts`]), and the
//! partial-carrier gate walks THROUGH a parametric constructor
//! (`KnowledgeBase::partial_transparent_carriers`), so `some(nan)` is compared
//! field-wise. WI-20260919-9KYPA closes the last leg: a parametric sort derives the
//! CONDITIONAL `NonEq` row itself ([`derive_conditional_noneq`], `NonEq[List] :-
//! NonEq[T]`), and `check_use_site_requires_eq` RESOLVES a goal against it instead of
//! reading the key's own provisions, so `Map[K = List[T = Float]]` is refused where the
//! type is written while `Map[K = List[T = Int64]]` loads. What remains out of scope is a
//! NAMED TUPLE key (`Map[K = (a: Float)]`), which has no sort to carry a provision at
//! all.

use std::collections::HashSet;

use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::Symbol;
use crate::kb::term::Term;
use crate::kb::term_view::{TermView, ViewHead};
use crate::kb::ClauseKind;
use crate::kb::KnowledgeBase;
use crate::kb::RuleId;

/// The lawfulness classification of every composite carrier — the fixpoint both
/// assertion passes read, computed by [`classify`]. ONE owner for the rule, because
/// the two halves are asserted at DIFFERENT points in the pipeline (see [`run`]) and
/// a recomputation could disagree: a sort classified Total by one and Partial by the
/// other would get an `Eq` beside a `NonEq`, which `check_eq_noneq_exclusive` reports
/// as a load error against a program the author never wrote.
pub(crate) struct EqClassification {
    /// Every composite carrier sort, in the ORIGINAL (possibly alias) symbols
    /// `composite_sorts` registered — what `assert_provides` and
    /// `field_constructors_of_sort` are keyed by.
    sorts: Vec<Symbol>,
    /// Canonical sorts whose `eq` is DISPATCHED (the author's own).
    boundary: HashSet<Symbol>,
    /// Canonical sorts that (transitively) reach an IEEE `Float` leaf.
    partial: HashSet<Symbol>,
    /// Each composite's field sorts, canonical on both sides — the fixpoint's edges.
    field_sorts: Vec<(Symbol, Vec<Symbol>)>,
}

/// WI-664 — compute the classification. Runs ONCE, at the EARLIER of the two
/// assertion points ([`derive_total_eq`]), because every input is final by then: the
/// entity field-type registry (`declare_field_types`), the sort-ops table and the
/// eq-dispatch index (`build_eq_dispatch_index`, immediately above the call), and the
/// source-level `SortProvidesInfo` facts.
///
/// THE FIELD REGISTRY IS NOT FROZEN, and the invariant is narrower than "nothing
/// changes" (found by review, which is why it is stated exactly rather than loosely):
/// `typing::elaborate_self_field_ties` (WI-1082) rewrites `entity_field_types` in
/// place DURING `type_check_sorts`, i.e. between this call and [`run`]. What the
/// fixpoint reads is only each field's HEAD SORT
/// ([`composite_field_sorts`] → `sort_functor_of_view`), and that pass fills UNWRITTEN
/// type ARGUMENTS (`rigidify_unwritten_sort_params`) without touching the head — so
/// the edge set is the same either side of it. [`run`] asserts that in debug rather
/// than trusting it: an elaboration that DID move a head would silently drop a
/// composite's `NonEq` and with it `field_wise_noneq_carriers`, re-laundering
/// `eq(Point(nan,_), Point(nan,_))` to true with nothing pointing at the cause.
pub(crate) fn classify(kb: &mut KnowledgeBase) -> EqClassification {
    let noneq_sym = kb.try_resolve_symbol("anthill.prelude.NonEq");
    // The eq-dispatch supply index — built here, before any `assert_provides`, so the
    // boundary set is computed against the same provisions the load-time index build
    // saw. `None` on a prelude-less KB (no `PartialEq.eq` ⇒ no `eq` spec op exists, so
    // nothing can supply an impl of it and no sort is a boundary).
    let eq_index = super::load::EqDispatchIndex::build(kb);

    // Every composite carrier sort: data sorts (with variant constructors) plus
    // free-standing entities (their own sort).
    let sorts = composite_sorts(kb);

    // Lawful-Eq BOUNDARIES (canonical), by the authoritative eq-dispatch signal.
    let boundary: HashSet<Symbol> = sorts
        .iter()
        .filter(|&&s| is_eq_boundary(kb, eq_index.as_ref(), s))
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

    EqClassification {
        sorts,
        boundary,
        partial,
        field_sorts,
    }
}

/// WI-1098 — assert the derived `Eq` (+ its `PartialEq` base) for every TOTAL
/// composite. A PRE-TYPER pass, and that placement is the whole point: a provision
/// only reaches a call site through the typer, which tags each spec-op call with a
/// `CallClass` that `req_insertion` turns into the caller-frame dictionary. Asserted
/// where the `NonEq` half is ([`run`], after the typer) the fact exists and NO call
/// site was ever rewritten to read it — MEASURED: `List.contains(cons(red, nil), red)`
/// still died with `DeferToRequirement: requirement param __req_eq not bound in caller
/// frame … frame binds []`, byte-identical to the no-provision baseline.
///
/// The SECOND reader is the sort-ops table, whose pass 2 inherits the spec's `eq` onto
/// each providing carrier; the call site refreshes that table right after this pass
/// because it is built above (the eq-dispatch index the classification reads is built
/// off it). Without the refresh the provision exists, dispatch RESOLVES it, and then
/// `sort_ops_lookup(carrier, eq)` answers `None` → `NoMatch` — so deriving a provision
/// BREAKS a direct `eq(a, b)` call that worked without one. `load.rs` carries that
/// measurement.
///
/// The `NonEq` half cannot move here, and the asymmetry has a reason rather than
/// being an accident of ordering: a derived `NonEq` carries the witness operation
/// `nonEqRefl`, which no carrier backs, so it must stand AFTER `check_provider_operations`
/// (see the module header). A derived `Eq`/`PartialEq` introduces no unbacked operation
/// — its `eq` is the builtin structural one, exactly as a hand-written `provides
/// PartialEq[T = Colour]` is, and that spelling passes both provider-coverage checks
/// today (the explicit-`provides` control). So this half is held to the same bar as a
/// written provision, which is what it should be.
pub(crate) fn derive_total_eq(kb: &mut KnowledgeBase, c: &EqClassification) {
    let partialeq_sym = kb.try_resolve_symbol("anthill.prelude.PartialEq");
    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq");
    // `Eq` requires `PartialEq`, so BOTH are asserted, exactly as the `NonEq` half
    // asserts its own `PartialEq` base.
    //
    // NO `sort_provides` RE-CHECK per carrier, unlike [`run`]'s loop, and the two
    // reasons it needs one are both already answered above: a carrier that ALREADY
    // provides is out of the seed (directly via `spoken_for`, transitively via
    // `provides_eq`), and the ALIAS case `run`'s guard exists for — two alias-distinct
    // symbols of ONE composite sort, which would otherwise each assert a row — is
    // removed at the source by `total_composites` returning one symbol per CANONICAL
    // sort. Re-asking would be a live relation scan per carrier at a point where
    // `kb.provides_index` is `None`, for an answer the seed computed.
    for s in total_composites(kb, c) {
        if let Some(pe) = partialeq_sym {
            assert_provides(kb, s, pe);
        }
        if let Some(eq) = eq_sym {
            assert_provides(kb, s, eq);
        }
    }
    // WI-20260918-CKD4J — THE `PartialEq` HALF OF A `Partial` COMPOSITE, here and not in
    // [`run`], for the same reason as the rows above: a provision reaches a call site
    // only through the typer. MEASURED: `same[X](a: X, b: X) requires PartialEq[X]` at
    // `pt(x: Float)` was refused at load ("`PartialEq[T = Pt]` cannot be supplied") —
    // a partial composite HAS a partial equality, and said so only after the typer had
    // finished. Only the `NonEq` half has a reason to stay in `run` (its unbacked
    // `nonEqRefl`); `PartialEq`'s `eq` is the builtin structural one, held to the same
    // provider-coverage bar as any written provision, which it passes.
    if let Some(pe) = partialeq_sym {
        let mut seen: HashSet<Symbol> = HashSet::new();
        for &s in &c.sorts {
            let cs = kb.canonical_sort_sym(s);
            if c.partial.contains(&cs)
                && seen.insert(cs)
                && !super::typing::sort_provides(kb, s, pe)
            {
                assert_provides(kb, s, pe);
            }
        }
    }
}

/// WI-20260918-CKD4J — a derived condition: `spec[P]` over the carrier's OWN type
/// parameter `P`. The derived row reads `provides X[S] :- spec₁[P₁], …`.
type Condition = (Symbol, Symbol);

/// WI-20260918-CKD4J — the CONDITIONAL half of the `Eq` derivation: rows for the
/// composites [`total_composites`] must leave out — a PARAMETRIC sort (`List[T]`,
/// `Option[T]`, a user `Box[T]`) and a composite whose field is a parametric sort at
/// concrete arguments (`holder(o: Option[T = Int64])`).
///
/// A parametric sort's lawful equality is CONDITIONAL on its arguments', so what it
/// derives is exactly the WI-869 form `pair.anthill` hand-writes — `provides
/// PartialEq[Box] :- PartialEq[T]` and `provides Eq[Box] :- Eq[T]`, over the parameters
/// its fields mention. An UNCONDITIONAL claim would make `List[Float]` lawful; this
/// makes it lawful exactly where `Float` would be, i.e. nowhere
/// (`a_float_behind_a_parametric_field_is_not_claimed_lawful`).
///
/// Per field TYPE, not per field head sort — the head-only reading is what excluded
/// these carriers. [`field_conditions`] answers what a field's equality rests on: a
/// parameter of the carrier rests on that parameter; a non-parametric sort on nothing,
/// if it provides the spec or is derivable; a parametric application `H[Q = a]` on
/// `H`'s own conditions TRANSLATED through its arguments — so `Option[T = Int64]` rests
/// on `Eq[Int64]` (true) and `Pair[A = Float, …]` on `Eq[Float]` (false).
///
/// A GREATEST fixpoint, like the total one and for the same reason: `List` is `cons(head:
/// T, tail: List[T = T])`, lawful iff `T` is, which only an optimistic seed derives.
/// Run AFTER [`derive_total_eq`], so the rows that pass asserted are read as provisions.
///
/// NOT DERIVED, each deliberately: a `Partial` composite (it derives `NonEq`), an
/// equality BOUNDARY (its `eq` is the author's), a carrier any equality provision
/// already names (`Pair` writes its own — not duplicated), and a sort with a field whose
/// equality nothing decides (an arrow, a `Float` argument, an unwritten argument).
/// THE `NonEq` MIRROR is the other half of the classification: `holder(o: Option[T =
/// Float])` reaches `Float` through its field type's ARGUMENTS ([`composite_field_sorts`])
/// and so classifies `Partial` — derived `NonEq` + `PartialEq`, compared field-wise — and
/// is no candidate here.
pub(crate) fn derive_conditional_eq(kb: &mut KnowledgeBase, c: &EqClassification) {
    let (Some(partial_eq), Some(eq)) = (
        kb.try_resolve_symbol("anthill.prelude.PartialEq"),
        kb.try_resolve_symbol("anthill.prelude.Eq"),
    ) else {
        return;
    };
    let spoken_for: HashSet<Symbol> = ["PartialEq", "Eq", "NonEq"]
        .into_iter()
        .filter_map(|n| kb.try_resolve_symbol(&format!("anthill.prelude.{n}")))
        .flat_map(|spec| super::typing::provision_carriers_of_spec(kb, spec))
        .map(|s| kb.canonical_sort_sym(s))
        .collect();
    // One symbol per canonical composite, in registration order.
    let mut seen: HashSet<Symbol> = HashSet::new();
    let candidates: Vec<Symbol> = c
        .sorts
        .iter()
        .copied()
        .filter(|&s| {
            let cs = kb.canonical_sort_sym(s);
            seen.insert(cs)
                && !c.boundary.contains(&cs)
                && !c.partial.contains(&cs)
                && !spoken_for.contains(&cs)
                && !super::typing::sort_provides(kb, s, eq)
                && !super::typing::sort_provides(kb, s, partial_eq)
        })
        .collect();
    for spec in [partial_eq, eq] {
        // Optimistic seed: every candidate derivable, resting on nothing.
        let mut derived: std::collections::HashMap<Symbol, Vec<Condition>> = candidates
            .iter()
            .map(|&s| (kb.canonical_sort_sym(s), Vec::new()))
            .collect();
        loop {
            let mut changed = false;
            for &s in &candidates {
                let cs = kb.canonical_sort_sym(s);
                if !derived.contains_key(&cs) {
                    continue;
                }
                let params: Vec<Symbol> = kb.type_param_syms_of(s).to_vec();
                let mut conds: Vec<Condition> = Vec::new();
                let mut ok = true;
                'fields: for ctor in kb.field_constructors_of_sort(s) {
                    let Some(fields) = kb.entity_field_types(ctor) else {
                        continue;
                    };
                    for (_, ftype) in fields.to_vec() {
                        match field_conditions(kb, &ftype, spec, &params, &derived) {
                            Some(fc) => {
                                for x in fc {
                                    if !conds.contains(&x) {
                                        conds.push(x);
                                    }
                                }
                            }
                            None => {
                                ok = false;
                                break 'fields;
                            }
                        }
                    }
                }
                if !ok {
                    derived.remove(&cs);
                    changed = true;
                } else if derived.get(&cs) != Some(&conds) {
                    derived.insert(cs, conds);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        for &s in &candidates {
            let Some(conds) = derived.get(&kb.canonical_sort_sym(s)).cloned() else {
                continue;
            };
            assert_provides(kb, s, spec);
            record_derived_conditions(kb, s, spec, &conds);
            // WI-20260919-9KYPA — carry the parameters across to `run`, which mirrors
            // them into the `NonEq` half. BOTH specs: the mirror needs the `Eq` list for
            // its disjuncts and the `PartialEq` list for the conditions `NonEq requires
            // PartialEq` obliges it to carry.
            let params: Vec<Symbol> = conds.iter().map(|&(_, p)| p).collect();
            if !params.is_empty() {
                let cs = kb.canonical_sort_sym(s);
                kb.conditional_eq_params.insert((cs, spec), params);
            }
        }
    }
}

/// WI-20260918-CKD4J — what a field of type `ty` needs for its `spec` equality, as
/// conditions over the carrier's own `params`: `Some(vec![])` for a field whose equality
/// holds outright, `None` for one nothing decides. `derived` is the fixpoint's current
/// verdict for the candidates (canonical carrier → its conditions).
fn field_conditions<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
    spec: Symbol,
    params: &[Symbol],
    derived: &std::collections::HashMap<Symbol, Vec<Condition>>,
) -> Option<Vec<Condition>> {
    // A field typed by one of the carrier's own parameters (`value: T`) is that
    // parameter's CANONICAL variable (`KnowledgeBase::canonical_type_param_var`) — or,
    // in a type the extractor produced, a `TypeVar` naming it.
    if let ViewHead::Var(v) = ty.head(kb) {
        return params
            .iter()
            .find(|&&p| {
                kb.canonical_type_param_var(p)
                    .is_some_and(|t| matches!(kb.get_term(t), Term::Var(w) if *w == v))
            })
            .map(|&p| vec![(spec, p)]);
    }
    if let Some(name) = super::typing::type_var_name_of_view(kb, ty) {
        let name = kb.local_name_of(name).to_string();
        return params
            .iter()
            .find(|p| kb.local_name_of(**p) == name)
            .map(|&p| vec![(spec, p)]);
    }
    let head = super::typing::sort_functor_of_view(kb, ty)?;
    if params.contains(&head) {
        return Some(vec![(spec, head)]);
    }
    if super::typing::is_sort_param_symbol(kb, head) {
        // Some OTHER sort's parameter: nothing here decides it.
        return None;
    }
    let h_params: Vec<Symbol> = kb.type_param_syms_of(head).to_vec();
    // `head`'s own conditions for `spec`, over ITS parameters: a candidate's current
    // verdict, else a written/derived provision (unconditional, or ONE conditional
    // clause — alternatives are not translated), else nothing.
    let h_conds: Vec<Condition> = if let Some(dc) = derived.get(&kb.canonical_sort_sym(head)) {
        dc.clone()
    } else if super::typing::sort_provides(kb, head, spec) {
        let spec_canon = kb.canonical_sort_sym(spec);
        let clauses: Vec<Vec<Value>> = super::typing::provision_conditions(kb, head)
            .into_iter()
            .filter(|g| kb.canonical_sort_sym(g.provided) == spec_canon)
            .map(|g| g.conditions)
            .collect();
        match clauses.as_slice() {
            [] => Vec::new(),
            [one] => {
                let mut out = Vec::with_capacity(one.len());
                for cv in one {
                    let (base, bindings) = super::typing::unwrap_spec_view_value(kb, cv)?;
                    let q = bindings.iter().find_map(|(_, t)| {
                        super::typing::sort_functor_of_view(
                            kb,
                            &crate::kb::term_view::TermIdView(*t),
                        )
                        .filter(|q| h_params.contains(q))
                    })?;
                    out.push((base, q));
                }
                out
            }
            _ => return None,
        }
    } else {
        return None;
    };
    // Translate each of `head`'s conditions through the field type's argument for it.
    // An UNWRITTEN argument of a SELF-reference (`tail: List` inside `List`) is the
    // carrier's own parameter of that name — the reading the typer's
    // `rigidify_unwritten_sort_params` gives it; unwritten anywhere else, nothing decides it.
    let self_ref = h_params.iter().all(|q| params.contains(q)) && !h_params.is_empty();
    let mut out: Vec<Condition> = Vec::new();
    for (cspec, q) in h_conds {
        let q_name = kb.local_name_of(q).to_string();
        let arg = ty
            .named_keys(kb)
            .into_iter()
            .find(|k| kb.local_name_of(*k) == q_name)
            .and_then(|k| ty.named_arg(kb, k))
            .map(|it| it.to_value());
        let needs = match arg {
            Some(arg) => field_conditions(kb, &arg, cspec, params, derived)?,
            None if self_ref => vec![(cspec, q)],
            None => return None,
        };
        for x in needs {
            if !out.contains(&x) {
                out.push(x);
            }
        }
    }
    Some(out)
}

/// WI-20260918-CKD4J — the `:- goals` tail of a derived row, filed exactly as the loader
/// files a written one (`load_provides_conditions`): one `ProvidesConditionInfo` per
/// condition, joined to the provision by its view, under a fresh clause index; and the
/// clause itself recorded for `provides_clause_count`. Nothing for an unconditional row.
fn record_derived_conditions(kb: &mut KnowledgeBase, carrier: Symbol, spec: Symbol, conds: &[Condition]) {
    let carrier_ref = kb.make_sort_ref(carrier);
    let provided = spec_view(kb, spec, carrier_ref);
    let mut lowered: Vec<Value> = Vec::with_capacity(conds.len());
    if !conds.is_empty() {
        let cond_sym = kb.resolve_symbol("anthill.reflect.ProvidesConditionInfo");
        let sort_ref_sym = kb.intern("sort_ref");
        let provided_sym = kb.intern("provided");
        let condition_sym = kb.intern("condition");
        let clause_sym = kb.intern("clause");
        kb.register_entity_fields(
            cond_sym,
            vec![sort_ref_sym, provided_sym, condition_sym, clause_sym],
        );
        let scope = kb.symbols.scope_id(carrier);
        let clause = kb.next_provides_clause_index(scope);
        let clause_term = kb.alloc(Term::Const(crate::kb::term::Literal::Int(clause as i64)));
        let carrier_term = kb.make_name_term_from_sym(carrier);
        for &(cspec, p) in conds {
            let param_ref = kb.make_sort_ref(p);
            let cv = Value::term(spec_view(kb, cspec, param_ref));
            lowered.push(cv.clone());
            kb.assert_fact_carrier(
                cond_sym,
                Vec::new(),
                vec![
                    (sort_ref_sym, Value::term(carrier_term)),
                    (provided_sym, Value::term(provided)),
                    (condition_sym, cv),
                    (clause_sym, Value::term(clause_term)),
                ],
                ClauseKind::Requirement,
                carrier,
                None,
            );
        }
    }
    kb.record_provides_clause(carrier, spec, lowered);
}

/// `SortView(spec, <spec's carrier param> = binding)` — the view shape of a provision's
/// spec and of each of its conditions (see [`assert_provides`]).
fn spec_view(kb: &mut KnowledgeBase, spec: Symbol, binding: crate::kb::term::TermId) -> crate::kb::term::TermId {
    let sort_view_sym = kb.resolve_symbol("anthill.reflect.SortView");
    let t_param = {
        let name = kb
            .type_params_of_sort(spec)
            .into_iter()
            .next()
            .unwrap_or_else(|| "T".to_string());
        kb.intern(&name)
    };
    let spec_name = kb.make_name_term_from_sym(spec);
    kb.alloc(Term::Fn {
        functor: sort_view_sym,
        pos_args: SmallVec::from_elem(spec_name, 1),
        named_args: SmallVec::from_elem((t_param, binding), 1),
    })
}

/// WI-664 entry point (a post-load pass). See the module header for placement, and
/// [`derive_total_eq`] for why the `Eq` half of the same classification is asserted
/// before the typer instead of here.
///
/// WI-1103 — THE PLACEMENT ALONE WAS SINGLE-PHASE ONLY, and this half is the one it
/// failed for. Standing after `check_provider_operations` keeps a derived `NonEq`'s
/// unbacked `nonEqRefl` from being refused *as it is created*; but the FACT then
/// persists, and the NEXT `load_phase_inner` runs that check again with the row
/// already in the relation, this time reaching it FIRST. MEASURED at 51d17d22 (so:
/// pre-WI-1098, and unchanged by it): `load_stdlib` then `load_all` into a live KB over the
/// full stdlib + host closure refused all five derived-`NonEq` carriers. So the
/// placement is no longer load-bearing on its own — every row asserted below is
/// MARKED (`mark_unbacked_derived_provision`) and the coverage walk skips it by that
/// mark in EVERY phase. The placement stays because the two must not disagree: were
/// this pass moved above the checks, the phase that derives a row would refuse it
/// before the mark existed. The `Eq` half has no such exposure — it introduces no
/// unbacked operation, so a later phase re-checking it passes, which is the same
/// thing as being held to a written provision's bar.
pub(crate) fn run(kb: &mut KnowledgeBase, c: &EqClassification) {
    let noneq_sym = kb.try_resolve_symbol("anthill.prelude.NonEq");
    let partialeq_sym = kb.try_resolve_symbol("anthill.prelude.PartialEq");
    // The classification was computed before the typer, and the typer REWRITES the
    // field registry (`elaborate_self_field_ties`). [`classify`]'s doc says why that is
    // still sound — the rewrite fills type arguments, never a field's head sort — and
    // this is that claim as a check rather than as prose. Debug-only: it re-walks every
    // composite's fields, which is a per-load cost the release build should not pay for
    // an invariant the suite exercises on every one of its stdlib loads.
    debug_assert!(
        {
            let now: Vec<(Symbol, Vec<Symbol>)> = c
                .sorts
                .iter()
                .map(|&s| {
                    let fs = composite_field_sorts(kb, s)
                        .into_iter()
                        .map(|f| kb.canonical_sort_sym(f))
                        .collect();
                    (kb.canonical_sort_sym(s), fs)
                })
                .collect();
            now == c.field_sorts
        },
        "eq_derive: a pass between `classify` and `run` moved a field's HEAD SORT, so \
         the Partial/Total classification was computed on edges that no longer exist — \
         a composite silently loses its derived `NonEq` and its field-wise comparison"
    );

    // Build the field-wise carrier set + derive `NonEq`/`PartialEq` for each Partial
    // composite. (Leaf `NonEq` providers like `Float` are in `partial` but not in
    // `sorts`, so they neither add constructors nor re-derive.)
    let mut field_wise: HashSet<Symbol> = HashSet::new();
    let mut derive: Vec<Symbol> = Vec::new();
    for &s in &c.sorts {
        if c.partial.contains(&kb.canonical_sort_sym(s)) {
            for ctor in kb.field_constructors_of_sort(s) {
                field_wise.insert(ctor);
            }
            derive.push(s);
        }
    }
    kb.field_wise_noneq_carriers = field_wise;
    // WI-20260918-CKD4J — the parametric composites' constructors, walked THROUGH by the
    // partial-carrier gate (see `partial_transparent_carriers`). Every one, boundary or
    // not: a parametric boundary's own `eq` (`Pair.eq`) compares its components, so a
    // `Float` argument makes it partial too. A NON-parametric boundary (`TotalFloat`)
    // is not here, and still shields what it holds.
    let transparent: HashSet<Symbol> = c
        .sorts
        .iter()
        .filter(|&&s| !kb.type_param_syms_of(s).is_empty())
        .flat_map(|&s| kb.field_constructors_of_sort(s))
        .collect();
    kb.partial_transparent_carriers = transparent;

    // WI-1103 — MARK every row asserted here. The exemption from provider-coverage
    // op-backing is this pass's placement made a property of the ROW, so it holds in
    // the phase that derives the row AND in every later phase, which walks the row
    // before this pass re-runs. Both specs are marked, not just `NonEq`: the placement
    // exempted both, and reproducing it exactly is what keeps a second phase's verdict
    // equal to the first's rather than merely closer to it.
    for s in derive {
        if let Some(ne) = noneq_sym {
            if !super::typing::sort_provides(kb, s, ne) {
                let rid = assert_provides(kb, s, ne);
                kb.mark_unbacked_derived_provision(rid);
            }
        }
        if let Some(pe) = partialeq_sym {
            if !super::typing::sort_provides(kb, s, pe) {
                let rid = assert_provides(kb, s, pe);
                kb.mark_unbacked_derived_provision(rid);
            }
        }
    }

    if let (Some(ne), Some(pe), Some(eq)) = (
        noneq_sym,
        partialeq_sym,
        kb.try_resolve_symbol("anthill.prelude.Eq"),
    ) {
        derive_conditional_noneq(kb, ne, pe, eq);
    }
}

/// WI-20260919-9KYPA — the CONDITIONAL `NonEq` mirror of [`derive_conditional_eq`]:
/// `provides NonEq[List] :- NonEq[T]`, so `List[T = Float]` is a WITNESSED `NonEq`
/// carrier and `Set[T = List[T = Float]]` is refused where the type is written
/// (`check_use_site_requires_eq`, which resolves the goal rather than reading the key's
/// own provisions). Without it that check looked `List` up, found no `NonEq`, and let an
/// unlawful key through — the gap §8.3 names.
///
/// ONE CLAUSE PER PARAMETER, where the `Eq` half emits one clause holding every
/// parameter. That asymmetry is the logic, not a shortcut: a parametric application is
/// lawfully `Eq` iff EVERY argument is (a conjunction, one clause), and is `NonEq` if ANY
/// argument is (a disjunction — and `provision_conditions` reads conditions as a
/// conjunction WITHIN a clause and a disjunction ACROSS clauses, so the disjunction has
/// to be spelled as separate clauses). `Pair[A = Float, B = Int64]` needs the `A` clause
/// alone to answer.
///
/// Mirrors only what THIS module derived ([`KnowledgeBase::conditional_eq_params`], whose
/// comment carries why a WRITTEN conditional `Eq` is not mirrored).
///
/// The row is MARKED like every other row this pass asserts: a derived `NonEq` carries
/// the witness operation `nonEqRefl`, which no carrier backs, and WI-1103's mark is what
/// exempts it from provider-coverage in the deriving phase AND in every later one.
///
/// Note it stands in [`run`], after `check_provider_operations`, and NOT beside
/// [`derive_conditional_eq`] — which is why the parameters have to be carried across on
/// the KB rather than recomputed here.
fn derive_conditional_noneq(kb: &mut KnowledgeBase, noneq: Symbol, partial_eq: Symbol, eq: Symbol) {
    // Registration order, so the clause indices a program gets do not depend on a hash
    // iteration order (they appear in `ProvidesConditionInfo` facts a test can read).
    let carriers: Vec<(Symbol, Vec<Symbol>, Vec<Symbol>)> = composite_sorts(kb)
        .into_iter()
        .filter_map(|s| {
            let cs = kb.canonical_sort_sym(s);
            let disjuncts = kb.conditional_eq_params.get(&(cs, eq))?.clone();
            // The `PartialEq` row's OWN parameters, not the `Eq` row's reused: see the
            // field's comment. Absent ⇒ this carrier derived no conditional `PartialEq`,
            // so a `NonEq` row could not discharge its `requires PartialEq` and is not
            // derived at all.
            let base = kb.conditional_eq_params.get(&(cs, partial_eq))?.clone();
            Some((s, disjuncts, base))
        })
        .collect();
    let mut done: HashSet<Symbol> = HashSet::new();
    for (s, params, partial_params) in carriers {
        // Idempotent across load phases, the same guard the loop above uses: phase 2
        // re-runs this pass with phase 1's row already in the relation, and a second
        // `record_derived_conditions` would file a SECOND clause at a fresh index — a
        // duplicate disjunct, which `provision_conditions` would then read as a real
        // alternative.
        if !done.insert(kb.canonical_sort_sym(s)) || super::typing::sort_provides(kb, s, noneq) {
            continue;
        }
        let rid = assert_provides(kb, s, noneq);
        kb.mark_unbacked_derived_provision(rid);
        for p in params {
            // EACH CLAUSE ALSO CARRIES THE `PartialEq` CONDITIONS, and that is not
            // belt-and-braces: the `NonEq` SPEC `requires PartialEq`, so
            // `check_provider_requires` holds every `NonEq` provision to supplying
            // `PartialEq` at the same carrier — and `PartialEq[Result]` is itself
            // conditional (`:- PartialEq[T], PartialEq[E]`). A clause conditioned on
            // `NonEq[T]` alone does not entail those, which the check reports as
            // `ProvisionConditionsTooWeak`. MEASURED: without this the whole stdlib
            // refused on `anthill.prelude.Result`.
            //
            // It is also the honest reading. `NonEq[Result] :- NonEq[T]` alone would
            // claim `Result[T = Float, E = <no equality at all>]` is a WITNESSED partial
            // carrier, when its `E` component has no equality to be partial about. The
            // claim is "every component has a partial equality AND at least one of them
            // is non-reflexive", which is what these conditions say.
            let mut conds: Vec<Condition> = vec![(noneq, p)];
            for &q in &partial_params {
                if !conds.contains(&(partial_eq, q)) {
                    conds.push((partial_eq, q));
                }
            }
            record_derived_conditions(kb, s, noneq, &conds);
        }
    }
}

/// WI-1098 — the composites that derive a lawful `Eq`: the symmetric half of the
/// `Partial`/`NonEq` classification above. An entity / named tuple whose every field
/// is itself lawfully `Eq` HAS a lawful structural equality, and saying so is what
/// discharges a `requires Eq[T]` at the carrier (`List.contains(l, red)`) — without
/// it such a call loads clean and dies inside the evaluator with `DeferToRequirement:
/// requirement param __req_eq not bound`.
///
/// A GREATEST fixpoint, where the `Partial` half above is a least one, and the
/// direction is forced: `Partial` GROWS from a known-partial leaf (`Float`), while
/// `Total` must hold for every field, so it SHRINKS from an optimistic seed. That is
/// also what decides a RECURSIVE composite — `node(l: Tree, r: Tree)` is `Eq` iff
/// `Tree` is `Eq`, which is true coinductively and underivable by any least fixpoint.
///
/// Excluded from the seed, each for its own reason:
///  * a lawful-Eq BOUNDARY — its `eq` is the author's, dispatched
///    ([`is_eq_boundary`]); deriving a provision over it would offer a SECOND
///    candidate for the same carrier (058 §4.9) where the author supplied one.
///  * a `Partial` composite — the other half of this same classification already
///    derives its `NonEq`, and `Eq` ⊥ `NonEq` (WI-658).
///  * a carrier that ALREADY provides `Eq` — the derivation is idempotent, not a
///    duplicate-provision error (the explicit-`provides` control).
///  * a PARAMETRIC sort (`List[T]`, `Option[T]`) — its lawful equality is CONDITIONAL
///    on its arguments' (`provides Eq[Pair] :- Eq[A], Eq[B]`), and an unconditional
///    `Eq[List]` would claim `List[Float]` lawful. [`derive_conditional_eq`] derives the
///    conditional row for it instead.
///
/// A field keeps its composite in the set only if the field's sort is NON-PARAMETRIC
/// and either already provides `Eq` or is itself Total. The non-parametric demand is
/// the same boundary the `Partial` half draws and for the same reason: `Pair`'s
/// `provides Eq[Pair] :- Eq[A], Eq[B]` reads as an `Eq` provider through
/// `sort_provides`, so a field typed `Pair[A = Float, B = Int64]` would otherwise
/// carry a `Float` into a derived-lawful composite — the parametric-container
/// propagation the module header documents as out of scope, here in the direction
/// where being wrong is a false CLAIM rather than a missed one.
fn total_composites(kb: &KnowledgeBase, c: &EqClassification) -> Vec<Symbol> {
    let EqClassification {
        sorts,
        boundary,
        partial,
        field_sorts,
    } = c;
    let Some(eq_sym) = kb.try_resolve_symbol("anthill.prelude.Eq") else {
        return Vec::new();
    };
    // `sort_provides` is a live relation scan while `kb.provides_index` is `None`
    // (it is not built until the typer starts, after this pass), and the field walk
    // asks the same handful of leaf sorts — `String`, `Int64`, `Symbol` — once per
    // field across ~130 composites. Memoized per canonical symbol.
    let mut eq_known: std::collections::HashMap<Symbol, bool> = std::collections::HashMap::new();
    let mut provides_eq = |kb: &KnowledgeBase, s: Symbol| -> bool {
        let key = kb.canonical_sort_sym(s);
        match eq_known.get(&key) {
            Some(&v) => v,
            None => {
                let v = super::typing::sort_provides(kb, s, eq_sym);
                eq_known.insert(key, v);
                v
            }
        }
    };
    let parametric = |kb: &KnowledgeBase, s: Symbol| !kb.type_param_syms_of(s).is_empty();
    // Every carrier ANY equality provision already names — read carrier-side, which is
    // a DIFFERENT question from the three above (WI-1069). See the seed's comment.
    let spoken_for: HashSet<Symbol> = ["PartialEq", "Eq", "NonEq"]
        .into_iter()
        .filter_map(|n| kb.try_resolve_symbol(&format!("anthill.prelude.{n}")))
        .flat_map(|spec| super::typing::provision_carriers_of_spec(kb, spec))
        .collect();

    let mut total: HashSet<Symbol> = sorts
        .iter()
        .copied()
        .filter(|&s| {
            let cs = kb.canonical_sort_sym(s);
            // `spoken_for` is not redundant with `provides_eq` / `partial` / `boundary`,
            // and the gap it closes was a FALSE CLAIM, not a missed one. Those three all
            // key on `sort_ref` — the PROVIDER — while a WITNESS names its carrier only
            // in the spec's `T` binding. MEASURED: `sort WrapperNonEq { provides
            // NonEq[T = Wrapper]; operation nonEqRefl() -> Wrapper = … }` put
            // `WrapperNonEq` in `partial` and left `Wrapper` seeded Total, so the
            // derivation asserted `provides Eq[Wrapper]` over an equality its author had
            // just witnessed as NON-reflexive — and `check_eq_noneq_exclusive` stayed
            // silent, grouping by `sort_ref` as well. The second symptom was a witness
            // `provides PartialEq[T = C]` binding no `eq`: `C` was not a boundary and
            // `sort_provides(C, PartialEq)` was false, so the derivation filed a SECOND
            // `(PartialEq, C)` claim beside the author's.
            //
            // The rule this makes true is the one the derivation is FOR: derive where the
            // author said NOTHING about this carrier's equality. "Nothing" has to mean
            // "no provision names it as a carrier", not "no provision is filed under its
            // own name".
            !boundary.contains(&cs)
                && !partial.contains(&cs)
                && !spoken_for.contains(&cs)
                && !parametric(kb, s)
                && !provides_eq(kb, s)
        })
        .map(|s| kb.canonical_sort_sym(s))
        .collect();
    loop {
        let mut changed = false;
        for (cs, fsorts) in field_sorts {
            if !total.contains(cs) {
                continue;
            }
            if fsorts
                .iter()
                .any(|&f| parametric(kb, f) || !(provides_eq(kb, f) || total.contains(&f)))
            {
                total.remove(cs);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // Back to the ORIGINAL (possibly alias) symbols the caller asserts against —
    // `assert_provides` keys the fact on the symbol it is handed, and `sorts` is what
    // `composite_sorts` registered — but ONE PER CANONICAL SORT. The `Partial` half
    // instead returns every alias and lets a `sort_provides` re-check in its loop
    // suppress the duplicate (the WI-660 note: "re-deriving a duplicate `NonEq` for two
    // alias-distinct symbols of one composite sort"). Deduping here answers the same
    // question by construction, so [`derive_total_eq`] needs no per-carrier relation
    // scan; FIRST wins, which is the row that re-check would have kept.
    let mut seen: HashSet<Symbol> = HashSet::new();
    sorts
        .iter()
        .copied()
        .filter(|&s| {
            let cs = kb.canonical_sort_sym(s);
            total.contains(&cs) && seen.insert(cs)
        })
        .collect()
}

/// Every composite carrier sort: data sorts (with variant constructors) plus
/// free-standing entities (their own sort). Derived from the entity-field-type
/// registry — one entry per constructor that carries a field schema — mapping each
/// constructor to its owning sort.
///
/// WI-856 — the ONE owner of "which composite carriers exist", shared with
/// [`super::load::eq_dispatch_carrier_domain`], which unions it into the eq index's
/// `SortInfo` walk to reach a NAMESPACE-LEVEL entity; that function carries the why.
pub(crate) fn composite_sorts(kb: &KnowledgeBase) -> Vec<Symbol> {
    let mut sorts: Vec<Symbol> = Vec::new();
    let mut seen: HashSet<Symbol> = HashSet::new();
    let ctor_functors: Vec<Symbol> = kb.entity_field_type_functors().copied().collect();
    for ctor in ctor_functors {
        // A variant maps to its parent sort; a free-standing / eponymous entity IS
        // its own sort. WI-946: that reflexive case is what `sort_of_constructor`
        // OWNS, so it is no longer re-spelled here as `strict(c)` + a `None` arm.
        // `unwrap_or` is the residual for a symbol with no registered sort at all;
        // measured over the loaded stdlib it never fires (244/244 field-schema
        // functors answer `Some`) — every write to the field-schema registry is
        // paired with a `register_entity_of` / `register_self_sort`.
        let sort = kb.sort_of_constructor(ctor).unwrap_or(ctor);
        if seen.insert(sort) {
            sorts.push(sort);
        }
    }
    sorts
}

/// Is `sort` a lawful-Eq boundary — its `eq` is dispatched, never field-wise-derived?
/// Literally the PREDICATE [`super::load::build_eq_dispatch_index`] uses to decide
/// what keys the eq-dispatch index, through its one owner
/// [`super::load::EqDispatchIndex`] — a declared `operation eq`, the op-bound spelling
/// `fact PartialEq/Eq[T=sort, eq=…]`, or (WI-837) a witness sort's own `eq`. Sharing
/// the function, rather than restating the criterion, is what keeps the classifier
/// boundary == the resolver's dispatch boundary, so a carrier that dispatches its own
/// `eq` is neither field-wise'd nor false-derived `NonEq` against its own `Eq`.
///
/// WI-856 — the DOMAINS now agree on the composite half too, so a NAMESPACE-LEVEL
/// entity that is a boundary here also keys the index there
/// ([`super::load::eq_dispatch_carrier_domain`]).
///
/// An AMBIGUOUS carrier (more than one candidate) is a boundary here and a load error
/// at the index build: this pass runs after that refusal is already recorded, and
/// treating it as non-boundary would pile a spurious `NonEq` conflict on top.
fn is_eq_boundary(
    kb: &KnowledgeBase,
    eq_index: Option<&super::load::EqDispatchIndex>,
    sort: Symbol,
) -> bool {
    eq_index.is_some_and(|ix| !ix.candidates(kb, sort).is_empty())
}

/// The sorts that ALREADY provide `NonEq` — the partial leaves the fixpoint seeds
/// from (the non-parametric `Float`, plus any hand-written `NonEq`). Scans the
/// `SortProvidesInfo` facts for a `NonEq` spec.
///
/// WI-20260919-9KYPA — UNCONDITIONALLY, and the filter is load-bearing, not hygiene.
/// This used to say it "runs BEFORE this pass derives any, so it never reads its own
/// output", which is true of the FIRST load phase and false of every later one: the rows
/// persist, so phase 2 re-classifies with them in the relation (the same WI-1103 hazard
/// that made the derived rows' op-backing exemption a MARK rather than a placement).
/// Once [`derive_conditional_noneq`] existed that stopped being harmless. A conditional
/// `NonEq[List] :- NonEq[T]` is not a partial leaf — `List` is partial at `Float` and
/// lawful at `Int64` — but seeded as one it makes EVERY composite holding a `List` field
/// `Partial`, which derives a `NonEq` for each and collides with the `provides Eq` those
/// composites write. MEASURED at this ticket: ~130 tests, the whole stdlib refusing on
/// `EffectExpression` and 20 more.
///
/// [`super::typing::provision_is_conditional`] is the shared reading, so the seed here
/// and `check_eq_noneq_exclusive` cannot disagree about which carriers are leaves.
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
        let Some(named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        let Some(sr) = super::typing::get_named_arg(kb, &named, "sort_ref") else {
            continue;
        };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else {
            continue;
        };
        let Some(spec_view) = super::typing::get_named_arg(kb, &named, "spec") else {
            continue;
        };
        let Some(spec_base) = super::load::provides_spec_base_sym(kb, spec_view) else {
            continue;
        };
        if kb.canonical_sort_sym(spec_base) == noneq_canon
            && !super::typing::provision_is_conditional(kb, carrier, noneq)
        {
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
///
/// WI-20260918-CKD4J (the `NonEq` mirror) — AND THE SORTS A FIELD TYPE'S ARGUMENTS
/// NAME, through every parametric application: `o: Option[T = Float]` contributes
/// `Option` and `Float`, `p: Pair[A = Float, B = Int64]` contributes `Pair`, `Float`,
/// `Int64`. A parametric container's equality compares its elements (a parametric
/// boundary's own `eq` included — `Pair.eq` compares components), so a `Float`
/// argument makes the field partial. Only the ARGUMENTS are entered, never a sort's
/// own fields, so a non-parametric boundary (`TotalFloat`) still shields its `Float`.
/// The Total half reads the same list and is unmoved by the extra entries: a field
/// whose head is parametric already excludes its composite there.
fn composite_field_sorts(kb: &KnowledgeBase, sort: Symbol) -> Vec<Symbol> {
    let mut out: Vec<Symbol> = Vec::new();
    for ctor in kb.field_constructors_of_sort(sort) {
        let Some(fields) = kb.entity_field_types(ctor) else {
            continue;
        };
        let fields: Vec<(Symbol, Value)> = fields.to_vec();
        for (_name, ftype) in &fields {
            push_type_sorts(kb, ftype, &mut out);
        }
    }
    out
}

/// A type's head sort, then — for a parametric head — the sorts its argument types
/// name, recursively. See [`composite_field_sorts`].
fn push_type_sorts<V: TermView>(kb: &KnowledgeBase, ty: &V, out: &mut Vec<Symbol>) {
    let Some(head) = super::typing::sort_functor_of_view(kb, ty) else {
        return;
    };
    out.push(head);
    if kb.type_param_syms_of(head).is_empty() {
        return;
    }
    for key in ty.named_keys(kb) {
        if let Some(arg) = ty.named_arg(kb, key) {
            push_type_sorts(kb, &arg.to_value(), out);
        }
    }
}

/// Assert a derived `SortProvidesInfo(sort_ref = carrier, spec = SortView(spec, <T>
/// = carrier))` fact — byte-identical in shape to `Float`'s `fact NonEq[T = Float]`
/// (the loader's `maybe_emit_fact_provides_info`, load.rs), so every provides-fact
/// reader (`check_eq_noneq_exclusive`, `sort_provides`, …) reads it unchanged.
///
/// WI-1103 — returns the row's `RuleId` so [`run`] can MARK it (the shape stays
/// byte-identical; the mark is KB-side, not a field). Deliberately not marked here:
/// [`derive_total_eq`] asserts through this same function and its rows are held to
/// provider coverage.
fn assert_provides(kb: &mut KnowledgeBase, carrier: Symbol, spec: Symbol) -> RuleId {
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
    let provides_sort = ClauseKind::Requirement;
    kb.assert_fact_carrier(
        provides_sym,
        Vec::new(),
        vec![
            (sort_ref_key, Value::term(sort_ref_term)),
            (spec_key, Value::term(spec_view)),
        ],
        provides_sort,
        carrier, // domain = the carrier
        None,
    )
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
                ViewHead::Functor {
                    functor: fa,
                    pos_arity: pa,
                    named_arity: na,
                },
                ViewHead::Functor {
                    functor: fb,
                    pos_arity: pb,
                    named_arity: nb,
                },
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
    /// reflexivity shortcut? `true` for a bare `Float` (read carrier-neutrally
    /// through the view from ANY carrier), for an entity whose constructor is a
    /// derived `NonEq` carrier ([`Self::field_wise_noneq_carriers`]), and for a
    /// tuple any of whose fields reaches one. `false` for a lawful-Eq boundary
    /// (`TotalFloat`/`Set`/`Map` — own `eq`, so NOT in the set), an all-`Eq`
    /// composite, and every scalar.
    ///
    /// WI-689 — a thin [`KnowledgeBase::fold_gate`] over
    /// [`crate::kb::resolve::REACHES_PARTIAL_CARRIER`]: a structural (non-σ) `Any`
    /// scan whose head-check stops at a `Float` leaf and at any sort/constructor
    /// head — reading the precomputed per-constructor classification in O(1) (it
    /// already stopped at lawful-Eq boundaries, so there is no descent into a
    /// `TotalFloat` field) — while a functor-less aggregate (tuple/unit, no sort to
    /// key on) walks its fields.
    pub(crate) fn value_reaches_partial_carrier(&self, v: &Value) -> bool {
        // A structural (non-σ) gate — `None` is the inert empty σ `fold_gate` never
        // consults for `chase_sigma: false`, so no `Substitution` is minted per call.
        self.fold_gate(v, None, 0, crate::kb::resolve::REACHES_PARTIAL_CARRIER)
    }
}
