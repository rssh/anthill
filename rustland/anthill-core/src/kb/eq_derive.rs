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
//!   A sort derives `Eq` iff every field's equality is lawful — a GREATEST one, since
//!   totality must hold for ALL fields and so shrinks from an optimistic seed
//!   ([`derive_conditional_eq`]'s fixpoint, over each field's TYPE).
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
//! * **The `eq` member** — each composite this module gives `PartialEq` also gets the
//!   `eq` a program would write for it ([`derived_eq_member_source`]): it compares the
//!   constructors and then each field through the `eq` the field's type supplies, so
//!   `eq(Point(nan,_), Point(nan,_))` is `Float.eq(nan, nan) ∧ … = false`, agreeing
//!   with the field-wise C++ `operator==`, and a field of a sort with its own `eq`
//!   (`Box.p: Pt`) is compared by that `eq`.
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
//!   same two reasons. [`derive_conditional_eq`] asserts every derived
//!   `Eq`+`PartialEq`, unconditional (`Colour`) and conditional (`List :- Eq[T]`)
//!   alike, and must run BEFORE the typer AND have its rows reach the sort-ops table
//!   (the load refreshes that table after it for exactly this reason) — that
//!   function's doc carries why, and why the `NonEq` half cannot join it.
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
//! member of a parametric sort compares a field typed by its parameter through the
//! parameter's `eq`, so `some(nan)` is unequal to itself. WI-20260919-9KYPA closes the
//! last leg: a parametric sort derives the CONDITIONAL `NonEq` row itself
//! ([`derive_conditional_noneq`], `NonEq[List] :- NonEq[T]`). The use-site key check (`check_use_site_requires_eq`) asks the positive
//! goal `Eq[T = key]` at the whole written key, so it reads the conditional `Eq` row
//! rather than this one: `Map[K = List[T = Float]]` is refused where the type is written
//! while `Map[K = List[T = Int64]]` loads, and a tuple key is read by its components.

use std::collections::HashSet;

use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::Symbol;
use crate::kb::term::Term;
use crate::kb::term_view::{TermView, ViewHead};
use crate::kb::{ClauseKind, ClauseLabel};
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
    /// Field sorts, canonical, whose own `eq` is declared and left unimplemented (`Map`'s,
    /// `typing::sorts_with_unbacked_eq`): a field of one is a field nothing decides.
    unbacked_eq: HashSet<Symbol>,
}

/// WI-664 — compute the classification. Runs ONCE, at the EARLIER of the two
/// assertion points ([`derive_conditional_eq`]), because every input is final by then: the
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
/// composite's `NonEq` with nothing pointing at the cause.
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

    let field_heads: HashSet<Symbol> =
        field_sorts.iter().flat_map(|(_, fs)| fs.iter().copied()).collect();
    let unbacked_eq = super::typing::sorts_with_unbacked_eq(kb, &field_heads);

    EqClassification {
        sorts,
        boundary,
        partial,
        field_sorts,
        unbacked_eq,
    }
}

/// WI-20260918-CKD4J — a derived condition: `spec[P]` over the carrier's OWN type
/// parameter `P`. The derived row reads `provides X[S] :- spec₁[P₁], …`.
pub(crate) type Condition = (Symbol, Symbol);

/// WI-1098 / WI-20260918-CKD4J — THE `Eq` derivation: the derived `Eq` (+ its `PartialEq`
/// base) of every composite whose fields' equality is lawful, and the `PartialEq` of a
/// `Partial` one. ONE pass for every such row (WI-20261102-YX17K): a non-parametric
/// composite (`Colour`, `Duration`) derives an UNCONDITIONAL row — the empty condition
/// list, recorded as one clause, exactly as a written `provides Eq[T = Colour]` is —
/// and a PARAMETRIC sort (`List[T]`, `Option[T]`, a user `Box[T]`) or a composite whose
/// field is one at concrete arguments (`holder(o: Option[T = Int64])`) a row resting
/// on its arguments' equality. There was a second pass for the first kind, deriving
/// the pair over each field's head sort; this one derived the same rows behind it, so
/// backing either out measured nothing.
///
/// A PRE-TYPER pass, and that placement is the whole point: a provision only reaches a
/// call site through the typer, which tags each spec-op call with a `CallClass` that
/// `req_insertion` turns into the caller-frame dictionary. Asserted where the `NonEq`
/// half is ([`run`], after the typer) the fact exists and NO call site was ever
/// rewritten to read it — MEASURED (WI-1098): `List.contains(cons(red, nil), red)` still
/// died with `DeferToRequirement: requirement param __req_eq not bound in caller frame …
/// frame binds []`, byte-identical to the no-provision baseline.
///
/// The SECOND reader is the sort-ops table, whose pass 2 inherits the spec's `eq` onto
/// each providing carrier; the load refreshes that table after this pass because it is
/// built above (the eq-dispatch index the classification reads is built off it).
/// Without the refresh the provision exists, dispatch RESOLVES it, and then
/// `sort_ops_lookup(carrier, eq)` answers `None` → `NoMatch` — so deriving a provision
/// BREAKS a direct `eq(a, b)` call that worked without one. `load.rs` carries that
/// measurement.
///
/// The `NonEq` half cannot move here, and the asymmetry has a reason rather than being
/// an accident of ordering: a derived `NonEq` carries the witness operation
/// `nonEqRefl`, which no carrier backs, so it must stand AFTER `check_provider_operations`
/// (see the module header). A derived `Eq`/`PartialEq` introduces no unbacked operation
/// — its `eq` is the derived member ([`derived_eq_member_source`]), as a hand-written
/// `provides PartialEq[T = Colour]`'s is — so these rows are held to the same bar as a
/// written provision, which is what they should be.
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
/// A GREATEST fixpoint, because totality must hold for ALL fields: `List` is `cons(head:
/// T, tail: List[T = T])`, lawful iff `T` is, which only an optimistic seed derives —
/// and a non-parametric composite reached through another one's field (`Box(c: Colour)`)
/// reads the field's current verdict in the fixpoint, not a row asserted before it.
///
/// NOT DERIVED, each deliberately: an equality BOUNDARY (its `eq` is the author's), a
/// carrier any equality provision already names (`Pair` writes its own — not
/// duplicated), and a sort with a field whose equality nothing decides (an arrow, an
/// opaque handle, an unwritten argument; for `Eq`, a `Float`).
///
/// A `Partial` composite is a candidate for `PartialEq` and not for `Eq`: `holder(o:
/// Option[T = Float])` reaches `Float` through its field type's ARGUMENTS
/// ([`composite_field_sorts`]) and so classifies `Partial`, and its `PartialEq` rests on
/// `PartialEq[Float]`, which holds. One with a field nothing decides derives no
/// `PartialEq`, and [`run`] then derives it no `NonEq`.
pub(crate) fn derive_conditional_eq(kb: &mut KnowledgeBase, c: &EqClassification) -> Vec<Symbol> {
    // Both or neither: the two are declared in one file, `prelude/eq.anthill`. Neither is a
    // prelude-less KB, which has no equality to derive.
    let (Some(partial_eq), Some(eq)) = (
        kb.try_resolve_symbol("anthill.prelude.PartialEq"),
        kb.try_resolve_symbol("anthill.prelude.Eq"),
    ) else {
        return Vec::new();
    };
    // The carriers given `PartialEq` here, for [`derived_eq_member_source`].
    let mut given: Vec<Symbol> = Vec::new();
    let spoken_for = EqualityProvisions::of(kb);
    // One symbol per canonical composite, in registration order.
    let mut seen: HashSet<Symbol> = HashSet::new();
    let all_candidates: Vec<Symbol> = c
        .sorts
        .iter()
        .copied()
        .filter(|&s| {
            let cs = kb.canonical_sort_sym(s);
            seen.insert(cs)
                && !c.boundary.contains(&cs)
                && !spoken_for.speak_for(kb, cs)
                // For its own values: a witness row of the composite's is about another sort
                // (WI-20261126-DHB0C, `sort_provides_for_itself`).
                && !super::typing::sort_provides_for_itself(kb, s, eq)
                && !super::typing::sort_provides_for_itself(kb, s, partial_eq)
        })
        .collect();
    for spec in [partial_eq, eq] {
        let candidates: Vec<Symbol> = all_candidates
            .iter()
            .copied()
            .filter(|&s| {
                spec == partial_eq || !c.partial.contains(&kb.canonical_sort_sym(s))
            })
            .collect();
        let derived = conditional_rows(kb, &candidates, spec, &c.unbacked_eq, &spoken_for);
        for &s in &candidates {
            let Some(conds) = derived.get(&kb.canonical_sort_sym(s)).cloned() else {
                continue;
            };
            assert_provides(kb, s, spec);
            record_derived_conditions(kb, s, spec, &conds);
            if spec == partial_eq {
                given.push(s);
            }
            // WI-20260919-9KYPA — carry the parameters across to `run`, which mirrors
            // them into the `NonEq` half. BOTH specs: the mirror needs the `Eq` list for
            // its disjuncts and the `PartialEq` list for the conditions `NonEq requires
            // PartialEq` obliges it to carry.
            if !conds.is_empty() {
                let cs = kb.canonical_sort_sym(s);
                kb.conditional_eq_conditions.insert((cs, spec), conds);
            }
        }
    }
    given
}

/// The conditions each of `candidates` can be given `spec` under, by canonical carrier — a
/// GREATEST fixpoint over the fields' types ([`field_conditions`]): every candidate seeded
/// derivable and resting on nothing, and one dropped as soon as a field's `spec` rests on
/// nothing the carrier can name. A carrier absent from the answer is given no row.
fn conditional_rows(
    kb: &KnowledgeBase,
    candidates: &[Symbol],
    spec: Symbol,
    unbacked_eq: &HashSet<Symbol>,
    equality_family: &EqualityProvisions,
) -> std::collections::HashMap<Symbol, Vec<Condition>> {
    let mut derived: std::collections::HashMap<Symbol, Vec<Condition>> = candidates
        .iter()
        .map(|&s| (kb.canonical_sort_sym(s), Vec::new()))
        .collect();
    loop {
        let mut changed = false;
        for &s in candidates {
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
                    match field_conditions(kb, &ftype, spec, &params, &derived, unbacked_eq, equality_family) {
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
    derived
}

/// `Hash` for the composites whose `Eq` is structural — derived by the pass above
/// (`given`, the carriers they gave `PartialEq`), or written with no condition and no `eq` of
/// the sort's own: a hash that agrees with that `eq`, where every field's type has one — over
/// a parameter, the row rests on `Hash` of it (`provides Hash[Option] :- Hash[T]`), as the
/// `Eq` row rests on `Eq`. A sort that writes its own `eq`, or a conditional `Eq` (`provides
/// Eq[T = Box] :- Ord[T]`, which a row resting on the fields' `Hash` would not entail), writes
/// its `hash` beside it; a field of one that writes no `hash` (`Box(p: Pt)`) leaves its carrier
/// without `Hash`: no hash its `eq` agrees with is known. The carriers given `Hash`, for
/// [`derived_hash_member_source`].
pub(crate) fn derive_hash(kb: &mut KnowledgeBase, c: &EqClassification, given: &[Symbol]) -> Vec<Symbol> {
    let (Some(eq), Some(hash), true) = (
        kb.try_resolve_symbol("anthill.prelude.Eq"),
        kb.try_resolve_symbol("anthill.prelude.Hash"),
        hash_members_writable(kb),
    ) else {
        return Vec::new();
    };
    let mut seen: HashSet<Symbol> = HashSet::new();
    let candidates: Vec<Symbol> = c
        .sorts
        .iter()
        .copied()
        .filter(|&s| {
            seen.insert(kb.canonical_sort_sym(s))
                && !c.boundary.contains(&kb.canonical_sort_sym(s))
                && (given.contains(&s) || !super::typing::provision_is_conditional(kb, s, eq))
                // Its own `Eq`, not one it witnesses for another sort: read as its own, a
                // witness of another's `Eq` was given `Hash` and, forwarded from it, an `Eq`
                // and a `PartialEq` of its values the derivation had not given it
                // (WI-20261126-DHB0C, `sort_provides_for_itself`).
                && super::typing::sort_provides_for_itself(kb, s, eq)
                && !super::typing::sort_provides_for_itself(kb, s, hash)
                // An operation `hash` the sort writes is its author's, which the row would
                // take as its member unread: such a sort writes its `provides Hash`.
                && kb.try_resolve_symbol(&format!("{}.hash", kb.qualified_name_of(s))).is_none()
        })
        .collect();
    let equality_family = EqualityProvisions::of(kb);
    let derived = conditional_rows(kb, &candidates, hash, &c.unbacked_eq, &equality_family);
    let mut out = Vec::new();
    for &s in &candidates {
        let Some(conds) = derived.get(&kb.canonical_sort_sym(s)).cloned() else {
            continue;
        };
        assert_provides(kb, s, hash);
        record_derived_conditions(kb, s, hash, &conds);
        out.push(s);
    }
    out
}

/// The composites whose `PartialEq` a program wrote and gave no `eq`: a provision binding no
/// member, of a sort that writes no `eq` and is no boundary. Each is given the member
/// [`derived_eq_member_source`] gives a composite whose `PartialEq` this load derived, so every
/// provision of `PartialEq` has a member and a typed `=` at the carrier calls it. `given` is
/// the composites the derivation gave `PartialEq`, which have theirs. Refused, each naming its
/// repair: one with a field whose equality nothing decides (a function, a sort whose `eq` is
/// declared and not implemented), whose author writes the `eq`; and one with a field typed by a
/// parameter whose provision states no condition, which the member's comparison at the
/// parameter needs (`:- PartialEq[T]`).
pub(crate) fn written_without_member(
    kb: &mut KnowledgeBase,
    c: &EqClassification,
    given: &[Symbol],
) -> (Vec<Symbol>, Vec<super::load::LoadError>) {
    let Some(partial_eq) = kb.try_resolve_symbol("anthill.prelude.PartialEq") else {
        return (Vec::new(), Vec::new());
    };
    let mut seen: HashSet<Symbol> = given.iter().map(|&s| kb.canonical_sort_sym(s)).collect();
    let written: Vec<Symbol> = c
        .sorts
        .iter()
        .copied()
        .filter(|&s| {
            let cs = kb.canonical_sort_sym(s);
            !c.boundary.contains(&cs)
                // A sort whose scope declares `eq` has one: the member an earlier load
                // derived, or a predicate its rules define (`derived_eq_member_source`).
                && kb.try_resolve_symbol(&format!("{}.eq", kb.qualified_name_of(s))).is_none()
                && super::typing::sort_provides(kb, s, partial_eq)
                && seen.insert(cs)
        })
        .collect();
    // Given's members count as decided: a field of a composite the derivation gave
    // `PartialEq` compares through its member.
    let mut candidates = written.clone();
    candidates.extend(given.iter().copied());
    let equality_family = EqualityProvisions::of(kb);
    let derived = conditional_rows(kb, &candidates, partial_eq, &c.unbacked_eq, &equality_family);
    let mut refusals = Vec::new();
    let mut members = Vec::new();
    for s in written {
        let params: Vec<Symbol> = kb.type_param_syms_of(s).to_vec();
        if let Some(needed) = derived.get(&kb.canonical_sort_sym(s)) {
            // The member compares a field typed by a parameter through `PartialEq` at it,
            // read from the slot the provision's condition gives its frame.
            let frame = super::typing::provider_dict_entries(kb, s, Some(partial_eq));
            let held = |p: Symbol| {
                frame.entries().iter().any(|e| {
                    kb.canonical_sort_sym(e.required_sort) == kb.canonical_sort_sym(partial_eq)
                        && spec_arguments(kb, &e.spec)
                            .iter()
                            .any(|a| own_param_of(kb, a, &params) == Some(p))
                })
            };
            let missing: Vec<Symbol> = needed.iter().map(|&(_, p)| p).filter(|&p| !held(p)).collect();
            if missing.is_empty() {
                members.push(s);
            } else if !super::typing::partial_eq_is_conditional(kb, s, partial_eq) {
                refusals.push(super::load::LoadError::EqNeedsCondition {
                    carrier: kb.qualified_name_of(s).to_string(),
                    params: missing.iter().map(|&p| kb.local_name_of(p).to_string()).collect(),
                });
            }
            // A condition that reaches `PartialEq` at the parameter through another spec
            // (`:- Eq[T]`) gives the frame that spec's slot, and a member's call at the
            // parameter is not read through it, written or derived alike. Such a provision is
            // left with no member, and refused for it once the load's suppliers are all in
            // ([`equality_reaching_no_eq`]) — a `PartialEq` forwarded from `provides Eq[Self]
            // :- Eq[T]` among them, which `partial_eq_is_conditional` reads before the row
            // exists: read here as unconditional, it was refused as a `PartialEq` "with no
            // condition" the author never wrote (WI-20261121-TV0PA).
            continue;
        }
        // A field of a boundary — a carrier whose `eq` its author wrote, a witness's among them
        // (`EqList` giving `List` its equality) — is decided by that `eq`, which the rows do not
        // read: the member is given, and typed with the rest.
        let undecided = kb.field_constructors_of_sort(s).into_iter().find_map(|ctor| {
            kb.entity_field_types(ctor)?.iter().find_map(|(name, ty)| {
                let at_a_boundary = super::typing::sort_functor_of_view(kb, ty)
                    .is_some_and(|h| c.boundary.contains(&kb.canonical_sort_sym(h)));
                (!at_a_boundary
                    && field_conditions(kb, ty, partial_eq, &params, &derived, &c.unbacked_eq, &equality_family).is_none())
                .then(|| (*name, ty.clone()))
            })
        });
        let Some((field, ty)) = undecided else {
            members.push(s);
            continue;
        };
        refusals.push(super::load::LoadError::EqNotDerivable {
            carrier: kb.qualified_name_of(s).to_string(),
            field: kb.local_name_of(field).to_string(),
            field_type: super::typing::type_display_name_value(kb, &ty),
        });
    }
    (members, refusals)
}

/// Whether a derived `eq` member can be written at all: the library it is written in —
/// `PartialEq.eq`, `struct_eq` and `Bool` — is loaded. [`derived_eq_member_source`] writes none
/// without it, and [`equality_reaching_no_eq`] then asks for none.
fn eq_members_writable(kb: &KnowledgeBase) -> bool {
    // Declared, not merely named: the bootstrap names `struct_eq` without the library.
    let declared = |n: &str| {
        kb.try_resolve_symbol(n)
            .is_some_and(|s| super::op_info::operation_is_declared(kb, s))
    };
    declared("anthill.prelude.PartialEq.eq")
        && declared("anthill.kernel.struct_eq")
        && kb.try_resolve_symbol("anthill.prelude.Bool").is_some()
}

/// A composite whose equality no derived member writes, by design: the two the member writer
/// leaves out ([`derived_eq_member_source`]), and so the two [`equality_reaching_no_eq`] does
/// not ask for one.
///
/// The desugaring targets (`TupleLiteral`, `ListLiteral`, …) are how a tuple or a literal is
/// represented, not sorts a program compares by their constructors: a tuple's components are
/// compared where `=` meets one (`KnowledgeBase::tuple_component_pairs`). And a sort whose
/// scope declares `eq` already — a predicate its rules define, which is no operation and so no
/// `eq` of the carrier's, and which the `eq` bridge proves — has the name for the program: a
/// member there would be a second definition of it.
fn compared_without_a_member(kb: &KnowledgeBase, carrier: Symbol) -> bool {
    use crate::parse::desugar_target as dt;
    let literals = [dt::TUPLE_LITERAL, dt::LIST_LITERAL, dt::SET_LITERAL].map(dt::qualified);
    literals.contains(&kb.qualified_name_of(carrier))
        || kb
            .try_resolve_symbol(&format!("{}.eq", kb.qualified_name_of(carrier)))
            .is_some()
}

/// WI-20261121-TV0PA — every composite a provision of `PartialEq` is about has an `eq` that
/// answers it, or the load is refused (`LoadError::EqualityReachesNoEq`). Asked once the load's
/// suppliers are all in: the forwarded rows (`Eq provides PartialEq`, so a witness that writes
/// `Eq` alone is read here), the derived members, and the eq-dispatch index rebuilt over them.
///
/// The run-time error it replaces is `EqualityWithNoMember`, raised at the first comparison: a
/// witness speaks for its carrier, so the load derives the carrier no equality, and a witness
/// that writes no `eq` leaves nothing to dispatch to — `sort W { provides PartialEq[T = C] }`
/// loaded and `eq(c(v: 1), c(v: 2))` died (MEASURED, c3371cd0). `PartialEq.eq` is a builtin,
/// so the provider-coverage check reads it as backed for every provider: the builtin is the
/// dispatch to the carrier's `eq`, and backs nothing where there is none. A carrier's own
/// provision with no `eq` is given the derived member, so it is refused here only where none
/// can be (a condition at another spec, [`written_without_member`]).
pub(crate) fn equality_reaching_no_eq(kb: &mut KnowledgeBase) -> Vec<super::load::LoadError> {
    let Some(partial_eq) = kb.try_resolve_symbol("anthill.prelude.PartialEq") else {
        return Vec::new();
    };
    if !eq_members_writable(kb) {
        return Vec::new();
    }
    let Some(index) = super::load::EqDispatchIndex::build(kb) else {
        return Vec::new();
    };
    let composites: HashSet<Symbol> = composite_sorts(kb)
        .into_iter()
        .filter(|&s| !compared_without_a_member(kb, s))
        .map(|s| kb.canonical_sort_sym(s))
        .collect();
    // Each composite's provisions of `PartialEq` at its carrier (WI-20261121-JE2MT), in
    // relation order; the composites in any order, the refusals being sorted below.
    let provisions = super::typing::ProvisionsOfSpec::of(kb, partial_eq);
    let eq_op = kb.try_resolve_symbol("anthill.prelude.PartialEq.eq");
    // Interned as the sort-operations table keys a short name (`load::intern_op_short`): looked
    // up, it can be another symbol (`record_members_that_supply_nothing` has the measurement).
    let eq_short = eq_op.map(|_| kb.intern("eq"));
    let mut unanswered: Vec<(Symbol, Vec<(Symbol, Symbol)>, Vec<Symbol>)> = Vec::new();
    for &carrier in &composites {
        let at = provisions.at_sort(kb, carrier);
        if at.is_empty() || !index.candidates(kb, carrier).is_empty() {
            continue;
        }
        let mut written: Vec<(Symbol, Symbol)> = Vec::new();
        let mut passed_over: Vec<Symbol> = Vec::new();
        for p in at {
            let entry = (
                kb.canonical_sort_sym(p.provider),
                written_spec_of(kb, p.provider, p.row, partial_eq, carrier),
            );
            if !written.contains(&entry) {
                written.push(entry);
            }
            // A witness's own `eq` the dispatch passed over for this carrier (WI-20261126-Q1WE9):
            // the member its name reaches, whatever it supplies the witness's own values
            // (WI-20261126-DHB0C).
            if let (Some(eq_op), Some(eq_short)) = (eq_op, eq_short) {
                if !super::typing::same_sort_canonical(kb, p.provider, carrier) {
                    if let Some(member) =
                        super::typing::member_declared_under(kb, p.provider, eq_op, eq_short)
                    {
                        if kb.witness_member_supplies_nothing(p.provider, eq_op, p.row)
                            && !passed_over.contains(&member)
                        {
                            passed_over.push(member);
                        }
                    }
                }
            }
        }
        unanswered.push((carrier, written, passed_over));
    }
    let mut out: Vec<(String, Vec<(String, String)>, Vec<String>)> = unanswered
        .into_iter()
        .map(|(carrier, provisions, passed_over)| {
            (
                kb.qualified_name_of(carrier).to_string(),
                provisions
                    .into_iter()
                    .map(|(provider, spec)| {
                        (
                            kb.qualified_name_of(provider).to_string(),
                            kb.qualified_name_of(spec).to_string(),
                        )
                    })
                    .collect(),
                passed_over.into_iter().map(|m| kb.qualified_name_of(m).to_string()).collect(),
            )
        })
        .collect();
    out.sort();
    out.into_iter()
        .map(|(carrier, provisions, passed_over)| super::load::LoadError::EqualityReachesNoEq {
            carrier,
            provisions,
            passed_over,
        })
        .collect()
}

/// The spec `provider` WROTE for the provision row `row` of `spec`, at `carrier`'s carrier:
/// `spec` itself, or, for a row the forwarding derived, the spec of the provision it was
/// derived from, followed down to the written one (`Hash` → `Eq` → `PartialEq`), as deep as the
/// forwarding derives (`derive_forwarded_provisions`' rounds). The source is `provider`'s
/// provision of the origin AT THE SAME CARRIER (WI-20261121-JE2MT): the forwarding asserts its
/// row at the source's bindings, so a provider writing `Eq` at two sorts is followed to the
/// one this row was derived from, not to the first it wrote.
fn written_spec_of(
    kb: &KnowledgeBase,
    provider: Symbol,
    row: RuleId,
    spec: Symbol,
    carrier: Symbol,
) -> Symbol {
    let provider = kb.canonical_sort_sym(provider);
    let (mut row, mut spec) = (row, spec);
    for _ in 0..8 {
        let Some(origin) = kb.derived_provision_origin_of(row) else {
            break;
        };
        spec = origin;
        let Some(source) = super::typing::ProvisionsOfSpec::of(kb, origin)
            .at_sort(kb, carrier)
            .into_iter()
            .find(|q| kb.canonical_sort_sym(q.provider) == provider)
            .map(|q| q.row)
        else {
            break;
        };
        row = source;
    }
    spec
}

/// The arguments of a spec application `v` (`PartialEq[T = A]`, `PartialEq[A]`), by position
/// and by name.
fn spec_arguments(kb: &KnowledgeBase, v: &Value) -> Vec<Value> {
    let mut out: Vec<Value> = (0..)
        .map_while(|i| v.pos_arg(kb, i).map(|a| a.to_value()))
        .collect();
    out.extend(v.named_keys(kb).into_iter().filter_map(|k| v.named_arg(kb, k).map(|a| a.to_value())));
    out
}

/// The `hash` a composite this load gave `Hash` is given ([`derive_hash`]), as
/// [`derived_eq_member_source`] gives its `eq`: the member a program would write, mixing a
/// constructor's position with each field's `hash` through the field type's instance —
///
/// ```text
/// operation hash(value: Self) -> Int64 =
///   match value
///     case just(v1) -> hash_mix(0, Hash.hash(v1))
///     case nada() -> 1
/// ```
///
/// — and, for a composite every field of which compares by structure, the structure's hash
/// (`struct_hash(value)`), which its `eq` agrees with as `===` does.
pub(crate) fn derived_hash_member_source(kb: &KnowledgeBase, carriers: &[Symbol]) -> Result<Option<String>, String> {
    let mut seen: HashSet<Symbol> = HashSet::new();
    let mut carriers: Vec<Symbol> = carriers
        .iter()
        .copied()
        .filter(|&s| seen.insert(kb.canonical_sort_sym(s)))
        .collect();
    if carriers.is_empty() {
        return Ok(None);
    }
    carriers.sort_by(|a, b| kb.qualified_name_of(*a).cmp(kb.qualified_name_of(*b)));
    let structural = structural_carriers(kb, &carriers);
    let mut out = String::new();
    for &carrier in &carriers {
        write_hash_member(kb, carrier, structural.contains(&kb.canonical_sort_sym(carrier)), &mut out)?;
    }
    Ok(Some(out))
}

/// Does the KB declare what a derived `hash` member calls — `Hash.hash` and the kernel's
/// `struct_hash` and `hash_mix`? Where it does not, no `Hash` row is derived: a row with no
/// member is one no call can run.
fn hash_members_writable(kb: &KnowledgeBase) -> bool {
    ["anthill.prelude.Hash.hash", "anthill.kernel.struct_hash", "anthill.kernel.hash_mix"]
        .iter()
        .all(|n| kb.try_resolve_symbol(n).is_some_and(|s| super::op_info::operation_is_declared(kb, s)))
}

/// One carrier's secondary entry with its `hash` member; see [`derived_hash_member_source`].
fn write_hash_member(kb: &KnowledgeBase, carrier: Symbol, by_structure: bool, out: &mut String) -> Result<(), String> {
    use std::fmt::Write;
    const HASH: &str = "..anthill.prelude.Hash.hash";
    const MIX: &str = "..anthill.kernel.hash_mix";
    let qn = kb.qualified_name_of(carrier);
    let scope = kb.symbols.scope_id(carrier);
    let value = unused_name(kb, scope, "value");
    let segments: Vec<&str> = qn.split('.').collect();
    for (depth, segment) in segments.iter().enumerate() {
        let _ = writeln!(out, "{}namespace {segment}", "  ".repeat(depth));
    }
    let indent = "  ".repeat(segments.len());
    let _ = writeln!(out, "{indent}operation hash({value}: Self) -> ..anthill.prelude.Int64 =");
    let close = |out: &mut String| {
        for depth in (0..segments.len()).rev() {
            let _ = writeln!(out, "{}end", "  ".repeat(depth));
        }
    };
    if by_structure {
        let _ = writeln!(out, "{indent}  ..anthill.kernel.struct_hash({value})");
        close(out);
        return Ok(());
    }
    let mut ctors = kb.field_constructors_of_sort(carrier);
    ctors.sort_by_key(|c| c.index());
    ctors.dedup();
    if ctors.is_empty() {
        return Err(format!("the composite `{qn}` has no constructor to hash"));
    }
    let _ = writeln!(out, "{indent}  match {value}");
    for (position, &ctor) in ctors.iter().enumerate() {
        let name = kb.local_name_of(ctor).to_string();
        let arity = kb.entity_field_types(ctor).map_or(0, |f| f.len());
        let binders: Vec<String> = (1..=arity).map(|i| unused_name(kb, scope, &format!("v{i}"))).collect();
        let mut acc = position.to_string();
        for b in &binders {
            acc = format!("{MIX}({acc}, {HASH}({b}))");
        }
        let _ = writeln!(out, "{indent}    case {name}({}) -> {acc}", binders.join(", "));
    }
    close(out);
    Ok(())
}

/// The `eq` a composite whose `PartialEq` this load derived is given: the member a
/// program would write for it, as the text of one secondary entry of the sort per
/// carrier. The loader loads the text in this same load, before the typer, with each
/// member in the derived provision's `where` block, so a member of a parametric sort
/// reads its provision's conditions (`provides PartialEq[Option] :- PartialEq[T]`)
/// as a written member does (`load::load_derived_eq_members`).
///
/// A member compares the constructors and then each field through the `eq` the
/// field's type supplies:
///
/// ```text
/// operation eq(left: Self, right: Self) -> Bool =
///   match (left, right)
///     case (just(l1), just(r1)) -> PartialEq.eq(l1, r1)
///     case (nada(), nada()) -> true
///     case _ -> false
/// ```
///
/// The typer pins each field's call at the field's type (`Box.p` → `Pt.eq`), or reads
/// it through the parameter's dictionary (`some(v)` → `T`'s). A recursive composite's
/// member calls itself. A composite whose every field compares by structure
/// ([`structural_carriers`]) is compared by structure, `left === right`, which is the
/// same answer.
///
/// The text is written in the standard library's names (`PartialEq.eq`, `Bool`, `===`), so
/// a knowledge base loaded without the library has no members, as it has no `eq` spec
/// operation to dispatch to one.
///
/// The text, with the carriers it gives a member, in its order; `None` when it gives
/// none. An `Err` is a carrier the text cannot be written for, which is a defect of this
/// function, reported rather than skipped.
pub(crate) fn derived_eq_member_source(
    kb: &KnowledgeBase,
    carriers: &[Symbol],
) -> Result<Option<(String, Vec<Symbol>)>, String> {
    if !eq_members_writable(kb) {
        return Ok(None);
    }
    let mut seen: HashSet<Symbol> = HashSet::new();
    let mut carriers: Vec<Symbol> = carriers
        .iter()
        .copied()
        .filter(|&s| seen.insert(kb.canonical_sort_sym(s)))
        .collect();
    if carriers.is_empty() {
        return Ok(None);
    }
    // In one order on every run: the carriers arrive in a hash map's, and the text's order
    // is the order its names are interned in.
    carriers.sort_by(|a, b| kb.qualified_name_of(*a).cmp(kb.qualified_name_of(*b)));
    carriers.retain(|&c| !compared_without_a_member(kb, c));
    if carriers.is_empty() {
        return Ok(None);
    }
    let structural = structural_carriers(kb, &carriers);
    let mut out = String::new();
    for &carrier in &carriers {
        let by_structure = structural.contains(&kb.canonical_sort_sym(carrier));
        write_member(kb, carrier, by_structure, &mut out)?;
    }
    Ok(Some((out, carriers)))
}

/// The scalar sorts whose `eq` is structural identity: a literal compare
/// (`literal_eq`) or `===` (`symbolEq`, `typeEq`).
const STRUCTURAL_SCALARS: [&str; 6] = [
    "anthill.prelude.Int64",
    "anthill.prelude.BigInt",
    "anthill.prelude.String",
    "anthill.prelude.Bool",
    "anthill.prelude.Type",
    "anthill.reflect.Symbol",
];

/// Is `sort` one of [`STRUCTURAL_SCALARS`], whose `eq` is identity of the two values?
pub(crate) fn is_identity_scalar(kb: &KnowledgeBase, sort: Symbol) -> bool {
    let cs = kb.canonical_sort_sym(sort);
    STRUCTURAL_SCALARS
        .iter()
        .any(|n| kb.try_resolve_symbol(n).is_some_and(|s| kb.canonical_sort_sym(s) == cs))
}

/// The carriers, canonical, whose every field compares by structure: a field of a
/// [`STRUCTURAL_SCALARS`] sort, or of a non-parametric carrier of this set. A greatest
/// fixpoint, so a recursive composite of such fields is in it. A parametric carrier is
/// never in it — a field typed by its parameter compares through the parameter's `eq`.
fn structural_carriers(kb: &KnowledgeBase, carriers: &[Symbol]) -> HashSet<Symbol> {
    let scalars: HashSet<Symbol> = STRUCTURAL_SCALARS
        .into_iter()
        .filter_map(|n| kb.try_resolve_symbol(n))
        .map(|s| kb.canonical_sort_sym(s))
        .collect();
    let mut set: HashSet<Symbol> = carriers
        .iter()
        .filter(|&&s| kb.type_param_syms_of(s).is_empty())
        .map(|&s| kb.canonical_sort_sym(s))
        .collect();
    loop {
        let mut changed = false;
        for &carrier in carriers {
            let cs = kb.canonical_sort_sym(carrier);
            if !set.contains(&cs) {
                continue;
            }
            let structural_field = |ty: &Value| {
                super::typing::sort_functor_of_view(kb, ty).is_some_and(|head| {
                    let h = kb.canonical_sort_sym(head);
                    kb.type_param_syms_of(head).is_empty()
                        && (scalars.contains(&h) || set.contains(&h))
                })
            };
            let every_field_structural =
                kb.field_constructors_of_sort(carrier).into_iter().all(|ctor| {
                    kb.entity_field_types(ctor)
                        .is_none_or(|fields| fields.iter().all(|(_, ty)| structural_field(ty)))
                });
            if !every_field_structural {
                set.remove(&cs);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    set
}

/// A name `base`, or `base` with `_` appended until it is, that nothing visible from
/// `scope` is called — so a binder of a member's pattern is a binder, never a
/// constructor pattern of a constructor in scope that happens to have its name.
fn unused_name(kb: &KnowledgeBase, scope: crate::intern::ScopeId, base: &str) -> String {
    let mut name = base.to_string();
    while !matches!(
        kb.symbols.resolve_in_scope(&name, scope),
        crate::intern::ResolveResult::NotFound
    ) {
        name.push('_');
    }
    name
}

/// One carrier's secondary entry with its member; see [`derived_eq_member_source`].
fn write_member(
    kb: &KnowledgeBase,
    carrier: Symbol,
    by_structure: bool,
    out: &mut String,
) -> Result<(), String> {
    use std::fmt::Write;
    const EQ: &str = "..anthill.prelude.PartialEq.eq";
    let qn = kb.qualified_name_of(carrier);
    let scope = kb.symbols.scope_id(carrier);
    let left = unused_name(kb, scope, "left");
    let right = unused_name(kb, scope, "right");
    // One entry per segment, each opening its child from its parent: an internal sort
    // is visible from the namespace that declares it, not from the top level.
    let segments: Vec<&str> = qn.split('.').collect();
    for (depth, segment) in segments.iter().enumerate() {
        let _ = writeln!(out, "{}namespace {segment}", "  ".repeat(depth));
    }
    let indent = "  ".repeat(segments.len());
    let _ = writeln!(
        out,
        "{indent}operation eq({left}: Self, {right}: Self) -> ..anthill.prelude.Bool ="
    );
    let close = |out: &mut String| {
        for depth in (0..segments.len()).rev() {
            let _ = writeln!(out, "{}end", "  ".repeat(depth));
        }
    };
    if by_structure {
        let _ = writeln!(out, "{indent}  {left} === {right}");
        close(out);
        return Ok(());
    }
    let mut ctors = kb.field_constructors_of_sort(carrier);
    ctors.sort_by_key(|c| c.index());
    ctors.dedup();
    if ctors.is_empty() {
        return Err(format!("the composite `{qn}` has no constructor to compare"));
    }
    let _ = writeln!(out, "{indent}  match ({left}, {right})");
    for &ctor in &ctors {
        // A case names a constructor of the scrutinee's own sort by its short name, which
        // is looked up among that sort's entities whatever the scope.
        let name = kb.local_name_of(ctor).to_string();
        let arity = kb.entity_field_types(ctor).map_or(0, |f| f.len());
        let binders = |side: &str| -> Vec<String> {
            (1..=arity)
                .map(|i| unused_name(kb, scope, &format!("{side}{i}")))
                .collect()
        };
        let (ls, rs) = (binders("l"), binders("r"));
        // Each field's equality, the next field's only where it holds.
        let compare = match arity {
            0 => "true".to_string(),
            _ => {
                let mut acc = format!("{EQ}({}, {})", ls[arity - 1], rs[arity - 1]);
                for i in (0..arity - 1).rev() {
                    acc = format!("(if {EQ}({}, {}) then {acc} else false)", ls[i], rs[i]);
                }
                acc
            }
        };
        let _ = writeln!(
            out,
            "{indent}    case ({name}({}), {name}({})) -> {compare}",
            ls.join(", "),
            rs.join(", ")
        );
    }
    if ctors.len() > 1 {
        let _ = writeln!(out, "{indent}    case _ -> false");
    }
    close(out);
    Ok(())
}

/// The carrier's own parameter among `params` that the type `ty` is: the parameter's canonical
/// variable (`KnowledgeBase::canonical_type_param_var`), in a type the extractor produced a
/// `TypeVar` naming it, and in a written condition (`:- PartialEq[T]`) the parameter by its name.
fn own_param_of(kb: &KnowledgeBase, ty: &Value, params: &[Symbol]) -> Option<Symbol> {
    if let ViewHead::Var(v) = ty.head(kb) {
        return params.iter().copied().find(|&p| {
            kb.canonical_type_param_var(p)
                .is_some_and(|t| matches!(kb.get_term(t), Term::Var(w) if *w == v))
        });
    }
    if let Some(name) = super::typing::type_var_name_of_view(kb, ty) {
        let name = kb.local_name_of(name).to_string();
        return params.iter().copied().find(|&p| kb.local_name_of(p) == name);
    }
    let head = super::typing::sort_functor_of_view(kb, ty)?;
    (params.contains(&head) && ty.named_keys(kb).is_empty()).then_some(head)
}

/// WI-20260918-CKD4J — what a field of type `ty` needs for its `spec` equality, as
/// conditions over the carrier's own `params`: `Some(vec![])` for a field whose equality
/// holds outright, `None` for one nothing decides. `derived` is the fixpoint's current
/// verdict for the candidates (canonical carrier → its conditions).
fn field_conditions(
    kb: &KnowledgeBase,
    ty: &crate::eval::value::Value,
    spec: Symbol,
    params: &[Symbol],
    derived: &std::collections::HashMap<Symbol, Vec<Condition>>,
    unbacked_eq: &HashSet<Symbol>,
    equality_family: &EqualityProvisions,
) -> Option<Vec<Condition>> {
    // A field typed by a tuple: its conditions are its components', from which the tuple's
    // instance is built (proposal 004's extension), and the unit's holds outright.
    if let Some(components) = super::typing::schema_fields(kb, ty) {
        let mut out: Vec<Condition> = Vec::new();
        for (_, component) in components {
            for x in field_conditions(kb, &component, spec, params, derived, unbacked_eq, equality_family)? {
                if !out.contains(&x) {
                    out.push(x);
                }
            }
        }
        return Some(out);
    }
    // A field typed by one of the carrier's own parameters (`value: T`).
    if matches!(ty.head(kb), ViewHead::Var(_)) || super::typing::type_var_name_of_view(kb, ty).is_some() {
        return own_param_of(kb, ty, params).map(|p| vec![(spec, p)]);
    }
    let head = super::typing::sort_functor_of_view(kb, ty)?;
    if params.contains(&head) {
        // A higher-kinded parameter applied (`xs: F[T = A]`): a condition over `F` says
        // nothing of `F[T = A]`'s equality, which the member compares the field at.
        if !ty.named_keys(kb).is_empty() {
            return None;
        }
        return Some(vec![(spec, head)]);
    }
    if super::typing::is_sort_param_symbol(kb, head) {
        // Some OTHER sort's parameter: nothing here decides it.
        return None;
    }
    if unbacked_eq.contains(&kb.canonical_sort_sym(head)) {
        return None;
    }
    let h_params: Vec<Symbol> = kb.type_param_syms_of(head).to_vec();
    // A parameter the field type leaves unwritten is an open slot (kernel-language §5.2,
    // a bare sort is a fresh instance), opened per value: two values' fields are of two
    // instances, and nothing decides an equality between them — `tail: List` inside `List`
    // as much as `s: Strm[T = Int64]` beside an unwritten `E`.
    let written: Vec<String> = ty
        .named_keys(kb)
        .into_iter()
        .map(|k| kb.local_name_of(k).to_string())
        .collect();
    if h_params.iter().any(|q| !written.iter().any(|w| w == kb.local_name_of(*q))) {
        return None;
    }
    // What `head`'s `spec` equality needs, over ITS parameters, each `(spec, parameter, may
    // rest on a parameter)`: a candidate's current verdict, else a written/derived provision
    // (unconditional, or ONE conditional clause — alternatives are not translated), else a
    // witness's ([`EqualityProvisions::witnessed`]), else nothing.
    let mut needs_of_head: Vec<(Symbol, Symbol, bool)> = if let Some(dc) =
        derived.get(&kb.canonical_sort_sym(head))
    {
        dc.iter().map(|&(cspec, q)| (cspec, q, true)).collect()
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
                        super::typing::sort_functor_of_view(kb, t).filter(|q| h_params.contains(q))
                    })?;
                    out.push((base, q, true));
                }
                out
            }
            _ => return None,
        }
    } else {
        match equality_family.witnessed(kb, head, spec) {
            Witnessed::At(needs) => needs,
            Witnessed::None | Witnessed::Undecided => return None,
        }
    };
    // `head`'s own `requires` hold at the field's arguments too: a dispatch to its `eq`
    // there builds its sort's dictionary (`Set[T = X]` asks `Eq[X]`). One of the equality
    // family over a parameter is a condition; any other must hold outright.
    let equality = equality_bases(kb);
    for entry in super::typing::direct_requires(kb, head) {
        let (base, bindings) = super::typing::unwrap_spec_view_value(kb, &entry.spec)?;
        let Some(q) = bindings.iter().find_map(|(_, t)| {
            super::typing::sort_functor_of_view(kb, t).filter(|q| h_params.contains(q))
        }) else {
            // Over none of `head`'s parameters: nothing the field's arguments change.
            continue;
        };
        needs_of_head.push((base, q, equality.contains(&kb.canonical_sort_sym(base))));
    }
    // Translate each through the field type's argument for its parameter.
    let mut out: Vec<Condition> = Vec::new();
    for (cspec, q, may_rest_on_a_parameter) in needs_of_head {
        let q_name = kb.local_name_of(q).to_string();
        let arg = ty
            .named_keys(kb)
            .into_iter()
            .find(|k| kb.local_name_of(*k) == q_name)
            .and_then(|k| ty.named_arg(kb, k))
            .map(|it| it.to_value())?;
        // A tuple as a type argument is read as a field typed by it is: its components'
        // conditions, the tuple's instance built from theirs (proposal 004's extension).
        let needs = field_conditions(kb, &arg, cspec, params, derived, unbacked_eq, equality_family)?;
        if !may_rest_on_a_parameter && !needs.is_empty() {
            return None;
        }
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
/// clause itself recorded for `provides_clause_count`. An unconditional row files its clause,
/// with no conditions, and no condition facts — as a written unconditional provision does.
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
                ClauseLabel::Content(carrier),
            );
        }
    }
    kb.record_provides_clause(carrier, spec, Value::term(provided), lowered, None);
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
/// [`derive_conditional_eq`] for why the `Eq` half of the same classification is asserted
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
         a composite silently loses its derived `NonEq`"
    );

    // (Leaf `NonEq` providers like `Float` are in `partial` but not in `sorts`, so they do
    // not re-derive.)
    let derive: Vec<Symbol> = c
        .sorts
        .iter()
        .copied()
        .filter(|&s| c.partial.contains(&kb.canonical_sort_sym(s)))
        .collect();
    // WI-1103 — MARK every row asserted here. The exemption from provider-coverage
    // op-backing is this pass's placement made a property of the ROW, so it holds in
    // the phase that derives the row AND in every later phase, which walks the row
    // before this pass re-runs.
    //
    // A `Partial` composite derives `NonEq` where it has the `PartialEq` `NonEq` requires —
    // derived before the typer ([`derive_conditional_eq`]), where every field's equality is
    // decided. One with a field nothing decides derives neither.
    for s in derive {
        let (Some(ne), Some(pe)) = (noneq_sym, partialeq_sym) else {
            continue;
        };
        if super::typing::sort_provides(kb, s, pe) && !super::typing::sort_provides(kb, s, ne) {
            let rid = assert_provides(kb, s, ne);
            kb.mark_unbacked_derived_provision(rid);
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

/// WI-20261006-SZKV7 — what decides ONE composite's equality, as a value two loads can
/// be compared by: who supplies its `eq`, and which provisions of the equality family
/// name it. See [`later_equality_refusals`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct EqualitySignature {
    /// The operations supplying its `eq`, through any of the three routes — the
    /// eq-dispatch candidates, by canonical symbol. WHO supplies it, not what the
    /// supplier computes: an operation declared again with another body is the same
    /// supplier, and a layer overriding a base operation is not this check's business.
    suppliers: HashSet<Symbol>,
    /// The provisions of `PartialEq` / `Eq` / `NonEq` that are about it.
    provisions: HashSet<EqualityProvision>,
}

/// One provision in an [`EqualitySignature`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct EqualityProvision {
    /// The provision row's head, read through the carrier-neutral view
    /// ([`super::term_view::goal_fingerprint`]). Its identity: a source presented again is
    /// the same provision, a provision of another instantiation (`List[T = String]` beside
    /// `List[T = Int64]`) is another.
    ///
    /// NOT THE ROW. A fact head that is a term and one that is an occurrence are deduped in
    /// two spaces (`KnowledgeBase::value_fact_dedup`, WI-815), so `provides PartialEq[T =
    /// P]` written through an alias in a later load is a second row of the provision an
    /// earlier load derived as a term, and keyed by row it read as new (WI-20261128-X3HW2).
    head: super::term_view::GoalKey,
    provider: Symbol,
    spec: Symbol,
    /// Whether `provider`'s provision of `spec` is conditional, and how many written
    /// clauses made it. Both are the PROVIDER's for the spec — conditions are filed per
    /// provider and spec, not per row — so a clause added for another carrier shows here
    /// too: that is how the provision is read from then on, for this carrier as well.
    conditional: bool,
    clauses: u32,
}

/// The equality-family specs, in the order a diagnostic lists them.
const EQUALITY_SPECS: [&str; 3] = ["PartialEq", "Eq", "NonEq"];

/// The provisions of the equality family, each spec's filed by CARRIER
/// ([`super::typing::ProvisionsOfSpec`], WI-20261121-JE2MT), in [`EQUALITY_SPECS`] order:
/// `sort W { provides Eq[T = C] }` is at `Eq[T = C]`, the carrier `C`'s own `Eq` would be at.
/// Read at the carrier and not at the parameter an operation receives on: `Eq` declares no
/// operation, so that reading filed the witness under `W`, `C` derived its own equality beside
/// the witness's, and `W.eq` was never called (MEASURED, c3371cd0, WI-20261121-TV0PA). The
/// derivation ([`EqualityProvisions::speak_for`]), the equality-closure record
/// ([`equality_signatures`]) and the load check ([`equality_reaching_no_eq`]) read it alike,
/// so they agree on which provisions are about a sort.
struct EqualityProvisions(Vec<(Symbol, super::typing::ProvisionsOfSpec)>);

impl EqualityProvisions {
    fn of(kb: &KnowledgeBase) -> Self {
        EqualityProvisions(
            EQUALITY_SPECS
                .into_iter()
                .filter_map(|n| kb.try_resolve_symbol(&format!("anthill.prelude.{n}")))
                .map(|spec| (spec, super::typing::ProvisionsOfSpec::of(kb, spec)))
                .collect(),
        )
    }

    /// Has a provision of the family spoken for `sort`'s equality — is one at its carrier? The
    /// derivation leaves such a sort alone.
    fn speak_for(&self, kb: &KnowledgeBase, sort: Symbol) -> bool {
        self.0.iter().any(|(_, provisions)| provisions.any_at_sort(kb, sort))
    }

    /// WI-20261121-DBR8V — what the provisions of ANOTHER provider at `sort`'s carrier (a
    /// witness's) say of `sort`'s `spec` equality, for a composite with a field of that sort:
    /// what the field's equality needs, over `sort`'s own parameters, as [`field_conditions`]
    /// reads a sort's own provision. A carrier's own provisions are `sort_provides`' to read,
    /// and the derivation reads them there; a witness's row is filed under the witness, so a
    /// field of a sort whose equality a witness gives was a field nothing decides: `sort D {
    /// entity d(c: C) }` beside `sort W { provides Eq[T = C]; operation eq(…) }` derived `D` no
    /// equality, and `eq(d(…), d(…))` was refused at the call, "`D` provides no `PartialEq`"
    /// (MEASURED, 31b367def). A witness that writes `Eq` alone has its `PartialEq` row by now:
    /// the forwarding writes it before the derivation (`load::load_phase_inner`).
    ///
    /// A witness at a parametric sort is read through its binding: `W2 provides Eq[T = Box[T =
    /// A]] :- Eq[T = A]` puts `Box`'s `T` at `W2`'s `A`, so a field `Box[T = X]` needs `Eq[X]`,
    /// and what `W2` requires of `A` it requires of `X`. Read only where that is all the
    /// provision says ([`witness_needs`]); any other shape leaves the field undecided.
    fn witnessed(&self, kb: &KnowledgeBase, sort: Symbol, spec: Symbol) -> Witnessed {
        let spec_canon = kb.canonical_sort_sym(spec);
        let Some((_, provisions)) = self.0.iter().find(|(s, _)| kb.canonical_sort_sym(*s) == spec_canon)
        else {
            return Witnessed::None;
        };
        let sort_canon = kb.canonical_sort_sym(sort);
        let mut verdict = Witnessed::None;
        for p in provisions.at_sort(kb, sort) {
            if kb.canonical_sort_sym(p.provider) == sort_canon {
                continue;
            }
            match witness_needs(kb, provisions, p, sort, spec) {
                Some(needs) => return Witnessed::At(needs),
                None => verdict = Witnessed::Undecided,
            }
        }
        verdict
    }
}

/// What [`EqualityProvisions::witnessed`] reads of a field's sort.
enum Witnessed {
    /// No provision of another provider is at the sort's carrier.
    None,
    /// One is, and the field's equality needs these, each `(spec, parameter of the sort, may
    /// rest on a parameter)`: none, for a provision that holds outright.
    At(Vec<(Symbol, Symbol, bool)>),
    /// One is, and does not say what the field's equality needs.
    Undecided,
}

/// The equality family a requirement may rest on a parameter at, canonical: `PartialEq` and
/// `Eq` ([`field_conditions`]).
fn equality_bases(kb: &KnowledgeBase) -> Vec<Symbol> {
    ["PartialEq", "Eq"]
        .into_iter()
        .filter_map(|n| kb.try_resolve_symbol(&format!("anthill.prelude.{n}")))
        .map(|s| kb.canonical_sort_sym(s))
        .collect()
}

/// WI-20261121-DBR8V — what the witness provision `p` of `spec`, at `head`'s carrier, needs of
/// `head`'s own parameters for a field of `head`'s type: its condition and the witness's own
/// `requires`, each read through the binding `head[Q = A, …]`, which puts each parameter `Q`
/// of `head` at a distinct parameter `A` of the witness. `None` for a provision that says more:
/// a binding at anything but `head` applied to the witness's parameters (`Box[T = Int64]`, which
/// the field's arguments would have to match, not condition), a condition or a requirement over
/// a parameter that binding does not name, and conditions that cannot be told apart — filed per
/// provider and spec, a witness's condition is read only where it writes this one provision of
/// the spec, in one clause, as a sort's own is.
fn witness_needs(
    kb: &KnowledgeBase,
    provisions: &super::typing::ProvisionsOfSpec,
    p: &super::typing::ProvisionAt,
    head: Symbol,
    spec: Symbol,
) -> Option<Vec<(Symbol, Symbol, bool)>> {
    let h_params: Vec<Symbol> = kb.type_param_syms_of(head).to_vec();
    let w_params: Vec<Symbol> = kb.type_param_syms_of(p.provider).to_vec();
    let binding = provisions.carrier_binding(kb, p)?;
    // Each of `head`'s parameters at a distinct parameter of the witness: (witness's, head's).
    let keys = binding.named_keys(kb);
    if keys.len() != h_params.len() {
        return None;
    }
    let mut at: Vec<(Symbol, Symbol)> = Vec::with_capacity(h_params.len());
    for &q in &h_params {
        let key = keys.iter().copied().find(|&k| kb.local_name_of(k) == kb.local_name_of(q))?;
        let a = own_param_of(kb, &binding.named_arg(kb, key)?.to_value(), &w_params)?;
        if at.iter().any(|&(b, _)| b == a) {
            return None;
        }
        at.push((a, q));
    }
    // The parameter of `head` a spec application over a parameter of the witness is at.
    let head_param = |v: &Value| -> Option<(Symbol, Symbol)> {
        let (base, bindings) = super::typing::unwrap_spec_view_value(kb, v)?;
        let a = bindings.iter().find_map(|(_, t)| own_param_of(kb, t, &w_params))?;
        at.iter().find(|&&(b, _)| b == a).map(|&(_, q)| (base, q))
    };
    let mut needs: Vec<(Symbol, Symbol, bool)> = Vec::new();
    if super::typing::provision_is_conditional(kb, p.provider, spec) {
        if provisions.rows_by(kb, p.provider) != 1 {
            return None;
        }
        let spec_canon = kb.canonical_sort_sym(spec);
        let clauses: Vec<Vec<Value>> = super::typing::provision_conditions(kb, p.provider)
            .into_iter()
            .filter(|g| kb.canonical_sort_sym(g.provided) == spec_canon)
            .map(|g| g.conditions)
            .collect();
        let [one] = clauses.as_slice() else {
            return None;
        };
        for cv in one {
            let (base, q) = head_param(cv)?;
            needs.push((base, q, true));
        }
    }
    // A dispatch to the witness's `eq` builds the witness's dictionary, so what it requires of
    // a parameter it requires at the field's argument there. One over none of its parameters
    // holds or not whatever the field's arguments are, and is the witness's own load's to check.
    let equality = equality_bases(kb);
    for entry in super::typing::direct_requires(kb, p.provider) {
        let (_, bindings) = super::typing::unwrap_spec_view_value(kb, &entry.spec)?;
        if !bindings.iter().any(|(_, t)| own_param_of(kb, t, &w_params).is_some()) {
            continue;
        }
        let (base, q) = head_param(&entry.spec)?;
        needs.push((base, q, equality.contains(&kb.canonical_sort_sym(base))));
    }
    Some(needs)
}

/// The [`EqualitySignature`] of every composite the KB holds now, by canonical sort.
fn equality_signatures(
    kb: &mut KnowledgeBase,
) -> std::collections::HashMap<Symbol, EqualitySignature> {
    let composites: Vec<Symbol> = composite_sorts(kb)
        .into_iter()
        .map(|s| kb.canonical_sort_sym(s))
        .collect();
    let mut out: std::collections::HashMap<Symbol, EqualitySignature> = composites
        .iter()
        .map(|&s| (s, EqualitySignature::default()))
        .collect();
    // (provider, spec) → (conditional?, clause count), asked once per pair rather than
    // once per row: the two are the provider's for the spec, whichever row asks.
    let mut read: std::collections::HashMap<(Symbol, Symbol), (bool, u32)> =
        std::collections::HashMap::new();
    // Read per composite: a provision at a primitive, an abstract sort or a spec's own
    // parameter is out of this check's domain — see [`later_equality_refusals`].
    let equality_family = EqualityProvisions::of(kb);
    for (spec, provisions) in &equality_family.0 {
        let spec = *spec;
        let spec_canon = kb.canonical_sort_sym(spec);
        for &composite in &composites {
            let Some(signature) = out.get_mut(&composite) else {
                continue;
            };
            for provision in provisions.at_sort(kb, composite) {
            let provider = kb.canonical_sort_sym(provision.provider);
            let (conditional, clauses) = *read.entry((provider, spec_canon)).or_insert_with(|| {
                (
                    kb.provision_has_conditions(provision.provider, spec),
                    kb.provides_clause_count(provision.provider, spec),
                )
            });
            // A stored row's head holds no `Opaque` token (the index refuses one), so its
            // fingerprint is faithful: two heads share it only if they are one provision.
            let head = super::term_view::goal_fingerprint(
                kb,
                kb.rule_head_value(provision.row),
                &super::subst::Substitution::new(),
            );
            assert!(head.is_opaque_free(), "a stored provision row's head keys faithfully");
            signature.provisions.insert(EqualityProvision {
                head,
                provider,
                spec: spec_canon,
                conditional,
                clauses,
            });
            }
        }
    }
    // No `PartialEq.eq` ⇒ no `eq` spec op, and nothing can supply an impl of it. A derived
    // member is the derivation's, recorded with the provisions it rides: a supplier is an
    // `eq` a program wrote, and one declared over a derived member is one
    // (`load::Loader::load_operation` takes the member out of the derived set).
    if let Some(eq_index) = super::load::EqDispatchIndex::build(kb) {
        for &carrier in &composites {
            let suppliers: Vec<Symbol> = eq_index
                .candidates(kb, carrier)
                .iter()
                .map(|c| kb.canonical_sym(c.target))
                .filter(|&t| !kb.is_derived_member(t))
                .collect();
            if let Some(signature) = out.get_mut(&carrier) {
                signature.suppliers.extend(suppliers);
            }
        }
    }
    out
}

/// Record the equality signatures of the KB as it stands — at EVERY exit of
/// `load::load_phase_inner`, and by nothing else.
///
/// `held` are the composites this load's [`later_equality_refusals`] refused. They KEEP
/// the entry they had, so the knowledge base a refused load leaves behind — a plain load
/// does not unwind — is refused again, by any later load, until it is repaired or
/// discarded. Every OTHER composite is recorded as it now is, whether the load succeeded
/// or failed for some unrelated reason, and both halves of that matter:
///
///   * a sort the failed load DEFINED must be in the record, or the next load could
///     change its equality with nothing to be held to;
///   * a row the failed load's passes DERIVED for an earlier composite (a field's
///     abstract sort was just given an equality) must be in it too, or the corrected
///     retry would be refused over a row no source wrote.
pub(crate) fn record_equality_signatures(kb: &mut KnowledgeBase, held: &[Symbol]) {
    let mut signatures = equality_signatures(kb);
    for carrier in held {
        // `held` is drawn from the record's own keys, so there is an entry to keep.
        if let Some(was) = kb.recorded_equality_signatures().get(carrier).cloned() {
            signatures.insert(*carrier, was);
        }
    }
    kb.set_equality_signatures(signatures);
}

/// WI-20261006-SZKV7 — A COMPOSITE'S EQUALITY IS CLOSED BY THE LOAD THAT DEFINES IT.
///
/// What decides a composite's equality is who supplies its `eq` and which provisions of
/// `PartialEq`, `Eq` and `NonEq` name it, and this module reads both through NEGATIONS:
/// a composite is classified only if it is NOT a lawful-`Eq` boundary (nothing supplies
/// its `eq`), and derived for only if nothing already SPEAKS for it (`spoken_for`, in the
/// two total derivations). Within one load that is sound — both sets are complete before
/// [`classify`] reads them. ACROSS loads it is not: they keep growing after the rows were
/// written down, and nothing takes a row back. A later load that adds to an earlier
/// sort's equality leaves in place
///
///   * that sort's derived rows, beside whatever the later load wrote;
///   * the derived rows of every composite HOLDING the sort, partiality being propagated
///     through fields;
///   * every call the earlier load's typer resolved against them — while the eq-dispatch
///     index, rebuilt per load, now answers `=` over the sort's values by the late `eq`;
///   * and, for a sort that reaches a `Float`, its own derived `NonEq`, which the next
///     classification reads back as a hand-written leaf ([`noneq_provider_sorts`]'s doc
///     names the hazard).
///
/// MEASURED before this refusal, `reading(v: Float)` loaded and then a witness sort
/// `provides Eq[T = Reading]` with `eq … = true`: the KB provides BOTH `NonEq` and `Eq`
/// for the one type, and `eq(reading(1.5), reading(2.5))` is `false` where one load of
/// the two sources answers `true`.
///
/// REFUSED, not repaired. Taking the rows back would oblige re-deriving every dependent
/// and re-resolving every call that read them, and would make an earlier load's facts
/// something a later load can change. A non-monotone update is refused; the same two
/// sources in ONE load are accepted, the derivation seeing everything at once.
///
/// BY COMPARING STATES, not by reading what the load did. Each composite's
/// [`EqualitySignature`] is recorded when a load ends, and here — after this load's
/// sources are in and before it derives anything — recomputed by the same function for
/// every composite in the record. A signature that differs is the refusal, whatever
/// route changed it: a witness sort's provision or a binding in a later entry, with an
/// `eq` or without; an `eq` member added to the sort, or to a witness an earlier load
/// declared; a condition attached to a provision; the sort declared again with more in
/// it. Earlier cuts read the load's additions instead — the sorts it derived for, the
/// rows in its rule slots, the operations it declared — and each notion leaks
/// (/code-review): an assert that repeats an earlier row lands on the earlier slot, and
/// a source presented again is declared again without adding anything.
///
/// WHAT IT DOES NOT SEE, stated rather than left to be found:
///
///   * COMPOSITES only — the sorts this module classifies. An `eq` for an abstract sort
///     is what a host's bindings do for the primitives, in whichever load they arrive;
///     it can still move the equality of a composite that HOLDS such a sort.
///   * what this load's own LATER passes add to an earlier composite — a provision
///     forwarded onto it through a spec other than these three, an `Eq` derived for it
///     because a field's sort has just been given one. Those are in the record by the
///     next load.
///   * what a supplier COMPUTES, and the composite's own shape: an `eq` operation
///     declared again with another body, a sort declared again with another
///     constructor. Declaring again across loads is how a layer overrides its base, and
///     whether that may reach an equality is a question about redeclaration, not this.
///
/// Returns the refusals with the carriers they are about, which the caller hands to
/// [`record_equality_signatures`] so that those stay held. Called once this load's
/// sources are in and the eq-dispatch index is built, before [`classify`]; above the
/// `run_typer` fork, so a partial load refuses the same thing.
pub(crate) fn later_equality_refusals(
    kb: &mut KnowledgeBase,
) -> (Vec<super::load::LoadError>, Vec<Symbol>) {
    if kb.recorded_equality_signatures().is_empty() {
        // Nothing has loaded into this KB before, or nothing with a composite in it:
        // there is no earlier sort to hold this load to. (A load that FAILED recorded
        // too, so this is not the state it leaves.)
        return (Vec::new(), Vec::new());
    }
    // Through the provider index: the signature asks each provision for its provider's
    // conditions, and unindexed that was a scan of the whole conditions relation per
    // provider — MEASURED on a later load at opt-level 0: 47 ms without the index, 6 ms
    // with it. The index was built here for this one read and dropped again, the
    // derivations below having to run without it; since WI-20261010-ANK4X it stands, and
    // takes the rows they assert.
    let now = equality_signatures(kb);
    let mut changed: Vec<(Symbol, Vec<String>)> = kb
        .recorded_equality_signatures()
        .iter()
        .filter_map(|(&carrier, was)| match now.get(&carrier) {
            Some(is) if is == was => None,
            Some(is) => Some((carrier, describe_equality_change(kb, carrier, was, is))),
            // Nothing un-declares a constructor, and a layer's discard restores the
            // record with the declarations — so this is not a state a load can reach,
            // and if one does it is refused rather than passed over.
            None => Some((carrier, vec!["it is no longer a composite sort".to_string()])),
        })
        .collect();
    changed.sort_by(|(a, _), (b, _)| kb.qualified_name_of(*a).cmp(kb.qualified_name_of(*b)));
    let held: Vec<Symbol> = changed.iter().map(|(carrier, _)| *carrier).collect();
    let refusals = changed
        .into_iter()
        .map(|(carrier, changes)| super::load::LoadError::EqualityOfEarlierSort {
            carrier: kb.qualified_name_of(carrier).to_string(),
            changes,
        })
        .collect();
    (refusals, held)
}

/// How `is` differs from `was`, each difference in the terms it was written in. Sorted,
/// so a refusal reads the same on every load.
fn describe_equality_change(
    kb: &KnowledgeBase,
    carrier: Symbol,
    was: &EqualitySignature,
    is: &EqualitySignature,
) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for &s in is.suppliers.difference(&was.suppliers) {
        out.push(format!("`{}` now supplies its `eq`", kb.qualified_name_of(s)));
    }
    for &s in was.suppliers.difference(&is.suppliers) {
        out.push(format!("`{}` no longer supplies its `eq`", kb.qualified_name_of(s)));
    }
    let by = |provider: Symbol| {
        if provider == carrier {
            "its own".to_string()
        } else {
            format!("`{}`'s", kb.qualified_name_of(provider))
        }
    };
    let same_head = |sig: &EqualitySignature, head: &super::term_view::GoalKey| {
        sig.provisions.iter().any(|p| &p.head == head)
    };
    for p in is.provisions.difference(&was.provisions) {
        let spec_name = kb.local_name_of(p.spec);
        out.push(if same_head(was, &p.head) {
            format!("{} provision of `{spec_name}` for it has changed", by(p.provider))
        } else {
            format!("{} provision of `{spec_name}` for it is new", by(p.provider))
        });
    }
    for p in was.provisions.difference(&is.provisions) {
        if !same_head(is, &p.head) {
            let spec_name = kb.local_name_of(p.spec);
            out.push(format!("{} provision of `{spec_name}` for it is gone", by(p.provider)));
        }
    }
    out.sort();
    out.dedup();
    out
}

/// WI-20260919-HXGXF — assert `carrier provides spec` with `conds` as its ONE clause's
/// conditions, and hand back nothing: the shared spelling of what this module has always
/// done inline, so `type_value_derive` files its rows exactly as the equality derivations
/// file theirs (same provision fact, same `ProvidesConditionInfo` rows, same clause
/// numbering) rather than growing a second, subtly different writer.
///
/// An EMPTY `conds` is an unconditional row, which is the concrete-sort case and not a
/// degenerate one — `record_derived_conditions` files the clause and no condition facts.
pub(crate) fn assert_derived_provision(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    spec: Symbol,
    conds: &[Condition],
) {
    assert_provides(kb, carrier, spec);
    record_derived_conditions(kb, carrier, spec, conds);
}

/// WI-20260919-9KYPA — the CONDITIONAL `NonEq` mirror of [`derive_conditional_eq`]:
/// `provides NonEq[List] :- NonEq[T]`, so `List[T = Float]` is a WITNESSED `NonEq`
/// carrier. It was what refused `Set[T = List[T = Float]]` where the type is written,
/// while that check asked `NonEq`; it asks `Eq` now (`check_use_site_requires_eq`) and
/// reads [`derive_conditional_eq`]'s row.
///
/// ONE CLAUSE PER PARAMETER, where the `Eq` half emits one clause holding every
/// parameter. That asymmetry is the logic, not a shortcut: a parametric application is
/// lawfully `Eq` iff EVERY argument is (a conjunction, one clause), and is `NonEq` if ANY
/// argument is (a disjunction — and `provision_conditions` reads conditions as a
/// conjunction WITHIN a clause and a disjunction ACROSS clauses, so the disjunction has
/// to be spelled as separate clauses). `Pair[A = Float, B = Int64]` needs the `A` clause
/// alone to answer.
///
/// Mirrors only what THIS module derived ([`KnowledgeBase::conditional_eq_conditions`], whose
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
    let carriers: Vec<(Symbol, Vec<Symbol>, Vec<Condition>)> = composite_sorts(kb)
        .into_iter()
        .filter_map(|s| {
            let cs = kb.canonical_sort_sym(s);
            let mut disjuncts: Vec<Symbol> = Vec::new();
            for &(_, p) in kb.conditional_eq_conditions.get(&(cs, eq))? {
                if !disjuncts.contains(&p) {
                    disjuncts.push(p);
                }
            }
            // The `PartialEq` row's OWN parameters, not the `Eq` row's reused: see the
            // field's comment. Absent ⇒ this carrier derived no conditional `PartialEq`,
            // so a `NonEq` row could not discharge its `requires PartialEq` and is not
            // derived at all.
            let base = kb.conditional_eq_conditions.get(&(cs, partial_eq))?.clone();
            // A parameter whose `Eq` the `PartialEq` row itself needs gives no clause:
            // `NonEq[T]` beside `Eq[T]` holds nowhere (`Eq` ⊥ `NonEq`). A field compared
            // through a witness that needs `Eq` of its argument (`W2 provides Eq[T = Box[T =
            // A]] :- Eq[T = A]`, WI-20261121-DBR8V) puts `Eq[U]` there, and the holder is then
            // partial at no `U`: where `Eq[U]` fails it has no equality at all. So does a field
            // of a sort that requires `Eq` of its argument (`xs: Set[T = T]`), whose holder
            // provided such a `NonEq` before (MEASURED) and now provides none.
            let eq_canon = kb.canonical_sort_sym(eq);
            disjuncts.retain(|&p| {
                !base.iter().any(|&(c, q)| q == p && kb.canonical_sort_sym(c) == eq_canon)
            });
            if disjuncts.is_empty() {
                return None;
            }
            Some((s, disjuncts, base))
        })
        .collect();
    let mut done: HashSet<Symbol> = HashSet::new();
    for (s, params, partial_conds) in carriers {
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
            for &c in &partial_conds {
                if !conds.contains(&c) {
                    conds.push(c);
                }
            }
            record_derived_conditions(kb, s, noneq, &conds);
        }
    }
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
    let ctor_functors: Vec<Symbol> = kb.entity_field_type_functors().collect();
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
///
/// A derived member is no boundary: it is the `eq` an earlier load derived from the fields,
/// and a composite holding its carrier is classified through those fields as it was there.
fn is_eq_boundary(
    kb: &KnowledgeBase,
    eq_index: Option<&super::load::EqDispatchIndex>,
    sort: Symbol,
) -> bool {
    eq_index.is_some_and(|ix| {
        ix.candidates(kb, sort)
            .iter()
            .any(|c| !kb.is_derived_member(c.target))
    })
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
    let Some(noneq) = noneq_sym else {
        return Vec::new();
    };
    // `NonEq`'s rows through the relation's one row decoder, so a provision on any
    // carrier is a row here as it is to the typer — and out of the spec's bucket of the
    // provider index (WI-20261010-ANK4X), where this decoded the whole relation to keep
    // the handful that name `NonEq`.
    super::typing::providers_of_spec(kb, noneq)
        .into_iter()
        .filter(|&provider| !super::typing::provision_is_conditional(kb, provider, noneq))
        .collect()
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
pub(crate) fn composite_field_sorts(kb: &KnowledgeBase, sort: Symbol) -> Vec<Symbol> {
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
/// [`derive_conditional_eq`] asserts through this same function and its rows are held to
/// provider coverage.
pub(crate) fn assert_provides(kb: &mut KnowledgeBase, carrier: Symbol, spec: Symbol) -> RuleId {
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
        ClauseLabel::Content(carrier),
    )
}

/// Two operands of `=` that are both tuples ([`KnowledgeBase::tuple_component_pairs`]).
pub(crate) enum TuplePairs {
    /// Two tuples of different shape (arity, labels): not equal.
    Mismatch,
    /// Their components, pairwise, in the order a tuple's view lists them.
    Pairs(Vec<(Value, Value)>),
}

impl KnowledgeBase {
    /// The components of two tuples, pairwise — `None` unless both operands are tuples, the
    /// named ones by the first operand's labels. An equality at two tuples no type reached
    /// compares them, each by the steps it takes for any operand; a typed one is `NamedTuple`'s
    /// member, which reads them by its type's labels ([`Self::tuple_component_pairs_by_labels`]).
    pub(crate) fn tuple_component_pairs(&self, a: &Value, b: &Value) -> Option<TuplePairs> {
        let (
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
        ) = (a.head(self), b.head(self))
        else {
            return None;
        };
        if !self.is_ordered_product_functor(fa) || !self.is_ordered_product_functor(fb) {
            return None;
        }
        if pa != pb || na != nb {
            return Some(TuplePairs::Mismatch);
        }
        let mut pairs = Vec::with_capacity(pa + na);
        for i in 0..pa {
            match (a.pos_arg(self, i), b.pos_arg(self, i)) {
                (Some(x), Some(y)) => pairs.push((x.to_value(), y.to_value())),
                _ => return Some(TuplePairs::Mismatch),
            }
        }
        for key in a.named_keys(self) {
            match (a.named_arg(self, key), b.named_arg(self, key)) {
                (Some(x), Some(y)) => pairs.push((x.to_value(), y.to_value())),
                _ => return Some(TuplePairs::Mismatch),
            }
        }
        Some(TuplePairs::Pairs(pairs))
    }

    /// The order a tuple's dictionary lists its components' sub-dictionaries in, and its
    /// derived `eq` compares them in: positional components by their index, named ones by
    /// label. A value may list its labels in another order than its type does (`<:` admits a
    /// permutation, kernel-language §4.5), so both read this order rather than either's own.
    pub(crate) fn tuple_component_order(&self, label: Symbol) -> (usize, String) {
        let name = self.local_name_of(label).to_string();
        match crate::intern::positional_label_index(&name) {
            Some(index) => (index, String::new()),
            None => (usize::MAX, name),
        }
    }

    /// The components of a tuple type, in [`Self::tuple_component_order`].
    pub(crate) fn tuple_type_components(&self, fields: Vec<(Symbol, Value)>) -> Vec<(Symbol, Value)> {
        let mut fields = fields;
        fields.sort_by_cached_key(|(label, _)| self.tuple_component_order(*label));
        fields
    }

    /// The pairs of `a`'s and `b`'s components at each of `labels`, in that order — a tuple's
    /// components as its type names them, read by label as every reader of a tuple reads them
    /// (kernel-language §4.5): a value wider than the type, or listing its labels in another
    /// order, is read at the type's labels alone. `None` where either is no tuple;
    /// [`TuplePairs::Mismatch`] where one lacks a label.
    pub(crate) fn tuple_component_pairs_by_labels(&self, a: &Value, b: &Value, labels: &[Symbol]) -> Option<TuplePairs> {
        let (xs, ys) = (self.tuple_components_by_labels(a, labels)?, self.tuple_components_by_labels(b, labels)?);
        Some(match (xs, ys) {
            (Some(xs), Some(ys)) => TuplePairs::Pairs(xs.into_iter().zip(ys).collect()),
            _ => TuplePairs::Mismatch,
        })
    }

    /// `v`'s components at each of `labels`, in that order, read by label
    /// ([`Self::tuple_component_pairs_by_labels`]). `None` where `v` is no tuple; `Some(None)`
    /// where it lacks a label.
    pub(crate) fn tuple_components_by_labels(&self, v: &Value, labels: &[Symbol]) -> Option<Option<Vec<Value>>> {
        if !matches!(v.head(self), ViewHead::Functor { functor, pos_arity: 0, .. } if self.is_ordered_product_functor(functor)) {
            return None;
        }
        let keys = v.named_keys(self);
        Some(
            labels
                .iter()
                .map(|&label| {
                    let key = keys.iter().copied().find(|&k| crate::kb::typing::same_label(self, k, label))?;
                    v.named_arg(self, key).map(|c| c.to_value())
                })
                .collect(),
        )
    }
}
