//! WI-20261121-JE2MT — THE SORT CARRIER, and the provisions of a spec at a carrier
//! (`docs/design/spec-carrier-set.md`, stage 1).
//!
//! A spec's SORT CARRIER is all its type-vars (decision 4). A provision's CARRIER is what
//! `Self` denotes for the values the provision is for (decision 5, §1's table): for a spec with
//! a dictionary, the spec at the provision's bindings (`Set provides Eq[T = Self]` is at
//! `Eq[T = Set]`); for a self-representing spec, the provider at its own type-vars. "Add this
//! provision unless one is written" — what the derivations ask — is whether a provision stands
//! at a carrier that unifies with the one to be added (§1; decision 2: any overlap skips).
//!
//! Before this, the derivations read ONE parameter per spec, on two ladders that disagree for
//! a spec no operation of which receives on its parameter: `provision_carriers_of_spec`
//! through the witness criterion's (L1, the parameter an operation receives on, which `Eq` and
//! `SortDomain` have none of, so a witness was filed under the WITNESS), and `provisions_about`
//! through `spec_carrier_param_or_sole` (L2). MEASURED (b1 of the design): `sort W { provides
//! SortDomain[T = Colour] }` had `sort_domain_derive` derive `Colour` a second row beside
//! `W`'s, since L1 filed `W`'s under `W`, while the reflect relation, on L2, said `W`'s row was
//! at `Colour` — and a call at `Colour` was answered by the derived row, `W`'s domain unread.
//!
//! What reads it: the equality derivation and its records (`eq_derive`), the law at a
//! carrier's `eq` (`load::EqProviders`), and the `SortDomain` and `TypeValue` derivations.
//! Every spec they read is a spec with a dictionary of one type-var. The readers of the single
//! carrier parameter on the per-call path — dispatch, the coherence grouping, the member
//! checks, the default rows — and the self-representing class are stage 2
//! (WI-20261122-CXR5B).

use super::*;

/// The SORT CARRIER of a spec: every type-var it declares, in declaration order (decision 4,
/// for every spec, both classes). It belongs to the sort, and it is what a substituted sort of
/// the spec binds. Nothing reads "the first" of it: a provision's carrier binds all of them.
pub(crate) struct SortCarrier {
    pub(crate) type_vars: SmallVec<[Symbol; 2]>,
}

/// The [`SortCarrier`] of `spec`, read off its declaration — on the CANONICAL spec, since an
/// alias symbol of it declares no type-vars — through the memo of the sort's parameters
/// ([`sort_type_params_as_pairs`]).
pub(crate) fn sort_carrier(kb: &KnowledgeBase, spec: Symbol) -> SortCarrier {
    let canon = kb.canonical_sort_sym(spec);
    SortCarrier {
        type_vars: sort_type_params_as_pairs(kb, canon).iter().map(|(p, _)| *p).collect(),
    }
}

/// WI-20261122-CXR5B — a provision's CARRIER (decision 5, §1's table of
/// `docs/design/spec-carrier-set.md`): what `Self` denotes for the values the provision is for,
/// as a type term, and whether the provider provides the spec FOR ITSELF there (decision 6).
pub(crate) struct ProvisionCarrier {
    /// The substituted sort. For a spec with a dictionary, the SPEC at the provision's bindings
    /// of its type-vars, the operation bindings left out (`Set provides Eq[T = Self]` is at
    /// `Eq[T = Set]`; `MyBag provides Bag2[T = Int64, C = Self]` at `Bag2[T = Int64, C = MyBag]`
    /// in either declaration order). For a SELF-REPRESENTING spec — one an operation of which
    /// takes a value of type `Self`, whatever else it takes (decision 8) — the PROVIDER at its
    /// own type-vars (`List provides Stream[T = T, E = {}]` is at `List[T = T]`): the values are
    /// the provider's, and the spec's type-vars are read off it. Read as the spec there, the
    /// stdlib's six `Stream` providers would each be "the default `Stream`" at carriers that
    /// unify, and `one_default` would refuse the library (the design's g1–g4).
    pub(crate) term: TermId,
    /// Does the provider provide the spec for itself (decision 6, every binding counts): its
    /// sort is the head of the carrier (every provision of a self-representing spec), or the
    /// head of one of the carrier's bindings. Otherwise the provision is a WITNESS.
    pub(crate) own: bool,
}

/// The [`ProvisionCarrier`] of the provision `provider provides spec_view`, a `SortProvidesInfo`
/// row's `sort_ref` and `spec`, on the term carrier.
///
/// A binding LEFT OUT of a spec of ONE type-var reads as the provider, as [`ProvisionsOfSpec`]
/// reads it (`kernel-language.md` §5.2 as it stands; decision 3 lands with the refusal it
/// restates). Left out of a spec of several, it is `?` and the carrier omits it — an omitted
/// binding is any ([`carrier_views_overlap`]). A spec with no type-var is its own carrier, and
/// a provider of it is a witness (`W1 provides Greeter` is at `Greeter`).
///
/// A name the KB has and no declaration — the bootstrap `Eq`, `PartialEq` and `NonEq` of a KB
/// loaded without the standard library — has no type-var to read, and its only rows are the
/// equality derivation's self-provisions: each is at its provider and is its own, as
/// [`ProvisionsOfSpec`] reads them (its `Shape::Undeclared`, measured there).
///
/// THE ONE OWNER of where a provision is: the `provision_carrier` / `own_provision` relations'
/// builtins and 058 §3.6's default rows read it, so the reflect layer and the index the hot path
/// reads cannot disagree about a row (`wi860_default_provider_relations_test` compares them).
pub(crate) fn provision_carrier(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    provider: Symbol,
    spec_view: TermId,
) -> ProvisionCarrier {
    let spec = kb.canonical_sort_sym(spec);
    let provider = kb.canonical_sort_sym(provider);
    if kb.sort_kind(spec).is_none() {
        return ProvisionCarrier { term: kb.make_name_term_from_sym(provider), own: true };
    }
    if spec_is_self_representing(kb, spec) {
        // `Self` of the provider, each type-var bound to the parameter itself — a `Ref` to the
        // parameter, as a provision's view stores one (`List[T = T]`), and not
        // [`own_application`]'s published logic variable, which is the provider at SOME
        // parameters and would make two rows of one provider two carriers.
        let params: SmallVec<[(Symbol, TermId); 2]> = sort_carrier(kb, provider)
            .type_vars
            .iter()
            .map(|&p| (p, kb.alloc(Term::Ref(p))))
            .collect();
        let base = kb.make_sort_ref(provider);
        return ProvisionCarrier { term: kb.make_parameterized_type(base, &params), own: true };
    }
    let type_vars = sort_carrier(kb, spec).type_vars;
    let view = Value::term(spec_view);
    // Bindings live on the `SortView` wrapper alone; a bare spec reference binds nothing.
    let binds = view_is_sort_view(kb, &view);
    let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    let mut own = false;
    for &tv in &type_vars {
        let written = binds.then(|| provision_binding_value_at_param(kb, tv, &view)).flatten();
        let bound = match written {
            // A term-carried view has term-carried children.
            Some(Value::Term { id, .. }) => id,
            Some(other) => panic!(
                "provision_carrier: a term-carried spec view of `{}` yielded a non-term binding \
                 {other:?}",
                kb.qualified_name_of(spec)
            ),
            None if type_vars.len() == 1 => kb.make_name_term_from_sym(provider),
            None => continue,
        };
        own |= composed_self_reference(kb, provider, &crate::kb::term_view::TermIdView(bound));
        bindings.push((tv, bound));
    }
    let base = kb.make_sort_ref(spec);
    ProvisionCarrier { term: kb.make_parameterized_type(base, &bindings), own }
}

/// Does `carrier`, a provision's carrier ([`provision_carrier`]), name `sort` — as its head,
/// or as the head of one of its bindings? The question decision 6 asks of a provision's
/// provider, asked of any sort: what a probe of the default rows "at one sort" lists.
pub(crate) fn carrier_names_sort(kb: &KnowledgeBase, carrier: TermId, sort: Symbol) -> bool {
    let view = crate::kb::term_view::TermIdView(carrier);
    let Some((head, bindings)) = carrier_view_parts(kb, &view) else {
        return false;
    };
    same_sort_canonical(kb, head, sort)
        || bindings.iter().any(|(_, b)| composed_self_reference(kb, sort, b))
}

/// The key 058 §3.6's default rows of `spec` are PARTITIONED by in their index, for a row at
/// `carrier`: the bucket of the carrier's head for a self-representing spec (the provider), and
/// for a spec with a dictionary the bucket of its binding of the spec's FIRST type-var. `None`
/// is a row every lookup reads: that binding left out (any), or not a carrier, or a spec with
/// no type-var.
///
/// AN INDEX KEY ONLY, and the one place a type-var is singled out: two rows are at one carrier
/// where their WHOLE substituted sorts meet ([`carriers_meet`]), and such rows bind their first
/// type-var to one bucket or one of them leaves it open, so a lookup that reads its key's bucket
/// and the open rows reads every row that can answer. Declaration order moves which rows share
/// a bucket, never an answer. A binding to a type parameter is in that parameter's bucket and
/// at no sort's, and meets only that parameter ([`bindings_meet`]): a provision at every type is
/// no default at a sort.
pub(crate) fn default_row_key(kb: &KnowledgeBase, spec: Symbol, carrier: TermId) -> Option<CarrierBucket> {
    let view = crate::kb::term_view::TermIdView(carrier);
    let canon = kb.canonical_sort_sym(spec);
    if spec_is_self_representing(kb, canon) {
        return carrier_view_bucket(kb, &view);
    }
    let first = *sort_carrier(kb, canon).type_vars.first()?;
    let (_, bindings) = carrier_view_parts(kb, &view)?;
    carrier_view_bucket(kb, binding_for_param(kb, &bindings, first, BindingKeyMatch::Label)?)
}

/// The partition key ([`default_row_key`]) a GOAL of a spec with a dictionary reads, its
/// bindings of the spec's type-vars in hand: its binding of the first type-var, where that is a
/// carrier. `None` — the binding absent, or a type parameter — has the lookup read every row of
/// the spec.
pub(crate) fn goal_row_key(
    kb: &KnowledgeBase,
    spec: Symbol,
    bindings: &[(Symbol, Value)],
) -> Option<CarrierBucket> {
    let first = *sort_carrier(kb, spec).type_vars.first()?;
    let bound = binding_for_param(kb, bindings, first, BindingKeyMatch::Label)?;
    if is_type_param_view(kb, bound) {
        return None;
    }
    carrier_view_bucket(kb, bound)
}

/// Do two bindings of one type-var describe a type in common, as 058 §3.6's rows read them? Two
/// bindings that are no type parameter where [`carrier_views_overlap`] says so — a parameter
/// NESTED in one (`List[T = E]`) is any there, which is what a conditional provision's row
/// means. A type parameter AT THE TOP of a binding meets only that same parameter: a provision
/// at every type (`AnyS provides Show[T = E]`) is no default at a sort, and a goal at a caller's
/// type parameter (`Ord[T = E]` in a generic body) is answered by the caller's `requires`, not
/// by a default. It is what the rows filed by one parameter's binding did — a type parameter's
/// row in that parameter's bucket, a type-parameter goal declined — read at every type-var,
/// so that which type-var is declared first decides nothing.
pub(crate) fn bindings_meet<A: TermView, B: TermView>(kb: &KnowledgeBase, a: &A, b: &B) -> bool {
    match (is_type_param_view(kb, a), is_type_param_view(kb, b)) {
        (false, false) => carrier_views_overlap(kb, a, b),
        (true, true) => view_ref_symbol(kb, a).is_some_and(|x| view_ref_symbol(kb, b) == Some(x)),
        _ => false,
    }
}

/// Are two default rows' carriers ([`provision_carrier`]) at one carrier: one head, and every
/// type-var both bind meeting ([`bindings_meet`]), a binding either leaves out being any. The
/// question `one_default` asks of two rows of one spec.
pub(crate) fn carriers_meet(kb: &KnowledgeBase, a: TermId, b: TermId) -> bool {
    let (head_a, row_a) = carrier_parts(kb, a);
    let (head_b, row_b) = carrier_parts(kb, b);
    same_sort_canonical(kb, head_a, head_b)
        && row_a.iter().all(|(tv, va)| match binding_for_param(kb, &row_b, *tv, BindingKeyMatch::Label) {
            Some(vb) => bindings_meet(kb, va, vb),
            None => true,
        })
}

/// Does a GOAL of `spec`, its bindings of the spec's type-vars in hand, describe a carrier in
/// common with `carrier`, a row's substituted sort? Type-var by type-var: a binding either
/// side leaves out is any, and two that both bind must meet ([`bindings_meet`]). The goal binds
/// no other key of interest: an operation binding is no type-var, and is not read.
pub(crate) fn carrier_meets_goal(
    kb: &KnowledgeBase,
    spec: Symbol,
    carrier: TermId,
    bindings: &[(Symbol, Value)],
) -> bool {
    let (_, row) = carrier_parts(kb, carrier);
    sort_carrier(kb, spec).type_vars.iter().all(|&tv| {
        match (
            binding_for_param(kb, &row, tv, BindingKeyMatch::Label),
            binding_for_param(kb, bindings, tv, BindingKeyMatch::Label),
        ) {
            (Some(a), Some(b)) => bindings_meet(kb, a, b),
            _ => true,
        }
    })
}

/// A default row's carrier as `(head, bindings)`. Every carrier is built by
/// [`provision_carrier`] as a sort reference or an application of one, so one that does not read
/// as either is a defect of that owner, and is refused here rather than read as no row.
fn carrier_parts(kb: &KnowledgeBase, carrier: TermId) -> (Symbol, SmallVec<[(Symbol, Value); 2]>) {
    carrier_view_parts(kb, &crate::kb::term_view::TermIdView(carrier)).unwrap_or_else(|| {
        panic!(
            "a default row's carrier `{}` is no sort and no application of one —              `provision_carrier` builds every carrier as one",
            type_display_name(kb, carrier)
        )
    })
}

/// Where a VALUE-DIRECTED lookup's runtime sort stands in a row's carrier — the asker knows the
/// sort of a value and no term ([`crate::kb::defaults::CarrierKey::Base`]). For a
/// self-representing spec the value is a provider's, and the carrier's head is that sort. For
/// a spec with a dictionary the value is the argument at the parameter the call dispatches on,
/// which is still read by the one-parameter ladder that dispatch reads
/// ([`spec_carrier_param_or_sole`]: the V readers of `docs/design/spec-carrier-set.md` §4, a
/// later step of WI-20261122-CXR5B); `None` where that ladder names no parameter, a lookup that
/// declines.
pub(crate) enum ValueSortAt {
    CarrierHead,
    Binding(Symbol),
}

/// The [`ValueSortAt`] of `spec`.
pub(crate) fn value_sort_at(kb: &KnowledgeBase, spec: Symbol) -> Option<ValueSortAt> {
    let canon = kb.canonical_sort_sym(spec);
    if spec_is_self_representing(kb, canon) {
        return Some(ValueSortAt::CarrierHead);
    }
    spec_carrier_param_or_sole(kb, canon).map(ValueSortAt::Binding)
}

/// Is `carrier`, a row of `spec`, at the runtime sort `sort` read at `at`? The row's sort there
/// must be `sort` itself: a binding to a type parameter, or one left out, is no sort, as a row
/// filed by its binding's sort was not.
pub(crate) fn carrier_at_value_sort(
    kb: &KnowledgeBase,
    carrier: TermId,
    at: &ValueSortAt,
    sort: Symbol,
) -> bool {
    let (head, bindings) = carrier_parts(kb, carrier);
    match at {
        ValueSortAt::CarrierHead => same_sort_canonical(kb, head, sort),
        ValueSortAt::Binding(p) => binding_for_param(kb, &bindings, *p, BindingKeyMatch::Label)
            .and_then(|b| carrier_view_parts(kb, b))
            .is_some_and(|(base, _)| same_sort_canonical(kb, base, sort)),
    }
}

/// One provision of a spec, as [`ProvisionsOfSpec`] holds it.
pub(crate) struct ProvisionAt {
    /// The row, which is the provision's identity.
    pub(crate) row: RuleId,
    /// The `sort_ref`, raw: who provides — not where the provision is.
    pub(crate) provider: Symbol,
}

/// The provisions of one spec, each filed by its carrier — "the provisions of `S` at a
/// substituted sort that unifies with `t`" (design §5, stage 1), for a reader that asks it of
/// many `t`. Read through the keyed provider index ([`provides_rows_of_spec`]), every row the
/// relation holds: an author's, an instance fact's, and those the derivations and the
/// forwarding wrote, which is what makes a derivation idempotent across load phases.
pub(crate) struct ProvisionsOfSpec {
    spec: Symbol,
    shape: Shape,
    rows: Vec<ProvisionAt>,
    /// Row indices by the bucket of their carrier's head ([`carrier_view_bucket`]), each in
    /// row order. A provision whose binding no sort and no structural head heads — a row, a
    /// value — is in none.
    by_bucket: HashMap<CarrierBucket, Vec<usize>>,
}

/// The shapes of spec [`ProvisionsOfSpec::at_sort`] is defined for.
#[derive(Clone, Copy)]
enum Shape {
    /// A spec with a dictionary of one type-var: every spec a derivation reads, declared.
    OneTypeVar(Symbol),
    /// A name the KB has and no declaration — the bootstrap `Eq`, `PartialEq` and `NonEq` of a
    /// KB loaded without the standard library (`load::register_prelude`). It has no type-var
    /// to read, and its only rows are the equality derivation's own, each a carrier's
    /// self-provision (`eq_derive::assert_provides` binds a `T` the declaration lacks to the
    /// provider): each is at its provider. MEASURED: asked as a declared spec of no type-var,
    /// about 150 tests of the lib and the CLI suites that load no stdlib failed.
    Undeclared,
    /// Any other declared spec: several type-vars, none, or self-representing — stage 2's.
    Other,
}

impl ProvisionsOfSpec {
    /// Every provision of `spec`, filed by its carrier.
    pub(crate) fn of(kb: &KnowledgeBase, spec: Symbol) -> Self {
        let canon = kb.canonical_sort_sym(spec);
        // The class decides what `Self` denotes (§1's table): a dictionary where no operation
        // takes a value of type `Self` (074 §2), the provider's value otherwise.
        let shape = match sort_carrier(kb, canon).type_vars.as_slice() {
            _ if kb.sort_kind(canon).is_none() => Shape::Undeclared,
            [tv] if !spec_is_self_representing(kb, canon) => Shape::OneTypeVar(*tv),
            _ => Shape::Other,
        };
        let mut out = ProvisionsOfSpec { spec: canon, shape, rows: Vec::new(), by_bucket: HashMap::new() };
        for row in provides_rows_of_spec(kb, canon) {
            let at = out.rows.len();
            let bucket = match shape {
                Shape::OneTypeVar(tv) => dictionary_carrier_bucket(kb, tv, &row),
                Shape::Undeclared => Some(CarrierBucket::Sort(kb.canonical_sort_sym(row.provider))),
                Shape::Other => None,
            };
            if let Some(b) = bucket {
                out.by_bucket.entry(b).or_default().push(at);
            }
            out.rows.push(ProvisionAt { row: row.rid, provider: row.provider });
        }
        out
    }

    /// The provisions whose carrier unifies with `S[T = sort]` — the carrier of the provision
    /// `sort provides S[T = Self]` the derivations add. In relation order.
    ///
    /// THE UNIFICATION IS THE DEFAULT ROWS' (`kb::defaults`' `check_one_default`): two carriers
    /// in one bucket ([`carrier_view_bucket`]) and overlapping there
    /// ([`carrier_views_overlap`]). Against a BARE `sort` the overlap is decided by the bucket
    /// alone — the bare name leaves every slot open, and an omitted binding is any — so
    /// `Eq[T = Box[T = Int64]]` is at `Box`'s carrier, and `Box` derives no equality beside it
    /// (decision 2). A binding to a type parameter (`Eq provides PartialEq[T = T]`, the
    /// refinement edge whose rows the forwarding materializes per carrier) is in that
    /// parameter's bucket and at no sort's, as it is to the default rows.
    ///
    /// Defined for a spec with a dictionary of ONE type-var, the shape every derivation reads,
    /// and for an undeclared bootstrap name ([`Shape::Undeclared`]).
    /// For one of several, which of them `Self` binds is not said by the sort alone; for a
    /// self-representing spec the carrier is the provider (decision 5). Both are stage 2's
    /// (WI-20261122-CXR5B), and asked of either with a provision to read this panics rather
    /// than answer a question no reader has yet.
    pub(crate) fn at_sort(&self, kb: &KnowledgeBase, sort: Symbol) -> Vec<&ProvisionAt> {
        self.assert_defined(kb, sort);
        self.by_bucket
            .get(&CarrierBucket::Sort(kb.canonical_sort_sym(sort)))
            .map(|at| at.iter().map(|&i| &self.rows[i]).collect())
            .unwrap_or_default()
    }

    /// Does any provision stand at the carrier [`Self::at_sort`] reads?
    pub(crate) fn any_at_sort(&self, kb: &KnowledgeBase, sort: Symbol) -> bool {
        self.assert_defined(kb, sort);
        self.by_bucket
            .get(&CarrierBucket::Sort(kb.canonical_sort_sym(sort)))
            .is_some_and(|at| !at.is_empty())
    }

    /// A spec with NO provision answers "none" at every carrier, whatever its shape — a KB
    /// loaded without the standard library has `anthill.prelude.Eq` as a bootstrap name with no
    /// type-vars and nothing providing it, and is a KB like any other. Only provisions read at
    /// an undefined carrier would be a wrong answer.
    fn assert_defined(&self, kb: &KnowledgeBase, sort: Symbol) {
        assert!(
            !matches!(self.shape, Shape::Other) || self.rows.is_empty(),
            "ProvisionsOfSpec::at_sort: `{}` is no spec with a dictionary of one type-var, the \
             only shape whose carrier `S[T = {}]` is read here (design spec-carrier-set §5)",
            kb.qualified_name_of(self.spec),
            kb.qualified_name_of(sort),
        );
    }
}

/// The bucket of `row`'s carrier, for a spec with a dictionary whose one type-var is `tv`: the
/// spec at `row`'s binding of `tv` (decision 5), filed by that binding's head.
///
/// A binding LEFT OUT reads as the provider, which is `kernel-language.md` §5.2 as it stands: a
/// left-out parameter is `?`, "the spec's carrier parameter excepted, which says which sort
/// provides" — and a spec of one type-var has no other. Decision 3 reads every left-out
/// type-var as `?`, and lands with stage 2 (WI-20261122-CXR5B) beside the refusal it restates.
/// Read as `?` here, it would put the provision at EVERY carrier. Only a refused program
/// writes one today (`ProvisionNamesNoCarrier` refuses `provides PartialEq`; a bare `provides
/// NonEq` is refused by its contract and its member check), and MEASURED, the refused `sort A
/// { …; provides PartialEq }` then gave each stdlib composite an equality-closure error beside
/// its one refusal — about 150 of them.
fn dictionary_carrier_bucket(kb: &KnowledgeBase, tv: Symbol, row: &ProvidesRow) -> Option<CarrierBucket> {
    // Bindings live on the `SortView` wrapper alone; a bare spec reference binds nothing.
    let binding = view_is_sort_view(kb, &row.spec_view)
        .then(|| provision_binding_value_at_param(kb, tv, &row.spec_view))
        .flatten();
    match binding {
        Some(binding) => carrier_view_bucket(kb, &binding),
        None => Some(CarrierBucket::Sort(kb.canonical_sort_sym(row.provider))),
    }
}
