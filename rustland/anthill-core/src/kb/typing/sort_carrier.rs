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
