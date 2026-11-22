//! WI-860 (proposal 058 §3.6, phase 8b) — the DEFAULTS SUBSTRATE.
//!
//! *Whether silence may pick* is not a property of a spec — `Monoid[Int64]` has no
//! canonical instance while `Monoid[List]` has concatenation — so it is a per-`(spec,
//! carrier)` partial function. 058 §3.6 expresses it as reflect-layer relations, on
//! proposal 035's variance pattern and with zero new grammar:
//!
//! ```text
//! entity DefaultProvider(spec: Symbol, provider: Symbol)   -- the DECLARED row
//! rule default_provider(?S, ?C, ?W) :- DefaultProvider(…), provision_carrier(?W, ?S, ?C)
//! rule default_provider(?S, ?C, ?C) :- self_provides(?C, ?S)   -- the INFERRED row
//! ```
//!
//! Both live in `stdlib/anthill/reflect/typing.anthill`, and **the relations are the
//! authority**: this module MATERIALIZES them into an index the hot path can read
//! (`EqDispatchIndex`'s pattern), and runs the two checks that cannot be SLD goals
//! because they are about the row SET rather than about one row.
//!
//! WI-861 ADDED THE CONSUMER — 058 §3.2's **rung 2a**, *an unselected dispatch takes the
//! DEFAULT among the tied most-specific candidates* — as [`default_among`], which every
//! tie site in the tree asks so the rung has one implementation. [`CarrierKey`] and
//! [`DefaultRung`](typing::DefaultRung) carry the two bounds on it: how precisely the
//! asker can name the carrier, and the one goal shape (an omitted NAMED slot) where a
//! default must NOT answer.
//!
//! The two checks:
//!
//! * **`one_default`** — any two answers for one carrier coincide, compared at
//!   OVERLAPPING carriers rather than equal ones ([`check_one_default`], which carries
//!   the why). NO-DISPLACEMENT NEEDS NO CODE: a self-providing carrier already has an
//!   inferred row, so an explicit row naming a rival violates `one_default` — *fill
//!   silence, never overwrite speech*.
//! * **check 1**, 058 §3.5's first selection-site check re-read at load: a
//!   `DefaultProvider` naming a provider that does not provide the spec is a typo, and
//!   the carrier it would key is underivable.
//!
//! WHAT THIS PASS MUST NOT INHERIT (WI-859's parting instruction, and the reason it is
//! not built on `provider_coherence_candidates`): the coherence grouping carries
//! POLICY — an op-less spec's provision is dropped, a concrete provider reshapes the
//! witness leg — while a default is about WHICH PROVISION SILENCE TAKES and has none of
//! that. The policy-free owner is [`typing::provision_carrier`] (where a provision is, and
//! whether it is its provider's own) over [`typing::all_provisions`], which is what both
//! this module and the `anthill.reflect.typing.provision_carrier_of` /
//! `own_provision_carrier_of` builtins behind the anthill rules call.
//!
//! THE FORK WI-859 LEFT FOR THIS PHASE, decided here: *does a carrier that owns no
//! member self-provide at all?* YES. `self_provides` is a relation over PROVISIONS —
//! "who supplies the dictionary for this `(spec, carrier)`" — and a carrier whose spec
//! ops all have default bodies supplies a perfectly good dictionary made of those
//! defaults. Asking `carrier_own_op` instead would make a carrier's default row appear
//! and disappear as its members are added and removed, which is not what a *default
//! instance* means. Driven by `a_carrier_owning_no_member_still_self_provides`.
//!
//! REFERENCE: proposal 058 §3.6; `docs/design/058-implementation.md` §6, §19.

use std::collections::HashMap;

use crate::intern::Symbol;
use crate::kb::load::LoadError;
use crate::kb::term::TermId;
use crate::kb::typing;
use crate::kb::KnowledgeBase;

/// WHICH `one_default` collision this is — a typed answer rather than one paragraph
/// covering every shape, the [`super::typing::TieRepair`] discipline: *"every way of
/// reaching this diagnostic must say which of the three it is, so a new one cannot
/// quietly inherit a repair the next compile rejects."*
///
/// The three arms are reachable and their repairs genuinely differ. A single wording was
/// written and it was WRONG for the third: it announced "carrier 'X' has 2 default
/// providers" where there are two DIFFERENT carriers, and advised "keep exactly one row
/// per carrier" — already satisfied, one mark each.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DefaultCollision {
    /// A DECLARED mark against a carrier that provides the spec ITSELF, whose inferred
    /// row it collides with. No-displacement (058 §3.6), and the shape needing the
    /// inferred row NAMED, since the author wrote only one line.
    Displaced,
    /// Two DECLARED marks at ONE carrier. Delete one.
    SameCarrier,
    /// Two DECLARED marks whose carriers OVERLAP without being equal — a ground row
    /// beside a parametric one for one family. Neither is redundant, and the repair is
    /// not "delete a duplicate" but "these two must not both apply".
    OverlappingCarriers,
    /// WI-20261122-CXR5B — two INFERRED rows: two providers each provide the spec FOR
    /// THEMSELVES at carriers in common (decision 6 of `docs/design/spec-carrier-set.md`,
    /// every binding counting: `Num provides Coll[C = Foo, Elem = Self]` beside `Foo provides
    /// Coll[C = Self, Elem = Num]`). Neither is a rival displacing the other, so the repair is
    /// a mark choosing one: `default provides` on it.
    TwoOwnProviders,
}

impl DefaultCollision {
    /// The ONE decision site, asked by the check rather than reasoned out at the message.
    fn of(a: &DefaultRow, b: &DefaultRow, same_carrier: bool) -> Self {
        let inferred = |r: &DefaultRow| r.origin == DefaultOrigin::Inferred;
        if inferred(a) && inferred(b) {
            // Possible only for a spec of several type-vars: two providers each heading a
            // binding of carriers that unify. A spec of one type-var cannot give two: each
            // own provision binds it to its provider, and two providers are two sorts.
            DefaultCollision::TwoOwnProviders
        } else if inferred(a) || inferred(b) {
            DefaultCollision::Displaced
        } else if same_carrier {
            DefaultCollision::SameCarrier
        } else {
            DefaultCollision::OverlappingCarriers
        }
    }
}

/// THE ONE OWNER of [`LoadError::AmbiguousDefaultProvider`]'s wording, read by both of
/// that error's faces — the `unselected_instance_message` / `ambiguous_spec_op_dispatch_
/// message` discipline, and not decoration here: `LoadError` renders through `Display`
/// unless the error is `Located`, and a post-load pass's errors are not, so a richer
/// `format_at` arm would have been text nobody could reach. MEASURED — `anthill load`
/// and `anthill check` both printed the terse face.
pub(crate) fn ambiguous_default_message(
    spec: &str,
    carrier: &str,
    providers: &[String],
    collision: DefaultCollision,
) -> String {
    let rows = providers.join("; ");
    let short = typing::short_name_of(spec);
    match collision {
        DefaultCollision::Displaced => format!(
            "default displaced: carrier '{}' provides '{}' ITSELF, so it is already its own \
             default — and a marked rival would silently change what every bracket-less call \
             on it means. The two rows are {}. 058 §3.6: fill silence, never overwrite speech; \
             delete the `DefaultProvider` row, or select the rival at the call sites that want \
             it with a `[{} = <provider>]` bracket",
            carrier, spec, rows, short
        ),
        DefaultCollision::SameCarrier => format!(
            "ambiguous default: carrier '{}' has {} default providers of '{}' ({}) — a default \
             is what a call that says NOTHING takes, so there is no site at which to select \
             one; keep exactly one `DefaultProvider(spec: {}, provider: …)` row per carrier",
            carrier,
            providers.len(),
            spec,
            rows,
            short
        ),
        DefaultCollision::OverlappingCarriers => format!(
            "overlapping defaults: '{}' has default providers at carriers that describe \
             carriers in COMMON ({}) — a call at a shared carrier would have two answers, and \
             defaults are NOT layered by specificity (there is no such rung: 058 §3.2 ranks \
             candidates, never defaults). Give the two marks disjoint carriers, or delete one",
            spec, rows
        ),
        DefaultCollision::TwoOwnProviders => format!(
            "two own defaults: '{}' is provided at carrier '{}' by two providers each for \
             ITSELF — each is the head of one of the carrier's bindings, so each provision is \
             its provider's own and its default. The rows are {}. A call there that names no \
             provider would have two answers: mark the one silence takes `default provides`, \
             or select a provider at the call sites with a `[{} = <provider>]` bracket",
            spec, carrier, rows, short
        ),
    }
}

/// THE ONE OWNER of [`LoadError::DefaultProviderDoesNotProvide`]'s wording — see
/// [`ambiguous_default_message`] for why both faces must read one function.
///
/// Names what DOES provide the spec, because the two mistakes behind this refusal are
/// repaired differently: a mistyped provider is fixed by picking from the list, an
/// unprovided spec by writing a provision at all, and "does not provide the spec" alone
/// does not distinguish them.
pub(crate) fn default_provider_not_a_provider_message(
    spec: &str,
    provider: &str,
    provides: &[String],
) -> String {
    let alternatives = if provides.is_empty() {
        format!("nothing provides '{}' at all", spec)
    } else {
        format!(
            "'{}' is provided by {}",
            spec,
            provides
                .iter()
                .map(|p| format!("'{}'", p))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    format!(
        "`fact DefaultProvider(spec: {}, provider: {})` names a provider that does not provide \
         the spec — {}. A default's CARRIER is derived from the provider's own provision, so \
         this row would name no carrier and do nothing",
        typing::short_name_of(spec),
        typing::short_name_of(provider),
        alternatives
    )
}

/// Where a default row came from — the half of a row a diagnostic MUST print, because
/// the two are repaired differently and one of them the author never wrote.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DefaultOrigin {
    /// A `fact DefaultProvider(spec: S, provider: W)` — the application's act when
    /// linking libraries that do not know each other (058 §3.6).
    Declared,
    /// INFERRED from the carrier's own provision: the carrier's own instance is its
    /// default, so the existing standard library needs no edits. This is the row that
    /// makes no-displacement derived rather than stated — and the row a displacement
    /// diagnostic has to NAME, since the author never wrote it and would otherwise read
    /// `one_default` as firing on a single declaration.
    Inferred,
}

impl DefaultOrigin {
    fn label(self) -> &'static str {
        match self {
            DefaultOrigin::Declared => "declared",
            DefaultOrigin::Inferred => "inferred from the carrier's own provision",
        }
    }
}

/// One answer of `default_provider(?S, ?C, ?W)`.
///
/// Fields are `pub(crate)`: 058 rung 2a (WI-861) reads them structurally from inside the
/// crate, and everything OUTSIDE reads [`DefaultProviderIndex::rendered_rows`] instead —
/// WI-859's rule for its own probe, and for its reason: a `TermId` is a hash-consed id
/// with no meaning outside this store, so publishing one would pin an internal into the
/// crate's contract one phase before its consumer exists to shape it.
#[derive(Clone, Copy, Debug)]
pub struct DefaultRow {
    /// The spec, canonical.
    pub(crate) spec: Symbol,
    /// The provision's CARRIER, the substituted sort its values are of
    /// ([`typing::provision_carrier`], WI-20261122-CXR5B decision 5): `Desc[T = Leaf]` for a
    /// sort's own provision, `Ord[T = List[T = E]]` for a conditional witness, `List[T = T]`
    /// for a provider of a self-representing spec. Kept as the whole term because
    /// `one_default` compares rows at unifiable carriers ([`typing::carrier_views_overlap`]),
    /// every type-var of the spec at once.
    pub(crate) carrier: TermId,
    /// The row's partition key in its spec's rows ([`typing::default_row_key`]), an index key
    /// only; `None` for a row every lookup of the spec reads.
    pub(crate) key: Option<typing::CarrierBucket>,
    /// The provider, canonical. A sort the `carrier` names for every INFERRED row (decision
    /// 6) — and also for a DECLARED mark naming a provider of its own provision, which is why
    /// the origin is stored rather than derived.
    pub(crate) provider: Symbol,
    /// WI-20260919-HXGXF — the provider's NAME TERM, so the probe can render it through
    /// the same walk it renders [`Self::carrier`] with.
    ///
    /// `render_row` used to print the carrier with `type_display_name` and the provider
    /// with `local_name_of`, and those two disagree for exactly one sort: the display
    /// walk has an arm for the BOTTOM type, so `Nothing` renders `nothing` there and
    /// `Nothing` here. Every other carrier agreed, so the asymmetry was invisible until
    /// `type_value_derive` filed the first provision ever held at `Nothing` — and then
    /// the corpus test comparing the SLD relation against this index failed on one row
    /// out of hundreds, reporting a disagreement that was only ever in the rendering.
    pub(crate) provider_name: TermId,
    pub(crate) origin: DefaultOrigin,
    /// Is the provision behind the row its provider's OWN (decision 6)? Every inferred row's
    /// is; a declared mark's is where it marks a provider of its own provision, and is not
    /// where it marks a witness. A declared own row is a choice among owns, which `one_default`
    /// admits beside another own provider's inferred row and the lookup takes over it.
    pub(crate) own: bool,
}

/// WI-860 — the materialized `default_provider` relation: 058 §3.6's rows, filed by SPEC and,
/// within a spec, partitioned by [`typing::default_row_key`] (WI-20261122-CXR5B: a row is at a
/// substituted sort, and a spec's rows were bucketed by the one sort its carrier parameter
/// bound, which a spec of several type-vars does not say).
///
/// Built once per load, after every `SortProvidesInfo` fact is asserted, and read by a
/// hash lookup — the [`super::load::EqDispatchIndex`] arrangement, and for the same
/// reason: the relation is the authority, but a per-dispatch SLD query for it is not
/// something the classifier's tie can afford.
///
/// NOTHING CONSUMES IT YET. Rung 2a — the classifier's tie consulting the default — is
/// phase 8c (WI-861); this phase is the relations plus the load checks, independently
/// green. The index is `pub` and probed by `wi860_default_provider_relations_test`,
/// which also asserts it AGREES with the anthill relation answer for answer. That
/// agreement is the guard against the one failure this arrangement invites: two
/// derivations of one relation drifting apart.
#[derive(Default, Debug, Clone)]
pub struct DefaultProviderIndex {
    by_spec: HashMap<Symbol, SpecDefaults>,
}

/// One spec's default rows, in the order they were derived (declared rows first, then
/// inferred), with their partition.
#[derive(Default, Debug, Clone)]
struct SpecDefaults {
    rows: Vec<DefaultRow>,
    /// Row indices by [`DefaultRow::key`], in row order.
    by_key: HashMap<typing::CarrierBucket, Vec<usize>>,
    /// The rows with no key, in row order: every lookup reads them.
    open: Vec<usize>,
}

impl SpecDefaults {
    fn push(&mut self, row: DefaultRow) {
        let at = self.rows.len();
        match row.key {
            Some(k) => self.by_key.entry(k).or_default().push(at),
            None => self.open.push(at),
        }
        self.rows.push(row);
    }

    /// The rows a lookup whose key is `key` reads: that key's and the open ones, or every row
    /// where the asker has no key. Rows at DISJOINT carriers coexist, so a reader filters what
    /// this answers rather than take the first.
    fn reads(&self, key: Option<typing::CarrierBucket>) -> Vec<&DefaultRow> {
        match key {
            None => self.rows.iter().collect(),
            Some(k) => {
                let mut at: Vec<usize> = self.by_key.get(&k).cloned().unwrap_or_default();
                at.extend(self.open.iter().copied());
                at.sort_unstable();
                at.into_iter().map(|i| &self.rows[i]).collect()
            }
        }
    }
}

impl DefaultProviderIndex {
    /// Every row, spec order unspecified.
    pub(crate) fn rows(&self) -> impl Iterator<Item = &DefaultRow> {
        self.by_spec.values().flat_map(|s| s.rows.iter())
    }

    /// THE PROBE — every row as `"spec | carrier | provider"`, sorted, using the LOCAL
    /// names and the type rendering the `default_provider` relation's own answers render
    /// to. Rendered rather than structural, WI-859's rule: this exists so the index can
    /// be compared to the relation it materializes, and a comparison is only meaningful
    /// between two things rendered the same way.
    ///
    /// The ORIGIN is deliberately absent — the relation has no such column, and this is
    /// the side that must line up with it. [`Self::rendered_rows_for_carrier`] carries it.
    pub fn rendered_rows(&self, kb: &KnowledgeBase) -> Vec<String> {
        let mut out: Vec<String> = self.rows().map(|r| render_row(kb, r, false)).collect();
        out.sort();
        out.dedup();
        out
    }

    /// [`Self::rendered_rows`] for the rows whose carrier names ONE sort — as its head or as
    /// the head of one of its bindings ([`typing::carrier_names_sort`]) — WITH each row's
    /// origin: the half a no-displacement diagnostic prints, and the half that says whether a
    /// row was inferred from the provider's own provision or written by hand. Sorted.
    pub fn rendered_rows_for_carrier(&self, kb: &KnowledgeBase, carrier_qn: &str) -> Vec<String> {
        let Some(sym) = kb.try_resolve_symbol(carrier_qn) else {
            return Vec::new();
        };
        let mut out: Vec<String> = self
            .rows()
            .filter(|r| typing::carrier_names_sort(kb, r.carrier, sym))
            .map(|r| render_row(kb, r, true))
            .collect();
        out.sort();
        out
    }
}

/// One row rendered — the LOCAL names, because that is what `type_display_name` answers
/// for the name terms the relation's `extract_sort_ref` hands back, and comparing the two
/// sides on different name forms would compare the renderings rather than the rows.
fn render_row(kb: &KnowledgeBase, r: &DefaultRow, with_origin: bool) -> String {
    let base = format!(
        "{} | {} | {}",
        kb.local_name_of(r.spec),
        typing::type_display_name(kb, r.carrier),
        typing::type_display_name(kb, r.provider_name)
    );
    if with_origin {
        format!("{} ({})", base, r.origin.label())
    } else {
        base
    }
}

/// WI-861 (058 §3.2 rung 2a) — the CARRIER a default lookup is keyed by, at the precision
/// its asker actually has.
///
/// TWO ARMS BECAUSE THERE ARE TWO ASKERS AND THEY KNOW DIFFERENT AMOUNTS, and an ENUM
/// rather than a `{ base, view }` pair because a carrier's base is DERIVABLE from its
/// view: carrying both would let a caller hand over a base that disagrees with the term
/// beside it, and nothing would catch it. The base is not a second identity — it is the
/// [`DefaultProviderIndex`] BUCKET KEY, and it is derived here rather than supplied.
#[derive(Clone, Copy, Debug)]
pub(crate) enum CarrierKey<'a> {
    /// The goal's SUBSTITUTED SORT, its bindings of the spec's type-vars — what the provision
    /// tie in [`typing::resolve_inner`] has, since the goal carries its own bindings. **This
    /// is the arm that can tell `X[Y]` from `X[Z]`**: rows are per substituted sort, so
    /// `Ord[T = List[T = Int64]]` and `Ord[T = List[T = String]]` are two rows, and only the
    /// overlap of every binding ([`typing::carrier_meets_goal`]) separates them. On the carrier
    /// each binding rides — a carrier that holds a value is an occurrence, and is compared with
    /// a row's stored term through the view.
    Goal(&'a [(Symbol, crate::eval::value::Value)]),
    /// Only the runtime carrier SORT is known — a VALUE-DIRECTED tie, where the receiver
    /// is a `Value::List` naming `List` and carrying no element type.
    ///
    /// This is NOT "match anything". It drops the overlap filter, which can only make the
    /// answer LESS decided: two rows at one base naming two providers (the DISJOINT pair
    /// `one_default` admits) leave [`default_provider_for`] with no unique answer and the
    /// tier-3 refusal stands. The base-only asker can decline where the term-carrying one
    /// would decide; it can never decide where the other would decline.
    Base(Symbol),
}

/// WI-861 (058 §3.6) — WHICH PROVIDER SILENCE TAKES for this `(spec, carrier)`, or `None`
/// when nothing says.
///
/// The index is the materialized `default_provider(?S, ?C, ?W)` relation, so this is that
/// query with `?S` and `?C` given. `one_default` guarantees at most one provider across
/// rows whose carriers OVERLAP — but rows at DISJOINT carriers of one base coexist by
/// design (`List[T = Int64]` beside `List[T = String]`), so two providers can still come
/// back from one bucket and the loop must answer `None` rather than take the first. That
/// is not a load-error case; it is a lookup at a carrier the asker described too loosely
/// (see [`CarrierKey::view`]).
///
/// `None` when the KB never built an index — a hand-built `KnowledgeBase` that never
/// loaded. Rung 2a then never fires, which is the pre-8c behaviour.
pub(crate) fn default_provider_for(
    kb: &KnowledgeBase,
    spec: Symbol,
    carrier: CarrierKey<'_>,
) -> Option<Symbol> {
    let index = kb.default_provider_index()?;
    let spec_canon = kb.canonical_sort_sym(spec);
    let Some(rows) = index.by_spec.get(&spec_canon) else {
        return None;
    };
    // The partition key is derived, never supplied — see [`CarrierKey`] — and only narrows
    // which rows are read: the filter is what answers.
    enum At<'b> {
        Goal(&'b [(Symbol, crate::eval::value::Value)]),
        Value(typing::ValueSortAt, Symbol),
    }
    let (key, at) = match carrier {
        CarrierKey::Goal(bindings) => (typing::goal_row_key(kb, spec_canon, bindings), At::Goal(bindings)),
        CarrierKey::Base(s) => {
            let pos = typing::value_sort_at(kb, spec_canon)?;
            let sort_key = Some(typing::CarrierBucket::Sort(kb.canonical_sort_sym(s)));
            let key = match &pos {
                typing::ValueSortAt::CarrierHead => sort_key,
                // The partition is by the FIRST type-var's binding; the value's sort keys it only
                // where that is the type-var the value is at.
                typing::ValueSortAt::Binding(p) => sort_key.filter(|_| {
                    typing::sort_carrier(kb, spec_canon).type_vars.first() == Some(p)
                }),
            };
            (key, At::Value(pos, s))
        }
    };
    let meeting: Vec<&DefaultRow> = rows
        .reads(key)
        .into_iter()
        .filter(|row| match &at {
            At::Goal(bindings) => typing::carrier_meets_goal(kb, spec_canon, row.carrier, bindings),
            At::Value(pos, s) => typing::carrier_at_value_sort(kb, row.carrier, pos, *s),
        })
        .collect();
    // A DECLARED OWN row is a mark choosing among providers each own at its carrier, which
    // `one_default` admits beside the others' inferred rows ([`DefaultCollision::
    // TwoOwnProviders`]'s repair): an inferred row of another provider at a carrier one such
    // mark meets yields to it. Every other row stays, so a mark does not settle a tie with a
    // rival it does not meet, nor with another mark.
    let marks: Vec<&DefaultRow> = meeting
        .iter()
        .copied()
        .filter(|r| r.own && r.origin == DefaultOrigin::Declared)
        .collect();
    let answering = meeting.into_iter().filter(|r| {
        r.origin != DefaultOrigin::Inferred
            || !marks
                .iter()
                .any(|m| m.provider != r.provider && typing::carriers_meet(kb, m.carrier, r.carrier))
    });
    let mut answer: Option<Symbol> = None;
    for row in answering {
        match answer {
            None => answer = Some(row.provider),
            // Rows are stored with a canonical provider, so this is an id compare.
            Some(w) if w == row.provider => {}
            Some(_) => return None,
        }
    }
    answer
}

/// WI-861 — 058 §3.2 RUNG 2a, as one predicate: *when exactly one of the tied candidates
/// is the default provider, take it.*
///
/// `providers` is the tied candidates' PROVIDER symbols in candidate order; the answer is
/// the index of the one the default names. Every caller reduces its own candidate type to
/// that sequence — a provision's `impl_sort`, a supplier's route-derived provider — so
/// the rung itself has one implementation and cannot say different things at the three
/// sites that ask it.
///
/// **EXACTLY ONE, not the first.** Two tied candidates naming one provider is a real
/// configuration (a carrier's own member beside its own instance fact's binding; one
/// provider reached through two non-identical provisions), and a default names a
/// PROVIDER — it does not choose between two of that provider's own texts. The refusal
/// stands there, which is what keeps WI-1027's fixture 2 and `TieRepair::
/// OneProviderTwoProvisions` reachable.
///
/// **SPECIFICITY RANKS FIRST** (058 §3.2): this is consulted only where the tie has
/// already survived the ranking its caller applies — `pick_most_specific` at the
/// provision site, and nothing at the supplier sites, which have no ranking at all
/// (`arbitrate_defaulted_supplier_tie`'s doc says why). A default is a fallback, never a
/// competitor: no candidate loses to one that ranks below it.
pub(crate) fn default_among<I: Iterator<Item = Symbol>>(
    kb: &KnowledgeBase,
    spec: Symbol,
    carrier: CarrierKey<'_>,
    providers: I,
) -> Option<usize> {
    let want = default_provider_for(kb, spec, carrier)?;
    let mut hit: Option<usize> = None;
    for (i, p) in providers.enumerate() {
        if kb.canonical_sort_sym(p) != want {
            continue;
        }
        if hit.is_some() {
            return None;
        }
        hit = Some(i);
    }
    hit
}

/// WI-860 — build the index and run 058 §3.6's two load checks.
///
/// Must run once every `SortProvidesInfo` fact is asserted, since BOTH legs read the
/// provision relation: the inferred leg IS that relation filtered to self-provisions,
/// and the declared leg derives its carrier from the named provider's own provision.
/// Placed after `eq_derive::run` for that reason — that pass is the last to assert
/// provisions, and a default row for a derived `PartialEq` provision must exist for the
/// same reason as one for a written provision.
///
/// WI-861 CALLS IT A SECOND TIME, EARLIER — see [`seed_default_provider_index`]. THIS
/// call is the authoritative one and the only one whose verdict is read.
#[must_use = "the default-provider refusals are load-blocking and must be merged"]
pub fn build_default_provider_index(kb: &mut KnowledgeBase) -> Vec<LoadError> {
    // ONE canonicalizing walk over the provisions, shared by both legs.
    // `canonical_sort_sym` is a qualified-name hash, not a symbol compare, so the
    // per-provision filter the declared leg needs is computed here rather than
    // recomputed for each mark (`marks × provisions` string hashes otherwise).
    // The carrier VIEW of a carrier-keyed provision is the provider's own name and has
    // to be MINTED, which is the `&mut` this loop spends; minting is idempotent on the
    // hash-consed store, so it adds no term the walk would not have added.
    //
    // A row of this index is KEYED on its carrier's term ([`push_row`]), so each
    // provision's view is lowered here, where the store is in hand: a binding written
    // through a type alias is the carrier its type is. A view with no term is a provision
    // the loader has refused where it is written (`ValueInTypeNotResolved`), and is no
    // row.
    let provisions: Vec<Provision> = typing::all_provisions(kb)
        .into_iter()
        .filter_map(|p| {
            let spec_view =
                crate::kb::node_occurrence::value_to_term(kb, &p.spec_view).ok()?;
            let provider = kb.canonical_sort_sym(p.provider);
            let spec = kb.canonical_sort_sym(p.spec);
            let carrier = typing::provision_carrier(kb, p.spec, provider, spec_view);
            Some(Provision {
                provider,
                provider_name: kb.make_name_term_from_sym(provider),
                spec,
                key: typing::default_row_key(kb, spec, carrier.term),
                carrier: carrier.term,
                own: carrier.own,
            })
        })
        .collect();
    let (declared, mut errors) = declared_default_rows(kb);

    let (rows, row_errors) = derive_rows(kb, &provisions, &declared);
    errors.extend(row_errors);
    let mut by_spec: HashMap<Symbol, SpecDefaults> = HashMap::new();
    for row in rows {
        by_spec.entry(row.spec).or_default().push(row);
    }
    kb.set_default_provider_index(DefaultProviderIndex { by_spec });
    errors
}

/// WI-861 — the SAME derivation, run BEFORE the typer, because rung 2a's first consumer
/// is a load-time refusal.
///
/// 058 §3.2's rung 2a is read by `check_apply_iter`, which runs inside `type_check_sorts`
/// — and the authoritative [`build_default_provider_index`] runs ~70 lines of pipeline
/// LATER, after `eq_derive::run`. Measured: with only the late build, every typer-site
/// flip in this rung's inventory stayed refused, because the index the tie consulted was
/// `None`. So the pass runs twice, over the provision relation as it stands at each point.
///
/// **THIS ONE'S VERDICT IS DISCARDED, AND THAT IS NOT A SILENT SKIP.** Rows are DERIVED
/// from provisions and provisions are only ever ADDED between the two calls (`eq_derive::
/// run` asserts, never retracts), so the late build's row set is a superset of this one's
/// and its error set is a superset too — every refusal this build could raise, that one
/// raises, with the derived provisions included. Collecting here instead would be the
/// unsound direction: check 1 would refuse a `DefaultProvider` naming a provider whose
/// only provision `eq_derive` has not asserted yet.
///
/// **WHAT THE TYPER THEREFORE CANNOT SEE** is a default row inferred from an `eq_derive`
/// derivation — i.e. a `PartialEq` / `NonEq` provision on a Float-containing composite.
/// That is exactly the coherent family (058 §3.7), whose ties are refused at LOAD by
/// `EqDispatchIndex` and never reach a rung; flip (4) of this ticket's inventory asserts
/// the family is untouched. The typer also runs against the pre-`eq_derive` PROVISION
/// relation itself, so seeding here reads the same relation the tie it serves was
/// computed from — aligned rather than merely early.
pub(crate) fn seed_default_provider_index(kb: &mut KnowledgeBase) {
    let _discarded = build_default_provider_index(kb);
}

/// One provision as this pass needs it: canonical keys for comparison, the provider's minted
/// name term for rendering, and where the provision is ([`typing::provision_carrier`]): its
/// carrier, that carrier's partition key, and whether it is the provider's own.
struct Provision {
    provider: Symbol,
    provider_name: TermId,
    spec: Symbol,
    carrier: TermId,
    key: Option<typing::CarrierBucket>,
    own: bool,
}

/// The row derivation proper.
fn derive_rows(
    kb: &KnowledgeBase,
    provisions: &[Provision],
    declared: &[(Symbol, Symbol)],
) -> (Vec<DefaultRow>, Vec<LoadError>) {
    let mut errors = Vec::new();
    let mut rows: Vec<DefaultRow> = Vec::new();

    // ── The DECLARED rows ────────────────────────────────────────────────────
    // Before the inferred ones, so a displacement diagnostic lists the declaration the
    // author wrote first and the inferred row it collides with second — the order the
    // repair reads in.
    for &(spec, provider) in declared {
        // CHECK 1 (058 §3.5, re-read at load). The predicate is the same
        // `impl_sorts_providing_spec` that `check_witness_provides_spec` asks at a
        // `[Spec = W]` bracket, because a `DefaultProvider` IS that bracket written once
        // for every silent site — so a provider that provides the spec nowhere is the
        // same typo one refusal over. It is load-bearing rather than merely helpful: the
        // row's CARRIER is derived from the provider's own provision, so without this a
        // mistyped mark would name no carrier and the row would silently vanish.
        let carriers = carriers_provided_by(provisions, spec, provider);
        if carriers.is_empty() {
            errors.push(LoadError::DefaultProviderDoesNotProvide {
                spec: kb.qualified_name_of(spec).to_string(),
                provider: kb.qualified_name_of(provider).to_string(),
                provides: typing::impl_sorts_providing_spec(kb, spec)
                    .into_iter()
                    .map(|s| kb.qualified_name_of(s).to_string())
                    .collect(),
            });
            continue;
        }
        // A provider may provide one spec at SEVERAL applications (the stdlib's
        // `Console provides Effect` ×3 — WI-842's bucketing case), so one mark yields
        // one row per application. That is the answer that composes: the mark says
        // "this provider is the default", and WHERE it is the default is whatever its
        // own provisions say — a conditional provision's row lands at the carrier its
        // clause WROTE (`List[T = E]`), which is all a default needs, since a default
        // only ever chooses among candidates that already resolved.
        // The provider's name TERM, reused from its own provision rather than minted:
        // `derive_rows` holds `kb` immutably, and CHECK 1 above has just established that
        // such a provision exists (`carriers` is non-empty), so the lookup is total. It is
        // what `render_row` prints the provider through, so that the provider and the
        // carrier go through ONE display walk — see [`DefaultRow::provider_name`].
        let provider_canon = kb.canonical_sort_sym(provider);
        let Some(provider_name) = provisions
            .iter()
            .find(|p| p.provider == provider_canon)
            .map(|p| p.provider_name)
        else {
            debug_assert!(
                false,
                "a declared mark passed CHECK 1 but names no provision to take its name term from"
            );
            continue;
        };
        for (carrier, key, own) in carriers {
            push_row(
                &mut rows,
                DefaultRow {
                    spec,
                    carrier,
                    key,
                    provider,
                    provider_name,
                    origin: DefaultOrigin::Declared,
                    own,
                },
            );
        }
    }

    // ── The INFERRED rows ────────────────────────────────────────────────────
    // "The provider's own provision is its default" (058 §3.6) — the clause that lets the
    // shipped standard library carry defaults with no edits at all. OWN is decision 6 of
    // `docs/design/spec-carrier-set.md`: the provider is the head of the carrier or of one of
    // its bindings, every binding counting.
    for p in provisions {
        if !p.own {
            // A WITNESS: its carrier names some other sort, a tuple or an arrow, so it is a
            // rival that may be MARKED default, never one that is inferred to be.
            continue;
        }
        push_row(
            &mut rows,
            DefaultRow {
                spec: p.spec,
                carrier: p.carrier,
                key: p.key,
                provider: p.provider,
                provider_name: p.provider_name,
                origin: DefaultOrigin::Inferred,
                own: true,
            },
        );
    }

    errors.extend(check_one_default(kb, &rows));
    (rows, errors)
}

/// Append `row` unless the SAME row is already present. Idempotence, not deduplication
/// of a conflict: a carrier that says twice that it provides one spec (`provides Desc[T =
/// Leaf]` beside a bare `provides Desc`, or a type-only provision COMPLETED by a
/// retroactive instance fact — WI-859's `(1, 0, 1)` cell) names ONE dictionary and must
/// yield ONE default row. Without this the completion shape would collide with itself
/// under `one_default`, refusing the very programs WI-431 exists to support. Both of
/// those spellings key the carrier at the provider, whose name term is minted once, so
/// they share a hash-consed id and collapse here.
///
/// SAME carrier, by term identity — NOT `carrier_views_overlap`. Overlap is
/// `one_default`'s question and it is deliberately coarser: `Box[T = E]` overlaps
/// `Box[T = Int64]`, so an overlap-keyed dedup would silently fold a provider's two
/// genuine provisions into one row while the anthill relation kept both — a divergence
/// the agreement test cannot see, since a collapsed row leaves no trace.
fn push_row(rows: &mut Vec<DefaultRow>, row: DefaultRow) {
    let dup = rows
        .iter()
        .any(|r| r.spec == row.spec && r.provider == row.provider && r.carrier == row.carrier);
    if !dup {
        rows.push(row);
    }
}

/// Every `fact DefaultProvider(spec: S, provider: W)` as `(spec sym, provider sym)`,
/// canonical, in fact order.
///
/// Both fields are SORT REFERENCES IN A FACT ARGUMENT — proven surface, and the same one
/// proposal 035's `fact Covariant(sort: List, param: T)` rides, which is why 058 §3.6
/// needs no grammar at all.
///
/// A row whose fields are not both NAME-LIKE is unreachable and says so with a
/// `debug_assert` rather than being waved through: the entity declares both as `Symbol`,
/// so a literal or a structured value is refused by the field-type check before this pass
/// runs, and a mark whose `provider` names a non-provider (an operation, another spec) is
/// name-like and reaches [`LoadError::DefaultProviderDoesNotProvide`] with the candidates
/// listed. Skipping silently here would leave an author with a default that does nothing
/// and no diagnostic — the one outcome check 1 exists to prevent.
fn declared_default_rows(kb: &KnowledgeBase) -> (Vec<(Symbol, Symbol)>, Vec<LoadError>) {
    let Some(entity) = kb.try_resolve_symbol("anthill.reflect.typing.DefaultProvider") else {
        return (Vec::new(), Vec::new());
    };
    let mut out = Vec::new();
    let mut errors = Vec::new();
    for rid in kb.rules_by_functor(entity) {
        // A DERIVED mark — `rule DefaultProvider(…) :- …` — is REFUSED, not skipped. The
        // SLD relation would answer from it while this reader (and both load checks)
        // would not, so the two halves of one relation would disagree; measured before
        // the refusal existed, such a program loaded clean with no row in the index.
        if !kb.is_fact(rid) {
            errors.push(LoadError::DerivedDefaultProvider {
                head: kb
                    .fact_head_term(rid)
                    .map(|t| typing::type_display_name(kb, t))
                    .unwrap_or_else(|| "DefaultProvider(…)".to_string()),
            });
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        // `sort_ref_functor`, not the spec-view reader: both fields are plain SORT
        // REFERENCES, the shape `variance_fact_params` reads for the `fact Covariant(sort:
        // List, param: T)` precedent this entity copies. `provides_spec_base_sym` peels a
        // `SortView` wrapper a symbol field never carries and does NOT peel the
        // `sort_ref(name: …)` wrapper a written symbol can.
        let field = |name: &str| {
            typing::get_named_arg(kb, &named, name)
                .and_then(|t| super::load::sort_ref_functor(kb, t))
                .map(|s| kb.canonical_sort_sym(s))
        };
        let (Some(spec), Some(provider)) = (field("spec"), field("provider")) else {
            debug_assert!(
                false,
                "a `DefaultProvider` fact whose `spec`/`provider` is not name-like reached \
                 the defaults pass — the field-type check was expected to refuse it first"
            );
            continue;
        };
        // Two IDENTICAL marks are one mark. Deduped here rather than left to `push_row`
        // so a duplicated bad mark reports check 1 ONCE.
        if !out.contains(&(spec, provider)) {
            out.push((spec, provider));
        }
    }
    (out, errors)
}

/// THE ONE OWNER of [`LoadError::DerivedDefaultProvider`]'s wording — see
/// [`ambiguous_default_message`] for why both faces read one function.
pub(crate) fn derived_default_provider_message(head: &str) -> String {
    format!(
        "`{}` is written as a RULE — 058 §3.6's defaults substrate reads `DefaultProvider` \
         FACTS, so a derived mark would answer through the `default_provider` relation while \
         staying invisible to `one_default` and to the materialized index: a default nothing \
         arbitrates. Write `fact DefaultProvider(spec: …, provider: …)`",
        head
    )
}

/// The carriers `provider`'s own provisions of `spec` are at — `(carrier, partition key)`.
///
/// This is where 058 §3.6's "the carrier is DERIVED from the provider's provision"
/// lives, and it is the whole reason conditionality composes for free: marking `ListOrd`
/// default yields a row at `Ord[T = List[T = E]]`, the exact carrier its provision claims, so
/// a conditional provision contributes a default at precisely the applications where the
/// provision itself holds.
fn carriers_provided_by(
    provisions: &[Provision],
    spec: Symbol,
    provider: Symbol,
) -> Vec<(TermId, Option<typing::CarrierBucket>, bool)> {
    let mut out: Vec<(TermId, Option<typing::CarrierBucket>, bool)> = Vec::new();
    for p in provisions {
        if p.spec != spec || p.provider != provider {
            continue;
        }
        // A mark naming a provider of its own provision is the inferred row said twice, which
        // `push_row` collapses — so a DECLARED row may stand at an own carrier too, which is why
        // the origin is stored rather than derived. Two carriers of one provider stay two
        // (`Console provides Effect` ×3, and equally `Box[T = E]` beside `Box[T = Int64]`); only
        // the identical carrier collapses — see [`push_row`] for why this is identity and not
        // overlap.
        if !out.iter().any(|&(c, _, _)| c == p.carrier) {
            out.push((p.carrier, p.key, p.own));
        }
    }
    out
}

/// 058 §3.6's `one_default` — two rows for one carrier must name one provider.
///
/// Compared at overlapping carriers ([`typing::carrier_views_overlap`]), the clause that
/// costs something: `List[T = E]` and `List[T = Int64]` are two rows describing carriers
/// in common, and admitting the pair would mean RANKING them by specificity at every
/// silent dispatch — a tier the ladder does not have. So the pair is refused rather than
/// the question inherited.
///
/// The cheap `(spec, key)` gate first, so the structural walk runs only for rows that can share
/// a carrier: two rows at one carrier bind the spec's first type-var to one bucket, or one of
/// them leaves it open ([`typing::default_row_key`]), so a differing key is a decided `false`
/// two compares in. The pairwise walk itself stays flat.
///
/// Each colliding PAIR is reported once and the list is sorted, so a program with two of
/// them reports the same two on every load — the rows are walked in fact order, which is
/// the loader's, not the author's.
fn check_one_default(kb: &KnowledgeBase, rows: &[DefaultRow]) -> Vec<LoadError> {
    let render = |r: &DefaultRow| {
        format!(
            "'{}' at carrier '{}' ({})",
            kb.qualified_name_of(r.provider),
            typing::carrier_display_name(kb, r.carrier),
            r.origin.label()
        )
    };
    let mut collisions: Vec<(&DefaultRow, &DefaultRow)> = Vec::new();
    for (i, a) in rows.iter().enumerate() {
        for b in &rows[i + 1..] {
            let keys_meet = match (a.key, b.key) {
                (Some(x), Some(y)) => x == y,
                _ => true,
            };
            if a.spec != b.spec || !keys_meet || a.provider == b.provider {
                continue;
            }
            // A mark choosing among providers each own at the carrier: the marked provider's
            // own provision beside another's inferred row (decision 6). The lookup takes the
            // mark ([`default_provider_for`]); a mark naming a WITNESS beside an own row is still
            // a displacement, refused below.
            let chooses_among_owns = |d: &DefaultRow, i: &DefaultRow| {
                d.origin == DefaultOrigin::Declared && d.own && i.origin == DefaultOrigin::Inferred
            };
            if chooses_among_owns(a, b) || chooses_among_owns(b, a) {
                continue;
            }
            if typing::carriers_meet(kb, a.carrier, b.carrier) {
                collisions.push((a, b));
            }
        }
    }
    collisions.sort_by_key(|(a, _)| {
        (
            kb.qualified_name_of(a.spec).to_string(),
            typing::carrier_display_name(kb, a.carrier),
        )
    });
    collisions
        .into_iter()
        .map(|(a, b)| {
            let (ca, cb) = (
                typing::carrier_display_name(kb, a.carrier),
                typing::carrier_display_name(kb, b.carrier),
            );
            LoadError::AmbiguousDefaultProvider {
                spec: kb.qualified_name_of(a.spec).to_string(),
                // AS RENDERED, not by term identity: `Ref(S)` and the nullary `Fn{S}` were
                // two spellings of one carrier and both occurred (measured; one term since
                // WI-20260902-JB6RS), and deciding on the rendered form still makes the arm
                // and the text agree by construction — if the message shows one carrier,
                // the arm is the one-carrier arm.
                collision: DefaultCollision::of(a, b, ca == cb),
                carrier: ca,
                providers: vec![render(a), render(b)],
            }
        })
        .collect()
}

/// WI-20261122-CXR5B — the lookup itself, at goals no call reaches yet: until a call's expected
/// type and the bindings it leaves open move (the ticket's later steps), a goal binding one
/// type-var of two is built only here.
#[cfg(test)]
mod lookup_tests {
    use super::*;
    use crate::eval::value::Value;

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("resolve {qn}"))
    }

    /// `Coll[C, Elem]` declared in the order given, `Foo`, and `decls`.
    fn program(ns: &str, first: &str, second: &str, decls: &str) -> String {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Coll
    sort {first} = ?
    sort {second} = ?
    operation first(c: C) -> Elem
  end
  sort Foo
    entity foo
  end
{decls}
end
"#
        )
    }

    /// What silence takes at `Coll[…]` bound as `at` gives, each `(type-var, sort)` by name.
    fn default_at(kb: &mut KnowledgeBase, ns: &str, at: &[(&str, &str)]) -> Option<String> {
        let spec = sym(kb, &format!("{ns}.Coll"));
        let bindings: Vec<(Symbol, Value)> = at
            .iter()
            .map(|(tv, sort)| {
                let s = sym(kb, sort);
                (sym(kb, &format!("{ns}.Coll.{tv}")), Value::term(kb.make_sort_ref(s)))
            })
            .collect();
        default_provider_for(kb, spec, CarrierKey::Goal(&bindings))
            .map(|p| kb.local_name_of(p).to_string())
    }

    /// A mark on a provider's OWN provision answers at its carrier, and a mark on a WITNESS at a
    /// carrier disjoint from it answers at its own; a goal meeting both (`Coll[C = Foo]`, `Elem`
    /// open) is the tie it was, the two marks being two answers. Before the review's fix the
    /// own mark took that goal too, every other meeting row dropped.
    #[test]
    fn an_own_mark_settles_only_the_rows_it_meets() {
        let ns = "cxr5b.marks";
        let src = program(
            ns,
            "C",
            "Elem",
            "  sort Num\n    entity num(v: Int64)\n    \
             default provides Coll[C = Foo, Elem = Self, first = Num.firstOf]\n    \
             operation firstOf(c: Foo) -> Num = num(v: 2)\n  end\n  \
             sort W\n    default provides Coll[C = Foo, Elem = Int64]\n    \
             operation first(c: Foo) -> Int64 = 1\n  end",
        );
        let mut kb = crate::kb::test_support::load_stdlib(Some(&src));
        let foo = format!("{ns}.Foo");
        let num = format!("{ns}.Num");
        assert_eq!(default_at(&mut kb, ns, &[("C", &foo), ("Elem", &num)]).as_deref(), Some("Num"));
        assert_eq!(
            default_at(&mut kb, ns, &[("C", &foo), ("Elem", "anthill.prelude.Int64")]).as_deref(),
            Some("W")
        );
        assert_eq!(default_at(&mut kb, ns, &[("C", &foo)]), None, "two marks meet `Coll[C = Foo]`");
    }

    /// A mark on a provision at a TYPE PARAMETER (`AnyC provides Coll[C = E, Elem = Int64]`, at
    /// every `C`) is no default at a sort, in either declaration order. Before the review's fix
    /// it answered `Coll[C = Foo, Elem = Int64]` with `Elem` declared first — the rows were then
    /// partitioned by `Elem`'s binding, and the overlap read `E` as any — and not with `C` first.
    #[test]
    fn a_mark_at_a_type_parameter_answers_no_sort_in_either_order() {
        for (ns, first, second) in [("cxr5b.anyc", "C", "Elem"), ("cxr5b.anye", "Elem", "C")] {
            let src = program(
                ns,
                first,
                second,
                "  sort AnyC\n    sort E = ?\n    default provides Coll[C = E, Elem = Int64]\n    \
                 operation first(c: E) -> Int64 = 1\n  end",
            );
            let mut kb = crate::kb::test_support::load_stdlib(Some(&src));
            let foo = format!("{ns}.Foo");
            assert_eq!(
                default_at(&mut kb, ns, &[("C", &foo), ("Elem", "anthill.prelude.Int64")]),
                None,
                "{ns}"
            );
        }
    }
}
