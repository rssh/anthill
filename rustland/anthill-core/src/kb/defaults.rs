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
//! that. The policy-free classifier is [`typing::witness_dispatch_carrier_view`] over
//! [`typing::all_provisions`], which is what both this module and the
//! `anthill.reflect.typing.dispatch_carrier` builtin behind the anthill rules call.
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
}

impl DefaultCollision {
    /// The ONE decision site, asked by the check rather than reasoned out at the message.
    fn of(a: &DefaultRow, b: &DefaultRow, same_carrier: bool) -> Self {
        if a.origin == DefaultOrigin::Inferred || b.origin == DefaultOrigin::Inferred {
            // Two INFERRED rows cannot collide: an inferred row's provider IS its carrier
            // base, so equal bases force equal providers and the pair never reaches here.
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
    /// The carrier as WRITTEN — `List[T = E]` for a conditional witness, a bare sort
    /// name for a self-provider. Kept as the view (not just its base) because
    /// `one_default` compares rows at unifiable carriers; see
    /// [`typing::carrier_views_overlap`].
    pub(crate) carrier: TermId,
    /// The carrier view's base sort, canonical — the key every DISPATCH reader uses,
    /// and so the key rung 2a (WI-861) will ask this index with.
    pub(crate) carrier_base: Symbol,
    /// The provider, canonical. Equal to `carrier_base` for every INFERRED row — and
    /// also for a DECLARED mark naming a self-provider, which is why the origin is
    /// stored rather than derived from that equality.
    pub(crate) provider: Symbol,
    pub(crate) origin: DefaultOrigin,
}

/// WI-860 — the materialized `default_provider` relation: 058 §3.6's rows, bucketed by
/// canonical carrier BASE.
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
#[derive(Default, Debug)]
pub struct DefaultProviderIndex {
    by_carrier_base: HashMap<Symbol, Vec<DefaultRow>>,
}

impl DefaultProviderIndex {
    /// Every default row for a carrier sort, in the order they were derived (declared
    /// rows first, then inferred). At most one survives the `one_default` check, so a
    /// caller on a successfully-loaded KB may treat a non-empty answer as singular —
    /// but the accessor hands back the list rather than an `Option`, so a consumer
    /// written against a KB whose errors were discarded sees the ambiguity instead of a
    /// silently-picked first.
    pub(crate) fn rows_for_carrier(&self, kb: &KnowledgeBase, carrier: Symbol) -> &[DefaultRow] {
        self.by_carrier_base
            .get(&kb.canonical_sort_sym(carrier))
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Every row, carrier-base order unspecified.
    pub(crate) fn rows(&self) -> impl Iterator<Item = &DefaultRow> {
        self.by_carrier_base.values().flatten()
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

    /// [`Self::rendered_rows`] for ONE carrier, WITH each row's origin — the half a
    /// no-displacement diagnostic prints, and the half that says whether a row was
    /// inferred from the carrier's own provision or written by hand.
    pub fn rendered_rows_for_carrier(&self, kb: &KnowledgeBase, carrier_qn: &str) -> Vec<String> {
        let Some(sym) = kb.try_resolve_symbol(carrier_qn) else {
            return Vec::new();
        };
        self.rows_for_carrier(kb, sym)
            .iter()
            .map(|r| render_row(kb, r, true))
            .collect()
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
        kb.local_name_of(r.provider)
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
pub(crate) enum CarrierKey {
    /// The carrier AS WRITTEN — what the provision tie in [`typing::resolve_inner`] has,
    /// since the goal carries its own bindings. **This is the arm that can tell `X[Y]`
    /// from `X[Z]`**: rows are per APPLICATION, so `List[T = Int64]` and `List[T =
    /// String]` are two rows sharing one bucket, and only [`typing::carrier_views_overlap`]
    /// separates them.
    View(TermId),
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
    carrier: CarrierKey,
) -> Option<Symbol> {
    let index = kb.default_provider_index()?;
    // The BUCKET KEY is derived, never supplied — see [`CarrierKey`]. `None` for a view
    // whose base is unreadable, which is the same decline the rung takes for a carrier it
    // cannot name at all. (`rows_for_carrier` canonicalizes, so neither arm does.)
    let (base, view) = match carrier {
        CarrierKey::View(v) => (typing::carrier_view_base(kb, v)?, Some(v)),
        CarrierKey::Base(s) => (s, None),
    };
    let spec_canon = kb.canonical_sort_sym(spec);
    let mut answer: Option<Symbol> = None;
    for row in index.rows_for_carrier(kb, base) {
        if row.spec != spec_canon {
            continue;
        }
        if let Some(v) = view {
            if !typing::carrier_views_overlap(kb, row.carrier, v) {
                continue;
            }
        }
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
    carrier: CarrierKey,
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
    let provisions: Vec<Provision> = typing::all_provisions(kb)
        .into_iter()
        .map(|p| {
            let provider = kb.canonical_sort_sym(p.provider);
            Provision {
                provider,
                provider_name: kb.make_name_term_from_sym(provider),
                spec: kb.canonical_sort_sym(p.spec),
                spec_decl: p.spec,
                spec_view: p.spec_view,
            }
        })
        .collect();
    let (declared, mut errors) = declared_default_rows(kb);

    let (rows, row_errors) = derive_rows(kb, &provisions, &declared);
    errors.extend(row_errors);
    let mut by_carrier_base: HashMap<Symbol, Vec<DefaultRow>> = HashMap::new();
    for row in rows {
        by_carrier_base
            .entry(row.carrier_base)
            .or_default()
            .push(row);
    }
    kb.set_default_provider_index(DefaultProviderIndex { by_carrier_base });
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

/// One provision as this pass needs it: canonical keys for comparison, the provider's
/// minted name term for the carrier-keyed case, and the spec AS DECLARED for the
/// classifier — which reads the spec's type parameters and so must be asked with the
/// symbol the declaration registered, not a canonical alias of it.
struct Provision {
    provider: Symbol,
    provider_name: TermId,
    spec: Symbol,
    spec_decl: Symbol,
    spec_view: TermId,
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
        let carriers = carriers_provided_by(kb, provisions, spec, provider);
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
        for (carrier, carrier_base) in carriers {
            push_row(
                &mut rows,
                DefaultRow {
                    spec,
                    carrier,
                    carrier_base,
                    provider,
                    origin: DefaultOrigin::Declared,
                },
            );
        }
    }

    // ── The INFERRED rows ────────────────────────────────────────────────────
    // "The carrier's own provision is its default" (058 §3.6) — the clause that lets the
    // shipped standard library carry defaults with no edits at all.
    for p in provisions {
        if typing::witness_dispatch_carrier_view(kb, p.spec_decl, p.provider, p.spec_view).is_some()
        {
            // A WITNESS: its carrier is some other sort, so it is a rival that may be
            // MARKED default, never one that is inferred to be.
            continue;
        }
        push_row(
            &mut rows,
            DefaultRow {
                spec: p.spec,
                carrier: p.provider_name,
                carrier_base: p.provider,
                provider: p.provider,
                origin: DefaultOrigin::Inferred,
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
        // REFERENCES, the shape `matches_variance_fact` reads for the `fact Covariant(sort:
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

/// The carriers `provider`'s own provisions of `spec` name — `(view, canonical base)`.
///
/// This is where 058 §3.6's "the carrier is DERIVED from the provider's provision"
/// lives, and it is the whole reason conditionality composes for free: marking `ListOrd`
/// default yields a row at `List[T = E]`, the exact carrier its provision claims, so a
/// conditional provision contributes a default at precisely the applications where the
/// provision itself holds.
fn carriers_provided_by(
    kb: &KnowledgeBase,
    provisions: &[Provision],
    spec: Symbol,
    provider: Symbol,
) -> Vec<(TermId, Symbol)> {
    let mut out: Vec<(TermId, Symbol)> = Vec::new();
    for p in provisions {
        if p.spec != spec || p.provider != provider {
            continue;
        }
        // `None` ⇒ the provider IS the carrier, i.e. the mark names a SELF-PROVIDER.
        // That row is inferred anyway, and marking it explicitly is not an error — it is
        // the same row said twice, which `push_row` collapses (so a DECLARED row may
        // carry `provider == carrier_base` too, which is why the origin is stored rather
        // than derived from that equality).
        let entry =
            match typing::witness_dispatch_carrier_view(kb, p.spec_decl, p.provider, p.spec_view) {
                Some(pair) => pair,
                None => (p.provider_name, p.provider),
            };
        // Two applications of one provider stay two carriers (`Console provides Effect`
        // ×3, and equally `Box[T = E]` beside `Box[T = Int64]`); only the identical
        // carrier collapses — see [`push_row`] for why this is identity and not overlap.
        if !out.iter().any(|&(v, _)| v == entry.0) {
            out.push(entry);
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
/// The cheap `(spec, carrier base)` gate first, so the structural walk runs only for rows
/// of ONE family: overlap requires a shared base, so a differing base is a decided `false`
/// two `Symbol` compares in. The pairwise walk itself stays flat — at the ~90 rows the
/// stdlib contributes, bucketing costs as many key comparisons as it saves.
///
/// Each colliding PAIR is reported once and the list is sorted, so a program with two of
/// them reports the same two on every load — the rows are walked in fact order, which is
/// the loader's, not the author's.
fn check_one_default(kb: &KnowledgeBase, rows: &[DefaultRow]) -> Vec<LoadError> {
    let render = |r: &DefaultRow| {
        format!(
            "'{}' at carrier '{}' ({})",
            kb.qualified_name_of(r.provider),
            typing::type_display_name(kb, r.carrier),
            r.origin.label()
        )
    };
    let mut collisions: Vec<(&DefaultRow, &DefaultRow)> = Vec::new();
    for (i, a) in rows.iter().enumerate() {
        for b in &rows[i + 1..] {
            if (a.spec, a.carrier_base) != (b.spec, b.carrier_base) || a.provider == b.provider {
                continue;
            }
            if typing::carrier_views_overlap(kb, a.carrier, b.carrier) {
                collisions.push((a, b));
            }
        }
    }
    collisions.sort_by_key(|(a, _)| {
        (
            kb.qualified_name_of(a.spec).to_string(),
            typing::type_display_name(kb, a.carrier),
        )
    });
    collisions
        .into_iter()
        .map(|(a, b)| {
            let (ca, cb) = (
                typing::type_display_name(kb, a.carrier),
                typing::type_display_name(kb, b.carrier),
            );
            LoadError::AmbiguousDefaultProvider {
                spec: kb.qualified_name_of(a.spec).to_string(),
                // AS RENDERED, not by term identity: `Ref(S)` and the nullary `Fn{S}` are
                // two spellings of one carrier and both occur (measured), so identity
                // would call one carrier two and print the OVERLAPPING wording over a
                // message naming the same carrier twice. Deciding on the rendered form
                // makes the arm and the text agree by construction — if the message shows
                // one carrier, the arm is the one-carrier arm.
                collision: DefaultCollision::of(a, b, ca == cb),
                carrier: ca,
                providers: vec![render(a), render(b)],
            }
        })
        .collect()
}
