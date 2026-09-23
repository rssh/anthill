//! Indexes over provision, requires and sort-info facts, and forwarded provisions
//! derived from them.

use super::*;

/// WI-661 (bucket-1 consolidation) — a reflect-fact index keyed by a canonical
/// sort/spec `Symbol`: one `HashMap<Symbol, Vec<RuleId>>` bucket map, built once per
/// load from a `rules_by_functor` scan, each bucket an order-preserving subsequence of
/// that scan (so first-match order is kept). This is the shared shape the per-fact
/// indexes previously hand-rolled — [`ProvidesIndex`] (two of these: spec-base and
/// carrier) and the SortInfo index (one, stored directly as
/// `KnowledgeBase::sort_info_index`). Identity is ALWAYS the canonical symbol
/// (`canonical_sort_sym`), never a last segment (WI-672, spec §8.6): two symbols with the
/// same qualified name collide into one bucket. WI-656 `op_records` (a rich per-op
/// record) and WI-659 [`SortAliasIndex`] (maps to `TermId` targets under string /
/// parent-sort keys) deliberately do NOT fold in — neither is a `Symbol → Vec<RuleId>`
/// bucket.
///
/// ONE DOCUMENTED EXCEPTION TO THE CANONICAL RULE, and it is not a relaxation of it:
/// [`crate::kb::KnowledgeBase::op_info_index`] (WI-20260912-1QVWA) keys `OperationInfo`
/// facts on the RAW `name` symbol, because the readers it serves compare
/// `op_info::head_name_ref(head) == Some(op_sym)` with raw `==` and `op_records` is keyed
/// under one spelling too. Canonicalizing THAT key would MERGE two distinct symbols
/// sharing a qualified name and flip a `None` to a `Some` — a behaviour change, where for
/// the sort relations canonicalizing is what makes the bucket exact. So the rule is "key
/// on whatever identity the consumer compares with", and for every sort-keyed index here
/// that is `canonical_sort_sym`. Check the consumer before changing a key; a key that does
/// not match its reader's comparison files facts in a bucket nobody looks in, which reads
/// as the relation being EMPTY for that symbol.
#[derive(Debug, Default, Clone)]
pub(crate) struct SymbolKeyedFactIndex {
    pub(super) buckets: HashMap<Symbol, Vec<crate::kb::RuleId>>,
}

impl SymbolKeyedFactIndex {
    /// The rids filed under `key_canon` (which the caller has already canonicalized),
    /// empty if none. Consumers still re-read each rid's field over the returned rids —
    /// the no-index fallback ([`Self::rids_or_scan`]) returns EVERY fact of the functor,
    /// so a per-fact re-filter is load-bearing there and stays at the call site.
    /// `key_canon` is canonical for every SORT-keyed index here; `op_info_index` passes a
    /// RAW operation symbol, by the exception stated on this type's doc. Whichever it is,
    /// it must be the identity the CALLER's per-fact comparison uses.
    pub(crate) fn get(&self, key_canon: Symbol) -> &[crate::kb::RuleId] {
        self.buckets.get(&key_canon).map_or(&[], |v| v.as_slice())
    }

    /// File `rid` under `key_canon`, appending so `rules_by_functor` order is preserved.
    /// Same keying rule as [`Self::get`], and it has to be the SAME key the lookup will
    /// use — canonical for the sort relations, raw for `op_info_index`.
    pub(crate) fn insert(&mut self, key_canon: Symbol, rid: crate::kb::RuleId) {
        self.buckets.entry(key_canon).or_default().push(rid);
    }

    /// The rids for a keyed lookup: the built index's `key_canon` bucket if present, else
    /// a live `rules_by_functor` scan of `functor_qn` (the pre-build / no-index fallback
    /// the load-time consumers hit before their index exists — it returns EVERY fact, so
    /// the caller keeps its own per-fact re-filter). `key_canon` must already be
    /// canonical. Collapses the identical fast-path/fallback selection every keyed
    /// consumer shared (`provides_rids_by_spec` / `_by_carrier`, `sort_info_rids_by_sort`,
    /// `requires_rids_by_sort`).
    ///
    /// WI-1112 — BOTH ARMS DROP RETRACTED RIDS, and the index arm has to say so
    /// explicitly. `rules_by_functor` is documented as "all ACTIVE (non-retracted)" and
    /// filters at query time; a bucket is frozen at build time, and no consumer's own
    /// re-filter covers the difference — `is_fact` reads `body_nodes.is_empty()` and
    /// answers `true` for a retracted slot just as happily as for a live one (the
    /// property `sort_info_index`' doc already warns about from the other side). Without
    /// this filter the two arms answer differently for exactly one input, so the
    /// invariant every one of these indexes rests on — "the index answers what the scan
    /// answers" — would be false, and the failure it produces is a PHANTOM row: for
    /// `requires_index`, a dictionary slot that outlives the declaration it came from.
    /// The cost is one bool per bucket entry, against a bucket of a handful and against the
    /// `to_vec` this replaced; MEASURED, alternating both arms in one process (11 pairs,
    /// release, whole stdlib load), the two distributions overlap completely — 102.8–122.1
    /// ms with the filter against 92.5–111.9 without — i.e. the difference is under this
    /// box's noise floor for one unchanged binary, and an order below what the index itself
    /// saves. `provides_index` and `sort_info_index` inherit the fix here for free.
    pub(super) fn rids_or_scan(
        kb: &KnowledgeBase,
        index: Option<&SymbolKeyedFactIndex>,
        key_canon: Symbol,
        functor_qn: &str,
    ) -> Vec<crate::kb::RuleId> {
        match index {
            Some(ix) => ix
                .get(key_canon)
                .iter()
                .copied()
                .filter(|rid| kb.is_rule_alive(*rid))
                .collect(),
            None => kb
                .try_resolve_symbol(functor_qn)
                .map(|s| kb.rules_by_functor(s))
                .unwrap_or_default(),
        }
    }
}

/// WI-660/WI-672 — the SortProvidesInfo (provider) index (see [`crate::kb::KnowledgeBase`]'s
/// `provides_index`). The provider relation, bucketed from BOTH endpoints so the
/// dispatch/coherence sites do a bucket lookup instead of scanning every provides
/// fact. BOTH directions now key on the CANONICAL sort symbol (`canonical_sort_sym`):
/// - `by_spec_base` keys on `canonical_sort_sym(spec_base)` — the spec-base sites
///   (`spec_has_any_providers`, `impl_sorts_providing_spec`, `collect_provides_candidates`)
///   compare with `canonical_sort_sym`, so an exact canonical key is faithful (both
///   drop a bare-interned spec base identically).
/// - `by_carrier` keys on `canonical_sort_sym(carrier)`. WI-672 re-keyed this from the
///   carrier's SHORT NAME (last segment) to its canonical symbol, and the carrier sites
///   now compare with `canonical_sort_sym` too (was `same_symbol`). A provider's
///   `sort_ref` carrier is the enclosing sort's resolved functor (`emit_*` /
///   `load_provides_clause` store `domain`), so canonical identity is exact — and it
///   de-conflates a top-level `sort Foo provides Bar` from a qualified `x.y.Foo` that
///   the former short-name bucket + `same_symbol` re-filter merged. Identity is by
///   symbol, never by last segment (spec §8.6). `build_provides_index` `debug_assert`s
///   that no carrier is an UNRESOLVED bare reference — the one shape canonical keying
///   could not bridge to a qualified form.
#[derive(Debug, Default, Clone)]
pub(crate) struct ProvidesIndex {
    /// Providers keyed by canonical spec base (`canonical_sort_sym(spec_base)`).
    by_spec_base: SymbolKeyedFactIndex,
    /// Providers keyed by canonical carrier (`canonical_sort_sym(carrier)`): the carrier
    /// is a resolved sort functor, so the canonical key IS the carrier identity.
    by_carrier: SymbolKeyedFactIndex,
    /// WI-864 — the same relation DECODED: canonical carrier → the `(rid, canonical spec
    /// base)` edges out of it, which is what [`provides_out_edges`] recomputes per hop of
    /// every transitive `sort_provides` walk. Two other buckets over the same facts would
    /// be redundant; this is not, because the cost it removes is the DECODE
    /// (`fact_head_named_args` + two `get_named_arg`s + `sort_ref_functor` +
    /// `provides_spec_base_sym` + two `canonical_sym` string hashes per fact), not the
    /// bucket lookup. Built in the SAME pass, by calling the very decode
    /// `provides_out_edges` uses, so the memo is that function computed once rather than a
    /// second spelling of it that could drift.
    ///
    /// The `rid` rides along because a bucket is frozen at build time while retraction is
    /// not — the reason [`SymbolKeyedFactIndex::rids_or_scan`] filters `is_rule_alive`,
    /// and the same filter applies here for the same reason.
    ///
    /// LIFECYCLE BY CONSTRUCTION: it lives INSIDE `ProvidesIndex`, so every point that
    /// drops `kb.provides_index` drops it, and the one builder fills it. There is no new
    /// invalidation surface to audit — which is the whole reason it is a field here rather
    /// than a cache of its own (cf. WI-1112, where a new index needed its producers
    /// enumerated, and WI-954, where a stale index answered EMPTY).
    pub(super) carrier_edges: HashMap<Symbol, SmallVec<[(crate::kb::RuleId, Symbol); 4]>>,
    /// WI-20260920-E3DC5 — the CONDITION relation (`ProvidesConditionInfo`), keyed by the
    /// canonical symbol of its `sort_ref` field's functor: the exact identity
    /// [`provision_conditions`] re-filters with (`same_sort_canonical`). That predicate
    /// answers about ONE sort and had no bucket to ask, so it walked every condition fact
    /// per call — 877 calls over a stdlib load, and the walk lengthens as the relation
    /// grows, which is the product both factors of `type_check_sorts`' cost were paying.
    ///
    /// MEASURED (release, stdlib + an empty namespace, `ANTHILL_LOAD_TIMING=1`, medians of
    /// 15 interleaved runs, both arms in ONE binary behind a switch so no binary-to-binary
    /// variance rides along). Forcing WI-20260919-HXGXF's `TypeValue` gate open — which
    /// asserts a condition row per parametric sort as well as a provision row per sort —
    /// grew `check_provider_requires`, this bucket's hottest consumer, by **+1.91 ms**
    /// without it and by **+0.65 ms** with it (6.05 → 7.96 ms against 5.66 → 6.31 ms).
    /// Per-call counters attribute that to `provision_conditions` itself: ~877 calls either
    /// way, whose total grew 2.8× for a 1.77× relation before the bucket and 1.4× after.
    ///
    /// A DIFFERENT RELATION IN THE SAME INDEX, and that is the point rather than an
    /// economy. Its validity window is `provides_index`' window EXACTLY, because the two
    /// relations have the same producers: every `ProvidesConditionInfo` fact is written
    /// beside the `SortProvidesInfo` fact it conditions — by the loader
    /// (`load_provides_conditions`, from a `provides … :- …` clause) or by
    /// `eq_derive::record_derived_conditions` (reached through `assert_derived_provision`,
    /// and from `eq_derive::run`'s `NonEq` mirror, which runs inside the same
    /// drop-and-rebuild bracket). So there is no window in which this bucket could be
    /// stale while `provides_index` is live, and — by `carrier_edges`' reasoning, which
    /// this follows deliberately — living INSIDE `ProvidesIndex` means every existing drop
    /// site drops it and the one builder fills it. A cache of its own would have added a
    /// fourth set of producers to audit (cf. WI-1112) for no separation that buys anything.
    conditions_by_carrier: SymbolKeyedFactIndex,
}

/// WI-660 — the provides-fact rids for a SPEC-BASE-keyed lookup: the `by_spec_base`
/// bucket when the index is built, else a live scan of every provides fact (the
/// pre-build / no-index fallback). Collapses the identical fast-path/fallback selection
/// the spec-base consumers share. The bucket keys on `canonical_sort_sym(base)`, so the
/// caller passes a canonical spec symbol; each consumer keeps its own per-fact filter.
pub(super) fn provides_rids_by_spec(
    kb: &KnowledgeBase,
    spec_canon: Symbol,
) -> Vec<crate::kb::RuleId> {
    SymbolKeyedFactIndex::rids_or_scan(
        kb,
        kb.provides_index.as_ref().map(|p| &p.by_spec_base),
        spec_canon,
        "anthill.reflect.SortProvidesInfo",
    )
}

/// WI-660/WI-672 — the provides-fact rids for a CARRIER-keyed lookup: the canonical-carrier
/// bucket when built, else a live scan. The bucket keys on `canonical_sort_sym(carrier)`, so
/// the caller passes the CANONICAL carrier — the transitive `provides` walk (WI-864)
/// canonicalizes once per walk and then carries canonical symbols, and relying on
/// `canonical_sym`'s idempotence per hop would make the extra call harmless, not free. The
/// one reader, [`provides_rows_of_provider_canon`], keeps the per-fact re-filter: the no-index
/// scan fallback returns EVERY provides fact, so the re-filter is load-bearing there.
pub(super) fn provides_rids_by_carrier_canon(
    kb: &KnowledgeBase,
    carrier_canon: Symbol,
) -> Vec<crate::kb::RuleId> {
    SymbolKeyedFactIndex::rids_or_scan(
        kb,
        kb.provides_index.as_ref().map(|p| &p.by_carrier),
        carrier_canon,
        "anthill.reflect.SortProvidesInfo",
    )
}

/// WI-20260923-32XFQ — ONE `anthill.reflect.SortProvidesInfo` fact, decoded: THE row reader
/// of the provision relation. Sixteen readers across the typer spelled this decode each for
/// itself — iterate the rids, skip a non-fact, read `sort_ref` → provider and `spec` → view
/// and base, `continue` on any missing field — and read it through [`provides_rows`],
/// [`provides_rows_of_provider`] and [`provides_rows_of_spec`] now. The two keyed forms
/// carry the per-fact canonical RE-FILTER their bucket needs, because the bucket's no-index
/// fallback returns EVERY provision fact: `self_supplied_entries` records a reader that
/// once forgot it (WI-660/672) and read another carrier's conversion as its own.
///
/// NOT read through here, deliberately: [`build_provides_index`], which files a rid under
/// each field INDEPENDENTLY (a fact with a readable `spec` and no readable `sort_ref` is still
/// in the spec bucket), and [`spec_has_any_providers`]' fallback scan, which answers what that
/// bucket answers. Both are keyed on one field; a row is all of them.
///
/// A row exists only when every field decodes. A VALUE-headed fact (a denoted-bearing spec)
/// has no term head and is not a row, as it was no row to any reader before: occurrence-
/// based provides lookup is gated effect-expressions-as-types work.
///
/// TWO DECODES STAY APART, because merging either one changes an answer:
///   * [`Self::provider`] is `sort_ref_functor`'s, which prefers a `sort_ref(name: …)` child;
///     two dispatch readers read the bare head instead — [`Self::sort_ref_head`].
///   * [`Self::spec_base`] is [`unwrap_spec_view`]'s. `crate::kb::load::provides_spec_base_sym`
///     also reads a DOTLESS `SortView` functor (a top-level `sort SortView`) as the view
///     wrapper, so its readers keep re-decoding the base from [`Self::spec_view`]. Every row
///     `unwrap_spec_view` refuses, that decode refuses too (the dotted-suffix test is one
///     half of its last-segment test), so such a reader skips exactly the rows it skipped.
#[derive(Clone, Debug)]
pub(super) struct ProvidesRow {
    pub(super) rid: crate::kb::RuleId,
    /// The `sort_ref`, RAW: the providing sort for a `provides` clause, the DERIVED carrier
    /// for a namespace-level instance fact. The PROVIDER, not the dispatch carrier — a
    /// witness names its carrier in the spec's bindings ([`witness_dispatch_carrier`]),
    /// though the index calls this key `carrier` ([`provides_rids_by_carrier_canon`]).
    pub(super) provider: Symbol,
    /// The `sort_ref` field as stored, for [`Self::sort_ref_head`].
    pub(super) sort_ref: TermId,
    /// The `spec` field: the full `SortView` term, or a bare spec reference.
    pub(super) spec_view: TermId,
    /// The spec's base sort, RAW.
    pub(super) spec_base: Symbol,
    /// The view's NAMED bindings, as [`unwrap_spec_view`] reads them — so a bare application
    /// (`Spec[T = X]` with no `SortView` wrapper) contributes none, and the view's
    /// POSITIONAL bindings are not here either. A reader that needs either reads
    /// [`Self::spec_view`] itself.
    pub(super) bindings: SmallVec<[(Symbol, TermId); 2]>,
}

impl ProvidesRow {
    /// The `sort_ref`'s bare HEAD functor, ignoring the `sort_ref(name: Ref(S))` child
    /// [`Self::provider`] prefers. [`impl_sorts_providing_spec`] and
    /// [`collect_provides_candidates`] decoded their impl sort this way and still do: the two
    /// reads differ only for a `sort_ref` carrying a `name:` argument, which nothing has
    /// minted since WI-361 — but a written reflect fact can, and reconciling the two is an
    /// answer changing, which is not a consolidation's to make. Total: a row's `sort_ref`
    /// passed `sort_ref_functor`, which admits exactly the `Fn` / `Ref` / `Ident` shapes read
    /// here.
    pub(super) fn sort_ref_head(&self, kb: &KnowledgeBase) -> Symbol {
        match kb.get_term(self.sort_ref) {
            Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => *functor,
            other => unreachable!(
                "a decoded provision row's sort_ref passed sort_ref_functor, which admits \
                 only Fn / Ref / Ident; got {other:?}"
            ),
        }
    }
}

/// WI-20260923-32XFQ — the fields every sort-clause reflect fact shares. `SortProvidesInfo`,
/// `SortRequiresInfo` and `ProvidesConditionInfo` are each a TERM-headed fact with a
/// `sort_ref` (the sort the clause is written on) and one more named field: `(owner through
/// `sort_ref_functor`, the `sort_ref` term, the field)`, or `None` for a rule, a value-headed
/// fact, or a missing field.
///
/// TERM-ONLY, and that is a skip rather than a decode: a value head has no `TermId`.
/// [`decoded_condition_row`] is the carrier-agnostic reader of the condition relation.
pub(super) fn sort_clause_fields(
    kb: &KnowledgeBase,
    rid: crate::kb::RuleId,
    field: &str,
) -> Option<(Symbol, TermId, TermId)> {
    if !kb.is_fact(rid) {
        return None;
    }
    let named = kb.fact_head_named_args(rid)?;
    let sort_ref = get_named_arg(kb, &named, "sort_ref")?;
    let owner = crate::kb::load::sort_ref_functor(kb, sort_ref)?;
    let value = get_named_arg(kb, &named, field)?;
    Some((owner, sort_ref, value))
}

/// [`ProvidesRow`]'s decoder: `None` for anything that is not a row, and for a row whose
/// provider `keep` refuses. Private, so a reader cannot pair it with a bucket and forget the
/// bucket's re-filter — the iterators below are the only doors.
///
/// `keep` is asked BEFORE the spec is unwrapped, because the provider-keyed reader's no-index
/// fallback hands it EVERY provision fact and a reader like `self_supplied_entries` runs once
/// per sort: unwrapping (and cloning the bindings of) every other carrier's row first would put
/// back a slice of the O(sorts × provisions) cost the carrier bucket exists to remove.
fn decode_provides_row(
    kb: &KnowledgeBase,
    rid: crate::kb::RuleId,
    keep: impl Fn(Symbol) -> bool,
) -> Option<ProvidesRow> {
    let (provider, sort_ref, spec_view) = sort_clause_fields(kb, rid, "spec")?;
    if !keep(provider) {
        return None;
    }
    let (spec_base, bindings) = unwrap_spec_view(kb, spec_view)?;
    Some(ProvidesRow {
        rid,
        provider,
        sort_ref,
        spec_view,
        spec_base,
        bindings,
    })
}

/// Every provision row, in relation order — a scan of the whole relation, and empty when
/// `SortProvidesInfo` is not declared at all.
pub(super) fn provides_rows(kb: &KnowledgeBase) -> impl Iterator<Item = ProvidesRow> + '_ {
    kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .map(|sym| kb.rules_by_functor(sym))
        .unwrap_or_default()
        .into_iter()
        .filter_map(move |rid| decode_provides_row(kb, rid, |_| true))
}

/// The rows whose PROVIDER is `provider` — the carrier-keyed bucket
/// ([`provides_rids_by_carrier_canon`]) with its re-filter built in: canonical sort identity,
/// [`same_sort_canonical`]'s.
pub(super) fn provides_rows_of_provider(
    kb: &KnowledgeBase,
    provider: Symbol,
) -> impl Iterator<Item = ProvidesRow> + '_ {
    provides_rows_of_provider_canon(kb, kb.canonical_sort_sym(provider))
}

/// [`provides_rows_of_provider`] for a caller that already holds the CANONICAL provider —
/// the transitive `provides` walk ([`provides_out_edges`]), which canonicalizes once per walk
/// rather than once per hop.
pub(super) fn provides_rows_of_provider_canon(
    kb: &KnowledgeBase,
    provider_canon: Symbol,
) -> impl Iterator<Item = ProvidesRow> + '_ {
    provides_rids_by_carrier_canon(kb, provider_canon)
        .into_iter()
        .filter_map(move |rid| {
            decode_provides_row(kb, rid, |p| {
                p == provider_canon || kb.canonical_sort_sym(p) == provider_canon
            })
        })
}

/// The rows providing `spec` — the spec-base bucket ([`provides_rids_by_spec`]) with its
/// canonical re-filter built in. The re-filter is not for show: the no-index fallback is
/// what the dispatch readers see today (`build_eq_dispatch_index` runs before
/// `build_provides_index`, and `eq_derive::run`'s caller nulls the index first), and it
/// returns EVERY provision fact.
pub(super) fn provides_rows_of_spec(
    kb: &KnowledgeBase,
    spec: Symbol,
) -> impl Iterator<Item = ProvidesRow> + '_ {
    let spec_canon = kb.canonical_sort_sym(spec);
    provides_rows_of_spec_in(kb, spec_canon, provides_rids_by_spec(kb, spec_canon))
}

/// WI-20260829-K0E8T — [`provides_rows_of_spec`] over rids the caller has already fetched
/// with [`provides_rids_by_spec`], for the one caller that must SEE the bucket before it
/// decides to walk it: [`witness_provides_admissibly`]'s gate, entered on the failure path
/// of every bare↔bare compatibility check, whose bucket is empty at 1263 of 1267
/// stdlib-load entries. Going through [`provides_rows_of_spec`] would canonicalize the spec
/// a second time (an FQN string hash) before it knows there is anything to compare.
///
/// The re-filter is CANONICAL, as the bucket is (WI-20260923-N3W68 #10): a provision whose
/// `SortView` base was resolved in another import scope is in the canonical bucket, and a
/// RAW compare then drops it — the silent no-op [`provider_spec_view_bindings`] warns of.
/// `collect_provides_candidates` compared raw until N3W68; a probe on "canonical-equal,
/// raw-different" fired zero times across the workspace suite, so that change served no
/// program newly.
pub(super) fn provides_rows_of_spec_in(
    kb: &KnowledgeBase,
    spec_canon: Symbol,
    rids: Vec<crate::kb::RuleId>,
) -> impl Iterator<Item = ProvidesRow> + '_ {
    rids.into_iter()
        .filter_map(move |rid| decode_provides_row(kb, rid, |_| true))
        .filter(move |row| kb.canonical_sort_sym(row.spec_base) == spec_canon)
}

/// WI-20260920-E3DC5 — ONE decoder for a `ProvidesConditionInfo` fact, shared by its three
/// readers: [`provision_conditions`], [`conditioned_provision_pairs`], and the
/// `conditions_by_carrier` bucket that [`build_provides_index`] fills.
///
/// EXTRACTED BECAUSE THE THIRD READER ARRIVED. Two of these existed as one function's body;
/// adding a bucket and a sweep would have made three copies of one criterion kept in step
/// by hand — the shape `carrier_edges`' doc refuses in so many words ("using the consumer's
/// own decode makes the memo the function, not a lookalike"), and the shape WI-838's
/// cross-kind blind spot came from. A bucket that decodes `sort_ref` even slightly
/// differently from the predicate reading out of it files facts where nobody looks, and
/// reads as the relation being EMPTY for that sort — which for this relation means a
/// conditional provision read as UNCONDITIONAL.
///
/// Carrier-agnostic throughout (`rule_head_value` + `head_field_term` / `head_field_value`),
/// and `sort_ref` through `sort_ref_functor` rather than a `Term::Fn` shape test:
/// `make_name_term_from_sym` applies the WI-511 canon and yields a `Ref` for a constructor
/// owner. The sibling reader `check_provider_requires` decodes the same field the same way.
///
/// `None` for a non-fact or a row missing any of the three fields — the rid is then in no
/// bucket AND invisible to both readers, which is the agreement that matters. The `clause`
/// index is NOT read here: only `provision_conditions` needs it, and it is the one field
/// whose absence is tolerated (it defaults) rather than disqualifying.
pub(super) fn decoded_condition_row(
    kb: &KnowledgeBase,
    rid: crate::kb::RuleId,
) -> Option<(Symbol, Symbol, Value)> {
    if !kb.is_fact(rid) {
        return None;
    }
    let head = kb.rule_head_value(rid);
    let sort_ref = crate::kb::op_info::head_field_term(kb, head, "sort_ref")?;
    let owner = crate::kb::load::sort_ref_functor(kb, sort_ref)?;
    let provided = crate::kb::op_info::head_field_value(kb, head, "provided")?;
    let condition = crate::kb::op_info::head_field_value(kb, head, "condition")?;
    let provided_base = spec_base_functor(kb, &provided)?;
    Some((owner, provided_base, condition))
}

/// WI-20260920-E3DC5 — the `ProvidesConditionInfo`-fact rids for a CARRIER-keyed lookup:
/// the canonical-`sort_ref` bucket when [`ProvidesIndex`] is built, else a live scan of
/// every condition fact (the pre-build / no-index fallback — which is the state the whole
/// derive block below `provides_index = None` runs in, by design). The bucket keys on
/// `canonical_sort_sym(sort_ref-functor)`, so the caller passes any sort symbol; the one
/// consumer keeps its per-fact `same_sort_canonical` re-filter, which is load-bearing on
/// the scan fallback because that arm returns EVERY condition fact.
pub(super) fn condition_rids_by_carrier(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
) -> Vec<crate::kb::RuleId> {
    SymbolKeyedFactIndex::rids_or_scan(
        kb,
        kb.provides_index.as_ref().map(|p| &p.conditions_by_carrier),
        kb.canonical_sort_sym(sort_sym),
        "anthill.reflect.ProvidesConditionInfo",
    )
}

/// WI-660/WI-672 — build the [`ProvidesIndex`] in ONE pass over the SortProvidesInfo facts:
/// `by_spec_base` keyed by canonical spec base, `by_carrier` by canonical carrier
/// (WI-672; see the struct doc). WI-20260920-E3DC5 adds a SECOND walk, over the
/// `ProvidesConditionInfo` facts, filling `conditions_by_carrier` — a different relation
/// with the same validity window, which is why it is built here and not on its own
/// schedule (the field's doc carries that argument). Called at TWO points in `load.rs`:
/// (1) `type_check_sorts` start — every provider that type-check itself needs already
/// exists (the loader/witness/instantiation passes all ran; `type_check` asserts none),
/// and type-check is the hot consumer; (2) again right after `eq_derive::run` (the only
/// LATER pass to assert provides facts — the derived composite `NonEq`/`PartialEq`), so
/// the second call folds those in for the post-eq_derive checks and the persisted
/// runtime index. Sound as a build-once-per-state index: after load, `SortProvidesInfo`
/// is `constant` (053/WI-665) so it never mutates at RUNTIME; the per-load-phase `None`
/// reset guards incremental loads. Mirrors the scan sites' extraction:
/// `get_named_arg("spec")` → `unwrap_spec_view` base, `get_named_arg("sort_ref")` →
/// `sort_ref_functor`.
pub(crate) fn build_provides_index(kb: &mut KnowledgeBase) {
    let Some(provides_sym) = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") else {
        return;
    };
    let mut by_spec_base = SymbolKeyedFactIndex::default();
    let mut by_carrier = SymbolKeyedFactIndex::default();
    // WI-864 — the decoded adjacency, filled from this same walk. See `carrier_edges`.
    let mut carrier_edges: HashMap<Symbol, SmallVec<[(crate::kb::RuleId, Symbol); 4]>> =
        HashMap::new();
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        if let Some(spec_tid) = get_named_arg(kb, &named, "spec") {
            if let Some((base, _)) = unwrap_spec_view(kb, spec_tid) {
                by_spec_base.insert(kb.canonical_sort_sym(base), rid);
            }
        }
        if let Some(sr_tid) = get_named_arg(kb, &named, "sort_ref") {
            if let Some(carrier) = crate::kb::load::sort_ref_functor(kb, sr_tid) {
                // WI-672: the carrier keys by canonical symbol. Two RESOLVED sort symbols
                // canonicalize equal iff they share a qualified name, so canonical keying
                // is exact for any resolved carrier — a top-level bare `sort Foo` keys
                // under itself and is queried under itself; a qualified carrier likewise.
                // The one shape canonical keying could NOT bridge is an UNRESOLVED bare
                // reference (`qualified_name_of` = its dotless raw name, no `by_qualified_name`
                // entry): the former `same_symbol` last-segment match papered over that,
                // canonical would misbucket it. A full-suite probe found ZERO bare-QN
                // carriers (resolved or not — every `provides` carrier is a qualified
                // enclosing sort, cf. WI-449), so this cannot arise today; assert it so a
                // future producer that regresses is LOUD, not a silent drop (repo rule).
                debug_assert!(
                    !matches!(
                        kb.symbols.get(carrier),
                        crate::intern::SymbolDef::Unresolved { .. }
                    ),
                    "WI-672: SortProvidesInfo carrier `{}` is unresolved — canonical re-key \
                     would misbucket it; resolve the `provides` carrier at its producer",
                    kb.qualified_name_of(carrier),
                );
                let carrier_canon = kb.canonical_sort_sym(carrier);
                by_carrier.insert(carrier_canon, rid);
                // WI-864: the out-edge, decoded once. `provides_spec_base_sym` and NOT the
                // `unwrap_spec_view` above, because this memoizes `provides_out_edges` —
                // whose spec decode is that one. The two agree on every shape the loader
                // emits, but "agree today" is not the invariant a memo may rest on: using
                // the consumer's own decode makes the memo the function, not a lookalike.
                if let Some(dst) = get_named_arg(kb, &named, "spec")
                    .and_then(|t| crate::kb::load::provides_spec_base_sym(kb, t))
                {
                    carrier_edges
                        .entry(carrier_canon)
                        .or_default()
                        .push((rid, kb.canonical_sort_sym(dst)));
                }
            }
        }
    }
    // WI-20260920-E3DC5 — the CONDITION bucket, over a second relation. A separate walk
    // and not a branch inside the one above: the two relations have different functors and
    // different fields, and the only thing they share is the window in which they are
    // valid (see `conditions_by_carrier`).
    //
    // `sort_ref_functor` and a CANONICAL key, matching the consumer arm for arm — the rule
    // [`SymbolKeyedFactIndex`] states: key on whatever identity the consumer compares
    // with, which here is `same_sort_canonical` over a `sort_ref_functor` read.
    // (`build_requires_index` matches `Term::Fn` because ITS consumer does; follow the
    // consumer, not the sibling builder.)
    //
    // NEITHER CHOICE IS DISTINGUISHED BY THE CORPUS TODAY, and that is recorded rather
    // than left for someone to assume otherwise: both mutations were MEASURED — bucketing
    // through a bare `Term::Fn` match, and keying on the raw symbol instead of the
    // canonical one — and the whole condition-index suite passes with either. Every
    // condition fact in a stdlib load has a `Term::Fn` `sort_ref` whose functor is already
    // canonical, because conditions are written on SORTS (a `Ref` comes from the WI-511
    // canon on a CONSTRUCTOR owner, and no `provides … :- …` has one). So these are
    // faithfulness choices, not defended positions: a future producer that writes a
    // constructor-owned or non-canonically-interned carrier would be served correctly by
    // this spelling and silently dropped by either other one — and a dropped fact here is
    // a provision read as UNCONDITIONAL, the `ProvisionConditionsTooWeak` over-claim minted
    // by an index. What IS pinned by a test is the carrier-agnostic head read; see below.
    let mut conditions_by_carrier = SymbolKeyedFactIndex::default();
    if let Some(cond_sym) = kb.try_resolve_symbol("anthill.reflect.ProvidesConditionInfo") {
        for rid in kb.rules_by_functor(cond_sym) {
            // THE CONSUMER'S OWN DECODE ([`decoded_condition_row`]), so the bucket holds
            // exactly the rids the readers can use — see that function for why all three
            // readers share it. A row it rejects is in no bucket AND invisible to the
            // readers, so the two arms still agree.
            //
            // The carrier-agnostic head read is load-bearing and is NOT justified by the
            // shipped derived rows — that claim was MEASURED AND IS FALSE, recorded here so
            // nobody re-derives it. A term-only `fact_head_named_args` builder was tried and
            // the whole condition-index suite still passed:
            // `eq_derive::record_derived_conditions` lowers every field through
            // `Value::term`, so its rows ARE term-carried. What fails is a head carrying a
            // denoted-bearing condition (a `Value::Node` inside the view, WI-662's shape on
            // the requires side) — `fact_head_named_args` is `None` for the whole head, the
            // fact lands in no bucket, and the provision silently reads UNCONDITIONAL.
            // Driven by `a_denoted_condition_fact_is_bucketed_not_dropped`, which builds
            // exactly that head because the loader cannot yet emit one.
            let Some((owner, _, _)) = decoded_condition_row(kb, rid) else {
                continue;
            };
            conditions_by_carrier.insert(kb.canonical_sort_sym(owner), rid);
        }
    }
    kb.provides_index = Some(ProvidesIndex {
        by_spec_base,
        by_carrier,
        carrier_edges,
        conditions_by_carrier,
    });
}

/// WI-1112 — the SortRequiresInfo-fact rids for a SORT-keyed lookup: the
/// canonical-`sort_ref` bucket when the index (a [`SymbolKeyedFactIndex`] stored directly
/// as `KnowledgeBase::requires_index`) is built, else a live scan of every
/// SortRequiresInfo fact (the pre-build / no-index fallback — and the state the index is
/// deliberately left in across every load-time mutation window). The bucket keys on
/// `canonical_sort_sym(sort_ref-functor)`, so the caller passes any sort symbol and the
/// lookup canonicalizes it; the one consumer keeps its own per-fact `same_sort_canonical`
/// re-filter, which is load-bearing on the scan fallback (it returns EVERY requires fact).
pub(super) fn requires_rids_by_sort(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
) -> Vec<crate::kb::RuleId> {
    SymbolKeyedFactIndex::rids_or_scan(
        kb,
        kb.requires_index.as_ref(),
        kb.canonical_sort_sym(sort_sym),
        "anthill.reflect.SortRequiresInfo",
    )
}

/// WI-1112 — build the SortRequiresInfo index (a [`SymbolKeyedFactIndex`]) in ONE pass
/// over the requires facts, bucketing each by the CANONICAL symbol of its `sort_ref`
/// field's functor — the exact key [`collect_sort_requires`] compares with
/// `same_sort_canonical`.
///
/// READ CARRIER-AGNOSTICALLY (`rule_head_value` + `op_info::head_field_term`), matching
/// the consumer arm for arm. This is not stylistic: a value-fact SortRequiresInfo — a
/// denoted-bearing spec, WI-662 — has NO `fact_head_named_args`, so building this the way
/// `build_sort_info_index` builds its own (term-only named args) would leave exactly those
/// facts in no bucket, and a bucket miss is a MISSING REQUIREMENT, not a slow answer.
/// Driven by `wi1112_requires_index_tests::a_denoted_requires_fact_is_bucketed_not_dropped`
/// — and NOT by `wi662_carrier_agnostic_requires_test`, which is where one would look
/// first: MEASURED, all three of its tests pass with the term-only builder in place,
/// because they read the chain immediately after `invalidate_requires_chain_cache` and so
/// measure the SCAN. The distinguishing assertion is that the index is `Some` at the read.
///
/// A `sort_ref` that is not a `Term::Fn` is left unbucketed, because the consumer matches
/// no other shape — the same faithfulness rule `build_sort_info_index` states for its
/// `name` field. Non-facts are skipped for the same reason (`anthill-cli`'s `run`
/// fixtures do write a bodied `rule SortRequiresInfo(…) :- …`, which the consumer's own
/// `is_fact` guard already excludes).
///
/// WHERE IT IS BUILT, AND WHY NOWHERE ELSE. `type_check_sorts` start, beside
/// `build_provides_index` / `build_sort_info_index`, and once more at the end of
/// `load_phase_inner` (after the last `invalidate_requires_chain_cache`) so the RUNTIME
/// readers inherit a live index. Both producers are done before the first of those:
/// `Loader::load_requires_decl` during the per-file load, and
/// `load::resolve_requires_bindings` — which RETRACTS and re-asserts, so a stale bucket
/// would serve a retracted rid — inside `resolve_instantiations`. A
/// `LoadOptions { run_typer: false }` load runs both of those and NO type-check, so it
/// deliberately gets no build at all: `load_phase_inner` resets the index at its start and
/// the partial path returns above both build points, leaving it `None`, i.e. scanning.
/// (That partial shape was a separate `load::load` entry point until WI-20260901-Q68AK;
/// the rule is unchanged, the door is now an option on the one pipeline.)
///
/// A future producer that runs after a build must call
/// `KnowledgeBase::invalidate_requires_chain_cache`, which drops this index — the one
/// invalidation point, shared with the chain caches computed from the same relation.
pub(crate) fn build_requires_index(kb: &mut KnowledgeBase) {
    let Some(requires_sym) = kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo") else {
        return;
    };
    let mut index = SymbolKeyedFactIndex::default();
    for rid in kb.rules_by_functor(requires_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head_value(rid);
        let Some(sort_ref_tid) = crate::kb::op_info::head_field_term(kb, head, "sort_ref") else {
            continue;
        };
        // `sort_ref_functor`, the provides side's decoder — see `collect_sort_requires`,
        // the scan this bucket must agree with, for why not a `Term::Fn` shape test.
        let Some(sr_functor) = crate::kb::load::sort_ref_functor(kb, sort_ref_tid) else {
            continue;
        };
        index.insert(kb.canonical_sort_sym(sr_functor), rid);
    }
    kb.requires_index = Some(index);
}

/// WI-671/WI-672 — the SortInfo-fact rids for a sort-keyed lookup: the canonical-sort
/// bucket when the index (a [`SymbolKeyedFactIndex`] stored directly as
/// `KnowledgeBase::sort_info_index`) is built, else a live scan of every SortInfo fact
/// (the pre-build / no-index fallback the load-time consumers hit). Collapses the
/// identical fast-path/fallback selection the four keyed consumers share; each keeps its
/// own per-fact `name` read over the returned rids.
pub(crate) fn sort_info_rids_by_sort(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
) -> Vec<crate::kb::RuleId> {
    SymbolKeyedFactIndex::rids_or_scan(
        kb,
        kb.sort_info_index.as_ref(),
        kb.canonical_sort_sym(sort_sym),
        "anthill.reflect.SortInfo",
    )
}

/// WI-671/WI-672 — build the SortInfo index (a [`SymbolKeyedFactIndex`]) in ONE pass over
/// the SortInfo facts, bucketing each by the CANONICAL sort symbol (`canonical_sort_sym`)
/// of its `name` field. `SortInfo.name` is always a resolved sort functor (`emit_sort_info`
/// emits `Term::Ref(sort_functor)`), so its canonical symbol IS the sort identity — an
/// exact key that de-conflates two DISTINCT sorts merely sharing a last segment (spec §8.6;
/// see `KnowledgeBase::sort_info_index`). Called at `type_check_sorts` start beside
/// `build_provides_index`, when every SortInfo fact is asserted and the relation is frozen
/// for the rest of the load. Value-fact heads (no named args) are skipped, as every keyed
/// consumer skips them.
///
/// WI-1008 — `emit_sort_info` is no longer the SOLE producer: `merge_secondary_entry_operations`
/// re-asserts a sort's record to add the operations its SECONDARY ENTRIES declare (059 R2).
/// Build-once stays sound because that pass runs in `resolve_instantiations`, strictly
/// before this call, and it drops `sort_info_index` when it rewrites — so nothing this
/// builds from can be a retracted slot. A future writer that runs AFTER this point must
/// drop the index too; a retracted RuleId left in a bucket is served, not detected
/// (`is_fact` reads a retracted slot happily).
pub(crate) fn build_sort_info_index(kb: &mut KnowledgeBase) {
    let Some(sort_info_sym) = kb.try_resolve_symbol("anthill.reflect.SortInfo") else {
        return;
    };
    let mut index = SymbolKeyedFactIndex::default();
    for rid in kb.rules_by_functor(sort_info_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        let Some(name_tid) = get_named_arg(kb, &named, "name") else {
            continue;
        };
        // The `name` field's Symbol, across the shapes the consumer reads: a bare `Ref`
        // (what `emit_sort_info` always emits) or a `Fn` head's functor (the consumers'
        // defensive read). Any other shape is matched by no consumer, so leaving it
        // unbucketed is faithful.
        let name_sym = match kb.get_term(name_tid) {
            Term::Ref(s) => *s,
            Term::Fn { functor, .. } => *functor,
            _ => continue,
        };
        index.insert(kb.canonical_sort_sym(name_sym), rid);
    }
    kb.sort_info_index = Some(index);
}

/// WI-325 — true iff at least one `SortProvidesInfo` fact exists whose
/// spec base matches `spec_sort`, regardless of whether the bindings
/// match any particular per-call goal. Used as one leg of
/// `spec_warrants_abstract_check`.
///
/// WI-617 — both sides are compared under `canonical_sort_sym`, matching the
/// sibling `impl_sorts_providing_spec`. A sort interns under multiple `Symbol`
/// ids (bare vs qualified); a provider fact's spec base may intern under a
/// non-canonical symbol relative to the queried `spec_sort`. A raw `==` would
/// then read false, `carrier_is_abstract_spec` would return false, and the
/// abstract-spec-carrier dispatch gates (WI-598/601/608/609/614) would spuriously
/// skip — regressing a legitimately-abstract spec value to a loud dispatch error.
pub(super) fn spec_has_any_providers(kb: &KnowledgeBase, spec_sort: Symbol) -> bool {
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    // WI-660 fast path: "any provider of this spec?" is a non-empty spec-base bucket
    // in the provider index (built once at type-check start; the bucket keys on the
    // SAME `canonical_sort_sym(base)` this scan compares, so non-empty ⟺ a match).
    if let Some(index) = &kb.provides_index {
        return !index.by_spec_base.get(spec_canon).is_empty();
    }
    // Fallback: the linear scan, for a call before the index is built.
    let Some(provides_sym) = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") else {
        return false;
    };
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        // A value-fact SortProvidesInfo (denoted-bearing spec) is skipped here;
        // occurrence-based provider lookup is gated effect-expressions-as-types
        // work (avoid the term-only `rule_head` panic on a value head).
        let Some(head_named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        let spec_view_tid = match get_named_arg(kb, &head_named, "spec") {
            Some(t) => t,
            None => continue,
        };
        if let Some((view_base_sym, _)) = unwrap_spec_view(kb, spec_view_tid) {
            if kb.canonical_sort_sym(view_base_sym) == spec_canon {
                return true;
            }
        }
    }
    false
}

/// WI-598 — true iff `carrier_sym` is itself an ABSTRACT spec sort: it has no
/// entity constructors of its own (no concrete representation) AND other sorts
/// `provides` it (it is an interface, not just an empty concrete sort). A value
/// whose static type is such a sort — e.g. `FiniteStream`, the declared return of
/// the finite `map`/`filter` — is really some concrete provider, so a body-less
/// carrier-param spec op on it must DEFER to eval's value-directed dispatch rather
/// than resolve the spec sort's OWN `requires` chain (which `FiniteStream provides
/// Stream → Stream requires EffectsRuntime[E]` leaves unsatisfiable at an abstract
/// access row). The constructor check keeps a CONCRETE carrier that happens to
/// provide a spec (a `List`, whose nil/cons make it concrete) on the concrete
/// dispatch path; the provider check keeps a constructor-less but non-spec sort
/// (none today) from silently deferring.
///
/// `sort_has_constructors` is the canonical data-sort-vs-spec predicate (qualified-
/// name based, so canonical-insensitive); `carrier_sym` is canonicalized before the
/// provider check so a non-canonical interning of the same logical sort still
/// matches its `SortProvidesInfo` facts.
///
/// WI-20260831-PYNS2 — ONE CALLER DELIBERATELY ASKS ITS QUESTION ABOVE THIS PREDICATE.
/// [`carrier_param_receiver`]'s WI-609 REFLEXIVE arm (carrier == the spec declaring the
/// called operation) keeps the constructor leg and drops the PROVIDER one, because
/// spec-hood is settled there by construction and the "non-spec sort" the provider leg
/// guards against cannot be the answer. Under the whole predicate, a spec no carrier
/// provides YET could not read its own row parameter off a receiver's written type
/// argument. Every other caller wants both legs.
pub(super) fn carrier_is_abstract_spec(kb: &KnowledgeBase, carrier_sym: Symbol) -> bool {
    let canon = kb.canonical_sort_sym(carrier_sym);
    !kb.sort_has_constructors(canon) && spec_has_any_providers(kb, canon)
}

/// WI-1109 — a kb-free comparable key for ONE provision/requires binding, so the sites
/// that must ask "the same bindings?" cannot drift into asking it three ways. The key is
/// the parameter's LOCAL name (spec parameters are named per spec, and the identity
/// forwarding relates them by name) paired with the value's canonical sort symbol when
/// the value heads a sort, else its hash-consed `TermId`. Deliberately not the raw
/// `TermId` alone: two structurally-equal bindings written in two places need not share
/// one id, and a hand-written row must be recognised as covering a derived one.
pub(super) fn binding_key(kb: &KnowledgeBase, name: Symbol, value: TermId) -> (String, String) {
    binding_key_named(kb, kb.local_name_of(name), value)
}

/// [`binding_key`] for a binding already held by its parameter's LOCAL NAME — the shape
/// WI-1111's translated derivation rows carry, since a mapped target parameter has no
/// symbol on the source row to borrow.
fn binding_key_named(kb: &KnowledgeBase, name: &str, value: TermId) -> (String, String) {
    (name.to_string(), binding_value_key(kb, value))
}

/// The VALUE half of [`binding_key_named`], and it must descend (WI-1111 review).
///
/// A first form matched `Term::Fn { functor, .. }` and kept only the base, so
/// `Box[E = Int64]` and `Box[E = Bool]` keyed ALIKE. [`bindings_cover_named`] then read a
/// hand-written row at one argument as COVERING the derived row needed at another,
/// [`forwarded_rows_to_derive`] skipped it, and — because
/// [`collect_provides_candidates`] has already excluded the conversion — the answer was
/// DELETED rather than relocated. That is the one invariant this whole exclusion rests
/// on. MEASURED: with a written `C provides Low[T = Box[E = Bool]]` beside
/// `C provides Top[T = Box[E = Int64]]`, the load FAILED with "'C' provides 'Top', which
/// requires 'Low', but 'C' does not provide 'Low'". Driven by
/// `a_sibling_row_at_other_arguments_does_not_suppress_the_derived_one`.
///
/// A NULLARY `Fn` KEYS AS ITS `Ref` DOES, deliberately: the loader writes a bare name
/// both ways (WI-224/WI-359's `substitute_impl_params_alloc` note), so collapsing them is
/// what keeps the two encodings of one sort comparing equal.
fn binding_value_key(kb: &KnowledgeBase, value: TermId) -> String {
    match kb.get_term(value) {
        Term::Ref(functor) | Term::Ident(functor) => kb
            .qualified_name_of(kb.canonical_sort_sym(*functor))
            .to_string(),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            let base = kb
                .qualified_name_of(kb.canonical_sort_sym(*functor))
                .to_string();
            if pos_args.is_empty() && named_args.is_empty() {
                return base;
            }
            let mut out = base;
            out.push('[');
            for (i, arg) in pos_args.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&binding_value_key(kb, *arg));
            }
            for (n, v) in named_args.iter() {
                if !out.ends_with('[') {
                    out.push(',');
                }
                out.push_str(kb.local_name_of(*n));
                out.push('=');
                out.push_str(&binding_value_key(kb, *v));
            }
            out.push(']');
            out
        }
        _ => format!("#{value:?}"),
    }
}

/// True iff `covering` binds everything `asked` binds, to the same values.
///
/// COVERAGE AND NOT EQUALITY, which a first draft got wrong and the suite caught: a
/// `requires` entry's spec view carries the spec's OPERATION bindings beside its type
/// parameters — MEASURED, `Ord requires PartialOrd[T]` decodes as
/// `[T, gt, gte, lt, lte]` — while a goal carries only what it asks about (`[T]`). An
/// equal-length test therefore refused every real entry while claiming to be precise.
/// Coverage keeps the property that matters: a binding the asker names must be present
/// AND agree, so an entry bound to a DIFFERENT parameter cannot answer.
/// The ASKED side is keyed by LOCAL NAME because a derived row's bindings are
/// TRANSLATED through the forwarding's parameter map (WI-1111) and a mapped target
/// parameter has no symbol on the source row to borrow; the COVERING side is a decoded
/// row and keys by `Symbol`. Both go through [`binding_key_named`], so the comparison is
/// the one it always was.
fn bindings_cover_named(
    kb: &KnowledgeBase,
    covering: &[(Symbol, TermId)],
    asked: &[(String, TermId)],
) -> bool {
    asked.iter().all(|(an, av)| {
        let ak = binding_key_named(kb, an.as_str(), *av);
        covering
            .iter()
            .any(|(cn, cv)| binding_key(kb, *cn, *cv) == ak)
    })
}

/// [`bindings_cover_named`] with BOTH sides keyed by local name — comparing two pending
/// derivation rows.
fn bindings_cover_named_pairs(
    kb: &KnowledgeBase,
    covering: &[(String, TermId)],
    asked: &[(String, TermId)],
) -> bool {
    asked.iter().all(|(an, av)| {
        let ak = binding_key_named(kb, an.as_str(), *av);
        covering
            .iter()
            .any(|(cn, cv)| binding_key_named(kb, cn.as_str(), *cv) == ak)
    })
}

/// WI-1109 — the local name of a value that IS an abstract type parameter, or `None`
/// when it is anything else. The name half of [`is_type_param_value`], which answers
/// only the shape; both forms this reads (`Ref`/`Ident`, and the WI-359 nullary `Fn`)
/// are the ones that predicate accepts.
pub(super) fn type_param_local_name(kb: &KnowledgeBase, value: TermId) -> Option<&str> {
    // The `is_sort_param_symbol` guard is NOT optional and its omission was a real hole
    // (review of WI-1109): reading the local name alone accepts a binding to a CONCRETE
    // sort whenever that sort's name happens to equal the spec parameter's, so
    // `provides Sp[T = T]` with a real nullary sort `T` in scope would read as an
    // identity forwarding and derive rows at the wrong bindings. Same arms, same
    // predicate as [`is_type_param_value`] — this only adds the NAME to the answer.
    let sym = match kb.get_term(value) {
        Term::Ref(sym) | Term::Ident(sym) => *sym,
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => *functor,
        _ => return None,
    };
    is_sort_param_symbol(kb, sym).then(|| kb.local_name_of(sym))
}

/// WI-1109/WI-1111 — is this provision a PARAMETER FORWARDING, and if so WHICH of the
/// subject's type parameters does each of the target's stand for? A row
/// `F provides S[p = q, …]` whose every binding sends one of `S`'s parameters to an
/// abstract type parameter of `F`. `Ord provides WeakOrd[T = T]` is the shipped one;
/// `F provides Sp[X = A]` (a renaming) and `F provides Sp[X = B, Y = A]` (a permutation)
/// are the same relation written with different letters.
///
/// THE MAP IS THE SOUNDNESS ARGUMENT, not a convenience. Because every target parameter
/// stands for exactly one subject parameter, a goal at `S` holds at the bindings the same
/// goal at `F` does READ THROUGH THE MAP, so [`derive_forwarded_provisions`] may translate
/// a carrier's bindings. A row binding a target parameter to a CONCRETE sort is
/// deliberately not a forwarding: `Int64 provides Ord[T = Int64]` is a claim about the
/// world, and translating nothing is exactly what makes it one.
///
/// WI-1109 SHIPPED THIS AS AN IDENTITY TEST — name-for-name — because copying bindings
/// needs no map. WI-1111 measured what the identity cost: with `F provides Sp[X = A]`
/// nothing was derived for a carrier of `F`, nothing classified the row a conversion, so
/// `F` itself was offered as the impl sort for EVERY `Sp` goal (its own parameters being
/// wildcards, the permuting form answered the mirrored goal too), the program loaded
/// clean and died at eval with `OperationBodyMissing`. Translating is the whole
/// difference, and it is the same three lines the identity form used to skip.
///
/// The keys are LOCAL NAMES on both sides for the reason `direct_requires`' dedup gives:
/// the same parameter reaches this function under different symbols depending on which
/// loader path wrote the row.
pub(super) fn forwarding_param_map(
    kb: &KnowledgeBase,
    carrier: Symbol,
    base: Symbol,
    bindings: &[(Symbol, TermId)],
) -> Option<Vec<(String, String)>> {
    if !is_param_forwarding(kb, carrier, base, bindings) {
        return None;
    }
    Some(
        bindings
            .iter()
            .map(|(name, value)| {
                (
                    kb.local_name_of(*name).to_string(),
                    type_param_local_name(kb, *value)
                        .expect("is_param_forwarding checked every binding")
                        .to_string(),
                )
            })
            .collect(),
    )
}

/// [`forwarding_param_map`] asked as a yes/no — the shape half, for readers that need
/// only to know the row forwards rather than where each parameter goes.
///
/// SEPARATE FROM THE MAP RATHER THAN `map(..).is_some()`, and deliberately: this is the
/// first conjunct of [`provision_is_conversion`], which runs for every provision row of
/// every sort whose chain is built, and building the map allocates a `String` pair per
/// binding. The measurements already recorded in this pass — a scanning
/// `self_supplied_entries` costing 80 % of a stdlib load, an un-hoisted decode costing 61×
/// — are what makes an allocation on that path worth avoiding.
pub(super) fn is_param_forwarding(
    kb: &KnowledgeBase,
    carrier: Symbol,
    base: Symbol,
    bindings: &[(Symbol, TermId)],
) -> bool {
    !bindings.is_empty()
        && !same_sort_canonical(kb, carrier, base)
        && bindings
            .iter()
            .all(|(_, value)| type_param_local_name(kb, *value).is_some())
}

/// One decoded `SortProvidesInfo` row, for WI-1109's derivation pass. Named apart from
/// the module's existing `ProvisionRow` (which carries a provider and a spec VIEW) —
/// this one is the raw (carrier, spec base, bindings) triple the pass indexes on.
struct DecodedProvision {
    pub(super) carrier: Symbol,
    pub(super) base: Symbol,
    pub(super) bindings: SmallVec<[(Symbol, TermId); 2]>,
}

/// WI-1109 — every provision row, decoded ONCE.
///
/// The pass runs with `kb.provides_index` dropped (it asserts into the relation it
/// reads), so each per-row helper it used to call degraded to a full scan of every
/// provision fact — and it called three of them per row per round: O(rounds × rows ×
/// relation). Decoding once and indexing makes it O(rounds × relation).
///
/// MEASURED, not reasoned (`ANTHILL_LOAD_TIMING=1` over the stdlib): the per-row shape
/// cost **266.8 ms** and this one costs **4.4 ms** — 61×, against a whole-load budget of
/// roughly 135 ms, so the un-hoisted pass very nearly tripled the time to load the
/// standard library. The control was the same loop with the indexes rebuilt inside it;
/// if anything it UNDERSTATES the original, which also re-scanned for the
/// already-provided check.
fn decoded_provision_rows(kb: &KnowledgeBase) -> Vec<DecodedProvision> {
    provides_rows(kb)
        .map(|row| DecodedProvision {
            carrier: kb.canonical_sort_sym(row.provider),
            base: kb.canonical_sort_sym(row.spec_base),
            bindings: row.bindings,
        })
        .collect()
}

/// The (carrier, provided-spec) pairs whose provision carries a `:- goals` tail, from ONE
/// sweep of the condition facts. A conditional provision neither forwards nor is forwarded
/// through — see [`derive_forwarded_provisions`].
///
/// ONE SWEEP IS WHAT THIS SAYS AND, SINCE WI-20260920-E3DC5, WHAT IT DOES. The body used
/// to call [`provision_conditions`] once PER CARRIER, and that predicate walks the WHOLE
/// `ProvidesConditionInfo` relation to answer about one sort — so the "one sweep" the
/// comment promised was in fact `carriers × conditions`, a product of two quantities that
/// BOTH grow with the program.
///
/// MEASURED AT FOUR SIZES, not inferred from the shape. A generated fixture of `n` carriers,
/// each writing one unconditional provision of a forwarder and one conditional provision
/// (so carriers AND conditions grow together, as they do when a derivation pass adds rows),
/// timed at the `derive_forwarded_provisions` mark. Two release binaries — this commit's
/// parent and this commit — run interleaved, medians of 5:
///
/// ```text
///   n       50     100     200     400       ×8 input   last doubling   exponent
///   before  3.26    7.83   23.96   82.06 ms    ×25.2        ×3.43          1.78
///   after   0.59    0.80    1.42    2.77 ms     ×4.7        ×1.95          0.96
/// ```
///
/// Before, each doubling multiplies the time by 2.41 → 3.06 → 3.43, climbing toward the ×4
/// of a pure quadratic as the fixed stdlib base cost washes out. After: 1.35 → 1.78 → 1.95,
/// climbing toward the ×2 of a linear pass. At `n = 400` this pass is 30× faster.
///
/// ON THE REAL STDLIB (release, + an empty namespace, medians of 15 interleaved runs):
/// forcing WI-20260919-HXGXF's `TypeValue` gate open takes the relation 219 → 387 rows and
/// the carrier list 101 → 180 (1.78×) while ALSO asserting a condition row per parametric
/// sort — and the pass went 0.51 → 2.04 ms, i.e. it grew by **4×** for a 1.78× input,
/// because the cost is the PRODUCT and not either factor. With this rewrite the same
/// comparison is 0.25 → 0.36 ms: the growth is 93 % gone, and per-step marks put the step
/// this function owns at 51 % of the pass before and under 10 % after.
///
/// THE CARRIER FILTER IS GONE WITH THE LOOP, and dropping it changes no answer: the only
/// reader asks `contains((r.carrier, r.base))` for rows `r` of the very relation the
/// carrier list was distilled from, so every pair it can ask about is one this collects.
/// Collecting the rest costs a `HashSet` entry per conditioned provision and saves
/// building the carrier list at all.
///
/// The emptiness test the per-carrier form applied (`!pc.conditions.is_empty()`) is not
/// lost either — it was already vacuous. [`provision_conditions`] creates a group only
/// when it has decoded a `condition` field to seed it with, so every group it returns has
/// at least one. Here the fact IS the condition, which is why the decode below reads the
/// field and then only checks that it is present.
pub(super) fn conditioned_provision_pairs(
    kb: &KnowledgeBase,
) -> std::collections::HashSet<(Symbol, Symbol)> {
    let mut out = std::collections::HashSet::new();
    let Some(cond_sym) = kb.try_resolve_symbol("anthill.reflect.ProvidesConditionInfo") else {
        return out;
    };
    for rid in kb.rules_by_functor(cond_sym) {
        // [`decoded_condition_row`] and not a second spelling of it: this set is consulted
        // INSTEAD of asking [`provision_conditions`], so a row that predicate would have
        // decoded and this one skipped is a conditional provision read as unconditional.
        let Some((owner, provided_base, _)) = decoded_condition_row(kb, rid) else {
            continue;
        };
        // Both endpoints canonical, because the asker's are: `decoded_provision_rows`
        // canonicalizes carrier and base, and the per-carrier form this replaces compared
        // owners with `same_sort_canonical`. Two symbols agree under that predicate
        // exactly when `canonical_sort_sym` sends them to one symbol, so a set keyed on
        // the canonical pair answers the same question with one lookup.
        out.insert((
            kb.canonical_sort_sym(owner),
            kb.canonical_sort_sym(provided_base),
        ));
    }
    out
}

/// WI-1109 (058 §3.8) — MATERIALIZE THE FORWARDED PROVISION ROWS.
///
/// A spec may forward to a lower floor of its own tower (`Ord provides WeakOrd[T = T]`).
/// 058 §3.8 states the consequence as one clause over the relation —
/// `provides(?W, PartialOrd[T = ?X]) :- provides(?W, Ord[T = ?X])` — and names "the
/// provision ROW a `requires PartialOrd[X]` goal finds" as the only missing piece. This
/// pass supplies exactly that row: for every carrier providing a forwarder, the
/// forwarded floor is asserted at the SAME bindings.
///
/// DERIVING THE ROW RATHER THAN TEACHING EACH READER IS THE POINT, and it was learned
/// the expensive way. The provides relation has many readers — the provider-requirements
/// load check, witness selection, the resolver's pin filter, dispatch, codegen — and a
/// forwarding invisible to any ONE of them is a silent wrong answer there. Measured
/// while building this: patching two readers surfaced a third. A materialized row is
/// read by all of them unchanged, which is why `eq_derive` asserts rows for composite
/// `Eq`/`NonEq` instead of teaching `sort_provides` about composites.
///
/// FILL SILENCE, NEVER OVERWRITE SPEECH ([`provides_spec_directly`]): a carrier already
/// providing the lower floor keeps its own row and gets no derived twin. That is what
/// keeps `Float` — which writes `provides PartialOrd` and no `compare` — untouched, and
/// what stops a derived row becoming a rival at a coherent spec.
///
/// A CONDITIONAL PROVISION DERIVES NOTHING, and the `!kb.is_fact` guard below is what
/// enforces it — deliberately, not incidentally. `Pair provides Ord[Pair] :- Ord[A],
/// Ord[B]` is a RULE, and this pass asserts FACTS: copying only the head would drop the
/// `:- goals` tail and claim the lower floor UNCONDITIONALLY, at element bindings where
/// the source provision does not hold. That is precisely the over-claim WI-1033's
/// `ProvisionConditionsTooWeak` exists to refuse, manufactured by the deriver instead of
/// written by an author. So the pass UNDER-derives here: a conditional provider writes
/// both floors by hand, each with its own tail (`pair.anthill` does, and its two tails
/// differ — weak iff both components weak, strong iff both strong, which is why one
/// copied tail could not serve both anyway). Deriving a conditional row means asserting
/// a rule with the source's body, and is the next increment, not this one.
pub(crate) fn derive_forwarded_provisions(kb: &mut KnowledgeBase) {
    // Bounded fixpoint, so a tower deeper than one hop still derives; the bound is a
    // runaway guard, not a depth claim — the shipped tower needs one round and settles
    // on the second, which is what ends the loop.
    const ROUNDS: usize = 8;
    for _round in 0..ROUNDS {
        let pending = forwarded_rows_to_derive(kb);
        if pending.is_empty() {
            return;
        }
        for (carrier, target, source_spec, bindings) in pending {
            let rid = assert_forwarded_provides(kb, carrier, target, &bindings);
            // Provenance, so a later refusal against this row can say where it came
            // from instead of naming a `provides` clause the author never wrote.
            kb.mark_derived_provision(rid, source_spec);
        }
    }
    // ONE MORE READ BEFORE ACCUSING THE FIXPOINT (WI-1111 review). The loop returns early
    // only when it OBSERVES an empty `pending`, so a tower whose last productive round is
    // the `ROUNDS`th falls out of the `for` having derived everything — and the assertion
    // below would then be raised on a COMPLETE fixpoint, with a message saying rows are
    // missing when none are. Ask once more; only a still-non-empty set is the failure the
    // assertion is about.
    if forwarded_rows_to_derive(kb).is_empty() {
        return;
    }
    // FALLING OUT OF THE LOOP MEANS THE LAST ROUND STILL HAD WORK, so rows a further
    // round would derive are missing — and a missing row is invisible to every reader
    // (they simply do not find the provision), which is the silent wrong answer this
    // pass exists to prevent. Say so rather than dropping it. `debug_assert` and not a
    // returned error because this function has no error channel and the condition is
    // measured unreachable: the shipped tower settles on round two, and ROUNDS is far
    // above any forwarding depth a library could plausibly declare.
    debug_assert!(
        false,
        "WI-1109: forwarded-provision derivation did not settle in {ROUNDS} rounds — \
         rows from a further round are missing, and every reader will answer as though \
         those provisions do not exist"
    );
}

/// One round: every (carrier, forwarded floor) row not already present, with the source
/// spec that produced it. Reads only — the caller asserts. The emitted bindings are keyed
/// by the TARGET's parameter LOCAL NAMES, already translated through
/// [`forwarding_param_map`].
pub(super) fn forwarded_rows_to_derive(
    kb: &KnowledgeBase,
) -> Vec<(Symbol, Symbol, Symbol, Vec<(String, TermId)>)> {
    let rows = decoded_provision_rows(kb);

    let conditioned = conditioned_provision_pairs(kb);

    // forwarder -> the floors it forwards to, each with the parameter MAP that translates
    // the forwarder's bindings into the floor's ([`forwarding_param_map`]). A CONDITIONAL
    // forwarding forwards nothing, for the reason `derive_forwarded_provisions` gives
    // about the carrier edge: the `:- goals` tail rides in separate facts, so reading the
    // row as unconditional would give every carrier an unconditional lower floor.
    let mut forwards: std::collections::HashMap<Symbol, Vec<(Symbol, Vec<(String, String)>)>> =
        std::collections::HashMap::new();
    for r in &rows {
        if conditioned.contains(&(r.carrier, r.base)) {
            continue;
        }
        let Some(map) = forwarding_param_map(kb, r.carrier, r.base, &r.bindings) else {
            continue;
        };
        let e = forwards.entry(r.carrier).or_default();
        // KEYED ON THE (floor, MAP) PAIR, not the floor alone: one forwarder may convert
        // to the same floor at two DIFFERENT parameters (`F provides Sp[X = A]` beside
        // `F provides Sp[X = B]`), which are two relocations and not one. Under the
        // identity test neither was a forwarding at all, so keeping only the first map
        // would under-derive newly-reachable territory rather than regress old.
        if !e.iter().any(|(base, m)| *base == r.base && *m == map) {
            e.push((r.base, map));
        }
    }
    if forwards.is_empty() {
        return Vec::new();
    }

    // (carrier, spec) -> the bindings it is ALREADY provided at. Fill silence, never
    // overwrite speech — and binding-precisely, so a row at OTHER bindings cannot
    // suppress the one actually needed.
    let mut existing: std::collections::HashMap<(Symbol, Symbol), Vec<&[(Symbol, TermId)]>> =
        std::collections::HashMap::new();
    for r in &rows {
        existing
            .entry((r.carrier, r.base))
            .or_default()
            .push(&r.bindings);
    }

    let mut pending: Vec<(Symbol, Symbol, Symbol, Vec<(String, TermId)>)> = Vec::new();
    for r in &rows {
        // The forwarding row itself is what is being read THROUGH, never a carrier of it.
        if same_sort_canonical(kb, r.carrier, r.base) {
            continue;
        }
        if conditioned.contains(&(r.carrier, r.base)) {
            continue;
        }
        let Some(targets) = forwards.get(&r.base) else {
            continue;
        };
        for (target, map) in targets {
            // TRANSLATE, don't copy (WI-1111). Each target parameter takes the value this
            // row binds the SUBJECT parameter the forwarding sends it to. A target
            // parameter whose subject parameter this row leaves unbound is simply absent,
            // which is what "not bound" already means everywhere else.
            let mapped: Vec<(String, TermId)> = map
                .iter()
                .filter_map(|(target_param, subject_param)| {
                    r.bindings
                        .iter()
                        .find(|(n, _)| kb.local_name_of(*n) == subject_param.as_str())
                        .map(|(_, v)| (target_param.clone(), *v))
                })
                .collect();
            // NO GUARD ON AN EMPTY `mapped`, deliberately (WI-1111 review). A source row
            // binding none of the parameters the forwarding names translates to a row
            // with NO bindings — which is exactly what `assert_forwarded_provides` already
            // says a target parameter the source left unbound means ("simply absent, which
            // is what 'not bound' already means everywhere else"). Skipping instead was a
            // silent drop on the very path that backs the candidate exclusion: the
            // conversion is excluded whether or not this fires, so a skip here DELETES the
            // answer rather than relocating it.
            let already = existing
                .get(&(r.carrier, *target))
                .is_some_and(|rows| rows.iter().any(|b| bindings_cover_named(kb, b, &mapped)));
            // AND THE PENDING TEST IS BINDING-AWARE, which WI-1111 measured the cost of:
            // keyed on the (carrier, target) PAIR alone it derived at most ONE binding per
            // round, so a carrier providing the forwarder at N distinct bindings needed N
            // rounds and nine of them exhausted `ROUNDS` — tripping the settle assertion in
            // a debug build and silently dropping rows in a release one. Driven by
            // `nine_bindings_of_one_forwarder_all_derive`.
            if already
                || pending.iter().any(|(c, t, _, b)| {
                    *c == r.carrier && *t == *target && bindings_cover_named_pairs(kb, b, &mapped)
                })
            {
                continue;
            }
            pending.push((r.carrier, *target, r.base, mapped));
        }
    }
    pending
}

/// Assert `SortProvidesInfo(sort_ref = carrier, spec = SortView(target, <bindings>))`.
/// The `eq_derive::assert_provides` shape, with the source row's bindings TRANSLATED
/// through the forwarding's parameter map rather than a single carrier binding
/// synthesized — [`forwarding_param_map`] is what makes the translation right, and
/// `bindings` arrives here already keyed by the target's own parameter local names.
fn assert_forwarded_provides(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    target: Symbol,
    bindings: &[(String, TermId)],
) -> RuleId {
    let provides_sym = kb.resolve_symbol("anthill.reflect.SortProvidesInfo");
    let sort_view_sym = kb.resolve_symbol("anthill.reflect.SortView");
    let sort_ref_key = kb.intern("sort_ref");
    let spec_key = kb.intern("spec");
    let spec_name = kb.make_name_term_from_sym(target);
    // TAKE THE KEYS FROM THE TARGET, NOT FROM THE SOURCE — the `eq_derive::assert_provides`
    // discipline, which reads `type_params_of_sort(spec)`. Two things go wrong otherwise,
    // and the first draft of this function did both (review of WI-1109).
    //
    // (1) The source row's keys are the FORWARDER's parameter symbols (`Ord`'s `T`), and
    // a reader comparing binding names by symbol identity would not see them as the
    // target's — the row would exist and answer no goal.
    //
    // (2) A forwarder parameter the forwarding provision does NOT map would be copied
    // anyway: `Fwd { sort T = ?  sort U = ?  provides Low[T = T] }` given a row
    // `C provides Fwd[T = Int64, U = Bool]` would emit `Low[T = Int64, U = Bool]` — a
    // binding for a parameter `Low` does not declare. Selecting BY THE TARGET'S OWN
    // PARAMETER LIST drops it, which is right: the forwarding said nothing about `U`.
    // A target parameter the source left unbound is simply absent, which is what "not
    // bound" already means everywhere else.
    let target_params: Vec<String> = kb.type_params_of_sort(target);
    let named_args: SmallVec<[(Symbol, TermId); 2]> = target_params
        .iter()
        .filter_map(|param| {
            bindings
                .iter()
                .find(|(name, _)| name.as_str() == param.as_str())
                .map(|(_, value)| (kb.intern(param), *value))
        })
        .collect();
    let spec_view = kb.alloc(Term::Fn {
        functor: sort_view_sym,
        pos_args: SmallVec::from_elem(spec_name, 1),
        named_args,
    });
    let sort_ref_term = kb.make_name_term_from_sym(carrier);
    kb.register_entity_fields(provides_sym, vec![sort_ref_key, spec_key]);
    kb.assert_fact_carrier(
        provides_sym,
        Vec::new(),
        vec![
            (sort_ref_key, crate::eval::value::Value::term(sort_ref_term)),
            (spec_key, crate::eval::value::Value::term(spec_view)),
        ],
        crate::kb::ClauseKind::Requirement,
        carrier,
        None,
    )
}
