//! Extent sources — the read seam of proposal 057 (`docs/proposals/057-extent-read-seam.md`).
//!
//! An **extent source** owns the *reads* of one or more functors: retrieval of
//! a mounted functor delegates to the source's [`ExtentSource::query`] instead
//! of (or beside) the resident discrimination tree. This module is the FOUNDATION
//! slice (WI-796): the trait read half, the query-contract types, the KB-owned
//! [`ExtentRegistry`] (`kb.extents`, successor to `route::RouteRegistry`), and the
//! shipped reference owner [`InMemoryExtentSource`]. It is buildable and testable
//! in ISOLATION — the conformance suite drives sources via DIRECT `query` calls,
//! with no resolver involvement.
//!
//! WI-797 wired the mount into resolution and load — the resolver's discrim-mount
//! delegation (`SearchStream::gather_extent_rows`), retiring `RouteHandler` into
//! `query`, and the loader / registration single-owner refusals on resident
//! collisions. (The read-beside-discrim `Store::retrieve` retirement — the other
//! half of R2 — waits on the store-registry→`kb.extents` move in the write seam,
//! WI-780: it backs the still-declared `QueryableStore.retrieve` op.) The
//! values-first `read_facts` accessor is WI-773. The write half
//! of the trait (`persist`/`update`/`retract`) arrives with the write seam
//! (WI-780); the trait grows one method-set per slice, never ahead of the code.
//!
//! ## The query contract (057 §"The query contract")
//!
//! 1. **Capability is declared.** [`ExtentProfile::query_modes`] is the store's
//!    pattern description, read at registration. The engine matches a goal to a
//!    satisfied mode ([`ExtentProfile::select_mode`]) or refuses it loud — a
//!    backend never re-derives groundness from a `Value`. [`QueryPattern::mode`]
//!    names which mode a call took.
//! 2. **Pushdown vocabulary is ground equality only.** [`QueryPattern::bound`] is
//!    every fully-ground argument slot as `slot = value`, nothing richer.
//! 3. **Soundness, stated once.** `query` returns a **superset** of the rows
//!    satisfying every `bound` equality; the engine re-unifies each returned row
//!    against the full goal and drops non-matches, so over-return is sound and
//!    only under-return (dropping a row that satisfies `bound`) is a bug.

use std::collections::HashMap;

use crate::eval::value::Value;
use crate::intern::Symbol;
use crate::kb::term::{Var, VarId};
use crate::kb::term_view::{views_structurally_equal, TermView};

use super::KnowledgeBase;

// ── The read interface ─────────────────────────────────────────

/// One owner per functor, for *reads*. This slice is the READ HALF only —
/// `owned` + `query`. Write / mirror / sync methods are not in the trait yet;
/// each arrives in the slice that implements it (writes with the write seam,
/// WI-780), with its caller. The trait grows with the code, never ahead of it.
pub trait ExtentSource {
    /// Registration authority: the `(fully-qualified functor name, profile)`
    /// pairs this source owns. Names resolve to `Symbol`s once, at registration
    /// (an unresolvable name is a loud [`ExtentRegError::UnresolvableName`]) —
    /// every engine structure downstream is `Symbol`-keyed, but a backend can
    /// only speak names, so the boundary is String here and `Symbol` past
    /// registration.
    fn owned(&self) -> Vec<(String, ExtentProfile)>;

    /// The discrimination contract of the mounted subtree: a lazy cursor over the
    /// ground rows matching `pattern` (see the module-level "query contract").
    /// Returns a **superset** of the rows satisfying `pattern.bound`; the engine
    /// re-filters. An unsupported `pattern.mode` is a loud
    /// [`ExtentError::NoSupportedMode`], never a silent empty cursor.
    fn query(
        &self,
        kb: &KnowledgeBase,
        pattern: &QueryPattern,
    ) -> Result<Box<dyn ExtentCursor>, ExtentError>;
}

/// Lazy, carrier-neutral, ground rows. Errors are per-row so a fallible backend
/// fails loud, never truncates silent. In-memory sources never error per row.
pub trait ExtentCursor {
    fn next(&mut self, kb: &KnowledgeBase) -> Option<Result<Value, ExtentError>>;
}

// ── The query-contract types ───────────────────────────────────

/// The digested selection for one call — the engine already walked the goal, so
/// the backend receives a chosen `mode` and the ground `bound`, never a raw goal.
#[derive(Clone, Debug)]
pub struct QueryPattern {
    /// Index into the owning [`ExtentProfile::query_modes`] this call took.
    pub mode: usize,
    /// Every fully-ground argument slot as `slot = value` (ground equality only).
    /// Carries ALL ground args (not just the mode's `required_ground`) for
    /// maximum pushdown; a mode gates *capability*, `bound` drives *filtering*.
    pub bound: Vec<(ArgKey, Value)>,
}

/// A functor argument slot — named or positional. `Copy` (both `Symbol` and
/// `u32` are), so `required_ground` / `bound` membership checks are cheap.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ArgKey {
    Named(Symbol),
    Pos(u32),
}

/// One declared pattern description: the slots a caller must ground for this
/// mode to apply. An empty `required_ground` is the *enumeration* mode.
#[derive(Clone, Debug)]
pub struct QueryMode {
    pub required_ground: Vec<ArgKey>,
}

/// The read profile of a functor's extent. This slice's axes only; `writability`
/// (per-functor `Monotonicity`, subsuming `store_monotonicity`) arrives with the
/// write seam (WI-780), so a materialized profile is NOT yet the home of write
/// policy — see [`ExtentRegistry::profiles`].
#[derive(Clone, Debug)]
pub struct ExtentProfile {
    /// The store's pattern descriptions, read at registration.
    pub query_modes: Vec<QueryMode>,
    /// Whether the whole extent can be streamed (an all-free goal answered).
    pub enumerable: bool,
    /// Whether `query` returns EVERY matching row (no sampling / truncation).
    pub complete: bool,
    /// Whether repeated reads are reproducible within a session.
    pub stability: Stability,
}

impl ExtentProfile {
    /// Engine-lite mode selection: the most-specific declared mode whose
    /// `required_ground` is a subset of the `ground` slots, or `None` when no
    /// mode applies (the caller maps `None` to a loud
    /// [`ExtentError::NoSupportedMode`] — this is how an *undeclared pattern* is
    /// refused, and how *enumeration on a non-enumerable source* is refused: an
    /// empty `ground` matches only a mode with empty `required_ground`, which a
    /// non-enumerable source does not declare).
    ///
    /// "Most-specific" = the satisfied mode requiring the most ground slots, so a
    /// keyed mode wins over the enumeration mode when both apply. On a tie (two
    /// satisfied modes requiring equally many slots) the LATER-declared one is
    /// chosen (`max_by_key` returns the last maximum) — an immaterial choice,
    /// since `bound` carries all ground args regardless of the mode picked.
    /// WI-797's resolver consumes this same method.
    pub fn select_mode(&self, ground: &[ArgKey]) -> Option<usize> {
        self.query_modes
            .iter()
            .enumerate()
            .filter(|(_, m)| m.required_ground.iter().all(|k| ground.contains(k)))
            .max_by_key(|(_, m)| m.required_ground.len())
            .map(|(i, _)| i)
    }
}

/// Read reproducibility. `Volatile` (and its observation memo) is a deferred
/// archetype — a loud registration error in v1, not a stub.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Stability {
    Stable,
    Volatile,
}

/// Errors surfaced through `query` / a cursor. Grows with slices (the write seam
/// adds write failures). Result-over-panic so a CLI / codegen caller renders it
/// through its own error channel.
#[derive(Clone, Debug)]
pub enum ExtentError {
    /// No declared query mode applies to the requested pattern.
    NoSupportedMode,
    /// A backend-specific failure (I/O, a remote error), carrying its message.
    Backend(String),
}

impl std::fmt::Display for ExtentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtentError::NoSupportedMode => {
                write!(f, "extent source: no declared query mode applies to this pattern")
            }
            ExtentError::Backend(msg) => write!(f, "extent source backend error: {msg}"),
        }
    }
}

impl std::error::Error for ExtentError {}

// ── The registry (kb.extents) ──────────────────────────────────

/// Handle into the [`ExtentRegistry`] source slab. Stable for the KB's lifetime.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SourceId(u32);

/// Errors from [`KnowledgeBase::register_extent_owner`]. Every variant is a loud
/// refusal — the interface refuses a capability it has not implemented (volatile,
/// non-enumerable oracle) rather than pretending to it, and refuses a structural
/// violation (double ownership, an ill-formed volatile profile).
#[derive(Clone, Debug)]
pub enum ExtentRegError {
    /// An `owned()` name did not resolve to a defined symbol.
    UnresolvableName(String),
    /// The functor already has a registered extent owner (single-owner rule).
    AlreadyOwned { functor: String },
    /// The functor already has resident facts/rules in `kb.rules` — mounting an
    /// owner over it would make the extent a SECOND, invisible source of truth.
    /// The registration-time complement of the loader's `FunctorOwnedByExtent`
    /// refusal (both enforce the single-owner rule, from the two orderings:
    /// mount-then-load vs load-then-mount). WI-797.
    ResidentCollision { functor: String },
    /// A `Volatile` source declared more than one query mode — the permanent
    /// well-formedness invariant of a volatile source (at most one mode, so its
    /// observation memo has a single key). Checked ahead of the v1 volatile gate
    /// so the violation surfaces as itself.
    VolatileMultiMode { functor: String, modes: usize },
    /// `Stability::Volatile` — deferred archetype (volatile + observation memo),
    /// a loud registration error until its slice lands.
    VolatileUnsupported { functor: String },
    /// A non-enumerable source — the deferred oracle archetype, a loud
    /// registration error until its slice lands.
    NonEnumerable { functor: String },
}

impl std::fmt::Display for ExtentRegError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtentRegError::UnresolvableName(name) => {
                write!(f, "register_extent_owner: unresolvable functor name '{name}'")
            }
            ExtentRegError::AlreadyOwned { functor } => write!(
                f,
                "register_extent_owner: functor '{functor}' already has an extent owner"
            ),
            ExtentRegError::ResidentCollision { functor } => write!(
                f,
                "register_extent_owner: functor '{functor}' already has resident facts/rules; \
                 a mounted source must own its functor exclusively (seed it through the store)"
            ),
            ExtentRegError::VolatileMultiMode { functor, modes } => write!(
                f,
                "register_extent_owner: volatile source for '{functor}' declares {modes} query \
                 modes; a volatile source must declare at most one"
            ),
            ExtentRegError::VolatileUnsupported { functor } => write!(
                f,
                "register_extent_owner: volatile source for '{functor}' is not supported in v1 \
                 (deferred archetype)"
            ),
            ExtentRegError::NonEnumerable { functor } => write!(
                f,
                "register_extent_owner: non-enumerable source for '{functor}' is not supported in \
                 v1 (deferred oracle archetype)"
            ),
        }
    }
}

impl std::error::Error for ExtentRegError {}

/// KB-owned aggregate of extent sources — successor to the retired `RouteHandler`
/// registry (WI-797).
/// Sources live in a `SourceId`-keyed slab; `mounts` names the owner of each
/// functor; `profiles` materializes each owned functor's read profile once, at
/// registration.
#[derive(Default)]
pub(crate) struct ExtentRegistry {
    /// `SourceId`-keyed slab. A `SourceId` is an index; sources are never
    /// removed, so indices stay valid for the KB's lifetime.
    sources: Vec<Box<dyn ExtentSource>>,
    /// Functor → owning source. The exclusive read-ownership table.
    mounts: HashMap<Symbol, SourceId>,
    /// Functor → materialized read profile, resolved once at registration. The
    /// eventual home of per-functor storage metadata (subsuming
    /// `store_monotonicity` when the write seam adds `writability`); in this read
    /// slice it holds read axes only.
    profiles: HashMap<Symbol, ExtentProfile>,
}

impl ExtentRegistry {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// The owner of `functor`, or `None` when the functor is resident (served by
    /// the discrim tree, not a mounted source).
    pub(crate) fn owner(&self, functor: Symbol) -> Option<&dyn ExtentSource> {
        let id = *self.mounts.get(&functor)?;
        Some(self.sources[id.0 as usize].as_ref())
    }

    /// The materialized read profile of `functor`, or `None` when unowned.
    pub(crate) fn profile(&self, functor: Symbol) -> Option<&ExtentProfile> {
        self.profiles.get(&functor)
    }

    #[allow(dead_code)]
    pub(crate) fn is_empty(&self) -> bool {
        self.sources.is_empty()
    }
}

impl KnowledgeBase {
    /// Register `source` as the exclusive read owner of every functor its
    /// `owned()` names. Resolves each name to a `Symbol` ONCE, here (loud on an
    /// unresolvable name), and enforces the read-side registration rules. All or
    /// nothing: if any owned functor fails a check, nothing is committed.
    ///
    /// Rules, per owned `(name, profile)`, in order:
    /// 1. `name` must resolve → else [`ExtentRegError::UnresolvableName`].
    /// 2. the functor must be unowned → else [`ExtentRegError::AlreadyOwned`]
    ///    (single-owner), AND have no resident facts/rules → else
    ///    [`ExtentRegError::ResidentCollision`] (WI-797, the load-then-mount
    ///    complement of the loader's `FunctorOwnedByExtent` refusal).
    /// 3. a `Volatile` profile must declare ≤1 mode → else
    ///    [`ExtentRegError::VolatileMultiMode`] (well-formedness).
    /// 4. `Volatile` is refused in v1 → [`ExtentRegError::VolatileUnsupported`].
    /// 5. a non-enumerable profile is refused in v1 →
    ///    [`ExtentRegError::NonEnumerable`].
    pub fn register_extent_owner(
        &mut self,
        source: Box<dyn ExtentSource>,
    ) -> Result<SourceId, ExtentRegError> {
        // Resolve + validate ALL owned functors before committing any (atomic).
        let owned = source.owned();
        let mut resolved: Vec<(Symbol, ExtentProfile)> = Vec::with_capacity(owned.len());
        for (name, profile) in owned {
            let sym = self
                .resolve_name_in_global(&name)
                .ok_or_else(|| ExtentRegError::UnresolvableName(name.clone()))?;

            if self.extents.mounts.contains_key(&sym)
                || resolved.iter().any(|(s, _)| *s == sym)
            {
                return Err(ExtentRegError::AlreadyOwned { functor: name });
            }
            // Single-owner, the other ordering (load-then-mount): a functor with
            // resident facts/rules can't also be mounted — the loader's
            // `FunctorOwnedByExtent` refusal is the mount-then-load complement.
            // `rules_by_functor` already drops retracted rules (WI-797).
            if !self.rules_by_functor(sym).is_empty() {
                return Err(ExtentRegError::ResidentCollision { functor: name });
            }
            if profile.stability == Stability::Volatile && profile.query_modes.len() > 1 {
                return Err(ExtentRegError::VolatileMultiMode {
                    functor: name,
                    modes: profile.query_modes.len(),
                });
            }
            if profile.stability == Stability::Volatile {
                return Err(ExtentRegError::VolatileUnsupported { functor: name });
            }
            if !profile.enumerable {
                return Err(ExtentRegError::NonEnumerable { functor: name });
            }
            resolved.push((sym, profile));
        }

        let id = SourceId(self.extents.sources.len() as u32);
        for (sym, profile) in resolved {
            self.extents.mounts.insert(sym, id);
            self.extents.profiles.insert(sym, profile);
        }
        self.extents.sources.push(source);
        Ok(id)
    }

    /// The registered extent owner of `functor`, or `None` when resident.
    pub fn extent_owner(&self, functor: Symbol) -> Option<&dyn ExtentSource> {
        self.extents.owner(functor)
    }

    /// The materialized read profile of an owned `functor`, or `None`.
    pub fn extent_profile(&self, functor: Symbol) -> Option<&ExtentProfile> {
        self.extents.profile(functor)
    }
}

// ── The values-first accessor (WI-773) ─────────────────────────

/// How [`KnowledgeBase::read_facts`] treats a bodied candidate for the read
/// functor — a *value* of the accessor's policy parameter (057 §"The accessor").
pub enum BodiedRulePolicy {
    /// Facts-only. ANY bodied candidate for the functor is a loud
    /// [`ExtentReadError::BodiedRule`] rendering the rule via
    /// [`crate::persistence::print::TermPrinter::print_rule`]. Result-over-panic,
    /// so a CLI / codegen caller renders it through its own error channel instead
    /// of the WI-770 assert-abort (exit 101, no span). The refusal is **blanket**:
    /// a bodied rule poisons the read regardless of the `selection`, even one
    /// whose head the selection would not have matched (the WI-770 / WI-772
    /// precedent — a divergent policy under one functor is the bug this centralises).
    Refuse,
    // The `Resolve` policy is NOT a variant here — it needs `&mut self`
    // (resolution allocates fresh vars / interns answers), so it ships as the
    // sibling method [`KnowledgeBase::read_facts_resolved`] (WI-774) rather than a
    // value of this `&self` parameter. `Resolve` IS SLD: it evaluates bodied rules
    // (guards honored) instead of refusing them, which is why it cannot share the
    // `&self` candidate-read `Refuse` rides.
}

/// Error from [`KnowledgeBase::read_facts`]. Result-over-panic so a CLI / codegen
/// caller renders it through its own channel (`error: {msg}`, exit 1) rather than
/// aborting (the WI-770 assert path).
#[derive(Clone, Debug)]
pub enum ExtentReadError {
    /// A bodied candidate was read under [`BodiedRulePolicy::Refuse`]. `rule` is
    /// the rendered `head :- body` (`TermPrinter::print_rule`) so the caller names
    /// the offender; `functor` is its fully-qualified name.
    BodiedRule { functor: String, rule: String },
    /// A mounted source refused or failed the query (an unsupported mode, a
    /// backend/row error). Carries the underlying [`ExtentError`].
    Extent { functor: String, source: ExtentError },
    /// No declared query mode applies to `selection` on a mounted source — an
    /// all-free selection against a non-enumerable (oracle) source. Unreachable
    /// for a v1 source (registration admits only enumerable owners, whose
    /// enumeration mode answers any selection); surfaced, not dropped, for when
    /// the oracle archetype lands.
    NoSupportedMode { functor: String },
    /// A [`BodiedRulePolicy`]-less [`KnowledgeBase::read_facts_resolved`] search
    /// TRUNCATED at the depth cap (WI-628/767). Its row set is then UNDECIDED
    /// (under-reported), never complete, so it is a loud refusal rather than a
    /// silently short list — the WI-767 "a missing answer is undecided, not
    /// refuted" discipline carried onto the Resolve read.
    SearchTruncated { functor: String },
    /// A [`KnowledgeBase::read_facts_resolved`] read of a functor with no declared
    /// field schema ([`KnowledgeBase::entity_field_names`] returned `None`), or a
    /// `selection` naming a field the functor lacks — the Resolve read needs the
    /// full field set to build a matching full-arity goal, so it cannot proceed.
    NoFieldSchema { functor: String },
}

impl std::fmt::Display for ExtentReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtentReadError::BodiedRule { functor, rule } => write!(
                f,
                "read_facts(`{functor}`): a bodied rule was read where only facts are \
                 allowed: {rule}"
            ),
            ExtentReadError::Extent { functor, source } => {
                write!(f, "read_facts(`{functor}`): {source}")
            }
            ExtentReadError::NoSupportedMode { functor } => write!(
                f,
                "read_facts(`{functor}`): no declared query mode applies to this selection"
            ),
            ExtentReadError::SearchTruncated { functor } => write!(
                f,
                "read_facts_resolved(`{functor}`): resolution truncated at the depth cap; \
                 the row set is undecided, not complete — raise the depth budget"
            ),
            ExtentReadError::NoFieldSchema { functor } => write!(
                f,
                "read_facts_resolved(`{functor}`): no declared field schema (or a selection \
                 names an undeclared field); cannot build a full-arity resolution goal"
            ),
        }
    }
}

impl std::error::Error for ExtentReadError {}

impl KnowledgeBase {
    /// The values-first read primitive every fact-reader migrates onto (057
    /// §"The accessor"): the rows of `functor` under the ground `selection`, over
    /// resident AND mounted extents uniformly. Returns row **`Value`s, never a
    /// `RuleId`** — the public read shape stays `RuleId`-free so the write seam's
    /// R4 ratchet (WI-780) can privatise the raw head-as-answer walk, and so a
    /// store-mounted functor (which has no resident `RuleId` to hand out) reads
    /// through the same door with zero caller change.
    ///
    /// `selection` is named-field ground equality (`field = value`) — the shape a
    /// caller already grounds (cpp-gen's `anthill_type`, a WorkItem's `id`);
    /// EMPTY selection = enumeration. It is the query contract's `bound` (057
    /// §"The query contract" rule 2), matched as a **superset**: a returned row
    /// must carry every selected field with the selected value, and MAY carry more
    /// (width is fine — a partial spec selects). `policy` decides bodied
    /// candidates ([`BodiedRulePolicy`]).
    ///
    /// The branch — resident discrim scan vs mount `query` — is internal; the
    /// caller never sees which source answered.
    pub fn read_facts(
        &self,
        functor: Symbol,
        selection: &[(Symbol, Value)],
        policy: BodiedRulePolicy,
    ) -> Result<Vec<Value>, ExtentReadError> {
        // Mounted extent (registration wrote a profile) → delegate to the owner's
        // `query`, re-filtering its (possibly over-returned) rows. A mounted
        // functor has NO resident rules (the single-owner loader/registration
        // refusals, WI-797), so the bodied-rule `policy` cannot apply here — the
        // read is vacuously facts-only.
        if self.extents.profile(functor).is_some() {
            return self.read_mounted_facts(functor, selection);
        }

        // Resident. Blanket bodied-rule refusal FIRST — O(1) and selection-
        // INDEPENDENT (WI-812). A bodied rule under the functor poisons the read
        // regardless of the `selection`, even one whose head the selection would
        // not have matched (the WI-770 / WI-772 precedent — a divergent policy
        // under one functor is the bug this centralises). The `has_bodied_rule`
        // gate proves the absence of any bodied rule with one map read; only the
        // refusal (error) path scans, to NAME the offender, and that is cold. This
        // separates "is this functor a pure table?" (the gate) from "which rows
        // match?" (the query below) — the two were entangled in the old
        // single-pass bucket scan.
        match policy {
            BodiedRulePolicy::Refuse => {
                if self.has_bodied_rule(functor) {
                    let rid = self
                        .rules_by_functor_iter(functor)
                        .find(|&rid| !self.is_fact(rid))
                        .expect("has_bodied_rule ⇒ a bodied rule is in the bucket");
                    return Err(ExtentReadError::BodiedRule {
                        functor: self.resolve_sym(functor).to_string(),
                        rule: crate::persistence::print::TermPrinter::new(self).print_rule(rid),
                    });
                }
            }
        }

        // The gate held: every rule under `functor` is a FACT. Collect the heads
        // matching `selection`.
        //
        // A non-empty selection on a functor with a declared field schema pushes
        // the selection DOWN through the discrimination tree: a full-arity
        // `functor(field: …)` pattern grounds the selected fields and wildcards the
        // rest, so the read is O(matching) and naturally functor-scoped rather than
        // an O(bucket) scan. Empty selection (enumeration is inherently every row)
        // and a SCHEMALESS functor (no full-arity pattern is buildable — the reason
        // the old accessor scanned) enumerate the bucket instead. `bound_matches`
        // is the authoritative selection filter either way (the 057 superset
        // contract, mirroring the mounted arm): it re-confirms the exact discrim
        // rows and narrows the enumerated rows.
        let bound = named_selection_as_bound(selection);
        if !selection.is_empty() {
            if let Some(pattern) = self.selection_query_pattern(functor, selection) {
                let rows: Vec<Value> = self
                    .query_fact_heads(&pattern)
                    .into_iter()
                    .filter(|head| bound_matches(self, head, &bound))
                    .collect();
                // The discrim pushdown keys on ARITY, so it matches only full-arity
                // facts; the bucket scan (`bound_matches`) is arity-agnostic. They
                // can diverge ONLY when a stored fact is not full-arity — a WI-716
                // loader-padding violation / malformed fact. Surface that loudly in
                // debug rather than silently dropping the row (the "loud over silent"
                // rule); the whole check (and its scan) is `cfg`'d out of release, so
                // the fast indexed path stands alone there.
                #[cfg(debug_assertions)]
                {
                    let scanned = self.scan_matching_fact_count(functor, &bound);
                    assert_eq!(
                        rows.len(),
                        scanned,
                        "read_facts: discrim pushdown for `{}` returned {} rows but the scan \
                         matched {} — a non-full-arity fact bypassed the full-arity pattern",
                        self.resolve_sym(functor),
                        rows.len(),
                        scanned,
                    );
                }
                return Ok(rows);
            }
        }
        // Enumeration (empty selection) or a schemaless functor: scan the bucket.
        // Keep the per-row `is_fact` filter (not merely a debug assert): the gate
        // held so every entry SHOULD be a fact, but filtering makes the facts-only
        // guarantee LOCAL — a `bodied_rule_counts` bug can never leak a bodied head
        // as a "fact" even in release, matching `query_fact_heads`' own filter.
        Ok(self
            .rules_by_functor_iter(functor)
            .filter_map(|rid| {
                if !self.is_fact(rid) {
                    debug_assert!(
                        false,
                        "read_facts: has_bodied_rule was false but a bodied rule under {} \
                         slipped through (bodied_rule_counts drift)",
                        self.resolve_sym(functor),
                    );
                    return None;
                }
                let head = self.rule_head_value(rid);
                bound_matches(self, head, &bound).then(|| head.clone())
            })
            .collect())
    }

    /// Count the resident FACT heads under `functor` matching `bound` by an
    /// arity-agnostic bucket scan — the authoritative selection semantics the
    /// mounted arm and the old resident scan use. Only [`Self::read_facts`]'s debug
    /// cross-check calls it, to catch a discrim pushdown that under-returns a
    /// non-full-arity fact; it is `#[cfg(debug_assertions)]` so the scan is never
    /// compiled into release.
    #[cfg(debug_assertions)]
    fn scan_matching_fact_count(&self, functor: Symbol, bound: &[(ArgKey, Value)]) -> usize {
        self.rules_by_functor_iter(functor)
            .filter(|&rid| self.is_fact(rid) && bound_matches(self, self.rule_head_value(rid), bound))
            .count()
    }

    /// Build the discrim query pattern for [`Self::read_facts`]'s SELECTIVE
    /// resident arm (WI-812): a full-arity `functor(field: …)` [`Value::Entity`]
    /// carrying EVERY declared field of `functor` ([`Self::entity_field_names`]) —
    /// each grounded to its `selection` value, or a wildcard var. `None` when the
    /// functor has NO declared field schema, or `selection` names a field it lacks;
    /// neither is expressible as a full-arity pattern, so the caller enumerates the
    /// bucket instead (a schemaless functor still reads exactly, just not indexed).
    ///
    /// The FULL field set is load-bearing — the same reason [`Self::enumeration_goal`]
    /// (the Resolve read's goal builder, which shares [`full_arity_entity_pattern`])
    /// carries it: the discrim tree keys on arity and stored fact heads are
    /// full-arity (the loader pads omitted fields, WI-716), so a partial pattern
    /// would key a wrong arity and match nothing. A fact that is NOT full-arity
    /// therefore fails to match — [`Self::read_facts`] guards that divergence with a
    /// debug cross-check against the scan.
    ///
    /// Unselected fields carry a DISTINCT wildcard var (`u32::MAX - i`, which never
    /// collides with a real allocated var). Distinct — not one reused var — so the
    /// pattern is a valid query for ANY consumer: [`Self::query_fact_heads`] discards
    /// the substitution, so reuse would also be sound there, but distinct vars keep
    /// it correct even if a future caller routes it through [`Self::query_view`]
    /// (which folds a repeated binding into an `is_contradiction`). All ids are
    /// synthetic, so the read stays `&self` (no `&mut self` fresh-var mint).
    fn selection_query_pattern(
        &self,
        functor: Symbol,
        selection: &[(Symbol, Value)],
    ) -> Option<Value> {
        let fields = self.entity_field_names(functor)?;
        // A selection key the functor does not declare cannot be pushed down as a
        // full-arity field slot — enumerate instead (the bucket + `bound_matches`
        // reads it exactly, returning empty if no fact carries the key).
        if selection.iter().any(|(k, _)| !fields.contains(k)) {
            return None;
        }
        Some(full_arity_entity_pattern(functor, fields, selection, |i, _| {
            Value::Var(Var::Global(VarId::new(u32::MAX - i as u32, functor)))
        }))
    }

    /// The `Resolve` counterpart of [`Self::read_facts`] (057 §"The accessor"; the
    /// WI-774 policy the [`BodiedRulePolicy`] note names): the rows of `functor`
    /// under the ground `selection`, computed by RESOLUTION rather than a candidate
    /// scan. Where `Refuse` finds candidates and REJECTS any bodied rule, `Resolve`
    /// IS SLD — it evaluates them, so a bodied rule's GUARD is honored (its
    /// head-instance is a row iff its body succeeds) and a mounted extent answers
    /// through the same door the resolver already mounts (WI-797). It DELEGATES to
    /// the resolver; there is no third read path (the 057 design synthesis:
    /// "read_facts(Resolve) delegates to the resolver, not a third mount path").
    ///
    /// This is the ENUMERATION (walkable, multi-valued) shape: every non-floundered
    /// solution is a row, in the resolver's most-specific-first discrim order. A
    /// SINGLE-VALUED read — pick THE most-specific row, loud on an
    /// incomparable-specificity tie (the decided WI-774 policy for a single-valued
    /// table functor) — layers on top and is deliberately NOT built here: no table
    /// functor reads single-valued yet, and the one single-valued realization
    /// resolve (`anthill.realization.realizes_effect`) is a proper predicate with
    /// mutually-exclusive NAF arms and its own loud tie-check, so the mechanism
    /// would have no consumer.
    ///
    /// WI-767 depth-cap discipline: a search that TRUNCATED at the depth cap has an
    /// UNDECIDED (under-reported) row set, so it is a loud
    /// [`ExtentReadError::SearchTruncated`] — never a silently short list. A
    /// FLOUNDERED solution (undischarged residual goals) proves nothing and is
    /// dropped (as `realizes_effect`'s own reader does). NOTE the loud channel here
    /// covers depth truncation only: a MOUNTED-backend query failure is handled by
    /// the resolver's mount path, which in v1 logs and yields empty (WI-797) rather
    /// than surfacing an error — so a mounted read can under-report without a loud
    /// signal until fallible backends land (WI-780). Immaterial to today's
    /// consumers, all of which read RESIDENT functors.
    ///
    /// Needs `&mut self` (resolution allocates fresh vars / interns answers), so it
    /// is a sibling method, not a `&self` [`BodiedRulePolicy`] variant.
    pub fn read_facts_resolved(
        &mut self,
        functor: Symbol,
        selection: &[(Symbol, Value)],
    ) -> Result<Vec<Value>, ExtentReadError> {
        let goal = self.enumeration_goal(functor, selection)?;
        let config = crate::kb::resolve::ResolveConfig::default();
        let (solutions, truncated) =
            self.resolve_goals_with_truncation(vec![goal.clone()], &config);
        if truncated {
            return Err(ExtentReadError::SearchTruncated {
                functor: self.resolve_sym(functor).to_string(),
            });
        }
        Ok(solutions
            .into_iter()
            .filter(|s| s.residual.is_empty())
            .map(|s| self.reify_value(&goal, &s.subst))
            .collect())
    }

    /// Build the enumeration goal for [`Self::read_facts_resolved`]: a
    /// `functor(field: …)` pattern carrying EVERY declared field of `functor`
    /// ([`Self::entity_field_names`]) — each grounded to its `selection` value, or
    /// a fresh var. A `Value::Entity` (the resolver's non-interned query idiom — a
    /// transient query pattern is never hash-consed, per the CLAUDE.md
    /// representation note). The FULL field set is load-bearing: unification needs
    /// a full-arity pattern to match a stored fact head (the loader pads omitted
    /// fields on stored heads, not on a runtime goal), so a partial goal would
    /// silently match nothing.
    fn enumeration_goal(
        &mut self,
        functor: Symbol,
        selection: &[(Symbol, Value)],
    ) -> Result<Value, ExtentReadError> {
        let fields: Vec<Symbol> = self
            .entity_field_names(functor)
            .ok_or_else(|| ExtentReadError::NoFieldSchema {
                functor: self.resolve_sym(functor).to_string(),
            })?
            .to_vec();
        // Every selection key must be a declared field — else the caller selected
        // on a field the functor lacks; loud, not a silent empty read.
        for (key, _) in selection {
            if !fields.contains(key) {
                return Err(ExtentReadError::NoFieldSchema {
                    functor: self.resolve_sym(functor).to_string(),
                });
            }
        }
        // Shared full-arity builder (see `selection_query_pattern`); here the
        // unselected fields are FRESH vars (a resolution goal reifies its answer via
        // the substitution, so each free column must be its own var — unlike the
        // `&self` discrim pattern, whose substitution is discarded).
        Ok(full_arity_entity_pattern(functor, &fields, selection, |_, f| {
            Value::Var(Var::Global(self.fresh_var(f)))
        }))
    }

    /// The mounted arm of [`Self::read_facts`]: push `selection` down as the query
    /// `bound`, select the mode, ride the shared [`Self::drain_extent_query`], and
    /// re-filter each returned row against `selection` (the source may over-return
    /// past the pushed-down equalities — sound; only under-return is a bug, 057
    /// §"The query contract" rule 3). Caller has already confirmed `functor` is
    /// mounted.
    fn read_mounted_facts(
        &self,
        functor: Symbol,
        selection: &[(Symbol, Value)],
    ) -> Result<Vec<Value>, ExtentReadError> {
        let profile = self
            .extents
            .profile(functor)
            .expect("read_mounted_facts on an unmounted functor");
        let bound = named_selection_as_bound(selection);
        let ground: Vec<ArgKey> = bound.iter().map(|(k, _)| *k).collect();
        let mode = profile.select_mode(&ground).ok_or_else(|| {
            ExtentReadError::NoSupportedMode { functor: self.resolve_sym(functor).to_string() }
        })?;
        // `bound` moves into the pattern; the drain borrows `&pattern` and hands
        // back owned rows (the cursor does not borrow it), so the re-filter below
        // reads `&pattern.bound` — no second clone of the selection values
        // (`named_selection_as_bound` already cloned once).
        let pattern = QueryPattern { mode, bound };
        let rows = self.drain_extent_query(functor, &pattern).map_err(|source| {
            ExtentReadError::Extent { functor: self.resolve_sym(functor).to_string(), source }
        })?;
        // The source may over-return, and read_facts hands rows straight to the
        // consumer with no further matching — so narrow here. Keep a row only if it
        // is OF `functor` AND satisfies the selection. The functor check mirrors the
        // resolver's re-unification, which drops a row whose head functor differs
        // from the goal's (`match_view_value_pattern`, resolve.rs) — a mounted
        // source that over-returns (057 §"query contract" rule 3) must over-return
        // rows of ITS functor, never a foreign one, and the accessor promises "rows
        // of `functor`". `bound_matches` alone is functor-blind, so both guards are
        // load-bearing.
        Ok(rows
            .into_iter()
            .filter(|row| {
                row_has_functor(self, row, functor) && bound_matches(self, row, &pattern.bound)
            })
            .collect())
    }

    /// The single place that speaks [`ExtentSource::query`] (WI-811): open the
    /// mounted owner's cursor for `pattern` and drain it into a `Vec` of its ground
    /// rows. Both mount readers ride this — the values-first fact accessor
    /// ([`Self::read_mounted_facts`], which then re-filters the over-returned
    /// superset) and the resolver's per-frame candidate gather
    /// (`SearchStream::gather_extent_rows`, which defers re-filtering to its lazy
    /// per-row match against the full goal). NO re-filtering and NO error
    /// decoration here: it returns the source's (possibly over-returned) superset
    /// verbatim and the raw [`ExtentError`], so each caller narrows and names the
    /// failure in its own vocabulary (read_facts → [`ExtentReadError`]; the
    /// resolver → a lenient `[extent]` log + empty). Caller has already selected the
    /// mode into `pattern` and confirmed `functor` is mounted.
    ///
    /// A drain error drops every row — the whole read fails / the frame offers no
    /// candidates — rather than returning a partial set, because a partial extent
    /// read silently treated as complete would be unsound. In-memory sources never
    /// error per row; this is the contract for the fallible backends the write seam
    /// (WI-780) adds.
    ///
    /// When the `read_facts` Resolve policy lands (WI-774) it delegates to the
    /// resolver — which already rides this drain — rather than adding a THIRD mount
    /// path; `Resolve` IS SLD.
    pub(crate) fn drain_extent_query(
        &self,
        functor: Symbol,
        pattern: &QueryPattern,
    ) -> Result<Vec<Value>, ExtentError> {
        // A materialized profile implies a mounted owner (registration writes both
        // atomically), so this lookup cannot be `None`.
        let owner = self
            .extents
            .owner(functor)
            .expect("mounted profile implies a mounted owner");
        let mut cursor = owner.query(self, pattern)?;
        let mut out = Vec::new();
        while let Some(next) = cursor.next(self) {
            out.push(next?);
        }
        Ok(out)
    }
}

/// Build a full-arity `functor(field: …)` [`Value::Entity`] — every declared
/// `field` grounded to its `selection` value, or `filler(index, field)`. The
/// shared shape behind both values-first read builders (WI-812):
/// [`KnowledgeBase::selection_query_pattern`] (the `&self` discrim pattern; filler
/// = a distinct synthetic wildcard) and [`KnowledgeBase::enumeration_goal`] (the
/// `&mut self` Resolve goal; filler = a fresh var). The FULL field set is
/// load-bearing — see either caller: the discrim tree / resolver unify a
/// full-arity pattern against a stored fact head, which the loader pads to full
/// arity (WI-716). `pos` is empty (a record functor). The caller guarantees every
/// `selection` key is one of `fields`, so each ungrounded slot is a free column.
fn full_arity_entity_pattern(
    functor: Symbol,
    fields: &[Symbol],
    selection: &[(Symbol, Value)],
    mut filler: impl FnMut(usize, Symbol) -> Value,
) -> Value {
    let named: Vec<(Symbol, Value)> = fields
        .iter()
        .enumerate()
        .map(|(i, &f)| {
            let v = selection
                .iter()
                .find(|(s, _)| *s == f)
                .map(|(_, v)| v.clone())
                .unwrap_or_else(|| filler(i, f));
            (f, v)
        })
        .collect();
    Value::Entity {
        functor,
        pos: std::rc::Rc::from(Vec::<Value>::new()),
        named: std::rc::Rc::from(named),
    }
}

/// Digest a named-field `selection` into the query contract's `bound`: the
/// accessor's public selection is `field = value` equalities (the shape callers
/// ground), keyed as [`ArgKey::Named`] — the only vocabulary a fact head's named
/// args and a source's `query_modes` share.
fn named_selection_as_bound(selection: &[(Symbol, Value)]) -> Vec<(ArgKey, Value)> {
    selection.iter().map(|(s, v)| (ArgKey::Named(*s), v.clone())).collect()
}

/// Whether `row`'s head functor is `functor`. A mounted source owns `functor`'s
/// reads and answers with its rows; this drops a row a broken / over-broad source
/// emitted under a foreign functor — the same guard the resolver applies through
/// its full-goal `match_view_value_pattern` re-unification. A non-functor row (a
/// bare scalar) is likewise not a row of `functor`.
fn row_has_functor(kb: &KnowledgeBase, row: &Value, functor: Symbol) -> bool {
    // `functor_sym` (WI-436) reads the head symbol off both a `Functor{Some(s)}`
    // and a bare `Ref(s)` spelling, so a nullary-constructor row is matched too.
    row.head(kb).functor_sym() == Some(functor)
}

// ── The shipped reference owner ────────────────────────────────

/// The reference `ExtentSource`: an enumerable + complete + stable in-memory
/// table, **seeded at construction**, read-only in this slice (it implements
/// `owned` + `query`; mutation arrives with the write seam). It exists so the
/// mounted path is real and tested — the conformance suite mounts it and drives
/// the query contract against it — and is also the owner-swap fixture and a
/// batteries-included mountable extent for embedders. NOT a test-only mock.
///
/// Declares two modes: enumeration (`required_ground: []`) and a by-key lookup
/// (`required_ground: [id_key]`). Each row's key is extracted from its content
/// at construction (content-to-key mapping), validated total (a seeded row that
/// lacks the key is a loud error), so keyed retrieval is exercised end to end.
#[derive(Debug)]
pub struct InMemoryExtentSource {
    functor_name: String,
    profile: ExtentProfile,
    rows: Vec<Value>,
}

impl InMemoryExtentSource {
    /// Mode index of the by-key lookup mode (mode 0 is enumeration).
    pub const BY_ID_MODE: usize = 1;
    /// Mode index of the enumeration mode.
    pub const ENUMERATE_MODE: usize = 0;

    /// Seed an in-memory table for `functor_name`, keyed by `id_key`. Every row
    /// must carry `id_key` (content-to-key mapping is total) — a row that does
    /// not is a loud [`ExtentError::Backend`], never silently dropped.
    pub fn new(
        kb: &KnowledgeBase,
        functor_name: impl Into<String>,
        id_key: ArgKey,
        rows: Vec<Value>,
    ) -> Result<Self, ExtentError> {
        for (i, row) in rows.iter().enumerate() {
            if arg_at(kb, row, id_key).is_none() {
                return Err(ExtentError::Backend(format!(
                    "InMemoryExtentSource: seeded row {i} lacks its key {id_key:?}"
                )));
            }
        }
        let profile = ExtentProfile {
            query_modes: vec![
                QueryMode { required_ground: vec![] },        // ENUMERATE_MODE
                QueryMode { required_ground: vec![id_key] },  // BY_ID_MODE
            ],
            enumerable: true,
            complete: true,
            stability: Stability::Stable,
        };
        Ok(Self { functor_name: functor_name.into(), profile, rows })
    }
}

impl ExtentSource for InMemoryExtentSource {
    fn owned(&self) -> Vec<(String, ExtentProfile)> {
        vec![(self.functor_name.clone(), self.profile.clone())]
    }

    fn query(
        &self,
        kb: &KnowledgeBase,
        pattern: &QueryPattern,
    ) -> Result<Box<dyn ExtentCursor>, ExtentError> {
        // Trust the engine-chosen mode, but validate the index (loud, not a panic
        // index / silent empty). An out-of-range mode is an unsupported pattern.
        if pattern.mode >= self.profile.query_modes.len() {
            return Err(ExtentError::NoSupportedMode);
        }
        // Ground-equality pushdown: keep rows whose every `bound` slot matches.
        // This returns EXACTLY the matching rows (a complete table can afford the
        // strong end of the superset contract); a slower backend could ignore
        // `bound` and stream its whole extent, still sound.
        let matched: Vec<Value> = self
            .rows
            .iter()
            .filter(|row| bound_matches(kb, row, &pattern.bound))
            .cloned()
            .collect();
        Ok(Box::new(VecCursor { iter: matched.into_iter() }))
    }
}

/// A cursor over a materialized `Vec<Value>`. In-memory rows never error.
struct VecCursor {
    iter: std::vec::IntoIter<Value>,
}

impl ExtentCursor for VecCursor {
    fn next(&mut self, _kb: &KnowledgeBase) -> Option<Result<Value, ExtentError>> {
        self.iter.next().map(Ok)
    }
}

/// Read a row's argument at `key` as a carrier-neutral view, or `None` when the
/// row has no such slot.
fn arg_at<'a>(
    kb: &'a KnowledgeBase,
    row: &'a Value,
    key: ArgKey,
) -> Option<crate::kb::term_view::ViewItem<'a>> {
    match key {
        ArgKey::Pos(i) => row.pos_arg(kb, i as usize),
        ArgKey::Named(s) => row.named_arg(kb, s),
    }
}

/// Whether `row` satisfies every ground equality in `bound`. A slot the row
/// lacks cannot equal its bound value, so the row is excluded (sound: it is a
/// genuine non-match of `slot = value`).
fn bound_matches(kb: &KnowledgeBase, row: &Value, bound: &[(ArgKey, Value)]) -> bool {
    bound.iter().all(|(key, want)| match arg_at(kb, row, *key) {
        Some(arg) => views_structurally_equal(kb, &arg, want),
        None => false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::SymbolKind;
    use crate::kb::term::{Literal, Term, Var};
    use smallvec::SmallVec;

    // ── Fixtures ───────────────────────────────────────────────

    const ID: Symbol = Symbol::from_raw(100);
    const NAME: Symbol = Symbol::from_raw(101);

    fn func() -> Symbol {
        Symbol::from_raw(200)
    }

    /// A `functor(id: <n>, name: <s>)` row. `named` ascending by symbol raw is
    /// the non-registered canonical order (`ID` < `NAME`).
    fn row(id: i64, name: &str) -> Value {
        Value::Entity {
            functor: func(),
            pos: [].into(),
            named: [(ID, Value::Int(id)), (NAME, Value::Str(name.to_string()))].into(),
        }
    }

    fn table() -> Vec<Value> {
        vec![row(1, "alpha"), row(2, "beta"), row(3, "gamma")]
    }

    /// A `functor(id, name)` row / table carrying a GIVEN functor — a realistic
    /// MOUNTED row whose head functor IS the mounted functor (as the resolver's
    /// re-unification requires, and `read_facts`'s functor re-filter now checks).
    /// The `row` / `table` fixtures above fix `func()`, fine for the direct-`query`
    /// conformance tests (they never re-filter on the functor); `read_facts`
    /// mounted tests need the functor to match the mount.
    fn row_f(functor: Symbol, id: i64, name: &str) -> Value {
        Value::Entity {
            functor,
            pos: [].into(),
            named: [(ID, Value::Int(id)), (NAME, Value::Str(name.to_string()))].into(),
        }
    }

    fn table_f(functor: Symbol) -> Vec<Value> {
        vec![row_f(functor, 1, "alpha"), row_f(functor, 2, "beta"), row_f(functor, 3, "gamma")]
    }

    fn source(kb: &KnowledgeBase) -> InMemoryExtentSource {
        InMemoryExtentSource::new(kb, "test.Item", ArgKey::Named(ID), table())
            .expect("well-formed seed")
    }

    /// Drive `source` the way the engine will (WI-797): select a mode from the
    /// ground slots (`None` → loud `NoSupportedMode`), then drain the cursor.
    fn engine_query(
        kb: &KnowledgeBase,
        src: &dyn ExtentSource,
        profile: &ExtentProfile,
        bound: Vec<(ArgKey, Value)>,
    ) -> Result<Vec<Value>, ExtentError> {
        let ground: Vec<ArgKey> = bound.iter().map(|(k, _)| *k).collect();
        let mode = profile.select_mode(&ground).ok_or(ExtentError::NoSupportedMode)?;
        let pattern = QueryPattern { mode, bound };
        drain(kb, src.query(kb, &pattern)?)
    }

    fn drain(
        kb: &KnowledgeBase,
        mut cursor: Box<dyn ExtentCursor>,
    ) -> Result<Vec<Value>, ExtentError> {
        let mut out = Vec::new();
        while let Some(r) = cursor.next(kb) {
            out.push(r?);
        }
        Ok(out)
    }

    fn ids(kb: &KnowledgeBase, rows: &[Value]) -> Vec<i64> {
        let mut v: Vec<i64> = rows
            .iter()
            .map(|r| match arg_at(kb, r, ArgKey::Named(ID)).map(|a| a.to_value()) {
                Some(Value::Int(n)) => n,
                other => panic!("row without Int id: {other:?}"),
            })
            .collect();
        v.sort();
        v
    }

    // ── Query contract: declared mode answers / undeclared refused ──

    #[test]
    fn declared_by_id_mode_answers() {
        let kb = KnowledgeBase::new();
        let src = source(&kb);
        let got = engine_query(
            &kb,
            &src,
            &src.profile,
            vec![(ArgKey::Named(ID), Value::Int(2))],
        )
        .expect("by_id is a declared mode");
        assert_eq!(ids(&kb, &got), vec![2]);
    }

    #[test]
    fn enumeration_mode_answers_whole_table() {
        let kb = KnowledgeBase::new();
        let src = source(&kb);
        // Via engine mode-selection (all-free goal → enumeration).
        let got = engine_query(&kb, &src, &src.profile, vec![]).expect("enumerable");
        assert_eq!(ids(&kb, &got), vec![1, 2, 3]);
        // And via a direct query on the declared enumeration mode index, pinning
        // the reference source's mode layout.
        let pattern = QueryPattern {
            mode: InMemoryExtentSource::ENUMERATE_MODE,
            bound: vec![],
        };
        let direct = drain(&kb, src.query(&kb, &pattern).unwrap()).unwrap();
        assert_eq!(ids(&kb, &direct), vec![1, 2, 3]);
    }

    #[test]
    fn undeclared_pattern_yields_no_supported_mode() {
        let kb = KnowledgeBase::new();
        let src = source(&kb);
        // Refusal is visible only on a source WITHOUT an enumeration mode (an
        // enumeration mode would answer any all-free goal). Use an oracle-shaped
        // profile: keyed-only, non-enumerable.
        let oracle = ExtentProfile {
            query_modes: vec![QueryMode { required_ground: vec![ArgKey::Named(ID)] }],
            enumerable: false,
            complete: true,
            stability: Stability::Stable,
        };
        // An all-free goal (enumeration) against a non-enumerable source: no mode
        // applies → the engine refuses it loud.
        assert_eq!(oracle.select_mode(&[]), None);
        let err = engine_query(&kb, &src, &oracle, vec![]).unwrap_err();
        assert!(matches!(err, ExtentError::NoSupportedMode));
    }

    #[test]
    fn out_of_range_mode_is_refused_by_query() {
        let kb = KnowledgeBase::new();
        let src = source(&kb);
        let bad = QueryPattern { mode: 99, bound: vec![] };
        assert!(matches!(src.query(&kb, &bad), Err(ExtentError::NoSupportedMode)));
    }

    // ── Query contract: ground-equality pushdown ───────────────

    #[test]
    fn ground_equality_pushdown_filters_to_the_match() {
        let kb = KnowledgeBase::new();
        let src = source(&kb);
        // A by_id query pushes the `id = 3` equality down; InMemory returns
        // exactly the matching row (the strong end of the superset contract).
        let got = engine_query(
            &kb,
            &src,
            &src.profile,
            vec![(ArgKey::Named(ID), Value::Int(3))],
        )
        .unwrap();
        assert_eq!(ids(&kb, &got), vec![3]);
    }

    // ── Query contract: soundness (under-return fails / over-return passes) ──

    /// The soundness predicate: `query` must return a SUPERSET of the rows
    /// satisfying `bound`. Returns `Err` naming a missing row (the under-return
    /// violation this catches); over-return is fine and returns `Ok`.
    fn assert_query_superset(
        kb: &KnowledgeBase,
        src: &dyn ExtentSource,
        pattern: &QueryPattern,
        expected_matches: &[Value],
    ) -> Result<Vec<Value>, String> {
        let got = drain(kb, src.query(kb, pattern).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
        for want in expected_matches {
            if !got.iter().any(|g| views_structurally_equal(kb, g, want)) {
                return Err(format!("under-return: missing row satisfying bound: {want:?}"));
            }
        }
        Ok(got)
    }

    /// A backend that drops the rows satisfying `bound` — the under-return bug,
    /// precisely: it returns exactly the NON-matches, so every genuine match is
    /// missing regardless of row order.
    struct UnderReturnSource {
        rows: Vec<Value>,
    }
    impl ExtentSource for UnderReturnSource {
        fn owned(&self) -> Vec<(String, ExtentProfile)> {
            vec![]
        }
        fn query(
            &self,
            kb: &KnowledgeBase,
            pattern: &QueryPattern,
        ) -> Result<Box<dyn ExtentCursor>, ExtentError> {
            let kept: Vec<Value> = self
                .rows
                .iter()
                .filter(|row| !bound_matches(kb, row, &pattern.bound))
                .cloned()
                .collect();
            Ok(Box::new(VecCursor { iter: kept.into_iter() }))
        }
    }

    /// A backend that ignores `bound` and streams its whole extent — over-return.
    struct OverReturnSource {
        rows: Vec<Value>,
    }
    impl ExtentSource for OverReturnSource {
        fn owned(&self) -> Vec<(String, ExtentProfile)> {
            vec![]
        }
        fn query(
            &self,
            _kb: &KnowledgeBase,
            _pattern: &QueryPattern,
        ) -> Result<Box<dyn ExtentCursor>, ExtentError> {
            Ok(Box::new(VecCursor { iter: self.rows.clone().into_iter() }))
        }
    }

    #[test]
    fn under_return_fails_conformance() {
        let kb = KnowledgeBase::new();
        // Bound `id = 1`; the only match is row(1), which UnderReturnSource drops.
        let pattern = QueryPattern {
            mode: 0,
            bound: vec![(ArgKey::Named(ID), Value::Int(1))],
        };
        let bad = UnderReturnSource { rows: table() };
        let verdict = assert_query_superset(&kb, &bad, &pattern, &[row(1, "alpha")]);
        assert!(verdict.is_err(), "under-return must FAIL soundness: {verdict:?}");
    }

    #[test]
    fn over_return_passes_conformance_and_caller_refilters() {
        let kb = KnowledgeBase::new();
        let pattern = QueryPattern {
            mode: 0,
            bound: vec![(ArgKey::Named(ID), Value::Int(2))],
        };
        let over = OverReturnSource { rows: table() };
        // Superset holds → PASSES (over-return is sound).
        let got = assert_query_superset(&kb, &over, &pattern, &[row(2, "beta")])
            .expect("over-return satisfies the superset contract");
        // The caller re-filters against `bound` (as the engine's re-unification
        // does), leaving exactly the true match.
        let refiltered: Vec<Value> =
            got.into_iter().filter(|r| bound_matches(&kb, r, &pattern.bound)).collect();
        assert_eq!(ids(&kb, &refiltered), vec![2]);
    }

    #[test]
    fn in_memory_source_passes_conformance() {
        let kb = KnowledgeBase::new();
        let src = source(&kb);
        let pattern = QueryPattern {
            mode: InMemoryExtentSource::BY_ID_MODE,
            bound: vec![(ArgKey::Named(ID), Value::Int(2))],
        };
        assert_query_superset(&kb, &src, &pattern, &[row(2, "beta")])
            .expect("the reference source is sound");
    }

    // ── Content-to-key mapping validated at seed ───────────────

    #[test]
    fn seeding_a_keyless_row_is_a_loud_error() {
        let kb = KnowledgeBase::new();
        // A row lacking the `id` key — content-to-key mapping is total, so seeding
        // must refuse it loudly rather than silently drop it.
        let keyless = Value::Entity {
            functor: func(),
            pos: [].into(),
            named: [(NAME, Value::Str("orphan".into()))].into(),
        };
        let err = InMemoryExtentSource::new(&kb, "test.Item", ArgKey::Named(ID), vec![keyless])
            .unwrap_err();
        assert!(matches!(err, ExtentError::Backend(_)));
    }

    // ── Registration: single-owner, volatile-single-mode, deferred gates ──

    /// A minimal source owning one functor with a caller-chosen profile — for
    /// exercising `register_extent_owner`'s checks without a real backend.
    struct ProfiledSource {
        name: String,
        profile: ExtentProfile,
    }
    impl ExtentSource for ProfiledSource {
        fn owned(&self) -> Vec<(String, ExtentProfile)> {
            vec![(self.name.clone(), self.profile.clone())]
        }
        fn query(
            &self,
            _kb: &KnowledgeBase,
            _pattern: &QueryPattern,
        ) -> Result<Box<dyn ExtentCursor>, ExtentError> {
            Ok(Box::new(VecCursor { iter: Vec::new().into_iter() }))
        }
    }

    fn stable_profile(modes: Vec<QueryMode>, enumerable: bool) -> ExtentProfile {
        ExtentProfile { query_modes: modes, enumerable, complete: true, stability: Stability::Stable }
    }

    /// Define `qname` so `resolve_name_in_global` finds it (registration resolves
    /// owned names to symbols).
    fn define(kb: &mut KnowledgeBase, qname: &str) -> Symbol {
        let short = qname.rsplit('.').next().unwrap();
        kb.symbols.define_qualified_only(short, qname, SymbolKind::Sort, 0)
    }

    #[test]
    fn happy_path_registers_owner_and_profile() {
        let mut kb = KnowledgeBase::new();
        let sym = define(&mut kb, "test.Widget");
        let src = ProfiledSource {
            name: "test.Widget".into(),
            profile: stable_profile(vec![QueryMode { required_ground: vec![] }], true),
        };
        let id = kb.register_extent_owner(Box::new(src)).expect("stable+enumerable registers");
        assert!(kb.extent_owner(sym).is_some());
        assert!(kb.extent_profile(sym).is_some());
        // The SourceId indexes the slab.
        assert_eq!(id, SourceId(0));
    }

    #[test]
    fn unresolvable_name_is_loud() {
        let mut kb = KnowledgeBase::new();
        let src = ProfiledSource {
            name: "test.NeverDefined".into(),
            profile: stable_profile(vec![QueryMode { required_ground: vec![] }], true),
        };
        let err = kb.register_extent_owner(Box::new(src)).unwrap_err();
        assert!(matches!(err, ExtentRegError::UnresolvableName(_)));
    }

    #[test]
    fn single_owner_is_enforced() {
        let mut kb = KnowledgeBase::new();
        define(&mut kb, "test.Widget");
        let mk = || ProfiledSource {
            name: "test.Widget".into(),
            profile: stable_profile(vec![QueryMode { required_ground: vec![] }], true),
        };
        kb.register_extent_owner(Box::new(mk())).expect("first owner");
        let err = kb.register_extent_owner(Box::new(mk())).unwrap_err();
        assert!(matches!(err, ExtentRegError::AlreadyOwned { .. }));
    }

    #[test]
    fn volatile_single_mode_is_enforced() {
        let mut kb = KnowledgeBase::new();
        define(&mut kb, "test.Feed");
        let two_modes = vec![
            QueryMode { required_ground: vec![] },
            QueryMode { required_ground: vec![ArgKey::Named(ID)] },
        ];
        let src = ProfiledSource {
            name: "test.Feed".into(),
            profile: ExtentProfile {
                query_modes: two_modes,
                enumerable: true,
                complete: true,
                stability: Stability::Volatile,
            },
        };
        let err = kb.register_extent_owner(Box::new(src)).unwrap_err();
        // The multi-mode violation surfaces as itself, ahead of the v1 volatile gate.
        assert!(matches!(err, ExtentRegError::VolatileMultiMode { modes: 2, .. }));
    }

    #[test]
    fn volatile_is_refused_in_v1() {
        let mut kb = KnowledgeBase::new();
        define(&mut kb, "test.Feed");
        let src = ProfiledSource {
            name: "test.Feed".into(),
            profile: ExtentProfile {
                query_modes: vec![QueryMode { required_ground: vec![ArgKey::Named(ID)] }],
                enumerable: true,
                complete: true,
                stability: Stability::Volatile,
            },
        };
        let err = kb.register_extent_owner(Box::new(src)).unwrap_err();
        assert!(matches!(err, ExtentRegError::VolatileUnsupported { .. }));
    }

    #[test]
    fn non_enumerable_is_refused_in_v1() {
        let mut kb = KnowledgeBase::new();
        define(&mut kb, "test.Oracle");
        let src = ProfiledSource {
            name: "test.Oracle".into(),
            profile: stable_profile(
                vec![QueryMode { required_ground: vec![ArgKey::Named(ID)] }],
                false,
            ),
        };
        let err = kb.register_extent_owner(Box::new(src)).unwrap_err();
        assert!(matches!(err, ExtentRegError::NonEnumerable { .. }));
    }

    // ── select_mode: most-specific-first ───────────────────────

    #[test]
    fn select_mode_prefers_the_most_specific() {
        let profile = stable_profile(
            vec![
                QueryMode { required_ground: vec![] },
                QueryMode { required_ground: vec![ArgKey::Named(ID)] },
            ],
            true,
        );
        // All-free → only enumeration applies.
        assert_eq!(profile.select_mode(&[]), Some(0));
        // id ground → the keyed mode is more specific and wins.
        assert_eq!(profile.select_mode(&[ArgKey::Named(ID)]), Some(1));
    }

    // ── read_facts (WI-773): the values-first accessor ─────────

    /// A ground resident fact `wi(id: <n>, tag: <t>)` interned into `kb`, so
    /// `rules_by_functor` finds it — the resident counterpart of the `row`
    /// fixture (which builds a raw `Value` for the mounted path).
    fn assert_wi_fact(kb: &mut KnowledgeBase, f: Symbol, id_field: Symbol, tag_field: Symbol, id: i64, tag: &str) {
        let sort = kb.make_name_term("Test");
        let domain = kb.make_name_term("test");
        let id_t = kb.alloc(Term::Const(Literal::Int(id)));
        let tag_t = kb.alloc(Term::Const(Literal::String(tag.to_string())));
        let head = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: [(id_field, id_t), (tag_field, tag_t)].into(),
        });
        kb.assert_fact(head, sort, domain, None);
    }

    #[test]
    fn read_facts_reads_resident_facts_and_filters_by_selection() {
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("wi");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");
        for (id, tag) in [(1, "a"), (2, "b"), (3, "a")] {
            assert_wi_fact(&mut kb, f, id_field, tag_field, id, tag);
        }
        // Empty selection = enumeration: every fact.
        let all = kb.read_facts(f, &[], BodiedRulePolicy::Refuse).expect("facts only");
        assert_eq!(all.len(), 3);
        // Named-field selection = superset filter: `tag = "a"` keeps two.
        let tagged_a = kb
            .read_facts(f, &[(tag_field, Value::Str("a".into()))], BodiedRulePolicy::Refuse)
            .expect("facts only");
        assert_eq!(tagged_a.len(), 2);
        // A selection that matches nothing returns empty (not an error).
        let none = kb
            .read_facts(f, &[(tag_field, Value::Str("z".into()))], BodiedRulePolicy::Refuse)
            .expect("facts only");
        assert!(none.is_empty());
    }

    #[test]
    fn read_facts_returns_values_not_rule_ids() {
        // The public read shape is values-first (057 R1): each returned row is the
        // fact's head `Value`, readable carrier-neutrally — never a `RuleId`.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("wi");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");
        assert_wi_fact(&mut kb, f, id_field, tag_field, 7, "a");
        let rows = kb.read_facts(f, &[], BodiedRulePolicy::Refuse).unwrap();
        assert_eq!(rows.len(), 1);
        // The row is a usable value: its `id` field reads back as 7.
        match rows[0].named_arg(&kb, id_field).map(|a| a.to_value()) {
            Some(Value::Term { id, .. }) => {
                assert!(matches!(kb.get_term(id), Term::Const(Literal::Int(7))));
            }
            other => panic!("expected an id field, got {other:?}"),
        }
    }

    #[test]
    fn read_facts_refuse_names_the_bodied_rule() {
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("wi");
        let g = kb.intern("g");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");
        // A matching FACT is asserted FIRST, then the bodied rule — pinning the
        // WI-772 landmine: a fact enumerated ahead of the bodied rule must not
        // hide the refusal (the loop early-returns only on the bodied rule, never
        // on a selection match).
        assert_wi_fact(&mut kb, f, id_field, tag_field, 1, "a");
        let sort = kb.make_name_term("Test");
        let domain = kb.make_name_term("test");
        let x_sym = kb.intern("x");
        let x = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(x)));
        let head = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_elem((id_field, var_x), 1),
        });
        let body = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![body], sort, domain, None);

        let err = kb.read_facts(f, &[], BodiedRulePolicy::Refuse).unwrap_err();
        match err {
            ExtentReadError::BodiedRule { functor, rule } => {
                assert_eq!(functor, "wi");
                // The message renders the rule (`head :- body`) so the caller
                // names the offender, not just "a bodied rule exists".
                assert!(rule.contains(":-"), "rendered as head :- body: {rule}");
                assert!(rule.contains('g'), "names the body atom: {rule}");
            }
            other => panic!("expected BodiedRule, got {other:?}"),
        }
    }

    #[test]
    fn read_facts_pushes_a_selection_down_through_the_discrim_tree() {
        // WI-812: a functor WITH a declared field schema takes the discrim
        // pushdown path (`selection_query_pattern` + `query_fact_heads`), not the
        // bucket scan. Correctness must match the scan for every selection shape.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("Item");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");
        // Declaring the field schema is what routes reads through the discrim tree.
        kb.register_entity_fields(f, vec![id_field, tag_field]);
        for (id, tag) in [(1, "a"), (2, "b"), (3, "a")] {
            assert_wi_fact(&mut kb, f, id_field, tag_field, id, tag);
        }
        // Selection on the less-selective field: `tag = "a"` keeps two rows.
        let tagged_a = kb
            .read_facts(f, &[(tag_field, Value::Str("a".into()))], BodiedRulePolicy::Refuse)
            .expect("facts only");
        assert_eq!(tagged_a.len(), 2);
        // Selection on the key field: `id = 2` keeps exactly one, and it is the
        // row whose `id` field is 2 (not some other row the pushdown misfiled).
        let by_id = kb
            .read_facts(f, &[(id_field, Value::Int(2))], BodiedRulePolicy::Refuse)
            .expect("facts only");
        assert_eq!(by_id.len(), 1);
        match by_id[0].named_arg(&kb, id_field).map(|a| a.to_value()) {
            Some(Value::Term { id, .. }) => {
                assert!(matches!(kb.get_term(id), Term::Const(Literal::Int(2))));
            }
            other => panic!("expected an id field of 2, got {other:?}"),
        }
        // A no-match selection is empty (not an error); empty selection enumerates.
        assert!(kb
            .read_facts(f, &[(id_field, Value::Int(9))], BodiedRulePolicy::Refuse)
            .unwrap()
            .is_empty());
        assert_eq!(kb.read_facts(f, &[], BodiedRulePolicy::Refuse).unwrap().len(), 3);
        // A selection on a field the schema does NOT declare falls back to
        // enumeration + `bound_matches` (no fact carries it → empty), never a panic.
        let ghost = kb.intern("ghost");
        assert!(kb
            .read_facts(f, &[(ghost, Value::Int(1))], BodiedRulePolicy::Refuse)
            .unwrap()
            .is_empty());
    }

    #[test]
    fn read_facts_discrim_pushdown_with_multiple_wildcard_fields() {
        // WI-812: a THREE-field schema selected on ONE field leaves TWO wildcard
        // positions — the case the 2-field tests don't exercise. Pins that the
        // discrim walk collects each matching leaf exactly ONCE (no duplicate rows)
        // across multiple wildcard-skip descents, and returns exactly the matches.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("Triple");
        let a = kb.intern("a");
        let b = kb.intern("b");
        let c = kb.intern("c");
        kb.register_entity_fields(f, vec![a, b, c]);
        let assert_triple = |kb: &mut KnowledgeBase, av: i64, bv: i64, cv: i64| {
            let sort = kb.make_name_term("Test");
            let domain = kb.make_name_term("test");
            let at = kb.alloc(Term::Const(Literal::Int(av)));
            let bt = kb.alloc(Term::Const(Literal::Int(bv)));
            let ct = kb.alloc(Term::Const(Literal::Int(cv)));
            let head = kb.alloc(Term::Fn {
                functor: f,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(a, at), (b, bt), (c, ct)]),
            });
            kb.assert_fact(head, sort, domain, None);
        };
        // Two rows share a=1 (so the a-selection has two matches, each with distinct
        // b,c wildcards); one row has a=2.
        assert_triple(&mut kb, 1, 10, 100);
        assert_triple(&mut kb, 1, 20, 200);
        assert_triple(&mut kb, 2, 30, 300);
        // Select on `a` only → two wildcard fields (b, c). Exactly two rows, no dupes.
        let a1 = kb
            .read_facts(f, &[(a, Value::Int(1))], BodiedRulePolicy::Refuse)
            .expect("facts only");
        assert_eq!(a1.len(), 2, "two a=1 rows, each collected once (no duplication)");
        // Every returned row genuinely carries a=1 (the wildcards didn't smear).
        for row in &a1 {
            match row.named_arg(&kb, a).map(|x| x.to_value()) {
                Some(Value::Term { id, .. }) => {
                    assert!(matches!(kb.get_term(id), Term::Const(Literal::Int(1))));
                }
                other => panic!("expected a=1, got {other:?}"),
            }
        }
        // Select on the middle field `b` (wildcards a and c) → one row.
        let b20 = kb
            .read_facts(f, &[(b, Value::Int(20))], BodiedRulePolicy::Refuse)
            .expect("facts only");
        assert_eq!(b20.len(), 1);
    }

    #[test]
    fn has_bodied_rule_gate_tracks_assert_and_retract() {
        // WI-812: the O(1) gate mirrors "does this functor's bucket hold any bodied
        // rule?" across asserts and retracts — a COUNT, so removing one of several
        // bodied rules leaves it set.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("wi");
        let g = kb.intern("g");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");

        // A pure table: facts only → gate is false.
        assert_wi_fact(&mut kb, f, id_field, tag_field, 1, "a");
        assert_wi_fact(&mut kb, f, id_field, tag_field, 2, "b");
        assert!(!kb.has_bodied_rule(f));

        // Assert two bodied rules under `f`.
        let mk_rule = |kb: &mut KnowledgeBase| {
            let sort = kb.make_name_term("Test");
            let domain = kb.make_name_term("test");
            let x = kb.fresh_var(id_field);
            let var_x = kb.alloc(Term::Var(Var::Global(x)));
            let head = kb.alloc(Term::Fn {
                functor: f,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_elem((id_field, var_x), 1),
            });
            let body = kb.alloc(Term::Fn {
                functor: g,
                pos_args: SmallVec::from_elem(var_x, 1),
                named_args: SmallVec::new(),
            });
            kb.assert_rule(head, vec![body], sort, domain, None)
        };
        let r1 = mk_rule(&mut kb);
        assert!(kb.has_bodied_rule(f));
        let r2 = mk_rule(&mut kb);
        assert!(kb.has_bodied_rule(f));

        // Retracting ONE of two bodied rules leaves the gate set (count semantics).
        kb.retract(r1);
        assert!(kb.has_bodied_rule(f), "one bodied rule remains");
        // Retracting the last clears it — back to a pure table.
        kb.retract(r2);
        assert!(!kb.has_bodied_rule(f));
        // Idempotent double-retract must not underflow the count.
        kb.retract(r2);
        assert!(!kb.has_bodied_rule(f));
    }

    #[test]
    fn read_facts_refuses_a_bodied_rule_no_selection_would_match() {
        // WI-812: the blanket refusal is SELECTION-INDEPENDENT — the O(1) gate
        // fires even for a selection whose match is a plain fact and whose value
        // the bodied rule's head could never carry. This is the WI-770/772 blanket
        // contract the gate preserves after the row read stopped being a full scan.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("Item");
        let g = kb.intern("g");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");
        kb.register_entity_fields(f, vec![id_field, tag_field]);
        assert_wi_fact(&mut kb, f, id_field, tag_field, 1, "a");
        // A bodied rule under `f` with a head `Item(id: ?x)` — a different arity, so
        // the `id = 1` selection below would never structurally reach it.
        let sort = kb.make_name_term("Test");
        let domain = kb.make_name_term("test");
        let x = kb.fresh_var(id_field);
        let var_x = kb.alloc(Term::Var(Var::Global(x)));
        let head = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_elem((id_field, var_x), 1),
        });
        let body = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![body], sort, domain, None);

        // A selection that matches the fact (id = 1) still refuses, because the gate
        // is functor-wide, not selection-scoped.
        let err = kb
            .read_facts(f, &[(id_field, Value::Int(1))], BodiedRulePolicy::Refuse)
            .unwrap_err();
        assert!(matches!(err, ExtentReadError::BodiedRule { .. }));
    }

    #[test]
    fn read_facts_reads_a_mounted_extent_uniformly() {
        // The mounted arm answers through the SAME accessor — the caller does not
        // see that a source, not the discrim tree, produced the rows.
        let mut kb = KnowledgeBase::new();
        let item = define(&mut kb, "test.Item");
        let src = InMemoryExtentSource::new(&kb, "test.Item", ArgKey::Named(ID), table_f(item))
            .expect("well-formed seed");
        kb.register_extent_owner(Box::new(src)).expect("stable+enumerable registers");
        // Enumeration (empty selection) streams the whole table.
        let all = kb.read_facts(item, &[], BodiedRulePolicy::Refuse).expect("enumerable");
        assert_eq!(ids(&kb, &all), vec![1, 2, 3]);
        // Selection pushdown: `id = 2` takes the keyed mode and returns one row.
        let one = kb
            .read_facts(item, &[(ID, Value::Int(2))], BodiedRulePolicy::Refuse)
            .expect("by-id is a declared mode");
        assert_eq!(ids(&kb, &one), vec![2]);
    }

    /// A mounted owner that OVER-returns — it ignores `bound` and streams its
    /// whole table (a sound backend, 057 §"query contract" rule 3). Distinct from
    /// the test-only `OverReturnSource` above in that it `owned()`s a functor, so
    /// it can be MOUNTED and drive `read_facts`.
    struct OverReturningOwner {
        name: String,
        rows: Vec<Value>,
    }
    impl ExtentSource for OverReturningOwner {
        fn owned(&self) -> Vec<(String, ExtentProfile)> {
            vec![(
                self.name.clone(),
                stable_profile(
                    vec![
                        QueryMode { required_ground: vec![] },
                        QueryMode { required_ground: vec![ArgKey::Named(ID)] },
                    ],
                    true,
                ),
            )]
        }
        fn query(
            &self,
            _kb: &KnowledgeBase,
            _pattern: &QueryPattern,
        ) -> Result<Box<dyn ExtentCursor>, ExtentError> {
            Ok(Box::new(VecCursor { iter: self.rows.clone().into_iter() }))
        }
    }

    #[test]
    fn read_facts_refilters_an_over_returning_mount() {
        // `read_facts`'s OWN superset re-filter — not the source's — is the guard
        // here: the owner streams all three rows regardless of the selection, so
        // the accessor must narrow to the true match itself. (InMemoryExtentSource
        // returns exact matches, so it cannot exercise this path.)
        let mut kb = KnowledgeBase::new();
        let item = define(&mut kb, "test.Item");
        let src = OverReturningOwner { name: "test.Item".into(), rows: table_f(item) };
        kb.register_extent_owner(Box::new(src)).expect("stable+enumerable registers");
        let got = kb
            .read_facts(item, &[(ID, Value::Int(2))], BodiedRulePolicy::Refuse)
            .expect("enumerable");
        assert_eq!(ids(&kb, &got), vec![2]);
    }

    #[test]
    fn read_facts_drops_a_foreign_functor_row_from_a_mount() {
        // A broken / over-broad source emits a row under the WRONG functor.
        // `read_facts`'s functor re-filter drops it — matching the resolver's
        // full-goal re-unification — so a foreign row carrying the selected key
        // does NOT leak through (the guard `bound_matches` alone would miss).
        let mut kb = KnowledgeBase::new();
        let item = define(&mut kb, "test.Item");
        let other = define(&mut kb, "test.Other");
        let rows = vec![
            row_f(item, 2, "beta"),     // correct functor, selected id
            row_f(other, 2, "foreign"), // FOREIGN functor, same id
        ];
        let src = OverReturningOwner { name: "test.Item".into(), rows };
        kb.register_extent_owner(Box::new(src)).expect("stable+enumerable registers");
        let got = kb
            .read_facts(item, &[(ID, Value::Int(2))], BodiedRulePolicy::Refuse)
            .expect("enumerable");
        assert_eq!(got.len(), 1, "only the correctly-functored row survives");
        assert_eq!(got[0].head(&kb).functor_sym(), Some(item));
    }

    // ── read_facts_resolved (WI-774): the Resolve read ─────────────

    /// Assert a GUARDED bodied rule `f(id: <id>, tag: <tag>) :- guard()` — a
    /// realization-shaped derivation whose head is a row iff `guard()` succeeds.
    /// The shape WI-770's blanket refusal rejects and WI-774's Resolve evaluates.
    fn assert_guarded_wi_rule(
        kb: &mut KnowledgeBase,
        f: Symbol,
        id_field: Symbol,
        tag_field: Symbol,
        id: i64,
        tag: &str,
        guard: Symbol,
    ) {
        let sort = kb.make_name_term("Test");
        let domain = kb.make_name_term("test");
        let id_t = kb.alloc(Term::Const(Literal::Int(id)));
        let tag_t = kb.alloc(Term::Const(Literal::String(tag.to_string())));
        let head = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: [(id_field, id_t), (tag_field, tag_t)].into(),
        });
        let body = kb.alloc(Term::Fn {
            functor: guard,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![body], sort, domain, None);
    }

    /// Assert a nullary ground fact `f()` — a guard that succeeds.
    fn assert_nullary_fact(kb: &mut KnowledgeBase, f: Symbol) {
        let sort = kb.make_name_term("Test");
        let domain = kb.make_name_term("test");
        let head = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(head, sort, domain, None);
    }

    /// The sorted `id` ints of a set of resolved rows (each a reified
    /// `Value::Entity` whose `id` child is a `Const(Int)`).
    fn resolved_ids(kb: &KnowledgeBase, rows: &[Value], id_field: Symbol) -> Vec<i64> {
        let mut v: Vec<i64> = rows
            .iter()
            .filter_map(|r| match r.named_arg(kb, id_field).map(|a| a.to_value()) {
                Some(Value::Term { id, .. }) => match kb.get_term(id) {
                    Term::Const(Literal::Int(n)) => Some(*n),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        v.sort();
        v
    }

    #[test]
    fn read_facts_resolved_enumerates_resident_facts() {
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("wi");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");
        kb.register_entity_fields(f, vec![id_field, tag_field]);
        for (id, tag) in [(1, "a"), (2, "b")] {
            assert_wi_fact(&mut kb, f, id_field, tag_field, id, tag);
        }
        let all = kb.read_facts_resolved(f, &[]).expect("resolves");
        assert_eq!(resolved_ids(&kb, &all, id_field), vec![1, 2]);
    }

    #[test]
    fn read_facts_resolved_honors_a_passing_bodied_rule_guard() {
        // The genuine CONTRAST with `Refuse`: a bodied rule is RESOLVED, not
        // rejected, so its guard is honored. `enabled()` present → the derived row
        // (id 3) joins the resident facts.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("wi");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");
        let enabled = kb.intern("enabled");
        kb.register_entity_fields(f, vec![id_field, tag_field]);
        assert_wi_fact(&mut kb, f, id_field, tag_field, 1, "a");
        assert_wi_fact(&mut kb, f, id_field, tag_field, 2, "b");
        assert_guarded_wi_rule(&mut kb, f, id_field, tag_field, 3, "c", enabled);
        assert_nullary_fact(&mut kb, enabled);
        let all = kb.read_facts_resolved(f, &[]).expect("resolves, guard honored");
        assert_eq!(resolved_ids(&kb, &all, id_field), vec![1, 2, 3]);
        // The SAME bodied rule is REFUSED by `Refuse` (the WI-770 shape) — proving
        // the two policies genuinely differ on a bodied candidate, not by accident.
        assert!(matches!(
            kb.read_facts(f, &[], BodiedRulePolicy::Refuse),
            Err(ExtentReadError::BodiedRule { .. })
        ));
    }

    #[test]
    fn read_facts_resolved_omits_a_row_whose_guard_fails() {
        // Guard `enabled()` ABSENT → the derived row does NOT appear, and (unlike
        // Refuse) resolving the bodied rule is NOT an error — the row is simply not
        // proved. This is the over-refusal WI-770 caused and WI-774 fixes.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("wi");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");
        let enabled = kb.intern("enabled");
        kb.register_entity_fields(f, vec![id_field, tag_field]);
        assert_wi_fact(&mut kb, f, id_field, tag_field, 1, "a");
        assert_guarded_wi_rule(&mut kb, f, id_field, tag_field, 3, "c", enabled);
        // `enabled()` is NOT asserted → the guard fails.
        let all = kb.read_facts_resolved(f, &[]).expect("resolves");
        assert_eq!(resolved_ids(&kb, &all, id_field), vec![1]);
    }

    #[test]
    fn read_facts_resolved_grounds_a_selection_field() {
        // A named-field selection grounds that slot in the goal (a `Value::Str`
        // unifies with the fact's `Const(String)` field — the shape cpp-gen uses to
        // ground `LanguageMapping.language`).
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("wi");
        let id_field = kb.intern("id");
        let tag_field = kb.intern("tag");
        kb.register_entity_fields(f, vec![id_field, tag_field]);
        for (id, tag) in [(1, "a"), (2, "b"), (3, "a")] {
            assert_wi_fact(&mut kb, f, id_field, tag_field, id, tag);
        }
        let a = kb
            .read_facts_resolved(f, &[(tag_field, Value::Str("a".into()))])
            .expect("resolves");
        assert_eq!(resolved_ids(&kb, &a, id_field), vec![1, 3]);
    }

    #[test]
    fn read_facts_resolved_refuses_a_functor_without_a_field_schema() {
        // No registered entity-field schema → no full-arity goal can be built; a
        // loud refusal, not a silent empty read.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("schemaless");
        let err = kb.read_facts_resolved(f, &[]).unwrap_err();
        assert!(matches!(err, ExtentReadError::NoFieldSchema { .. }));
    }
}
