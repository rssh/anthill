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
//! Wiring the mount into resolution and load — discrim mounts, tagged candidates,
//! retiring `RouteHandler` / `Store::retrieve` into `query` (retirement stage R2),
//! and the loader's single-owner refusal on resident collisions — is the sibling
//! item WI-797. The values-first `read_facts` accessor is WI-773. The write half
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

/// KB-owned aggregate of extent sources — successor to `route::RouteRegistry`.
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
    ///    (single-owner). Resident-collision refusal (a functor with resident
    ///    facts/rules) lands with the loader wiring, WI-797.
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
}
