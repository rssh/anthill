/// Unified KnowledgeBase — hash-consed terms, facts, indexes, sort lattice.
///
/// One struct maintains everything. Sort relations are facts; entity-of
/// indexes are materialized alongside other indexes.
///
/// See: docs/stage0/rust-term-store-design.md §7, §9 (Layer 0)

pub mod term;
pub mod subst;
pub mod load;
pub mod resolve;
pub mod occurrence;
pub mod node_occurrence;
pub mod typing;
pub(crate) mod region;
pub(crate) mod flow_derive;
pub mod op_info;
pub mod op_requirements;
pub mod req_insertion;
pub mod simp_rewrite;
pub mod term_view;
pub mod execute;
pub mod route;
pub(crate) mod persist_subst;
pub(crate) mod discrim;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::{SymbolTable, SymbolDef, SymbolKind, Symbol};
use crate::span::{SourceRegistry, SourceSpan};
use term::{Term, TermId, TermStore, TermSource, Var, VarId};
use node_occurrence::NodeOccurrence;
use discrim::SubstTree;
use resolve::BuiltinTag;

// ── Rule handle ─────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct RuleId(u32);

impl RuleId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn from_index(index: usize) -> Self {
        RuleId(index as u32)
    }

    pub fn from_raw(raw: u32) -> Self {
        RuleId(raw)
    }

    pub fn raw(self) -> u32 {
        self.0
    }
}

/// Backwards-compatible alias.
pub type FactId = RuleId;

// ── Constraint handle ───────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ConstraintId(u32);

impl ConstraintId {
    pub fn index(self) -> usize { self.0 as usize }
    pub fn raw(self) -> u32 { self.0 }
}

// ── Guard types ─────────────────────────────────────────────────

/// Classification of a guard for optimized checking.
#[derive(Clone, Debug)]
#[allow(dead_code)]
enum GuardKind {
    /// Functional dependency: at most one fact with these key field values.
    /// Pre-check: query discrim tree for existing fact with same key.
    FunctionalDep {
        sort_functor: Symbol,
        key_fields: Vec<Symbol>,
    },
    /// Cardinality bound: count of matching facts <= max_count.
    CardinalityBound {
        sort_functor: Symbol,
        max_count: usize,
    },
    /// General guard: insert, evaluate full LogicalQuery, retract on failure.
    General,
}

/// A registered integrity guard.
struct Guard {
    #[allow(dead_code)]
    id: ConstraintId,
    /// The guard's `LogicalQuery`, carried carrier-agnostically (WI-023): a
    /// `Value::Term` for the hash-consed structural form the loader builds today,
    /// a `Value::Node` occurrence when a guard rides denoted patterns. Read only
    /// through [`TermView`](term_view::TermView), so the engine never assumes a
    /// `TermId`.
    query: crate::eval::value::Value,
    #[allow(dead_code)]
    kind: GuardKind,
    #[allow(dead_code)]
    trigger_sorts: Vec<TermId>,
    /// Source `constraint` label, for violation diagnostics. `None` if unlabeled.
    label: Option<String>,
}

/// Outcome of evaluating one registered guard in the WI-023 post-load check.
#[derive(Debug, PartialEq, Eq)]
pub enum GuardCheck {
    /// The constraint holds under the current facts.
    Holds,
    /// The constraint is violated. Carries the source label, if any.
    Violated(Option<String>),
    /// The constraint uses a `LogicalQuery` form the shared lowerer cannot
    /// handle — an unknown constructor, or a non-goal-shaped leaf (WI-513).
    /// Carries the source label (if any) and the lowering-error detail. The
    /// loader routes this to a load-BLOCKING error rather than silently loading
    /// with the invariant unenforced.
    Unsupported(Option<String>, String),
}

// ── Rule entry ──────────────────────────────────────────────────

struct RuleEntry {
    /// The fact/rule head, carrier-agnostic (WI-348 Phase B): `Value::Term`
    /// for the universal hash-consed case, a `Value::Node` for a value fact
    /// carrying a `denoted` occurrence. The many term-only callers read it as a
    /// `TermId` via `rule_head` (which panics on a value head — carrier-agnostic
    /// readers use `rule_head_value` / `TermView`; term-only readers migrate
    /// reactively when that panic actually fires, as `is_equation` did).
    head: crate::eval::value::Value,
    /// WI-246: the rule body — body atoms as `NodeOccurrence` (De Bruijn-encoded
    /// `Expr::Var` leaves), the SOLE body representation now that the term
    /// `body: Vec<TermId>` field is dropped. What the resolver opens as goals
    /// (`with_fresh_vars`) and the typer / `simp_rewrite` walk and rewrite
    /// (uniform with op bodies). Empty for ground facts.
    body_nodes: Vec<Rc<NodeOccurrence>>,
    sort: TermId,
    domain: TermId,
    meta: Option<TermId>,
    retracted: bool,
    /// Number of de Bruijn-encoded free variables in head+body.
    /// Zero for ground facts. Used by resolver to allocate fresh globals.
    arity: u32,
    /// Pre-DeBruijn Global VarIds in DeBruijn-index order (i.e.
    /// `globals[0]` is the Global VarId that was assigned DeBruijn 0
    /// during rule load). Empty for ground facts. Used by structured-
    /// proof step synthesis to assert step rules in the parent's
    /// variable frame so cited-rule lifts produce `var_<i>` names
    /// aligned with the consumer's preamble declarations.
    globals: Vec<VarId>,
    /// Number of leading DeBruijn slots whose vars are SHARED with a
    /// parent rule's frame. When `shared_arity > 0`, the lift skips
    /// forall-quantifying `var_0..var_{shared_arity-1}` (those refer
    /// to the consumer's already-declared preamble vars); only
    /// `var_{shared_arity}..var_{arity-1}` (the step-introduced new
    /// vars) get emitted as declare-consts.
    shared_arity: u32,
    /// Citation handle for labeled rules. Indexed under
    /// `rules_by_label` so `rule_id_by_qn` resolves a rule by its
    /// label even when the head's functor differs from the label
    /// (e.g. `rule simple_lemma: gte(?x, 3.0) :- ...` — head functor
    /// is `gte`, label is `simple_lemma`). `None` for unlabeled rules
    /// (they remain reachable through `rules_by_functor` on the head).
    label: Option<Symbol>,
}

/// Collect the ground `TermId` leaves reachable in a value (WI-348 Phase B), for
/// the value-fact refcount helpers. Recurses through `Value::Entity` / `Tuple`
/// children directly and through a `Value::Node` occurrence via `TermView`.
fn collect_value_ground_terms_into(
    kb: &KnowledgeBase,
    v: &crate::eval::value::Value,
    out: &mut Vec<TermId>,
) {
    use crate::eval::value::Value;
    match v {
        Value::Term(t) => out.push(*t),
        Value::Entity { pos, named, .. } | Value::Tuple { pos, named } => {
            for c in pos.iter() {
                collect_value_ground_terms_into(kb, c, out);
            }
            for (_, c) in named.iter() {
                collect_value_ground_terms_into(kb, c, out);
            }
        }
        Value::Node(occ) => collect_occ_ground_terms_into(kb, occ, out),
        _ => {}
    }
}

/// Walk a `Value::Node` occurrence through `TermView`, pushing every ground
/// `TermId` child and recursing into nested value / occurrence children. A
/// non-`Functor` head (Const / Ref / Ident / Opaque) carries no ground child.
fn collect_occ_ground_terms_into(
    kb: &KnowledgeBase,
    occ: &std::rc::Rc<node_occurrence::NodeOccurrence>,
    out: &mut Vec<TermId>,
) {
    use term_view::{TermView, ViewHead, ViewItem};
    let pos_arity = match occ.head(kb) {
        ViewHead::Functor { pos_arity, .. } => pos_arity,
        _ => return,
    };
    for i in 0..pos_arity {
        match occ.pos_arg(kb, i) {
            Some(ViewItem::Term(t)) => out.push(t),
            Some(ViewItem::Value(c)) => collect_value_ground_terms_into(kb, c, out),
            Some(ViewItem::Node(o)) => collect_occ_ground_terms_into(kb, &o, out),
            None => {}
        }
    }
    for sym in occ.named_keys(kb) {
        match occ.named_arg(kb, sym) {
            Some(ViewItem::Term(t)) => out.push(t),
            Some(ViewItem::Value(c)) => collect_value_ground_terms_into(kb, c, out),
            Some(ViewItem::Node(o)) => collect_occ_ground_terms_into(kb, &o, out),
            None => {}
        }
    }
}

// ── Sort kind ───────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SortKind {
    Sort,
    Enum,
}

// ── Sort operations table ───────────────────────────────────────

/// WI-240 — per-impl-sort operations table. For each impl sort `S`
/// with a `fact Spec[bindings]`, maps each of `Spec`'s declared op
/// short names to the symbol the runtime should invoke: `S.<op>` when
/// the impl overrides with a runnable body, otherwise the spec op
/// itself (`Spec.<op>` — resolved via the spec's rewrite rule or a
/// registered builtin at runtime).
///
/// Built once at load time by `load::build_sort_ops_table`, after all
/// `SortProvidesInfo` / `OperationInfo` facts are asserted. Dispatch
/// consumers (the typer's `resolve_at_goal`, the eval's
/// `apply_within`) read it via [`KnowledgeBase::sort_ops_lookup`] — a
/// direct table lookup, replacing the prior
/// `format!("{impl_qn}.{op}").or_else(spec_qn)` string-concatenation
/// fallback. See `docs/design/operation-call-model.md` §"Putting it
/// together: dispatch end-to-end".
#[derive(Default, Debug)]
pub(crate) struct SortOpsTable {
    /// impl sort symbol → (op short-name symbol → target op symbol).
    by_impl: HashMap<Symbol, HashMap<Symbol, Symbol>>,
}

// ── KnowledgeBase ───────────────────────────────────────────────

/// A process-unique identity for a [`KnowledgeBase`], assigned at `new()` from a
/// monotonic counter so distinct KBs — including the many created across tests —
/// never collide. WI-471 stamps it onto cached `TermId`s in
/// `NodeOccurrence::term_cache` so a future (WI-472) deferred term-release queue
/// can tell which store a queued `TermId` belongs to.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct KbId(u64);

impl KbId {
    fn next() -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(1);
        KbId(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

pub struct KnowledgeBase {
    // Term storage (hash-consed, refcounted)
    pub(crate) terms: TermStore,
    pub(crate) symbols: SymbolTable,
    /// WI-471: process-unique id, stamped onto cached occurrence `TermId`s
    /// (`NodeOccurrence::term_cache`) so a future deferred-release queue can
    /// route a queued `TermId` back to this store.
    pub(crate) id: KbId,

    // Rules (facts are rules with empty body)
    rules: Vec<RuleEntry>,

    // Indexes — all maintained atomically by assert/retract
    by_sort: HashMap<TermId, Vec<RuleId>>,
    rules_by_functor: HashMap<Symbol, Vec<RuleId>>,
    by_domain: HashMap<TermId, Vec<RuleId>>,
    rules_by_label: HashMap<Symbol, Vec<RuleId>>,

    // Entity-of indexes: entity → parent sort (1-level, non-transitive).
    // Materialized indexes for EntityOf(entity, parent) facts.
    sort_entities: HashMap<TermId, Vec<TermId>>,   // sort → its entity constructors
    entity_parent: HashMap<TermId, TermId>,         // entity → its parent sort
    sort_info: HashMap<TermId, SortKind>,

    // Discrimination tree index for structural term matching
    discrim: SubstTree<RuleId>,

    // WI-233: dedup index for ground facts (body-empty rules). Keyed by
    // (head, sort, domain) so `assert_fact` can short-circuit on a
    // duplicate in O(1) instead of scanning `by_sort[sort]` linearly.
    // Pre-WI-233 the scan averaged ~180 entries per call on a stdlib
    // load; this index brings it to a single hash lookup.
    fact_dedup: HashMap<(TermId, TermId, TermId), RuleId>,

    // Builtin dispatch: functor symbol → builtin tag
    builtins: HashMap<Symbol, BuiltinTag>,

    // Entity field registry: functor symbol → ordered field names.
    // Populated during load_entity, used by convert_term for partial named-arg expansion.
    pub(crate) entity_fields: HashMap<Symbol, Vec<Symbol>>,

    // Set of functor symbols that are constructors (entities with a parent sort).
    // Populated by register_entity_of, used by is_constructor_symbol for O(1) lookup.
    constructor_symbols: HashSet<Symbol>,

    // Variable counter for fresh VarId allocation
    next_var: u32,

    // Base substitution for each sort: maps all params + operations to themselves.
    // Computed by resolve_instantiations() after loading.
    // Key: sort functor symbol. Value: list of (slot_name, Ref(slot_name)) pairs.
    sort_base_subst: HashMap<Symbol, Vec<(Symbol, TermId)>>,

    // Well-known sort terms (cached for future layers)
    #[allow(dead_code)]
    sort_sort: Option<TermId>,
    #[allow(dead_code)]
    entity_of_sort: Option<TermId>,

    // Guards — integrity constraints checked on assert
    guards: Vec<Guard>,
    guards_by_sort: HashMap<TermId, Vec<usize>>,

    /// WI-251 — span side-table keyed by stored term TermId. Populated
    /// by `load.rs::create_occurrence_ex` for every expression /
    /// fact-head / rule-head term registered during load. Replaces the
    /// legacy `the legacy occurrence by-term index(t).first().span(...)` lookup
    /// used by typing.rs error-formatting paths.
    pub(crate) term_spans: HashMap<TermId, crate::span::SourceSpan>,
    /// WI-251 — first-encountered span keyed by functor symbol.
    /// Populated alongside `term_spans` so typing.rs can recover a
    /// representative span for an operation / sort / entity when only
    /// its symbol is in hand (e.g. `check_operation_bodies`'s
    /// span-by-op-sym lookup).
    pub(crate) functor_spans: HashMap<Symbol, crate::span::SourceSpan>,

    /// WI-242 — value-typed operation bodies keyed by operation symbol.
    /// WI-305: this side-table is now the SOLE store of operation bodies — the
    /// `OperationInfo.body` / `OperationImpl.body` fact fields were dropped, and
    /// the term handle is no longer built/stored. anthill code reaches a body via
    /// the `anthill.reflect.operation_body` builtin (which reads this table).
    /// See `docs/design/occurrence-as-value-type.md`.
    ///
    /// WI-348 / **WI-370**: deliberately NOT collapsed into the `OperationInfo`
    /// value fact (which would complete the "everything is facts" model). The
    /// body is keyed data (`Symbol` → body), but it is *also* an `Expr`
    /// occurrence whose control-flow forms (`let`/`if`/`match`) read `Opaque` in
    /// `occ_head`. The discrimination tree indexes a fact head's *full* nested
    /// structure, so a fact-resident body would force the insert walk down into
    /// that `Expr` — building a per-body structural MIRROR in the trie that no
    /// query prunes on (the body is never a discriminator; ops are found by
    /// `name`), needing `occ_head` to mirror the whole `Expr` enum, and risking
    /// deep recursion. Doing the collapse *cleanly* — body in the fact, still
    /// shape-queryable — needs a **custom-unification / custom-search hook at a
    /// discrim node** (delegate the body subterm to on-demand `TermView` unify
    /// instead of trie descent): tracked as **WI-370**. Until that lands, the
    /// body stays here, reachable relationally via `operation_body`.
    pub(crate) op_bodies: HashMap<Symbol, Rc<NodeOccurrence>>,

    /// Proposal 039 / WI-084 — a term-level constant's DECLARED TYPE, keyed by
    /// its `SymbolKind::Const` symbol, as a carrier-agnostic `Value`. Read by
    /// the typer to type a bare const reference (fold-free: only the declared
    /// type, never the value). A dedicated table — NOT folded into a reflect
    /// `ConstInfo` fact in this phase; that consolidation can come with the
    /// resolution/typing phase if reflection needs it.
    pub(crate) const_types: HashMap<Symbol, crate::eval::value::Value>,

    /// Proposal 039 / WI-084 — a term-level constant's defining-expression body,
    /// keyed by its `SymbolKind::Const` symbol. A SEPARATE table from `op_bodies`
    /// on purpose: `op_bodies_iter` is scanned by operation-only passes (e.g.
    /// `req_insertion`), which must not see const bodies. Bodyless (host-supplied)
    /// consts have no entry. Folding the body to a value is a later phase.
    pub(crate) const_bodies: HashMap<Symbol, Rc<NodeOccurrence>>,

    /// WI-443 — true once the loader has built any `dot_apply` expression.
    /// The typer's tree-reassembly gate reads it: a DotApply is ALWAYS
    /// rewritten by the typer (to the dispatched call), so its ancestors
    /// must be reassembled for the rewrite to reach the stored body (and
    /// thus eval) even when no `[simp]` equation is loaded.
    pub(crate) has_dot_applies: bool,

    /// WI-429: every `RigidTypeProjection` the loader FORMS, with its source
    /// span — the work-list for the end-of-load formation sweep
    /// (`typing::validate_rigid_projection_formations`). A projection stored
    /// in a position the typer never eliminates (an entity field type, a
    /// fact/rule type slot) would otherwise carry a malformed projection
    /// (typo'd member, bare-spec subject) silently. Drained by the sweep at
    /// the end of each load phase.
    pub(crate) rigid_projection_formations: Vec<(TermId, SourceSpan)>,

    /// WI-402 (existential half): the operations whose return type the loader
    /// REWROTE from an existential carrier (`-> C ensures Spec[C, …]` → the spec
    /// with the carrier dropped). The `abstracting_return` (WI-401) gate skips
    /// exactly these — an `ensures` admits the abstract return only when the loader
    /// actually formed the existential, NOT for any op that merely names the return
    /// sort in an `ensures` (that stays the strict escape). Keyed on the op symbol.
    pub(crate) existential_return_ops: std::collections::HashSet<Symbol>,

    // WI-348 (value-fact payoff): the `op_effects` side-table is GONE. A
    // `denoted`-bearing effect label (`Modify[c]`) now lives in the
    // `OperationInfo` fact itself — the loader builds that fact as a *value
    // fact* (a `Value::Node` head carrying a value effects list) and
    // `lookup_operation_info` reads the effects back from the fact. This is
    // the side-table collapse the WI-348 design doc names as the payoff:
    // effects ride in the queryable fact, not a Rust-side map.

    // Entity field type registry: functor symbol → [(field_name, type_term)].
    // Populated during load_entity, used by type_check_sorts.
    entity_field_types: HashMap<Symbol, Vec<(Symbol, crate::eval::value::Value)>>,

    // SortRequiresInfo facts already finalized by resolve_requires_bindings.
    // Keyed by post-reassert RuleId. Lets incremental loads skip stdlib facts.
    resolved_requires_facts: HashSet<RuleId>,

    // Source registry (file names/paths)
    pub(crate) sources: SourceRegistry,

    // Goal-routing registry — per-functor `RouteHandler`s that surface
    // external row streams as resolution candidates. Empty by default;
    // populated by host code via `register_route_handler`. See
    // `kb/route.rs` and proposal 007 §11.
    pub(crate) routes: route::RouteRegistry,

    // WI-218 — static-dispatch rewrite tables.
    // `dispatch_rewrites`: original apply TermId → rewritten apply TermId
    //   (with `fn` substituted from spec op to impl op). The
    //   post-typing rewrite pass uses this to substitute apply terms
    //   bottom-up in operation bodies.
    // `dispatch_origin`: rewritten apply TermId → original spec op symbol.
    //   Read by reflection / proof-record specialization / debug tooling
    //   for provenance ("this was originally Spec.op, dispatched to
    //   Impl.op"). The interpreter never reads it.
    pub(crate) dispatch_rewrites: HashMap<TermId, TermId>,
    pub(crate) dispatch_origin: HashMap<TermId, Symbol>,

    // WI-226 Cache A — memoized transitive `requires` closure per sort.
    // After WI-230, this cache is dormant — `requires_chain` now routes
    // through `requires_tree_cache` (the tree-shaped cache). Kept here
    // to avoid breaking the `requires_chain_cache_contains` accessor
    // tests rely on; cleared at the same time as the tree cache.
    pub(crate) requires_chain_cache: RefCell<HashMap<Symbol, Rc<Vec<crate::kb::typing::RequiresEntry>>>>,

    // WI-230 — memoized substitution-composed `requires` tree per sort.
    // Each entry is the `Rc<Vec<RequiresNode>>` `requires_tree(kb, S)`
    // returns. Same lifetime as Cache A: fills lazily during typing;
    // invalidated by `invalidate_requires_chain_cache`.
    pub(crate) requires_tree_cache: RefCell<HashMap<Symbol, Rc<Vec<crate::kb::typing::RequiresNode>>>>,

    // Memoized synthesized requirement-param names per parent sort —
    // `__req_<spec short name>` in chain order. Same lifetime as the
    // requires caches (derives from the chain); invalidated by
    // `invalidate_requires_chain_cache`. Avoids rebuilding the Vec +
    // collision-disambiguation HashMap on every frame push.
    pub(crate) synth_req_names_cache: RefCell<HashMap<Symbol, Rc<Vec<Symbol>>>>,

    // WI-424 — memoized `(param symbol, canonical Var term)` pairs per
    // parametric sort (`typing::sort_type_params_as_pairs`). Consulted on hot
    // paths (per apply call site in the typer's receiver classification, per
    // value-directed dispatch at eval); the uncached computation walks the
    // whole symbol table + per-param SortAlias scans. A sort's params and
    // their alias facts are fixed at scan/load time, so entries never go
    // stale within a session.
    pub(crate) sort_param_pairs_cache: RefCell<HashMap<Symbol, Rc<Vec<(Symbol, TermId)>>>>,

    // WI-226 Cache B — memoized spec-op SLD dispatch results, keyed by
    // `(op_short, SortGoal, scope)`. Saves re-walking `SortProvidesInfo`
    // for repeated spec-op calls at the same (spec, bindings, scope) —
    // common in bodies that call `eq(a, b); eq(c, d); …` at the same T.
    //
    // The scope is captured as `Vec<RequiresEntry>` in the key, so calls
    // from different enclosing sorts don't collide. Within one body the
    // scope is fixed and the key effectively reduces to the goal + op.
    //
    // WI-507: the op's short-name symbol is part of the key. The cached
    // `DispatchOutcome` resolves the impl op via `sort_ops_lookup(impl_sort,
    // op_short)`, so two DIFFERENT carrier-only ops on the SAME carrier
    // (e.g. `clear(s)` and `insert(s, x)` on a `MutableStack`) produce the
    // same goal but must NOT share a memo entry — without `op_short` the
    // first-resolved op poisons the other (`clear` → `MutableStack.insert`).
    //
    // Same lifetime caveat as Cache A: callers asserting new
    // `SortProvidesInfo` post-typing must call
    // `invalidate_resolve_cache`.
    pub(crate) resolve_cache: RefCell<
        HashMap<
            (Symbol, crate::kb::typing::SortGoal, Vec<crate::kb::typing::RequiresEntry>),
            (crate::kb::typing::DispatchOutcome, Option<crate::kb::typing::ResolvedRequiresNode>),
        >,
    >,

    // WI-240 — per-impl-sort operations table; see `SortOpsTable`.
    // Built at load time, read by dispatch consumers via
    // `sort_ops_lookup`.
    pub(crate) sort_ops: SortOpsTable,
}

impl KnowledgeBase {
    pub fn new() -> Self {
        Self {
            terms: TermStore::new(),
            symbols: SymbolTable::new(),
            id: KbId::next(),
            rules: Vec::new(),
            by_sort: HashMap::new(),
            rules_by_functor: HashMap::new(),
            rules_by_label: HashMap::new(),
            by_domain: HashMap::new(),
            sort_entities: HashMap::new(),
            entity_parent: HashMap::new(),
            sort_info: HashMap::new(),
            discrim: SubstTree::new(),
            fact_dedup: HashMap::new(),
            builtins: HashMap::new(),
            entity_fields: HashMap::new(),
            constructor_symbols: HashSet::new(),
            next_var: 0,
            sort_base_subst: HashMap::new(),
            sort_sort: None,
            entity_of_sort: None,
            guards: Vec::new(),
            guards_by_sort: HashMap::new(),
            term_spans: HashMap::new(),
            functor_spans: HashMap::new(),
            op_bodies: HashMap::new(),
            const_types: HashMap::new(),
            const_bodies: HashMap::new(),
            has_dot_applies: false,
            rigid_projection_formations: Vec::new(),
            existential_return_ops: std::collections::HashSet::new(),
            entity_field_types: HashMap::new(),
            resolved_requires_facts: HashSet::new(),
            sources: SourceRegistry::new(),
            routes: route::RouteRegistry::new(),
            dispatch_rewrites: HashMap::new(),
            dispatch_origin: HashMap::new(),
            requires_chain_cache: RefCell::new(HashMap::new()),
            requires_tree_cache: RefCell::new(HashMap::new()),
            synth_req_names_cache: RefCell::new(HashMap::new()),
            sort_param_pairs_cache: RefCell::new(HashMap::new()),
            resolve_cache: RefCell::new(HashMap::new()),
            sort_ops: SortOpsTable::default(),
        }
    }

    /// Drop the memoized `requires_chain` results. Called when a new
    /// `SortRequiresInfo` fact is asserted after the cache filled, so
    /// stale chains can't be served. WI-226 / WI-230. Clears both the
    /// flat chain cache and the tree cache.
    #[allow(dead_code)]
    pub fn invalidate_requires_chain_cache(&self) {
        self.requires_chain_cache.borrow_mut().clear();
        self.requires_tree_cache.borrow_mut().clear();
        self.synth_req_names_cache.borrow_mut().clear();
    }

    /// Drop the memoized spec-op SLD dispatch results. Called when a
    /// new `SortProvidesInfo` fact is asserted after the cache filled.
    /// WI-226.
    #[allow(dead_code)]
    pub fn invalidate_resolve_cache(&self) {
        self.resolve_cache.borrow_mut().clear();
    }

    /// WI-226: number of entries in the resolve cache. Diagnostic /
    /// test inspector — counts how many `(goal, scope)` pairs have
    /// been memoized.
    pub fn resolve_cache_len(&self) -> usize {
        self.resolve_cache.borrow().len()
    }

    /// WI-226 / WI-230: does the `requires_chain` (tree) cache hold an
    /// entry for `sort_sym`? Diagnostic / test inspector —
    /// distinguishes pre-first-call (empty) from post-first-call
    /// (memoized) state. After WI-230 this points at the tree cache,
    /// which is the canonical source of `requires_chain` results.
    pub fn requires_chain_cache_contains(&self, sort_sym: Symbol) -> bool {
        self.requires_tree_cache.borrow().contains_key(&sort_sym)
    }

    /// Record that `original_apply` should be rewritten to `rewritten_apply`
    /// (a new apply term with `fn` substituted from spec op to impl op),
    /// and remember `spec_op_sym` as the original spec call's symbol.
    /// WI-218: typing-time spec→impl rewrite for static dispatch.
    /// Exposed publicly so tests and out-of-tree elaboration passes can
    /// stage their own term-level rewrites alongside the typer's.
    pub fn record_dispatch_rewrite(
        &mut self,
        original_apply: TermId,
        rewritten_apply: TermId,
        spec_op_sym: Symbol,
    ) {
        self.dispatch_rewrites.insert(original_apply, rewritten_apply);
        self.dispatch_origin.insert(rewritten_apply, spec_op_sym);
    }

    /// True iff `term` was rewritten from a spec-op call. Returns the
    /// original spec op symbol for provenance / debug / reflection.
    /// The interpreter does not consult this — runtime semantics use
    /// the rewritten term's `fn` directly.
    pub fn dispatch_origin_of(&self, term: TermId) -> Option<Symbol> {
        self.dispatch_origin.get(&term).copied()
    }

    /// Iterate (rewritten_term, original_spec_op) pairs. Useful for
    /// reflection, debug tooling, and tests.
    pub fn dispatch_origin_iter(&self) -> impl Iterator<Item = (TermId, Symbol)> + '_ {
        self.dispatch_origin.iter().map(|(t, s)| (*t, *s))
    }

    /// Look up the rewritten TermId an original term maps to, if any.
    /// Reflection / tooling / external-elaboration consumers read this
    /// to see what an apply (or any term) was rewritten to.
    pub fn dispatch_rewrite_of(&self, original: TermId) -> Option<TermId> {
        self.dispatch_rewrites.get(&original).copied()
    }

    /// Register a synthesizing pass by qualified name. Returns a PassId
    /// that can be passed to `the legacy alloc_synthesized helper`'s `by:`
    /// field. Idempotent — re-registering returns the same PassId.
    /// Passes call this at startup (or first use) to obtain their identifier.
    pub fn register_pass(&mut self, qualified_name: &str) -> crate::kb::occurrence::PassId {
        crate::kb::occurrence::PassId::from_symbol(self.symbols.intern(qualified_name))
    }

    /// Has this SortRequiresInfo fact already been finalized
    /// (operations auto-bound) by resolve_requires_bindings?
    pub fn is_requires_resolved(&self, rid: RuleId) -> bool {
        self.resolved_requires_facts.contains(&rid)
    }

    /// Mark a (post-reassert) SortRequiresInfo RuleId as finalized.
    pub fn mark_requires_resolved(&mut self, rid: RuleId) {
        self.resolved_requires_facts.insert(rid);
    }

    // ── Source & occurrence access ─────────────────────────────

    pub fn register_source(&mut self, name: String) -> crate::span::SourceId {
        self.sources.register(name)
    }

    pub fn source_name(&self, id: crate::span::SourceId) -> &str {
        self.sources.name(id)
    }

    /// WI-242 — get the value-typed body node for an operation, if the
    /// loader produced one. None for body-less ops (spec declarations).
    pub fn op_body_node(&self, op_sym: Symbol) -> Option<&Rc<NodeOccurrence>> {
        self.op_bodies.get(&op_sym)
    }

    /// WI-242 — record the value-typed body node for an operation.
    /// Called by the loader during operation conversion.
    pub fn set_op_body_node(&mut self, op_sym: Symbol, node: Rc<NodeOccurrence>) {
        self.op_bodies.insert(op_sym, node);
    }

    /// Proposal 039 / WI-084 — the declared type of a term-level constant, if
    /// `const_sym` names one. `None` for any non-const symbol.
    pub fn const_type(&self, const_sym: Symbol) -> Option<&crate::eval::value::Value> {
        self.const_types.get(&const_sym)
    }

    /// Proposal 039 / WI-084 — record a constant's declared type (loader).
    pub fn set_const_type(&mut self, const_sym: Symbol, ty: crate::eval::value::Value) {
        self.const_types.insert(const_sym, ty);
    }

    /// Proposal 039 / WI-084 — the defining-expression body of a term-level
    /// constant, if one was stored. `None` for a bodyless (host-supplied) const.
    pub fn const_body_node(&self, const_sym: Symbol) -> Option<&Rc<NodeOccurrence>> {
        self.const_bodies.get(&const_sym)
    }

    /// Proposal 039 / WI-084 — record a constant's body node (loader).
    pub fn set_const_body_node(&mut self, const_sym: Symbol, node: Rc<NodeOccurrence>) {
        self.const_bodies.insert(const_sym, node);
    }

    /// WI-251 — span for a stored term, if the loader recorded one.
    pub fn term_span(&self, t: TermId) -> Option<crate::span::SourceSpan> {
        self.term_spans.get(&t).copied()
    }

    /// WI-251 — first span recorded for `functor` during load, if any.
    pub fn functor_span(&self, functor: Symbol) -> Option<crate::span::SourceSpan> {
        self.functor_spans.get(&functor).copied()
    }

    /// WI-251 — iterate every operation's `(symbol, body NodeOccurrence)`.
    /// Passes (e.g. `req_insertion::run`) that need to scan all bodies
    /// consume this; the iteration order is unspecified.
    pub fn op_bodies_iter(&self) -> impl Iterator<Item = (Symbol, &Rc<NodeOccurrence>)> + '_ {
        self.op_bodies.iter().map(|(s, n)| (*s, n))
    }

    // ── Term allocation ─────────────────────────────────────────

    /// Allocate a term (hash-consed, refcounted).
    pub fn alloc(&mut self, term: Term) -> TermId {
        // WI-511: a nullary application of a registered constructor is stored in
        // its bare `Ref` form, so a fact written as `Fn{c}` and a rule pattern
        // spelled `Ref(c)` share ONE TermId. This ELIMINATES the dual
        // representation that WI-436 only bridged at the view layer
        // (`functor_view_head`): with a single storage form, raw `Term::Fn`
        // readers and `head()`-routed readers agree without a canonicalizer.
        // Gated on `is_constructor_symbol` (kind-isolated, same as the bridge):
        // ops-as-values are `Value::OpRef`, never `Term::Ref`, and sorts/params
        // aren't constructors, so the WI-391 `Ref`=wildcard / `Fn`=concrete
        // TYPE-dispatch distinction is untouched.
        if let Term::Fn { functor, pos_args, named_args } = &term {
            if pos_args.is_empty() && named_args.is_empty() && self.is_constructor_symbol(*functor) {
                let f = *functor;
                return self.terms.alloc(Term::Ref(f));
            }
        }
        self.terms.alloc(term)
    }

    /// Intern a string, returning a Symbol.
    pub fn intern(&mut self, s: &str) -> Symbol {
        self.symbols.intern(s)
    }

    /// Define a Resolved symbol in the given scope. Wrapper exposing
    /// `SymbolTable::define` for downstream crates that need to
    /// register synthesized symbols (e.g. anthill-cli's
    /// `dispatch_structured` synthesizing transient step rules).
    /// Idempotent on re-definition: returns the existing symbol if
    /// `short_name` already lives in the scope.
    pub fn define_symbol(
        &mut self,
        short_name: &str,
        qualified_name: &str,
        kind: crate::intern::SymbolKind,
        scope_raw: u32,
    ) -> Symbol {
        self.symbols.define(short_name, qualified_name, kind, scope_raw)
    }

    /// Allocate a fresh logic variable id, carrying the display name.
    pub fn fresh_var(&mut self, name: Symbol) -> VarId {
        let id = self.next_var;
        self.next_var += 1;
        VarId::new(id, name)
    }

    /// Resolve a Symbol back to its short (display) name.
    pub fn resolve_sym(&self, sym: Symbol) -> &str {
        self.symbols.name(sym)
    }

    /// Get the qualified name for a resolved Symbol.
    /// Returns the short name if the symbol is unresolved.
    pub fn qualified_name_of(&self, sym: Symbol) -> &str {
        match self.symbols.get(sym) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name,
            SymbolDef::Unresolved { name } => name,
        }
    }

    /// Kind of a resolved symbol (Sort, Entity, Operation, …).
    /// `None` for unresolved symbols.
    pub fn kind_of(&self, sym: Symbol) -> Option<crate::intern::SymbolKind> {
        match self.symbols.get(sym) {
            SymbolDef::Resolved { kind, .. } => Some(*kind),
            SymbolDef::Unresolved { .. } => None,
        }
    }

    /// Scope symbol that owns `sym`. Delegates to the symbol table.
    pub fn scope_of(&self, sym: Symbol) -> Option<Symbol> {
        self.symbols.scope_of(sym)
    }

    /// Type-parameter names declared inside a sort's body (`sort T = ?`
    /// inside `sort S { ... }`). Returns the names in alphabetical
    /// order — stable across runs but not necessarily source order.
    /// Empty when the sort has no body, no children, or no params.
    pub fn type_params_of_sort(&self, sort_sym: Symbol) -> Vec<String> {
        let qn = self.qualified_name_of(sort_sym);
        let prefix = format!("{qn}.");
        // Find the body scope by looking only at *direct* children of
        // the sort — qualified names with no further dots after the
        // prefix. `HashMap.iter()` order is non-deterministic, so a
        // grandchild (e.g. an operation parameter) would otherwise
        // sometimes win and yield the wrong scope.
        let body_scope = self.symbols.by_qualified_name.iter()
            .find_map(|(child_qn, child_sym)| {
                if !child_qn.starts_with(&prefix) { return None; }
                if child_qn[prefix.len()..].contains('.') { return None; }
                match self.symbols.get(*child_sym) {
                    SymbolDef::Resolved { scope_raw, .. } => Some(*scope_raw),
                    _ => None,
                }
            });
        let Some(scope_raw) = body_scope else { return Vec::new() };
        let Some(scope) = self.symbols.scope(scope_raw) else { return Vec::new() };
        // Source-order, not alphabetical: positional sort bindings rely
        // on declaration order (`Map[String, Int]` mapping index 0→K,
        // 1→V follows the order K and V were declared, not their
        // alphabetic sort). The HashSet path is still used by
        // `is_type_param` membership checks.
        scope.type_params_ordered.clone()
    }

    /// Get the Term for a TermId.
    pub fn get_term(&self, id: TermId) -> &Term {
        self.terms.get(id)
    }

    // ── Rule assertion / retraction ─────────────────────────────

    /// Assert a rule into the KB. The primary method: head + body + metadata.
    /// Facts are rules with an empty body. Uses `insert_pattern` to handle
    /// variables in the head. The term body is materialized to the rule's
    /// occurrence body — the sole stored form — via [`Self::term_body_to_nodes`].
    /// Rules whose vars must close to De Bruijn go through
    /// [`Self::assert_rule_debruijn_with_nodes`] (synthesized / hand-built) or
    /// the loader's native occurrence build; this entry asserts the head + body
    /// as given (ground facts, or callers that closed vars themselves).
    pub fn assert_rule(
        &mut self,
        head: TermId,
        body: Vec<TermId>,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        let body_nodes = self.term_body_to_nodes(&body);
        self.assert_rule_nodes(head, body_nodes, sort, domain, meta)
    }

    /// Materialize a term body into the rule's occurrence body (WI-246/WI-372) —
    /// the single `Vec<TermId>` → `Vec<NodeOccurrence>` converter for every
    /// caller that builds a rule from terms (the primary [`Self::assert_rule`]
    /// and the synthesized / hand-built rules routed through
    /// [`Self::assert_rule_debruijn_with_nodes`]). Each atom is a read-only
    /// `materialize_from_handle` walk (De Bruijn / Global leaves preserved as
    /// `Expr::Var`); the term body is neither stored nor incref'd (its `RuleEntry`
    /// field was dropped). The loader builds occurrences natively from the parse
    /// IR and never comes through here. Empty body ⇒ empty occurrence body (a
    /// fact). The occurrence body is the resolver's goal source and the
    /// typer/`simp` view.
    pub fn term_body_to_nodes(&self, body: &[TermId]) -> Vec<Rc<NodeOccurrence>> {
        body.iter()
            .map(|&b| node_occurrence::materialize_from_handle(self, b))
            .collect()
    }

    /// Core rule-insertion epilogue: the occurrence body is already final (in the
    /// rule's stored form). Increfs head/sort/domain/meta, pushes the `RuleEntry`,
    /// and updates the sort / domain / functor / fact-dedup / discrimination
    /// indexes. The single storage path: callers materialize a term body to
    /// occurrences first ([`Self::term_body_to_nodes`]) or supply the loader's
    /// native occurrences, then close to De Bruijn via
    /// [`Self::finalize_rule_debruijn_nodes`] before landing here. Sets
    /// `arity`/`shared_arity`/`globals` to their ground-fact defaults; De Bruijn
    /// callers overwrite them.
    pub fn assert_rule_nodes(
        &mut self,
        head: impl Into<crate::eval::value::Value>,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        // WI-373: the head is carrier-agnostic — a `Value::Term` for the
        // universal hash-consed case, or a `Value::Node`/`Entity` for a value
        // rule head carrying a denoted occurrence. Every existing caller passes a
        // `TermId` (→ `Value::Term` via `From`), so the term path is unchanged.
        // Builtins always take precedence over rules at resolution time (checked
        // first in step_init), so rules with builtin functors are allowed but
        // effectively shadowed during resolution.
        let head: crate::eval::value::Value = head.into();
        let is_fact = body_nodes.is_empty();
        // The hash-consed head term for the ground-fact dedup index below — only a
        // `Value::Term` head has one; a `Node`/`Entity` head is keyless (a dedup-miss,
        // not unsoundness — WI-348 Phase B). Read before `head` moves into the entry.
        let head_term = match &head {
            crate::eval::value::Value::Term(t) => Some(*t),
            _ => None,
        };
        let rule_id = self.push_value_head_entry(head, body_nodes, sort, domain, meta);

        // WI-233: ground-fact dedup index. Inserted only for body-empty entries
        // (rules with a body match structurally via the discrim tree, not
        // exact-equality) AND only for a `Term`-carrier head — a value `Node`
        // head has no `TermId` key, a dedup-miss not unsoundness (WI-348 Phase
        // B). We do not overwrite an existing entry; the dedup check in
        // `assert_fact` upstream routes duplicates to the existing RuleId first.
        if is_fact {
            if let Some(t) = head_term {
                self.fact_dedup.entry((t, sort, domain)).or_insert(rule_id);
            }
        }
        rule_id
    }

    /// Store a value head + occurrence body as a `RuleEntry` and index it
    /// carrier-agnostically (WI-348/WI-373) — the shared storage epilogue of
    /// [`Self::assert_rule_nodes`] and [`Self::assert_fact_value`], so the two
    /// cannot drift in how a value head is owned and indexed. Increfs the head's
    /// ground `TermId` leaves (a `Value::Term(t)` yields exactly `[t]`, matching
    /// the old `terms.incref(head)`; a `Node`/`Entity` head increfs its ground
    /// children — symmetric with `retract`'s `release_value_ground`) +
    /// sort/domain/meta, pushes the entry (arity/shared_arity/globals at
    /// ground-fact defaults — De Bruijn callers overwrite), indexes
    /// `by_sort`/`by_domain`/`rules_by_functor` (functor via the head's
    /// `TermView`, any carrier), and inserts the head into the discrim tree
    /// through its `TermView`. Does NOT touch `fact_dedup` — that key is
    /// `Term`-only and caller-specific.
    fn push_value_head_entry(
        &mut self,
        head: crate::eval::value::Value,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        let rule_id = RuleId(self.rules.len() as u32);

        self.incref_value_ground(&head);
        self.terms.incref(sort);
        self.terms.incref(domain);
        if let Some(m) = meta {
            self.terms.incref(m);
        }

        // Top-level functor via the head's `TermView` (any carrier — WI-348).
        // WI-436: a 0-ary constructor head reads as the bare `Ref(c)`; `functor_sym`
        // reads `c` off either spelling so a nullary-constructor fact (`fact none`)
        // is still indexed under its functor symbol, mirroring the discrim tree
        // (which indexes it as `Ref(c)`).
        let head_functor = term_view::TermView::head(&head, self).functor_sym();

        self.rules.push(RuleEntry {
            head: head.clone(),
            body_nodes,
            sort,
            domain,
            meta,
            retracted: false,
            arity: 0,
            globals: Vec::new(),
            shared_arity: 0,
            label: None,
        });

        self.by_sort.entry(sort).or_default().push(rule_id);
        self.by_domain.entry(domain).or_default().push(rule_id);
        if let Some(f) = head_functor {
            self.rules_by_functor.entry(f).or_default().push(rule_id);
        }

        // Discrimination tree index (insert_pattern handles vars in head). The
        // view-driven walk needs `&self` (Node-carrying value heads read the
        // whole KB — WI-348), so run it with the index detached.
        self.with_discrim_detached(move |kb, discrim| {
            discrim.insert_pattern(kb, &head, rule_id);
        });

        rule_id
    }

    /// Run `f` with the discrimination index moved out of `self`, so a
    /// view-driven walk can read the whole KB (`&self` — Node-carrying value
    /// heads need it, WI-348) without aliasing `&mut self.discrim`. The index
    /// is always swapped back before returning — including when `f`
    /// early-returns — so the KB can never be left holding the empty
    /// placeholder (Phase A review guard #4). A panic inside `f` unwinds past
    /// the restore, but that already aborts the operation loudly.
    fn with_discrim_detached<R>(
        &mut self,
        f: impl FnOnce(&Self, &mut SubstTree<RuleId>) -> R,
    ) -> R {
        // Restore the index on drop — including on unwind — so a panic inside
        // `f` (the discrim ViewHead guards, the insert/remove `expect`s) can
        // never leave the KB holding the empty placeholder (WI-348 review #5).
        struct Restore<'a> {
            kb: &'a mut KnowledgeBase,
            discrim: SubstTree<RuleId>,
        }
        impl Drop for Restore<'_> {
            fn drop(&mut self) {
                self.kb.discrim = std::mem::replace(&mut self.discrim, SubstTree::new());
            }
        }
        let detached = std::mem::replace(&mut self.discrim, SubstTree::new());
        let mut guard = Restore { kb: self, discrim: detached };
        f(&*guard.kb, &mut guard.discrim)
    }

    // ── Guards ───────────────────────────────────────────────────

    /// Register a guard on the KB (WI-023). The guard is any [`TermView`] — a
    /// hash-consed `TermId` `LogicalQuery` (the loader's form today), a `Value`,
    /// or a `Value::Node` occurrence — stored carrier-agnostically and read back
    /// only through `TermView`, so the engine never assumes a `TermId`. Trigger
    /// sorts are auto-extracted from the structure.
    ///
    /// [`TermView`]: term_view::TermView
    pub fn add_guard<V: term_view::TermView>(&mut self, guard: V) -> ConstraintId {
        self.add_guard_labeled(guard, None)
    }

    /// [`add_guard`](Self::add_guard) carrying the source constraint's label for
    /// violation diagnostics.
    pub fn add_guard_labeled<V: term_view::TermView>(
        &mut self,
        guard: V,
        label: Option<String>,
    ) -> ConstraintId {
        use crate::eval::value::Value;
        use crate::kb::persist_subst::BindValue;
        // Own the guard carrier-agnostically. `as_bind_value` captures the whole
        // structure (a `TermId` IS its structure; a `Value`/`Node` clones cheaply)
        // and never yields a `Path` (that variant is for deferred subst leaves).
        let query = match guard.as_bind_value() {
            BindValue::Term(t) => Value::Term(t),
            BindValue::Value(v) => v,
            BindValue::Path(_) => unreachable!("TermView::as_bind_value never yields a Path"),
        };
        let trigger_sorts = self.extract_trigger_sorts(&query);
        let id = ConstraintId(self.guards.len() as u32);
        // Keep any hash-consed leaves alive for the guard's lifetime. Guards are
        // never retracted, so this incref is matched by no decref (as before).
        let mut grounds = Vec::new();
        collect_value_ground_terms_into(self, &query, &mut grounds);
        for t in grounds {
            self.terms.incref(t);
        }
        for &s in &trigger_sorts {
            self.guards_by_sort.entry(s).or_default().push(id.index());
        }
        self.guards.push(Guard {
            id,
            query,
            kind: GuardKind::General,
            trigger_sorts,
            label,
        });
        id
    }

    /// Empty if reflect stdlib not loaded — guard then triggers on no sorts.
    fn extract_trigger_sorts(&mut self, guard: &crate::eval::value::Value) -> Vec<TermId> {
        let syms = execute::LogicalQuerySymbols::resolve(self);
        let mut out = Vec::new();
        self.collect_trigger_sorts(guard, &syms, &mut out);
        out
    }

    /// Carrier-agnostic structural walk (WI-023): reads the `LogicalQuery` through
    /// [`TermView`](term_view::TermView), so a `TermId` and a `Value::Node`
    /// occurrence carrying the same query extract identical trigger sorts.
    fn collect_trigger_sorts(
        &mut self,
        view: &crate::eval::value::Value,
        syms: &execute::LogicalQuerySymbols,
        out: &mut Vec<TermId>,
    ) {
        use term_view::{TermView, ViewHead};
        let head = TermView::head(view, self);
        let Some(functor) = head.functor_sym() else { return };

        if Some(functor) == syms.pattern_query {
            let inner = TermView::named_arg(view, self, syms.term).map(|c| c.to_value());
            if let Some(inner) = inner {
                if let Some(sort) = self.view_to_trigger_sort(&inner) {
                    if !out.contains(&sort) {
                        out.push(sort);
                    }
                }
            }
            return;
        }

        if Some(functor) == syms.sort_query {
            let name = TermView::named_arg(view, self, syms.sort_name)
                .map(|c| c.to_value())
                .and_then(|v| match TermView::head(&v, self) {
                    ViewHead::Const(term::Literal::String(s)) => Some(s),
                    _ => None,
                });
            if let Some(name) = name {
                if let Some(sym) = self.try_resolve_symbol(&name) {
                    let sort_term = self.make_name_term_from_sym(sym);
                    if !out.contains(&sort_term) {
                        out.push(sort_term);
                    }
                }
            }
            return;
        }

        // Recurse into every structural child (named then positional). Own each
        // child as a `Value` before recursing so no borrow of `self` is held.
        let pos_arity = match &head {
            ViewHead::Functor { pos_arity, .. } => *pos_arity,
            _ => 0,
        };
        for k in TermView::named_keys(view, self) {
            let child = TermView::named_arg(view, self, k).map(|c| c.to_value());
            if let Some(child) = child {
                self.collect_trigger_sorts(&child, syms, out);
            }
        }
        for i in 0..pos_arity {
            let child = TermView::pos_arg(view, self, i).map(|c| c.to_value());
            if let Some(child) = child {
                self.collect_trigger_sorts(&child, syms, out);
            }
        }
    }

    fn view_to_trigger_sort(&mut self, view: &crate::eval::value::Value) -> Option<TermId> {
        let functor = term_view::TermView::head(view, self).functor_sym()?;
        if let Some(parent) = self.constructor_parent_sort(functor) {
            return Some(parent);
        }
        let sort_term = self.make_name_term_from_sym(functor);
        if self.sort_kind(sort_term).is_some() {
            Some(sort_term)
        } else {
            None
        }
    }

    /// Number of registered guards.
    pub fn guard_count(&self) -> usize {
        self.guards.len()
    }

    /// Sorts whose facts re-fire guard `cid`.
    pub fn guard_trigger_sorts(&self, cid: ConstraintId) -> &[TermId] {
        self.guards.get(cid.index())
            .map(|g| g.trigger_sorts.as_slice())
            .unwrap_or(&[])
    }

    /// Assert a fact with guard checking.
    /// Returns Some(rule_id) if all guards pass, None if any guard is violated.
    pub fn assert_checked(
        &mut self,
        term: TermId,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> Option<RuleId> {
        let guard_indices: Vec<usize> = self.guards_by_sort
            .get(&sort)
            .cloned()
            .unwrap_or_default();

        if guard_indices.is_empty() {
            return Some(self.assert_fact(term, sort, domain, meta));
        }

        // General path: insert tentatively, check guards, retract on failure.
        // Carrier-agnostic: the guard is read through `TermView` (WI-023).
        let rule_id = self.assert_fact(term, sort, domain, meta);

        for &idx in &guard_indices {
            let query = self.guards[idx].query.clone();
            // WI-518: `evaluate_guard` resolves the constraint outright — occurrence
            // (`Value::Node`) leaves now resolve through `resolve_goals` like term
            // leaves, so there is no longer a gated outcome to defer here.
            match self.evaluate_guard(&query) {
                Ok(true) => {}
                Ok(false) => {
                    self.retract(rule_id);
                    return None;
                }
                // WI-513: an unsupported-form lowering error on this per-assert
                // runtime path is an internal invariant violation — the post-load
                // `check_all_guards` pass makes such a constraint load-BLOCKING, so a
                // KB never finishes loading with one registered. Reaching it here
                // means a guard was registered without going through that check (a
                // programmer error, not user input). Retract and surface loudly.
                Err(e) => {
                    self.retract(rule_id);
                    let label = self.guards[idx].label.clone();
                    panic!(
                        "assert_checked: integrity constraint{} uses an unsupported \
                         LogicalQuery form ({}) — should have been rejected as \
                         load-blocking by check_all_guards (WI-513)",
                        load::label_suffix(&label), e,
                    );
                }
            }
        }

        Some(rule_id)
    }

    /// Evaluate every registered guard against the current KB — the WI-023
    /// post-load constraint check. Carrier-agnostic: each guard is read through
    /// [`TermView`](term_view::TermView).
    pub fn check_all_guards(&mut self) -> Vec<GuardCheck> {
        let mut out = Vec::with_capacity(self.guards.len());
        for idx in 0..self.guards.len() {
            let query = self.guards[idx].query.clone();
            let label = self.guards[idx].label.clone();
            // WI-513: `evaluate_guard` lowers the constraint through the shared
            // carrier-neutral `lower_query`, which surfaces an unsupported
            // LogicalQuery form (unknown ctor / non-goal leaf) loudly as a
            // `LowerError` rather than silently treating it as vacuously true.
            // WI-518: occurrence (`Value::Node`) leaves resolve like term leaves.
            match self.evaluate_guard(&query) {
                Ok(true) => out.push(GuardCheck::Holds),
                Ok(false) => out.push(GuardCheck::Violated(label)),
                Err(e) => out.push(GuardCheck::Unsupported(label, e.to_string())),
            }
        }
        out
    }

    /// Read a named child of a `LogicalQuery` view as an owned, carrier-agnostic
    /// `Value` (dropping any borrow of `self`).
    fn guard_child(&mut self, view: &crate::eval::value::Value, field: Symbol) -> Option<crate::eval::value::Value> {
        term_view::TermView::named_arg(view, self, field).map(|c| c.to_value())
    }

    /// Evaluate a `LogicalQuery` guard (read through `TermView`): `Ok(true)` if it
    /// holds, `Ok(false)` if violated, `Err(LowerError)` if the constraint uses a
    /// LogicalQuery form the shared lowerer cannot handle (WI-513 — surfaced loudly
    /// instead of vacuously holding). Carrier-agnostic — occurrence (`Value::Node`)
    /// and term leaves both resolve through `resolve_goals` (WI-518). Quantifier
    /// dispatch compares interned [`LogicalQuerySymbols`] (no per-node `String`).
    fn evaluate_guard(&mut self, guard: &crate::eval::value::Value) -> Result<bool, execute::LowerError> {
        let syms = execute::LogicalQuerySymbols::resolve(self);
        let Some(functor) = term_view::TermView::head(guard, self).functor_sym() else {
            // A bare leaf as a whole guard is not a quantified constraint we
            // enforce — it vacuously holds.
            return Ok(true);
        };
        let f = Some(functor);
        if f == syms.lone_q {
            self.eval_count_guard(guard, &syms, 0, 1)
        } else if f == syms.one_q {
            self.eval_count_guard(guard, &syms, 1, 1)
        } else if f == syms.some_q {
            self.eval_count_guard(guard, &syms, 1, usize::MAX)
        } else if f == syms.no_q {
            self.eval_count_guard(guard, &syms, 0, 0)
        } else if f == syms.forall_q {
            self.eval_forall_guard(guard, &syms)
        } else if f == syms.negation {
            self.eval_negation_guard(guard, &syms)
        } else {
            // Any other constructor — a top-level `pattern_query` / `conjunction`
            // from a NON-quantified constraint, or an unsupported kind — is not
            // ENFORCED (vacuously holds), but we still LOWER it so an unsupported
            // form surfaces as `Err(LowerError)` rather than silently passing
            // (WI-513). `.map(|_| true)` discards the goals: we validate the form,
            // we don't run the constraint.
            self.lower_query_with(guard, &syms).map(|_| true)
        }
    }

    /// Evaluate a counting quantifier guard (lone_q, one_q, some_q, no_q).
    fn eval_count_guard(
        &mut self,
        guard: &crate::eval::value::Value,
        syms: &execute::LogicalQuerySymbols,
        min: usize,
        max: usize,
    ) -> Result<bool, execute::LowerError> {
        let condition = self.guard_child(guard, syms.condition);
        let body = self.guard_child(guard, syms.body);

        let mut goals: Vec<crate::eval::value::Value> = Vec::new();
        if let Some(c) = &condition {
            goals.extend(self.lower_query_with(c, syms)?);
        }
        if let Some(b) = &body {
            // empty_query produces no goals — treat as trivially true
            goals.extend(self.lower_query_with(b, syms)?);
        }

        if goals.is_empty() {
            // No goals means trivially satisfied; count depends on context
            return Ok(min == 0);
        }

        let config = resolve::ResolveConfig {
            // One extra to detect overflow. `saturating_add` guards `some_q`,
            // whose `max` is `usize::MAX` (an unbounded upper bound) — a plain
            // `+ 1` would overflow-panic in debug / wrap to 0 (= unlimited) in
            // release.
            max_solutions: max.saturating_add(1),
            // WI-519: count only DEFINITE solutions — a floundered residual
            // (an undischarged goal) must not inflate the quantifier count.
            definite_only: true,
            ..resolve::ResolveConfig::default()
        };
        let solutions = self.resolve_goals(goals, &config);
        let count = solutions.len();
        Ok(count >= min && count <= max)
    }

    /// Evaluate forall_q(var, condition, body): condition AND body must hold
    /// for all solutions. Equivalent to: no solutions of (condition AND NOT body).
    fn eval_forall_guard(
        &mut self,
        guard: &crate::eval::value::Value,
        syms: &execute::LogicalQuerySymbols,
    ) -> Result<bool, execute::LowerError> {
        let condition = self.guard_child(guard, syms.condition);
        let body = self.guard_child(guard, syms.body);

        // forall x: P -: Q ≡ no x: P -: not(Q)
        let mut goals: Vec<crate::eval::value::Value> = Vec::new();
        if let Some(c) = &condition {
            goals.extend(self.lower_query_with(c, syms)?);
        }
        if let Some(b) = &body {
            let body_goals = self.lower_query_with(b, syms)?;
            if !body_goals.is_empty() {
                // Negate each body goal: `not(g)`, carrier-faithful (WI-518) — `g`
                // may be a Term or an occurrence Node. Use the QUALIFIED NAF builtin
                // symbol `anthill.reflect.not` (`syms.not`), the SAME symbol the
                // shared lowerer's `negation` arm uses, so `get_builtin_view`
                // classifies the goal as `BuiltinTag::Not` and NAF fires. A bare
                // `intern("not")` is a DIFFERENT, unregistered symbol — `not(g)`
                // would then resolve as an ordinary unmatched predicate (0
                // solutions), so a VIOLATED forall would silently "hold" (the
                // loud-over-silent rule's classic failure). Loud if reflect's `not`
                // is unavailable, mirroring the `negation` arm.
                let not_sym = syms.not.ok_or(execute::LowerError::NotYetImplemented(
                    "forall body negation without loaded anthill.reflect.not",
                ))?;
                for g in body_goals {
                    goals.push(self.make_goal_value(not_sym, vec![g]));
                }
            }
        }

        if goals.is_empty() {
            return Ok(true);
        }

        // If any DEFINITE solution exists, the forall is violated. WI-519: a
        // floundered residual must NOT count — counting it would report the
        // forall violated on an undecided (undischarged) witness.
        let config = resolve::ResolveConfig {
            max_solutions: 1,
            definite_only: true,
            ..resolve::ResolveConfig::default()
        };
        let solutions = self.resolve_goals(goals, &config);
        Ok(solutions.is_empty())
    }

    /// Evaluate negation(query): the inner query must have no solutions.
    fn eval_negation_guard(
        &mut self,
        guard: &crate::eval::value::Value,
        syms: &execute::LogicalQuerySymbols,
    ) -> Result<bool, execute::LowerError> {
        let inner = self.guard_child(guard, syms.query);

        if let Some(inner) = &inner {
            let goals = self.lower_query_with(inner, syms)?;
            if goals.is_empty() {
                return Ok(false); // negation of empty_query (always true) = false
            }
            let config = resolve::ResolveConfig {
                max_solutions: 1,
                // WI-519: only a DEFINITE inner solution refutes the negation; a
                // floundered residual is undecided, not a refutation.
                definite_only: true,
                ..resolve::ResolveConfig::default()
            };
            let solutions = self.resolve_goals(goals, &config);
            Ok(solutions.is_empty()) // negation holds if no solutions
        } else {
            Ok(true)
        }
    }

    pub fn assert_fact(
        &mut self,
        term: TermId,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        // WI-233: O(1) ground-fact dedup. Pre-WI-233 this was a linear
        // scan over `by_sort[sort]` which approached O(N²) total work
        // across many same-sort facts (~180 entries scanned per call
        // on the stdlib load; ~224 per call for the project workitem
        // set). At current N the wins are in the noise (~1-2ms in
        // release) but the algorithmic improvement matters as workitem
        // sets grow.
        if let Some(&rid) = self.fact_dedup.get(&(term, sort, domain)) {
            // Re-check `retracted` — the entry stays in the dedup map
            // even after retract() so re-asserting after retract
            // returns the same RuleId rather than allocating a new
            // slot. If callers want re-assert-after-retract to revive
            // the fact, they go through assert_rule directly.
            let entry = &self.rules[rid.index()];
            if !entry.retracted {
                return rid;
            }
        }
        self.assert_rule(term, vec![], sort, domain, meta)
    }

    /// Assert a value fact — a fact whose head is carrier-agnostic and may
    /// carry a `Value::Node` (denoted) subterm (WI-348 Phase B). A `Value::Term`
    /// head is an ordinary ground fact and routes to [`Self::assert_fact`]
    /// (hash-consed dedup + refcount). A Node-bearing head is stored directly:
    /// indexed by functor via its `TermView`, skipped by `fact_dedup` (no
    /// `TermId` key — a dedup-miss, not unsound), and inserted into the
    /// discrimination tree through the value carrier.
    pub fn assert_fact_value(
        &mut self,
        head: crate::eval::value::Value,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        use crate::eval::value::Value;
        if let Value::Term(t) = head {
            return self.assert_fact(t, sort, domain, meta);
        }
        // A value (Node/Entity) head: store + index via the shared epilogue. No
        // body (a fact) and no `fact_dedup` (its key is `Term`-only).
        self.push_value_head_entry(head, Vec::new(), sort, domain, meta)
    }

    /// Assert a fact `functor(pos…, named…)` from carrier-agnostic `Value`
    /// children, choosing the carrier once (WI-366). If every child is a ground
    /// `Value::Term`, the head is the hash-consed `Term::Fn` and routes to
    /// [`Self::assert_fact`] (dedup + structural sharing); if any child carries a
    /// `Value::Node` (a denoted value-in-type), the head is a `Value::Entity`
    /// value fact via [`Self::assert_fact_value`]. Collapses the
    /// build-Term-or-Entity choice the sort-relation producers (`SortAlias` /
    /// `SortRequiresInfo` / `SortProvidesInfo`) otherwise repeat.
    pub fn assert_fact_carrier(
        &mut self,
        functor: Symbol,
        pos: Vec<crate::eval::value::Value>,
        named: Vec<(Symbol, crate::eval::value::Value)>,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        use crate::eval::value::Value;
        // One source of the carrier decision, shared with [`Self::reify`]: the
        // all-ground head rides as a hash-consed `Term::Fn` (dedup + sharing) and
        // a `Value::Node`-bearing one as a `Value::Entity` value fact. Routing on
        // the assembled carrier keeps the two paths from ever disagreeing.
        match self.fn_value(functor, pos, named) {
            Value::Term(term) => self.assert_fact(term, sort, domain, meta),
            head => self.assert_fact_value(head, sort, domain, meta),
        }
    }

    /// Incref the ground `TermId` leaves reachable in a value head (WI-348
    /// Phase B), keeping them alive for the rule's lifetime — including those
    /// carried *inside* a `Value::Node` occurrence (e.g. a `denoted` Type's
    /// `TypeChild::Ground`), which the occurrence builders do NOT refcount
    /// themselves (review #1): without this, a hash-consed term shared with a
    /// term-carrier fact would dangle when that fact is retracted. Walks the
    /// head through `TermView` — the same surface the discrimination tree
    /// indexes — so the owned set matches what is searched.
    ///
    /// Known gap (deferred to the value-fact payoff phase): a Type/EffectExpr
    /// occurrence's `type_args`, and any field key not yet interned, are not
    /// surfaced by `TermView` and so are not owned here. Symmetric with
    /// `release_value_ground`, so balanced regardless.
    fn incref_value_ground(&mut self, v: &crate::eval::value::Value) {
        for t in self.collect_value_ground_terms(v) {
            self.terms.incref(t);
        }
    }

    /// Inverse of [`Self::incref_value_ground`], for retract. Collects the same
    /// multiset (the head Value is immutable once stored), so every incref is
    /// matched by exactly one release.
    fn release_value_ground(&mut self, v: &crate::eval::value::Value) {
        for t in self.collect_value_ground_terms(v) {
            self.terms.release(t);
        }
    }

    /// The ground `TermId` leaves reachable in a value, via `TermView` (so a
    /// `Value::Node` occurrence's ground children are included). Read-only; the
    /// caller increfs / releases the result.
    fn collect_value_ground_terms(&self, v: &crate::eval::value::Value) -> Vec<TermId> {
        let mut out = Vec::new();
        collect_value_ground_terms_into(self, v, &mut out);
        out
    }

    /// Mark a rule/fact as retracted. Removes from active indexes, decrements refcounts.
    pub fn retract(&mut self, id: RuleId) {
        let entry = &mut self.rules[id.index()];
        if entry.retracted {
            return;
        }
        entry.retracted = true;

        let head_val = entry.head.clone();
        let sort = entry.sort;
        let domain = entry.domain;
        let meta = entry.meta;
        // WI-246: body atoms are occurrences with no separate refcount to
        // release; emptiness (fact-ness) reads the occurrence body.
        let is_fact = entry.body_nodes.is_empty();
        let label = entry.label;

        // Remove from indexes
        if let Some(v) = self.by_sort.get_mut(&sort) {
            v.retain(|&rid| rid != id);
        }
        if let Some(v) = self.by_domain.get_mut(&domain) {
            v.retain(|&rid| rid != id);
        }
        // rules_by_functor via the head's `TermView` functor (any carrier — WI-348).
        // WI-436: `functor_sym` reads a 0-ary constructor's symbol off its bare
        // `Ref(c)` head, so retract removes from the SAME `rules_by_functor` bucket
        // `assert` populated (insert/retract stay symmetric).
        let head_functor = term_view::TermView::head(&head_val, self).functor_sym();
        if let Some(f) = head_functor {
            if let Some(v) = self.rules_by_functor.get_mut(&f) {
                v.retain(|&rid| rid != id);
            }
        }
        if let Some(label_sym) = label {
            if let Some(v) = self.rules_by_label.get_mut(&label_sym) {
                v.retain(|&rid| rid != id);
            }
        }

        // WI-233: ground-fact dedup index. Remove only if this RuleId
        // is the one currently keyed at (head, sort, domain) — a
        // previously-retracted-then-re-asserted fact may have a
        // different RuleId at that key.
        if is_fact {
            // Only Term-carrier heads were dedup-indexed (WI-348 Phase B).
            if let crate::eval::value::Value::Term(head_t) = &head_val {
                if let std::collections::hash_map::Entry::Occupied(e) =
                    self.fact_dedup.entry((*head_t, sort, domain))
                {
                    if *e.get() == id {
                        e.remove();
                    }
                }
            }
        }

        // Remove from discrimination tree (before releasing terms). The
        // view-driven walk needs `&self`, so detach the index first (WI-348).
        self.with_discrim_detached(|kb, discrim| {
            discrim.remove_ground(kb, &head_val, &id);
        });

        // Release refcounts (head/sort/domain/meta; the body atoms are
        // occurrences with no term-store refcount of their own — WI-246).
        self.release_value_ground(&head_val);
        self.terms.release(sort);
        self.terms.release(domain);
        if let Some(m) = meta {
            self.terms.release(m);
        }
    }

    // ── Sort management ─────────────────────────────────────────

    /// Register a sort term with its kind.
    pub fn register_sort(&mut self, sort_term: TermId, kind: SortKind) {
        self.sort_info.insert(sort_term, kind);
    }

    /// Register an entity-of relationship: entity is a constructor of parent sort.
    /// Updates in-memory indexes (sort_entities, entity_parent).
    /// The loader separately asserts EntityOf(entity, parent) facts in the KB.
    pub fn register_entity_of(&mut self, entity: TermId, parent: TermId) {
        self.sort_entities
            .entry(parent)
            .or_default()
            .push(entity);
        self.entity_parent.insert(entity, parent);
        // WI-511: an entity identity may be built as `Fn{c}` (before `c` is a
        // known constructor) OR as the canonical `Ref(c)` (alloc canonicalizes
        // once `c` is registered). Extract the functor from either carrier and
        // dual-key the canonical `Ref(c)` form, so an entity *value* that
        // arrives as `Ref(c)` (post-flip alloc) resolves to the same parent via
        // `is_entity_of` / `entity_parent_sort` as the `Fn{c}` identity does.
        let functor = match *self.terms.get(entity) {
            Term::Fn { functor, .. } => Some(functor),
            Term::Ref(s) => Some(s),
            _ => None,
        };
        if let Some(f) = functor {
            self.constructor_symbols.insert(f);
            let ref_tid = self.terms.alloc(Term::Ref(f));
            if ref_tid != entity {
                self.entity_parent.entry(ref_tid).or_insert(parent);
            }
        }
    }

    /// Check if `sub` is an entity of `sup` (1-level entity → parent sort).
    pub fn is_entity_of(&self, sub: TermId, sup: TermId) -> bool {
        if sub == sup {
            return true;
        }
        self.entity_parent.get(&sub) == Some(&sup)
    }

    /// Get the parent sort of an entity (1-level, non-transitive).
    pub fn entity_parent_sort(&self, entity: TermId) -> Option<TermId> {
        self.entity_parent.get(&entity).copied()
    }

    /// Get the parent sort of a constructor by its functor symbol.
    /// Searches entity_parent for any entity whose functor matches.
    pub fn constructor_parent_sort(&self, functor: Symbol) -> Option<TermId> {
        for (&entity_tid, &parent_tid) in &self.entity_parent {
            // WI-511: an entity identity is `Fn{c}` or the canonical `Ref(c)`.
            let f = match *self.terms.get(entity_tid) {
                Term::Fn { functor: f, .. } => Some(f),
                Term::Ref(s) => Some(s),
                _ => None,
            };
            if f == Some(functor) {
                return Some(parent_tid);
            }
        }
        None
    }

    /// All entity-constructor functor symbols whose parent sort is `sort_sym`
    /// (WI-397). Enumerated from the entity→parent index, which holds every
    /// registered entity; the returned symbols are exactly the
    /// [`Self::entity_field_types`] keys (both the index key and the field-types
    /// key come from `remap_name(entity.name)` — `name_to_sort_term` builds the
    /// `entity_parent` key as `Fn{remap_name(..)}`). Used by the projection
    /// eliminator to resolve a field-access receiver's field type.
    pub fn constructors_of_sort(&self, sort_sym: Symbol) -> Vec<Symbol> {
        let mut out = Vec::new();
        for (&entity_tid, &parent_tid) in &self.entity_parent {
            let parent_functor = match self.terms.get(parent_tid) {
                Term::Fn { functor, .. } => Some(*functor),
                Term::Ref(s) => Some(*s),
                _ => None,
            };
            if parent_functor != Some(sort_sym) {
                continue;
            }
            match self.terms.get(entity_tid) {
                Term::Fn { functor, .. } => out.push(*functor),
                Term::Ref(s) => out.push(*s),
                _ => {}
            }
        }
        out
    }

    /// Constructors to inspect when resolving a FIELD of `sort_sym`: its entity
    /// variants ([`Self::constructors_of_sort`]) PLUS `sort_sym` itself when it
    /// is a free-standing entity. A top-level `entity Pose(x, y)` is its own
    /// constructor with no parent sort, so `constructors_of_sort` is empty for
    /// it, yet `entity_field_types(Pose)` holds its fields — the same
    /// free-standing-entity case `check_constructor_iter` handles ("the entity
    /// is its own type"). Field lookups that only walked `constructors_of_sort`
    /// thus missed every field of a free-standing entity (WI-490: a `(p).x` on
    /// such a receiver failed dot dispatch). Self is appended (deduped) so a
    /// normal multi-variant sort — whose own symbol carries no
    /// `entity_field_types` — is unaffected.
    pub fn field_constructors_of_sort(&self, sort_sym: Symbol) -> Vec<Symbol> {
        let mut out = self.constructors_of_sort(sort_sym);
        if self.entity_field_types(sort_sym).is_some() && !out.contains(&sort_sym) {
            out.push(sort_sym);
        }
        out
    }

    /// Does `sort_sym` have any entity constructor — i.e. is it a
    /// constructor-shaped DATA sort rather than an abstract spec? Used by the
    /// provider-info loader (WI-407) to tell `sort QueryableStore { fact Store }`
    /// (Store is an abstract spec → a provider edge) from `sort Holder { fact
    /// Color[..] }` (Color is a data sort with `entity red/green` → a data fact,
    /// NOT a provider edge).
    ///
    /// Reads the SYMBOL TABLE (a direct child symbol of kind `Entity`), not the
    /// runtime `entity_parent` index, ON PURPOSE: `entity_parent` is populated
    /// incrementally as each sort body loads, so a fact processed BEFORE its
    /// referenced sort's body (a forward reference) would see it empty and
    /// misclassify a data sort as a spec. Child symbols are all defined in
    /// `scan_definitions` (pass 1, before any loading), so this answer is
    /// load-order-independent. Mirrors [`Self::type_params_of_sort`]'s
    /// direct-child scan.
    pub fn sort_has_constructors(&self, sort_sym: Symbol) -> bool {
        let qn = self.qualified_name_of(sort_sym);
        let prefix = format!("{qn}.");
        self.symbols.by_qualified_name.iter().any(|(child_qn, &child_sym)| {
            child_qn.starts_with(&prefix)
                && !child_qn[prefix.len()..].contains('.')   // direct child only
                && matches!(self.kind_of(child_sym), Some(SymbolKind::Entity))
        })
    }

    // ── Query ───────────────────────────────────────────────────

    /// All active rules/facts of a given sort (including entities of that sort).
    pub fn by_sort(&self, sort: TermId) -> Vec<RuleId> {
        let mut result = Vec::new();

        // Direct entries of this sort
        if let Some(ids) = self.by_sort.get(&sort) {
            for &rid in ids {
                if !self.rules[rid.index()].retracted {
                    result.push(rid);
                }
            }
        }

        // Entries of entity children (1-level only)
        if let Some(children) = self.sort_entities.get(&sort) {
            for &child in children {
                if let Some(ids) = self.by_sort.get(&child) {
                    for &rid in ids {
                        if !self.rules[rid.index()].retracted {
                            result.push(rid);
                        }
                    }
                }
            }
        }

        result
    }

    /// All active rules/facts with a given top-level functor symbol.
    /// Remove `id` from the `rules_by_functor` head index without
    /// retracting the rule. The rule still exists in the KB —
    /// reachable by `try_resolve_symbol` (for cite-resolution),
    /// `by_sort`, `by_domain`, and direct `RuleId` access — but
    /// SLD's `rules_by_functor`-driven goal resolution will not consult
    /// it.
    ///
    /// Used for opt-in equational rules per WI-139: equational
    /// laws (head is an `=` application) without a `[simp]` /
    /// `[unfold]` attribute are cite-required only and must not
    /// drive automatic SLD rewriting (which would loop on rules
    /// like `add_comm: add(a, b) = add(b, a)`).
    pub fn unindex_functor(&mut self, id: RuleId) {
        let head = self.rule_head(id);
        if let Term::Fn { functor, .. } = *self.terms.get(head) {
            if let Some(v) = self.rules_by_functor.get_mut(&functor) {
                v.retain(|&rid| rid != id);
            }
        }
    }

    pub fn rules_by_functor(&self, sym: Symbol) -> Vec<RuleId> {
        self.rules_by_functor
            .get(&sym)
            .map(|v| {
                v.iter()
                    .copied()
                    .filter(|rid| !self.rules[rid.index()].retracted)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// All active rules/facts belonging to a given domain.
    pub fn by_domain(&self, domain: TermId) -> Vec<RuleId> {
        self.by_domain
            .get(&domain)
            .map(|v| {
                v.iter()
                    .copied()
                    .filter(|rid| !self.rules[rid.index()].retracted)
                    .collect()
            })
            .unwrap_or_default()
    }

    // ── Rule accessors ───────────────────────────────────────────

    /// Get the head of a rule/fact as a hash-consed `TermId`. The head is stored
    /// carrier-agnostically (`Value`, WI-348 Phase B); the universal case is
    /// `Value::Term`. This is the **single** term-only head reader (WI-348 folded
    /// the former `head_term_id` helper in here — there is no generic "head →
    /// TermId" operation, since a value-fact head has no `TermId`). **Panics on a
    /// value-fact head** (`Value::Entity` / `Value::Node`): the panic is the
    /// deliberate trip-wire — a value fact must never reach a term-only head
    /// reader; carrier-agnostic readers use `rule_head_value` / `TermView`. (The
    /// `is_equation` bug was exactly such a leak, surfaced by this panic, then fixed.)
    pub fn rule_head(&self, id: RuleId) -> TermId {
        match &self.rules[id.index()].head {
            crate::eval::value::Value::Term(t) => *t,
            other => panic!(
                "rule_head: head is not a Term carrier — a value fact reached a \
                 term-only head reader (WI-348); read via `rule_head_value` / \
                 `TermView` instead: {}",
                other.type_name(),
            ),
        }
    }

    /// Get the head of a rule as a carrier-agnostic `Value` (WI-348). The
    /// universal case is `Value::Term`; a value fact (e.g. an `OperationInfo`
    /// carrying a `denoted` effect label) carries a `Value::Entity` / `Value::Node`.
    /// Readers that must tolerate both carriers walk this via `TermView` rather
    /// than calling the panicking `rule_head` term-only reader.
    pub fn rule_head_value(&self, id: RuleId) -> &crate::eval::value::Value {
        &self.rules[id.index()].head
    }

    /// The head of a fact as a ground hash-consed `TermId`, or `None` if it is a
    /// value fact (a `Value::Node`/`Value::Entity`-carrying head — WI-348/WI-366).
    /// The carrier-agnostic skip for the term-only readers of the sort-relation
    /// reflect facts (`SortAlias` / `SortRequiresInfo` / `SortProvidesInfo`): a
    /// value head has no `TermId`, so a term-only reader treats `None` as "skip
    /// this fact" — occurrence-based handling is gated effect-expressions-as-types
    /// work (the producer surfaces a diagnostic). Avoids the `rule_head` panic
    /// on a value head.
    pub fn fact_head_term(&self, id: RuleId) -> Option<TermId> {
        match &self.rules[id.index()].head {
            crate::eval::value::Value::Term(t) => Some(*t),
            _ => None,
        }
    }

    /// The named args of a fact head when it is a ground `Term::Fn`, else `None`
    /// (a value head, or a non-`Fn` term). An owned clone — the carrier-agnostic
    /// skip peer of [`Self::fact_head_term`] for readers that pull named fields
    /// (`sort_ref` / `spec`) off a sort-relation reflect fact.
    pub fn fact_head_named_args(&self, id: RuleId) -> Option<SmallVec<[(Symbol, TermId); 2]>> {
        match self.get_term(self.fact_head_term(id)?) {
            Term::Fn { named_args, .. } => Some(named_args.clone()),
            _ => None,
        }
    }

    /// Whether a rule id refers to a live (non-retracted) rule. Out-of-bounds
    /// ids return false. Use before reading rule fields when the caller
    /// can't guarantee the id was just produced.
    pub fn is_rule_alive(&self, id: RuleId) -> bool {
        self.rules
            .get(id.index())
            .map(|r| !r.retracted)
            .unwrap_or(false)
    }

    /// Whether a rule is a fact — i.e. has an empty body. Backed by the
    /// occurrence body (`body_nodes`), the sole body representation (WI-246).
    pub fn is_fact(&self, id: RuleId) -> bool {
        self.rules[id.index()].body_nodes.is_empty()
    }

    /// WI-246: the rule body atoms as `NodeOccurrence`s (empty for facts) — the
    /// sole body representation. The form the resolver opens as goals and the
    /// typer / `simp_rewrite` walk.
    pub fn rule_body_nodes(&self, id: RuleId) -> &[Rc<NodeOccurrence>] {
        &self.rules[id.index()].body_nodes
    }

    /// WI-282: replace a rule's body atoms with their typer-rewritten form (the
    /// rule-body peer of [`set_op_body_node`]). Used after dot dispatch rewrites a
    /// body's `Expr::DotApply` to its `Apply`/`field_access` form. Dispatch never
    /// changes a body's variable set (the receiver var is reused, the synthesized
    /// field-name is a `Ref` constant), so the rule's `arity`/`globals`/
    /// `shared_arity` stay valid and the head-indexed discrim entry is untouched.
    pub fn set_rule_body_nodes(&mut self, id: RuleId, body_nodes: Vec<Rc<NodeOccurrence>>) {
        self.rules[id.index()].body_nodes = body_nodes;
    }

    /// Get the sort of a rule.
    pub fn rule_sort(&self, id: RuleId) -> TermId {
        self.rules[id.index()].sort
    }

    /// Get the domain of a rule.
    pub fn rule_domain(&self, id: RuleId) -> TermId {
        self.rules[id.index()].domain
    }

    /// Get the meta of a rule.
    pub fn rule_meta(&self, id: RuleId) -> Option<TermId> {
        self.rules[id.index()].meta
    }

    // ── Fact accessors (aliases for rule accessors) ──────────────

    /// Get the head term of a fact (alias for `rule_head`).
    pub fn fact_term(&self, id: RuleId) -> TermId {
        self.rule_head(id)
    }

    /// Get the sort of a fact (alias for `rule_sort`).
    pub fn fact_sort(&self, id: RuleId) -> TermId {
        self.rule_sort(id)
    }

    /// Get the domain of a fact (alias for `rule_domain`).
    pub fn fact_domain(&self, id: RuleId) -> TermId {
        self.rule_domain(id)
    }

    /// Get the meta of a fact (alias for `rule_meta`).
    pub fn fact_meta(&self, id: RuleId) -> Option<TermId> {
        self.rule_meta(id)
    }

    // ── Sort management queries ──────────────────────────────────

    /// WI-240 — look up the runtime target op for a spec op dispatched
    /// onto impl sort `impl_sort`. `op_short` is the spec op's short
    /// name symbol (e.g. `lt`). Returns `S.<op>` when the impl
    /// overrides with a runnable body, the spec op itself when it
    /// relies on the spec's rewrite-rule default, or `None` when the
    /// impl carries no entry for `op_short` (the impl doesn't claim to
    /// provide this spec — the typer rejects such dispatches before
    /// this lookup). Direct table read, no string concatenation.
    pub fn sort_ops_lookup(&self, impl_sort: Symbol, op_short: Symbol) -> Option<Symbol> {
        let key = self.canonical_sort_sym(impl_sort);
        self.sort_ops.by_impl.get(&key)?.get(&op_short).copied()
    }

    /// WI-240 — record a `(impl_sort, op_short) → target` entry. Called
    /// only by `load::build_sort_ops_table`.
    pub(crate) fn insert_sort_op(&mut self, impl_sort: Symbol, op_short: Symbol, target: Symbol) {
        let key = self.canonical_sort_sym(impl_sort);
        self.sort_ops.by_impl.entry(key).or_default().insert(op_short, target);
    }

    /// Canonicalize a sort symbol to the single resolved `Symbol` for
    /// its qualified name. The same logical sort can be interned under
    /// several `Symbol`s (e.g. an unresolved scan-time copy and the
    /// resolved load-time copy); `by_qualified_name` maps the QN to one
    /// canonical resolved symbol. Used as the `sort_ops` outer key so a
    /// table populated under one copy is found via another at dispatch.
    /// WI-350: also used by the carrier-aware dispatch filter and the
    /// interpreter's value-directed dispatch, which compare sort identities
    /// that may be interned under different copies.
    pub(crate) fn canonical_sort_sym(&self, sym: Symbol) -> Symbol {
        let qn = self.qualified_name_of(sym);
        self.symbols.by_qualified_name.get(qn).copied().unwrap_or(sym)
    }

    /// Get sort kind info.
    pub fn sort_kind(&self, sort_term: TermId) -> Option<SortKind> {
        self.sort_info.get(&sort_term).copied()
    }

    /// Iterate sort_info entries (sort term → kind).
    pub fn sort_info_iter(&self) -> impl Iterator<Item = (&TermId, &SortKind)> {
        self.sort_info.iter()
    }

    /// Get the base substitution for a sort (maps all slots to themselves).
    pub fn sort_base_subst(&self, sym: Symbol) -> Option<&[(Symbol, TermId)]> {
        self.sort_base_subst.get(&sym).map(|v| v.as_slice())
    }

    /// Set the base substitution for a sort.
    pub fn set_sort_base_subst(&mut self, sym: Symbol, subst: Vec<(Symbol, TermId)>) {
        self.sort_base_subst.insert(sym, subst);
    }

    /// Get immediate entity children of a sort.
    pub fn sort_children(&self, sort_term: TermId) -> &[TermId] {
        self.sort_entities
            .get(&sort_term)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    // ── Counting ─────────────────────────────────────────────────

    /// Number of active (non-retracted) entries with empty body (ground facts).
    pub fn fact_count(&self) -> usize {
        // WI-246: body-emptiness reads the occurrence body (`body_nodes`), not
        // the term `body` — both have equal arity (assert enforces it), so this
        // is unchanged, but it does not depend on the term body that is being
        // retired.
        self.rules.iter().filter(|r| !r.retracted && r.body_nodes.is_empty()).count()
    }

    /// Number of active (non-retracted) entries with non-empty body (proper rules).
    pub fn rule_count(&self) -> usize {
        self.rules.iter().filter(|r| !r.retracted && !r.body_nodes.is_empty()).count()
    }

    /// All live (non-retracted) rule ids — *including* the WI-139 cite-required
    /// equational rules that `unindex_functor` pulled from `rules_by_functor`.
    /// WI-363's op-coverage check enumerates equational definitions this way:
    /// `rule op(args) = rhs` has no functor-index entry, so a `rules_by_functor`
    /// walk would miss it. Returns an owned `Vec` so callers can mutate the KB
    /// (intern, resolve) while iterating.
    pub fn live_rule_ids(&self) -> Vec<RuleId> {
        (0..self.rules.len())
            .map(RuleId::from_index)
            .filter(|&r| !self.rules[r.index()].retracted)
            .collect()
    }

    /// Live term count in the hash-consed `TermStore`. Diagnostic — used by
    /// 026.1 Q4's acceptance test to verify external-stream scans do not grow
    /// the main term store.
    pub fn term_store_len(&self) -> usize {
        self.terms.len()
    }

    // ── Term matching ─────────────────────────────────────────────
    //
    // match_term inserts `target` into a temporary discrimination tree and
    // queries with `pattern`, reusing the real KB indexing infrastructure.

    /// Match `pattern` against `target` using a temporary discrimination tree.
    ///
    /// Variables on the pattern side bind to corresponding subterms of
    /// `target`. Variables on the target side are inserted into the tree
    /// as variable edges and bind when the pattern provides concrete values.
    ///
    /// Returns `Some(subst)` on success, `None` on failure.
    pub fn match_term(&self, pattern: TermId, target: TermId) -> Option<subst::Substitution> {
        self.match_view(pattern, &term_view::TermIdView(target))
    }

    /// Value-aware match: unifies a rule-head pattern (always `TermId`)
    /// against any [`TermView`] target. For a `TermIdView(t)` target this
    /// is semantically equivalent to `match_term(pattern, t)`; for a
    /// `Value`-backed target it preserves lineage (no promotion into the
    /// `TermStore`). Variable bindings flow into the result substitution
    /// as `Value::Term` for Term targets and the raw `Value` for others.
    pub fn match_view<V: term_view::TermView>(
        &self,
        pattern: TermId,
        target: &V,
    ) -> Option<subst::Substitution> {
        let mut tree = SubstTree::<()>::new();
        tree.insert_pattern(self, &term_view::TermIdView(pattern), ());
        let results = tree.query_resolved(self, target, |_| pattern);
        results.into_iter()
            .map(|(_, s)| s)
            .find(|s| !s.is_contradiction())
    }

    /// Find all active rules/facts whose head matches the given pattern.
    ///
    /// Uses the discrimination tree for multi-level structural dispatch.
    /// Variable bindings are resolved via path extraction from head terms.
    /// Representation-neutral (WI-349): the pattern is anything implementing
    /// [`term_view::TermView`] — a `TermId` ground pattern, a `Value`, or a
    /// `Value::Node` occurrence — so there is no term-only query door. Thin
    /// alias for [`Self::query_view`] (the established `TermView` core), which
    /// reads the pattern against the structurally-keyed discrimination tree (no
    /// hash-cons identity required).
    pub fn query<V: term_view::TermView>(
        &self,
        pattern: V,
    ) -> Vec<(RuleId, subst::Substitution)> {
        self.query_view(&pattern)
    }

    /// `query` generic over the goal representation: `pattern` is anything
    /// viewable as a term — `TermIdView(TermId)` for the term-goal path, or a
    /// `Value` / `Value::Node` occurrence goal (WI-246), since the matcher
    /// reads the goal only through [`TermView`] and the discrim tree indexes
    /// rule heads structurally. Avoids lowering an occurrence goal to a
    /// hash-consed term just to look up candidates.
    pub fn query_view<V: term_view::TermView>(
        &self,
        pattern: &V,
    ) -> Vec<(RuleId, subst::Substitution)> {
        let rules = &self.rules;
        let candidates = self.discrim.query_resolved_value(
            self,
            pattern,
            |rid: &RuleId| rules[rid.index()].head.clone(),
        );

        let mut results = Vec::new();
        for (rid, tree_subst) in candidates {
            if rules[rid.index()].retracted {
                continue;
            }
            if tree_subst.is_contradiction() {
                continue;
            }
            results.push((rid, tree_subst));
        }
        // Stable-sort: facts (empty body) before rules (non-empty body).
        // The discrimination tree uses HashMap internally, so candidate order
        // is non-deterministic. DFS resolution depends on trying ground facts
        // before recursive rules to find base-case solutions first.
        results.sort_by_key(|(rid, _)| if rules[rid.index()].body_nodes.is_empty() { 0 } else { 1 });
        results
    }

    /// Find all active rules (non-empty body) whose head matches the pattern.
    /// Representation-neutral over the pattern carrier (WI-349).
    pub fn query_rules<V: term_view::TermView>(
        &self,
        pattern: V,
    ) -> Vec<(RuleId, subst::Substitution)> {
        self.query(pattern)
            .into_iter()
            .filter(|(rid, _)| !self.rules[rid.index()].body_nodes.is_empty())
            .collect()
    }

    // ── Variable-aware operations ─────────────────────────────

    /// Collect all VarIds occurring in a term (DFS, deduped).
    pub fn collect_vars(&self, term: TermId) -> Vec<VarId> {
        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        self.collect_vars_rec(term, &mut vars, &mut seen);
        vars
    }

    fn collect_vars_rec(&self, term: TermId, vars: &mut Vec<VarId>, seen: &mut std::collections::HashSet<u32>) {
        match self.terms.get(term) {
            Term::Var(Var::Global(vid)) => {
                if seen.insert(vid.raw()) {
                    vars.push(*vid);
                }
            }
            Term::Var(Var::DeBruijn(_)) => {}
            Term::Fn { pos_args, named_args, .. } => {
                let pos_args = pos_args.clone();
                let named_args = named_args.clone();
                for &id in pos_args.iter() {
                    self.collect_vars_rec(id, vars, seen);
                }
                for &(_, id) in named_args.iter() {
                    self.collect_vars_rec(id, vars, seen);
                }
            }
            _ => {}
        }
    }

    /// Map a function over the children of an Fn term, returning the same TermId
    /// if nothing changed (avoids unnecessary allocation and hash-consing).
    pub(crate) fn map_fn_children(&mut self, term: TermId, mut f: impl FnMut(&mut Self, TermId) -> TermId) -> TermId {
        match self.terms.get(term).clone() {
            Term::Fn { functor, pos_args, named_args } => {
                let mut changed = false;
                let new_pos: SmallVec<[TermId; 4]> = pos_args
                    .iter()
                    .map(|&id| { let r = f(self, id); if r != id { changed = true; } r })
                    .collect();
                let new_named: SmallVec<[(crate::intern::Symbol, TermId); 2]> = named_args
                    .iter()
                    .map(|&(sym, id)| { let r = f(self, id); if r != id { changed = true; } (sym, r) })
                    .collect();
                if changed {
                    self.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named })
                } else {
                    term
                }
            }
            _ => term,
        }
    }

    /// Apply a substitution to a term, replacing Var nodes with their bindings.
    /// Returns a new hash-consed TermId.
    pub fn apply_subst(&mut self, term: TermId, subst: &subst::Substitution) -> TermId {
        match self.terms.get(term).clone() {
            // Term-world substitution: a non-`Term` carrier (a `Value::Node`)
            // can't be a `Term` child, so a var bound to one stays the var.
            Term::Var(Var::Global(vid)) => match subst.resolve_as_value(vid) {
                Some(crate::eval::value::Value::Term(t)) => *t,
                _ => term,
            },
            Term::Var(Var::DeBruijn(_)) => term,
            Term::Fn { .. } => self.map_fn_children(term, |kb, id| kb.apply_subst(id, subst)),
            _ => term,
        }
    }

    // ── Walk / reify ──────────────────────────────────────────────

    /// Chase Var→binding→Var chains through a substitution, **term-world**:
    /// returns the final non-variable `TermId`, or the last unbound Var — and a
    /// var bound to a non-`Term` carrier (a `Value::Node`, a scalar) STOPS the
    /// chase at that var (the Node is not represented in the `TermId` result).
    /// Use this only where a `TermId` is genuinely the right shape — building a
    /// term (`apply_subst`), inspecting a synthetic term marker
    /// (`forall_impl` / `push_choice` goal-classification), or recursing over
    /// term structure (`is_ground`, `collect_unbound_vars`). The carrier-faithful
    /// chase that SURFACES a `Value::Node` is [`Self::walk_view`]; a builtin
    /// reading a term-shaped arg uses `walk_arg_term` (which rejects a non-term
    /// carrier rather than silently chasing past it). WI-348.
    pub fn walk(&self, term: TermId, subst: &subst::Substitution) -> TermId {
        use crate::eval::value::Value;
        let mut current = term;
        loop {
            match self.terms.get(current) {
                Term::Var(Var::Global(vid)) => match subst.resolve_as_value(*vid) {
                    Some(Value::Term(bound)) => {
                        if *bound == current {
                            return current; // self-referential, stop
                        }
                        current = *bound;
                    }
                    // Non-`Term` carrier (a `Value::Node`/scalar) or unbound:
                    // stop at the var. This is the term-world chase; the
                    // carrier-faithful one is `walk_view`.
                    _ => return current,
                },
                _ => return current,
            }
        }
    }

    /// `TermView`-aware [`walk`] (WI-277): chase Var→binding chains through
    /// the substitution following **both** term and non-term `Value`
    /// bindings, returning the resolved `Value`. `Value::Term(t)` for a
    /// term-shaped result (a `Fn`, a leaf, or an unbound var — to recurse
    /// into / inspect), or a non-term `Value` (`Value::Node`, a literal, …)
    /// when a variable is bound to one. The view-level counterpart of
    /// `walk`, used by the typer-phase rewriter's occurrence build side.
    pub fn walk_view(
        &self,
        term: TermId,
        subst: &subst::Substitution,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        let mut current = term;
        loop {
            match self.terms.get(current) {
                Term::Var(Var::Global(vid)) => match subst.resolve_as_value(*vid) {
                    Some(Value::Term(next)) if *next != current => current = *next,
                    Some(Value::Term(_)) | None => return Value::Term(current),
                    Some(other) => return other.clone(),
                },
                _ => return Value::Term(current),
            }
        }
    }

    /// Deep-reify a term through the substitution to a carrier-agnostic
    /// [`Value`] (WI-348). The carrier-faithful successor of the former
    /// `TermId`-only reify: a var bound to a `Value::Node` (a denoted/occurrence
    /// answer) — or any other non-`Term` value — is returned with its
    /// **identity intact**, never materialized to a `TermId` (which is lossy: it
    /// drops the occurrence's identity/span).
    ///
    /// Reification rebuilds **through `Term::Fn` structure**, chasing each var
    /// child's binding chain: an all-`Term` result rebuilds a hash-consed
    /// `Value::Term(Fn)` (the universal case), a `Fn` with any non-`Term` child
    /// becomes the same `Value::Entity` carrier a value fact uses (assembled by
    /// [`Self::fn_value`]). A var bound to a non-`Term` *carrier* (`Value::Node`
    /// / `Entity` / `Tuple` / scalar) is returned **as-is** — its identity is
    /// the answer; recursing into such a carrier's own children to chase a
    /// nested unbound var is unnecessary until value *rule* heads land
    /// (WI-348 Phase C, no consumer yet). Read an answer binding with this; a
    /// caller that handles a non-`Term` carrier narrows explicitly (`if let
    /// Value::Term(t) = …`) or reads it carrier-agnostically via
    /// [`crate::kb::term_view::TermView`], while one that genuinely demands a
    /// hash-consed term uses [`crate::eval::value::Value::expect_term`] (which
    /// fails loud on a non-`Term` carrier — WI-477).
    pub fn reify(&mut self, term: TermId, subst: &subst::Substitution) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        // Chase the var chain carrier-faithfully — `walk_view` surfaces a
        // non-`Term` binding the `TermId`-only `walk` cannot see.
        match self.walk_view(term, subst) {
            Value::Term(t) => match self.terms.get(t).clone() {
                Term::Fn { functor, pos_args, named_args } => {
                    let pos: Vec<Value> =
                        pos_args.iter().map(|&id| self.reify(id, subst)).collect();
                    let named: Vec<(Symbol, Value)> = named_args
                        .iter()
                        .map(|&(sym, id)| (sym, self.reify(id, subst)))
                        .collect();
                    self.fn_value(functor, pos, named)
                }
                // Leaf (Const/Ref/Ident/…) or an unbound `Var` — already final.
                _ => Value::Term(t),
            },
            // A bound non-`Term` carrier (`Value::Node` / `Entity` / scalar /
            // `Var`) — return as-is, identity preserved through the answer.
            other => other,
        }
    }

    /// Assemble a functor application `functor(pos…, named…)` from child
    /// `Value`s into its canonical head carrier (WI-348) — the **single source**
    /// of the `Term`-vs-`Value::Entity` decision, shared by [`Self::reify`]
    /// (rebuilding a reified `Fn`) and [`Self::assert_fact_carrier`] (asserting
    /// the result). All-`Term` children rebuild a hash-consed `Value::Term(Fn)`
    /// (the universal case — dedup-able, indexes identically); any non-`Term`
    /// child forces a `Value::Entity`, which cannot hash-cons but reads back
    /// through `TermView` like its term twin.
    fn fn_value(
        &mut self,
        functor: Symbol,
        pos: Vec<crate::eval::value::Value>,
        named: Vec<(Symbol, crate::eval::value::Value)>,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        let all_term = pos.iter().all(|v| matches!(v, Value::Term(_)))
            && named.iter().all(|(_, v)| matches!(v, Value::Term(_)));
        if all_term {
            let pos_args: SmallVec<[TermId; 4]> =
                pos.iter().map(|v| v.expect_term()).collect();
            let named_args: SmallVec<[(Symbol, TermId); 2]> = named
                .iter()
                .map(|(s, v)| (*s, v.expect_term()))
                .collect();
            Value::Term(self.alloc(Term::Fn { functor, pos_args, named_args }))
        } else {
            Value::Entity {
                functor,
                pos: std::rc::Rc::from(pos),
                named: std::rc::Rc::from(named),
            }
        }
    }

    /// Deep-reify a goal [`Value`] through `σ`, carrier-faithfully — the
    /// `Value`-carrier front for [`Self::reify`] (WI-348). A `Value::Term`
    /// deep-substitutes via `reify` (rebuilding through `Term::Fn`); a
    /// `Value::Node` occurrence substitutes via `substitute_occurrence`, which
    /// **preserves the occurrence's identity/span** — it is spliced/rewritten in
    /// place, never rebuilt structurally and never dropped to a bare var; a
    /// scalar / value-level var passes through. Used at the resolver's goal
    /// boundaries that need a σ-applied goal as a `Value` — NAF sub-resolution
    /// and assumed-fact matching — so neither lowers an occurrence goal to a
    /// hash-consed term. Distinct from `reify_goal_value` (resolve.rs), the
    /// term-only materializer (`Value -> TermId`, no `σ`) the remaining
    /// term-structured goal-handlers still use.
    pub(crate) fn reify_value(
        &mut self,
        v: &crate::eval::value::Value,
        subst: &subst::Substitution,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        match v {
            Value::Term(t) => self.reify(*t, subst),
            Value::Node(occ) => {
                Value::Node(node_occurrence::substitute_occurrence(self, occ, subst))
            }
            other => other.clone(),
        }
    }

    // ── De Bruijn conversion ────────────────────────────────────

    /// Assert a rule with De Bruijn conversion applied, occurrence body supplied
    /// directly (WI-246/WI-372 — the single rule-DeBruijn-assertion path). The
    /// loader builds the occurrences natively from the parse IR; the synthesized
    /// / hand-built callers convert a term body once via
    /// [`Self::term_body_to_nodes`]. The `head` is carrier-agnostic (WI-373):
    /// every existing caller passes a `TermId` (→ `Value::Term`), but it may also
    /// carry a `Value::Node`/`Entity` value head whose vars close to De Bruijn
    /// like a term head's (an `Expr` Node child works; a *denoted* `Type` Node
    /// child still needs the WI-342-P3 Type-occurrence var-walk). The rule's free
    /// vars are collected from the head + occurrence body in the same
    /// first-occurrence order (`collect_value_head_vars` mirrors
    /// `collect_occurrence_global_vars_ordered` mirrors `collect_vars_rec`), then
    /// `finalize_rule_debruijn_nodes` closes head + occurrences.
    pub fn assert_rule_debruijn_with_nodes(
        &mut self,
        head: impl Into<crate::eval::value::Value>,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        let head = head.into();
        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        self.collect_value_head_vars(&head, &mut vars, &mut seen);
        for n in &body_nodes {
            node_occurrence::collect_occurrence_global_vars_ordered(self, n, &mut vars, &mut seen);
        }
        self.finalize_rule_debruijn_nodes(head, body_nodes, vars, 0, sort, domain, meta)
    }

    /// Collect a rule head's Global `VarId`s in first-occurrence order,
    /// carrier-agnostically (WI-373) — the head twin of
    /// `collect_occurrence_global_vars_ordered` (body). A `Value::Term` walks via
    /// `collect_vars_rec`; a `Value::Node` via the occurrence walker; a
    /// `Value::Entity` recurses pos-then-named, matching the term-head walk order
    /// so head/body De Bruijn indices align.
    pub(crate) fn collect_value_head_vars(
        &self,
        head: &crate::eval::value::Value,
        vars: &mut Vec<VarId>,
        seen: &mut std::collections::HashSet<u32>,
    ) {
        use crate::eval::value::Value;
        match head {
            Value::Term(t) => self.collect_vars_rec(*t, vars, seen),
            Value::Node(occ) => {
                node_occurrence::collect_occurrence_global_vars_ordered(self, occ, vars, seen)
            }
            // A functor head or an anonymous tuple: recurse into the children
            // (any of which can carry vars), pos before named.
            Value::Entity { pos, named, .. } | Value::Tuple { pos, named } => {
                for c in pos.iter() {
                    self.collect_value_head_vars(c, vars, seen);
                }
                for (_, c) in named.iter() {
                    self.collect_value_head_vars(c, vars, seen);
                }
            }
            // Scalar head children carry no Global vars.
            Value::Int(_) | Value::BigInt(_) | Value::Float(_) | Value::Bool(_)
            | Value::Str(_) | Value::Unit => {}
            // A bare value-level var (WI-109) or a runtime carrier
            // (Closure/Stream/Lazy/…) is not a shape a stored rule head takes —
            // fail loudly rather than silently undercount the rule's arity.
            other => debug_assert!(
                false,
                "WI-373: unexpected value rule-head carrier in var-collection: {}",
                other.type_name(),
            ),
        }
    }

    /// Close a rule head's Global vars to De Bruijn, carrier-agnostically
    /// (WI-373) — the head twin of the body's `node_to_debruijn` close, kept in
    /// lockstep with [`Self::collect_value_head_vars`] (same carriers, same
    /// recursion). A `Value::Term` closes via `term_to_debruijn`; a `Value::Node`
    /// occurrence via `node_to_debruijn`; a `Value::Entity`/`Tuple` recurses into
    /// its children; a scalar has no vars; any other carrier fails loudly.
    fn close_value_head_debruijn(
        &mut self,
        head: crate::eval::value::Value,
        vars: &[VarId],
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        match head {
            Value::Term(t) => Value::Term(self.term_to_debruijn(t, vars)),
            Value::Node(occ) => Value::Node(node_occurrence::node_to_debruijn(self, &occ, vars)),
            Value::Entity { functor, pos, named } => {
                let pos: Vec<Value> = pos
                    .iter()
                    .map(|c| self.close_value_head_debruijn(c.clone(), vars))
                    .collect();
                let named: Vec<(Symbol, Value)> = named
                    .iter()
                    .map(|(s, c)| (*s, self.close_value_head_debruijn(c.clone(), vars)))
                    .collect();
                Value::Entity { functor, pos: std::rc::Rc::from(pos), named: std::rc::Rc::from(named) }
            }
            Value::Tuple { pos, named } => {
                let pos: Vec<Value> = pos
                    .iter()
                    .map(|c| self.close_value_head_debruijn(c.clone(), vars))
                    .collect();
                let named: Vec<(Symbol, Value)> = named
                    .iter()
                    .map(|(s, c)| (*s, self.close_value_head_debruijn(c.clone(), vars)))
                    .collect();
                Value::Tuple { pos: std::rc::Rc::from(pos), named: std::rc::Rc::from(named) }
            }
            // Scalars have no vars to close.
            h @ (Value::Int(_) | Value::BigInt(_) | Value::Float(_) | Value::Bool(_)
            | Value::Str(_) | Value::Unit) => h,
            // A bare value-level var or a runtime carrier is not a stored
            // rule-head shape — fail loudly rather than leave a var unclosed.
            h => {
                debug_assert!(
                    false,
                    "WI-373: unexpected value rule-head carrier in De Bruijn close: {}",
                    h.type_name(),
                );
                h
            }
        }
    }

    /// WI-246/WI-372 finalize: the occurrence body is supplied directly (a term
    /// body is materialized first via [`Self::term_body_to_nodes`]). Closes head
    /// + occurrence body to the shared De Bruijn form against `vars` (collected
    /// by the caller from head + occurrences, in first-occurrence order), inserts
    /// via `assert_rule_nodes`, and records arity / shared_arity / globals. The
    /// single rule-DeBruijn-closure path (`assert_rule_debruijn_with_nodes` and
    /// its shared-frame twin both land here).
    #[allow(clippy::too_many_arguments)]
    fn finalize_rule_debruijn_nodes(
        &mut self,
        head: impl Into<crate::eval::value::Value>,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        vars: Vec<VarId>,
        shared_arity: u32,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        let head = head.into();
        let arity = vars.len() as u32;
        // Close head + occurrence body to De Bruijn against the shared `vars`
        // (Global → DeBruijn, including vars inside any TermId pattern/param
        // fields the occurrence carries); ground facts (`vars` empty) keep both
        // as-is. The head close is carrier-agnostic (`close_value_head_debruijn`),
        // mirroring the body's `node_to_debruijn`.
        let (db_head, db_nodes) = if vars.is_empty() {
            (head, body_nodes)
        } else {
            let new_head = self.close_value_head_debruijn(head, &vars);
            let mut out = Vec::with_capacity(body_nodes.len());
            for n in &body_nodes {
                out.push(node_occurrence::node_to_debruijn(self, n, &vars));
            }
            (new_head, out)
        };
        let rule_id = self.assert_rule_nodes(db_head, db_nodes, sort, domain, meta);
        let entry = &mut self.rules[rule_id.index()];
        entry.arity = arity;
        entry.shared_arity = shared_arity;
        entry.globals = vars;
        rule_id
    }

    /// Pre-DeBruijn Global VarIds for this rule, indexed by their
    /// assigned DeBruijn number. Empty for ground facts. Used by
    /// structured-proof step synthesis (proposal 031) to align step
    /// rule variables with the parent's frame.
    pub fn rule_globals(&self, id: RuleId) -> &[VarId] {
        &self.rules[id.index()].globals
    }

    /// Resolve a qualified rule name to the first matching `RuleId`.
    /// Convenience for the common pattern of looking up a rule's
    /// metadata (globals, shared_arity, ...) by name. For labeled
    /// multi-head rules see [`Self::rule_ids_by_qn`] — they have
    /// multiple rids sharing one label.
    pub fn rule_id_by_qn(&self, qn: &str) -> Option<RuleId> {
        let sym = self.try_resolve_symbol(qn)?;
        if let Some(ids) = self.rules_by_label.get(&sym) {
            if let Some(&rid) = ids.first() {
                return Some(rid);
            }
        }
        self.rules_by_functor(sym).first().copied()
    }

    /// All rule ids that resolve to `qn` — label-first, then
    /// rules_by_functor fallback. Labeled multi-head rules
    /// (`rule X: H1, H2 :- B`) desugar at load time into N rules
    /// sharing label X; `using X` fans out over this list so each
    /// head contributes its own lifted implication clause. For
    /// unlabeled `qn` the returned ids are the rules whose head's
    /// functor symbol resolves to `qn` (SLD lookup semantics).
    pub fn rule_ids_by_qn(&self, qn: &str) -> Vec<RuleId> {
        let Some(sym) = self.try_resolve_symbol(qn) else { return Vec::new() };
        if let Some(ids) = self.rules_by_label.get(&sym) {
            if !ids.is_empty() {
                return ids.clone();
            }
        }
        self.rules_by_functor(sym)
    }

    /// Citation handle for labeled rules. `None` for unlabeled rules
    /// (those resolve via `rules_by_functor` on the head).
    pub fn rule_label(&self, id: RuleId) -> Option<Symbol> {
        self.rules[id.index()].label
    }

    /// Tag an already-asserted rule with a citation label so
    /// `rule_id_by_qn(label_qn)` resolves it even when the head's
    /// functor differs from the label (post-proposal-032 unified
    /// head-as-conclusion encoding). Idempotent re-tagging with the
    /// same label is allowed; a different label is a programming bug
    /// and panics.
    pub fn set_rule_label(&mut self, id: RuleId, label: Symbol) {
        let entry = &mut self.rules[id.index()];
        match entry.label {
            Some(existing) if existing == label => return,
            Some(existing) => panic!(
                "rule {id:?} already labeled {existing:?}, cannot re-tag as {label:?}"),
            None => entry.label = Some(label),
        }
        self.rules_by_label.entry(label).or_default().push(id);
    }

    /// Assert a rule using a CALLER-PROVIDED Global VarIds list as the DeBruijn
    /// frame (proposal 031), occurrence body supplied directly (WI-372). The
    /// head + occurrences are reindexed against the collected `vars` rather than
    /// recomputed from the rule's own free vars; any Global VarId NOT in
    /// `seed_globals` is appended in first-seen order. Used by
    /// `dispatch_structured` to synthesize step rules in the parent's variable
    /// frame so shared variable names produce identical DeBruijn indices (and
    /// therefore identical `var_<i>` SMT names) across the parent rule and every
    /// step's cited-rule lift. The shared-frame twin of
    /// [`Self::assert_rule_debruijn_with_nodes`]; a term-bodied caller converts
    /// once via [`Self::term_body_to_nodes`].
    pub fn assert_rule_debruijn_with_nodes_in_frame(
        &mut self,
        head: impl Into<crate::eval::value::Value>,
        body_nodes: Vec<Rc<NodeOccurrence>>,
        seed_globals: &[VarId],
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        // `term_to_debruijn` / `node_to_debruijn` map positions in reverse (last
        // entry → DeBruijn 0). Parent's seed must stay at the TAIL so its shared
        // vars retain DeBruijn 0..seed_len-1 (matching the parent's own
        // assignment); step-introduced vars are prepended. Vars are collected
        // from head + occurrences in the SAME first-occurrence order as
        // `assert_rule_debruijn_with_nodes` (so frame alignment is preserved).
        let head = head.into();
        let seen: std::collections::HashSet<u32> =
            seed_globals.iter().map(|v| v.raw()).collect();
        let mut vars = Vec::new();
        let mut collected = std::collections::HashSet::new();
        self.collect_value_head_vars(&head, &mut vars, &mut collected);
        for n in &body_nodes {
            node_occurrence::collect_occurrence_global_vars_ordered(self, n, &mut vars, &mut collected);
        }
        vars.retain(|v| !seen.contains(&v.raw()));
        vars.extend(seed_globals.iter().copied());

        let shared_arity = seed_globals.len() as u32;
        self.finalize_rule_debruijn_nodes(head, body_nodes, vars, shared_arity, sort, domain, meta)
    }

    /// Number of leading DeBruijn slots that are shared with a parent
    /// rule's frame. Zero for ordinary rules; positive for
    /// step rules synthesized via `assert_rule_debruijn_with_nodes_in_frame`.
    pub fn rule_shared_arity(&self, id: RuleId) -> u32 {
        self.rules[id.index()].shared_arity
    }

    /// Convert a single term: replace Global(vid) with DeBruijn(index).
    /// Index is `var_order.len() - 1 - position_in_var_order`.
    fn term_to_debruijn(&mut self, term: TermId, var_order: &[VarId]) -> TermId {
        match self.terms.get(term).clone() {
            Term::Var(Var::Global(vid)) => {
                if let Some(pos) = var_order.iter().position(|v| *v == vid) {
                    let idx = (var_order.len() - 1 - pos) as u32;
                    self.alloc(Term::Var(Var::DeBruijn(idx)))
                } else {
                    term // not in var_order, keep as Global
                }
            }
            Term::Var(Var::DeBruijn(_)) => term,
            Term::Fn { .. } => self.map_fn_children(term, |kb, id| kb.term_to_debruijn(id, var_order)),
            _ => term,
        }
    }

    /// Open a de Bruijn term: replace DeBruijn(i) with Global(fresh_vars[i]).
    /// `fresh_vars`: array of fresh VarIds, indexed by de Bruijn index.
    pub fn term_from_debruijn(&mut self, term: TermId, fresh_vars: &[VarId]) -> TermId {
        match self.terms.get(term).clone() {
            Term::Var(Var::DeBruijn(idx)) => {
                if let Some(&vid) = fresh_vars.get(idx as usize) {
                    self.alloc(Term::Var(Var::Global(vid)))
                } else {
                    term // index out of range, keep as DeBruijn
                }
            }
            Term::Var(Var::Global(_)) => term,
            Term::Fn { .. } => self.map_fn_children(term, |kb, id| kb.term_from_debruijn(id, fresh_vars)),
            _ => term,
        }
    }

    /// Get the arity (number of de Bruijn variables) of a rule.
    pub fn rule_arity(&self, id: RuleId) -> u32 {
        self.rules[id.index()].arity
    }

    // ── Rule classification ─────────────────────────────────────

    /// The canonical equality functor — the head symbol every loaded
    /// equation (`lhs = rhs`) carries. Resolves to `anthill.prelude.Eq.eq`
    /// when the prelude is loaded (the symbol the loader builds equation
    /// heads with — `load.rs`), falling back to a bare `eq` only for
    /// prelude-less KBs (e.g. `simp_rewrite`'s bare-`new()` unit tests).
    ///
    /// `[simp]` firing (`simp_rewrite`) must look up `rules_by_functor` under
    /// *this* symbol, not a freshly-interned bare `eq`: the two differ once
    /// the prelude is loaded, so a bare `intern("eq")` finds none of the
    /// loaded `[simp]` equations (WI-283).
    pub fn eq_functor(&mut self) -> Symbol {
        self.try_resolve_symbol("anthill.prelude.Eq.eq")
            .unwrap_or_else(|| self.intern("eq"))
    }

    /// The canonical unification functor — `anthill.kernel.unify`, the head an
    /// `<=>`-spelled equation carries (proposal 049). The bind-side peer of
    /// [`Self::eq_functor`]: equational rule selection (`apply_eq_rules`, the
    /// typer's `try_fire`) queries/scans under BOTH so a migrated `<=>` equation
    /// and a legacy `=` one are both found while WI-526's `=`→`<=>` relabel is
    /// in flight. Falls back to a bare `unify` only for kernel-less unit KBs.
    pub fn unify_functor(&mut self) -> Symbol {
        self.try_resolve_symbol("anthill.kernel.unify")
            .unwrap_or_else(|| self.intern("unify"))
    }

    /// Check if a rule is an equation: head functor is "eq" or "unify" (the
    /// `<=>` head, proposal 049) with 2 positional args and an empty body. The
    /// classification is **type-independent** — purely the head shape — so it
    /// recognizes a migrated `<=>` equation identically to a legacy `=` one.
    pub fn is_equation(&self, id: RuleId) -> bool {
        let entry = &self.rules[id.index()];
        if !entry.body_nodes.is_empty() || entry.retracted {
            return false;
        }
        // WI-348: the resolver's candidate triage (`resolve.rs` eq/non-eq split)
        // calls this on EVERY matched candidate, so a value-fact head — a
        // `Modify[c]`-effect `OperationInfo`, an entity `FieldInfo`, a
        // value-in-type fact — reaches here and must NOT hit the term-only
        // `rule_head` reader (which panics on a `Value::Entity`/`Value::Node`).
        // Read the head functor + positional arity carrier-agnostically via
        // `TermView`: behaviour-identical for the universal `Value::Term(Fn)` head
        // (same functor symbol, `pos_arity == pos_args.len()`), and a value fact —
        // never `eq`-headed — falls through to `false` as it always should.
        match term_view::TermView::head(&entry.head, self) {
            term_view::ViewHead::Functor { functor: Some(functor), pos_arity, .. } => {
                let name = self.symbols.name(functor);
                (name == "eq" || name == "unify") && pos_arity == 2
            }
            _ => false,
        }
    }

    /// Instantiate a rule's body with fresh variables, incorporating bindings
    /// from a discrimination tree match.
    ///
    /// The discrim tree's `tree_subst` has a mix of entries:
    /// - **Query vars** → rule-head subterms (concrete values or `Var(rule_vid)`)
    /// - **Rule vars** → concrete query subterms (when query had concrete values)
    ///
    /// This method:
    /// 1. Builds a rename map: for each rule var, use concrete value from
    ///    tree_subst if available, otherwise create a fresh var
    /// 2. Applies rename to rule body → `fresh_body`
    /// 3. Builds `answer_links` mapping query vars to fresh vars (or concrete
    ///    values) based on tree_subst entries
    ///
    /// Returns `(fresh_nodes, answer_links)`: the opened, head-match-renamed
    /// occurrence body (pushed by the resolver as `Value::Node` goals) and
    /// `answer_links` mapping query variables to their fresh counterparts (or
    /// concrete values).
    pub fn with_fresh_vars(
        &mut self,
        id: RuleId,
        tree_subst: &subst::Substitution,
    ) -> (Vec<Rc<NodeOccurrence>>, subst::Substitution) {
        let arity = self.rules[id.index()].arity;
        // WI-373 gap 3 (delivered): a query var matched against a position
        // INSIDE a value rule head now threads a nested `VarPath` and
        // `extract_value_at_path` descends into the head's `Value::Node` child
        // (the discrim binding-extraction), so the head match enters
        // `tree_subst` carrier-faithfully — no longer an empty/unconstrained
        // answer. The arity > 0 path below never reads the head term (the
        // match is fully encoded in `tree_subst`), so a value rule head no
        // longer needs the term-only `rule_head` reader here. Only the
        // arity == 0 legacy path reads it (for the head's Global vars) — it
        // takes `rule_head` locally, and a value head there stays the LOUD
        // guard (a ground value-headed rule has no head vars to collect; an
        // arity-0 value rule with head vars is WI-342-P3 / gap 1 territory).
        // WI-246: the rule's occurrence body — opened + head-match-renamed, then
        // pushed by the resolver as `Value::Node` goals (and driving the
        // caller-var delay pre-check). The term body (`RuleEntry.body`) is no
        // longer opened/renamed here — it is on no resolution path.
        let body_nodes = self.rules[id.index()].body_nodes.clone();

        // WI-246: matching a `Value::Node` goal binds head/rule vars to
        // `Value::Node` subparts of the goal. The De Bruijn / rename / answer-
        // link logic below reads `tree_subst` term-only (`iter_terms` /
        // narrowing to `Value::Term`), which would silently DROP those bindings —
        // losing the head-match constraint and letting the rule body run
        // unconstrained (exponential over-exploration). Reify each
        // `Value::Node` binding to a hash-consed term first. Fast-path: term
        // goals produce no `Value::Node` binding, so pass `tree_subst` through
        // untouched (no rebuild, and preserves any parent chain).
        let normalized;
        let tree_subst = if tree_subst
            .iter()
            .any(|(_, v)| matches!(v, crate::eval::value::Value::Node(_)))
        {
            let entries: Vec<(VarId, crate::eval::value::Value)> =
                tree_subst.iter().map(|(v, val)| (*v, val.clone())).collect();
            let mut norm = subst::Substitution::new();
            for (vid, val) in entries {
                match val {
                    crate::eval::value::Value::Node(occ) => {
                        let t = node_occurrence::occurrence_to_term(self, &occ);
                        norm.bind(self, vid, t);
                    }
                    crate::eval::value::Value::Term(t) => norm.bind(self, vid, t),
                    other => norm.bind_value(self, vid, other),
                }
            }
            normalized = norm;
            &normalized
        } else {
            tree_subst
        };

        if arity > 0 {
            // De Bruijn path: allocate N fresh vars, open DeBruijn to Global
            let name_sym = self.intern("_");
            let fresh_vars: Vec<VarId> = (0..arity)
                .map(|_| self.fresh_var(name_sym))
                .collect();

            // Build answer_links (query var → fresh var) and body_rename
            // (fresh var → concrete value from head match).
            //
            // tree_subst contains two kinds of entries:
            // 1. Synthetic VarId(u32::MAX - n): DeBruijn var n matched a
            //    concrete query value. These are substituted directly into
            //    the body via body_rename. NOT added to answer_links — the
            //    fresh var is eliminated from the body, so adding it to the
            //    caller's substitution via bind_compressed would be dead
            //    work (O(n²) scan for nothing).
            // 2. Query VarId: query var matched a subterm of the rule head.
            //    Open any DeBruijn vars in the value to their fresh globals.
            let mut answer_links = subst::Substitution::new();
            let mut body_rename = subst::Substitution::new();
            // Walk only Value::Term bindings — this code path uses TermIds
            // for DeBruijn rename + caller-var linkage. Non-Term bindings
            // from external streams flow through a different path.
            for (ts_vid, bound_term) in tree_subst.iter_terms() {
                let is_synthetic = ts_vid.raw() > u32::MAX - arity - 1;
                if is_synthetic {
                    let db_index = (u32::MAX - ts_vid.raw()) as usize;
                    if let Some(&fresh_vid) = fresh_vars.get(db_index) {
                        body_rename.bind(self, fresh_vid, bound_term);
                    }
                } else {
                    let opened = self.term_from_debruijn(bound_term, &fresh_vars);
                    answer_links.bind(self, ts_vid, opened);
                }
            }

            // Occurrence body: De Bruijn-open with the same fresh vars, then
            // apply the head-match rename via `substitute_occurrence` (replace
            // fresh vars with the concrete head-match values; unmatched fresh
            // vars stay as variables, bound during body resolution).
            // WI-298: thread `self` into the opener so it can remap DeBruijn
            // vars inside the remaining TermId-typed Expr fields
            // (Let.type_annotation, Apply.type_args, ApplyWithin.type_args)
            // via `term_from_debruijn`, mirroring `node_to_debruijn` on the
            // closing side.
            let mut opened_nodes: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(body_nodes.len());
            for n in body_nodes.iter() {
                opened_nodes.push(node_occurrence::open_debruijn_node(self, n, &fresh_vars));
            }
            let final_nodes = if body_rename.bindings.is_empty() {
                opened_nodes
            } else {
                let mut out = Vec::with_capacity(opened_nodes.len());
                for n in &opened_nodes {
                    out.push(node_occurrence::substitute_occurrence(self, n, &body_rename));
                }
                out
            };

            (final_nodes, answer_links)
        } else {
            // Legacy path: Global vars (ground facts or rules not yet converted).
            // WI-246: collect rule vars from the head (a hash-consed term) + the
            // OCCURRENCE body. Legacy bodies use Global vars, parallel to
            // `body_nodes`, so no term body is read here. `rule_head` is the LOUD
            // guard for a value head reaching this arity-0 path (a ground value
            // fact has no head vars; an arity-0 value rule with head vars is
            // gap 1 / WI-342-P3 territory) — the arity > 0 path above no longer
            // reads it, so value rule heads with vars resolve there unguarded.
            let head = self.rule_head(id);
            let mut all_vars = Vec::new();
            let mut seen = std::collections::HashSet::new();
            self.collect_vars_rec(head, &mut all_vars, &mut seen);
            for n in &body_nodes {
                node_occurrence::collect_occurrence_global_vars(n, &mut all_vars, &mut seen);
            }

            let mut rename = subst::Substitution::new();
            for vid in &all_vars {
                // Term-narrow: a non-`Term` carrier here would need De Bruijn
                // opening over an occurrence (WI-348 Phase C) — until then a
                // Node binding falls through to a fresh var, as before.
                if let Some(crate::eval::value::Value::Term(bound)) =
                    tree_subst.resolve_as_value(*vid)
                {
                    let bound = *bound;
                    if !matches!(self.terms.get(bound), Term::Var(_)) {
                        rename.bind(self, *vid, bound);
                        continue;
                    }
                }
                let fresh = self.fresh_var(vid.name());
                let fresh_term = self.alloc(Term::Var(Var::Global(fresh)));
                rename.bind(self, *vid, fresh_term);
            }

            // Occurrence body: legacy bodies already use Global vars, so just
            // apply the same `rename` via `substitute_occurrence`.
            let mut final_nodes = Vec::with_capacity(body_nodes.len());
            for n in &body_nodes {
                final_nodes.push(node_occurrence::substitute_occurrence(self, n, &rename));
            }

            let mut answer_links = subst::Substitution::new();
            for (ts_vid, bound_term) in tree_subst.iter_terms() {
                if all_vars.contains(&ts_vid) {
                    continue;
                }
                match self.terms.get(bound_term) {
                    Term::Var(Var::Global(rule_vid)) => {
                        let rule_vid = *rule_vid;
                        if let Some(crate::eval::value::Value::Term(renamed)) =
                            rename.resolve_as_value(rule_vid)
                        {
                            answer_links.bind(self, ts_vid, *renamed);
                        }
                    }
                    _ => {
                        let renamed_term = self.apply_subst(bound_term, &rename);
                        answer_links.bind(self, ts_vid, renamed_term);
                    }
                }
            }

            (final_nodes, answer_links)
        }
    }

    // ── Helpers ─────────────────────────────────────────────────

    /// Convenience: allocate a nullary functor term (name with no args).
    /// WI-511: routes through [`Self::alloc`], so a constructor symbol
    /// canonicalizes to `Ref(c)` (a sort / non-constructor name stays `Fn`).
    pub fn make_name_term(&mut self, name: &str) -> TermId {
        let sym = self.symbols.intern(name);
        self.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// Look up a qualified name and create a nullary Fn term.
    /// Falls back to intern() if no resolved symbol exists.
    /// Callers should pass qualified names (e.g. "Color.red", not "red").
    pub fn resolve_qualified_name_term(&mut self, name: &str) -> TermId {
        let sym = if let Some(&found) = self.symbols.by_qualified_name.get(name) {
            found
        } else {
            self.symbols.intern(name)
        };
        self.terms.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// Look up a resolved symbol by qualified name or short name.
    ///
    /// Panics if no resolved symbol is found — all functor names must be
    /// pre-defined in register_prelude() or scan_definitions().
    pub fn resolve_symbol(&self, name: &str) -> Symbol {
        if let Some(found) = self.try_resolve_symbol(name) {
            return found;
        }
        panic!(
            "resolve_symbol: '{}' is not a resolved symbol. \
             Define it in register_prelude() or ensure it is scanned.",
            name
        );
    }

    /// Look up an already-interned symbol by its exact name without
    /// allocating a new one. Unlike `try_resolve_symbol`, this matches
    /// the raw intern key (e.g. a bare op short name like `lt`), not a
    /// qualified name. Returns `None` when the name was never interned.
    /// WI-240 — used by the eval's dispatch table lookup to recover the
    /// short-name symbol `build_sort_ops_table` keyed its entries by.
    pub fn lookup_symbol(&self, name: &str) -> Option<Symbol> {
        self.symbols.lookup(name)
    }

    /// Look up a resolved symbol by qualified name.
    pub fn try_resolve_symbol(&self, name: &str) -> Option<Symbol> {
        self.symbols.by_qualified_name.get(name).copied()
    }

    /// Resolve a name using scope-aware resolution from _global scope.
    /// Tries qualified name first, then scope-aware parent chain.
    pub fn resolve_name_in_global(&mut self, name: &str) -> Option<Symbol> {
        if let Some(&sym) = self.symbols.by_qualified_name.get(name) {
            return Some(sym);
        }
        let global = self.make_name_term("_global");
        match self.symbols.resolve_in_scope(name, global.raw()) {
            crate::intern::ResolveResult::Found(s) => Some(s),
            // WI-040 / WI-521: the reserved kernel vocab and the implicit prelude
            // resolve via the same lowest-precedence fallback the loader uses, so a
            // bare reflection name (`OperationInfo`, …) or prelude name still
            // resolves here (e.g. the reflect bridge's `SortQuery`) after the
            // `_global` imports were removed.
            _ => crate::kb::load::implicit_qualified(name)
                .and_then(|qn| self.symbols.by_qualified_name.get(qn).copied()),
        }
    }

    /// Check if a qualified name has a defined symbol in the symbol table.
    pub fn has_qualified_name(&self, name: &str) -> bool {
        self.symbols.by_qualified_name.contains_key(name)
    }

    /// Resolve a qualified name and return its short name (if defined).
    pub fn qualified_short_name(&self, name: &str) -> Option<&str> {
        self.symbols.by_qualified_name.get(name).map(|&sym| self.symbols.name(sym))
    }

    /// Allocate a nullary functor term from an already-interned symbol.
    /// WI-511: routes through [`Self::alloc`], so a constructor symbol
    /// canonicalizes to `Ref(c)` (a sort / non-constructor name stays `Fn`).
    pub fn make_name_term_from_sym(&mut self, sym: Symbol) -> TermId {
        self.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// Allocate an entity `Term::Fn`, canonicalizing its named args to the
    /// functor's declared field order via [`Self::sort_named_canonical`]. This
    /// is the single funnel for Rust-side entity-term construction (WI-299):
    /// the discrimination matcher (`discrim.rs`) descends named keys
    /// *positionally* and the loader canonicalizes loaded patterns/facts to
    /// declared field order (`load.rs` via `entity_field_names`), so a built
    /// term MUST use that same order or it silently matches zero solutions.
    /// Builders route through here instead of sorting named args ad-hoc by
    /// `Symbol::index()` (interning order), which only *coincidentally* equals
    /// declared order and would break under any change to interning order, with
    /// no error. `pos_args` pass through unchanged (positional order is already
    /// significant). When the functor has no registered field list,
    /// `sort_named_canonical` falls back to interning order — preserving the
    /// prior behavior for anonymous shapes.
    pub fn make_entity_term(
        &mut self,
        functor: Symbol,
        pos_args: SmallVec<[TermId; 4]>,
        mut named_args: SmallVec<[(Symbol, TermId); 2]>,
    ) -> TermId {
        self.sort_named_canonical(functor, &mut named_args);
        self.alloc(Term::Fn { functor, pos_args, named_args })
    }

    // ── List construction ────────────────────────────────────────

    /// Build a cons-list term from a slice of TermIds.
    pub fn build_list(&mut self, items: &[TermId]) -> TermId {
        let nil_sym = self.resolve_symbol("anthill.prelude.List.nil");
        let cons_sym = self.resolve_symbol("anthill.prelude.List.cons");
        let head_sym = self.intern("head");
        let tail_sym = self.intern("tail");

        let mut list = self.alloc(Term::Fn {
            functor: nil_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        for &item in items.iter().rev() {
            let mut args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            args.push((head_sym, item));
            args.push((tail_sym, list));
            list = self.make_entity_term(cons_sym, SmallVec::new(), args);
        }
        list
    }

    // ── Type term constructors (anthill.prelude.Type entities) ───

    /// sort_ref(name: <sym>) — reference to a named sort.
    pub fn make_sort_ref(&mut self, sort_sym: Symbol) -> TermId {
        // WI-361 producer flip: a bare sort is the term `Ref(S)` itself — no
        // `sort_ref(name: Ref(S))` wrapper. The sort symbol IS the functor for
        // discrimination (`rules_by_functor`, discrim top-edge); dual-form readers
        // (`extract_sort_ref_sym` / `type_head`) still recognize the deep
        // `sort_ref` shape for any residual/reflect terms.
        self.alloc(Term::Ref(sort_sym))
    }

    // ── WI-342: Value-carried (occurrence) type builders ───────────────
    //
    // Peers of the `make_*` `TermId` builders above, producing the
    // `Value`-carried form (`Rc<NodeOccurrence>` with `NodeKind::Type` /
    // `NodeKind::EffectExpr`) required once a subtree carries a real `denoted`
    // occurrence (the carrier rule, design doc §2). These do NOT allocate in
    // the `TermStore` — they wrap occurrences — and are NOT yet called from the
    // live loader (dual-path; the `TermId` builders stay the live path until
    // P3 routes `unify_types` onto `TermView`). Ground children ride in
    // `TypeChild::Ground(TermId)`; only the `denoted` spine is occurrence-linked.

    /// `denoted(value: NodeOccurrence)` carried as a Type occurrence
    /// (`TypeNode::Denoted`). `value` is the carried source content — for
    /// `Modify[c]` an `Expr::Ref(c)` occurrence (see [`Self::make_denoted_occ_ref`]).
    /// The SOLE `denoted` builder: every production value-in-type rides as this
    /// `Value::Node` occurrence (WI-366 retired the ground `TermId` `denoted`).
    pub fn make_denoted_occ(
        &self,
        value: Rc<NodeOccurrence>,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_type(node_occurrence::TypeNode::Denoted { value }, span, owner)
    }

    /// Convenience: `denoted(value: Ref(sym))` carried as an occurrence — the
    /// occurrence-form peer of `make_denoted(alloc(Term::Ref(sym)))`, which is
    /// exactly how the loader lowers a value-in-type today (load.rs:5244).
    pub fn make_denoted_occ_ref(
        &self,
        sym: Symbol,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        let value = NodeOccurrence::new_expr(node_occurrence::Expr::Ref(sym), span, owner);
        self.make_denoted_occ(value, span, owner)
    }

    /// `parameterized(base, bindings)` carried as a Type occurrence.
    /// Occurrence peer of [`Self::make_parameterized_type`].
    pub fn make_parameterized_occ(
        &self,
        base: node_occurrence::TypeChild,
        bindings: Vec<(Symbol, node_occurrence::TypeChild)>,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_type(
            node_occurrence::TypeNode::Parameterized { base, bindings },
            span,
            owner,
        )
    }

    /// `named_tuple(fields)` carried as a Type occurrence (WI-342). Occurrence
    /// peer of [`Self::make_named_tuple_type`]; minted when a tuple field's type
    /// is `denoted`-bearing. WI-361: the `(name, type)` children are assembled into
    /// the `Value`-carried `List[NamedTupleElement]` the carrier stores (mirroring the term
    /// form), so the field-type poison rides as `Value::Node` while ground field
    /// types stay `Value::Term`.
    pub fn make_named_tuple_occ(
        &mut self,
        fields: Vec<(Symbol, node_occurrence::TypeChild)>,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        let fields_value = self.build_named_tuple_fields_value(fields);
        NodeOccurrence::new_type(
            node_occurrence::TypeNode::NamedTuple { fields: fields_value },
            span,
            owner,
        )
    }

    /// WI-361: assemble a `named_tuple`'s `(name, type)` children into the
    /// `Value`-carried `List[NamedTupleElement]` the [`node_occurrence::TypeNode::NamedTuple`]
    /// carrier stores — the same shape [`Self::make_named_tuple_type`] builds as a
    /// hash-consed term, but in the `Value` world so a poisoned (`Value::Node`) field
    /// type rides as-is and a ground one stays `Value::Term` (no lift). `cons` cells
    /// and `NamedTupleElement` records are `Value::Entity`s ordered by
    /// [`Self::sort_named_canonical`], matching the term form's discrim/eq key so the
    /// two carriers compare cross-carrier.
    fn build_named_tuple_fields_value(
        &mut self,
        fields: Vec<(Symbol, node_occurrence::TypeChild)>,
    ) -> crate::eval::value::Value {
        use crate::eval::value::Value;
        use node_occurrence::TypeChild;
        let element_sym = self.resolve_symbol("anthill.prelude.NamedTupleElement");
        let name_key = self.intern("name");
        let type_key = self.intern("type");

        let mut elems: Vec<Value> = Vec::with_capacity(fields.len());
        for (field_name, child) in fields {
            let type_value = match child {
                TypeChild::Ground(t) => Value::Term(t),
                TypeChild::Node(o) => Value::Node(o),
            };
            let name_ref = Value::Term(self.alloc(Term::Ref(field_name)));
            let mut named = vec![(name_key, name_ref), (type_key, type_value)];
            self.sort_named_canonical(element_sym, &mut named);
            elems.push(Value::Entity {
                functor: element_sym,
                pos: Rc::from(Vec::new()),
                named: Rc::from(named),
            });
        }
        // The `cons`/`nil` spine reuses the shared `Value`-list builder (its
        // `[head, tail]` order is canonical, matching `sort_named_canonical`).
        crate::kb::load::build_value_list(self, elems)
    }

    /// `arrow(param, result, effects)` carried as a Type occurrence.
    /// Occurrence peer of [`Self::make_arrow_type`].
    pub fn make_arrow_occ(
        &self,
        param: node_occurrence::TypeChild,
        result: node_occurrence::TypeChild,
        effects: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_type(
            node_occurrence::TypeNode::Arrow { param, result, effects },
            span,
            owner,
        )
    }

    /// `effects_rows(effects_expr: EffectExpression)` carried as a Type
    /// occurrence. Occurrence peer of [`Self::make_effects_rows_type`].
    pub fn make_effects_rows_occ(
        &self,
        effects_expr: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_type(
            node_occurrence::TypeNode::EffectsRows { effects_expr },
            span,
            owner,
        )
    }

    /// EffectExpression `present(label)` carried as an occurrence.
    pub fn make_present_occ(
        &self,
        label: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(
            node_occurrence::EffectExprNode::Present { label },
            span,
            owner,
        )
    }

    /// EffectExpression `absent(label)` carried as an occurrence.
    pub fn make_absent_occ(
        &self,
        label: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(
            node_occurrence::EffectExprNode::Absent { label },
            span,
            owner,
        )
    }

    /// EffectExpression `merge(left, right)` carried as an occurrence.
    pub fn make_merge_occ(
        &self,
        left: node_occurrence::TypeChild,
        right: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(
            node_occurrence::EffectExprNode::Merge { left, right },
            span,
            owner,
        )
    }

    /// EffectExpression `open(tail)` carried as an occurrence.
    pub fn make_open_occ(
        &self,
        tail: node_occurrence::TypeChild,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(
            node_occurrence::EffectExprNode::Open { tail },
            span,
            owner,
        )
    }

    /// EffectExpression `empty_row` carried as an occurrence.
    pub fn make_empty_row_occ(
        &self,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_effect_expr(node_occurrence::EffectExprNode::EmptyRow, span, owner)
    }

    /// Convenience: sort_ref from a name string (resolves or interns the name).
    pub fn make_sort_ref_by_name(&mut self, name: &str) -> TermId {
        let sym = if let Some(s) = self.try_resolve_symbol(name) { s } else { self.intern(name) };
        self.make_sort_ref(sym)
    }

    /// parameterized(base: <type>, bindings: List[TypeBinding]).
    pub fn make_parameterized_type(&mut self, base: TermId, bindings: &[(Symbol, TermId)]) -> TermId {
        // WI-361 producer flip: term-backed — the base sort IS the functor and the
        // bindings ARE the named args (`List[T = Int]` = `Fn{List, named:[(T, …)]}`),
        // with no `parameterized(base, bindings: List[TypeBinding])` wrapper. The base
        // sort is the discriminating functor (native `rules_by_functor`/discrim
        // selectivity, produced directly). `base` is a sort reference `Ref(S)` (post
        // make_sort_ref flip), read via the reader.
        let base_sym = crate::kb::typing::extract_sort_ref_sym(self, &crate::kb::term_view::TermIdView(base))
            .expect("make_parameterized_type: base must be a sort reference");
        if bindings.is_empty() {
            // A parameterized type with no bindings IS the bare sort (`List[]` ≡
            // `List`) — emit `Ref(S)`, never a degenerate no-arg `Fn{S}` (which
            // `type_head` classifies as `Error`, losing the base sort). Mirrors the
            // inference's own empty-bindings guard; also covers an over-applied
            // non-parametric sort whose stray bindings were dropped at load.
            return self.alloc(Term::Ref(base_sym));
        }
        let named_args: SmallVec<[(Symbol, TermId); 2]> = bindings.iter().copied().collect();
        self.make_entity_term(base_sym, SmallVec::new(), named_args)
    }

    /// arrow(param: <type>, result: <type>, effects: <effects_rows Type>).
    ///
    /// WI-307 v1a row-substrate: `effects` is the singular
    /// `effects_rows(EffectExpression)` Type — not `List[Type]`. The caller
    /// still passes a flat `&[TermId]` of effect labels for ergonomics; we
    /// canonicalize internally (sort by `type_display_name`, dedup, fold into
    /// a right-associated `merge`-chain ending in `empty_row` for closed
    /// rows or `open(tail)` when a `Var::Global` is present). Mixing concrete
    /// labels and a row-tail `Var::Global` in one list is the documented row
    /// shape: `effects { Modify[c], E }` lowers to
    /// `[Modify[c]-term, Var(E)-term]`
    /// → `merge(present(Modify[c]), open(?E))`.
    ///
    /// At most one `Var::Global` is expected (the row tail). Additional
    /// Var::Global past the first are folded as if they were extra labels —
    /// the canonical form still parses, but row unification will treat them
    /// as duplicate tails (semantically nonsensical, but representable).
    /// Var::DeBruijn and Var::Rigid fall through to the labels arm (per
    /// code-review #6) — their unification semantics aren't row-tail.
    ///
    /// **Bootstrap dependency** (code-review #13) — beyond the
    /// `anthill.prelude.TypeExtractor.Arrow` symbol made_arrow_type
    /// needs, this function now also requires
    /// `anthill.prelude.TypeExtractor.EffectsRows` and the five
    /// `anthill.prelude.EffectExpression.{empty_row, present, absent, open,
    /// merge}` entity symbols. All six are pre-registered by
    /// `kb::load::register_stdlib_scopes` (the same path that registers
    /// `TypeExtractor.Arrow`); a KB constructed without `register_prelude` panics
    /// at the first builder call with a clear `resolve_symbol` message
    /// rather than silently producing malformed terms.
    pub fn make_arrow_type(&mut self, param: TermId, result: TermId, effects: &[TermId]) -> TermId {
        let effects_rows_term = self.build_canonical_effects_rows(effects);
        self.make_arrow_from_effects_rows(param, result, effects_rows_term)
    }

    /// Build `arrow(param, result, effects)` from an ALREADY-canonical
    /// `effects_rows(EffectExpression)` Type — the `effects` child is a row, not a
    /// raw label list, so it must NOT be re-canonicalized.
    /// [`Self::make_arrow_type`] canonicalizes a raw label list, then calls this.
    pub(crate) fn make_arrow_from_effects_rows(
        &mut self,
        param: TermId,
        result: TermId,
        effects_rows: TermId,
    ) -> TermId {
        let arrow_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.Arrow");
        let param_key = self.intern("param");
        let result_key = self.intern("result");
        let effects_key = self.intern("effects");

        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((effects_key, effects_rows));
        named_args.push((param_key, param));
        named_args.push((result_key, result));
        self.make_entity_term(arrow_sym, SmallVec::new(), named_args)
    }

    // ── EffectExpression builders (WI-307 v1a) ──────────────────────────

    /// EffectExpression `empty_row` — the closed empty row `{}` (pure).
    pub fn make_effect_expression_empty_row(&mut self) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.empty_row");
        self.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// WI-337: bootstrap-safe variant of the
    /// `make_effects_rows_type(make_effect_expression_empty_row())` pair.
    /// Returns `None` when the EffectExpression / `effects_rows` symbols
    /// are not yet registered (i.e. before [`load::register_prelude`] has
    /// run). The panicking variants are convenient for the typer hot
    /// path — `make_arrow_type` and friends require the symbols already
    /// — but `arrow_compatible` / `unify_arrow` can be reached at
    /// bootstrap time on a malformed legacy arrow term that has only one
    /// of `param`/`result`/`effects` populated, in which case the typer
    /// should degrade gracefully rather than crash. The caller decides
    /// the soundness-preserving fallback (typically "reject the missing
    /// side" so the check returns false without claiming compatibility).
    pub fn try_make_empty_effects_rows(&mut self) -> Option<TermId> {
        let empty_sym = self.try_resolve_symbol(
            "anthill.prelude.EffectExpression.empty_row",
        )?;
        let rows_sym = self.try_resolve_symbol(
            "anthill.prelude.TypeExtractor.EffectsRows",
        )?;
        let empty = self.alloc(Term::Fn {
            functor: empty_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let expr_key = self.intern("effects_expr");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((expr_key, empty));
        Some(self.make_entity_term(rows_sym, SmallVec::new(), named_args))
    }

    /// EffectExpression `present(label: Type)` — a single present effect.
    pub fn make_effect_expression_present(&mut self, label: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.present");
        let label_key = self.intern("label");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((label_key, label));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// EffectExpression `absent(label: Type)` — `-e` absence guarantee.
    /// Unused in v1a (presence-only); reserved for v1b's `lacks` constraints.
    pub fn make_effect_expression_absent(&mut self, label: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.absent");
        let label_key = self.intern("label");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((label_key, label));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// EffectExpression `open(tail: Type)` — a row variable tail, carrying
    /// the tail `Type` (a `Term::Var` for an unbound row, or a resolved row
    /// type after substitution).
    pub fn make_effect_expression_open(&mut self, tail: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.open");
        let tail_key = self.intern("tail");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((tail_key, tail));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// EffectExpression `merge(left, right)` — union of two expressions.
    /// The canonical row form right-folds present labels into this:
    /// `merge(present(l₁), merge(present(l₂), …, tail))`.
    pub fn make_effect_expression_merge(&mut self, left: TermId, right: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.EffectExpression.merge");
        let left_key = self.intern("left");
        let right_key = self.intern("right");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((left_key, left));
        named_args.push((right_key, right));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// Wrap an EffectExpression in the `effects_rows(effects_expr: …)` Type
    /// entity — the bridge from EffectExpression to Type position
    /// (WI-320 substrate). Use this when storing a row in any Type-typed
    /// slot (e.g. `arrow.effects`, `EffectsRuntime[Effects = …]`).
    pub fn make_effects_rows_type(&mut self, expr: TermId) -> TermId {
        let sym = self.resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
        let expr_key = self.intern("effects_expr");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((expr_key, expr));
        self.make_entity_term(sym, SmallVec::new(), named_args)
    }

    /// Build a canonical `effects_rows(EffectExpression)` Type from a flat
    /// `&[TermId]` of effect-list elements — the surface representation the
    /// loader and the typer already produce (mixed `Term::Fn` concrete labels
    /// and at most one `Term::Var` row-tail).
    ///
    /// **Canonical form** (so two arrow types with the same effects in
    /// different source order hash-cons to the same TermId):
    ///   - sort labels by `type_display_name` (stable across runs);
    ///   - dedup adjacent identical labels (rows are sets, idempotent);
    ///   - right-fold into `merge(present(l₁), merge(present(l₂), …, tail))`
    ///     where `tail` is `open(?ρ)` if a Var was present, else `empty_row`.
    ///
    /// An empty input list with no tail yields `effects_rows(empty_row)` — the
    /// closed pure row.
    /// WI-441: the row-tail Var a term denotes — the term itself for a bare
    /// `Var::Global` / `Var::Rigid`, the `SortAlias` target Var for a `Ref(S.E)`
    /// (a sort-level row param referenced from an op signature, which lowers as a
    /// Ref). `None` for anything else (a label, a ground type, a `DeBruijn`).
    ///
    /// WI-516: `Var::Rigid` counts as a row tail. An effect-set-valued type param
    /// is rigidified (Skolemized) while an operation body is checked, so a forced/
    /// performed captured effect — a `@ Eff` row whose tail is the op's `Eff`
    /// param — surfaces in the body's inferred effect list as a bare `Var::Rigid`.
    /// Re-canonicalizing that list (here, and at the arrow-occ build site
    /// typing.rs `make_*_occ`) MUST fold it as `open(tail)`, NOT `present(label)`:
    /// a rigid set-valued var is a row VARIABLE, not a single concrete label.
    /// This matches the decompose side (`row_tail_termid` / `effects_rows_to_flat_list`),
    /// which already treat any/bare `Var` as a tail. `Var::DeBruijn` (rule-side,
    /// pre-binder-open; proposal 025 Skolems are minted as Rigid, not DeBruijn)
    /// stays excluded — it never reaches a typed op-signature effect row.
    pub(crate) fn row_tail_var_of(&self, t: TermId) -> Option<TermId> {
        use crate::kb::term::{Term as T, Var as V};
        let is_tail_var = |v: &V| matches!(v, V::Global(_) | V::Rigid(_));
        match self.get_term(t) {
            T::Var(v) if is_tail_var(v) => Some(t),
            T::Ref(sym) => {
                let target = crate::kb::typing::resolve_sort_alias(self, *sym)?;
                match self.get_term(target) {
                    T::Var(v) if is_tail_var(v) => Some(target),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub fn build_canonical_effects_rows(&mut self, effects: &[TermId]) -> TermId {
        // Partition into atoms (`present(label)` / `absent(label)`) and
        // row-tail Var::Global. At most one tail var is expected; if
        // multiple Global vars appear, all-but-the-first are stuffed
        // into the atoms list (canonical form still parses; row
        // unification surfaces the malformed shape).
        //
        // WI-307 code-review #6 / WI-516: `Var::Global` and `Var::Rigid`
        // qualify as row tails (see `row_tail_var_of`). A rigid arises when an
        // effect-set type param is Skolemized during op-body checking; it is a
        // row VARIABLE and folds as `open(tail)`. `Var::DeBruijn` (rule-side,
        // pre-binder-open) stays excluded — it has different unification
        // semantics and never reaches a typed op-signature effect row; it falls
        // through to the atoms arm, where row unification surfaces it as a
        // schema-shape failure rather than a silent mis-classification.
        //
        // WI-327: pre-built `present` / `absent` atoms (e.g. `-E` from
        // surface grammar lowered via `make_effect_expression_absent`)
        // are recognized by their functor symbols and kept as-is. Bare
        // labels are still wrapped in `present(label)`. Mixed input is
        // sorted by display name with the wrapper applied so canonical
        // form is stable regardless of how each atom arrived.
        use crate::kb::term::Term;
        let absent_sym = self.try_resolve_symbol(
            "anthill.prelude.EffectExpression.absent",
        );
        let present_sym = self.try_resolve_symbol(
            "anthill.prelude.EffectExpression.present",
        );
        let mut atoms: Vec<TermId> = Vec::new();
        // WI-441: ALL row-tail Vars are collected — a row UNION (`{ES, EF}`,
        // the lazy combinators' merge row) folds each as its own `open(…)`.
        // (Pre-WI-441 only the first Var became the tail; the rest were
        // stuffed into the atoms list and wrapped `present(var)` — a
        // malformed shape decompose read as a present LABEL.)
        let mut tail_vars: Vec<TermId> = Vec::new();
        for &e in effects {
            // WI-441: a SORT-level row param referenced in a written row lowers
            // as `Ref(S.E)` (it is not a type param of the CURRENT scope) — its
            // `SortAlias` target Var is the row tail every other reader binds.
            let row_var = self.row_tail_var_of(e);
            match self.get_term(e) {
                _ if row_var.is_some() => {
                    let v = row_var.expect("checked is_some");
                    if !tail_vars.contains(&v) {
                        tail_vars.push(v);
                    }
                }
                Term::Fn { functor, .. }
                    if Some(*functor) == absent_sym
                        || Some(*functor) == present_sym =>
                {
                    // Pre-built EffectExpression atom (WI-327 `-E` →
                    // `absent(E)`, or any prior `present(E)` wrapper).
                    // Keep as-is.
                    atoms.push(e);
                }
                _ => {
                    // Bare label — wrap in present().
                    let wrapped = self.make_effect_expression_present(e);
                    atoms.push(wrapped);
                }
            }
        }
        // Canonical ordering: sort by type_display_name, then dedup.
        atoms.sort_by_cached_key(|&t| crate::kb::typing::type_display_name(self, t));
        atoms.dedup();

        // Right-fold: innermost tail first (additional tails as open(…)
        // merges), then merge() walking back through the sorted atom list.
        let mut acc = match tail_vars.first() {
            Some(&tail) => self.make_effect_expression_open(tail),
            None => self.make_effect_expression_empty_row(),
        };
        for &extra_tail in tail_vars.iter().skip(1) {
            let o = self.make_effect_expression_open(extra_tail);
            acc = self.make_effect_expression_merge(o, acc);
        }
        for &atom in atoms.iter().rev() {
            acc = self.make_effect_expression_merge(atom, acc);
        }
        self.make_effects_rows_type(acc)
    }

    /// type_var(name: <sym>) — a type variable for inference.
    pub fn make_type_var(&mut self, name: Symbol) -> TermId {
        let type_var_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.TypeVar");
        let name_key = self.intern("name");
        let name_val = self.alloc(Term::Ref(name));
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((name_key, name_val));
        self.make_entity_term(type_var_sym, SmallVec::new(), named_args)
    }

    /// denoted(value: <term>) — a value-in-type carried faithfully as a hash-consed
    /// term. The term twin of `TypeNode::Denoted` (WI-390 re-introduced this after
    /// WI-366 retired the ground builder), so a `denoted` round-trips through the
    /// term store. `value` is the ground/qualified reference structure; a local-binder
    /// value rides a `Positioned` internal (see [`Self::make_positioned`]).
    pub fn make_denoted(&mut self, value: TermId) -> TermId {
        let denoted_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.Denoted");
        let value_key = self.intern("value");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((value_key, value));
        self.make_entity_term(denoted_sym, SmallVec::new(), named_args)
    }

    /// expr_carried(value: <term>, member: Ref(<sym>)) — the term twin of an
    /// expression-carried type projection `s.T` / `s.Sort` (WI-376). `value` is the
    /// receiver occurrence's term (a ground `Ref(s)` for a param/local receiver);
    /// `member` is the projected type-member name, carried as `Ref(sym)` exactly as
    /// [`Self::make_type_var`] carries its `name`. The type-member sibling of
    /// [`Self::make_denoted`]. (A *compound* receiver — `(expr).T` — would instead
    /// ride a `TypeNode::ExprCarried` Node carrier; that surface does not parse yet.)
    pub fn make_expr_carried(&mut self, value: TermId, member: Symbol) -> TermId {
        let expr_carried_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.ExprCarried");
        let value_key = self.intern("value");
        let member_key = self.intern("member");
        let member_val = self.alloc(Term::Ref(member));
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((value_key, value));
        named_args.push((member_key, member_val));
        self.make_entity_term(expr_carried_sym, SmallVec::new(), named_args)
    }

    /// rigid_type_projection(sort: Ref(<decl>), var: <subject>, member: Ref(<sym>)) —
    /// the TYPE-receiver projection `P.Key` / `MemStore.Key` (WI-428, design §5.3): the
    /// type-keyed sibling of [`Self::make_expr_carried`]. `subject` is the projection's
    /// receiver TERM — `Ref(P)` for a rigid type-parameter, `Ref(S)` for a concrete
    /// sort; `decl_sort` is the sort whose `requires` chain lends the subject its
    /// members (= the subject itself for a concrete-sort subject — the discriminator
    /// the eliminator uses). All three slots are ground, so the projection always
    /// hash-conses (no Node carrier).
    pub fn make_rigid_projection(
        &mut self,
        decl_sort: Symbol,
        subject: TermId,
        member: Symbol,
    ) -> TermId {
        let functor = self.resolve_symbol("anthill.prelude.TypeExtractor.RigidTypeProjection");
        let sort_key = self.intern("sort");
        let var_key = self.intern("var");
        let member_key = self.intern("member");
        let sort_val = self.alloc(Term::Ref(decl_sort));
        let member_val = self.alloc(Term::Ref(member));
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((sort_key, sort_val));
        named_args.push((var_key, subject));
        named_args.push((member_key, member_val));
        self.make_entity_term(functor, SmallVec::new(), named_args)
    }

    /// Occurrence twin of [`Self::make_expr_carried`] for a COMPOUND receiver
    /// (`a.b.T`): the receiver is a field-access `Expr` occurrence (a `DotApply`
    /// chain over the value path) that cannot hash-cons, so the whole projection
    /// rides a [`node_occurrence::TypeNode::ExprCarried`] Node carrier rather than a
    /// ground term. `receiver` is that field-path occurrence; `member` the projected
    /// type-member name, carried as a ground `Ref` child exactly as the term form
    /// does — so `TermView` reads `value` / `member` identically across carriers, and
    /// `extract_type` yields the same `TypeExtractor::ExprCarried`. WI-397.
    pub fn make_expr_carried_occ(
        &mut self,
        receiver: std::rc::Rc<node_occurrence::NodeOccurrence>,
        member: Symbol,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> std::rc::Rc<node_occurrence::NodeOccurrence> {
        let member_ref = self.alloc(Term::Ref(member));
        node_occurrence::NodeOccurrence::new_type(
            node_occurrence::TypeNode::ExprCarried {
                value: node_occurrence::TypeChild::Node(receiver),
                member: node_occurrence::TypeChild::Ground(member_ref),
            },
            span,
            owner,
        )
    }

    /// Positioned(pos, internal) — a local-binder reference (a lambda parameter /
    /// `let`-local, scope-local and not globally unique) carried with its absolute
    /// binding-site identity `pos`, so two distinct locals with the same surface name
    /// don't collide as one hash-consed term. WI-390: `Positioned` is leaf-only (it
    /// wraps a binder leaf, never a compound) and unifies structurally as an ordinary
    /// `Term::Fn`; the type-level alpha-equivalence reading is deferred.
    pub fn make_positioned(&mut self, pos: TermId, internal: TermId) -> TermId {
        let positioned_sym = self.resolve_symbol("anthill.reflect.Positioned");
        let pos_key = self.intern("pos");
        let internal_key = self.intern("internal");
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((pos_key, pos));
        named_args.push((internal_key, internal));
        self.make_entity_term(positioned_sym, SmallVec::new(), named_args)
    }

    /// named_tuple(fields: List[NamedTupleElement]).
    pub fn make_named_tuple_type(&mut self, fields: &[(Symbol, TermId)]) -> TermId {
        let named_tuple_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.NamedTuple");
        let element_sym = self.resolve_symbol("anthill.prelude.NamedTupleElement");
        let fields_key = self.intern("fields");
        let name_key = self.intern("name");
        let type_key = self.intern("type");

        let field_terms: Vec<TermId> = fields.iter().map(|(field_name, field_type)| {
            let name_ref = self.alloc(Term::Ref(*field_name));
            let mut args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            args.push((name_key, name_ref));
            args.push((type_key, *field_type));
            self.make_entity_term(element_sym, SmallVec::new(), args)
        }).collect();

        let fields_list = self.build_list(&field_terms);

        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((fields_key, fields_list));
        self.make_entity_term(named_tuple_sym, SmallVec::new(), named_args)
    }

    /// nothing — bottom type.
    pub fn make_nothing_type(&mut self) -> TermId {
        let nothing_sym = self.resolve_symbol("anthill.prelude.TypeExtractor.Nothing");
        self.alloc(Term::Fn {
            functor: nothing_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    // ── Name-level substitution ──────────────────────────────────

    /// Replace all occurrences of `from` with `to` throughout a term's structure.
    /// Returns a new hash-consed TermId (may be the same if no replacement occurred).
    pub fn subst_term(&mut self, term: TermId, from: TermId, to: TermId) -> TermId {
        if term == from {
            return to;
        }
        self.map_fn_children(term, |kb, id| kb.subst_term(id, from, to))
    }

    /// Apply multiple substitutions (from → to) to a term.
    pub fn subst_term_multi(&mut self, mut term: TermId, bindings: &[(TermId, TermId)]) -> TermId {
        for &(from, to) in bindings {
            term = self.subst_term(term, from, to);
        }
        term
    }

    // ── Entity field registry ──────────────────────────────────

    /// Register the ordered field names for an entity functor.
    pub fn register_entity_fields(&mut self, functor: Symbol, fields: Vec<Symbol>) {
        self.entity_fields.insert(functor, fields);
    }

    /// Look up the ordered field names for an entity functor.
    pub fn entity_field_names(&self, functor: Symbol) -> Option<&[Symbol]> {
        self.entity_fields.get(&functor).map(|v| v.as_slice())
    }

    /// Register entity field types: functor → [(field_name, type)]. WI-342: the
    /// field type is carrier-agnostic — a `denoted`-bearing field type (a
    /// value-in-type / dependent field) rides as `Value::Node`, a ground field
    /// type as `Value::Term`.
    pub fn register_entity_field_types(&mut self, functor: Symbol, fields: Vec<(Symbol, crate::eval::value::Value)>) {
        self.entity_field_types.insert(functor, fields);
    }

    /// Look up the field types for an entity functor (carrier-agnostic `Value`).
    pub fn entity_field_types(&self, functor: Symbol) -> Option<&[(Symbol, crate::eval::value::Value)]> {
        self.entity_field_types.get(&functor).map(|v| v.as_slice())
    }

    /// Iterate all functor symbols that have registered field types.
    pub fn entity_field_type_functors(&self) -> impl Iterator<Item = &Symbol> {
        self.entity_field_types.keys()
    }

    /// Check if a functor symbol is a constructor (entity with a parent sort).
    /// O(1) lookup via pre-built index populated by register_entity_of.
    pub fn is_constructor_symbol(&self, functor: Symbol) -> bool {
        self.constructor_symbols.contains(&functor)
    }

    /// WI-352 — whether `sym` is an operation's reserved `result` binder
    /// (`<op>.result`, proposal 041), by its **symbol kind**. WI-341 first
    /// moved this off a spelling match (`rsplit('.') == "result"`) onto symbol
    /// identity; WI-351 used a `PlaceRole` side-table; WI-352 makes the kind
    /// itself carry the truth, so this is exactly `kind == OpResult`. Keeps
    /// `Cell.new.result` masking (WI-314) unchanged.
    pub(crate) fn is_result_binder(&self, sym: Symbol) -> bool {
        self.kind_of(sym) == Some(crate::intern::SymbolKind::OpResult)
    }

    /// A free-standing entity: declared at namespace level (registered fields)
    /// with no parent sort, so it is not a constructor. A bare reference to one
    /// denotes the entity as a type rather than a construction.
    pub fn is_free_standing_entity(&self, functor: Symbol) -> bool {
        self.entity_field_types(functor).is_some() && !self.is_constructor_symbol(functor)
    }

    // ── Builtin dispatch ────────────────────────────────────────

    /// Register a builtin by its fully-qualified name.
    /// Creates a resolved definition if the name isn't already defined.
    /// Derives the proper scope from the namespace prefix of the qualified name.
    pub fn register_builtin(&mut self, qualified_name: &str, tag: BuiltinTag) {
        let sym = if let Some(&resolved) = self.symbols.by_qualified_name.get(qualified_name) {
            resolved
        } else {
            let short = qualified_name.rsplit('.').next().unwrap_or(qualified_name);
            // Find scope from namespace prefix (e.g. "anthill.reflect.typing" for
            // "anthill.reflect.typing.is_entity_of")
            let ns_sym_opt = if let Some(dot_pos) = qualified_name.rfind('.') {
                let ns_prefix = &qualified_name[..dot_pos];
                self.symbols.by_qualified_name.get(ns_prefix).copied()
            } else {
                None
            };
            let scope_raw = if let Some(ns_sym) = ns_sym_opt {
                self.make_name_term_from_sym(ns_sym).raw()
            } else {
                panic!(
                    "register_builtin: namespace prefix for '{}' not found. \
                     Call register_prelude() first to create the namespace hierarchy.",
                    qualified_name
                )
            };
            self.symbols.define(short, qualified_name, SymbolKind::Operation, scope_raw)
        };
        self.builtins.insert(sym, tag);
    }

    /// Register the standard builtins.
    pub fn register_standard_builtins(&mut self) {
        self.register_builtin("anthill.reflect.nonvar", BuiltinTag::NonVar);
        self.register_builtin("anthill.reflect.ground", BuiltinTag::Ground);
        self.register_builtin("anthill.reflect.qualified_name", BuiltinTag::QualifiedName);
        self.register_builtin("anthill.reflect.short_name", BuiltinTag::ShortName);
        self.register_builtin("anthill.reflect.lookup_symbol", BuiltinTag::LookupSymbol);
        self.register_builtin("anthill.reflect.not", BuiltinTag::Not);
        self.register_builtin("anthill.reflect.typing.is_entity_of", BuiltinTag::IsEntityOf);
        self.register_builtin("anthill.reflect.typing.extract_sort_ref", BuiltinTag::ExtractSort);
        self.register_builtin("anthill.reflect.resolve_sort_instantiation_param", BuiltinTag::ResolveSortInstParam);
        self.register_builtin("anthill.reflect.scope", BuiltinTag::Scope);
        self.register_builtin("anthill.reflect.kind", BuiltinTag::Kind);
        self.register_builtin("anthill.reflect.feed.provenance", BuiltinTag::Provenance);
        self.register_builtin("anthill.reflect.field_access", BuiltinTag::FieldAccess);
        self.register_builtin("anthill.reflect.Expr.ho_apply", BuiltinTag::HoApply);
        // Resolver primitives (proposal 033 / 049)
        self.register_builtin("anthill.kernel.push_choice", BuiltinTag::PushChoice);
        self.register_builtin("anthill.kernel.unify", BuiltinTag::Unify);
        // Arithmetic and comparison
        self.register_builtin("anthill.prelude.Eq.eq", BuiltinTag::Eq);
        self.register_builtin("anthill.prelude.Eq.neq", BuiltinTag::Neq);
        self.register_builtin("anthill.prelude.Ordered.gt", BuiltinTag::Gt);
        self.register_builtin("anthill.prelude.Ordered.lt", BuiltinTag::Lt);
        self.register_builtin("anthill.prelude.Ordered.gte", BuiltinTag::Gte);
        self.register_builtin("anthill.prelude.Ordered.lte", BuiltinTag::Lte);
        self.register_builtin("anthill.prelude.Numeric.add", BuiltinTag::Add);
        self.register_builtin("anthill.prelude.Numeric.sub", BuiltinTag::Sub);
        self.register_builtin("anthill.prelude.Numeric.mul", BuiltinTag::Mul);
        // Conversions
        self.register_builtin("anthill.prelude.BigInt.to_bigint", BuiltinTag::ToBigInt);
        self.register_builtin("anthill.prelude.BigInt.to_int", BuiltinTag::ToInt);

        // Occurrence builtins (stubs — full implementations in future phases)
        self.register_builtin("anthill.reflect.occurrence_term", BuiltinTag::OccurrenceTerm);
        self.register_builtin("anthill.reflect.occurrence_span", BuiltinTag::OccurrenceSpan);
        self.register_builtin("anthill.reflect.occurrence_owner", BuiltinTag::OccurrenceOwner);
        self.register_builtin("anthill.reflect.sub_occurrences", BuiltinTag::SubOccurrences);
        self.register_builtin("anthill.reflect.operation_body", BuiltinTag::OperationBody);
    }

    /// Re-resolve builtins after scan_definitions().
    /// If scan_definitions created a new resolved symbol for a builtin's
    /// qualified name (from .anthill source), remap the builtin to use it.
    pub fn resolve_builtins(&mut self) {
        let old: Vec<(Symbol, BuiltinTag)> = self.builtins.drain().collect();
        for (old_sym, tag) in old {
            let qualified = match self.symbols.get(old_sym) {
                SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                SymbolDef::Unresolved { name } => name.clone(),
            };
            let sym = self.symbols.by_qualified_name.get(&qualified)
                .copied().unwrap_or(old_sym);
            self.builtins.insert(sym, tag);
        }
    }

    /// True iff `sym` is a registered resolver builtin (`anthill.prelude.Eq.eq`,
    /// `Numeric.add`, …). WI-363: a spec op that maps to a builtin is backed by
    /// the host primitive, not an anthill body/rule — so the op-provision check
    /// must treat it as satisfied.
    pub fn is_builtin(&self, sym: Symbol) -> bool {
        self.builtins.contains_key(&sym)
    }

    /// Check if a goal term's functor is a registered builtin.
    /// Returns `Some(tag)` if so, `None` otherwise.
    pub fn get_builtin(&self, goal: TermId) -> Option<BuiltinTag> {
        self.get_builtin_view(&term_view::TermIdView(goal))
    }

    /// `get_builtin` generic over the goal representation — classifies a goal
    /// by the builtin table from the functor read through [`TermView`], so a
    /// `Value::Node` occurrence goal (WI-246) is dispatched without lowering.
    pub fn get_builtin_view<V: term_view::TermView>(&self, goal: &V) -> Option<BuiltinTag> {
        match goal.head(self) {
            term_view::ViewHead::Functor { functor: Some(sym), .. } => {
                self.builtins.get(&sym).copied()
            }
            _ => None,
        }
    }
}

impl Default for KnowledgeBase {
    fn default() -> Self {
        Self::new()
    }
}

impl TermSource for KnowledgeBase {
    fn term(&self, id: TermId) -> &Term {
        self.terms.get(id)
    }
    fn sym_name(&self, sym: Symbol) -> &str {
        self.symbols.name(sym)
    }
    fn qualified_name(&self, sym: Symbol) -> &str {
        self.qualified_name_of(sym)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use term::Literal;
    use smallvec::SmallVec;

    #[test]
    fn assert_and_query_by_sort() {
        let mut kb = KnowledgeBase::new();
        let sort_account = kb.make_name_term("Account");
        let domain = kb.make_name_term("banking");

        let acct1 = {
            let id_sym = kb.intern("account");
            let arg = kb.alloc(Term::Const(Literal::String("A001".into())));
            kb.alloc(Term::Fn {
                functor: id_sym,
                pos_args: SmallVec::from_elem(arg, 1),
                named_args: SmallVec::new(),
            })
        };

        let fid = kb.assert_fact(acct1, sort_account, domain, None);
        let results = kb.by_sort(sort_account);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], fid);
    }

    #[test]
    fn make_entity_term_orders_named_by_declared_field_not_interning() {
        // WI-299: `make_entity_term` must order named args by the functor's
        // DECLARED field order, not by `Symbol::index()` (interning order). We
        // intern the fields in the REVERSE of their declared order so the two
        // orders disagree; an ad-hoc `s.index()` sort would mis-order the term
        // and silently miss the loader-canonicalized pattern in the (positional)
        // discrimination matcher.
        let mut kb = KnowledgeBase::new();

        // Intern `second` BEFORE `first`, so index(second) < index(first) — the
        // OPPOSITE of the declared `[first, second]` order registered below.
        let second = kb.intern("second");
        let first = kb.intern("first");
        assert!(
            second.index() < first.index(),
            "test setup: interning order must invert declared order"
        );

        let functor = kb.intern("Pair");
        kb.register_entity_fields(functor, vec![first, second]);

        let v1 = kb.alloc(Term::Const(Literal::Int(1)));
        let v2 = kb.alloc(Term::Const(Literal::Int(2)));
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named.push((second, v2));
        named.push((first, v1));
        let term = kb.make_entity_term(functor, SmallVec::new(), named);

        match kb.terms.get(term) {
            Term::Fn { named_args, .. } => {
                let order: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
                assert_eq!(
                    order,
                    vec![first, second],
                    "named args must follow declared field order, not interning order"
                );
            }
            other => panic!("expected Term::Fn, got {other:?}"),
        }

        // With NO registered field list, `make_entity_term` falls back to
        // interning order (anonymous shape) — preserving prior behavior.
        let anon = kb.intern("Anon");
        let mut named2: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named2.push((first, v1));
        named2.push((second, v2));
        let anon_term = kb.make_entity_term(anon, SmallVec::new(), named2);
        match kb.terms.get(anon_term) {
            Term::Fn { named_args, .. } => {
                let order: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
                // `second` was interned first, so it sorts first under the fallback.
                assert_eq!(order, vec![second, first]);
            }
            other => panic!("expected Term::Fn, got {other:?}"),
        }
    }

    #[test]
    fn value_fact_node_head_indexes_queries_and_preserves_node_identity() {
        // WI-348 Phase B: a fact whose head carries a `Value::Node` (denoted)
        // is stored, indexed (by_sort / rules_by_functor / discrim), queried back, and
        // — crucially — a variable query binds the SAME occurrence (Node identity
        // preserved through the answer via the carrier-faithful resolve).
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb); // interns Type.denoted etc. for occ_head
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let f_sym = kb.intern("op_with_denoted");
        let c_sym = kb.intern("c");
        let sort = kb.make_name_term("MySort");
        let domain = kb.make_name_term("test");

        // Head: f(denoted(value: Ref(c))) — the positional arg is a Node.
        let denoted_occ = kb.make_denoted_occ_ref(c_sym, span, None);
        let head = Value::Entity {
            functor: f_sym,
            pos: Rc::from(vec![Value::Node(Rc::clone(&denoted_occ))]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };

        let rid = kb.assert_fact_value(head, sort, domain, None);

        // Indexed by sort and by top-level functor (via the head's TermView).
        assert_eq!(kb.by_sort(sort), vec![rid]);
        assert_eq!(kb.rules_by_functor(f_sym), vec![rid]);

        // Query f(?x): the value fact matches; ?x binds the Node by identity.
        let xv = kb.fresh_var(c_sym);
        let var_t = kb.alloc(Term::Var(Var::Global(xv)));
        let query = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_t, 1),
            named_args: SmallVec::new(),
        });
        let results = kb.query(query);
        assert_eq!(results.len(), 1, "value fact should be found by f(?x)");
        assert_eq!(results[0].0, rid);
        match results[0].1.resolve_as_value(xv) {
            Some(Value::Node(occ)) => assert!(
                Rc::ptr_eq(&occ, &denoted_occ),
                "?x must bind the SAME occurrence — Node identity preserved",
            ),
            other => panic!("?x should bind a Value::Node, got {other:?}"),
        }

        // Retract removes it from the active indexes.
        kb.retract(rid);
        assert!(kb.by_sort(sort).is_empty(), "retracted value fact left in by_sort");
        assert!(kb.query(query).is_empty(), "retracted value fact still queryable");
    }

    #[test]
    fn value_fact_named_node_args_resolve_by_key() {
        // WI-348 Phase B (review #4): a value head with NAMED args — one a Node,
        // one a ground term — resolves each query var to the child keyed by NAME
        // (not by position), and the Node arg keeps occurrence identity. Exercises
        // the carrier-faithful `extract_value_at_path` Named arm that the
        // positional-only happy-path test never touched.
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let f_sym = kb.intern("op_named");
        let c_sym = kb.intern("c");
        // `alpha` interned before `beta` → canonical (Symbol-index) order [alpha, beta].
        let alpha = kb.intern("alpha");
        let beta = kb.intern("beta");
        let sort = kb.make_name_term("MySort");
        let domain = kb.make_name_term("test");

        let denoted_occ = kb.make_denoted_occ_ref(c_sym, span, None);
        let beta_t = kb.alloc(Term::Const(Literal::Int(7)));
        let head = Value::Entity {
            functor: f_sym,
            pos: Rc::from(Vec::<Value>::new()),
            named: {
                let n: Vec<(Symbol, Value)> = vec![
                    (alpha, Value::Node(Rc::clone(&denoted_occ))),
                    (beta, Value::Term(beta_t)),
                ];
                Rc::from(n)
            },
        };

        let rid = kb.assert_fact_value(head, sort, domain, None);

        // Query f(alpha: ?x, beta: ?y).
        let xv = kb.fresh_var(c_sym);
        let yv = kb.fresh_var(c_sym);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let yt = kb.alloc(Term::Var(Var::Global(yv)));
        let query = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(alpha, xt), (beta, yt)]),
        });
        let results = kb.query(query);
        assert_eq!(results.len(), 1, "named-arg value fact should be found");
        assert_eq!(results[0].0, rid);

        // alpha → the Node (by key); beta → the Int term (by key).
        match results[0].1.resolve_as_value(xv) {
            Some(Value::Node(occ)) => assert!(
                Rc::ptr_eq(&occ, &denoted_occ),
                "alpha must bind the SAME occurrence",
            ),
            other => panic!("alpha should bind the Node, got {other:?}"),
        }
        assert_eq!(
            results[0].1.resolve_as_value(yv).map(|v| v.expect_term()),
            Some(beta_t),
            "beta must bind its ground term by key, not by position",
        );
    }

    #[test]
    fn value_fact_full_resolver_search_binds_node_as_value() {
        // WI-348: drive a value-fact head through the FULL SLD resolver
        // (`kb.resolve`, not just `kb.query` — so it exercises the resolver's
        // per-candidate triage, the path `is_equation` sits on) and confirm the
        // answer binds the query var to the Node *as a `Value`*, occurrence
        // identity intact. The substitution result is carrier-agnostic — a
        // `Value`, NOT a `TermId`: materializing the Node to a term would be lossy
        // and is never needed (consumers read the binding via `resolve_as_value`).
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let f_sym = kb.intern("vf");
        let c_sym = kb.intern("c");
        let sort = kb.make_name_term("MySort");
        let domain = kb.make_name_term("test");

        // Value fact: vf(Node(denoted(c))) — a Node-carrying head.
        let denoted_occ = kb.make_denoted_occ_ref(c_sym, span, None);
        let head = Value::Entity {
            functor: f_sym,
            pos: Rc::from(vec![Value::Node(Rc::clone(&denoted_occ))]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        kb.assert_fact_value(head, sort, domain, None);

        // SEARCH via the full resolver (not `kb.query`): vf(?x).
        let xv = kb.fresh_var(c_sym);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let goal = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let config = resolve::ResolveConfig {
            max_solutions: 4,
            ..resolve::ResolveConfig::default()
        };
        let solutions = kb.resolve(&[goal], &config);
        assert_eq!(solutions.len(), 1, "the value fact must be found by the full resolver");

        // ?x binds the Node *as a Value*, identity preserved through the answer
        // substitution — the carrier-agnostic substitution result.
        match solutions[0].subst.resolve_as_value(xv) {
            Some(Value::Node(occ)) => assert!(
                Rc::ptr_eq(&occ, &denoted_occ),
                "?x must bind the SAME occurrence through the full resolver",
            ),
            other => panic!("?x should bind the Node through resolve, got {other:?}"),
        }

        // WI-348: `reify` is now carrier-agnostic — reading the answer binding
        // through it preserves the Node identity (the former `TermId`-only reify
        // SILENTLY dropped it, leaving `?x` unbound: this is the gap this test
        // now closes). The bare var reifies to the Node itself; the whole goal
        // `vf(?x)` reifies to a `Value::Entity` carrying that same Node in its
        // child slot (the `Fn`-with-a-non-`Term`-child carrier).
        let subst = solutions[0].subst.clone();
        match kb.reify(xt, &subst) {
            Value::Node(occ) => assert!(
                Rc::ptr_eq(&occ, &denoted_occ),
                "reify(?x) must yield the SAME occurrence, identity intact",
            ),
            other => panic!("reify(?x) should yield the Node, got {other:?}"),
        }
        match kb.reify(goal, &subst) {
            Value::Entity { functor, pos, named } => {
                assert_eq!(functor, f_sym, "reify(vf(?x)) keeps the functor");
                assert!(named.is_empty(), "vf has no named args");
                match &pos[..] {
                    [Value::Node(occ)] => assert!(
                        Rc::ptr_eq(occ, &denoted_occ),
                        "reify(vf(?x)) must carry the SAME occurrence in its child slot",
                    ),
                    other => panic!("reify(vf(?x)) pos should be [Node], got {other:?}"),
                }
            }
            other => panic!("reify(vf(?x)) should be a Value::Entity, got {other:?}"),
        }
    }

    #[test]
    fn value_fact_dedup_keeps_distinct_node_answers() {
        // WI-348: the answer-dedup now keys on a carrier-agnostic structural
        // fingerprint (`goal_fingerprint`) instead of a materialized
        // `TermId`. Two solutions that bind the query var to
        // STRUCTURALLY-DISTINCT `Value::Node` answers must therefore stay
        // distinct — the former key dropped the Node to the bare var, collapsing
        // both to one key and silently losing a genuine answer.
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb); // interns the `denoted` field key `value`
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let f_sym = kb.intern("vf");
        let sort = kb.make_name_term("MySort");
        let domain = kb.make_name_term("test");

        // Two value facts with structurally-distinct Node heads:
        // vf(denoted(c1)), vf(denoted(c2)).
        for name in ["c1", "c2"] {
            let c = kb.intern(name);
            let occ = kb.make_denoted_occ_ref(c, span, None);
            let head = Value::Entity {
                functor: f_sym,
                pos: Rc::from(vec![Value::Node(occ)]),
                named: Rc::from(Vec::<(Symbol, Value)>::new()),
            };
            kb.assert_fact_value(head, sort, domain, None);
        }

        // Query vf(?x): both facts match, two distinct Node answers.
        let xv = kb.fresh_var(f_sym);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let goal = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let config = resolve::ResolveConfig {
            max_solutions: 8,
            ..resolve::ResolveConfig::default()
        };
        let solutions = kb.resolve(&[goal], &config);

        // The dedup fingerprints the Node structure, so it keeps both — it does
        // NOT collapse them to one var key (the pre-WI-348 materialize-to-`TermId` bug).
        assert_eq!(solutions.len(), 2, "distinct Node answers must NOT be deduped to one");

        let nodes: Vec<_> = solutions
            .iter()
            .filter_map(|s| match s.subst.resolve_as_value(xv) {
                Some(Value::Node(occ)) => Some(Rc::clone(occ)),
                _ => None,
            })
            .collect();
        assert_eq!(nodes.len(), 2, "both answers bind ?x to a Node");
        assert!(
            !Rc::ptr_eq(&nodes[0], &nodes[1]),
            "the two Node answers are distinct occurrences, kept distinct by the structural key",
        );
    }

    #[test]
    fn entity_of_query_includes_children() {
        let mut kb = KnowledgeBase::new();
        let nat = kb.make_name_term("Nat");
        let zero = kb.make_name_term("zero");
        let domain = kb.make_name_term("test");

        kb.register_sort(nat, SortKind::Sort);
        kb.register_entity_of(zero, nat);

        // Assert a fact of sort `zero`
        let zero_val = kb.make_name_term("zero");
        let fid = kb.assert_fact(zero_val, zero, domain, None);

        // Query by_sort(Nat) should include the zero fact (entity children)
        let results = kb.by_sort(nat);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], fid);

        // is_entity_of
        assert!(kb.is_entity_of(zero, nat));
        assert!(!kb.is_entity_of(nat, zero));
    }

    #[test]
    fn value_rule_head_node_stored_and_read_back() {
        // WI-373 slice 1: the carrier-agnostic storage epilogue `assert_rule_nodes`
        // (converged with `assert_fact_value`) stores a RULE head — with a body,
        // not just a fact — that carries a `Value::Node` denoted occurrence, and
        // `rule_head_value` reads it back with the occurrence identity intact.
        // (DeBruijn-*closing* a denoted head is gated on WI-342 P3 — the
        // Type-occurrence var-walk — so this exercises the no-var storage path.)
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let vf = kb.intern("vf");
        let cond = kb.intern("cond");
        let sort = kb.make_name_term("MySort");
        let domain = kb.make_name_term("test");

        // Head vf(denoted(c1)) — a ground Value::Entity carrying a Node child.
        let c1 = kb.intern("c1");
        let denoted = kb.make_denoted_occ_ref(c1, span, None);
        let head = Value::Entity {
            functor: vf,
            pos: Rc::from(vec![Value::Node(Rc::clone(&denoted))]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };

        // A ground body atom, so this is a rule (non-empty body), not a fact.
        let cond_goal = kb.alloc(Term::Fn {
            functor: cond,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[cond_goal]);

        let rid = kb.assert_rule_nodes(head, body_nodes, sort, domain, None);

        match kb.rule_head_value(rid) {
            Value::Entity { functor, pos, .. } => {
                assert_eq!(*functor, vf);
                match &pos[0] {
                    Value::Node(occ) => assert!(
                        Rc::ptr_eq(occ, &denoted),
                        "the denoted occurrence must survive storage with identity intact",
                    ),
                    other => panic!("head child should be the Node, got {other:?}"),
                }
            }
            other => panic!("value rule head should be a Value::Entity, got {other:?}"),
        }
    }

    #[test]
    fn value_head_debruijn_var_in_occurrence_indexes_like_term() {
        // WI-373: a De Bruijn var carried INSIDE an occurrence value head now
        // keys a var-edge in the discrimination tree, the same as a term head's
        // De Bruijn var — `occ_index_var` surfaces `Expr::Var` of any kind,
        // mirroring `TermIdView`'s `Term::Var(v) => Some(v)`. Before this fix the
        // insert read `Opaque` and panicked ("value-fact keying unimplemented").
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);

        let vf = kb.intern("vf");
        let g = kb.intern("g");
        let cond = kb.intern("cond");
        let sort = kb.make_name_term("MySort");
        let domain = kb.make_name_term("test");

        // An occurrence `g(DeBruijn(0))` — the shape a stored value rule head's
        // child takes after De Bruijn closure.
        let xv = kb.fresh_var(vf);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let g_term = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let g_global = node_occurrence::materialize_from_handle(&kb, g_term);
        let g_db = node_occurrence::node_to_debruijn(&mut kb, &g_global, &[xv]);

        let head = Value::Entity {
            functor: vf,
            pos: Rc::from(vec![Value::Node(g_db)]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let cond_goal = kb.alloc(Term::Fn {
            functor: cond,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[cond_goal]);

        // Indexes without panicking (the De Bruijn var routes to a var-edge)...
        let rid = kb.assert_rule_nodes(head, body_nodes, sort, domain, None);

        // ...and the head is discoverable by a query on its functor.
        let yv = kb.fresh_var(vf);
        let yt = kb.alloc(Term::Var(Var::Global(yv)));
        let query = kb.alloc(Term::Fn {
            functor: vf,
            pos_args: SmallVec::from_elem(yt, 1),
            named_args: SmallVec::new(),
        });
        let found = kb.query(query);
        assert!(
            found.iter().any(|(r, _)| *r == rid),
            "the De Bruijn-bearing value head must be indexed + queryable",
        );
    }

    #[test]
    fn value_rule_head_with_var_asserts_closes_and_indexes() {
        // WI-373: a var-bearing value rule head asserts via the carrier-agnostic
        // De Bruijn path — `collect_value_head_vars` finds the var inside the Expr
        // Node child (arity 1), `close_value_head_debruijn` closes it, and gap-2
        // discrim keying indexes it (queryable). RESOLVING such a head is loudly
        // gated on the binding-extraction half of gap 3 (see `with_fresh_vars`).
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);

        let vf = kb.intern("vf");
        let g = kb.intern("g");
        let thing = kb.intern("thing");
        let sort = kb.make_name_term("MySort");
        let domain = kb.make_name_term("test");

        // Head vf(g(?x)) — g(?x) carried as an Expr Node; body thing(?x).
        let xv = kb.fresh_var(vf);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let g_x = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let g_occ = node_occurrence::materialize_from_handle(&kb, g_x);
        let head = Value::Entity {
            functor: vf,
            pos: Rc::from(vec![Value::Node(g_occ)]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let thing_x = kb.alloc(Term::Fn {
            functor: thing,
            pos_args: SmallVec::from_elem(xt, 1),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[thing_x]);

        // Closure: collect the var inside the Node + close to De Bruijn + index.
        let rid = kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);
        assert_eq!(kb.rule_arity(rid), 1, "?x inside the Node is the rule's one var");

        // Discoverable by a query on its functor (gap-2 keying).
        let yv = kb.fresh_var(vf);
        let yt = kb.alloc(Term::Var(Var::Global(yv)));
        let g_y = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(yt, 1),
            named_args: SmallVec::new(),
        });
        let query = kb.alloc(Term::Fn {
            functor: vf,
            pos_args: SmallVec::from_elem(g_y, 1),
            named_args: SmallVec::new(),
        });
        assert!(
            kb.query(query).iter().any(|(r, _)| *r == rid),
            "the var-bearing value rule head must be indexed + queryable",
        );
    }

    #[test]
    fn value_rule_head_with_var_resolves_and_binds_nested() {
        // WI-373 gap 3 (binding extraction): RESOLVE against a var-bearing value
        // rule head. Rule  vf(g(?x)) :- thing(?x)  with head carried as a
        // Value::Node, plus fact thing("active"). A query vf(g(?y)) must bind the
        // NESTED ?y to the rule's head var, run the body, and answer ?y="active".
        // Before the nested binding-extraction this yielded an empty tree_subst
        // (?y unconstrained — a silent wrong answer) and `with_fresh_vars`
        // loud-guarded the value head; now it resolves carrier-faithfully.
        use crate::eval::value::Value;
        use crate::intern::Symbol;
        use crate::kb::load::register_prelude;
        use crate::kb::resolve::ResolveConfig;
        use std::rc::Rc;
        use term::Var;

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);

        let vf = kb.intern("vf");
        let g = kb.intern("g");
        let thing = kb.intern("thing");
        let sort = kb.make_name_term("MySort");
        let domain = kb.make_name_term("test");

        // Fact thing("active").
        let active = kb.alloc(Term::Const(Literal::String("active".into())));
        let thing_active = kb.alloc(Term::Fn {
            functor: thing, pos_args: SmallVec::from_elem(active, 1), named_args: SmallVec::new(),
        });
        kb.assert_fact(thing_active, sort, domain, None);

        // Rule vf(g(?x)) :- thing(?x), head g(?x) carried as a Value::Node.
        let xv = kb.fresh_var(vf);
        let xt = kb.alloc(Term::Var(Var::Global(xv)));
        let g_x = kb.alloc(Term::Fn {
            functor: g, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let g_occ = node_occurrence::materialize_from_handle(&kb, g_x);
        let head = Value::Entity {
            functor: vf,
            pos: Rc::from(vec![Value::Node(g_occ)]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let thing_x = kb.alloc(Term::Fn {
            functor: thing, pos_args: SmallVec::from_elem(xt, 1), named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[thing_x]);
        kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);

        let config = ResolveConfig::default();

        // Query vf(g(?y)) → 1 solution with ?y = "active".
        let yv = kb.fresh_var(vf);
        let yt = kb.alloc(Term::Var(Var::Global(yv)));
        let g_y = kb.alloc(Term::Fn {
            functor: g, pos_args: SmallVec::from_elem(yt, 1), named_args: SmallVec::new(),
        });
        let q_var = kb.alloc(Term::Fn {
            functor: vf, pos_args: SmallVec::from_elem(g_y, 1), named_args: SmallVec::new(),
        });
        let sols = kb.resolve(&[q_var], &config);
        assert_eq!(sols.len(), 1, "vf(g(?y)) should resolve through the value rule head");
        let bound = kb.reify(yt, &sols[0].subst).expect_term();
        assert_eq!(bound, active, "nested ?y must bind to \"active\", got {:?}", bound);

        // Query vf(g("active")) → succeeds (body thing("active") holds).
        let g_active = kb.alloc(Term::Fn {
            functor: g, pos_args: SmallVec::from_elem(active, 1), named_args: SmallVec::new(),
        });
        let q_ok = kb.alloc(Term::Fn {
            functor: vf, pos_args: SmallVec::from_elem(g_active, 1), named_args: SmallVec::new(),
        });
        assert_eq!(kb.resolve(&[q_ok], &config).len(), 1, "vf(g(\"active\")) should hold");

        // Query vf(g("missing")) → fails (no thing("missing")).
        let missing = kb.alloc(Term::Const(Literal::String("missing".into())));
        let g_missing = kb.alloc(Term::Fn {
            functor: g, pos_args: SmallVec::from_elem(missing, 1), named_args: SmallVec::new(),
        });
        let q_no = kb.alloc(Term::Fn {
            functor: vf, pos_args: SmallVec::from_elem(g_missing, 1), named_args: SmallVec::new(),
        });
        assert_eq!(kb.resolve(&[q_no], &config).len(), 0, "vf(g(\"missing\")) should fail");
    }

    #[test]
    fn retract_removes_from_index() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("T");
        let domain = kb.make_name_term("d");
        let term = kb.alloc(Term::Const(Literal::Int(42)));

        let fid = kb.assert_fact(term, sort, domain, None);
        assert_eq!(kb.by_sort(sort).len(), 1);

        kb.retract(fid);
        assert_eq!(kb.by_sort(sort).len(), 0);
    }

    #[test]
    fn match_term_const() {
        let mut kb = KnowledgeBase::new();
        let a = kb.alloc(Term::Const(Literal::Int(42)));
        let b = kb.alloc(Term::Const(Literal::Int(42)));
        let c = kb.alloc(Term::Const(Literal::Int(99)));

        assert!(kb.match_term(a, b).is_some());
        assert!(kb.match_term(a, c).is_none());
    }

    #[test]
    fn match_term_var_binds() {
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_term = kb.alloc(Term::Var(Var::Global(vid)));
        let target = kb.alloc(Term::Const(Literal::Int(42)));

        let s = kb.match_term(var_term, target).expect("should match");
        assert_eq!(s.resolve_as_value(vid).map(|v| v.expect_term()), Some(target));
    }

    #[test]
    fn match_term_var_consistency() {
        // ?x matches first arg, then must match same value in second arg
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_term = kb.alloc(Term::Var(Var::Global(vid)));

        let f_sym = kb.intern("f");
        let val = kb.alloc(Term::Const(Literal::Int(1)));

        // Pattern: f(?x, ?x)
        let pattern = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[var_term, var_term]),
            named_args: SmallVec::new(),
        });

        // Target: f(1, 1) — should match
        let target_ok = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[val, val]),
            named_args: SmallVec::new(),
        });
        assert!(kb.match_term(pattern, target_ok).is_some());

        // Target: f(1, 2) — should fail (inconsistent binding for ?x)
        let val2 = kb.alloc(Term::Const(Literal::Int(2)));
        let target_bad = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[val, val2]),
            named_args: SmallVec::new(),
        });
        assert!(kb.match_term(pattern, target_bad).is_none());
    }

    #[test]
    fn match_term_fn_structure() {
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let g = kb.intern("g");
        let val = kb.alloc(Term::Const(Literal::Int(1)));

        let term_f = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        let term_g = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        // Same functor + args → matches
        assert!(kb.match_term(term_f, term_f).is_some());
        // Different functor → fails
        assert!(kb.match_term(term_f, term_g).is_none());
    }

    #[test]
    fn match_view_against_value_entity() {
        // Pattern `Account(?x)` (TermId) matched against a runtime
        // `Value::Entity { functor: Account, pos: [Value::Str("A001")] }`.
        // Proves the Q2 goal: rule-head patterns can unify with
        // non-TermId Value targets without promoting them into TermStore.
        use crate::eval::value::Value;

        let mut kb = KnowledgeBase::new();
        let f = kb.intern("Account");
        let x_sym = kb.intern("x");
        let xv = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(xv)));
        let pattern = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let value_target = Value::Entity {
            functor: f,
            pos: vec![Value::Str("A001".into())].into(),
            named: Vec::new().into(),
        };

        let subst = kb.match_view(pattern, &value_target)
            .expect("match should succeed");
        // ?x's binding is the Value (not a TermId) — lineage preserved.
        match subst.resolve_as_value(xv) {
            Some(Value::Str(s)) => assert_eq!(s, "A001"),
            other => panic!("expected Value::Str, got {other:?}"),
        }
        // resolve() returns None because the binding isn't a TermId.
        assert!(!matches!(subst.resolve_as_value(xv), Some(Value::Term(_))));
    }

    #[test]
    fn match_view_binds_vars_to_nested_value_entities() {
        // Pattern `Pair(?x, ?y)` matched against a runtime
        // `Pair(Entity{ inner(a: 1, b: "hi") }, Tuple(2, Entity{ leaf }))`.
        // Proves variables capture non-trivial structured Values out of
        // Substitution — the core WI-045/Q1 contract for external-source
        // bindings that must not be promoted to TermId.
        use crate::eval::value::Value;

        let mut kb = KnowledgeBase::new();
        let pair = kb.intern("Pair");
        let inner = kb.intern("Inner");
        let leaf = kb.intern("Leaf");
        let a_field = kb.intern("a");
        let b_field = kb.intern("b");

        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let xv = kb.fresh_var(x_sym);
        let yv = kb.fresh_var(y_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(xv)));
        let var_y = kb.alloc(Term::Var(Var::Global(yv)));
        let pattern = kb.alloc(Term::Fn {
            functor: pair,
            pos_args: SmallVec::from_slice(&[var_x, var_y]),
            named_args: SmallVec::new(),
        });

        let inner_val = Value::Entity {
            functor: inner,
            pos: Vec::new().into(),
            named: vec![(a_field, Value::Int(1)), (b_field, Value::Str("hi".into()))].into(),
        };
        let leaf_val = Value::Entity { functor: leaf, pos: Vec::new().into(), named: Vec::new().into() };
        let nested_tuple = Value::Tuple {
            pos: vec![Value::Int(2), leaf_val.clone()].into(),
            named: Vec::new().into(),
        };
        let target = Value::Entity {
            functor: pair,
            pos: vec![inner_val.clone(), nested_tuple.clone()].into(),
            named: Vec::new().into(),
        };

        let subst = kb.match_view(pattern, &target).expect("match should succeed");

        match subst.resolve_as_value(xv) {
            Some(Value::Entity { functor, named, .. }) => {
                assert_eq!(*functor, inner);
                assert_eq!(named.len(), 2);
                assert!(named.iter().any(|(k, v)|
                    *k == a_field && matches!(v, Value::Int(1))));
                assert!(named.iter().any(|(k, v)|
                    *k == b_field && matches!(v, Value::Str(s) if s == "hi")));
            }
            other => panic!("expected Value::Entity(Inner) for ?x, got {other:?}"),
        }

        match subst.resolve_as_value(yv) {
            Some(Value::Tuple { pos, .. }) => {
                assert_eq!(pos.len(), 2);
                assert!(matches!(pos[0], Value::Int(2)));
                match &pos[1] {
                    Value::Entity { functor, .. } => assert_eq!(*functor, leaf),
                    other => panic!("expected nested Leaf entity, got {other:?}"),
                }
            }
            other => panic!("expected Value::Tuple for ?y, got {other:?}"),
        }

        // Both variables bind to non-Term Values → resolve() returns None.
        assert!(!matches!(subst.resolve_as_value(xv), Some(Value::Term(_))));
        assert!(!matches!(subst.resolve_as_value(yv), Some(Value::Term(_))));
    }

    #[test]
    fn match_view_binds_vars_to_node_occurrence_children() {
        // WI-276: a `[simp]` rule LHS `add(?a, ?b)` (TermId pattern) matches a
        // reflect Expr occurrence `Value::Node(add(1, 2))` and binds ?a/?b to
        // the child occurrences (identity preserved, not promoted to TermId).
        // This is the substrate that lets the typer-phase rewriting engine
        // (proposal 043) fire simp rules over expression occurrences.
        use crate::eval::value::Value;
        use crate::kb::node_occurrence::{Expr, NodeOccurrence};
        use crate::kb::term::Literal;
        use crate::span::{SourceId, SourceSpan};
        use std::rc::Rc;

        let mut kb = KnowledgeBase::new();
        let add = kb.intern("add");
        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let av = kb.fresh_var(a_sym);
        let bv = kb.fresh_var(b_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(av)));
        let var_b = kb.alloc(Term::Var(Var::Global(bv)));
        let pattern = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });

        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);
        let child_a = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let child_b = NodeOccurrence::new_expr(Expr::Const(Literal::Int(2)), span, None);
        let add_occ = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: add,
                pos_args: vec![Rc::clone(&child_a), Rc::clone(&child_b)],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );
        let target = Value::Node(add_occ);

        let subst = kb.match_view(pattern, &target).expect("match should succeed");

        match subst.resolve_as_value(av) {
            Some(Value::Node(occ)) => {
                assert!(matches!(occ.as_expr(), Some(Expr::Const(Literal::Int(1)))));
                assert!(Rc::ptr_eq(&occ, &child_a), "?a should bind the same Rc child");
            }
            other => panic!("expected Value::Node for ?a, got {other:?}"),
        }
        match subst.resolve_as_value(bv) {
            Some(Value::Node(occ)) => {
                assert!(matches!(occ.as_expr(), Some(Expr::Const(Literal::Int(2)))));
                assert!(Rc::ptr_eq(&occ, &child_b), "?b should bind the same Rc child");
            }
            other => panic!("expected Value::Node for ?b, got {other:?}"),
        }
        // Non-Term bindings → narrowing to a term returns None (lineage preserved).
        assert!(!matches!(subst.resolve_as_value(av), Some(Value::Term(_))));
        assert!(!matches!(subst.resolve_as_value(bv), Some(Value::Term(_))));
    }

    #[test]
    fn wi342_value_carried_modify_c_arrow_reads_through_termview() {
        // WI-342 P1+P2 slice. Build a real `(Cell) -> Unit ! {-Modify[c]}` arrow
        // as a Value-carried occurrence spine: the `denoted(c)` carries an
        // Rc<NodeOccurrence>, so the carrier rule poisons every container up to
        // `arrow` — each is `NodeKind::Type` / `NodeKind::EffectExpr`, while
        // ground children (param/result/sort_ref/empty_row) stay hash-consed
        // `TermId`. Assert it reads back through `TermView` with the SAME functor
        // surface as its `Term::Fn` twin, and that the `denoted` is reached
        // (Rep A: via the type-specific `as_type` walk for `bindings`) carrying
        // the identity-bearing occurrence the producer built.
        use crate::kb::load::register_prelude;
        use crate::kb::node_occurrence::{Expr, TypeChild, TypeNode};
        use crate::kb::term_view::{TermView, ViewHead, ViewItem};
        use crate::span::{SourceId, SourceSpan};

        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 10);

        let c_sym = kb.intern("c");
        let modify_sym = kb.intern("Modify");
        let t_sym = kb.intern("T");
        let param_ty = kb.make_sort_ref_by_name("Cell");
        let result_ty = kb.make_sort_ref_by_name("Unit");

        // `modify_base` and `empty_row_tid` are ground children the Value-carried
        // spine reuses below. WI-366: the former ground "TermId twin" of the whole
        // arrow (built via the retired `make_denoted`) is gone — production never
        // builds a ground `denoted`, so the cross-carrier identity comparison it
        // fed was dead-path; the Value-form reads below stand on their own.
        let modify_base = kb.make_sort_ref(modify_sym);
        let empty_row_tid = kb.make_effect_expression_empty_row();

        let arrow_sym = kb.resolve_symbol("anthill.prelude.TypeExtractor.Arrow");
        let effects_rows_sym = kb.resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
        let merge_sym = kb.resolve_symbol("anthill.prelude.EffectExpression.merge");
        let absent_sym = kb.resolve_symbol("anthill.prelude.EffectExpression.absent");

        let param_key = kb.intern("param");
        let result_key = kb.intern("result");
        let effects_key = kb.intern("effects");
        let effects_expr_key = kb.intern("effects_expr");
        let left_key = kb.intern("left");
        let right_key = kb.intern("right");
        let label_key = kb.intern("label");

        // ── Value-carried spine (the new producer builders). ──
        let denoted_occ = kb.make_denoted_occ_ref(c_sym, span, None);
        let param_occ = kb.make_parameterized_occ(
            TypeChild::Ground(modify_base),
            vec![(t_sym, TypeChild::Node(Rc::clone(&denoted_occ)))],
            span,
            None,
        );
        let absent_occ = kb.make_absent_occ(TypeChild::Node(Rc::clone(&param_occ)), span, None);
        let merge_occ = kb.make_merge_occ(
            TypeChild::Node(Rc::clone(&absent_occ)),
            TypeChild::Ground(empty_row_tid),
            span,
            None,
        );
        let effects_rows_occ =
            kb.make_effects_rows_occ(TypeChild::Node(Rc::clone(&merge_occ)), span, None);
        let arrow_occ = kb.make_arrow_occ(
            TypeChild::Ground(param_ty),
            TypeChild::Ground(result_ty),
            TypeChild::Node(Rc::clone(&effects_rows_occ)),
            span,
            None,
        );

        let functor_of = |h: &ViewHead| match h {
            ViewHead::Functor { functor, .. } => *functor,
            _ => None,
        };

        // Carrier identity: the Value-form arrow head is the `Arrow` functor.
        let head = arrow_occ.head(&kb);
        assert_eq!(functor_of(&head), Some(arrow_sym));
        assert!(
            matches!(head, ViewHead::Functor { named_arity: 3, pos_arity: 0, .. }),
            "arrow exposes param/result/effects, got {head:?}",
        );

        // arrow.param / arrow.result are ground (no denoted) → hash-consed Terms.
        let p = arrow_occ.named_arg(&kb, param_key).expect("arrow.param");
        assert!(matches!(p, ViewItem::Term(t) if t == param_ty), "param ground, got {p:?}");
        let r = arrow_occ.named_arg(&kb, result_key).expect("arrow.result");
        assert!(matches!(r, ViewItem::Term(t) if t == result_ty), "result ground, got {r:?}");

        // Walk the poisoned spine through `TermView`, functor by functor.
        let eff = arrow_occ.named_arg(&kb, effects_key).expect("arrow.effects");
        assert_eq!(functor_of(&eff.head(&kb)), Some(effects_rows_sym));

        let merge_v = eff.named_arg(&kb, effects_expr_key).expect("effects_rows.effects_expr");
        assert_eq!(functor_of(&merge_v.head(&kb)), Some(merge_sym));

        // merge.left is poisoned (Node → absent); merge.right is the ground
        // `empty_row` (Term), proving ground subtrees stay hash-consed.
        let left = merge_v.named_arg(&kb, left_key).expect("merge.left");
        assert_eq!(functor_of(&left.head(&kb)), Some(absent_sym));
        let right = merge_v.named_arg(&kb, right_key).expect("merge.right");
        assert!(
            matches!(right, ViewItem::Term(t) if t == empty_row_tid),
            "merge.right is the ground empty_row Term, got {right:?}",
        );

        let paramd = left.named_arg(&kb, label_key).expect("absent.label");
        // WI-361: the parameterized carrier mirrors the term-backed `Fn{Modify, T}`
        // — its head functor IS the base sort `Modify` (no `parameterized` wrapper)
        // and the binding `T` reads as a named arg, so `TermView` reads the carrier
        // and its `Term::Fn` twin identically.
        assert_eq!(functor_of(&paramd.head(&kb)), Some(modify_sym));
        assert!(
            matches!(paramd.head(&kb), ViewHead::Functor { named_arity: 1, pos_arity: 0, .. }),
            "parameterized exposes its single binding T as a named arg, got {:?}",
            paramd.head(&kb),
        );

        // The binding value `T = denoted(c)` is reached as the named arg `T`,
        // carrying the identity-bearing occurrence (the poison source) — not a
        // hash-consed Term.
        let t_arg = paramd.named_arg(&kb, t_sym).expect("parameterized.T binding");
        let ViewItem::Node(denoted_seen) = &t_arg else {
            panic!("binding value is the poisoned denoted Node, got {t_arg:?}");
        };
        assert!(Rc::ptr_eq(denoted_seen, &denoted_occ), "denoted Rc identity preserved");

        // Storage is unchanged (`TypeNode::Parameterized { base, bindings }`); the
        // Rc identity of the carrier occurrence is preserved through the view.
        let ViewItem::Node(param_seen) = &paramd else {
            panic!("parameterized read as a Node occurrence, got {paramd:?}");
        };
        assert!(Rc::ptr_eq(param_seen, &param_occ), "view preserves Rc identity");
        let TypeNode::Denoted { value } =
            denoted_seen.as_type().expect("denoted is a Type node")
        else {
            panic!("expected Denoted");
        };
        assert!(
            matches!(value.as_expr(), Some(Expr::Ref(s)) if *s == c_sym),
            "denoted carries the source Ref(c) occurrence, got {:?}",
            value.as_expr(),
        );
        // The carried occurrence is NOT a hash-consed Ref — it is an
        // identity-bearing NodeOccurrence (the whole point of the carrier rule).
        assert!(
            value.as_type().is_none() && value.as_expr().is_some(),
            "denoted value is an Expr-kind occurrence",
        );
    }

    #[test]
    fn match_term_equals_match_view_of_termidview() {
        // For TermId-backed targets, match_term and match_view produce
        // structurally-equivalent substitutions. Proves the wrapper is
        // semantically transparent on the fast path.
        use crate::kb::term_view::TermIdView;

        let mut kb = KnowledgeBase::new();
        let f = kb.intern("pair");
        let x_sym = kb.intern("x");
        let xv = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(xv)));
        let lit = kb.alloc(Term::Const(Literal::Int(7)));
        let pattern = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_slice(&[var_x, lit]),
            named_args: SmallVec::new(),
        });
        let a = kb.alloc(Term::Const(Literal::Int(3)));
        let target = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_slice(&[a, lit]),
            named_args: SmallVec::new(),
        });

        let via_term = kb.match_term(pattern, target).expect("match_term");
        let via_view = kb.match_view(pattern, &TermIdView(target)).expect("match_view");

        assert_eq!(via_term.resolve_as_value(xv).map(|v| v.expect_term()), via_view.resolve_as_value(xv).map(|v| v.expect_term()));
        assert_eq!(via_term.resolve_as_value(xv).map(|v| v.expect_term()), Some(a));
    }

    #[test]
    fn subst_term_replaces_name() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("T");
        let int = kb.make_name_term("Int64");

        // Build Option(T) = Fn("Option", pos_args=[Fn("T",[])], named_args=[])
        let option_sym = kb.intern("Option");
        let option_t = kb.alloc(Term::Fn {
            functor: option_sym,
            pos_args: SmallVec::from_elem(t, 1),
            named_args: SmallVec::new(),
        });

        let result = kb.subst_term(option_t, t, int);
        match kb.get_term(result) {
            Term::Fn { functor, pos_args, .. } => {
                assert_eq!(*functor, option_sym);
                assert_eq!(pos_args.len(), 1);
                assert_eq!(pos_args[0], int);
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }

    #[test]
    fn subst_term_identity() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("T");
        let int = kb.make_name_term("Int64");
        let string = kb.make_name_term("String");

        // Substituting a name that doesn't appear should return the same term
        let result = kb.subst_term(t, int, string);
        assert_eq!(result, t);
    }

    #[test]
    fn subst_term_nested() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("T");
        let int = kb.make_name_term("Int64");

        // Build pair(T, T)
        let pair_sym = kb.intern("pair");
        let pair_tt = kb.alloc(Term::Fn {
            functor: pair_sym,
            pos_args: SmallVec::from_slice(&[t, t]),
            named_args: SmallVec::new(),
        });

        let result = kb.subst_term(pair_tt, t, int);
        match kb.get_term(result) {
            Term::Fn { pos_args, .. } => {
                // Both args should now be Int
                for &id in pos_args.iter() {
                    assert_eq!(id, int);
                }
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }

    #[test]
    fn query_by_pattern() {
        let mut kb = KnowledgeBase::new();
        let fact_sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");

        // Assert parent("alice", "bob") and parent("bob", "charlie")
        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));

        let fact1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        let fact2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[bob, charlie]),
            named_args: SmallVec::new(),
        });

        kb.assert_fact(fact1, fact_sort, domain, None);
        kb.assert_fact(fact2, fact_sort, domain, None);

        // Query: parent(?x, "bob") — should find only fact1
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vid)));
        let pattern = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, bob]),
            named_args: SmallVec::new(),
        });

        let results = kb.query(pattern);
        assert_eq!(results.len(), 1);
        let (_, ref s) = results[0];
        assert_eq!(s.resolve_as_value(vid).map(|v| v.expect_term()), Some(alice));
    }

    #[test]
    fn query_view_matches_via_value_node_goal() {
        // WI-246: a `Value::Node` occurrence goal finds the same candidate(s)
        // as the equivalent `TermId` goal — the matcher reads the goal only
        // through `TermView`, so an occurrence goal needs no lowering to a
        // hash-consed term to be looked up in the discrim tree.
        use crate::eval::value::Value;
        let mut kb = KnowledgeBase::new();
        let fact_sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");
        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));
        let fact1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        let fact2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[bob, charlie]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact1, fact_sort, domain, None);
        kb.assert_fact(fact2, fact_sort, domain, None);

        // Goal `parent(?x, "bob")` built as a term, then materialized to an
        // occurrence and queried as a `Value::Node` — must match fact1 only,
        // binding ?x → "alice", identically to the `TermId` query.
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vid)));
        let pattern = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, bob]),
            named_args: SmallVec::new(),
        });
        let term_hits = kb.query(pattern);

        let occ = node_occurrence::materialize_from_handle(&kb, pattern);
        let node_hits = kb.query_view(&Value::Node(occ));

        assert_eq!(node_hits.len(), 1, "Value::Node goal matches one fact");
        assert_eq!(node_hits.len(), term_hits.len(), "same candidate count as TermId goal");
        assert_eq!(node_hits[0].0, term_hits[0].0, "same matched rule/fact");
        assert_eq!(
            node_hits[0].1.resolve_as_value(vid).map(|v| v.expect_term()),
            Some(alice),
            "?x bound to \"alice\" via the occurrence goal",
        );
    }

    #[test]
    fn assert_rule_with_body() {
        let mut kb = KnowledgeBase::new();
        let rule_sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");
        let grandparent_sym = kb.intern("grandparent");

        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let z_sym = kb.intern("z");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let vz = kb.fresh_var(z_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let var_z = kb.alloc(Term::Var(Var::Global(vz)));

        // grandparent(?x, ?z) :- parent(?x, ?y), parent(?y, ?z)
        let head = kb.alloc(Term::Fn {
            functor: grandparent_sym,
            pos_args: SmallVec::from_slice(&[var_x, var_z]),
            named_args: SmallVec::new(),
        });
        let b1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, var_y]),
            named_args: SmallVec::new(),
        });
        let b2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_y, var_z]),
            named_args: SmallVec::new(),
        });

        let rid = kb.assert_rule(head, vec![b1, b2], rule_sort, domain, None);

        // body should have two atoms
        assert_eq!(kb.rule_body_nodes(rid).len(), 2);
        assert_eq!(kb.rule_head(rid), head);

        // fact_count should be 0, rule_count should be 1
        assert_eq!(kb.fact_count(), 0);
        assert_eq!(kb.rule_count(), 1);
    }

    #[test]
    fn query_rules_filters_facts() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Test");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");

        // Assert a ground fact f(1)
        let v1 = kb.alloc(Term::Const(Literal::Int(1)));
        let fact_term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(v1, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact_term, sort, domain, None);

        // Assert a rule f(?x) :- g(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let rule_head = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let g_sym = kb.intern("g");
        let body_lit = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(rule_head, vec![body_lit], sort, domain, None);

        // query() should find both
        let q_sym = kb.intern("q");
        let qv = kb.fresh_var(q_sym);
        let var_q = kb.alloc(Term::Var(Var::Global(qv)));
        let pattern = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_q, 1),
            named_args: SmallVec::new(),
        });
        assert_eq!(kb.query(pattern).len(), 2);

        // query_rules() should find only the rule
        assert_eq!(kb.query_rules(pattern).len(), 1);
    }

    #[test]
    fn apply_subst_replaces_vars() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vid)));
        let val = kb.alloc(Term::Const(Literal::Int(42)));

        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let mut s = subst::Substitution::new();
        s.bind(&kb, vid, val);
        let result = kb.apply_subst(term, &s);

        match kb.get_term(result) {
            Term::Fn { pos_args, .. } => {
                assert_eq!(pos_args[0], val);
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }

    #[test]
    fn collect_vars_finds_all() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));

        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[var_x, var_y, var_x]),
            named_args: SmallVec::new(),
        });

        let vars = kb.collect_vars(term);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&vx));
        assert!(vars.contains(&vy));
    }

    #[test]
    fn retract_releases_body_terms() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");
        let g_sym = kb.intern("g");

        let val = kb.alloc(Term::Const(Literal::Int(99)));
        let head = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        let body_lit = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let rid = kb.assert_rule(head, vec![body_lit], sort, domain, None);
        assert_eq!(kb.rule_count(), 1);

        kb.retract(rid);
        assert_eq!(kb.rule_count(), 0);
        assert_eq!(kb.fact_count(), 0);
    }
}

/// WI-518: a guard riding an occurrence (`Value::Node`) leaf now RESOLVES through
/// `resolve_goals`, carrier-neutrally, exactly as a term leaf does — the WI-514
/// gate (which used to report such a guard `Gated` / refuse the assertion / panic)
/// has dissolved. These tests are the spike turned into regressions: an occurrence
/// self-loop constraint `no edge(?p, ?p)` lowered through the new `Vec<Value>` path
/// matches real self-loop facts, excludes non-self-loops, and enforces at both the
/// post-load `check_all_guards` pass and the per-assert runtime path.
#[cfg(test)]
mod wi518_occurrence_guard_resolution_tests {
    use super::*;
    use crate::eval::value::Value;
    use crate::intern::Symbol;
    use crate::kb::node_occurrence::{Expr, NodeOccurrence};
    use crate::span::{SourceId, SourceSpan};
    use smallvec::SmallVec;
    use std::rc::Rc;

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 0)
    }

    /// Register a `LogicalQuery` constructor symbol under its qualified name
    /// (`anthill.reflect.LogicalQuery.<short>`) and return it — mirroring the
    /// loader's `logical_query_ctor`. WI-513: the guard engine dispatches by the
    /// interned qualified `LogicalQuerySymbols`, so a guard built in a bare KB must
    /// use the SAME qualified symbol `LogicalQuerySymbols::resolve` will look up
    /// (an `intern("no_q")` short name would not match). Field-key symbols
    /// (`condition`/`body`/`term`/…) stay short-name interned — both sides intern
    /// them identically.
    fn lq_ctor(kb: &mut KnowledgeBase, short: &str) -> Symbol {
        let qn = format!("anthill.reflect.LogicalQuery.{short}");
        kb.symbols.define(short, &qn, SymbolKind::Operation, 0)
    }

    /// Build `no_q(condition: pattern_query(term: <leaf>), body: empty_query)` — a
    /// quantified guard around `leaf` (the top level is a quantifier so
    /// `evaluate_guard` descends into the shared lowerer). The leaf is any goal
    /// `Value`: a `Value::Term` for the hash-consed case, a `Value::Node` for an
    /// occurrence goal.
    fn no_q_guard(kb: &mut KnowledgeBase, leaf: Value) -> Value {
        let no_q = lq_ctor(kb, "no_q");
        let condition = kb.intern("condition");
        let body = kb.intern("body");
        let pattern_query = lq_ctor(kb, "pattern_query");
        let term = kb.intern("term");
        let empty_query = lq_ctor(kb, "empty_query");

        let pq = Value::Entity {
            functor: pattern_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(term, leaf)]),
        };
        let empty = Value::Entity {
            functor: empty_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        Value::Entity {
            functor: no_q,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(condition, pq), (body, empty)]),
        }
    }

    /// The occurrence goal `edge(?p, ?p)` — a self-loop pattern carrying a SHARED
    /// `Value::Node` variable across both positional slots, as a `denoted`
    /// occurrence would. This is the leaf the WI-514 gate used to refuse; WI-518
    /// resolves it.
    fn edge_self_loop_occurrence(kb: &mut KnowledgeBase) -> Value {
        let edge = kb.intern("edge");
        let p = kb.intern("p");
        let vid = kb.fresh_var(p);
        let var_occ = NodeOccurrence::new_expr(Expr::Var(Var::Global(vid)), span(), None);
        let ctor = NodeOccurrence::new_expr(
            Expr::Constructor {
                name: edge,
                pos_args: vec![var_occ.clone(), var_occ],
                named_args: Vec::new(),
            },
            span(),
            None,
        );
        Value::Node(ctor)
    }

    /// Assert a ground `edge(from, to)` fact (both args nullary atoms).
    fn assert_edge(kb: &mut KnowledgeBase, sort: TermId, domain: TermId, from: &str, to: &str) -> RuleId {
        let edge = kb.intern("edge");
        let from_t = kb.make_name_term(from);
        let to_t = kb.make_name_term(to);
        let fact = kb.alloc(Term::Fn {
            functor: edge,
            pos_args: SmallVec::from_slice(&[from_t, to_t]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact, sort, domain, None)
    }

    /// The spike: a `no edge(?p, ?p)` guard whose condition is an OCCURRENCE leaf
    /// resolves through `resolve_goals` and is VIOLATED by a real self-loop fact
    /// (`edge(n1, n1)`) — never reported `Gated`. The shared `?p` is what makes
    /// the match a genuine self-loop check, not a blanket `edge` match.
    #[test]
    fn occurrence_self_loop_guard_violated_by_self_loop() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Graph");
        let domain = kb.make_name_term("test");
        assert_edge(&mut kb, sort, domain, "n1", "n1"); // a self-loop
        assert_edge(&mut kb, sort, domain, "n2", "n3"); // not a self-loop

        let leaf = edge_self_loop_occurrence(&mut kb);
        let query = no_q_guard(&mut kb, leaf);
        kb.add_guard_labeled(query, Some("no_self_loop".to_string()));

        assert_eq!(
            kb.check_all_guards(),
            vec![GuardCheck::Violated(Some("no_self_loop".to_string()))],
            "an occurrence self-loop leaf must RESOLVE and be violated by edge(n1, n1)",
        );
    }

    /// The exclusion half: with only a NON-self-loop fact (`edge(n2, n3)`), the same
    /// occurrence guard `no edge(?p, ?p)` resolves to zero matches and HOLDS — the
    /// shared `?p` correctly excludes `edge(n2, n3)`.
    #[test]
    fn occurrence_self_loop_guard_holds_without_self_loop() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Graph");
        let domain = kb.make_name_term("test");
        assert_edge(&mut kb, sort, domain, "n2", "n3"); // not a self-loop

        let leaf = edge_self_loop_occurrence(&mut kb);
        let query = no_q_guard(&mut kb, leaf);
        kb.add_guard_labeled(query, Some("no_self_loop".to_string()));

        assert_eq!(
            kb.check_all_guards(),
            vec![GuardCheck::Holds],
            "an occurrence self-loop leaf must exclude edge(n2, n3) and hold",
        );
    }

    /// The per-assert runtime path (the one that USED to panic on an occurrence
    /// guard): with the `no edge(?p, ?p)` guard wired to the `Graph` sort,
    /// `assert_checked` of a self-loop fact resolves the occurrence guard, finds the
    /// just-inserted self-loop, and REJECTS the fact (returns `None`) — enforcing
    /// the invariant rather than panicking.
    #[test]
    fn occurrence_guard_enforced_at_assert_checked() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Graph");
        let domain = kb.make_name_term("test");

        let leaf = edge_self_loop_occurrence(&mut kb);
        let query = no_q_guard(&mut kb, leaf);
        let cid = kb.add_guard_labeled(query, Some("no_self_loop".to_string()));
        // The synthetic occurrence query carries no resolvable trigger sort, so wire
        // the guard to the asserted fact's sort by hand (the per-assert lookup keys
        // on `guards_by_sort`).
        kb.guards_by_sort.entry(sort).or_default().push(cid.index());

        let edge = kb.intern("edge");
        let n1 = kb.make_name_term("n1");
        let self_loop = kb.alloc(Term::Fn {
            functor: edge,
            pos_args: SmallVec::from_slice(&[n1, n1]),
            named_args: SmallVec::new(),
        });
        let rid = kb.assert_checked(self_loop, sort, domain, None);
        assert!(
            rid.is_none(),
            "asserting a self-loop under `no edge(?p, ?p)` must be rejected (None), not panic",
        );
    }

    /// A term-leaf guard is unaffected: `no_q` with no matching facts holds.
    /// Guards against the carrier-neutral port regressing ordinary term constraints.
    #[test]
    fn term_leaf_guard_still_evaluates() {
        let mut kb = KnowledgeBase::new();
        // A hash-consed TermId leaf (a nullary `widget` atom) — never matched by
        // any fact, so `no_q` holds.
        let widget = kb.intern("widget");
        let leaf_term = kb.alloc(Term::Fn {
            functor: widget,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let query = no_q_guard(&mut kb, Value::Term(leaf_term));
        kb.add_guard_labeled(query, Some("term_constraint".to_string()));

        assert_eq!(
            kb.check_all_guards(),
            vec![GuardCheck::Holds],
            "a term-leaf `no_q` with no matching facts must hold",
        );
    }

    /// `lower_logical_query`'s RECURSIVE `conjunction` arm threads goal `Value`s
    /// carrier-neutrally: a term leaf on the left, an occurrence leaf on the right.
    /// Both must lower and resolve — with a matching `flag()` fact and a self-loop
    /// `edge(n1, n1)`, the conjunction succeeds and the `no_q` is violated. (The
    /// WI-514 gate used to refuse the whole conjunction for the occurrence leaf.)
    #[test]
    fn conjunction_with_occurrence_leaf_resolves() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Graph");
        let domain = kb.make_name_term("test");
        assert_edge(&mut kb, sort, domain, "n1", "n1");
        // A nullary `flag()` fact for the term-leaf side.
        let flag = kb.intern("flag");
        let flag_fact = kb.alloc(Term::Fn {
            functor: flag,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(flag_fact, sort, domain, None);

        let no_q = lq_ctor(&mut kb, "no_q");
        let condition = kb.intern("condition");
        let body = kb.intern("body");
        let conjunction = lq_ctor(&mut kb, "conjunction");
        let left = kb.intern("left");
        let right = kb.intern("right");
        let pattern_query = lq_ctor(&mut kb, "pattern_query");
        let term = kb.intern("term");
        let empty_query = lq_ctor(&mut kb, "empty_query");

        // Left: a hash-consed `flag()` term leaf.
        let flag_leaf = kb.alloc(Term::Fn {
            functor: flag,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let pq_term = Value::Entity {
            functor: pattern_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(term, Value::Term(flag_leaf))]),
        };
        // Right: the occurrence self-loop leaf.
        let pq_occ = Value::Entity {
            functor: pattern_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(term, edge_self_loop_occurrence(&mut kb))]),
        };
        let conj = Value::Entity {
            functor: conjunction,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(left, pq_term), (right, pq_occ)]),
        };
        let empty = Value::Entity {
            functor: empty_query,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let query = Value::Entity {
            functor: no_q,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(condition, conj), (body, empty)]),
        };
        kb.add_guard_labeled(query, Some("conj_constraint".to_string()));

        assert_eq!(
            kb.check_all_guards(),
            vec![GuardCheck::Violated(Some("conj_constraint".to_string()))],
            "a conjunction mixing a term leaf and an occurrence leaf must resolve and be violated",
        );
    }
}
