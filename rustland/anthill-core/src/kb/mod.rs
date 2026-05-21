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
pub mod op_info;
pub mod op_requirements;
pub mod req_insertion;
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
use crate::span::SourceRegistry;
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
    term: TermId,
    #[allow(dead_code)]
    kind: GuardKind,
    #[allow(dead_code)]
    trigger_sorts: Vec<TermId>,
}

// ── Rule entry ──────────────────────────────────────────────────

struct RuleEntry {
    head: TermId,
    body: Vec<TermId>,
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
    /// (they remain reachable through `by_functor` on the head).
    label: Option<Symbol>,
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

pub struct KnowledgeBase {
    // Term storage (hash-consed, refcounted)
    pub(crate) terms: TermStore,
    pub(crate) symbols: SymbolTable,

    // Rules (facts are rules with empty body)
    rules: Vec<RuleEntry>,

    // Indexes — all maintained atomically by assert/retract
    by_sort: HashMap<TermId, Vec<RuleId>>,
    by_functor: HashMap<Symbol, Vec<RuleId>>,
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
    /// Populated by the loader alongside the existing Handle-wrapped
    /// `OperationInfo.body` fact field; consumer migration to read this
    /// rather than the Handle path is filed as WI-247.
    /// See `docs/design/occurrence-as-value-type.md`.
    pub(crate) op_bodies: HashMap<Symbol, Rc<NodeOccurrence>>,

    // Entity field type registry: functor symbol → [(field_name, type_term)].
    // Populated during load_entity, used by type_check_sorts.
    entity_field_types: HashMap<Symbol, Vec<(Symbol, TermId)>>,

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

    // WI-226 Cache B — memoized spec-op SLD dispatch results, keyed by
    // `(SortGoal, scope)`. Saves re-walking `SortProvidesInfo` for
    // repeated spec-op calls at the same (spec, bindings, scope) — common
    // in bodies that call `eq(a, b); eq(c, d); …` at the same T.
    //
    // The scope is captured as `Vec<RequiresEntry>` in the key, so calls
    // from different enclosing sorts don't collide. Within one body the
    // scope is fixed and the key effectively reduces to the goal.
    //
    // Same lifetime caveat as Cache A: callers asserting new
    // `SortProvidesInfo` post-typing must call
    // `invalidate_resolve_cache`.
    pub(crate) resolve_cache: RefCell<
        HashMap<
            (crate::kb::typing::SortGoal, Vec<crate::kb::typing::RequiresEntry>),
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
            rules: Vec::new(),
            by_sort: HashMap::new(),
            by_functor: HashMap::new(),
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
            entity_field_types: HashMap::new(),
            resolved_requires_facts: HashSet::new(),
            sources: SourceRegistry::new(),
            routes: route::RouteRegistry::new(),
            dispatch_rewrites: HashMap::new(),
            dispatch_origin: HashMap::new(),
            requires_chain_cache: RefCell::new(HashMap::new()),
            requires_tree_cache: RefCell::new(HashMap::new()),
            synth_req_names_cache: RefCell::new(HashMap::new()),
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
    /// variables in the head.
    ///
    pub fn assert_rule(
        &mut self,
        head: TermId,
        body: Vec<TermId>,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        // Note: builtins always take precedence over rules at resolution time
        // (checked first in step_init), so rules with builtin functors are
        // allowed but effectively shadowed during resolution.

        let rule_id = RuleId(self.rules.len() as u32);

        // Incref on all referenced terms
        self.terms.incref(head);
        self.terms.incref(sort);
        self.terms.incref(domain);
        if let Some(m) = meta {
            self.terms.incref(m);
        }
        for &b in &body {
            self.terms.incref(b);
        }

        self.rules.push(RuleEntry {
            head,
            body,
            sort,
            domain,
            meta,
            retracted: false,
            arity: 0,
            globals: Vec::new(),
            shared_arity: 0,
            label: None,
        });

        // Update indexes
        self.by_sort.entry(sort).or_default().push(rule_id);

        // Index by domain
        self.by_domain.entry(domain).or_default().push(rule_id);

        // Index by top-level functor
        if let Term::Fn { functor, .. } = *self.terms.get(head) {
            self.by_functor.entry(functor).or_default().push(rule_id);
        }

        // WI-233: ground-fact dedup index. Inserted only for body-empty
        // entries — rules with a body are matched structurally via the
        // discrim tree, not exact-equality. We do not overwrite an
        // existing entry; the dedup check in `assert_fact` upstream
        // routes duplicates to the existing RuleId before we get here.
        if self.rules[rule_id.index()].body.is_empty() {
            self.fact_dedup.entry((head, sort, domain)).or_insert(rule_id);
        }

        // Discrimination tree index (insert_pattern handles vars in head)
        self.discrim.insert_pattern(&self.terms, head, rule_id);

        rule_id
    }

    // ── Guards ───────────────────────────────────────────────────

    /// Register a guard on the KB. Trigger sorts are auto-extracted from
    /// the LogicalQuery tree.
    pub fn add_guard(&mut self, guard_term: TermId) -> ConstraintId {
        let trigger_sorts = self.extract_trigger_sorts(guard_term);
        let id = ConstraintId(self.guards.len() as u32);
        self.terms.incref(guard_term);
        for &s in &trigger_sorts {
            self.guards_by_sort.entry(s).or_default().push(id.index());
        }
        self.guards.push(Guard {
            id,
            term: guard_term,
            kind: GuardKind::General,
            trigger_sorts,
        });
        id
    }

    /// Empty if reflect stdlib not loaded — guard then triggers on no sorts.
    fn extract_trigger_sorts(&mut self, guard_term: TermId) -> Vec<TermId> {
        let syms = execute::LogicalQuerySymbols::resolve(self);
        let mut out = Vec::new();
        self.collect_trigger_sorts(guard_term, &syms, &mut out);
        out
    }

    fn collect_trigger_sorts(
        &mut self,
        term: TermId,
        syms: &execute::LogicalQuerySymbols,
        out: &mut Vec<TermId>,
    ) {
        let (functor, named, pos) = match self.terms.get(term) {
            Term::Fn { functor, named_args, pos_args } => {
                (*functor, named_args.clone(), pos_args.clone())
            }
            _ => return,
        };

        if Some(functor) == syms.pattern_query {
            let inner = named.iter()
                .find(|(s, _)| *s == syms.term)
                .map(|(_, t)| *t);
            if let Some(inner_tid) = inner {
                if let Some(sort) = self.term_to_trigger_sort(inner_tid) {
                    if !out.contains(&sort) {
                        out.push(sort);
                    }
                }
            }
            return;
        }

        if Some(functor) == syms.sort_query {
            let name = named.iter()
                .find(|(s, _)| *s == syms.sort_name)
                .and_then(|(_, t)| match self.terms.get(*t) {
                    Term::Const(term::Literal::String(s)) => Some(s.clone()),
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

        for (_, t) in &named {
            self.collect_trigger_sorts(*t, syms, out);
        }
        for &t in &pos {
            self.collect_trigger_sorts(t, syms, out);
        }
    }

    fn term_to_trigger_sort(&mut self, t: TermId) -> Option<TermId> {
        let functor = match self.terms.get(t) {
            Term::Fn { functor, .. } => *functor,
            Term::Ref(s) => *s,
            _ => return None,
        };
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

        // General path: insert tentatively, check guards, retract on failure
        let rule_id = self.assert_fact(term, sort, domain, meta);

        for &idx in &guard_indices {
            let guard_term = self.guards[idx].term;
            if !self.evaluate_guard(guard_term) {
                self.retract(rule_id);
                return None;
            }
        }

        Some(rule_id)
    }

    /// Evaluate a LogicalQuery guard term. Returns true if the guard holds.
    fn evaluate_guard(&mut self, guard_term: TermId) -> bool {
        let term = self.terms.get(guard_term).clone();
        match term {
            Term::Fn { functor, named_args, .. } => {
                let name = self.resolve_sym(functor);
                match name {
                    "lone_q" => self.eval_count_guard(&named_args, 0, 1),
                    "one_q" => self.eval_count_guard(&named_args, 1, 1),
                    "some_q" => self.eval_count_guard(&named_args, 1, usize::MAX),
                    "no_q" => self.eval_count_guard(&named_args, 0, 0),
                    "forall_q" => self.eval_forall_guard(&named_args),
                    "negation" => self.eval_negation_guard(&named_args),
                    _ => true, // unknown guard kind: vacuously true
                }
            }
            _ => true,
        }
    }

    /// Evaluate a counting quantifier guard (lone_q, one_q, some_q, no_q).
    /// Named args: (var: Symbol, condition: LogicalQuery, body: LogicalQuery)
    fn eval_count_guard(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
        min: usize,
        max: usize,
    ) -> bool {
        // Extract condition and body from named args
        let condition = named_args.iter()
            .find(|(s, _)| self.resolve_sym(*s) == "condition")
            .map(|(_, t)| *t);
        let body = named_args.iter()
            .find(|(s, _)| self.resolve_sym(*s) == "body")
            .map(|(_, t)| *t);

        // Lower condition + body to resolution goals
        let mut goals = Vec::new();
        if let Some(cond) = condition {
            goals.extend(self.lower_logical_query(cond));
        }
        if let Some(b) = body {
            let body_goals = self.lower_logical_query(b);
            // empty_query produces no goals — treat as trivially true
            goals.extend(body_goals);
        }

        if goals.is_empty() {
            // No goals means trivially satisfied; count depends on context
            return min == 0;
        }

        let config = resolve::ResolveConfig {
            max_solutions: max + 1, // one extra to detect overflow
            ..resolve::ResolveConfig::default()
        };
        let solutions = self.resolve(&goals, &config);
        let count = solutions.len();
        count >= min && count <= max
    }

    /// Evaluate forall_q(var, condition, body): condition AND body must hold
    /// for all solutions. Equivalent to: no solutions of (condition AND NOT body).
    fn eval_forall_guard(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> bool {
        let condition = named_args.iter()
            .find(|(s, _)| self.resolve_sym(*s) == "condition")
            .map(|(_, t)| *t);
        let body = named_args.iter()
            .find(|(s, _)| self.resolve_sym(*s) == "body")
            .map(|(_, t)| *t);

        // forall x: P -: Q ≡ no x: P -: not(Q)
        // Check: condition goals + negation of body goals must have no solutions
        let mut goals = Vec::new();
        if let Some(c) = condition {
            goals.extend(self.lower_logical_query(c));
        }
        if let Some(b) = body {
            let body_goals = self.lower_logical_query(b);
            if !body_goals.is_empty() {
                // Negate the body: build not(body_goal) for each
                let not_sym = self.intern("not");
                for g in body_goals {
                    let not_term = self.alloc(Term::Fn {
                        functor: not_sym,
                        pos_args: SmallVec::from_elem(g, 1),
                        named_args: SmallVec::new(),
                    });
                    goals.push(not_term);
                }
            }
        }

        if goals.is_empty() {
            return true;
        }

        // If any solution exists, the forall is violated
        let config = resolve::ResolveConfig {
            max_solutions: 1,
            ..resolve::ResolveConfig::default()
        };
        let solutions = self.resolve(&goals, &config);
        solutions.is_empty()
    }

    /// Evaluate negation(query): the inner query must have no solutions.
    fn eval_negation_guard(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> bool {
        // negation has a single positional arg or named "query"
        let inner = named_args.iter()
            .find(|(s, _)| self.resolve_sym(*s) == "query")
            .map(|(_, t)| *t);

        if let Some(inner_term) = inner {
            let goals = self.lower_logical_query(inner_term);
            if goals.is_empty() {
                return false; // negation of empty_query (always true) = false
            }
            let config = resolve::ResolveConfig {
                max_solutions: 1,
                ..resolve::ResolveConfig::default()
            };
            let solutions = self.resolve(&goals, &config);
            solutions.is_empty() // negation holds if no solutions
        } else {
            true
        }
    }

    /// Convert a LogicalQuery term to resolution goals.
    fn lower_logical_query(&mut self, lq_term: TermId) -> Vec<TermId> {
        let term = self.terms.get(lq_term).clone();
        match term {
            Term::Fn { functor, pos_args, named_args } => {
                let name = self.resolve_sym(functor).to_string();
                match name.as_str() {
                    "pattern_query" => {
                        let pattern = named_args.iter()
                            .find(|(s, _)| self.resolve_sym(*s) == "term")
                            .map(|(_, t)| *t)
                            .or_else(|| pos_args.first().copied());
                        pattern.into_iter().collect()
                    }
                    "conjunction" => {
                        let left = named_args.iter()
                            .find(|(s, _)| self.resolve_sym(*s) == "left")
                            .map(|(_, t)| *t);
                        let right = named_args.iter()
                            .find(|(s, _)| self.resolve_sym(*s) == "right")
                            .map(|(_, t)| *t);
                        let mut goals = Vec::new();
                        if let Some(l) = left { goals.extend(self.lower_logical_query(l)); }
                        if let Some(r) = right { goals.extend(self.lower_logical_query(r)); }
                        goals
                    }
                    "empty_query" => Vec::new(),
                    "negation" => {
                        let inner = named_args.iter()
                            .find(|(s, _)| self.resolve_sym(*s) == "query")
                            .map(|(_, t)| *t);
                        if let Some(inner_term) = inner {
                            let inner_goals = self.lower_logical_query(inner_term);
                            if inner_goals.is_empty() {
                                return Vec::new();
                            }
                            if inner_goals.len() == 1 {
                                let not_sym = self.intern("not");
                                let not_term = self.alloc(Term::Fn {
                                    functor: not_sym,
                                    pos_args: SmallVec::from_slice(&inner_goals),
                                    named_args: SmallVec::new(),
                                });
                                vec![not_term]
                            } else {
                                // Multiple goals: negate as conjunction
                                // TODO: proper conjunction wrapping
                                inner_goals
                            }
                        } else {
                            Vec::new()
                        }
                    }
                    _ => vec![lq_term],
                }
            }
            _ => vec![lq_term],
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

    /// Mark a rule/fact as retracted. Removes from active indexes, decrements refcounts.
    pub fn retract(&mut self, id: RuleId) {
        let entry = &mut self.rules[id.index()];
        if entry.retracted {
            return;
        }
        entry.retracted = true;

        let head = entry.head;
        let sort = entry.sort;
        let domain = entry.domain;
        let meta = entry.meta;
        let body: Vec<TermId> = entry.body.clone();
        let label = entry.label;

        // Remove from indexes
        if let Some(v) = self.by_sort.get_mut(&sort) {
            v.retain(|&rid| rid != id);
        }
        if let Some(v) = self.by_domain.get_mut(&domain) {
            v.retain(|&rid| rid != id);
        }
        if let Term::Fn { functor, .. } = *self.terms.get(head) {
            if let Some(v) = self.by_functor.get_mut(&functor) {
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
        if body.is_empty() {
            if let std::collections::hash_map::Entry::Occupied(e) =
                self.fact_dedup.entry((head, sort, domain))
            {
                if *e.get() == id {
                    e.remove();
                }
            }
        }

        // Remove from discrimination tree (before releasing terms)
        self.discrim.remove_ground(&self.terms, head, &id);

        // Release refcounts
        self.terms.release(head);
        self.terms.release(sort);
        self.terms.release(domain);
        if let Some(m) = meta {
            self.terms.release(m);
        }
        for b in body {
            self.terms.release(b);
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
        if let Term::Fn { functor, .. } = *self.terms.get(entity) {
            self.constructor_symbols.insert(functor);
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
            if let Term::Fn { functor: f, .. } = *self.terms.get(entity_tid) {
                if f == functor {
                    return Some(parent_tid);
                }
            }
        }
        None
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
    /// Remove `id` from the `by_functor` head index without
    /// retracting the rule. The rule still exists in the KB —
    /// reachable by `try_resolve_symbol` (for cite-resolution),
    /// `by_sort`, `by_domain`, and direct `RuleId` access — but
    /// SLD's `by_functor`-driven goal resolution will not consult
    /// it.
    ///
    /// Used for opt-in equational rules per WI-139: equational
    /// laws (head is an `=` application) without a `[simp]` /
    /// `[unfold]` attribute are cite-required only and must not
    /// drive automatic SLD rewriting (which would loop on rules
    /// like `add_comm: add(a, b) = add(b, a)`).
    pub fn unindex_functor(&mut self, id: RuleId) {
        let head = self.rules[id.index()].head;
        if let Term::Fn { functor, .. } = *self.terms.get(head) {
            if let Some(v) = self.by_functor.get_mut(&functor) {
                v.retain(|&rid| rid != id);
            }
        }
    }

    pub fn by_functor(&self, sym: Symbol) -> Vec<RuleId> {
        self.by_functor
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

    /// Get the head term of a rule.
    pub fn rule_head(&self, id: RuleId) -> TermId {
        self.rules[id.index()].head
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

    /// Get the body literals of a rule (empty for ground facts).
    pub fn rule_body(&self, id: RuleId) -> &[TermId] {
        &self.rules[id.index()].body
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
    fn canonical_sort_sym(&self, sym: Symbol) -> Symbol {
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
        self.rules.iter().filter(|r| !r.retracted && r.body.is_empty()).count()
    }

    /// Number of active (non-retracted) entries with non-empty body (proper rules).
    pub fn rule_count(&self) -> usize {
        self.rules.iter().filter(|r| !r.retracted && !r.body.is_empty()).count()
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
        tree.insert_pattern(&self.terms, pattern, ());
        let results = tree.query_resolved(self, target, |_| pattern);
        results.into_iter()
            .map(|(_, s)| s)
            .find(|s| !s.is_contradiction())
    }

    /// Find all active rules/facts whose head matches the given pattern.
    ///
    /// Uses the discrimination tree for multi-level structural dispatch.
    /// Variable bindings are resolved via path extraction from head terms.
    pub fn query(&self, pattern: TermId) -> Vec<(RuleId, subst::Substitution)> {
        let rules = &self.rules;
        let pattern_view = term_view::TermIdView(pattern);
        let candidates = self.discrim.query_resolved(
            self,
            &pattern_view,
            |rid: &RuleId| rules[rid.index()].head,
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
        results.sort_by_key(|(rid, _)| if rules[rid.index()].body.is_empty() { 0 } else { 1 });
        results
    }

    /// Find all active rules (non-empty body) whose head matches the pattern.
    pub fn query_rules(&self, pattern: TermId) -> Vec<(RuleId, subst::Substitution)> {
        self.query(pattern)
            .into_iter()
            .filter(|(rid, _)| !self.rules[rid.index()].body.is_empty())
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

    /// Collect all vars from a rule's head + body.
    fn collect_rule_vars(&self, head: TermId, body: &[TermId]) -> Vec<VarId> {
        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        self.collect_vars_rec(head, &mut vars, &mut seen);
        for &b in body {
            self.collect_vars_rec(b, &mut vars, &mut seen);
        }
        vars
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
            Term::Var(Var::Global(vid)) => subst.resolve_with_term(vid).unwrap_or(term),
            Term::Var(Var::DeBruijn(_)) => term,
            Term::Fn { .. } => self.map_fn_children(term, |kb, id| kb.apply_subst(id, subst)),
            _ => term,
        }
    }

    // ── Walk / reify ──────────────────────────────────────────────

    /// Chase Var→binding→Var chains through a substitution.
    /// Returns the final non-variable TermId, or the last unbound Var.
    pub fn walk(&self, term: TermId, subst: &subst::Substitution) -> TermId {
        let mut current = term;
        loop {
            match self.terms.get(current) {
                Term::Var(Var::Global(vid)) => {
                    if let Some(bound) = subst.resolve_with_term(*vid) {
                        if bound == current {
                            return current; // self-referential, stop
                        }
                        current = bound;
                    } else {
                        return current;
                    }
                }
                _ => return current,
            }
        }
    }

    /// Deep walk — recursively chase all vars through the substitution,
    /// rebuilding the term with concrete bindings. Unlike `apply_subst`
    /// which doesn't chase transitive variable chains.
    pub fn reify(&mut self, term: TermId, subst: &subst::Substitution) -> TermId {
        let walked = self.walk(term, subst);
        match self.terms.get(walked) {
            Term::Var(_) => walked,
            Term::Fn { .. } => self.map_fn_children(walked, |kb, id| kb.reify(id, subst)),
            _ => walked,
        }
    }

    // ── De Bruijn conversion ────────────────────────────────────

    /// Convert a rule's head and body from Global vars to DeBruijn indices.
    /// Called after loading a rule. Sets the rule's arity.
    /// `var_order`: free variables in order of first occurrence (from collect_rule_vars).
    /// Convention: first var = highest index (outermost binder).
    /// Convert head and body terms to de Bruijn BEFORE asserting.
    /// Returns (new_head, new_body, arity).
    pub fn terms_to_debruijn(
        &mut self,
        head: TermId,
        body: &[TermId],
    ) -> (TermId, Vec<TermId>, u32) {
        let vars = if body.is_empty() {
            self.collect_vars(head)
        } else {
            self.collect_rule_vars(head, body)
        };

        if vars.is_empty() {
            return (head, body.to_vec(), 0);
        }

        let new_head = self.term_to_debruijn(head, &vars);
        let new_body: Vec<TermId> = body.iter()
            .map(|&b| self.term_to_debruijn(b, &vars))
            .collect();
        (new_head, new_body, vars.len() as u32)
    }

    /// Free vars in head ∪ body (ordered for DeBruijn assignment).
    /// Ground-fact case (empty body) skips the rule-vars merge.
    fn collect_head_body_vars(&self, head: TermId, body: &[TermId]) -> Vec<VarId> {
        if body.is_empty() {
            self.collect_vars(head)
        } else {
            self.collect_rule_vars(head, body)
        }
    }

    /// Assert a rule with de Bruijn conversion applied.
    pub fn assert_rule_debruijn(
        &mut self,
        head: TermId,
        body: Vec<TermId>,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        let vars = self.collect_head_body_vars(head, &body);
        self.finalize_rule_debruijn(head, body, vars, 0, sort, domain, meta)
    }

    /// Shared epilogue for both DeBruijn-asserting paths: convert
    /// head/body against `vars` (in-place when non-empty), insert as
    /// a Rule, save `arity`, `shared_arity`, and `globals` on the
    /// entry. Vars list ordering convention follows
    /// `term_to_debruijn`'s reverse mapping (last entry → DeBruijn 0).
    #[allow(clippy::too_many_arguments)]
    fn finalize_rule_debruijn(
        &mut self,
        head: TermId,
        body: Vec<TermId>,
        vars: Vec<VarId>,
        shared_arity: u32,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        let arity = vars.len() as u32;
        let (db_head, db_body) = if vars.is_empty() {
            (head, body)
        } else {
            let new_head = self.term_to_debruijn(head, &vars);
            let new_body: Vec<TermId> = body.iter()
                .map(|&b| self.term_to_debruijn(b, &vars))
                .collect();
            (new_head, new_body)
        };
        let rule_id = self.assert_rule(db_head, db_body, sort, domain, meta);
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
        self.by_functor(sym).first().copied()
    }

    /// All rule ids that resolve to `qn` — label-first, then
    /// by_functor fallback. Labeled multi-head rules
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
        self.by_functor(sym)
    }

    /// Citation handle for labeled rules. `None` for unlabeled rules
    /// (those resolve via `by_functor` on the head).
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

    /// Assert a rule using a CALLER-PROVIDED Global VarIds list as
    /// the DeBruijn frame (proposal 031). The terms are
    /// reindexed against `vars` rather than recomputed from the
    /// rule's own free vars; any Global VarId NOT in `vars` is
    /// appended in first-seen order. Used by `dispatch_structured`
    /// to synthesize step rules in the parent's variable frame so
    /// shared variable names produce identical DeBruijn indices
    /// (and therefore identical `var_<i>` SMT names) across the
    /// parent rule and every step's cited-rule lift.
    pub fn assert_rule_debruijn_in_frame(
        &mut self,
        head: TermId,
        body: Vec<TermId>,
        seed_globals: &[VarId],
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        // `term_to_debruijn` maps positions in reverse (last entry →
        // DeBruijn 0). Parent's seed must stay at the TAIL so its
        // shared vars retain DeBruijn 0..seed_len-1 (matching the
        // parent's own assignment); step-introduced vars are
        // prepended.
        let seen: std::collections::HashSet<u32> =
            seed_globals.iter().map(|v| v.raw()).collect();
        let mut vars = self.collect_head_body_vars(head, &body);
        vars.retain(|v| !seen.contains(&v.raw()));
        vars.extend(seed_globals.iter().copied());

        let shared_arity = seed_globals.len() as u32;
        self.finalize_rule_debruijn(head, body, vars, shared_arity, sort, domain, meta)
    }

    /// Number of leading DeBruijn slots that are shared with a parent
    /// rule's frame. Zero for ordinary rules; positive for
    /// step rules synthesized via `assert_rule_debruijn_in_frame`.
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

    /// Check if a rule is an equation: head functor is "eq" with 2 positional
    /// args and body is empty.
    pub fn is_equation(&self, id: RuleId) -> bool {
        let entry = &self.rules[id.index()];
        if !entry.body.is_empty() || entry.retracted {
            return false;
        }
        match self.terms.get(entry.head) {
            Term::Fn { functor, pos_args, .. } => {
                self.symbols.name(*functor) == "eq" && pos_args.len() == 2
            }
            _ => false,
        }
    }

    /// Create a fresh copy of a rule's head and body with all variables renamed
    /// to fresh VarIds. Returns `(new_head, new_body)`.
    pub fn standardize_apart(&mut self, id: RuleId) -> (TermId, Vec<TermId>) {
        let head = self.rules[id.index()].head;
        let body = self.rules[id.index()].body.clone();
        let all_vars = self.collect_rule_vars(head, &body);

        // Build a renaming substitution
        let mut rename = subst::Substitution::new();
        for vid in all_vars {
            let fresh = self.fresh_var(vid.name());
            let fresh_term = self.alloc(Term::Var(Var::Global(fresh)));
            rename.bind(vid, fresh_term);
        }

        let new_head = self.apply_subst(head, &rename);
        let new_body: Vec<TermId> = body
            .iter()
            .map(|&b| self.apply_subst(b, &rename))
            .collect();

        (new_head, new_body)
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
    /// Returns `(fresh_body, answer_links)` where `answer_links` maps
    /// query variables to their fresh counterparts (or concrete values).
    pub fn with_fresh_vars(
        &mut self,
        id: RuleId,
        tree_subst: &subst::Substitution,
    ) -> (Vec<TermId>, subst::Substitution) {
        let arity = self.rules[id.index()].arity;
        let head = self.rules[id.index()].head;
        let body = self.rules[id.index()].body.clone();

        if arity > 0 {
            // De Bruijn path: allocate N fresh vars, open DeBruijn to Global
            let name_sym = self.intern("_");
            let fresh_vars: Vec<VarId> = (0..arity)
                .map(|_| self.fresh_var(name_sym))
                .collect();

            // Open head and body
            let _fresh_head = self.term_from_debruijn(head, &fresh_vars);
            let fresh_body: Vec<TermId> = body.iter()
                .map(|&b| self.term_from_debruijn(b, &fresh_vars))
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
                        body_rename.bind(fresh_vid, bound_term);
                    }
                } else {
                    let opened = self.term_from_debruijn(bound_term, &fresh_vars);
                    answer_links.bind(ts_vid, opened);
                }
            }

            // Apply rename to body: replace fresh vars with concrete values
            // from the head match. Unmatched fresh vars stay as variables
            // (will be bound during body resolution).
            let final_body = if body_rename.bindings.is_empty() {
                fresh_body
            } else {
                fresh_body.iter()
                    .map(|&b| self.apply_subst(b, &body_rename))
                    .collect()
            };

            (final_body, answer_links)
        } else {
            // Legacy path: Global vars (ground facts or rules not yet converted)
            let all_vars = self.collect_rule_vars(head, &body);

            let mut rename = subst::Substitution::new();
            for vid in &all_vars {
                if let Some(bound) = tree_subst.resolve_with_term(*vid) {
                    if !matches!(self.terms.get(bound), Term::Var(_)) {
                        rename.bind(*vid, bound);
                        continue;
                    }
                }
                let fresh = self.fresh_var(vid.name());
                let fresh_term = self.alloc(Term::Var(Var::Global(fresh)));
                rename.bind(*vid, fresh_term);
            }

            let fresh_body: Vec<TermId> = body
                .iter()
                .map(|&b| self.apply_subst(b, &rename))
                .collect();

            let mut answer_links = subst::Substitution::new();
            for (ts_vid, bound_term) in tree_subst.iter_terms() {
                if all_vars.contains(&ts_vid) {
                    continue;
                }
                match self.terms.get(bound_term) {
                    Term::Var(Var::Global(rule_vid)) => {
                        let rule_vid = *rule_vid;
                        if let Some(renamed) = rename.resolve_with_term(rule_vid) {
                            answer_links.bind(ts_vid, renamed);
                        }
                    }
                    _ => {
                        let renamed_term = self.apply_subst(bound_term, &rename);
                        answer_links.bind(ts_vid, renamed_term);
                    }
                }
            }

            (fresh_body, answer_links)
        }
    }

    /// Apply a substitution to each goal in a list, returning new goal terms.
    ///
    /// Used to propagate concrete bindings from a ground fact match to
    /// remaining goals.
    pub fn apply_subst_each(
        &mut self,
        goals: &[TermId],
        subst: &subst::Substitution,
    ) -> Vec<TermId> {
        goals.iter().map(|&g| self.apply_subst(g, subst)).collect()
    }

    // ── Helpers ─────────────────────────────────────────────────

    /// Convenience: allocate a nullary functor term (name with no args).
    pub fn make_name_term(&mut self, name: &str) -> TermId {
        let sym = self.symbols.intern(name);
        self.terms.alloc(Term::Fn {
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
            _ => None,
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
    pub fn make_name_term_from_sym(&mut self, sym: Symbol) -> TermId {
        self.terms.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
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
            args.sort_by_key(|(s, _)| s.index());
            list = self.alloc(Term::Fn {
                functor: cons_sym,
                pos_args: SmallVec::new(),
                named_args: args,
            });
        }
        list
    }

    // ── Type term constructors (anthill.prelude.Type entities) ───

    /// sort_ref(name: <sym>) — reference to a named sort.
    pub fn make_sort_ref(&mut self, sort_sym: Symbol) -> TermId {
        let sort_ref_sym = self.resolve_symbol("anthill.prelude.Type.sort_ref");
        let name_key = self.intern("name");
        let name_val = self.alloc(Term::Ref(sort_sym));
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((name_key, name_val));
        self.alloc(Term::Fn {
            functor: sort_ref_sym,
            pos_args: SmallVec::new(),
            named_args,
        })
    }

    /// Convenience: sort_ref from a name string (resolves or interns the name).
    pub fn make_sort_ref_by_name(&mut self, name: &str) -> TermId {
        let sym = if let Some(s) = self.try_resolve_symbol(name) { s } else { self.intern(name) };
        self.make_sort_ref(sym)
    }

    /// parameterized(base: <type>, bindings: List[TypeBinding]).
    pub fn make_parameterized_type(&mut self, base: TermId, bindings: &[(Symbol, TermId)]) -> TermId {
        let parameterized_sym = self.resolve_symbol("anthill.prelude.Type.parameterized");
        let type_binding_sym = self.resolve_symbol("anthill.prelude.Type.TypeBinding");
        let base_key = self.intern("base");
        let bindings_key = self.intern("bindings");
        let param_key = self.intern("param");
        let value_key = self.intern("value");

        let binding_terms: Vec<TermId> = bindings.iter().map(|(param_sym, value_term)| {
            let param_ref = self.alloc(Term::Ref(*param_sym));
            let mut args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            args.push((param_key, param_ref));
            args.push((value_key, *value_term));
            args.sort_by_key(|(s, _)| s.index());
            self.alloc(Term::Fn {
                functor: type_binding_sym,
                pos_args: SmallVec::new(),
                named_args: args,
            })
        }).collect();

        let bindings_list = self.build_list(&binding_terms);

        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((base_key, base));
        named_args.push((bindings_key, bindings_list));
        named_args.sort_by_key(|(s, _)| s.index());
        self.alloc(Term::Fn {
            functor: parameterized_sym,
            pos_args: SmallVec::new(),
            named_args,
        })
    }

    /// arrow(param: <type>, result: <type>, effects: List[Type]).
    pub fn make_arrow_type(&mut self, param: TermId, result: TermId, effects: &[TermId]) -> TermId {
        let arrow_sym = self.resolve_symbol("anthill.prelude.Type.arrow");
        let param_key = self.intern("param");
        let result_key = self.intern("result");
        let effects_key = self.intern("effects");

        let effects_list = self.build_list(effects);

        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((effects_key, effects_list));
        named_args.push((param_key, param));
        named_args.push((result_key, result));
        named_args.sort_by_key(|(s, _)| s.index());
        self.alloc(Term::Fn {
            functor: arrow_sym,
            pos_args: SmallVec::new(),
            named_args,
        })
    }

    /// type_var(name: <sym>) — a type variable for inference.
    pub fn make_type_var(&mut self, name: Symbol) -> TermId {
        let type_var_sym = self.resolve_symbol("anthill.prelude.Type.type_var");
        let name_key = self.intern("name");
        let name_val = self.alloc(Term::Ref(name));
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((name_key, name_val));
        self.alloc(Term::Fn {
            functor: type_var_sym,
            pos_args: SmallVec::new(),
            named_args,
        })
    }

    /// named_tuple(fields: List[TypeField]).
    pub fn make_named_tuple_type(&mut self, fields: &[(Symbol, TermId)]) -> TermId {
        let named_tuple_sym = self.resolve_symbol("anthill.prelude.Type.named_tuple");
        let type_field_sym = self.resolve_symbol("anthill.prelude.Type.TypeField");
        let fields_key = self.intern("fields");
        let name_key = self.intern("name");
        let type_key = self.intern("type");

        let field_terms: Vec<TermId> = fields.iter().map(|(field_name, field_type)| {
            let name_ref = self.alloc(Term::Ref(*field_name));
            let mut args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            args.push((name_key, name_ref));
            args.push((type_key, *field_type));
            args.sort_by_key(|(s, _)| s.index());
            self.alloc(Term::Fn {
                functor: type_field_sym,
                pos_args: SmallVec::new(),
                named_args: args,
            })
        }).collect();

        let fields_list = self.build_list(&field_terms);

        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((fields_key, fields_list));
        self.alloc(Term::Fn {
            functor: named_tuple_sym,
            pos_args: SmallVec::new(),
            named_args,
        })
    }

    /// nothing — bottom type.
    pub fn make_nothing_type(&mut self) -> TermId {
        let nothing_sym = self.resolve_symbol("anthill.prelude.Type.nothing");
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

    /// Register entity field types: functor → [(field_name, type_term)].
    pub fn register_entity_field_types(&mut self, functor: Symbol, fields: Vec<(Symbol, TermId)>) {
        self.entity_field_types.insert(functor, fields);
    }

    /// Look up the field types for an entity functor.
    pub fn entity_field_types(&self, functor: Symbol) -> Option<&[(Symbol, TermId)]> {
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
        self.register_builtin("anthill.reflect.field_access", BuiltinTag::FieldAccess);
        self.register_builtin("anthill.reflect.Expr.ho_apply", BuiltinTag::HoApply);
        // Resolver primitives (proposal 033)
        self.register_builtin("anthill.kernel.push_choice", BuiltinTag::PushChoice);
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

    /// Check if a goal term's functor is a registered builtin.
    /// Returns `Some(tag)` if so, `None` otherwise.
    pub fn get_builtin(&self, goal: TermId) -> Option<BuiltinTag> {
        match self.terms.get(goal) {
            Term::Fn { functor, .. } => self.builtins.get(functor).copied(),
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
        assert_eq!(s.resolve_with_term(vid), Some(target));
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
        assert!(subst.resolve_with_term(xv).is_none());
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
        assert!(subst.resolve_with_term(xv).is_none());
        assert!(subst.resolve_with_term(yv).is_none());
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

        assert_eq!(via_term.resolve_with_term(xv), via_view.resolve_with_term(xv));
        assert_eq!(via_term.resolve_with_term(xv), Some(a));
    }

    #[test]
    fn subst_term_replaces_name() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("T");
        let int = kb.make_name_term("Int");

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
        let int = kb.make_name_term("Int");
        let string = kb.make_name_term("String");

        // Substituting a name that doesn't appear should return the same term
        let result = kb.subst_term(t, int, string);
        assert_eq!(result, t);
    }

    #[test]
    fn subst_term_nested() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("T");
        let int = kb.make_name_term("Int");

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
        assert_eq!(s.resolve_with_term(vid), Some(alice));
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

        // rule_body should return the body
        assert_eq!(kb.rule_body(rid).len(), 2);
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
        s.bind(vid, val);
        let result = kb.apply_subst(term, &s);

        match kb.get_term(result) {
            Term::Fn { pos_args, .. } => {
                assert_eq!(pos_args[0], val);
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }

    #[test]
    fn standardize_apart_produces_fresh_vars() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");
        let g_sym = kb.intern("g");

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let head = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let body_lit = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let rid = kb.assert_rule(head, vec![body_lit], sort, domain, None);
        let (new_head, new_body) = kb.standardize_apart(rid);

        // Head and body should have a different variable
        assert_ne!(new_head, head);
        let head_vars = kb.collect_vars(new_head);
        assert_eq!(head_vars.len(), 1);
        assert_ne!(head_vars[0], vx);

        // Body should share the same fresh variable as head
        assert_eq!(new_body.len(), 1);
        let body_vars = kb.collect_vars(new_body[0]);
        assert_eq!(body_vars.len(), 1);
        assert_eq!(head_vars[0], body_vars[0]);
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
