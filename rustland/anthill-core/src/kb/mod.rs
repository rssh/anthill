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
pub(crate) mod persist_subst;
pub(crate) mod discrim;

use std::collections::HashMap;

use smallvec::SmallVec;

use crate::intern::{SymbolTable, SymbolDef, SymbolKind, Symbol};
use term::{Term, TermId, TermStore, VarId};
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
}

/// Backwards-compatible alias.
pub type FactId = RuleId;

// ── Rule entry ──────────────────────────────────────────────────

struct RuleEntry {
    head: TermId,
    body: Vec<TermId>,
    sort: TermId,
    domain: TermId,
    meta: Option<TermId>,
    retracted: bool,
}

// ── Sort kind ───────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SortKind {
    Abstract,
    Defined,
    Constructor,
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

    // Entity-of indexes: entity → parent sort (1-level, non-transitive).
    // Materialized indexes for EntityOf(entity, parent) facts.
    sort_entities: HashMap<TermId, Vec<TermId>>,   // sort → its entity constructors
    entity_parent: HashMap<TermId, TermId>,         // entity → its parent sort
    sort_info: HashMap<TermId, SortKind>,

    // Discrimination tree index for structural term matching
    discrim: SubstTree<RuleId>,

    // Builtin dispatch: functor symbol → builtin tag
    builtins: HashMap<Symbol, BuiltinTag>,

    // Entity field registry: functor symbol → ordered field names.
    // Populated during load_entity, used by convert_term for partial named-arg expansion.
    entity_fields: HashMap<Symbol, Vec<Symbol>>,

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
}

impl KnowledgeBase {
    pub fn new() -> Self {
        Self {
            terms: TermStore::new(),
            symbols: SymbolTable::new(),
            rules: Vec::new(),
            by_sort: HashMap::new(),
            by_functor: HashMap::new(),
            by_domain: HashMap::new(),
            sort_entities: HashMap::new(),
            entity_parent: HashMap::new(),
            sort_info: HashMap::new(),
            discrim: SubstTree::new(),
            builtins: HashMap::new(),
            entity_fields: HashMap::new(),
            next_var: 0,
            sort_base_subst: HashMap::new(),
            sort_sort: None,
            entity_of_sort: None,
        }
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

    /// Allocate a fresh logic variable id, carrying the display name.
    pub fn fresh_var(&mut self, name: Symbol) -> VarId {
        let id = self.next_var;
        self.next_var += 1;
        VarId::new(id, name)
    }

    /// Resolve a Symbol back to a string.
    pub fn resolve_sym(&self, sym: Symbol) -> &str {
        self.symbols.name(sym)
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
        });

        // Update indexes
        self.by_sort.entry(sort).or_default().push(rule_id);

        // Index by domain
        self.by_domain.entry(domain).or_default().push(rule_id);

        // Index by top-level functor
        if let Term::Fn { functor, .. } = *self.terms.get(head) {
            self.by_functor.entry(functor).or_default().push(rule_id);
        }

        // Discrimination tree index (insert_pattern handles vars in head)
        self.discrim.insert_pattern(&self.terms, head, rule_id);

        rule_id
    }

    /// Assert a ground fact (rule with empty body). Idempotent: if an identical
    /// fact (same head, sort, domain) already exists, returns the existing RuleId.
    pub fn assert_fact(
        &mut self,
        term: TermId,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> RuleId {
        // Dedup: check if this exact fact already exists
        if let Some(ids) = self.by_sort.get(&sort) {
            for &rid in ids {
                let entry = &self.rules[rid.index()];
                if !entry.retracted
                    && entry.head == term
                    && entry.domain == domain
                    && entry.body.is_empty()
                {
                    return rid;
                }
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
    }

    /// Check if `sub` is an entity of `sup` (1-level entity → parent sort).
    pub fn is_entity_of(&self, sub: TermId, sup: TermId) -> bool {
        if sub == sup {
            return true;
        }
        self.entity_parent.get(&sub) == Some(&sup)
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

    /// Get sort kind info.
    pub fn sort_kind(&self, sort_term: TermId) -> Option<SortKind> {
        self.sort_info.get(&sort_term).copied()
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
        let mut tree = SubstTree::<()>::new();
        tree.insert_pattern(&self.terms, target, ());
        let results = tree.query_resolved(&self.terms, pattern, |_| target);
        // Filter out contradictory substitutions (e.g. ?x bound to two different values)
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
        let candidates = self.discrim.query_resolved(
            &self.terms,
            pattern,
            |rid: &RuleId| rules[rid.index()].head,
        );

        let mut results = Vec::new();
        for (rid, tree_subst) in candidates {
            if self.rules[rid.index()].retracted {
                continue;
            }
            if tree_subst.is_contradiction() {
                continue;
            }
            results.push((rid, tree_subst));
        }
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
            Term::Var(vid) => {
                if seen.insert(vid.raw()) {
                    vars.push(*vid);
                }
            }
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
    fn map_fn_children(&mut self, term: TermId, mut f: impl FnMut(&mut Self, TermId) -> TermId) -> TermId {
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
            Term::Var(vid) => subst.resolve(vid).unwrap_or(term),
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
                Term::Var(vid) => {
                    if let Some(bound) = subst.resolve(*vid) {
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
            let fresh_term = self.alloc(Term::Var(fresh));
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
        let head = self.rules[id.index()].head;
        let body = self.rules[id.index()].body.clone();
        let all_vars = self.collect_rule_vars(head, &body);

        // Step 1: Build rename map for rule variables
        // If tree_subst has a concrete binding for a rule var → use it directly
        // Otherwise → create a fresh var
        let mut rename = subst::Substitution::new();

        for vid in &all_vars {
            if let Some(bound) = tree_subst.resolve(*vid) {
                if !matches!(self.terms.get(bound), Term::Var(_)) {
                    // tree_subst has rule_var → concrete: substitute directly
                    rename.bind(*vid, bound);
                    continue;
                }
            }
            // No concrete binding — create fresh var
            let fresh = self.fresh_var(vid.name());
            let fresh_term = self.alloc(Term::Var(fresh));
            rename.bind(*vid, fresh_term);
        }

        // Step 2: Apply rename to rule body → fresh_body
        let fresh_body: Vec<TermId> = body
            .iter()
            .map(|&b| self.apply_subst(b, &rename))
            .collect();

        // Step 3: Build answer_links from tree_subst
        // For each tree_subst entry whose key is a query var (not a rule var),
        // map it to the appropriate fresh var or concrete value
        let mut answer_links = subst::Substitution::new();

        for (ts_vid, bound_term) in &tree_subst.bindings {
            // Skip entries keyed by rule vars — they're already in rename
            if all_vars.contains(ts_vid) {
                continue;
            }
            // This is a query var entry
            match self.terms.get(*bound_term) {
                Term::Var(rule_vid) => {
                    // query_var → Var(rule_vid): find what rename mapped rule_vid to
                    let rule_vid = *rule_vid;
                    if let Some(renamed) = rename.resolve(rule_vid) {
                        answer_links.bind(*ts_vid, renamed);
                    }
                }
                _ => {
                    // query_var → structured term: apply rename to replace
                    // any rule variables inside with their fresh copies
                    let renamed_term = self.apply_subst(*bound_term, &rename);
                    answer_links.bind(*ts_vid, renamed_term);
                }
            }
        }

        (fresh_body, answer_links)
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

    /// Try to look up a resolved symbol by qualified name.
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

        kb.register_sort(nat, SortKind::Defined);
        kb.register_sort(zero, SortKind::Constructor);
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
        let var_term = kb.alloc(Term::Var(vid));
        let target = kb.alloc(Term::Const(Literal::Int(42)));

        let s = kb.match_term(var_term, target).expect("should match");
        assert_eq!(s.resolve(vid), Some(target));
    }

    #[test]
    fn match_term_var_consistency() {
        // ?x matches first arg, then must match same value in second arg
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_term = kb.alloc(Term::Var(vid));

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
        let var_x = kb.alloc(Term::Var(vid));
        let pattern = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, bob]),
            named_args: SmallVec::new(),
        });

        let results = kb.query(pattern);
        assert_eq!(results.len(), 1);
        let (_, ref s) = results[0];
        assert_eq!(s.resolve(vid), Some(alice));
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
        let var_x = kb.alloc(Term::Var(vx));
        let var_y = kb.alloc(Term::Var(vy));
        let var_z = kb.alloc(Term::Var(vz));

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
        let var_x = kb.alloc(Term::Var(vx));
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
        let var_q = kb.alloc(Term::Var(qv));
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
        let var_x = kb.alloc(Term::Var(vid));
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
        let var_x = kb.alloc(Term::Var(vx));

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
        let var_x = kb.alloc(Term::Var(vx));
        let var_y = kb.alloc(Term::Var(vy));

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
