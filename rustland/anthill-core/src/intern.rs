/// Symbol table — maps strings to compact `Symbol(u32)` handles,
/// with optional resolution metadata (kind, scope, qualified name).
///
/// Symbols can be **Unresolved** (just a name, deduplicated) or
/// **Resolved** (short name + qualified name + kind + parent scope).
/// The scan-then-load pipeline defines symbols during scanning, then
/// resolves references during loading.

use std::collections::{HashMap, HashSet};
use smallvec::SmallVec;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Symbol(u32);

impl Symbol {
    pub fn index(self) -> u32 {
        self.0
    }

    /// Create from raw index. Used for synthetic VarIds (de Bruijn).
    pub fn from_raw(raw: u32) -> Self {
        Symbol(raw)
    }
}

// ── Symbol metadata ─────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymbolKind {
    Sort,
    Entity,
    Operation,
    Namespace,
    Fact,
    Rule,
    Constraint,
    /// An operation parameter — the `input` place of the operation frame
    /// (proposal 046 / WI-352). Also the implicit dataflow `provenance` of the
    /// name: an op param IS its input.
    Param,
    Field,
    Goal,
    // ── Operation-frame places (WI-352) ─────────────────────────────
    // The reserved result and callback-derived binders introduced by an
    // operation signature. WI-351 mis-tagged these as `Param` (a result is
    // not a parameter) and kept the real classification in an external
    // `place_roles` side-table; WI-352 moves the truth onto the symbol's
    // kind, so `provenance` and `is_result_binder` are functions of it. These
    // route as values and stay scope-encapsulated exactly like `Param`.
    /// The operation's reserved return-value name `<op>.result` (and its
    /// tuple-field projections) — proposal 041. `provenance = op_result`;
    /// `is_result_binder(sym) == (kind == OpResult)`.
    OpResult,
    /// A parameter of a callback-typed op parameter — `<op>.f.a`. A flow
    /// *target* (the op feeds it); carries no `provenance` of its own.
    CallbackParam,
    /// A callback-typed op parameter's result — `<op>.f.result`.
    /// `provenance = fresh_output` (the callback mints it inside the op).
    CallbackResult,
    /// A `let`-bound local in an operation body. `provenance = local`.
    /// (WI-352 reserves the kind; *tagging* let-locals with it — interning
    /// them as scoped symbols during body lowering — is deferred.)
    LocalLet,
}

#[derive(Clone, Debug)]
pub enum SymbolDef {
    Unresolved {
        name: String,
    },
    Resolved {
        short_name: String,
        qualified_name: String,
        kind: SymbolKind,
        scope_raw: u32,
        /// WI-352 — for a *callable* place (an operation, or a callback-typed
        /// parameter), the ordered argument-place symbols it binds: an op's
        /// param places (`reduce.xs`, `reduce.z`, `reduce.f`) or a callback's
        /// own param places (`reduce.f.a`, `reduce.f.t`). Empty for everything
        /// else. This makes the higher-order structure self-describing on the
        /// symbol, so a body's `apply(F, args)` maps `args[i]` to `F`'s i-th
        /// place purely from symbol data — what the flow-derivation pass keys
        /// on, for the op (self-recursion) and callbacks alike. The result
        /// place is `<F>.result`, found by name, so it is not stored here.
        arg_places: Vec<Symbol>,
    },
}

#[derive(Clone, Debug)]
pub struct ScopeInclusion {
    pub parent_scope_raw: u32,
    pub instantiation_term_raw: u32,
    /// If true, this is an enclosing-scope relationship (sort/namespace body)
    /// and export filtering is bypassed.
    pub is_enclosing: bool,
}

// ── Resolution result ───────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum ResolveResult {
    Found(Symbol),
    Ambiguous(Vec<Symbol>),
    NotFound,
}

// ── Scope ───────────────────────────────────────────────────────

/// All per-scope data consolidated into one struct.
#[derive(Debug, Default)]
pub struct Scope {
    /// Definitions in this scope: short_name → Symbol
    pub locals: HashMap<String, Symbol>,
    /// Imported aliases: short_name → original Symbol
    pub imports: HashMap<String, Symbol>,
    /// Names this scope exposes to the enclosing scope through a
    /// (non-enclosing) variant-exposure parent link — populated from a sort's
    /// entity-variant short names ONLY. An empty set disables the filter (the
    /// scope is reachable only via `requires`/wildcard, which see everything).
    /// User `export` statements do NOT populate this — names are visible by
    /// default (proposal 044).
    pub exposed: HashSet<String>,
    /// Parent scope inclusions (enclosing + requires + imports)
    pub parents: Vec<ScopeInclusion>,
    /// Type parameter names (excluded from parent lookups)
    pub type_params: HashSet<String>,
    /// Type parameter names in declaration order. Parallel to
    /// `type_params` for membership tests; this is what positional
    /// sort bindings (e.g. `Map[String, Int]` for a `sort Map { sort
    /// K = ?; sort V = ? }`) consult to map index 0 → "K", index 1 →
    /// "V". Insertion-order preserves the source-text declaration
    /// order, which is the binding contract.
    pub type_params_ordered: Vec<String>,
}

// ── SymbolTable ─────────────────────────────────────────────────

#[derive(Debug, Default)]
pub struct SymbolTable {
    defs: Vec<SymbolDef>,
    /// Dedup map for Unresolved symbols: name → Symbol
    pub(crate) intern_map: HashMap<String, Symbol>,
    /// Qualified name → unique resolved Symbol
    pub by_qualified_name: HashMap<String, Symbol>,
    /// All per-scope data: scope_raw → Scope
    scopes: HashMap<u32, Scope>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a name, returning a Symbol. Creates an Unresolved entry
    /// if the name hasn't been seen before (deduplicated).
    pub fn intern(&mut self, s: &str) -> Symbol {
        if let Some(&sym) = self.intern_map.get(s) {
            return sym;
        }
        let sym = Symbol(self.defs.len() as u32);
        self.defs.push(SymbolDef::Unresolved {
            name: s.to_owned(),
        });
        self.intern_map.insert(s.to_owned(), sym);
        sym
    }

    /// Look up an existing symbol by name without allocating one if it
    /// isn't present. Returns `None` when no one has interned the name.
    /// Used by read-only paths (e.g. the loader looking for parse-side
    /// `"type_name"` / `"type_args"` named args without forcing them
    /// into existence).
    pub fn lookup(&self, s: &str) -> Option<Symbol> {
        self.intern_map.get(s).copied()
    }

    /// Define a new resolved symbol in a scope. If the same short_name
    /// already exists in the scope, returns the existing symbol (merge
    /// behavior — e.g. `namespace X` extends an existing `sort X`).
    /// Otherwise creates a new entry and indexes it.
    pub fn define(
        &mut self,
        short_name: &str,
        qualified_name: &str,
        kind: SymbolKind,
        scope_raw: u32,
    ) -> Symbol {
        let scope = self.scopes.entry(scope_raw).or_default();
        if let Some(&existing) = scope.locals.get(short_name) {
            return existing;
        }
        let sym = Symbol(self.defs.len() as u32);
        self.defs.push(SymbolDef::Resolved {
            short_name: short_name.to_owned(),
            qualified_name: qualified_name.to_owned(),
            kind,
            scope_raw,
            arg_places: Vec::new(),
        });
        scope.locals.insert(short_name.to_owned(), sym);
        self.by_qualified_name
            .insert(qualified_name.to_owned(), sym);
        sym
    }

    /// WI-352 — record the ordered argument-place symbols of a *callable*
    /// place (an operation, or a callback-typed parameter). See
    /// [`SymbolDef::Resolved::arg_places`]. Idempotent overwrite; a no-op on
    /// an unresolved symbol.
    pub fn set_arg_places(&mut self, sym: Symbol, places: Vec<Symbol>) {
        if let Some(SymbolDef::Resolved { arg_places, .. }) = self.defs.get_mut(sym.0 as usize) {
            *arg_places = places;
        }
    }

    /// WI-352 — the ordered argument-place symbols of `sym` (empty when `sym`
    /// is not a callable place, or unresolved). The result place is `<sym>.result`
    /// (found by name), not included here.
    pub fn arg_places(&self, sym: Symbol) -> &[Symbol] {
        match self.defs.get(sym.0 as usize) {
            Some(SymbolDef::Resolved { arg_places, .. }) => arg_places,
            _ => &[],
        }
    }

    /// Mark a name as exposed from a scope to its enclosing scope via the
    /// variant-exposure parent link (populated from entity variants only).
    pub fn add_exposed(&mut self, scope_raw: u32, name: &str) {
        self.scopes
            .entry(scope_raw)
            .or_default()
            .exposed
            .insert(name.to_owned());
    }

    /// Check if a name is a type parameter of the given scope.
    pub fn is_type_param(&self, scope_raw: u32, name: &str) -> bool {
        self.scopes.get(&scope_raw)
            .map_or(false, |s| s.type_params.contains(name))
    }

    /// Record a type parameter name for a scope (excluded from parent lookups).
    pub fn add_type_param(&mut self, scope_raw: u32, name: &str) {
        let scope = self.scopes.entry(scope_raw).or_default();
        if scope.type_params.insert(name.to_owned()) {
            scope.type_params_ordered.push(name.to_owned());
        }
    }

    /// Record an imported name alias in a scope.
    /// Makes `short_name` resolve to `sym` locally in the given scope.
    pub fn add_import(&mut self, scope_raw: u32, short_name: &str, sym: Symbol) {
        self.scopes
            .entry(scope_raw)
            .or_default()
            .imports
            .insert(short_name.to_owned(), sym);
    }

    /// Record a parent scope inclusion (from `requires` or `import`).
    pub fn add_parent(&mut self, scope_raw: u32, inclusion: ScopeInclusion) {
        self.scopes
            .entry(scope_raw)
            .or_default()
            .parents
            .push(inclusion);
    }

    /// Get a scope by its raw id.
    pub fn scope(&self, scope_raw: u32) -> Option<&Scope> {
        self.scopes.get(&scope_raw)
    }

    /// Get or create a scope by its raw id.
    pub fn scope_mut(&mut self, scope_raw: u32) -> &mut Scope {
        self.scopes.entry(scope_raw).or_default()
    }

    /// Resolve a name within a scope. Resolution order:
    /// 1. Local: find symbol defined directly in this scope
    /// 1b. Imports: check imported name aliases
    /// 2. Parent scopes: check parent inclusions (exposed variants only across
    ///    a variant-exposure link, excluding type params)
    /// 3. NotFound if nothing matches
    pub fn resolve_in_scope(&self, name: &str, scope_raw: u32) -> ResolveResult {
        let mut visited = std::collections::HashSet::new();
        self.resolve_in_scope_recursive(name, scope_raw, &mut visited)
    }

    fn resolve_in_scope_recursive(
        &self,
        name: &str,
        scope_raw: u32,
        visited: &mut std::collections::HashSet<u32>,
    ) -> ResolveResult {
        if !visited.insert(scope_raw) {
            return ResolveResult::NotFound; // cycle
        }

        // Collect eligible parent scopes (filter + extract) while holding
        // the borrow on self.scopes, then drop it before recursing.
        let eligible_parents: SmallVec<[u32; 4]> = if let Some(scope) = self.scopes.get(&scope_raw) {
            // 1. Local: check locals defined in this scope — O(1) lookup
            if let Some(&sym) = scope.locals.get(name) {
                return ResolveResult::Found(sym);
            }

            // 1b. Imported name aliases (from selective/plain imports)
            if let Some(&sym) = scope.imports.get(name) {
                return ResolveResult::Found(sym);
            }

            // 2. Filter parent scopes by type_params and the `exposed` set.
            // `exposed` holds a sort's entity variants (proposal 044 job 2): a
            // non-empty set leaks only those variants to the enclosing scope; an
            // empty set (specs, namespaces) is fully visible via requires/wildcard.
            scope.parents.iter().filter_map(|p| {
                if !p.is_enclosing {
                    if let Some(parent) = self.scopes.get(&p.parent_scope_raw) {
                        if parent.type_params.contains(name) {
                            return None;
                        }
                        if !parent.exposed.is_empty() && !parent.exposed.contains(name) {
                            return None;
                        }
                    }
                }
                Some(p.parent_scope_raw)
            }).collect()
        } else {
            return ResolveResult::NotFound;
        };
        // Borrow on self.scopes is dropped — safe to recurse.

        let mut matches = Vec::new();
        for parent_scope in eligible_parents {
            match self.resolve_in_scope_recursive(name, parent_scope, visited) {
                ResolveResult::Found(sym) => matches.push(sym),
                ResolveResult::Ambiguous(mut candidates) => matches.append(&mut candidates),
                ResolveResult::NotFound => {}
            }
        }

        // Deduplicate matches (same symbol may be reachable via multiple paths)
        matches.sort_by_key(|s| s.0);
        matches.dedup();

        match matches.len() {
            0 => ResolveResult::NotFound,
            1 => ResolveResult::Found(matches[0]),
            _ => ResolveResult::Ambiguous(matches),
        }
    }

    /// Get the display name of a symbol (short_name for Resolved, name for Unresolved).
    pub fn name(&self, sym: Symbol) -> &str {
        match &self.defs[sym.0 as usize] {
            SymbolDef::Unresolved { name } => name,
            SymbolDef::Resolved { short_name, .. } => short_name,
        }
    }

    /// Alias for `name()` — backward compatibility.
    pub fn resolve(&self, sym: Symbol) -> &str {
        self.name(sym)
    }

    /// Get the full SymbolDef for a symbol.
    pub fn get(&self, sym: Symbol) -> &SymbolDef {
        &self.defs[sym.0 as usize]
    }

    /// Check if a symbol is resolved (has kind, scope, qualified name).
    pub fn is_resolved(&self, sym: Symbol) -> bool {
        matches!(&self.defs[sym.0 as usize], SymbolDef::Resolved { .. })
    }

    /// Scope symbol that owns `sym` (the symbol whose body contains it as a
    /// local). `None` at the top-level `_global` scope or for unresolved
    /// symbols. Linear scan over defs — fine at introspection rates.
    pub fn scope_of(&self, sym: Symbol) -> Option<Symbol> {
        let scope_raw = match self.get(sym) {
            SymbolDef::Resolved { scope_raw, .. } => *scope_raw,
            SymbolDef::Unresolved { .. } => return None,
        };
        for (i, def) in self.defs.iter().enumerate() {
            if let SymbolDef::Resolved { scope_raw: sraw, kind, .. } = def {
                if *sraw != scope_raw { continue; }
                if matches!(kind, SymbolKind::Sort | SymbolKind::Namespace | SymbolKind::Operation) {
                    let candidate = Symbol::from_raw(i as u32);
                    if candidate != sym { return Some(candidate); }
                }
            }
        }
        None
    }

}

// ── Backward-compatible type alias ──────────────────────────────

/// Alias: old code that uses `Interner` keeps compiling.
pub type Interner = SymbolTable;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_dedup() {
        let mut st = SymbolTable::new();
        let a = st.intern("foo");
        let b = st.intern("foo");
        assert_eq!(a, b);
        assert_eq!(st.name(a), "foo");
    }

    #[test]
    fn define_creates_new_entry_different_scopes() {
        let mut st = SymbolTable::new();
        let s1 = st.define("foo", "A.foo", SymbolKind::Operation, 10);
        let s2 = st.define("foo", "B.foo", SymbolKind::Operation, 20);
        assert_ne!(s1, s2);
        assert_eq!(st.name(s1), "foo");
        assert_eq!(st.name(s2), "foo");
        assert!(st.is_resolved(s1));
        assert!(st.is_resolved(s2));
    }

    #[test]
    fn define_same_scope_reuses() {
        let mut st = SymbolTable::new();
        let s1 = st.define("Foo", "A.Foo", SymbolKind::Sort, 10);
        let s2 = st.define("Foo", "A.Foo", SymbolKind::Namespace, 10);
        assert_eq!(s1, s2, "same short_name in same scope should reuse");
    }

    #[test]
    fn resolve_in_scope_local() {
        let mut st = SymbolTable::new();
        let s = st.define("eq", "Eq.eq", SymbolKind::Operation, 100);
        match st.resolve_in_scope("eq", 100) {
            ResolveResult::Found(found) => assert_eq!(found, s),
            other => panic!("expected Found, got {:?}", other),
        }
    }

    #[test]
    fn resolve_in_scope_parent() {
        let mut st = SymbolTable::new();
        // Define "eq" in scope 100 (Eq)
        let eq_sym = st.define("eq", "Eq.eq", SymbolKind::Operation, 100);
        st.add_exposed(100, "eq");

        // Scope 200 (Ordered) includes scope 100 (Eq)
        st.add_parent(200, ScopeInclusion {
            parent_scope_raw: 100,
            instantiation_term_raw: 0,
            is_enclosing: false,
        });

        // "eq" should resolve in scope 200 via parent
        match st.resolve_in_scope("eq", 200) {
            ResolveResult::Found(found) => assert_eq!(found, eq_sym),
            other => panic!("expected Found, got {:?}", other),
        }
    }

    #[test]
    fn resolve_excludes_type_params() {
        let mut st = SymbolTable::new();
        // Define "T" as a sort in scope 100
        st.define("T", "Eq.T", SymbolKind::Sort, 100);
        st.add_exposed(100, "T");
        st.add_type_param(100, "T");

        // Define "eq" in scope 100
        let eq_sym = st.define("eq", "Eq.eq", SymbolKind::Operation, 100);
        st.add_exposed(100, "eq");

        // Scope 200 includes scope 100
        st.add_parent(200, ScopeInclusion {
            parent_scope_raw: 100,
            instantiation_term_raw: 0,
            is_enclosing: false,
        });

        // "T" should NOT resolve from parent (it's a type param)
        match st.resolve_in_scope("T", 200) {
            ResolveResult::NotFound => {}
            other => panic!("expected NotFound for type param, got {:?}", other),
        }

        // "eq" should resolve normally
        match st.resolve_in_scope("eq", 200) {
            ResolveResult::Found(found) => assert_eq!(found, eq_sym),
            other => panic!("expected Found, got {:?}", other),
        }
    }

    #[test]
    fn resolve_ambiguous() {
        let mut st = SymbolTable::new();
        // Define "foo" in two different parent scopes
        st.define("foo", "A.foo", SymbolKind::Operation, 100);
        st.add_exposed(100, "foo");
        st.define("foo", "B.foo", SymbolKind::Operation, 200);
        st.add_exposed(200, "foo");

        // Scope 300 includes both
        st.add_parent(300, ScopeInclusion {
            parent_scope_raw: 100,
            instantiation_term_raw: 0,
            is_enclosing: false,
        });
        st.add_parent(300, ScopeInclusion {
            parent_scope_raw: 200,
            instantiation_term_raw: 0,
            is_enclosing: false,
        });

        match st.resolve_in_scope("foo", 300) {
            ResolveResult::Ambiguous(candidates) => assert_eq!(candidates.len(), 2),
            other => panic!("expected Ambiguous, got {:?}", other),
        }
    }

    #[test]
    fn local_shadows_parent() {
        let mut st = SymbolTable::new();
        // Define "foo" in parent scope 100
        st.define("foo", "A.foo", SymbolKind::Operation, 100);
        st.add_exposed(100, "foo");

        // Define "foo" locally in scope 200
        let local_foo = st.define("foo", "B.foo", SymbolKind::Operation, 200);

        // Scope 200 includes 100
        st.add_parent(200, ScopeInclusion {
            parent_scope_raw: 100,
            instantiation_term_raw: 0,
            is_enclosing: false,
        });

        // Local should win
        match st.resolve_in_scope("foo", 200) {
            ResolveResult::Found(found) => assert_eq!(found, local_foo),
            other => panic!("expected Found (local), got {:?}", other),
        }
    }
}
