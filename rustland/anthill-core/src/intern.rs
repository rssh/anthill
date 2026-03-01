/// Symbol table — maps strings to compact `Symbol(u32)` handles,
/// with optional resolution metadata (kind, scope, qualified name).
///
/// Symbols can be **Unresolved** (just a name, deduplicated) or
/// **Resolved** (short name + qualified name + kind + parent scope).
/// The scan-then-load pipeline defines symbols during scanning, then
/// resolves references during loading.

use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Symbol(u32);

impl Symbol {
    pub fn index(self) -> u32 {
        self.0
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
    Param,
    Field,
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

// ── SymbolTable ─────────────────────────────────────────────────

#[derive(Debug, Default)]
pub struct SymbolTable {
    defs: Vec<SymbolDef>,
    /// Dedup map for Unresolved symbols: name → Symbol
    intern_map: HashMap<String, Symbol>,
    /// Short name → all resolved Symbols with that short name
    by_short_name: HashMap<String, Vec<Symbol>>,
    /// Qualified name → unique resolved Symbol
    pub by_qualified_name: HashMap<String, Symbol>,
    /// Scope (raw u32) → set of exported short names
    scope_exports: HashMap<u32, HashSet<String>>,
    /// Scope (raw u32) → parent scope inclusions
    scope_parents: HashMap<u32, Vec<ScopeInclusion>>,
    /// Scope (raw u32) → type parameter names (excluded from parent lookups)
    scope_type_params: HashMap<u32, HashSet<String>>,
    /// Scope (raw u32) → imported name aliases: short_name → original Symbol.
    /// Selective/plain imports register the imported sort/namespace name
    /// directly so it resolves locally without parent-scope export filtering.
    scope_imports: HashMap<u32, HashMap<String, Symbol>>,
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

    /// Define a new resolved symbol. Always creates a new entry
    /// (no dedup — two sorts named "Foo" in different scopes get
    /// different Symbols). Indexes in by_short_name and by_qualified_name.
    pub fn define(
        &mut self,
        short_name: &str,
        qualified_name: &str,
        kind: SymbolKind,
        scope_raw: u32,
    ) -> Symbol {
        let sym = Symbol(self.defs.len() as u32);
        self.defs.push(SymbolDef::Resolved {
            short_name: short_name.to_owned(),
            qualified_name: qualified_name.to_owned(),
            kind,
            scope_raw,
        });
        self.by_short_name
            .entry(short_name.to_owned())
            .or_default()
            .push(sym);
        self.by_qualified_name
            .insert(qualified_name.to_owned(), sym);
        sym
    }

    /// Record an exported name for a scope.
    pub fn add_export(&mut self, scope_raw: u32, name: &str) {
        self.scope_exports
            .entry(scope_raw)
            .or_default()
            .insert(name.to_owned());
    }

    /// Record a type parameter name for a scope (excluded from parent lookups).
    pub fn add_type_param(&mut self, scope_raw: u32, name: &str) {
        self.scope_type_params
            .entry(scope_raw)
            .or_default()
            .insert(name.to_owned());
    }

    /// Record an imported name alias in a scope.
    /// Makes `short_name` resolve to `sym` locally in the given scope.
    pub fn add_import(&mut self, scope_raw: u32, short_name: &str, sym: Symbol) {
        self.scope_imports
            .entry(scope_raw)
            .or_default()
            .insert(short_name.to_owned(), sym);
    }

    /// Record a parent scope inclusion (from `requires` or `import`).
    pub fn add_parent(&mut self, scope_raw: u32, inclusion: ScopeInclusion) {
        self.scope_parents
            .entry(scope_raw)
            .or_default()
            .push(inclusion);
    }

    /// Resolve a name within a scope. Resolution order:
    /// 1. Local: find symbol defined directly in this scope
    /// 2. Parent scopes: check parent inclusions (exports only, excluding type params)
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

        // 1. Local: check by_short_name entries that match this scope
        if let Some(syms) = self.by_short_name.get(name) {
            for &sym in syms {
                if let SymbolDef::Resolved {
                    scope_raw: s_raw, ..
                } = &self.defs[sym.0 as usize]
                {
                    if *s_raw == scope_raw {
                        return ResolveResult::Found(sym);
                    }
                }
            }
        }

        // 1b. Imported name aliases (from selective/plain imports)
        if let Some(imports) = self.scope_imports.get(&scope_raw) {
            if let Some(&sym) = imports.get(name) {
                return ResolveResult::Found(sym);
            }
        }

        // 2. Parent scopes (recursively)
        if let Some(parents) = self.scope_parents.get(&scope_raw) {
            let mut matches = Vec::new();
            for inclusion in parents {
                let parent_scope = inclusion.parent_scope_raw;

                // Skip if name is a type param in the parent scope,
                // UNLESS this is an enclosing scope (operations within a sort
                // should see the sort's type parameters).
                if !inclusion.is_enclosing {
                    if let Some(type_params) = self.scope_type_params.get(&parent_scope) {
                        if type_params.contains(name) {
                            continue;
                        }
                    }
                }

                // Check exports: if exports exist and are non-empty, name must be exported
                // (enclosing-scope parents bypass this check — you see everything in your own scope)
                if !inclusion.is_enclosing {
                    if let Some(exports) = self.scope_exports.get(&parent_scope) {
                        if !exports.is_empty() && !exports.contains(name) {
                            continue;
                        }
                    }
                }

                // Find symbol in parent scope (recursively)
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
                0 => {}
                1 => return ResolveResult::Found(matches[0]),
                _ => return ResolveResult::Ambiguous(matches),
            }
        }

        ResolveResult::NotFound
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

    /// Find a resolved symbol by short name that has kind Sort.
    pub fn find_sort_symbol(&self, name: &str) -> Option<Symbol> {
        self.by_short_name.get(name).and_then(|syms| {
            syms.iter().find(|&&sym| {
                matches!(
                    &self.defs[sym.0 as usize],
                    SymbolDef::Resolved {
                        kind: SymbolKind::Sort,
                        ..
                    }
                )
            }).copied()
        })
    }

    /// Find any resolved symbol by short name (first match).
    pub fn find_resolved_symbol(&self, name: &str) -> Option<Symbol> {
        self.by_short_name.get(name).and_then(|syms| {
            syms.first().copied()
        })
    }

    /// Find a resolved symbol by short name, returning the most recently
    /// defined one. Definitions are ordered: prelude (register_prelude)
    /// → stdlib (scan_definitions) → user source, so "last wins" naturally
    /// gives priority to the most specific definition.
    /// Returns `None` if no resolved symbol exists for the name.
    pub fn find_preferred_symbol(&self, name: &str) -> Option<Symbol> {
        self.by_short_name.get(name).and_then(|syms| {
            syms.last().copied()
        })
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
    fn define_creates_new_entry() {
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
        st.add_export(100, "eq");

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
        st.add_export(100, "T");
        st.add_type_param(100, "T");

        // Define "eq" in scope 100
        let eq_sym = st.define("eq", "Eq.eq", SymbolKind::Operation, 100);
        st.add_export(100, "eq");

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
        st.add_export(100, "foo");
        st.define("foo", "B.foo", SymbolKind::Operation, 200);
        st.add_export(200, "foo");

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
        st.add_export(100, "foo");

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
