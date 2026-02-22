/// Substitution — maps logic variables to term ids.
///
/// See: docs/stage0/rust-term-store-design.md §3.4

use std::collections::HashMap;

use super::term::{Term, TermId, TermStore, VarId};

#[derive(Clone, Debug)]
pub struct Substitution {
    pub bindings: HashMap<VarId, TermId>,
    pub parent: Option<Box<Substitution>>,
    /// Set to true when a variable is bound to two different concrete terms.
    pub contradiction: bool,
}

impl Substitution {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
            contradiction: false,
        }
    }

    pub fn with_parent(parent: Substitution) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(Box::new(parent)),
            contradiction: false,
        }
    }

    /// Look up a variable binding, walking parent chain.
    pub fn resolve(&self, var: VarId) -> Option<TermId> {
        if let Some(&id) = self.bindings.get(&var) {
            return Some(id);
        }
        if let Some(ref parent) = self.parent {
            return parent.resolve(var);
        }
        None
    }

    /// Bind a variable to a term id.
    ///
    /// If the variable is already bound to a different term, marks the
    /// substitution as contradictory.
    pub fn bind(&mut self, var: VarId, term: TermId) {
        if let Some(&existing) = self.bindings.get(&var) {
            if existing != term {
                self.contradiction = true;
            }
            // Keep existing binding (first-wins), but flag the contradiction
            return;
        }
        self.bindings.insert(var, term);
    }

    /// Whether this substitution contains a contradiction
    /// (a variable bound to two different concrete terms).
    pub fn is_contradiction(&self) -> bool {
        self.contradiction
    }

    /// Add bindings with path compression in one operation.
    ///
    /// For each `(vid, term)` in `new_bindings`:
    /// 1. Scan existing entries: any `?w → Var(vid)` becomes `?w → term`
    /// 2. Insert `vid → term`
    ///
    /// Keeps the substitution always flat — no chains, no `walk` needed.
    pub fn bind_compressed<I>(&mut self, new_bindings: I, terms: &TermStore)
    where
        I: IntoIterator<Item = (VarId, TermId)>,
    {
        for (vid, term) in new_bindings {
            // Compress: update any existing binding that pointed to Var(vid)
            for (_, existing_term) in self.bindings.iter_mut() {
                if let Term::Var(ev) = terms.get(*existing_term) {
                    if *ev == vid {
                        *existing_term = term;
                    }
                }
            }
            self.bindings.insert(vid, term);
        }
    }

    /// Iterate over all bindings.
    pub fn iter(&self) -> impl Iterator<Item = (&VarId, &TermId)> {
        self.bindings.iter()
    }
}

impl Default for Substitution {
    fn default() -> Self {
        Self::new()
    }
}
