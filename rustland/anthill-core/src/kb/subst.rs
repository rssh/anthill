/// Substitution — maps logic variables to term ids.
///
/// Functional now; `chase()` stubbed for Layer 1 (unification).
/// See: docs/stage0/term-store-design.md §3.4

use std::collections::HashMap;

use super::term::{TermId, VarId};

#[derive(Clone, Debug)]
pub struct Substitution {
    pub bindings: HashMap<VarId, TermId>,
    pub parent: Option<Box<Substitution>>,
}

impl Substitution {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
        }
    }

    pub fn with_parent(parent: Substitution) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(Box::new(parent)),
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
    pub fn bind(&mut self, var: VarId, term: TermId) {
        self.bindings.insert(var, term);
    }

    /// Chase variable bindings through the substitution chain.
    /// Stubbed for Layer 1 — currently just returns the input.
    pub fn chase(&self, _id: TermId) -> TermId {
        // Layer 1 will follow Var → TermId → Var → ... chains
        _id
    }
}

impl Default for Substitution {
    fn default() -> Self {
        Self::new()
    }
}
