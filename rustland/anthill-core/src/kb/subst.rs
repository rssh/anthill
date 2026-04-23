/// Substitution — maps logic variables to runtime `Value`s.
///
/// Per proposal 026.1 Q1, bindings carry `Value` rather than raw `TermId`,
/// so the resolver and evaluator speak the same runtime representation.
/// `Value::Term(tid)` remains the dominant variant (facts / rule heads /
/// KB-resident data) and preserves O(1) structural equality via hash-consing
/// in the `TermStore`. Non-`Term` variants appear when the source is an
/// external-backed stream (`Value::Entity`), a literal in a rule body
/// (`Value::Int`, etc.), or an evaluator-bound value threaded through.
///
/// See: docs/stage0/rust-term-store-design.md §3.4, docs/proposals/026.1

use std::collections::HashMap;

use super::term::{Term, TermId, TermStore, Var, VarId};
use crate::eval::value::Value;

#[derive(Clone, Debug)]
pub struct Substitution {
    pub bindings: HashMap<VarId, Value>,
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

    /// Narrow resolve: returns `Some(tid)` only when the binding is
    /// `Value::Term(tid)` — the dominant resolver-internal case. Non-`Term`
    /// bindings (external sources, literals) return `None` here; use
    /// [`Self::resolve_as_value`] for the covering view that surfaces any
    /// `Value` variant.
    pub fn resolve_with_term(&self, var: VarId) -> Option<TermId> {
        if let Some(v) = self.bindings.get(&var) {
            return match v {
                Value::Term(tid) => Some(*tid),
                _ => None,
            };
        }
        if let Some(ref parent) = self.parent {
            return parent.resolve_with_term(var);
        }
        None
    }

    /// Covering resolve: returns any binding as a `Value`, including the
    /// `Value::Term(tid)` variant (which [`Self::resolve_with_term`] would
    /// also surface) and non-`Term` variants produced by external stream
    /// sources or rule-body literals (which the `_term` path hides).
    /// Prefer this when the caller can handle any lineage; use
    /// `resolve_with_term` only when a `TermId` is genuinely required
    /// (discrim-tree indexing, serialization, etc.).
    pub fn resolve_as_value(&self, var: VarId) -> Option<&Value> {
        if let Some(v) = self.bindings.get(&var) {
            return Some(v);
        }
        if let Some(ref parent) = self.parent {
            return parent.resolve_as_value(var);
        }
        None
    }

    /// Bind a variable to a `TermId` — the dominant resolver path. Wraps
    /// the `TermId` as `Value::Term(tid)` for storage. If the variable is
    /// already bound to a different concrete term, marks the substitution
    /// as contradictory.
    pub fn bind_term(&mut self, var: VarId, term: TermId) {
        if let Some(existing) = self.bindings.get(&var) {
            match existing {
                Value::Term(existing_tid) if *existing_tid == term => return,
                _ => {
                    self.contradiction = true;
                    return;
                }
            }
        }
        self.bindings.insert(var, Value::Term(term));
    }

    /// Bind a variable to a runtime `Value`. Used when the source is not
    /// KB-resident: external stream rows, interpreter-evaluated values, or
    /// literals decoded from rule bodies. Preserves lineage — an incoming
    /// `Value::Entity` stays as such rather than being promoted to
    /// `Value::Term` via `TermStore::alloc`.
    pub fn bind_value(&mut self, var: VarId, val: Value) {
        if let Some(existing) = self.bindings.get(&var) {
            if !existing.structural_eq(&val) {
                self.contradiction = true;
            }
            return;
        }
        self.bindings.insert(var, val);
    }

    /// Legacy alias for `bind_term`. New code should prefer the explicit
    /// name to make the fast-path vs. value-path choice visible.
    #[inline]
    pub fn bind(&mut self, var: VarId, term: TermId) {
        self.bind_term(var, term);
    }

    /// Whether this substitution contains a contradiction
    /// (a variable bound to two different concrete terms).
    pub fn is_contradiction(&self) -> bool {
        self.contradiction
    }

    /// Add bindings with path compression in one operation. Operates over
    /// the `Value::Term` subset — non-`Term` entries are never
    /// path-compression sources or targets. Mixed bindings are left
    /// untouched (their walker, if ever needed, handles them structurally).
    ///
    /// For each `(vid, term)` in `new_bindings`:
    /// 1. Scan existing `Value::Term` entries: any `?w → Var(vid)` becomes
    ///    `?w → term`.
    /// 2. Insert `vid → term`.
    pub fn bind_compressed<I>(&mut self, new_bindings: I, terms: &TermStore)
    where
        I: IntoIterator<Item = (VarId, TermId)>,
    {
        for (vid, term) in new_bindings {
            for (_, existing) in self.bindings.iter_mut() {
                if let Value::Term(existing_tid) = existing {
                    if let Term::Var(Var::Global(ev)) = terms.get(*existing_tid) {
                        if *ev == vid {
                            *existing = Value::Term(term);
                        }
                    }
                }
            }
            self.bindings.insert(vid, Value::Term(term));
        }
    }

    /// Iterate over all bindings. Yields `(VarId, Value)` references;
    /// callers that only care about `Value::Term` entries should filter.
    pub fn iter(&self) -> impl Iterator<Item = (&VarId, &Value)> {
        self.bindings.iter()
    }

    /// Iterate over only the `Value::Term` bindings, yielding
    /// `(VarId, TermId)` — the ergonomic form for resolver-internal code
    /// that wants to stay in the TermId world.
    pub fn iter_terms(&self) -> impl Iterator<Item = (VarId, TermId)> + '_ {
        self.bindings.iter().filter_map(|(v, val)| match val {
            Value::Term(tid) => Some((*v, *tid)),
            _ => None,
        })
    }
}

impl Default for Substitution {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Symbol;

    fn vid(id: u32) -> VarId {
        VarId::new(id, Symbol::from_raw(0))
    }

    #[test]
    fn bind_term_roundtrips_as_value_term() {
        let mut s = Substitution::new();
        let v = vid(1);
        let t = TermId::from_raw(42);
        s.bind_term(v, t);
        assert_eq!(s.resolve_with_term(v), Some(t));
        match s.resolve_as_value(v) {
            Some(Value::Term(tid)) => assert_eq!(*tid, t),
            other => panic!("expected Value::Term, got {other:?}"),
        }
    }

    #[test]
    fn bind_value_accepts_non_term() {
        let mut s = Substitution::new();
        let v = vid(1);
        s.bind_value(v, Value::Int(42));
        // resolve (TermId-only path) returns None for non-Term bindings.
        assert_eq!(s.resolve_with_term(v), None);
        // lookup surfaces the full Value.
        match s.resolve_as_value(v) {
            Some(Value::Int(42)) => {}
            other => panic!("expected Value::Int(42), got {other:?}"),
        }
    }

    #[test]
    fn bind_twice_same_term_is_not_contradiction() {
        let mut s = Substitution::new();
        let v = vid(1);
        let t = TermId::from_raw(7);
        s.bind_term(v, t);
        s.bind_term(v, t);
        assert!(!s.is_contradiction());
    }

    #[test]
    fn bind_twice_different_term_is_contradiction() {
        let mut s = Substitution::new();
        let v = vid(1);
        s.bind_term(v, TermId::from_raw(1));
        s.bind_term(v, TermId::from_raw(2));
        assert!(s.is_contradiction());
    }

    #[test]
    fn bind_term_then_value_is_contradiction_when_distinct() {
        let mut s = Substitution::new();
        let v = vid(1);
        s.bind_term(v, TermId::from_raw(1));
        // A non-Term value can't be equal to a Value::Term under scalar_eq
        // (cross-variant compare is `false`) — so rebinding flags a
        // contradiction, preserving the "same var, different concrete
        // binding" invariant across lineage boundaries.
        s.bind_value(v, Value::Int(99));
        assert!(s.is_contradiction());
    }

    #[test]
    fn bind_value_equal_scalar_not_contradiction() {
        let mut s = Substitution::new();
        let v = vid(1);
        s.bind_value(v, Value::Int(42));
        s.bind_value(v, Value::Int(42));
        assert!(!s.is_contradiction());
    }

    #[test]
    fn lookup_walks_parent_chain() {
        let mut parent = Substitution::new();
        parent.bind_term(vid(1), TermId::from_raw(10));
        let child = Substitution::with_parent(parent);
        assert_eq!(child.resolve_with_term(vid(1)), Some(TermId::from_raw(10)));
        matches!(child.resolve_as_value(vid(1)), Some(Value::Term(_)));
    }

    #[test]
    fn iter_terms_filters_out_non_term_values() {
        let mut s = Substitution::new();
        s.bind_term(vid(1), TermId::from_raw(100));
        s.bind_value(vid(2), Value::Int(42));
        s.bind_term(vid(3), TermId::from_raw(300));
        let pairs: Vec<(VarId, TermId)> = s.iter_terms().collect();
        assert_eq!(pairs.len(), 2);
        // Sort for deterministic compare (HashMap iter order isn't stable).
        let mut raws: Vec<u32> = pairs.iter().map(|(v, _)| v.raw()).collect();
        raws.sort();
        assert_eq!(raws, vec![1, 3]);
    }

    #[test]
    fn bind_value_stores_structured_entity() {
        let mut s = Substitution::new();
        let v = vid(1);
        let functor = Symbol::from_raw(7);
        let key = Symbol::from_raw(8);
        let entity = Value::Entity {
            functor,
            pos: vec![Value::Int(10), Value::Str("hi".into())],
            named: vec![(key, Value::Bool(true))],
        };
        s.bind_value(v, entity);
        assert_eq!(s.resolve_with_term(v), None);
        match s.resolve_as_value(v) {
            Some(Value::Entity { functor: f, pos, named }) => {
                assert_eq!(*f, functor);
                assert!(matches!(pos.as_slice(), [Value::Int(10), Value::Str(_)]));
                assert_eq!(named.len(), 1);
                assert_eq!(named[0].0, key);
                assert!(matches!(named[0].1, Value::Bool(true)));
            }
            other => panic!("expected Value::Entity, got {other:?}"),
        }
    }

    #[test]
    fn bind_value_stores_structured_tuple() {
        let mut s = Substitution::new();
        let v = vid(1);
        let tuple = Value::Tuple {
            pos: vec![Value::Int(1), Value::Int(2), Value::Int(3)],
            named: vec![],
        };
        s.bind_value(v, tuple);
        assert_eq!(s.resolve_with_term(v), None);
        match s.resolve_as_value(v) {
            Some(Value::Tuple { pos, named }) => {
                assert_eq!(pos.len(), 3);
                assert!(named.is_empty());
            }
            other => panic!("expected Value::Tuple, got {other:?}"),
        }
    }

    #[test]
    fn bind_value_equal_entity_not_contradiction() {
        let mut s = Substitution::new();
        let v = vid(1);
        let make_entity = || Value::Entity {
            functor: Symbol::from_raw(7),
            pos: vec![Value::Int(10), Value::Str("hi".into())],
            named: vec![(Symbol::from_raw(8), Value::Bool(true))],
        };
        s.bind_value(v, make_entity());
        s.bind_value(v, make_entity());
        assert!(!s.is_contradiction());
    }

    #[test]
    fn bind_value_different_entity_is_contradiction() {
        let mut s = Substitution::new();
        let v = vid(1);
        s.bind_value(
            v,
            Value::Entity {
                functor: Symbol::from_raw(7),
                pos: vec![Value::Int(10)],
                named: vec![],
            },
        );
        s.bind_value(
            v,
            Value::Entity {
                functor: Symbol::from_raw(7),
                pos: vec![Value::Int(11)],
                named: vec![],
            },
        );
        assert!(s.is_contradiction());
    }

    #[test]
    fn bind_value_nested_entity_equal_not_contradiction() {
        let mut s = Substitution::new();
        let v = vid(1);
        let make = || Value::Entity {
            functor: Symbol::from_raw(7),
            pos: vec![Value::Tuple {
                pos: vec![Value::Int(1), Value::Str("x".into())],
                named: vec![],
            }],
            named: vec![],
        };
        s.bind_value(v, make());
        s.bind_value(v, make());
        assert!(!s.is_contradiction());
    }

    #[test]
    fn bind_compressed_leaves_non_term_entries_untouched() {
        let mut store = TermStore::new();
        let v1 = vid(1);
        let v2 = vid(2);
        let var_v1 = store.alloc(Term::Var(Var::Global(v1)));
        let target = TermId::from_raw(999);

        let mut s = Substitution::new();
        s.bindings.insert(v2, Value::Term(var_v1));  // v2 → Var(v1)
        s.bindings.insert(vid(3), Value::Int(77));   // non-Term: untouched
        s.bind_compressed(std::iter::once((v1, target)), &store);

        // v2's binding now points through to `target`.
        assert_eq!(s.resolve_with_term(v2), Some(target));
        // v3's non-Term binding is preserved as-is.
        assert!(matches!(s.resolve_as_value(vid(3)), Some(Value::Int(77))));
    }
}
