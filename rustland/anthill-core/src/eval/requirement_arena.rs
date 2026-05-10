//! Requirement arena — refcounted storage for first-class requirement
//! values (the runtime side of the operation-call model, WI-223).
//!
//! A requirement value is the materialization of a resolved spec impl.
//! Per `docs/design/operation-call-model.md` §"Runtime: frame, requirement
//! value, closure", each slot stores `{ functor: <impl_sort>, requirements:
//! [<sub-handles>] }` — the impl identity plus the deps it was constructed
//! with. Bodies dispatch through requirement values via
//! `requirement_at_current(i, op_short)`; sub-deps are reached through
//! `requirement_at_sort(chain, k)` projections into the arena.
//!
//! Mirrors `CellArena` / `MapArena` / `SubstArena`: Clone bumps the slot's
//! refcount; Drop decrements and frees at zero. The held `requirements`
//! vec is taken out under `borrow_mut` and dropped after the arena borrow
//! is released — its handles cascade-decrement, which would re-borrow.
//! No-cycles policy (operation-call-model design §"No-cycles policy") means
//! refcount alone is sufficient for cleanup.

use std::cell::RefCell;
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::Symbol;

struct Slot {
    functor: Option<Symbol>,
    requirements: Option<SmallVec<[RequirementHandle; 1]>>,
    refcount: u32,
}

pub(crate) struct RequirementArena {
    slots: Vec<Slot>,
    free_list: Vec<u32>,
}

impl RequirementArena {
    fn new() -> Self {
        Self { slots: Vec::new(), free_list: Vec::new() }
    }

    fn alloc_raw(
        &mut self,
        functor: Symbol,
        requirements: SmallVec<[RequirementHandle; 1]>,
    ) -> u32 {
        let slot = Slot {
            functor: Some(functor),
            requirements: Some(requirements),
            refcount: 1,
        };
        if let Some(reused) = self.free_list.pop() {
            self.slots[reused as usize] = slot;
            reused
        } else {
            let raw = self.slots.len() as u32;
            self.slots.push(slot);
            raw
        }
    }

    fn retain_raw(&mut self, raw: u32) {
        self.slots[raw as usize].refcount += 1;
    }

    /// Decrement refcount; if it hits zero, take the held `requirements`
    /// vec out and return it. The caller drops the vec after releasing
    /// the arena borrow — sub-handles' `Drop` decrement other arena
    /// slots, which would re-borrow.
    fn release_and_take(&mut self, raw: u32) -> Option<SmallVec<[RequirementHandle; 1]>> {
        let slot = &mut self.slots[raw as usize];
        debug_assert!(slot.refcount > 0, "release on freed requirement slot {raw}");
        slot.refcount -= 1;
        if slot.refcount == 0 {
            self.free_list.push(raw);
            slot.functor = None;
            slot.requirements.take()
        } else {
            None
        }
    }

    fn live(&self) -> usize {
        self.slots.iter().filter(|s| s.functor.is_some()).count()
    }
}

#[derive(Clone)]
pub struct RequirementArenaRef(Rc<RefCell<RequirementArena>>);

impl RequirementArenaRef {
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(RequirementArena::new())))
    }

    /// Allocate a fresh slot holding `(functor, requirements)`; return an
    /// owning handle (initial refcount = 1). The `requirements` vec is
    /// moved in; caller's prior handles in it are now owned by the slot.
    pub fn alloc(
        &self,
        functor: Symbol,
        requirements: SmallVec<[RequirementHandle; 1]>,
    ) -> RequirementHandle {
        let raw = self.0.borrow_mut().alloc_raw(functor, requirements);
        RequirementHandle { raw, arena: self.clone() }
    }

    /// Return the impl functor stored at `h`. Read under a brief borrow
    /// — Symbol is Copy so no callback dance is needed.
    pub fn functor(&self, h: &RequirementHandle) -> Symbol {
        self.0
            .borrow()
            .slots[h.raw as usize]
            .functor
            .expect("requirement arena slot missing functor")
    }

    /// Project the k-th bundled sub-requirement of `h`. Bumps the
    /// sub-handle's refcount (clone) so the returned handle owns its own
    /// reference. Used by the eval to reduce
    /// `requirement_at_sort(chain, k)`.
    ///
    /// Implementation: read the sub-handle's `raw` under a plain borrow,
    /// then bump refcount + build a fresh handle under a fresh `borrow_mut`.
    /// `RequirementHandle::clone` would re-enter the same arena's
    /// `RefCell` while we're still holding the read borrow, panicking
    /// with "already borrowed".
    pub fn project(&self, h: &RequirementHandle, k: usize) -> RequirementHandle {
        let sub_raw = {
            let arena = self.0.borrow();
            let slot = &arena.slots[h.raw as usize];
            let reqs = slot.requirements.as_ref()
                .expect("requirement arena slot missing requirements");
            reqs.get(k)
                .map(|sub| sub.raw)
                .unwrap_or_else(|| panic!(
                    "requirement_at_sort: index {k} out of range (slot has {} sub-requirements)",
                    reqs.len()
                ))
        };
        self.0.borrow_mut().retain_raw(sub_raw);
        RequirementHandle { raw: sub_raw, arena: self.clone() }
    }

    /// Number of bundled sub-requirements at `h`.
    pub fn arity(&self, h: &RequirementHandle) -> usize {
        self.0
            .borrow()
            .slots[h.raw as usize]
            .requirements
            .as_ref()
            .map(|r| r.len())
            .unwrap_or(0)
    }

    /// Live-slot count — diagnostic for refcount tests.
    pub fn live(&self) -> usize { self.0.borrow().live() }
}

impl Default for RequirementArenaRef {
    fn default() -> Self { Self::new() }
}

/// Refcounted requirement handle. Clone bumps the slot refcount; Drop
/// decrements and frees the slot at zero. Identity is `(arena, raw)`.
pub struct RequirementHandle {
    raw: u32,
    arena: RequirementArenaRef,
}

impl RequirementHandle {
    pub fn raw(&self) -> u32 { self.raw }

    pub fn functor(&self) -> Symbol {
        self.arena.functor(self)
    }

    pub fn project(&self, k: usize) -> RequirementHandle {
        self.arena.project(self, k)
    }

    pub fn arity(&self) -> usize {
        self.arena.arity(self)
    }
}

impl Clone for RequirementHandle {
    fn clone(&self) -> Self {
        self.arena.0.borrow_mut().retain_raw(self.raw);
        Self { raw: self.raw, arena: self.arena.clone() }
    }
}

impl Drop for RequirementHandle {
    fn drop(&mut self) {
        // Defer the cascade: take the held requirements vec out under
        // `borrow_mut`, then drop it after releasing the arena borrow.
        // Sub-handle drops would otherwise re-borrow the same arena.
        let cascade = self.arena.0.borrow_mut().release_and_take(self.raw);
        drop(cascade);
    }
}

impl std::fmt::Debug for RequirementHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RequirementHandle({})", self.raw)
    }
}

impl PartialEq for RequirementHandle {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw && Rc::ptr_eq(&self.arena.0, &other.arena.0)
    }
}
impl Eq for RequirementHandle {}

impl std::hash::Hash for RequirementHandle {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(raw: u32) -> Symbol { Symbol::from_raw(raw) }

    #[test]
    fn alloc_and_drop_reclaims() {
        let arena = RequirementArenaRef::new();
        let h = arena.alloc(sym(1), SmallVec::new());
        assert_eq!(arena.live(), 1);
        drop(h);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn clone_bumps_refcount() {
        let arena = RequirementArenaRef::new();
        let h = arena.alloc(sym(1), SmallVec::new());
        let h2 = h.clone();
        drop(h);
        assert_eq!(arena.live(), 1);
        drop(h2);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn free_list_reuses_slot() {
        let arena = RequirementArenaRef::new();
        let h1 = arena.alloc(sym(1), SmallVec::new());
        let raw1 = h1.raw();
        drop(h1);
        let h2 = arena.alloc(sym(2), SmallVec::new());
        assert_eq!(h2.raw(), raw1);
    }

    #[test]
    fn cascading_drop_releases_subrequirements() {
        // Parent requirement bundles a child. Dropping the parent should
        // cascade: release the parent's slot, then drop the child handle
        // it owned, which releases the child's slot. Live count goes
        // 2 → 0 after a single drop on the parent.
        let arena = RequirementArenaRef::new();
        let child = arena.alloc(sym(10), SmallVec::new());
        let mut bundle: SmallVec<[RequirementHandle; 1]> = SmallVec::new();
        bundle.push(child);
        let parent = arena.alloc(sym(20), bundle);
        assert_eq!(arena.live(), 2);
        drop(parent);
        assert_eq!(arena.live(), 0,
            "dropping parent must cascade-drop its bundled child");
    }

    #[test]
    fn shared_subrequirement_kept_alive_via_other_owner() {
        // Two parents share a child via clone. Dropping one parent
        // releases its slot but keeps the child alive (the other parent
        // still owns a reference).
        let arena = RequirementArenaRef::new();
        let child = arena.alloc(sym(10), SmallVec::new());
        let mut bundle1: SmallVec<[RequirementHandle; 1]> = SmallVec::new();
        bundle1.push(child.clone());
        let mut bundle2: SmallVec<[RequirementHandle; 1]> = SmallVec::new();
        bundle2.push(child);
        let parent1 = arena.alloc(sym(20), bundle1);
        let parent2 = arena.alloc(sym(30), bundle2);
        assert_eq!(arena.live(), 3);
        drop(parent1);
        assert_eq!(arena.live(), 2,
            "child must stay live while parent2 still references it");
        drop(parent2);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn project_returns_owned_subrequirement() {
        let arena = RequirementArenaRef::new();
        let child = arena.alloc(sym(10), SmallVec::new());
        let mut bundle: SmallVec<[RequirementHandle; 1]> = SmallVec::new();
        bundle.push(child);
        let parent = arena.alloc(sym(20), bundle);
        // Project out the 0-th sub-requirement — caller now owns its
        // own handle to the child's slot (refcount bumped).
        let projected = parent.project(0);
        assert_eq!(projected.functor(), sym(10));
        // Drop the parent — cascade would normally free the child, but
        // `projected` holds a reference, so the child slot survives.
        drop(parent);
        assert_eq!(arena.live(), 1,
            "projected handle must keep child alive after parent drop");
        drop(projected);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn nested_chain_cascades_in_order() {
        // env_LLI → env_LI → env_I (Example 8 from operation-call-model
        // §"Impls have their own requires from day one"). Dropping the
        // outermost cascades all three.
        let arena = RequirementArenaRef::new();
        let env_i = arena.alloc(sym(1), SmallVec::new());
        let mut bundle_li: SmallVec<[RequirementHandle; 1]> = SmallVec::new();
        bundle_li.push(env_i);
        let env_li = arena.alloc(sym(2), bundle_li);
        let mut bundle_lli: SmallVec<[RequirementHandle; 1]> = SmallVec::new();
        bundle_lli.push(env_li);
        let env_lli = arena.alloc(sym(3), bundle_lli);
        assert_eq!(arena.live(), 3);
        drop(env_lli);
        assert_eq!(arena.live(), 0,
            "drop on outermost env must cascade through env_LI → env_I");
    }

    #[test]
    fn distinct_handles_compare_by_slot() {
        let arena = RequirementArenaRef::new();
        let a = arena.alloc(sym(1), SmallVec::new());
        let a_clone = a.clone();
        let b = arena.alloc(sym(2), SmallVec::new());
        assert_eq!(a, a_clone);
        assert_ne!(a, b);
    }

    #[test]
    fn handles_from_different_arenas_are_unequal() {
        let arena1 = RequirementArenaRef::new();
        let arena2 = RequirementArenaRef::new();
        let h1 = arena1.alloc(sym(1), SmallVec::new());
        let h2 = arena2.alloc(sym(1), SmallVec::new());
        assert_eq!(h1.raw(), h2.raw());
        assert_ne!(h1, h2);
    }

    #[test]
    fn arity_reports_bundled_count() {
        let arena = RequirementArenaRef::new();
        let c1 = arena.alloc(sym(1), SmallVec::new());
        let c2 = arena.alloc(sym(2), SmallVec::new());
        let mut bundle: SmallVec<[RequirementHandle; 1]> = SmallVec::new();
        bundle.push(c1);
        bundle.push(c2);
        let parent = arena.alloc(sym(10), bundle);
        assert_eq!(parent.arity(), 2);
    }
}
