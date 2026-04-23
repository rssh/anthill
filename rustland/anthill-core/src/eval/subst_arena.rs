//! Substitution arena — refcounted storage for first-class `Substitution`
//! values (proposal 026.1 §Substitution + WI-047 follow-up).
//!
//! Mirrors the `StreamArena` / `ClosureArena` shape: an arena slot owns the
//! whole `kb::subst::Substitution` struct (including its `parent` chain);
//! `SubstHandle` is an arena slot index with refcount-on-clone semantics.
//! Compose produces a new arena entry — we never share parent chains across
//! slots, keeping lifetime reasoning simple.

use std::cell::RefCell;
use std::rc::Rc;

use crate::kb::subst::Substitution;

struct Slot {
    subst: Option<Substitution>,
    refcount: u32,
}

pub(crate) struct SubstArena {
    slots: Vec<Slot>,
    free_list: Vec<u32>,
}

impl SubstArena {
    fn new() -> Self {
        Self { slots: Vec::new(), free_list: Vec::new() }
    }

    fn alloc_raw(&mut self, subst: Substitution) -> u32 {
        if let Some(reused) = self.free_list.pop() {
            self.slots[reused as usize] = Slot { subst: Some(subst), refcount: 1 };
            reused
        } else {
            let raw = self.slots.len() as u32;
            self.slots.push(Slot { subst: Some(subst), refcount: 1 });
            raw
        }
    }

    fn retain_raw(&mut self, raw: u32) {
        self.slots[raw as usize].refcount += 1;
    }

    fn release_and_take(&mut self, raw: u32) -> Option<Substitution> {
        let slot = &mut self.slots[raw as usize];
        debug_assert!(slot.refcount > 0, "release on freed subst slot {raw}");
        slot.refcount -= 1;
        if slot.refcount == 0 {
            self.free_list.push(raw);
            slot.subst.take()
        } else {
            None
        }
    }

    fn live(&self) -> usize {
        self.slots.iter().filter(|s| s.subst.is_some()).count()
    }
}

#[derive(Clone)]
pub struct SubstArenaRef(Rc<RefCell<SubstArena>>);

impl SubstArenaRef {
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(SubstArena::new())))
    }

    pub fn alloc(&self, subst: Substitution) -> SubstHandle {
        let raw = self.0.borrow_mut().alloc_raw(subst);
        SubstHandle { raw, arena: self.clone() }
    }

    /// Borrow the underlying `Substitution` for a read-only callback.
    pub fn with_subst<R>(&self, h: &SubstHandle, f: impl FnOnce(&Substitution) -> R) -> R {
        let arena = self.0.borrow();
        let slot = &arena.slots[h.raw as usize];
        let subst = slot.subst.as_ref().expect("subst arena slot missing subst");
        f(subst)
    }

    /// Number of live substitution slots (diagnostic for refcount tests).
    pub fn live(&self) -> usize { self.0.borrow().live() }
}

impl Default for SubstArenaRef {
    fn default() -> Self { Self::new() }
}

/// Refcounted substitution handle. Clone bumps the slot's refcount; Drop
/// decrements and frees the slot at zero.
pub struct SubstHandle {
    raw: u32,
    arena: SubstArenaRef,
}

impl SubstHandle {
    pub fn raw(&self) -> u32 { self.raw }
    pub(crate) fn arena(&self) -> &SubstArenaRef { &self.arena }
}

impl Clone for SubstHandle {
    fn clone(&self) -> Self {
        self.arena.0.borrow_mut().retain_raw(self.raw);
        Self { raw: self.raw, arena: self.arena.clone() }
    }
}

impl Drop for SubstHandle {
    fn drop(&mut self) {
        // Defer dropping the released substitution until after the arena
        // borrow is released — Substitution's own Drop can recursively free
        // parent-chain entries.
        let freed = self.arena.0.borrow_mut().release_and_take(self.raw);
        drop(freed);
    }
}

impl std::fmt::Debug for SubstHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SubstHandle({})", self.raw)
    }
}

impl PartialEq for SubstHandle {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw && Rc::ptr_eq(&self.arena.0, &other.arena.0)
    }
}
impl Eq for SubstHandle {}

impl std::hash::Hash for SubstHandle {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_and_drop_reclaims() {
        let arena = SubstArenaRef::new();
        let h = arena.alloc(Substitution::new());
        assert_eq!(arena.live(), 1);
        drop(h);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn clone_bumps_refcount() {
        let arena = SubstArenaRef::new();
        let h = arena.alloc(Substitution::new());
        let h2 = h.clone();
        drop(h);
        assert_eq!(arena.live(), 1);
        drop(h2);
        assert_eq!(arena.live(), 0);
    }
}
