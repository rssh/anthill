//! Substitution arena — refcounted storage for first-class `Substitution`
//! values (proposal 026.1 §Substitution + WI-047 follow-up).
//!
//! Mirrors the `StreamArena` / `ClosureArena` shape: an arena slot owns (behind an
//! `Rc`, so a read holds no arena borrow — `SubstHandle::with_subst`) the
//! whole `kb::subst::Substitution` struct (including its `parent` chain);
//! `SubstHandle` is an arena slot index with refcount-on-clone semantics.
//! Compose produces a new arena entry — we never share parent chains across
//! slots, keeping lifetime reasoning simple.

use std::cell::RefCell;
use std::rc::Rc;

use crate::kb::subst::Substitution;

struct Slot {
    /// Behind an `Rc` so a read can take the substitution OUT of the arena's borrow
    /// before looking at it (`SubstHandle::with_subst`); the arena's own refcount below
    /// still decides when the slot is freed.
    subst: Option<Rc<Substitution>>,
    refcount: u32,
}

pub(crate) struct SubstArena {
    slots: Vec<Slot>,
    free_list: Vec<u32>,
}

impl SubstArena {
    fn new() -> Self {
        Self {
            slots: Vec::new(),
            free_list: Vec::new(),
        }
    }

    fn alloc_raw(&mut self, subst: Rc<Substitution>) -> u32 {
        if let Some(reused) = self.free_list.pop() {
            self.slots[reused as usize] = Slot {
                subst: Some(subst),
                refcount: 1,
            };
            reused
        } else {
            let raw = self.slots.len() as u32;
            self.slots.push(Slot {
                subst: Some(subst),
                refcount: 1,
            });
            raw
        }
    }

    fn retain_raw(&mut self, raw: u32) {
        self.slots[raw as usize].refcount += 1;
    }

    fn release_and_take(&mut self, raw: u32) -> Option<Rc<Substitution>> {
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
        let raw = self.0.borrow_mut().alloc_raw(Rc::new(subst));
        SubstHandle {
            raw,
            arena: self.clone(),
        }
    }

    /// Number of live substitution slots (diagnostic for refcount tests).
    pub fn live(&self) -> usize {
        self.0.borrow().live()
    }
}

impl Default for SubstArenaRef {
    fn default() -> Self {
        Self::new()
    }
}

/// Refcounted substitution handle. Clone bumps the slot's refcount; Drop
/// decrements and frees the slot at zero.
pub struct SubstHandle {
    raw: u32,
    arena: SubstArenaRef,
}

impl SubstHandle {
    pub fn raw(&self) -> u32 {
        self.raw
    }

    /// Borrow the underlying `Substitution` for a read-only callback — from THIS
    /// HANDLE'S OWN arena.
    ///
    /// WI-20260923-9R5HN — a method on the handle, for `MapHandle::with_body`'s reason
    /// (WI-20260922-BRT4Y). The arena form (`interp.subst_arena().with_subst(&h, …)`)
    /// indexed the RECEIVER's slot table with `h.raw`, and nothing tied the two
    /// together: a substitution minted by one interpreter and read by another indexed
    /// a table it did not belong to — out of bounds (a panic), or a populated slot
    /// holding some OTHER substitution, answered silently. That is reachable as soon
    /// as a `Substitution` operation is interpreter-mapped, because the rule-body
    /// operand gate reduces each call in its own scratch bridge interpreter, and
    /// `Substitution.lookup` already was. The handle carries its arena (for its
    /// refcount), so reading through it cannot pick the wrong one.
    ///
    /// AND NO ARENA BORROW IS HELD WHILE `f` RUNS: the slot's `Rc` is cloned under a
    /// momentary borrow and `f` reads that. `f` routinely clones binding values
    /// (`Substitution.bindings`, `compose`), and a binding that is itself a
    /// `Value::Substitution` of this arena bumps its refcount through `borrow_mut` — a
    /// `RefCell already borrowed` panic while the read held the borrow (MEASURED,
    /// `a_read_may_clone_a_handle_into_its_own_arena`). Two reads of one handle nest
    /// (`compose(s, s)`), which a take-and-restore read would not allow.
    pub fn with_subst<R>(&self, f: impl FnOnce(&Substitution) -> R) -> R {
        let subst = Rc::clone(
            self.arena.0.borrow().slots[self.raw as usize]
                .subst
                .as_ref()
                .expect("subst arena slot missing subst"),
        );
        f(&subst)
    }
}

impl Clone for SubstHandle {
    fn clone(&self) -> Self {
        self.arena.0.borrow_mut().retain_raw(self.raw);
        Self {
            raw: self.raw,
            arena: self.arena.clone(),
        }
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

    /// WI-20260923-9R5HN — a handle reads the arena that MINTED it. Two arenas each
    /// hold a substitution at slot 0; the handle from `a` must answer `a`'s. The
    /// arena-receiver form this replaced (`b.with_subst(&h, …)`) indexed whichever
    /// arena it was called on, and would have answered `b`'s binding here — the
    /// bridge-interpreter shape, where a value minted by one interpreter is read by
    /// another. `cell_arena`'s and `map_arena`'s twins are the same test.
    #[test]
    fn a_handle_reads_the_arena_that_minted_it() {
        use crate::eval::Value;
        use crate::kb::term::VarId;
        let mut kb = crate::kb::KnowledgeBase::new();
        let x = VarId::new(0, kb.intern("x"));
        let bound_to = |n: i64| {
            let mut s = Substitution::new();
            s.bindings.insert(x, Value::Int(n));
            s
        };
        let a = SubstArenaRef::new();
        let b = SubstArenaRef::new();
        let in_b = b.alloc(bound_to(7));
        let in_a = a.alloc(bound_to(1));
        assert_eq!(
            in_a.raw(),
            in_b.raw(),
            "both at slot 0 — the case that aliases"
        );
        let read = |h: &SubstHandle| h.with_subst(|s| s.bindings.get(&x).cloned());
        assert!(
            matches!(read(&in_a), Some(Value::Int(1))),
            "a's handle reads a's substitution"
        );
        assert!(
            matches!(read(&in_b), Some(Value::Int(7))),
            "and b's reads b's"
        );
    }

    /// WI-20260923-9R5HN — the read holds NO arena borrow while the callback runs, so the
    /// callback may clone a value that is itself a handle into the SAME arena.
    /// `Substitution.bindings` and `compose` do exactly that (`val.clone()`,
    /// `reify_value`), and cloning a `Value::Substitution` bumps its slot's refcount
    /// through `borrow_mut`. CONTROL, MEASURED with the callback run under the slot
    /// borrow (the shape this read had): `already borrowed: BorrowMutError`.
    #[test]
    fn a_read_may_clone_a_handle_into_its_own_arena() {
        use crate::eval::Value;
        use crate::kb::term::VarId;
        let mut kb = crate::kb::KnowledgeBase::new();
        let x = VarId::new(0, kb.intern("x"));
        let arena = SubstArenaRef::new();
        let inner = arena.alloc(Substitution::new());
        let mut outer = Substitution::new();
        outer.bindings.insert(x, Value::Substitution(inner));
        let h = arena.alloc(outer);
        let cloned = h.with_subst(|s| s.bindings.get(&x).cloned());
        assert!(matches!(cloned, Some(Value::Substitution(_))));
        drop(cloned);
        drop(h);
        assert_eq!(
            arena.live(),
            0,
            "both slots reclaimed once the handles are gone"
        );
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
