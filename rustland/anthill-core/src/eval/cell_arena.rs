//! Cell arena — refcounted storage for first-class `Cell` values
//! (proposal 037 §"Cell[V]" + design doc `docs/design/cell-runtime.md`).
//!
//! Mirrors `MapArena` / `SubstArena` / `StreamArena`: an arena slot owns
//! the held `Value`; `CellHandle` is an arena slot index with
//! refcount-on-clone semantics. Unlike the other arenas, Cell slots are
//! mutable in place — `Cell.set` overwrites the slot's value via
//! [`CellArenaRef::write`].
//!
//! Identity is the slot index: every `Cell.new` allocates a fresh slot,
//! so two cells with the same initial value are still distinct. This is
//! the opaque-handle scheme from proposal 037 §"Resource type plug-in"
//! (and matches Rust `Cell::new` / OCaml `ref` / Haskell `IORef`).

use std::cell::RefCell;
use std::rc::Rc;

use super::value::Value;

struct Slot {
    value: Option<Value>,
    refcount: u32,
}

pub(crate) struct CellArena {
    slots: Vec<Slot>,
    free_list: Vec<u32>,
}

impl CellArena {
    fn new() -> Self {
        Self { slots: Vec::new(), free_list: Vec::new() }
    }

    fn alloc_raw(&mut self, value: Value) -> u32 {
        if let Some(reused) = self.free_list.pop() {
            self.slots[reused as usize] = Slot { value: Some(value), refcount: 1 };
            reused
        } else {
            let raw = self.slots.len() as u32;
            self.slots.push(Slot { value: Some(value), refcount: 1 });
            raw
        }
    }

    fn retain_raw(&mut self, raw: u32) {
        self.slots[raw as usize].refcount += 1;
    }

    /// Decrement refcount; if it hits zero, take the held `Value` out and
    /// return it. The caller drops it after releasing the arena borrow —
    /// the value's own `Drop` may transitively decrement refcounts on
    /// other handles, which would re-borrow the arena.
    fn release_and_take(&mut self, raw: u32) -> Option<Value> {
        let slot = &mut self.slots[raw as usize];
        debug_assert!(slot.refcount > 0, "release on freed cell slot {raw}");
        slot.refcount -= 1;
        if slot.refcount == 0 {
            self.free_list.push(raw);
            slot.value.take()
        } else {
            None
        }
    }

    fn live(&self) -> usize {
        self.slots.iter().filter(|s| s.value.is_some()).count()
    }
}

#[derive(Clone)]
pub struct CellArenaRef(Rc<RefCell<CellArena>>);

impl CellArenaRef {
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(CellArena::new())))
    }

    /// Allocate a fresh slot holding `value`; return an owning handle
    /// (initial refcount = 1).
    pub fn alloc(&self, value: Value) -> CellHandle {
        let raw = self.0.borrow_mut().alloc_raw(value);
        CellHandle { raw, arena: self.clone() }
    }

    /// Read the held value via a scoped borrow. The callback runs while
    /// the arena's `borrow` is held — it must not trigger further arena
    /// operations on the same arena (no allocs / writes / drops within).
    pub fn with_value<R>(&self, h: &CellHandle, f: impl FnOnce(&Value) -> R) -> R {
        let arena = self.0.borrow();
        let slot = &arena.slots[h.raw as usize];
        let v = slot.value.as_ref().expect("cell arena slot missing value");
        f(v)
    }

    /// Snapshot the held value. Briefly takes the slot's value out under
    /// `borrow_mut`, clones it with no borrow held, then puts the original
    /// back. Pattern from `ClosureArenaRef::clone_env`: avoids holding a
    /// borrow across the recursive `Value::clone` (which may bump
    /// refcounts on nested arena handles, requiring its own
    /// `borrow_mut`). A Cell holding another Cell handle (either today,
    /// before the cycle-prevention typer rule lands, or under the
    /// chain-aware rule which accepts `Cell[Cell[Int]]` since it can't
    /// cycle) would re-enter `borrow_mut` on the same arena under a
    /// plain borrow + clone — hence the swap-out.
    pub fn read(&self, h: &CellHandle) -> Value {
        let stolen = {
            let mut arena = self.0.borrow_mut();
            let slot = &mut arena.slots[h.raw as usize];
            slot.value.take().expect("cell arena slot missing value")
        };
        let cloned = stolen.clone();
        {
            let mut arena = self.0.borrow_mut();
            arena.slots[h.raw as usize].value = Some(stolen);
        }
        cloned
    }

    /// Replace the slot's value with `new`. Returns the prior value so the
    /// caller can drop it after releasing the arena borrow (avoids the
    /// recursive-drop reborrow problem; same constraint as
    /// `release_and_take`).
    pub fn write(&self, h: &CellHandle, new: Value) -> Value {
        let mut arena = self.0.borrow_mut();
        let slot = &mut arena.slots[h.raw as usize];
        let prev = slot.value.take().expect("cell arena slot missing value");
        slot.value = Some(new);
        prev
    }

    /// Live-slot count — diagnostic for refcount tests.
    pub fn live(&self) -> usize { self.0.borrow().live() }
}

impl Default for CellArenaRef {
    fn default() -> Self { Self::new() }
}

/// Refcounted cell handle. Clone bumps the slot refcount; Drop decrements
/// and frees the slot at zero. Identity is `(arena, raw)`: two handles
/// with the same `raw` from the same arena are the same cell.
pub struct CellHandle {
    raw: u32,
    arena: CellArenaRef,
}

impl CellHandle {
    pub fn raw(&self) -> u32 { self.raw }
}

impl Clone for CellHandle {
    fn clone(&self) -> Self {
        self.arena.0.borrow_mut().retain_raw(self.raw);
        Self { raw: self.raw, arena: self.arena.clone() }
    }
}

impl Drop for CellHandle {
    fn drop(&mut self) {
        // Defer dropping the held Value until after the arena borrow is
        // released — the value may transitively own other arena handles
        // whose Drop would re-borrow.
        let freed = self.arena.0.borrow_mut().release_and_take(self.raw);
        drop(freed);
    }
}

impl std::fmt::Debug for CellHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CellHandle({})", self.raw)
    }
}

impl PartialEq for CellHandle {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw && Rc::ptr_eq(&self.arena.0, &other.arena.0)
    }
}
impl Eq for CellHandle {}

impl std::hash::Hash for CellHandle {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_and_drop_reclaims() {
        let arena = CellArenaRef::new();
        let h = arena.alloc(Value::Int(7));
        assert_eq!(arena.live(), 1);
        drop(h);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn clone_bumps_refcount() {
        let arena = CellArenaRef::new();
        let h = arena.alloc(Value::Int(1));
        let h2 = h.clone();
        drop(h);
        assert_eq!(arena.live(), 1);
        drop(h2);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn free_list_reuses_slot() {
        let arena = CellArenaRef::new();
        let h1 = arena.alloc(Value::Int(0));
        let raw1 = h1.raw();
        drop(h1);
        let h2 = arena.alloc(Value::Int(0));
        assert_eq!(h2.raw(), raw1);
    }

    #[test]
    fn write_replaces_value() {
        let arena = CellArenaRef::new();
        let h = arena.alloc(Value::Int(1));
        let prev = arena.write(&h, Value::Int(42));
        assert_eq!(prev.as_int(), Some(1));
        assert_eq!(arena.read(&h).as_int(), Some(42));
    }

    #[test]
    fn fresh_cells_are_distinct() {
        let arena = CellArenaRef::new();
        let a = arena.alloc(Value::Int(0));
        let b = arena.alloc(Value::Int(0));
        assert_ne!(a.raw(), b.raw(), "fresh cells must have distinct slot indices");
    }

    #[test]
    fn distinct_handles_compare_by_slot() {
        let arena = CellArenaRef::new();
        let a = arena.alloc(Value::Int(0));
        let a_clone = a.clone();
        let b = arena.alloc(Value::Int(0));
        assert_eq!(a, a_clone);
        assert_ne!(a, b);
    }

    #[test]
    fn handles_from_different_arenas_are_unequal() {
        let arena1 = CellArenaRef::new();
        let arena2 = CellArenaRef::new();
        let h1 = arena1.alloc(Value::Int(0));
        let h2 = arena2.alloc(Value::Int(0));
        // Same raw (both slot 0), but different arenas.
        assert_eq!(h1.raw(), h2.raw());
        assert_ne!(h1, h2);
    }
}
