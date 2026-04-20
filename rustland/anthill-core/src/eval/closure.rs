//! Closures + closure arena.
//!
//! A closure captures the lexical environment at the lambda site and the
//! body term. When applied, it pushes a fresh frame with the captured env
//! extended by the parameter binding.
//!
//! The handle (`ClosureHandle`) is a refcounted smart pointer: cloning bumps
//! the arena slot's refcount; dropping decrements and frees the slot at
//! zero. This lets `Value::clone`/`Value::drop` maintain closure lifetime
//! without threading the interpreter through every clone site. See WI-055
//! (and WI-058 for the eventual mark-sweep GC that handles cycles).

use std::cell::RefCell;
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::term::TermId;

use super::value::Value;

pub struct Closure {
    /// The full param pattern (var / tuple / constructor / literal / wildcard).
    /// Matched against the arg at call time via `pattern::match_pattern`, so
    /// `lambda (a, b) -> ...` works naturally — the caller passes a tuple
    /// and the closure destructures it on entry.
    pub param_pattern: TermId,
    pub body: TermId,
    pub env: SmallVec<[(Symbol, Value); 4]>,
}

struct Slot {
    value: Option<Closure>,
    refcount: u32,
}

/// Internal storage: slot array + free-list. `ClosureArenaRef` wraps this
/// behind `Rc<RefCell<...>>` so clones/drops of `ClosureHandle` can bump
/// the refcount without threading the interpreter through every site.
pub(crate) struct ClosureArena {
    slots: Vec<Slot>,
    free_list: Vec<u32>,
}

impl ClosureArena {
    fn new() -> Self {
        Self { slots: Vec::new(), free_list: Vec::new() }
    }

    fn alloc_raw(&mut self, c: Closure) -> u32 {
        if let Some(reused) = self.free_list.pop() {
            self.slots[reused as usize] = Slot { value: Some(c), refcount: 1 };
            reused
        } else {
            let raw = self.slots.len() as u32;
            self.slots.push(Slot { value: Some(c), refcount: 1 });
            raw
        }
    }

    fn get_raw(&self, raw: u32) -> &Closure {
        self.slots[raw as usize].value.as_ref()
            .expect("closure arena slot already released")
    }

    fn get_raw_mut(&mut self, raw: u32) -> &mut Closure {
        self.slots[raw as usize].value.as_mut()
            .expect("closure arena slot already released")
    }

    fn retain_raw(&mut self, raw: u32) {
        self.slots[raw as usize].refcount += 1;
    }

    /// Decrement refcount; if it hits zero, take the `Closure` out and return
    /// it so the caller can drop it **after** releasing the arena borrow.
    /// Dropping in-place would recursively drop any `Value::Closure` in the
    /// env, and those drops would try to reborrow the arena → panic.
    fn release_and_take(&mut self, raw: u32) -> Option<Closure> {
        let slot = &mut self.slots[raw as usize];
        debug_assert!(slot.refcount > 0, "release on freed closure slot {raw}");
        slot.refcount -= 1;
        if slot.refcount == 0 {
            self.free_list.push(raw);
            slot.value.take()
        } else {
            None
        }
    }

    /// Number of currently-live slots (occupied, not in the free-list).
    /// Exposed for reclamation observability — diagnostics and tests.
    fn live(&self) -> usize {
        self.slots.iter().filter(|s| s.value.is_some()).count()
    }
}

/// Shared reference to a closure arena. Cheap to clone (refcount bump on
/// the underlying `Rc`). Held by `Interpreter` and by every `ClosureHandle`.
#[derive(Clone)]
pub struct ClosureArenaRef(Rc<RefCell<ClosureArena>>);

impl ClosureArenaRef {
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(ClosureArena::new())))
    }

    /// Store a closure, returning an owning handle (initial refcount = 1).
    pub fn alloc(&self, c: Closure) -> ClosureHandle {
        let raw = self.0.borrow_mut().alloc_raw(c);
        ClosureHandle { raw, arena: self.clone() }
    }

    /// Read a closure via a scoped borrow; the closure `f` runs while the
    /// arena's borrow is held, so `f` must not trigger further arena
    /// operations (no closure alloc/retain/release within it). Use this for
    /// extracting `Copy` fields only — to snapshot non-Copy data like the
    /// env, go through [`Self::take_env`] which drops the borrow before
    /// the `Clone` impls run.
    pub fn with<R>(&self, h: &ClosureHandle, f: impl FnOnce(&Closure) -> R) -> R {
        let borrow = self.0.borrow();
        f(borrow.get_raw(h.raw))
    }

    /// Clone a closure's captured env without holding the arena borrow
    /// across the clone. `Value::clone` for a `Value::Closure` needs
    /// `borrow_mut` (to bump the slot refcount), which panics if any other
    /// borrow is already held. We swap the env out under a brief
    /// `borrow_mut`, clone it with no borrow held, then swap it back.
    ///
    /// Safe because the interpreter is single-threaded and synchronous:
    /// nothing else runs during the swap-out-swap-in window, so observers
    /// never see an empty env.
    pub fn clone_env(
        &self,
        h: &ClosureHandle,
    ) -> SmallVec<[(Symbol, Value); 4]> {
        let mut stolen = {
            let mut arena = self.0.borrow_mut();
            let c = arena.get_raw_mut(h.raw);
            std::mem::take(&mut c.env)
        };
        let cloned = stolen.clone();
        {
            let mut arena = self.0.borrow_mut();
            std::mem::swap(&mut arena.get_raw_mut(h.raw).env, &mut stolen);
        }
        cloned
    }

    /// Live-slot count — for reclamation observability.
    pub fn live(&self) -> usize { self.0.borrow().live() }
}

impl Default for ClosureArenaRef {
    fn default() -> Self { Self::new() }
}

/// Refcounted handle. Clone increments the slot refcount, Drop decrements.
/// Not `Copy` by design: every copy must go through `Clone` so the refcount
/// stays correct. Cycles are not collected — see WI-058.
pub struct ClosureHandle {
    raw: u32,
    arena: ClosureArenaRef,
}

impl ClosureHandle {
    pub fn raw(&self) -> u32 { self.raw }
}

impl Clone for ClosureHandle {
    fn clone(&self) -> Self {
        self.arena.0.borrow_mut().retain_raw(self.raw);
        Self { raw: self.raw, arena: self.arena.clone() }
    }
}

impl Drop for ClosureHandle {
    fn drop(&mut self) {
        // Defer the dying `Closure`'s own drop until after the arena borrow
        // is released — its env may contain further `Value::Closure`s whose
        // drops need to reacquire `borrow_mut`, which a stacked borrow on
        // this thread would refuse.
        let freed = self.arena.0.borrow_mut().release_and_take(self.raw);
        drop(freed);
    }
}

impl std::fmt::Debug for ClosureHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ClosureHandle({})", self.raw)
    }
}

impl PartialEq for ClosureHandle {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw && Rc::ptr_eq(&self.arena.0, &other.arena.0)
    }
}
impl Eq for ClosureHandle {}

impl std::hash::Hash for ClosureHandle {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dummy_closure() -> Closure {
        Closure {
            param_pattern: TermId::from_raw(0),
            body: TermId::from_raw(0),
            env: SmallVec::new(),
        }
    }

    #[test]
    fn alloc_get_drop_reclaims() {
        let arena = ClosureArenaRef::new();
        let h = arena.alloc(dummy_closure());
        assert_eq!(arena.live(), 1);
        drop(h);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn clone_bumps_refcount() {
        let arena = ClosureArenaRef::new();
        let h = arena.alloc(dummy_closure());
        let h2 = h.clone();
        drop(h);
        assert_eq!(arena.live(), 1, "slot still alive while h2 holds a ref");
        drop(h2);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn free_list_reuses_slot() {
        let arena = ClosureArenaRef::new();
        let h1 = arena.alloc(dummy_closure());
        let raw1 = h1.raw();
        drop(h1);
        let h2 = arena.alloc(dummy_closure());
        assert_eq!(h2.raw(), raw1);
    }

    #[test]
    fn with_reads_closure() {
        let arena = ClosureArenaRef::new();
        let h = arena.alloc(Closure {
            param_pattern: TermId::from_raw(7),
            body: TermId::from_raw(0),
            env: SmallVec::new(),
        });
        let pat = arena.with(&h, |c| c.param_pattern);
        assert_eq!(pat, TermId::from_raw(7));
    }
}
