//! WI-SPGBP — the arena behind a first-class `KB` value.
//!
//! `execute(loaded(sources), q)` hands anthill code a KB VALUE. That value is a
//! DISCARDABLE LAYER over the interpreter's own knowledge base: [`crate::kb::layer`]
//! measured that a full snapshot of the scoped state costs 0.16 % of one load, so the
//! layer is applied in place and its predecessor state is parked here until the last
//! holder of the value goes away.
//!
//! Mirrors `CellArena` / `MapArena` / `StreamArena`: a slot, a refcount, a handle that
//! retains on clone and releases on drop. ONE THING IS DIFFERENT, and it is the reason
//! this is its own module rather than another copy of that template — **releasing a layer
//! cannot free it**. Restoring a snapshot needs `&mut KnowledgeBase`, which a `Drop` impl
//! has no way to reach. So a release only RETIRES the slot, and
//! [`LayerArenaRef::sweep`] — called by the interpreter where it does hold the KB — is
//! what actually discards.
//!
//! # Layers are a stack, and deferral is correct rather than merely tolerated
//!
//! `stack` holds the live layers innermost-last, and a sweep discards only from the top.
//! When a deeper layer is retired while an inner one is still held, nothing happens yet —
//! and that is the right answer, not a leak worth avoiding: the inner layer's own
//! snapshot was taken WITH the deeper one applied, so restoring it yields "base + deeper
//! layer", and the deeper restore then yields the base. Unwinding in any other order
//! would install a state that never existed.
//!
//! The same fact read from the other side is the caveat a caller has to know: layers
//! COMPOSE IN CREATION ORDER. Two live layers means the second sees the first, because
//! the KB they both scope is one KB. See [`crate::kb::layer`] for why that is the
//! deliberate consequence of measuring the alternative.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::kb::layer::KbScopedSnapshot;
use crate::kb::KnowledgeBase;

struct Slot {
    /// The state to restore when this layer is discarded; `None` once swept.
    snapshot: Option<KbScopedSnapshot>,
    refcount: u32,
}

pub(crate) struct LayerArena {
    slots: Vec<Slot>,
    /// Live layers, innermost LAST. A sweep discards only from the back.
    stack: Vec<u32>,
}

impl LayerArena {
    fn new() -> Self {
        Self {
            slots: Vec::new(),
            stack: Vec::new(),
        }
    }
}

/// The arena, plus the flag [`LayerArenaRef::sweep`] reads before touching it.
struct Shared {
    arena: RefCell<LayerArena>,
    /// Has any slot's refcount reached zero since the last sweep?
    ///
    /// OUTSIDE the `RefCell` on purpose. `sweep` runs once per iteration of the
    /// interpreter's trampoline — the hottest loop there is — and a run with no layers
    /// at all must pay one `Cell` read there, not a `RefCell` borrow.
    retired: Cell<bool>,
}

/// A shared handle on the arena. Cloned into every [`KbHandle`], and held by the
/// interpreter.
#[derive(Clone)]
pub(crate) struct LayerArenaRef(Rc<Shared>);

impl LayerArenaRef {
    pub(crate) fn new() -> Self {
        Self(Rc::new(Shared {
            arena: RefCell::new(LayerArena::new()),
            retired: Cell::new(false),
        }))
    }

    /// Push a layer whose predecessor state is `snapshot`, returning the owning handle.
    ///
    /// The CALLER has already applied the layer to the KB — this only parks what it
    /// displaced. Keeping the two steps apart is deliberate: the load that makes a layer
    /// can FAIL, and a caller that has to restore its own snapshot on the failure path
    /// never registers a slot it would then have to unwind.
    pub(crate) fn push(&self, snapshot: KbScopedSnapshot) -> KbHandle {
        let mut arena = self.0.arena.borrow_mut();
        let raw = arena.slots.len() as u32;
        arena.slots.push(Slot {
            snapshot: Some(snapshot),
            refcount: 1,
        });
        arena.stack.push(raw);
        drop(arena);
        KbHandle {
            raw,
            arena: self.clone(),
        }
    }

    /// WI-SPGBP — retain the INNERMOST live layer, or `None` when none is applied.
    ///
    /// This is what makes "a lazy stream holds the KB it was made from" TRUE rather than
    /// approximately true. A search is built against the KB AS IT STANDS — every layer
    /// currently applied, not just the one the caller happened to name — so pinning the
    /// argument alone leaves two holes: `execute(kb(), q)` under a live layer would pin
    /// NOTHING, and `execute(A, q)` with a later layer `B` on top would pin only `A`
    /// while the search reads `A + B`. In both, a discard between the call and the pull
    /// silently changes the answers.
    ///
    /// The innermost handle closes both, because layers unwind innermost-first: holding
    /// the top stops the top being swept, and [`Self::sweep`] will not reach past it to
    /// anything below. ONE handle pins the whole stack.
    pub(crate) fn retain_innermost(&self) -> Option<KbHandle> {
        let raw = {
            let mut arena = self.0.arena.borrow_mut();
            let raw = *arena.stack.last()?;
            arena.slots[raw as usize].refcount += 1;
            raw
        };
        Some(KbHandle {
            raw,
            arena: self.clone(),
        })
    }

    /// Is there anything for [`Self::sweep`] to do? ONE `Cell` read, no `RefCell` borrow
    /// and no refcount traffic.
    ///
    /// [`Interpreter::sweep_layers`] runs once per iteration of the evaluator's
    /// trampoline — the hottest loop in the interpreter — and a program that never called
    /// `KB.loaded` must pay essentially nothing there. This is that gate.
    pub(crate) fn has_retired(&self) -> bool {
        self.0.retired.get()
    }

    /// Discard every layer whose last holder has gone, innermost first. Answers HOW MANY
    /// were discarded, so the caller knows whether state computed under a layer has to go
    /// with it.
    ///
    /// Idempotent, and O(1) when there is nothing to do. Slots are never reused, so a
    /// swept `raw` can only be reached through a handle that no longer exists.
    pub(crate) fn sweep(&self, kb: &mut KnowledgeBase) -> usize {
        let mut discarded = 0;
        loop {
            if !self.0.retired.get() {
                return discarded;
            }
            let snapshot = {
                let mut arena = self.0.arena.borrow_mut();
                match arena.stack.last().copied() {
                    Some(top) if arena.slots[top as usize].refcount == 0 => {
                        arena.stack.pop();
                        arena.slots[top as usize].snapshot.take()
                    }
                    // The innermost layer is still held. A deeper retired layer waits for
                    // it — see the module docs on why unwinding out of order would
                    // install a state that never existed. Clearing the flag is safe: the
                    // inner layer's own release sets it again.
                    _ => {
                        self.0.retired.set(false);
                        return discarded;
                    }
                }
            };
            match snapshot {
                // Restored with NO arena borrow held: `restore_scoped` drops the layer's
                // own tables, whose values can own arena handles of their own.
                Some(s) => {
                    kb.restore_scoped(s);
                    discarded += 1;
                }
                None => unreachable!("WI-SPGBP: a live layer slot always holds its snapshot"),
            }
        }
    }

    /// Live (unswept) layer count — the reader the refcount tests assert on.
    pub(crate) fn depth(&self) -> usize {
        self.0.arena.borrow().stack.len()
    }
}

impl Default for LayerArenaRef {
    fn default() -> Self {
        Self::new()
    }
}

/// A first-class `KB` value: an owning reference to one layer.
///
/// Identity is `(arena, raw)`. Cloning retains; dropping releases, and the LAST release
/// retires the slot for the next [`LayerArenaRef::sweep`].
pub struct KbHandle {
    raw: u32,
    arena: LayerArenaRef,
}

impl KbHandle {
    pub fn raw(&self) -> u32 {
        self.raw
    }
}

impl Clone for KbHandle {
    fn clone(&self) -> Self {
        {
            let mut arena = self.arena.0.arena.borrow_mut();
            arena.slots[self.raw as usize].refcount += 1;
        }
        Self {
            raw: self.raw,
            arena: self.arena.clone(),
        }
    }
}

impl Drop for KbHandle {
    fn drop(&mut self) {
        let mut arena = self.arena.0.arena.borrow_mut();
        let slot = &mut arena.slots[self.raw as usize];
        debug_assert!(slot.refcount > 0, "WI-SPGBP: release on a swept layer slot");
        slot.refcount -= 1;
        if slot.refcount == 0 {
            self.arena.0.retired.set(true);
        }
    }
}

impl std::fmt::Debug for KbHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "KbHandle({})", self.raw)
    }
}

impl PartialEq for KbHandle {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw && Rc::ptr_eq(&self.arena.0, &other.arena.0)
    }
}
