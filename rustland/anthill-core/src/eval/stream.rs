//! LogicalStream runtime (proposal 026 §KB queries and LogicalStream).
//!
//! A stream is a pull-based producer of `Value`s. The `splitFirst` primitive
//! returns `Option[Pair[T, Stream]]` — `none` at end, `some(pair(v, rest))`
//! otherwise. Every other stream operation in the stdlib (`head`, `tail`,
//! `collect`, `isEmpty`, ...) derives from this via rules.
//!
//! Runtime variants:
//! - `Resolver(SearchStream)` — wraps the KB SLD resolver. Each pump yields
//!   one `Solution` (opaque substitution handle for v1).
//! - `Empty` — zero solutions.
//! - `Pure(Value)` — singleton.
//! - `MPlus { left, right }` — concatenation (left first, then right).
//! - `Native(...)` — escape hatch for external data sources (not yet
//!   exercised; reserved for Q4 external-backed KBs).
//!
//! The `StreamHandle` is arena-refcounted (same pattern as `ClosureHandle`):
//! cloning bumps the slot's refcount, dropping decrements and frees at zero.

use std::cell::RefCell;
use std::rc::Rc;

use crate::kb::resolve::SearchStream;

use super::value::Value;

/// Body of a stream. Kept distinct from [`StreamHandle`] so arena slots
/// can be swapped in place (see `split_first` — `Resolver` consumes the
/// underlying `SearchStream` by value on each pump).
pub enum StreamSource {
    /// Wraps a KB resolver search. The `SearchStream` option is `take()`n
    /// on each pump and replaced with the continuation, so the arena slot
    /// is always valid but holds `None` transiently during a pump.
    Resolver(Option<SearchStream>),
    /// No solutions.
    Empty,
    /// Exactly one solution — the contained `Value`.
    Pure(Option<Value>),
    /// Concatenation: drain `left` first, then `right`.
    MPlus { left: StreamHandle, right: StreamHandle },
    /// Host-supplied iterator — see Q4. Left as a placeholder `Native`
    /// variant so the enum shape is stable; no callers construct it yet.
    Native(Box<dyn FnMut() -> Option<Value>>),
}

struct Slot {
    source: Option<StreamSource>,
    refcount: u32,
}

pub(crate) struct StreamArena {
    slots: Vec<Slot>,
    free_list: Vec<u32>,
}

impl StreamArena {
    fn new() -> Self {
        Self { slots: Vec::new(), free_list: Vec::new() }
    }

    fn alloc_raw(&mut self, src: StreamSource) -> u32 {
        if let Some(reused) = self.free_list.pop() {
            self.slots[reused as usize] = Slot { source: Some(src), refcount: 1 };
            reused
        } else {
            let raw = self.slots.len() as u32;
            self.slots.push(Slot { source: Some(src), refcount: 1 });
            raw
        }
    }

    fn retain_raw(&mut self, raw: u32) {
        self.slots[raw as usize].refcount += 1;
    }

    fn release_and_take(&mut self, raw: u32) -> Option<StreamSource> {
        let slot = &mut self.slots[raw as usize];
        debug_assert!(slot.refcount > 0, "release on freed stream slot {raw}");
        slot.refcount -= 1;
        if slot.refcount == 0 {
            self.free_list.push(raw);
            slot.source.take()
        } else {
            None
        }
    }

    fn live(&self) -> usize {
        self.slots.iter().filter(|s| s.source.is_some()).count()
    }
}

#[derive(Clone)]
pub struct StreamArenaRef(Rc<RefCell<StreamArena>>);

impl StreamArenaRef {
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(StreamArena::new())))
    }

    pub fn alloc(&self, src: StreamSource) -> StreamHandle {
        let raw = self.0.borrow_mut().alloc_raw(src);
        StreamHandle { raw, arena: self.clone() }
    }

    /// Take the source out of the slot, run `f` on it, and put the
    /// (possibly-updated) source back. The slot briefly holds `None` while
    /// `f` runs — splitFirst needs this because the resolver's
    /// `SearchStream::split_first` takes `self` by value.
    pub fn with_source_mut<R>(
        &self,
        h: &StreamHandle,
        f: impl FnOnce(StreamSource) -> (StreamSource, R),
    ) -> R {
        let src = {
            let mut arena = self.0.borrow_mut();
            arena.slots[h.raw as usize].source.take()
                .expect("stream arena slot missing source")
        };
        let (new_src, result) = f(src);
        {
            let mut arena = self.0.borrow_mut();
            arena.slots[h.raw as usize].source = Some(new_src);
        }
        result
    }

    /// Number of live stream slots (diagnostic for refcount tests).
    pub fn live(&self) -> usize { self.0.borrow().live() }
}

impl Default for StreamArenaRef {
    fn default() -> Self { Self::new() }
}

/// Refcounted stream handle. Clone bumps the slot's refcount; Drop
/// decrements and frees the slot at zero. Not `Copy`: every alias must
/// go through `Clone`.
pub struct StreamHandle {
    raw: u32,
    arena: StreamArenaRef,
}

impl StreamHandle {
    pub fn raw(&self) -> u32 { self.raw }
    #[allow(dead_code)]  // arena handle accessor; kept for future stream ops
    pub(crate) fn arena(&self) -> &StreamArenaRef { &self.arena }
}

impl Clone for StreamHandle {
    fn clone(&self) -> Self {
        self.arena.0.borrow_mut().retain_raw(self.raw);
        Self { raw: self.raw, arena: self.arena.clone() }
    }
}

impl Drop for StreamHandle {
    fn drop(&mut self) {
        // Defer dropping the released source until after the arena borrow
        // is gone — an MPlus source holds further StreamHandles whose
        // Drop impls would try to reborrow.
        let freed = self.arena.0.borrow_mut().release_and_take(self.raw);
        drop(freed);
    }
}

impl std::fmt::Debug for StreamHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "StreamHandle({})", self.raw)
    }
}

impl PartialEq for StreamHandle {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw && Rc::ptr_eq(&self.arena.0, &other.arena.0)
    }
}
impl Eq for StreamHandle {}

impl std::hash::Hash for StreamHandle {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_stream_live_drop() {
        let arena = StreamArenaRef::new();
        let h = arena.alloc(StreamSource::Empty);
        assert_eq!(arena.live(), 1);
        drop(h);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn clone_bumps_refcount() {
        let arena = StreamArenaRef::new();
        let h = arena.alloc(StreamSource::Empty);
        let h2 = h.clone();
        drop(h);
        assert_eq!(arena.live(), 1, "slot alive while h2 holds a ref");
        drop(h2);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn mplus_drop_cascades_through_children() {
        let arena = StreamArenaRef::new();
        let left = arena.alloc(StreamSource::Empty);
        let right = arena.alloc(StreamSource::Empty);
        let merged = arena.alloc(StreamSource::MPlus { left, right });
        assert_eq!(arena.live(), 3);
        drop(merged);
        assert_eq!(arena.live(), 0, "cascaded drop frees children");
    }
}
