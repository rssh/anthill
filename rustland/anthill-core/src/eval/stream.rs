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
//! - `Native(...)` — host-supplied closure-driven iterator (test/demo
//!   shortcut — no schema, no row-source identity).
//! - `External(Box<dyn ExternalStream>)` — proposal 026.1 Q4. Trait-driven
//!   variant for queryable persistence backends (file rows, SQL cursors,
//!   API responses). Yields `Value::Entity` rows without `TermStore`
//!   allocation. See proposal 007 §11.
//!
//! The `StreamHandle` is arena-refcounted (same pattern as `ClosureHandle`):
//! cloning bumps the slot's refcount, dropping decrements and frees at zero.

use std::cell::RefCell;
use std::rc::Rc;

use crate::intern::Symbol;
use crate::kb::resolve::SearchStream;
use crate::kb::term::VarId;

use super::value::Value;

/// Trait-driven external row source. Proposal 026.1 Q4 + proposal 007 §11.
///
/// Backends (file-rows, SQL cursors, HTTP responses) implement this to
/// surface row data into the resolver as `Value::Entity` (or any non-
/// `Value::Term` variant) — i.e. without paying the hash-cons tax that
/// `assert_fact` does for a bulk-loaded fact. Each `next` call yields one
/// row; `None` signals exhaustion.
///
/// `description` is a short, human-readable identity for the row source
/// (e.g. `"FileStore[anthill/workitems/]"`, `"SqlStore[audit_entries]"`),
/// surfaced in error messages and diagnostics. Implementors should make
/// it cheap — it's `&str` so there's no per-call allocation.
pub trait ExternalStream {
    fn next(&mut self) -> Option<Value>;
    fn description(&self) -> &str {
        "external-stream"
    }
}

/// Body of a stream. Kept distinct from [`StreamHandle`] so arena slots
/// can be swapped in place (see `split_first` — `Resolver` consumes the
/// underlying `SearchStream` by value on each pump).
pub enum StreamSource {
    /// Wraps a KB resolver search. The `SearchStream` option is `take()`n
    /// on each pump and replaced with the continuation, so the arena slot
    /// is always valid but holds `None` transiently during a pump.
    Resolver {
        search: Option<SearchStream>,
        /// WI-SPGBP — the scoped-KB LAYER this search runs against, when it was made
        /// from one (`execute(loaded(sources), q)`); `None` for the ambient KB.
        ///
        /// THE STREAM OWNS IT, and that is the whole reason the ticket made the `kb`
        /// argument a VALUE rather than adding a bracket operation. This search is
        /// pumped later, by `splitFirst` — a scope popped at a bracket's exit would
        /// leave it resolving against a base that is gone. Holding the handle here
        /// keeps the layer applied for exactly as long as there is a search that
        /// might read it.
        layer: Option<crate::eval::layer_arena::KbHandle>,
    },
    /// WI-714 (proposal 052): a resolver search whose yielded `Solution`s are
    /// MATERIALIZED onto a relation's free variables — the runtime backing of a
    /// `Relation[T]` consumed as a stream. Like `Resolver`, but each pull projects
    /// the answer substitution onto `columns` (`(column name, free VarId)` in the
    /// relation's declaration order) into a named-tuple `Value::Tuple` row —
    /// 1-collapsing to the element for a single column, to `Value::Unit` for zero.
    /// This is the ONE place a relation solution materializes (§Typing 2); the
    /// continuation stays a `MaterializedResolver`, so every pull materializes
    /// identically. `search` is `take()`n per pump like `Resolver`.
    MaterializedResolver {
        search: Option<SearchStream>,
        columns: Rc<[(Symbol, VarId)]>,
    },
    /// No solutions.
    Empty,
    /// WI-20260911-8Y5BE — a resolver search that reported a FAULT. Not `Empty`: a pull
    /// is refused (`stream_misused`) rather than answered as the end of the stream,
    /// because the rows already consumed are not a complete answer set.
    Faulted,
    /// Exactly one solution — the contained `Value`.
    Pure(Option<Value>),
    /// Concatenation: drain `left` first, then `right`.
    MPlus {
        left: StreamHandle,
        right: StreamHandle,
    },
    /// Host-supplied closure iterator. Test/demo shortcut — no schema, no
    /// row-source identity. Production backends should use `External`.
    Native(Box<dyn FnMut() -> Option<Value>>),
    /// Trait-driven external row source (proposal 026.1 Q4). The contract
    /// is that yielded `Value`s are *not* hash-consed into the main
    /// `TermStore` — they enter σ as `Value::Entity` (or another non-Term
    /// variant) and reach the unifier through `TermView`.
    External(Box<dyn ExternalStream>),
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
        Self {
            slots: Vec::new(),
            free_list: Vec::new(),
        }
    }

    fn alloc_raw(&mut self, src: StreamSource) -> u32 {
        if let Some(reused) = self.free_list.pop() {
            self.slots[reused as usize] = Slot {
                source: Some(src),
                refcount: 1,
            };
            reused
        } else {
            let raw = self.slots.len() as u32;
            self.slots.push(Slot {
                source: Some(src),
                refcount: 1,
            });
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
        StreamHandle {
            raw,
            arena: self.clone(),
        }
    }

    /// Number of live stream slots (diagnostic for refcount tests).
    pub fn live(&self) -> usize {
        self.0.borrow().live()
    }
}

impl Default for StreamArenaRef {
    fn default() -> Self {
        Self::new()
    }
}

/// Refcounted stream handle. Clone bumps the slot's refcount; Drop
/// decrements and frees the slot at zero. Not `Copy`: every alias must
/// go through `Clone`.
pub struct StreamHandle {
    raw: u32,
    arena: StreamArenaRef,
}

impl StreamHandle {
    pub fn raw(&self) -> u32 {
        self.raw
    }

    /// Take the source out of the slot, run `f` on it, and put the
    /// (possibly-updated) source back. The slot briefly holds `None` while
    /// `f` runs — splitFirst needs this because the resolver's
    /// `SearchStream::split_first` takes `self` by value.
    ///
    /// WI-20260923-9R5HN — on the HANDLE, reading the arena it carries, as
    /// `ClosureHandle::with` and `MapHandle::with_body` do: a stream minted in one
    /// scratch bridge interpreter and pumped in another would otherwise index a slot
    /// table it does not belong to.
    pub fn with_source_mut<R>(&self, f: impl FnOnce(StreamSource) -> (StreamSource, R)) -> R {
        let src = {
            let mut arena = self.arena.0.borrow_mut();
            arena.slots[self.raw as usize]
                .source
                .take()
                .expect("stream arena slot missing source")
        };
        let (new_src, result) = f(src);
        {
            let mut arena = self.arena.0.borrow_mut();
            arena.slots[self.raw as usize].source = Some(new_src);
        }
        result
    }
}

impl Clone for StreamHandle {
    fn clone(&self) -> Self {
        self.arena.0.borrow_mut().retain_raw(self.raw);
        Self {
            raw: self.raw,
            arena: self.arena.clone(),
        }
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

    /// WI-20260923-9R5HN — a handle pumps the arena that MINTED it: `a` holds `Faulted`
    /// and `b` holds `Empty`, both at slot 0, and `a`'s handle must see `Faulted`.
    #[test]
    fn a_handle_reads_the_arena_that_minted_it() {
        let (a, b) = (StreamArenaRef::new(), StreamArenaRef::new());
        let in_b = b.alloc(StreamSource::Empty);
        let in_a = a.alloc(StreamSource::Faulted);
        assert_eq!(
            in_a.raw(),
            in_b.raw(),
            "both at slot 0 — the case that aliases"
        );
        let faulted = in_a.with_source_mut(|src| {
            let is = matches!(src, StreamSource::Faulted);
            (src, is)
        });
        assert!(faulted, "a's handle reads a's source");
    }

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
