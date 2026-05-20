//! Map arena — refcounted storage for first-class `Map` values
//! (proposal 035 §Mechanics).
//!
//! Mirrors the `SubstArena` / `StreamArena` shape: an arena slot owns the
//! whole `MapBody`; `MapHandle` is an arena slot index with refcount-on-clone
//! semantics. Mutating ops (`put`, `remove`) produce a new arena entry — Map
//! values are immutable from anthill's point of view. `MapBody` is itself a
//! persistent (structurally-shared) map, so deriving a new entry is O(1) +
//! the single-key edit rather than an O(N) full copy.
//!
//! Type erasure: at runtime K and V are gone — the entry's key is one of
//! `MapKey` (Int / Bool / Str / Term hash). The type checker is responsible
//! for ruling out heterogeneous keys; if user code somehow obtains a value
//! whose key type doesn't match the map's, the lookup just misses.

use std::cell::RefCell;
use std::rc::Rc;

use imbl::{HashMap as ImHashMap, Vector as ImVector};

use crate::kb::term::TermId;

use super::value::Value;

/// Hashable / orderable key view over a `Value`. Map operations canonicalize
/// the user-supplied `Value::Int` / `Value::Bool` / `Value::Str` /
/// `Value::Term` into one of these variants. Other variants (Tuple, Entity,
/// Closure, Stream, …) are not supported as keys for the v1 builtin —
/// inserting one is a runtime type error.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MapKey {
    Int(i64),
    Bool(bool),
    Str(String),
    /// Hash-consed term — TermId is structural identity in the KB so two
    /// equal terms map to the same slot.
    Term(TermId),
}

impl MapKey {
    pub fn try_from_value(v: &Value) -> Option<Self> {
        match v {
            Value::Int(n) => Some(MapKey::Int(*n)),
            Value::Bool(b) => Some(MapKey::Bool(*b)),
            Value::Str(s) => Some(MapKey::Str(s.clone())),
            Value::Term(tid) => Some(MapKey::Term(*tid)),
            _ => None,
        }
    }

    pub fn to_value(&self) -> Value {
        match self {
            MapKey::Int(n) => Value::Int(*n),
            MapKey::Bool(b) => Value::Bool(*b),
            MapKey::Str(s) => Value::Str(s.clone()),
            MapKey::Term(tid) => Value::Term(*tid),
        }
    }
}

/// Owned map content: a structurally-shared persistent map preserving
/// insertion order. `lookup` answers get / contains / insert in O(log N);
/// `order` records each key's first-insertion position so keys / values /
/// entries iterate in insertion order — the documented `Map` contract,
/// exercised by `map_keys_values_entries_preserve_insertion_order`. Stable
/// order matters for byte-identical test fixtures and for diagnostics that
/// reflect program order rather than hash-table order.
///
/// Both halves are persistent (`imbl`), so `Clone` is O(1) structural
/// sharing. That makes the arena's copy-on-write `put` / `remove` cheap:
/// `clone_body` no longer copies the whole map, so building an N-entry map
/// by folding `put` drops from O(N²) to O(N log N).
#[derive(Clone, Default)]
pub struct MapBody {
    lookup: ImHashMap<MapKey, Value>,
    order: ImVector<MapKey>,
}

impl MapBody {
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert or update. A new key is appended to `order`; re-inserting an
    /// existing key keeps its original position and only updates the value
    /// (matching `IndexMap::insert` semantics the builtins relied on).
    pub fn insert(&mut self, key: MapKey, value: Value) {
        if self.lookup.insert(key.clone(), value).is_none() {
            self.order.push_back(key);
        }
    }

    pub fn get(&self, key: &MapKey) -> Option<&Value> {
        self.lookup.get(key)
    }

    pub fn contains_key(&self, key: &MapKey) -> bool {
        self.lookup.contains_key(key)
    }

    /// Remove a key, preserving the order of the remaining entries.
    pub fn shift_remove(&mut self, key: &MapKey) {
        if self.lookup.remove(key).is_some() {
            if let Some(pos) = self.order.iter().position(|k| k == key) {
                self.order.remove(pos);
            }
        }
    }

    pub fn len(&self) -> usize {
        self.order.len()
    }

    pub fn keys(&self) -> impl Iterator<Item = &MapKey> {
        self.order.iter()
    }

    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.order
            .iter()
            .map(move |k| self.lookup.get(k).expect("order/lookup invariant"))
    }

    pub fn iter(&self) -> impl Iterator<Item = (&MapKey, &Value)> {
        self.order
            .iter()
            .map(move |k| (k, self.lookup.get(k).expect("order/lookup invariant")))
    }
}

struct Slot {
    body: Option<MapBody>,
    refcount: u32,
}

pub(crate) struct MapArena {
    slots: Vec<Slot>,
    free_list: Vec<u32>,
}

impl MapArena {
    fn new() -> Self {
        Self { slots: Vec::new(), free_list: Vec::new() }
    }

    fn alloc_raw(&mut self, body: MapBody) -> u32 {
        if let Some(reused) = self.free_list.pop() {
            self.slots[reused as usize] = Slot { body: Some(body), refcount: 1 };
            reused
        } else {
            let raw = self.slots.len() as u32;
            self.slots.push(Slot { body: Some(body), refcount: 1 });
            raw
        }
    }

    fn retain_raw(&mut self, raw: u32) {
        self.slots[raw as usize].refcount += 1;
    }

    fn release_and_take(&mut self, raw: u32) -> Option<MapBody> {
        let slot = &mut self.slots[raw as usize];
        debug_assert!(slot.refcount > 0, "release on freed map slot {raw}");
        slot.refcount -= 1;
        if slot.refcount == 0 {
            self.free_list.push(raw);
            slot.body.take()
        } else {
            None
        }
    }

    fn live(&self) -> usize {
        self.slots.iter().filter(|s| s.body.is_some()).count()
    }
}

#[derive(Clone)]
pub struct MapArenaRef(Rc<RefCell<MapArena>>);

impl MapArenaRef {
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(MapArena::new())))
    }

    pub fn alloc(&self, body: MapBody) -> MapHandle {
        let raw = self.0.borrow_mut().alloc_raw(body);
        MapHandle { raw, arena: self.clone() }
    }

    /// Borrow the underlying `MapBody` for a read-only callback.
    pub fn with_body<R>(&self, h: &MapHandle, f: impl FnOnce(&MapBody) -> R) -> R {
        let arena = self.0.borrow();
        let slot = &arena.slots[h.raw as usize];
        let body = slot.body.as_ref().expect("map arena slot missing body");
        f(body)
    }

    /// Clone the underlying `MapBody` — used by `put`/`remove` to derive a
    /// fresh, independent map without touching the original. `MapBody` is
    /// persistent, so this clone is O(1) structural sharing; the subsequent
    /// single-key edit copies only the touched path (O(log N)).
    pub fn clone_body(&self, h: &MapHandle) -> MapBody {
        self.with_body(h, |b| b.clone())
    }

    /// Number of live map slots (diagnostic for refcount tests).
    pub fn live(&self) -> usize { self.0.borrow().live() }
}

impl Default for MapArenaRef {
    fn default() -> Self { Self::new() }
}

/// Refcounted map handle. Clone bumps the slot's refcount; Drop decrements
/// and frees the slot at zero.
pub struct MapHandle {
    raw: u32,
    arena: MapArenaRef,
}

impl MapHandle {
    pub fn raw(&self) -> u32 { self.raw }
    #[allow(dead_code)]  // arena handle accessor; kept for future map ops
    pub(crate) fn arena(&self) -> &MapArenaRef { &self.arena }
}

impl Clone for MapHandle {
    fn clone(&self) -> Self {
        self.arena.0.borrow_mut().retain_raw(self.raw);
        Self { raw: self.raw, arena: self.arena.clone() }
    }
}

impl Drop for MapHandle {
    fn drop(&mut self) {
        let freed = self.arena.0.borrow_mut().release_and_take(self.raw);
        drop(freed);
    }
}

impl std::fmt::Debug for MapHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MapHandle({})", self.raw)
    }
}

impl PartialEq for MapHandle {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw && Rc::ptr_eq(&self.arena.0, &other.arena.0)
    }
}
impl Eq for MapHandle {}

impl std::hash::Hash for MapHandle {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_and_drop_reclaims() {
        let arena = MapArenaRef::new();
        let h = arena.alloc(MapBody::new());
        assert_eq!(arena.live(), 1);
        drop(h);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn clone_bumps_refcount() {
        let arena = MapArenaRef::new();
        let h = arena.alloc(MapBody::new());
        let h2 = h.clone();
        drop(h);
        assert_eq!(arena.live(), 1);
        drop(h2);
        assert_eq!(arena.live(), 0);
    }

    #[test]
    fn map_key_round_trips() {
        let kv = vec![
            (Value::Int(7), MapKey::Int(7)),
            (Value::Bool(true), MapKey::Bool(true)),
            (Value::Str("k".into()), MapKey::Str("k".into())),
        ];
        for (v, expected) in kv {
            assert_eq!(MapKey::try_from_value(&v), Some(expected.clone()));
            assert!(expected.to_value().scalar_eq(&v));
        }
    }
}
