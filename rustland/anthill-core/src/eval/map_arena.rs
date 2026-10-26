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
//! Type erasure: at runtime K and V are gone — the entry's key is a `MapKey`, a
//! literal or a structural fingerprint of the key value. The type checker is
//! responsible for ruling out heterogeneous keys; if user code somehow obtains a
//! value whose key type doesn't match the map's, the lookup just misses.

use std::cell::RefCell;
use std::rc::Rc;

use imbl::{HashMap as ImHashMap, Vector as ImVector};

use crate::kb::subst::Substitution;
use crate::kb::term::Literal;
use crate::kb::term_view::{goal_fingerprint, GoalKey, TermView, ViewHead};
use crate::kb::KnowledgeBase;

use super::value::Value;

/// The slot a `Value` addresses in a `Map`, judged by the value and not by its carrier:
/// it is read through [`TermView`], so a value built by an operation (`Value::Entity`,
/// `Value::Tuple`), read from a fact (`Value::Term`) or bound in a rule body
/// (`Value::Node`) addresses one slot. Built by [`MapKey::of_value`].
///
/// A LITERAL keys as the literal, so `"alice"` is one slot whether it is a native
/// `Value::Str` or a fact's `Term::Const`: a relation column keeps the carrier the search
/// proved it on (WI-20260827-3ZNBC).
///
/// EVERYTHING ELSE keys by its structural fingerprint ([`goal_fingerprint`], the key
/// value-fact dedup uses), with the value first put under it kept beside the key for
/// [`MapKey::to_value`]. So a name is one slot on both of its carriers —
/// `Value::SymbolRef(s)` from `Dictionary.impl` and `Term::Ref(s)` from `lookup_symbol`
/// (WI-1016) — and a nullary constructor, a sort and a namespace-level entity key by
/// their symbol; an unresolved `Term::Ident(s)` is another term and another slot. A
/// `Float` or `BigInt` keys by its literal the same way (`Map[K = Float]` itself is
/// refused by the typer, WI-644).
///
/// NO KEY IS INTERNED: reading a key never writes to the term store, a `Map.get` that
/// misses included.
///
/// Not a key, and a builtin's type error: an unbound variable, which denotes nothing to
/// key on, and a value whose fingerprint bears an `Opaque` leaf — a closure, a stream, a
/// map, a cell, an occurrence the view does not decompose — since no slot could tell two
/// of them apart.
///
/// [`goal_fingerprint`]: crate::kb::term_view::goal_fingerprint
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MapKey {
    Int(i64),
    Bool(bool),
    Str(String),
    Struct(StructKey),
}

/// A structural key: equal and hashed by its fingerprint alone, so the value it keeps —
/// the first one put under it, on whatever carrier — takes no part in which slot it is.
#[derive(Clone, Debug)]
pub struct StructKey {
    shape: GoalKey,
    value: Value,
}

impl PartialEq for StructKey {
    fn eq(&self, other: &Self) -> bool {
        self.shape == other.shape
    }
}

impl Eq for StructKey {}

impl std::hash::Hash for StructKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.shape.hash(state);
    }
}

impl MapKey {
    /// The key `v` addresses, or `None` for a value that is no key (see [`MapKey`]).
    pub fn of_value(kb: &KnowledgeBase, v: &Value) -> Option<Self> {
        match v.head(kb) {
            ViewHead::Const(Literal::Int(n)) => Some(MapKey::Int(n)),
            ViewHead::Const(Literal::Bool(b)) => Some(MapKey::Bool(b)),
            ViewHead::Const(Literal::String(s)) => Some(MapKey::Str(s)),
            ViewHead::Var(_) | ViewHead::Opaque => None,
            _ => {
                let shape = goal_fingerprint(kb, v, &Substitution::new());
                shape.is_opaque_free().then(|| {
                    MapKey::Struct(StructKey {
                        shape,
                        value: v.carried().clone(),
                    })
                })
            }
        }
    }

    /// The key back as a `Value` — what `Map.keys` / `Map.entries` hand out: a literal
    /// as its native value, any other key as the value first put under it. Feeding it
    /// back to [`Self::of_value`] gives the same key, so `Map.get(m, k)` for a `k` out of
    /// `Map.keys(m)` hits.
    pub fn to_value(&self) -> Value {
        match self {
            MapKey::Int(n) => Value::Int(*n),
            MapKey::Bool(b) => Value::Bool(*b),
            MapKey::Str(s) => Value::Str(s.clone()),
            MapKey::Struct(k) => k.value.clone(),
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

    /// Remove a key, preserving the order of the remaining entries. The
    /// `order` scan makes this O(N) (unlike the O(log N) `insert`/`get`);
    /// acceptable because map removal is rare on the interpreter's paths.
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
        Self {
            slots: Vec::new(),
            free_list: Vec::new(),
        }
    }

    fn alloc_raw(&mut self, body: MapBody) -> u32 {
        if let Some(reused) = self.free_list.pop() {
            self.slots[reused as usize] = Slot {
                body: Some(body),
                refcount: 1,
            };
            reused
        } else {
            let raw = self.slots.len() as u32;
            self.slots.push(Slot {
                body: Some(body),
                refcount: 1,
            });
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
        MapHandle {
            raw,
            arena: self.clone(),
        }
    }

    /// Number of live map slots (diagnostic for refcount tests).
    pub fn live(&self) -> usize {
        self.0.borrow().live()
    }
}

impl Default for MapArenaRef {
    fn default() -> Self {
        Self::new()
    }
}

/// Refcounted map handle. Clone bumps the slot's refcount; Drop decrements
/// and frees the slot at zero.
pub struct MapHandle {
    raw: u32,
    arena: MapArenaRef,
}

impl MapHandle {
    pub fn raw(&self) -> u32 {
        self.raw
    }

    /// Borrow the underlying `MapBody` for a read-only callback — from THIS HANDLE'S
    /// OWN arena.
    ///
    /// WI-20260922-BRT4Y — a method on the handle, not on an arena that is handed the
    /// handle. The arena form (`interp.maps.with_body(&h, …)`) indexed the RECEIVER's
    /// arena with `h.raw`, and nothing tied the two together: a handle minted by one
    /// interpreter and read by another indexed a slot table it did not belong to —
    /// out of bounds (a panic, measured), or, worse, some OTHER map that sat at the same
    /// index. It became reachable when `Map`'s operations became visible to the rule-body
    /// operand gate: `Map.size(Map.put(Map.empty(), "a", 1)) = 1` reduces each call in its
    /// own scratch bridge interpreter, so the inner call's map reached the outer call
    /// from another arena. The handle already carries its arena (for its refcount), so
    /// reading through it cannot pick the wrong one.
    pub fn with_body<R>(&self, f: impl FnOnce(&MapBody) -> R) -> R {
        let arena = self.arena.0.borrow();
        let slot = &arena.slots[self.raw as usize];
        let body = slot.body.as_ref().expect("map arena slot missing body");
        f(body)
    }

    /// Clone the underlying `MapBody` — used by `put`/`remove` to derive a
    /// fresh, independent map without touching the original. `MapBody` is
    /// persistent, so this clone is O(1) structural sharing; the subsequent
    /// single-key edit copies only the touched path (O(log N)). Reads this
    /// handle's own arena, for [`Self::with_body`]'s reason.
    pub fn clone_body(&self) -> MapBody {
        self.with_body(|b| b.clone())
    }
    #[allow(dead_code)] // arena handle accessor; kept for future map ops
    pub(crate) fn arena(&self) -> &MapArenaRef {
        &self.arena
    }
}

impl Clone for MapHandle {
    fn clone(&self) -> Self {
        self.arena.0.borrow_mut().retain_raw(self.raw);
        Self {
            raw: self.raw,
            arena: self.arena.clone(),
        }
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
    use crate::intern::Symbol;
    use crate::kb::term::{Term, TermId};

    /// The key `v` addresses, which every row below expects to exist.
    fn key(kb: &KnowledgeBase, v: &Value) -> MapKey {
        MapKey::of_value(kb, v).unwrap_or_else(|| panic!("no key for {v:?}"))
    }

    fn name_key(kb: &KnowledgeBase, s: Symbol) -> MapKey {
        key(kb, &Value::SymbolRef(s))
    }

    fn term_key(kb: &KnowledgeBase, t: TermId) -> MapKey {
        key(kb, &Value::term(t))
    }

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
        let kb = KnowledgeBase::new();
        let kv = vec![
            (Value::Int(7), MapKey::Int(7)),
            (Value::Bool(true), MapKey::Bool(true)),
            (Value::Str("k".into()), MapKey::Str("k".into())),
        ];
        for (v, expected) in kv {
            assert_eq!(MapKey::of_value(&kb, &v), Some(expected.clone()));
            assert!(expected.to_value().scalar_eq(&v));
        }
    }

    /// WI-1016: the two carriers of ONE reflect `Symbol` address ONE map slot.
    ///
    /// `Value::SymbolRef(s)` (what `Dictionary.impl` / `OpRef.op` mint) and
    /// `Value::Term` wrapping the hash-consed `Term::Ref(s)` (what `lookup_symbol`
    /// / `scope` mint) are the same symbol, so a `put` through one must be found
    /// by a `get` through the other.
    #[test]
    fn both_symbol_carriers_key_one_map_slot() {
        let mut kb = KnowledgeBase::new();
        let s = kb.intern("demo.Thing");
        let ref_tid = kb.alloc(Term::Ref(s));

        let via_symbolref = name_key(&kb, s);
        assert_eq!(
            via_symbolref,
            term_key(&kb, ref_tid),
            "a symbol keys the same slot whichever carrier it arrived on",
        );

        // And the round-trip out of `keys` addresses that slot again.
        let mut body = MapBody::new();
        body.insert(via_symbolref.clone(), Value::Int(1));
        let back = body.keys().next().cloned().expect("one key");
        assert_eq!(
            key(&kb, &back.to_value()),
            via_symbolref,
            "a key read back out of the map re-keys to itself",
        );

        // A term-carried LITERAL keys as that literal, so it addresses the same slot
        // its native twin does (WI-20260827-3ZNBC).
        let int_tid = kb.alloc(Term::Const(crate::kb::term::Literal::Int(3)));
        assert_eq!(term_key(&kb, int_tid), MapKey::Int(3));
        assert_eq!(
            term_key(&kb, int_tid),
            key(&kb, &Value::Int(3)),
            "a literal keys the same slot whichever carrier it arrived on",
        );
    }

    /// WI-1023 — the spellings of one name key one slot.
    ///
    /// `resolve_qualified_name_term` used to mint `Fn{c,[],[]}`, bypassing the canon that
    /// rewrites it to `Ref(c)`; WI-20260902-CZJ2N moved the canon into `TermStore::alloc`,
    /// so the two are one `TermId` and this row pins that. The `SymbolRef` carrier keys
    /// with them.
    ///
    /// `Term::Ident` must NOT join them: it is a different term, and keying it as the
    /// name would let one `put` overwrite the other's entry.
    #[test]
    fn a_non_canonicalized_nullary_constructor_keys_as_its_name() {
        let mut kb = KnowledgeBase::new();
        let c = kb.intern("demo.Color.red");
        kb.mark_constructor_symbol(c);

        let ref_tid = kb.alloc(Term::Ref(c));
        let fn_tid = kb.resolve_qualified_name_term("demo.Color.red");
        assert_eq!(
            ref_tid, fn_tid,
            "the mint no longer bypasses the canon — one name, one term"
        );

        let via_ref = term_key(&kb, ref_tid);
        assert_eq!(name_key(&kb, c), via_ref);
        assert_eq!(
            term_key(&kb, fn_tid),
            via_ref,
            "a nullary constructor names its symbol however it is spelled",
        );

        // One slot, reachable through each spelling.
        let mut body = MapBody::new();
        body.insert(via_ref.clone(), Value::Int(4));
        assert_eq!(
            body.get(&name_key(&kb, c)).and_then(|v| match v {
                Value::Int(n) => Some(*n),
                _ => None,
            }),
            Some(4),
        );

        let ident_tid = kb.alloc(Term::Ident(c));
        assert_ne!(
            term_key(&kb, ident_tid),
            via_ref,
            "an unresolved identifier is not the resolved name",
        );

        // A SORT: its two spellings are one term since WI-20260902-JB6RS, and they key
        // alike, so a `Map` keyed by TYPE values cannot tell `S` from `S()`. The symbol
        // must be DEFINED with the sort kind: an `intern`-only one carries no kinds, and
        // the row would pass for the wrong reason.
        let g = kb.global_scope();
        let sort = kb.define_symbol("Color", "demo.Color", crate::intern::SymbolKind::Sort, g);
        assert!(
            kb.has_kind(sort, crate::intern::SymbolKind::Sort) && !kb.is_constructor_symbol(sort),
            "premise: a sort has a type reading and is not a constructor"
        );
        let sort_fn = kb.resolve_qualified_name_term("demo.Color");
        let sort_ref = kb.alloc(Term::Ref(sort));
        assert_eq!(sort_fn, sort_ref, "a sort's nullary application is its bare name");
        assert_eq!(term_key(&kb, sort_fn), term_key(&kb, sort_ref));

        let str_tid = kb.alloc(Term::Const(crate::kb::term::Literal::String("s".into())));
        assert_eq!(term_key(&kb, str_tid), MapKey::Str("s".into()));
        assert_eq!(
            term_key(&kb, str_tid),
            key(&kb, &Value::Str("s".into())),
            "a string keys one slot on either carrier",
        );
    }
}
