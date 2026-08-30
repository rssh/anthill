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
//! `MapKey` (Int / Bool / Str / Symbol / Term hash). The type checker is
//! responsible for ruling out heterogeneous keys; if user code somehow obtains a
//! value whose key type doesn't match the map's, the lookup just misses.

use std::cell::RefCell;
use std::rc::Rc;

use imbl::{HashMap as ImHashMap, Vector as ImVector};

use crate::intern::Symbol;
use crate::kb::term::{Literal, Term, TermId};
use crate::kb::term_view::{TermView, ViewHead};
use crate::kb::KnowledgeBase;

use super::value::Value;

/// Hashable / orderable key view over a `Value`. Map operations canonicalize
/// the user-supplied `Value::Int` / `Value::Bool` / `Value::Str` /
/// `Value::SymbolRef` / `Value::Term` into one of these variants. Other variants
/// (Tuple, Entity, Closure, Stream, …) are not supported as keys for the v1
/// builtin — inserting one is a runtime type error.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MapKey {
    Int(i64),
    Bool(bool),
    Str(String),
    /// A named symbol — the key BOTH carriers of a reflect `Symbol` collapse to.
    /// See [`MapKey::try_from_value`] for why it is a variant of its own rather
    /// than a `Term(Term::Ref(s))`.
    Ref(Symbol),
    /// Hash-consed term — TermId is structural identity in the KB so two
    /// equal terms map to the same slot.
    Term(TermId),
}

impl MapKey {
    /// The key `v` addresses, or `None` for a carrier a v1 `Map` cannot key on.
    ///
    /// TAKES THE KB TO CANONICALIZE, and that is what the `Ref` variant is for.
    /// A reflect `Symbol` rides on TWO carriers — `Value::SymbolRef(s)` from
    /// `Dictionary.impl` / `OpRef.op` / `OpRef.named`, and `Value::Term` wrapping
    /// `Term::Ref(s)` from `lookup_symbol` / `scope` — and a `Map` is a STORE KEY,
    /// so keying them apart would put one symbol in two slots: `Map.get(m,
    /// lookup_symbol("…"))` would miss an entry `Map.put` stored under
    /// `Dictionary.impl(d)`. This is the same rule `TermPrinter::write_symbol_ref`
    /// enforces for the printed spelling (WI-1015).
    ///
    /// WI-20260827-3ZNBC APPLIES THAT RULE TO LITERALS, which ride on the same two
    /// carriers for the same reason: a relation column keeps whatever carrier the
    /// search proved it on, so `"alice"` reaches a map key as `Value::Str` from a
    /// host call and as `Value::Term(Const(…))` from a fact match. Keying them apart
    /// put one string in two slots and `Map.get` answered `none()` — see the arms
    /// below, and the assertions that used to pin the split.
    ///
    /// The SYMBOL rewrite COLLAPSES NOTHING that was not already one key: `Term::Ref` is
    /// hash-consed, so there is exactly one `TermId` per symbol and `Term(t) ↔
    /// Ref(s)` is a bijection. Deliberately NOT routed through
    /// [`KnowledgeBase::value_symbol`], which is the right reader for "does this
    /// value NAME something" but is WIDER by three carriers — and they do not all
    /// fail the same way, so one blanket "widening is unsafe" would be wrong:
    ///
    ///  - `Term::Ident(s)` — a widening here MERGES KEYS. `Ident(s)` and `Ref(s)`
    ///    are distinct terms today, so collapsing them makes one `put` silently
    ///    overwrite the other's entry. This is the case that decides the reader.
    ///  - `Value::Node(Expr::Ref(s))` — not keyed at all: `None`, so `Map.put`
    ///    hard-errors. A REFUSAL, which is the right failure mode for a carrier
    ///    whose occurrence identity a map key cannot represent. (WI-20260827-3ZNBC
    ///    keys a Const-headed occurrence, and ONLY that: a literal's identity is the
    ///    literal, which a `MapKey` represents exactly. The refusal above is
    ///    unchanged for every other occurrence.)
    ///
    /// THE `Term` ARM ASKS `ViewHead`, NOT `Term::Ref` (WI-1023) — "is this term a
    /// NAME", not "is it spelled `Ref`". `resolve_qualified_name_term` deliberately
    /// bypasses [`KnowledgeBase::alloc`]'s WI-511 canon, so a non-canonicalized
    /// nullary constructor `Fn{c,[],[]}` exists in the store; it IS the same name as
    /// `Ref(c)` and `functor_view_head` already reads it as `ViewHead::Ref(c)`, so
    /// the by-spelling match declined it and accepted a key SPLIT — the mirror image
    /// of the `Ident` merge, and the wrong direction for the same reason. Reading
    /// the head keeps `Ident` distinct for free: it heads as `ViewHead::Ident`, so
    /// the widening reaches exactly the spellings of one name and no further.
    ///
    /// THE CANON IS GATED ON `is_constructor_symbol`, AND THAT GATE IS THE POINT,
    /// not a residual gap. `functor_view_head` rewrites a nullary `Fn` only for a
    /// registered CONSTRUCTOR; for a sort or type param, `Ref(s)` and `Fn{s,[],[]}`
    /// are not two spellings of one name at all — they are WI-391's
    /// wildcard-vs-concrete type-dispatch distinction, which `alloc`'s own canon
    /// says outright it must not disturb. Merging those two would be the `Ident`
    /// mistake with different symbols. So `resolve_qualified_name_term("…Color")`
    /// (a sort) keeps its own key by design, while `…Color.red` (a constructor)
    /// joins its name's; both are driven.
    pub fn try_from_value(kb: &KnowledgeBase, v: &Value) -> Option<Self> {
        match v {
            Value::Int(n) => Some(MapKey::Int(*n)),
            Value::Bool(b) => Some(MapKey::Bool(*b)),
            Value::Str(s) => Some(MapKey::Str(s.clone())),
            Value::SymbolRef(s) => Some(MapKey::Ref(*s)),
            // A HANDLE OVER A LITERAL KEYS AS THAT LITERAL (WI-20260827-3ZNBC), so
            // `m.get("alice")` finds the entry a relation drain put under a
            // `Value::Term(Const("alice"))`. This is a MERGE, and the right one: the
            // two carriers DENOTE one string, and a map is keyed by what a key IS.
            // It used to split — a term-carried literal took `MapKey::Term(tid)` —
            // which was invisible while the drain reified every column into a native
            // scalar, and became a silent `none()` from `Map.get` the moment a column
            // kept its own carrier. Read off the TERM rather than through `head`,
            // which would build a `ViewHead::Const` by cloning the payload for the
            // Float/BigInt arms that do not use it (WI-1023).
            //
            // FLOAT AND BIGINT STAY ON `MapKey::Term`, and that is not an oversight:
            // `MapKey` has no variant for either, so their NATIVE twins are refused
            // outright (`None` below) — `Float` deliberately, since WI-644 refuses
            // `Map[K = Float]` for want of lawful equality. The hash-consed `TermId`
            // is a sound key for a term-carried one (one `TermId` per structurally
            // equal const), so this keeps exactly the behaviour it had; the native/
            // handle asymmetry for `BigInt` predates this and is untouched.
            Value::Term { id: tid, .. } => match kb.get_term(*tid) {
                Term::Const(Literal::Int(n)) => Some(MapKey::Int(*n)),
                Term::Const(Literal::Bool(b)) => Some(MapKey::Bool(*b)),
                Term::Const(Literal::String(s)) => Some(MapKey::Str(s.clone())),
                Term::Const(_) => Some(MapKey::Term(*tid)),
                _ => match v.head(kb) {
                    ViewHead::Ref(s) => Some(MapKey::Ref(s)),
                    _ => Some(MapKey::Term(*tid)),
                },
            },
            // The occurrence carrier answers the SAME two questions the arms above do
            // — "what literal is this" and "what name is this" — and gives the same
            // key back, so one entity or one string addresses one slot however it was
            // proved. What it CANNOT answer here is a structural non-literal: its
            // identity is the term it denotes, and minting that needs `&mut kb` to
            // intern. That case is not refused, it is HANDLED ONE LAYER OUT, by
            // [`MapKey::of_value_interning`] — which every `Map` builtin goes through.
            // `None` from here means "ask that one", not "no key exists".
            Value::Node(_) => match v.head(kb) {
                ViewHead::Const(Literal::Int(n)) => Some(MapKey::Int(n)),
                ViewHead::Const(Literal::Bool(b)) => Some(MapKey::Bool(b)),
                ViewHead::Const(Literal::String(s)) => Some(MapKey::Str(s)),
                ViewHead::Ref(sym) => Some(MapKey::Ref(sym)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The key `v` addresses, INTERNING a structural occurrence if that is what it
    /// takes — the entry point every `Map` builtin uses.
    ///
    /// WI-20260827-3ZNBC. [`Self::try_from_value`] answers off `&kb` alone and so
    /// cannot key a `Value::Node` that denotes a CONSTRUCTOR APPLICATION: the key for
    /// such a value is the term it denotes, and that term may not be interned yet.
    /// Leaving it refused would have kept exactly the defect this ticket removes —
    /// `Map.put(m, Board(1, 2), v)` succeeding for a board proved by a fact match
    /// (`Value::Term` → `MapKey::Term`) and hard-erroring for the identical board
    /// bound by a rule-body builtin (`Value::Node`), i.e. one program working or not
    /// depending on how its value was carried. `occurrence_to_term` is the same
    /// lowering the resolver and `proof_verify` already use for this carrier.
    ///
    /// THE INTERN IS PAID ONLY WHERE THE ALTERNATIVE WAS AN ERROR: a native, a
    /// `Value::Term`, a literal or a name occurrence all key off `try_from_value`
    /// above without touching the store, so no `Map.get` that worked before now
    /// writes to it. (That is the cost this ticket removed from the relation drain,
    /// and it is not being reintroduced on a path that had one.)
    ///
    /// A VAR-HEADED occurrence is still refused, and must be: an unbound logic
    /// variable denotes nothing to key on, and `Value::Var` is refused above for the
    /// same reason.
    pub fn of_value_interning(kb: &mut KnowledgeBase, v: &Value) -> Option<Self> {
        if let Some(k) = Self::try_from_value(kb, v) {
            return Some(k);
        }
        let Value::Node(occ) = v.carried() else {
            return None;
        };
        if matches!(v.head(kb), ViewHead::Var(_)) {
            return None;
        }
        let occ = std::rc::Rc::clone(occ);
        Some(MapKey::Term(
            crate::kb::node_occurrence::occurrence_to_term(kb, &occ),
        ))
    }

    /// The key back as a `Value` — what `Map.keys` / `Map.entries` hand out.
    ///
    /// A `Ref` key spells itself `Value::SymbolRef`, the carrier-free form, rather
    /// than re-interning a `Term::Ref`: this is a READ, and it must not need
    /// `&mut kb`. The two are indistinguishable to every structural consumer
    /// (`ViewHead::Ref`), and feeding it back to `try_from_value` returns the same
    /// key, so `Map.get(m, k)` for a `k` out of `Map.keys(m)` still hits.
    pub fn to_value(&self) -> Value {
        match self {
            MapKey::Int(n) => Value::Int(*n),
            MapKey::Bool(b) => Value::Bool(*b),
            MapKey::Str(s) => Value::Str(s.clone()),
            MapKey::Ref(s) => Value::SymbolRef(*s),
            MapKey::Term(tid) => Value::term(*tid),
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
            assert_eq!(MapKey::try_from_value(&kb, &v), Some(expected.clone()));
            assert!(expected.to_value().scalar_eq(&v));
        }
    }

    /// WI-1016: the two carriers of ONE reflect `Symbol` address ONE map slot.
    ///
    /// `Value::SymbolRef(s)` (what `Dictionary.impl` / `OpRef.op` mint) and
    /// `Value::Term` wrapping the hash-consed `Term::Ref(s)` (what `lookup_symbol`
    /// / `scope` mint) are the same symbol, so a `put` through one must be found
    /// by a `get` through the other. CONTROL: drop the `Term::Ref` arm of
    /// `try_from_value` and the two keys differ — this fails on the `assert_eq!`.
    #[test]
    fn both_symbol_carriers_key_one_map_slot() {
        let mut kb = KnowledgeBase::new();
        let s = kb.intern("demo.Thing");
        let ref_tid = kb.alloc(Term::Ref(s));

        let via_symbolref = MapKey::try_from_value(&kb, &Value::SymbolRef(s));
        let via_term = MapKey::try_from_value(&kb, &Value::term(ref_tid));
        assert_eq!(via_symbolref, Some(MapKey::Ref(s)));
        assert_eq!(
            via_symbolref, via_term,
            "a symbol keys the same slot whichever carrier it arrived on",
        );

        // And the round-trip out of `keys` addresses that slot again.
        let mut body = MapBody::new();
        body.insert(via_symbolref.clone().unwrap(), Value::Int(1));
        let back = body.keys().next().cloned().expect("one key");
        assert_eq!(
            MapKey::try_from_value(&kb, &back.to_value()),
            via_symbolref,
            "a key read back out of the map re-keys to itself",
        );

        // A term-carried LITERAL keys as that literal, so it addresses the same slot
        // its native twin does (WI-20260827-3ZNBC). This assertion used to read
        // `Some(MapKey::Term(int_tid))` under the sentence "a NON-`Ref` term is
        // untouched — the canon is the symbol spelling only"; that sentence was
        // written when the relation drain reified every column, so no term-carried
        // literal could reach a map key. A column keeps its own carrier now, and the
        // split it described was `Map.get(m, 3)` answering `none()` for an entry
        // `Map.put` had stored under the same 3.
        let int_tid = kb.alloc(Term::Const(crate::kb::term::Literal::Int(3)));
        assert_eq!(
            MapKey::try_from_value(&kb, &Value::term(int_tid)),
            Some(MapKey::Int(3)),
        );
        assert_eq!(
            MapKey::try_from_value(&kb, &Value::term(int_tid)),
            MapKey::try_from_value(&kb, &Value::Int(3)),
            "a literal keys the same slot whichever carrier it arrived on",
        );
    }

    /// WI-1023 — the THIRD spelling of one name keys with the other two.
    ///
    /// `resolve_qualified_name_term` mints `Fn{c,[],[]}` through `terms.alloc`,
    /// deliberately bypassing the WI-511 canon that would rewrite it to `Ref(c)`.
    /// It denotes the same constructor, and `functor_view_head` says so
    /// (`ViewHead::Ref(c)`), so keying it as `Term(tid)` put one name in two slots.
    ///
    /// CONTROL, MEASURED by restoring `match kb.get_term(*tid) { Term::Ref(s) =>
    /// … }`: `via_nullary_fn` comes back `Some(MapKey::Term(fn_tid))`, the
    /// `assert_eq!` against `Ref(c)` fails, and the `MapBody` read below answers
    /// `None` where the `put` stored under the canonical spelling.
    ///
    /// `Term::Ident` is the arm that must NOT move, and it is asserted here rather
    /// than argued: widening it would MERGE two distinct terms and let one `put`
    /// overwrite the other's entry.
    #[test]
    fn a_non_canonicalized_nullary_constructor_keys_as_its_name() {
        let mut kb = KnowledgeBase::new();
        let c = kb.intern("demo.Color.red");
        kb.mark_constructor_symbol(c);

        // The three spellings: the canonical `Ref`, the value carrier, and the
        // nullary `Fn` `resolve_qualified_name_term` mints.
        let ref_tid = kb.alloc(Term::Ref(c));
        let fn_tid = kb.resolve_qualified_name_term("demo.Color.red");
        assert_ne!(
            ref_tid, fn_tid,
            "premise: the mint really does bypass the canon"
        );

        let via_ref = MapKey::try_from_value(&kb, &Value::term(ref_tid));
        let via_symbolref = MapKey::try_from_value(&kb, &Value::SymbolRef(c));
        let via_nullary_fn = MapKey::try_from_value(&kb, &Value::term(fn_tid));
        assert_eq!(via_ref, Some(MapKey::Ref(c)));
        assert_eq!(via_symbolref, via_ref);
        assert_eq!(
            via_nullary_fn, via_ref,
            "a nullary constructor names its symbol however it is spelled",
        );

        // One slot, reachable through the third spelling.
        let mut body = MapBody::new();
        body.insert(via_ref.clone().unwrap(), Value::Int(4));
        assert_eq!(
            body.get(&via_nullary_fn.unwrap()).and_then(|v| match v {
                Value::Int(n) => Some(*n),
                _ => None,
            }),
            Some(4),
        );

        // `Ident(c)` is a DIFFERENT term and stays a different key — the merge the
        // by-spelling match was protecting against is still protected.
        let ident_tid = kb.alloc(Term::Ident(c));
        assert_eq!(
            MapKey::try_from_value(&kb, &Value::term(ident_tid)),
            Some(MapKey::Term(ident_tid)),
            "an unresolved identifier is not the resolved name",
        );

        // AND THE GATE: for a NON-constructor the two spellings are not one name.
        // `functor_view_head` rewrites a nullary `Fn` only for a registered
        // constructor, because for a sort `Ref(s)` vs `Fn{s}` IS WI-391's
        // wildcard-vs-concrete type distinction. Asserted so the widening's
        // boundary is driven rather than assumed — this is the case that would
        // silently merge if the `is_constructor_symbol` gate were dropped.
        let sort = kb.intern("demo.Color");
        assert!(
            !kb.is_constructor_symbol(sort),
            "premise: a sort is not a constructor"
        );
        let sort_fn = kb.resolve_qualified_name_term("demo.Color");
        let sort_ref = kb.alloc(Term::Ref(sort));
        assert_eq!(
            MapKey::try_from_value(&kb, &Value::term(sort_fn)),
            Some(MapKey::Term(sort_fn)),
        );
        assert_ne!(
            MapKey::try_from_value(&kb, &Value::term(sort_fn)),
            MapKey::try_from_value(&kb, &Value::term(sort_ref)),
            "a sort's nullary application and its bare Ref are not one name",
        );

        // A `Term::Const` key is read off the term (no `head`, so no payload clone)
        // and must key identically to what the view would have said — which since
        // WI-20260827-3ZNBC is the LITERAL, not the `TermId`, so it meets its native
        // twin in one slot.
        let str_tid = kb.alloc(Term::Const(crate::kb::term::Literal::String("s".into())));
        assert_eq!(
            MapKey::try_from_value(&kb, &Value::term(str_tid)),
            Some(MapKey::Str("s".into())),
        );
        assert_eq!(
            MapKey::try_from_value(&kb, &Value::term(str_tid)),
            MapKey::try_from_value(&kb, &Value::Str("s".into())),
            "a string keys one slot on either carrier",
        );
    }
}
