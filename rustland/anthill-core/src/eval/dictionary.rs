//! The requirement dictionary — ONE representation, an ordinary value.
//!
//! `docs/design/requirement-channel.md` §9: a dictionary is **immutable**,
//! **acyclic** and — after the typing pass — **ground**, so an
//! `(impl symbol, ordered children)` tree is a first-order value and nothing
//! more. It therefore rides the carrier every other first-order value rides,
//! `Value::Entity { functor: Dictionary, pos: subs, named: [(impl, SymbolRef)] }`
//! — exactly the shape WI-1019's `TermView` announces and WI-1040's σ producer
//! (`dictionary_value_of_tree`, kb/typing.rs) already builds.
//!
//! WI-1045 retired the `RequirementArena` this module replaces. What the arena
//! bought was deallocation; what it cost was a **second identity** —
//! `(arena, raw)`, so two scratch interpreters gave one dictionary two
//! identities and every comparison had to be routed through the view or it
//! silently answered wrong — plus a **conversion at every crossing**. Both are
//! gone: σ, [`crate::eval::frame::Frame::requirements`],
//! `Closure::requirements` and the reflect `Dictionary` face now name the same
//! value, and the SLD→eval crossing converts nothing.
//!
//! # Why a wrapper at all
//!
//! [`Dictionary`] is a **proof, not a representation**: it holds the very
//! `Value` and [`Dictionary::as_value`] hands it straight back — there is no
//! second layout to keep in step, and `into_value`/`from_value` are a wrap and
//! an unwrap, never a rebuild. It exists so the three reads the channel makes at
//! ~30 sites — [`Dictionary::impl_sort`], [`Dictionary::arity`],
//! [`Dictionary::sub`] — are **total**, with the one shape check paid at the
//! boundary where a `Value` of unknown provenance arrives
//! ([`Dictionary::from_value`], which validates the WHOLE tree). That is the
//! repo's make-illegal-states-unrepresentable rule applied to a carrier that,
//! by §9, must not be a variant of its own.
//!
//! # Storage is a separate decision, and this does not make it
//!
//! "One representation" is shape and identity — one functor, one key set, one
//! comparison — not which store holds it. Nothing here is interned: a
//! conditional provision composes over type arguments, so the distinct-dictionary
//! family follows the carried types that actually occur (no static bound), while
//! interned terms live for the KB's lifetime. See CLAUDE.md's Representation
//! note — matching and indexing key on structural `DiscrimKey`s, never on
//! `TermId` identity, so a non-interned carrier indexes identically.

use std::rc::Rc;

use crate::intern::Symbol;
use crate::kb::KnowledgeBase;

use super::value::Value;

/// A requirement dictionary: `Dictionary(sub₀ … subₙ₋₁, impl: S)`.
///
/// The wrapped `Value` is always a `Value::Entity` whose functor is the
/// `anthill.realization.runtime.Dictionary` sort symbol, whose positional
/// children are themselves dictionaries, and whose one named child is
/// `impl → Value::SymbolRef(S)`. Every constructor here establishes that, so
/// the accessors below are total.
#[derive(Clone, Debug)]
pub struct Dictionary(Value);

impl Dictionary {
    /// Build `Dictionary(subs…, impl: impl_sort)`.
    ///
    /// `None` in a KB that never loaded `anthill.realization.runtime` — the
    /// producer then reports that it cannot build one, which is the same answer
    /// [`crate::kb::term_view::dictionary_view_syms`] gives for the same reason.
    pub fn build(
        kb: &KnowledgeBase,
        impl_sort: Symbol,
        subs: impl IntoIterator<Item = Dictionary>,
    ) -> Option<Dictionary> {
        let (ctor, impl_key) = crate::kb::term_view::dictionary_view_syms(kb)?;
        let pos: Vec<Value> = subs.into_iter().map(|d| d.0).collect();
        Some(Dictionary(Value::Entity {
            functor: ctor,
            pos: pos.into(),
            named: vec![(impl_key, Value::SymbolRef(impl_sort))].into(),
        }))
    }

    /// Recognize a dictionary in a `Value` of unknown provenance — the ONE
    /// boundary check, and the only place the shape is tested.
    ///
    /// Validates the WHOLE tree (functor, the single `impl` named child, and
    /// every positional child recursively), which is what makes [`Self::sub`]
    /// total rather than fallible-per-read. A dictionary is tiny — arity 0–2,
    /// depth 1–3 — so the walk costs less than threading an `Option` through
    /// every projection would.
    ///
    /// `None` for anything else, INCLUDING a `Dictionary`-functored entity whose
    /// children are not dictionaries: half a dictionary is not one, and
    /// admitting it would move the failure to a read that has no way to report.
    pub fn from_value(kb: &KnowledgeBase, v: &Value) -> Option<Dictionary> {
        let (ctor, impl_key) = crate::kb::term_view::dictionary_view_syms(kb)?;
        Self::from_value_with(ctor, impl_key, v)
    }

    fn from_value_with(ctor: Symbol, impl_key: Symbol, v: &Value) -> Option<Dictionary> {
        let Value::Entity {
            functor,
            pos,
            named,
        } = v
        else {
            return None;
        };
        if *functor != ctor {
            return None;
        }
        match named.as_ref() {
            [(k, Value::SymbolRef(_))] if *k == impl_key => {}
            _ => return None,
        }
        for sub in pos.iter() {
            Self::from_value_with(ctor, impl_key, sub)?;
        }
        Some(Dictionary(v.clone()))
    }

    /// The impl this dictionary pins — the `impl` named child.
    ///
    /// Total: every constructor above established the single `impl →
    /// SymbolRef` named child. This is what `RequirementHandle::functor` was.
    pub fn impl_sort(&self) -> Symbol {
        match &self.0 {
            Value::Entity { named, .. } => match named.as_ref() {
                [(_, Value::SymbolRef(s))] => *s,
                other => unreachable!(
                    "a Dictionary's named children are exactly `impl -> SymbolRef`, got {other:?}"
                ),
            },
            other => unreachable!("a Dictionary wraps a Value::Entity, got {other:?}"),
        }
    }

    /// How many sub-dictionaries this one bundles — its POSITIONAL arity.
    ///
    /// Positional, not named, because the sub-dictionaries are an ORDERED
    /// bundle: slot `k` is the k-th entry of the WI-857 dictionary layout, so
    /// the order is the identity.
    pub fn arity(&self) -> usize {
        match &self.0 {
            Value::Entity { pos, .. } => pos.len(),
            other => unreachable!("a Dictionary wraps a Value::Entity, got {other:?}"),
        }
    }

    /// Sub-dictionary `k` — reading positional child `k`. `None` past the end.
    ///
    /// This is what `RequirementHandle::project` was, minus the refcount: the
    /// child `Value` is `Rc`-backed, so the clone is a refcount bump either way.
    pub fn sub(&self, k: usize) -> Option<Dictionary> {
        match &self.0 {
            Value::Entity { pos, .. } => pos.get(k).cloned().map(Dictionary),
            other => unreachable!("a Dictionary wraps a Value::Entity, got {other:?}"),
        }
    }

    /// The dictionary AS the value it is. Not a conversion — the same `Value`.
    pub fn as_value(&self) -> &Value {
        &self.0
    }

    /// The dictionary AS the value it is, by move.
    pub fn into_value(self) -> Value {
        self.0
    }
}

/// Structural equality — the `(impl, ordered subs)` tree, which is all a
/// dictionary is. No arena half to drop (the mistake WI-1019 recorded at
/// [`Value::opaque_carrier_eq`]) because there is no arena.
impl PartialEq for Dictionary {
    fn eq(&self, other: &Self) -> bool {
        self.impl_sort() == other.impl_sort()
            && self.arity() == other.arity()
            && (0..self.arity()).all(|k| self.sub(k) == other.sub(k))
    }
}
impl Eq for Dictionary {}

/// A dictionary held inside a `Value` — the `Value::OpRef` `dict` slot.
///
/// `Value` cannot contain a `Dictionary` inline (a `Dictionary` contains a
/// `Value`, so the layout would be infinite); the `Rc` is that indirection and
/// nothing else. Minted at an eta site and by `Dictionary.resolveOp`, both rare,
/// so the one allocation buys the same proof the unboxed form carries.
pub type BoxedDictionary = Rc<Dictionary>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::KnowledgeBase;

    /// A KB that DECLARES the two names a dictionary is spelled with, without
    /// loading the stdlib — enough for [`Dictionary::build`] to answer.
    ///
    /// `define_qualified_only`, not `intern`: `dictionary_view_syms` resolves by
    /// QUALIFIED NAME, and `intern` does not register one — MEASURED, an interned
    /// spelling left `build` answering `None`. That is the same reason the eval
    /// producer must be able to fail loudly rather than assume the sort is there.
    fn kb_with_dictionary_sort() -> KnowledgeBase {
        use crate::intern::SymbolKind;
        let mut kb = KnowledgeBase::new();
        let global = kb.global_scope();
        kb.symbols.define_qualified_only(
            "Dictionary",
            "anthill.realization.runtime.Dictionary",
            SymbolKind::Sort,
            global,
        );
        kb.symbols.define_qualified_only(
            "impl",
            "anthill.realization.runtime.Dictionary.impl",
            SymbolKind::Operation,
            global,
        );
        kb
    }

    /// WI-1045 — [`runtime_carrier_sort`]'s `Dictionary` row survived the carrier
    /// change, and this is the test that says the RELOCATION is load-bearing.
    ///
    /// The row used to be a fixed `Value::Requirement(_) => Dictionary` entry. With
    /// a dictionary carried as a `Value::Entity`, the entity path asks
    /// `sort_of_constructor`, which is the belongs-to INDEX — and a constructor-less
    /// sort is deliberately absent from it (`register_self_sort` runs per entity, and
    /// `Dictionary` declares none). So the row had to be restated as a fallback.
    ///
    /// The first assertion is the PREMISE: if `sort_of_constructor` ever answered for
    /// `Dictionary`, the fallback would be unreachable and this test would be
    /// measuring nothing. CONTROL: delete the `.or_else(dictionary_carrier)` in
    /// `runtime_carrier_sort` and the second assertion reports `None`.
    #[test]
    fn a_dictionary_still_names_its_carrier_sort() {
        let kb = kb_with_dictionary_sort();
        let (ctor, _) =
            crate::kb::term_view::dictionary_view_syms(&kb).expect("both names are interned above");
        let impl_sym = ctor;
        assert_eq!(
            kb.sort_of_constructor(ctor),
            None,
            "PREMISE: `Dictionary` is constructor-less, so the belongs-to index has \
             no entry for it — which is why the carrier row needs a fallback at all",
        );
        let dict = Dictionary::build(&kb, impl_sym, []).expect("both names resolve");
        assert_eq!(
            crate::eval::eval::runtime_carrier_sort(&kb, dict.as_value()),
            Some(ctor),
            "a dictionary value names the `Dictionary` sort as its carrier — the \
             WI-577 row, relocated rather than dropped",
        );
    }

    /// The boundary check is a CHECK, not a coercion: half a dictionary is not one.
    ///
    /// A `Dictionary`-functored entity whose positional child is NOT a dictionary
    /// must be refused here, where the caller can report it, rather than at a
    /// [`Dictionary::sub`] read that has no way to.
    #[test]
    fn a_dictionary_functored_entity_with_a_foreign_child_is_not_a_dictionary() {
        let kb = kb_with_dictionary_sort();
        let (ctor, impl_key) = crate::kb::term_view::dictionary_view_syms(&kb).unwrap();
        let good = Dictionary::build(&kb, ctor, []).unwrap();
        assert!(
            Dictionary::from_value(&kb, good.as_value()).is_some(),
            "PREMISE: a well-formed one IS recognized, so the refusals below are not \
             a function that refuses everything",
        );

        let foreign_child = Value::Entity {
            functor: ctor,
            pos: vec![Value::Int(1)].into(),
            named: vec![(impl_key, Value::SymbolRef(ctor))].into(),
        };
        assert!(
            Dictionary::from_value(&kb, &foreign_child).is_none(),
            "a positional child that is not a dictionary makes the whole thing not one",
        );

        let bad_impl = Value::Entity {
            functor: ctor,
            pos: vec![].into(),
            named: vec![(impl_key, Value::Int(1))].into(),
        };
        assert!(
            Dictionary::from_value(&kb, &bad_impl).is_none(),
            "`impl` must name a symbol — otherwise `impl_sort` would have to panic",
        );
    }
}
