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
//! ([`Dictionary::from_value`], which validates the WHOLE tree, and its
//! carrier-neutral twin [`Dictionary::from_view`] for a dictionary on another
//! carrier — the reflect face's `expect_dictionary` tries both). That is the
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
use crate::kb::term::TermId;

use super::value::Value;

/// A requirement dictionary: `Dictionary(sub₀ … subₙ₋₁, impl: S)`.
///
/// The wrapped `Value` is always a `Value::Entity` whose functor is the
/// `anthill.realization.runtime.Dictionary` sort symbol, whose positional
/// children are themselves dictionaries, and whose named children are
/// `impl → Value::SymbolRef(S)` and, for a tuple's `TypeValue` instance only, `labels`, one
/// label per positional child ([`Dictionary::build_labelled`]), and, where its provider
/// provides the spec at more than one application, `at → Value::Term(SortView(Spec, …))`, the
/// application it is for ([`Dictionary::build_at`]). The three are told apart by their
/// carriers — a symbol, a tuple of symbols, a term — as the accessors below read them. Every
/// constructor here establishes that, so the accessors below are total.
#[derive(Clone, Debug)]
pub struct Dictionary(Value);

impl Dictionary {
    /// WI-20261009-D0SD4 — this dictionary with every `Rc` in it made anew; see
    /// [`crate::kb::deep_clone`].
    pub(crate) fn deep_clone_with(&self, copier: &mut crate::kb::deep_clone::Copier) -> Dictionary {
        let Dictionary(value) = self;
        Dictionary(copier.value(value))
    }
}

#[cfg(test)]
impl Dictionary {
    /// A dictionary over ANY value, for a test of code that only CARRIES one (the deep
    /// copy's rows). Not a dictionary anything could dispatch through.
    pub(crate) fn wrapping_for_test(value: Value) -> Dictionary {
        Dictionary(value)
    }
}

impl Dictionary {
    /// Build `Dictionary(subs…, impl: impl_sort)`.
    ///
    /// `None` in a KB that never loaded `anthill.realization.runtime` — the
    /// producer then reports that it cannot build one, which is the same answer
    /// [`crate::kb::term_view::dictionary_view_syms`] gives for the same reason.
    ///
    /// WI-867 — `pub(crate)`, NOT `pub`: it knows a provider and no spec, so it cannot
    /// tell a dictionary that carries evidence from one that is short of it, and while
    /// it was reachable from outside it was a third host path past the layout with no
    /// name saying so. A host builds none: its call is typed and the typer builds the
    /// call's dictionaries ([`crate::eval::Interpreter::call`]). A caller that builds the
    /// value alone names the blindness with
    /// [`crate::eval::Interpreter::alloc_dictionary_unchecked`].
    pub(crate) fn build(
        kb: &KnowledgeBase,
        impl_sort: Symbol,
        subs: impl IntoIterator<Item = Dictionary>,
    ) -> Option<Dictionary> {
        Self::build_labelled(kb, impl_sort, subs, None)
    }

    /// [`Self::build`], with the labels of a tuple's components where the dictionary is a
    /// tuple's `TypeValue`, `Fillable` or `PartialEq` instance (proposal 004's extension):
    /// `Dictionary(‹Int64's›, ‹String's›, impl: NamedTuple, labels: (a, b))`, one label per
    /// sub-dictionary, in the order the subs are listed. `labels` is `None` for every other
    /// dictionary.
    pub(crate) fn build_labelled(
        kb: &KnowledgeBase,
        impl_sort: Symbol,
        subs: impl IntoIterator<Item = Dictionary>,
        labels: Option<&[Symbol]>,
    ) -> Option<Dictionary> {
        Self::build_at(kb, impl_sort, subs, labels, None)
    }

    /// [`Self::build_labelled`], with the application the dictionary is for, `at`, the spec
    /// view `SortView(Spec, K = V, …)`, where its provider provides the spec at more than one
    /// (WI-20261122-CXR5B; [`crate::kb::typing::dictionary_application_view`] decides it): a
    /// dispatch through the dictionary reads the operation off the provision at that
    /// application ([`Self::application_for`]). `None` for every other dictionary.
    pub(crate) fn build_at(
        kb: &KnowledgeBase,
        impl_sort: Symbol,
        subs: impl IntoIterator<Item = Dictionary>,
        labels: Option<&[Symbol]>,
        at: Option<TermId>,
    ) -> Option<Dictionary> {
        let (ctor, impl_key) = crate::kb::term_view::dictionary_view_syms(kb)?;
        let pos: Vec<Value> = subs.into_iter().map(|d| d.0).collect();
        let mut named = vec![(impl_key, Value::SymbolRef(impl_sort))];
        if let Some(labels) = labels {
            assert_eq!(
                labels.len(),
                pos.len(),
                "a tuple's dictionary holds one label per sub-dictionary"
            );
            let labels_key = crate::kb::term_view::dictionary_labels_key(kb)?;
            named.push((labels_key, labels_value(labels)));
        }
        if let Some(at) = at {
            let at_key = crate::kb::term_view::dictionary_at_key(kb)?;
            named.push((at_key, Value::term(at)));
        }
        if named.len() > 1 {
            kb.canonicalize_record_named_args(ctor, &mut named);
        }
        Some(Dictionary(Value::Entity {
            functor: ctor,
            pos: pos.into(),
            named: named.into(),
        }))
    }

    /// Recognize a dictionary in a `Value` of unknown provenance — the ONE
    /// boundary check, and the only place the shape is tested.
    ///
    /// Validates the WHOLE tree (functor, the `impl` named child, a tuple's `labels` and an
    /// application's `at`, and every positional child recursively), which is what makes [`Self::sub`]
    /// total rather than fallible-per-read. A dictionary is tiny — arity 0–2,
    /// depth 1–3 — so the walk costs less than threading an `Option` through
    /// every projection would.
    ///
    /// `None` for anything else, INCLUDING a `Dictionary`-functored entity whose
    /// children are not dictionaries: half a dictionary is not one, and
    /// admitting it would move the failure to a read that has no way to report.
    pub fn from_value(kb: &KnowledgeBase, v: &Value) -> Option<Dictionary> {
        let (ctor, impl_key) = crate::kb::term_view::dictionary_view_syms(kb)?;
        Self::from_value_with(kb, ctor, impl_key, v)
    }

    fn from_value_with(kb: &KnowledgeBase, ctor: Symbol, impl_key: Symbol, v: &Value) -> Option<Dictionary> {
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
        // One `impl` naming a symbol, and beside it a tuple's `labels`, one symbol per sub, and
        // an application's `at`, a term — each at most once. The two optional keys are looked
        // up only where a dictionary holds more than `impl`, which almost none does.
        let impl_ok = |(k, v): &(Symbol, Value)| *k == impl_key && matches!(v, Value::SymbolRef(_));
        match named.as_ref() {
            [i] if impl_ok(i) => {}
            [_] => return None,
            more => {
                let labels_key = crate::kb::term_view::dictionary_labels_key(kb);
                let at_key = crate::kb::term_view::dictionary_at_key(kb);
                let (mut impls, mut labels, mut ats) = (0, 0, 0);
                for child @ (k, v) in more {
                    if impl_ok(child) {
                        impls += 1;
                    } else if Some(*k) == labels_key
                        && labels_of_value(v).is_some_and(|l| l.len() == pos.len())
                    {
                        labels += 1;
                    } else if Some(*k) == at_key && matches!(v, Value::Term { .. }) {
                        ats += 1;
                    } else {
                        return None;
                    }
                }
                if impls != 1 || labels > 1 || ats > 1 {
                    return None;
                }
            }
        }
        for sub in pos.iter() {
            Self::from_value_with(kb, ctor, impl_key, sub)?;
        }
        Some(Dictionary(v.clone()))
    }

    /// WI-20260909-NAR1X — the CARRIER-NEUTRAL twin of [`Self::from_value`]: recognize
    /// a dictionary through [`TermView`], whatever carrier it rides, and REBUILD it as
    /// the `Value::Entity` every accessor above reads.
    ///
    /// **WHY A SECOND READER RATHER THAN A SECOND ARM IN `from_value`.** One dictionary
    /// has THREE carriers by design — a `TermId`, a `Value::Entity`, and a
    /// `NodeOccurrence` (`Expr::Dictionary`) — and WI-1045's rule is that all three
    /// present ONE head, ONE key set and ONE child list through `TermView`
    /// (`requirement-channel.md` §9). `from_value` matches the `Value::Entity` carrier
    /// STRUCTURALLY, so it is blind to the other two; that is right for its callers,
    /// which hold a value eval itself built, and wrong for a resolver clause variable,
    /// whose σ binding is materialized into an `Expr::Dictionary` occurrence by the goal
    /// walk. MEASURED: `?d` supplied through a rule head reaches
    /// `dictionary_dispatch_target` as `Value::Node(Expr::Dictionary { .. })`, and
    /// `from_value` answers `None` for it.
    ///
    /// **NOT MERGED INTO `from_value`, because the fast path is the difference.**
    /// `from_value` wraps the value it was handed and allocates nothing; this rebuilds.
    /// Its one production caller, the reflect face's `expect_dictionary`
    /// (`eval/builtins.rs`), tries it FIRST and falls back here — WI-20260911-5G28A
    /// measured a head-passed dictionary reaching `Dictionary.sub` on the occurrence
    /// carrier and being refused before it did. A new reader of a dictionary of unknown
    /// provenance goes through that function, not `from_value` alone. So the two are
    /// kept apart, and what stops them drifting is
    /// that they answer the same question about the same three carriers: any change to
    /// the SHAPE — the functor, the `impl` child, a tuple's `labels` and an application's
    /// `at`, sub-dictionaries positional —
    /// must land in both, and each names the other.
    ///
    /// `None` for anything that is not a whole dictionary, on the same rule
    /// `from_value` states: half a dictionary is not one.
    pub(crate) fn from_view<V: crate::kb::term_view::TermView + ?Sized>(
        kb: &KnowledgeBase,
        v: &V,
    ) -> Option<Dictionary> {
        use crate::kb::term_view::{TermView, ViewHead};
        let (ctor, impl_key) = crate::kb::term_view::dictionary_view_syms(kb)?;
        let ViewHead::Functor {
            functor: f,
            pos_arity,
            named_arity: named_arity @ (1..=3),
        } = v.head(kb)
        else {
            return None;
        };
        if f != ctor {
            return None;
        }
        // A tuple's `labels` (see [`Self::build_labelled`]) and an application's `at` ([`Self::
        // build_at`]), the two other keys there are; every key beside `impl` is one of them.
        let (labels, at) = match named_arity {
            1 => (None, None),
            _ => {
                let labels = match crate::kb::term_view::dictionary_labels_key(kb)
                    .and_then(|key| v.named_arg(kb, key))
                {
                    None => None,
                    Some(child) => {
                        let labels = crate::kb::term_view::labels_of_view(kb, &child)?;
                        Some((labels.len() == pos_arity).then_some(labels)?)
                    }
                };
                let at = match crate::kb::term_view::dictionary_at_key(kb).and_then(|key| v.named_arg(kb, key)) {
                    None => None,
                    Some(child) => Some(child.as_term_id()?),
                };
                if 1 + usize::from(labels.is_some()) + usize::from(at.is_some()) != named_arity {
                    return None;
                }
                (labels, at)
            }
        };
        // The `impl` child is a SYMBOL on every carrier — `Value::SymbolRef` on the
        // value one, `Term::Ref` on the term one, an owned `SymbolRef` synthesized by
        // `occ_view_named` on the occurrence one — so it is read as a nullary head
        // rather than by variant, which is what makes this carrier-neutral.
        let impl_sort = match v.named_arg(kb, impl_key)?.head(kb) {
            ViewHead::Ident(s) => s,
            ViewHead::Functor {
                functor: s,
                pos_arity: 0,
                ..
            } => s,
            _ => return None,
        };
        let mut subs: Vec<Dictionary> = Vec::with_capacity(pos_arity);
        for i in 0..pos_arity {
            subs.push(Self::from_view(kb, &v.pos_arg(kb, i)?)?);
        }
        Self::build_at(kb, impl_sort, subs, labels.as_deref(), at)
    }

    /// The impl this dictionary pins — the `impl` named child.
    ///
    /// Total: every constructor above established the `impl → SymbolRef` named child. This is what `RequirementHandle::functor` was.
    pub fn impl_sort(&self) -> Symbol {
        match &self.0 {
            // The one child naming a symbol: a tuple's `labels` is a tuple of them, and an
            // application's `at` a term.
            Value::Entity { named, .. } => named
                .iter()
                .find_map(|(_, v)| match v {
                    Value::SymbolRef(s) => Some(*s),
                    _ => None,
                })
                .unwrap_or_else(|| {
                    unreachable!("a Dictionary's named children hold `impl -> SymbolRef`, got {named:?}")
                }),
            other => unreachable!("a Dictionary wraps a Value::Entity, got {other:?}"),
        }
    }

    /// The labels of a tuple's components, where this is a tuple's `TypeValue`, `Fillable` or `PartialEq` instance
    /// ([`Self::build_labelled`]), one per sub-dictionary; `None` for every other dictionary.
    pub fn labels(&self) -> Option<Vec<Symbol>> {
        labels_of_value(self.labels_child()?)
    }

    /// The `labels` child, the one named child that is a tuple ([`Self::build_labelled`]):
    /// `impl` is a symbol and `at` a term.
    fn labels_child(&self) -> Option<&Value> {
        match &self.0 {
            Value::Entity { named, .. } => named
                .iter()
                .map(|(_, v)| v)
                .find(|v| matches!(v, Value::Tuple { .. } | Value::Unit)),
            other => unreachable!("a Dictionary wraps a Value::Entity, got {other:?}"),
        }
    }

    /// The application this dictionary is for, the spec view under its `at` key ([`Self::
    /// build_at`]), the one named child that is a term; `None` for a dictionary whose provider
    /// provides its spec at one application.
    pub fn at(&self) -> Option<TermId> {
        match &self.0 {
            Value::Entity { named, .. } => named.iter().find_map(|(_, v)| match v {
                Value::Term { id, .. } => Some(*id),
                _ => None,
            }),
            other => unreachable!("a Dictionary wraps a Value::Entity, got {other:?}"),
        }
    }

    /// The application of `spec_op`'s spec this dictionary is for, as the resolution of the
    /// operation reads one ([`crate::kb::typing::resolve_op_target_at`]): its `at`, read at the
    /// spec the view names, where that spec is the operation's own. `None` where it holds none,
    /// or one of another spec — whose type-vars are not the operation's spec's, so it says
    /// nothing about which of that spec's applications the provider is asked at.
    pub(crate) fn application_for(
        &self,
        kb: &KnowledgeBase,
        spec_op: Symbol,
    ) -> Option<crate::kb::typing::SpecApplication> {
        crate::kb::typing::application_of_view_for_op(kb, self.at()?, spec_op)
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

/// Structural equality — the `(impl, labels, at, ordered subs)` tree, which is all a
/// dictionary is. No arena half to drop (the mistake WI-1019 recorded at
/// [`Value::opaque_carrier_eq`]) because there is no arena.
impl PartialEq for Dictionary {
    fn eq(&self, other: &Self) -> bool {
        self.impl_sort() == other.impl_sort()
            && same_labels(self.labels_child(), other.labels_child())
            && self.at() == other.at()
            && self.arity() == other.arity()
            && (0..self.arity()).all(|k| self.sub(k) == other.sub(k))
    }
}
impl Eq for Dictionary {}

/// A tuple's labels as a dictionary holds them: a positional tuple of symbols, as an `OpRef`
/// holds its spread labels (`term_view`'s `"spread"` arm), so their order is their identity.
pub(crate) fn labels_value(labels: &[Symbol]) -> Value {
    if labels.is_empty() {
        // `()`'s labels: the tuple of no components is `Unit`.
        return Value::Unit;
    }
    Value::Tuple {
        pos: labels.iter().copied().map(Value::SymbolRef).collect(),
        named: Vec::new().into(),
    }
}

/// Do two `labels` children ([`Dictionary::labels_child`]) hold the same labels, in order? Read
/// in place: dictionaries are compared where frames and stamps are.
fn same_labels(a: Option<&Value>, b: Option<&Value>) -> bool {
    let items = |v: &Value| match v {
        Value::Tuple { pos, .. } => pos
            .iter()
            .map(|l| match l {
                Value::SymbolRef(s) => Some(*s),
                _ => None,
            })
            .collect::<smallvec::SmallVec<[Option<Symbol>; 4]>>(),
        _ => smallvec::SmallVec::new(),
    };
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => items(a) == items(b),
        _ => false,
    }
}

/// The labels [`labels_value`] holds; `None` for any other value.
fn labels_of_value(v: &Value) -> Option<Vec<Symbol>> {
    match v {
        Value::Tuple { pos, named } if named.is_empty() => pos
            .iter()
            .map(|l| match l {
                Value::SymbolRef(s) => Some(*s),
                _ => None,
            })
            .collect(),
        // The tuple of no components.
        Value::Unit => Some(Vec::new()),
        _ => None,
    }
}

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
