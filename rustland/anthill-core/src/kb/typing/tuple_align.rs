/// WI-799: how many of `a`'s components `b` must account for — one of the two
/// axes of [`TupleAlign`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum TupleWidth {
    /// WIDTH SUBTYPING. `b`'s components need only be a name-keyed SUBSET of
    /// `a`'s, dropped from ANYWHERE (WI-804) — a consumer of a `(a, c)`-typed
    /// value asks for `.a` and `.c`, and an `(a, b, c)` value answers both
    /// wherever they sit. Correct for a `<:` between DATA tuples, and for nothing
    /// else here: it is a SUBTYPING allowance, so a relation that means EQUALITY
    /// must not take it (that was the [`TupleAlign::EQUALITY`] defect).
    Subset,
    /// EQUAL ARITY. Forced for a parameter list — eval passes exactly as many
    /// arguments as the call site's type says, so a narrower list is not a
    /// supertype (WI-782) — and correct for an equality relation, where admitting
    /// a subset in one argument position makes the relation ASYMMETRIC.
    Exact,
}

/// WI-803: may the correspondence REORDER, or must each match come after the
/// previous one — the third axis of [`TupleAlign`].
///
/// This axis did not exist until WI-803 because it had exactly one live value:
/// every discipline preserved order, so naming it would have bought surface area
/// and no type-safety. WI-804 wrote the DATA arm's order requirement down as an
/// explicit INTERIM for precisely this moment.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum TupleOrder {
    /// POSITION IS LOAD-BEARING: each `b` name must occur in `a` AFTER the
    /// previous one. A component may be dropped from anywhere (that preserves the
    /// order of those that remain), but a PERMUTATION is refused. Forced for a
    /// parameter list, which is applied positionally, and for an equality, whose
    /// operands are two tuple IDENTITIES and where order is part of identity.
    Preserved,
    /// NAME-KEYED, order immaterial: each `b` name is looked up in `a` from the
    /// start. Correct for a data tuple under `<:` — the consumer of an
    /// `(a: TA, c: TC)`-typed value asks for `.a` and `.c`, and the value answers
    /// both wherever the components sit. Order belongs to a tuple's IDENTITY;
    /// `<:` is a different relation and carrying the rule across is the mistake
    /// WI-788 made and WI-804 named.
    ///
    /// FIRST match, not any match: that is what makes this walk agree with the
    /// READER it licenses. `TupleComponents::by_label` (eval/value.rs) scans a
    /// value's components and returns the FIRST with the wanted name, so under a
    /// resume-after-previous scan the two picked DIFFERENT components on a
    /// duplicate label — the tuple conformed on the second `a` while `t.a` read
    /// the first (WI-805). Looking up from the start is the reader's own rule.
    ///
    /// WI-805 has since refused a duplicate label at every producer that keys a tuple
    /// on labels the author WROTE — the literal and the tuple type at parse
    /// (`check_label_unique`), and a `...rest: R` capture's leftover named
    /// arguments in `normalize_variadic_capture` — so no such tuple can put the two
    /// walks in that position again. The discipline is still load-bearing, not
    /// vestigial: labels reaching here may be DERIVED rather than written (a `Concat`
    /// / `Project` schema), and the reader compares SHORT names, so two distinct
    /// qualified symbols sharing a last segment collide for it whether or not they
    /// collide here.
    ///
    /// A variadic capture is NOT one of the derived cases, and an earlier draft of
    /// this comment listing it as one is what let that producer ship unguarded: its
    /// labels are written in source, as a call's named arguments, and only become a
    /// tuple in the typer.
    ///
    /// What is shared is the FIRST-MATCH discipline, not the whole rule: this walk
    /// compares names by `Symbol` IDENTITY while the reader compares SHORT names
    /// (a value's component symbol may carry a qualified path). That difference
    /// predates WI-803 and is not introduced here, but it does bound the claim —
    /// the two agree on WHICH occurrence of a repeated name to take, not
    /// necessarily on whether two spellings name the same component.
    Free,
}

/// WI-799: what the two lists' NAMES must satisfy for the alignment to be
/// admissible at all — the second axis of [`TupleAlign`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum TupleNames {
    /// The names must agree at each slot they are aligned at. This is what keeps
    /// `(a: Int64)` and `(_1: Int64)` apart: a component's name IS its access path
    /// — `t.x` reads `Value::Tuple.named`, `t._N` reads `.pos`, and a tuple has
    /// exactly one of those populated — so relating them would license a read with
    /// no value behind it (WI-775), and proposal 004 rule 4 makes them different
    /// types.
    Exact,
    /// As `Exact`, OR one side carries the synthetic `_1.._n` convention, which
    /// makes no claim about which slot is which (WI-442). That escape is what lets
    /// a named-binder callback `(acc: Acc, x: Elem)` accept a multi-param op's
    /// eta arrow `(_1, _2)`.
    ///
    /// Legitimate ONLY for a parameter list. Granting it to a data tuple would
    /// relate `(a: Int64, b: String)` to `(Int64, String)`, which proposal 004
    /// rule 4 makes a different type. This is the axis that is easy to miss —
    /// see [`TupleAlign`] on the miscount that cost.
    ExactOrSynthetic,
}

/// WI-775/WI-799: the alignment discipline [`align_named_tuple_slots`] applies
/// between two named-tuple field lists. The two positions look identical as TYPES
/// — WI-766 made an arrow's parameter list and a tuple type literally the same
/// surface — but they are not interchangeable, so the caller states which one it
/// is.
///
/// WI-799 made this a POLICY over two independent axes rather than an enum over
/// two SITES. The enum named where it was called from (`ByName` / `ParamList`),
/// which had gone wrong in three ways:
///
///  * `ByName` no longer aligned by name — WI-788 made it a slot-wise walk, and
///    its own doc conceded the name was "about names PARTICIPATING, not about the
///    correspondence being built from them". A reader reaching for "align by name"
///    got positional alignment.
///  * With the axes fused, how many there were was a matter of OPINION: WI-788
///    shipped a comment asserting the modes differed in EXACTLY ONE way (width),
///    missing the synthetic escape entirely. As data, the axes are countable.
///  * A site enum can only express the disciplines that have a SITE. "Exact width,
///    names exact" is a real third discipline that no site was named for, so the
///    equality relation took the width-subtyping mode and was silently asymmetric
///    — see [`TupleAlign::EQUALITY`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) struct TupleAlign {
    width: TupleWidth,
    names: TupleNames,
    order: TupleOrder,
}

impl TupleAlign {
    /// A DATA tuple under `<:`. FULLY NAME-KEYED: width from anywhere, names
    /// exact, order immaterial.
    ///
    /// WI-788 made the correspondence POSITIONAL, because the order-insensitive
    /// lookup it replaced admitted a PERMUTATION that the value representation
    /// never performs: the carrier keeps SOURCE order (WI-786) and a destructuring
    /// binder list read it POSITIONALLY (WI-785), so binder `i` received the
    /// value's `i`-th component while the typer had given it the type of the
    /// DECLARED `i`-th field — an operation declared `-> Int64` returned a
    /// `String` on a clean load.
    ///
    /// WI-803 restored the name-keying by fixing THE READER instead. The typer
    /// now resolves each binder's LABEL from the expected type and the matcher
    /// fetches that component by name (`Pattern::Tuple.labels`,
    /// `match_tuple_pattern`), so a permuted value hands each binder the
    /// component the typer typed it from. Order is a tuple's IDENTITY, never a
    /// term of `<:` — see [`TupleOrder`].
    pub(super) const DATA: Self = Self {
        width: TupleWidth::Subset,
        names: TupleNames::Exact,
        order: TupleOrder::Free,
    };

    /// An ARROW'S PARAMETER LIST. Equal arity, with the synthetic escape.
    ///
    /// Sound here and only here, and forced here: a parameter list is APPLIED
    /// positionally, so slot `i` is slot `i` and there are exactly as many slots
    /// as the call site passes arguments.
    ///
    /// WI-791: selected by the arrow's own `arity` child, never by the param
    /// slot's shape, so it is reached ONLY for a real parameter list (arity ≠ 1).
    /// A lone tuple-typed parameter is a DATA tuple and takes the [`Self::DATA`]
    /// road with everything else at arity one.
    ///
    /// WI-782: no by-name rung, which is why a permutation is not admitted by
    /// matching names up — the runtime performs no such reordering, so
    /// `(y: Bool, x: Int64)` is compared slot-for-slot against
    /// `(x: Int64, y: Bool)`, where matching by name accepted it and let an
    /// operation declared `-> Int64` evaluate to `Bool(true)` with no trap.
    ///
    /// WI-803: order [`TupleOrder::Preserved`], and here it is not an interim but
    /// the rule — a parameter list is applied by POSITION, so slot `i` is slot `i`
    /// and no by-label reader can be substituted for the one eval performs.
    pub(super) const PARAM_LIST: Self = Self {
        width: TupleWidth::Exact,
        names: TupleNames::ExactOrSynthetic,
        order: TupleOrder::Preserved,
    };

    /// EQUALITY between two data tuples — [`unify_named_tuple`]'s discipline, and
    /// the one the two-variant enum could not express (WI-799).
    ///
    /// Unification is SYMMETRIC by nature and is driven bidirectionally by the
    /// resolver, but it was taking the width-SUBTYPING mode, so it inherited a
    /// direction: `unify((x: A, y: B), (x: A))` succeeded while the same two
    /// arguments swapped failed. Width is an allowance for a consumer that reads
    /// only what it asked for; an equality has no consumer to be lenient toward,
    /// and answering differently depending on which side a caller happened to pass
    /// first is a defect however the relation is spelled.
    ///
    /// Identical to [`Self::PARAM_LIST`] on width and to [`Self::DATA`] on names —
    /// which is exactly why the axes have to be data rather than a site enum. It
    /// is neither site.
    ///
    /// WI-803: order [`TupleOrder::Preserved`], and this is the axis on which it
    /// now parts company with [`Self::DATA`]. Unification asks whether two tuples
    /// are the SAME TYPE, and §4.5 makes component order part of a tuple's
    /// identity — so `(a: Int64, b: String)` and `(b: String, a: Int64)` must not
    /// unify, even though each conforms to the other under `<:`.
    pub(super) const EQUALITY: Self = Self {
        width: TupleWidth::Exact,
        names: TupleNames::Exact,
        order: TupleOrder::Preserved,
    };

    pub(super) fn width(self) -> TupleWidth {
        self.width
    }

    pub(super) fn names(self) -> TupleNames {
        self.names
    }

    pub(super) fn order(self) -> TupleOrder {
        self.order
    }
}
