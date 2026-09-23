//! Named-tuple alignment and unification, under the `tuple_align` policy.

use super::*;

/// WI-442: are these named-tuple fields the canonical POSITIONAL convention —
/// exactly `_1, _2, …, _n` in order? This is the field-name shape the WI-355
/// tuple-arrow lowering and the [`operation_as_function_value`] eta arrow mint
/// produce for an UNNAMED arrow param / multi-param op (spec §4.5). Such names
/// are SYNTHETIC and make no claim about what the slots are called, which is what
/// lets [`align_named_tuple_slots`] zip a `_1.._n` list against a named-binder
/// arrow (`(acc, x)`) by position — in [`TupleAlign::PARAM_LIST`] mode only, since
/// only a parameter list is applied positionally (WI-775).
///
/// WI-782 first RETIRED this gate (letting any two equal-arity lists zip) and
/// then restored it, because dropping it made `operation get_a(t: (a: Int64, b:
/// Int64))` satisfy a genuinely 2-parameter `(p: Int64, q: Int64) -> Int64` — a
/// lone tuple-typed parameter collapsed to the tuple's own 2-field term, and no
/// name test could tell the two apart.
///
/// WI-791 TOOK THAT JOB AWAY, and this gate is better for it. Arity is now a
/// child of the arrow, so a collapsed tuple parameter never reaches
/// [`TupleAlign::PARAM_LIST`] at all — [`unify_arrow_params`] routes arity one to
/// the ordinary type relation. The gate no longer stands between a data tuple and
/// a parameter list; it is asked only about two genuine parameter LISTS of equal
/// length, where its question — do these agree on which slot is which? — is the
/// only one it was ever sound to answer.
///
/// That also closes the two spellings it demonstrably could NOT catch, both
/// MEASURED to load clean and then trap `ArityMismatch` at eval, and both
/// PRE-EXISTING rather than WI-782 regressions:
///
///   * the POSITIONAL spelling `(t: (Int64, Int64))`, whose components are minted
///     `_1, _2` by `intern_positional_label` — the idiomatic spelling was the one
///     that slipped through; and
///   * a LEADING-ZERO spelling `(t: (_01: Int64, _02: Int64))`, which the reading
///     below used to admit as synthetic (it was a bare `parse::<usize>()`, and
///     that accepts leading zeros). WI-790 closed that: `_01` is a USER label
///     here as it already was in eval, and the decision went eval's way — if
///     `_01` is a user label, a list spelling its binders `_01, _02` is a NAMED
///     list making a real claim about which slot is which, so zipping it against
///     `(p, q)` by position is precisely the unsoundness this gate exists to
///     refuse, not a courtesy to surface intent.
///
/// Neither is refused by a better name test — each is refused because 1 ≠ 2. That
/// stayed true through WI-790: the leading-zero program above is refused on ARITY
/// by `leading_zero_component_names_do_not_make_a_parameter_list`, one gate
/// earlier, so nothing depended on this function admitting it.
///
/// The index check requires the field at position `i` to be named `_{i+1}`, so it
/// (and the zip in `align_named_tuple_slots`) relies on [`named_tuple_fields`]
/// yielding fields in construction/declaration order — which it does (it reads
/// the `fields` list spine in order; only the per-element record args are
/// name-sorted, not the list).
fn is_positional_tuple_names(kb: &KnowledgeBase, fields: &[(Symbol, Value)]) -> bool {
    !fields.is_empty()
        && fields
            .iter()
            .enumerate()
            .all(|(i, (name, _))| is_positional_label_at(kb.local_name_of(*name), i))
}

/// WI-800: an [`align_named_tuple_slots`] correspondence — one `a` index per `b`
/// component. Inline up to 8; a wider tuple spills to the heap exactly as the old
/// `(Value, Value)` pair vector always did, so this only ever removes allocations,
/// never adds one. (8 is the usual small-buffer pick, NOT a measured cover of the
/// corpus's tuple arities — no such measurement was taken, and none is claimed.)
pub(super) type AlignedSlots = SmallVec<[usize; 8]>;

/// WI-442: align two named-tuple field lists — for each component of `b`, the
/// INDEX of the `a` component it corresponds to — or `None` when the shapes are
/// incompatible. A field-wise relation (unify / subtype) relates
/// `a_fields[slots[i]].1` to `b_fields[i].1`.
///
/// WI-800 made the correspondence itself the return value. It used to return the
/// `(a_type, b_type)` pairs directly, which discarded the one thing a caller that
/// is not a field-wise relation needs: WHICH slot of `a` each `b` component landed
/// on. The tuple-literal expected-type threading needs exactly that (it writes
/// back into `a`'s slots), and lacking it, it had its own order-blind by-name
/// lookup — a second, differently-behaved alignment one call away from this one.
/// Returning indices also spares the two `Value` clones per component that
/// building the pairs cost every relation on this path.
///
/// The CORRESPONDENCE is one walk for every discipline — slot by slot, in list
/// order (both field lists are in declaration / positional order, since the
/// `named_tuple` builders preserve it, so this is the correspondence the runtime
/// actually performs). What the caller chooses is not the walk but the POLICY it
/// runs under: [`TupleAlign`]'s three axes. Applying one policy to consumers that
/// read the tuple differently is precisely the WI-782 defect; naming the policies
/// after the two SITES that had one, rather than after the axes, is WI-799's.
///
/// * [`TupleAlign::DATA`] — a data tuple under `<:`. Name-keyed width, names
///   exact.
/// * [`TupleAlign::PARAM_LIST`] — an arrow's parameter list, APPLIED
///   positionally. Equal arity, with the synthetic `_1.._n` escape.
/// * [`TupleAlign::EQUALITY`] — unification. Equal arity, names exact.
///
/// WI-782, on why an order-insensitive rung is wrong for a parameter list — it
/// was order-insensitive and width-subtyping, and the runtime is neither.
/// WI-788 then established that a DATA tuple is no more order-insensitive than a
/// parameter list, so the two modes now share this one zip:
///   * ORDER — `(y: Bool, x: Int64)` satisfied `(x: Int64, y: Bool)` because the
///     same NAMES occur on both sides, but nothing reorders the ARGUMENTS, so
///     `f(7, true)` put `7` in the `Bool` slot and an operation declared
///     `-> Int64` evaluated to `Bool(true)` with no trap. Zipped by position it
///     fails on the types instead, which is correct.
///   * ARITY — a 2-parameter value satisfied a 3-parameter one, the extra field
///     width-ignored, then trapped `ArityMismatch` at eval. Eval passes exactly
///     as many arguments as the call site's type says, so a narrower parameter
///     list is not a supertype.
pub(super) fn align_named_tuple_slots(
    kb: &KnowledgeBase,
    a_fields: &[(Symbol, Value)],
    b_fields: &[(Symbol, Value)],
    mode: TupleAlign,
) -> Option<AlignedSlots> {
    // WI-799/WI-803: the THREE axes are `mode`'s FIELDS — see [`TupleWidth`] /
    // [`TupleNames`] / [`TupleOrder`] for what each admits and why. They were a
    // two-variant enum tabulated here, which is how the codebase came to disagree
    // with itself about how many axes there even were. Keep the count here honest:
    // WI-803 added `order` and this comment said "two" until the /simplify pass
    // caught it, which is that same drift starting over.
    //
    // WI-803 retired WI-804's ORDER interim by promoting order to the third axis
    // ([`TupleOrder`]) and fixing the READER that the interim was protecting.
    // What the interim said: `<:` between data tuples is properly NAME-KEYED, but
    // a destructuring binder list (WI-785) read by SLOT and COUNT, so admitting a
    // permutation bound binder `i` to a component the typer typed from a different
    // field — an operation declared `-> Int64` returning a `String` on a clean
    // load. Width was admitted anyway because it changes the COUNT and so fails
    // LOUDLY; only the silent half was held back.
    //
    // The reader now binds by LABEL: the typer resolves each binder's component
    // name from the expected type into `Pattern::Tuple.labels` and
    // `match_tuple_pattern` fetches by name. A permuted value therefore hands each
    // binder the component the typer typed it from, and the count no longer has to
    // agree either — so the loud half is retired with the silent one.
    //
    // The axis is deliberately NOT a `mode == TupleAlign::DATA` test: that would
    // reintroduce the named-SITE branch one line below the axes that exist to
    // replace it, which is the whole of WI-799.
    // EXHAUSTIVE, no wildcard: a new `TupleWidth` must force an arm here rather
    // than fall through to "no width check at all", which would read as handled.
    match mode.width() {
        TupleWidth::Exact => {
            if a_fields.len() != b_fields.len() {
                return None;
            }
        }
        TupleWidth::Subset => {
            if a_fields.len() < b_fields.len() {
                return None;
            }
        }
    }
    // Width stops SHORT of the unit type. Every test below is vacuous on an empty
    // `b`, so `(a: A, b: B)` would conform to `()` — but `()` is not "the record
    // with no fields", it is the UNIT sort, which §4.5 gives exactly ONE value,
    // and a 2-component tuple is not that value. Unit relates to unit only.
    if b_fields.is_empty() && !a_fields.is_empty() {
        return None;
    }
    // The SYNTHETIC escape is a whole-list property, so it is decided first and
    // bypasses the name walk entirely.
    if mode.names() == TupleNames::ExactOrSynthetic
        && (is_positional_tuple_names(kb, a_fields) || is_positional_tuple_names(kb, b_fields))
    {
        // THE TWO AXES ARE COUPLED HERE, and only here: this zip stops at the
        // SHORTER list, so it is a correct alignment only because the width gate
        // above already required equal arity. Pairing this escape with `Subset`
        // width would relate `(a: A, b: B, c: C)` to `(_1: A, _2: B)` by silent
        // TRUNCATION — the combination `mod tuple_align` exists to make
        // unconstructible. Asserted rather than assumed: the sealing is what makes
        // it true, and a seal is exactly the kind of thing a later edit reopens.
        debug_assert_eq!(
            a_fields.len(),
            b_fields.len(),
            "WI-799: the synthetic escape zips, so it requires TupleWidth::Exact; \
             a Subset-width policy reaching here would align by truncation",
        );
        // WI-800, on what a RELEASE build does if that assert's invariant is ever
        // broken: these indices are `b`'s positions, so a SHORTER `a` makes
        // `aligned_pairs` panic on `a_fields[slot]` rather than truncate to the
        // shorter list as the pair-building zip used to. A panic in the typer is not
        // a diagnostic and is not an improvement — but it is a LOUD wrong over a
        // silent one, and the seal plus the assert above are what keep it
        // unreachable. Do not "fix" it by clamping to the shorter length: that
        // restores exactly the silent truncation the seal exists to prevent.
        return Some((0..b_fields.len()).collect());
    }
    // Name-keyed. The ORDER axis says only WHERE each lookup starts:
    //   * `Preserved` — resume after the previous match, so each `b` name must
    //     occur in `a` AFTER the one before it. Dropping components preserves the
    //     order of those that remain, so width still passes; a PERMUTATION does
    //     not. At equal arity this degenerates to the slot-for-slot agreement
    //     `PARAM_LIST` needs, which is why one walk serves every discipline.
    //   * `Free` — restart from 0, so a permutation aligns. FIRST match, which is
    //     `field_access`' own rule; see [`TupleOrder::Free`] on the duplicate-label
    //     disagreement (WI-805) that resuming caused.
    let mut next = 0;
    let mut slots = AlignedSlots::with_capacity(b_fields.len());
    for (b_name, _) in b_fields {
        let from = match mode.order() {
            TupleOrder::Preserved => next,
            TupleOrder::Free => 0,
        };
        let off = a_fields[from..].iter().position(|(n, _)| n == b_name)?;
        slots.push(from + off);
        next = from + off + 1;
    }
    Some(slots)
}

/// WI-800: the `(a_type, b_type)` pairs an [`align_named_tuple_slots`] result stands
/// for, BORROWED — what a field-wise relation (unify / subtype) wants, and what the
/// alignment returned directly before the threading needed the indices themselves.
///
/// It is a function rather than three inline zips because the pairing carries an
/// invariant the types do not enforce: the slot indexes `a`, the position indexes
/// `b`. Written out at each site, `b_fields[slot]` compiles and silently misaligns —
/// the failure class WI-788/799/800 each paid for once already. Borrowing keeps the
/// clone-elision that returning indices bought: the pairs are views, never copies.
///
/// The `zip` needs the assert, and it is the one line here that could fail QUIETLY.
/// `slots` is [`align_named_tuple_slots`]' output, which always has one entry per `b`
/// component — but `zip` stops at the shorter side, so a `slots` that had drifted
/// shorter would drop the trailing components and every caller's `.all(…)` would pass
/// VACUOUSLY on the ones it never looked at. That is a relation accepting a tuple whose
/// last component was never checked. (The other misuse — a slot out of range for `a` —
/// panics on the index and so cannot pass silently.)
pub(super) fn aligned_pairs<'a>(
    slots: &'a [usize],
    a_fields: &'a [(Symbol, Value)],
    b_fields: &'a [(Symbol, Value)],
) -> impl Iterator<Item = (&'a Value, &'a Value)> + 'a {
    debug_assert_eq!(
        slots.len(),
        b_fields.len(),
        "WI-800: an alignment has one slot per `b` component; a shorter `slots` would \
         zip-truncate and relate only a PREFIX, passing the rest vacuously",
    );
    slots
        .iter()
        .zip(b_fields.iter())
        .map(|(&slot, (_, b_ty))| (&a_fields[slot].1, b_ty))
}

/// WI-342: the sole `named_tuple` unification, carrier-agnostic over [`TermView`]
/// (both the `TermId` dispatch via [`TermIdView`] and the `Value` carrier route
/// here). Fields are read via [`named_tuple_fields`] on each carrier and aligned
/// SLOT BY SLOT with the names required to agree at each slot (WI-788 — these are
/// data tuples, whose component order is part of their type identity as much as
/// their names are). The equal-arity variant, with its synthetic `_1.._n` escape,
/// belongs to [`unify_arrow_params`] (WI-775) as [`TupleAlign::PARAM_LIST`].
///
/// WI-799: takes [`TupleAlign::EQUALITY`] — exact width, names exact. It used to
/// take the width-SUBTYPING mode, which made this relation ASYMMETRIC; see that
/// constant's doc for the defect and for why the two-variant enum it predates
/// could not express the fix.
pub(super) fn unify_named_tuple<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    unify_named_tuple_as(kb, subst, a, b, TupleAlign::EQUALITY)
}

/// [`unify_named_tuple`] with the alignment stated explicitly — `PARAM_LIST` only
/// from [`unify_arrow_params`], where the tuples are an arrow's parameter lists.
pub(super) fn unify_named_tuple_as<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
    mode: TupleAlign,
) -> bool {
    let a_fields = named_tuple_fields(kb, a);
    let b_fields = named_tuple_fields(kb, b);
    match align_named_tuple_slots(kb, &a_fields, &b_fields, mode) {
        // WI-20260904-60143 — a `for`, not `all`: every slot is unified and the verdict is
        // their conjunction, so which components a discarding caller reads back out of σ
        // does not depend on which slot disagreed first. See [`unify_parameterized_view`].
        // (`all` short-circuits; a `for` does not.)
        Some(slots) => {
            let mut ok = true;
            for (a_type, b_type) in aligned_pairs(&slots, &a_fields, &b_fields) {
                ok &= unify_types(kb, subst, a_type, b_type);
            }
            ok
        }
        None => false,
    }
}

/// WI-791: the parameter count two arrows AGREE on, or `None` when they do not
/// (or when either fails to state one) — in which case they are unrelatable and
/// both the unify and the subtype path refuse.
///
/// This is the whole of the ticket's fix, and it is one equality because the
/// count is a ground child rather than something inferred from the param slot's
/// shape: `operation get_a(t: (a: Int64, b: Int64))` mints arity 1 and a declared
/// `(p: Int64, q: Int64) -> R` mints arity 2, so the two stop being the same term
/// and stop standing in for each other. Every spelling that used to slip past the
/// name-shape gate — the positional `(Int64, Int64)`, whose components are minted
/// `_1, _2`, and the leading-zero `(_01: …, _02: …)`, which `parse::<usize>()`
/// accepted — fails here instead, because none of them is a question about names.
/// Both callers reach this only from an `(arrow, arrow)` dispatch arm, so a side
/// that states NO arity is a MALFORMED arrow, not a legitimate absence — the two
/// are folded into one `None` here because the relation has no diagnostic channel
/// (it returns `bool`), but they are not the same thing, and a malformed arrow
/// silently comparing as "not conformant" hides real defects: WI-791 shipped a
/// first draft in which two hand-built test arrows lost their `arity` child, and
/// both tests kept passing while covering nothing. The `debug_assert` makes that
/// loud where it can be — under test, which is the only place a hand-built arrow
/// term exists.
pub(super) fn agreed_arrow_arity<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    a: &A,
    b: &B,
) -> Option<usize> {
    // Intern once, not once per side — this runs on every arrow comparison.
    let arity_key = kb.intern("arity");
    let (na, nb) = (arrow_arity(kb, a, arity_key), arrow_arity(kb, b, arity_key));
    debug_assert!(
        na.is_some() && nb.is_some(),
        "WI-791: an `arrow` must state its parameter-list arity; \
         a term reaching the arrow-vs-arrow relation without one is malformed \
         (build it with `make_arrow_type` / `make_arrow_occ`, or add the `arity` \
         child explicitly via `make_arity_term`)",
    );
    (na? == nb?).then_some(na?)
}

/// WI-775: relate an arrow's two param slots, at an arity both sides agree on
/// (WI-791 established it in the caller). Identical to [`unify_types`] except
/// that two named-tuple PARAMETER LISTS align in [`TupleAlign::PARAM_LIST`] mode,
/// so a named-binder callback `(acc, x)` still unifies against a multi-param op's
/// eta arrow `(_1, _2)` (WI-442). Everything the param list CONTAINS is an
/// ordinary type again — a nested tuple component is data, and recursing through
/// `unify_types` re-imposes name alignment on it.
///
/// WI-791: `arity` selects WHICH relation applies, which is the second half of
/// the fix. At arity ONE the slot is not a list at all — it is the sole
/// parameter's TYPE — so it relates as an ordinary type, and a tuple there is
/// DATA, aligned by name with width subtyping. WI-782 had to route a lone
/// tuple-typed parameter through `PARAM_LIST` (it could not tell one from a list)
/// and knowingly paid for it by false-rejecting correct programs:
/// `get_x(t: (x: Int64, y: Bool))` handed to a `(u: (y: Bool, x: Int64)) -> R`
/// callback, and the narrower `(a: Int64)` against `(a: Int64, b: Int64)`. Both
/// load again, and for the right reason: the consumer reads `t.x` by NAME.
pub(super) fn unify_arrow_params<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
    arity: usize,
) -> bool {
    // WALK FIRST, then classify. A param slot routinely holds a bound var —
    // `unify_types` opens with the same two `walk_view`s for exactly that reason
    // (see its head). Classifying the RAW carrier would read `type_var`, miss the
    // arm, and fall through to `unify_types`, which walks, sees `named_tuple`,
    // and dispatches to the EQUALITY `unify_named_tuple` — silently downgrading
    // the mode on the one path that most needs it. WI-799 made that downgrade
    // STRICTER, not laxer (exact width, and no synthetic escape), so the
    // fallthrough now REFUSES a positional eta arrow rather than mis-relating it
    // — still wrong, still silent, and still what the walk prevents.
    let (aw, bw) = (walk_view(kb, subst, a), walk_view(kb, subst, b));
    if arity != 1 && both_named_tuples(kb, &aw, &bw) {
        return unify_named_tuple_as(kb, subst, &aw, &bw, TupleAlign::PARAM_LIST);
    }
    unify_types(kb, subst, &aw, &bw)
}

/// WI-775: do both carriers head as `named_tuple`? The shared head test behind
/// [`unify_arrow_params`] and [`arrow_params_compatible`] — kept in one place so
/// the two param-list entry points cannot drift apart.
pub(super) fn both_named_tuples<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    b: &B,
) -> bool {
    matches!(
        (
            type_dispatch_name_view(kb, a),
            type_dispatch_name_view(kb, b)
        ),
        (Some("named_tuple"), Some("named_tuple"))
    )
}
