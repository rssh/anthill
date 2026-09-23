//! Rendering types for diagnostics (`type_display_name*`, mismatch-pair rendering) and
//! small named-argument accessors over terms.

use super::*;

// ── Helpers ────────────────────────────────────────────────────

/// Render a type `Value` — the `Value` face of [`type_display_name_view`], which every
/// carrier goes through so one type cannot have two names.
///
/// WI-860 made this `pub` (its `TermId` twin [`type_display_name`] already was): the
/// answers of a reflect relation read through SLD arrive on BOTH carriers — a name
/// normalized by `extract_sort_ref` as a `Value::Term`, a field read straight off a
/// matched fact as a `Value::Node` — so anything comparing a relation's answers to a
/// rendering needs the carrier-neutral face. WI-702: shared with
/// [`crate::kb::KnowledgeBase::effect_row_blocking_equations`] so the defining-equation
/// request sites render a declined op's row identically.
pub fn type_display_name_value(kb: &KnowledgeBase, v: &Value) -> String {
    match v {
        // The one occurrence-only shape lives there; see [`type_display_name_occ`].
        Value::Node(occ) => type_display_name_occ(kb, occ),
        other => type_display_name_view(kb, other),
    }
}

/// A legible rendering of a `Literal` for type-error messages (mirrors
/// `persistence::print`'s `write_literal`: a float keeps its decimal point, a
/// string is quoted). Display-only — not a round-trip-faithful serialization.
fn literal_display(lit: &Literal) -> String {
    match lit {
        Literal::Int(n) => n.to_string(),
        Literal::BigInt(n) => n.to_string(),
        Literal::Float(f) => {
            let s = f.to_string();
            if s.contains('.') {
                s
            } else {
                format!("{s}.0")
            }
        }
        Literal::String(s) => {
            // The canonical `.anthill` string escaper (shared with `TermPrinter`), so
            // a denoted string literal renders identically across carriers rather than
            // via Rust `Debug`, which diverges on control/unicode chars.
            let mut buf = String::new();
            crate::persistence::print::write_anthill_string(s, &mut buf);
            buf
        }
        Literal::Bool(b) => if *b { "true" } else { "false" }.to_string(),
    }
}

/// Render a `Value::Node` `Type` / `EffectExpression` occurrence — the OCCURRENCE face of
/// [`type_display_name_view`], which does the whole of the work bar the one shape below.
///
/// THE ONE SHAPE THE SHARED HEAD CANNOT NAME, kept here for the same reason the
/// groundness gate keeps its own `Value::Node` arm: it is a deferral with a named owner,
/// not a missing arm. `type_node_head` reads a `Parameterized`'s head functor off its
/// BASE (WI-361 — the bindings are the named args, so the carrier and its term twin read
/// alike), and `parameterized_base_functor` has no symbol to give when that base is
/// itself an occurrence — a projection in base position, which `elim_child` can build.
/// The view then heads `Opaque` and the shared walk could only say `?`, dropping the base
/// AND the bindings. No term twin of this shape exists, so nothing disagrees with it;
/// what it must not do is regress.
fn type_display_name_occ(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> String {
    if let NodeKind::Type(TypeNode::Parameterized { base, bindings }) = &occ.kind {
        if !matches!(occ.head(kb), ViewHead::Opaque) {
            return type_display_name_view(kb, occ);
        }
        let base_name = type_child_display_name(kb, base);
        if bindings.is_empty() {
            return base_name;
        }
        let params: Vec<String> = bindings
            .iter()
            .map(|(p, c)| {
                format!(
                    "{} = {}",
                    kb.local_name_of(*p),
                    type_child_display_name(kb, c)
                )
            })
            .collect();
        return format!("{}[{}]", base_name, params.join(", "));
    }
    type_display_name_view(kb, occ)
}

/// Display name of a [`TypeChild`]: ground via [`type_display_name`], poisoned
/// via [`type_display_name_occ`].
fn type_child_display_name(kb: &KnowledgeBase, child: &TypeChild) -> String {
    match child {
        TypeChild::Interned(t) => type_display_name(kb, *t),
        TypeChild::Node(n) => type_display_name_occ(kb, n),
    }
}

/// WI-791: decode a non-negative `Const(Int)` term — the arrow `arity` child's
/// carrier. `None` for any other shape, which the display path treats as "arity
/// not stated" (a `Function[A, B]`, or a term this cannot read).
pub(super) fn const_usize_of(kb: &KnowledgeBase, t: TermId) -> Option<usize> {
    match kb.get_term(t) {
        Term::Const(Literal::Int(n)) if *n >= 0 => Some(*n as usize),
        _ => None,
    }
}

/// WI-791: render an arrow's param slot for a DIAGNOSTIC. At arity one the slot
/// holds the sole parameter's TYPE, so a TUPLE there needs its own
/// parameter-list parens: without them `(t: (a: A, b: B)) -> R` and
/// `(a: A, b: B) -> R` render to the same text, and a rejection reading
/// `expected (p: A, q: B) -> R, got (a: A, b: B) -> R` restates the very
/// confusion it is reporting.
///
/// `param_is_tuple` is a STRUCTURAL test, not "does the rendering start with a
/// paren": a nested arrow param renders `((a: A, b: B)) -> R`, which also opens
/// with `(`, and wrapping that would print `(((a: A, b: B)) -> R) -> S` where
/// every other non-tuple arity-1 param takes no parens at all (`Int64 -> R`).
fn display_arrow_param(rendered: String, arity: Option<usize>, param_is_tuple: bool) -> String {
    if arity == Some(1) && param_is_tuple {
        format!("({rendered})")
    } else {
        rendered
    }
}

/// WI-795: render a type mismatch's `(expected, actual)` pair for a diagnostic.
///
/// Each side normally renders independently via [`type_display_name_value`], and
/// for every mismatch but one that is enough. The exception is two arrows
/// differing ONLY in their WI-791 `arity` child: the arrow renderer walks the
/// param spine and never the arity, so both sides come out byte-identical and
/// the message reads `expected X, got X` — it tells the user two types disagree
/// while showing the same type twice, and says nothing about the parameter COUNT
/// that is the actual fault. That message is the one WI-794's per-binder
/// annotation check deliberately defers every misaligned-arity case to (blaming a
/// specific annotation when a parameter is missing is worse than saying nothing),
/// so a handoff target that cannot express an arity defect makes the deferral a
/// downgrade rather than a delegation.
///
/// When both sides are arrows whose arities DIFFER, each is qualified with its
/// own parameter count. A side whose param slot is NOT its own additionally drops
/// the rendered arrow: a lambda takes its parameter types from the CONTEXT, so a
/// 2-binder lambda at a 3-parameter slot carries the slot's 3-component list
/// under an arity of 2 — printing that list is what made the original message
/// unreadable, and it contradicts the count standing beside it.
///
/// Every other mismatch renders exactly as before, including an arrow pair
/// differing in a param TYPE: the qualification is gated on both arities being
/// present and UNEQUAL, which no param-type difference satisfies.
pub(super) fn render_mismatch_pair(
    kb: &KnowledgeBase,
    expected: &Value,
    actual: &Value,
) -> (String, String) {
    let (e, a) = render_mismatch_pair_by_cause(kb, expected, actual);
    // WI-776's 1-COLLAPSE NOTE WAS DELETED HERE (WI-20260818-YQB1Y), not moved. It explained
    // an `expected (a: Int64), got Int64` pair in which BOTH sides were correct — the two
    // faces of the schema 1-collapse, which the reader had no way to know about. 052 OQ5
    // option A dropped that collapse, so nothing computes a bare element where a one-field
    // tuple is expected any more: a `Without`/`Project` residual, a single-member projection
    // and a materialized one-column row are all `(a: A)` now. Every surviving instance of that
    // pair is an ordinary author error whose two rendered types state the whole fault, and a
    // note attributing it to a collapse that no longer exists would be a WRONG explanation.
    // WI-795: the CAUSE-AGNOSTIC backstop. Everything above fixes one KNOWN way
    // for two unequal types to render alike (the unwalked `arity` child). This
    // catches the rest without having to name them.
    //
    // Two identical sides are never a legitimate diagnostic: either the renderer
    // failed to express a distinction the checker made — the WI-795 defect, of
    // which `arity` was one instance and others plausibly remain in any child no
    // display arm walks — or the mismatch is spurious and the two types really
    // are equal, which is a worse bug in the check. Both deserve to be seen
    // rather than printed as a tautology the reader is left to decode.
    //
    // It reports rather than panics BECAUSE this is the diagnostic path: a
    // `debug_assert` here would convert a user's type error into a crash, and do
    // nothing at all in release, which is precisely when a confusing message is
    // most expensive. The user still gets the underlying rejection; they
    // additionally get told the message is incomplete, instead of silently
    // receiving one that cannot be acted on.
    // WI-872: ONE CAUSE NAMED OUT OF THE BACKSTOP'S RESIDUE, and it is the residue's
    // most likely member — two sorts that differ ONLY in namespace render alike by
    // construction, because every type rendering here is by SHORT name. Checked inside
    // the `e == a` guard rather than beside the arity cause: it is not a re-rendering
    // (there is no qualified renderer, and adding a parallel one to name a namespace
    // would duplicate the renderer), it is a NOTE, so it belongs exactly where the
    // untargeted note would otherwise go.
    if e == a {
        if let Some((expected_qn, actual_qn)) = short_name_sort_collision(kb, expected, actual) {
            return (
                e,
                format!(
                    "{a} {}",
                    short_name_collision_note(&expected_qn, &actual_qn)
                ),
            );
        }
        return (e, format!("{a} {IDENTICAL_RENDERING_NOTE}"));
    }
    (e, a)
}

/// WI-872 — the sort symbols a type MENTIONS, at any depth.
///
/// Shape-agnostic on purpose: it decodes no `sort_ref` / `parameterized` / tuple / arrow
/// layout, it collects every referenced symbol the KB knows as a SORT. A collision NESTED
/// under a parameterized type is therefore found by the same walk that finds a bare one,
/// and both are MEASURED reachable — `takeA(f: a.Foo)` given a `b.Foo`, and
/// `takeL(f: List[T = a.Foo])` given a `List[T = b.Foo]`, which before this printed
/// `expected List[T = Foo], got List[T = Foo]` with the "please report it" note.
fn mentioned_sort_syms<V: TermView>(kb: &KnowledgeBase, ty: &V, out: &mut Vec<Symbol>) {
    let head = ty.head(kb);
    match head {
        ViewHead::Functor {
            functor: Some(f), ..
        }
        | ViewHead::Ident(f) => {
            // A TYPE PARAMETER IS NOT A SORT HERE, though `sort_kind` says it is:
            // `load_abstract_sort` registers a `sort T = ?` alias with
            // `register_sort(.., SortKind::Sort)`, and after a stdlib load 37 `SortAlias`
            // sources are named `T`. Collecting them would let a `T`/`T` pair be found
            // FIRST and short-circuit a real sort collision deeper in the same type, and
            // would make the note's repair ("qualify it, or rename one sort") advice the
            // reader cannot take about a foreign sort's own parameter.
            // Canonical too: `sort_info` is keyed by the resolved copy, and a type term
            // may carry another interning of the same name.
            // Skipping the SYMBOL, not the subtree: a parameterized head still has its
            // bindings walked below, so a collision under `T[A = a.Foo]` is not lost.
            if !is_sort_param_symbol(kb, f)
                && (kb.sort_kind(f).is_some() || kb.sort_kind(kb.canonical_sort_sym(f)).is_some())
            {
                out.push(f);
            }
        }
        _ => {}
    }
    if let ViewHead::Functor {
        pos_arity,
        named_arity,
        ..
    } = head
    {
        for i in 0..pos_arity {
            if let Some(child) = ty.pos_arg(kb, i) {
                mentioned_sort_syms(kb, &child, out);
            }
        }
        if named_arity > 0 {
            for k in ty.named_keys(kb) {
                if let Some(child) = ty.named_arg(kb, k) {
                    mentioned_sort_syms(kb, &child, out);
                }
            }
        }
    }
}

/// WI-872 — do the two sides of an identically-rendering mismatch mention two DIFFERENT
/// sorts under one short name? Returns the offending pair's QUALIFIED names.
///
/// THE PAIR MUST BE THE DIFFERENCE BETWEEN THE SIDES, not merely present on both. A
/// naive cross product finds `a.Foo` on the expected side and `b.Foo` on the actual side
/// even when BOTH sides are `Map[K = a.Foo, V = b.Foo]` — one type that lawfully mentions
/// two same-short-named sorts — and would then blame a collision that is not the cause
/// while SUPPRESSING [`IDENTICAL_RENDERING_NOTE`], i.e. hiding exactly the renderer gap
/// the backstop exists to surface. So a symbol qualifies only if it is UNIQUE TO ITS
/// SIDE: `e` absent from the actual side, `a` absent from the expected side.
///
/// NOT DRIVEN, AND THE HONEST REASON: the population this guard protects is WI-795's
/// unknown residue — pairs that render alike for a cause nobody has named — so a fixture
/// for it cannot be written without first naming that cause, which is what the backstop
/// exists in place of. It is a guard against MISATTRIBUTION, and the direction it is
/// wrong in (silencing the backstop) is the expensive one. The two collision tests in
/// `wi872_short_name_sort_identity_test` do NOT discriminate it: in both, each sort is
/// unique to its side, so they pass with or without the uniqueness filter.
///
/// The first qualifying pair is reported — with two, the message would name a cause per
/// pair and the reader needs one to see what happened.
fn short_name_sort_collision(
    kb: &KnowledgeBase,
    expected: &Value,
    actual: &Value,
) -> Option<(String, String)> {
    let (mut expected_syms, mut actual_syms) = (Vec::new(), Vec::new());
    mentioned_sort_syms(kb, expected, &mut expected_syms);
    mentioned_sort_syms(kb, actual, &mut actual_syms);
    let unique_to =
        |s: &Symbol, other: &[Symbol]| !other.iter().any(|o| same_sort_canonical(kb, *s, *o));
    for e in &expected_syms {
        if !unique_to(e, &actual_syms) {
            continue;
        }
        for a in &actual_syms {
            if unique_to(a, &expected_syms)
                && !same_sort_canonical(kb, *e, *a)
                && kb.local_name_of(*e) == kb.local_name_of(*a)
            {
                return Some((
                    kb.qualified_name_of(*e).to_string(),
                    kb.qualified_name_of(*a).to_string(),
                ));
            }
        }
    }
    None
}

/// WI-872: appended in place of [`IDENTICAL_RENDERING_NOTE`] when the identical rendering
/// has a KNOWN cause — a short-name sort collision. Phrased so the reader can act: the
/// two qualified names ARE the repair (qualify the reference, or rename one sort), which
/// "please report it" could never be.
fn short_name_collision_note(expected_qn: &str, actual_qn: &str) -> String {
    format!(
        "(these render alike because two different sorts share the short name \
         `{}` — expected `{expected_qn}`, got `{actual_qn}`)",
        short_name_of(expected_qn)
    )
}

/// WI-795: appended to a mismatch whose two sides render identically — see
/// [`render_mismatch_pair`]. Phrased for the person reading the compiler output,
/// who otherwise has no way to tell a renderer gap from nonsense.
const IDENTICAL_RENDERING_NOTE: &str =
    "(these render alike but are not the same type — the difference is in a \
     component this diagnostic does not print; please report it)";

/// WI-795: the cause-directed half of [`render_mismatch_pair`] — renders each side
/// and qualifies BOTH with their parameter counts when the sides are arrows whose
/// arities differ. Split out so the identical-rendering backstop above wraps every
/// return path rather than just the fallthrough.
fn render_mismatch_pair_by_cause(
    kb: &KnowledgeBase,
    expected: &Value,
    actual: &Value,
) -> (String, String) {
    let (e, a) = (
        type_display_name_value(kb, expected),
        type_display_name_value(kb, actual),
    );
    // `lookup_symbol`, not `intern`: a diagnostic renders off `&KnowledgeBase`. A
    // KB that never interned "arity" holds no arrow, so there is nothing to qualify.
    let Some(arity_key) = kb.lookup_symbol("arity") else {
        return (e, a);
    };
    match (
        arrow_display_arity(kb, expected, arity_key),
        arrow_display_arity(kb, actual, arity_key),
    ) {
        (Some(ne), Some(na)) if ne != na => (
            arity_qualified_arrow(kb, expected, ne, e),
            arity_qualified_arrow(kb, actual, na, a),
        ),
        _ => (e, a),
    }
}

/// WI-795: the stated parameter-list arity of a type that IS an `arrow`, else
/// `None`. Unlike [`agreed_arrow_arity`] this runs on an arbitrary mismatched
/// pair rather than from an `(arrow, arrow)` dispatch arm, so the head is tested
/// rather than assumed.
///
/// BELT AND BRACES, stated honestly: the obvious way to reach this without the
/// head test — a non-arrow type with a parameter literally named `arity` bound to
/// an integer — does NOT in fact slip through, because a value-in-type binding is
/// a WI-302 `denoted` wrapper and [`const_usize_of`] already rejects it (measured
/// on `Vec[arity = 3]` vs `Vec[arity = 2]`, which renders identically with the
/// test removed). So this guards a shape no current spelling produces. It is kept
/// because the alternative is relying on that coincidence of two unrelated
/// encodings, but it should not be read as load-bearing.
fn arrow_display_arity(kb: &KnowledgeBase, ty: &Value, arity_key: Symbol) -> Option<usize> {
    if !matches!(type_head(kb, ty), TypeHead::Arrow) {
        return None;
    }
    arrow_arity(kb, ty, arity_key)
}

/// WI-795: qualify one side of an arity mismatch with its parameter count. The
/// rendered arrow is kept only when its param slot is the side's OWN parameter
/// list — see [`render_mismatch_pair`].
fn arity_qualified_arrow(kb: &KnowledgeBase, ty: &Value, arity: usize, rendered: String) -> String {
    if arrow_param_list_is_own(kb, ty, arity) {
        format!("a {arity}-parameter function {rendered}")
    } else {
        format!("a {arity}-parameter function")
    }
}

/// WI-795: does this arrow's `param` slot hold the parameter list its own `arity`
/// child describes? This is WI-791's consistency question read off one arrow: at
/// arity `n != 1` the slot IS the parameter list, so it must be a `named_tuple`
/// of exactly `n` components.
///
/// A `false` means the slot came from somewhere other than the side's own
/// written parameters — in practice a lambda that was handed the context's
/// parameter list, which is precisely the shape that renders identically to the
/// type it is being refused against.
///
/// ARITY 1 IS A KNOWN INCOMPLETENESS, not a proof of ownership. There the slot is
/// the sole parameter's TYPE, and every type is a well-formed sole-parameter type,
/// so consistency cannot distinguish a written parameter from an inherited one and
/// this answers `true` unconditionally. A 1-binder lambda at a 2-parameter slot
/// therefore still renders the context's list as its own
/// (`a 1-parameter function ((a: Int64, b: Int64)) -> Int64` — measured, and pinned
/// by `a_one_binder_lambda_still_shows_an_inherited_sole_parameter_type`). That is
/// tolerable where the n-parameter case was not: the count is stated, the two sides
/// differ (WI-791's arity-1 paren wrap sees to that), and the reported fault is
/// still the arity. Closing it needs provenance — whether the type was WRITTEN —
/// which no amount of looking at the finished arrow can recover.
fn arrow_param_list_is_own(kb: &KnowledgeBase, ty: &Value, arity: usize) -> bool {
    if arity == 1 {
        return true;
    }
    let Some(param) = view_child_value(kb, ty, "param") else {
        return false;
    };
    matches!(type_head(kb, &param), TypeHead::NamedTuple)
        && named_tuple_fields(kb, &param).len() == arity
}

/// The name a diagnostic shows for a hash-consed type — the `TermId` face of the ONE
/// walk every carrier goes through. See [`type_display_name_view`].
pub fn type_display_name(kb: &KnowledgeBase, ty: TermId) -> String {
    type_display_name_view(kb, &TermIdView(ty))
}

/// WI-20260904-B1KFS — ONE DISPLAY WALK, SO ONE TYPE HAS ONE NAME ON WHATEVER CARRIER IT
/// RIDES.
///
/// **THE DEFECT.** This was two hand-kept renderers — a `TermId` one keyed on
/// `Term::Fn`'s functor and a `Value::Node` one keyed on `TypeNode`/`EffectExprNode` —
/// and a THIRD carrier that reached neither: [`type_display_name_value`]'s
/// `other => resolved_functor_name(…)` answered a `Value::Entity` with its BARE FUNCTOR.
/// So `Map[K = Bool]` rendered `"Map[K = Bool]"` as a term and `"Map"` as its entity
/// twin, with the bindings SILENTLY DROPPED from a user-facing type error — the shape of
/// message that sends an author to the wrong place. The entity spelling is not exotic:
/// `KnowledgeBase::fn_value` builds it for ANY application with a non-leaf child, which
/// is exactly what `KnowledgeBase::reify` hands back for a type carrying an occurrence.
///
/// Keyed on [`ViewHead`], so every arm below is reached from every carrier. The nine
/// meta-constructor arms are the term renderer's, unchanged in what they print; the
/// effect-atom, `dot_apply` and `Ident` arms are the occurrence renderer's, which the
/// term carrier had been missing (a `Term::Ident` fell to `format!("{:?}")` and printed
/// `TermId(8960)` — the id, not even the term).
///
/// KEYED ON THE LOCAL NAME, with the looseness that implies — a user sort named `Arrow`
/// renders as an arrow. That is the rule the term renderer already ran on and WI-CZJ2N
/// restated for `Nothing`; one rule, not a new one.
///
/// **THE ORDER KEY IS A DIFFERENT QUESTION, and this is why it now has its own name.**
/// `build_canonical_effects_rows` sorts effect atoms by a display string, and under the
/// occurrence renderer's atom arms `present(A)` and `absent(A)` both render `"A"` — one
/// key for two different atoms. `sort_by_cached_key` is STABLE, so a shared key leaves
/// their order to the INPUT order and `{A, -A}` and `{-A, A}` canonicalize to two
/// different terms that then fail to unify. That reader takes
/// [`effect_atom_order_key`] instead, which is this walk's generic arm and nothing else.
fn type_display_name_view<V: TermView>(kb: &KnowledgeBase, v: &V) -> String {
    match v.head(kb) {
        // WI-307 code-review #7: render variables by their NAME, not a `{:?}` that
        // embeds allocation-order indices and would break the
        // canonical-form-stable-across-runs claim of `build_canonical_effects_rows`.
        // Two distinct vars sharing a textual name sort together, deliberately.
        ViewHead::Var(Var::Global(vid)) | ViewHead::Var(Var::Rigid(vid)) => {
            format!("?{}", kb.local_name_of(vid.name()))
        }
        // A De Bruijn index has no name. In practice these do not reach a type display
        // (the typer runs post-binder-open); the arm keeps the walk total.
        ViewHead::Var(Var::DeBruijn(_)) => "?".to_string(),
        // WI-404 / WI-6RXGD: a value-in-type LITERAL (`3` in `Vec[N = 3]`) renders as the
        // literal, so a mismatch reads `N = 3` vs `N = 4` rather than `TermId(8960)`.
        ViewHead::Const(lit) => literal_display(&lit),
        // WI-H054K: `bottom`, the spelling `persistence::print` gives the same term. A
        // `⊥` reaches a type position when σ binds a type-position variable to a carrier
        // denoting no type, and it is GROUND, hence CHECKED and named in a diagnostic.
        ViewHead::Bottom => "bottom".to_string(),
        ViewHead::Ident(s) => kb.local_name_of(s).to_string(),
        // A carrier with no structure to read — a closure, a stream. Not a type and not
        // nameable as one; `?` is what the occurrence renderer already answered.
        ViewHead::Opaque => "?".to_string(),
        // A functor-LESS application is a `Value::Tuple`, which no type has a twin for
        // (every hash-consed type application carries a functor). `?`, as before.
        ViewHead::Functor { functor: None, .. } => "?".to_string(),
        ViewHead::Functor {
            functor: Some(f),
            pos_arity,
            named_arity: _,
        } => {
            // THE LOWERCASE FORMS ARE KEYED ON THE QUALIFIED NAME, and the capitalized
            // `TypeExtractor` ones below on the LOCAL name. That is not an inconsistency:
            // the capitalized set has no homonym and has been keyed loosely since it was
            // written, while `guarded`, `merge` and `open` each name a SECOND, unrelated
            // stdlib constructor — `anthill.reflect.LogicalQuery.guarded(query,
            // condition)` beside `EffectExpression.guarded(label, guard)`,
            // `SortedSet.merge` beside `EffectExpression.merge`. Keyed locally, a
            // `LogicalQuery.guarded` term reaching the "raw term display" fallback would
            // render `"?"` (it has no `label` child) instead of its children — a silent
            // drop, in the walk that exists to remove them. `is_list_cons_cell` already
            // keys this way.
            if let Some(rendered) = qualified_form_display(kb, v, f) {
                return rendered;
            }
            match kb.local_name_of(f) {
                // Arrow(param, result, effects, arity) — WI-307/WI-331: `effects` is a
                // singular `EffectsRows(EffectExpression)` Type, not a legacy `List[Type]`.
                "Arrow" => {
                    let p = named_child_display(kb, v, "param");
                    let r = named_child_display(kb, v, "result");
                    // WI-791: an arity-1 tuple param is ONE parameter, not a list.
                    let arity = named_child(kb, v, "arity")
                        .and_then(|c| c.literal_int64(kb))
                        .and_then(|n| usize::try_from(n).ok());
                    let param_is_tuple = named_child(kb, v, "param")
                        .is_some_and(|c| matches!(type_head(kb, &c), TypeHead::NamedTuple));
                    format!("{} -> {}", display_arrow_param(p, arity, param_is_tuple), r)
                }
                "TypeVar" => named_child(kb, v, "name")
                    .and_then(|c| view_ref_symbol(kb, &c))
                    .map(|s| format!("?{}", kb.local_name_of(s)))
                    .unwrap_or_else(|| "?".to_string()),
                // `(f: T, n: U)`. WI-361: the fields ride as a `List[TypeField]` on BOTH
                // carriers, and [`list_records_to_pairs`] already decodes either.
                // ELEMENT-WISE, NOT VIA `list_records_to_pairs`, and the difference is a
                // SILENT DROP. That decoder skips a cell whose record is missing `name` or
                // `type` and walks on, so `(a: A, <malformed>)` would render `(a: A)` — a
                // component vanishing without trace. The term renderer emitted `?: ?` there,
                // which is the louder answer and the one kept; reading each field's children
                // through the same walk keeps both carriers on it.
                "NamedTuple" => {
                    let parts: Vec<String> = named_child(kb, v, "fields")
                        .map(|fs| value_list_elements(kb, &fs))
                        .unwrap_or_default()
                        .into_iter()
                        .map(|f| {
                            format!(
                                "{}: {}",
                                named_child_display(kb, &f, "name"),
                                named_child_display(kb, &f, "type")
                            )
                        })
                        .collect();
                    format!("({})", parts.join(", "))
                }
                // WI-CZJ2N — `Nothing` is a NULLARY constructor, and a nullary functor IS the
                // bare reference, so the two spellings the term renderer needed two arms for
                // are one arm here.
                "Nothing" => "nothing".to_string(),
                // WI-400 / WI-397: a projection renders `receiver.member`, not the generic
                // `ExprCarried[value = …]`, so a neutral-projection type error reads legibly.
                "ExprCarried" => format!(
                    "{}.{}",
                    named_child_display(kb, v, "value"),
                    named_child_display(kb, v, "member")
                ),
                // WI-428: a rigid type-receiver projection — `P.Key` / `MemStore.Key`.
                "RigidTypeProjection" => format!(
                    "{}.{}",
                    named_child_display(kb, v, "var"),
                    named_child_display(kb, v, "member")
                ),
                // WI-302: value-in-type — render the carried value directly (`Modify[c]`
                // shows `c`, not `denoted[value = c]`).
                "Denoted" => named_child_display(kb, v, "value"),
                // WI-320: EffectExpression-in-Type — row braces around the wrapped
                // expression, whose atoms are the arms just below.
                "EffectsRows" => format!("{{{}}}", named_child_display(kb, v, "effects_expr")),
                // A plain application: a parameterized type `S[p = v, …]` (WI-860: the same
                // string whether it arrived as `Fn{S, named}`, a `TypeNode::Parameterized`,
                // or an `Expr::Apply` read off a matched fact's carrier binding), and the
                // raw-term fallback for everything that is not one of the forms above.
                _ => type_application_display(kb, v, f, pos_arity),
            }
        }
    }
}

/// WI-20260904-B1KFS — the forms keyed on their QUALIFIED constructor name: the
/// `anthill.prelude.EffectExpression.*` atoms with the ROW they spell, and `dot_apply`.
/// `None` for any other functor, which then takes the local-name arms above.
///
/// **A ROW IS RENDERED AS A ROW, not as its fold.** `build_canonical_effects_rows` folds
/// a row into `merge(a₁, merge(a₂, …, empty_row))`, so a naive `merge => "{l}, {r}"` plus
/// an empty `empty_row` prints `{External, }` — a trailing separator on every row in the
/// system, empty rows included. [`join_row_parts`] drops the empty terminator instead.
///
/// **AND AN `absent` KEEPS ITS `-`.** Rendering it as its bare LABEL — which is what the
/// occurrence renderer did, and what the first draft of this merge adopted — makes
/// `{External}` and `{-External}` the SAME STRING, so a mismatch between them prints
/// `expected Stream[E = {External}], got Stream[E = {External}]` and trips the
/// identical-rendering backstop for the one difference the message exists to show.
/// Proposal 064's negative claim is not decoration; it cannot be dropped from the
/// rendering of the row that makes it. `-` therefore belongs HERE, on the atom, and not
/// (as it was) only in [`effect_atom_display`]'s caller-side arm — one spelling, on
/// whatever carrier and in whatever position the atom is read.
///
/// WI-478: a `guarded` atom shows its label and deliberately does not read its GUARD (the
/// conservatively-present view), matching the occurrence renderer.
fn qualified_form_display<V: TermView>(
    kb: &KnowledgeBase,
    v: &V,
    functor: Symbol,
) -> Option<String> {
    let qualified = kb.qualified_name_of(functor);
    // WI-302 field path `c.contents` inside a `denoted`, and the `s.provider.K` receiver
    // spine of a neutral projection. ARGUMENT-FREE ONLY: a `dot_apply` carrying arguments
    // is a CALL, and rendering it `r.n` would drop them — the silent drop this walk exists
    // to remove — so it falls through to the generic arm, which shows every child it has.
    //
    // Compared to `dt::qualified(…)` — the marker-stripped address a resolved KB symbol
    // reports and the one `wrapped_expr_head` interns for the occurrence carrier — and
    // NOT through `dt::is`, which additionally admits the bare short name. Short-name
    // admission is the looseness this whole dispatch exists to avoid.
    if qualified == dt::qualified(dt::DOT_APPLY) {
        if named_child(kb, v, "args").is_some_and(|a| is_list_cons_cell(kb, &a)) {
            return None;
        }
        return Some(format!(
            "{}.{}",
            named_child_display(kb, v, "receiver"),
            named_child_display(kb, v, "name")
        ));
    }
    let short = qualified.strip_prefix("anthill.prelude.EffectExpression.")?;
    match short {
        "present" => Some(named_child_display(kb, v, "label")),
        "absent" => Some(format!("-{}", named_child_display(kb, v, "label"))),
        "guarded" => Some(named_child_display(kb, v, "label")),
        "open" => Some(named_child_display(kb, v, "tail")),
        // The closed empty row. `{}` is how the language spells it; the term renderer had
        // no arm and leaked the CONSTRUCTOR name, so `Stream[E = {}]` read
        // `Stream[E = {empty_row}]` on that carrier. Five refusal assertions pinned that
        // text and now pin `E = {}` (WI-1059 ×2, WI-1061 ×2, WI-1063).
        "empty_row" => Some(String::new()),
        "merge" => Some(join_row_parts(
            named_child_display(kb, v, "left"),
            named_child_display(kb, v, "right"),
        )),
        // A constructor under this prefix that is none of the above: not a form this
        // renders, so it takes the generic application arm and shows its children rather
        // than being guessed at.
        _ => None,
    }
}

/// Join two rendered halves of a `merge` spine, dropping an EMPTY one — which is what the
/// `empty_row` terminator renders to. Without this every row carries a trailing `", "`.
fn join_row_parts(left: String, right: String) -> String {
    match (left.is_empty(), right.is_empty()) {
        (true, _) => right,
        (_, true) => left,
        _ => format!("{left}, {right}"),
    }
}

/// The generic `name(pos…)[k = v, …]` rendering — [`type_display_name_view`]'s default
/// arm, and the whole of [`effect_atom_order_key`].
///
/// POSITIONAL ARGUMENTS ARE SHOWN. The term renderer iterated `named_args` only and
/// printed a bare `S` for `Fn{S, [a], []}`; a type application has no positional
/// arguments, so what that silently dropped was always a NON-type term reaching the
/// "raw term display" fallback — and dropping its children is the same defect in
/// miniature as dropping `Map`'s bindings.
fn type_application_display<V: TermView>(
    kb: &KnowledgeBase,
    v: &V,
    functor: Symbol,
    pos_arity: usize,
) -> String {
    let mut out = kb.local_name_of(functor).to_string();
    if pos_arity > 0 {
        let ps: Vec<String> = (0..pos_arity)
            .map(|i| match v.pos_arg(kb, i) {
                Some(c) => type_display_name_item(kb, &c),
                None => "?".to_string(),
            })
            .collect();
        out.push_str(&format!("({})", ps.join(", ")));
    }
    let keys = v.named_keys(kb);
    if !keys.is_empty() {
        let ps: Vec<String> = keys
            .iter()
            .map(|k| {
                format!(
                    "{} = {}",
                    kb.local_name_of(*k),
                    match v.named_arg(kb, *k) {
                        Some(c) => type_display_name_item(kb, &c),
                        None => "?".to_string(),
                    }
                )
            })
            .collect();
        out.push_str(&format!("[{}]", ps.join(", ")));
    }
    out
}

/// WI-20260904-B1KFS — THE CANONICAL ORDER KEY FOR AN EFFECT ATOM, which is NOT its
/// display and must not become it again.
///
/// `KnowledgeBase::build_canonical_effects_rows` sorts a row's atoms by this and folds
/// them in that order, so two rows written in different orders reach the SAME term and
/// unify. It used to sort by [`type_display_name`], which was safe only while that
/// function rendered an atom as `present[label = A]`. It no longer does: an atom now
/// shows its LABEL, so `present(A)` and `absent(A)` render the same string —
/// `sort_by_cached_key` is stable, their order would fall back to the INPUT order, and
/// `{A, -A}` and `{-A, A}` would canonicalize to two different terms.
///
/// This is the generic application rendering applied UNCONDITIONALLY — the atom's
/// FUNCTOR and every child it has, so `present(A)`, `absent(A)` and two `guarded(A, …)`
/// with different guards each key differently. That is the property the sort needs:
/// INJECTIVE on the atom, and deterministic.
///
/// IT IS NOT THE OLD KEY BYTE-FOR-BYTE, and an earlier draft of this doc claimed it was.
/// The children render through [`type_display_name_item`], i.e. the NEW walk, so an atom
/// whose label is a `denoted` keys `present[label = c]` where it used to key
/// `present[label = Denoted[value = c]]`; positional arguments now show too. The ORDER of
/// atoms within a canonical row can therefore differ from before. That is harmless and is
/// not the same claim: a canonical form needs one representative per row, not the same
/// representative it had last release — rows are rebuilt from source at load, and both
/// sides of any comparison go through this one key.
pub(crate) fn effect_atom_order_key(kb: &KnowledgeBase, t: TermId) -> String {
    let v = TermIdView(t);
    match v.head(kb) {
        ViewHead::Functor {
            functor: Some(f),
            pos_arity,
            ..
        } => type_application_display(kb, &v, f, pos_arity),
        // Not an application (a bare row-tail var, a literal) — nothing to disambiguate,
        // so the display IS the key.
        _ => type_display_name_view(kb, &v),
    }
}

/// One named child of `v`, or `None` when the key is absent / unresolvable.
fn named_child<'a, V: TermView>(
    kb: &'a KnowledgeBase,
    v: &'a V,
    key: &str,
) -> Option<ViewItem<'a>> {
    kb.lookup_symbol(key).and_then(|s| v.named_arg(kb, s))
}

/// One named child of `v`, rendered — `?` when absent, which is what every hand-written
/// arm this walk replaced answered for a missing field.
fn named_child_display<V: TermView>(kb: &KnowledgeBase, v: &V, key: &str) -> String {
    match named_child(kb, v, key) {
        Some(c) => type_display_name_item(kb, &c),
        None => "?".to_string(),
    }
}

/// A child, rendered through the entry point its carrier owns — so a `Value::Node` child
/// still reaches [`type_display_name_occ`]'s one occurrence-only shape.
fn type_display_name_item(kb: &KnowledgeBase, item: &ViewItem<'_>) -> String {
    match item {
        ViewItem::Term(t) => type_display_name(kb, *t),
        ViewItem::Node(occ) => type_display_name_occ(kb, occ),
        ViewItem::Value(v) => type_display_name_value(kb, v),
        ViewItem::Owned(v) => type_display_name_value(kb, v),
    }
}

/// The symbol a view names, when it names one: a bare reference (`Ref` / nullary
/// application) or an unresolved `Ident`. The carrier-neutral face of the
/// `extract_ref_field` this replaced, which read `Term::Ref`/`Term::Ident` only.
fn view_ref_symbol<V: TermView>(kb: &KnowledgeBase, v: &V) -> Option<Symbol> {
    match v.head(kb) {
        ViewHead::Ident(s) => Some(s),
        ViewHead::Functor {
            functor: Some(f),
            pos_arity: 0,
            named_arity: 0,
        } => Some(f),
        _ => None,
    }
}

/// Functor symbols of a sort's constructor children.
pub(super) fn sort_constructor_syms(kb: &KnowledgeBase, sort: Symbol) -> Vec<Symbol> {
    // `sort_children` IS the answer now. It used to hand back entity-identity
    // TERMS, so this read each one's functor through `TermView::head()` (a 0-ary
    // constructor is spelled `Ref(c)` or `Fn{c}` depending on registration order)
    // and deduped, because the same constructor could appear under both
    // spellings. `sort_entities` stores symbols and dedups at registration, so
    // both the per-element unwrap and the dedup are gone.
    kb.sort_children(sort).to_vec()
}

pub fn get_named_arg(
    kb: &KnowledgeBase,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    key: &str,
) -> Option<TermId> {
    named_args
        .iter()
        .find(|(s, _)| kb.local_name_of(*s) == key)
        .map(|(_, v)| *v)
}

/// Read a `String`-const named field off a fact's named args — [`get_named_arg`]
/// narrowed to the field kind the realization/proof facts are mostly made of.
/// `None` for an absent field AND for one whose value is not a string literal, so
/// a caller that needs those distinguished must ask separately.
pub fn get_named_string_arg(
    kb: &KnowledgeBase,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    key: &str,
) -> Option<String> {
    match kb.get_term(get_named_arg(kb, named_args, key)?) {
        Term::Const(Literal::String(s)) => Some(s.clone()),
        _ => None,
    }
}

pub fn extract_sym_arg(
    kb: &KnowledgeBase,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    pos_args: &SmallVec<[TermId; 4]>,
    key: &str,
) -> Option<Symbol> {
    named_args
        .iter()
        .find(|(s, _)| kb.local_name_of(*s) == key)
        .and_then(|(_, v)| match kb.get_term(*v) {
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            _ => None,
        })
        .or_else(|| {
            pos_args.first().and_then(|v| match kb.get_term(*v) {
                Term::Ref(s) | Term::Ident(s) => Some(*s),
                _ => None,
            })
        })
}

pub fn unwrap_option(kb: &KnowledgeBase, opt: TermId) -> Option<TermId> {
    if let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(opt)
    {
        if kb.local_name_of(*functor) == "some" {
            if !pos_args.is_empty() {
                return Some(pos_args[0]);
            }
            if !named_args.is_empty() {
                return Some(named_args[0].1);
            }
        }
    }
    None
}

pub fn list_to_vec(kb: &KnowledgeBase, mut term: TermId) -> Vec<TermId> {
    let mut items = Vec::new();
    loop {
        match kb.get_term(term) {
            Term::Fn {
                functor,
                named_args,
                pos_args,
            } => {
                let name = kb.local_name_of(*functor);
                if name == "nil" {
                    break;
                }
                if name == "cons" {
                    let head = named_args
                        .iter()
                        .find(|(s, _)| kb.local_name_of(*s) == "head")
                        .map(|(_, v)| *v)
                        .or_else(|| pos_args.first().copied());
                    let tail = named_args
                        .iter()
                        .find(|(s, _)| kb.local_name_of(*s) == "tail")
                        .map(|(_, v)| *v)
                        .or_else(|| pos_args.get(1).copied());
                    if let Some(h) = head {
                        items.push(h);
                    }
                    if let Some(t) = tail {
                        term = t;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
    items
}
