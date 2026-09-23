//! WI-361 stage 2: the term-backed Type classifier (`TypeExtractor`, `TypeHead`).

use super::*;

// ── WI-361 stage 2: term-backed Type classifier ─────────────────────────────

/// The reified structural form of a `Type` — the Rust mirror of the stdlib
/// `anthill.prelude.TypeExtractor` enum (sort.anthill), computed on demand by
/// [`extract_type`]. It backs the `anthill.reflect.extract` builtin and is the
/// engine-internal classifier the typer/codegen `match` over (replacing ad-hoc
/// functor-name-keyed dispatch as readers migrate).
///
/// **Dual-form.** A `Type` value is converging from a deep ADT representation
/// (`sort_ref(name)` / `parameterized(base, bindings)` terms) onto a *term
/// backing*: a bare sort `S` is `Term::Ref(S)`, a type application `S[p = v, …]`
/// is `Fn{S, named:[(p, v), …]}` (the base sort is the functor — no
/// `parameterized` wrapper). [`extract_type`] reads BOTH forms into the same
/// variants, so producers and readers can migrate independently. The structural
/// type forms (`arrow` / `effects_rows` / `named_tuple` / `denoted` / `nothing`
/// / `type_var`) stay entities in both worlds and read identically.
///
/// Sub-type children are owned [`Value`]s (the carrier the builtin emits and the
/// typer is migrating onto, WI-342); symbol heads (`SortRef`/`TypeVar` name,
/// `Parameterized` base) are `Symbol`s.
#[derive(Clone, Debug)]
pub enum TypeExtractor {
    /// A bare sort `S` — term-backed `Ref(S)` or deep `sort_ref(name: Ref(S))`.
    SortRef(Symbol),
    /// A type variable — deep `type_var(name)`.
    TypeVar(Symbol),
    /// A type application `S[p = v, …]` — term-backed `Fn{S, named}` or deep
    /// `parameterized(base, bindings)`. `bindings` are `(param, value-type)`.
    Parameterized {
        base: Symbol,
        bindings: Vec<(Symbol, Value)>,
    },
    /// An arrow type — `arrow(param, result, effects, arity)`. WI-791: `arity` is
    /// the parameter-list LENGTH as written, and is what says how to read `param`
    /// (arity 1 ⇒ the sole parameter's type; otherwise ⇒ the parameter list, a
    /// `named_tuple` of exactly `arity` fields).
    ///
    /// DECODED here, like the sibling `Symbol` fields, rather than handed on as a
    /// raw `Value`: this is the boundary whose job is to turn a term's children
    /// into Rust values, and leaving arity undecoded made every consumer write its
    /// own `Const(Int)` reader. An arrow whose child is missing or unreadable is
    /// [`TypeExtractor::Error`], not an arrow with a guessed count.
    Arrow {
        param: Value,
        result: Value,
        effects: Value,
        arity: usize,
    },
    /// WI-1083 — a UNIVERSALLY QUANTIFIED type, `∀ binders. body`: the type of an
    /// operation that declares type parameters, taken as a function VALUE. Mirrors
    /// `anthill.prelude.TypeExtractor.PolyType`; ∀ by construction, so no quantifier
    /// is stored (see that entity's doc for why a per-binder one would make an
    /// illegal state representable).
    ///
    /// `binders` ARE VARIABLES, NOT NAMES — each is the bound variable's own term,
    /// classifying as [`TypeExtractor::FlexVar`]. WI-1079's rule is why: `id` is a
    /// variable's identity and `name` is not, so a `Symbol` could not say which
    /// occurrences of `body` a binder binds — which is a binder's whole content.
    ///
    /// EVERY CONSUMER INSTANTIATES ([`instantiate_poly_type`]) rather than reading
    /// this directly: a ∀ is a schema, and comparing one against a monotype without
    /// ∀-elimination is the aliasing the eta gate used to exclude these operations
    /// over.
    PolyType {
        binders: Vec<Value>,
        /// WI-20260904-50B2K part (c) — the `=>` of `∀a. C a => t`; EMPTY for a plain ∀.
        context: Vec<Value>,
        body: Value,
    },
    /// A value standing in a type-argument position (`Modify[c]`) —
    /// `denoted(value)`; carries the value occurrence.
    Denoted(Value),
    /// WI-376: an expression-carried projection `s.T` / `s.Sort` — `value` is the
    /// receiver type occurrence (a param/local ref, or any typed expression),
    /// `member` the projected type-member name (`T`, `Sort`, `E`). The type-member
    /// sibling of [`TypeExtractor::Denoted`]; eliminated at the unify boundary by
    /// projecting the receiver's synthesized type (a `Denoted` value-in-type stays).
    ExprCarried { value: Value, member: Symbol },
    /// WI-428: a RIGID type-receiver projection `P.Key` / `MemStore.Key` — the
    /// type-keyed sibling of [`TypeExtractor::ExprCarried`] (design §5.3). `subject`
    /// is the projection's receiver type term (`Ref(P)` for a rigid type-parameter,
    /// `Ref(S)` for a concrete sort); `sort` is the sort whose `requires` chain lends
    /// the subject its members (= the subject's own symbol for a concrete-sort
    /// subject); `member` the projected member name.
    RigidTypeProjection {
        sort: Symbol,
        subject: Value,
        member: Symbol,
    },
    /// An effect row in type position — `effects_rows(expr: EffectExpression)`.
    EffectsRows(Value),
    /// A named tuple type — `named_tuple(fields)`; `(name, field-type)` pairs.
    NamedTuple(Vec<(Symbol, Value)>),
    /// The bottom type `nothing`.
    Nothing,
    /// Not a well-formed type form (a non-type term or a malformed type
    /// expression). Keeps [`extract_type`] total. Note: in the *term-backed*
    /// representation a parameterized type is structurally identical to an
    /// ordinary data term `Fn{f, named}`, so a data term with named args reifies
    /// as `Parameterized` rather than `Error` — there is no structural type/data
    /// distinction (by design; the caller knows it holds a type). Only a bare
    /// `Fn{f}` with no args, or a non-functor / non-`Ref` shape, is `Error`.
    ///
    /// WI-1079 took the two LOGICAL VARIABLE carriers out of here. They were reported as
    /// malformed input — total in the letter, wrong in the spirit — and a reader could not
    /// tell an opaque constant from a unifiable hole. See [`TypeExtractor::FlexVar`].
    Error,
    /// WI-1079 — a still-FLEXIBLE logical variable (`Term::Var(Var::Global)`), which unifies
    /// with anything: an INSTANTIATED forall, the type `empty()` has at a use before its
    /// context pins it.
    ///
    /// `id` IS THE IDENTITY, `name` IS NOT, and a consumer that compares these must compare
    /// `id`: a variable's name is what a diagnostic prints, while two variables minted for one
    /// parameter name are different types that render alike (`?E` vs `?E`, the trap WI-1063
    /// records). Mirrors `anthill.prelude.TypeExtractor.FlexVar`.
    FlexVar { name: Symbol, id: u32 },
    /// WI-1079 — an OPAQUE CONSTANT (`Term::Var(Var::Rigid)`), which unifies with nothing but
    /// itself: an opened existential (WI-1063's ρ), or a parameter rigidified for the duration
    /// of a body check (WI-392 / WI-1059). `Var::Rigid`'s own doc names it — "equivalent to
    /// 'Skolem constant' (resolution literature) or 'eigenvariable' (sequent calculus)".
    ///
    /// THE DISTINCTION FROM [`FlexVar`](Self::FlexVar) IS THE WHOLE POINT of this variant
    /// pair. Converting a skolem into a `TypeVar` — the smaller change — would have kept
    /// `extract` total AND still lost what makes it a skolem, since `TypeVar(name)` carries a
    /// name and nothing else. Same `id` rule as its sibling.
    Skolem { name: Symbol, id: u32 },
}

/// The structural kind of a type carrier WITHOUT materializing its children —
/// the cheap classification shared by [`extract_type`] (which adds the child
/// payloads) and the dispatch-key readers ([`sort_functor_of`], the callable
/// decomposition in [`arrow_parts`]) that only need the head. Dual-form:
/// recognizes both the deep representation
/// (`sort_ref` / `parameterized` / …) and the term backing (`Ref(S)` /
/// `Fn{S, named}`).
pub(super) enum TypeHead {
    SortRef(Symbol),
    TypeVar(Symbol),
    /// WI-1079 — the ENGINE's own logical variables, which had no classification at all
    /// before: `head.functor_sym()` is `None` for a bare variable, so both fell out of the
    /// `else` below as [`TypeHead::Error`]. `FlexVar` unifies with anything (an instantiated
    /// forall); `Skolem` unifies with nothing but itself (an opened existential, or a
    /// parameter rigidified for a body check). Carried as the `VarId` because that is a
    /// variable's IDENTITY — two skolems of one parameter name are different types that
    /// render alike.
    FlexVar(VarId),
    Skolem(VarId),
    /// `base` is the base sort symbol. WI-361: a parameterized type is the term
    /// backing `Fn{S, named}` (the base sort IS the functor, bindings ARE the named
    /// args) on both carriers — there is no `parameterized(base, bindings)` wrapper.
    Parameterized {
        base: Symbol,
    },
    Arrow,
    /// WI-1083 — `∀ binders. body`, the type an eta-lifted type-parameterized
    /// operation has. Classified by head like every other form; the children are
    /// read only by [`extract_type`].
    PolyType,
    Denoted,
    ExprCarried,
    /// WI-428: a rigid type-receiver projection (`P.Key` / `MemStore.Key`).
    RigidProjection,
    EffectsRows,
    NamedTuple,
    Nothing,
    Error,
}

/// Classify a type carrier's head — see [`TypeHead`]. Cheap: reads at most the
/// `type_var` name, never the bindings / fields / arrow children. WI-361: a bare
/// sort is `Ref(S)` and a parameterized type is `Fn{S, named}` (functor = base
/// sort) on both carriers — there is no deep `sort_ref`/`parameterized` wrapper.
/// WI-20260918-CKD4J — the parameter a type NAMES, when it is a type variable
/// (`TypeExtractor.TypeVar[name = T]`, the form a sort's field typed by its own `T`
/// takes): its `name` symbol. `None` for any other type.
pub(crate) fn type_var_name_of_view<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<Symbol> {
    match type_head(kb, ty) {
        TypeHead::TypeVar(s) => Some(s),
        _ => None,
    }
}

pub(super) fn type_head<V: TermView>(kb: &KnowledgeBase, ty: &V) -> TypeHead {
    // WI-436: a 0-ary TypeExtractor meta-ctor (`Nothing`) canonicalizes to a bare
    // `Ref` head, so classify by the functor SYMBOL read off either spelling
    // (`functor_sym` accepts `Ref` and `Functor`) — otherwise `Nothing` would be
    // mis-read as a bare SortRef. A `Ref` whose symbol is an ordinary sort (NOT a
    // TypeExtractor meta-ctor) is the bare sort reference `Ref(S)` (WI-361).
    let head = ty.head(kb);
    let named_arity = match &head {
        ViewHead::Functor { named_arity, .. } => *named_arity,
        _ => 0,
    };
    // WI-20260902-CZJ2N: the retired `ViewHead::Ref` variant WAS this predicate. A
    // bare sort reference is a NULLARY functor head now, so the shape is spelled out.
    let is_bare_ref = matches!(
        head,
        ViewHead::Functor {
            pos_arity: 0,
            named_arity: 0,
            ..
        }
    );
    // WI-1079 — A BARE LOGICAL VARIABLE IS A TYPE, and before this arm it was the one form
    // that reached `Error` while being perfectly well-formed. It has no functor symbol, so it
    // fell through the `else` below and was reported as malformed input.
    //
    // `Var::DeBruijn` STAYS `Error`, and that is a statement rather than an omission: a
    // DeBruijn index is a RULE's binder, opened to a fresh `Global` before anything type-
    // checks, so a type carrying one is a rule term being read as a type — not a variable form
    // this layer represents. The BOUND type variable of a `forall` is a different thing again
    // and has no carrier yet; it arrives with `PolyType` (WI-1083).
    if let ViewHead::Var(v) = &head {
        return match v {
            Var::Global(vid) => TypeHead::FlexVar(*vid),
            Var::Rigid(vid) => TypeHead::Skolem(*vid),
            Var::DeBruijn(_) => TypeHead::Error,
        };
    }
    let Some(f) = head.functor_sym() else {
        return TypeHead::Error;
    };
    match kb.qualified_name_of(f) {
        "anthill.prelude.TypeExtractor.TypeVar" => match view_child_sym(kb, ty, "name") {
            Some(s) => TypeHead::TypeVar(s),
            None => TypeHead::Error,
        },
        "anthill.prelude.TypeExtractor.Nothing" => TypeHead::Nothing,
        // WI-818: the SAME bottom under its surface spelling. Two producers
        // exist for one concept: `anthill.prelude.Nothing` is the stdlib's
        // declared bottom SORT (nothing.anthill — what `Error.raise`'s declared
        // return resolves to via `import anthill.prelude.{Nothing}`), while
        // `TypeExtractor.Nothing` is the typer/reflect extractor tag
        // (register_prelude's scoped define + `make_nothing_type`). Without
        // this arm a body ending in a raise never typed (`Nothing <: s.T`
        // failed), which is why `Stream.head` stayed body-less from WI-567
        // until WI-818. Collapsing the two spellings into ONE symbol is the
        // deeper fix (they still differ for structural-identity readers).
        "anthill.prelude.Nothing" => TypeHead::Nothing,
        "anthill.prelude.TypeExtractor.Denoted" => TypeHead::Denoted,
        "anthill.prelude.TypeExtractor.ExprCarried" => TypeHead::ExprCarried,
        "anthill.prelude.TypeExtractor.RigidTypeProjection" => TypeHead::RigidProjection,
        "anthill.prelude.TypeExtractor.EffectsRows" => TypeHead::EffectsRows,
        "anthill.prelude.TypeExtractor.Arrow" => TypeHead::Arrow,
        "anthill.prelude.TypeExtractor.PolyType" => TypeHead::PolyType,
        "anthill.prelude.TypeExtractor.NamedTuple" => TypeHead::NamedTuple,
        // WI-425: a bare DotApply expression carrier (`s.cell` outside an
        // ExprCarried wrapper) is NOT a type — without this arm the named_arity>0
        // fallthrough below would classify it as a parameterized type over a
        // phantom sort named `dot_apply` (and `sort_functor_of_view` would report
        // that as a real sort head).
        qualified if qualified == dt::qualified(dt::DOT_APPLY) => TypeHead::Error,
        // An ordinary (non-meta-ctor) NULLARY head is the sort reference; a
        // `Fn{S, named}` with bindings is a parameterized type; anything else — a head
        // carrying POSITIONAL arguments — is malformed as a type, since a type's
        // arguments are named bindings.
        //
        // WI-20260902-CZJ2N — THE NULLARY ARM NOW COVERS `Fn{S, [], []}` TOO, and that
        // is a real reclassification rather than a rename. This comment used to read "a
        // no-arg `Fn{S}` of an ordinary sort is malformed (a bare sort is `Ref(S)`,
        // never `Fn{S}`)", and `is_bare_ref` was `matches!(head, ViewHead::Ref(_))`;
        // with that head retired, both spellings reach one arm. The shape has NOT gone
        // away — a `SymbolKind::Sort` name is exactly what the storage canon EXEMPTS, so
        // `sort_inst_to_value`'s concrete spec identity `Fn{S}` still exists in the
        // store — it has stopped being `TypeHead::Error`.
        //
        // THAT IS THE RIGHT ANSWER, and it is not what keeps the dispatch distinction:
        // `Fn{S}` is a spec identity the loader BUILDS deliberately, so classifying it
        // malformed was never a check anything relied on. What separates the concrete
        // identity from the WILDCARD `Ref(S)` is `impl_param_ref`, which matches
        // `Term::Ref` / `Term::Ident` on the raw term and never asks this function —
        // driven by `type_head_reads_both_nullary_sort_spellings_alike` below, whose
        // second half asserts the wildcard test still tells them apart.
        //
        // The trailing `_ => Error` is therefore NOT unreachable, which this ticket's
        // plan predicted it would be: `Fn{f, [x], []}` still lands there, and
        // `type_extract_test::extract_non_type_reifies_error` drives it.
        _ if is_bare_ref => TypeHead::SortRef(f),
        _ if named_arity > 0 => TypeHead::Parameterized { base: f },
        _ => TypeHead::Error,
    }
}

/// The canonical dispatch tag for a type's form — [`type_head`] mapped to the
/// `&str` names the unify/subtype dispatch arms match on. Unlike the raw functor
/// short-name, this canonicalizes BOTH
/// representations: a term-backed bare sort `Ref(S)` reports `"sort_ref"` and a
/// term-backed `Fn{S, named}` reports `"parameterized"`, so the dispatch arms
/// fire identically for the deep and the term-backed form (WI-361 stage 2). On
/// the deep form it agrees with the raw functor name for every Type constructor.
pub(super) fn type_dispatch_name(kb: &KnowledgeBase, ty: TermId) -> Option<&'static str> {
    type_dispatch_name_view(kb, &TermIdView(ty))
}

/// [`type_dispatch_name`] over any [`TermView`] carrier — the canonical dispatch
/// tag from [`type_head`], so the view-structural unify/subtype arms route a
/// `Value::Node` (or term-backed) carrier by its *canonical* form rather than its
/// raw functor. WI-361: once the parameterized carrier mirrors the term backing
/// (functor = base sort) and the producers build `Fn{S, named}`, the raw functor
/// is the base sort `S`, not `parameterized` — so dispatch MUST canonicalize or
/// the `(parameterized, parameterized)` arm (and the `denoted` alpha path beneath
/// it) is missed.
pub(super) fn type_dispatch_name_view<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
) -> Option<&'static str> {
    match type_head(kb, ty) {
        TypeHead::SortRef(_) => Some("sort_ref"),
        TypeHead::TypeVar(_) => Some("type_var"),
        TypeHead::Parameterized { .. } => Some("parameterized"),
        TypeHead::Arrow => Some("arrow"),
        // WI-1083 — NAMED, unlike the two variable forms beside it, and for the
        // opposite reason. A ∀ should never reach the structural arms at all
        // (`check_bare_ref` eliminates it at the reference, which is the one mint's one
        // consumer), and what it must never do if it somehow does is MATCH `arrow` —
        // comparing a schema to a monotype is exactly the aliasing the eta gate used to
        // exist for. Naming it makes that a mismatch no arm accepts; leaving it `None`
        // would file it under `Error`, which is reserved for malformed USER input
        // (WI-391) and would say the opposite of what a well-formed ∀ is.
        TypeHead::PolyType => Some("poly_type"),
        TypeHead::Denoted => Some("denoted"),
        TypeHead::ExprCarried => Some("expr_carried"),
        TypeHead::RigidProjection => Some("rigid_type_projection"),
        TypeHead::EffectsRows => Some("effects_rows"),
        TypeHead::NamedTuple => Some("named_tuple"),
        TypeHead::Nothing => Some("nothing"),
        TypeHead::Error => None,
        // WI-1079 — NO DISPATCH TAG, deliberately, and it is the one place the new forms are
        // NOT propagated. This tag routes the STRUCTURAL unify/subtype arms, and a variable
        // never reaches them: unification binds or refuses it first (`resolved_var`, the
        // rigid-vs-rigid identity compare). Both carriers answered `None` here before this
        // ticket because they answered `Error` above; giving them a name now would change
        // ROUTING, which is a typer change nothing asked for and which this ticket's scope —
        // "reflect cannot SEE these forms" — does not include.
        TypeHead::FlexVar(_) | TypeHead::Skolem(_) => None,
    }
}

/// Classify a (carrier-agnostic) type carrier into a [`TypeExtractor`] — the head
/// ([`type_head`]) plus its materialized child payloads. Total. Reads both the
/// deep and the term-backed Type representations (WI-361 stage 2).
pub fn extract_type<V: TermView>(kb: &KnowledgeBase, ty: &V) -> TypeExtractor {
    match type_head(kb, ty) {
        TypeHead::SortRef(s) => TypeExtractor::SortRef(s),
        TypeHead::TypeVar(s) => TypeExtractor::TypeVar(s),
        TypeHead::Nothing => TypeExtractor::Nothing,
        TypeHead::Error => TypeExtractor::Error,
        // WI-1079: the `VarId` splits into the two fields the reflect entity declares —
        // `id` the identity, `name` the rendering. Nothing else is read; a variable has no
        // children.
        TypeHead::FlexVar(vid) => TypeExtractor::FlexVar {
            name: vid.name(),
            id: vid.raw(),
        },
        TypeHead::Skolem(vid) => TypeExtractor::Skolem {
            name: vid.name(),
            id: vid.raw(),
        },
        TypeHead::Denoted => match view_child_value(kb, ty, "value") {
            Some(v) => TypeExtractor::Denoted(v),
            None => TypeExtractor::Error,
        },
        // WI-376: an expression-carried projection — read the receiver occurrence
        // (`value`) and the projected member name (`member`, a `Ref(sym)` ground
        // child read by `view_child_sym`). Either child missing → `Error`, keeping
        // `extract_type` total.
        TypeHead::ExprCarried => match (
            view_child_value(kb, ty, "value"),
            view_child_sym(kb, ty, "member"),
        ) {
            (Some(value), Some(member)) => TypeExtractor::ExprCarried { value, member },
            _ => TypeExtractor::Error,
        },
        // WI-428: a rigid type-receiver projection — declaring sort (`sort`), the
        // subject type term (`var`), and the member name; all `Ref(sym)` ground
        // children except the subject, which rides as a value for uniform reading.
        TypeHead::RigidProjection => match (
            view_child_sym(kb, ty, "sort"),
            view_child_value(kb, ty, "var"),
            view_child_sym(kb, ty, "member"),
        ) {
            (Some(sort), Some(subject), Some(member)) => TypeExtractor::RigidTypeProjection {
                sort,
                subject,
                member,
            },
            _ => TypeExtractor::Error,
        },
        TypeHead::EffectsRows => match view_child_value(kb, ty, "effects_expr") {
            Some(e) => TypeExtractor::EffectsRows(e),
            None => TypeExtractor::Error,
        },
        TypeHead::Arrow => match (
            view_child_value(kb, ty, "param"),
            view_child_value(kb, ty, "result"),
            view_child_value(kb, ty, "effects"),
            view_child_value(kb, ty, "arity").and_then(|a| match a {
                Value::Term { id, .. } => const_usize_of(kb, id),
                _ => None,
            }),
        ) {
            (Some(param), Some(result), Some(effects), Some(arity)) => TypeExtractor::Arrow {
                param,
                result,
                effects,
                arity,
            },
            _ => TypeExtractor::Error,
        },
        // WI-1083: the binder list is a `List[Term]` of BARE elements (not the
        // two-field records `Parameterized`/`NamedTuple` carry), so it decodes through
        // [`value_list_elements`]. A missing child is `Error`, keeping `extract_type` total
        // exactly as a child-less `Arrow` is — AND SO IS AN EMPTY BINDER LIST, which is the
        // half that matters more: `value_list_elements` cannot distinguish `nil` from a
        // list it could not decode, and a ∀ read with no binders is not an unreadable type
        // but the WRONG one (its body's bound variables would read as free, and
        // `instantiate_poly_type` would hand the body back with nothing freshened).
        // [`generalize_eta_arrow`] never mints one — "a `PolyType` has at least one binder"
        // is its stated invariant — so rejecting here enforces it rather than assuming it.
        TypeHead::PolyType => match (
            view_child_value(kb, ty, "binders"),
            view_child_value(kb, ty, "body"),
        ) {
            (Some(bs), Some(body)) => {
                let binders = value_list_elements(kb, &bs);
                if binders.is_empty() {
                    TypeExtractor::Error
                } else {
                    // WI-20260904-50B2K part (c): an ABSENT `context` child reads as the
                    // EMPTY context — a ∀ carried in a shape written before the field
                    // existed is a plain ∀, which is what it always was.
                    //
                    // A PRESENT-BUT-UNDECODABLE ONE IS AN ERROR, NOT AN EMPTY CONTEXT, and
                    // the first cut had it the other way. `value_list_elements` cannot tell
                    // `nil` from a list it failed to decode — the reason the `binders` arm
                    // ten lines up rejects an empty result outright — so mapping the child
                    // straight to `unwrap_or_default()` turned a malformed constraint list
                    // into "no constraints": a DROPPED REQUIREMENT, which is the wrong
                    // accept this whole slice exists to prevent. `value_is_nil_list`
                    // separates the two. /code-review found it.
                    match view_child_value(kb, ty, "context") {
                        None => TypeExtractor::PolyType {
                            binders,
                            context: Vec::new(),
                            body,
                        },
                        Some(cs) => {
                            let context = value_list_elements(kb, &cs);
                            if context.is_empty() && !value_is_nil_list(kb, &cs) {
                                TypeExtractor::Error
                            } else {
                                TypeExtractor::PolyType {
                                    binders,
                                    context,
                                    body,
                                }
                            }
                        }
                    }
                }
            }
            _ => TypeExtractor::Error,
        },
        TypeHead::NamedTuple => TypeExtractor::NamedTuple(named_tuple_fields(kb, ty)),
        TypeHead::Parameterized { base } => {
            // The named args ARE the bindings on both carriers (WI-361).
            TypeExtractor::Parameterized {
                base,
                bindings: term_backed_bindings(kb, ty),
            }
        }
    }
}

/// Bindings of a parameterized type `Fn{S, named}` — the named args ARE the
/// `(param, value-type)` bindings (no `bindings: List[TypeBinding]` wrapper). Reads
/// both carriers: a term-backed `TermId` and a `Value::Node` whose view exposes the
/// bindings as named args.
fn term_backed_bindings<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Vec<(Symbol, Value)> {
    ty.named_keys(kb)
        .into_iter()
        .filter_map(|k| named_child_value(kb, ty, k).map(|v| (k, v)))
        .collect()
}

/// Fields of a `named_tuple(fields: List[TypeField])` as `(name, field-type)`.
/// WI-361: carrier-agnostic — reads the single `fields` child (a `Term` cons-list
/// for a ground tuple, a `Value`-carried `List[TypeField]` for a poisoned
/// `Value::Node` tuple) and decodes it the same way for both.
pub(super) fn named_tuple_fields<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Vec<(Symbol, Value)> {
    match view_child_value(kb, ty, "fields") {
        Some(fields) => list_records_to_pairs(kb, &fields, "name", "type"),
        None => Vec::new(),
    }
}

/// A view's named child (keyed by short field name) as an owned [`Value`].
pub(super) fn view_child_value<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
    key: &str,
) -> Option<Value> {
    let sym = kb.lookup_symbol(key)?;
    named_child_value(kb, ty, sym)
}

/// A view's named child as the `Symbol` it references (`Ref(s)` / `Ident(s)`).
pub(super) fn view_child_sym<V: TermView>(kb: &KnowledgeBase, ty: &V, key: &str) -> Option<Symbol> {
    kb.value_symbol(&view_child_value(kb, ty, key)?)
}

/// The "sort head" of an inferred type — the least declared sort it
/// widens to, as a `Symbol` (WI-284). It reads the typer-reflect Type
/// shapes (the form the typer stores in `inferred_type`) and unwraps them to
/// the underlying sort symbol:
///   - bare `Ref(S)`                    → `S`
///   - `Fn{S, named}` (parameterized)   → `S` (params dropped)
///   - everything else                  → `None`
/// `None` is the unresolved-type-variable case (dispatch-undecidable for the
/// type-directed `@[simp]` engine) and the structural variants (arrow / named_tuple
/// / …), which have no single sort head.
pub fn sort_functor_of(kb: &KnowledgeBase, ty: TermId) -> Option<Symbol> {
    sort_functor_of_view(kb, &TermIdView(ty))
}

/// Carrier-agnostic [`sort_functor_of`] (WI-342): the sort head of any type read
/// through [`TermView`] — a ground `TermId` (via [`TermIdView`]) or a `Value` /
/// `Value::Node` carrier alike, so a consumer that has a `Value`-carried type need
/// not re-ground it just to widen to its sort. The sort head is the base of a bare
/// sort or a (deep / term-backed) parameterized type; the structural variants have
/// none. WI-320: `effects_rows`/`denoted`/`arrow` have no underlying sort head to
/// widen to — `None` means the sort head is undefined for an occurrence typed as one
/// of them, the correct conservative answer (no `@[simp]` rule targets those
/// positions yet).
pub fn sort_functor_of_view<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<Symbol> {
    match type_head(kb, ty) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s, .. } => Some(s),
        _ => None,
    }
}
