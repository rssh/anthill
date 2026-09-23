//! `TypeResult` (a node's type plus its effects) and the type-value helpers the typer
//! builds results with: effect merging, arrow construction, deep resolution walks and
//! symbol substitution over carried types.

use super::*;

// ── TypeResult ─────────────────────────────────────────────────

/// Result of type_check: inferred type + updated env + collected effects.
/// Mirrors typing_pass_spec.anthill: `TypeResult(type: Type, env: TypingEnv, effects: List[Type])`
pub struct TypeResult {
    /// WI-342 ty-slot migration: the inferred type is carrier-agnostic — a
    /// ground type rides as `Value::Term`, a denoted-bearing type (today: a
    /// lambda arrow carrying a `Modify[c]` effect) as `Value::Node`. The typer is
    /// now `Value`-native end-to-end: consumers read it through [`TermView`]
    /// (`Value: TermView`); no re-grounding bridge remains.
    pub ty: Value,
    pub env: TypingEnv,
    /// WI-342 effects-vertical: effect labels are carrier-agnostic `Value`
    /// (ground → `Value::Term`, denoted-bearing → `Value::Node`). Pre-E2 every
    /// label is `Value::Term` (behaviour-identical to the old `Vec<TermId>`).
    pub effects: Vec<Value>,
    /// WI-283: the (possibly-rewritten) occurrence this result describes.
    /// The typer is *tree-producing*: every result carries the node it
    /// is the type of, so a parent build-frame can reassemble itself
    /// from rewritten children and the [`TypeBuildFrame::Stamp`] frame
    /// can record the inferred type onto the *resulting* node. For a
    /// node that no `@[simp]` rule rewrites this is the input occurrence
    /// (identity); a firing frame replaces it with the synthesized RHS
    /// (`synthesized_expr`, with the input occ as its `from`).
    pub node: Rc<NodeOccurrence>,
}

impl TypeResult {
    /// Pure result — no effects. WI-342: takes a ground `TermId` (the common
    /// case) and wraps it `Value::Term`, so the ~14 ground producers are
    /// unchanged. A producer of a `Value`-carried type (the LambdaBody Node
    /// arrow) builds `TypeResult { ty: <Value>, .. }` directly.
    pub fn pure(ty: TermId, env: TypingEnv, node: Rc<NodeOccurrence>) -> Self {
        Self {
            ty: Value::term(ty),
            env,
            effects: Vec::new(),
            node,
        }
    }

    /// Pure result whose type is already carrier-agnostic (`Value`) — e.g. a
    /// var-ref whose bound type came from the `Value`-carried env (WI-341 Stage
    /// A). A `Value::Node` (denoted-bearing callback arrow) flows through
    /// unchanged.
    pub fn pure_value(ty: Value, env: TypingEnv, node: Rc<NodeOccurrence>) -> Self {
        Self {
            ty,
            env,
            effects: Vec::new(),
            node,
        }
    }
}

/// Filter effects: keep only external effects (on non-local resources).
/// Effects on let-bound resources are local and don't propagate.
pub(crate) fn external_effects(
    kb: &KnowledgeBase,
    env: &TypingEnv,
    effects: &[Value],
) -> Vec<Value> {
    effects
        .iter()
        .filter(|effect| {
            // An effect like Modify[store] — check if 'store' is a local resource
            // Effect terms are sort_ref or parameterized. Extract the resource symbol.
            match extract_effect_resource_sym(kb, effect) {
                Some(sym) => !env.is_local_resource(sym),
                None => true, // can't determine resource — assume external
            }
        })
        .cloned()
        .collect()
}

/// Extract the resource symbol named by an effect label, carrier-agnostically
/// (WI-361/WI-342). A `Modify[c]` label is a `parameterized` type whose binding
/// value carries the resource as `denoted(Ref(c))` → `Some(c)`; a bare effect
/// label (e.g. `ReadIO` = a `sort_ref`, no binding) has no resource → `None`.
/// One `extract_type` classification reads BOTH the ground `TermId` and the
/// `Value::Node` (denoted-bearing) forms — no `TermId`-specific twin. Effect
/// labels are well-formed `parameterized(base: sort_ref(Modify), …)` types
/// (`make_sort_ref` base) in production, so the base classifies cleanly.
pub(crate) fn extract_effect_resource_sym(kb: &KnowledgeBase, effect: &Value) -> Option<Symbol> {
    let TypeExtractor::Parameterized { bindings, .. } = extract_type(kb, effect) else {
        return None;
    };
    bindings
        .iter()
        .find_map(|(_, v)| effect_binding_resource(kb, v))
}

/// The resource sort a `Modify` binding value names — `denoted(Ref(c)) → c` —
/// read carrier-agnostically over [`TermView`] (one walk for the ground `TermId`
/// `denoted(value: Ref(c))` and the `Value::Node` `Denoted{Expr::Ref(c)}`
/// occurrence alike, no per-carrier branch): [`type_head`] classifies the
/// `denoted` wrapper and the inner `sort_ref` / bare `Ref(S)` for either carrier,
/// and `named_arg` reads the `value` child as a `ViewItem` (itself a `TermView`).
fn effect_binding_resource<V: TermView>(kb: &KnowledgeBase, v: &V) -> Option<Symbol> {
    match type_head(kb, v) {
        TypeHead::Denoted => {
            let value_sym = kb.lookup_symbol("value")?;
            let inner = v.named_arg(kb, value_sym)?;
            match type_head(kb, &inner) {
                TypeHead::SortRef(s) => Some(s),
                _ => None,
            }
        }
        // Defensive: a non-`denoted` bare value names its sort directly.
        TypeHead::SortRef(s) => Some(s),
        _ => None,
    }
}

/// WI-342: place a carrier-agnostic type [`Value`] into a [`TypeChild`] slot of a
/// `Value::Node` occurrence being built — `Term` → `Ground`, `Node` → `Node`.
/// A scalar/`Var` type value is a typer bug (types are `Term`/`Node`); re-ground
/// it defensively so we don't panic.
/// WI-20260904-02ERR: [`value_to_type_child`] with the caller's provenance. A type
/// VARIABLE is the only child whose carrier is minted here rather than carried in, so it is
/// the only one whose span this decides; every other arm ignores it.
fn value_to_type_child_at(
    kb: &mut KnowledgeBase,
    v: &Value,
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> TypeChild {
    match v {
        Value::Var(var) => kb.type_var_child(*var, span, owner),
        other => value_to_type_child(kb, other),
    }
}

pub(super) fn value_to_type_child(kb: &mut KnowledgeBase, v: &Value) -> TypeChild {
    match v {
        Value::Term { id: t, .. } => TypeChild::Interned(*t),
        Value::Node(occ) => TypeChild::Node(Rc::clone(occ)),
        // WI-20260904-02ERR: a VARIABLE in a type slot is well-formed, not a typer bug.
        // WI-1079 admitted it at the READING end (`type_head`'s arm, and the `FlexVar` /
        // `Skolem` reflect forms) and never gave the BUILDING path the matching arm — so
        // this site called it "a typer bug" while `type_head` called the same form
        // "perfectly well-formed". `type_var_child` decides the carrier (see there: a
        // `DeBruijn` is still interned, a per-site `Global`/`Rigid` is not).
        //
        // THE SPAN COMES FROM THE CALLER when it has one — see [`value_to_type_child_at`],
        // which is what the container builders use. This bare entry point has none to
        // inherit, so it stamps `empty_span()`; `/code-review` found the earlier version
        // claiming producers called `type_var_child` directly when NONE did, which meant
        // every inferred var was stamped offset 0 of the FIRST LOADED SOURCE — a real file
        // position, in the prelude, that any diagnostic anchored on it would point at.
        Value::Var(v) => kb.type_var_child(*v, crate::kb::node_occurrence::empty_span(), None),
        other => {
            // A scalar/`Entity` is a typer bug here (types are `Term`/`Node`/`Var`);
            // mint a fresh `?ungrounded` type var so we don't panic in release.
            debug_assert!(
                false,
                "WI-342: non-type Value in a TypeChild slot: {other:?}"
            );
            let sym = kb.intern("?ungrounded");
            TypeChild::Interned(kb.make_type_var(sym))
        }
    }
}

/// WI-20260904-02ERR: does this type value force the OCCURRENCE carrier for its container?
///
/// Two forms cannot ride a hash-consed container. A `Value::Node` is the original one — a
/// `denoted` that cannot hash-cons. A `Value::Var` is the one this ticket added: a per-site
/// inference variable is unique to its site, so a container built over it is shareable with
/// NOTHING and interning it buys nothing while pinning a slot for ever.
///
/// THE GATE USED TO SPELL ONLY THE FIRST, and each builder's ground branch then read every
/// remaining field with `expect_term` — so a variable field walked into "expected a
/// hash-consed Value::Term, got Value::Var" rather than taking the carrier it needed.
/// MEASURED on `wi_50b2k_binder_inference_test`'s two nested/solved-arrow rows.
fn type_value_needs_occurrence(v: &Value) -> bool {
    matches!(v, Value::Node(_) | Value::Var(_))
}

/// WI-342: build `parameterized(base, bindings)` carrier-agnostically. When any
/// binding value is a `Value::Node` (e.g. a `List` whose element type is a
/// lambda-arrow carrying `Modify[c]`), mint a `Value::Node` via
/// [`KnowledgeBase::make_parameterized_occ`] so the poisoned child is CARRIED,
/// not re-grounded; otherwise the hash-consed [`KnowledgeBase::make_parameterized_type`].
/// `base` is the ground `sort_ref` (`List`/`Set`/…); `span`/`owner` stamp the new
/// occurrence when Node-carried.
pub(super) fn parameterized_value(
    kb: &mut KnowledgeBase,
    base: TermId,
    bindings: &[(Symbol, Value)],
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    // WI-470 scope: a parameterized type stays HASH-CONSED when closed — a `TermId`
    // `Fn{S, named}` carries its bindings fully (no erasure) and is the load-bearing
    // index key (`by_sort`/`fact_dedup`), exactly the "nominal, heavily-shared"
    // structure the representation note keeps hash-consed. Only a POISONED binding
    // value (a `denoted` that cannot hash-cons) forces the `Value::Node` carrier; the
    // arrow→effect-row spine is what this migration moves to occurrence-primary, not
    // `List[T]`. (Flipping closed parameterizeds to `Node` added erasure risk at every
    // `.as_term()` consumer for no payoff — reverted.)
    if bindings.iter().any(|(_, v)| type_value_needs_occurrence(v)) {
        let mut children: Vec<(Symbol, TypeChild)> = Vec::with_capacity(bindings.len());
        for (s, v) in bindings {
            children.push((*s, value_to_type_child_at(kb, v, span, owner)));
        }
        Value::Node(kb.make_parameterized_occ(TypeChild::Interned(base), children, span, owner))
    } else {
        // Closed: no binding is a `Value::Node` OR a `Value::Var` (checked above), so
        // every one is a `Value::Term` — hash-consed.
        let mut terms: Vec<(Symbol, TermId)> = Vec::with_capacity(bindings.len());
        for (s, v) in bindings {
            terms.push((*s, v.expect_term()));
        }
        Value::term(kb.make_parameterized_type(base, &terms))
    }
}

/// WI-342: build `named_tuple(fields)` carrier-agnostically. When any field type
/// is a `Value::Node` (e.g. a tuple element that is a lambda carrying `Modify[c]`),
/// mint a `Value::Node` via [`KnowledgeBase::make_named_tuple_occ`] — whose `fields`
/// is the WI-361 `Value`-carried `List[TypeField]` mirroring the term form — so the
/// poisoned field is CARRIED, not re-grounded; otherwise the hash-consed
/// [`KnowledgeBase::make_named_tuple_type`]. `TermView` reads both carriers alike.
pub(super) fn named_tuple_value(
    kb: &mut KnowledgeBase,
    fields: &[(Symbol, Value)],
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    if fields.iter().any(|(_, v)| type_value_needs_occurrence(v)) {
        let mut children: Vec<(Symbol, TypeChild)> = Vec::with_capacity(fields.len());
        for (s, v) in fields {
            children.push((*s, value_to_type_child_at(kb, v, span, owner)));
        }
        Value::Node(kb.make_named_tuple_occ(children, span, owner))
    } else {
        // Ground branch: no field is a `Value::Node` OR a `Value::Var` (checked above),
        // so every value is a `Value::Term` — unwrap it for the hash-consed builder.
        let mut terms: Vec<(Symbol, TermId)> = Vec::with_capacity(fields.len());
        for (s, v) in fields {
            terms.push((*s, v.expect_term()));
        }
        Value::term(kb.make_named_tuple_type(&terms))
    }
}

/// WI-20260824-6RXGD — the GROUND twin of a written value-in-type LITERAL type argument,
/// or `None` for every other shape.
///
/// A denoted written in a type-argument bracket (`field_access[Name = "x"](…)`,
/// `Vec[N = 3]`) arrives as a `Value::Node`: `Loader::type_expr_to_value` mints any
/// denoted-bearing type on that carrier because a denoted can carry POISON — a value
/// occurrence referring to a parameter, as in `Modify[c]`. A LITERAL carries none, and a
/// binding to a Node is unreadable by a term-backed callee: the `TermId` deep σ-walk that
/// resolves a return type mentioning the parameter stops at a non-`Term` binding (WI-394).
/// (The `Value`-level walk the apply resolves the return through now SPLICES such a binding
/// back — [`splice_non_term_bindings`] — so that stop no longer strands it; the re-grounding
/// is kept, and dropping it is unmeasured.)
/// [`synthesize_field_access`] already builds its own `Name` argument ground for that
/// reason; this gives the surface channel the same shape, so a call a person writes binds
/// where the compiler's own rewrite does.
///
/// NOT A CARRIER RULE CHANGE. Only this one call site re-grounds, and only a closed
/// literal — every other consumer of the written type still sees the Node it saw before,
/// including `lower_value_or_gate`, whose WI-366 gate reads term-representability to decide
/// whether a `provides Foo[Int64, 3]` clause is reported as unresolved rather than silently
/// accepted.
pub(super) fn ground_literal_denoted(kb: &mut KnowledgeBase, v: &Value) -> Option<Value> {
    let Value::Node(occ) = v else {
        return None;
    };
    let NodeKind::Type(TypeNode::Denoted { value }) = &occ.kind else {
        return None;
    };
    let NodeKind::Expr {
        expr: Expr::Const(lit),
        ..
    } = &value.kind
    else {
        return None;
    };
    let lit_term = kb.alloc(Term::Const(lit.clone()));
    Some(Value::term(kb.make_denoted(lit_term)))
}

/// WI-759 — the string a `denoted` value-in-type carries, or `None` for any other type form.
/// Carrier-neutral: the denoted's inner value rides as an occurrence from the typer's own
/// synthesis and as a hash-consed term from a written `[Name = "f"]` type argument.
pub(super) fn denoted_name(kb: &KnowledgeBase, v: &Value) -> Option<String> {
    let TypeExtractor::Denoted(inner) = extract_type(kb, v) else {
        return None;
    };
    match &inner {
        Value::Str(s) => Some(s.clone()),
        Value::Term { id } => match kb.get_term(*id) {
            Term::Const(Literal::String(s)) => Some(s.clone()),
            _ => None,
        },
        Value::Node(occ) => match occ.as_expr() {
            Some(Expr::Const(Literal::String(s))) => Some(s.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// WI-462: thread a tuple LITERAL's EXPECTED component types into its inferred ones, IN
/// PLACE. A component's inferred type can be a free var (`cons(h, t)` over a bare
/// `xs : List` binds `h` to a fresh `?_`) while the expected type carries the real one;
/// unifying the two binds the var (`h ⟹ xs.T`) and the σ-walked result replaces it, so the
/// tuple built from `fields` carries it. A component the expected type does not account for
/// is left alone.
///
/// WI-800: the correspondence is [`align_named_tuple_slots`] in [`TupleAlign::DATA`] mode —
/// the SAME walk, in the same argument order (`actual`, `expected`), that the relation
/// DECIDING this literal's conformance runs: `types_compatible` →
/// [`named_tuple_compatible`], which hardcodes `DATA`. It used to be an independent
/// order-blind lookup keyed on SHORT names, which disagreed with that relation in both
/// directions:
///
///  * it threaded where the relation REFUSES. A permuted literal `(b: ?_, a: 3)` against
///    `(a: Int64, b: String)` had `String` threaded into its `b` component, so the type
///    reported back in the "got" position was one the literal was never given and the
///    relation never accepted. Not a soundness bug — the relation still refuses the
///    program — but the message describes a fiction.
///  * it threaded a DIFFERENT slot than the relation aligns whenever the two disagree
///    about which component a name picks. `find` takes the FIRST component of that name;
///    the alignment takes the first at or after the previous match. With duplicate labels
///    those are different components, and it is the ALIGNMENT's choice that the relation
///    (and so the accepted program) is built on.
///
/// Sharing the walk also keeps width working: the drop is name-keyed from ANYWHERE
/// (WI-804), so `(head: h, mid: 1, rest: t)` against `(head: …, rest: …)` still threads
/// `rest`, which a raw index-for-index zip would have missed.
///
/// It also moves the keying from SHORT NAMES to SYMBOL IDENTITY, which the old doc had
/// warned against ("regardless of symbol identity"). That warning does not survive the
/// sharing, and the reason is not local: `fields` is the very list the built tuple type
/// carries, so the symbols conformance compares on the ACTUAL side are these, and the ones
/// it compares on the EXPECTED side are `exp_fields`'. Threading now agrees with the
/// relation by construction — where the symbols fail to line up, conformance fails on the
/// same comparison, so the hint is only ever withheld from a program that is refused
/// anyway.
///
/// `DATA` is the discipline of the relation that decides ACCEPTANCE, which is not the only
/// relation this literal's type may meet: `check_apply_iter`'s INFERENCE unify can reach
/// [`unify_named_tuple`], whose `EQUALITY` discipline takes exact width and so refuses a
/// width step this hint took. That is tolerated for the same reason the unify itself is —
/// its failure does not decide acceptance (see the `wi799_tuple_align_policy` module doc) —
/// but it is why the claim here is "the relation that decides", not "every relation that
/// runs". If a hint threaded under the wrong one of the three ever costs something
/// measurable, the fix is to make the discipline a parameter, not to widen `DATA`.
///
/// This is a hint, not a relation: alignment failure is a threading NO-OP (every component
/// keeps its inferred type) and the refusal is left to the relation, which reports it with
/// a located diagnostic. It must stay that way — a `TupleAlign::DATA` miss here is not
/// evidence the program is ill-typed, only that there is no expectation to push down.
///
/// RESIDUAL (not this ticket): the pass exists at all only because `types_compatible` will
/// not BIND a var on the actual side — a checking relation that bound would need no
/// separate hint, and no second correspondence to keep in step with the first. WI-800
/// removes the duplicate correspondence, not the duplicate pass.
pub(super) fn thread_expected_tuple_fields(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    fields: &mut [(Symbol, Value)],
    exp_fields: &[(Symbol, Value)],
) {
    let Some(slots) = align_named_tuple_slots(kb, fields, exp_fields, TupleAlign::DATA) else {
        return;
    };
    for (&slot, (_, exp_ty)) in slots.iter().zip(exp_fields.iter()) {
        unify_types(kb, subst, &fields[slot].1, exp_ty);
        let walked = walk_type_deep_value(kb, subst, &fields[slot].1);
        fields[slot].1 = walked;
    }
}

/// WI-470: build an `arrow(param, result, effects)` type as an occurrence —
/// always a `Value::Node` (occurrence-primary; the representation note disclaims
/// hash-consing for arrows/binders). A ground child rides as `TypeChild::Interned`
/// (poison flows up, not down), so a fully-ground arrow is a Node spine over
/// interned leaves; a denoted-bearing child (e.g. a lambda body effect `Modify[c]`)
/// is CARRIED as a poisoned `TypeChild::Node`. Consumers read either through
/// `TermView` (`arrow_compatible_view` / `subtype_effect_rows` at the op-boundary
/// return check); a genuine TermId demand materializes via `occurrence_to_term`
/// (WI-815 retired the memoizing `cached_term` wrapper — structural identity is
/// now a `GoalKey` walk, which needs no term at all). Label order is not
/// load-bearing — row unify/subtype compare label
/// sets. `span`/`owner` stamp the occurrences. (WI-342 introduced the Node arm for
/// poisoned arrows; WI-470 made it the sole arm.)
pub(super) fn make_arrow_value(
    kb: &mut KnowledgeBase,
    param: &Value,
    result: &Value,
    effects: &[Value],
    arity: usize,
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    // WI-470 (occurrence-primary): an inferred arrow is minted unconditionally as
    // a `Value::Node` occurrence — the representation note disclaims hash-consing
    // for arrows/binders, so the typer no longer chooses the hash-consed
    // `make_arrow_type` for the ground case. A ground child still rides as
    // `TypeChild::Interned(TermId)` (poison flows up, not down), so a fully-ground
    // arrow is a Node spine over interned leaves; consumers read it through
    // `TermView` (already carrier-agnostic — `unify_*`, `extract_type`,
    // `decompose_effect_row`), and a genuine TermId demand materializes via
    // `occurrence_to_term` (WI-815). Label order is not load-bearing (rows compare as
    // sets). The former `if poisoned` ground fast-path is retired: the hash-consed
    // arrow is now a *derived* form, not the primary one.
    let mut row = kb.make_empty_row_occ(span, owner);
    for label in effects.iter().rev() {
        // WI-470: a row-tail `Var` (a row-polymorphic body's open tail, threaded
        // here as `Value::Term(Var::Global)` by `effect_row_present_values`) folds
        // as `open(tail)`, NOT `present(var)` — mirroring the canonicalization the
        // retired ground path got from `build_canonical_effects_rows`. Wrapping a
        // tail var in `present` would make `decompose_effect_row` read it as a
        // present LABEL rather than the row tail (the WI-441 bug class), corrupting
        // row unify/subtype of an inferred row-polymorphic function value. (Present
        // labels here are bare sort_ref/parameterized atoms — `op.effects` /
        // inferred `body_effects` never carry pre-built `present`/`absent` atoms,
        // so no atom-preservation arm is needed, unlike the loader's row lowering.)
        let atom = match label {
            Value::Term { id: t, .. } if kb.row_tail_var_of(*t).is_some() => {
                let tail = kb.row_tail_var_of(*t).expect("checked is_some");
                kb.make_open_occ(TypeChild::Interned(tail), span, owner)
            }
            _ => {
                let label_child = value_to_type_child_at(kb, label, span, owner);
                kb.make_present_occ(label_child, span, owner)
            }
        };
        row = kb.make_merge_occ(TypeChild::Node(atom), TypeChild::Node(row), span, owner);
    }
    let effects_child =
        TypeChild::Node(kb.make_effects_rows_occ(TypeChild::Node(row), span, owner));
    // WI-20260904-02ERR: the arrow builder has the written span — an un-annotated binder
    // is the commonest inferred type var, so this is the one that most wants provenance.
    let param_child = value_to_type_child_at(kb, param, span, owner);
    let result_child = value_to_type_child_at(kb, result, span, owner);
    // WI-791: `arity` is passed in, never read back off `param` — the caller is the
    // only one that still knows whether a `named_tuple` param is a parameter LIST
    // or one tuple-typed parameter.
    let arrow = kb.make_arrow_occ(param_child, result_child, effects_child, arity, span, owner);
    Value::Node(arrow)
}

/// Merge two effect lists (set union). WI-342 effects-vertical: dedup
/// carrier-agnostically via [`views_structurally_equal`] (WI-486) — a ground
/// `Value::Term` label and a `Value::Node` label (now live — `Modify[c]`) of the
/// same structure dedup ACROSS carriers, not just within one. Set semantics thus
/// hold for both carriers at the merge point, not only after the row
/// canonicalizer.
pub(super) fn merge_effects(kb: &KnowledgeBase, a: &[Value], b: &[Value]) -> Vec<Value> {
    let mut result = a.to_vec();
    merge_effects_into(kb, &mut result, b);
    result
}

/// WI-657(8): in-place peer of [`merge_effects`] for the accumulator idiom
/// (`acc = merge_effects(kb, &acc, &more)`). Dedup-appends `incoming` into `acc`
/// without the per-call `acc.to_vec()` copy the by-value form pays — the
/// accumulation loops (`if/match/collection` join, per-arg effect roll-up) run
/// this many times per node, so copying the growing accumulator each round was an
/// O(n²) realloc. Behaviour-identical: same carrier-agnostic dedup, same order.
pub(super) fn merge_effects_into(kb: &KnowledgeBase, acc: &mut Vec<Value>, incoming: &[Value]) {
    for e in incoming {
        // WI-486: carrier-agnostic dedup so a ground `Value::Term` label and a
        // `Value::Node` `Modify[c]` of the same structure collapse across carriers.
        if !acc.iter().any(|r| views_structurally_equal(kb, r, e)) {
            acc.push(e.clone());
        }
    }
}

/// NodeOccurrence-aware var_ref detection — peer of
/// [`extract_var_ref_sym`] for the [`type_check_node`] dispatch path.
/// Returns the symbol the variable refers to when `occ`'s Expr is a
/// `VarRef`; otherwise `None`.
pub(super) fn extract_var_ref_sym_node(occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    if let NodeKind::Expr {
        expr: Expr::VarRef { name },
        ..
    } = &occ.kind
    {
        Some(*name)
    } else {
        None
    }
}

/// Recursively replace `Term::Ref(s)` with `Term::Ref(map[s])` inside
/// `term`. Used to substitute param-name references in operation effects
/// at call sites — e.g., `Cell.set` declares `effects Modify[c]` (with
/// `c` as its parameter); when called as `Cell.set(s, ...)` from a body,
/// `Modify[c]` is rewritten to `Modify[s]` so the calling op's declared
/// `effects Modify[s]` matches. Caller is expected to short-circuit on
/// empty maps (the typical case) — this fn does not check.
pub(crate) fn substitute_ref_syms(
    kb: &mut KnowledgeBase,
    term: TermId,
    map: &HashMap<Symbol, Symbol>,
) -> TermId {
    let var_ref_sym = kb.resolve_symbol("anthill.reflect.Expr.var_ref");
    substitute_ref_syms_rec(kb, term, map, var_ref_sym)
}

fn substitute_ref_syms_rec(
    kb: &mut KnowledgeBase,
    term: TermId,
    map: &HashMap<Symbol, Symbol>,
    var_ref_sym: Symbol,
) -> TermId {
    match kb.get_term(term).clone() {
        Term::Ref(s) => map
            .get(&s)
            .map_or(term, |&new_sym| kb.alloc(Term::Ref(new_sym))),
        // WI-592: a `var_ref(name: Ref(b))` is a binder VARIABLE reference, not a
        // bare param-name occurrence to rename. Leave it intact — recursing would
        // rewrite the binder's `name` child, corrupting `var_ref(name: c)` into
        // `var_ref(name: Green)` when `map` carries `c ↦ Green` (a constructor /
        // value argument, which `param_to_arg_head` records for a re-keyed
        // effect). The call's VALUE substitution (`build_call_guard_sigma` →
        // [`substitute_ref_terms`]) is what replaces a bound binder, and it does
        // so WHOLESALE (WI-552), so a binder→binder rename rides that path; this
        // pass touches only the bare `Ref` spine of effect LABELS (`Modify[c]` →
        // `Modify[s]`, WI-209). The same recurse-corruption WI-552 fixed in
        // `substitute_ref_terms`, here for the param-name rename.
        Term::Fn { functor, .. } if functor == var_ref_sym => term,
        Term::Fn { .. } => kb.map_fn_children(term, |kb, child| {
            substitute_ref_syms_rec(kb, child, map, var_ref_sym)
        }),
        _ => term,
    }
}

/// WI-342 effects-vertical: param-name `Ref` substitution over a carrier-agnostic
/// effect label. A ground (`Value::Term`) label rewrites via [`substitute_ref_syms`];
/// a `Value::Node` label needs occurrence-level `Ref` rewrite — deferred to E2
/// (no Node effect label is minted pre-E2, so it is currently unreachable).
pub(super) fn substitute_ref_syms_value(
    kb: &mut KnowledgeBase,
    e: &Value,
    map: &HashMap<Symbol, Symbol>,
) -> Value {
    match e {
        Value::Term { id: t, .. } => Value::term(substitute_ref_syms(kb, *t, map)),
        // WI-342 E2: re-key the `Ref` spine of a `Value::Node` label (a callee's
        // `Modify[c]` → the caller's `Modify[s]`) via the occurrence rewriter.
        Value::Node(occ) => Value::Node(crate::kb::node_occurrence::substitute_ref_syms_occ(
            occ, map,
        )),
        other => other.clone(),
    }
}

/// WI-342 effects-vertical: deep type-var resolution over a carrier-agnostic
/// effect label. Ground labels resolve via [`walk_type_deep`]; a live
/// `Value::Node` label (`Modify[c]`) carries its resource as an `Expr::Ref`, not
/// a type variable, so there is nothing to resolve and it is returned as-is —
/// correct, not merely deferred. (A future Node label that nests an unresolved
/// type-var in a binding would need an occurrence walk here; none is minted.)
pub(super) fn walk_type_deep_value(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    e: &Value,
) -> Value {
    walk_type_deep_value_g(kb, subst, e, false)
}

/// The grounding sibling of [`walk_type_deep_value`] — see [`walk_type_deep_g`]. δ-grounds
/// a concrete-subject `RigidProjection` (incl. one nested in a `Value::Node` binding) at
/// the call-site result-resolve points; otherwise identical pure-σ propagation.
pub(super) fn resolve_type_deep_value(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    e: &Value,
) -> Value {
    walk_type_deep_value_g(kb, subst, e, true)
}

/// Shared body of [`walk_type_deep_value`] (`ground = false`, pure σ) and
/// [`resolve_type_deep_value`] (`ground = true`, σ + call-time concrete-fill).
pub(super) fn walk_type_deep_value_g(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    e: &Value,
    ground: bool,
) -> Value {
    match e {
        // The term walk first — byte-identical wherever every binding it meets is a term —
        // then the bindings it cannot hold; see [`splice_non_term_bindings`].
        Value::Term { id: t, .. } => {
            let walked = walk_type_deep_g(kb, subst, *t, ground);
            splice_non_term_bindings(kb, subst, walked, ground)
                .unwrap_or_else(|| Value::term(walked))
        }
        // WI-441: a NODE-carried type DOES carry type-param vars — a callback
        // arrow's effect-row tail (`@ {EffP, -Modify[x]}`) is a GROUND child
        // Var inside the occurrence tree. The old "Nodes carry Refs, not
        // type-param vars" assumption left those un-walked, so the rigidify
        // pass missed them (the body then unified/leaked the raw Global).
        // Rebuild share-preservingly: unchanged subtrees keep their Rc.
        Value::Node(occ) => Value::Node(rewrite_type_occ_deep(kb, subst, occ, ground)),
        // WI-20260904-B1KFS — AN ENTITY-CARRIED TYPE'S INNER VARS ARE WALKED TOO. This
        // was `other => other.clone()`, so `Map[K = ?T]` had its `?T` resolved as a term
        // and left RAW as its `Value::Entity` twin — one type, two answers, and the
        // disagreeing one silently skips the resolution. That entity is not exotic:
        // `KnowledgeBase::fn_value` builds it for ANY application with a non-leaf child,
        // which is what `KnowledgeBase::reify` hands back for a type carrying an
        // occurrence. It is the SAME mistake the WI-441 note above records having already
        // been made and fixed for `Value::Node` — "the old `Nodes carry Refs, not
        // type-param vars` assumption left those un-walked, so the rigidify pass missed
        // them (the body then unified/leaked the raw Global)" — on the untouched twin.
        //
        // `Value::Tuple` rides the same arm: it is the functor-LESS application, and a
        // child of one is reached exactly as a child of an entity is.
        Value::Entity {
            functor,
            pos,
            named,
        } => Value::Entity {
            functor: *functor,
            pos: pos
                .iter()
                .map(|c| walk_type_deep_value_g(kb, subst, c, ground))
                .collect(),
            named: named
                .iter()
                .map(|(s, c)| (*s, walk_type_deep_value_g(kb, subst, c, ground)))
                .collect(),
        },
        Value::Tuple { pos, named } => Value::Tuple {
            pos: pos
                .iter()
                .map(|c| walk_type_deep_value_g(kb, subst, c, ground))
                .collect(),
            named: named
                .iter()
                .map(|(s, c)| (*s, walk_type_deep_value_g(kb, subst, c, ground)))
                .collect(),
        },
        // A `Value::Var` CHILD IS RESOLVED HERE, and the first draft of this arm said it
        // was "resolved by the caller's walk — see `walk_value_to_resolved`". That was
        // WRONG and the error is worth keeping visible: `walk_value_to_resolved` chases
        // the TOP-LEVEL var chain only and never descends into an entity (its own doc says
        // "every other form (`Value::Node`, entities) is already resolved"). So
        // `Entity{K: Value::Var(?T)}` walked to itself with `?T` raw while its term twin
        // `Map[K = Term::Var(?T)]` resolved — the SAME carrier disagreement this ticket
        // removes, surviving on the other VAR SPELLING. And the shape is producible
        // precisely because a `Value::Var` is a LEAF (`lowers_to_leaf_term`): `fn_value`
        // builds the entity as soon as a SIBLING child is non-leaf, so a var rides beside
        // it. `reify_value` (kb/mod.rs) needed both this arm and the children arms above
        // for the same reason; one without the other is half a walk.
        //
        // Cycle-guarded by the same `visited` reasoning as `walk_value_to_resolved`: a
        // bound var's value is walked, and an unbound one (or a cycle, which
        // `resolve_as_value` terminates) is returned as itself.
        Value::Var(Var::Global(vid)) => match subst.resolve_as_value(*vid) {
            Some(bound) => {
                let bound = bound.clone();
                walk_type_deep_value_g(kb, subst, &bound, ground)
            }
            None => e.clone(),
        },
        // A LEAF: a scalar, a rigid/De Bruijn var (neither is σ-bound), an interpreter
        // handle. Nothing beneath it to resolve.
        other => other.clone(),
    }
}

/// THE BINDINGS THE TERM WALK CANNOT HOLD. [`walk_type_deep_g`] is `TermId` in and out, so
/// a variable bound to a non-`Term` carrier comes back from it as the bare variable —
/// `walk_type` "deliberately STOPS" there (WI-394) — and a bare variable in a RESOLVED type
/// is a wildcard. A type rides the occurrence carrier whenever it carries a denoted, so an
/// operation's own type parameter bound to `Foo[T = Int64, N = 3]` was dropped from every
/// return type that names it. MEASURED, each loading with ZERO errors while its hash-consed
/// twin (`Foo[T = Int64]` against `Foo[T = String]`) is refused:
///
///   * `idf[A](x: A) -> A` returning `Foo[T = Int64, N = 3]` where the caller declares
///     `Foo[T = String, N = 3]` — the identity function, a WRONG ACCEPT;
///   * `wrap[A](x: A) -> Option[T = A]`, the same one level down;
///   * and a field projection on such a value refused outright: `field_access`'s declared
///     `-> FieldOf[T = R, Name = Name]` kept `R` a variable, so the reduction saw an
///     abstract operand and `mk(1).v` stayed `FieldOf[T = ?R, Name = "v"]`.
///
/// So each such variable is replaced by its binding, walked on ITS carrier, and the spine
/// above it is rebuilt through [`KnowledgeBase::fn_value`] — the one owner of the
/// term-versus-entity decision, which hash-conses an application whose children are all
/// leaves and builds a `Value::Entity` otherwise, read through `TermView` exactly like its
/// term twin. `None` when nothing needed splicing, so the common case keeps its term.
/// [`rewrite_type_occ_deep`] asks the same of an occurrence's interned children, and places
/// the answer with [`spliced_type_child`].
///
/// THE SAME TWO STOPS AS THE TERM WALK, for the same reasons: a NEUTRAL head
/// (`RigidProjection` / `ExprCarried`) is an identity slot and is not descended, and a
/// variable whose chain ends UNBOUND stays the variable it was. One more is this walk's
/// own: a binding that is a VALUE-world occurrence (an expression, not a `Type` /
/// `EffectExpression` one) is not a type, and is left as the variable rather than spliced
/// into a type position — the answer the term walk always gave it.
fn splice_non_term_bindings(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    t: TermId,
    ground: bool,
) -> Option<Value> {
    match kb.get_term(t).clone() {
        Term::Var(Var::Global(vid)) => {
            let bound = subst.resolve_as_value(vid)?;
            if matches!(bound, Value::Term { .. }) {
                return None; // `walk_type` already followed it
            }
            let bound = bound.clone();
            match walk_type_deep_value_g(kb, subst, &bound, ground) {
                // A chain ending at a VARIABLE, on either spelling — `TypeNode::Var` is a
                // variable's NESTED spelling and must not escape into value position
                // (WI-20260904-02ERR) — leaves the term walk's answer: nothing to splice.
                Value::Var(_) => None,
                Value::Node(occ) if matches!(occ.as_type(), Some(TypeNode::Var(_))) => None,
                Value::Node(occ) if occ.as_type().is_none() && occ.as_effect_expr().is_none() => {
                    None
                }
                Value::Term { id, .. } if id == t => None,
                // A LEAF (a value-in-type literal reaching the variable as `Value::Int(3)`) is
                // held as its term, the lowering `fn_value` gives the same leaf one level down
                // — so one type does not take two carriers depending on its depth.
                leaf if leaf.lowers_to_leaf_term() => {
                    kb.alloc_from_value(&leaf).ok().map(Value::term)
                }
                spliced => Some(spliced),
            }
        }
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            if matches!(
                type_head(kb, &TermIdView(t)),
                TypeHead::RigidProjection | TypeHead::ExprCarried
            ) {
                return None;
            }
            let mut changed = false;
            let mut pos = Vec::with_capacity(pos_args.len());
            for c in pos_args {
                let s = splice_non_term_bindings(kb, subst, c, ground);
                changed |= s.is_some();
                pos.push(s.unwrap_or_else(|| Value::term(c)));
            }
            let mut named = Vec::with_capacity(named_args.len());
            for (k, c) in named_args {
                let s = splice_non_term_bindings(kb, subst, c, ground);
                changed |= s.is_some();
                named.push((k, s.unwrap_or_else(|| Value::term(c))));
            }
            changed.then(|| kb.fn_value(functor, pos, named))
        }
        _ => None,
    }
}

/// WI-441: deep-resolve vars inside a NODE-carried type occurrence by
/// rebuilding it with every `TypeChild::Interned` mapped through
/// [`walk_type_deep`] and every `TypeChild::Node` recursed. Share-preserving:
/// an unchanged subtree returns its original `Rc` (so an all-ground-stable
/// tree costs only the traversal). `Denoted` (a VALUE occurrence — no type
/// vars) and `ExprCarried` (an expression receiver) are returned as-is — neither can
/// embed a row var today; extend when one does. `NamedTuple` WAS in that list and is
/// not any more: WI-20260904-02ERR walks its `Value`-carried `fields` through
/// [`walk_type_deep_value_g`], because once a type VARIABLE could ride the occurrence
/// carrier a tuple's field types stopped resolving (a wrong accept).
pub(super) fn rewrite_type_occ_deep(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    occ: &Rc<NodeOccurrence>,
    ground: bool,
) -> Rc<NodeOccurrence> {
    fn child(
        kb: &mut KnowledgeBase,
        subst: &Substitution,
        c: &TypeChild,
        ground: bool,
        changed: &mut bool,
    ) -> TypeChild {
        match c {
            TypeChild::Interned(t) => {
                let w = walk_type_deep_g(kb, subst, *t, ground);
                // The bindings the term walk cannot hold, as in `walk_type_deep_value_g`'s
                // `Value::Term` arm — the SAME drop on this carrier: `Two[L = A, R = Foo[T =
                // Int64, N = 3]]` with `A` bound to an occurrence-carried type kept `A` a
                // wildcard (MEASURED: a wrong `L` loaded clean). Placed by
                // [`spliced_type_child`].
                if let Some(spliced) = splice_non_term_bindings(kb, subst, w, ground) {
                    match spliced_type_child(kb, &spliced) {
                        Some(c) => {
                            *changed = true;
                            return c;
                        }
                        // A spliced type this carrier has no child form for. Loud in a
                        // debug build; a release keeps the term walk's answer, which is no
                        // worse than before the splice existed.
                        None => debug_assert!(
                            false,
                            "rewrite_type_occ_deep: no occurrence child for the spliced \
                             type {spliced:?}"
                        ),
                    }
                }
                if w != *t {
                    *changed = true;
                }
                TypeChild::Interned(w)
            }
            // WI-20260904-02ERR: the SECOND σ walk that must be able to change a child's
            // carrier (the first is `node_occurrence::map_type_child`). A bound `?T` becomes
            // the interned type it denotes; an unbound one keeps the un-interned leaf.
            // Without this arm the recursion below returns an occurrence and the variable is
            // never substituted on this path — the deep walk would silently stop resolving
            // type vars that moved carrier.
            TypeChild::Node(n) if matches!(n.as_type(), Some(TypeNode::Var(_))) => {
                let Some(TypeNode::Var(v)) = n.as_type() else {
                    unreachable!("guarded by the arm's `matches!`")
                };
                match v {
                    Var::Global(vid) => match subst.resolve_as_value(*vid) {
                        None => TypeChild::Node(Rc::clone(n)),
                        Some(bound) => {
                            let bound = bound.clone();
                            *changed = true;
                            // The same answer `SubstTypeRewrite::var` gives, from the same
                            // helper, so the two σ walks cannot drift: the type the binding
                            // DENOTES, or a loud `⊥` when it denotes none.
                            let t = crate::kb::node_occurrence::type_denoted_by(kb, &bound)
                                .unwrap_or_else(|| kb.alloc(Term::Bottom));
                            TypeChild::Interned(walk_type_deep_g(kb, subst, t, ground))
                        }
                    },
                    _ => TypeChild::Node(Rc::clone(n)),
                }
            }
            TypeChild::Node(n) => {
                let r = rewrite_type_occ_deep(kb, subst, n, ground);
                if !Rc::ptr_eq(&r, n) {
                    *changed = true;
                }
                TypeChild::Node(r)
            }
        }
    }
    let mut changed = false;
    let rebuilt: Option<NodeKind> = match &occ.kind {
        NodeKind::Type(node) => match node {
            // WI-20260904-02ERR: substituting a var can change its CARRIER, which a
            // `NodeKind` cannot express — so it is done one level up, in `child` above.
            TypeNode::Var(_) => None,
            TypeNode::Arrow {
                param,
                result,
                effects,
                arity,
            } => {
                let (p, r, e) = (
                    child(kb, subst, param, ground, &mut changed),
                    child(kb, subst, result, ground, &mut changed),
                    child(kb, subst, effects, ground, &mut changed),
                );
                // WI-791: arity is TRANSPLANTED, not rewritten — it is a count, not a
                // type, so σ / rigidify / δ-ground have nothing to say about it. This
                // is the property the reverted in-slot encoding lacked.
                Some(NodeKind::Type(TypeNode::Arrow {
                    param: p,
                    result: r,
                    effects: e,
                    arity: arity.clone(),
                }))
            }
            TypeNode::Parameterized { base, bindings } => {
                let b = child(kb, subst, base, ground, &mut changed);
                let bs: Vec<(Symbol, TypeChild)> = bindings
                    .iter()
                    .map(|(s, c)| (*s, child(kb, subst, c, ground, &mut changed)))
                    .collect();
                Some(NodeKind::Type(TypeNode::Parameterized {
                    base: b,
                    bindings: bs,
                }))
            }
            TypeNode::EffectsRows { effects_expr } => {
                let e = child(kb, subst, effects_expr, ground, &mut changed);
                Some(NodeKind::Type(TypeNode::EffectsRows { effects_expr: e }))
            }
            // WI-1083 — σ DOES NOT WALK UNDER A ∀, and that is a decision rather than
            // an omission: a `PolyType`'s binders are bound, so a σ that happened to
            // carry one of them would substitute under its own binder (capture). The
            // body's genuinely free variables lose nothing by it, because every
            // consumer instantiates the ∀ away first
            // ([`instantiate_poly_type`]) and what a σ walk meets downstream is the
            // instantiated body. Joins `Denoted` / `ExprCarried`, which decline for their
            // own reasons. (`NamedTuple` USED to be in this list and no longer is —
            // WI-20260904-02ERR gave it a walking arm above.)
            // WI-20260904-02ERR — A NAMED TUPLE'S FIELDS ARE WALKED. It used to join the
            // decliners above, and its "own reason" was never written down because it did
            // not have one: WI-361 carries `fields` as a `Value`-carried
            // `List[NamedTupleElement]` rather than as `TypeChild` children, so the
            // `child` helper this function is built on had nothing to walk — an omission
            // wearing a decision's clothes.
            //
            // IT WAS UNREACHABLE UNTIL A VARIABLE COULD RIDE THIS CARRIER. A tuple whose
            // field types were all ground stayed HASH-CONSED, and `walk_type_deep_g`
            // resolved its vars structurally; only a `denoted` field forced the occurrence
            // form, and a `denoted` carries no type var to resolve. Once a per-site type
            // variable stopped being interned, `(a: Int64, b: ?param)` took the occurrence
            // carrier and its `?param` stopped resolving — MEASURED as a WRONG ACCEPT, not
            // a crash: `both_halves_of_a_solved_arrow_resolve_together` LOADED
            // `Function[A = Int64, B = (a: Int64, b: String)]` whose body pins `b` to
            // `Int64`.
            //
            // `walk_type_deep_value_g` is the right walk and already total over the shapes
            // in that list — it descends `Value::Entity` (WI-20260904-B1KFS) and resolves a
            // `Value::Var` child (the arm below it), which are exactly the element records
            // and the field types.
            //
            // REBUILT UNCONDITIONALLY. The other arms set `changed` by comparing children,
            // but WI-486 left ONE `Value` comparator and it is not a cheap structural
            // equality — so this arm pays a rebuild of the tuple occurrence rather than a
            // deep compare to decide whether to. Correct either way; the share-preservation
            // the sibling arms get is what is given up.
            TypeNode::NamedTuple { fields } => {
                let walked = walk_type_deep_value_g(kb, subst, fields, ground);
                changed = true;
                Some(NodeKind::Type(TypeNode::NamedTuple { fields: walked }))
            }
            TypeNode::Denoted { .. } | TypeNode::ExprCarried { .. } | TypeNode::PolyType { .. } => {
                None
            }
        },
        NodeKind::EffectExpr(node) => match node {
            EffectExprNode::Merge { left, right } => {
                let (l, r) = (
                    child(kb, subst, left, ground, &mut changed),
                    child(kb, subst, right, ground, &mut changed),
                );
                Some(NodeKind::EffectExpr(EffectExprNode::Merge {
                    left: l,
                    right: r,
                }))
            }
            EffectExprNode::Present { label } => {
                let l = child(kb, subst, label, ground, &mut changed);
                Some(NodeKind::EffectExpr(EffectExprNode::Present { label: l }))
            }
            EffectExprNode::Guarded { label, guard } => {
                // Substitute the label (a `TypeChild`, like `Present`); the guard
                // `Value` is inert phase-1 metadata (decompose treats guarded as
                // present), carried unchanged. (This used to cite `TypeNode::NamedTuple`
                // as the precedent; that arm now walks its fields — WI-20260904-02ERR —
                // so the reason here stands on the guard's own inertness alone.)
                let l = child(kb, subst, label, ground, &mut changed);
                Some(NodeKind::EffectExpr(EffectExprNode::Guarded {
                    label: l,
                    guard: guard.clone(),
                }))
            }
            EffectExprNode::Absent { label } => {
                let l = child(kb, subst, label, ground, &mut changed);
                Some(NodeKind::EffectExpr(EffectExprNode::Absent { label: l }))
            }
            EffectExprNode::Open { tail } => {
                let t = child(kb, subst, tail, ground, &mut changed);
                Some(NodeKind::EffectExpr(EffectExprNode::Open { tail: t }))
            }
            EffectExprNode::EmptyRow => None,
        },
        _ => None,
    };
    match rebuilt {
        Some(kind) if changed => Rc::new(NodeOccurrence {
            kind,
            span: occ.span,
            owner: occ.owner,
        }),
        _ => Rc::clone(occ),
    }
}

/// A type [`splice_non_term_bindings`] produced, placed as a child of a type occurrence. A
/// term and an occurrence are children as they are — an occurrence-carried binding stays
/// one, UNINTERNED. An application rebuilt around one (a `Value::Entity`: `Option[T = A]`
/// with `A` bound to `Foo[T = Int64, N = 3]`) has no child form of its own, and is LOWERED
/// to the type term it is — `value_to_term`, lossless for an occurrence (WI-390) — which is
/// the answer [`rewrite_type_occ_deep`]'s own `TypeNode::Var` arm already gives a bound
/// variable: the type it denotes, interned. `None` only when it does not lower.
fn spliced_type_child(kb: &mut KnowledgeBase, v: &Value) -> Option<TypeChild> {
    match v {
        Value::Term { id, .. } => Some(TypeChild::Interned(*id)),
        Value::Node(occ) => Some(TypeChild::Node(Rc::clone(occ))),
        other => value_to_term(kb, other).ok().map(TypeChild::Interned),
    }
}

/// WI-342 env data-flow: resolve sort-level type params in a carrier-agnostic
/// constructor field type through the pattern subst (`case some(name)` over
/// `Option[T = String]` resolves `name`'s declared `T` to `String`). A field's
/// top-level type-param var is resolved through the subst via [`resolve_as_value`]
/// (so a `Value::Node` type-param value — a denoted-bearing arg — is surfaced as a
/// Node, not dropped); a ground binding routes through [`walk_type`] as before. A
/// `Value::Node` field carries `Ref`s, not type-param vars, so it is returned as-is
/// (same rationale as [`walk_type_deep_value`]).
pub(super) fn walk_type_value(kb: &KnowledgeBase, subst: &Substitution, ty: &Value) -> Value {
    // Iterative + cycle-guarded (WI-417), mirroring `walk_type`: follow a
    // `Value::Term(Var)` binding chain via `resolve_as_value`. A field type that
    // is itself a type-param var resolves through the subst's `Value` binding,
    // which may be a `Value::Node` (carried, not re-grounded). A non-var /
    // unbound term falls to the TermId walk; a `Value::Node` ends the chain. A
    // CYCLIC substitution (those vars are all unified) returns a representative
    // instead of recursing forever.
    let mut cur = ty.clone();
    let mut visited: SmallVec<[VarId; 4]> = SmallVec::new();
    loop {
        let t = match &cur {
            Value::Term { id: t, .. } => *t,
            _ => return cur,
        };
        let vid = match kb.get_term(t) {
            Term::Var(Var::Global(vid)) => *vid,
            _ => return Value::term(walk_type(kb, subst, t)),
        };
        if visited.contains(&vid) {
            return cur;
        }
        match subst.resolve_as_value(vid) {
            Some(bound) => {
                visited.push(vid);
                cur = bound.clone();
            }
            None => return Value::term(walk_type(kb, subst, t)),
        }
    }
}

/// DEEP counterpart of [`walk_type_value`] for a constructor pattern's field
/// type. [`walk_type_value`] resolves only a TOP-LEVEL type-param var; a
/// PARAMETERIZED field type (`recw.source: Stream[T = T, E = E]`) carries its
/// type-param vars NESTED in the `Fn`'s named_args, which the shallow
/// [`walk_type`] leaves untouched — so destructuring `case recw(src)` over a
/// `Rec[T = Elem, E = Eff]` scrutinee left `src : Stream[T = ?_, E = ?_]`
/// instead of threading the carrier's element/effect in (WI-413; the same gap
/// also blocked a `List`-impl `split -> Option[(T, List)]` from threading its
/// destructured head). Recurse into the parameterized type's children while
/// preserving the top-level `Value::Node` surfacing (a denoted-bearing
/// type-param value is carried, not re-grounded).
pub(super) fn walk_pattern_field_type_deep(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    ty: &Value,
) -> Value {
    // Top-level type-param var → resolve through the subst's `Value` binding
    // first, so a `Value::Node` (denoted) binding surfaces rather than being
    // dropped by the term-only deep walk (which keeps a Node-bound var).
    // Iterative + cycle-guarded (WI-417): a cyclic `Value::Term(Var)` chain
    // returns its representative rather than recursing forever.
    let mut cur = ty.clone();
    let mut visited: SmallVec<[VarId; 4]> = SmallVec::new();
    loop {
        let Value::Term { id: t, .. } = &cur else {
            break;
        };
        let Term::Var(Var::Global(vid)) = kb.get_term(*t) else {
            break;
        };
        let vid = *vid;
        if visited.contains(&vid) {
            break;
        }
        match subst.resolve_as_value(vid) {
            Some(bound) => {
                visited.push(vid);
                cur = bound.clone();
            }
            None => break,
        }
    }
    // Otherwise deep-walk: a parameterized `Fn` has its type params resolved in
    // every nested position; a ground term / `Value::Node` is returned as-is.
    walk_type_deep_value(kb, subst, &cur)
}
