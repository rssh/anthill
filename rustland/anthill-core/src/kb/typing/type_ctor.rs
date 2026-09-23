//! Type-level constructors evaluated at the return-type normalization boundary
//! (`Concat`, `Without`, `FieldOf`, `Project`, `Rename`, membership) and the relation
//! schema types they build.

use super::*;

/// WI-714 / WI-20260818-YQB1Y — build a relation SCHEMA type from an ordered column list:
/// `Unit` for zero columns, else the named tuple keyed by the columns IN GIVEN ORDER (not
/// re-sorted, so the type's field order matches the runtime materialized row). The shared
/// shape that [`assemble_relation_type`] (a fresh / projected relation) and
/// [`without_named_tuple_types`] (fix's post-drop residual) both produce.
///
/// THE SCHEMA IS THE ROW TYPE, AT EVERY ARITY — 052 OQ5, option A, decided
/// 2026-08-18. There is no arity-one special case: a one-column relation's schema is the
/// one-field named tuple `(age: Int64)`, its rows are `(age: 30)`, and `r.head.age` reads
/// the column. This function used to 1-collapse arity one to the sole column's TYPE, which
/// is what erased the relation's ARITY and made three distinct schemas indistinguishable:
///
///  * ARITY 1 — the column's NAME was gone, so a derived schema (`Concat` / `Without` /
///    `Project`) had no name for it and each REFUSED a one-column operand.
///  * ARITY 0 vs 1 — `Unit` meant both "no columns" and "one `Unit`-typed column"
///    (WI-728's recorded limit). `Unit` now means zero columns and nothing else, because
///    a one-`Unit`-column relation is `(u: Unit)`.
///  * ARITY n vs 1 — a named tuple meant both "n columns" and "ONE column whose type is
///    that named tuple". That one was a SILENT WRONG ANSWER rather than a refusal, because
///    the shape it was confused with is the ordinary working case and no type-level check
///    could separate them: over `entity pair_holder(p: (a: Int64, b: String))`,
///    `rule pairs(?p)` had the SAME schema type as a two-column relation over `a`/`b`, so
///    `person_row.join(pairs, …)` type-checked against a four-column merged schema while
///    the row `join_run` materializes had three. `Concat` was the one member of the family
///    with no runtime backstop for it — `fix` / `project` / `negate` each ask the VALUE
///    "is there a column of this name?" and refuse loudly, but merging is name-free, so
///    there was nothing to detect and nothing to check. Dropping the collapse is what
///    closes it; there was no fix inside the collapse.
///
/// THE VALUE AND TERM HALVES MOVED WITH IT, which is what kernel-language.md §6.8 required
/// of any revision ("revisiting it means moving both halves together"): `materialize_solution`
/// (eval/mod.rs) builds a one-column row as the one-field tuple, and `convert.rs` no longer
/// 1-collapses a single-member distributive projection `x.(f)` to the scalar `x.f`. All
/// three sides now agree at arity one.
pub(super) fn relation_schema_type(
    kb: &mut KnowledgeBase,
    columns: &[(Symbol, Value)],
    sp: crate::span::SourceSpan,
) -> Value {
    match columns.len() {
        0 => Value::term(kb.make_sort_ref_by_name("anthill.prelude.Unit")),
        _ => named_tuple_value(kb, columns, sp, None),
    }
}

/// WI-1128 / WI-20260818-YQB1Y — read a relation schema's COLUMNS, or `None` if the type is
/// no relation schema at all. `Some` is the field list in schema order; the EMPTY list is
/// the membership (0-column) schema `Unit`, which is a real answer and not a refusal.
///
/// TOTAL AND EXACT SINCE THE COLLAPSE WAS DROPPED. While arity one presented as the sole
/// column's element type, this reader had to classify three shapes it could not tell apart
/// (a collapsed single column, a written non-schema operand, and — undetectably — an
/// n-column schema versus a one-column schema over an n-field tuple), and every caller had
/// to phrase a two-reading message about a collapse that may never have happened. A schema
/// is now `Unit` or a named tuple, full stop: `Some(fields)` states the arity, and the
/// callers below can compute merged / dropped / selected schemas from it without a special
/// case at one column.
///
/// The MESSAGE is still each caller's own, because what the author should do next differs
/// per operation (merge / drop / select) and a shared sentence would have to be vague about
/// all three.
pub(super) fn schema_fields(kb: &KnowledgeBase, t: &Value) -> Option<Vec<(Symbol, Value)>> {
    // Resolved ONCE. A `Unit` that does not resolve costs a WRONG REFUSAL rather than a
    // wrong acceptance — every caller here refuses on `None`, so the failure mode is a
    // loud error naming `Unit` as a non-schema, not a silently mis-computed schema.
    let unit = kb.try_resolve_symbol("anthill.prelude.Unit");
    match extract_type(kb, t) {
        TypeExtractor::NamedTuple(fields) => Some(fields),
        // A BARE `Unit` sort ref — exactly what [`relation_schema_type`] mints for zero
        // columns, and now ONLY that. A `Unit[..]` APPLICATION is a different type and must
        // not read as membership, the same distinction `membership_schema_type` draws.
        TypeExtractor::SortRef(s) if unit == Some(s) => Some(Vec::new()),
        _ => None,
    }
}

/// WI-1128 / WI-20260818-YQB1Y — the sentence every derived-schema constructor appends when
/// its operand is not a relation schema. ONE wording, because after the collapse was dropped
/// there is exactly ONE way to fail this test — the operand is neither `Unit` nor a named
/// tuple — where there used to be three shapes needing three different pieces of advice.
pub(super) fn not_a_schema_tail(kb: &KnowledgeBase, v: &Value) -> String {
    format!(
        "`{}` is not a relation schema — a schema is the named tuple of the relation's \
         columns (`(name: String, age: Int64)`), or `Unit` for a membership relation with \
         none. If a `Relation[..]` type was written where its SCHEMA `r.T` was meant, or a \
         plain scalar where a relation was, it names no columns at all.",
        type_display_name_value(kb, v)
    )
}

/// WI-1128 — [`concat_named_tuple_types`]'s per-operand read, and the refusal when the
/// operand is no relation schema. ONE function for BOTH operands, so `a` and `b` cannot
/// drift apart — the discipline [`CtorReduction::operand_names`] states one level up.
///
/// WI-20260818-YQB1Y — A MEMBERSHIP OPERAND IS NO LONGER REFUSED, and the reason it was is
/// exactly the reason that went away. `Unit` used to mean both "no columns" and "one
/// `Unit`-typed column", so reading it as "nothing to merge" could emit a merged schema
/// TYPE with one column fewer than the merged column list `join_run` builds from the two
/// VALUES. `Unit` is now zero columns and nothing else, so merging one contributes no
/// fields and the merged type matches the merged row exactly. Joining a membership relation
/// is a FILTER, and it now types as one.
fn concat_operand_fields(
    kb: &KnowledgeBase,
    v: &Value,
    which: &str,
) -> Result<Vec<(Symbol, Value)>, String> {
    schema_fields(kb, v).ok_or_else(|| {
        format!(
            "`Concat` cannot merge operand `{which}`: {}",
            not_a_schema_tail(kb, v)
        )
    })
}

/// WI-714 (proposal 052) — the INTERNAL type-level operation behind the `Concat[A, B]`
/// type constructor: given two relation SCHEMAS, produce the named tuple whose fields are
/// `A`'s followed by `B`'s. Both operands must be schemas ([`schema_fields`] — a named
/// tuple, or `Unit` for a membership relation) with DISJOINT field names; anything else,
/// or a field-name collision, is an error, returned as a message [`reduce_type_ctor`]
/// wraps in a `TypeError`.
///
/// WI-20260818-YQB1Y — BOTH REFUSALS THIS SITE USED TO OWN ARE GONE, because the fact each
/// rested on is gone with the 1-collapse ([`relation_schema_type`]). A ONE-COLUMN operand
/// merges like any other: its schema names its column, so the merged schema names it too.
/// A MEMBERSHIP (`Unit`) operand contributes no fields: `Unit` now means zero columns and
/// only that, so the merged TYPE has exactly the columns the merged VALUE
/// (`join_run`'s `cols1 ++ cols2`) carries. The disjoint-name rule below is the only
/// operand check left, and it is a real one — the merged row is keyed by name.
///
/// `Concat` is a type FORM (the surface a signature writes); this is its reduction — the
/// projection precedent (`ExprCarried` is the form, `project_type_member` its reduction).
/// The result is an ordinary named tuple.
fn concat_named_tuple_types(
    kb: &mut KnowledgeBase,
    a: &Value,
    b: &Value,
    site: &CtorReduceSite,
) -> Result<Value, String> {
    let fa = concat_operand_fields(kb, a, "a")?;
    let fb = concat_operand_fields(kb, b, "b")?;
    let mut merged: Vec<(Symbol, Value)> = Vec::with_capacity(fa.len() + fb.len());
    merged.extend(fa);
    for (name, ty) in fb {
        if merged.iter().any(|(n, _)| *n == name) {
            // WI-731 — NAMES THE OPERATOR, not just the verb. "rename one" was advice with
            // no spelling behind it while `project` was the only thing that renamed, and
            // `project` SELECTS too, so taking it meant listing every column of the operand
            // to move one name. `rename` is the operator that does only this.
            return Err(format!(
                "`concat` operands share the field name `{n}` — a merged schema requires \
                 disjoint field names. Re-key one side first: `r.rename(newName: r.{n})` \
                 keeps every other column as it is (or use `project` if you also want to \
                 drop columns)",
                n = kb.local_name_of(name)
            ));
        }
        merged.push((name, ty));
    }
    // Through [`relation_schema_type`], NOT `named_tuple_value` directly — every producer in
    // this family goes through it, and `Concat` was the one that did not (review-found,
    // MEASURED). Since WI-20260818-YQB1Y a `Unit` operand contributes an EMPTY field list, so
    // `merged` can legitimately be empty — and an empty named tuple is `()`, which is NOT the
    // `Unit` a zero-column relation's schema is and NOT what `materialize_solution` builds for
    // a zero-column row. Measured before the fix: `anyone.join(anyone, …)` over two membership
    // relations typed as `Relation[T = ()]` against a `Unit`-declared consumer, and `negate`
    // over it reported "free column(s): " with an empty list. That is the same
    // type-disagrees-with-its-own-value lie this ticket removed, one arity further down.
    Ok(relation_schema_type(kb, &merged, site.sp))
}

/// WI-714 / WI-727 — does a type mention the sort `sort_sym` as a HEAD ANYWHERE? The
/// reducer's `_`-arm guard so a type-constructor (`Concat` / `Without`) nested in an
/// unsupported carrier is surfaced loudly rather than cloned through un-reduced. Recurses
/// through EVERY carrier — parameterized bindings, arrow parts, named-tuple fields, effect
/// rows — mirroring [`value_contains_projection`].
fn type_mentions_sort(kb: &KnowledgeBase, ty: &Value, sort_sym: Symbol) -> bool {
    match extract_type(kb, ty) {
        TypeExtractor::Parameterized { base, bindings } => {
            base == sort_sym
                || bindings
                    .iter()
                    .any(|(_, v)| type_mentions_sort(kb, v, sort_sym))
        }
        // WI-791: `arity` is a COUNT, not a type — no sort can hide in it.
        TypeExtractor::Arrow {
            param,
            result,
            effects,
            arity: _,
        } => {
            type_mentions_sort(kb, &param, sort_sym)
                || type_mentions_sort(kb, &result, sort_sym)
                || type_mentions_sort(kb, &effects, sort_sym)
        }
        TypeExtractor::NamedTuple(fields) => fields
            .iter()
            .any(|(_, v)| type_mentions_sort(kb, v, sort_sym)),
        TypeExtractor::EffectsRows(e) => type_mentions_sort(kb, &e, sort_sym),
        _ => false,
    }
}

/// WI-714 / WI-727 — the per-op reduction gate: which type constructors a return
/// type writes, in a SINGLE traversal, so the >99% of ops that write none skip
/// [`reduce_type_ctor`]'s descent entirely. Returns one flag per
/// [`TYPE_CTORS`] entry, positionally. A return type may write more than one, and
/// the reduction boundary applies each flagged ctor in turn.
///
/// WI-734 — indexed by the family slice rather than a hardcoded tuple, so adding a ctor is
/// one line in [`TYPE_CTORS`]: previously the family was enumerated independently
/// here and at the reduction boundary, and a new ctor added to one but not the other would
/// silently never reduce instead of failing to compile.
pub(super) fn return_reducible_ctors(kb: &KnowledgeBase, ty: &Value) -> [bool; TYPE_CTORS.len()] {
    let syms = resolved_ctor_family(kb);
    fn walk(
        kb: &KnowledgeBase,
        ty: &Value,
        syms: &[Option<Symbol>; TYPE_CTORS.len()],
        out: &mut [bool; TYPE_CTORS.len()],
    ) {
        match extract_type(kb, ty) {
            TypeExtractor::Parameterized { base, bindings } => {
                for (i, s) in syms.iter().enumerate() {
                    out[i] |= Some(base) == *s;
                }
                for (_, v) in &bindings {
                    walk(kb, v, syms, out);
                }
            }
            TypeExtractor::Arrow {
                param,
                result,
                effects,
                arity: _,
            } => {
                walk(kb, &param, syms, out);
                walk(kb, &result, syms, out);
                walk(kb, &effects, syms, out);
            }
            TypeExtractor::NamedTuple(fields) => {
                for (_, v) in &fields {
                    walk(kb, v, syms, out);
                }
            }
            TypeExtractor::EffectsRows(e) => walk(kb, &e, syms, out),
            _ => {}
        }
    }
    let mut out = [false; TYPE_CTORS.len()];
    walk(kb, ty, &syms, &mut out);
    out
}

/// WI-714 / WI-727 — a type constructor (`Concat[A, B]`, `Without[T, Drop]`,
/// `Membership[T]`) reduced at the return-type normalization boundary by
/// [`reduce_type_ctor`]. Each is a type FORM keyed on its own sort symbol (never a domain
/// op's identity), reading its operands by param name and reducing them.
pub(super) struct TypeCtor {
    /// The constructor sort's qualified name (`anthill.prelude.Concat`).
    pub(super) qn: &'static str,
    /// Display label for diagnostics (`Concat`).
    pub(super) label: &'static str,
    /// The operand names and the reduction over them — paired, so the two cannot disagree
    /// about arity.
    reduction: CtorReduction,
}

/// WI-728 — a constructor's operand names PAIRED with the reduction that consumes them, so
/// an operand list and a reducer of differing arity are unrepresentable. Two arities are in
/// use: BINARY (the schema algebra — merge / drop / keep / select) and UNARY (a type-level
/// PREDICATE: one operand, asserted and returned).
enum CtorReduction {
    /// One operand: `Ctor[T = <a>]` reduces to `reduce(a)`. The family's predicate shape —
    /// the reduction ACCEPTS (yielding the asserted type) or raises a LOUD error, so a
    /// constraint a signature cannot state in a parameter position is stated in the return
    /// type and checked at load.
    Unary {
        /// The operand parameter's name (`"T"`).
        operand: &'static str,
        /// The reduction over the resolved operand → the asserted type (or an error message
        /// the caller wraps in a `TypeError`).
        reduce: fn(&mut KnowledgeBase, &Value, &CtorReduceSite) -> Result<Value, String>,
    },
    /// Two operands: `Ctor[op0 = <a>, op1 = <b>]` reduces to `reduce(a, b)`.
    Binary {
        /// The two operand parameter names, in declaration order (`["A", "B"]`).
        operands: [&'static str; 2],
        /// The reduction over the two resolved operands → the merged type (or an error
        /// message the caller wraps in a `TypeError`).
        reduce: fn(&mut KnowledgeBase, &Value, &Value, &CtorReduceSite) -> Result<Value, String>,
    },
}

impl CtorReduction {
    /// The operand names, IN DECLARATION ORDER — the order the reducer's parameters are in.
    ///
    /// LOAD-BEARING, not cosmetic: [`reduce_type_ctor`] reads the ctor application's
    /// bindings THROUGH this list, so these strings decide WHICH binding each reducer
    /// argument receives, and the list's LENGTH is what makes that read total. Changing a
    /// name here to something prettier, or reordering, silently re-wires the reduction —
    /// a well-formed `Concat[A = …, B = …]` would start reporting "needs `A` and `B`".
    /// It is also what the diagnostic prints, but that is the incidental use.
    fn operand_names(&self) -> &[&'static str] {
        match self {
            CtorReduction::Unary { operand, .. } => std::slice::from_ref(operand),
            CtorReduction::Binary { operands, .. } => operands,
        }
    }
}

/// WI-759 — the SITE a type constructor reduces at. `Concat` / `Without` are purely
/// STRUCTURAL — they merge and shrink named tuples and read nothing but `sp`. `FieldOf` is
/// scope-SENSITIVE: an `internal` field is projectable only from inside its declaring scope
/// (WI-369), so its reduction depends on WHERE it reduces, not only on its operands. Rather
/// than let the one scope-sensitive member reach for an ambient env, the site travels with
/// the reduction for the whole family.
#[derive(Clone, Copy)]
pub(super) struct CtorReduceSite {
    /// The reducing occurrence's source span — the span a constructed type carries.
    pub(super) sp: crate::span::SourceSpan,
    /// The reducing occurrence's diagnostic span, for a nested resolution that raises.
    pub(super) span: Option<Span>,
    /// The scope of the code the reduction runs in ([`TypingEnv::referencing_scope`]),
    /// or `None` at a file's top level, where [`hidden_field_owner`] reads it as the
    /// global scope (WI-977). The lexical scope an `internal` visibility check tests
    /// against, and the one its diagnostic NAMES. A structural reduction ignores it.
    ///
    /// TWO producers, and the second is easy to miss: an OPERATION body supplies the
    /// operation's own scope, and a RULE body supplies the rule's `domain` — a
    /// `FieldOf` reduction is reached from the rule-body dot-dispatch sweep as well as
    /// from an op body, which is why `type_rule_bodies` sets a scope at all. Naming
    /// only the enclosing sort here is what let a rule body's projection go unchecked.
    pub(super) scope: Option<Symbol>,
}

const CONCAT_CTOR: TypeCtor = TypeCtor {
    qn: "anthill.prelude.Concat",
    label: "Concat",
    reduction: CtorReduction::Binary {
        operands: ["A", "B"],
        reduce: concat_named_tuple_types,
    },
};

const WITHOUT_CTOR: TypeCtor = TypeCtor {
    qn: "anthill.prelude.Without",
    label: "Without",
    reduction: CtorReduction::Binary {
        operands: ["T", "Drop"],
        reduce: without_named_tuple_types,
    },
};

/// WI-759 — the type-ARGUMENT channel a `field_access` call carries its selector name on;
/// `FieldOf`'s second operand. Named once so the synthesized call's type argument and the
/// constructor that reads it cannot drift apart.
pub(super) const FIELD_OF_NAME_OPERAND: &str = "Name";

const FIELD_OF_CTOR: TypeCtor = TypeCtor {
    qn: "anthill.prelude.FieldOf",
    label: "FieldOf",
    reduction: CtorReduction::Binary {
        operands: ["T", FIELD_OF_NAME_OPERAND],
        reduce: field_of_type,
    },
};

/// WI-732 — the type-ARGUMENT channel a `project_run` call carries its keep spec on;
/// `Project`'s second operand. Named once, for the reason on [`FIELD_OF_NAME_OPERAND`].
pub(super) const PROJECT_KEEP_OPERAND: &str = "Keep";

const PROJECT_CTOR: TypeCtor = TypeCtor {
    qn: "anthill.prelude.Project",
    label: "Project",
    reduction: CtorReduction::Binary {
        operands: ["T", PROJECT_KEEP_OPERAND],
        reduce: project_schema_type,
    },
};

/// WI-731 — `Rename[T, Map]`: the TYPE-position surface of a schema RENAME. The fourth
/// member of the family — `Concat` merges two schemas, `Without` shrinks one by a drop-set,
/// `Project` restricts one to a keep-set, `Rename` re-keys some of one IN PLACE.
const RENAME_CTOR: TypeCtor = TypeCtor {
    qn: "anthill.prelude.Rename",
    label: "Rename",
    reduction: CtorReduction::Binary {
        operands: ["T", RENAME_MAP_OPERAND],
        reduce: rename_schema_type,
    },
};

/// WI-731 — the type-ARGUMENT channel `rename` carries its rename map on; `Rename`'s second
/// operand. Named once, for the reason on [`FIELD_OF_NAME_OPERAND`].
const RENAME_MAP_OPERAND: &str = "Map";

const MEMBERSHIP_CTOR: TypeCtor = TypeCtor {
    qn: "anthill.prelude.Membership",
    label: "Membership",
    reduction: CtorReduction::Unary {
        operand: "T",
        reduce: membership_schema_type,
    },
};

/// WI-714 / WI-727 — every type constructor, as ONE family. The family's shared rules (the
/// abstract-operand reading below, the operand-name lookup, the reduction boundary) are
/// stated once here rather than per constructor.
///
/// ORDER IS PART OF THE DECLARATION, NOT COSMETIC (WI-728, review-found). The reduction
/// boundary makes ONE pass in this order, and a ctor whose operand is a SIBLING defers on it
/// ([`operand_not_yet_known`] case 2) — so a member placed BEFORE one that can appear inside
/// its operands is the member whose reduction gets skipped, leaving a residual nothing
/// revisits. Adding a member is still one line, but the line's POSITION is a decision:
/// **place it after every member that can appear in its operands.**
///
/// WI-20260818-YQB1Y WEAKENED THIS RULE FROM CORRECTNESS TO COST, and the array order is
/// UNCHANGED because of it. The reduction boundary is now a FIXPOINT rather than one pass, so
/// a member stranded by the order is revisited on the next pass and every nesting reduces
/// whatever the order is. NO TOTAL ORDER COULD HAVE DONE THAT: `Concat[A = Without[…]]` and
/// `Without[T = Concat[…]]` are duals, each wanting the other member first, and both are four
/// lines of ordinary source — reordering to serve one MEASURABLY regressed the other before
/// the fixpoint replaced it. Both are pinned, in both directions, by
/// `yqb1y_concat_and_without_are_inverses_at_arity_one`.
///
/// What the order still decides is HOW MANY PASSES a given nesting costs, so placing a member
/// after those that can appear in its operands is still the cheaper arrangement — just no
/// longer a correctness rule.
///
/// `MEMBERSHIP_CTOR` is LAST for a reason that is sharper for a PREDICATE than for the
/// computing members. A stranded COMPUTING ctor is caught downstream — its unreduced form
/// offers no schema, so any use of the result fails loudly (see [`reduce_type_ctor`]'s
/// CAVEAT). A
/// stranded PREDICATE has no such backstop of its own: on success it reduces to its operand,
/// so the reduced form is an ORDINARY type and an unreduced one is only noticed where
/// something compares against the reduced form. MEASURED, by reordering: a signature that
/// DECLARES the reduced type does catch it — and reports a correct program as wrong, blaming
/// a residual — while a result merely consumed (`negate(r).isEmpty`) compares against nothing
/// and would lose the assertion in silence. Being last is what makes both unreachable;
/// `wi728_..._a_predicate_over_another_ctors_result_still_reduces` is the check, since a
/// comment alone would not survive a reordering.
pub(super) const TYPE_CTORS: [&TypeCtor; 6] = [
    &CONCAT_CTOR,
    &WITHOUT_CTOR,
    &FIELD_OF_CTOR,
    &PROJECT_CTOR,
    &RENAME_CTOR,
    &MEMBERSHIP_CTOR,
];

/// WI-734 — the family's constructor sorts, resolved once. Kept out of the per-operand
/// path deliberately: [`operand_not_yet_known`] runs once per operand per reduction and
/// `try_resolve_symbol` is a string-keyed lookup, which the gated boundary
/// ([`return_reducible_ctors`]) exists specifically to keep off the common path.
/// `None` for a ctor whose sort is not loaded — the same "then it cannot appear" reading
/// [`reduce_type_ctor`] takes at its own resolve.
fn resolved_ctor_family(kb: &KnowledgeBase) -> [Option<Symbol>; TYPE_CTORS.len()] {
    let mut out = [None; TYPE_CTORS.len()];
    for (i, c) in TYPE_CTORS.iter().enumerate() {
        out[i] = kb.try_resolve_symbol(c.qn);
    }
    out
}

/// WI-734 — is a ctor operand NOT YET KNOWN, i.e. is the reduction merely *deferred*
/// rather than *impossible*? Two shapes qualify:
///
/// 1. The operand is a logic VARIABLE (`ViewHead::Var`) — an un-instantiated type
///    parameter (`Var::Rigid`, the skolem a generic op's `[S]` becomes) or an unsolved
///    inference var (`Var::Global`). It may ground at an outer call site.
/// 2. The operand is itself an UNREDUCED ctor — a residual this same rule produced one
///    level down (`Concat[A = Without[..], B = ..]`). Reducing the outer one is equally
///    deferred, so the family stays internally consistent instead of the inner residual
///    tripping the outer reducer's concrete-operand check.
///
/// 3. The operand is an UN-DISCHARGED PROJECTION — `ExprCarried` (`r.T`, WI-376) or
///    `RigidTypeProjection` (`P.Key`, WI-428). A projection is eliminated against the
///    RECEIVER's per-call type, so inside a wrapper whose own parameter is written bare
///    (`negate(r)` in `once(r: Relation) -> …`) there is no receiver type to project yet
///    and the projection survives the elimination pass. That is the same "may ground at an
///    outer call site" situation as case 1, and WI-728 is where it became REACHABLE:
///    `Membership`'s single operand is a bare projection, whereas every binary member has a
///    second operand (`Keep`, `Drop`, `Name`) that is usually still a variable and so
///    deferred the whole ctor by case 1 before the projection was ever inspected.
///    MEASURED: without this arm, `operation once(r: Relation) -> Relation = negate(r)` —
///    a program that loads clean before WI-728, and whose parameter is spelled exactly as
///    `negate`'s own — is refused with the fabricated "one free column of type `r.T`".
///
/// Deliberately a SHALLOW head test: a variable nested *inside* an otherwise concrete
/// operand (a named-tuple field type) does not block the merge, which copies field types
/// verbatim. And deliberately NOT keyed on `TypeExtractor::Error` — that is a total-ness
/// catch-all covering genuinely malformed types too, so keying on it would silently
/// convert real errors into residuals.
fn operand_not_yet_known(
    kb: &KnowledgeBase,
    v: &Value,
    family: &[Option<Symbol>; TYPE_CTORS.len()],
) -> bool {
    if matches!(v.head(kb), ViewHead::Var(_)) {
        return true;
    }
    match extract_type(kb, v) {
        TypeExtractor::Parameterized { base, .. } => family.contains(&Some(base)),
        TypeExtractor::ExprCarried { .. } | TypeExtractor::RigidTypeProjection { .. } => true,
        _ => false,
    }
}

/// WI-728 — one already-reduced binding of a ctor application, by operand NAME. Short
/// (local) name, like every other type-parameter lookup: the binding symbols carry the
/// declaring sort's scope, and the family's operand names are written as they appear in
/// `sort.anthill`.
///
/// DELIBERATELY NOT ENROLLED in [`binding_for_param`]'s ledger, which is the repo's one
/// rule for looking a binding up BY PARAMETER SYMBOL. This asks a different question: it
/// starts from a `&'static str` written in Rust, and the operand symbols are scoped to the
/// declaring sort, so interning the bare name would not produce a symbol that matches
/// (`define_qualified_only`). Extracted from the open-coded comparison the reducer already
/// did rather than introduced here — the note exists so a later change to the binding-key
/// rule knows this site reads names, not keys, and is unaffected by it.
fn ctor_operand(kb: &KnowledgeBase, bindings: &[(Symbol, Value)], name: &str) -> Option<Value> {
    bindings
        .iter()
        .find(|(p, _)| kb.local_name_of(*p) == name)
        .map(|(_, v)| v.clone())
}

/// WI-714 / WI-727 — evaluate a type constructor (`cfg`) wherever it appears in a
/// type: `Ctor[op0 = <a>, …]` reduces to `cfg.reduction` applied to its operands. The INTERNAL type-level
/// operation behind the `Concat` / `Without` FORMS — keyed on the constructor's sort symbol
/// and evaluated at the SAME return-type normalization boundary the `s.T` projection is, so
/// ANY signature may write it; never keyed on a domain operation's identity. Recurses through
/// parameterized BINDINGS (where a schema-producing ctor sits — the `T` binding of
/// `Relation[T = Ctor[..]]`).
///
/// WI-734 — the family's ABSTRACT-OPERAND rule, settled once for `Concat` / `Without` and
/// any future member: an operand that is NOT YET KNOWN ([`operand_not_yet_known`]) leaves
/// the ctor SYMBOLIC (returned unreduced) so it can reduce later, once the operand grounds;
/// an operand that IS known but cannot be merged (a name collision, or a shape that is no
/// relation schema at all) stays a LOUD error. "Cannot reduce yet" and "cannot reduce ever"
/// are different
/// answers and no longer share the concrete-malformation diagnostic.
///
/// CONFLUENCE: a residual can only exist over an un-instantiated operand, so a fully
/// CONCRETE type is always fully reduced — there are never two comparable forms of one
/// concrete type.
///
/// THE EXCEPTION THAT USED TO EXIST HERE IS CLOSED (WI-20260818-YQB1Y). A SIBLING family
/// member reads as "not yet known", so an outer ctor defers on it; with ONE pass in array
/// order, a sibling sitting LATER reduced afterwards and left the outer ctor unreduced over a
/// now-concrete operand nothing revisited — so a fully concrete type COULD carry a residual,
/// across members, in whichever nesting direction the order did not favour (WI-728,
/// review-found). The boundary is now a FIXPOINT, which revisits until nothing changes, so
/// both nesting directions reduce and no order has to be chosen between them.
///
/// CAVEAT: a residual reduces later only where the reduction gate fires, and
/// [`return_reducible_ctors`] reads an op's DECLARED return type — so a generic wrapper
/// must PROPAGATE the ctor in its own signature (as `join` / `fix` do); widening to a bare
/// `Relation` lets the residual escape unreduced. That escape is SAFE, not a silent wrong
/// schema: A/B-verified, a column use on an escaped residual — dropped or kept alike —
/// fails LOUDLY at dot dispatch (`<unresolved receiver>.<col>`), because an unreduced ctor
/// offers no named-tuple schema to resolve against. The cost of widening is that the
/// result is unusable columnwise, never that it answers wrongly.
///
/// THAT SAFETY ARGUMENT IS ABOUT A SCHEMA-COMPUTING MEMBER, and does NOT transfer to a
/// PREDICATE one (WI-728). It rests on the escaped residual being unusable — but a
/// predicate reduces to its own operand on success, so its escaped result is a perfectly
/// usable type and what is lost is the ASSERTION, silently. `Relation.negate` happens to
/// keep a runtime guard that re-asks the question; a predicate written on any other sort
/// has nothing behind it. So for a predicate: propagate it, or keep a runtime check, and
/// do not read this paragraph as saying the escape costs only convenience.
///
/// A ctor nested in a non-parameterized-argument carrier (a named-tuple field, arrow,
/// effect row) remains a LOUD error — never a silent pass-through. A carrier that mentions
/// no `cfg` ctor returns unchanged.
///
/// AN UNRESOLVABLE CTOR SORT returns the type unchanged. Sound for the same reason across
/// the family, predicate included: the qualified name is the one a SIGNATURE writes, and a
/// signature naming a sort that does not resolve is itself a load error — so there is no
/// reachable state where a `Membership[..]` exists to assert and its sort does not. This is
/// a totality arm, not a fallback, and the reasoning is recorded because for a predicate the
/// failure mode of getting it wrong is an assertion that silently stops firing.
pub(super) fn reduce_type_ctor(
    kb: &mut KnowledgeBase,
    ty: &Value,
    ctx: &TypeErrorContext,
    site: &CtorReduceSite,
    cfg: &TypeCtor,
) -> Result<Value, TypeError> {
    let (sp, span) = (site.sp, site.span);
    let ctor_sym = match kb.try_resolve_symbol(cfg.qn) {
        Some(s) => s,
        None => return Ok(ty.clone()),
    };
    match extract_type(kb, ty) {
        TypeExtractor::Parameterized { base, bindings } => {
            // Reduce each binding first — the schema-producing ctor is nested (the `T`
            // binding of `Relation[T = Ctor[..]]`), so descend before evaluating.
            let mut reduced: Vec<(Symbol, Value)> = Vec::with_capacity(bindings.len());
            for (p, v) in bindings {
                reduced.push((p, reduce_type_ctor(kb, &v, ctx, site, cfg)?));
            }
            if base == ctor_sym {
                // `Ctor[op0 = .., ..]` — read the operands by param name and reduce. Any
                // operand missing is the same "needs its operands" error at every arity.
                let operands: Option<SmallVec<[Value; 2]>> = cfg
                    .reduction
                    .operand_names()
                    .iter()
                    .map(|name| ctor_operand(kb, &reduced, name))
                    .collect();
                let Some(operands) = operands else {
                    return Err(projection_type_error(
                        ctx,
                        span,
                        &format!(
                            "`{}` needs {}",
                            cfg.label,
                            cfg.reduction
                                .operand_names()
                                .iter()
                                .map(|n| format!("`{n}`"))
                                .collect::<Vec<_>>()
                                .join(" and ")
                        ),
                    ));
                };
                // WI-734 — an operand that is NOT YET KNOWN leaves the ctor SYMBOLIC
                // rather than raising: reduction is deferred to the boundary where the
                // operand grounds. Distinguishing this from a CONCRETE operand the
                // reducer genuinely cannot merge is the whole point — handing an
                // unknown to `cfg.reduce` made it report the concrete-malformation
                // message ("is not a relation schema"), blaming a shape the author never
                // wrote for what is really an un-instantiated type parameter.
                let family = resolved_ctor_family(kb);
                if operands
                    .iter()
                    .any(|o| operand_not_yet_known(kb, o, &family))
                {
                    let base_id = kb.make_sort_ref(base);
                    return Ok(parameterized_value(kb, base_id, &reduced, sp, None));
                }
                // `operands` was collected FROM `operand_names()`, and [`CtorReduction`]
                // pairs those names with the reducer that consumes them — so its length is
                // this variant's arity and the indexing below cannot be out of range.
                match &cfg.reduction {
                    CtorReduction::Unary { reduce, .. } => reduce(kb, &operands[0], site),
                    CtorReduction::Binary { reduce, .. } => {
                        reduce(kb, &operands[0], &operands[1], site)
                    }
                }
                .map_err(|msg| projection_type_error(ctx, span, &msg))
            } else {
                let base_id = kb.make_sort_ref(base);
                Ok(parameterized_value(kb, base_id, &reduced, sp, None))
            }
        }
        // A ctor nested in a NON-parameterized-argument carrier is out of the first
        // increment's scope — surface it LOUDLY rather than clone an un-reduced ctor
        // through. A carrier that mentions no ctor is returned unchanged.
        _ => {
            if type_mentions_sort(kb, ty, ctor_sym) {
                Err(projection_type_error(
                    ctx,
                    span,
                    &format!(
                        "`{0}` is only supported as a direct type argument (e.g. `Relation[T = \
                         {0}[..]]`); a `{0}` nested in a tuple field, arrow, or effect row is \
                         not yet supported",
                        cfg.label
                    ),
                ))
            } else {
                Ok(ty.clone())
            }
        }
    }
}

/// WI-727 (proposal 056) — the INTERNAL type-level operation behind the `Without[T, Drop]`
/// type constructor, the DUAL of [`concat_named_tuple_types`]: given a named-tuple type `t`
/// and a record type `drop` naming the columns to remove, produce `t` with every field
/// named in `drop` dropped. The residual is typed exactly as a relation schema is (`Unit`
/// for no kept column, else the named tuple) — `Without` can shrink to 0/1 fields, which
/// `Concat` (only grows) never does. BOTH checks the capture is deliberately unconstrained
/// about live HERE (proposal 056 §2.2): a `drop` field naming no `t` field, or one whose
/// (captured) type mismatches its column, is an error the caller wraps in a `TypeError`.
/// `drop` is the record the variadic capture (`...args: R`) produced, so an EMPTY `drop`
/// (an empty capture, `r.fix()`) drops nothing — the identity. `Without` is a type FORM (the
/// surface a signature writes); this is its reduction (the `Concat` / projection precedent).
fn without_named_tuple_types(
    kb: &mut KnowledgeBase,
    t: &Value,
    drop: &Value,
    site: &CtorReduceSite,
) -> Result<Value, String> {
    // The fields to drop — `drop` is the captured record type (a named tuple). An empty
    // capture (an empty named tuple, or `Unit`) drops nothing → the identity (OQ #6).
    let drop_fields = match extract_type(kb, drop) {
        TypeExtractor::NamedTuple(f) => f,
        // A bare `Unit` drop (a generic `Without[T, Unit]`) drops nothing → identity. Both
        // sides must be `Some` and equal — a `.zip` guards against `None == None` (a headless
        // `drop` when `Unit` is also unresolvable) silently selecting this arm.
        _ if sort_functor_of_view(kb, drop)
            .zip(kb.try_resolve_symbol("anthill.prelude.Unit"))
            .is_some_and(|(f, u)| f == u) =>
        {
            Vec::new()
        }
        _ => {
            return Err(
                "`Without` drop operand must be a record (named tuple) of the columns \
                        to drop — the record a variadic capture (`...args: R`) produces"
                    .to_string(),
            )
        }
    };
    if drop_fields.is_empty() {
        return Ok(t.clone());
    }
    // The base schema's columns, to match each dropped field against BY NAME. WI-1128:
    // read by the shared [`schema_fields`], phrased HERE, because what the author should do
    // next about a DROP differs from what they should do about a merge.
    //
    // WI-20260818-YQB1Y — a ONE-COLUMN base is no longer a special case: its schema names
    // its column, so `fix` can drop it like any other. A MEMBERSHIP base yields the empty
    // field list, and each dropped field then fails the name check below with a message
    // naming the field the author actually wrote — which is more use than a shape claim.
    let t_fields = schema_fields(kb, t).ok_or_else(|| {
        format!(
            "`Without` cannot drop from operand `T`: {}",
            not_a_schema_tail(kb, t)
        )
    })?;
    // Membership + type checks — the LOAD errors that give the capture its meaning (§2.2).
    // Each dropped field must NAME a column of the base schema (recording the name to drop),
    // and its captured type must MATCH that column (a `fix(x: "s")` over an `Int64` column
    // `x` is rejected here).
    let mut dropped: Vec<Symbol> = Vec::with_capacity(drop_fields.len());
    for (dname, dty) in &drop_fields {
        match t_fields.iter().find(|(tn, _)| *tn == *dname) {
            None => {
                return Err(format!(
                    "`Without` drops the field `{}`, which is not a column of the base schema \
                     (a captured argument names no column to restrict)",
                    kb.local_name_of(*dname)
                ))
            }
            Some((_, tty)) => {
                let mut probe = Substitution::new();
                if !types_compatible(kb, &mut probe, dty, tty) {
                    return Err(format!(
                        "`Without` drops the field `{}` with a value whose type does not match \
                         its column",
                        kb.local_name_of(*dname)
                    ));
                }
            }
        }
        dropped.push(*dname);
    }
    // Keep every base field NOT dropped, in the base's order; type the residual as any
    // relation schema is typed (0 → `Unit`, else the named tuple). WI-20260818-YQB1Y: at one
    // remaining column that is `(a: A)`, so `Concat` and `Without` are now INVERSES at every
    // arity — the §6.8 limit the collapse imposed ("nothing downstream can supply the lost
    // `a`") is retired rather than worked around.
    let kept: Vec<(Symbol, Value)> = t_fields
        .into_iter()
        .filter(|(tn, _)| !dropped.contains(tn))
        .collect();
    Ok(relation_schema_type(kb, &kept, site.sp))
}

/// WI-728 (proposal 052) — the INTERNAL type-level operation behind the `Membership[T]`
/// type constructor: the family's first PREDICATE member. Where `Concat` / `Without` /
/// `Project` COMPUTE a schema, this one only ASSERTS a schema is CLOSED — `Unit`, the schema
/// of zero columns — and returns it. A schema that still has columns is a LOAD error.
///
/// It exists because a signature cannot state the constraint in its PARAMETER position.
/// `negate(r: Relation[T = Unit])` leaves the parameter non-ground in `E` (a `Relation`
/// threads an effect row too), and the arg-vs-param check is gated on groundness
/// ([`validate_arg_against_param`]) — so the constraint was silently unchecked, and pinning
/// `E` to close that gap over-narrows the row every caller must then match. Stating it in
/// the RETURN type instead puts it where the family already reduces, after the projection
/// `r.T` has been discharged against the actual argument.
///
/// WHAT THE MESSAGE NAMES. A relation schema spells its column names at EVERY arity since
/// the 1-collapse was dropped (WI-20260818-YQB1Y), so an open schema is always a named tuple
/// and the message always names the free columns — including the one-column case, which used
/// to have collapsed to its element type and could only be described by that type.
///
/// A SHAPE THIS CANNOT NAME GETS A SHAPE CLAIM, not an invented column. `extract_type` is
/// TOTAL — `TypeExtractor::Error` is its catch-all for a genuinely malformed type, and an
/// arrow / effect-row / denoted operand is well-formed but is no relation schema at all.
/// Reporting a free column for any of those states a fact about the author's code that is
/// not true and sends them to close columns that do not exist. Only a NAMED TUPLE takes the
/// column reading; everything else says what it is. `without_named_tuple_types` phrases its
/// catch-all the same way, and this is the correction that brings the two into line
/// (review-found, WI-728).
///
/// WI-728'S RECORDED LIMIT IS RETIRED (WI-20260818-YQB1Y). A one-column relation whose
/// column type IS `Unit` used to collapse to the same `Unit` a zero-column relation does, so
/// this check accepted it and only the drain refused it. Without the collapse that relation's
/// schema is `(u: Unit)` — a named tuple with one free column — so it is refused HERE, at
/// load, by the ordinary arm above. `wi728_a_unit_typed_column_is_distinguishable_from_no_columns`
/// drives the retirement: it asserts the load error, and fails on a back-out (the pre-change
/// tree loads that program clean).
///
/// The runtime guard in `Relation.negate` is still NOT redundant, for its other two reasons:
/// a schema that was never statically known (an abstract `S` leaves the assertion symbolic,
/// WI-734) and a relation built through reflect rather than from surface code.
fn membership_schema_type(
    kb: &mut KnowledgeBase,
    t: &Value,
    _site: &CtorReduceSite,
) -> Result<Value, String> {
    let extracted = extract_type(kb, t);
    // `Unit` — the 0-column schema — is the one accepted operand; return it unchanged so
    // the enclosing `Relation[T = Membership[T = r.T]]` reduces to `Relation[T = Unit]`.
    // A BARE sort ref, which is exactly what `relation_schema_type` mints for zero columns:
    // a `Unit[..]` APPLICATION is a different type and must not read as closed. And if `Unit`
    // itself does not resolve there is no verdict to give — DEFER (return the operand
    // unreduced) rather than let a failed lookup turn the accepted type into the offender.
    let unit = kb.try_resolve_symbol("anthill.prelude.Unit");
    let Some(unit) = unit else {
        return Ok(t.clone());
    };
    if matches!(extracted, TypeExtractor::SortRef(s) if s == unit) {
        return Ok(t.clone());
    }
    let offending = match extracted {
        // `short_name_of`, as every other named-tuple field LIST in this module renders one
        // (`no_such_member_message`, the projection diagnostics): a component symbol can
        // carry its declaring scope, and a column called `test.ns.name` in a message about
        // the author's columns is noise they cannot act on.
        //
        // WI-20260818-YQB1Y — this arm now covers EVERY open schema, arity one included:
        // a one-column relation is `(age: Int64)`, so the message names `age` where it used
        // to have to fall back to naming the column's TYPE. There is no longer a shape a
        // free column can hide in.
        TypeExtractor::NamedTuple(fields) => format!(
            "free column(s): {}",
            fields
                .iter()
                .map(|(n, _)| short_name_of(kb.local_name_of(*n)).to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
        // Anything else is not a relation schema at all; say so, and claim no columns.
        _ => format!(
            "the type `{}`, which is not a relation schema",
            type_display_name_value(kb, t)
        ),
    };
    Err(format!(
        "`Membership` requires a CLOSED schema (`Unit` — a relation whose columns are all \
         bound), but this one has {offending}; close the columns first — bind them by \
         applying the relation, or project ALL of them away in one step (a projection that \
         leaves any column behind still fails here)"
    ))
}

/// WI-759 — the member a field projection `x.f` selects: the projected TYPE plus the
/// constructor that DECLARES it. The result of [`resolve_projected_member`], which is the
/// ONE resolution both directions of the projection share.
pub(super) struct ProjectedMember {
    /// The projected member's type.
    pub(super) ty: Value,
    /// EVERY `(declaring constructor, field symbol)` that declares this member — the pairs
    /// WI-369's `internal` visibility check needs. EMPTY for a receiver whose members have
    /// no declaring constructor: a named tuple's components carry no `internal` marker, so
    /// there is nothing to hide. That is the CORRECT answer there, not a missing arm.
    ///
    /// ALL of them, not the first: `field_constructors_of_sort` returns HashMap iteration
    /// order, so a multi-variant sort declaring one field name across variants — one of them
    /// `internal` — would otherwise get a RUN-DEPENDENT visibility verdict. The codebase
    /// settles this the same way wherever it walks those constructors (load.rs's
    /// continued-walk field resolve, and `resolve_field_type`, whose returned TYPE is
    /// already order-independent): collect from every constructor, never break on the first.
    owners: Vec<(Symbol, Symbol)>,
}

/// WI-759 — why [`resolve_projected_member`] did not produce a member, as the two answers
/// its callers must treat DIFFERENTLY.
pub(super) enum MemberMiss {
    /// The receiver has no member of that name — or has no members at all. NOT an error by
    /// itself: the forward dot dispatch reads this as "not a field projection" and continues
    /// to its remaining modes (a relation column, then `DotDispatchNoMatch`). Carries no
    /// message precisely because the common path DISCARDS it — every relation column
    /// projection `r.col` probes and misses here, and building a diagnostic string for each
    /// one would be pure waste. The reducer, which has no next mode to try, formats its own
    /// via [`no_such_member_message`].
    NoSuchMember,
    /// The member EXISTS but its type could not be resolved — a genuine diagnostic that both
    /// directions must surface. Kept distinct from `NoSuchMember` so it is never swallowed
    /// into a fall-through: reporting "no such member" for a field that plainly exists points
    /// the user at the wrong thing.
    Unresolvable(String),
}

/// WI-759 — the diagnostic for a member name that names nothing on `recv_ty`, built ONLY
/// where it is actually reported (the reduction). Names what the receiver does offer, so a
/// typo is a one-line fix rather than a hunt.
fn no_such_member_message(kb: &KnowledgeBase, recv_ty: &Value, field_name: &str) -> String {
    match extract_type(kb, recv_ty) {
        TypeExtractor::NamedTuple(fields) => format!(
            "`{field_name}` is not a component of the tuple ({})",
            fields
                .iter()
                .map(|(f, _)| short_name_of(kb.local_name_of(*f)).to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
        _ => match sort_functor_of_view(kb, recv_ty) {
            Some(s) => format!(
                "`{}` has no field `{field_name}`",
                short_name_of(kb.qualified_name_of(s))
            ),
            None => format!(
                "cannot project the field `{field_name}` from a receiver with no concrete sort"
            ),
        },
    }
}

/// WI-759 — the `internal` constructor hiding `m`'s field from `scope`, if any (WI-369).
/// Shared by both directions so they cannot disagree about visibility.
///
/// The VERDICT is order-independent — it asks whether ANY declaring constructor is hidden,
/// over the full `owners` list rather than one HashMap-ordered pick. (Which hidden
/// constructor gets NAMED when several are, is a diagnostic detail.) Conservative by
/// construction: a field reachable through an `internal` variant stays encapsulated even
/// when a public sibling variant declares the same name.
/// WI-977 — answers the REFERENCING SCOPE alongside the owner, because the caller's
/// diagnostic has to name it and this is the only place it is known to exist. It used
/// to answer only the owner, and the caller filled the scope slot with the literal
/// string `"another scope"` — a fabricated name in a user-visible diagnostic, which
/// rendered as `cannot be referenced from scope 'another scope'`.
///
/// THE `None` IS RESOLVED HERE, ONCE, AND IT IS THE GLOBAL SCOPE — not "no scope, so
/// skip the check". `scope` in is [`TypingEnv::referencing_scope`], absent for a
/// projection written at a file's top level;
/// [`internal_field_hidden_from`] used to answer `false` for
/// that and say so ("there is no lexical scope to test against, so enforcement is
/// skipped (permissive)"). MEASURED against that arm: a top-level
/// `operation topPeek(b: Box) -> Int64 = b.v` reading an `internal` constructor's
/// field of another sort loaded CLEAN, while the identical body inside any `sort` or
/// `namespace` was refused — so WI-369 encapsulation was unenforced for exactly the
/// code with no scope to be inside. §8.6 makes `internal` "hidden from outside the
/// declaring scope", and top-level code is outside it; the global scope is the scope
/// such code is written in, so asking the question against it is both the honest
/// reading and the one that closes the hole. A top-level `internal` declaration is
/// unaffected — its declaring scope IS the global one, so it stays visible there.
pub(super) fn hidden_field_owner(
    kb: &mut KnowledgeBase,
    m: &ProjectedMember,
    scope: Option<Symbol>,
) -> Option<(Symbol, Symbol, ScopeId)> {
    let from = match scope {
        Some(s) => kb.symbols.scope_id(s),
        None => kb.global_scope(),
    };
    m.owners
        .iter()
        .find(|(ctor, _)| internal_field_hidden_from(kb, from, *ctor))
        .map(|(ctor, fsym)| (*ctor, *fsym, from))
}

/// WI-759 — resolve `recv_ty`'s member named `field_name`: the projection lookup, stated
/// ONCE. Both directions of the `x.f` rewrite go through it — the FORWARD dot dispatch (to
/// decide that `f` names a member at all, and to reject an `internal` one at the dot's own
/// span) and the REVERSE re-type ([`field_of_type`], reducing the `FieldOf` the rewritten
/// node's declared return writes). That sharing is the point: the two used to be separate
/// traversals and had already drifted — the forward one grew a named-tuple arm (WI-638) the
/// reverse never got (WI-758), so a rewritten named-tuple projection failed on re-type
/// against `field_access`'s own reflect signature.
///
/// TWO receivers declare members statically:
///  1. a NAMED TUPLE — components matched by SHORT name, as the forward dot dispatch does,
///     and forced here anyway: the incoming `field_name` is a NAME (a source-level `x.f`, or
///     a `FieldOf` denoted), so there is no symbol to compare identities with.
///  2. an ENTITY / sort receiver — the field's declared type with the receiver's
///     type-arguments substituted, plus EVERY constructor that declares it.
///
/// A NAMED TUPLE IS THEREFORE MATCHED TWO WAYS, BY DESIGN — by SHORT NAME here, and by
/// SYMBOL IDENTITY in every relation over two named tuples ([`align_named_tuple_slots`],
/// and since WI-800 the tuple-literal expected-type threading with them). Which one is
/// available is decided by the operands, not by taste: a relation has two type-level tuples
/// whose symbols come from one producer (the reasoning `without_named_tuple_types` records),
/// and a READER holding a bare name has nothing to compare identities with. The two CAN
/// disagree — see WI-805, where a duplicate-labelled tuple has the relation typing one
/// component and this lookup reading another.
///
/// A `Term` receiver is deliberately NOT handled here. Its "fields" are a runtime term's
/// named arguments rather than a declared schema, so ANY name projects — an answer that is
/// right for the REDUCTION (a written `field_access(t, "x")` is genuine reflect
/// metaprogramming) and wrong for the forward DOT DISPATCH, where it would make `t.typo`
/// type-check silently instead of raising `DotDispatchNoMatch`. That case therefore lives in
/// [`field_of_type`] alone, keeping this lookup about members a receiver actually DECLARES.
pub(super) fn resolve_projected_member(
    kb: &mut KnowledgeBase,
    recv_ty: &Value,
    field_name: &str,
    span: Option<Span>,
) -> Result<ProjectedMember, MemberMiss> {
    if let TypeExtractor::NamedTuple(fields) = extract_type(kb, recv_ty) {
        return fields
            .iter()
            .find(|(f, _)| short_name_of(kb.local_name_of(*f)) == field_name)
            .map(|(_, t)| ProjectedMember {
                ty: t.clone(),
                owners: Vec::new(),
            })
            .ok_or(MemberMiss::NoSuchMember);
    }
    let recv_sort = sort_functor_of_view(kb, recv_ty).ok_or(MemberMiss::NoSuchMember)?;
    // EVERY declaring constructor — see `ProjectedMember::owners` for why not the first.
    let owners: Vec<(Symbol, Symbol)> = kb
        .field_constructors_of_sort(recv_sort)
        .into_iter()
        .filter_map(|c| {
            kb.entity_field_types(c).and_then(|fields| {
                fields
                    .iter()
                    .find(|(f, _)| short_name_of(kb.local_name_of(*f)) == field_name)
                    .map(|(f, _)| (c, *f))
            })
        })
        .collect();
    // `resolve_field_type` matches the field by SYMBOL, and a given field name is the same
    // symbol across a sort's constructors — so the variants differ in their `owners` entry,
    // never in the field symbol itself.
    let field_sym = owners.first().ok_or(MemberMiss::NoSuchMember)?.1;
    let ctx = TypeErrorContext::EntityField {
        entity: recv_sort,
        field: field_sym,
    };
    // The field's DECLARED type with the receiver's type-arguments substituted — the
    // `Option[T = String].value : String` step. Its own failure (an abstract field type with
    // no interface to read, a divergent multi-variant type) is already a projection
    // diagnostic; carry that message rather than restate it, and as `Unresolvable` rather
    // than `NoSuchMember` so no caller can turn it into a silent fall-through.
    let (ty, _) = resolve_field_type(kb, recv_ty, field_sym, &ctx, span)
        .map_err(|e| MemberMiss::Unresolvable(type_error_detail(&e)))?;
    Ok(ProjectedMember { ty, owners })
}

/// WI-759 — the INTERNAL type-level operation behind the `FieldOf[T, Name]` type
/// constructor: the type of `T`'s member named `Name`. It is what makes
/// `anthill.reflect.field_access`'s DECLARED signature self-correcting — re-typing a stored
/// `field_access(recv, "f")` node re-derives the field's type from the signature instead of
/// from a typer hatch keyed on `field_access`'s own identity.
///
/// `Name` is a compile-time NAME in TYPE position, i.e. a `denoted` value-in-type carrying a
/// string. There are no singleton types — a field name in VALUE position types as plain
/// `String` and loses the name — so the denoted type-argument channel is the only route that
/// carries it, and this is its first string-valued use.
///
/// An operand that is not yet known never reaches here: the family's abstract-operand rule
/// (WI-734) leaves the constructor symbolic instead, which is what lets `FieldOf` sit in a
/// signature checked before the receiver's type is known — a rule body's
/// `field_access(?t, f)` has no static receiver at all.
fn field_of_type(
    kb: &mut KnowledgeBase,
    t: &Value,
    name: &Value,
    site: &CtorReduceSite,
) -> Result<Value, String> {
    let field_name = denoted_name(kb, name).ok_or_else(|| {
        "`FieldOf` name operand must be a field NAME in type position (a string literal, or a \
         type parameter bound to one through the type-argument channel)"
            .to_string()
    })?;
    // The GENUINE reflect metaprogramming call: a `Term`'s fields are a runtime term's named
    // arguments, not a declared schema, so any name projects and the result is a `Term`.
    // Checked HERE rather than in `resolve_projected_member` on purpose — see that
    // function's docs: shared with the forward dot dispatch it would make `t.typo`
    // type-check silently, and `Term` is an opaque `sort Term = ?` that would otherwise
    // resolve nothing.
    if sort_functor_of_view(kb, t)
        .zip(kb.try_resolve_symbol("anthill.reflect.Term"))
        .is_some_and(|(recv, term)| recv == term)
    {
        return Ok(t.clone());
    }
    let member = match resolve_projected_member(kb, t, &field_name, site.span) {
        Ok(m) => m,
        Err(MemberMiss::Unresolvable(msg)) => return Err(msg),
        Err(MemberMiss::NoSuchMember) => return Err(no_such_member_message(kb, t, &field_name)),
    };
    // WI-369: projecting a field whose owning constructor is `internal`, from outside its
    // declaring scope, aliases encapsulated state. The check rides the SAME resolution that
    // produced the type — one traversal, and no way for the two to disagree about which
    // constructor owns the field. A source-level `x.f` is rejected earlier, at the dot's own
    // span with the precise diagnostic; this closes the hand-written desugared form, which
    // never passes through dot dispatch.
    if let Some((ctor, field, from_scope)) = hidden_field_owner(kb, &member, site.scope) {
        // WI-977 — names the referencing scope, as the two dot-dispatch renderings of
        // this same refusal do. "outside its declaring scope" restated the rule the
        // author had just hit; the scope they wrote it in is what locates the line.
        let from = kb.scope_display_name(from_scope).to_string();
        return Err(format!(
            "field `{}` is declared by the `internal` constructor `{}` and cannot be \
             projected from scope '{}'",
            short_name_of(kb.qualified_name_of(field)),
            short_name_of(kb.qualified_name_of(ctor)),
            from,
        ));
    }
    Ok(member.ty)
}

/// WI-759 — the human-readable detail of a nested `TypeError` raised while resolving a
/// projected member, for re-reporting through the constructor family's `String` error
/// channel. [`resolve_field_type`] fails as a [`projection_type_error`] — a
/// `TypeError::Other` whose `actual` IS the message — so that message is carried through
/// verbatim; any other shape is re-reported by its debug form rather than swallowed.
fn type_error_detail(e: &TypeError) -> String {
    match e {
        TypeError::Other { actual, .. } => actual.clone(),
        other => format!("{other:?}"),
    }
}
