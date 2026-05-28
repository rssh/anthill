/// Typing pass — type-check expressions following typing_pass_spec.anthill.
///
/// Rust implementation of TypingEnv, TypeResult, TypeError, and type_check.
/// Types are TermId values in the KB (types are terms in anthill).
/// Effects are tracked as List[Type] alongside the value type.

use std::collections::HashMap;
use std::rc::Rc;

use smallvec::SmallVec;

use super::term::{Term, TermId, Literal, Var, VarId};
use super::node_occurrence::{
    for_each_child, for_each_pattern_child, materialize_from_handle,
    Expr, MatchBranch, NodeKind, NodeOccurrence,
};
use super::{KnowledgeBase, SortKind};
use crate::intern::Symbol;
use crate::span::Span;

// ── TypeError ──────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum TypeError {
    /// Canonical type mismatch from `assert_compatible`. `context` is where
    /// in the program the mismatch was detected so the user-facing message
    /// can name the field/operation rather than just "type mismatch".
    TypeMismatch {
        span: Option<Span>,
        context: TypeErrorContext,
        expected: TermId,
        actual: TermId,
    },
    UnknownField {
        span: Option<Span>,
        entity_name: Symbol,
        field: Symbol,
    },
    NoParentSort {
        name: Symbol,
    },
    UnresolvedName {
        span: Option<Span>,
        name: Symbol,
    },
    /// Constructor symbol has no declared entity-field-types entry.
    /// Reported from `check_constructor_iter` when `entity_field_types`
    /// returns None for what looked like a constructor invocation.
    NoConstructor {
        span: Option<Span>,
        name: Symbol,
    },
    /// `check_apply_iter` was handed a functor symbol that is neither
    /// a known operation, a constructor, nor a var-bound arrow type.
    UnknownApplyFunctor {
        span: Option<Span>,
        name: Symbol,
    },
    /// Spec-op dispatch found no impl whose per-call bindings match the
    /// inferred type arguments. `op` is the qualified spec-op symbol
    /// (e.g. `anthill.prelude.Numeric.add`).
    DispatchNoMatch {
        span: Option<Span>,
        op: Symbol,
    },
    /// Spec-op dispatch found multiple impls — the coherence rule (C)
    /// rejects ambiguous resolution.
    DispatchAmbiguous {
        span: Option<Span>,
        op: Symbol,
    },
    /// `op[bindings](args)` named a binding key that doesn't correspond
    /// to any of the op's declared type-parameters. Replaces the
    /// WI-269 Phase D silent-drop site in `seed_op_type_args`.
    NoSuchTypeParam {
        span: Option<Span>,
        op: Symbol,
        name: Symbol,
    },
    /// A call's type-param could not be pinned from explicit bindings,
    /// from caller-side expected type, or from argument inference. Names
    /// the unconstrained parameter so the user can fix the call by
    /// writing `op[T = …](args)`.
    UnconstrainedTypeParam {
        span: Option<Span>,
        op: Symbol,
        type_param: Symbol,
    },
    /// Bottom or other post-elaboration expression seen by the surface
    /// typer — emitted only by `req_insertion`, never user-written.
    BottomExpr {
        span: Option<Span>,
    },
    /// Aggregation node — collects multiple sibling failures
    /// (e.g. a list literal with two ill-typed elements).
    Multiple {
        errors: Vec<TypeError>,
    },
    /// Catchall for auxiliary typing-pass checks (effect declarations,
    /// match exhaustiveness, HO pattern fragment, rule var consistency).
    /// Promote to a dedicated variant when a consumer discriminates on it.
    Other {
        span: Option<Span>,
        context: TypeErrorContext,
        expected: String,
        actual: String,
    },
}

#[derive(Clone, Copy, Debug)]
pub enum RuleField {
    Head,
    Body,
    Whole,
}

impl RuleField {
    fn name(self) -> &'static str {
        match self {
            RuleField::Head => "head",
            RuleField::Body => "body",
            RuleField::Whole => "rule",
        }
    }
}

#[derive(Clone, Debug)]
pub enum TypeErrorContext {
    EntityField { entity: Symbol, field: Symbol },
    OperationReturn { op_name: Symbol },
    OperationEffects { op_name: Symbol },
    OperationMatch { op_name: Symbol },
    Rule { name: Symbol, field: RuleField },
}

impl TypeErrorContext {
    pub fn entity_name(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeErrorContext::EntityField { entity, .. } => kb.resolve_sym(*entity).to_string(),
            TypeErrorContext::OperationReturn { op_name }
            | TypeErrorContext::OperationEffects { op_name }
            | TypeErrorContext::OperationMatch { op_name } => kb.resolve_sym(*op_name).to_string(),
            TypeErrorContext::Rule { name, .. } => kb.resolve_sym(*name).to_string(),
        }
    }

    pub fn field_name(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeErrorContext::EntityField { field, .. } => kb.resolve_sym(*field).to_string(),
            TypeErrorContext::OperationReturn { .. } => "return".to_string(),
            TypeErrorContext::OperationEffects { .. } => "effects".to_string(),
            TypeErrorContext::OperationMatch { .. } => "match".to_string(),
            TypeErrorContext::Rule { field, .. } => field.name().to_string(),
        }
    }
}

impl TypeError {
    pub fn format(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeError::TypeMismatch { expected, actual, .. } => {
                format!("type mismatch: expected {}, got {}",
                    type_display_name(kb, *expected),
                    type_display_name(kb, *actual))
            }
            TypeError::UnknownField { entity_name, field, .. } => {
                format!("unknown field '{}' in entity {}",
                    kb.resolve_sym(*field), kb.resolve_sym(*entity_name))
            }
            TypeError::NoParentSort { name } => {
                format!("entity has no parent sort: {}", kb.resolve_sym(*name))
            }
            TypeError::UnresolvedName { name, .. } => {
                format!("unresolved name: {}", kb.resolve_sym(*name))
            }
            TypeError::NoConstructor { name, .. } => {
                format!("no constructor: {}", kb.resolve_sym(*name))
            }
            TypeError::UnknownApplyFunctor { name, .. } => {
                format!("unknown apply functor: {}", kb.resolve_sym(*name))
            }
            TypeError::DispatchNoMatch { op, .. } => {
                format!(
                    "dispatch failed: no impl of {} for the per-call bindings",
                    kb.qualified_name_of(*op),
                )
            }
            TypeError::DispatchAmbiguous { op, .. } => {
                format!(
                    "dispatch failed: multiple impls of {} match the per-call bindings (coherence rule)",
                    kb.qualified_name_of(*op),
                )
            }
            TypeError::NoSuchTypeParam { op, name, .. } => {
                format!(
                    "{} has no type parameter named '{}'",
                    kb.qualified_name_of(*op),
                    kb.resolve_sym(*name),
                )
            }
            TypeError::UnconstrainedTypeParam { op, type_param, .. } => {
                let op_name = kb.qualified_name_of(*op);
                format!(
                    "type parameter '{0}' of {1} is unconstrained — use `{2}[{0} = …](…)`",
                    kb.resolve_sym(*type_param),
                    op_name,
                    short_name_of(op_name),
                )
            }
            TypeError::BottomExpr { .. } => {
                "bottom or post-elaboration expression in surface IR".to_string()
            }
            TypeError::Multiple { errors } => {
                let parts: Vec<String> = errors.iter().map(|e| e.format(kb)).collect();
                parts.join("; ")
            }
            TypeError::Other { expected, actual, .. } => {
                format!("expected {}, got {}", expected, actual)
            }
        }
    }

    pub fn span(&self, _kb: &KnowledgeBase) -> Option<Span> {
        match self {
            TypeError::TypeMismatch { span, .. }
            | TypeError::UnknownField { span, .. }
            | TypeError::UnresolvedName { span, .. }
            | TypeError::NoConstructor { span, .. }
            | TypeError::UnknownApplyFunctor { span, .. }
            | TypeError::DispatchNoMatch { span, .. }
            | TypeError::DispatchAmbiguous { span, .. }
            | TypeError::NoSuchTypeParam { span, .. }
            | TypeError::UnconstrainedTypeParam { span, .. }
            | TypeError::BottomExpr { span } => *span,
            TypeError::Other { span, .. } => *span,
            TypeError::NoParentSort { .. } => None,
            TypeError::Multiple { errors } => errors.iter().find_map(|e| e.span(_kb)),
        }
    }

    /// Flatten a `Multiple` into its leaf errors; non-`Multiple` becomes
    /// a single-element vec. Lets the operation-body driver push each
    /// sibling failure as its own load error.
    pub fn flatten(self) -> Vec<TypeError> {
        match self {
            TypeError::Multiple { errors } => {
                let mut out = Vec::with_capacity(errors.len());
                for e in errors {
                    out.extend(e.flatten());
                }
                out
            }
            other => vec![other],
        }
    }

    /// Lossy conversion to LoadError for legacy callers (load.rs, CLI).
    /// Resolves spans, formats type terms via `type_display_name`.
    pub fn to_load_error(&self, kb: &KnowledgeBase) -> super::load::LoadError {
        use super::load::LoadError;
        match self {
            TypeError::TypeMismatch { context, expected, actual, .. } => LoadError::TypeMismatch {
                entity_name: context.entity_name(kb),
                field_name: context.field_name(kb),
                expected_type: type_display_name(kb, *expected),
                actual_type: type_display_name(kb, *actual),
                span: self.span(kb),
            },
            TypeError::UnknownField { entity_name, field, .. } => {
                let field_name = kb.resolve_sym(*field).to_string();
                LoadError::TypeMismatch {
                    entity_name: kb.resolve_sym(*entity_name).to_string(),
                    expected_type: "known field".to_string(),
                    actual_type: format!("unknown field '{}'", field_name),
                    field_name,
                    span: self.span(kb),
                }
            }
            TypeError::NoParentSort { name } => LoadError::TypeMismatch {
                entity_name: kb.resolve_sym(*name).to_string(),
                field_name: "parent_sort".to_string(),
                expected_type: "parent sort".to_string(),
                actual_type: "none".to_string(),
                span: None,
            },
            TypeError::UnresolvedName { name, .. } => LoadError::TypeMismatch {
                entity_name: kb.resolve_sym(*name).to_string(),
                field_name: "name".to_string(),
                expected_type: "resolved name".to_string(),
                actual_type: "unresolved".to_string(),
                span: self.span(kb),
            },
            TypeError::NoConstructor { name, .. } => LoadError::TypeMismatch {
                entity_name: kb.resolve_sym(*name).to_string(),
                field_name: "constructor".to_string(),
                expected_type: "known constructor".to_string(),
                actual_type: "unknown".to_string(),
                span: self.span(kb),
            },
            TypeError::UnknownApplyFunctor { name, .. } => LoadError::TypeMismatch {
                entity_name: kb.resolve_sym(*name).to_string(),
                field_name: "apply".to_string(),
                expected_type: "known operation or arrow-typed variable".to_string(),
                actual_type: "unknown functor".to_string(),
                span: self.span(kb),
            },
            TypeError::DispatchNoMatch { op, .. } => LoadError::TypeMismatch {
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "dispatch".to_string(),
                expected_type: "matching impl for per-call bindings".to_string(),
                actual_type: "no impl matches".to_string(),
                span: self.span(kb),
            },
            TypeError::DispatchAmbiguous { op, .. } => LoadError::TypeMismatch {
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "dispatch".to_string(),
                expected_type: "unique impl for per-call bindings".to_string(),
                actual_type: "multiple impls match (coherence rule)".to_string(),
                span: self.span(kb),
            },
            TypeError::NoSuchTypeParam { op, name, .. } => LoadError::TypeMismatch {
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "type_arg".to_string(),
                expected_type: "declared type-param name".to_string(),
                actual_type: format!("unknown type-param '{}'", kb.resolve_sym(*name)),
                span: self.span(kb),
            },
            TypeError::UnconstrainedTypeParam { op, type_param, .. } => {
                let op_qn = kb.qualified_name_of(*op);
                let suggestion = format!(
                    "unconstrained — use `{}[{} = …](…)`",
                    short_name_of(op_qn),
                    kb.resolve_sym(*type_param),
                );
                LoadError::TypeMismatch {
                    entity_name: op_qn.to_string(),
                    field_name: "type_arg".to_string(),
                    expected_type: format!("a type for '{}'", kb.resolve_sym(*type_param)),
                    actual_type: suggestion,
                    span: self.span(kb),
                }
            }
            TypeError::BottomExpr { .. } => LoadError::TypeMismatch {
                entity_name: "<bottom>".to_string(),
                field_name: "expr".to_string(),
                expected_type: "surface expression".to_string(),
                actual_type: "bottom / post-elaboration form".to_string(),
                span: self.span(kb),
            },
            TypeError::Multiple { errors } => {
                // Lossy: keep the first error's structured form so legacy
                // single-error consumers see something. Callers that care
                // about all errors call `flatten()` and convert per-element.
                if let Some(first) = errors.first() {
                    first.to_load_error(kb)
                } else {
                    LoadError::TypeMismatch {
                        entity_name: "<empty>".to_string(),
                        field_name: "".to_string(),
                        expected_type: String::new(),
                        actual_type: String::new(),
                        span: None,
                    }
                }
            }
            TypeError::Other { context, expected, actual, .. } => LoadError::TypeMismatch {
                entity_name: context.entity_name(kb),
                field_name: context.field_name(kb),
                expected_type: expected.clone(),
                actual_type: actual.clone(),
                span: self.span(kb),
            },
        }
    }
}

// ── TypingEnv ──────────────────────────────────────────────────

#[derive(Clone)]
pub struct TypingEnv {
    // WI-259: Symbol-keyed (was String-keyed). Symbol is a Copy
    // u32 newtype that's already interned and trivially hashable;
    // String keys cost a fresh allocation per bind + a hash over
    // the name's bytes at every lookup, and TypingEnv gets cloned
    // on every Visit push of the iterative typer.
    var_bindings: HashMap<Symbol, TermId>,
    type_bindings: HashMap<Symbol, TermId>,
    local_resources: Vec<Symbol>,
    /// Enclosing sort for defer-to-requirement detection plus a
    /// cached `requires_chain` snapshot. The chain is consulted for every
    /// spec-op call site under this body; caching once per body avoids
    /// re-walking `SortRequiresInfo` per apply.
    enclosing: Option<EnclosingSort>,
    pub diagnostics: Vec<String>,
}

#[derive(Clone)]
struct EnclosingSort {
    sort: Symbol,
    requires: Vec<RequiresEntry>,
}

impl TypingEnv {
    pub fn empty() -> Self {
        Self {
            var_bindings: HashMap::new(),
            type_bindings: HashMap::new(),
            local_resources: Vec::new(),
            enclosing: None,
            diagnostics: Vec::new(),
        }
    }

    /// Set the sort whose body is currently being type-checked and
    /// snapshot its `requires` chain (cheap-ish: one `SortRequiresInfo`
    /// scan via `requires_chain`). `check_apply` reads the cached chain
    /// per spec-op dispatch without re-walking facts.
    pub fn set_enclosing_sort(&mut self, kb: &mut KnowledgeBase, sort: Option<Symbol>) {
        self.enclosing = sort.map(|s| EnclosingSort {
            sort: s,
            requires: requires_chain(kb, s),
        });
    }

    pub fn enclosing_sort(&self) -> Option<Symbol> {
        self.enclosing.as_ref().map(|e| e.sort)
    }

    fn enclosing_requires(&self) -> Option<&[RequiresEntry]> {
        self.enclosing.as_ref().map(|e| e.requires.as_slice())
    }

    pub fn bind_var(&mut self, name: Symbol, ty: TermId) {
        self.var_bindings.insert(name, ty);
    }

    pub fn lookup_var(&self, name: Symbol) -> Option<TermId> {
        self.var_bindings.get(&name).copied()
    }

    pub fn bind_type(&mut self, param: Symbol, ty: TermId) {
        self.type_bindings.insert(param, ty);
    }

    pub fn lookup_type(&self, param: Symbol) -> Option<TermId> {
        self.type_bindings.get(&param).copied()
    }

    pub fn declare_local_resource(&mut self, name: Symbol) {
        self.local_resources.push(name);
    }

    pub fn is_local_resource(&self, name: Symbol) -> bool {
        self.local_resources.iter().any(|r| *r == name)
    }
}

// ── TypeResult ─────────────────────────────────────────────────

/// Result of type_check: inferred type + updated env + collected effects.
/// Mirrors typing_pass_spec.anthill: TypeResult(type: Type, env: TypingEnv, effects: List[Type])
pub struct TypeResult {
    pub ty: TermId,
    pub env: TypingEnv,
    pub effects: Vec<TermId>,
    /// WI-283: the (possibly-rewritten) occurrence this result describes.
    /// The typer is *tree-producing*: every result carries the node it
    /// is the type of, so a parent build-frame can reassemble itself
    /// from rewritten children and the [`TypeBuildFrame::Stamp`] frame
    /// can record the inferred type onto the *resulting* node. For a
    /// node that no `[simp]` rule rewrites this is the input occurrence
    /// (identity); a firing frame replaces it with the synthesized RHS
    /// (`synthesized_expr`, with the input occ as its `from`).
    pub node: Rc<NodeOccurrence>,
}

impl TypeResult {
    /// Pure result — no effects.
    pub fn pure(ty: TermId, env: TypingEnv, node: Rc<NodeOccurrence>) -> Self {
        Self { ty, env, effects: Vec::new(), node }
    }
}

/// Filter effects: keep only external effects (on non-local resources).
/// Effects on let-bound resources are local and don't propagate.
pub(crate) fn external_effects(kb: &KnowledgeBase, env: &TypingEnv, effects: &[TermId]) -> Vec<TermId> {
    effects.iter().filter(|&&effect| {
        // An effect like Modify[store] — check if 'store' is a local resource
        // Effect terms are sort_ref or parameterized. Extract the resource symbol.
        match extract_effect_resource_sym(kb, effect) {
            Some(sym) => !env.is_local_resource(sym),
            None => true, // can't determine resource — assume external
        }
    }).copied().collect()
}

/// Extract the resource symbol from an effect term.
/// e.g., Modify[T = store] → Some(store), or sort_ref(name: Modify) → None (no resource)
pub(crate) fn extract_effect_resource_sym(kb: &KnowledgeBase, effect: TermId) -> Option<Symbol> {
    let functor_name = type_functor_name(kb, effect)?;
    match functor_name {
        "parameterized" => {
            if let Term::Fn { named_args, .. } = kb.get_term(effect) {
                let bindings_tid = get_named_arg(kb, named_args, "bindings")?;
                let bindings = list_to_vec(kb, bindings_tid);
                for b in &bindings {
                    if let Some(value_tid) = binding_value(kb, *b) {
                        // WI-302: a value-in-type binding (`Modify[c]`) stores the
                        // resource as `denoted(value: Ref(c))`; see through the
                        // wrapper to the underlying value before extracting.
                        let value_tid = unwrap_denoted_value(kb, value_tid);
                        if let Some(sym) = extract_sort_ref_sym(kb, value_tid) {
                            return Some(sym);
                        }
                        if let Term::Ref(s) = kb.get_term(value_tid) {
                            return Some(*s);
                        }
                    }
                }
            }
            None
        }
        "sort_ref" => None,
        _ => None,
    }
}

/// Merge two effect lists (set union by TermId).
fn merge_effects(a: &[TermId], b: &[TermId]) -> Vec<TermId> {
    let mut result = a.to_vec();
    for e in b {
        if !result.contains(e) {
            result.push(*e);
        }
    }
    result
}

/// NodeOccurrence-aware var_ref detection — peer of
/// [`extract_var_ref_sym`] for the [`type_check_node`] dispatch path.
/// Returns the symbol the variable refers to when `occ`'s Expr is a
/// `VarRef`; otherwise `None`.
fn extract_var_ref_sym_node(occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    if let NodeKind::Expr { expr: Expr::VarRef { name }, .. } = &occ.kind {
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
    match kb.get_term(term).clone() {
        Term::Ref(s) => map
            .get(&s)
            .map_or(term, |&new_sym| kb.alloc(Term::Ref(new_sym))),
        Term::Fn { .. } => kb.map_fn_children(term, |kb, child| {
            substitute_ref_syms(kb, child, map)
        }),
        _ => term,
    }
}

// ── Helpers ────────────────────────────────────────────────────

pub fn type_display_name(kb: &KnowledgeBase, ty: TermId) -> String {
    match kb.get_term(ty) {
        Term::Fn { functor, named_args, .. } => {
            let fname = kb.resolve_sym(*functor);
            match fname {
                "sort_ref" => {
                    // sort_ref(name: Ref(sym))
                    extract_ref_field(kb, named_args, "name")
                        .map(|s| kb.resolve_sym(s).to_string())
                        .unwrap_or_else(|| "?".to_string())
                }
                "parameterized" => {
                    // parameterized(base: type, bindings: List[TypeBinding])
                    let base_name = get_named_arg(kb, named_args, "base")
                        .map(|b| type_display_name(kb, b))
                        .unwrap_or_else(|| "?".to_string());
                    let bindings_tid = get_named_arg(kb, named_args, "bindings");
                    let bindings = bindings_tid.map(|b| list_to_vec(kb, b)).unwrap_or_default();
                    let params: Vec<String> = bindings.iter().map(|b| {
                        if let Term::Fn { named_args: ba, .. } = kb.get_term(*b) {
                            let p = extract_ref_field(kb, ba, "param")
                                .map(|s| kb.resolve_sym(s).to_string())
                                .unwrap_or_else(|| "?".to_string());
                            let v = get_named_arg(kb, ba, "value")
                                .map(|v| type_display_name(kb, v))
                                .unwrap_or_else(|| "?".to_string());
                            format!("{} = {}", p, v)
                        } else {
                            "?".to_string()
                        }
                    }).collect();
                    if params.is_empty() {
                        base_name
                    } else {
                        format!("{}[{}]", base_name, params.join(", "))
                    }
                }
                "arrow" => {
                    // arrow(param: type, result: type, effects: List[Type])
                    let p = get_named_arg(kb, named_args, "param")
                        .map(|t| type_display_name(kb, t))
                        .unwrap_or_else(|| "?".to_string());
                    let r = get_named_arg(kb, named_args, "result")
                        .map(|t| type_display_name(kb, t))
                        .unwrap_or_else(|| "?".to_string());
                    format!("{} -> {}", p, r)
                }
                "type_var" => {
                    extract_ref_field(kb, named_args, "name")
                        .map(|s| format!("?{}", kb.resolve_sym(s)))
                        .unwrap_or_else(|| "?".to_string())
                }
                "named_tuple" => {
                    let fields_tid = get_named_arg(kb, named_args, "fields");
                    let fields = fields_tid.map(|f| list_to_vec(kb, f)).unwrap_or_default();
                    let parts: Vec<String> = fields.iter().map(|f| {
                        if let Term::Fn { named_args: fa, .. } = kb.get_term(*f) {
                            let n = extract_ref_field(kb, fa, "name")
                                .map(|s| kb.resolve_sym(s).to_string())
                                .unwrap_or_else(|| "?".to_string());
                            let t = get_named_arg(kb, fa, "type")
                                .map(|v| type_display_name(kb, v))
                                .unwrap_or_else(|| "?".to_string());
                            format!("{}: {}", n, t)
                        } else {
                            "?".to_string()
                        }
                    }).collect();
                    format!("({})", parts.join(", "))
                }
                "nothing" => "nothing".to_string(),
                "denoted" => {
                    // WI-302: value-in-type — render the carried value directly
                    // (`Modify[c]` shows `c`, not `denoted[value = c]`).
                    get_named_arg(kb, named_args, "value")
                        .map(|v| type_display_name(kb, v))
                        .unwrap_or_else(|| "?".to_string())
                }
                "effects_rows" => {
                    // WI-320: EffectExpression-in-Type — render with row braces
                    // (`{…}`) around the wrapped expression. The inner is an
                    // EffectExpression term (present / absent / open / merge /
                    // empty_row); a dedicated EffectExpression pretty-printer
                    // is a WI-307 follow-on. For now the inner term renders
                    // through type_display_name's generic Fn fallback, which is
                    // readable enough for diagnostics until row machinery lands.
                    get_named_arg(kb, named_args, "effects_expr")
                        .map(|e| format!("{{{}}}", type_display_name(kb, e)))
                        .unwrap_or_else(|| "{?}".to_string())
                }
                _ => {
                    // Fallback: raw term display (for non-type terms)
                    let name = fname.to_string();
                    let params: Vec<String> = named_args.iter()
                        .map(|(s, v)| format!("{} = {}", kb.resolve_sym(*s), type_display_name(kb, *v)))
                        .collect();
                    if params.is_empty() {
                        name
                    } else {
                        format!("{}[{}]", name, params.join(", "))
                    }
                }
            }
        }
        Term::Ref(s) => kb.resolve_sym(*s).to_string(),
        Term::Var(v) => {
            // WI-307 code-review #7: render variables by their name (not
            // TermId Debug, which would embed allocation-order indices and
            // break the canonical-form-stable-across-runs claim of
            // `build_canonical_effects_rows`). All three Var variants —
            // Global, DeBruijn, Rigid — carry a `name: Symbol`; resolve it
            // so two distinct vars sharing a textual name (e.g. `T` from
            // different scopes) sort together.
            let name_sym = match v {
                crate::kb::term::Var::Global(vid) => vid.name(),
                crate::kb::term::Var::DeBruijn(_) => {
                    // De Bruijn indices have no name; render as `?` so they
                    // sort consistently. In practice these don't reach
                    // `type_display_name` because the typer operates on
                    // post-binder-open terms, but the arm keeps the
                    // function total.
                    return "?".to_string();
                }
                crate::kb::term::Var::Rigid(vid) => vid.name(),
            };
            format!("?{}", kb.resolve_sym(name_sym))
        }
        _ => format!("{:?}", ty),
    }
}

/// Extract a Ref(sym) from a named arg field.
fn extract_ref_field(kb: &KnowledgeBase, named_args: &SmallVec<[(Symbol, TermId); 2]>, key: &str) -> Option<Symbol> {
    get_named_arg(kb, named_args, key)
        .and_then(|tid| match kb.get_term(tid) {
            Term::Ref(s) => Some(*s),
            Term::Ident(s) => Some(*s),
            _ => None,
        })
}

/// Functor symbols of a sort's constructor children.
fn sort_constructor_syms(kb: &KnowledgeBase, sort_term: TermId) -> Vec<Symbol> {
    kb.sort_children(sort_term)
        .iter()
        .filter_map(|&et| match kb.get_term(et) {
            Term::Fn { functor, .. } => Some(*functor),
            _ => None,
        })
        .collect()
}

/// Convert a raw sort term (Fn { functor: sym }) to a sort_ref type term.
fn sort_term_to_type(kb: &mut KnowledgeBase, sort_term: TermId) -> TermId {
    let sym = match kb.get_term(sort_term) {
        Term::Fn { functor, .. } => Some(*functor),
        Term::Ref(s) => Some(*s),
        _ => None,
    };
    match sym {
        Some(s) => kb.make_sort_ref(s),
        None => sort_term,
    }
}

pub fn get_named_arg(kb: &KnowledgeBase, named_args: &SmallVec<[(Symbol, TermId); 2]>, key: &str) -> Option<TermId> {
    named_args.iter()
        .find(|(s, _)| kb.resolve_sym(*s) == key)
        .map(|(_, v)| *v)
}

pub fn extract_sym_arg(
    kb: &KnowledgeBase,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    pos_args: &SmallVec<[TermId; 4]>,
    key: &str,
) -> Option<Symbol> {
    named_args.iter()
        .find(|(s, _)| kb.resolve_sym(*s) == key)
        .and_then(|(_, v)| match kb.get_term(*v) {
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            _ => None,
        })
        .or_else(|| pos_args.first().and_then(|v| match kb.get_term(*v) {
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            _ => None,
        }))
}

pub fn unwrap_option(kb: &KnowledgeBase, opt: TermId) -> Option<TermId> {
    if let Term::Fn { functor, pos_args, named_args } = kb.get_term(opt) {
        if kb.resolve_sym(*functor) == "some" {
            if !pos_args.is_empty() { return Some(pos_args[0]); }
            if !named_args.is_empty() { return Some(named_args[0].1); }
        }
    }
    None
}

pub fn list_to_vec(kb: &KnowledgeBase, mut term: TermId) -> Vec<TermId> {
    let mut items = Vec::new();
    loop {
        match kb.get_term(term) {
            Term::Fn { functor, named_args, pos_args } => {
                let name = kb.resolve_sym(*functor);
                if name == "nil" { break; }
                if name == "cons" {
                    let head = named_args.iter()
                        .find(|(s, _)| kb.resolve_sym(*s) == "head")
                        .map(|(_, v)| *v)
                        .or_else(|| pos_args.first().copied());
                    let tail = named_args.iter()
                        .find(|(s, _)| kb.resolve_sym(*s) == "tail")
                        .map(|(_, v)| *v)
                        .or_else(|| pos_args.get(1).copied());
                    if let Some(h) = head { items.push(h); }
                    if let Some(t) = tail { term = t; } else { break; }
                } else { break; }
            }
            _ => break,
        }
    }
    items
}


// ── Iterative-typer work ops ───────────────────────────────────
//
// Let / Match / Lambda body recursion is the dominant deep-nesting
// source on typing_pass_spec.anthill. Convert just those three
// recursion paths to a Visit/Build work-stack walker so chained
// `let A = …; let B = …; …` and nested matches stay flat on the
// host stack. Other variants (Apply, Constructor, If, ListLit,
// SetLit, TupleLit) keep their existing `check_*` helpers; their
// recursion is bounded by argument count / branch count rather than
// source nesting depth.

enum TypeWorkOp {
    /// `expected` is the WI-270 top-down type hint — the caller's
    /// expected type for the value at this position. It seeds Apply /
    /// Constructor return-type unification, threads through Let /
    /// Match / If branches, and decomposes through Lambda arrows.
    /// `None` at the root Visit and at positions where no hint is
    /// available (leaf args, scrutinees, conditions).
    Visit {
        occ: Rc<NodeOccurrence>,
        env: Rc<TypingEnv>,
        expected: Option<TermId>,
        /// WI-283: remaining `[simp]` fire-fuel for this node. Inherited
        /// unchanged by child Visits; spent (`fuel - 1`) only when an
        /// Apply/Constructor fires and re-`Visit`s its synthesized RHS.
        /// Bounds the fire chain (→ termination) without host recursion.
        fuel: usize,
    },
    Build(TypeBuildFrame),
}

/// Push a node Visit preceded *underneath* by a [`TypeBuildFrame::Stamp`]
/// frame (WI-284). The Stamp sits just below the Visit on the work
/// stack, so it pops only after the Visit and all of its sub-work have
/// produced this node's `TypeResult` — at which point it records the
/// inferred type onto that result's `node` (WI-283: the *resulting*,
/// possibly-rewritten occurrence, not the input — identical until a
/// `[simp]` rule fires). Routing every node visit through here stamps
/// each typed occurrence exactly once, uniformly across all iterative
/// arms (Apply / Constructor / Let / Match / Lambda / If / collection
/// literals — every form is a work-stack Build frame after WI-285, so
/// there is no recursive `type_check_node` re-entry).
fn push_visit(
    work: &mut Vec<TypeWorkOp>,
    occ: Rc<NodeOccurrence>,
    env: Rc<TypingEnv>,
    expected: Option<TermId>,
    fuel: usize,
) {
    work.push(TypeWorkOp::Build(TypeBuildFrame::Stamp));
    work.push(TypeWorkOp::Visit { occ, env, expected, fuel });
}

/// Push a Visit with no top-down hint. Used at positions where the
/// caller's expected doesn't bound the child's type — Apply / Ctor
/// args (constrained by op.params / entity_field_types), the
/// scrutinee of a Match (drives the branch envs but takes no hint
/// from outside), and the condition of an If (always `Bool`).
fn push_visit_no_hint(work: &mut Vec<TypeWorkOp>, occ: Rc<NodeOccurrence>, env: Rc<TypingEnv>, fuel: usize) {
    push_visit(work, occ, env, None, fuel);
}

// WI-258: env-carrying frames hold `Rc<TypingEnv>`. Sibling Visits
// share the same Rc; only the mutating sites (LetAfterValue body env,
// LambdaBody body env, MatchAfterScrutinee branch envs) clone the
// inner `TypingEnv` via `Rc::make_mut`. Saves N-1 HashMap clones per
// multi-arg call site on deep specs.
enum TypeBuildFrame {
    /// All Apply args finished; drain N = `pos_count + named_keys.len()`
    /// results, hand them to `check_apply_iter` which runs the
    /// non-recursive subst / dispatch / classify logic. `expected`
    /// (WI-270) is unified with the op's return type before the
    /// unconstrained-param check so caller context flows into the seed.
    Apply {
        occ: Rc<NodeOccurrence>,
        fn_sym: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        env: Rc<TypingEnv>,
        expected: Option<TermId>,
        /// WI-283: fire-fuel inherited from this node's `Visit`; on a fire
        /// the RHS is re-`Visit`ed with `fuel - 1` (bounds the chain).
        fuel: usize,
    },
    /// All Constructor args finished; drain results and call
    /// `check_constructor_iter`. WI-270: `expected` flows into the
    /// parent-type unification so a caller-side `Option[Int]`
    /// constrains `some(?)`'s inferred T.
    Constructor {
        occ: Rc<NodeOccurrence>,
        ctor_sym: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        env: Rc<TypingEnv>,
        span: Option<Span>,
        expected: Option<TermId>,
        /// WI-283: fire-fuel — see [`TypeBuildFrame::Apply::fuel`].
        fuel: usize,
    },
    /// Value finished; compute the body's ext_env and schedule the
    /// body Visit, plus a `LetFinal` frame to combine results. If the
    /// value's TypeResult is `None`, the let propagates failure up
    /// without visiting the body (see WI-204 feedback — no fallbacks).
    /// `body_expected` is the let's own `expected` (the outer hint),
    /// passed forward to the body Visit per WI-270.
    LetAfterValue {
        occ: Rc<NodeOccurrence>,
        pattern: TermId,
        annotation: Option<TermId>,
        body_occ: Rc<NodeOccurrence>,
        body_expected: Option<TermId>,
        /// WI-283: fire-fuel to propagate onto the body `Visit`.
        fuel: usize,
    },
    /// Body finished; merge `value_effects` (captured at
    /// `LetAfterValue` time so we didn't need to keep `value_r`
    /// alive — its `env` was moved into the body's ext_env, which is
    /// the whole point of WI-258's COW) with `body_r.effects` and
    /// return the let's TypeResult.
    LetFinal {
        occ: Rc<NodeOccurrence>,
        /// The let value's (possibly-rewritten) node, captured at
        /// `LetAfterValue` (its `TypeResult` is consumed there); paired
        /// with the body's node to reassemble the `Let` (WI-283).
        value_node: Rc<NodeOccurrence>,
        value_effects: Vec<TermId>,
    },
    /// Scrutinee finished; walk the branch patterns for coverage,
    /// compute each branch's env, schedule body Visits + a
    /// `MatchFinal` frame. `body_expected` flows to every branch body.
    MatchAfterScrutinee {
        occ: Rc<NodeOccurrence>,
        branches: Vec<MatchBranch>,
        outer_env: Rc<TypingEnv>,
        body_expected: Option<TermId>,
        /// WI-283: fire-fuel to propagate onto each branch-body `Visit`.
        fuel: usize,
    },
    /// All branch bodies finished; pop `branch_count` results, filter
    /// per-branch effects against each branch's local resources,
    /// emit non-exhaustiveness diagnostics, return the match's
    /// TypeResult.
    MatchFinal {
        occ: Rc<NodeOccurrence>,
        /// The scrutinee's (possibly-rewritten) node, captured at
        /// `MatchAfterScrutinee`; paired with the branch bodies to
        /// reassemble the `Match` (WI-283). Guards aren't typed/visited,
        /// so they're re-read from `occ` unchanged.
        scr_node: Rc<NodeOccurrence>,
        scr_effects: Vec<TermId>,
        branch_envs: Vec<Rc<TypingEnv>>,
        branch_count: usize,
        outer_env: Rc<TypingEnv>,
        scr_ty: Option<TermId>,
        covered_entities: Vec<Symbol>,
        has_wildcard: bool,
        /// WI-287: the match's own expected type (the parent's hint).
        /// `Some` ⇒ checked mode (every branch must conform); `None` ⇒
        /// synthesis mode (result is the join — a common supertype — of
        /// the branch types).
        body_expected: Option<TermId>,
    },
    /// Lambda body finished; build the `arrow(param, body_ty,
    /// body_effects)` type and return a pure result (creating a
    /// lambda is itself effect-free).
    ///
    /// `param_type` is the type the param was bound to in the body env
    /// (annotation, the expected arrow's param slot, or a fresh type
    /// var). Threading it here keeps the arrow's param slot identical
    /// to what the body referenced — without it, `build` would re-derive
    /// a *different* fresh var and the arrow would claim `?a -> T` while
    /// the body was typed under a distinct `?b`.
    LambdaBody { occ: Rc<NodeOccurrence>, param_type: TermId, outer_env: Rc<TypingEnv> },
    /// WI-285: all three If sub-expressions finished (drained in
    /// `[condition, then, else]` order); merge their effects and return
    /// the if's `TypeResult`. WI-287: the type is the join of the then /
    /// else branch types (checked against `expected` when present), not
    /// just the then-branch type. Replaces the recursive-helper arm so a
    /// deep else-if chain stays on the heap.
    IfExpr { occ: Rc<NodeOccurrence>, env: Rc<TypingEnv>, expected: Option<TermId> },
    /// WI-285: all list elements finished; drain `count`, infer the
    /// element type (`element_hint` when bound by an outer
    /// `List[T = X]`, else the first element's type), build
    /// `List[T = elem]` (former `check_list_literal`).
    ListLit { occ: Rc<NodeOccurrence>, env: Rc<TypingEnv>, element_hint: Option<TermId>, count: usize },
    /// WI-285: as [`TypeBuildFrame::ListLit`], for `Set[T = elem]`.
    SetLit { occ: Rc<NodeOccurrence>, env: Rc<TypingEnv>, element_hint: Option<TermId>, count: usize },
    /// WI-285: all tuple fields finished (positional then named);
    /// drain `pos_count + named_names.len()`, building the named-tuple
    /// type (`_0`, `_1`, … for positional fields, declared names for
    /// named ones; former `check_tuple_literal`).
    TupleLit { occ: Rc<NodeOccurrence>, env: Rc<TypingEnv>, pos_count: usize, named_names: Vec<Symbol> },
    /// WI-284: record a node's inferred type. Pushed by [`push_visit`]
    /// just under the node's Visit, so when it pops the node's
    /// `TypeResult` is on top of `results`. Peeks that result — never
    /// pops or pushes, so it is results-neutral and doesn't perturb the
    /// Apply / Constructor / MatchFinal drains or the final
    /// single-result invariant — and writes the type onto the result's
    /// `node` (WI-283: the resulting occurrence, which the result itself
    /// carries — so the frame needs no stored `occ`).
    Stamp,
}

// ── type_check_expr ────────────────────────────────────────────

/// Infer the type of an expression. Returns TypeResult with type, env, and effects.
/// Public back-compat entry point. The typer's canonical dispatch flow
/// now walks `Rc<NodeOccurrence>` trees via [`type_check_node`]; this
/// shim materializes a NodeOccurrence (from a Handle wrapper or by
/// converting a raw `Term::Fn` shape used by hand-built test inputs)
/// and delegates.
pub fn type_check_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    expr: TermId,
) -> Result<TypeResult, TypeError> {
    type_check_expr_expected(kb, env, expr, None)
}

/// WI-270: variant of [`type_check_expr`] that threads a top-down
/// `expected` hint from the caller. Use this from the operation-body
/// driver (passing `op.return_type`) and from any other site with a
/// declared expected type.
pub fn type_check_expr_expected(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    expr: TermId,
    expected: Option<TermId>,
) -> Result<TypeResult, TypeError> {
    let node = materialize_from_handle(kb, expr);
    type_check_node(kb, env, &node, expected)
}

/// Move out of `Rc<TypingEnv>` without cloning when sole owner; else
/// clone the inner `TypingEnv`. Used at TypeResult-construction sites
/// where we need an owned `TypingEnv` for `TypeResult.env`.
#[inline]
fn unwrap_env(env: Rc<TypingEnv>) -> TypingEnv {
    Rc::try_unwrap(env).unwrap_or_else(|rc| (*rc).clone())
}

/// Canonical typer entry — walk a `Rc<NodeOccurrence>` and produce a
/// `TypeResult`. Runs a Visit/Build work-stack so the Let / Match /
/// Lambda body-recursion paths stay flat on the host stack regardless
/// of source nesting depth. Other variants delegate to their existing
/// `check_*` helpers (which may call back through here, adding ≤ 1
/// host frame per Apply / Constructor / If / collection level — those
/// recursions are bounded by argument count, not source depth).
pub fn type_check_node(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    expected: Option<TermId>,
) -> Result<TypeResult, TypeError> {
    let mut work: Vec<TypeWorkOp> = Vec::with_capacity(32);
    let mut results: Vec<Result<TypeResult, TypeError>> = Vec::with_capacity(32);
    // WI-283: gate the in-typer `[simp]` firing on whether any `[simp]`
    // equation is indexed at all — read once per walk, so the common
    // no-rule case pays nothing per node.
    let simp_enabled = super::simp_rewrite::has_simp_equations(kb);
    // WI-283: `[simp]` fire-fuel rides on each `Visit` (not the host stack).
    // When an Apply/Constructor fires, the synthesized RHS is re-`Visit`ed
    // with `fuel - 1` on this same work-stack — so a non-terminating /
    // non-confluent `[simp]` rule (e.g. a commutative law mistagged
    // `[simp]`) bottoms out at `fuel == 0` leaving a partial redex (exactly
    // as the fuel-bounded `simp_rewrite::run` did) instead of recursing the
    // host stack to overflow. Children inherit the fuel unchanged; only a
    // fire spends it. Matches the WI-285 iterative discipline.
    push_visit(&mut work, Rc::clone(occ), Rc::new(env.clone()), expected, super::simp_rewrite::SIMP_FUEL);
    while let Some(op) = work.pop() {
        match op {
            TypeWorkOp::Visit { occ, env, expected, fuel } => {
                visit_type(kb, occ, env, expected, fuel, &mut work, &mut results)
            }
            TypeWorkOp::Build(frame) => build_type(kb, frame, simp_enabled, &mut work, &mut results),
        }
    }
    debug_assert_eq!(results.len(), 1, "iterative typer: expected exactly one result");
    results.pop().expect("iterative typer: missing final result")
}

/// Type-check a bare-identifier reference (Ref / Ident / VarRef) by
/// dispatching across the resolution paths: env-bound var,
/// constructor, zero-arg operation. Returns `Err(UnresolvedName)`
/// when none match — the strict equivalent of the pre-WI-264 silent-
/// None bail.
fn check_bare_ref(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    sym: Symbol,
    span: Option<Span>,
    occ: &Rc<NodeOccurrence>,
) -> Result<TypeResult, TypeError> {
    if let Some(ty) = env.lookup_var(sym) {
        return Ok(TypeResult::pure(ty, env.clone(), Rc::clone(occ)));
    }
    if kb.is_constructor_symbol(sym) {
        return check_constructor_iter(kb, env, sym, &[], &[], &[], &[], span, None, occ);
    }
    if let Some(ret_ty) = lookup_operation_return_type(kb, sym) {
        return Ok(TypeResult::pure(ret_ty, env.clone(), Rc::clone(occ)));
    }
    // A bare reference to a free-standing entity denotes the entity as a type,
    // not a construction — its type is the reflect `Type` sort, so it can be
    // passed to operations taking a `Type` (e.g. `facts_of(kb(), WorkItem)`).
    if kb.is_free_standing_entity(sym) {
        let type_ty = kb.make_sort_ref_by_name("anthill.prelude.Type");
        return Ok(TypeResult::pure(type_ty, env.clone(), Rc::clone(occ)));
    }
    Err(TypeError::UnresolvedName { span, name: sym })
}

/// Aggregate sibling errors into one `TypeError`. Flattens nested
/// `Multiple` so the result has a single-level error vec. Single-
/// error fast-path avoids the Vec allocation when one ill-typed
/// sibling is the typical case.
fn aggregate_errors(errors: Vec<TypeError>) -> TypeError {
    if errors.len() == 1 && !matches!(errors[0], TypeError::Multiple { .. }) {
        return errors.into_iter().next().unwrap();
    }
    let flat: Vec<TypeError> = errors.into_iter().flat_map(TypeError::flatten).collect();
    if flat.len() == 1 {
        flat.into_iter().next().unwrap()
    } else {
        TypeError::Multiple { errors: flat }
    }
}

/// Aggregate any `Err` entries in `results` into a single `TypeError`.
/// Returns `Ok(())` when every result is `Ok` — callers then proceed
/// to use the sub-results with the invariant that they're all `Ok`.
fn collect_arg_errors<'a>(
    results: impl IntoIterator<Item = &'a Result<TypeResult, TypeError>>,
) -> Result<(), TypeError> {
    let errors: Vec<TypeError> = results
        .into_iter()
        .filter_map(|r| r.as_ref().err().cloned())
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(aggregate_errors(errors))
    }
}

/// Dispatch a single Visit: produce a leaf TypeResult directly,
/// delegate to a recursive helper, or push a Build frame + child
/// Visits for the env-changing Let / Match / Lambda cases.
fn visit_type(
    kb: &mut KnowledgeBase,
    occ: Rc<NodeOccurrence>,
    env: Rc<TypingEnv>,
    expected: Option<TermId>,
    // WI-283: the `[simp]` fire-fuel for this node; passed unchanged to
    // child Visits and to the Apply/Constructor/Let/Match build frames so
    // a fire can spend it (`fuel - 1`) when it re-`Visit`s the RHS.
    fuel: usize,
    work: &mut Vec<TypeWorkOp>,
    results: &mut Vec<Result<TypeResult, TypeError>>,
) {
    // Expr / MatchBranch don't derive Clone (Expr's classification
    // RefCell + the implicit sharing through Rc), so we match by
    // reference and `Rc::clone` / hand-clone the slots we need.
    let occ_span = Some(occ.span.span);
    let expr = match &occ.kind {
        NodeKind::Expr { expr, .. } => expr,
        NodeKind::RuleHead { .. } | NodeKind::Pattern(_) => {
            // RuleHead never appears in op/rule body position; Pattern
            // is reached via its parent Expr's pattern slot and handled
            // there, not as a typing target on its own (WI-318).
            results.push(Err(TypeError::BottomExpr { span: occ_span }));
            return;
        }
    };
    match expr {
        // ── Iterative cases ─────────────────────────────────────
        Expr::Let { pattern, type_annotation, value, body } => {
            // WI-318: pattern is now a Pattern-kind occurrence; bridge
            // to TermId for the existing term-based env-extension path.
            let pattern = super::node_occurrence::pattern_to_term(kb, pattern);
            let annotation = *type_annotation;
            let value_occ = Rc::clone(value);
            let body_occ = Rc::clone(body);
            // WI-270: value's expected is the let's annotation only —
            // the outer `expected` doesn't constrain `let x = e` since
            // `e`'s type isn't required to match the let-expression's
            // result type. The let's own `expected` instead flows
            // through to the body.
            work.push(TypeWorkOp::Build(TypeBuildFrame::LetAfterValue {
                occ: Rc::clone(&occ),
                pattern,
                annotation,
                body_occ,
                body_expected: expected,
                fuel,
            }));
            push_visit(work, value_occ, env, annotation, fuel);
        }
        Expr::Match { scrutinee, branches } => {
            let scrutinee_occ = Rc::clone(scrutinee);
            let branches_cloned: Vec<MatchBranch> = branches
                .iter()
                .map(|b| MatchBranch {
                    pattern: Rc::clone(&b.pattern),
                    guard: b.guard.as_ref().map(Rc::clone),
                    body: Rc::clone(&b.body),
                    span: b.span,
                })
                .collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::MatchAfterScrutinee {
                occ: Rc::clone(&occ),
                branches: branches_cloned,
                outer_env: Rc::clone(&env),
                body_expected: expected,
                fuel,
            }));
            push_visit_no_hint(work, scrutinee_occ, env, fuel);
        }
        Expr::Lambda { param, body } => {
            // WI-318: `param` is now a Pattern-kind Rc<NodeOccurrence>.
            // The typer's existing helpers (extract_pattern_type_ann /
            // extend_env_from_pattern) operate on the reflect-Term shape,
            // so bridge via `pattern_to_term` for now. A follow-up should
            // rewrite those helpers to consume Pattern natively.
            let param = super::node_occurrence::pattern_to_term(kb, param);
            let body_occ = Rc::clone(body);
            // Lambda param type, in priority order:
            //   1. explicit annotation on the pattern,
            //   2. the expected arrow's param slot (checking direction —
            //      e.g. `let f: Function[A, B] = lambda q -> ...` already
            //      threads `Function[A, B]` here as `expected`),
            //   3. a fresh type var (synthesis — left for body usage and
            //      the eventual call site to pin via unification).
            // Previously this used only (1), so an unannotated lambda left
            // its param unbound in the body env and every reference to it
            // failed resolution as `UnresolvedName`.
            let param_type = extract_pattern_type_ann(kb, param)
                .or_else(|| expected.and_then(|exp| extract_function_param_type(kb, exp)))
                .unwrap_or_else(|| {
                    let fresh = kb.intern("?param");
                    kb.make_type_var(fresh)
                });
            let mut lambda_env = (*env).clone();
            extend_env_from_pattern(kb, &mut lambda_env, param, Some(param_type));
            // WI-270: if expected is `arrow(param, result, effects)`,
            // decompose and pass `result` to the body. Mismatching
            // shapes (or `None`) leave the body without a hint.
            let body_expected = expected
                .and_then(|exp| extract_function_type_parts(kb, exp))
                .map(|(ret, _)| ret);
            work.push(TypeWorkOp::Build(TypeBuildFrame::LambdaBody {
                occ: Rc::clone(&occ),
                param_type,
                outer_env: env,
            }));
            push_visit(work, body_occ, Rc::new(lambda_env), body_expected, fuel);
        }

        // ── Leaf cases ──────────────────────────────────────────
        Expr::Const(Literal::Int(_)) | Expr::Const(Literal::BigInt(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("Int"), unwrap_env(env), Rc::clone(&occ)),
        )),
        Expr::Const(Literal::Float(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("Float"), unwrap_env(env), Rc::clone(&occ)),
        )),
        Expr::Const(Literal::String(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("String"), unwrap_env(env), Rc::clone(&occ)),
        )),
        Expr::Const(Literal::Bool(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("Bool"), unwrap_env(env), Rc::clone(&occ)),
        )),
        // `Handle(_)` literals are reserved for materialized runtime
        // values; they never appear in surface source. If one shows up,
        // it's a post-elaboration form being re-typed.
        Expr::Const(_) => results.push(Err(TypeError::BottomExpr { span: occ_span })),
        Expr::Ref(sym) => {
            let r = check_bare_ref(kb, &*env, *sym, occ_span, &occ);
            results.push(r);
        }
        Expr::Ident(sym) => {
            let r = check_bare_ref(kb, &*env, *sym, occ_span, &occ);
            results.push(r);
        }
        Expr::VarRef { name } => {
            let r = check_bare_ref(kb, &*env, *name, occ_span, &occ);
            results.push(r);
        }

        // ── Iterative Apply / Constructor ───────────────────────
        // Push child Visits for every arg in reverse so they pop in
        // forward order, then a Build frame that drains the
        // pre-computed arg results and runs the subst / dispatch /
        // classify logic without recursing through `type_check_node`.
        Expr::Apply { functor, pos_args, named_args, .. } => {
            let functor = *functor;
            let pos_args = pos_args.clone();
            let named_args = named_args.clone();
            let occ_clone = Rc::clone(&occ);
            work.push(TypeWorkOp::Build(TypeBuildFrame::Apply {
                occ: occ_clone,
                fn_sym: functor,
                pos_args: pos_args.clone(),
                named_args: named_args.clone(),
                env: Rc::clone(&env),
                expected,
                fuel,
            }));
            for (_, arg) in named_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env), fuel);
            }
            for arg in pos_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env), fuel);
            }
        }
        Expr::Constructor { name, pos_args, named_args } => {
            let name = *name;
            let pos_args = pos_args.clone();
            let named_args = named_args.clone();
            work.push(TypeWorkOp::Build(TypeBuildFrame::Constructor {
                occ: Rc::clone(&occ),
                ctor_sym: name,
                pos_args: pos_args.clone(),
                named_args: named_args.clone(),
                env: Rc::clone(&env),
                span: occ_span,
                expected,
                fuel,
            }));
            for (_, arg) in named_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env), fuel);
            }
            for arg in pos_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env), fuel);
            }
        }

        // ── If / collection literals (WI-285) ───────────────────
        //    Native Build frames, like Apply / Constructor: push child
        //    Visits + a Build frame that drains their results. No
        //    re-entry into `type_check_node`, so a deep else-if chain
        //    (which nests in the else branch) stays on the heap.
        Expr::If { condition, then_branch, else_branch } => {
            let condition = Rc::clone(condition);
            let then_branch = Rc::clone(then_branch);
            let else_branch = Rc::clone(else_branch);
            // Drain order [cond, then, else]: push reversed. The
            // condition is always `Bool` (no hint); both branches share
            // the if's `expected` (WI-270).
            work.push(TypeWorkOp::Build(TypeBuildFrame::IfExpr { occ: Rc::clone(&occ), env: Rc::clone(&env), expected }));
            push_visit(work, else_branch, Rc::clone(&env), expected, fuel);
            push_visit(work, then_branch, Rc::clone(&env), expected, fuel);
            push_visit_no_hint(work, condition, env, fuel);
        }
        Expr::ListLit(elems) => {
            let elems = elems.clone();
            // WI-270: an outer `List[T = X]` makes X each element's
            // expected, and the empty-list fallback.
            let element_hint = expected.and_then(|exp| extract_type_param(kb, exp, "T"));
            work.push(TypeWorkOp::Build(TypeBuildFrame::ListLit {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env),
                element_hint,
                count: elems.len(),
            }));
            for e in elems.iter().rev() {
                push_visit(work, Rc::clone(e), Rc::clone(&env), element_hint, fuel);
            }
        }
        Expr::SetLit(elems) => {
            let elems = elems.clone();
            let element_hint = expected.and_then(|exp| extract_type_param(kb, exp, "T"));
            work.push(TypeWorkOp::Build(TypeBuildFrame::SetLit {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env),
                element_hint,
                count: elems.len(),
            }));
            for e in elems.iter().rev() {
                push_visit(work, Rc::clone(e), Rc::clone(&env), element_hint, fuel);
            }
        }
        Expr::TupleLit { positional, named } => {
            let positional = positional.clone();
            let named = named.clone();
            let named_names: Vec<Symbol> = named.iter().map(|(s, _)| *s).collect();
            // Drain order [pos…, named…]: push named reversed, then
            // positional reversed. Tuple fields take no hint.
            work.push(TypeWorkOp::Build(TypeBuildFrame::TupleLit {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env),
                pos_count: positional.len(),
                named_names,
            }));
            for (_, e) in named.iter().rev() {
                push_visit_no_hint(work, Rc::clone(e), Rc::clone(&env), fuel);
            }
            for e in positional.iter().rev() {
                push_visit_no_hint(work, Rc::clone(e), Rc::clone(&env), fuel);
            }
        }

        // Unresolved logical-var slots in the surface IR are not a
        // typer-level error — the surface programmer wrote `?y` and
        // the loader couldn't pin it to a let/match binding by symbol.
        // Synthesize a fresh type-var so the surrounding apply / let
        // can still type-check; declared signatures resolve the
        // expression's type on the consumer side.
        Expr::Var(_) => {
            let fresh = kb.intern("?logical_var");
            let ty = kb.make_type_var(fresh);
            results.push(Ok(TypeResult::pure(ty, unwrap_env(env), Rc::clone(&occ))));
        }

        // `DotApply` is a pre-dispatch form (WI-278): the `[simp]` dot rules
        // should have rewritten it to an `Apply` / field access before the
        // typer runs. One surviving here is an unresolved member access — the
        // no-match error at its source span. A dedicated diagnostic is part of
        // the dot-dispatch deliverable; for now it falls into `BottomExpr`.
        Expr::DotApply { .. }
        // Post-elaboration forms — emitted by req_insertion, not the
        // surface typer.
        | Expr::HoApply { .. }
        | Expr::Instantiation { .. }
        | Expr::ApplyWithin { .. }
        | Expr::HoApplyWithin { .. }
        | Expr::ConstructorWithin { .. }
        | Expr::LambdaWithin { .. }
        | Expr::RequirementAtSort { .. }
        | Expr::ConstructRequirement { .. }
        | Expr::Bottom => results.push(Err(TypeError::BottomExpr { span: occ_span })),
    }
}

/// WI-283: reassemble `occ` from the children's (possibly-rewritten)
/// `TypeResult.node`s — supplied as the node's child results in
/// `for_each_child` source order, all `Ok` — returning `occ` unchanged
/// (same `Rc`) when no child moved. The mechanism that makes the typer
/// *tree-producing*: a `[simp]` rewrite below a node propagates up as the
/// ancestor chain is rebuilt.
fn reassemble_children(
    occ: &Rc<NodeOccurrence>,
    child_results: &[&Result<TypeResult, TypeError>],
) -> Rc<NodeOccurrence> {
    let nodes: Vec<Rc<NodeOccurrence>> = child_results
        .iter()
        .map(|r| Rc::clone(&r.as_ref().expect("reassemble_children: Ok child").node))
        .collect();
    super::simp_rewrite::reassemble(occ, &nodes)
}

/// [`reassemble_children`] for a contiguous slice of child results (the
/// `for_each_child`-ordered `group` the wrapper frames drain), gated on
/// `simp_enabled`: with no `[simp]` rules nothing was rewritten, so the
/// node is the unchanged `occ` and the per-node collect+walk is skipped.
fn reassemble_if_enabled(
    simp_enabled: bool,
    occ: &Rc<NodeOccurrence>,
    child_results: &[Result<TypeResult, TypeError>],
) -> Rc<NodeOccurrence> {
    if !simp_enabled {
        return Rc::clone(occ);
    }
    let refs: Vec<&Result<TypeResult, TypeError>> = child_results.iter().collect();
    reassemble_children(occ, &refs)
}

/// WI-283: reassemble a `Match` from its (rewritten) scrutinee + branch
/// bodies. Match needs its own path because its **guards are not
/// typed/visited** (so they have no result `node`); they're re-read from
/// `occ` unchanged and interleaved after each body, reproducing
/// `for_each_child(Match)` order ([scrutinee, pattern, body, guard?, …])
/// for the shared `reassemble`. WI-318: `pattern` is now a Pattern-kind
/// occurrence child — typer doesn't rewrite patterns so they're passed
/// through identical (Rc::clone of the original `branch.pattern`).
/// `branch_results` are the branch-body `TypeResult`s (all `Ok`), in
/// branch order. Returns `occ` unchanged when nothing moved.
fn reassemble_match(
    occ: &Rc<NodeOccurrence>,
    scr_node: &Rc<NodeOccurrence>,
    branch_results: &[Result<TypeResult, TypeError>],
) -> Rc<NodeOccurrence> {
    let branches = match occ.as_expr() {
        Some(Expr::Match { branches, .. }) => branches,
        _ => return Rc::clone(occ),
    };
    let mut children: Vec<Rc<NodeOccurrence>> =
        Vec::with_capacity(1 + branch_results.len() * 3);
    children.push(Rc::clone(scr_node));
    for (branch, r) in branches.iter().zip(branch_results.iter()) {
        // WI-318: emit pattern in for_each_child order.
        children.push(Rc::clone(&branch.pattern));
        children.push(Rc::clone(&r.as_ref().expect("reassemble_match: Ok body").node));
        if let Some(g) = &branch.guard {
            children.push(Rc::clone(g));
        }
    }
    super::simp_rewrite::reassemble(occ, &children)
}

/// WI-283: try firing a `[simp]` rule at `node`, fetching the simp pass
/// for synthesized-RHS provenance. The typer's firing site; reuses
/// `simp_rewrite`'s matcher + RHS builder, including its type-directed
/// guard ([`simp_fire_guard_holds`]) — `node`'s children are already typed
/// (bottom-up), so their `min_sort` is available for the guard here.
fn fire_simp(kb: &mut KnowledgeBase, node: &Rc<NodeOccurrence>) -> Option<Rc<NodeOccurrence>> {
    let pass = super::simp_rewrite::simp_pass(kb);
    super::simp_rewrite::try_fire(kb, node, pass)
}

/// Assemble a Let / Match / Lambda result from its child results.
fn build_type(
    kb: &mut KnowledgeBase,
    frame: TypeBuildFrame,
    simp_enabled: bool,
    work: &mut Vec<TypeWorkOp>,
    results: &mut Vec<Result<TypeResult, TypeError>>,
) {
    match frame {
        TypeBuildFrame::Stamp => {
            // The node's freshly-produced result is on top of `results`
            // (this frame sits just under its Visit). Peek — don't
            // consume — and record the inferred type onto the result's
            // (possibly-rewritten) node. Ill-typed nodes (`Err`) are
            // left unstamped (`inferred_type` stays `None`).
            if let Some(Ok(r)) = results.last() {
                r.node.set_inferred_type(r.ty);
            }
        }
        TypeBuildFrame::Apply { occ, fn_sym, pos_args, named_args, env, expected, fuel } => {
            let total = pos_args.len() + named_args.len();
            let drain_start = results.len() - total;
            let mut arg_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            let named_results = arg_results.split_off(pos_args.len());
            let pos_results = arg_results;
            // WI-283: when `[simp]` rules exist, reassemble this Apply from
            // its children's (possibly-rewritten) `.node`s and fire a rule
            // at it *before* classifying (a fired node is discarded, so
            // classifying it would be wasted); on a fire, re-type the RHS so
            // chains/cascades reach fixpoint and the produced apply gets
            // classified for req_insertion. With no `[simp]` rules the node
            // is the unchanged input occ — no reassembly, no per-node cost.
            let node = if simp_enabled {
                // Surface an ill-typed child first — we need `Ok` children to
                // read their `.node` (check_apply_iter aggregates the same).
                if let Err(e) = collect_arg_errors(pos_results.iter().chain(named_results.iter())) {
                    results.push(Err(e));
                    return;
                }
                let child_refs: Vec<&Result<TypeResult, TypeError>> =
                    pos_results.iter().chain(named_results.iter()).collect();
                let node = reassemble_children(&occ, &child_refs);
                // Fire only while fuel remains; on a fire, re-`Visit` the RHS
                // with `fuel - 1` on this same work-stack (no host recursion)
                // so the chain is bounded — a non-terminating rule bottoms
                // out at fuel 0 leaving a partial redex, not a stack overflow.
                if fuel > 0 {
                    if let Some(rhs) = fire_simp(kb, &node) {
                        push_visit(work, rhs, env, expected, fuel - 1);
                        return;
                    }
                }
                node
            } else {
                occ
            };
            let span = Some(node.span.span);
            let r = check_apply_iter(
                kb, &*env, &node, fn_sym, &pos_args, &named_args,
                &pos_results, &named_results, span, expected,
            );
            results.push(r);
        }
        TypeBuildFrame::Constructor { occ, ctor_sym, pos_args, named_args, env, span, expected, fuel } => {
            let total = pos_args.len() + named_args.len();
            let drain_start = results.len() - total;
            let mut arg_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            let named_results = arg_results.split_off(pos_args.len());
            let pos_results = arg_results;
            // WI-283: reassemble + fire (gated on `[simp]` rules existing) —
            // mirrors the Apply arm (a `[simp]` rule may target a domain
            // constructor too, e.g. `transpose(transpose(?m)) = ?m`).
            let node = if simp_enabled {
                if let Err(e) = collect_arg_errors(pos_results.iter().chain(named_results.iter())) {
                    results.push(Err(e));
                    return;
                }
                let child_refs: Vec<&Result<TypeResult, TypeError>> =
                    pos_results.iter().chain(named_results.iter()).collect();
                let node = reassemble_children(&occ, &child_refs);
                if fuel > 0 {
                    if let Some(rhs) = fire_simp(kb, &node) {
                        push_visit(work, rhs, env, expected, fuel - 1);
                        return;
                    }
                }
                node
            } else {
                occ
            };
            let r = check_constructor_iter(
                kb, &*env, ctor_sym, &pos_args, &named_args,
                &pos_results, &named_results, span, expected, &node,
            );
            results.push(r);
        }
        TypeBuildFrame::LetAfterValue { occ, pattern, annotation, body_occ, body_expected, fuel } => {
            let value_r = results.pop().expect("LetAfterValue: missing value result");
            // Propagate failure up rather than typing the body under a
            // synthesized env — see WI-204 feedback (no fallbacks).
            let r = match value_r {
                Ok(r) => r,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };
            // WI-283: keep the value's (possibly-rewritten) node to
            // reassemble the `Let` at `LetFinal` (its result is consumed here).
            let value_node = Rc::clone(&r.node);
            let (value_ty, value_effects, mut ext_env) =
                (Some(r.ty), r.effects, r.env);
            let bound_ty = annotation.or(value_ty);
            extend_env_from_pattern(kb, &mut ext_env, pattern, bound_ty);
            if let Some(var_name) = extract_pattern_var_name(kb, pattern) {
                ext_env.declare_local_resource(var_name);
            }
            work.push(TypeWorkOp::Build(TypeBuildFrame::LetFinal { occ, value_node, value_effects }));
            push_visit(work, body_occ, Rc::new(ext_env), body_expected, fuel);
        }
        TypeBuildFrame::LetFinal { occ, value_node, value_effects } => {
            let body_r = results.pop().expect("LetFinal: missing body result");
            let body_r = match body_r {
                Ok(r) => r,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };
            let effects = merge_effects(&value_effects, &body_r.effects);
            // WI-283: reassemble the `Let` from [pattern, value, body]
            // (`for_each_child(Let)` order, WI-318 added pattern) so a
            // rewrite in any of them propagates. The pattern itself is
            // passed through unchanged (typer doesn't rewrite patterns).
            let node = if simp_enabled {
                let pattern_clone = match occ.as_expr() {
                    Some(Expr::Let { pattern, .. }) => Rc::clone(pattern),
                    _ => Rc::clone(&occ), // defensive; unreachable for Let frame
                };
                super::simp_rewrite::reassemble(
                    &occ,
                    &[pattern_clone, value_node, Rc::clone(&body_r.node)],
                )
            } else {
                Rc::clone(&occ)
            };
            results.push(Ok(TypeResult {
                ty: body_r.ty,
                env: body_r.env,
                effects,
                node,
            }));
        }
        TypeBuildFrame::MatchAfterScrutinee { occ, branches, outer_env, body_expected, fuel } => {
            let scr_r = results.pop().expect("MatchAfterScrutinee: missing scrutinee result");
            let scr_ty = scr_r.as_ref().ok().map(|r| r.ty);
            let scr_effects = scr_r.as_ref().ok().map(|r| r.effects.clone()).unwrap_or_default();
            // WI-283: the scrutinee's (possibly-rewritten) node for
            // reassembly — falling back to the original when it didn't type.
            let scr_node = scr_r
                .as_ref()
                .ok()
                .map(|r| Rc::clone(&r.node))
                .unwrap_or_else(|| match occ.as_expr() {
                    Some(Expr::Match { scrutinee, .. }) => Rc::clone(scrutinee),
                    _ => Rc::clone(&occ),
                });

            // Coverage / exhaustiveness inputs are derived purely from
            // pattern terms, independent of body type-checks — compute
            // here so MatchFinal can run the check without re-walking.
            let mut covered_entities: Vec<Symbol> = Vec::new();
            let mut has_wildcard = false;
            // Constructors of the scrutinee sort. A bare `case red` parses as a
            // var_pattern (the name could be a binding or a nullary
            // constructor); recognizing it as a constructor needs the
            // candidate set. The scrutinee sort's own constructors are that
            // set — resolving against them replaces the removed global
            // short→qualified fallback the late lookup relied on.
            let scrutinee_ctors: Vec<Symbol> = scr_ty
                .and_then(|sty| extract_sort_ref_sym(kb, sty))
                .map(|s| {
                    let sort_term = kb.make_name_term_from_sym(s);
                    sort_constructor_syms(kb, sort_term)
                })
                .unwrap_or_default();
            let mut branch_envs: Vec<Rc<TypingEnv>> = Vec::with_capacity(branches.len());
            for branch in &branches {
                // WI-318: branch.pattern is a Pattern-kind occurrence;
                // bridge to TermId for the existing term-based helpers.
                let pattern_tid = super::node_occurrence::pattern_to_term(kb, &branch.pattern);
                collect_covered_entities(
                    kb,
                    pattern_tid,
                    &scrutinee_ctors,
                    &mut covered_entities,
                    &mut has_wildcard,
                );
                let mut branch_env = (*outer_env).clone();
                extend_env_from_pattern(kb, &mut branch_env, pattern_tid, scr_ty);
                branch_envs.push(Rc::new(branch_env));
            }

            let branch_count = branches.len();
            // Materialize Visit envs first (Rc::clone from branch_envs),
            // then move branch_envs into the MatchFinal frame.
            let visit_envs: Vec<Rc<TypingEnv>> =
                branch_envs.iter().map(Rc::clone).collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::MatchFinal {
                occ,
                scr_node,
                scr_effects,
                branch_envs,
                branch_count,
                outer_env,
                scr_ty,
                covered_entities,
                has_wildcard,
                body_expected,
            }));
            for (branch, env) in branches.iter().zip(visit_envs.into_iter()).rev() {
                push_visit(work, Rc::clone(&branch.body), env, body_expected, fuel);
            }
        }
        TypeBuildFrame::MatchFinal {
            occ,
            scr_node,
            scr_effects,
            branch_envs,
            branch_count,
            outer_env,
            scr_ty,
            covered_entities,
            has_wildcard,
            body_expected,
        } => {
            let drain_start = results.len() - branch_count;
            let branch_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(branch_results.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble the `Match` from the (rewritten) scrutinee
            // and branch bodies (guards re-read from `occ`, unchanged) before
            // `branch_results` is consumed below.
            let node = if simp_enabled {
                reassemble_match(&occ, &scr_node, &branch_results)
            } else {
                Rc::clone(&occ)
            };
            let mut effects = scr_effects;
            let mut branch_tys: Vec<(TermId, Option<Span>)> =
                Vec::with_capacity(branch_count);
            for (i, body_r) in branch_results.into_iter().enumerate() {
                let body_r = body_r.expect("aggregator");
                branch_tys.push((body_r.ty, Some(body_r.node.span.span)));
                // Filter effects against this branch's locals so
                // pattern-bound resources don't leak past the case
                // arm (their bindings live only inside the branch).
                let branch_external = external_effects(kb, &*branch_envs[i], &body_r.effects);
                effects = merge_effects(&effects, &branch_external);
            }

            // WI-287: the match's result type accounts for *every* branch,
            // not just branch 0. In checked mode (an expected type flowed
            // in) each branch must conform to it; in synthesis mode the
            // result is the join (a common supertype) of the branch types,
            // and branches with no common supertype are a type error rather
            // than being silently typed as branch 0.
            let result_ty = match compute_branch_join_type(kb, &branch_tys, body_expected, "match") {
                Ok(ty) => ty,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };

            let mut result_env = (*outer_env).clone();
            if !has_wildcard {
                if let Some(sty) = scr_ty {
                    if let Some(sort_sym) = extract_sort_ref_sym(kb, sty) {
                        let sort_term = kb.make_name_term_from_sym(sort_sym);
                        if kb.sort_kind(sort_term) == Some(SortKind::Enum) {
                            let all_entities = sort_constructor_syms(kb, sort_term);
                            let missing: Vec<String> = all_entities
                                .iter()
                                .filter(|e| {
                                    !covered_entities
                                        .iter()
                                        .any(|c| same_symbol(kb, *c, **e))
                                })
                                .map(|s| kb.resolve_sym(*s).to_string())
                                .collect();
                            if !missing.is_empty() {
                                let sort_name = kb.resolve_sym(sort_sym);
                                result_env.diagnostics.push(format!(
                                    "non-exhaustive match on {}: missing {}",
                                    sort_name,
                                    missing.join(", ")
                                ));
                            }
                        }
                    }
                }
            }
            results.push(Ok(TypeResult { ty: result_ty, env: result_env, effects, node }));
        }
        TypeBuildFrame::LambdaBody { occ, param_type, outer_env } => {
            let body_r = results.pop().expect("LambdaBody: missing body result");
            // Build arrow(param, result, effects) type term. `param_type`
            // is the exact type the param was bound to in the body env
            // (see the `Expr::Lambda` visit case), so the arrow's param
            // slot and the body's view of the param agree.
            let a_val = param_type;
            let b_val = body_r.as_ref().ok().map(|r| r.ty).unwrap_or_else(|| {
                let fresh = kb.intern("?result");
                kb.make_type_var(fresh)
            });
            let body_effects = body_r
                .as_ref()
                .ok()
                .map(|r| r.effects.clone())
                .unwrap_or_default();
            let fn_type = kb.make_arrow_type(a_val, b_val, &body_effects);
            // Creating a lambda is itself pure — body effects live in the type.
            // If the body itself errored, propagate that error rather than
            // synthesizing a lambda over an ill-typed body.
            match body_r {
                // WI-283: reassemble the lambda from its [param, body]
                // (WI-318 added param) so a `[simp]` rewrite in either
                // propagates up. The param is passed through unchanged
                // (typer doesn't rewrite patterns).
                Ok(ref r) => {
                    let node = if simp_enabled {
                        let param_clone = match occ.as_expr() {
                            Some(Expr::Lambda { param, .. }) => Rc::clone(param),
                            _ => Rc::clone(&occ), // defensive; unreachable
                        };
                        super::simp_rewrite::reassemble(&occ, &[param_clone, Rc::clone(&r.node)])
                    } else {
                        Rc::clone(&occ)
                    };
                    results.push(Ok(TypeResult::pure(fn_type, unwrap_env(outer_env), node)))
                }
                Err(e) => results.push(Err(e)),
            }
        }
        TypeBuildFrame::IfExpr { occ, env, expected } => {
            // Children drained in [condition, then, else] order.
            let drain_start = results.len() - 3;
            let group: Vec<Result<TypeResult, TypeError>> = results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(group.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble from [cond, then, else] (before consuming
            // `group`) so a `[simp]` rewrite inside a branch propagates up.
            let node = reassemble_if_enabled(simp_enabled, &occ, &group);
            let mut it = group.into_iter().map(|r| r.expect("aggregator"));
            let cond_r = it.next().unwrap();
            let then_r = it.next().unwrap();
            let else_r = it.next().unwrap();
            let mut effects = Vec::new();
            effects = merge_effects(&effects, &cond_r.effects);
            effects = merge_effects(&effects, &then_r.effects);
            effects = merge_effects(&effects, &else_r.effects);
            // WI-287: the if's type is the join of both branches (checked
            // against `expected` when present), not just the then-branch
            // type — an `if` with incompatible arms is otherwise silently
            // typed as its then-branch.
            let branch_tys = [
                (then_r.ty, Some(then_r.node.span.span)),
                (else_r.ty, Some(else_r.node.span.span)),
            ];
            let ty = match compute_branch_join_type(kb, &branch_tys, expected, "if") {
                Ok(ty) => ty,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };
            results.push(Ok(TypeResult { ty, env: unwrap_env(env), effects, node }));
        }
        TypeBuildFrame::ListLit { occ, env, element_hint, count } => {
            let drain_start = results.len() - count;
            let group: Vec<Result<TypeResult, TypeError>> = results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(group.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble from the (possibly-rewritten) elements.
            let node = reassemble_if_enabled(simp_enabled, &occ, &group);
            let mut effects = Vec::new();
            let mut element_type: Option<TermId> = element_hint;
            for r in group {
                let r = r.expect("aggregator");
                if element_type.is_none() {
                    element_type = Some(r.ty);
                }
                effects = merge_effects(&effects, &r.effects);
            }
            let t_val = element_type.unwrap_or_else(|| {
                let fresh = kb.intern("?T");
                kb.make_type_var(fresh)
            });
            let list_base = kb.make_sort_ref_by_name("List");
            let t_sym = kb.intern("T");
            let list_type = kb.make_parameterized_type(list_base, &[(t_sym, t_val)]);
            results.push(Ok(TypeResult { ty: list_type, env: unwrap_env(env), effects, node }));
        }
        TypeBuildFrame::SetLit { occ, env, element_hint, count } => {
            let drain_start = results.len() - count;
            let group: Vec<Result<TypeResult, TypeError>> = results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(group.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble from the (possibly-rewritten) elements.
            let node = reassemble_if_enabled(simp_enabled, &occ, &group);
            let mut effects = Vec::new();
            let mut element_type: Option<TermId> = element_hint;
            for r in group {
                let r = r.expect("aggregator");
                if element_type.is_none() {
                    element_type = Some(r.ty);
                }
                effects = merge_effects(&effects, &r.effects);
            }
            let t_val = element_type.unwrap_or_else(|| {
                let fresh = kb.intern("?T");
                kb.make_type_var(fresh)
            });
            let set_base = kb.make_sort_ref_by_name("Set");
            let t_sym = kb.intern("T");
            let set_type = kb.make_parameterized_type(set_base, &[(t_sym, t_val)]);
            results.push(Ok(TypeResult { ty: set_type, env: unwrap_env(env), effects, node }));
        }
        TypeBuildFrame::TupleLit { occ, env, pos_count, named_names } => {
            let total = pos_count + named_names.len();
            let drain_start = results.len() - total;
            let group: Vec<Result<TypeResult, TypeError>> = results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(group.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble from [positional…, named…] elements.
            let node = reassemble_if_enabled(simp_enabled, &occ, &group);
            let mut effects = Vec::new();
            let mut field_types: Vec<(Symbol, TermId)> = Vec::new();
            let mut it = group.into_iter();
            for i in 0..pos_count {
                let r = it.next().unwrap().expect("aggregator");
                let field_name = kb.intern(&format!("_{}", i));
                field_types.push((field_name, r.ty));
                effects = merge_effects(&effects, &r.effects);
            }
            for name in named_names {
                let r = it.next().unwrap().expect("aggregator");
                field_types.push((name, r.ty));
                effects = merge_effects(&effects, &r.effects);
            }
            let tuple_type = kb.make_named_tuple_type(&field_types);
            results.push(Ok(TypeResult { ty: tuple_type, env: unwrap_env(env), effects, node }));
        }
    }
}

/// Attach a call-site `CallClass` to its NodeOccurrence's `RefCell`
/// — the canonical channel for downstream consumers post-WI-251.
/// `req_insertion::run` walks `kb.op_bodies` and reads the
/// classification off each Apply NodeOccurrence; eval reads it
/// directly from the same RefCell at dispatch time.
fn classify(_kb: &mut KnowledgeBase, occ: &Rc<NodeOccurrence>, class: CallClass) {
    occ.set_classification(class);
}

// ── Expression form checkers ───────────────────────────────────

/// apply(fn, args): type-check with type parameter instantiation.
/// 1. fn is a known operation → unify arg types with param types, resolve return type
/// 2. fn is a variable with arrow type → extract return type and effects
/// Non-recursive Apply checker. Identical to the legacy `check_apply`
/// but reads per-arg `TypeResult`s from `pos_results` / `named_results`
/// (pre-computed by the iterative typer's Build phase) instead of
/// calling `type_check_node` itself. This is the function the iterative
/// `Build::Apply` arm calls.
fn check_apply_iter(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    fn_sym: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    span: Option<Span>,
    expected: Option<TermId>,
) -> Result<TypeResult, TypeError> {
    // Surface any sub-expression failure before continuing. Aggregate
    // sibling errors so a multi-arg call reports every ill-typed arg
    // in a single diagnostic rather than the first.
    collect_arg_errors(pos_results.iter().chain(named_results.iter()))?;

    // Materializer fallback: bare-functor constructor invocations land
    // in `Apply`; route them through the constructor checker so
    // type-param inference still fires.
    if kb.is_constructor_symbol(fn_sym) {
        return check_constructor_iter(
            kb, env, fn_sym, pos_args, named_args, pos_results, named_results, span, expected, occ,
        );
    }

    // Path 1: known operation — unify args with params to instantiate type params
    if let Some(op) = lookup_operation_info_full(kb, fn_sym) {
        let mut subst = Substitution::new();
        // WI-269 Phase D: explicit call-site `op[bindings]` bindings
        // seed the substitution first. Returns `NoSuchTypeParam` on
        // an unknown binding name.
        seed_op_type_args(kb, &mut subst, &op, occ, fn_sym, span)?;
        // WI-270: caller-side expected type seeds the substitution via
        // `op.return_type` before argument inference. With caller
        // context (`let v: Option[WorkItem] = term_as_entity(t)`) the
        // op's `?E` Var binds to WorkItem here, and the post-arg
        // unconstrained-param check sees it as pinned.
        if let Some(exp) = expected {
            unify_types(kb, &mut subst, op.return_type, exp);
        }
        let mut arg_effects: Vec<TermId> = Vec::new();
        let mut param_to_arg_sym: HashMap<Symbol, Symbol> = HashMap::new();

        for (i, arg_occ) in pos_args.iter().enumerate() {
            if let Some(arg_var_sym) = extract_var_ref_sym_node(arg_occ) {
                if let Some(&(param_sym, _)) = op.params.get(i) {
                    param_to_arg_sym.insert(param_sym, arg_var_sym);
                }
            }
            if let Ok(ref arg_result) = pos_results[i] {
                if let Some(&(_, param_type)) = op.params.get(i) {
                    unify_types(kb, &mut subst, arg_result.ty, param_type);
                }
                arg_effects = merge_effects(&arg_effects, &arg_result.effects);
            }
        }

        for (i, (arg_name, arg_occ)) in named_args.iter().enumerate() {
            if let Some(arg_var_sym) = extract_var_ref_sym_node(arg_occ) {
                param_to_arg_sym.insert(*arg_name, arg_var_sym);
            }
            if let Ok(ref arg_result) = named_results[i] {
                if let Some(param_type) = op.params.iter()
                    .find(|(s, _)| *s == *arg_name)
                    .map(|(_, t)| *t)
                {
                    unify_types(kb, &mut subst, arg_result.ty, param_type);
                }
                arg_effects = merge_effects(&arg_effects, &arg_result.effects);
            }
        }

        // Apply param-name substitution to op.effects (WI-209), then
        // walk each through `walk_type_deep` so type-var bindings from
        // arg-unification propagate into nested positions in the effect
        // (e.g. `Stream.head`'s `effects E` → `Error` once `vid_E` is
        // bound by `unify_parameterized_with_sort_ref`). Skip the
        // param-name walk when no var_ref args were seen.
        let pre_substituted: Vec<TermId> = if param_to_arg_sym.is_empty() {
            op.effects.clone()
        } else {
            op.effects
                .iter()
                .map(|e| substitute_ref_syms(kb, *e, &param_to_arg_sym))
                .collect()
        };
        let substituted_op_effects: Vec<TermId> = pre_substituted
            .iter()
            .map(|e| walk_type_deep(kb, &subst, *e))
            .collect();
        let effects = merge_effects(&substituted_op_effects, &arg_effects);

        // Resolve return type deeply so `Option[T = Var(vid_T)]`
        // collapses to `Option[T = Term]` once `vid_T` is bound.
        let resolved_ret = walk_type_deep(kb, &subst, op.return_type);

        // WI-270: every declared op type-parameter must be pinned by
        // some combination of: explicit `[bindings]`, caller-side
        // `expected`, or argument unification. If a type-param's Var
        // is still unbound after all that, the call would silently
        // produce a `Var(?T)`-bearing return type; surface this as a
        // named diagnostic so the user can fix it by writing
        // `op[T = …](…)`. Replaces the WI-269 Phase D silent-drop
        // marker.
        check_unconstrained_type_params(kb, &subst, &op, fn_sym, span)?;

        // Write resolved op type-arg values back to the apply
        // occurrence so the eval can install them on the callee's
        // `Frame.type_args` (WI-272). Positional, in the callee's
        // `[T1, T2, ...]` declaration order; each entry pairs the
        // declared name symbol with the term the substitution walked
        // its Var to. Skipped for ops without `[...]` (the common
        // case) — `resolved_type_args` defaults to empty.
        if !op.type_params.is_empty() {
            let mut resolved: Vec<(Symbol, TermId)> = Vec::with_capacity(op.type_params.len());
            for (name, var_term) in &op.type_params {
                let walked = walk_type_deep(kb, &subst, *var_term);
                resolved.push((*name, walked));
            }
            occ.set_resolved_type_args(resolved);
        }

        // WI-210 phase 3 dispatch (proposal 038): if `fn_sym` is a spec
        // op (declared without body on a parametric sort), look up the
        // unique impl op based on the per-call substitution. The proposal-
        // 038 unification of builtin-sort symbols (Int as the same Symbol
        // whether referenced bare or via anthill.prelude.Int) makes
        // candidate matching deterministic — `fact Numeric[T = Int]` in
        // the rustland binding emits a SortProvidesInfo whose binding
        // value resolves to the same Int sort as the per-call subst sees.
        if let Some(spec_sort) = lookup_spec_op_dispatch(kb, fn_sym) {
            // The op's short name (e.g. "add" for "anthill.prelude.Numeric.add")
            // joins with the impl sort to find the impl operation symbol.
            let op_qn = kb.qualified_name_of(fn_sym).to_string();
            let op_short_sym = kb.intern(short_name_of(&op_qn));
            let enclosing_requires = env.enclosing_requires().unwrap_or(&[]);
            let (outcome, resolved_tree) = dispatch_spec_op_cached(
                kb, &subst, spec_sort, op_short_sym, enclosing_requires,
            );
            let enclosing_sort = env.enclosing_sort();
            match outcome {
                DispatchOutcome::NoCandidates => {}
                DispatchOutcome::Unique(impl_op_sym) => {
                    // WI-231: tag the call site. The requirement-
                    // insertion pass (`req_insertion::run`) reads the
                    // side-table and emits the actual IR rewrite — no
                    // inline emission here. WI-218 / WI-222 Phase E (i) /
                    // WI-228 semantics encoded by which CallClass
                    // variant we tag.
                    //
                    // WI-237: only rewrite to a *concrete* impl op — one
                    // that has a runnable body. A body-less `impl_op_sym`
                    // is a spec-level declaration (e.g. the auto-bound
                    // `anthill.prelude.String.eq` a `provides` block
                    // registers, or a derived `Ordered.lt` whose body
                    // lives in a separate `rule {}`). Rewriting the call
                    // to it produces a runtime `unknown operation`
                    // (no body, no builtin) or — worse — mis-resolves to
                    // the wrong sibling op. Leaving the call as the spec
                    // op lets the runtime resolve it via its registered
                    // builtin or the spec's own derived rule.
                    if impl_op_sym != fn_sym
                        && op_has_runnable_body(kb, impl_op_sym)
                    {
                        let impl_sort = impl_parent_of_op(kb, impl_op_sym);
                        let needs_reqs = impl_sort
                            .map(|s| !requires_chain(kb, s).is_empty())
                            .unwrap_or(false);
                        let class = if needs_reqs {
                            CallClass::ConcreteApplyWithin {
                                fn_target_sym: impl_op_sym,
                                callee_spec_sort: impl_sort.unwrap(),
                                spec_op_sym: fn_sym,
                                enclosing_sort,
                                resolved_tree: resolved_tree.clone(),
                            }
                        } else {
                            CallClass::PinNow {
                                spec_op_sym: fn_sym,
                                impl_op_sym,
                            }
                        };
                        classify(kb, occ, class);
                    }
                }
                DispatchOutcome::NoMatch => {
                    return Err(TypeError::DispatchNoMatch { span, op: fn_sym });
                }
                DispatchOutcome::Ambiguous => {
                    return Err(TypeError::DispatchAmbiguous { span, op: fn_sym });
                }
                DispatchOutcome::Deferred => {
                    if let Some(slot) =
                        find_requires_slot(kb, &subst, spec_sort, enclosing_requires)
                    {
                        // WI-232: capture the matched entry so
                        // req_insertion::run can read it directly,
                        // without re-indexing the chain at emit time.
                        let resolved_spec = enclosing_requires[slot].clone();
                        classify(
                            kb,
                            occ,
                            CallClass::DeferToRequirement {
                                spec_op_sym: fn_sym,
                                op_short_sym,
                                resolved_spec,
                                slot,
                                enclosing_sort,
                            },
                        );
                    }
                }
            }
        } else {
            // WI-222 Phase E (i) Direct case: fn_sym is not a spec op.
            // If its parent sort declares any `requires`, tag for an
            // `apply_within(fn = Ref(fn_sym), …)` rewrite. Otherwise no
            // tag and the call stays as plain apply.
            if let Some(parent_sym) = impl_parent_of_op(kb, fn_sym) {
                if !requires_chain(kb, parent_sym).is_empty() {
                    classify(
                        kb,
                        occ,
                        CallClass::ConcreteApplyWithin {
                            fn_target_sym: fn_sym,
                            callee_spec_sort: parent_sym,
                            spec_op_sym: fn_sym,
                            enclosing_sort: env.enclosing_sort(),
                            resolved_tree: None,
                        },
                    );
                }
            }
        }

        return Ok(TypeResult { ty: resolved_ret, env: env.clone(), effects, node: Rc::clone(occ) });
    }

    // Path 2: variable with arrow type
    if let Some(fn_type_tid) = env.lookup_var(fn_sym) {
        if let Some((ret_type, effects)) = extract_function_type_parts(kb, fn_type_tid) {
            return Ok(TypeResult { ty: ret_type, env: env.clone(), effects, node: Rc::clone(occ) });
        }
    }

    // Path 3: unknown functor — collect arg effects (from pre-computed
    // results) and fall back to the declared return type if any.
    let mut effects: Vec<TermId> = Vec::new();
    for r in pos_results.iter().chain(named_results.iter()) {
        if let Ok(r) = r {
            effects = merge_effects(&effects, &r.effects);
        }
    }
    let _ = pos_args;
    let _ = named_args;
    lookup_operation_return_type(kb, fn_sym)
        .map(|ty| TypeResult { ty, env: env.clone(), effects, node: Rc::clone(occ) })
        .ok_or(TypeError::UnknownApplyFunctor { span, name: fn_sym })
}

/// WI-218: allocate a rewritten `apply` term with `fn = impl_op_sym`,
/// keeping the same args. Record (original → rewritten) in
/// `kb.dispatch_rewrites` and (rewritten → spec_op_sym) in
/// `kb.dispatch_origin`. The post-typing rewrite pass uses these maps
/// to substitute the rewritten term into operation bodies bottom-up.
pub(crate) fn record_apply_rewrite(
    kb: &mut KnowledgeBase,
    original_apply: TermId,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    pos_args: &SmallVec<[TermId; 4]>,
    spec_op_sym: Symbol,
    impl_op_sym: Symbol,
) {
    if kb.dispatch_rewrites.contains_key(&original_apply) {
        // Idempotent — the same apply term may be type-checked through
        // multiple paths (e.g. when the typer is invoked twice on a
        // body). The first rewrite is canonical.
        return;
    }
    // Reuse the apply term's existing functor symbol rather than re-interning
    // the short name "apply" — the latter risks producing a different Symbol
    // value than the loader's `anthill.reflect.Expr.apply`, which the eval's
    // reflect-symbol cache compares against.
    let apply_functor = match kb.get_term(original_apply) {
        Term::Fn { functor, .. } => *functor,
        _ => return,
    };
    let fn_arg = kb.intern("fn");
    let new_fn_ref = kb.alloc(Term::Ref(impl_op_sym));
    let new_named: SmallVec<[(Symbol, TermId); 2]> = named_args
        .iter()
        .map(|(s, t)| if *s == fn_arg { (*s, new_fn_ref) } else { (*s, *t) })
        .collect();
    let rewritten_apply = kb.alloc(Term::Fn {
        functor: apply_functor,
        pos_args: pos_args.clone(),
        named_args: new_named,
    });
    kb.record_dispatch_rewrite(original_apply, rewritten_apply, spec_op_sym);
}

/// Last segment of a dotted qualified name (`foo.bar.baz` → `baz`).
/// Returns the input unchanged when it has no dot.
fn short_name_of(qn: &str) -> &str {
    qn.rsplit_once('.').map(|(_, s)| s).unwrap_or(qn)
}

/// Resolve `op_sym`'s parent sort by stripping the last qualified-name
/// segment. The parent owns the op's `requires_chain` — the right
/// `callee_spec_sort` to feed into `build_projected_requirements_list`
/// (WI-228 fix: the previous Pin-now path passed the spec sort instead
/// of the impl's parent, so projections walked an empty chain).
pub fn impl_parent_of_op(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    let qn = kb.qualified_name_of(op_sym);
    let (parent_qn, _) = qn.rsplit_once('.')?;
    kb.try_resolve_symbol(parent_qn)
}

/// True iff `a` and `b` denote the same logical sort / symbol.
///
/// Identity is the resolved `Symbol`; this helper adds two name-based
/// bridges that exact `Symbol ==` misses:
///
/// 1. **Differently-interned resolved copies** of the same sort compare
///    equal via their (unique) qualified name.
/// 2. **Resolved ↔ unresolved** of the same sort: some reflection facts
///    still carry unresolved short-name symbols (`qualified_name_of`
///    returns just the short name for those). A bare short name matches
///    the last segment of a qualified name.
///
/// Crucially it does NOT match two *fully-qualified* names that merely
/// share a last segment — `anthill.cli.Main` and `anthill.todo.Main`
/// stay distinct.
pub fn same_symbol(kb: &KnowledgeBase, a: Symbol, b: Symbol) -> bool {
    if a == b {
        return true;
    }
    let aq = kb.qualified_name_of(a);
    let bq = kb.qualified_name_of(b);
    if aq == bq {
        return true;
    }
    let a_bare = !aq.contains('.');
    let b_bare = !bq.contains('.');
    match (a_bare, b_bare) {
        (true, false) => bq.rsplit('.').next() == Some(aq),
        (false, true) => aq.rsplit('.').next() == Some(bq),
        _ => false,
    }
}

/// WI-227: interned stdlib symbols + field names needed to allocate
/// the three requirement-projection IR forms. Resolved once at the
/// entry point so the recursive search doesn't re-look-up per dep.
/// `pub` only so the WI-227 test file can drive `build_dep_projection`
/// directly with synthetic inputs.
pub struct ProjectionSyms {
    /// `anthill.reflect.Expr.var_ref` — named requirement-param read
    /// (names model; replaced the positional `requirement_at_current`).
    pub var_ref: Symbol,
    /// `anthill.reflect.Expr.requirement_at_sort`
    pub ras: Symbol,
    /// `anthill.reflect.Expr.construct_requirement`
    pub construct: Symbol,
    /// `anthill.prelude.List.nil`
    pub nil: Symbol,
    /// `anthill.prelude.List.cons`
    pub cons: Symbol,
    pub slot: Symbol,
    pub chain: Symbol,
    pub impl_functor: Symbol,
    pub requirements: Symbol,
    pub head: Symbol,
    pub tail: Symbol,
    /// `name` field of `var_ref`.
    pub name: Symbol,
}

impl ProjectionSyms {
    pub fn resolve(kb: &mut KnowledgeBase) -> Option<Self> {
        Some(Self {
            var_ref: kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")?,
            ras: kb.try_resolve_symbol("anthill.reflect.Expr.requirement_at_sort")?,
            construct: kb.try_resolve_symbol("anthill.reflect.Expr.construct_requirement")?,
            nil: kb.try_resolve_symbol("anthill.prelude.List.nil")?,
            cons: kb.try_resolve_symbol("anthill.prelude.List.cons")?,
            slot: kb.intern("slot"),
            chain: kb.intern("chain"),
            impl_functor: kb.intern("impl_functor"),
            requirements: kb.intern("requirements"),
            head: kb.intern("head"),
            tail: kb.intern("tail"),
            name: kb.intern("name"),
        })
    }
}

/// WI-234 (Model 1): build the dispatching-dict expression for the
/// Direct path — `construct_requirement(callee_spec_sort, [<projections
/// per callee chain>])`. Each projection sources its sub-instance from
/// `caller_requires` via the three-strategy search in
/// `build_dep_projection`. The caller wraps the result in a
/// single-entry cons-list to form the `apply_within.requirements`
/// channel.
fn build_dispatching_dict_direct(
    kb: &mut KnowledgeBase,
    callee_spec_sort: Symbol,
    caller_sort: Option<Symbol>,
    caller_requires: &[RequiresEntry],
    syms: &ProjectionSyms,
) -> Option<TermId> {
    let callee_chain = requires_chain(kb, callee_spec_sort);
    // Hoist Strategy 2's per-slot `requires_chain` walk out of the dep
    // loop: it depends only on `caller_requires`, not on the current
    // dep, so the worst-case cost drops from O(deps × slots × |SortRequiresInfo|)
    // to O(slots × |SortRequiresInfo|).
    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| requires_chain(kb, ar.required_sort))
        .collect();
    let mut proj_terms: Vec<TermId> = Vec::with_capacity(callee_chain.len());
    for dep in &callee_chain {
        if let Some(t) = build_dep_projection(
            kb, dep, caller_sort, caller_requires, &caller_sub_chains, syms,
        ) {
            proj_terms.push(t);
        }
    }
    let sub_reqs_list = super::load::build_cons_list(
        kb, &proj_terms, syms.nil, syms.cons, syms.head, syms.tail,
    );
    Some(build_construct_requirement(kb, syms, callee_spec_sort, sub_reqs_list))
}

/// Wrap a single dispatching-dict expression in the single-entry
/// cons-list shape used for `apply_within.requirements` under Model 1.
fn wrap_dispatch_channel(
    kb: &mut KnowledgeBase,
    dict_term: TermId,
    syms: &ProjectionSyms,
) -> TermId {
    super::load::build_cons_list(
        kb, &[dict_term], syms.nil, syms.cons, syms.head, syms.tail,
    )
}

/// WI-227: recursively search for an IR projection that delivers a
/// requirement value satisfying `dep` at runtime, given `caller_requires`
/// as the caller's frame-level requirement chain. Tries named-param
/// match, then nested-handle match via `caller_sub_chains[i]`, then SLD
/// resolution against `SortProvidesInfo`. `caller_sub_chains` must be
/// `[requires_chain(c.required_sort) for c in caller_requires]` — the
/// nested-search index, computed once by the caller.
///
/// `caller_sort` is the enclosing op's parent sort — needed to turn a
/// caller-chain index into the synthesized `__req_*` param name
/// (`req_name_for_chain_index`). It is `None` only for ops with no
/// enclosing sort, in which case `caller_requires` is empty and
/// Strategies 1 & 2 never fire.
///
/// `pub` so the WI-227 test file can drive each strategy synthetically.
///
/// Reference: docs/design/operation-call-model.md §"Two primitives",
/// §"Call rewrite cases".
pub fn build_dep_projection(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    caller_sort: Option<Symbol>,
    caller_requires: &[RequiresEntry],
    caller_sub_chains: &[Vec<RequiresEntry>],
    syms: &ProjectionSyms,
) -> Option<TermId> {
    // Strategy 1 — named-param, binding-aware. Match by (required_sort,
    // bindings) so a caller with Eq[T=X] does NOT match dep Eq[T=Y]
    // (WI-226 correctness fix).
    if let Some(i) = caller_requires
        .iter()
        .position(|c| entries_cover(kb, c, dep))
    {
        let name = req_name_for_chain_index(kb, caller_sort?, i)?;
        return Some(build_req_var_ref(kb, syms, name));
    }

    // Strategy 2 — nested via caller slots' transitive `requires_chain`,
    // binding-aware. The slot's runtime requirement value bundles its
    // spec's deps in the same order, so a single `requirement_at_sort`
    // projects them.
    for (i, sub_chain) in caller_sub_chains.iter().enumerate() {
        if let Some(k) = sub_chain.iter().position(|s| entries_cover(kb, s, dep)) {
            let name = req_name_for_chain_index(kb, caller_sort?, i)?;
            let inner = build_req_var_ref(kb, syms, name);
            return Some(build_req_at_sort(kb, syms, inner, k));
        }
    }

    // Strategy 3 — static construction via SortProvidesInfo. Build a
    // SortGoal from the dep's spec bindings and run SLD resolution.
    let goal = goal_from_requires_entry(kb, dep)?;
    let scope = ResolutionScope { available_requires: caller_requires };
    match resolve(kb, &goal, &scope) {
        ResolutionResult::Resolved(tree) => emit_tree_as_projection(kb, caller_sort, &tree, syms),
        _ => None,
    }
}

/// WI-226: binding-aware predicate for slot matching in
/// `build_dep_projection`. True iff `caller`'s spec covers `dep`'s spec
/// — same `required_sort` AND every type-param binding of `dep` is
/// satisfied by `caller`'s binding for the same key (either identical
/// or with one side being a type-param wildcard, mirroring
/// `requires_entry_covers_goal`'s flexibility).
fn entries_cover(kb: &KnowledgeBase, caller: &RequiresEntry, dep: &RequiresEntry) -> bool {
    if caller.required_sort != dep.required_sort {
        return false;
    }
    let Some((_, caller_bindings)) = unwrap_spec_view(kb, caller.spec) else {
        return false;
    };
    let Some((_, dep_bindings)) = unwrap_spec_view(kb, dep.spec) else {
        return false;
    };
    // Bindingless `requires X` matches any dep; no constraints to check.
    if dep_bindings.is_empty() {
        return true;
    }
    let spec_qn = kb.qualified_name_of(dep.required_sort).to_string();
    for (dep_k, dep_val) in &dep_bindings {
        if !is_type_param_binding(kb, *dep_k, &spec_qn) {
            continue;
        }
        // Find the caller's binding for the same key. `same_symbol`
        // bridges differently-interned copies of the key without
        // matching an unrelated type param that merely shares a short
        // name (e.g. two specs' `T`).
        let caller_val = caller_bindings
            .iter()
            .find(|(ck, _)| same_symbol(kb, *ck, *dep_k))
            .map(|(_, v)| *v);
        let Some(caller_val) = caller_val else {
            return false;
        };
        // Either side a type-param wildcard ⇒ unconstrained, accept.
        if is_type_param_value(kb, caller_val) || is_type_param_value(kb, *dep_val) {
            continue;
        }
        if !dispatch_values_match(kb, caller_val, *dep_val)
            && !dispatch_values_match(kb, *dep_val, caller_val)
        {
            return false;
        }
    }
    true
}

/// WI-227: translate a `ResolvedRequiresNode` into a projection IR term.
/// `FromScope` becomes `var_ref(name = __req_<caller chain slot>)`;
/// `Leaf` becomes `construct_requirement(impl, nil)`; `Conditional`
/// recursively emits sub-projections and wraps them in a
/// `construct_requirement(impl, cons_list)`. `caller_sort` is the
/// enclosing op's parent sort, used to name `FromScope` chain slots.
fn emit_tree_as_projection(
    kb: &mut KnowledgeBase,
    caller_sort: Option<Symbol>,
    tree: &ResolvedRequiresNode,
    syms: &ProjectionSyms,
) -> Option<TermId> {
    match tree {
        ResolvedRequiresNode::FromScope { scope_index, .. } => {
            let name = req_name_for_chain_index(kb, caller_sort?, *scope_index)?;
            Some(build_req_var_ref(kb, syms, name))
        }
        ResolvedRequiresNode::Leaf { impl_sort, .. } => {
            let nil_list = super::load::build_cons_list(
                kb, &[], syms.nil, syms.cons, syms.head, syms.tail,
            );
            Some(build_construct_requirement(kb, syms, *impl_sort, nil_list))
        }
        ResolvedRequiresNode::Conditional { impl_sort, sub_resolutions, .. } => {
            let mut sub_terms: SmallVec<[TermId; 4]> = SmallVec::new();
            for sub in sub_resolutions {
                sub_terms.push(emit_tree_as_projection(kb, caller_sort, sub, syms)?);
            }
            let list = super::load::build_cons_list(
                kb, &sub_terms, syms.nil, syms.cons, syms.head, syms.tail,
            );
            Some(build_construct_requirement(kb, syms, *impl_sort, list))
        }
    }
}

/// Build a value-position `var_ref(name = Ref(name_sym))` — the named
/// requirement-param read that replaces the positional
/// `requirement_at_current(slot)` under the names model (WI-237). Shared
/// by `build_dep_projection` Strategies 1 & 2-inner, `emit_tree_as_projection`'s
/// `FromScope`, and the `DeferToRequirement` emitter. There is no Self-slot
/// `+1` shift any more — the Self requirement is the named param `__req_self`.
fn build_req_var_ref(kb: &mut KnowledgeBase, syms: &ProjectionSyms, name_sym: Symbol) -> TermId {
    let name_ref = kb.alloc(Term::Ref(name_sym));
    kb.alloc(Term::Fn {
        functor: syms.var_ref,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(syms.name, name_ref)]),
    })
}


/// Build `requirement_at_sort(chain = <inner>, slot = <k>)`.
fn build_req_at_sort(
    kb: &mut KnowledgeBase,
    syms: &ProjectionSyms,
    inner: TermId,
    k: usize,
) -> TermId {
    let slot_lit = kb.alloc(Term::Const(Literal::Int(k as i64)));
    kb.alloc(Term::Fn {
        functor: syms.ras,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(syms.chain, inner), (syms.slot, slot_lit)]),
    })
}

/// Build `construct_requirement(impl_functor = <Ref(impl)>, requirements = <list>)`.
fn build_construct_requirement(
    kb: &mut KnowledgeBase,
    syms: &ProjectionSyms,
    impl_sym: Symbol,
    requirements_list: TermId,
) -> TermId {
    let impl_ref = kb.alloc(Term::Ref(impl_sym));
    kb.alloc(Term::Fn {
        functor: syms.construct,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (syms.impl_functor, impl_ref),
            (syms.requirements, requirements_list),
        ]),
    })
}

/// Extract a `SortGoal` from a `RequiresEntry`'s SortView, keeping only
/// type-parameter bindings (op bindings don't constrain dispatch).
fn goal_from_requires_entry(kb: &KnowledgeBase, entry: &RequiresEntry) -> Option<SortGoal> {
    let (_, raw_bindings) = unwrap_spec_view(kb, entry.spec)?;
    let spec_qn = kb.qualified_name_of(entry.required_sort).to_string();
    let bindings: SmallVec<[(Symbol, TermId); 2]> = raw_bindings
        .into_iter()
        .filter(|(k, _)| is_type_param_binding(kb, *k, &spec_qn))
        .collect();
    Some(SortGoal {
        spec_sort: entry.required_sort,
        bindings,
    })
}

/// WI-222 Phase E (i) / WI-228: rewrite a Pin-now or Direct apply to
/// apply_within with a concrete fn (impl/op symbol) and a projected
/// requirements channel. Used when the callee's parent sort has non-
/// empty `requires_chain` so the callee body can read
/// `frame.requirements`. Returns true iff the rewrite was recorded.
///
/// When `resolved_tree` is `Some`, the requirements list is built from
/// the SLD-resolved sub_resolutions (WI-228 path) — conditional impls
/// produce nested `construct_requirement` IR. When `None`, the
/// per-dep search runs against the callee's `requires_chain`
/// (Direct-call path; no SLD tree available).
pub(crate) fn record_apply_within_concrete(
    kb: &mut KnowledgeBase,
    original_apply: TermId,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    pos_args: &SmallVec<[TermId; 4]>,
    fn_target_sym: Symbol,
    callee_spec_sort: Symbol,
    spec_op_sym: Symbol,
    caller_sort: Option<Symbol>,
    caller_requires: &[RequiresEntry],
    resolved_tree: Option<&ResolvedRequiresNode>,
) -> bool {
    use smallvec::SmallVec;

    if kb.dispatch_rewrites.contains_key(&original_apply) {
        return false;
    }
    let aw_sym = match kb.try_resolve_symbol("anthill.reflect.Expr.apply_within") {
        Some(s) => s,
        None => return false,
    };
    let syms = match ProjectionSyms::resolve(kb) {
        Some(s) => s,
        None => return false,
    };
    let orig_args_tid = match get_named_arg(kb, named_args, "args") {
        Some(t) => t,
        None => return false,
    };
    let dict_term = match resolved_tree {
        Some(tree) => match emit_tree_as_projection(kb, caller_sort, tree, &syms) {
            Some(t) => t,
            None => return false,
        },
        None => match build_dispatching_dict_direct(
            kb, callee_spec_sort, caller_sort, caller_requires, &syms,
        ) {
            Some(t) => t,
            None => return false,
        },
    };
    let requirements_list = wrap_dispatch_channel(kb, dict_term, &syms);

    let fn_ref = kb.alloc(Term::Ref(fn_target_sym));
    let fn_field = kb.intern("fn");
    let args_field = kb.intern("args");
    let reqs_field = kb.intern("requirements");

    let rewritten = kb.alloc(Term::Fn {
        functor: aw_sym,
        pos_args: pos_args.clone(),
        named_args: SmallVec::from_slice(&[
            (fn_field, fn_ref),
            (args_field, orig_args_tid),
            (reqs_field, requirements_list),
        ]),
    });
    kb.record_dispatch_rewrite(original_apply, rewritten, spec_op_sym);
    true
}

/// WI-222 Phase C+D / WI-237 (names model): defer-to-requirement rewrite.
/// Emits `apply_within(fn = Ref(spec_op_sym), args = <orig>,
/// requirements = [var_ref(name = __req_<slot>)])`. Dispatch from
/// spec-op to impl-op happens at the apply_within reduction by reading
/// the dispatching dict's functor. `slot` is the position of the
/// matching entry in `enclosing_sort`'s `requires` chain; the chain
/// index is mapped to the synthesized `__req_*` param name via
/// `req_name_for_chain_index`.
pub(crate) fn record_apply_within_rewrite(
    kb: &mut KnowledgeBase,
    original_apply: TermId,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    pos_args: &SmallVec<[TermId; 4]>,
    spec_op_sym: Symbol,
    enclosing_sort: Option<Symbol>,
    slot: usize,
) -> bool {
    use smallvec::SmallVec;

    if kb.dispatch_rewrites.contains_key(&original_apply) {
        return false;
    }
    let aw_sym = match kb.try_resolve_symbol("anthill.reflect.Expr.apply_within") {
        Some(s) => s,
        None => return false,
    };
    let syms = match ProjectionSyms::resolve(kb) {
        Some(s) => s,
        None => return false,
    };
    let orig_args_tid = match get_named_arg(kb, named_args, "args") {
        Some(t) => t,
        None => return false,
    };

    let enclosing_sort = match enclosing_sort {
        Some(s) => s,
        None => return false,
    };
    let name = match req_name_for_chain_index(kb, enclosing_sort, slot) {
        Some(n) => n,
        None => return false,
    };
    let dict_expr = build_req_var_ref(kb, &syms, name);
    let requirements_list = wrap_dispatch_channel(kb, dict_expr, &syms);

    let fn_ref = kb.alloc(Term::Ref(spec_op_sym));
    let fn_field = kb.intern("fn");
    let args_field = kb.intern("args");
    let reqs_field = kb.intern("requirements");

    let rewritten = kb.alloc(Term::Fn {
        functor: aw_sym,
        pos_args: pos_args.clone(),
        named_args: SmallVec::from_slice(&[
            (fn_field, fn_ref),
            (args_field, orig_args_tid),
            (reqs_field, requirements_list),
        ]),
    });
    kb.record_dispatch_rewrite(original_apply, rewritten, spec_op_sym);
    true
}

/// Full operation info for type checking: params with types, return type, effects.
struct OperationInfoFull {
    params: Vec<(Symbol, TermId)>,  // (param_name, param_type)
    return_type: TermId,
    effects: Vec<TermId>,
    /// Operation-level type parameters in declaration order, as
    /// `(name, Var(VarId) term)` pairs.
    type_params: Vec<(Symbol, TermId)>,
}

/// Look up complete OperationInfo for a functor.
/// Thin wrapper over `kb::op_info::lookup_operation_info` for the
/// fields the typer cares about (params + return + effects, no body).
fn lookup_operation_info_full(kb: &KnowledgeBase, functor: Symbol) -> Option<OperationInfoFull> {
    let rec = super::op_info::lookup_operation_info(kb, functor)?;
    Some(OperationInfoFull {
        params: rec.params,
        return_type: rec.return_type,
        effects: rec.effects,
        type_params: rec.type_params,
    })
}

/// Seed `subst` from `op[bindings](args)` call sites: named bindings
/// match by name, positional by declaration order. Names that don't
/// match any declared type-param produce a `NoSuchTypeParam` error so
/// the user sees the typo rather than a silent return-type Var leaking
/// to the caller.
fn seed_op_type_args(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    op: &OperationInfoFull,
    occ: &Rc<NodeOccurrence>,
    fn_sym: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    let type_args = match &occ.kind {
        NodeKind::Expr { expr: Expr::Apply { type_args, .. }, .. } => type_args,
        _ => return Ok(()),
    };
    if type_args.is_empty() || op.type_params.is_empty() {
        return Ok(());
    }
    let mut positional_idx = 0;
    for (name_opt, value) in type_args {
        let target = match name_opt {
            Some(name_sym) => op.type_params.iter()
                .find(|(n, _)| n == name_sym)
                .map(|(_, v)| *v)
                .ok_or(TypeError::NoSuchTypeParam {
                    span,
                    op: fn_sym,
                    name: *name_sym,
                })?,
            None => {
                let v = op.type_params.get(positional_idx).map(|(_, v)| *v);
                positional_idx += 1;
                match v {
                    Some(v) => v,
                    None => continue,
                }
            }
        };
        unify_types(kb, subst, target, *value);
    }
    Ok(())
}

/// WI-270 — after seeding from `[bindings]`, expected, and arg
/// unification, every declared type-param must resolve to a non-Var
/// term. An unresolved Var means the caller can't recover the return
/// type's concrete shape; surface `UnconstrainedTypeParam` with the
/// param's name so the user can pin it via `op[T = …](…)`.
fn check_unconstrained_type_params(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    if op.type_params.is_empty() {
        return Ok(());
    }
    for (name, var_term) in &op.type_params {
        let resolved = walk_type_deep(kb, subst, *var_term);
        if let Term::Var(Var::Global(_)) = kb.get_term(resolved) {
            return Err(TypeError::UnconstrainedTypeParam {
                span,
                op: fn_sym,
                type_param: *name,
            });
        }
    }
    Ok(())
}

/// WI-210 — `op_sym` is a "spec operation" if it is declared in a sort
/// that has at least one `sort <Param> = ?` declaration AND the
/// operation has no body. Spec operations are subject to call-site
/// dispatch via `SortProvidesInfo` lookup.
///
/// Returns the *parent sort* symbol (the spec sort) when `op_sym`
/// qualifies; `None` otherwise.
pub fn lookup_spec_op_dispatch(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    use crate::intern::{SymbolDef, SymbolKind};

    // The parent sort's qualified name is the op's qualified name
    // with the last segment stripped off.
    let op_qn = kb.qualified_name_of(op_sym);
    let (parent_qn, _short) = op_qn.rsplit_once('.')?;

    let parent_sym = kb.try_resolve_symbol(parent_qn)?;
    if !matches!(
        kb.symbols.get(parent_sym),
        SymbolDef::Resolved { kind: SymbolKind::Sort, .. }
    ) {
        return None;
    }
    if kb.type_params_of_sort(parent_sym).is_empty() {
        return None;
    }

    // The op must be body-less (declaration only). We reuse the same
    // OperationInfo lookup machinery as `lookup_operation_info_full`
    // but read the `body` field instead.
    if !operation_has_no_body(kb, op_sym) {
        return None;
    }

    Some(parent_sym)
}

/// WI-231 — per-call-site classification produced by the typer for
/// consumption by the requirement-insertion pass (`kb/req_insertion.rs`).
/// Each tagged apply site carries its `CallClass` on the apply
/// occurrence's `OccurrenceEntry`; `req_insertion::run` walks the
/// classified occurrences and emits the corresponding rewrite into
/// `kb.dispatch_rewrites`.
///
/// External codegen targets (Rust monomorphization, reflection
/// tooling, alternative elaborations) can read these classifications
/// directly (via `kb.occurrence_store().classifications_iter()`) and
/// choose to emit their own elaboration rather than invoking the
/// standard pass.
///
/// Reference: docs/design/operation-call-model.md §"Pass structure:
/// typer first, requirement-insertion separate".
#[derive(Clone, Debug)]
pub enum CallClass {
    /// Pin-now rewrite from a spec op to a concrete impl op (WI-218).
    /// The impl's parent sort has no `requires`, so the call becomes
    /// a plain `apply(fn = Ref(impl_op_sym), args)` — no apply_within
    /// wrap, no requirements channel.
    PinNow {
        spec_op_sym: Symbol,
        impl_op_sym: Symbol,
    },
    /// Pin-now to an impl whose parent sort has `requires`, OR a
    /// Direct call to a non-spec op whose parent has `requires`
    /// (WI-222 Phase E (i)). Emits `apply_within(fn = Ref(fn_target),
    /// args, requirements = …)`. `resolved_tree` is `Some` for the
    /// Pin-now path (WI-228 tree-threaded projection); `None` for
    /// Direct (falls back to per-dep search against `caller_requires`
    /// derived from `enclosing_sort`).
    ///
    ConcreteApplyWithin {
        fn_target_sym: Symbol,
        callee_spec_sort: Symbol,
        spec_op_sym: Symbol,
        enclosing_sort: Option<Symbol>,
        resolved_tree: Option<ResolvedRequiresNode>,
    },
    /// Defer-to-requirement (WI-222 Phase C+D): dispatch deferred to
    /// runtime via `apply_within(fn = requirement_at_current(slot,
    /// op = some(op_short)), args, requirements = …)`. The impl is
    /// determined at dispatch time by reading `frame.requirements[slot]`.
    ///
    /// WI-232: `resolved_spec` is the matched requires entry from the
    /// caller's chain — `enclosing_requires[slot]` at classification
    /// time. Embedding it eliminates the slot→entry re-indexing in
    /// `req_insertion::run`; `resolved_spec.required_sort` replaces the
    /// previous parallel `spec_sort` field.
    DeferToRequirement {
        spec_op_sym: Symbol,
        op_short_sym: Symbol,
        resolved_spec: RequiresEntry,
        slot: usize,
        enclosing_sort: Option<Symbol>,
    },
}

/// WI-210 — dispatch result for a spec-op call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DispatchOutcome {
    /// No `SortProvidesInfo` records exist for this spec at all.
    /// Dispatch is opt-in per spec: with zero candidates, the call
    /// type-checks against the spec's signature (legacy semantics)
    /// — no impl is required. Stdlib specs like `Numeric` and `Map`
    /// rely on this to be called without explicit impl declarations.
    NoCandidates,
    /// Exactly one candidate's bindings match the per-call subst.
    /// Carries the impl operation symbol for the runtime to call.
    Unique(Symbol),
    /// Candidates exist but none match the inferred bindings.
    /// User likely forgot to declare an impl at the right binding.
    NoMatch,
    /// Two or more candidates match — coherence rule (C) rejects.
    Ambiguous,
    /// WI-221 (defer-to-requirement, open-bound trigger): spec sort
    /// reached via the enclosing sort's `requires` chain. Impl varies
    /// per requirement value at runtime, so Pin-now rewrite is skipped.
    /// See `docs/design/operation-call-model.md` §"Defer-to-requirement
    /// detection".
    Deferred,
}

/// WI-221/WI-222 — defer-to-requirement detection (open-bound trigger).
/// Returns the **slot index** (position in `chain`) of the first matching
/// requires entry, or `None` if the spec sort isn't reached via this
/// chain. WI-222 needs the slot to populate `requirement_at_current(slot
/// = N)` in the rewritten `apply_within`. The chain is cached on
/// `TypingEnv` (see `set_enclosing_sort`) to avoid re-walking
/// `SortRequiresInfo` per apply check.
pub fn find_requires_slot(
    kb: &KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    chain: &[RequiresEntry],
) -> Option<usize> {
    use smallvec::SmallVec;
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();

    for (idx, entry) in chain.iter().enumerate() {
        if entry.required_sort != spec_sort {
            continue;
        }
        // Extract bindings from the entry's SortView term. Plain
        // bindingless requires (e.g. `requires Paintable`) match
        // unconditionally — any per-call subst for this spec is reached
        // via the requires.
        let bindings: SmallVec<[(Symbol, TermId); 2]> = match kb.get_term(entry.spec) {
            Term::Fn { functor, named_args, pos_args } => {
                let f_qn = kb.qualified_name_of(*functor);
                if f_qn == "anthill.reflect.SortView" || f_qn.ends_with(".SortView") {
                    named_args.clone()
                } else if pos_args.is_empty() && named_args.is_empty() {
                    // Plain sort term, e.g. `requires Paintable`.
                    SmallVec::new()
                } else {
                    continue;
                }
            }
            Term::Ref(_) | Term::Ident(_) => SmallVec::new(),
            _ => continue,
        };

        if bindings.is_empty() {
            return Some(idx);
        }

        // The post-`resolve_requires_bindings` SortView for a `requires`
        // entry carries bindings for both type-params (e.g. `T`) and
        // auto-bound operations (e.g. `eq`, `neq`). Only the type-param
        // bindings constrain the per-call substitution — op bindings are
        // resolved against the enclosing sort's operations and don't
        // participate in defer-to-requirement matching. We detect a
        // type-param slot via SortAlias resolution: only spec params
        // produce a `Term::Var` alias target. If no type-param bindings
        // surface (spec has no params, or all bindings are ops), the
        // entry matches vacuously.
        let mut all_match = true;
        for (binding_short_sym, entry_value) in &bindings {
            let binding_short = kb.resolve_sym(*binding_short_sym);
            let param_qn = format!("{spec_qn}.{binding_short}");
            let param_qn_sym = match kb.try_resolve_symbol(&param_qn) {
                Some(s) => s,
                None => continue,
            };
            let alias_target = match resolve_sort_alias(kb, param_qn_sym) {
                Some(t) => t,
                None => continue,
            };
            let vid = match kb.get_term(alias_target) {
                Term::Var(Var::Global(v)) => *v,
                _ => continue,
            };
            let per_call_value = match subst.resolve_with_term(vid) {
                // Unbound spec param: this is the OPEN-T defer trigger.
                // The call's binding was not constrained to a concrete
                // carrier (often because the typer unified two free Vars
                // and bound the *other* direction). Per
                // `docs/design/operation-call-model.md` §"Defer-to-
                // requirement detection", an open type-var in the goal
                // means defer — the impl is determined at runtime by the
                // requirement value the caller passed. Match this entry.
                None => continue,
                Some(v) => v,
            };
            // Either side may be a wildcard (a type-param value): the
            // requires entry might use the enclosing sort's open T
            // (`requires Eq[T]`) or a concrete carrier (`requires Eq[T=Int]`).
            // Symmetric match — try both directions.
            if !dispatch_values_match(kb, per_call_value, *entry_value)
                && !dispatch_values_match(kb, *entry_value, per_call_value)
            {
                all_match = false;
                break;
            }
        }
        if all_match {
            return Some(idx);
        }
    }
    None
}

// ── WI-224 — SLD-based instance synthesis ──────────────────────
//
// Replacement for the original single-shot `find_unique_impl_op`. Per
// `docs/design/operation-call-model.md` §"Resolution": instance
// synthesis is an SLD query over `SortProvidesInfo`. Each candidate's
// head may be a non-conditional fact (a "leaf" impl with no further
// requirements) or a conditional impl whose sort declares its own
// `requires` chain (the subgoals).
//
// `find_unique_impl_op` (kept as a thin compatibility wrapper) now
// delegates to `resolve`.

/// A goal in instance resolution: "find an impl that provides `spec_sort`
/// at the given bindings." Bindings keyed by the spec's short
/// parameter names (`T`, `State`, …) per the `SortView` convention.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SortGoal {
    pub spec_sort: Symbol,
    pub bindings: SmallVec<[(Symbol, TermId); 2]>,
}

/// Context for `resolve` — the `requires` entries already in scope
/// (matched at scope_index `i` so the requirement-insertion pass can
/// emit `requirement_at_current(i)`).
#[derive(Clone)]
pub struct ResolutionScope<'a> {
    pub available_requires: &'a [RequiresEntry],
}

/// The synthesized resolution chain. Returned to the requirement-
/// insertion pass which emits the IR (`construct_requirement` /
/// `requirement_at_current` / projections) per node.
#[derive(Clone, Debug)]
pub enum ResolvedRequiresNode {
    /// Non-conditional impl. `impl_sort` is the carrier sort symbol
    /// (e.g., `IntEq`), `bindings` is the head's per-binding values
    /// after impl-param substitution.
    Leaf {
        impl_sort: Symbol,
        spec_sort: Symbol,
        bindings: SmallVec<[(Symbol, TermId); 2]>,
    },
    /// Conditional impl: head matched + sub_resolutions resolved.
    Conditional {
        impl_sort: Symbol,
        spec_sort: Symbol,
        bindings: SmallVec<[(Symbol, TermId); 2]>,
        sub_resolutions: Vec<ResolvedRequiresNode>,
    },
    /// Matched an entry in `scope.available_requires`. No new
    /// construction needed — the caller's `frame.requirements[slot]`
    /// already holds the right requirement value.
    FromScope {
        scope_index: usize,
        spec_sort: Symbol,
    },
}

impl ResolvedRequiresNode {
    /// The spec sort this tree resolves (for diagnostics / WI-226).
    pub fn spec_sort(&self) -> Symbol {
        match self {
            ResolvedRequiresNode::Leaf { spec_sort, .. }
            | ResolvedRequiresNode::Conditional { spec_sort, .. }
            | ResolvedRequiresNode::FromScope { spec_sort, .. } => *spec_sort,
        }
    }

    /// The impl carrier sort. `None` for `FromScope` — no specific
    /// impl is pinned; the runtime reads the slot's bundled handle.
    pub fn impl_sort(&self) -> Option<Symbol> {
        match self {
            ResolvedRequiresNode::Leaf { impl_sort, .. }
            | ResolvedRequiresNode::Conditional { impl_sort, .. } => Some(*impl_sort),
            ResolvedRequiresNode::FromScope { .. } => None,
        }
    }
}

/// Outcome of `resolve`. The error variants carry enough context to
/// produce a user diagnostic (NoMatch / Ambiguous / Cyclic).
#[derive(Clone, Debug)]
pub enum ResolutionResult {
    Resolved(ResolvedRequiresNode),
    /// No candidate's head unifies with the goal.
    NoMatch { goal_text: String, hint: String },
    /// Multiple candidates match and specificity coherence couldn't
    /// pick a unique winner. `candidate_impl_qns` lists the colliding
    /// carriers for the diagnostic.
    Ambiguous { goal_text: String, candidate_impl_qns: Vec<String> },
    /// Detected a cycle in conditional-instance resolution. `path` is
    /// the goal stack at the point the cycle was detected.
    Cyclic { path: Vec<String> },
}

/// Public entry point — instance synthesis for `goal` in `scope`.
/// Takes a mutable KB because conditional resolution allocates
/// freshly-substituted subgoal terms (impl-param `Ref(EqList.A)`
/// replaced by the matched per-call value) for the recursive
/// resolution step.
pub fn resolve(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    scope: &ResolutionScope,
) -> ResolutionResult {
    let mut stack: Vec<SortGoal> = Vec::new();
    resolve_inner(kb, goal, scope, &mut stack)
}

fn resolve_inner(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    scope: &ResolutionScope,
    stack: &mut Vec<SortGoal>,
) -> ResolutionResult {
    for (i, ar) in scope.available_requires.iter().enumerate() {
        if ar.required_sort != goal.spec_sort {
            continue;
        }
        if requires_entry_covers_goal(kb, ar, goal) {
            return ResolutionResult::Resolved(ResolvedRequiresNode::FromScope {
                scope_index: i,
                spec_sort: goal.spec_sort,
            });
        }
    }

    if stack.iter().any(|g| goals_equal(kb, g, goal)) {
        let mut path: Vec<String> = stack.iter().map(|g| format_goal(kb, g)).collect();
        path.push(format_goal(kb, goal));
        return ResolutionResult::Cyclic { path };
    }
    stack.push(goal.clone());

    let candidates = collect_provides_candidates(kb, goal);

    if candidates.is_empty() {
        stack.pop();
        return ResolutionResult::NoMatch {
            goal_text: format_goal(kb, goal),
            hint: format!(
                "no impl provides {}; add `fact {0}[…]` or `requires {0}[…]` in scope",
                kb.qualified_name_of(goal.spec_sort)
            ),
        };
    }

    let chosen = match pick_most_specific(kb, &candidates) {
        Some(idx) => &candidates[idx],
        None => {
            stack.pop();
            let candidate_impl_qns: Vec<String> = candidates
                .iter()
                .map(|c| kb.qualified_name_of(c.impl_sort).to_string())
                .collect();
            return ResolutionResult::Ambiguous {
                goal_text: format_goal(kb, goal),
                candidate_impl_qns,
            };
        }
    };

    // Save chosen's data before recursing: `resolve_inner` takes &mut kb
    // (it allocates substituted subgoal terms) and `chosen` borrows
    // `candidates` immutably; cloning out releases that borrow.
    let chosen_impl_sort = chosen.impl_sort;
    let chosen_bindings = chosen.resolved_head_bindings.clone();
    let chosen_impl_subst = chosen.impl_subst.clone();
    drop(candidates);

    let sub_goals: Vec<SortGoal> = candidate_sub_goals_owned(
        kb, chosen_impl_sort, &chosen_impl_subst,
    );
    let mut sub_resolutions: Vec<ResolvedRequiresNode> = Vec::with_capacity(sub_goals.len());
    for sg in &sub_goals {
        match resolve_inner(kb, sg, scope, stack) {
            ResolutionResult::Resolved(t) => sub_resolutions.push(t),
            err => {
                stack.pop();
                return err;
            }
        }
    }
    stack.pop();

    let tree = if sub_resolutions.is_empty() {
        ResolvedRequiresNode::Leaf {
            impl_sort: chosen_impl_sort,
            spec_sort: goal.spec_sort,
            bindings: chosen_bindings,
        }
    } else {
        ResolvedRequiresNode::Conditional {
            impl_sort: chosen_impl_sort,
            spec_sort: goal.spec_sort,
            bindings: chosen_bindings,
            sub_resolutions,
        }
    };
    ResolutionResult::Resolved(tree)
}

/// A SortProvidesInfo candidate matched against a goal. Carries the
/// impl sort + the impl-side substitution (impl param → resolved
/// value) used to instantiate the impl's `requires_chain` subgoals.
struct Candidate {
    /// The carrier sort symbol (e.g., `IntEq`, `EqList`).
    impl_sort: Symbol,
    /// Head bindings after impl-param substitution — used for the
    /// resolved tree node's `bindings` slot.
    resolved_head_bindings: SmallVec<[(Symbol, TermId); 2]>,
    /// Impl-side substitution: maps the impl sort's type-param symbols
    /// to the values they got from matching the goal. Used to
    /// instantiate the impl's `requires_chain` subgoals.
    impl_subst: SmallVec<[(Symbol, TermId); 2]>,
    /// True iff the candidate's head is fully-ground (no impl-params
    /// referenced) — i.e., a strictly more-specific instance than a
    /// candidate whose head still carries impl-params. Used by
    /// `pick_most_specific`.
    head_specificity: u32,
}

/// Walk `SortProvidesInfo` facts, return those whose head pattern
/// unifies with `goal.bindings`. A candidate whose binding values do
/// not match the goal's is dropped silently and does NOT count as
/// "spec is in use" — `Eq[T = Type]` (meta-equality on Type values)
/// and `Eq[T = Int]` (equality on Int values) are independent specs
/// that happen to share the same spec sort; the presence of one in
/// the KB must not gate dispatch of the other.
fn collect_provides_candidates(
    kb: &KnowledgeBase,
    goal: &SortGoal,
) -> Vec<Candidate> {
    let provides_sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return Vec::new(),
    };
    // Spec's type-param short names — hoisted out of the candidate
    // loop so the inner binding-walk just does a string membership
    // check instead of format!+resolve+sort-alias per binding.
    let type_param_names: Vec<String> = kb.type_params_of_sort(goal.spec_sort);

    let mut out: Vec<Candidate> = Vec::new();
    for rid in kb.by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head(rid);
        let head_named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args.clone(),
            _ => continue,
        };
        let sort_ref_tid = match get_named_arg(kb, &head_named, "sort_ref") {
            Some(t) => t,
            None => continue,
        };
        let spec_view_tid = match get_named_arg(kb, &head_named, "spec") {
            Some(t) => t,
            None => continue,
        };
        let impl_sort = match kb.get_term(sort_ref_tid) {
            Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => *functor,
            _ => continue,
        };
        let Some((view_base_sym, view_bindings)) = unwrap_spec_view(kb, spec_view_tid) else {
            continue;
        };
        if view_base_sym != goal.spec_sort {
            continue;
        }

        let impl_param_set = impl_param_symbols(kb, impl_sort);
        let mut impl_subst: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        let mut head_specificity: u32 = 0;
        let mut all_match = true;
        let mut resolved_head_bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for (binding_short, candidate_value) in &view_bindings {
            let short_name = kb.resolve_sym(*binding_short);
            if !type_param_names.iter().any(|n| n == short_name) {
                // Op-binding (auto-bound `eq`/`neq`/…) — doesn't drive
                // dispatch.
                continue;
            }
            let per_call_value = match goal_binding_value(kb, goal, *binding_short) {
                Some(t) => t,
                None => {
                    all_match = false;
                    break;
                }
            };
            if !match_candidate_against_goal(
                kb,
                *candidate_value,
                per_call_value,
                &impl_param_set,
                &mut impl_subst,
                &mut head_specificity,
            ) {
                all_match = false;
                break;
            }
            // Build resolved head bindings inline; consumers want the
            // per-callsite ground value (not the candidate's free
            // pattern).
            resolved_head_bindings.push((*binding_short, per_call_value));
        }
        if !all_match {
            continue;
        }
        out.push(Candidate {
            impl_sort,
            resolved_head_bindings,
            impl_subst,
            head_specificity,
        });
    }
    out
}


/// Unwrap a `SortView(base, …named)` term into `(base_sort_sym,
/// named_bindings)`. Accepts a bare functor (no SortView wrap) as the
/// no-bindings case. Returns `None` for shapes that don't fit either
/// case (caller must filter).
fn unwrap_spec_view(
    kb: &KnowledgeBase,
    spec_view_tid: TermId,
) -> Option<(Symbol, SmallVec<[(Symbol, TermId); 2]>)> {
    match kb.get_term(spec_view_tid) {
        Term::Fn { functor, pos_args, named_args } => {
            let f_qn = kb.qualified_name_of(*functor);
            if f_qn == "anthill.reflect.SortView" || f_qn.ends_with(".SortView") {
                let base_sym = pos_args.first().copied().and_then(|t| match kb.get_term(t) {
                    Term::Fn { functor, .. }
                    | Term::Ref(functor)
                    | Term::Ident(functor) => Some(*functor),
                    _ => None,
                })?;
                Some((base_sym, named_args.clone()))
            } else {
                Some((*functor, SmallVec::new()))
            }
        }
        Term::Ref(s) | Term::Ident(s) => Some((*s, SmallVec::new())),
        _ => None,
    }
}

/// Look up `goal.bindings[short]` (the per-call value for the spec's
/// short parameter name). Compared by **resolved short name** rather
/// than symbol-identity: the candidate's binding_short and the goal's
/// stored key may have been interned through different paths (the
/// candidate-side loader vs. the goal-construction call below) — but
/// they always render to the same short name (e.g. "T").
fn goal_binding_value(kb: &KnowledgeBase, goal: &SortGoal, short: Symbol) -> Option<TermId> {
    if let Some(v) = goal.bindings.iter().find(|(k, _)| *k == short).map(|(_, v)| *v) {
        return Some(v);
    }
    let name = kb.resolve_sym(short);
    goal.bindings
        .iter()
        .find(|(k, _)| kb.resolve_sym(*k) == name)
        .map(|(_, v)| *v)
}

/// Type-param short-name symbols declared on an impl sort. Used to
/// distinguish impl-param `Ref(EqList.A)` from concrete refs (e.g.,
/// `Ref(Int)`) when matching the candidate's head.
fn impl_param_symbols(kb: &KnowledgeBase, impl_sort: Symbol) -> SmallVec<[Symbol; 2]> {
    let mut out: SmallVec<[Symbol; 2]> = SmallVec::new();
    let impl_qn = kb.qualified_name_of(impl_sort).to_string();
    for short in kb.type_params_of_sort(impl_sort) {
        let qn = format!("{impl_qn}.{short}");
        if let Some(s) = kb.try_resolve_symbol(&qn) {
            out.push(s);
        }
    }
    out
}

/// Match a candidate-side value (potentially containing impl-param
/// `Ref`s) against a per-call value. Captures impl-subst bindings on
/// the way; returns false on shape mismatch. Recursive on parametric
/// values so `List[T = A]` properly binds `A` to the per-call's `T`.
fn match_candidate_against_goal(
    kb: &KnowledgeBase,
    candidate_value: TermId,
    per_call_value: TermId,
    impl_params: &[Symbol],
    impl_subst: &mut SmallVec<[(Symbol, TermId); 2]>,
    specificity: &mut u32,
) -> bool {
    // (1) Candidate side is an impl-param ref → bind it (or check
    // consistency with an earlier binding).
    if let Some(p) = impl_param_ref(kb, candidate_value, impl_params) {
        if let Some((_, prev)) = impl_subst.iter().find(|(k, _)| *k == p) {
            return values_structurally_equal(kb, *prev, per_call_value);
        }
        impl_subst.push((p, per_call_value));
        // An impl-param ref contributes no specificity weight.
        return true;
    }
    // (2) Candidate side is a parametric Fn — recurse into its bindings.
    if let Some((c_base, c_bindings)) = parametric_value_parts(kb, candidate_value) {
        // Per-call side must also be parametric with the same base.
        let (p_base, p_bindings) = match parametric_value_parts(kb, per_call_value) {
            Some(parts) => parts,
            None => {
                // A type-param wildcard on the per-call side can match
                // a structured candidate — accept (the WI-218 path
                // already treats this case as `Deferred`).
                if is_type_param_value(kb, per_call_value) {
                    return true;
                }
                return false;
            }
        };
        if c_base != p_base {
            return false;
        }
        *specificity = specificity.saturating_add(1);
        // Each candidate binding must find a matching per-call binding.
        for (k, c_val) in &c_bindings {
            let p_val = match p_bindings.iter().find(|(kk, _)| kk == k).map(|(_, v)| *v) {
                Some(v) => v,
                None => return false,
            };
            if !match_candidate_against_goal(
                kb,
                *c_val,
                p_val,
                impl_params,
                impl_subst,
                specificity,
            ) {
                return false;
            }
        }
        return true;
    }
    // (3) Concrete sort ref/identifier — use the existing shallow check.
    if dispatch_values_match(kb, per_call_value, candidate_value) {
        *specificity = specificity.saturating_add(1);
        return true;
    }
    false
}

/// If `value` is `Ref(sym)` / `Ident(sym)` where `sym` is one of
/// `impl_params`, return `Some(sym)`. None otherwise.
fn impl_param_ref(kb: &KnowledgeBase, value: TermId, impl_params: &[Symbol]) -> Option<Symbol> {
    let sym = match kb.get_term(value) {
        Term::Ref(s) | Term::Ident(s) => *s,
        _ => return None,
    };
    if impl_params.contains(&sym) {
        Some(sym)
    } else {
        None
    }
}

/// Decompose a parametric value `Functor(named: [(k, v), ...])` into
/// `(functor, named_args)`. Returns `None` for non-parametric shapes
/// (bare refs, sort_ref wraps, literals).
fn parametric_value_parts(
    kb: &KnowledgeBase,
    value: TermId,
) -> Option<(Symbol, SmallVec<[(Symbol, TermId); 2]>)> {
    match kb.get_term(value) {
        Term::Fn { functor, named_args, pos_args } => {
            // sort_ref(name: ...) wraps a concrete sort ref; not
            // parametric for our purpose.
            let f_qn = kb.qualified_name_of(*functor);
            if f_qn == "sort_ref" || f_qn.ends_with(".sort_ref") {
                return None;
            }
            // SortView is the candidate-side parametric encoding —
            // unwrap into (base, bindings).
            if f_qn == "anthill.reflect.SortView" || f_qn.ends_with(".SortView") {
                let base = pos_args
                    .first()
                    .copied()
                    .and_then(|t| match kb.get_term(t) {
                        Term::Fn { functor, .. }
                        | Term::Ref(functor)
                        | Term::Ident(functor) => Some(*functor),
                        _ => None,
                    });
                return base.map(|b| (b, named_args.clone()));
            }
            // parameterized(base, bindings = [Binding(P, V), ...]) is
            // the typer-side encoding. Translate into (base, [(P, V)]).
            // Match both the bare short name (from loader-side conversion)
            // and the fully-qualified `anthill.prelude.Type.parameterized`
            // (which is what the typer's reified arg-type unification
            // produces).
            if f_qn == "parameterized" || f_qn.ends_with(".parameterized") {
                let base = get_named_arg(kb, named_args, "base")
                    .and_then(|t| match kb.get_term(t) {
                        Term::Fn { functor, .. }
                        | Term::Ref(functor)
                        | Term::Ident(functor) => Some(*functor),
                        _ => None,
                    });
                let bindings_tid = get_named_arg(kb, named_args, "bindings");
                let mut out: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                if let Some(bt) = bindings_tid {
                    for binding in list_to_vec(kb, bt) {
                        if let (Some(p), Some(v)) =
                            (binding_param_sym(kb, binding), binding_value(kb, binding))
                        {
                            out.push((p, v));
                        }
                    }
                }
                return base.map(|b| (b, out));
            }
            // WI-320: `effects_rows(effects_expr = E)` is a structural Type
            // variant (wraps an EffectExpression), not a parametric spec
            // carrier — `effects_expr` is a *field*, not a spec parameter.
            // Without this explicit None, the generic-Fn catch-all below
            // would falsely classify it as a parametric instance with a
            // phantom (param = effects_expr, value = E) binding, leading
            // spec-resolution and `values_structurally_equal` to treat it
            // as a satisfaction site.
            if f_qn == "effects_rows" || f_qn.ends_with(".effects_rows") {
                return None;
            }
            // Generic Fn — non-empty named_args means parametric.
            if !named_args.is_empty() {
                Some((*functor, named_args.clone()))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Structural equality check on two term values — used when an impl
/// param is encountered twice in the head and must bind consistently.
fn values_structurally_equal(kb: &KnowledgeBase, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    // Hash-consing collapses identical structures into one TermId, so
    // distinct ids generally indicate a shape difference. Still, walk
    // sort_ref / parametric forms to catch the shallow encoding noise.
    let a_sym = sort_sym_of_term(kb, a);
    let b_sym = sort_sym_of_term(kb, b);
    match (a_sym, b_sym) {
        (Some(x), Some(y)) if x == y => {
            // Check nested bindings if parametric.
            match (parametric_value_parts(kb, a), parametric_value_parts(kb, b)) {
                (Some((_, ab)), Some((_, bb))) => {
                    if ab.len() != bb.len() {
                        return false;
                    }
                    ab.iter().all(|(k, av)| {
                        bb.iter()
                            .find(|(kk, _)| kk == k)
                            .map_or(false, |(_, bv)| values_structurally_equal(kb, *av, *bv))
                    })
                }
                _ => true,
            }
        }
        _ => false,
    }
}

/// Coherence-by-specificity. Picks the candidate with the strictly-
/// highest `head_specificity` count. Returns `None` if no unique
/// winner (multiple candidates tied at the max).
fn pick_most_specific(_kb: &KnowledgeBase, candidates: &[Candidate]) -> Option<usize> {
    if candidates.is_empty() {
        return None;
    }
    let max = candidates.iter().map(|c| c.head_specificity).max().unwrap();
    let mut winners = candidates
        .iter()
        .enumerate()
        .filter(|(_, c)| c.head_specificity == max);
    let first = winners.next()?;
    if winners.next().is_some() {
        return None;
    }
    Some(first.0)
}

/// Build subgoals for a chosen conditional candidate by substituting
/// the impl-side substitution into the impl sort's `requires_chain`.
/// Filters out op-bindings (which the loader stores alongside type-
/// param bindings on a `SortView` — see `find_requires_slot`'s same
/// distinction) — only type-param bindings drive resolution.
fn candidate_sub_goals_owned(
    kb: &mut KnowledgeBase,
    impl_sort: Symbol,
    impl_subst: &[(Symbol, TermId)],
) -> Vec<SortGoal> {
    let chain = requires_chain(kb, impl_sort);
    let mut out: Vec<SortGoal> = Vec::with_capacity(chain.len());
    for entry in &chain {
        let required_sort = entry.required_sort;
        let Some((_, entry_bindings)) = unwrap_spec_view(kb, entry.spec) else {
            continue;
        };
        let spec_qn = kb.qualified_name_of(required_sort).to_string();
        let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for (k, v) in &entry_bindings {
            // Op-bindings (auto-bound `eq`, `neq`, …) don't constrain
            // resolution — skip.
            if !is_type_param_binding(kb, *k, &spec_qn) {
                continue;
            }
            let substituted = substitute_impl_params_alloc(kb, *v, impl_subst);
            bindings.push((*k, substituted));
        }
        out.push(SortGoal {
            spec_sort: required_sort,
            bindings,
        });
    }
    out
}

/// True iff `short` names a type-parameter (vs an op) of the spec at
/// `spec_qn`. Determined by checking whether `<spec_qn>.<short>`
/// resolves to a SortAlias-bearing symbol — only spec params do.
fn is_type_param_binding(kb: &KnowledgeBase, short: Symbol, spec_qn: &str) -> bool {
    let short_name = kb.resolve_sym(short).to_string();
    let qn = format!("{spec_qn}.{short_name}");
    let Some(s) = kb.try_resolve_symbol(&qn) else {
        return false;
    };
    resolve_sort_alias(kb, s).is_some()
}

/// Replace every `Ref(p)` / `Ident(p)` / nullary `Fn(p, [], [])` in
/// `term` where `p` is in `impl_subst` with its bound value. The
/// nullary-Fn shape is what `convert_term` produces for a bare name
/// like `A` inside a `requires Eq[T = A]` clause — it's structurally
/// the same as `Ref(A)` for resolution purposes. Allocates new Fn
/// terms when children need substitution; returns the original TermId
/// otherwise.
fn substitute_impl_params_alloc(
    kb: &mut KnowledgeBase,
    term: TermId,
    impl_subst: &[(Symbol, TermId)],
) -> TermId {
    match kb.get_term(term).clone() {
        Term::Ref(s) | Term::Ident(s) => {
            if let Some((_, v)) = impl_subst.iter().find(|(k, _)| *k == s) {
                *v
            } else {
                term
            }
        }
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            // Nullary Fn — treat as a name reference.
            if let Some((_, v)) = impl_subst.iter().find(|(k, _)| *k == functor) {
                return *v;
            }
            term
        }
        Term::Fn { functor, pos_args, named_args } => {
            let mut changed = false;
            let new_pos: SmallVec<[TermId; 4]> = pos_args.iter().map(|t| {
                let nt = substitute_impl_params_alloc(kb, *t, impl_subst);
                if nt != *t { changed = true; }
                nt
            }).collect();
            let new_named: SmallVec<[(Symbol, TermId); 2]> = named_args.iter().map(|(k, t)| {
                let nt = substitute_impl_params_alloc(kb, *t, impl_subst);
                if nt != *t { changed = true; }
                (*k, nt)
            }).collect();
            if !changed { return term; }
            kb.alloc(Term::Fn {
                functor,
                pos_args: new_pos,
                named_args: new_named,
            })
        }
        _ => term,
    }
}

/// True iff `entry`'s bindings cover `goal`. Used at the
/// `available_requires` lookup step (step 1 of `resolve`).
/// Filters out op-bindings (auto-bound `eq`, `neq`, …) — only type-
/// param bindings constrain matching.
fn requires_entry_covers_goal(
    kb: &KnowledgeBase,
    entry: &RequiresEntry,
    goal: &SortGoal,
) -> bool {
    let Some((_, entry_bindings)) = unwrap_spec_view(kb, entry.spec) else {
        return false;
    };
    if entry_bindings.is_empty() {
        return true;
    }
    let spec_qn = kb.qualified_name_of(goal.spec_sort).to_string();
    for (k, e_val) in &entry_bindings {
        if !is_type_param_binding(kb, *k, &spec_qn) {
            continue;
        }
        let g_val = match goal_binding_value(kb, goal, *k) {
            Some(v) => v,
            None => return false,
        };
        if is_type_param_value(kb, *e_val) || is_type_param_value(kb, g_val) {
            continue;
        }
        if !dispatch_values_match(kb, g_val, *e_val)
            && !dispatch_values_match(kb, *e_val, g_val)
        {
            return false;
        }
    }
    true
}

/// Structural equality between two goals for cycle detection.
/// Binding keys compared via `same_symbol` — bridges differently-interned
/// copies without colliding two specs' same-short-named type params.
fn goals_equal(kb: &KnowledgeBase, a: &SortGoal, b: &SortGoal) -> bool {
    if a.spec_sort != b.spec_sort {
        return false;
    }
    if a.bindings.len() != b.bindings.len() {
        return false;
    }
    a.bindings.iter().all(|(k, av)| {
        b.bindings
            .iter()
            .find(|(kk, _)| same_symbol(kb, *kk, *k))
            .map_or(false, |(_, bv)| values_structurally_equal(kb, *av, *bv))
    })
}

/// Human-readable goal text for diagnostics ("Eq[T = Int]").
fn format_goal(kb: &KnowledgeBase, goal: &SortGoal) -> String {
    let mut out = kb.qualified_name_of(goal.spec_sort).to_string();
    if !goal.bindings.is_empty() {
        out.push('[');
        let mut first = true;
        for (k, v) in &goal.bindings {
            if !first {
                out.push_str(", ");
            }
            first = false;
            out.push_str(kb.resolve_sym(*k));
            out.push_str(" = ");
            out.push_str(&format_term_for_goal(kb, *v));
        }
        out.push(']');
    }
    out
}

/// Render a binding value compactly. Sort symbols → short name;
/// parametric forms → `Base[K = V]`.
fn format_term_for_goal(kb: &KnowledgeBase, t: TermId) -> String {
    if let Some(sym) = extract_sort_ref_sym(kb, t) {
        return kb.qualified_name_of(sym).to_string();
    }
    match kb.get_term(t) {
        Term::Ref(s) | Term::Ident(s) => kb.qualified_name_of(*s).to_string(),
        Term::Fn { functor, pos_args, named_args } => {
            let base = kb.qualified_name_of(*functor).to_string();
            if pos_args.is_empty() && named_args.is_empty() {
                base
            } else {
                let mut s = base;
                s.push('[');
                let mut first = true;
                for (k, v) in named_args.iter() {
                    if !first { s.push_str(", "); }
                    first = false;
                    s.push_str(kb.resolve_sym(*k));
                    s.push_str(" = ");
                    s.push_str(&format_term_for_goal(kb, *v));
                }
                s.push(']');
                s
            }
        }
        Term::Const(Literal::Int(i)) => i.to_string(),
        _ => format!("<term#{}>", t.raw()),
    }
}

/// Build a `SortGoal` from a per-call substitution at a spec sort,
/// reading each declared spec param via its SortAlias-to-Var. Used by
/// `find_unique_impl_op` (compat wrapper) and by external callers
/// constructing a goal from typer state.
pub fn sort_goal_from_subst(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
) -> SortGoal {
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    for short in kb.type_params_of_sort(spec_sort) {
        let short_sym = match kb.try_resolve_symbol(&format!("{spec_qn}.{short}")) {
            Some(s) => s,
            None => continue,
        };
        let alias_target = match resolve_sort_alias(kb, short_sym) {
            Some(t) => t,
            None => continue,
        };
        let vid = match kb.get_term(alias_target) {
            Term::Var(Var::Global(v)) => *v,
            _ => continue,
        };
        if let Some(val) = subst.resolve_with_term(vid) {
            let short_intern = kb.try_resolve_symbol(&short).unwrap_or_else(|| {
                // Spec param's *short* name (e.g. "T") may not be registered
                // as a top-level symbol; fall back to its qualified form.
                short_sym
            });
            let canonical = canonicalize_type_value(kb, val);
            bindings.push((short_intern, canonical));
        }
    }
    SortGoal {
        spec_sort,
        bindings,
    }
}

/// WI-228: convert the typer's reified `Type.parameterized(base = sort_ref(name: X),
/// bindings = [TypeBinding(param: P, value: V), ...])` representation
/// into the canonical `Fn(X, [], [(P, V)*])` shape SLD matching expects.
/// Recurses into binding values so nested parametric types canonicalize
/// at every level.
///
/// Returns the input unchanged when (a) the term is not in
/// `parameterized` shape (e.g. plain `Ref(Int)` or an already-canonical
/// `Fn(List, [], [(T, Ref(Int))])`), or (b) it is parameterized but no
/// child binding rewrote AND the functor already matches the unwrapped
/// base — i.e. nothing needed translating. The change-detection
/// short-circuit keeps the common case (already-canonical input)
/// allocation-free.
///
/// Note: cannot reuse `parametric_value_parts` here because its
/// `parameterized` arm extracts the base via the raw functor of the
/// `base` field, which for the typer's encoding is the `sort_ref`
/// functor rather than the underlying sort sym; this function unwraps
/// `sort_ref(name: X)` to X explicitly.
fn canonicalize_type_value(kb: &mut KnowledgeBase, ty: TermId) -> TermId {
    use smallvec::SmallVec;
    let term = kb.get_term(ty).clone();
    let Term::Fn { functor, named_args, .. } = term else {
        return ty;
    };
    let f_qn = kb.qualified_name_of(functor);
    if !(f_qn == "parameterized" || f_qn.ends_with(".parameterized")) {
        return ty;
    }
    let Some(base_tid) = get_named_arg(kb, &named_args, "base") else { return ty };
    let Some(base_sym) = extract_sort_ref_sym(kb, base_tid) else { return ty };
    let Some(bindings_tid) = get_named_arg(kb, &named_args, "bindings") else { return ty };
    let mut canonical_named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    for binding in list_to_vec(kb, bindings_tid) {
        let Some(param_sym) = binding_param_sym(kb, binding) else { continue };
        let Some(value_tid) = binding_value(kb, binding) else { continue };
        let canonical_value = canonicalize_type_value(kb, value_tid);
        canonical_named.push((param_sym, canonical_value));
    }
    kb.alloc(Term::Fn {
        functor: base_sym,
        pos_args: SmallVec::new(),
        named_args: canonical_named,
    })
}

/// WI-210/WI-224 — find the unique impl operation symbol for a spec-op
/// call. Thin wrapper over `dispatch_spec_op_with_tree` that drops the
/// `ResolvedRequiresNode`. Callers that need the tree (WI-228: requirement
/// projection for Pin-now) call `dispatch_spec_op_with_tree` directly.
pub fn find_unique_impl_op(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    op_short_sym: Symbol,
    enclosing_requires: &[RequiresEntry],
) -> DispatchOutcome {
    dispatch_spec_op_with_tree(kb, subst, spec_sort, op_short_sym, enclosing_requires).0
}

/// WI-228 — same as `find_unique_impl_op` but also returns the full
/// `ResolvedRequiresNode` (when one was produced). The tree carries the impl's
/// sub_resolutions for conditional instances, which the requirement-
/// insertion pass turns into nested `construct_requirement` IR.
///
/// Delegates to `dispatch_spec_op_cached` — the legacy compat path
/// (`find_unique_impl_op`) thus also benefits from WI-226 Cache B.
pub fn dispatch_spec_op_with_tree(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    op_short_sym: Symbol,
    enclosing_requires: &[RequiresEntry],
) -> (DispatchOutcome, Option<ResolvedRequiresNode>) {
    dispatch_spec_op_cached(kb, subst, spec_sort, op_short_sym, enclosing_requires)
}

/// WI-226 — cached variant of `dispatch_spec_op_with_tree`. Repeated
/// spec-op calls at the same `(SortGoal, scope)` hit the per-KB memo
/// (`kb.resolve_cache`) and skip the SLD walk. The defer-trigger
/// check (which depends on `subst` via `find_requires_slot`) runs
/// uncached because it reads typer-side vars; the rest is keyed on the
/// canonicalized goal + scope.
pub fn dispatch_spec_op_cached(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    op_short_sym: Symbol,
    enclosing_requires: &[RequiresEntry],
) -> (DispatchOutcome, Option<ResolvedRequiresNode>) {
    if !enclosing_requires.is_empty()
        && find_requires_slot(kb, subst, spec_sort, enclosing_requires).is_some()
    {
        return (DispatchOutcome::Deferred, None);
    }
    let goal = sort_goal_from_subst(kb, subst, spec_sort);
    let key = (goal.clone(), enclosing_requires.to_vec());
    if let Some(cached) = kb.resolve_cache.borrow().get(&key) {
        return cached.clone();
    }
    let result = resolve_at_goal(kb, &goal, op_short_sym, enclosing_requires);
    kb.resolve_cache.borrow_mut().insert(key, result.clone());
    result
}

/// Resolve a pre-built `SortGoal` to a `(DispatchOutcome, Option<ResolvedRequiresNode>)`.
/// Shared body of `dispatch_spec_op_with_tree` and `dispatch_spec_op_cached`
/// — they differ only in pre-check (defer trigger) and memoization.
fn resolve_at_goal(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    op_short_sym: Symbol,
    enclosing_requires: &[RequiresEntry],
) -> (DispatchOutcome, Option<ResolvedRequiresNode>) {
    let scope = ResolutionScope { available_requires: enclosing_requires };

    // No matching candidate ⇒ NoCandidates (permissive fall-through).
    // An unrelated `SortProvidesInfo` record for the same spec — e.g.
    // `Eq[T = Type]` when the goal is `Eq[T = Int]` — must not gate
    // dispatch: those are distinct specifications about distinct
    // sorts. Per-binding matching in `collect_provides_candidates` is
    // the only mechanism that decides relevance.
    let candidates = collect_provides_candidates(kb, &goal);
    if candidates.is_empty() {
        for ar in scope.available_requires {
            if ar.required_sort == goal.spec_sort && requires_entry_covers_goal(kb, ar, &goal) {
                return (DispatchOutcome::Deferred, None);
            }
        }
        return (DispatchOutcome::NoCandidates, None);
    }

    let mut stack: Vec<SortGoal> = Vec::new();
    match resolve_inner(kb, &goal, &scope, &mut stack) {
        ResolutionResult::Resolved(tree) => match &tree {
            ResolvedRequiresNode::Leaf { impl_sort, .. }
            | ResolvedRequiresNode::Conditional { impl_sort, .. } => {
                // WI-240 — direct table lookup. The load-time
                // `build_sort_ops_table` already resolved impl-override
                // vs spec-default for `(impl_sort, op_short)`; no
                // string concatenation, no try/catch fallback here.
                match kb.sort_ops_lookup(*impl_sort, op_short_sym) {
                    Some(s) => (DispatchOutcome::Unique(s), Some(tree)),
                    None => (DispatchOutcome::NoMatch, None),
                }
            }
            ResolvedRequiresNode::FromScope { .. } => (DispatchOutcome::Deferred, None),
        },
        ResolutionResult::NoMatch { .. } => (DispatchOutcome::NoMatch, None),
        ResolutionResult::Ambiguous { .. } => (DispatchOutcome::Ambiguous, None),
        ResolutionResult::Cyclic { .. } => (DispatchOutcome::NoMatch, None),
    }
}

/// WI-210 — compare a per-call subst's binding (a typer-side Type term,
/// e.g. `sort_ref(name: Ref(X))`) against a candidate's `SortView`
/// binding value (typically a bare `Ref(X)` from the loader's
/// `convert_term`). The two shapes carry the same nominal sort but
/// differ in wrapping; `types_lesseq` doesn't bridge them. We
/// extract the underlying sort symbol from each side and compare.
/// Falls through to `types_lesseq` for the same-shape case so that
/// future work (parameterized values, entity-of-sort subtyping in
/// binding values) keeps working as the relation grows.
fn dispatch_values_match(
    kb: &KnowledgeBase,
    per_call_value: TermId,
    candidate_value: TermId,
) -> bool {
    // A universally-quantified candidate matches any per-call value. The
    // fact-loading path stores type-params as `Term::Ref`, the op-signature
    // path as `Term::Var`; both shapes mean "for any T."
    if is_type_param_value(kb, candidate_value) {
        return true;
    }
    if types_lesseq(kb, per_call_value, candidate_value) {
        return true;
    }
    let per_call_sym = sort_sym_of_term(kb, per_call_value);
    let candidate_sym = sort_sym_of_term(kb, candidate_value);
    match (per_call_sym, candidate_sym) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

/// True iff `value` references an abstract type-parameter — directly as a
/// `Term::Var`, or as a `Term::Ref` / `Term::Ident` to a sort-level type-param
/// symbol (the loader signal for `sort T = ?`).
fn is_type_param_value(kb: &KnowledgeBase, value: TermId) -> bool {
    match kb.get_term(value) {
        Term::Var(_) => true,
        Term::Ref(sym) | Term::Ident(sym) => is_sort_param_symbol(kb, *sym),
        _ => false,
    }
}

/// Extract the underlying sort symbol from a term in any of the
/// shapes a binding value may take: `sort_ref(name: Ref(X))`,
/// bare `Ref(X)` / `Ident(X)`, or a nullary `Fn { functor: X, … }`.
fn sort_sym_of_term(kb: &KnowledgeBase, t: TermId) -> Option<Symbol> {
    if let Some(s) = extract_sort_ref_sym(kb, t) {
        return Some(s);
    }
    match kb.get_term(t) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        Term::Fn { functor, .. } => Some(*functor),
        _ => None,
    }
}

/// True iff an `OperationInfo` exists for `op_sym` and it has no body.
/// (Operations declared without a body ⇒ specs / abstract decls.) WI-305: the
/// body is no longer a fact field; it lives in the `op_body_node` side-table,
/// so the body presence is read from there. The OperationInfo-existence gate is
/// preserved — a symbol with no `OperationInfo` (which the old field-walk would
/// report as "has body" via the loop falling through to `false`) must keep that
/// answer so non-operation symbols are not misclassified as body-less spec ops.
fn operation_has_no_body(kb: &KnowledgeBase, op_sym: Symbol) -> bool {
    if super::op_info::lookup_operation_info(kb, op_sym).is_none() {
        return false; // no OperationInfo ⇒ not a body-less operation
    }
    kb.op_body_node(op_sym).is_none()
}

/// True iff `op_sym` resolves to an operation the runtime can actually
/// invoke by symbol: an `OperationInfo` exists for it AND its `body` is
/// `some(...)`. A symbol with no `OperationInfo` (e.g. the auto-bound
/// `anthill.prelude.String.eq` a `provides` block registers) or with
/// `body = none` (a spec-level declaration / derived op) is NOT a valid
/// static-dispatch rewrite target — the runtime resolves those via a
/// registered builtin or the spec's own derived rule. WI-237.
fn op_has_runnable_body(kb: &KnowledgeBase, op_sym: Symbol) -> bool {
    match super::op_info::lookup_operation_info(kb, op_sym) {
        Some(rec) => rec.body_node.is_some(),
        None => false,
    }
}

/// Tuple-literal special case routed from `check_constructor_iter`:
/// empty tuple → `Unit`; populated tuple → `named_tuple` whose fields
/// are `_0, _1, …` for positional args and the source label for named
/// args.
fn check_tuple_literal_constructor(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    occ: &Rc<NodeOccurrence>,
) -> Result<TypeResult, TypeError> {
    if pos_results.is_empty() && named_results.is_empty() {
        let unit_ty = kb.make_sort_ref_by_name("anthill.prelude.Unit");
        return Ok(TypeResult::pure(unit_ty, env.clone(), Rc::clone(occ)));
    }

    collect_arg_errors(pos_results.iter().chain(named_results.iter()))?;

    let pos_labeled = pos_results
        .iter()
        .enumerate()
        .map(|(i, r)| (kb.intern(&format!("_{}", i)), r.as_ref().expect("aggregator")));
    let named_labeled = named_args
        .iter()
        .zip(named_results.iter())
        .map(|((name, _), r)| (*name, r.as_ref().expect("aggregator")));

    let mut effects: Vec<TermId> = Vec::new();
    let mut tuple_fields: Vec<(Symbol, TermId)> = Vec::new();
    for (label, r) in pos_labeled.chain(named_labeled) {
        tuple_fields.push((label, r.ty));
        effects = merge_effects(&effects, &r.effects);
    }
    let tuple_ty = kb.make_named_tuple_type(&tuple_fields);
    Ok(TypeResult { ty: tuple_ty, env: env.clone(), effects, node: Rc::clone(occ) })
}

/// Type a `ListLiteral` / `SetLiteral` that reached the constructor checker
/// (un-desugared `[...]` / `{...}`) as `base[T = elem]`. The element type is
/// the expected `T` (checking direction) or the first element's type, else a
/// fresh var. Mirrors the `Expr::ListLit` / `Expr::SetLit` build frames.
/// (WI-289)
fn check_seq_literal_constructor(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    pos_results: &[Result<TypeResult, TypeError>],
    expected: Option<TermId>,
    occ: &Rc<NodeOccurrence>,
    base_name: &str,
) -> Result<TypeResult, TypeError> {
    // Defensive (the constructor checker already surfaced arg errors before
    // routing here): never `.expect` an `Err` element result.
    collect_arg_errors(pos_results.iter())?;
    let mut element_type = expected.and_then(|e| extract_type_param(kb, e, "T"));
    let mut effects: Vec<TermId> = Vec::new();
    for r in pos_results {
        let r = r.as_ref().expect("aggregator");
        if element_type.is_none() {
            element_type = Some(r.ty);
        }
        effects = merge_effects(&effects, &r.effects);
    }
    let t_val = element_type.unwrap_or_else(|| {
        let fresh = kb.intern("?T");
        kb.make_type_var(fresh)
    });
    let base = kb.make_sort_ref_by_name(base_name);
    let t_sym = kb.intern("T");
    let seq_type = kb.make_parameterized_type(base, &[(t_sym, t_val)]);
    Ok(TypeResult { ty: seq_type, env: env.clone(), effects, node: Rc::clone(occ) })
}

/// Non-recursive Constructor checker — peer of `check_apply_iter`.
/// Reads per-arg `TypeResult`s from `pos_results` / `named_results`
/// (pre-computed by the iterative typer) instead of calling
/// `type_check_node` itself. Handles both the surface
/// `constructor(name=…, args=[…])` form and implicit constructor calls
/// (an `Apply` whose functor is a constructor symbol — routed here
/// from `check_apply_iter`).
fn check_constructor_iter(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    ctor_sym: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    span: Option<Span>,
    expected: Option<TermId>,
    occ: &Rc<NodeOccurrence>,
) -> Result<TypeResult, TypeError> {
    let _ = pos_args; // arg-NodeOccurrence references kept for parity with check_apply_iter

    // Surface any sub-expression failure before continuing.
    collect_arg_errors(pos_results.iter().chain(named_results.iter()))?;

    // `()` and `(a, b, …)` parse as a `TupleLiteral` entity and the loader
    // wraps them as `constructor(name: Ref(TupleLiteral), args: …)`. They
    // land here even though they are not user-declared constructors, and
    // the declared `TupleLiteral` entity has no fields, so the field-driven
    // path below would type them as `sort_ref(TupleLiteral)` — which
    // doesn't unify with `Unit` or with a named-tuple type. Route to
    // tuple semantics instead.
    if kb.qualified_name_of(ctor_sym) == "anthill.reflect.TupleLiteral" {
        return check_tuple_literal_constructor(
            kb, env, named_args, pos_results, named_results, occ,
        );
    }
    // WI-289: `[...]` / `{...}` that wasn't desugared to cons/nil (no
    // expected List/Set type at the use site — e.g. an op body
    // `-> List[T] = [...]`) is loaded as `constructor(name: ListLiteral
    // /SetLiteral, args: …)`. Like `TupleLiteral` above, the declared
    // entity has no element fields, so the field-driven path would type it
    // as `sort_ref(ListLiteral)` and fail the surrounding `List[T]` check.
    // Type it as `List[T = elem]` / `Set[T = elem]`, mirroring the
    // `Expr::ListLit` / `Expr::SetLit` builds. (The body node stays a
    // `constructor(ListLiteral)` for eval/codegen, which handle it.)
    if kb.qualified_name_of(ctor_sym) == "anthill.reflect.ListLiteral" {
        return check_seq_literal_constructor(kb, env, pos_results, expected, occ, "List");
    }
    if kb.qualified_name_of(ctor_sym) == "anthill.reflect.SetLiteral" {
        return check_seq_literal_constructor(kb, env, pos_results, expected, occ, "Set");
    }

    // Free-standing entities (declared at namespace level, not nested in a
    // sort block) have no parent sort, but their entity_field_types IS
    // registered — the entity is its own type. Without this, a let-bound
    // `WorkItem(...)` types as `None`, the body's env loses enclosing_sort,
    // and downstream spec-op calls fail dispatch (WI-204 feedback).
    let parent_sort = kb.constructor_parent_sort(ctor_sym);
    let parent_type = match parent_sort {
        Some(parent_tid) => sort_term_to_type(kb, parent_tid),
        None => kb.make_sort_ref(ctor_sym),
    };

    let field_types = match kb.entity_field_types(ctor_sym) {
        Some(ft) => ft.to_vec(),
        None => return Err(TypeError::NoConstructor { span, name: ctor_sym }),
    };

    let mut subst = Substitution::new();
    let mut effects = Vec::new();

    // WI-270: caller context unifies with the parent type first so a
    // hint like `Option[Int]` constrains `some(?)` to T=Int even
    // when the value-side carries a fresh type-var. Runs before the
    // empty-field-types early return below so 0-arg constructors
    // (`nil()`, `Map.empty()`) also see the hint.
    if let Some(exp) = expected {
        unify_types(kb, &mut subst, parent_type, exp);
    }

    for &(field_sym, declared_type) in &field_types {
        if let Some((idx, _)) = named_args.iter().enumerate().find(|(_, (s, _))| *s == field_sym) {
            if let Ok(ref r) = named_results[idx] {
                unify_types(kb, &mut subst, r.ty, declared_type);
                effects = merge_effects(&effects, &r.effects);
            }
        }
    }

    for (i, r_opt) in pos_results.iter().enumerate() {
        if let Some(&(_, declared_type)) = field_types.get(i) {
            if let Ok(r) = r_opt {
                unify_types(kb, &mut subst, r.ty, declared_type);
                effects = merge_effects(&effects, &r.effects);
            }
        }
    }

    if subst.bindings.is_empty() {
        return Ok(TypeResult { ty: parent_type, env: env.clone(), effects, node: Rc::clone(occ) });
    }

    // Build parameterized type from the sort's type params + substitution bindings.
    // Look up SortAlias facts for the parent sort's scope to find param names → Var mappings.
    // For free-standing entities there is no parent sort to walk; the entity's
    // own symbol is the type — no type params to discover, so return the
    // simple sort_ref directly.
    let parent_sym = match parent_sort {
        Some(parent_tid) => match kb.get_term(parent_tid) {
            Term::Fn { functor, .. } => *functor,
            _ => return Ok(TypeResult { ty: parent_type, env: env.clone(), effects, node: Rc::clone(occ) }),
        },
        None => return Ok(TypeResult { ty: parent_type, env: env.clone(), effects, node: Rc::clone(occ) }),
    };

    let alias_sym = kb.try_resolve_symbol("SortAlias");
    let mut param_bindings: Vec<(Symbol, TermId)> = Vec::new();

    if let Some(a_sym) = alias_sym {
        let parent_name = kb.qualified_name_of(parent_sym).to_string();
        // Collect alias info: (param_short_name, VarId, bound_type)
        let mut alias_info: Vec<(String, TermId)> = Vec::new();
        for rid in kb.by_functor(a_sym) {
            if !kb.is_fact(rid) { continue; }
            let head = kb.rule_head(rid);
            if let Term::Fn { pos_args, .. } = kb.get_term(head) {
                if pos_args.len() >= 2 {
                    let sort_tid = pos_args[0];
                    let target_tid = pos_args[1];
                    if let Term::Fn { functor: alias_functor, .. } = kb.get_term(sort_tid) {
                        let alias_name = kb.qualified_name_of(*alias_functor).to_string();
                        if alias_name.starts_with(&parent_name) && alias_name.len() > parent_name.len() {
                            let param_short = alias_name[parent_name.len() + 1..].to_string();
                            if let Term::Var(Var::Global(vid)) = kb.get_term(target_tid) {
                                if let Some(bound_type) = subst.resolve_with_term(*vid) {
                                    alias_info.push((param_short, bound_type));
                                }
                            }
                        }
                    }
                }
            }
        }
        for (param_short, bound_type) in alias_info {
            let param_sym = kb.intern(&param_short);
            param_bindings.push((param_sym, bound_type));
        }
    }

    if param_bindings.is_empty() {
        Ok(TypeResult { ty: parent_type, env: env.clone(), effects, node: Rc::clone(occ) })
    } else {
        let base = kb.make_sort_ref(parent_sym);
        let param_type = kb.make_parameterized_type(base, &param_bindings);
        Ok(TypeResult { ty: param_type, env: env.clone(), effects, node: Rc::clone(occ) })
    }
}

/// Extract return type and effects from an arrow(param, result, effects) type term.
/// True when `ty` is `parameterized(base = Function, …)` — the stdlib
/// `Function[A, B, E]` surface type. `arrow` is the typer's shorthand for
/// it, so the two are the same callable type (see [`arrow_parts`]).
fn is_function_type(kb: &KnowledgeBase, ty: TermId) -> bool {
    if type_functor_name(kb, ty) != Some("parameterized") {
        return false;
    }
    let base = match kb.get_term(ty) {
        Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "base"),
        _ => None,
    };
    base.and_then(|b| extract_sort_ref_sym(kb, b))
        .is_some_and(|s| kb.qualified_name_of(s) == "anthill.prelude.Function")
}

/// Decompose a callable type into `(param, result, effects)`.
///
/// The typer's canonical function type is `arrow(param, result, effects)`;
/// the stdlib surface type `Function[A, B, E]` is the *same* type — `arrow`
/// is its shorthand (`A` = param, `B` = result, `E` = effects). Both
/// decompose here so a `Function`-typed operation parameter is callable
/// (`operation map(l, f: Function[A, B]) = ... f(h) ...`) just like a
/// lambda-bound arrow. `param` is `None` only when the source omits it.
/// Returns `None` for non-callable types. (WI-289)
fn arrow_parts(kb: &KnowledgeBase, ty: TermId) -> Option<(Option<TermId>, TermId, Vec<TermId>)> {
    match type_functor_name(kb, ty) {
        Some("arrow") => {
            let named_args = match kb.get_term(ty) {
                Term::Fn { named_args, .. } => named_args.clone(),
                _ => return None,
            };
            let result = get_named_arg(kb, &named_args, "result")?;
            let param = get_named_arg(kb, &named_args, "param");
            // WI-307 v1a: arrow.effects is now `effects_rows(EffectExpression)`
            // (singular Type), not `List[Type]`. Decode the EffectExpression
            // back to the flat `Vec<TermId>` shape that pre-v1a callers
            // expect (concrete labels + at most one tail Var) so non-row-aware
            // consumers (region.rs, op_info, type_display_name) keep working
            // unchanged. Row-aware callers (unify_arrow, arrow_compatible)
            // walk the effects_rows EffectExpression directly.
            let effects = get_named_arg(kb, &named_args, "effects")
                .map(|e| effects_rows_to_flat_list(kb, e))
                .unwrap_or_default();
            Some((param, result, effects))
        }
        Some("parameterized") if is_function_type(kb, ty) => {
            let result = extract_type_param(kb, ty, "B")?;
            let param = extract_type_param(kb, ty, "A");
            // Function[E] parameter binding still flows through as List[Type]
            // (the parameter shape hasn't migrated). When/if Function.E binds
            // an effects_rows Type, this branch follows the arrow branch.
            //
            // WI-307 code-review #5: dispatch via Symbol identity, not
            // short-name compare. A user-defined entity in another namespace
            // with short name `effects_rows` would otherwise be misrouted
            // through effects_rows_to_flat_list. The cached symbol resolves
            // against the canonical anthill.prelude.Type.effects_rows; a
            // missing symbol (pre-stdlib bootstrap) falls back to the legacy
            // List path, which is correct since no effects_rows term can
            // exist before its symbol is registered.
            let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.Type.effects_rows");
            let effects = extract_type_param(kb, ty, "E")
                .map(|e| {
                    let is_effects_rows = match (effects_rows_sym, kb.get_term(e)) {
                        (Some(er), Term::Fn { functor, .. }) => *functor == er,
                        _ => false,
                    };
                    if is_effects_rows {
                        effects_rows_to_flat_list(kb, e)
                    } else {
                        list_to_vec(kb, e)
                    }
                })
                .unwrap_or_default();
            Some((param, result, effects))
        }
        _ => None,
    }
}

/// WI-307 v1a: flatten an `effects_rows(EffectExpression)` Type into the
/// pre-v1a `Vec<TermId>` shape: concrete labels followed by an optional
/// row-tail `Var`. Inverse of `KnowledgeBase::build_canonical_effects_rows`.
///
/// **Structural walk** — visits the EffectExpression algebra via a stack
/// (no shape assumption about `merge` associativity). Each node dispatches
/// by short functor name:
///   - `empty_row`         → terminate this branch
///   - `present(label)`    → push `label` to `out`
///   - `absent(label)`     → skip (v1a presence-only; the flat-list shape
///                          has no slot for absences, lacks-constraints
///                          land with v1b)
///   - `open(tail)`        → push `tail` (the row-tail Var) to `out`
///   - `merge(left, right)`→ stack both subtrees
///   - bare `Term::Var`    → push as tail (matches the shape the WI-320
///                          bridge fact emits: `effects_rows(?expr)` whose
///                          inner is an unbound Var. Without this, the
///                          bridge head decodes to an empty flat list and
///                          effects silently vanish.)
///
/// **Non-wrapper tolerance** — when `ty` is not an `effects_rows` term, the
/// function falls back to `list_to_vec(kb, ty)` for back-compat with the
/// legacy List[Type] shape that still lives in OperationInfo.effects and
/// parameterized E bindings until those slots migrate. A `debug_assert`
/// surfaces the case in dev builds so any unexpected non-wrapper reaching
/// this site is easy to spot during migration.
pub(crate) fn effects_rows_to_flat_list(kb: &KnowledgeBase, ty: TermId) -> Vec<TermId> {
    // Unwrap effects_rows; non-wrapper inputs flow through legacy list_to_vec.
    // The fallback path is intentional during the migration window, but
    // surface unexpected shapes in dev builds so silent data-loss doesn't
    // accumulate.
    //
    // Dispatch via Symbol identity (code-review #5) rather than short-name
    // compare so a user-defined `effects_rows` entity in another namespace
    // isn't misrouted here.
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.Type.effects_rows");
    let expr = match (effects_rows_sym, kb.get_term(ty)) {
        (Some(er), Term::Fn { functor, named_args, .. }) if *functor == er => {
            match get_named_arg(kb, named_args, "effects_expr") {
                Some(e) => e,
                None => {
                    debug_assert!(
                        false,
                        "effects_rows term missing effects_expr field"
                    );
                    return Vec::new();
                }
            }
        }
        _ => {
            // Legacy: caller passed an unwrapped List or some other shape.
            // OperationInfo.effects (still List) and Function[E] with a
            // legacy List binding hit this; the typer's transient terms
            // before make_arrow_type also can.
            return list_to_vec(kb, ty);
        }
    };

    // Structural walk over the EffectExpression algebra (any associativity).
    let mut out: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = vec![expr];
    while let Some(node) = stack.pop() {
        match kb.get_term(node) {
            // Bare Var inside effects_rows is an open-row tail (e.g. the
            // WI-320 bridge fact head shape `effects_rows(?expr)`). Treat
            // as if wrapped in `open(tail = ?expr)` — pushing it to `out`
            // keeps the row-tail visible to downstream readers.
            Term::Var(_) => out.push(node),
            Term::Fn { functor, named_args, .. } => {
                let name = kb.resolve_sym(*functor);
                match name {
                    "empty_row" => {}
                    "present" => {
                        if let Some(label) = get_named_arg(kb, named_args, "label") {
                            out.push(label);
                        }
                    }
                    "absent" => {
                        // v1a presence-only — lacks-constraint slot lands w/ v1b.
                    }
                    "open" => {
                        if let Some(tail) = get_named_arg(kb, named_args, "tail") {
                            out.push(tail);
                        }
                    }
                    "merge" => {
                        // Push right first so left is visited first (LIFO).
                        // The walk is shape-agnostic: nested merges in
                        // either subtree are descended structurally rather
                        // than peeked at the head — non-canonical
                        // associativity no longer drops payload.
                        if let Some(r) = get_named_arg(kb, named_args, "right") {
                            stack.push(r);
                        }
                        if let Some(l) = get_named_arg(kb, named_args, "left") {
                            stack.push(l);
                        }
                    }
                    _ => {
                        // Unknown functor inside an EffectExpression payload
                        // — likely an upstream construction bug. Surface in
                        // dev builds; tolerate in release (caller decides).
                        debug_assert!(
                            false,
                            "unexpected functor in EffectExpression walk: {}",
                            name
                        );
                    }
                }
            }
            // Term::Ref / Const / Ident / Bottom inside an EffectExpression
            // are ill-typed — surface in dev, ignore in release.
            _ => {
                debug_assert!(
                    false,
                    "unexpected term shape in EffectExpression walk"
                );
            }
        }
    }
    out
}

/// Result + effects of a callable type (`arrow` or `Function[A, B, E]`).
/// Used when applying a function value — `f(x)` yields the result type.
fn extract_function_type_parts(kb: &KnowledgeBase, fn_type: TermId) -> Option<(TermId, Vec<TermId>)> {
    arrow_parts(kb, fn_type).map(|(_, result, effects)| (result, effects))
}

/// The param type of a callable (`arrow` or `Function[A, B, E]`), used to
/// type a lambda's parameter from the checking direction (an expected
/// `Function[A, B]` tells us the param is `A`).
fn extract_function_param_type(kb: &KnowledgeBase, fn_type: TermId) -> Option<TermId> {
    arrow_parts(kb, fn_type).and_then(|(param, _, _)| param)
}

/// Ordered component types of a `named_tuple(fields: [TypeField(name,
/// type), …])` type. Used to bind a tuple-destructuring pattern's
/// sub-patterns positionally (`lambda (a, b) -> ...` checked against
/// `Function[(A, B), R]` types `a: A`, `b: B`). Returns `None` for a
/// non-tuple type.
fn named_tuple_field_types(kb: &KnowledgeBase, ty: TermId) -> Option<Vec<TermId>> {
    if type_functor_name(kb, ty) != Some("named_tuple") {
        return None;
    }
    let fields_tid = match kb.get_term(ty) {
        Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "fields"),
        _ => None,
    }?;
    let mut out = Vec::new();
    for field in list_to_vec(kb, fields_tid) {
        if let Term::Fn { named_args, .. } = kb.get_term(field) {
            if let Some(field_ty) = get_named_arg(kb, named_args, "type") {
                out.push(field_ty);
            }
        }
    }
    Some(out)
}

/// Extract the variable name symbol from a `var_pattern`.
fn extract_pattern_var_name(kb: &KnowledgeBase, pattern: TermId) -> Option<Symbol> {
    if let Term::Fn { functor, named_args, pos_args, .. } = kb.get_term(pattern) {
        let fname = kb.resolve_sym(*functor);
        if fname == "var_pattern" {
            return extract_sym_arg(kb, named_args, pos_args, "name");
        }
    }
    None
}


/// Extract a named type parameter from a parameterized type term.
/// e.g. extract_type_param(kb, List[T = Int], "T") → Some(Int)
/// Extract a type parameter from a parameterized type.
/// e.g. extract_type_param(kb, parameterized(base: sort_ref(List), bindings: [TypeBinding(param: T, value: Int)]), "T") → Some(sort_ref(Int))
pub(crate) fn extract_type_param(kb: &KnowledgeBase, ty: TermId, param: &str) -> Option<TermId> {
    if let Term::Fn { functor, named_args, .. } = kb.get_term(ty) {
        let fname = kb.resolve_sym(*functor);
        if fname == "parameterized" {
            // Search bindings list for TypeBinding with matching param
            let bindings_tid = get_named_arg(kb, named_args, "bindings")?;
            for binding in list_to_vec(kb, bindings_tid) {
                if let Term::Fn { named_args: ba, .. } = kb.get_term(binding) {
                    if let Some(psym) = extract_ref_field(kb, ba, "param") {
                        if kb.resolve_sym(psym) == param {
                            return get_named_arg(kb, ba, "value");
                        }
                    }
                }
            }
            None
        } else {
            // Fallback: direct named arg lookup (for compatibility)
            named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == param)
                .map(|(_, v)| *v)
        }
    } else {
        None
    }
}

// ── Pattern env extension ──────────────────────────────────────

/// Build a `Substitution` from a `parameterized(base, bindings)` type
/// for a constructor pattern's field types: each scrutinee binding's
/// param symbol maps to the type-param `Var(Global)` registered for
/// `parent_sort`, bound to the binding's value type. So
/// `case some(name)` over `Option[T = String]` resolves `some.value`'s
/// declared type to `String`, binding `name: String`.
///
/// Lookup is scoped to `parent_sort` via [`type_param_vid_in_sort`];
/// short-name resolution is ambiguous when many sorts declare
/// `sort T = ?`.
fn build_pattern_subst(
    kb: &KnowledgeBase,
    scrutinee_type: TermId,
    parent_sort: Symbol,
) -> Option<Substitution> {
    if type_functor_name(kb, scrutinee_type) != Some("parameterized") {
        return None;
    }
    let named_args = match kb.get_term(scrutinee_type) {
        Term::Fn { named_args, .. } => named_args.clone(),
        _ => return None,
    };
    let bindings_tid = get_named_arg(kb, &named_args, "bindings")?;

    let mut subst = Substitution::new();
    let mut any = false;
    for b in list_to_vec(kb, bindings_tid) {
        let (Some(param), Some(value)) = (binding_param_sym(kb, b), binding_value(kb, b))
        else { continue };
        if let Some(vid) = type_param_vid_in_sort(kb, parent_sort, param) {
            subst.bind_term(vid, value);
            any = true;
        }
    }
    if any { Some(subst) } else { None }
}

/// Look up the type-parameter `Var(Global)` registered for
/// `<parent_sort>.<param_sym>`. Resolves the qualified short name to a
/// `Symbol` and delegates to [`resolve_sort_alias`]'s exact-symbol
/// match — unambiguous even when many sorts declare the same short
/// param name (`sort T = ?` recurs in List, Option, Stream …).
fn type_param_vid_in_sort(
    kb: &KnowledgeBase,
    parent_sort: Symbol,
    param_sym: Symbol,
) -> Option<crate::kb::term::VarId> {
    let qualified = format!(
        "{}.{}",
        kb.qualified_name_of(parent_sort),
        kb.resolve_sym(param_sym),
    );
    let qualified_sym = kb.try_resolve_symbol(&qualified)?;
    let alias_target = resolve_sort_alias(kb, qualified_sym)?;
    match kb.get_term(alias_target) {
        Term::Var(Var::Global(v)) => Some(*v),
        _ => None,
    }
}

fn extend_env_from_pattern(
    kb: &mut KnowledgeBase,
    env: &mut TypingEnv,
    pattern: TermId,
    scrutinee_type: Option<TermId>,
) {
    if let Term::Fn { functor, named_args, pos_args } = kb.get_term(pattern).clone() {
        let functor_name = kb.resolve_sym(functor).to_string();
        match functor_name.as_str() {
            "var_pattern" => {
                if let Some(sym) = extract_sym_arg(kb, &named_args, &pos_args, "name") {
                    // Bind the pattern var even when its type is unknown —
                    // a pattern-bound name is in scope regardless. Without
                    // this, tuple-destructuring lambda params
                    // (`lambda (a, b) -> ...`, whose sub-patterns recurse
                    // here with no component type) and match vars over an
                    // un-inferred scrutinee stayed unbound and every
                    // reference failed as `UnresolvedName`. (WI-289)
                    let ty = scrutinee_type.unwrap_or_else(|| {
                        let fresh = kb.intern("?pat");
                        kb.make_type_var(fresh)
                    });
                    env.bind_var(sym, ty);
                    // Pattern-bound names are local — effects on them
                    // shouldn't escape the surrounding match/case scope
                    // (matches `check_let_expr`'s declare_local_resource
                    // for let bindings). Without this, a body like
                    //   match Cell.get(s) case wis(b, _) -> persist(b, ...)
                    // would surface persist's `Modify[b]` as an external
                    // effect even though b's lifetime ends at case end.
                    env.declare_local_resource(sym);
                }
            }
            "constructor_pattern" => {
                let name_sym = extract_sym_arg(kb, &named_args, &pos_args, "name");
                let args_tid = get_named_arg(kb, &named_args, "args");
                if let (Some(ctor_sym), Some(args)) = (name_sym, args_tid) {
                    let field_types = kb.entity_field_types(ctor_sym).map(|f| f.to_vec());
                    let sub_patterns = list_to_vec(kb, args);
                    if let Some(fields) = field_types {
                        // Substitute the scrutinee's type args into the
                        // constructor's declared field types. For
                        // `case some(name)` over `Option[T = String]`,
                        // `some.value`'s declared type `T` resolves to
                        // `String` — without this `name` binds to the
                        // raw type-param term and surfaces as a bare
                        // `TermId` in later return-type checks.
                        let parent_sort = kb.constructor_parent_sort(ctor_sym)
                            .and_then(|t| match kb.get_term(t) {
                                Term::Fn { functor, .. } => Some(*functor),
                                Term::Ref(s) => Some(*s),
                                _ => None,
                            });
                        let subst = scrutinee_type
                            .zip(parent_sort)
                            .and_then(|(st, p)| build_pattern_subst(kb, st, p));
                        for (i, sub_pat) in sub_patterns.iter().enumerate() {
                            let field_type = fields.get(i).map(|(_, ty)| {
                                match &subst {
                                    Some(s) => walk_type(kb, s, *ty),
                                    None => *ty,
                                }
                            });
                            extend_env_from_pattern(kb, env, *sub_pat, field_type);
                        }
                    } else {
                        for sub_pat in &sub_patterns {
                            extend_env_from_pattern(kb, env, *sub_pat, None);
                        }
                    }
                }
            }
            "tuple_pattern" => {
                // Loaded tuple patterns store their sub-patterns under the
                // `elements` list (load.rs `PatternTuple` build), not
                // `args` — the old `args`/`pos_args.first()` lookup always
                // missed, leaving `lambda (a, b) -> ...` params unbound.
                // When the scrutinee is a tuple type, bind each
                // sub-pattern to its component type — so `lambda (a, b) ->
                // a + b` checked against `Function[(Int, Int), Int]` types
                // a/b as Int and `+` dispatches uniquely. Otherwise the
                // component type is unknown and var_pattern mints a fresh
                // type var.
                if let Some(elements) = get_named_arg(kb, &named_args, "elements") {
                    let sub_patterns = list_to_vec(kb, elements);
                    let components = scrutinee_type.and_then(|t| named_tuple_field_types(kb, t));
                    for (i, sub_pat) in sub_patterns.iter().enumerate() {
                        let comp = components.as_ref().and_then(|c| c.get(i).copied());
                        extend_env_from_pattern(kb, env, *sub_pat, comp);
                    }
                }
            }
            _ => {} // wildcard, literal_pattern — no bindings
        }
    }
}

fn extract_pattern_type_ann(kb: &KnowledgeBase, pattern: TermId) -> Option<TermId> {
    if let Term::Fn { named_args, .. } = kb.get_term(pattern) {
        let type_ann = get_named_arg(kb, named_args, "type_ann")?;
        unwrap_option(kb, type_ann)
    } else {
        None
    }
}

// ── Operation info lookup ──────────────────────────────────────

fn lookup_operation_return_type(kb: &KnowledgeBase, functor: Symbol) -> Option<TermId> {
    lookup_operation_field(kb, functor, "return_type")
}


fn lookup_operation_field(kb: &KnowledgeBase, functor: Symbol, field: &str) -> Option<TermId> {
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")?;
    for rid in kb.by_functor(op_info_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            let name_val = named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "name")
                .map(|(_, v)| *v);
            if let Some(name_tid) = name_val {
                if let Term::Ref(s) = kb.get_term(name_tid) {
                    if *s == functor {
                        return named_args.iter()
                            .find(|(s, _)| kb.resolve_sym(*s) == field)
                            .map(|(_, v)| *v);
                    }
                }
            }
        }
    }
    None
}

// ── Type unification ───────────────────────────────────────────

use super::subst::Substitution;

/// Unify two type terms, binding type variables in the substitution.
/// Returns true if unification succeeds.
///
/// - `Term::Var` on either side → bind in substitution
/// - `sort_ref(name: X)` where X is a type param (SortAlias to Var) → resolve and recurse
/// - Ground types → check `types_compatible` (includes subtyping)
///
/// WI-307 v1a: `kb` is `&mut` to enable fresh tail-variable allocation
/// inside `unify_effect_expression` when both rows have labels the other
/// lacks (the canonical Rémy row-rewrite arm). Pre-WI-307 this function
/// took `&KnowledgeBase`; the change ripples to every `unify_*` helper
/// and to `types_compatible` (which `unify_types` falls back to). All
/// 49 call sites in the typer already have `&mut KnowledgeBase` available.
pub fn unify_types(kb: &mut KnowledgeBase, subst: &mut Substitution, a: TermId, b: TermId) -> bool {
    let a_resolved = walk_type(kb, subst, a);
    let b_resolved = walk_type(kb, subst, b);

    if a_resolved == b_resolved {
        return true;
    }

    if let Term::Var(Var::Global(vid)) = kb.get_term(a_resolved) {
        if occurs_in(kb, *vid, b_resolved) { return false; }
        subst.bind(*vid, b_resolved);
        return !subst.is_contradiction();
    }
    if let Term::Var(Var::Global(vid)) = kb.get_term(b_resolved) {
        if occurs_in(kb, *vid, a_resolved) { return false; }
        subst.bind(*vid, a_resolved);
        return !subst.is_contradiction();
    }

    let a_functor = type_functor_name(kb, a_resolved);
    let b_functor = type_functor_name(kb, b_resolved);

    match (a_functor, b_functor) {
        (Some("parameterized"), Some("parameterized")) => {
            unify_parameterized(kb, subst, a_resolved, b_resolved)
        }
        (Some("parameterized"), Some("sort_ref")) => {
            unify_parameterized_with_sort_ref(kb, subst, a_resolved, b_resolved)
        }
        (Some("sort_ref"), Some("parameterized")) => {
            unify_parameterized_with_sort_ref(kb, subst, b_resolved, a_resolved)
        }
        (Some("arrow"), Some("arrow")) => {
            unify_arrow(kb, subst, a_resolved, b_resolved)
        }
        (Some("named_tuple"), Some("named_tuple")) => {
            unify_named_tuple(kb, subst, a_resolved, b_resolved)
        }
        (Some("effects_rows"), Some("effects_rows")) => {
            // WI-320 substrate: structural unification on the wrapped
            // EffectExpression. The hash-cons short-circuit at line 4711
            // already caught the both-ground identical case; this arm
            // covers the post-walk case where the wrappers point at
            // structurally-equivalent but distinct TermIds. Row
            // unification proper (Rémy / Lindley-Cheney over the
            // EffectExpression algebra) is WI-307 — when it lands the
            // recursive `unify_types` call here will dispatch into
            // dedicated `present` / `absent` / `open` / `merge` arms
            // instead of falling through to `types_compatible`.
            let a_inner = match kb.get_term(a_resolved) {
                Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "effects_expr"),
                _ => return false,
            };
            let b_inner = match kb.get_term(b_resolved) {
                Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "effects_expr"),
                _ => return false,
            };
            match (a_inner, b_inner) {
                (Some(x), Some(y)) => unify_types(kb, subst, x, y),
                _ => false,
            }
        }
        _ => types_compatible(kb, a_resolved, b_resolved),
    }
}

/// Unify `parameterized(B, [P = V, …])` with `sort_ref(B)`.
///
/// `sort_ref(B)` doesn't pin B's sort-level type parameters — they're
/// the loader-cached unification Vars shared across B's signature
/// (per `sort T = ?` registration in `load.rs`). Binding each P's
/// canonical Var to V in the substitution propagates the parameterized
/// side's bindings into B's return-type and effect positions.
///
/// Bases must match. Type params not bound on the parameterized side
/// stay unbound (caller didn't constrain them — width subtyping).
fn unify_parameterized_with_sort_ref(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    parameterized: TermId,
    sort_ref: TermId,
) -> bool {
    let pbase = match kb.get_term(parameterized) {
        Term::Fn { named_args, .. } => {
            match get_named_arg(kb, named_args, "base") {
                Some(b) => b,
                None => return types_compatible(kb, parameterized, sort_ref),
            }
        }
        _ => return types_compatible(kb, parameterized, sort_ref),
    };
    let pbase_sym = match extract_sort_ref_sym(kb, pbase) {
        Some(s) => s,
        None => return types_compatible(kb, parameterized, sort_ref),
    };
    let sref_sym = match extract_sort_ref_sym(kb, sort_ref) {
        Some(s) => s,
        None => return types_compatible(kb, parameterized, sort_ref),
    };
    if pbase_sym != sref_sym {
        return types_compatible(kb, parameterized, sort_ref);
    }

    let bindings_tid = match kb.get_term(parameterized) {
        Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "bindings"),
        _ => None,
    };
    if let Some(bt) = bindings_tid {
        for binding in list_to_vec(kb, bt) {
            let psym = match binding_param_sym(kb, binding) {
                Some(s) => s,
                None => continue,
            };
            let value = match binding_value(kb, binding) {
                Some(v) => v,
                None => continue,
            };
            let qualified = format!(
                "{}.{}",
                kb.qualified_name_of(pbase_sym),
                kb.resolve_sym(psym),
            );
            let qualified_sym = match kb.try_resolve_symbol(&qualified) {
                Some(s) => s,
                None => continue,
            };
            if let Some(alias_target) = resolve_sort_alias(kb, qualified_sym) {
                if let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) {
                    if !occurs_in(kb, *vid, value) {
                        subst.bind(*vid, value);
                    }
                }
            }
        }
    }
    true
}

/// Occurs check: does `vid` appear anywhere inside `term`?
fn occurs_in(kb: &KnowledgeBase, vid: VarId, term: TermId) -> bool {
    match kb.get_term(term) {
        Term::Var(Var::Global(v)) => *v == vid,
        Term::Fn { pos_args, named_args, .. } => {
            pos_args.iter().any(|t| occurs_in(kb, vid, *t))
                || named_args.iter().any(|(_, t)| occurs_in(kb, vid, *t))
        }
        _ => false,
    }
}

/// Like [`walk_type`] but recurses into `Term::Fn` children so Var
/// bindings propagate into nested positions like `Option[T = Var(vid)]`.
/// Used at call-site result-resolve points (return type, effect row);
/// internal unification keeps using the shallow `walk_type` since the
/// per-functor `unify_parameterized` / `unify_arrow` arms already
/// recurse structurally.
fn walk_type_deep(kb: &mut KnowledgeBase, subst: &Substitution, ty: TermId) -> TermId {
    let resolved = walk_type(kb, subst, ty);
    match kb.get_term(resolved) {
        Term::Fn { .. } => {
            kb.map_fn_children(resolved, |kb, child| walk_type_deep(kb, subst, child))
        }
        _ => resolved,
    }
}

/// Walk a type term through the substitution, resolving Vars and type params.
fn walk_type(kb: &KnowledgeBase, subst: &Substitution, ty: TermId) -> TermId {
    match kb.get_term(ty) {
        Term::Var(Var::Global(vid)) => {
            match subst.resolve_with_term(*vid) {
                Some(bound) => walk_type(kb, subst, bound),
                None => ty,
            }
        }
        Term::Fn { functor, .. } if kb.resolve_sym(*functor) == "sort_ref" => {
            let sym = match extract_sort_ref_sym(kb, ty) {
                Some(s) => s,
                None => return ty,
            };
            // Only resolve the sort_ref through its SortAlias-to-Var if
            // the symbol is a *sort-level type parameter* (registered
            // via `sort T = ?` inside a sort body). Top-level abstract
            // sorts like `sort Term = ?` in anthill.reflect also have a
            // SortAlias-to-Var entry, but they're concrete-but-opaque
            // types from a typer perspective — collapsing every
            // sort_ref(Term) into Term's alias Var would lose the
            // sort_ref form and surface as `TermId(N)` in diagnostics.
            if !is_sort_param_symbol(kb, sym) {
                return ty;
            }
            let alias_target = match resolve_sort_alias(kb, sym) {
                Some(t) => t,
                None => return ty,
            };
            if let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) {
                subst.resolve_with_term(*vid).map_or(alias_target, |bound| walk_type(kb, subst, bound))
            } else {
                alias_target
            }
        }
        _ => ty,
    }
}

/// True iff `sym` is a sort-level type parameter — i.e., its short
/// name is registered in the type_params set of its defining scope's
/// parent sort. Distinguishes `sort T = ?` inside `sort Stream { … }`
/// (which IS a type-param) from `sort Term = ?` at namespace level
/// (which is a top-level abstract sort, not a type parameter).
fn is_sort_param_symbol(kb: &KnowledgeBase, sym: Symbol) -> bool {
    use crate::intern::SymbolDef;
    let SymbolDef::Resolved { scope_raw, .. } = kb.symbols.get(sym) else {
        return false;
    };
    let short_name = kb.resolve_sym(sym);
    kb.symbols.is_type_param(*scope_raw, short_name)
}

/// Look up SortAlias(sort_term, target) for a symbol. Returns the target TermId if found.
///
/// Two passes with exact-Symbol-identity precedence over short-name fallback.
/// The fallback exists for legacy callers that pass a short-name symbol when
/// the SortAlias's pos-arg holds the qualified one. The precedence matters
/// because parameter short names like "T" recur across sorts (Eq.T, Numeric.T,
/// List.T, …) — without exact-match-first the fallback would return whichever
/// alias appeared first in by_functor order, causing proposal-038 / WI-210
/// dispatch to resolve the wrong logical Var.
fn resolve_sort_alias(kb: &KnowledgeBase, sym: Symbol) -> Option<TermId> {
    let alias_sym = kb.try_resolve_symbol("SortAlias")?;
    let sort_name = kb.resolve_sym(sym);
    let find = |matches: fn(&KnowledgeBase, Symbol, Symbol, &str) -> bool| {
        for rid in kb.by_functor(alias_sym) {
            if !kb.is_fact(rid) { continue; }
            let head = kb.rule_head(rid);
            if let Term::Fn { pos_args, .. } = kb.get_term(head) {
                if pos_args.len() >= 2 {
                    if let Term::Fn { functor, .. } = kb.get_term(pos_args[0]) {
                        if matches(kb, *functor, sym, sort_name) {
                            return Some(pos_args[1]);
                        }
                    }
                }
            }
        }
        None
    };
    find(|_, f, s, _| f == s)
        .or_else(|| find(|kb, f, _, n| kb.resolve_sym(f) == n))
}

/// Unify two parameterized types: bases must unify, each binding value must unify.
fn unify_parameterized(kb: &mut KnowledgeBase, subst: &mut Substitution, a: TermId, b: TermId) -> bool {
    let (a_args, b_args) = match (kb.get_term(a), kb.get_term(b)) {
        (Term::Fn { named_args: aa, .. }, Term::Fn { named_args: ba, .. }) => (aa.clone(), ba.clone()),
        _ => return false,
    };

    // Unify bases
    let a_base = get_named_arg(kb, &a_args, "base");
    let b_base = get_named_arg(kb, &b_args, "base");
    match (a_base, b_base) {
        (Some(ab), Some(bb)) => {
            if !unify_types(kb, subst, ab, bb) { return false; }
        }
        _ => return false,
    }

    // Unify bindings by param name
    let a_bindings = get_named_arg(kb, &a_args, "bindings")
        .map(|b| list_to_vec(kb, b)).unwrap_or_default();
    let b_bindings = get_named_arg(kb, &b_args, "bindings")
        .map(|b| list_to_vec(kb, b)).unwrap_or_default();

    for ab in &a_bindings {
        let a_param = binding_param_sym(kb, *ab);
        let a_value = binding_value(kb, *ab);
        if let (Some(param), Some(av)) = (a_param, a_value) {
            let bv = b_bindings.iter()
                .find(|bb| binding_param_sym(kb, **bb) == Some(param))
                .and_then(|bb| binding_value(kb, *bb));
            if let Some(bv) = bv {
                if !unify_types(kb, subst, av, bv) { return false; }
            }
        }
    }

    true
}

/// Unify two arrow types: params, results, and effects must unify.
fn unify_arrow(kb: &mut KnowledgeBase, subst: &mut Substitution, a: TermId, b: TermId) -> bool {
    let (a_args, b_args) = match (kb.get_term(a), kb.get_term(b)) {
        (Term::Fn { named_args: aa, .. }, Term::Fn { named_args: ba, .. }) => (aa.clone(), ba.clone()),
        _ => return false,
    };

    // Unify params
    let a_param = get_named_arg(kb, &a_args, "param");
    let b_param = get_named_arg(kb, &b_args, "param");
    match (a_param, b_param) {
        (Some(ap), Some(bp)) => {
            if !unify_types(kb, subst, ap, bp) { return false; }
        }
        _ => return false,
    }

    // Unify results
    let a_result = get_named_arg(kb, &a_args, "result");
    let b_result = get_named_arg(kb, &b_args, "result");
    match (a_result, b_result) {
        (Some(ar), Some(br)) => {
            if !unify_types(kb, subst, ar, br) { return false; }
        }
        _ => return false,
    }

    // WI-307 v1a: unify the effects rows. Pre-WI-307 this site SKIPPED
    // effects entirely; the row unification arm dispatches the
    // Rémy/Lindley-Cheney algorithm over the `effects_rows(EffectExpression)`
    // payload built by `make_arrow_type`'s canonicalization.
    let a_effects = get_named_arg(kb, &a_args, "effects");
    let b_effects = get_named_arg(kb, &b_args, "effects");
    match (a_effects, b_effects) {
        (Some(ae), Some(be)) => {
            if !unify_effect_rows(kb, subst, ae, be) { return false; }
        }
        // One side missing the effects field — treat as empty row on that
        // side and require the other to also be empty.
        (None, None) => {}
        (Some(ae), None) => {
            let empty = kb.make_effect_expression_empty_row();
            let empty_rows = kb.make_effects_rows_type(empty);
            if !unify_effect_rows(kb, subst, ae, empty_rows) { return false; }
        }
        (None, Some(be)) => {
            let empty = kb.make_effect_expression_empty_row();
            let empty_rows = kb.make_effects_rows_type(empty);
            if !unify_effect_rows(kb, subst, empty_rows, be) { return false; }
        }
    }

    true
}

// ── WI-307 v1a row unification ──────────────────────────────────────────

/// Decompose an arrow.effects field (`effects_rows(EffectExpression)` Type)
/// into (present_labels, open_tail, absent_labels) by structurally walking
/// the EffectExpression algebra through the current substitution.
///
/// Walks substitution at every node — if a row-tail `open(?ρ)` has been
/// bound to a concrete EffectExpression (merge chain etc.) by a prior row
/// unification, the walk recurses into the bound value. So a row that was
/// just `open(?ρ)` becomes its full decomposed shape once ?ρ is resolved.
///
/// `absent_labels` (v1b's `-e` lacks-constraint slot) is collected but not
/// yet consumed by the unifier — v1a is presence-only.
fn decompose_effect_row(
    kb: &KnowledgeBase,
    subst: &Substitution,
    effects_field: TermId,
) -> (Vec<TermId>, Option<TermId>, Vec<TermId>) {
    // Walk the wrapper through substitution; unwrap effects_rows.
    let walked_field = walk_type(kb, subst, effects_field);
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.Type.effects_rows");
    let expr = match (effects_rows_sym, kb.get_term(walked_field)) {
        (Some(er), Term::Fn { functor, named_args, .. }) if *functor == er => {
            match get_named_arg(kb, named_args, "effects_expr") {
                Some(e) => e,
                None => return (Vec::new(), None, Vec::new()),
            }
        }
        // Not an effects_rows wrapper — could be a bare Var (the whole row
        // is itself an unbound row variable, mostly seen in tests building
        // partial arrows). Treat as a single open-tail row.
        (_, Term::Var(_)) => return (Vec::new(), Some(walked_field), Vec::new()),
        _ => return (Vec::new(), None, Vec::new()),
    };

    let mut present = Vec::new();
    let mut absent = Vec::new();
    let mut tail: Option<TermId> = None;
    let mut stack: Vec<TermId> = vec![expr];
    while let Some(node_raw) = stack.pop() {
        let node = walk_type(kb, subst, node_raw);
        match kb.get_term(node) {
            // Unbound Var directly inside the algebra — row-tail.
            Term::Var(_) => {
                // If we somehow already have a tail and this is a different
                // var, the row is malformed. Keep the first; later v1a
                // hardening will reject this.
                if tail.is_none() {
                    tail = Some(node);
                }
            }
            Term::Fn { functor, named_args, .. } => {
                let name = kb.resolve_sym(*functor);
                match name {
                    "empty_row" => {}
                    "present" => {
                        if let Some(l) = get_named_arg(kb, named_args, "label") {
                            present.push(l);
                        }
                    }
                    "absent" => {
                        if let Some(l) = get_named_arg(kb, named_args, "label") {
                            absent.push(l);
                        }
                    }
                    "open" => {
                        if let Some(t) = get_named_arg(kb, named_args, "tail") {
                            // Re-walk through the open-tail: a bound row
                            // variable resolves to a concrete EffectExpression
                            // here. Pushing onto the stack continues the walk.
                            stack.push(t);
                        }
                    }
                    "merge" => {
                        if let Some(r) = get_named_arg(kb, named_args, "right") {
                            stack.push(r);
                        }
                        if let Some(l) = get_named_arg(kb, named_args, "left") {
                            stack.push(l);
                        }
                    }
                    _ => {
                        // Unknown functor inside an EffectExpression —
                        // upstream bug. Surface in dev, tolerate in release.
                        debug_assert!(
                            false,
                            "decompose_effect_row: unexpected functor `{}`",
                            name
                        );
                    }
                }
            }
            _ => {
                debug_assert!(
                    false,
                    "decompose_effect_row: unexpected term shape"
                );
            }
        }
    }

    (present, tail, absent)
}

/// Pair present-labels from two rows by greedy structural unification.
///
/// Returns `(only_a, only_b)` — labels left over once every successful
/// pairing has been unified through `subst`. The canonical form
/// (`build_canonical_effects_rows`) sorts labels by `type_display_name`, so
/// parallel rows present labels in the same order and the greedy walk
/// produces the natural pairing for the common case (`{Modify[c], Error}`
/// vs `{Modify[c], Error}`).
///
/// **Limitation (v1a)** — no rollback. If a greedy pair unifies but a
/// downstream tail-binding step fails, the substitution is contaminated. In
/// practice the typer wraps unification calls in higher-level error
/// reporting, so the failed unification produces a top-level type error
/// rather than silent corruption. Backtracking is a v1b nicety.
fn pair_present_labels(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_present: &[TermId],
    b_present: &[TermId],
) -> (Vec<TermId>, Vec<TermId>) {
    let mut b_matched = vec![false; b_present.len()];
    let mut only_a: Vec<TermId> = Vec::new();
    for &al in a_present {
        let mut paired = false;
        for (i, &bl) in b_present.iter().enumerate() {
            if b_matched[i] {
                continue;
            }
            // Functor-name pre-filter: cheap rejection before invoking
            // unify_types (which may bind the substitution on failure for
            // partial structural success). This is just a hint — the
            // authoritative match is unify_types' return value.
            let af = type_functor_name(kb, al);
            let bf = type_functor_name(kb, bl);
            if af != bf {
                continue;
            }
            if unify_types(kb, subst, al, bl) {
                b_matched[i] = true;
                paired = true;
                break;
            }
        }
        if !paired {
            only_a.push(al);
        }
    }
    let only_b: Vec<TermId> = b_present
        .iter()
        .enumerate()
        .filter(|(i, _)| !b_matched[*i])
        .map(|(_, &t)| t)
        .collect();
    (only_a, only_b)
}

/// Bind a row-tail variable to a synthesized EffectExpression representing
/// `extra_labels ++ (open(final_tail) | empty_row)`.
///
/// `tail` is the open()'s tail field (a `Term::Var(Var::Global(vid))` in
/// practice). The binding `vid := merge(present(l1), …, merge(present(ln),
/// <open(final_tail) or empty_row>))` plays the role of the row-rewrite
/// equation: subsequent `decompose_effect_row` calls that walk through the
/// substitution recover the labels and the new tail position.
///
/// When `final_tail` is `None`, the tail closes (`empty_row`); when
/// `Some(fresh)`, it stays open and `fresh` becomes the shared extension
/// point between two open rows.
fn bind_row_tail(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    tail: TermId,
    extra_labels: &[TermId],
    final_tail: Option<TermId>,
) -> bool {
    let vid = match kb.get_term(tail) {
        Term::Var(Var::Global(vid)) => *vid,
        // Tail isn't a bindable Global Var — only succeed if the binding
        // would have been a no-op (no extras, no fresh tail).
        _ => return extra_labels.is_empty() && final_tail.is_none(),
    };

    // Build the inner tail: open(fresh) if shared, empty_row if closed.
    let inner = match final_tail {
        Some(ft) => kb.make_effect_expression_open(ft),
        None => kb.make_effect_expression_empty_row(),
    };
    // Right-fold extras into the inner tail.
    let mut acc = inner;
    for &l in extra_labels.iter().rev() {
        let p = kb.make_effect_expression_present(l);
        acc = kb.make_effect_expression_merge(p, acc);
    }

    if occurs_in(kb, vid, acc) {
        return false;
    }
    subst.bind(vid, acc);
    !subst.is_contradiction()
}

/// WI-307 v1a row unification — the Rémy/Lindley-Cheney algorithm on
/// `effects_rows(EffectExpression)` payloads.
///
/// 1. Decompose each row into (present, tail, absent) through the current
///    substitution.
/// 2. Pair common labels by greedy unification (canonical sort makes the
///    parallel order natural).
/// 3. Resolve tails:
///    - both closed, no extras → trivially unify;
///    - both closed but extras present → reject (sets differ);
///    - one open, the other closed → other-side extras absorbed by the
///      open tail, closing it;
///    - both open → fresh shared tail `?ρ'`; each side's tail binds to its
///      own extras + `open(?ρ')`.
///
/// **Presence-only** for v1a — `absent` labels (`-e` lacks-constraints) are
/// collected during decomposition but the unifier doesn't reject on them.
/// v1b's `lacks` arm extends this.
fn unify_effect_rows(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_effects: TermId,
    b_effects: TermId,
) -> bool {
    // Fast path: identical TermIds — hash-cons identity covers the canonical
    // case where both arrows shared an effects field.
    if a_effects == b_effects {
        return true;
    }

    let (a_present, a_tail, _a_absent) = decompose_effect_row(kb, subst, a_effects);
    let (b_present, b_tail, _b_absent) = decompose_effect_row(kb, subst, b_effects);

    let (only_a, only_b) = pair_present_labels(kb, subst, &a_present, &b_present);

    match (a_tail, b_tail) {
        (None, None) => only_a.is_empty() && only_b.is_empty(),
        (None, Some(b_t)) => {
            // a is closed, b is open.
            // a has no tail to absorb b's extras — b's extras must be empty.
            if !only_b.is_empty() {
                return false;
            }
            // b's tail absorbs a's extras, closing b.
            bind_row_tail(kb, subst, b_t, &only_a, None)
        }
        (Some(a_t), None) => {
            // Symmetric.
            if !only_a.is_empty() {
                return false;
            }
            bind_row_tail(kb, subst, a_t, &only_b, None)
        }
        (Some(a_t), Some(b_t)) => {
            // Both open. If tails are already the same Var and no extras,
            // we're done — avoids allocating a fresh tail.
            let a_walked = walk_type(kb, subst, a_t);
            let b_walked = walk_type(kb, subst, b_t);
            if a_walked == b_walked && only_a.is_empty() && only_b.is_empty() {
                return true;
            }
            // Fresh shared tail var ρ'. Both sides extend their respective
            // labels and end in `open(ρ')` — afterward a future
            // decompose_effect_row reveals (only_a + only_b) as present
            // labels with shared tail ρ'.
            let fresh_sym = kb.intern("?rho");
            let fresh_vid = kb.fresh_var(fresh_sym);
            let fresh_var = kb.alloc(Term::Var(Var::Global(fresh_vid)));
            bind_row_tail(kb, subst, a_t, &only_b, Some(fresh_var))
                && bind_row_tail(kb, subst, b_t, &only_a, Some(fresh_var))
        }
    }
}

/// Unify two named tuple types: matching fields must unify.
fn unify_named_tuple(kb: &mut KnowledgeBase, subst: &mut Substitution, a: TermId, b: TermId) -> bool {
    let (a_args, b_args) = match (kb.get_term(a), kb.get_term(b)) {
        (Term::Fn { named_args: aa, .. }, Term::Fn { named_args: ba, .. }) => (aa.clone(), ba.clone()),
        _ => return false,
    };

    let a_fields = get_named_arg(kb, &a_args, "fields")
        .map(|f| list_to_vec(kb, f)).unwrap_or_default();
    let b_fields = get_named_arg(kb, &b_args, "fields")
        .map(|f| list_to_vec(kb, f)).unwrap_or_default();

    // Every field in b must have a matching field in a that unifies
    for bf in &b_fields {
        let b_name = field_name_sym(kb, *bf);
        let b_type = field_type(kb, *bf);
        if let (Some(name), Some(bt)) = (b_name, b_type) {
            let at = a_fields.iter()
                .find(|af| field_name_sym(kb, **af) == Some(name))
                .and_then(|af| field_type(kb, *af));
            match at {
                Some(at) => {
                    if !unify_types(kb, subst, at, bt) { return false; }
                }
                None => return false,
            }
        }
    }

    true
}

// ── Type compatibility (subtyping) ─────────────────────────────

/// Check if `actual` type is compatible with (subtype of) `expected` type.
/// Works on Type entity terms: sort_ref, parameterized, arrow, named_tuple, type_var, nothing.
/// Lattice `≤` on type terms — `actual <: expected` with reflexivity.
/// Alias for [`types_compatible`]; prefer this name when the directional
/// nature of the relation matters (subtype check, effect-element
/// compatibility, etc.). The strict (irreflexive) version is
/// [`is_subtype`].
pub fn types_lesseq(kb: &KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    types_compatible(kb, actual, expected)
}

pub fn types_compatible(kb: &KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    if actual == expected {
        return true;
    }

    let actual_functor = type_functor_name(kb, actual);
    let expected_functor = type_functor_name(kb, expected);

    // type_var is compatible with anything (wildcard for inference)
    if actual_functor == Some("type_var") || expected_functor == Some("type_var") {
        return true;
    }

    // nothing is bottom — compatible with any type
    if actual_functor == Some("nothing") {
        return true;
    }

    match (actual_functor, expected_functor) {
        (Some("sort_ref"), Some("sort_ref")) => {
            sort_ref_compatible(kb, actual, expected)
        }
        (Some("parameterized"), Some("parameterized")) => {
            parameterized_compatible(kb, actual, expected)
        }
        // Name-binding normalization: a bare sort name `S` is `S` with
        // its type params unconstrained — it is compatible with any
        // instantiation `S[bindings]` and vice versa. The typer infers
        // a bare type for nullary constructors (`nil()` → `List`,
        // `none()` → `Option`), so a body whose branches mix `List` and
        // `List[T = Row]` must still satisfy a `List[T = Row]` return
        // annotation. Only the base sort identity is checked here; the
        // bindings on the parameterized side stand unconstrained
        // against the bare side.
        (Some("sort_ref"), Some("parameterized")) => {
            base_sort_compatible(kb, actual, parameterized_base(kb, expected))
        }
        (Some("parameterized"), Some("sort_ref")) => {
            base_sort_compatible(kb, expected, parameterized_base(kb, actual))
        }
        (Some("arrow"), Some("arrow")) => {
            arrow_compatible(kb, actual, expected)
        }
        // `arrow` is the typer's shorthand for the stdlib `Function[A, B, E]`
        // (see `arrow_parts`), so a lambda's `arrow(Int, Int)` body satisfies
        // a declared `Function[Int, Int]` return and vice versa. (WI-289)
        (Some("arrow"), Some("parameterized")) | (Some("parameterized"), Some("arrow")) => {
            arrow_function_compatible(kb, actual, expected)
        }
        (Some("named_tuple"), Some("named_tuple")) => {
            named_tuple_compatible(kb, actual, expected)
        }
        (Some("effects_rows"), Some("effects_rows")) => {
            // WI-320 substrate: compatibility on the wrapped EffectExpression.
            // The line-5049 short-circuit (`actual == expected`) handled the
            // identical-TermId case via hash-consing; this arm catches the
            // structurally-equivalent-but-distinct-TermId case. Row
            // subsumption (open-tail absorbing extra labels; `lacks` check)
            // is WI-307; until then this is conservative — distinct logical-
            // var positions inside differently-allocated EffectExpression
            // terms compare incompatible. Sound (no false positives).
            let a_inner = match kb.get_term(actual) {
                Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "effects_expr"),
                _ => return false,
            };
            let b_inner = match kb.get_term(expected) {
                Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "effects_expr"),
                _ => return false,
            };
            match (a_inner, b_inner) {
                (Some(x), Some(y)) => types_compatible(kb, x, y),
                _ => false,
            }
        }
        _ => false,
    }
}

/// Compatibility between the typer's `arrow(param, result, effects)` and the
/// stdlib `Function[A, B, E]` (in either order) — they denote the same
/// callable type. Decomposes both via [`arrow_parts`] (which yields `None`
/// for a non-`Function` parameterized type, so `arrow` vs `List[T]` stays
/// incompatible) and checks param + result compatibility. (WI-289)
fn arrow_function_compatible(kb: &KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    match (arrow_parts(kb, actual), arrow_parts(kb, expected)) {
        (Some((a_param, a_result, _)), Some((b_param, b_result, _))) => {
            // Param is contravariant (expected param <: actual param) and
            // result covariant — matching `arrow_compatible`. Effects are
            // not compared here, also as in `arrow_compatible` (effect
            // discharge is checked separately on the operation row).
            let params_ok = match (a_param, b_param) {
                (Some(ap), Some(bp)) => types_compatible(kb, bp, ap),
                _ => true,
            };
            params_ok && types_compatible(kb, a_result, b_result)
        }
        _ => false,
    }
}

/// The `base` sort_ref of a `parameterized(base, bindings)` type term.
fn parameterized_base(kb: &KnowledgeBase, ty: TermId) -> Option<TermId> {
    if let Term::Fn { named_args, .. } = kb.get_term(ty) {
        return get_named_arg(kb, named_args, "base");
    }
    None
}

/// Compare a `sort_ref` against an optional `sort_ref` base (extracted
/// from a parameterized type's `base` field). Used by the
/// bare-vs-parameterized arms of `types_compatible` — only the base
/// sort identity matters; the parameterized side's bindings are left
/// unconstrained against the bare side.
fn base_sort_compatible(kb: &KnowledgeBase, sort_ref: TermId, base: Option<TermId>) -> bool {
    match base {
        Some(b) => sort_ref_compatible(kb, sort_ref, b),
        None => false,
    }
}

/// Get the functor name of a Type entity term.
fn type_functor_name<'a>(kb: &'a KnowledgeBase, ty: TermId) -> Option<&'a str> {
    match kb.get_term(ty) {
        Term::Fn { functor, .. } => Some(kb.resolve_sym(*functor)),
        _ => None,
    }
}

/// Strict subtype check: actual is a proper subtype of expected.
/// `is_subtype(A, A)` is false. `is_subtype(red, Color)` is true.
pub fn is_subtype(kb: &KnowledgeBase, sub: TermId, sup: TermId) -> bool {
    sub != sup && types_compatible(kb, sub, sup)
}

/// WI-287: one step up the entity→enclosing-sort chain. `Some(parent
/// sort as a type)` when `t` is a `sort_ref` to an entity nested in a
/// sort; `None` for a top-level sort (no enclosing parent) or a
/// non-`sort_ref` type. Lets [`join_types`] find a common supertype of
/// two distinct entity-typed branches even when leaves weren't already
/// widened to their sort.
fn widen_to_parent_sort(kb: &mut KnowledgeBase, t: TermId) -> Option<TermId> {
    let sym = extract_sort_ref_sym(kb, t)?;
    let parent = kb.constructor_parent_sort(sym)?;
    Some(sort_term_to_type(kb, parent))
}

/// WI-287: a common supertype (an upper bound) of two branch types in the
/// (top-less) Type lattice, or `None` when they have none. NOT necessarily
/// the strict least upper bound: a polymorphic `none()`/`nil()` typed bare
/// `Option`/`List` could in principle specialize to the sibling branch's
/// `Option[T=Int]` (making the strict lub `Option[T=Int]`), but the typer
/// neither tracks that a bare type is the polymorphic kind nor unifies it
/// here, so for the bare-vs-parameterized case this returns the more-
/// general type instead (see [`more_general_type`]) — a sound upper bound,
/// not the lub. Commutative: `join_types(a, b) == join_types(b, a)`, so
/// folding branches is order-independent. A wildcard (`type_var`) branch
/// imposes no constraint, so the other branch's type is the result. When
/// exactly one type conforms to the other (`types_compatible`, covering
/// entity→sort and `requires`-refine) the supertype wins; when both
/// directions hold (identical, or bare-vs-parameterized) [`more_general_type`]
/// decides; failing both, the sides are widened one level up the
/// entity→enclosing-sort chain and retried. The climb is bounded — each
/// step strictly ascends or a side stops widening — so it terminates.
fn join_types(kb: &mut KnowledgeBase, a: TermId, b: TermId) -> Option<TermId> {
    if type_functor_name(kb, a) == Some("type_var") {
        return Some(b);
    }
    if type_functor_name(kb, b) == Some("type_var") {
        return Some(a);
    }
    let (mut a, mut b) = (a, b);
    // Bound defensively against any pathological parent cycle; real
    // entity→sort chains are a single level.
    for _ in 0..64 {
        match (types_compatible(kb, a, b), types_compatible(kb, b, a)) {
            // `a <: b` only: `b` is the supertype.
            (true, false) => return Some(b),
            // `b <: a` only: `a` is the supertype.
            (false, true) => return Some(a),
            // Mutually compatible: identical types, or the bare-vs-
            // parameterized normalization where both directions hold
            // (`Option` vs `Option[T=Int]`). We return the less-
            // constrained side — a sound upper bound, deliberately more
            // general than the strict lub (which would keep the bindings)
            // — picked deterministically so the result is order-
            // independent. (Different parameterizations like
            // `List[Int]`/`List[String]` are NOT mutually compatible — the
            // parameterized arm checks bindings — so they fall through to
            // the widen step.)
            (true, true) => return Some(more_general_type(kb, a, b)),
            // Incomparable: widen the entity side(s) one level and retry.
            (false, false) => {
                let wa = widen_to_parent_sort(kb, a);
                let wb = widen_to_parent_sort(kb, b);
                match (wa, wb) {
                    (None, None) => return None,
                    _ => {
                        if let Some(x) = wa {
                            a = x;
                        }
                        if let Some(y) = wb {
                            b = y;
                        }
                    }
                }
            }
        }
    }
    None
}

/// WI-287: between two *mutually*-`types_compatible` types, the upper
/// bound to keep. This arm is reached only when `types_compatible` holds
/// in BOTH directions, which (apart from identical types) means the
/// bare-vs-parameterized normalization: `Option` and `Option[T=Int]` each
/// conform to the other (a bare sort is "compatible with any instantiation
/// and vice versa"). The *strict* lub here is the parameterized side
/// (`Option[T=Int]`): a polymorphic `none()` specializes to it. But the
/// typer can't tell a polymorphic bare (`none()`/`nil()`, safe to
/// specialize) from a declared `-> Option` carrying some other unknown `T`
/// (where claiming `Int` would be wrong), so we deliberately return the
/// bare (more-general) side — a sound upper bound that never over-claims a
/// binding, at the cost of dropping the strict lub's precision. A
/// return/annotation pins the bindings via checked mode regardless; this
/// only affects annotation-free synthesis. Returns `a` when neither side
/// is parameterized (identical types). Keeps [`join_types`] commutative.
fn more_general_type(kb: &KnowledgeBase, a: TermId, b: TermId) -> TermId {
    match (type_functor_name(kb, a), type_functor_name(kb, b)) {
        (Some("sort_ref"), Some("parameterized")) => a,
        (Some("parameterized"), Some("sort_ref")) => b,
        _ => a,
    }
}

/// WI-287: the result type of a branching expression (`match` / `if`),
/// computed from *every* branch body instead of taking branch 0 (the old
/// soundness gap). `construct` names the form for diagnostics ("match",
/// "if"); `branch_tys` are the branch-body types in source order.
///
/// When an expected type is present every branch must conform to it
/// (`types_compatible`, covering entity→sort and `requires`-refine) —
/// the enforcement the old code skipped, since it only type-checked the
/// synthesized type, which was branch 0. The result is the join of the
/// branch types ([`join_types`] — a sound common supertype, not strictly
/// the lub), preferred for precision but never widened past the expected
/// type and never collapsed to a `type_var` hint (which would lose the
/// concrete branch type when the expression is passed as a generic
/// argument). The Type lattice is top-less: branches with no common
/// supertype and no expected type to bound them (e.g. `Int` vs
/// `String`) are a type error, reported against the branch that breaks
/// the join.
fn compute_branch_join_type(
    kb: &mut KnowledgeBase,
    branch_tys: &[(TermId, Option<Span>)],
    expected: Option<TermId>,
    construct: &str,
) -> Result<TermId, TypeError> {
    // Intern once up front so the type-lattice borrows below can take
    // `kb` immutably without colliding with a deferred `kb.intern`.
    let branch_ctx = TypeErrorContext::Rule {
        name: kb.intern(construct),
        field: RuleField::Whole,
    };
    let (first_ty, _) = match branch_tys.first() {
        Some(&b) => b,
        None => {
            return Err(TypeError::Other {
                span: None,
                context: branch_ctx,
                expected: format!("non-empty {construct} expression"),
                actual: format!("{construct} with no branches"),
            })
        }
    };

    // Checked mode: every branch must conform to the expected type
    // (`types_compatible` covers entity→sort and `requires`-refine).
    // This is the enforcement the old code skipped — it only ever
    // type-checked the synthesized type, which was branch 0.
    if let Some(exp) = expected {
        for &(bt, span) in branch_tys {
            if !types_compatible(kb, bt, exp) {
                return Err(TypeError::TypeMismatch {
                    span,
                    context: branch_ctx,
                    expected: exp,
                    actual: bt,
                });
            }
        }
    }

    // Synthesized type: the join (common supertype) of the branch types. Track the
    // branch that breaks the join (no common supertype) for diagnostics.
    let mut acc = first_ty;
    let mut clash: Option<(TermId, Option<Span>)> = None;
    for &(bt, span) in &branch_tys[1..] {
        match join_types(kb, acc, bt) {
            Some(j) => acc = j,
            None => {
                clash = Some((bt, span));
                break;
            }
        }
    }

    match (clash, expected) {
        // The join exists: prefer this precise synthesized type, but
        // never widen past an expected type the branches already satisfy
        // (and never collapse a precise join to a `type_var` hint).
        (None, None) => Ok(acc),
        (None, Some(exp)) => {
            if acc == exp || types_compatible(kb, acc, exp) {
                Ok(acc)
            } else {
                Ok(exp)
            }
        }
        // No climb-computed join, but every branch conforms to `expected`
        // (checked above) — `expected` is their common upper bound. This
        // is the `requires`-refine case the entity-parent climb can't see.
        // A `type_var` `exp`, though, is no real bound (it's compatible
        // with anything), so accepting it would collapse a genuine clash
        // to a wildcard — report the clash instead, mirroring the
        // type_var guard in the `(None, Some)` arm above.
        (Some((bt, span)), Some(exp)) => {
            if type_functor_name(kb, exp) == Some("type_var") {
                Err(TypeError::TypeMismatch {
                    span,
                    context: branch_ctx,
                    expected: acc,
                    actual: bt,
                })
            } else {
                Ok(exp)
            }
        }
        // No expected type and no common supertype — the top-less lattice
        // has no join, so the branch types genuinely clash.
        (Some((bt, span)), None) => Err(TypeError::TypeMismatch {
            span,
            context: branch_ctx,
            expected: acc,
            actual: bt,
        }),
    }
}

/// sort_ref(name: A) compatible with sort_ref(name: B)
/// if A == B, or A is_entity_of B, or A refines B via requires.
fn sort_ref_compatible(kb: &KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    let actual_sym = match extract_sort_ref_sym(kb, actual) {
        Some(s) => s,
        None => return false,
    };
    let expected_sym = match extract_sort_ref_sym(kb, expected) {
        Some(s) => s,
        None => return false,
    };

    sort_sym_compatible(kb, actual_sym, expected_sym)
}

/// Check if sort symbol A is compatible with sort symbol B:
/// same symbol, entity_of, or refines via requires chain.
fn sort_sym_compatible(kb: &KnowledgeBase, actual_sym: Symbol, expected_sym: Symbol) -> bool {
    if actual_sym == expected_sym {
        return true;
    }

    // Name-based equality (handles qualified vs short name)
    let actual_name = kb.resolve_sym(actual_sym);
    let expected_name = kb.resolve_sym(expected_sym);
    if actual_name == expected_name {
        return true;
    }

    // Entity subtyping: actual is entity of parent sort.
    // Check both direct match and transitive (parent's requires chain).
    if let Some(parent_tid) = kb.constructor_parent_sort(actual_sym) {
        if let Term::Fn { functor: parent_functor, .. } = kb.get_term(parent_tid) {
            if sort_sym_compatible(kb, *parent_functor, expected_sym) {
                return true;
            }
        }
    }

    // Requires/refines: A refines B if A requires B (directly or transitively)
    if sort_refines(kb, actual_sym, expected_sym) {
        return true;
    }

    false
}

// ── Requires chain ─────────────────────────────────────────────

/// A direct requires entry: sort A requires spec B with the given SortView term.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RequiresEntry {
    /// The base sort symbol of the required spec (e.g., Eq in `requires Eq[T=Int]`).
    pub required_sort: Symbol,
    /// The full SortView term (carries bindings like T=Int, combine=add).
    pub spec: TermId,
}

/// WI-230 — tree-shaped declaration of a sort's `requires` chain. Each
/// node holds one `RequiresEntry` plus a recursive `Vec` of sub-entries
/// (the required spec's *own* `requires`, transitively). Substitution
/// is composed top-down so each node's `entry.spec` carries the
/// *root-scoped* view of bindings — Eq in `Wi222Outer requires Ordered
/// requires Eq` reads `T = Wi222Outer.T` directly, not `T = Ordered.T`.
///
/// This mirrors the runtime arena's `RequirementSlot` tree shape (slot
/// = node, sub-handles = sub_requires) and the typer's
/// `ResolvedRequiresNode::Conditional { sub_resolutions }`. All three layers
/// now share one tree skeleton; consumers can walk them by the same
/// recursion.
#[derive(Clone, Debug)]
pub struct RequiresNode {
    pub entry: RequiresEntry,
    pub sub_requires: Vec<RequiresNode>,
}

impl RequiresNode {
    /// Walk the tree and accumulate every node's entry into a flat list
    /// (pre-order). Back-compat for callers that consumed the old
    /// `Vec<RequiresEntry>` shape; new code should walk the tree directly.
    pub fn flatten_into(&self, out: &mut Vec<RequiresEntry>) {
        out.push(self.entry.clone());
        for sub in &self.sub_requires {
            sub.flatten_into(out);
        }
    }
}

/// WI-230 flatten helper for a forest of top-level nodes (the shape
/// `requires_tree` returns).
pub fn flatten_requires_tree(nodes: &[RequiresNode]) -> Vec<RequiresEntry> {
    let mut out = Vec::new();
    for node in nodes {
        node.flatten_into(&mut out);
    }
    out
}

/// Collect the full transitive requires chain for a sort.
/// Returns all (required_sort_sym, spec_term) pairs reachable from `sort_sym`.
///
/// WI-230: now a thin wrapper over `requires_tree` + `flatten_requires_tree`.
/// Substituted bindings flow through (each entry's spec is root-scoped),
/// which differs from the pre-WI-230 behavior of returning each entry
/// in its *declaring* sort's view. Consumers that compared bindings via
/// `dispatch_values_match` continue to work — the equivalence is
/// preserved under symmetric matching with type-param wildcards.
///
/// Takes `&mut KnowledgeBase` because substitution composition may
/// allocate freshly-substituted `Term::Fn` nodes. Consumers that only
/// read `required_sort` (and never compare bindings) should use
/// `requires_chain_flat` instead — it doesn't substitute and so
/// preserves the `&KnowledgeBase` signature.
pub fn requires_chain(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Vec<RequiresEntry> {
    let tree = requires_tree(kb, sort_sym);
    flatten_requires_tree(&tree)
}

/// Synthesize the requirement-param name for each entry of
/// `parent_sort`'s transitive `requires` chain. Returns `Rc<Vec<Symbol>>`
/// in chain order — index `k` is chain slot `k`. Memoized on
/// `synth_req_names_cache`; invalidated alongside `requires_chain` caches
/// when new `SortRequiresInfo` facts are asserted.
///
/// The name is `__req_<spec short name, lowercased>`; chain entries that
/// share that base (two-of-the-same-spec, or two specs with the same
/// short name) are disambiguated by the entry's hash-consed `spec`
/// TermId — content-derived, never positional, so the name stays a pure
/// function of `(kb, parent_sort)`. Both the IR emitter (`req_insertion`)
/// and eval's frame-push call this, so they compute identical names. The
/// Self slot (`__req_self`) is not part of the chain — frame-push and
/// the emitter handle it separately.
///
/// Uses `requires_chain` (always substitution-composed) rather than
/// `requires_chain_flat` (whose bindings depend on tree-cache state),
/// so the names are deterministic across the typer and eval passes.
pub fn synth_req_names(kb: &mut KnowledgeBase, parent_sort: Symbol) -> Rc<Vec<Symbol>> {
    if let Some(cached) = kb.synth_req_names_cache.borrow().get(&parent_sort) {
        return cached.clone();
    }
    let chain = requires_chain(kb, parent_sort);
    let mut bases: Vec<String> = Vec::with_capacity(chain.len());
    for entry in &chain {
        let mut s = String::from("__req_");
        push_short_lc(kb, entry.required_sort, &mut s);
        bases.push(s);
    }
    let mut counts: HashMap<&str, usize> = HashMap::new();
    for b in &bases {
        *counts.entry(b.as_str()).or_default() += 1;
    }
    let mut out: Vec<Symbol> = Vec::with_capacity(chain.len());
    for (entry, base) in chain.iter().zip(bases.iter()) {
        let name = if counts[base.as_str()] > 1 {
            format!("{base}_{}", entry.spec.raw())
        } else {
            base.clone()
        };
        out.push(kb.intern(&name));
    }
    let rc = Rc::new(out);
    kb.synth_req_names_cache.borrow_mut().insert(parent_sort, rc.clone());
    rc
}

/// The requirement-param name for chain slot `idx` of `parent_sort`'s
/// `requires` chain. Thin lookup over [`synth_req_names`]; `None` iff
/// `idx` is out of range.
pub fn req_name_for_chain_index(
    kb: &mut KnowledgeBase,
    parent_sort: Symbol,
    idx: usize,
) -> Option<Symbol> {
    synth_req_names(kb, parent_sort).get(idx).copied()
}

/// Append `sym`'s short name (last dotted segment), lowercased with
/// non-alphanumeric characters mapped to `_`, to `out` — for building
/// identifier-safe synthesized names.
fn push_short_lc(kb: &KnowledgeBase, sym: Symbol, out: &mut String) {
    let name = kb.resolve_sym(sym);
    let short = name.rsplit('.').next().unwrap_or(name);
    for ch in short.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push('_');
        }
    }
}

/// WI-230 — pre-WI-230 flat chain (no substitution composition). Used
/// by consumers that only filter on `required_sort` and don't read the
/// spec bindings — `sort_refines`, `check_obligations`,
/// `seed_entry_requirements`, etc. Keeps `&KnowledgeBase` so callers
/// up the `types_compatible` chain don't need to convert to `&mut`.
///
/// Memoized on the same `requires_tree_cache` as `requires_tree` since
/// the flat shape can be derived by flattening the tree. The
/// substituted bindings in the tree are dropped in the flatten step
/// (consumers of the flat form ignore bindings anyway).
pub fn requires_chain_flat(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<RequiresEntry> {
    if let Some(cached) = kb.requires_tree_cache.borrow().get(&sort_sym) {
        return flatten_requires_tree(&cached);
    }
    // No cache yet — build the flat chain directly (without substitution)
    // and skip the tree-cache write (we don't have &mut). Subsequent
    // calls on a populated tree cache hit the fast path above.
    let mut result = Vec::new();
    let mut visited: Vec<Symbol> = Vec::new();
    collect_requires_unsubstituted(kb, sort_sym, &mut result, &mut visited);
    result
}

/// WI-230 internal: the pre-WI-230 transitive walk, without
/// substitution composition. Equivalent to the old `collect_requires`.
/// Used as a fallback by `requires_chain_flat` when the tree cache
/// isn't yet populated for the queried sort.
fn collect_requires_unsubstituted(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
    result: &mut Vec<RequiresEntry>,
    visited: &mut Vec<Symbol>,
) {
    if visited.contains(&sort_sym) { return; }
    visited.push(sort_sym);
    for entry in direct_requires(kb, sort_sym) {
        result.push(entry.clone());
        collect_requires_unsubstituted(kb, entry.required_sort, result, visited);
    }
}

/// WI-230 — build the substitution-composed `requires` tree for
/// `sort_sym`. Top-level memoized on `kb.requires_tree_cache`: first
/// call walks `SortRequiresInfo` and substitutes; subsequent calls
/// for the same sort return the same `Rc<Vec<RequiresNode>>` from cache.
pub fn requires_tree(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Rc<Vec<RequiresNode>> {
    if let Some(cached) = kb.requires_tree_cache.borrow().get(&sort_sym) {
        return cached.clone();
    }
    let mut visited: Vec<Symbol> = Vec::new();
    let nodes = build_requires_tree(kb, sort_sym, &HashMap::new(), &mut visited);
    let rc = Rc::new(nodes);
    kb.requires_tree_cache
        .borrow_mut()
        .insert(sort_sym, rc.clone());
    rc
}

/// WI-230 internal: recursive tree builder. Threads a substitution map
/// (`subst`) from parent into the child level — at each step, the
/// child's raw spec gets its `Ref(<parent's-param-qualified>)` atoms
/// rewritten to whatever the parent bound them to. Returns the list
/// of top-level RequiresNodes (one per direct `requires` of `sort_sym`).
fn build_requires_tree(
    kb: &mut KnowledgeBase,
    sort_sym: Symbol,
    subst: &HashMap<Symbol, TermId>,
    visited: &mut Vec<Symbol>,
) -> Vec<RequiresNode> {
    if visited.contains(&sort_sym) {
        // Cycle break — return empty so siblings still get walked.
        return Vec::new();
    }
    visited.push(sort_sym);

    let raw_entries = direct_requires(kb, sort_sym);
    let mut nodes = Vec::with_capacity(raw_entries.len());
    for raw in raw_entries {
        let substituted_spec = substitute_in_spec(kb, raw.spec, subst);
        let entry = RequiresEntry {
            required_sort: raw.required_sort,
            spec: substituted_spec,
        };
        let child_subst = build_child_subst_map(kb, &entry);
        let sub_requires = build_requires_tree(kb, raw.required_sort, &child_subst, visited);
        nodes.push(RequiresNode { entry, sub_requires });
    }

    visited.pop();
    nodes
}

/// WI-230 internal: walk `SortRequiresInfo` for one sort and return
/// its direct (non-transitive) requires entries. Same logic as the
/// pre-WI-230 `collect_requires` but without the recursive descent —
/// the tree builder owns recursion.
fn direct_requires(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<RequiresEntry> {
    let mut out = Vec::new();
    let Some(requires_sym) = kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo") else {
        return out;
    };

    for rid in kb.by_functor(requires_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        // Check that this SortRequiresInfo is for our sort. `same_symbol`
        // keys on resolved-Symbol / qualified-name identity so a fact
        // for anthill.cli.Main is not mistaken for one about
        // anthill.todo.Main.
        let sort_ref_tid = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "sort_ref")
            .map(|(_, v)| *v)
        {
            Some(t) => t,
            None => continue,
        };
        let sr_functor = match kb.get_term(sort_ref_tid) {
            Term::Fn { functor, .. } => *functor,
            _ => continue,
        };
        if !same_symbol(kb, sr_functor, sort_sym) {
            continue;
        }

        // Extract spec (SortView) and the base sort it describes.
        let spec_tid = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "spec")
            .map(|(_, v)| *v)
        {
            Some(t) => t,
            None => continue,
        };
        let base_functor = match kb.get_term(spec_tid) {
            Term::Fn { functor, pos_args, named_args, .. } if !pos_args.is_empty() => {
                match kb.get_term(pos_args[0]) {
                    Term::Fn { functor, .. } => *functor,
                    _ => continue,
                }
            }
            Term::Fn { functor, pos_args, named_args, .. }
                if pos_args.is_empty() && named_args.is_empty() =>
            {
                *functor
            }
            _ => continue,
        };

        out.push(RequiresEntry { required_sort: base_functor, spec: spec_tid });
    }
    out
}

/// WI-230 internal: substitution-aware deep walk. Replaces both
/// `Term::Ref(s)` AND nullary `Term::Fn(s, [], [])` (the loader's
/// alternative encoding for a bare name reference; see WI-224's
/// `substitute_impl_params_alloc`) where `s` is in `map` with the
/// mapped TermId. Recurses into non-nullary `Term::Fn` children.
/// Allocates fresh `Term::Fn` nodes only when a child was actually
/// rewritten (preserves hash-cons identity for unchanged sub-terms).
fn substitute_in_spec(
    kb: &mut KnowledgeBase,
    spec: TermId,
    map: &HashMap<Symbol, TermId>,
) -> TermId {
    if map.is_empty() {
        return spec;
    }
    match kb.get_term(spec).clone() {
        Term::Ref(s) => map.get(&s).copied().unwrap_or(spec),
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            // Nullary Fn — treat as a name reference.
            map.get(&functor).copied().unwrap_or(spec)
        }
        Term::Fn { .. } => kb.map_fn_children(spec, |kb, child| {
            substitute_in_spec(kb, child, map)
        }),
        _ => spec,
    }
}

/// WI-230 internal: from an entry whose spec has already been
/// substituted to the current scope, build the substitution map to
/// pass into the entry's required_sort sub-tree. Maps each binding's
/// *qualified* param symbol (e.g. `anthill.prelude.Eq.T`) to its
/// substituted value, so the child's raw spec (which uses qualified
/// `Ref(Eq.T)`) translates one more level toward root scope.
fn build_child_subst_map(
    kb: &KnowledgeBase,
    entry: &RequiresEntry,
) -> HashMap<Symbol, TermId> {
    let mut map = HashMap::new();
    let Some((base_sort, bindings)) = unwrap_spec_view(kb, entry.spec) else {
        return map;
    };
    let base_qn = kb.qualified_name_of(base_sort).to_string();
    for (short_sym, value) in &bindings {
        let short_name = kb.resolve_sym(*short_sym);
        let param_qn = format!("{base_qn}.{short_name}");
        if let Some(param_qualified) = kb.try_resolve_symbol(&param_qn) {
            map.insert(param_qualified, *value);
        }
    }
    map
}

/// Check if sort A refines sort B via `requires` chain.
fn sort_refines(kb: &KnowledgeBase, a_sym: Symbol, b_sym: Symbol) -> bool {
    let chain = requires_chain_flat(kb, a_sym);
    chain.iter().any(|entry| same_symbol(kb, entry.required_sort, b_sym))
}

// ── Obligation checking ────────────────────────────────────────

/// A missing obligation: sort declares `requires` but doesn't provide an operation.
#[derive(Clone, Debug)]
pub struct MissingObligation {
    /// The sort that declared `requires`.
    pub sort_name: String,
    /// The required spec sort (e.g., "Eq").
    pub required_sort: String,
    /// The missing operation name.
    pub operation: String,
}

/// Check that all operations required by `requires` clauses are provided.
/// Returns a list of missing obligations.
pub fn check_obligations(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<MissingObligation> {
    let mut missing = Vec::new();
    let sort_name = kb.resolve_sym(sort_sym).to_string();
    let chain = requires_chain_flat(kb, sort_sym);

    // Collect operations provided by this sort
    let provided_ops = sort_operation_names(kb, sort_sym);

    for entry in &chain {
        // Get operations required by the spec sort
        let required_ops = sort_operation_names(kb, entry.required_sort);
        let required_sort_name = kb.resolve_sym(entry.required_sort).to_string();

        for op in &required_ops {
            if !provided_ops.iter().any(|p| p == op) {
                missing.push(MissingObligation {
                    sort_name: sort_name.clone(),
                    required_sort: required_sort_name.clone(),
                    operation: op.clone(),
                });
            }
        }
    }

    missing
}

/// Get operation names defined in a sort (from SortInfo.operations).
fn sort_operation_names(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<String> {
    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(s) => s,
        None => return Vec::new(),
    };

    for rid in kb.by_functor(sort_info_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        // Match sort by name field (may be Ref(sym) or Fn { functor: sym })
        let name_tid = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "name")
            .map(|(_, v)| *v)
        {
            Some(t) => t,
            None => continue,
        };
        let name_sym = match kb.get_term(name_tid) {
            Term::Fn { functor, .. } => *functor,
            Term::Ref(s) => *s,
            _ => continue,
        };
        if !same_symbol(kb, name_sym, sort_sym) {
            continue;
        }

        // Extract operations list
        let ops_tid = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "operations")
            .map(|(_, v)| *v)
        {
            Some(t) => t,
            None => return Vec::new(),
        };

        return list_to_vec(kb, ops_tid).iter().filter_map(|op_ref| {
            match kb.get_term(*op_ref) {
                Term::Ref(s) => Some(kb.resolve_sym(*s).to_string()),
                Term::Fn { functor, .. } => Some(kb.resolve_sym(*functor).to_string()),
                _ => None,
            }
        }).collect();
    }

    Vec::new()
}

/// Extract the sort symbol from a sort_ref(name: Ref(sym)) term.
/// Returns None if the term is not a sort_ref.
pub fn extract_sort_ref_sym(kb: &KnowledgeBase, ty: TermId) -> Option<Symbol> {
    if let Term::Fn { functor, named_args, .. } = kb.get_term(ty) {
        if kb.resolve_sym(*functor) == "sort_ref" {
            return extract_ref_field(kb, named_args, "name");
        }
    }
    None
}

/// WI-302: unwrap a `denoted(value: V)` wrapper to its inner value term.
/// Value-in-type bindings (`Modify[c]`) store the resource as
/// `denoted(value: Ref(c))`; readers that want the underlying value see
/// through the wrapper. Returns the input unchanged when not a `denoted`.
fn unwrap_denoted_value(kb: &KnowledgeBase, ty: TermId) -> TermId {
    if let Term::Fn { functor, named_args, .. } = kb.get_term(ty) {
        if kb.resolve_sym(*functor) == "denoted" {
            if let Some(v) = get_named_arg(kb, named_args, "value") {
                return v;
            }
        }
    }
    ty
}

/// The "sort head" of an inferred type — the least declared sort it
/// widens to, as a `Symbol` (WI-284). It reads the typer-reflect Type
/// shapes (the form the typer stores in `inferred_type`, which is what
/// `min_sort` feeds it) and unwraps them to the underlying sort symbol:
///   - `sort_ref(name: S)`              → `S`
///   - `parameterized(base: B, …)`      → sort head of `B` (params dropped)
///   - bare `Ref(S)`                    → `S`
///   - everything else                  → `None`
/// `None` is the unresolved-type-variable case (dispatch-undecidable for
/// the type-directed `[simp]` engine) — but it ALSO covers the
/// SLD-`canonicalize_type_value` shape `Fn(S, [], […])` and
/// qualified-/`Ident`-functor types. Those are not the reflect shapes
/// the typer records as an expression's type, so they're out of scope
/// here; a caller that passes them must extend this reader (e.g. with a
/// `SymbolKind::Sort` check on the functor).
pub fn sort_functor_of(kb: &KnowledgeBase, ty: TermId) -> Option<Symbol> {
    match type_functor_name(kb, ty) {
        Some("sort_ref") => extract_sort_ref_sym(kb, ty),
        Some("parameterized") => {
            let base = match kb.get_term(ty) {
                Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "base"),
                _ => None,
            }?;
            sort_functor_of(kb, base)
        }
        // WI-320: `effects_rows(EffectExpression)` is a structural Type
        // variant — like `denoted`, it has no underlying sort head to widen
        // to. Returning None means `min_sort` is undefined for occurrences
        // typed as an effect-row, which is the correct conservative answer
        // for Scope A (no `[simp]` rules target effect-row positions yet).
        // Once WI-307 wires `arrow.effects` to row form, returning the
        // `EffectsRuntime` kind anchor here may be revisited.
        Some("effects_rows") => None,
        _ => match kb.get_term(ty) {
            Term::Ref(s) => Some(*s),
            _ => None,
        },
    }
}

/// `min_sort` (WI-284): the least declared sort an occurrence inhabits
/// — the type-directed `[simp]` engine's dispatch key. Reads the
/// occurrence's typer-kept inferred type (set by the typer's `Stamp`
/// frame, [`NodeOccurrence::set_inferred_type`]) and widens it via
/// [`sort_functor_of`]. `None` when the occurrence is untyped /
/// ill-typed, or its type is still an unresolved variable. A
/// compile-time reader over an *expression* — never a runtime goal or
/// a callable `typeof`.
pub fn min_sort(kb: &KnowledgeBase, occ: &NodeOccurrence) -> Option<Symbol> {
    sort_functor_of(kb, occ.inferred_type()?)
}

/// WI-283 — the type-directed firing guard for `[simp]` rewriting.
///
/// A `[simp]` rule's guard is its explicit `:- …` *plus* the `requires` of
/// its enclosing sort (proposal 043 §4.1). When the rule is scoped to a
/// **parametric (spec) sort** — its redex functor is a *spec op*, e.g.
/// `Numeric.add` — that law holds only for carriers that *satisfy* the
/// sort. So the rule fires only where the **carrier** arguments' least
/// sorts ([`min_sort`]) provide the spec; otherwise firing would rewrite
/// where the requirement is unmet (unsound — it would erase an ill-typed
/// call, or apply a law that doesn't hold for that carrier).
///
/// The carrier arguments are the parameters declared with the spec sort's
/// own type-parameter — `add(a: T, b: T)` → both `a` and `b`;
/// `scale(v: T, k: Int)` → just `v`; `bar(k: Int, x: T)` → just `x`. Using
/// a positional shortcut (`pos_args[0]`) instead would test the wrong
/// argument whenever the carrier is not the leading parameter — wrongly
/// firing where a *non-carrier* arg's type happens to provide the spec.
///
/// Returns `true` (fire) when the redex functor is **not** a spec op — a
/// concrete top-level identity (`transpose(transpose(?m)) = ?m`); the
/// functor symbol already pins the sort, so structural match is sound —
/// **or** it is a spec op with ≥1 carrier argument and every carrier's
/// least sort provides the spec. Returns `false` (don't fire) when the
/// signature is unavailable, a carrier argument is missing, its type is
/// unresolved (a free type var — satisfaction undecidable), or it does not
/// provide the spec.
pub fn simp_fire_guard_holds(kb: &KnowledgeBase, redex: &NodeOccurrence) -> bool {
    let (functor, pos_args) = match redex.as_expr() {
        Some(Expr::Apply { functor, pos_args, .. }) => (*functor, pos_args),
        Some(Expr::Constructor { name, pos_args, .. }) => (*name, pos_args),
        _ => return true,
    };
    // Concrete (non-spec) functor: guard-free monomorphic identity.
    let Some(spec_sort) = lookup_spec_op_dispatch(kb, functor) else {
        return true;
    };
    // Without the signature we can't tell which arguments carry the spec,
    // so we can't verify the law applies — don't fire.
    let Some(rec) = super::op_info::lookup_operation_info(kb, functor) else {
        return false;
    };
    let type_params = kb.type_params_of_sort(spec_sort);
    let mut checked_carrier = false;
    for (i, (_param_name, param_type)) in rec.params.iter().enumerate() {
        // Is this parameter declared with the spec sort's type-parameter?
        let is_carrier = sort_functor_of(kb, *param_type)
            .is_some_and(|s| type_params.iter().any(|tp| tp.as_str() == kb.resolve_sym(s)));
        if !is_carrier {
            continue;
        }
        // Carrier read from its positional slot. A carrier supplied by name
        // (no positional slot) is conservatively not fired — the `[simp]`
        // matcher does not match a positional rule LHS against a named-arg
        // redex either, so such a redex never reaches a fire regardless.
        let Some(arg) = pos_args.get(i) else { return false };
        match min_sort(kb, arg) {
            Some(carrier) if sort_provides(kb, carrier, spec_sort) => checked_carrier = true,
            _ => return false,
        }
    }
    checked_carrier
}

/// parameterized(base: A, bindings: [...]) <: parameterized(base: B, bindings: [...])
/// if bases are compatible and all expected bindings have compatible actual values.
fn parameterized_compatible(kb: &KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    let (actual_args, expected_args) = match (kb.get_term(actual), kb.get_term(expected)) {
        (Term::Fn { named_args: a, .. }, Term::Fn { named_args: e, .. }) => {
            (a.clone(), e.clone())
        }
        _ => return false,
    };

    // Check base compatibility
    let actual_base = get_named_arg(kb, &actual_args, "base");
    let expected_base = get_named_arg(kb, &expected_args, "base");
    match (actual_base, expected_base) {
        (Some(a), Some(e)) => {
            if !types_compatible(kb, a, e) {
                return false;
            }
        }
        _ => return false,
    }

    // Check bindings: each expected binding must have a compatible actual binding
    let expected_bindings = get_named_arg(kb, &expected_args, "bindings")
        .map(|b| list_to_vec(kb, b))
        .unwrap_or_default();
    let actual_bindings = get_named_arg(kb, &actual_args, "bindings")
        .map(|b| list_to_vec(kb, b))
        .unwrap_or_default();

    for eb in &expected_bindings {
        let exp_param = binding_param_sym(kb, *eb);
        let exp_value = binding_value(kb, *eb);
        match (exp_param, exp_value) {
            (Some(param), Some(exp_val)) => {
                // Find matching actual binding
                let actual_val = actual_bindings.iter()
                    .find(|ab| binding_param_sym(kb, **ab) == Some(param))
                    .and_then(|ab| binding_value(kb, *ab));
                match actual_val {
                    Some(av) => {
                        if !types_compatible(kb, av, exp_val) {
                            return false;
                        }
                    }
                    None => return false,
                }
            }
            _ => return false,
        }
    }

    true
}

/// Extract param symbol from TypeBinding(param: Ref(sym), value: ...).
fn binding_param_sym(kb: &KnowledgeBase, binding: TermId) -> Option<Symbol> {
    if let Term::Fn { named_args, .. } = kb.get_term(binding) {
        extract_ref_field(kb, named_args, "param")
    } else {
        None
    }
}

/// Extract value from TypeBinding(param: ..., value: type_term).
fn binding_value(kb: &KnowledgeBase, binding: TermId) -> Option<TermId> {
    if let Term::Fn { named_args, .. } = kb.get_term(binding) {
        get_named_arg(kb, named_args, "value")
    } else {
        None
    }
}

/// arrow(param: A1, result: R1, effects: E1) <: arrow(param: A2, result: R2, effects: E2)
/// if A2 <: A1 (contravariant), R1 <: R2 (covariant), and E1 ⊆ E2 (covariant effects).
fn arrow_compatible(kb: &KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    let (actual_args, expected_args) = match (kb.get_term(actual), kb.get_term(expected)) {
        (Term::Fn { named_args: a, .. }, Term::Fn { named_args: e, .. }) => {
            (a.clone(), e.clone())
        }
        _ => return false,
    };

    // Contravariant param: expected param must be subtype of actual param
    let actual_param = get_named_arg(kb, &actual_args, "param");
    let expected_param = get_named_arg(kb, &expected_args, "param");
    match (actual_param, expected_param) {
        (Some(ap), Some(ep)) => {
            if !types_compatible(kb, ep, ap) {  // note: reversed for contravariance
                return false;
            }
        }
        _ => return false,
    }

    // Covariant result: actual result must be subtype of expected result
    let actual_result = get_named_arg(kb, &actual_args, "result");
    let expected_result = get_named_arg(kb, &expected_args, "result");
    match (actual_result, expected_result) {
        (Some(ar), Some(er)) => {
            if !types_compatible(kb, ar, er) {
                return false;
            }
        }
        _ => return false,
    }

    // Covariant effects: actual effects ⊆ expected effects.
    // A pure function (no effects) is usable where effects are declared.
    //
    // WI-307 v1a migration: arrow.effects is now `effects_rows(EffectExpression)`
    // (singular Type), so decode it via the flat-list shim. The naive
    // positional subset check below is unchanged — proper row subtyping
    // (open-tail absorption of extras) lands in the v1a row-unification
    // commit when this site rewires to walk the EffectExpression directly.
    let actual_effects = get_named_arg(kb, &actual_args, "effects")
        .map(|e| effects_rows_to_flat_list(kb, e))
        .unwrap_or_default();
    let expected_effects = get_named_arg(kb, &expected_args, "effects")
        .map(|e| effects_rows_to_flat_list(kb, e))
        .unwrap_or_default();

    for ae in &actual_effects {
        if !expected_effects.iter().any(|ee| types_compatible(kb, *ae, *ee)) {
            return false;
        }
    }

    true
}

/// named_tuple(fields: [...]) <: named_tuple(fields: [...])
/// Width subtyping: actual may have more fields than expected.
/// Depth subtyping: each expected field's type must be a supertype of actual's.
fn named_tuple_compatible(kb: &KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    let (actual_args, expected_args) = match (kb.get_term(actual), kb.get_term(expected)) {
        (Term::Fn { named_args: a, .. }, Term::Fn { named_args: e, .. }) => {
            (a.clone(), e.clone())
        }
        _ => return false,
    };

    let expected_fields = get_named_arg(kb, &expected_args, "fields")
        .map(|f| list_to_vec(kb, f))
        .unwrap_or_default();
    let actual_fields = get_named_arg(kb, &actual_args, "fields")
        .map(|f| list_to_vec(kb, f))
        .unwrap_or_default();

    // Every expected field must have a matching actual field with compatible type
    for ef in &expected_fields {
        let exp_name = field_name_sym(kb, *ef);
        let exp_type = field_type(kb, *ef);
        match (exp_name, exp_type) {
            (Some(name), Some(et)) => {
                let actual_type = actual_fields.iter()
                    .find(|af| field_name_sym(kb, **af) == Some(name))
                    .and_then(|af| field_type(kb, *af));
                match actual_type {
                    Some(at) => {
                        if !types_compatible(kb, at, et) {
                            return false;
                        }
                    }
                    None => return false,
                }
            }
            _ => return false,
        }
    }

    true
}

/// Extract name symbol from TypeField(name: Ref(sym), type: ...).
fn field_name_sym(kb: &KnowledgeBase, field: TermId) -> Option<Symbol> {
    if let Term::Fn { named_args, .. } = kb.get_term(field) {
        extract_ref_field(kb, named_args, "name")
    } else {
        None
    }
}

/// Extract type from TypeField(name: ..., type: type_term).
fn field_type(kb: &KnowledgeBase, field: TermId) -> Option<TermId> {
    if let Term::Fn { named_args, .. } = kb.get_term(field) {
        get_named_arg(kb, named_args, "type")
    } else {
        None
    }
}

// ── Unified type checking ──────────────────────────────────────

use super::load::LoadError;

/// Type-check the given sort terms and return errors as `LoadError` for
/// the load pipeline. Use [`type_check_sorts_typed`] when structured
/// `TypeError` values are needed (programmatic access, IDE diagnostics).
pub fn type_check_sorts(kb: &mut KnowledgeBase, sort_terms: &[TermId]) -> Vec<LoadError> {
    let typed = type_check_sorts_typed(kb, sort_terms);
    typed.iter().map(|e| e.to_load_error(kb)).collect()
}

/// Structured form of [`type_check_sorts`]: returns `Vec<TypeError>`,
/// preserving occurrence ids and term ids so consumers can format on
/// demand or filter by variant.
/// Feature flag — type-check + simp-rewrite operations declared at
/// *namespace* level (free functions, e.g. the `anthill.cli.parse` parser).
/// They have bodies in `op_bodies` but no `SortInfo`, so the sort loop in
/// [`type_check_sorts_typed`] never reaches them — meaning they are
/// currently **not type-checked at all** (a pre-existing gap, independent
/// of WI-283).
///
/// **OFF** until the typer can actually handle free-op bodies: a trial
/// sweep surfaced ~25 eval-fixture failures from constructs the
/// eval/interpreter supports but the typer (only ever run on sort ops)
/// does not — higher-order calls of `Function[A,B]`-typed values
/// (`f(f(x))`), effect-declaration checks, and some name resolution. Flip
/// to `true` and fix those under **WI-289**.
const TYPECHECK_FREE_OPS: bool = true;

pub fn type_check_sorts_typed(kb: &mut KnowledgeBase, sort_terms: &[TermId]) -> Vec<TypeError> {
    let mut errors: Vec<TypeError> = Vec::new();
    // Ops reached via a sort's `SortInfo` — so the gated free-op sweep
    // doesn't re-check them (collected only when the sweep is enabled).
    let mut sort_owned_ops: std::collections::HashSet<Symbol> = std::collections::HashSet::new();

    if let Some(sort_info_sym) = kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        for &sort_term in sort_terms {
            let sort_functor = match kb.get_term(sort_term) {
                Term::Fn { functor, .. } => *functor,
                _ => continue,
            };

            let sort_info = find_sort_info(kb, sort_info_sym, sort_functor);
            let (ctor_syms, op_syms) = match sort_info {
                Some((ctors, ops)) => (ctors, ops),
                None => continue,
            };

            check_entity_facts(kb, &ctor_syms, &mut errors);
            check_operation_bodies(kb, &op_syms, &mut errors);
            if TYPECHECK_FREE_OPS {
                sort_owned_ops.extend(op_syms.iter().copied());
            }
            check_pattern_fragment(kb, sort_term, &mut errors);
            check_rule_typing(kb, sort_term, &mut errors);
        }
    }

    // WI-289 (gated OFF — see [`TYPECHECK_FREE_OPS`]): type-check +
    // simp-rewrite every operation body not owned by a sort. Snapshot first
    // — typing mutates `op_bodies` via the simp write-back; `check_operation_
    // bodies` skips body-less / OperationInfo-less symbols and derives each
    // op's enclosing sort from its QN parent (a namespace ⇒ no requires).
    if TYPECHECK_FREE_OPS {
        let free_ops: Vec<Symbol> = kb
            .op_bodies_iter()
            .map(|(s, _)| s)
            .filter(|s| !sort_owned_ops.contains(s))
            .collect();
        if !free_ops.is_empty() {
            check_operation_bodies(kb, &free_ops, &mut errors);
        }
    }

    errors
}

/// Extract constructor and operation symbol lists from a SortInfo fact.
///
/// WI-237: matched on `same_symbol` (qualified-name identity) like the
/// other five resolve_sym audit sites. The bundle's `sort Main` short
/// name no longer collides with `anthill.cli.Main` here, so the typer
/// actually checks the anthill-todo bundle's cmd_X bodies. The chain of
/// follow-up issues this exposed is fixed under WI-237: types_compatible
/// name-binding normalization, pattern type-arg propagation (now
/// ctor-aware via `entity_field_types`, not SortAlias short-name lookup),
/// anthill-stl spec-fact embedding, bundle effect declarations, and
/// `op_has_runnable_body` guarding WI-218 from rewriting spec ops to
/// body-less impl symbols. Diagnostic: `wi237_diag_test.rs`.
fn find_sort_info(kb: &KnowledgeBase, sort_info_sym: Symbol, sort_functor: Symbol) -> Option<(Vec<Symbol>, Vec<Symbol>)> {
    for rid in kb.by_functor(sort_info_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        let name_tid = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "name")
            .map(|(_, v)| *v)
        {
            Some(t) => t,
            None => continue,
        };
        let name_sym = match kb.get_term(name_tid) {
            Term::Fn { functor, .. } => *functor,
            Term::Ref(s) => *s,
            _ => continue,
        };
        if !same_symbol(kb, name_sym, sort_functor) {
            continue;
        }

        let ctors = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "constructors")
            .map(|(_, v)| extract_sym_list(kb, *v))
            .unwrap_or_default();

        let ops = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "operations")
            .map(|(_, v)| extract_sym_list(kb, *v))
            .unwrap_or_default();

        return Some((ctors, ops));
    }
    None
}

/// Extract a list of Symbols from a cons-list of Ref terms.
fn extract_sym_list(kb: &KnowledgeBase, list_tid: TermId) -> Vec<Symbol> {
    list_to_vec(kb, list_tid).iter().filter_map(|tid| {
        match kb.get_term(*tid) {
            Term::Ref(s) => Some(*s),
            Term::Fn { functor, .. } => Some(*functor),
            _ => None,
        }
    }).collect()
}

/// Check a value against a declared type. Returns Some(TypeError) on mismatch.
///
/// Takes `&mut KnowledgeBase` because the parameterized-spec path runs
/// the canonical instance resolver (WI-274), which allocates
/// substituted subgoal terms during conditional resolution.
fn check_value_against_type(
    kb: &mut KnowledgeBase,
    value: TermId,
    declared_type: TermId,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    let type_functor = type_functor_name(kb, declared_type);

    match type_functor {
        Some("sort_ref") => {
            let declared_sym = extract_sort_ref_sym(kb, declared_type)?;
            check_value_against_sort_ref(kb, value, declared_sym, declared_type, entity_sym, field_sym, span)
        }
        Some("parameterized") => {
            check_value_against_parameterized(kb, value, declared_type, entity_sym, field_sym, span)
        }
        _ => None, // type_var, arrow, named_tuple, nothing — skip for now
    }
}

/// Check value against a simple sort_ref type.
fn check_value_against_sort_ref(
    kb: &KnowledgeBase,
    value: TermId,
    declared_sym: Symbol,
    declared_type: TermId,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    let is_prim = |sym: Symbol, expected: &str| -> bool {
        let name = kb.resolve_sym(sym);
        name == expected || name == &format!("anthill.prelude.{}", expected)
    };

    match kb.get_term(value) {
        Term::Const(lit) => {
            let ok = match lit {
                Literal::String(_) => is_prim(declared_sym, "String"),
                Literal::Int(_) => is_prim(declared_sym, "Int"),
                Literal::Float(_) => is_prim(declared_sym, "Float"),
                Literal::Bool(_) => is_prim(declared_sym, "Bool"),
                _ => true,
            };
            let actual = match lit {
                Literal::String(_) => "String",
                Literal::Int(_) => "Int",
                Literal::Float(_) => "Float",
                Literal::Bool(_) => "Bool",
                _ => "?",
            };
            // WI-036: a primitive value also satisfies a spec-sort field when
            // its primitive sort provides the spec (e.g. `5` for a field typed
            // `Eq`, since `Int provides Eq`).
            if ok || lit_sort_provides(kb, actual, declared_sym) {
                None
            } else {
                Some(TypeError::Other {
                    span,
                    context: TypeErrorContext::EntityField { entity: entity_sym, field: field_sym },
                    expected: type_display_name(kb, declared_type),
                    actual: actual.to_string(),
                })
            }
        }
        Term::Fn { functor: val_functor, .. } => {
            check_value_sort_membership(
                kb, kb.constructor_parent_sort(*val_functor),
                declared_sym, declared_type, entity_sym, field_sym, span,
            )
        }
        Term::Ref(val_sym) if kb.is_constructor_symbol(*val_sym) => {
            check_value_sort_membership(
                kb, kb.constructor_parent_sort(*val_sym),
                declared_sym, declared_type, entity_sym, field_sym, span,
            )
        }
        _ => None,
    }
}

/// True if the primitive sort of a literal (`"Int"`, `"String"`, …) provides
/// the spec sort `declared_sym` (WI-036 — a primitive value in a spec field).
fn lit_sort_provides(kb: &KnowledgeBase, prim: &str, declared_sym: Symbol) -> bool {
    kb.try_resolve_symbol(&format!("anthill.prelude.{prim}"))
        .is_some_and(|prim_sym| sort_provides(kb, prim_sym, declared_sym))
}

/// Shared check for a constructor value against a declared sort: accept direct
/// membership (the value's parent sort is the declared sort) or, per WI-036,
/// when the parent sort provides the declared spec sort.
fn check_value_sort_membership(
    kb: &KnowledgeBase,
    parent: Option<TermId>,
    declared_sym: Symbol,
    declared_type: TermId,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    let parent = parent?;
    if constructor_matches_declared(kb, parent, declared_sym) {
        return None;
    }
    if sort_sym_of_term(kb, parent).is_some_and(|p| sort_provides(kb, p, declared_sym)) {
        return None;
    }
    Some(TypeError::Other {
        span,
        context: TypeErrorContext::EntityField { entity: entity_sym, field: field_sym },
        expected: type_display_name(kb, declared_type),
        actual: extract_parent_name(kb, parent),
    })
}

/// Check value against a parameterized type like List[T=Int].
///
/// Takes `&mut KnowledgeBase` for the binding-precise spec check
/// (WI-274) — see [`spec_resolves_at_bindings`].
fn check_value_against_parameterized(
    kb: &mut KnowledgeBase,
    value: TermId,
    declared_type: TermId,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    let declared_args = match kb.get_term(declared_type) {
        Term::Fn { named_args, .. } => named_args.clone(),
        _ => return None,
    };

    // Extract base sort
    let base_tid = get_named_arg(kb, &declared_args, "base")?;
    let base_sym = extract_sort_ref_sym(kb, base_tid)?;

    // Get the value's constructor symbol
    let val_functor = match kb.get_term(value) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(s) if kb.is_constructor_symbol(*s) => *s,
        _ => return None,
    };

    // Check entity belongs to base sort. WI-036: when the base is a spec
    // sort (e.g. `Comparable[T = Int]`), a value whose own sort provides that
    // spec is accepted — and since its constructor is not a base constructor,
    // the per-field substitution walk below is skipped.
    //
    // WI-274: precise about the *bindings*. Rather than the base-only
    // `sort_provides` (does the value's sort provide the spec at all),
    // run the canonical instance resolver at the declared bindings —
    // the same resolver operation-requires uses. This rejects a
    // binding mismatch (`Comparable[T = Gadget]` holding a Widget,
    // where Widget provides Comparable only at `T = Widget`) and
    // checks conditional providers at the actual element type (List
    // provides Eq requires elementEq: `Eq[T = List[Int]]` resolves,
    // `Eq[T = List[NonEq]]` does not). The base-only `sort_provides`
    // is kept for the binding-free case, where it is already precise.
    if let Some(parent) = kb.constructor_parent_sort(val_functor) {
        if !constructor_matches_declared(kb, parent, base_sym) {
            let goal_bindings = declared_type_goal_bindings(kb, &declared_args);
            let accepted = if goal_bindings.is_empty() {
                sort_sym_of_term(kb, parent).is_some_and(|p| sort_provides(kb, p, base_sym))
            } else {
                spec_resolves_at_bindings(kb, base_sym, goal_bindings)
            };
            if accepted {
                return None;
            }
            return Some(TypeError::Other {
                span,
                context: TypeErrorContext::EntityField { entity: entity_sym, field: field_sym },
                expected: type_display_name(kb, declared_type),
                actual: extract_parent_name(kb, parent),
            });
        }
    }

    // Build substitution from type bindings (T → Int). Look up each
    // param's `Var` scoped to `base_sym` — the SortAlias index has
    // multiple entries for short names like "T" (List, Option, Stream,
    // …), and an unscoped short-name lookup may return the wrong sort's
    // `Var`, leaving `walk_type` on the entity's field types
    // unsubstituted.
    let bindings_tid = get_named_arg(kb, &declared_args, "bindings")?;
    let bindings = list_to_vec(kb, bindings_tid);
    let mut subst = Substitution::new();
    for b in &bindings {
        let param_sym = binding_param_sym(kb, *b);
        let value_type = binding_value(kb, *b);
        if let (Some(psym), Some(vt)) = (param_sym, value_type) {
            if let Some(vid) = type_param_vid_in_sort(kb, base_sym, psym) {
                subst.bind(vid, vt);
            }
        }
    }

    // Check each field of the value entity against the instantiated field type
    let val_named_args = match kb.get_term(value) {
        Term::Fn { named_args, .. } => named_args.clone(),
        _ => return None,
    };

    let ctor_field_types = match kb.entity_field_types(val_functor) {
        Some(ft) => ft.to_vec(),
        None => return None,
    };

    for &(fsym, declared_field_type) in &ctor_field_types {
        let fval = match val_named_args.iter().find(|(s, _)| *s == fsym) {
            Some((_, v)) => *v,
            None => continue,
        };
        if matches!(kb.get_term(fval), Term::Var(_)) { continue; }

        // Walk the field type through the substitution to resolve type params
        let instantiated_type = walk_type(kb, &subst, declared_field_type);

        if let Some(err) = check_value_against_type(kb, fval, instantiated_type, entity_sym, fsym, span) {
            return Some(err);
        }
    }

    None
}

/// WI-274: collect a parameterized type's bindings as `SortGoal`
/// bindings — `(spec short-param symbol, value type term)` pairs. The
/// value terms are [canonicalized](canonicalize_goal_value) into the
/// bare-sort-ref shape the instance resolver matches against.
fn declared_type_goal_bindings(
    kb: &mut KnowledgeBase,
    declared_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> SmallVec<[(Symbol, TermId); 2]> {
    let raw: Vec<(Symbol, TermId)> = match get_named_arg(kb, declared_args, "bindings") {
        Some(bindings_tid) => list_to_vec(kb, bindings_tid)
            .into_iter()
            .filter_map(|b| match (binding_param_sym(kb, b), binding_value(kb, b)) {
                (Some(p), Some(v)) => Some((p, v)),
                _ => None,
            })
            .collect(),
        None => Vec::new(),
    };
    raw.into_iter()
        .map(|(p, v)| (p, canonicalize_goal_value(kb, v)))
        .collect()
}

/// WI-274: rewrite a field-type type term into the canonical shape the
/// instance resolver matches against. Field types encode sort
/// references as `sort_ref(name: Ref(S))`, whereas the resolver's
/// candidate side (from `SortProvidesInfo` / `requires` clauses) uses
/// bare sort refs. Unwrap every `sort_ref` to its bare `Ref(S)` —
/// recursing through `parameterized(base, bindings)` so nested element
/// types (`List[T = Int]`) expose their real base and value sorts to
/// `parametric_value_parts`.
fn canonicalize_goal_value(kb: &mut KnowledgeBase, value: TermId) -> TermId {
    if let Some(s) = extract_sort_ref_sym(kb, value) {
        return kb.alloc(Term::Ref(s));
    }
    kb.map_fn_children(value, |kb, child| canonicalize_goal_value(kb, child))
}

/// WI-274: binding-precise spec satisfaction. A field declared with a
/// parameterized spec is accepted iff the spec resolves at the
/// *declared bindings* through the canonical instance resolver
/// ([`resolve`], typing.rs) — the same resolver operation-requires
/// uses, accepting iff `Resolved`. Empty scope: field validation has
/// no enclosing `requires` to draw on. Conditional providers descend
/// recursively (List provides Eq requires elementEq), so the goal
/// resolves only when the element type also provides the spec.
fn spec_resolves_at_bindings(
    kb: &mut KnowledgeBase,
    spec_sort: Symbol,
    bindings: SmallVec<[(Symbol, TermId); 2]>,
) -> bool {
    let goal = SortGoal { spec_sort, bindings };
    let scope = ResolutionScope { available_requires: &[] };
    matches!(resolve(kb, &goal, &scope), ResolutionResult::Resolved(_))
}

/// Check all facts for the given entity constructors against their declared field types.
fn check_entity_facts(kb: &mut KnowledgeBase, ctor_syms: &[Symbol], errors: &mut Vec<TypeError>) {
    for &ctor_sym in ctor_syms {
        let field_types = match kb.entity_field_types(ctor_sym) {
            Some(ft) => ft.to_vec(),
            None => continue,
        };
        if field_types.is_empty() { continue; }

        for rid in kb.by_functor(ctor_sym) {
            if !kb.is_fact(rid) { continue; }

            // Skip entity definitions and metadata
            let fact_sort = kb.rule_sort(rid);
            let fact_sort_name = match kb.get_term(fact_sort) {
                Term::Fn { functor: f, .. } => kb.resolve_sym(*f),
                Term::Ref(s) => kb.resolve_sym(*s),
                _ => "",
            };
            if ["Entity", "EntityInfo", "SortInfo", "OperationInfo", "FieldInfo", "SortRequiresInfo"]
                .contains(&fact_sort_name)
            {
                continue;
            }

            let head = kb.rule_head(rid);
            let named_args = match kb.get_term(head) {
                Term::Fn { named_args, .. } => named_args.clone(),
                _ => continue,
            };

            let span: Option<Span> = kb.term_span(head)
                .or_else(|| kb.functor_span(ctor_sym))
                .map(|s| s.span);

            for &(field_sym, declared_type) in &field_types {
                let field_value = match named_args.iter().find(|(s, _)| *s == field_sym) {
                    Some((_, v)) => *v,
                    None => continue,
                };

                if matches!(kb.get_term(field_value), Term::Var(Var::Global(_) | Var::DeBruijn(_))) {
                    continue;
                }

                if let Some(err) = check_value_against_type(kb, field_value, declared_type, ctor_sym, field_sym, span) {
                    errors.push(err);
                }
            }
        }
    }
}

/// True if sort `carrier` provides spec `spec` — i.e. a `SortProvidesInfo`
/// fact records `carrier` as its `sort_ref` and `spec` as the spec base.
/// `maybe_emit_fact_provides_info` normalizes both explicit `provides`
/// clauses and bare `fact Spec[T=X]` facts into `SortProvidesInfo`, so this
/// one query covers both. Used so a fact field declared with a spec sort
/// accepts a value whose own sort satisfies that spec (WI-036).
fn sort_provides(kb: &KnowledgeBase, carrier: Symbol, spec: Symbol) -> bool {
    let provides_sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return false,
    };
    for rid in kb.by_functor(provides_sym) {
        let named = match kb.get_term(kb.rule_head(rid)) {
            Term::Fn { named_args, .. } => named_args.clone(),
            _ => continue,
        };
        let carrier_ok = get_named_arg(kb, &named, "sort_ref")
            .and_then(|t| super::load::sort_ref_functor(kb, t))
            .is_some_and(|c| same_symbol(kb, c, carrier));
        let spec_ok = get_named_arg(kb, &named, "spec")
            .and_then(|t| super::load::provides_spec_base_sym(kb, t))
            .is_some_and(|s| same_symbol(kb, s, spec));
        if carrier_ok && spec_ok {
            return true;
        }
    }
    false
}

/// Check if a constructor's parent sort matches the declared type symbol.
fn constructor_matches_declared(kb: &KnowledgeBase, parent: TermId, declared_type_sym: Symbol) -> bool {
    let parent_sym = match kb.get_term(parent) {
        Term::Fn { functor: f, .. } => Some(*f),
        Term::Ref(s) => Some(*s),
        _ => None,
    };
    let declared_name = kb.resolve_sym(declared_type_sym);
    parent_sym.map_or(false, |ps| {
        let pn = kb.resolve_sym(ps);
        pn == declared_name
            || pn.strip_suffix(declared_name).map_or(false, |p| p.ends_with('.'))
            || declared_name.strip_suffix(pn).map_or(false, |p| p.ends_with('.'))
    })
}

fn extract_parent_name(kb: &KnowledgeBase, parent: TermId) -> String {
    match kb.get_term(parent) {
        Term::Fn { functor: f, .. } => kb.resolve_sym(*f).to_string(),
        Term::Ref(s) => kb.resolve_sym(*s).to_string(),
        _ => "?".to_string(),
    }
}

/// Check operation bodies against their declared return types.
fn check_operation_bodies(kb: &mut KnowledgeBase, op_syms: &[Symbol], errors: &mut Vec<TypeError>) {
    struct OpInfo {
        op_sym: Symbol,
        return_type: TermId,
        declared_effects: Vec<TermId>,
        body_node: Rc<NodeOccurrence>,
        params: Vec<(Symbol, TermId)>,
        span: Option<Span>,
    }

    let mut ops_to_check = Vec::new();

    for &op_sym in op_syms {
        let rec = match super::op_info::lookup_operation_info(kb, op_sym) {
            Some(r) => r,
            None => continue,
        };
        // Body-less ops (specs) have no body to type-check.
        let body_node = match rec.body_node {
            Some(n) => n,
            None => continue,
        };
        let span = kb.functor_span(rec.op_sym).map(|s| s.span);
        ops_to_check.push(OpInfo {
            op_sym: rec.op_sym,
            return_type: rec.return_type,
            declared_effects: rec.effects,
            body_node,
            params: rec.params,
            span,
        });
    }

    // WI-314: region set for result-escape masking — program-global, so
    // compute it once before the per-op loop.
    let region_sorts = super::region::region_sorts(kb);

    for op in &ops_to_check {
        let mut env = TypingEnv::empty();
        // WI-221: snapshot the enclosing sort + its requires chain so
        // defer-to-requirement detection in `check_apply` runs from a
        // cached chain instead of re-walking SortRequiresInfo per call.
        let op_qn = kb.qualified_name_of(op.op_sym).to_string();
        let parent_sym = op_qn
            .rsplit_once('.')
            .and_then(|(parent_qn, _)| kb.try_resolve_symbol(parent_qn));
        env.set_enclosing_sort(kb, parent_sym);
        for (name, ty) in &op.params {
            env.bind_var(*name, *ty);
        }

        // WI-270: thread the declared return type as the body's
        // top-down `expected`. The body's `let v: T = …`-style
        // annotations and inner Apply/Constructor calls then see a
        // caller-side hint that pins otherwise-free type-params.
        match type_check_node(kb, &env, &op.body_node, Some(op.return_type)) {
            Ok(result) => {
                // WI-283: the typer is tree-producing — `result.node` is
                // the (possibly `[simp]`-rewritten) body. Write the
                // redex-free tree back so the return-type check below and
                // every downstream consumer (req_insertion, eval, codegen)
                // see the rewritten form. Only when a rule actually fired
                // (`ptr_eq` unchanged ⇒ no allocation, no write).
                if !Rc::ptr_eq(&result.node, &op.body_node) {
                    kb.set_op_body_node(op.op_sym, Rc::clone(&result.node));
                }
                if !types_compatible(kb, result.ty, op.return_type) {
                    errors.push(TypeError::TypeMismatch {
                        span: None,
                        context: TypeErrorContext::OperationReturn { op_name: op.op_sym },
                        expected: op.return_type,
                        actual: result.ty,
                    });
                }

                // WI-314: operation-boundary effect masking. Drops effects
                // on non-escaping locals (as before) and masks / re-keys
                // `Modify[result]` from freshly-allocated regions per the
                // return type — see kb::region.
                let op_result_sym = kb.try_resolve_symbol(&format!("{}.result", op_qn));
                let ext_effects = super::region::op_boundary_effects(
                    kb,
                    &result.env,
                    op.return_type,
                    op_result_sym,
                    &region_sorts,
                    &result.effects,
                );
                for effect in &ext_effects {
                    if !op.declared_effects.contains(effect) {
                        let effect_name = type_display_name(kb, *effect);
                        let declared_names: Vec<String> = op.declared_effects.iter()
                            .map(|e| type_display_name(kb, *e))
                            .collect();
                        if !declared_names.iter().any(|d| d == &effect_name) {
                            errors.push(TypeError::Other {
                                span: op.span,
                                context: TypeErrorContext::OperationEffects { op_name: op.op_sym },
                                expected: format!("declared: [{}]", declared_names.join(", ")),
                                actual: format!("undeclared effect: {}", effect_name),
                            });
                        }
                    }
                }

                // Collect exhaustiveness diagnostics from the typing env
                for diag in &result.env.diagnostics {
                    errors.push(TypeError::Other {
                        span: op.span,
                        context: TypeErrorContext::OperationMatch { op_name: op.op_sym },
                        expected: "exhaustive".to_string(),
                        actual: diag.clone(),
                        });
                }
            }
            Err(err) => {
                // Body failed to type — surface the structured error
                // instead of silently dropping it. Flatten an aggregation
                // node into its leaves so each sibling failure shows up
                // as its own load error.
                for e in err.flatten() {
                    errors.push(e);
                }
            }
        }
    }
}


/// Collect which entity constructors a pattern covers (recursively).
fn collect_covered_entities(
    kb: &KnowledgeBase,
    pattern: TermId,
    scrutinee_ctors: &[Symbol],
    covered: &mut Vec<Symbol>,
    has_wildcard: &mut bool,
) {
    if let Term::Fn { functor, named_args, pos_args, .. } = kb.get_term(pattern) {
        let fname = kb.resolve_sym(*functor).to_string();
        match fname.as_str() {
            "wildcard" => { *has_wildcard = true; }
            "var_pattern" => {
                // A var_pattern might actually be a nullary constructor (e.g.
                // `case red`). The pattern name is stored bare (it could be a
                // binding), so recognize it by matching against the scrutinee
                // sort's constructors — `red` against `Color.red` modulo
                // short/qualified — rather than a global name lookup. A name
                // that matches no constructor is a binding (catch-all).
                if let Some(sym) = extract_sym_arg(kb, named_args, pos_args, "name") {
                    if let Some(&ctor) = scrutinee_ctors.iter().find(|&&c| same_symbol(kb, c, sym)) {
                        covered.push(ctor);
                    } else if kb.is_constructor_symbol(sym) || kb.constructor_parent_sort(sym).is_some() {
                        covered.push(sym);
                    } else {
                        *has_wildcard = true;
                    }
                } else {
                    *has_wildcard = true;
                }
            }
            "constructor_pattern" => {
                // constructor_pattern(name: sym, args: ...)
                if let Some(sym) = extract_sym_arg(kb, named_args, pos_args, "name") {
                    covered.push(sym);
                }
            }
            "literal_pattern" => {
                // literal patterns don't cover enum entities — skip
            }
            _ => {
                // Unknown pattern form — be conservative, treat as wildcard
                *has_wildcard = true;
            }
        }
    }
}

// ── HO pattern fragment checking ───────────────────────────────

/// Validate that rules conform to the hereditary Harrop pattern fragment.
/// This ensures higher-order unification remains decidable.
fn check_pattern_fragment(kb: &KnowledgeBase, sort_term: TermId, errors: &mut Vec<TypeError>) {
    let ho_apply_sym = match kb.try_resolve_symbol("anthill.reflect.Expr.ho_apply") {
        Some(s) => s,
        None => return,
    };

    for rid in kb.by_domain(sort_term) {
        if kb.is_fact(rid) { continue; } // skip facts — only check rules

        // Head stays a hash-consed term (it is searched in the discrim tree),
        // so the head checks remain term-based.
        let head = kb.rule_head(rid);

        let head_sym = match kb.get_term(head) {
            Term::Fn { functor, .. } => *functor,
            _ => continue,
        };
        let span = kb.term_span(head).map(|s| s.span);

        // Rule 1: head must not contain ho_apply (no predicate variables in head)
        if term_contains_functor(kb, head, ho_apply_sym) {
            errors.push(TypeError::Other {
                span,
                context: TypeErrorContext::Rule { name: head_sym, field: RuleField::Head },
                expected: "no predicate variables in rule head".to_string(),
                actual: "ho_apply in head position".to_string(),
            });
        }

        // Check body goals for pattern fragment violations — WI-246: walk the
        // OCCURRENCE body (`rule_body_nodes`), not the term body. `ho_apply` is
        // not a recognized reflect materialize key, so it stays faithful
        // (`Expr::Apply { functor: ho_apply, … }`) in the occurrence form.
        for goal in kb.rule_body_nodes(rid) {
            check_ho_apply_pattern_occ(kb, goal, ho_apply_sym, head_sym, span, errors);
        }
    }
}

/// Check an occurrence (rule-body goal) for ho_apply pattern fragment
/// violations — WI-246: the occurrence-walking twin of the former
/// `check_ho_apply_pattern` term-walker. `ho_apply` materializes faithfully to
/// `Expr::Apply { functor: ho_apply, … }` (not a recognized reflect key), so
/// the structural checks carry over: the functor-bearing forms
/// (`Apply`/`Constructor`/`Instantiation`) mirror the term-walker's `Term::Fn`,
/// and `Expr::Var(DeBruijn)` mirrors `Term::Var(DeBruijn)` in the stored body.
fn check_ho_apply_pattern_occ(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    ho_apply_sym: Symbol,
    rule_sym: Symbol,
    span: Option<Span>,
    errors: &mut Vec<TypeError>,
) {
    let Some(expr) = occ.as_expr() else { return };

    // The ho_apply-specific fragment rules apply to the functor-bearing forms
    // (Apply/Constructor/Instantiation) — the occurrence analogue of `Term::Fn`.
    // `ho_apply` materializes to `Expr::Apply`, but match all three for parity
    // with the term-walker's functor check.
    let ho_pos_args = match expr {
        Expr::Apply { functor, pos_args, .. } if *functor == ho_apply_sym => Some(pos_args),
        Expr::Constructor { name, pos_args, .. } if *name == ho_apply_sym => Some(pos_args),
        Expr::Instantiation { name, pos_args, .. } if *name == ho_apply_sym => Some(pos_args),
        _ => None,
    };

    if let Some(pos_args) = ho_pos_args {
        if !pos_args.is_empty() {
        // This is an ho_apply — check pattern fragment rules.

        // Rule 2: first arg (predicate) must be a variable. If it's instead a
        // nested ho_apply (predicate applied to predicate), flag it.
        let pred = &pos_args[0];
        if !matches!(pred.as_expr(), Some(Expr::Var(_))) {
            if let Some(Expr::Apply { functor: inner_f, .. }) = pred.as_expr() {
                if *inner_f == ho_apply_sym {
                    errors.push(TypeError::Other {
                        span,
                        context: TypeErrorContext::Rule { name: rule_sym, field: RuleField::Body },
                        expected: "variable as predicate in ho_apply".to_string(),
                        actual: "nested ho_apply (predicate applied to predicate)".to_string(),
                    });
                }
            }
        }

        // Rule 3: remaining args must be distinct (no duplicate variables).
        let mut seen_vars: Vec<u32> = Vec::new();
        for arg in &pos_args[1..] {
            if let Some(Expr::Var(Var::DeBruijn(idx))) = arg.as_expr() {
                if seen_vars.contains(idx) {
                    errors.push(TypeError::Other {
                        span,
                        context: TypeErrorContext::Rule { name: rule_sym, field: RuleField::Body },
                        expected: "distinct variables in ho_apply args".to_string(),
                        actual: format!("duplicate variable ?{} in predicate application", idx),
                    });
                }
                seen_vars.push(*idx);
            }

            // Rule 3b: args must not contain ho_apply (no predicate variable as argument).
            if occurrence_contains_functor(arg, ho_apply_sym) {
                errors.push(TypeError::Other {
                    span,
                    context: TypeErrorContext::Rule { name: rule_sym, field: RuleField::Body },
                    expected: "first-order args in ho_apply".to_string(),
                    actual: "predicate variable as argument to predicate".to_string(),
                });
            }
        }
        }
    }

    // Recurse into ALL sub-occurrences. The term-walker recursed every
    // `Term::Fn` child, and reflect-encoded if/match/let/lambda/list/… are
    // `Term::Fn` in term-land, so an `ho_apply` nested in a control-flow or
    // container form must still be checked.
    for_each_child(expr, |c| {
        check_ho_apply_pattern_occ(kb, c, ho_apply_sym, rule_sym, span, errors);
    });
}

/// Check if an occurrence (or any sub-occurrence) contains the given functor.
/// Occurrence-walking twin of [`term_contains_functor`] for the rule-body
/// pattern-fragment check; `Apply`/`Constructor`/`Instantiation` carry the
/// functor (mirroring `Term::Fn`).
fn occurrence_contains_functor(occ: &Rc<NodeOccurrence>, target: Symbol) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(o) = stack.pop() {
        if let Some(expr) = o.as_expr() {
            let functor = match expr {
                Expr::Apply { functor, .. } => Some(*functor),
                Expr::Constructor { name, .. } | Expr::Instantiation { name, .. } => Some(*name),
                _ => None,
            };
            if functor == Some(target) {
                return true;
            }
            for_each_child(expr, |c| stack.push(Rc::clone(c)));
        }
    }
    false
}

/// Check if a term (or any subterm) contains the given functor. Still used for
/// the rule HEAD (a hash-consed term); the body uses [`occurrence_contains_functor`].
fn term_contains_functor(kb: &KnowledgeBase, term: TermId, target_functor: Symbol) -> bool {
    match kb.get_term(term) {
        Term::Fn { functor, pos_args, named_args, .. } => {
            if *functor == target_functor { return true; }
            pos_args.iter().any(|a| term_contains_functor(kb, *a, target_functor))
                || named_args.iter().any(|(_, a)| term_contains_functor(kb, *a, target_functor))
        }
        _ => false,
    }
}

// ── Rule type checking ─────────────────────────────────────────

/// Check that rule variables have consistent types across head and body.
/// For each rule in the given sort's domain:
/// 1. Collect type constraints from head (operation params, entity fields)
/// 2. Collect type constraints from body goals
/// 3. Unify all constraints for each variable — must be consistent
fn check_rule_typing(kb: &mut KnowledgeBase, sort_term: TermId, errors: &mut Vec<TypeError>) {
    for rid in kb.by_domain(sort_term) {
        if kb.is_fact(rid) { continue; } // facts have no body — nothing to check

        let head = kb.rule_head(rid);
        let mut subst = Substitution::new();
        let mut var_types: HashMap<u32, TermId> = std::collections::HashMap::new();

        // Collect type constraints from the head (still a hash-consed term).
        collect_term_type_constraints(kb, head, &mut var_types, &mut subst);

        // Collect type constraints from the body goals (WI-246: the occurrence
        // body, not the term body). The head term and the body occurrences are
        // closed against the same `vars`, so their De Bruijn idx keys align.
        // WI-307: `collect_occurrence_type_constraints` now takes `&mut kb`
        // (so `unify_types` can allocate fresh row tails); the body-node
        // slice is cloned out first so the immutable borrow doesn't conflict
        // with the inner mutable kb pass.
        let body_nodes: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
        for node in &body_nodes {
            collect_occurrence_type_constraints(kb, node, &mut var_types, &mut subst);
        }

        // Check for contradictions in the substitution
        if subst.is_contradiction() {
            let head_sym = match kb.get_term(head) {
                Term::Fn { functor, .. } => *functor,
                _ => continue,
            };
            let span = kb.term_span(head).map(|s| s.span);
            errors.push(TypeError::Other {
                span,
                context: TypeErrorContext::Rule { name: head_sym, field: RuleField::Whole },
                expected: "consistent variable types".to_string(),
                actual: "contradictory variable types".to_string(),
            });
        }
    }
}

/// Collect type constraints from a term: for each variable in an operation/entity
/// argument position, record the expected type.
fn collect_term_type_constraints(
    kb: &mut KnowledgeBase,
    term: TermId,
    var_types: &mut HashMap<u32, TermId>,
    subst: &mut Substitution,
) {
    match kb.get_term(term) {
        Term::Fn { functor, pos_args, named_args, .. } => {
            let functor = *functor;
            let pos_args = pos_args.clone();
            let named_args = named_args.clone();

            // Try to get expected types from operation params or entity fields
            if let Some(op) = lookup_operation_info_full(kb, functor) {
                // Operation call: match args to param types
                for (i, &arg) in pos_args.iter().enumerate() {
                    if let Some(&(_, param_type)) = op.params.get(i) {
                        constrain_var_type(kb, arg, param_type, var_types, subst);
                    }
                }
            } else if let Some(field_types) = kb.entity_field_types(functor) {
                // Entity constructor: match named args to field types
                let field_types = field_types.to_vec();
                for &(field_sym, field_type) in &field_types {
                    if let Some((_, arg_tid)) = named_args.iter().find(|(s, _)| *s == field_sym) {
                        constrain_var_type(kb, *arg_tid, field_type, var_types, subst);
                    }
                }
            }

            // Recurse into subterms
            for &arg in pos_args.iter() {
                collect_term_type_constraints(kb, arg, var_types, subst);
            }
            for &(_, arg) in named_args.iter() {
                collect_term_type_constraints(kb, arg, var_types, subst);
            }
        }
        _ => {}
    }
}

/// If `term` is a variable, record that it should have `expected_type`.
/// If the variable already has a type, unify the two.
fn constrain_var_type(
    kb: &mut KnowledgeBase,
    term: TermId,
    expected_type: TermId,
    var_types: &mut HashMap<u32, TermId>,
    subst: &mut Substitution,
) {
    let vid = match kb.get_term(term) {
        Term::Var(Var::Global(vid)) => vid.raw(),
        Term::Var(Var::DeBruijn(idx)) => *idx,
        _ => return,
    };
    constrain_vid(kb, vid, expected_type, var_types, subst);
}

/// Shared core of `constrain_var_type` / `constrain_occ_var_type`: record the
/// var's expected type, or unify against an existing one (keyed by the var's
/// raw id / De Bruijn idx — the same key space for a rule's head term and its
/// body occurrences, both closed against the same `vars`).
fn constrain_vid(
    kb: &mut KnowledgeBase,
    vid: u32,
    expected_type: TermId,
    var_types: &mut HashMap<u32, TermId>,
    subst: &mut Substitution,
) {
    if let Some(&existing_type) = var_types.get(&vid) {
        if !unify_types(kb, subst, existing_type, expected_type) {
            subst.contradiction = true;
        }
    } else {
        var_types.insert(vid, expected_type);
    }
}

/// WI-246: occurrence-body twin of [`collect_term_type_constraints`] — walk a
/// rule-body goal OCCURRENCE, constraining op-arg (positional) / entity-field
/// (named) var positions to their declared types. Mirrors the term walker's
/// op/entity functor dispatch and recursion, reading `Expr` instead of
/// `Term::Fn` so the typer no longer reads the term body. Control-flow / reflect
/// forms add no constraints themselves but are recursed into via their children.
///
/// Reflect-data forms carry their sub-pattern / param / type-annotation as
/// `TermId` fields (not occ children), which `for_each_child` does not
/// enumerate. They are closed to the rule's De Bruijn space by
/// `node_to_debruijn`, so we type-check them via the term collector — covering
/// op/entity calls nested in a pattern/param exactly as the term walker did.
fn collect_occurrence_type_constraints(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    var_types: &mut HashMap<u32, TermId>,
    subst: &mut Substitution,
) {
    // WI-298: descend into Pattern children so a var living in a pattern's
    // nested type-annotation Expr leaf gets the same op-arg / entity-field
    // constraint walk applied to the rest of the rule. Symmetric with
    // `node_to_debruijn` and `collect_occurrence_global_vars_ordered`.
    if let Some(pat) = occ.as_pattern() {
        for_each_pattern_child(pat, |c| {
            collect_occurrence_type_constraints(kb, c, var_types, subst)
        });
        return;
    }
    let Some(expr) = occ.as_expr() else { return };
    match expr {
        Expr::Apply { functor, pos_args, named_args, .. } => {
            constrain_application(kb, *functor, pos_args, named_args, var_types, subst);
        }
        Expr::Constructor { name, pos_args, named_args }
        | Expr::Instantiation { name, pos_args, named_args } => {
            constrain_application(kb, *name, pos_args, named_args, var_types, subst);
        }
        // WI-318: pattern is now a Pattern-kind child reached by
        // `for_each_child` below. Only `type_annotation` remains a
        // TermId-typed field needing the term-collector.
        Expr::Let { type_annotation, .. } => {
            if let Some(t) = type_annotation {
                collect_term_type_constraints(kb, *t, var_types, subst);
            }
        }
        // WI-318: Lambda / LambdaWithin params AND MatchBranch.pattern
        // are now Pattern-kind occurrences walked by `for_each_child`
        // below. Any nested TermId-typed children (e.g. a Var pattern's
        // type_ann Expr-kind occurrence) are reached via that recursion;
        // no explicit term-level call needed here.
        _ => {}
    }
    for_each_child(expr, |c| collect_occurrence_type_constraints(kb, c, var_types, subst));
}

/// Constrain the op-arg (positional) / entity-field (named) var positions of one
/// applied occurrence — the occurrence analog of the op/entity dispatch in
/// [`collect_term_type_constraints`].
fn constrain_application(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    var_types: &mut HashMap<u32, TermId>,
    subst: &mut Substitution,
) {
    if let Some(op) = lookup_operation_info_full(kb, functor) {
        for (i, arg) in pos_args.iter().enumerate() {
            if let Some(&(_, param_type)) = op.params.get(i) {
                constrain_occ_var_type(kb, arg, param_type, var_types, subst);
            }
        }
    } else if let Some(field_types) = kb.entity_field_types(functor) {
        let field_types = field_types.to_vec();
        for &(field_sym, field_type) in &field_types {
            if let Some((_, arg)) = named_args.iter().find(|(s, _)| *s == field_sym) {
                constrain_occ_var_type(kb, arg, field_type, var_types, subst);
            }
        }
    }
}

/// Occurrence analog of [`constrain_var_type`]: if `occ` is a var leaf, record /
/// unify its expected type.
fn constrain_occ_var_type(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    expected_type: TermId,
    var_types: &mut HashMap<u32, TermId>,
    subst: &mut Substitution,
) {
    let vid = match occ.as_expr() {
        Some(Expr::Var(Var::Global(vid))) => vid.raw(),
        Some(Expr::Var(Var::DeBruijn(idx))) => *idx,
        _ => return,
    };
    constrain_vid(kb, vid, expected_type, var_types, subst);
}

