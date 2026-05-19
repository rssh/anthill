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
    materialize_from_handle,
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
}

impl TypeResult {
    /// Pure result — no effects.
    pub fn pure(ty: TermId, env: TypingEnv) -> Self {
        Self { ty, env, effects: Vec::new() }
    }
}

/// Filter effects: keep only external effects (on non-local resources).
/// Effects on let-bound resources are local and don't propagate.
fn external_effects(kb: &KnowledgeBase, env: &TypingEnv, effects: &[TermId]) -> Vec<TermId> {
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
fn extract_effect_resource_sym(kb: &KnowledgeBase, effect: TermId) -> Option<Symbol> {
    let functor_name = type_functor_name(kb, effect)?;
    match functor_name {
        "parameterized" => {
            if let Term::Fn { named_args, .. } = kb.get_term(effect) {
                let bindings_tid = get_named_arg(kb, named_args, "bindings")?;
                let bindings = list_to_vec(kb, bindings_tid);
                for b in &bindings {
                    if let Some(value_tid) = binding_value(kb, *b) {
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
fn substitute_ref_syms(
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
    },
    Build(TypeBuildFrame),
}

/// Push a Visit with no top-down hint. Used at positions where the
/// caller's expected doesn't bound the child's type — Apply / Ctor
/// args (constrained by op.params / entity_field_types), the
/// scrutinee of a Match (drives the branch envs but takes no hint
/// from outside), and the condition of an If (always `Bool`).
fn push_visit_no_hint(work: &mut Vec<TypeWorkOp>, occ: Rc<NodeOccurrence>, env: Rc<TypingEnv>) {
    work.push(TypeWorkOp::Visit { occ, env, expected: None });
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
    },
    /// All Constructor args finished; drain results and call
    /// `check_constructor_iter`. WI-270: `expected` flows into the
    /// parent-type unification so a caller-side `Option[Int]`
    /// constrains `some(?)`'s inferred T.
    Constructor {
        ctor_sym: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        env: Rc<TypingEnv>,
        span: Option<Span>,
        expected: Option<TermId>,
    },
    /// Value finished; compute the body's ext_env and schedule the
    /// body Visit, plus a `LetFinal` frame to combine results. If the
    /// value's TypeResult is `None`, the let propagates failure up
    /// without visiting the body (see WI-204 feedback — no fallbacks).
    /// `body_expected` is the let's own `expected` (the outer hint),
    /// passed forward to the body Visit per WI-270.
    LetAfterValue {
        pattern: TermId,
        annotation: Option<TermId>,
        body_occ: Rc<NodeOccurrence>,
        body_expected: Option<TermId>,
    },
    /// Body finished; merge `value_effects` (captured at
    /// `LetAfterValue` time so we didn't need to keep `value_r`
    /// alive — its `env` was moved into the body's ext_env, which is
    /// the whole point of WI-258's COW) with `body_r.effects` and
    /// return the let's TypeResult.
    LetFinal { value_effects: Vec<TermId> },
    /// Scrutinee finished; walk the branch patterns for coverage,
    /// compute each branch's env, schedule body Visits + a
    /// `MatchFinal` frame. `body_expected` flows to every branch body.
    MatchAfterScrutinee {
        branches: Vec<MatchBranch>,
        outer_env: Rc<TypingEnv>,
        body_expected: Option<TermId>,
    },
    /// All branch bodies finished; pop `branch_count` results, filter
    /// per-branch effects against each branch's local resources,
    /// emit non-exhaustiveness diagnostics, return the match's
    /// TypeResult.
    MatchFinal {
        scr_effects: Vec<TermId>,
        branch_envs: Vec<Rc<TypingEnv>>,
        branch_count: usize,
        outer_env: Rc<TypingEnv>,
        scr_ty: Option<TermId>,
        covered_entities: Vec<Symbol>,
        has_wildcard: bool,
    },
    /// Lambda body finished; build the `arrow(param, body_ty,
    /// body_effects)` type and return a pure result (creating a
    /// lambda is itself effect-free).
    LambdaBody { param: TermId, outer_env: Rc<TypingEnv> },
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
    work.push(TypeWorkOp::Visit {
        occ: Rc::clone(occ),
        env: Rc::new(env.clone()),
        expected,
    });
    while let Some(op) = work.pop() {
        match op {
            TypeWorkOp::Visit { occ, env, expected } => {
                visit_type(kb, occ, env, expected, &mut work, &mut results)
            }
            TypeWorkOp::Build(frame) => build_type(kb, frame, &mut work, &mut results),
        }
    }
    debug_assert_eq!(results.len(), 1, "iterative typer: expected exactly one result");
    results.pop().expect("iterative typer: missing final result")
}

/// Try to resolve `sym` to a constructor symbol. Handles both the
/// already-qualified case (sym is itself the constructor) and the
/// short-name case where the loader didn't link the body's reference
/// to the qualified entity symbol. Returns `Some(qualified)` when the
/// short symbol maps to exactly one entity short→qualified index entry.
fn resolve_constructor_sym(kb: &KnowledgeBase, sym: Symbol) -> Option<Symbol> {
    if kb.is_constructor_symbol(sym) {
        return Some(sym);
    }
    if let Some(q) = kb.entity_qualified_for_short(sym) {
        if kb.is_constructor_symbol(q) {
            return Some(q);
        }
    }
    None
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
) -> Result<TypeResult, TypeError> {
    if let Some(ty) = env.lookup_var(sym) {
        return Ok(TypeResult::pure(ty, env.clone()));
    }
    if let Some(ctor_sym) = resolve_constructor_sym(kb, sym) {
        return check_constructor_iter(kb, env, ctor_sym, &[], &[], &[], &[], span, None);
    }
    if let Some(ret_ty) = lookup_operation_return_type(kb, sym) {
        return Ok(TypeResult::pure(ret_ty, env.clone()));
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
    work: &mut Vec<TypeWorkOp>,
    results: &mut Vec<Result<TypeResult, TypeError>>,
) {
    // Expr / MatchBranch don't derive Clone (Expr's classification
    // RefCell + the implicit sharing through Rc), so we match by
    // reference and `Rc::clone` / hand-clone the slots we need.
    let occ_span = Some(occ.span.span);
    let expr = match &occ.kind {
        NodeKind::Expr { expr, .. } => expr,
        NodeKind::RuleHead { .. } => {
            results.push(Err(TypeError::BottomExpr { span: occ_span }));
            return;
        }
    };
    match expr {
        // ── Iterative cases ─────────────────────────────────────
        Expr::Let { pattern, type_annotation, value, body } => {
            let pattern = *pattern;
            let annotation = *type_annotation;
            let value_occ = Rc::clone(value);
            let body_occ = Rc::clone(body);
            // WI-270: value's expected is the let's annotation only —
            // the outer `expected` doesn't constrain `let x = e` since
            // `e`'s type isn't required to match the let-expression's
            // result type. The let's own `expected` instead flows
            // through to the body.
            work.push(TypeWorkOp::Build(TypeBuildFrame::LetAfterValue {
                pattern,
                annotation,
                body_occ,
                body_expected: expected,
            }));
            work.push(TypeWorkOp::Visit {
                occ: value_occ,
                env,
                expected: annotation,
            });
        }
        Expr::Match { scrutinee, branches } => {
            let scrutinee_occ = Rc::clone(scrutinee);
            let branches_cloned: Vec<MatchBranch> = branches
                .iter()
                .map(|b| MatchBranch {
                    pattern: b.pattern,
                    guard: b.guard.as_ref().map(Rc::clone),
                    body: Rc::clone(&b.body),
                    span: b.span,
                })
                .collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::MatchAfterScrutinee {
                branches: branches_cloned,
                outer_env: Rc::clone(&env),
                body_expected: expected,
            }));
            push_visit_no_hint(work, scrutinee_occ, env);
        }
        Expr::Lambda { param, body } => {
            let param = *param;
            let body_occ = Rc::clone(body);
            let param_type = extract_pattern_type_ann(kb, param);
            let mut lambda_env = (*env).clone();
            extend_env_from_pattern(kb, &mut lambda_env, param, param_type);
            // WI-270: if expected is `arrow(param, result, effects)`,
            // decompose and pass `result` to the body. Mismatching
            // shapes (or `None`) leave the body without a hint.
            let body_expected = expected
                .and_then(|exp| extract_function_type_parts(kb, exp))
                .map(|(ret, _)| ret);
            work.push(TypeWorkOp::Build(TypeBuildFrame::LambdaBody {
                param,
                outer_env: env,
            }));
            work.push(TypeWorkOp::Visit {
                occ: body_occ,
                env: Rc::new(lambda_env),
                expected: body_expected,
            });
        }

        // ── Leaf cases ──────────────────────────────────────────
        Expr::Const(Literal::Int(_)) | Expr::Const(Literal::BigInt(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("Int"), unwrap_env(env)),
        )),
        Expr::Const(Literal::Float(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("Float"), unwrap_env(env)),
        )),
        Expr::Const(Literal::String(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("String"), unwrap_env(env)),
        )),
        Expr::Const(Literal::Bool(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("Bool"), unwrap_env(env)),
        )),
        // `Handle(_)` literals are reserved for materialized runtime
        // values; they never appear in surface source. If one shows up,
        // it's a post-elaboration form being re-typed.
        Expr::Const(_) => results.push(Err(TypeError::BottomExpr { span: occ_span })),
        Expr::Ref(sym) => {
            let r = check_bare_ref(kb, &*env, *sym, occ_span);
            results.push(r);
        }
        Expr::Ident(sym) => {
            let r = check_bare_ref(kb, &*env, *sym, occ_span);
            results.push(r);
        }
        Expr::VarRef { name } => {
            let r = check_bare_ref(kb, &*env, *name, occ_span);
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
            }));
            for (_, arg) in named_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env));
            }
            for arg in pos_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env));
            }
        }
        Expr::Constructor { name, pos_args, named_args } => {
            let name = *name;
            let pos_args = pos_args.clone();
            let named_args = named_args.clone();
            work.push(TypeWorkOp::Build(TypeBuildFrame::Constructor {
                ctor_sym: name,
                pos_args: pos_args.clone(),
                named_args: named_args.clone(),
                env: Rc::clone(&env),
                span: occ_span,
                expected,
            }));
            for (_, arg) in named_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env));
            }
            for arg in pos_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env));
            }
        }

        // ── Recursive-helper cases (depth bounded by source breadth,
        //    not nesting): if has fixed arity, collection literals
        //    iterate over flat element lists. Their `check_*` helpers
        //    re-enter `type_check_node`, adding ≤ 1 host frame per
        //    level; the iterative dispatch keeps the inner recursion
        //    flat.
        Expr::If { condition, then_branch, else_branch } => {
            let condition = Rc::clone(condition);
            let then_branch = Rc::clone(then_branch);
            let else_branch = Rc::clone(else_branch);
            let r = check_if_expr(kb, &*env, &condition, &then_branch, &else_branch, expected);
            results.push(r);
        }
        Expr::ListLit(elems) => {
            let elems = elems.clone();
            let r = check_list_literal(kb, &*env, &elems, expected);
            results.push(r);
        }
        Expr::SetLit(elems) => {
            let elems = elems.clone();
            let r = check_set_literal(kb, &*env, &elems, expected);
            results.push(r);
        }
        Expr::TupleLit { positional, named } => {
            let positional = positional.clone();
            let named = named.clone();
            let r = check_tuple_literal(kb, &*env, &positional, &named);
            results.push(r);
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
            results.push(Ok(TypeResult::pure(ty, unwrap_env(env))));
        }

        // Post-elaboration forms — emitted by req_insertion, not the
        // surface typer.
        Expr::HoApply { .. }
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

/// Assemble a Let / Match / Lambda result from its child results.
fn build_type(
    kb: &mut KnowledgeBase,
    frame: TypeBuildFrame,
    work: &mut Vec<TypeWorkOp>,
    results: &mut Vec<Result<TypeResult, TypeError>>,
) {
    match frame {
        TypeBuildFrame::Apply { occ, fn_sym, pos_args, named_args, env, expected } => {
            let total = pos_args.len() + named_args.len();
            let drain_start = results.len() - total;
            let mut arg_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            let named_results = arg_results.split_off(pos_args.len());
            let pos_results = arg_results;
            let span = Some(occ.span.span);
            let r = check_apply_iter(
                kb, &*env, &occ, fn_sym, &pos_args, &named_args,
                &pos_results, &named_results, span, expected,
            );
            results.push(r);
        }
        TypeBuildFrame::Constructor { ctor_sym, pos_args, named_args, env, span, expected } => {
            let total = pos_args.len() + named_args.len();
            let drain_start = results.len() - total;
            let mut arg_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            let named_results = arg_results.split_off(pos_args.len());
            let pos_results = arg_results;
            let r = check_constructor_iter(
                kb, &*env, ctor_sym, &pos_args, &named_args,
                &pos_results, &named_results, span, expected,
            );
            results.push(r);
        }
        TypeBuildFrame::LetAfterValue { pattern, annotation, body_occ, body_expected } => {
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
            let (value_ty, value_effects, mut ext_env) =
                (Some(r.ty), r.effects, r.env);
            let bound_ty = annotation.or(value_ty);
            extend_env_from_pattern(kb, &mut ext_env, pattern, bound_ty);
            if let Some(var_name) = extract_pattern_var_name(kb, pattern) {
                ext_env.declare_local_resource(var_name);
            }
            work.push(TypeWorkOp::Build(TypeBuildFrame::LetFinal { value_effects }));
            work.push(TypeWorkOp::Visit {
                occ: body_occ,
                env: Rc::new(ext_env),
                expected: body_expected,
            });
        }
        TypeBuildFrame::LetFinal { value_effects } => {
            let body_r = results.pop().expect("LetFinal: missing body result");
            let body_r = match body_r {
                Ok(r) => r,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };
            let effects = merge_effects(&value_effects, &body_r.effects);
            results.push(Ok(TypeResult {
                ty: body_r.ty,
                env: body_r.env,
                effects,
            }));
        }
        TypeBuildFrame::MatchAfterScrutinee { branches, outer_env, body_expected } => {
            let scr_r = results.pop().expect("MatchAfterScrutinee: missing scrutinee result");
            let scr_ty = scr_r.as_ref().ok().map(|r| r.ty);
            let scr_effects = scr_r.as_ref().ok().map(|r| r.effects.clone()).unwrap_or_default();

            // Coverage / exhaustiveness inputs are derived purely from
            // pattern terms, independent of body type-checks — compute
            // here so MatchFinal can run the check without re-walking.
            let mut covered_entities: Vec<Symbol> = Vec::new();
            let mut has_wildcard = false;
            let mut branch_envs: Vec<Rc<TypingEnv>> = Vec::with_capacity(branches.len());
            for branch in &branches {
                collect_covered_entities(
                    kb,
                    branch.pattern,
                    &mut covered_entities,
                    &mut has_wildcard,
                );
                let mut branch_env = (*outer_env).clone();
                extend_env_from_pattern(kb, &mut branch_env, branch.pattern, scr_ty);
                branch_envs.push(Rc::new(branch_env));
            }

            let branch_count = branches.len();
            // Materialize Visit envs first (Rc::clone from branch_envs),
            // then move branch_envs into the MatchFinal frame.
            let visit_envs: Vec<Rc<TypingEnv>> =
                branch_envs.iter().map(Rc::clone).collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::MatchFinal {
                scr_effects,
                branch_envs,
                branch_count,
                outer_env,
                scr_ty,
                covered_entities,
                has_wildcard,
            }));
            for (branch, env) in branches.iter().zip(visit_envs.into_iter()).rev() {
                work.push(TypeWorkOp::Visit {
                    occ: Rc::clone(&branch.body),
                    env,
                    expected: body_expected,
                });
            }
        }
        TypeBuildFrame::MatchFinal {
            scr_effects,
            branch_envs,
            branch_count,
            outer_env,
            scr_ty,
            covered_entities,
            has_wildcard,
        } => {
            let drain_start = results.len() - branch_count;
            let branch_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(branch_results.iter()) {
                results.push(Err(e));
                return;
            }
            let mut effects = scr_effects;
            let mut result_ty: Option<TermId> = None;
            for (i, body_r) in branch_results.into_iter().enumerate() {
                let body_r = body_r.expect("aggregator");
                if result_ty.is_none() {
                    result_ty = Some(body_r.ty);
                }
                // Filter effects against this branch's locals so
                // pattern-bound resources don't leak past the case
                // arm (their bindings live only inside the branch).
                let branch_external = external_effects(kb, &*branch_envs[i], &body_r.effects);
                effects = merge_effects(&effects, &branch_external);
            }

            let mut result_env = (*outer_env).clone();
            if !has_wildcard {
                if let Some(sty) = scr_ty {
                    if let Some(sort_sym) = extract_sort_ref_sym(kb, sty) {
                        let sort_term = kb.make_name_term_from_sym(sort_sym);
                        if kb.sort_kind(sort_term) == Some(SortKind::Enum) {
                            let entity_terms = kb.sort_children(sort_term);
                            let all_entities: Vec<Symbol> = entity_terms
                                .iter()
                                .filter_map(|&et| match kb.get_term(et) {
                                    Term::Fn { functor, .. } => Some(*functor),
                                    _ => None,
                                })
                                .collect();
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
            results.push(match result_ty {
                Some(ty) => Ok(TypeResult { ty, env: result_env, effects }),
                None => Err(TypeError::Other {
                    span: None,
                    context: TypeErrorContext::Rule {
                        name: kb.intern("match"),
                        field: RuleField::Whole,
                    },
                    expected: "non-empty match expression".to_string(),
                    actual: "match with no branches".to_string(),
                }),
            });
        }
        TypeBuildFrame::LambdaBody { param, outer_env } => {
            let body_r = results.pop().expect("LambdaBody: missing body result");
            let param_type = extract_pattern_type_ann(kb, param);
            // Build arrow(param, result, effects) type term
            let a_val = param_type.unwrap_or_else(|| {
                let fresh = kb.intern("?param");
                kb.make_type_var(fresh)
            });
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
                Ok(_) => results.push(Ok(TypeResult::pure(fn_type, unwrap_env(outer_env)))),
                Err(e) => results.push(Err(e)),
            }
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
            kb, env, fn_sym, pos_args, named_args, pos_results, named_results, span, expected,
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

        return Ok(TypeResult { ty: resolved_ret, env: env.clone(), effects });
    }

    // Path 2: variable with arrow type
    if let Some(fn_type_tid) = env.lookup_var(fn_sym) {
        if let Some((ret_type, effects)) = extract_function_type_parts(kb, fn_type_tid) {
            return Ok(TypeResult { ty: ret_type, env: env.clone(), effects });
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
        .map(|ty| TypeResult { ty, env: env.clone(), effects })
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
    kb: &KnowledgeBase,
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
        if !kb.rule_body(rid).is_empty() {
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
    let result = resolve_at_goal(kb, &goal, spec_sort, op_short_sym, enclosing_requires);
    kb.resolve_cache.borrow_mut().insert(key, result.clone());
    result
}

/// Resolve a pre-built `SortGoal` to a `(DispatchOutcome, Option<ResolvedRequiresNode>)`.
/// Shared body of `dispatch_spec_op_with_tree` and `dispatch_spec_op_cached`
/// — they differ only in pre-check (defer trigger) and memoization.
fn resolve_at_goal(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    spec_sort: Symbol,
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
                let op_short = kb.resolve_sym(op_short_sym).to_string();
                let impl_qn = kb.qualified_name_of(*impl_sort).to_string();
                let spec_qn = kb.qualified_name_of(spec_sort).to_string();
                let resolved = kb
                    .try_resolve_symbol(&format!("{impl_qn}.{op_short}"))
                    .or_else(|| kb.try_resolve_symbol(&format!("{spec_qn}.{op_short}")));
                match resolved {
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

/// True iff the OperationInfo for `op_sym` records body = none.
/// (Operations declared without a body ⇒ specs / abstract decls.)
fn operation_has_no_body(kb: &KnowledgeBase, op_sym: Symbol) -> bool {
    let op_info_sym = match kb.try_resolve_symbol("anthill.reflect.OperationInfo") {
        Some(s) => s,
        None => return false,
    };
    for rid in kb.by_functor(op_info_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        let name_sym = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "name")
            .and_then(|(_, v)| match kb.get_term(*v) { Term::Ref(s) => Some(*s), _ => None })
        {
            Some(s) => s,
            None => continue,
        };
        if name_sym != op_sym { continue; }

        let body_opt = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "body")
            .map(|(_, v)| *v)
        {
            Some(t) => t,
            None => return true,  // no body field at all
        };
        return unwrap_option(kb, body_opt).is_none();
    }
    false
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
) -> Result<TypeResult, TypeError> {
    if pos_results.is_empty() && named_results.is_empty() {
        let unit_ty = kb.make_sort_ref_by_name("anthill.prelude.Unit");
        return Ok(TypeResult::pure(unit_ty, env.clone()));
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
    Ok(TypeResult { ty: tuple_ty, env: env.clone(), effects })
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
            kb, env, named_args, pos_results, named_results,
        );
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
        return Ok(TypeResult { ty: parent_type, env: env.clone(), effects });
    }

    // Build parameterized type from the sort's type params + substitution bindings.
    // Look up SortAlias facts for the parent sort's scope to find param names → Var mappings.
    // For free-standing entities there is no parent sort to walk; the entity's
    // own symbol is the type — no type params to discover, so return the
    // simple sort_ref directly.
    let parent_sym = match parent_sort {
        Some(parent_tid) => match kb.get_term(parent_tid) {
            Term::Fn { functor, .. } => *functor,
            _ => return Ok(TypeResult { ty: parent_type, env: env.clone(), effects }),
        },
        None => return Ok(TypeResult { ty: parent_type, env: env.clone(), effects }),
    };

    let alias_sym = kb.try_resolve_symbol("SortAlias");
    let mut param_bindings: Vec<(Symbol, TermId)> = Vec::new();

    if let Some(a_sym) = alias_sym {
        let parent_name = kb.qualified_name_of(parent_sym).to_string();
        // Collect alias info: (param_short_name, VarId, bound_type)
        let mut alias_info: Vec<(String, TermId)> = Vec::new();
        for rid in kb.by_functor(a_sym) {
            if !kb.rule_body(rid).is_empty() { continue; }
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
        Ok(TypeResult { ty: parent_type, env: env.clone(), effects })
    } else {
        let base = kb.make_sort_ref(parent_sym);
        let param_type = kb.make_parameterized_type(base, &param_bindings);
        Ok(TypeResult { ty: param_type, env: env.clone(), effects })
    }
}

/// Extract return type and effects from an arrow(param, result, effects) type term.
fn extract_function_type_parts(kb: &KnowledgeBase, fn_type: TermId) -> Option<(TermId, Vec<TermId>)> {
    if let Term::Fn { functor, named_args, .. } = kb.get_term(fn_type) {
        let name = kb.resolve_sym(*functor);
        if name == "arrow" {
            let ret_type = get_named_arg(kb, named_args, "result")?;
            let effects = get_named_arg(kb, named_args, "effects")
                .map(|e| list_to_vec(kb, e))
                .unwrap_or_default();
            return Some((ret_type, effects));
        }
    }
    None
}

/// if_expr: effects = cond ∪ then ∪ else
fn check_if_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    condition: &Rc<NodeOccurrence>,
    then_branch: &Rc<NodeOccurrence>,
    else_branch: &Rc<NodeOccurrence>,
    expected: Option<TermId>,
) -> Result<TypeResult, TypeError> {
    // WI-270: both branches share the caller's expected hint; the
    // condition is always `Bool` so it carries no hint.
    let results = [
        type_check_node(kb, env, condition, None),
        type_check_node(kb, env, then_branch, expected),
        type_check_node(kb, env, else_branch, expected),
    ];
    collect_arg_errors(results.iter())?;
    let [cond_r, then_r, else_r] = results.map(|r| r.expect("aggregator"));

    let mut effects = Vec::new();
    effects = merge_effects(&effects, &cond_r.effects);
    effects = merge_effects(&effects, &then_r.effects);
    effects = merge_effects(&effects, &else_r.effects);

    Ok(TypeResult { ty: then_r.ty, env: env.clone(), effects })
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

// ── Collection literals ────────────────────────────────────────

/// ListLiteral: elems are positional, no source-form tail in the
/// NodeOccurrence model — the materializer expands cons-list sugar into
/// the elements vector.
fn check_list_literal(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    elems: &[Rc<NodeOccurrence>],
    expected: Option<TermId>,
) -> Result<TypeResult, TypeError> {
    // WI-270: if `expected` is `List[T = X]`, propagate X as each
    // element's expected so e.g. `[1, 2]: List[BigInt]` types
    // elements as BigInt rather than Int.
    let element_hint = expected.and_then(|exp| extract_type_param(kb, exp, "T"));
    let results: Vec<Result<TypeResult, TypeError>> = elems
        .iter()
        .map(|e| type_check_node(kb, env, e, element_hint))
        .collect();
    collect_arg_errors(results.iter())?;

    let mut effects = Vec::new();
    let mut element_type: Option<TermId> = element_hint;
    for r in results {
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

    Ok(TypeResult { ty: list_type, env: env.clone(), effects })
}

/// SetLiteral: elems are positional.
fn check_set_literal(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    elems: &[Rc<NodeOccurrence>],
    expected: Option<TermId>,
) -> Result<TypeResult, TypeError> {
    let element_hint = expected.and_then(|exp| extract_type_param(kb, exp, "T"));
    let results: Vec<Result<TypeResult, TypeError>> = elems
        .iter()
        .map(|e| type_check_node(kb, env, e, element_hint))
        .collect();
    collect_arg_errors(results.iter())?;

    let mut effects = Vec::new();
    let mut element_type: Option<TermId> = element_hint;
    for r in results {
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

    Ok(TypeResult { ty: set_type, env: env.clone(), effects })
}

/// TupleLiteral: positional fields produce a named-tuple type with
/// `_0`, `_1`, … field names; explicitly named fields keep their name.
fn check_tuple_literal(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    positional: &[Rc<NodeOccurrence>],
    named: &[(Symbol, Rc<NodeOccurrence>)],
) -> Result<TypeResult, TypeError> {
    let pos_results: Vec<Result<TypeResult, TypeError>> = positional
        .iter()
        .map(|e| type_check_node(kb, env, e, None))
        .collect();
    let named_results: Vec<Result<TypeResult, TypeError>> = named
        .iter()
        .map(|(_, e)| type_check_node(kb, env, e, None))
        .collect();
    collect_arg_errors(pos_results.iter().chain(named_results.iter()))?;

    let mut effects = Vec::new();
    let mut field_types: Vec<(Symbol, TermId)> = Vec::new();
    for (i, r) in pos_results.into_iter().enumerate() {
        let r = r.expect("aggregator");
        let field_name = kb.intern(&format!("_{}", i));
        field_types.push((field_name, r.ty));
        effects = merge_effects(&effects, &r.effects);
    }
    for ((name, _), r) in named.iter().zip(named_results.into_iter()) {
        let r = r.expect("aggregator");
        field_types.push((*name, r.ty));
        effects = merge_effects(&effects, &r.effects);
    }

    let tuple_type = kb.make_named_tuple_type(&field_types);

    Ok(TypeResult { ty: tuple_type, env: env.clone(), effects })
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
    kb: &KnowledgeBase,
    env: &mut TypingEnv,
    pattern: TermId,
    scrutinee_type: Option<TermId>,
) {
    if let Term::Fn { functor, named_args, pos_args } = kb.get_term(pattern).clone() {
        let functor_name = kb.resolve_sym(functor).to_string();
        match functor_name.as_str() {
            "var_pattern" => {
                if let Some(sym) = extract_sym_arg(kb, &named_args, &pos_args, "name") {
                    if let Some(ty) = scrutinee_type {
                        env.bind_var(sym, ty);
                    }
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
                let args_tid = get_named_arg(kb, &named_args, "args")
                    .or_else(|| pos_args.first().copied());
                if let Some(args) = args_tid {
                    for sub_pat in &list_to_vec(kb, args) {
                        extend_env_from_pattern(kb, env, *sub_pat, None);
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
        if !kb.rule_body(rid).is_empty() { continue; }
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
pub fn unify_types(kb: &KnowledgeBase, subst: &mut Substitution, a: TermId, b: TermId) -> bool {
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
    kb: &KnowledgeBase,
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
            if !kb.rule_body(rid).is_empty() { continue; }
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
fn unify_parameterized(kb: &KnowledgeBase, subst: &mut Substitution, a: TermId, b: TermId) -> bool {
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
fn unify_arrow(kb: &KnowledgeBase, subst: &mut Substitution, a: TermId, b: TermId) -> bool {
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

    true
}

/// Unify two named tuple types: matching fields must unify.
fn unify_named_tuple(kb: &KnowledgeBase, subst: &mut Substitution, a: TermId, b: TermId) -> bool {
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
        (Some("named_tuple"), Some("named_tuple")) => {
            named_tuple_compatible(kb, actual, expected)
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
        if !kb.rule_body(rid).is_empty() { continue; }
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
        if !kb.rule_body(rid).is_empty() { continue; }
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
    let actual_effects = get_named_arg(kb, &actual_args, "effects")
        .map(|e| list_to_vec(kb, e))
        .unwrap_or_default();
    let expected_effects = get_named_arg(kb, &expected_args, "effects")
        .map(|e| list_to_vec(kb, e))
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
pub fn type_check_sorts_typed(kb: &mut KnowledgeBase, sort_terms: &[TermId]) -> Vec<TypeError> {
    let mut errors: Vec<TypeError> = Vec::new();

    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(s) => s,
        None => return errors,
    };

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
        check_pattern_fragment(kb, sort_term, &mut errors);
        check_rule_typing(kb, sort_term, &mut errors);
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
        if !kb.rule_body(rid).is_empty() { continue; }
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
fn check_value_against_type(
    kb: &KnowledgeBase,
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
            if !ok {
                let actual = match lit {
                    Literal::String(_) => "String",
                    Literal::Int(_) => "Int",
                    Literal::Float(_) => "Float",
                    Literal::Bool(_) => "Bool",
                    _ => "?",
                };
                Some(TypeError::Other {
                    span,
                    context: TypeErrorContext::EntityField { entity: entity_sym, field: field_sym },
                    expected: type_display_name(kb, declared_type),
                    actual: actual.to_string(),
                })
            } else {
                None
            }
        }
        Term::Fn { functor: val_functor, .. } => {
            if let Some(parent) = kb.constructor_parent_sort(*val_functor) {
                if !constructor_matches_declared(kb, parent, declared_sym) {
                    return Some(TypeError::Other {
                        span,
                        context: TypeErrorContext::EntityField { entity: entity_sym, field: field_sym },
                        expected: type_display_name(kb, declared_type),
                        actual: extract_parent_name(kb, parent),
                    });
                }
            }
            None
        }
        Term::Ref(val_sym) => {
            if kb.is_constructor_symbol(*val_sym) {
                if let Some(parent) = kb.constructor_parent_sort(*val_sym) {
                    if !constructor_matches_declared(kb, parent, declared_sym) {
                        return Some(TypeError::Other {
                            span,
                            context: TypeErrorContext::EntityField { entity: entity_sym, field: field_sym },
                            expected: type_display_name(kb, declared_type),
                            actual: extract_parent_name(kb, parent),
                        });
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Check value against a parameterized type like List[T=Int].
fn check_value_against_parameterized(
    kb: &KnowledgeBase,
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

    // Check entity belongs to base sort
    if let Some(parent) = kb.constructor_parent_sort(val_functor) {
        if !constructor_matches_declared(kb, parent, base_sym) {
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

/// Check all facts for the given entity constructors against their declared field types.
fn check_entity_facts(kb: &KnowledgeBase, ctor_syms: &[Symbol], errors: &mut Vec<TypeError>) {
    for &ctor_sym in ctor_syms {
        let field_types = match kb.entity_field_types(ctor_sym) {
            Some(ft) => ft.to_vec(),
            None => continue,
        };
        if field_types.is_empty() { continue; }

        for rid in kb.by_functor(ctor_sym) {
            if !kb.rule_body(rid).is_empty() { continue; }

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
                if !types_compatible(kb, result.ty, op.return_type) {
                    errors.push(TypeError::TypeMismatch {
                        span: None,
                        context: TypeErrorContext::OperationReturn { op_name: op.op_sym },
                        expected: op.return_type,
                        actual: result.ty,
                    });
                }

                // Filter out local resource effects — only external effects must be declared
                let ext_effects = external_effects(kb, &result.env, &result.effects);
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
    covered: &mut Vec<Symbol>,
    has_wildcard: &mut bool,
) {
    if let Term::Fn { functor, named_args, pos_args, .. } = kb.get_term(pattern) {
        let fname = kb.resolve_sym(*functor).to_string();
        match fname.as_str() {
            "wildcard" => { *has_wildcard = true; }
            "var_pattern" => {
                // A var_pattern might actually be a nullary constructor (e.g., `case red`)
                if let Some(sym) = extract_sym_arg(kb, named_args, pos_args, "name") {
                    let qname = kb.qualified_name_of(sym);
                    let resolved = kb.try_resolve_symbol(qname);
                    let ctor_sym = resolved.unwrap_or(sym);
                    if kb.is_constructor_symbol(ctor_sym) || kb.constructor_parent_sort(ctor_sym).is_some() {
                        covered.push(ctor_sym);
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
        let body = kb.rule_body(rid);
        if body.is_empty() { continue; } // skip facts — only check rules

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

        // Check body goals for pattern fragment violations
        for &goal_tid in body {
            check_ho_apply_pattern(kb, goal_tid, ho_apply_sym, head_sym, span, errors);
        }
    }
}

/// Check a term for ho_apply pattern fragment violations.
fn check_ho_apply_pattern(
    kb: &KnowledgeBase,
    term: TermId,
    ho_apply_sym: Symbol,
    rule_sym: Symbol,
    span: Option<Span>,
    errors: &mut Vec<TypeError>,
) {
    match kb.get_term(term) {
        Term::Fn { functor, pos_args, named_args, .. } => {
            let functor = *functor;
            let pos_args = pos_args.clone();
            let named_args = named_args.clone();

            if functor == ho_apply_sym && !pos_args.is_empty() {
                // This is an ho_apply — check pattern fragment rules

                // Rule 2: first arg (predicate) must be a variable
                let pred = pos_args[0];
                if !matches!(kb.get_term(pred), Term::Var(_)) {
                    // After body_rename, the var may be substituted with a concrete term.
                    // In stored rules (DeBruijn), it should be a Var. In opened rules, it may not be.
                    // Only check stored (DeBruijn) rules.
                    if matches!(kb.get_term(pred), Term::Fn { .. }) {
                        // Check if it's another ho_apply — predicate applied to predicate
                        if let Term::Fn { functor: inner_f, .. } = kb.get_term(pred) {
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
                }

                // Rule 3: remaining args must be distinct (no duplicate variables)
                let mut seen_vars: Vec<u32> = Vec::new();
                for &arg in &pos_args[1..] {
                    if let Term::Var(Var::DeBruijn(idx)) = kb.get_term(arg) {
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

                    // Rule 3b: args must not contain ho_apply (no predicate variable as argument)
                    if term_contains_functor(kb, arg, ho_apply_sym) {
                        errors.push(TypeError::Other {
                            span,
                            context: TypeErrorContext::Rule { name: rule_sym, field: RuleField::Body },
                            expected: "first-order args in ho_apply".to_string(),
                            actual: "predicate variable as argument to predicate".to_string(),
                        });
                    }
                }
            }

            // Recurse into subterms
            for &arg in pos_args.iter() {
                check_ho_apply_pattern(kb, arg, ho_apply_sym, rule_sym, span, errors);
            }
            for &(_, arg) in named_args.iter() {
                check_ho_apply_pattern(kb, arg, ho_apply_sym, rule_sym, span, errors);
            }
        }
        _ => {}
    }
}

/// Check if a term (or any subterm) contains the given functor.
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
fn check_rule_typing(kb: &KnowledgeBase, sort_term: TermId, errors: &mut Vec<TypeError>) {
    for rid in kb.by_domain(sort_term) {
        let body = kb.rule_body(rid);
        if body.is_empty() { continue; } // facts have no body — nothing to check

        let head = kb.rule_head(rid);
        let mut subst = Substitution::new();
        let mut var_types: HashMap<u32, TermId> = std::collections::HashMap::new();

        // Collect type constraints from head
        collect_term_type_constraints(kb, head, &mut var_types, &mut subst);

        // Collect type constraints from body goals
        for &goal_tid in body {
            collect_term_type_constraints(kb, goal_tid, &mut var_types, &mut subst);
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
    kb: &KnowledgeBase,
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
    kb: &KnowledgeBase,
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

    if let Some(&existing_type) = var_types.get(&vid) {
        // Variable already has a type — unify with the new expected type
        if !unify_types(kb, subst, existing_type, expected_type) {
            subst.contradiction = true;
        }
    } else {
        var_types.insert(vid, expected_type);
    }
}

