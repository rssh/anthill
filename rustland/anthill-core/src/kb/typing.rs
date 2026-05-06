/// Typing pass — type-check expressions following typing_pass_spec.anthill.
///
/// Rust implementation of TypingEnv, TypeResult, TypeError, and type_check.
/// Types are TermId values in the KB (types are terms in anthill).
/// Effects are tracked as List[Type] alongside the value type.

use std::collections::HashMap;

use smallvec::SmallVec;

use super::term::{Term, TermId, Literal, HandleKind, Var, VarId};
use super::occurrence::OccurrenceId;
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
        occ: Option<OccurrenceId>,
        context: TypeErrorContext,
        expected: TermId,
        actual: TermId,
    },
    UnknownField {
        occ: Option<OccurrenceId>,
        entity_name: Symbol,
        field: Symbol,
    },
    NoParentSort {
        name: Symbol,
    },
    UnresolvedName {
        occ: Option<OccurrenceId>,
        name: Symbol,
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
            TypeError::Other { expected, actual, .. } => {
                format!("expected {}, got {}", expected, actual)
            }
        }
    }

    pub fn span(&self, kb: &KnowledgeBase) -> Option<Span> {
        match self {
            TypeError::TypeMismatch { occ, .. }
            | TypeError::UnknownField { occ, .. }
            | TypeError::UnresolvedName { occ, .. } => {
                occ.map(|id| kb.occurrences.span(id).span)
            }
            TypeError::Other { span, .. } => *span,
            TypeError::NoParentSort { .. } => None,
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
    var_bindings: HashMap<String, TermId>,
    type_bindings: HashMap<String, TermId>,
    expected_collection_type: Option<TermId>,
    local_resources: Vec<String>,
    pub diagnostics: Vec<String>,
}

impl TypingEnv {
    pub fn empty() -> Self {
        Self {
            var_bindings: HashMap::new(),
            type_bindings: HashMap::new(),
            expected_collection_type: None,
            local_resources: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    pub fn bind_var(&mut self, name: String, ty: TermId) {
        self.var_bindings.insert(name, ty);
    }

    pub fn lookup_var(&self, name: &str) -> Option<TermId> {
        self.var_bindings.get(name).copied()
    }

    pub fn bind_type(&mut self, param: String, ty: TermId) {
        self.type_bindings.insert(param, ty);
    }

    pub fn lookup_type(&self, param: &str) -> Option<TermId> {
        self.type_bindings.get(param).copied()
    }

    pub fn with_expected_collection_type(&self, ty: Option<TermId>) -> Self {
        let mut env = self.clone();
        env.expected_collection_type = ty;
        env
    }

    pub fn expected_collection_type(&self) -> Option<TermId> {
        self.expected_collection_type
    }

    pub fn declare_local_resource(&mut self, name: String) {
        self.local_resources.push(name);
    }

    pub fn is_local_resource(&self, name: &str) -> bool {
        self.local_resources.iter().any(|r| r == name)
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
        // Effect terms are sort_ref or parameterized. Extract the resource name.
        let resource_name = extract_effect_resource_name(kb, effect);
        match resource_name {
            Some(name) => !env.is_local_resource(&name),
            None => true, // can't determine resource — assume external
        }
    }).copied().collect()
}

/// Extract the resource name from an effect term.
/// e.g., Modify[T = store] → "store", or sort_ref(name: Modify) → None (no resource)
fn extract_effect_resource_name(kb: &KnowledgeBase, effect: TermId) -> Option<String> {
    let functor_name = type_functor_name(kb, effect)?;
    match functor_name {
        "parameterized" => {
            // parameterized(base: sort_ref(Modify), bindings: [TypeBinding(param: T, value: sort_ref(store))])
            if let Term::Fn { named_args, .. } = kb.get_term(effect) {
                let bindings_tid = get_named_arg(kb, named_args, "bindings")?;
                let bindings = list_to_vec(kb, bindings_tid);
                // Take the first binding's value as the resource
                for b in &bindings {
                    if let Some(value_tid) = binding_value(kb, *b) {
                        // The resource could be sort_ref(name: store) or just a Ref
                        if let Some(sym) = extract_sort_ref_sym(kb, value_tid) {
                            return Some(kb.resolve_sym(sym).to_string());
                        }
                        if let Term::Ref(s) = kb.get_term(value_tid) {
                            return Some(kb.resolve_sym(*s).to_string());
                        }
                    }
                }
            }
            None
        }
        "sort_ref" => {
            // A bare effect like sort_ref(Branch) — no resource parameter
            None
        }
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

pub fn resolve_handle(kb: &KnowledgeBase, handle_tid: TermId) -> TermId {
    match kb.get_term(handle_tid) {
        Term::Const(Literal::Handle(HandleKind::Occurrence, occ_raw)) => {
            let occ_id = OccurrenceId::from_raw(*occ_raw);
            kb.occurrences.term(occ_id)
        }
        _ => handle_tid,
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


// ── type_check_expr ────────────────────────────────────────────

/// Infer the type of an expression. Returns TypeResult with type, env, and effects.
pub fn type_check_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    expr: TermId,
) -> Option<TypeResult> {
    let term = kb.get_term(expr).clone();
    match &term {
        // Literals → pure
        Term::Const(Literal::Int(_)) => Some(TypeResult::pure(kb.make_sort_ref_by_name("Int"), env.clone())),
        Term::Const(Literal::Float(_)) => Some(TypeResult::pure(kb.make_sort_ref_by_name("Float"), env.clone())),
        Term::Const(Literal::String(_)) => Some(TypeResult::pure(kb.make_sort_ref_by_name("String"), env.clone())),
        Term::Const(Literal::Bool(_)) => Some(TypeResult::pure(kb.make_sort_ref_by_name("Bool"), env.clone())),
        // Handle — resolve and recurse
        Term::Const(Literal::Handle(HandleKind::Occurrence, occ_raw)) => {
            let inner = kb.occurrences.term(OccurrenceId::from_raw(*occ_raw));
            type_check_expr(kb, env, inner)
        }
        // Variable reference — pure
        Term::Ref(sym) => {
            let name = kb.resolve_sym(*sym).to_string();
            if let Some(ty) = env.lookup_var(&name) {
                Some(TypeResult::pure(ty, env.clone()))
            } else if kb.is_constructor_symbol(*sym) {
                infer_constructor_type(kb, env, *sym, &SmallVec::new(), &SmallVec::new())
            } else {
                None
            }
        }
        Term::Ident(sym) => {
            let name = kb.resolve_sym(*sym).to_string();
            env.lookup_var(&name).map(|ty| TypeResult::pure(ty, env.clone()))
        }
        // Fn — expression forms
        Term::Fn { functor, named_args, pos_args } => {
            let functor_name = kb.resolve_sym(*functor).to_string();
            let named_args = named_args.clone();
            let pos_args = pos_args.clone();
            match functor_name.as_str() {
                "int_lit" => Some(TypeResult::pure(kb.make_sort_ref_by_name("Int"), env.clone())),
                "float_lit" => Some(TypeResult::pure(kb.make_sort_ref_by_name("Float"), env.clone())),
                "string_lit" => Some(TypeResult::pure(kb.make_sort_ref_by_name("String"), env.clone())),
                "bool_lit" => Some(TypeResult::pure(kb.make_sort_ref_by_name("Bool"), env.clone())),
                "var_ref" => {
                    let name_sym = extract_sym_arg(kb, &named_args, &pos_args, "name")?;
                    let name = kb.resolve_sym(name_sym).to_string();
                    env.lookup_var(&name).map(|ty| TypeResult::pure(ty, env.clone()))
                }
                "constructor" => {
                    let name_sym = extract_sym_arg(kb, &named_args, &pos_args, "name")?;
                    let args_tid = get_named_arg(kb, &named_args, "args");
                    let ctor_args: SmallVec<[TermId; 4]> = args_tid
                        .map(|a| list_to_vec(kb, a).into_iter().collect())
                        .unwrap_or_default();
                    infer_constructor_type(kb, env, name_sym, &ctor_args, &SmallVec::new())
                }
                "apply" => check_apply(kb, env, &named_args, &pos_args),
                "if_expr" => check_if_expr(kb, env, &named_args),
                "let_expr" => check_let_expr(kb, env, &named_args),
                "match_expr" => check_match_expr(kb, env, &named_args),
                "lambda" => check_lambda(kb, env, &named_args),
                "ListLiteral" | "anthill.reflect.ListLiteral" => {
                    check_list_literal(kb, env, &pos_args, &named_args)
                }
                "SetLiteral" | "anthill.reflect.SetLiteral" => {
                    check_set_literal(kb, env, &pos_args)
                }
                "TupleLiteral" | "anthill.reflect.TupleLiteral" => {
                    check_tuple_literal(kb, env, &pos_args)
                }
                _ => {
                    let f_sym = *functor;
                    if kb.is_constructor_symbol(f_sym) {
                        infer_constructor_type(kb, env, f_sym, &pos_args, &named_args)
                    } else {
                        lookup_operation_return_type(kb, f_sym).map(|ty| TypeResult::pure(ty, env.clone()))
                    }
                }
            }
        }
        _ => None,
    }
}

// ── Expression form checkers ───────────────────────────────────

/// apply(fn, args): type-check with type parameter instantiation.
/// 1. fn is a known operation → unify arg types with param types, resolve return type
/// 2. fn is a variable with arrow type → extract return type and effects
fn check_apply(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    pos_args: &SmallVec<[TermId; 4]>,
) -> Option<TypeResult> {
    let fn_sym = extract_sym_arg(kb, named_args, pos_args, "fn")?;

    // Path 1: known operation — unify args with params to instantiate type params
    if let Some(op) = lookup_operation_info_full(kb, fn_sym) {
        let mut subst = Substitution::new();
        let mut effects = op.effects.clone();

        // Get actual arguments from the apply node
        let args_tid = get_named_arg(kb, named_args, "args")
            .or_else(|| pos_args.get(1).copied());
        let arg_values: Vec<TermId> = args_tid
            .map(|a| list_to_vec(kb, a))
            .unwrap_or_default();

        // Unify each arg type with the corresponding param type
        for (i, arg_tid) in arg_values.iter().enumerate() {
            // Extract value from ApplyArg(name, value)
            let arg_expr = if let Term::Fn { named_args: aa, .. } = kb.get_term(*arg_tid) {
                get_named_arg(kb, aa, "value")
                    .map(|v| resolve_handle(kb, v))
            } else {
                None
            };

            if let Some(expr) = arg_expr {
                if let Some(arg_result) = type_check_expr(kb, env, expr) {
                    // Get the declared param type at this position
                    if let Some(&(_, param_type)) = op.params.get(i) {
                        unify_types(kb, &mut subst, arg_result.ty, param_type);
                    }
                    effects = merge_effects(&effects, &arg_result.effects);
                }
            }
        }

        // Resolve return type through the substitution
        let resolved_ret = walk_type(kb, &subst, op.return_type);
        return Some(TypeResult { ty: resolved_ret, env: env.clone(), effects });
    }

    // Path 2: variable with arrow type
    let fn_name = kb.resolve_sym(fn_sym).to_string();
    if let Some(fn_type_tid) = env.lookup_var(&fn_name) {
        if let Some((ret_type, effects)) = extract_function_type_parts(kb, fn_type_tid) {
            return Some(TypeResult { ty: ret_type, env: env.clone(), effects });
        }
    }

    None
}

/// Full operation info for type checking: params with types, return type, effects.
struct OperationInfoFull {
    params: Vec<(Symbol, TermId)>,  // (param_name, param_type)
    return_type: TermId,
    effects: Vec<TermId>,
}

/// Look up complete OperationInfo for a functor.
fn lookup_operation_info_full(kb: &KnowledgeBase, functor: Symbol) -> Option<OperationInfoFull> {
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")?;
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
        if name_sym != functor { continue; }

        let return_type = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "return_type")
            .map(|(_, v)| *v)?;

        let effects = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "effects")
            .map(|(_, v)| list_to_vec(kb, *v))
            .unwrap_or_default();

        let mut params = Vec::new();
        if let Some(params_tid) = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "params")
            .map(|(_, v)| *v)
        {
            for param_tid in &list_to_vec(kb, params_tid) {
                if let Term::Fn { named_args: pargs, .. } = kb.get_term(*param_tid) {
                    let pname = pargs.iter()
                        .find(|(s, _)| kb.resolve_sym(*s) == "name")
                        .and_then(|(_, v)| match kb.get_term(*v) { Term::Ref(s) => Some(*s), _ => None });
                    let ptype = pargs.iter()
                        .find(|(s, _)| kb.resolve_sym(*s) == "type_name")
                        .map(|(_, v)| *v);
                    if let (Some(name), Some(ty)) = (pname, ptype) {
                        params.push((name, ty));
                    }
                }
            }
        }

        return Some(OperationInfoFull { params, return_type, effects });
    }
    None
}

/// Infer the type of a constructor application, including type parameter instantiation.
/// e.g., cons(head: 1, tail: nil) → parameterized(List, [T=Int])
fn infer_constructor_type(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    ctor_sym: Symbol,
    pos_args: &SmallVec<[TermId; 4]>,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TypeResult> {
    let parent_tid = kb.constructor_parent_sort(ctor_sym)?;
    let parent_type = sort_term_to_type(kb, parent_tid);

    // Get the constructor's declared field types
    let field_types = kb.entity_field_types(ctor_sym)?.to_vec();
    if field_types.is_empty() {
        return Some(TypeResult::pure(parent_type, env.clone()));
    }

    let mut subst = Substitution::new();
    let mut effects = Vec::new();

    // Unify named args with field types
    for &(field_sym, declared_type) in &field_types {
        let arg_tid = named_args.iter()
            .find(|(s, _)| *s == field_sym)
            .map(|(_, v)| *v);
        if let Some(arg) = arg_tid {
            if let Some(r) = type_check_expr(kb, env, resolve_handle(kb, arg)) {
                unify_types(kb, &mut subst, r.ty, declared_type);
                effects = merge_effects(&effects, &r.effects);
            }
        }
    }

    // Unify positional args with field types in order
    for (i, &arg) in pos_args.iter().enumerate() {
        if let Some(&(_, declared_type)) = field_types.get(i) {
            // For constructor expression form, args are ApplyArg(name, value)
            let actual_arg = if let Term::Fn { named_args: aa, .. } = kb.get_term(arg) {
                get_named_arg(kb, aa, "value")
                    .map(|v| resolve_handle(kb, v))
                    .unwrap_or(arg)
            } else {
                arg
            };
            if let Some(r) = type_check_expr(kb, env, actual_arg) {
                unify_types(kb, &mut subst, r.ty, declared_type);
                effects = merge_effects(&effects, &r.effects);
            }
        }
    }

    // If any type params were bound, build a parameterized type
    if subst.bindings.is_empty() {
        return Some(TypeResult { ty: parent_type, env: env.clone(), effects });
    }

    // Build parameterized type from the sort's type params + substitution bindings.
    // Look up SortAlias facts for the parent sort's scope to find param names → Var mappings.
    let parent_sym = match kb.get_term(parent_tid) {
        Term::Fn { functor, .. } => *functor,
        _ => return Some(TypeResult { ty: parent_type, env: env.clone(), effects }),
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
        Some(TypeResult { ty: parent_type, env: env.clone(), effects })
    } else {
        let base = kb.make_sort_ref(parent_sym);
        let param_type = kb.make_parameterized_type(base, &param_bindings);
        Some(TypeResult { ty: param_type, env: env.clone(), effects })
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
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TypeResult> {
    let cond = get_named_arg(kb, named_args, "cond")?;
    let then_b = get_named_arg(kb, named_args, "then_branch")?;
    let else_b = get_named_arg(kb, named_args, "else_branch")?;

    let cond_r = type_check_expr(kb, env, resolve_handle(kb, cond));
    let then_r = type_check_expr(kb, env, resolve_handle(kb, then_b));
    let else_r = type_check_expr(kb, env, resolve_handle(kb, else_b));

    let ty = then_r.as_ref().map(|r| r.ty)
        .or_else(|| else_r.as_ref().map(|r| r.ty))?;

    let mut effects = Vec::new();
    if let Some(ref r) = cond_r { effects = merge_effects(&effects, &r.effects); }
    if let Some(ref r) = then_r { effects = merge_effects(&effects, &r.effects); }
    if let Some(ref r) = else_r { effects = merge_effects(&effects, &r.effects); }

    Some(TypeResult { ty, env: env.clone(), effects })
}

/// let_expr: effects = value ∪ body (with local resource scoping).
///
/// Optional `type_name` named arg supplies the let-binding's annotation
/// (proposal 035 form (1)). When present, the annotation overrides the
/// value's inferred type in the body env so subsequent uses of the
/// variable typecheck against the annotation rather than the (possibly
/// looser) inferred RHS type. Type-erased constructors like `Map.empty()`
/// rely on this — their inferred return type has free type-parameter
/// variables that the annotation pins down.
fn check_let_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TypeResult> {
    let pattern = get_named_arg(kb, named_args, "pattern")?;
    let value = get_named_arg(kb, named_args, "value")?;
    let body = get_named_arg(kb, named_args, "body")?;
    let annotation = get_named_arg(kb, named_args, "type_name");

    let value_r = type_check_expr(kb, env, resolve_handle(kb, value));
    let value_ty = value_r.as_ref().map(|r| r.ty);

    let mut ext_env = value_r.as_ref().map(|r| r.env.clone()).unwrap_or_else(|| env.clone());
    // Annotation, when present, takes precedence as the bound variable's
    // type. The value's inferred type still drives effect propagation
    // (read above from value_r.effects); the annotation only affects how
    // the body sees the variable.
    let bound_ty = annotation.or(value_ty);
    extend_env_from_pattern(kb, &mut ext_env, pattern, bound_ty);

    // Declare let-bound variable as a local resource for effect scoping
    if let Some(var_name) = extract_pattern_var_name(kb, pattern) {
        ext_env.declare_local_resource(var_name);
    }

    let body_r = type_check_expr(kb, &ext_env, resolve_handle(kb, body))?;

    let mut effects = Vec::new();
    if let Some(ref r) = value_r { effects = merge_effects(&effects, &r.effects); }
    effects = merge_effects(&effects, &body_r.effects);

    Some(TypeResult { ty: body_r.ty, env: body_r.env, effects })
}

/// Extract the variable name from a pattern (for var_pattern).
fn extract_pattern_var_name(kb: &KnowledgeBase, pattern: TermId) -> Option<String> {
    if let Term::Fn { functor, named_args, pos_args, .. } = kb.get_term(pattern) {
        let fname = kb.resolve_sym(*functor);
        if fname == "var_pattern" {
            return extract_sym_arg(kb, named_args, pos_args, "name")
                .map(|s| kb.resolve_sym(s).to_string());
        }
    }
    None
}

/// match_expr: effects = scrutinee ∪ all branches. Also checks exhaustiveness.
fn check_match_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TypeResult> {
    let scrutinee = get_named_arg(kb, named_args, "scrutinee")?;
    let branches = get_named_arg(kb, named_args, "branches")?;

    let scr_r = type_check_expr(kb, env, resolve_handle(kb, scrutinee));
    let scr_ty = scr_r.as_ref().map(|r| r.ty);

    let mut effects = Vec::new();
    if let Some(ref r) = scr_r { effects = merge_effects(&effects, &r.effects); }

    let branch_list = list_to_vec(kb, branches);
    let mut result_ty: Option<TermId> = None;
    let mut covered_entities: Vec<Symbol> = Vec::new();
    let mut has_wildcard = false;

    for branch_tid in &branch_list {
        if let Term::Fn { named_args: br_args, .. } = kb.get_term(*branch_tid).clone() {
            let pattern = get_named_arg(kb, &br_args, "pattern");
            let body = get_named_arg(kb, &br_args, "body");
            if let (Some(pat), Some(bod)) = (pattern, body) {
                collect_covered_entities(kb, pat, &mut covered_entities, &mut has_wildcard);
                let mut branch_env = env.clone();
                extend_env_from_pattern(kb, &mut branch_env, pat, scr_ty);
                if let Some(body_r) = type_check_expr(kb, &branch_env, resolve_handle(kb, bod)) {
                    if result_ty.is_none() { result_ty = Some(body_r.ty); }
                    effects = merge_effects(&effects, &body_r.effects);
                }
            }
        }
    }

    // Exhaustiveness check: if scrutinee type is an enum, all entities must be covered
    let mut result_env = env.clone();
    if !has_wildcard {
        if let Some(sty) = scr_ty {
            if let Some(sort_sym) = extract_sort_ref_sym(kb, sty) {
                let sort_term = kb.make_name_term_from_sym(sort_sym);
                if kb.sort_kind(sort_term) == Some(SortKind::Enum) {
                    let entity_terms = kb.sort_children(sort_term);
                    let all_entities: Vec<Symbol> = entity_terms.iter().filter_map(|&et| {
                        match kb.get_term(et) {
                            Term::Fn { functor, .. } => Some(*functor),
                            _ => None,
                        }
                    }).collect();
                    let missing: Vec<String> = all_entities.iter()
                        .filter(|e| !covered_entities.iter().any(|c| {
                            *c == **e || kb.resolve_sym(*c) == kb.resolve_sym(**e)
                        }))
                        .map(|s| kb.resolve_sym(*s).to_string())
                        .collect();
                    if !missing.is_empty() {
                        let sort_name = kb.resolve_sym(sort_sym);
                        result_env.diagnostics.push(
                            format!("non-exhaustive match on {}: missing {}", sort_name, missing.join(", "))
                        );
                    }
                }
            }
        }
    }

    result_ty.map(|ty| TypeResult { ty, env: result_env, effects })
}

/// lambda: body effects are encoded in the function type per proposal 003.
/// Pure lambda → Function[A, B]. Effectful lambda → Function[A, B, E = effects].
/// Creating a lambda is itself pure (no effects propagated to enclosing expr).
fn check_lambda(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TypeResult> {
    let param = get_named_arg(kb, named_args, "param")?;
    let body = get_named_arg(kb, named_args, "body")?;

    let param_type = extract_pattern_type_ann(kb, param);
    let mut lambda_env = env.clone();
    extend_env_from_pattern(kb, &mut lambda_env, param, param_type);

    let body_r = type_check_expr(kb, &lambda_env, resolve_handle(kb, body));

    // Build arrow(param, result, effects) type term
    let a_val = param_type.unwrap_or_else(|| {
        let fresh = kb.intern("?param");
        kb.make_type_var(fresh)
    });
    let b_val = body_r.as_ref().map(|r| r.ty).unwrap_or_else(|| {
        let fresh = kb.intern("?result");
        kb.make_type_var(fresh)
    });
    let body_effects = body_r.as_ref().map(|r| r.effects.clone()).unwrap_or_default();

    let fn_type = kb.make_arrow_type(a_val, b_val, &body_effects);

    // Creating a lambda is pure — effects are in the type, not in the evaluation
    Some(TypeResult::pure(fn_type, env.clone()))
}

// ── Collection literals ────────────────────────────────────────

/// ListLiteral: pos_args are elements, named_arg "tail" is optional tail.
/// Type = List[T = element_type], using expected_collection_type from env if available.
fn check_list_literal(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    pos_args: &SmallVec<[TermId; 4]>,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TypeResult> {
    let mut effects = Vec::new();
    let mut element_type: Option<TermId> = None;

    // Try to get expected element type from context
    if let Some(expected) = env.expected_collection_type() {
        element_type = extract_type_param(kb, expected, "T");
    }

    // Type-check each element
    for &elem in pos_args.iter() {
        if let Some(r) = type_check_expr(kb, env, resolve_handle(kb, elem)) {
            if element_type.is_none() {
                element_type = Some(r.ty);
            }
            effects = merge_effects(&effects, &r.effects);
        }
    }

    // Type-check tail if present
    let tail = get_named_arg(kb, named_args, "tail");
    if let Some(tail_tid) = tail {
        if let Some(r) = type_check_expr(kb, env, resolve_handle(kb, tail_tid)) {
            effects = merge_effects(&effects, &r.effects);
        }
    }

    // Build parameterized(base: sort_ref(List), bindings: [TypeBinding(param: T, value: element_type)])
    let t_val = element_type.unwrap_or_else(|| {
        let fresh = kb.intern("?T");
        kb.make_type_var(fresh)
    });
    let list_base = kb.make_sort_ref_by_name("List");
    let t_sym = kb.intern("T");
    let list_type = kb.make_parameterized_type(list_base, &[(t_sym, t_val)]);

    Some(TypeResult { ty: list_type, env: env.clone(), effects })
}

/// SetLiteral: pos_args are elements.
/// Type = Set[T = element_type].
fn check_set_literal(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    pos_args: &SmallVec<[TermId; 4]>,
) -> Option<TypeResult> {
    let mut effects = Vec::new();
    let mut element_type: Option<TermId> = None;

    if let Some(expected) = env.expected_collection_type() {
        element_type = extract_type_param(kb, expected, "T");
    }

    for &elem in pos_args.iter() {
        if let Some(r) = type_check_expr(kb, env, resolve_handle(kb, elem)) {
            if element_type.is_none() {
                element_type = Some(r.ty);
            }
            effects = merge_effects(&effects, &r.effects);
        }
    }

    let t_val = element_type.unwrap_or_else(|| {
        let fresh = kb.intern("?T");
        kb.make_type_var(fresh)
    });
    let set_base = kb.make_sort_ref_by_name("Set");
    let t_sym = kb.intern("T");
    let set_type = kb.make_parameterized_type(set_base, &[(t_sym, t_val)]);

    Some(TypeResult { ty: set_type, env: env.clone(), effects })
}

/// TupleLiteral: pos_args are fields. Type = Tuple with per-field types.
fn check_tuple_literal(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    pos_args: &SmallVec<[TermId; 4]>,
) -> Option<TypeResult> {
    let mut effects = Vec::new();
    let mut field_types: Vec<(Symbol, TermId)> = Vec::new();

    for (i, &elem) in pos_args.iter().enumerate() {
        if let Some(r) = type_check_expr(kb, env, resolve_handle(kb, elem)) {
            let field_name = kb.intern(&format!("_{}", i));
            field_types.push((field_name, r.ty));
            effects = merge_effects(&effects, &r.effects);
        } else {
            let field_name = kb.intern(&format!("_{}", i));
            let fresh = kb.intern(&format!("?field_{}", i));
            field_types.push((field_name, kb.make_type_var(fresh)));
        }
    }

    // Build named_tuple(fields: List[TypeField])
    let tuple_type = kb.make_named_tuple_type(&field_types);

    Some(TypeResult { ty: tuple_type, env: env.clone(), effects })
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
                        env.bind_var(kb.resolve_sym(sym).to_string(), ty);
                    }
                }
            }
            "constructor_pattern" => {
                let name_sym = extract_sym_arg(kb, &named_args, &pos_args, "name");
                let args_tid = get_named_arg(kb, &named_args, "args");
                if let (Some(ctor_sym), Some(args)) = (name_sym, args_tid) {
                    let field_types = kb.entity_field_types(ctor_sym).map(|f| f.to_vec());
                    let sub_patterns = list_to_vec(kb, args);
                    if let Some(fields) = field_types {
                        for (i, sub_pat) in sub_patterns.iter().enumerate() {
                            let field_type = fields.get(i).map(|(_, ty)| *ty);
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
        (Some("arrow"), Some("arrow")) => {
            unify_arrow(kb, subst, a_resolved, b_resolved)
        }
        (Some("named_tuple"), Some("named_tuple")) => {
            unify_named_tuple(kb, subst, a_resolved, b_resolved)
        }
        _ => types_compatible(kb, a_resolved, b_resolved),
    }
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
            let alias_target = match resolve_sort_alias(kb, sym) {
                Some(t) => t,
                None => return ty,
            };
            // Alias to Var (type param) → resolve through substitution
            if let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) {
                subst.resolve_with_term(*vid).map_or(alias_target, |bound| walk_type(kb, subst, bound))
            } else {
                alias_target
            }
        }
        _ => ty,
    }
}

/// Look up SortAlias(sort_term, target) for a symbol. Returns the target TermId if found.
fn resolve_sort_alias(kb: &KnowledgeBase, sym: Symbol) -> Option<TermId> {
    let alias_sym = kb.try_resolve_symbol("SortAlias")?;
    let sort_name = kb.resolve_sym(sym);

    for rid in kb.by_functor(alias_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
        if let Term::Fn { pos_args, .. } = kb.get_term(head) {
            if pos_args.len() >= 2 {
                // pos_args[0] = sort term, pos_args[1] = target
                if let Term::Fn { functor, .. } = kb.get_term(pos_args[0]) {
                    if *functor == sym || kb.resolve_sym(*functor) == sort_name {
                        return Some(pos_args[1]);
                    }
                }
            }
        }
    }
    None
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
        (Some("arrow"), Some("arrow")) => {
            arrow_compatible(kb, actual, expected)
        }
        (Some("named_tuple"), Some("named_tuple")) => {
            named_tuple_compatible(kb, actual, expected)
        }
        _ => false,
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
pub struct RequiresEntry {
    /// The base sort symbol of the required spec (e.g., Eq in `requires Eq[T=Int]`).
    pub required_sort: Symbol,
    /// The full SortView term (carries bindings like T=Int, combine=add).
    pub spec: TermId,
}

/// Collect the full transitive requires chain for a sort.
/// Returns all (required_sort_sym, spec_term) pairs reachable from `sort_sym`.
pub fn requires_chain(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<RequiresEntry> {
    let mut result = Vec::new();
    let mut visited = Vec::new();
    collect_requires(kb, sort_sym, &mut result, &mut visited);
    result
}

fn collect_requires(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
    result: &mut Vec<RequiresEntry>,
    visited: &mut Vec<Symbol>,
) {
    if visited.contains(&sort_sym) { return; }
    visited.push(sort_sym);

    let requires_sym = match kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo") {
        Some(s) => s,
        None => return,
    };

    let sort_name = kb.resolve_sym(sort_sym);

    for rid in kb.by_functor(requires_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        // Check if this SortRequiresInfo is for our sort
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
        if sr_functor != sort_sym && kb.resolve_sym(sr_functor) != sort_name {
            continue;
        }

        // Get spec field — SortView(base_sort, bindings...)
        let spec_tid = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "spec")
            .map(|(_, v)| *v)
        {
            Some(t) => t,
            None => continue,
        };

        // Extract base sort from spec:
        // - SortView(base_sort, bindings...): pos_args[0] is the base sort term
        // - Plain sort term (nullary Fn): functor is the sort itself
        let base_functor = match kb.get_term(spec_tid) {
            Term::Fn { functor, pos_args, named_args, .. } if !pos_args.is_empty() => {
                // SortView: base sort is in pos_args[0]
                match kb.get_term(pos_args[0]) {
                    Term::Fn { functor, .. } => *functor,
                    _ => continue,
                }
            }
            Term::Fn { functor, pos_args, named_args, .. }
                if pos_args.is_empty() && named_args.is_empty() => {
                // Plain sort term: `requires Paintable`
                *functor
            }
            _ => continue,
        };

        result.push(RequiresEntry { required_sort: base_functor, spec: spec_tid });

        // Transitive: follow base sort's requires
        collect_requires(kb, base_functor, result, visited);
    }
}

/// Check if sort A refines sort B via `requires` chain.
fn sort_refines(kb: &KnowledgeBase, a_sym: Symbol, b_sym: Symbol) -> bool {
    let chain = requires_chain(kb, a_sym);
    let b_name = kb.resolve_sym(b_sym);
    chain.iter().any(|entry| {
        entry.required_sort == b_sym || kb.resolve_sym(entry.required_sort) == b_name
    })
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
    let chain = requires_chain(kb, sort_sym);

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

    let sort_name = kb.resolve_sym(sort_sym);

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
        if name_sym != sort_sym && kb.resolve_sym(name_sym) != sort_name {
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
fn find_sort_info(kb: &KnowledgeBase, sort_info_sym: Symbol, sort_functor: Symbol) -> Option<(Vec<Symbol>, Vec<Symbol>)> {
    let sort_name = kb.resolve_sym(sort_functor);
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
        if name_sym != sort_functor && kb.resolve_sym(name_sym) != sort_name {
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

    // Build substitution from type bindings (T → Int)
    let bindings_tid = get_named_arg(kb, &declared_args, "bindings")?;
    let bindings = list_to_vec(kb, bindings_tid);
    let mut subst = Substitution::new();
    for b in &bindings {
        let param_sym = binding_param_sym(kb, *b);
        let value_type = binding_value(kb, *b);
        if let (Some(psym), Some(vt)) = (param_sym, value_type) {
            // Resolve the type param's SortAlias Var and bind it
            if let Some(alias_target) = resolve_sort_alias(kb, psym) {
                if let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) {
                    subst.bind(*vid, vt);
                }
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

            let span: Option<Span> = kb.occurrences.by_term(head)
                .first()
                .or_else(|| kb.occurrences.by_functor(ctor_sym).iter()
                    .find(|&&occ_id| kb.occurrences.term(occ_id) == head))
                .map(|&occ_id| kb.occurrences.span(occ_id).span);

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
    let op_info_sym = match kb.try_resolve_symbol("anthill.reflect.OperationInfo") {
        Some(s) => s,
        None => return,
    };

    struct OpInfo {
        op_sym: Symbol,
        return_type: TermId,
        declared_effects: Vec<TermId>,
        body_expr: TermId,
        params: Vec<(String, TermId)>,
        span: Option<Span>,
    }

    let mut ops_to_check = Vec::new();

    for &op_sym in op_syms {
        // Find OperationInfo for this operation
        for rid in kb.by_functor(op_info_sym) {
            if !kb.rule_body(rid).is_empty() { continue; }
            let head = kb.rule_head(rid);
            let named_args = match kb.get_term(head) {
                Term::Fn { named_args, .. } => named_args.clone(),
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

            let return_type = match named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "return_type")
                .map(|(_, v)| *v)
            {
                Some(t) => t,
                None => continue,
            };

            let body_opt = match named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "body")
                .map(|(_, v)| *v)
            {
                Some(t) => t,
                None => continue,
            };
            let body_handle = match unwrap_option(kb, body_opt) {
                Some(h) => h,
                None => continue,
            };
            let body_expr = resolve_handle(kb, body_handle);

            let declared_effects = named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "effects")
                .map(|(_, v)| list_to_vec(kb, *v))
                .unwrap_or_default();

            let mut params = Vec::new();
            if let Some(params_tid) = named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "params")
                .map(|(_, v)| *v)
            {
                for param_tid in &list_to_vec(kb, params_tid) {
                    if let Term::Fn { named_args: pargs, .. } = kb.get_term(*param_tid) {
                        let pname = pargs.iter()
                            .find(|(s, _)| kb.resolve_sym(*s) == "name")
                            .and_then(|(_, v)| match kb.get_term(*v) { Term::Ref(s) => Some(*s), _ => None })
                            .map(|s| kb.resolve_sym(s).to_string());
                        let ptype = pargs.iter()
                            .find(|(s, _)| kb.resolve_sym(*s) == "type_name")
                            .map(|(_, v)| *v);
                        if let (Some(name), Some(ty)) = (pname, ptype) {
                            params.push((name, ty));
                        }
                    }
                }
            }

            let span = kb.occurrences.by_functor(name_sym)
                .first()
                .map(|&occ_id| kb.occurrences.span(occ_id).span);

            ops_to_check.push(OpInfo { op_sym: name_sym, return_type, declared_effects, body_expr, params, span });
            break; // found the OperationInfo for this op
        }
    }

    for op in &ops_to_check {
        let mut env = TypingEnv::empty();
        for (name, ty) in &op.params {
            env.bind_var(name.clone(), *ty);
        }

        if let Some(result) = type_check_expr(kb, &env, op.body_expr) {
            if !types_compatible(kb, result.ty, op.return_type) {
                errors.push(TypeError::TypeMismatch {
                    occ: None,
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
        let span = kb.occurrences.by_term(head)
            .first()
            .map(|&occ_id| kb.occurrences.span(occ_id).span);

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
            let span = kb.occurrences.by_term(head)
                .first()
                .map(|&occ_id| kb.occurrences.span(occ_id).span);
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

