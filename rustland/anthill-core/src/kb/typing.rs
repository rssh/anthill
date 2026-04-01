/// Typing pass — type-check expressions following typing_pass_spec.anthill.
///
/// Rust implementation of TypingEnv, TypeResult, TypeError, and type_check.
/// Types are TermId values in the KB (types are terms in anthill).
/// Effects are tracked as List[Type] alongside the value type.

use std::collections::HashMap;

use smallvec::SmallVec;

use super::term::{Term, TermId, Literal, HandleKind};
use super::occurrence::OccurrenceId;
use super::KnowledgeBase;
use crate::intern::Symbol;
use crate::span::Span;

// ── TypeError ──────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum TypeError {
    TypeMismatch {
        occ: Option<OccurrenceId>,
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
        }
    }

    pub fn span(&self, kb: &KnowledgeBase) -> Option<Span> {
        let occ = match self {
            TypeError::TypeMismatch { occ, .. } => *occ,
            TypeError::UnknownField { occ, .. } => *occ,
            TypeError::UnresolvedName { occ, .. } => *occ,
            TypeError::NoParentSort { .. } => None,
        };
        occ.map(|id| kb.occurrences.span(id).span)
    }
}

// ── TypingEnv ──────────────────────────────────────────────────

#[derive(Clone)]
pub struct TypingEnv {
    var_bindings: HashMap<String, TermId>,
    type_bindings: HashMap<String, TermId>,
    expected_collection_type: Option<TermId>,
    local_resources: Vec<String>,
}

impl TypingEnv {
    pub fn empty() -> Self {
        Self {
            var_bindings: HashMap::new(),
            type_bindings: HashMap::new(),
            expected_collection_type: None,
            local_resources: Vec::new(),
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

    /// Merge effects from another result (set union by TermId).
    pub fn merge_effects(&mut self, other: &TypeResult) {
        for e in &other.effects {
            if !self.effects.contains(e) {
                self.effects.push(*e);
            }
        }
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
        Term::Fn { functor, pos_args, named_args } => {
            let name = kb.resolve_sym(*functor);
            if pos_args.is_empty() && named_args.is_empty() {
                name.to_string()
            } else {
                let params: Vec<String> = named_args.iter()
                    .map(|(s, v)| format!("{} = {}", kb.resolve_sym(*s), type_display_name(kb, *v)))
                    .collect();
                if params.is_empty() {
                    name.to_string()
                } else {
                    format!("{}[{}]", name, params.join(", "))
                }
            }
        }
        Term::Ref(s) => kb.resolve_sym(*s).to_string(),
        _ => format!("{:?}", ty),
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

/// Build a cons-list term from a slice of TermIds.
fn build_list(kb: &mut KnowledgeBase, items: &[TermId]) -> TermId {
    let nil_sym = kb.intern("nil");
    let cons_sym = kb.intern("cons");
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");

    let mut list = kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    for &item in items.iter().rev() {
        let mut args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        args.push((head_sym, item));
        args.push((tail_sym, list));
        args.sort_by_key(|(s, _)| s.index());
        list = kb.alloc(Term::Fn {
            functor: cons_sym,
            pos_args: SmallVec::new(),
            named_args: args,
        });
    }
    list
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
        Term::Const(Literal::Int(_)) => Some(TypeResult::pure(kb.make_name_term("Int"), env.clone())),
        Term::Const(Literal::Float(_)) => Some(TypeResult::pure(kb.make_name_term("Float"), env.clone())),
        Term::Const(Literal::String(_)) => Some(TypeResult::pure(kb.make_name_term("String"), env.clone())),
        Term::Const(Literal::Bool(_)) => Some(TypeResult::pure(kb.make_name_term("Bool"), env.clone())),
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
                kb.constructor_parent_sort(*sym).map(|ty| TypeResult::pure(ty, env.clone()))
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
                "int_lit" => Some(TypeResult::pure(kb.make_name_term("Int"), env.clone())),
                "float_lit" => Some(TypeResult::pure(kb.make_name_term("Float"), env.clone())),
                "string_lit" => Some(TypeResult::pure(kb.make_name_term("String"), env.clone())),
                "bool_lit" => Some(TypeResult::pure(kb.make_name_term("Bool"), env.clone())),
                "var_ref" => {
                    let name_sym = extract_sym_arg(kb, &named_args, &pos_args, "name")?;
                    let name = kb.resolve_sym(name_sym).to_string();
                    env.lookup_var(&name).map(|ty| TypeResult::pure(ty, env.clone()))
                }
                "constructor" => {
                    let name_sym = extract_sym_arg(kb, &named_args, &pos_args, "name")?;
                    kb.constructor_parent_sort(name_sym).map(|ty| TypeResult::pure(ty, env.clone()))
                }
                "apply" => check_apply(kb, env, &named_args, &pos_args),
                "if_expr" => check_if_expr(kb, env, &named_args),
                "let_expr" => check_let_expr(kb, env, &named_args),
                "match_expr" => check_match_expr(kb, env, &named_args),
                "lambda" => check_lambda(kb, env, &named_args),
                _ => {
                    let f_sym = *functor;
                    if kb.is_constructor_symbol(f_sym) {
                        kb.constructor_parent_sort(f_sym).map(|ty| TypeResult::pure(ty, env.clone()))
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

/// apply(fn, args): two paths —
/// 1. fn is a known operation → return type + effects from OperationInfo
/// 2. fn is a variable with Function[A, B, E] type → extract B and E
fn check_apply(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    pos_args: &SmallVec<[TermId; 4]>,
) -> Option<TypeResult> {
    let fn_sym = extract_sym_arg(kb, named_args, pos_args, "fn")?;

    // Path 1: known operation
    if let Some(ret_type) = lookup_operation_return_type(kb, fn_sym) {
        let callee_effects = lookup_operation_effects(kb, fn_sym);
        return Some(TypeResult { ty: ret_type, env: env.clone(), effects: callee_effects });
    }

    // Path 2: variable with Function type
    let fn_name = kb.resolve_sym(fn_sym).to_string();
    if let Some(fn_type_tid) = env.lookup_var(&fn_name) {
        if let Some((ret_type, effects)) = extract_function_type_parts(kb, fn_type_tid) {
            return Some(TypeResult { ty: ret_type, env: env.clone(), effects });
        }
    }

    None
}

/// Extract return type (B) and effects (E) from a Function[A, B, E] type term.
fn extract_function_type_parts(kb: &KnowledgeBase, fn_type: TermId) -> Option<(TermId, Vec<TermId>)> {
    if let Term::Fn { functor, named_args, .. } = kb.get_term(fn_type) {
        let name = kb.resolve_sym(*functor);
        if name == "Function" || name == "anthill.prelude.Function" {
            let ret_type = named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "B")
                .map(|(_, v)| *v)?;
            let effects = named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "E")
                .map(|(_, v)| list_to_vec(kb, *v))
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

/// let_expr: effects = value ∪ body
fn check_let_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TypeResult> {
    let pattern = get_named_arg(kb, named_args, "pattern")?;
    let value = get_named_arg(kb, named_args, "value")?;
    let body = get_named_arg(kb, named_args, "body")?;

    let value_r = type_check_expr(kb, env, resolve_handle(kb, value));
    let value_ty = value_r.as_ref().map(|r| r.ty);

    let mut ext_env = value_r.as_ref().map(|r| r.env.clone()).unwrap_or_else(|| env.clone());
    extend_env_from_pattern(kb, &mut ext_env, pattern, value_ty);

    let body_r = type_check_expr(kb, &ext_env, resolve_handle(kb, body))?;

    let mut effects = Vec::new();
    if let Some(ref r) = value_r { effects = merge_effects(&effects, &r.effects); }
    effects = merge_effects(&effects, &body_r.effects);

    Some(TypeResult { ty: body_r.ty, env: body_r.env, effects })
}

/// match_expr: effects = scrutinee ∪ all branches
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

    for branch_tid in &branch_list {
        if let Term::Fn { named_args: br_args, .. } = kb.get_term(*branch_tid).clone() {
            let pattern = get_named_arg(kb, &br_args, "pattern");
            let body = get_named_arg(kb, &br_args, "body");
            if let (Some(pat), Some(bod)) = (pattern, body) {
                let mut branch_env = env.clone();
                extend_env_from_pattern(kb, &mut branch_env, pat, scr_ty);
                if let Some(body_r) = type_check_expr(kb, &branch_env, resolve_handle(kb, bod)) {
                    if result_ty.is_none() { result_ty = Some(body_r.ty); }
                    effects = merge_effects(&effects, &body_r.effects);
                }
            }
        }
    }

    result_ty.map(|ty| TypeResult { ty, env: env.clone(), effects })
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

    // Build Function[A, B] or Function[A, B, E] type term
    let function_sym = kb.intern("Function");
    let a_key = kb.intern("A");
    let b_key = kb.intern("B");
    let a_val = param_type.unwrap_or_else(|| kb.make_name_term("?"));
    let b_val = body_r.as_ref().map(|r| r.ty).unwrap_or_else(|| kb.make_name_term("?"));
    let body_effects = body_r.as_ref().map(|r| r.effects.clone()).unwrap_or_default();

    let mut fn_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    fn_args.push((a_key, a_val));
    fn_args.push((b_key, b_val));

    // If body has effects, encode them in the function type as E parameter
    if !body_effects.is_empty() {
        let e_key = kb.intern("E");
        let effects_list = build_list(kb, &body_effects);
        fn_args.push((e_key, effects_list));
    }

    fn_args.sort_by_key(|(s, _)| s.index());
    let fn_type = kb.alloc(Term::Fn {
        functor: function_sym,
        pos_args: SmallVec::new(),
        named_args: fn_args,
    });

    // Creating a lambda is pure — effects are in the type, not in the evaluation
    Some(TypeResult::pure(fn_type, env.clone()))
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

fn lookup_operation_effects(kb: &KnowledgeBase, functor: Symbol) -> Vec<TermId> {
    match lookup_operation_field(kb, functor, "effects") {
        Some(effects_tid) => list_to_vec(kb, effects_tid),
        None => Vec::new(),
    }
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

// ── type_check_operations entry point ──────────────────────────

use super::load::LoadError;

/// Type-check all operations with expression bodies.
pub fn type_check_operations(kb: &mut KnowledgeBase) -> Vec<LoadError> {
    let mut errors = Vec::new();

    let op_info_sym = match kb.try_resolve_symbol("anthill.reflect.OperationInfo") {
        Some(s) => s,
        None => return errors,
    };

    struct OpInfo {
        op_name: String,
        return_type: TermId,
        declared_effects: Vec<TermId>,
        body_expr: TermId,
        params: Vec<(String, TermId)>,
        span: Option<Span>,
    }

    let mut ops_to_check = Vec::new();

    for rid in kb.by_functor(op_info_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args.clone(),
            _ => continue,
        };

        let op_name_sym = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "name")
            .and_then(|(_, v)| match kb.get_term(*v) { Term::Ref(s) => Some(*s), _ => None })
        {
            Some(s) => s,
            None => continue,
        };
        let op_name = kb.resolve_sym(op_name_sym).to_string();

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

        // Declared effects
        let declared_effects = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "effects")
            .map(|(_, v)| list_to_vec(kb, *v))
            .unwrap_or_default();

        // Params
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

        let span = kb.occurrences.by_functor(op_name_sym)
            .first()
            .map(|&occ_id| kb.occurrences.span(occ_id).span);

        ops_to_check.push(OpInfo { op_name, return_type, declared_effects, body_expr, params, span });
    }

    for op in &ops_to_check {
        let mut env = TypingEnv::empty();
        for (name, ty) in &op.params {
            env.bind_var(name.clone(), *ty);
        }

        if let Some(result) = type_check_expr(kb, &env, op.body_expr) {
            // Check return type
            if result.ty != op.return_type {
                let inferred_name = type_display_name(kb, result.ty);
                let expected_name = type_display_name(kb, op.return_type);
                if inferred_name != expected_name {
                    errors.push(LoadError::TypeMismatch {
                        entity_name: op.op_name.clone(),
                        field_name: "return".to_string(),
                        expected_type: expected_name,
                        actual_type: inferred_name,
                        span: op.span,
                    });
                }
            }

            // Check effects: body effects ⊆ declared effects
            // Filter out local resource effects first
            for effect in &result.effects {
                if !op.declared_effects.contains(effect) {
                    let effect_name = type_display_name(kb, *effect);
                    let declared_names: Vec<String> = op.declared_effects.iter()
                        .map(|e| type_display_name(kb, *e))
                        .collect();
                    // Only report if effect name doesn't match any declared (by name)
                    if !declared_names.iter().any(|d| d == &effect_name) {
                        errors.push(LoadError::TypeMismatch {
                            entity_name: op.op_name.clone(),
                            field_name: "effects".to_string(),
                            expected_type: format!("declared: [{}]", declared_names.join(", ")),
                            actual_type: format!("undeclared effect: {}", effect_name),
                            span: op.span,
                        });
                    }
                }
            }
        }
    }

    errors
}
