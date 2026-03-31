/// Typing pass — type-check expressions following typing_pass_spec.anthill.
///
/// Rust implementation of TypingEnv, TypeResult, TypeError, and type_check.
/// Types are TermId values in the KB (types are terms in anthill).

use std::collections::HashMap;

use smallvec::SmallVec;

use super::term::{Term, TermId, Literal, HandleKind};
use super::occurrence::OccurrenceId;
use super::KnowledgeBase;
use crate::intern::Symbol;
use crate::span::Span;

// ── TypeError ──────────────────────────────────────────────────

/// Typing error — mirrors anthill.reflect.typing_pass.TypeError.
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

/// Typing environment — mirrors anthill.reflect.typing_pass.TypingEnv.
/// Variable bindings map names to type TermIds.
/// Type parameter bindings map param names to type TermIds (for generics).
#[derive(Clone)]
pub struct TypingEnv {
    var_bindings: HashMap<String, TermId>,
    type_bindings: HashMap<String, TermId>,
    expected_collection_type: Option<TermId>,
}

impl TypingEnv {
    pub fn empty() -> Self {
        Self {
            var_bindings: HashMap::new(),
            type_bindings: HashMap::new(),
            expected_collection_type: None,
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
}

// ── TypeResult ─────────────────────────────────────────────────

/// Result of type_check: the inferred type + updated env.
pub struct TypeResult {
    pub ty: TermId,
    pub env: TypingEnv,
}

// ── Helpers ────────────────────────────────────────────────────

/// Display name for a type term (for error messages).
pub fn type_display_name(kb: &KnowledgeBase, ty: TermId) -> String {
    match kb.get_term(ty) {
        Term::Fn { functor, pos_args, named_args } => {
            let name = kb.resolve_sym(*functor);
            if pos_args.is_empty() && named_args.is_empty() {
                name.to_string()
            } else {
                // Parameterized type: Name[args]
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
        Term::Const(Literal::Int(n)) => format!("{}", n),
        Term::Const(Literal::String(s)) => format!("\"{}\"", s),
        _ => format!("{:?}", ty),
    }
}

/// Resolve an occurrence handle to its underlying expression term.
pub fn resolve_handle(kb: &KnowledgeBase, handle_tid: TermId) -> TermId {
    match kb.get_term(handle_tid) {
        Term::Const(Literal::Handle(HandleKind::Occurrence, occ_raw)) => {
            let occ_id = OccurrenceId::from_raw(*occ_raw);
            kb.occurrences.term(occ_id)
        }
        _ => handle_tid,
    }
}

/// Extract a named_arg value by key name.
pub fn get_named_arg(kb: &KnowledgeBase, named_args: &SmallVec<[(Symbol, TermId); 2]>, key: &str) -> Option<TermId> {
    named_args.iter()
        .find(|(s, _)| kb.resolve_sym(*s) == key)
        .map(|(_, v)| *v)
}

/// Extract a Symbol from named_args (by key name) or first pos_arg.
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

/// Unwrap Option term: some(value) → Some(value_tid), none() → None.
pub fn unwrap_option(kb: &KnowledgeBase, opt: TermId) -> Option<TermId> {
    if let Term::Fn { functor, pos_args, named_args } = kb.get_term(opt) {
        if kb.resolve_sym(*functor) == "some" {
            if !pos_args.is_empty() { return Some(pos_args[0]); }
            if !named_args.is_empty() { return Some(named_args[0].1); }
        }
    }
    None
}

/// Walk a cons-list term and return elements as Vec<TermId>.
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

/// Infer the type of an expression term. Returns the type as a TermId.
pub fn type_check_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    expr: TermId,
) -> Option<TermId> {
    let term = kb.get_term(expr).clone();
    match &term {
        // Literals → primitive type terms
        Term::Const(Literal::Int(_)) => Some(kb.make_name_term("Int")),
        Term::Const(Literal::Float(_)) => Some(kb.make_name_term("Float")),
        Term::Const(Literal::String(_)) => Some(kb.make_name_term("String")),
        Term::Const(Literal::Bool(_)) => Some(kb.make_name_term("Bool")),
        // Handle — resolve and recurse
        Term::Const(Literal::Handle(HandleKind::Occurrence, occ_raw)) => {
            let inner = kb.occurrences.term(OccurrenceId::from_raw(*occ_raw));
            type_check_expr(kb, env, inner)
        }
        // Variable reference
        Term::Ref(sym) => {
            let name = kb.resolve_sym(*sym).to_string();
            if let Some(ty) = env.lookup_var(&name) {
                Some(ty)
            } else if kb.is_constructor_symbol(*sym) {
                kb.constructor_parent_sort(*sym)
            } else {
                None
            }
        }
        Term::Ident(sym) => {
            let name = kb.resolve_sym(*sym).to_string();
            env.lookup_var(&name)
        }
        // Function / expression forms
        Term::Fn { functor, named_args, pos_args } => {
            let functor_name = kb.resolve_sym(*functor).to_string();
            let named_args = named_args.clone();
            let pos_args = pos_args.clone();
            match functor_name.as_str() {
                "int_lit" => Some(kb.make_name_term("Int")),
                "float_lit" => Some(kb.make_name_term("Float")),
                "string_lit" => Some(kb.make_name_term("String")),
                "bool_lit" => Some(kb.make_name_term("Bool")),
                "var_ref" => {
                    let name_sym = extract_sym_arg(kb, &named_args, &pos_args, "name")?;
                    let name = kb.resolve_sym(name_sym).to_string();
                    env.lookup_var(&name)
                }
                "constructor" => {
                    let name_sym = extract_sym_arg(kb, &named_args, &pos_args, "name")?;
                    kb.constructor_parent_sort(name_sym)
                }
                "apply" => {
                    let fn_sym = extract_sym_arg(kb, &named_args, &pos_args, "fn")?;
                    lookup_operation_return_type(kb, fn_sym)
                }
                "if_expr" => {
                    check_if_expr(kb, env, &named_args)
                }
                "let_expr" => {
                    check_let_expr(kb, env, &named_args)
                }
                "match_expr" => {
                    check_match_expr(kb, env, &named_args)
                }
                "lambda" => {
                    check_lambda(kb, env, &named_args)
                }
                _ => {
                    let f_sym = *functor;
                    if kb.is_constructor_symbol(f_sym) {
                        kb.constructor_parent_sort(f_sym)
                    } else {
                        lookup_operation_return_type(kb, f_sym)
                    }
                }
            }
        }
        _ => None,
    }
}

// ── Expression form checkers ───────────────────────────────────

fn check_if_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TermId> {
    let cond = get_named_arg(kb, named_args, "cond")?;
    let then_b = get_named_arg(kb, named_args, "then_branch")?;
    let else_b = get_named_arg(kb, named_args, "else_branch")?;

    let _cond_type = type_check_expr(kb, env, resolve_handle(kb, cond));
    let then_type = type_check_expr(kb, env, resolve_handle(kb, then_b));
    let else_type = type_check_expr(kb, env, resolve_handle(kb, else_b));

    then_type.or(else_type)
}

fn check_let_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TermId> {
    let pattern = get_named_arg(kb, named_args, "pattern")?;
    let value = get_named_arg(kb, named_args, "value")?;
    let body = get_named_arg(kb, named_args, "body")?;

    let value_type = type_check_expr(kb, env, resolve_handle(kb, value));
    let mut ext_env = env.clone();
    extend_env_from_pattern(kb, &mut ext_env, pattern, value_type);
    type_check_expr(kb, &ext_env, resolve_handle(kb, body))
}

fn check_match_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TermId> {
    let scrutinee = get_named_arg(kb, named_args, "scrutinee")?;
    let branches = get_named_arg(kb, named_args, "branches")?;

    let scrutinee_type = type_check_expr(kb, env, resolve_handle(kb, scrutinee));
    let branch_list = list_to_vec(kb, branches);
    let mut result_type: Option<TermId> = None;

    for branch_tid in &branch_list {
        if let Term::Fn { named_args: br_args, .. } = kb.get_term(*branch_tid).clone() {
            let pattern = get_named_arg(kb, &br_args, "pattern");
            let body = get_named_arg(kb, &br_args, "body");
            if let (Some(pat), Some(bod)) = (pattern, body) {
                let mut branch_env = env.clone();
                extend_env_from_pattern(kb, &mut branch_env, pat, scrutinee_type);
                if let Some(body_type) = type_check_expr(kb, &branch_env, resolve_handle(kb, bod)) {
                    if result_type.is_none() {
                        result_type = Some(body_type);
                    }
                }
            }
        }
    }
    result_type
}

fn check_lambda(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<TermId> {
    let param = get_named_arg(kb, named_args, "param")?;
    let body = get_named_arg(kb, named_args, "body")?;

    let param_type = extract_pattern_type_ann(kb, param);
    let mut lambda_env = env.clone();
    extend_env_from_pattern(kb, &mut lambda_env, param, param_type);

    let body_type = type_check_expr(kb, &lambda_env, resolve_handle(kb, body));

    // Build Function[A, B] type term
    let function_sym = kb.intern("Function");
    let a_key = kb.intern("A");
    let b_key = kb.intern("B");
    let a_val = param_type.unwrap_or_else(|| kb.make_name_term("?"));
    let b_val = body_type.unwrap_or_else(|| kb.make_name_term("?"));
    let mut fn_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    fn_args.push((a_key, a_val));
    fn_args.push((b_key, b_val));
    fn_args.sort_by_key(|(s, _)| s.index());
    Some(kb.alloc(Term::Fn {
        functor: function_sym,
        pos_args: SmallVec::new(),
        named_args: fn_args,
    }))
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
            // wildcard, literal_pattern — no bindings
            _ => {}
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

// ── Operation return type lookup ───────────────────────────────

fn lookup_operation_return_type(kb: &KnowledgeBase, functor: Symbol) -> Option<TermId> {
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
                            .find(|(s, _)| kb.resolve_sym(*s) == "return_type")
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

    // Collect operation info upfront to avoid borrow issues
    struct OpInfo {
        op_name: String,
        return_type: TermId,
        body_expr: TermId,
        params: Vec<(String, TermId)>,  // (param_name, param_type)
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

        // Extract params
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

        ops_to_check.push(OpInfo { op_name, return_type, body_expr, params, span });
    }

    // Now type-check each operation (with &mut kb)
    for op in &ops_to_check {
        let mut env = TypingEnv::empty();
        for (name, ty) in &op.params {
            env.bind_var(name.clone(), *ty);
        }

        if let Some(inferred) = type_check_expr(kb, &env, op.body_expr) {
            if inferred != op.return_type {
                // Check by name as fallback (same type may have different TermIds)
                let inferred_name = type_display_name(kb, inferred);
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
        }
    }

    errors
}
