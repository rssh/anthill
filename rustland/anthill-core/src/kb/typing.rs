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
    for_each_child, for_each_pattern_child, materialize_from_handle, occurrence_structural_eq,
    EffectExprNode, Expr, MatchBranch, NodeKind, NodeOccurrence, TypeChild, TypeNode,
};
use super::persist_subst::BindValue;
use super::term_view::{views_structurally_equal, TermIdView, TermView, ViewHead, ViewItem};
use super::{KnowledgeBase, SortKind};
use crate::eval::value::Value;
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
        // WI-342 (S2): carrier-agnostic `Value` — a denoted-bearing type
        // (a lambda's `Value::Node` arrow) flows straight into the diagnostic
        // without re-grounding. Rendered via `type_display_name_value`.
        expected: Value,
        actual: Value,
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
    /// WI-325: a spec-op call left at least one type parameter abstract
    /// AND the enclosing operation's `requires` chain does not cover the
    /// spec sort. Without a covering `requires`, the runtime has no impl
    /// to dispatch to — so we name this at body-load time rather than at
    /// the first call site that hits a fresh carrier. `spec_op_sym` is the
    /// spec op (e.g. `anthill.prelude.Eq.eq`), `spec_sort_sym` is the spec
    /// sort (e.g. `anthill.prelude.Eq`), and `abstract_params` lists the
    /// spec's short type-param names the call left abstract — used to
    /// suggest the exact `requires {spec}[{T = …}]` clause to add.
    MissingRequiresForSpecOp {
        span: Option<Span>,
        spec_op_sym: Symbol,
        spec_sort_sym: Symbol,
        abstract_params: SmallVec<[Symbol; 2]>,
    },
    /// Bottom or other post-elaboration expression seen by the surface
    /// typer — emitted only by `req_insertion`, never user-written.
    BottomExpr {
        span: Option<Span>,
    },
    /// WI-279: a value-receiver dot form `?x.member(args)` / `?x.member`
    /// whose `member` resolves to no operation declared on the receiver's
    /// least sort (the dot-dispatch default fallback found nothing).
    /// `receiver_sort` is the receiver's `min_sort`, or `None` when the
    /// receiver's type is unresolved (dispatch then undecidable). Reported
    /// at the dot's source span.
    DotDispatchNoMatch {
        span: Option<Span>,
        member: Symbol,
        receiver_sort: Option<Symbol>,
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
    LetBinding { var: Symbol },
}

impl TypeErrorContext {
    pub fn entity_name(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeErrorContext::EntityField { entity, .. } => kb.resolve_sym(*entity).to_string(),
            TypeErrorContext::OperationReturn { op_name }
            | TypeErrorContext::OperationEffects { op_name }
            | TypeErrorContext::OperationMatch { op_name } => kb.resolve_sym(*op_name).to_string(),
            TypeErrorContext::Rule { name, .. } => kb.resolve_sym(*name).to_string(),
            TypeErrorContext::LetBinding { var } => kb.resolve_sym(*var).to_string(),
        }
    }

    pub fn field_name(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeErrorContext::EntityField { field, .. } => kb.resolve_sym(*field).to_string(),
            TypeErrorContext::OperationReturn { .. } => "return".to_string(),
            TypeErrorContext::OperationEffects { .. } => "effects".to_string(),
            TypeErrorContext::OperationMatch { .. } => "match".to_string(),
            TypeErrorContext::Rule { field, .. } => field.name().to_string(),
            TypeErrorContext::LetBinding { .. } => "annotation".to_string(),
        }
    }
}

impl TypeError {
    pub fn format(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeError::TypeMismatch { expected, actual, .. } => {
                format!("type mismatch: expected {}, got {}",
                    type_display_name_value(kb, expected),
                    type_display_name_value(kb, actual))
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
            TypeError::MissingRequiresForSpecOp {
                spec_op_sym, spec_sort_sym, abstract_params, ..
            } => {
                let op_qn = kb.qualified_name_of(*spec_op_sym);
                let spec_qn = kb.qualified_name_of(*spec_sort_sym);
                let spec_short = short_name_of(spec_qn);
                let params_list: Vec<String> = abstract_params
                    .iter()
                    .map(|p| format!("{0} = …", kb.resolve_sym(*p)))
                    .collect();
                format!(
                    "spec op `{}` called at abstract type — add `requires {}[{}]` to the enclosing sort, or specialize to a concrete carrier",
                    op_qn,
                    spec_short,
                    params_list.join(", "),
                )
            }
            TypeError::BottomExpr { .. } => {
                "bottom or post-elaboration expression in surface IR".to_string()
            }
            TypeError::DotDispatchNoMatch { member, receiver_sort, .. } => {
                let m = kb.resolve_sym(*member);
                match receiver_sort {
                    Some(s) => format!(
                        "no member '{}' on {}: dot dispatch found no operation '{}' declared on the receiver's sort",
                        m, kb.qualified_name_of(*s), m,
                    ),
                    None => format!(
                        "cannot dispatch `.{}`: the receiver's type is unresolved",
                        m,
                    ),
                }
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
            | TypeError::MissingRequiresForSpecOp { span, .. }
            | TypeError::DotDispatchNoMatch { span, .. }
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
                expected_type: type_display_name_value(kb, expected),
                actual_type: type_display_name_value(kb, actual),
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
            TypeError::MissingRequiresForSpecOp {
                spec_op_sym, spec_sort_sym, abstract_params, ..
            } => {
                let op_qn = kb.qualified_name_of(*spec_op_sym);
                let spec_qn = kb.qualified_name_of(*spec_sort_sym);
                let spec_short = short_name_of(spec_qn);
                let params_list: Vec<String> = abstract_params
                    .iter()
                    .map(|p| format!("{0} = …", kb.resolve_sym(*p)))
                    .collect();
                let suggestion = format!(
                    "missing `requires {}[{}]` on enclosing sort",
                    spec_short,
                    params_list.join(", "),
                );
                LoadError::TypeMismatch {
                    entity_name: op_qn.to_string(),
                    field_name: "requires".to_string(),
                    expected_type: format!("`requires {}[…]` covering abstract type parameter", spec_short),
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
            TypeError::DotDispatchNoMatch { member, receiver_sort, .. } => LoadError::TypeMismatch {
                entity_name: receiver_sort
                    .map(|s| kb.qualified_name_of(s).to_string())
                    .unwrap_or_else(|| "<unresolved receiver>".to_string()),
                field_name: kb.resolve_sym(*member).to_string(),
                expected_type: "operation declared on the receiver's sort".to_string(),
                actual_type: "no such member (dot dispatch)".to_string(),
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
    // WI-341 Stage A: a var's TYPE is carrier-agnostic (`Value`) — a callback
    // parameter whose arrow effect is denoted-bearing (`Modify[a]`) is a
    // `Value::Node` arrow and cannot be a hash-consed `TermId`. Ground bindings
    // are `Value::Term`.
    var_bindings: HashMap<Symbol, Value>,
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
            local_resources: Vec::new(),
            enclosing: None,
            diagnostics: Vec::new(),
        }
    }

    /// Set the sort whose body is currently being type-checked and
    /// snapshot its **direct** `requires` chain (cheap-ish: one
    /// `SortRequiresInfo` scan via `direct_requires_chain`). `check_apply`
    /// reads the cached chain per spec-op dispatch without re-walking
    /// facts.
    ///
    /// WI-239: direct (not flat-transitive) so the slot indices
    /// `find_requires_slot` / `build_dep_projection` / `FromScope`
    /// produce line up with `synth_req_names` (also direct). A transitive
    /// spec reached through a direct require is located by
    /// `find_requires_location` instead.
    pub fn set_enclosing_sort(&mut self, kb: &mut KnowledgeBase, sort: Option<Symbol>) {
        self.enclosing = sort.map(|s| EnclosingSort {
            sort: s,
            requires: direct_requires_chain(kb, s),
        });
    }

    pub fn enclosing_sort(&self) -> Option<Symbol> {
        self.enclosing.as_ref().map(|e| e.sort)
    }

    fn enclosing_requires(&self) -> Option<&[RequiresEntry]> {
        self.enclosing.as_ref().map(|e| e.requires.as_slice())
    }

    pub fn bind_var(&mut self, name: Symbol, ty: Value) {
        self.var_bindings.insert(name, ty);
    }

    pub fn lookup_var(&self, name: Symbol) -> Option<Value> {
        self.var_bindings.get(&name).cloned()
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
    /// node that no `[simp]` rule rewrites this is the input occurrence
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
        Self { ty: Value::Term(ty), env, effects: Vec::new(), node }
    }

    /// Pure result whose type is already carrier-agnostic (`Value`) — e.g. a
    /// var-ref whose bound type came from the `Value`-carried env (WI-341 Stage
    /// A). A `Value::Node` (denoted-bearing callback arrow) flows through
    /// unchanged.
    pub fn pure_value(ty: Value, env: TypingEnv, node: Rc<NodeOccurrence>) -> Self {
        Self { ty, env, effects: Vec::new(), node }
    }
}

/// Filter effects: keep only external effects (on non-local resources).
/// Effects on let-bound resources are local and don't propagate.
pub(crate) fn external_effects(kb: &KnowledgeBase, env: &TypingEnv, effects: &[Value]) -> Vec<Value> {
    effects.iter().filter(|effect| {
        // An effect like Modify[store] — check if 'store' is a local resource
        // Effect terms are sort_ref or parameterized. Extract the resource symbol.
        match extract_effect_resource_sym(kb, effect) {
            Some(sym) => !env.is_local_resource(sym),
            None => true, // can't determine resource — assume external
        }
    }).cloned().collect()
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
    bindings.iter().find_map(|(_, v)| effect_binding_resource(kb, v))
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
fn value_to_type_child(kb: &mut KnowledgeBase, v: &Value) -> TypeChild {
    match v {
        Value::Term(t) => TypeChild::Ground(*t),
        Value::Node(occ) => TypeChild::Node(Rc::clone(occ)),
        other => {
            // A scalar/`Var`/`Entity` is a typer bug here (types are `Term`/`Node`);
            // mint a fresh `?ungrounded` type var so we don't panic in release.
            debug_assert!(false, "WI-342: non-type Value in a TypeChild slot: {other:?}");
            let sym = kb.intern("?ungrounded");
            TypeChild::Ground(kb.make_type_var(sym))
        }
    }
}

/// WI-342: build `parameterized(base, bindings)` carrier-agnostically. When any
/// binding value is a `Value::Node` (e.g. a `List` whose element type is a
/// lambda-arrow carrying `Modify[c]`), mint a `Value::Node` via
/// [`KnowledgeBase::make_parameterized_occ`] so the poisoned child is CARRIED,
/// not re-grounded; otherwise the hash-consed [`KnowledgeBase::make_parameterized_type`].
/// `base` is the ground `sort_ref` (`List`/`Set`/…); `span`/`owner` stamp the new
/// occurrence when Node-carried.
fn parameterized_value(
    kb: &mut KnowledgeBase,
    base: TermId,
    bindings: &[(Symbol, Value)],
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    if bindings.iter().any(|(_, v)| matches!(v, Value::Node(_))) {
        let mut children: Vec<(Symbol, TypeChild)> = Vec::with_capacity(bindings.len());
        for (s, v) in bindings {
            children.push((*s, value_to_type_child(kb, v)));
        }
        Value::Node(kb.make_parameterized_occ(TypeChild::Ground(base), children, span, owner))
    } else {
        // Ground branch: no binding is a `Value::Node` (checked above), so every
        // value is a `Value::Term` — unwrap it directly for the hash-consed builder.
        let mut terms: Vec<(Symbol, TermId)> = Vec::with_capacity(bindings.len());
        for (s, v) in bindings {
            terms.push((*s, v.as_term().expect("parameterized_value ground branch: Term binding")));
        }
        Value::Term(kb.make_parameterized_type(base, &terms))
    }
}

/// WI-342: build `named_tuple(fields)` carrier-agnostically. When any field type
/// is a `Value::Node` (e.g. a tuple element that is a lambda carrying `Modify[c]`),
/// mint a `Value::Node` via [`KnowledgeBase::make_named_tuple_occ`] — whose `fields`
/// is the WI-361 `Value`-carried `List[TypeField]` mirroring the term form — so the
/// poisoned field is CARRIED, not re-grounded; otherwise the hash-consed
/// [`KnowledgeBase::make_named_tuple_type`]. `TermView` reads both carriers alike.
fn named_tuple_value(
    kb: &mut KnowledgeBase,
    fields: &[(Symbol, Value)],
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    if fields.iter().any(|(_, v)| matches!(v, Value::Node(_))) {
        let mut children: Vec<(Symbol, TypeChild)> = Vec::with_capacity(fields.len());
        for (s, v) in fields {
            children.push((*s, value_to_type_child(kb, v)));
        }
        Value::Node(kb.make_named_tuple_occ(children, span, owner))
    } else {
        // Ground branch: no field is a `Value::Node` (checked above), so every
        // value is a `Value::Term` — unwrap it directly for the hash-consed builder.
        let mut terms: Vec<(Symbol, TermId)> = Vec::with_capacity(fields.len());
        for (s, v) in fields {
            terms.push((*s, v.as_term().expect("named_tuple_value ground branch: Term field")));
        }
        Value::Term(kb.make_named_tuple_type(&terms))
    }
}

/// WI-342: build an `arrow(param, result, effects)` type carrier-agnostically.
/// When any of `param` / `result` / an effect label is a `Value::Node`
/// (denoted-bearing — e.g. a lambda body effect `Modify[c]`), mint a `Value::Node`
/// arrow occurrence so the poisoned child is CARRIED, not re-grounded; the
/// op-boundary return check then compares it cross-carrier (`arrow_compatible_view`
/// + `subtype_effect_rows`). When everything is ground, build the hash-consed
/// `make_arrow_type` (its children are then provably `Value::Term`, unwrapped via
/// `as_term`). Label order is not load-bearing — row unify/subtype compare label
/// sets. `span`/`owner` stamp a Node-carried occurrence.
fn make_arrow_value(
    kb: &mut KnowledgeBase,
    param: &Value,
    result: &Value,
    effects: &[Value],
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    let poisoned = matches!(param, Value::Node(_))
        || matches!(result, Value::Node(_))
        || effects.iter().any(|e| matches!(e, Value::Node(_)));
    if poisoned {
        let mut row = kb.make_empty_row_occ(span, owner);
        for label in effects.iter().rev() {
            let label_child = value_to_type_child(kb, label);
            let present = kb.make_present_occ(label_child, span, owner);
            row = kb.make_merge_occ(TypeChild::Node(present), TypeChild::Node(row), span, owner);
        }
        let effects_child =
            TypeChild::Node(kb.make_effects_rows_occ(TypeChild::Node(row), span, owner));
        let param_child = value_to_type_child(kb, param);
        let result_child = value_to_type_child(kb, result);
        let arrow = kb.make_arrow_occ(param_child, result_child, effects_child, span, owner);
        Value::Node(arrow)
    } else {
        let p = param.as_term().expect("make_arrow_value: ground param");
        let r = result.as_term().expect("make_arrow_value: ground result");
        let effect_tids: Vec<TermId> = effects
            .iter()
            .map(|e| e.as_term().expect("make_arrow_value: ground effect"))
            .collect();
        Value::Term(kb.make_arrow_type(p, r, &effect_tids))
    }
}

/// Merge two effect lists (set union). WI-342 effects-vertical: dedup
/// carrier-agnostically via [`Value::structural_eq`] — ground labels compare by
/// `TermId` (its `scalar_eq` fallback), and a `Value::Node` label (now live —
/// `Modify[c]`) compares by occurrence structure rather than never-dedup. Set
/// semantics thus hold for both carriers at the merge point, not only after the
/// row canonicalizer.
fn merge_effects(a: &[Value], b: &[Value]) -> Vec<Value> {
    let mut result = a.to_vec();
    for e in b {
        if !result.iter().any(|r| r.structural_eq(e)) {
            result.push(e.clone());
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

/// WI-342 effects-vertical: param-name `Ref` substitution over a carrier-agnostic
/// effect label. A ground (`Value::Term`) label rewrites via [`substitute_ref_syms`];
/// a `Value::Node` label needs occurrence-level `Ref` rewrite — deferred to E2
/// (no Node effect label is minted pre-E2, so it is currently unreachable).
fn substitute_ref_syms_value(
    kb: &mut KnowledgeBase,
    e: &Value,
    map: &HashMap<Symbol, Symbol>,
) -> Value {
    match e {
        Value::Term(t) => Value::Term(substitute_ref_syms(kb, *t, map)),
        // WI-342 E2: re-key the `Ref` spine of a `Value::Node` label (a callee's
        // `Modify[c]` → the caller's `Modify[s]`) via the occurrence rewriter.
        Value::Node(occ) => {
            Value::Node(super::node_occurrence::substitute_ref_syms_occ(occ, map))
        }
        other => other.clone(),
    }
}

/// WI-342 effects-vertical: deep type-var resolution over a carrier-agnostic
/// effect label. Ground labels resolve via [`walk_type_deep`]; a live
/// `Value::Node` label (`Modify[c]`) carries its resource as an `Expr::Ref`, not
/// a type variable, so there is nothing to resolve and it is returned as-is —
/// correct, not merely deferred. (A future Node label that nests an unresolved
/// type-var in a binding would need an occurrence walk here; none is minted.)
fn walk_type_deep_value(kb: &mut KnowledgeBase, subst: &Substitution, e: &Value) -> Value {
    match e {
        Value::Term(t) => Value::Term(walk_type_deep(kb, subst, *t)),
        other => other.clone(),
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
fn walk_type_value(kb: &KnowledgeBase, subst: &Substitution, ty: &Value) -> Value {
    match ty {
        Value::Term(t) => {
            // A field type that is itself a type-param var resolves through the
            // subst's `Value` binding, which may be a `Value::Node` (carried, not
            // re-grounded). A non-var / unbound term falls to the TermId walk.
            if let Term::Var(Var::Global(vid)) = kb.get_term(*t) {
                if let Some(bound) = subst.resolve_as_value(*vid) {
                    return walk_type_value(kb, subst, &bound.clone());
                }
            }
            Value::Term(walk_type(kb, subst, *t))
        }
        other => other.clone(),
    }
}

// ── Helpers ────────────────────────────────────────────────────

/// WI-342 effects-vertical: display name of a carrier-agnostic effect label.
/// A ground label uses [`type_display_name`]; a `Value::Node` label renders via
/// its [`TermView`] functor (adequate for the effect-name comparison; full
/// occurrence pretty-printing is out of scope).
fn type_display_name_value(kb: &KnowledgeBase, v: &Value) -> String {
    match v {
        Value::Term(t) => type_display_name(kb, *t),
        // WI-342 E2: render a `Value::Node` label to the SAME string
        // `type_display_name` produces for the equivalent term (see
        // [`type_display_name_occ`]) — the op-boundary check compares declared
        // vs. actual labels by name across carriers, so the two must agree.
        Value::Node(occ) => type_display_name_occ(kb, occ),
        other => match resolved_functor_name(kb, other) {
            Some(name) => name.to_string(),
            None => "?".to_string(),
        },
    }
}

/// Render a `Value::Node` `Type` / `EffectExpression` effect-label occurrence to
/// the SAME string [`type_display_name`] produces for the equivalent hash-consed
/// term. Carrier-paired with that function arm-for-arm (a `denoted` shows its
/// carried value; `parameterized` shows `base[p = v, …]`; `effects_rows` shows
/// `{…}`) so a declared label and a structurally-equal actual label compare
/// equal regardless of which carrier each rode in on.
fn type_display_name_occ(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> String {
    match &occ.kind {
        NodeKind::Type(TypeNode::Denoted { value }) => match &value.kind {
            NodeKind::Expr { expr: Expr::Ref(s), .. } => kb.resolve_sym(*s).to_string(),
            _ => "?".to_string(),
        },
        NodeKind::Type(TypeNode::Parameterized { base, bindings }) => {
            let base_name = type_child_display_name(kb, base);
            if bindings.is_empty() {
                base_name
            } else {
                let params: Vec<String> = bindings
                    .iter()
                    .map(|(p, c)| format!("{} = {}", kb.resolve_sym(*p), type_child_display_name(kb, c)))
                    .collect();
                format!("{}[{}]", base_name, params.join(", "))
            }
        }
        NodeKind::Type(TypeNode::EffectsRows { effects_expr }) => {
            format!("{{{}}}", type_child_display_name(kb, effects_expr))
        }
        NodeKind::Type(TypeNode::Arrow { param, result, .. }) => format!(
            "{} -> {}",
            type_child_display_name(kb, param),
            type_child_display_name(kb, result)
        ),
        // Mirrors `type_display_name`'s `named_tuple` arm: `(f: T, n: U)`. WI-361:
        // decode the `Value`-carried `List[TypeField]` and display each field type.
        NodeKind::Type(TypeNode::NamedTuple { fields }) => {
            let parts: Vec<String> = list_records_to_pairs(kb, fields, "name", "type")
                .into_iter()
                .map(|(n, v)| format!("{}: {}", kb.resolve_sym(n), type_display_name_value(kb, &v)))
                .collect();
            format!("({})", parts.join(", "))
        }
        NodeKind::EffectExpr(EffectExprNode::Present { label })
        | NodeKind::EffectExpr(EffectExprNode::Absent { label }) => {
            type_child_display_name(kb, label)
        }
        NodeKind::EffectExpr(EffectExprNode::Merge { left, right }) => format!(
            "{}, {}",
            type_child_display_name(kb, left),
            type_child_display_name(kb, right)
        ),
        NodeKind::EffectExpr(EffectExprNode::Open { tail }) => type_child_display_name(kb, tail),
        NodeKind::EffectExpr(EffectExprNode::EmptyRow) => String::new(),
        _ => "?".to_string(),
    }
}

/// Display name of a [`TypeChild`]: ground via [`type_display_name`], poisoned
/// via [`type_display_name_occ`].
fn type_child_display_name(kb: &KnowledgeBase, child: &TypeChild) -> String {
    match child {
        TypeChild::Ground(t) => type_display_name(kb, *t),
        TypeChild::Node(n) => type_display_name_occ(kb, n),
    }
}

pub fn type_display_name(kb: &KnowledgeBase, ty: TermId) -> String {
    match kb.get_term(ty) {
        Term::Fn { functor, named_args, .. } => {
            let fname = kb.resolve_sym(*functor);
            // WI-361: a bare sort is `Term::Ref(S)` (the `Term::Ref` arm below),
            // and a parameterized type is `Fn{S, named}` whose functor is the base
            // sort — handled by the generic `_` arm (renders `S[p = v, …]`). The
            // remaining structural forms are the `TypeExtractor.*` entities.
            match fname {
                "Arrow" => {
                    // Arrow(param, result, effects) — WI-307/WI-331: `effects` is
                    // a singular `EffectsRows(EffectExpression)` Type, not a
                    // legacy `List[Type]`.
                    let p = get_named_arg(kb, named_args, "param")
                        .map(|t| type_display_name(kb, t))
                        .unwrap_or_else(|| "?".to_string());
                    let r = get_named_arg(kb, named_args, "result")
                        .map(|t| type_display_name(kb, t))
                        .unwrap_or_else(|| "?".to_string());
                    format!("{} -> {}", p, r)
                }
                "TypeVar" => {
                    extract_ref_field(kb, named_args, "name")
                        .map(|s| format!("?{}", kb.resolve_sym(s)))
                        .unwrap_or_else(|| "?".to_string())
                }
                "NamedTuple" => {
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
                "Nothing" => "nothing".to_string(),
                "Denoted" => {
                    // WI-302: value-in-type — render the carried value directly
                    // (`Modify[c]` shows `c`, not `denoted[value = c]`).
                    get_named_arg(kb, named_args, "value")
                        .map(|v| type_display_name(kb, v))
                        .unwrap_or_else(|| "?".to_string())
                }
                "EffectsRows" => {
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
        expected: Option<Value>,
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
    expected: Option<Value>,
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
        expected: Option<Value>,
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
        expected: Option<Value>,
        /// WI-283: fire-fuel — see [`TypeBuildFrame::Apply::fuel`].
        fuel: usize,
    },
    /// WI-279: all DotApply children finished (drain order
    /// `[receiver, ...pos, ...named]`). Resolve `member` against the
    /// receiver's least sort (`min_sort`, read from the receiver child's
    /// result type), then synthesize the dispatched `Apply` and re-`Visit`
    /// it — so the produced call rides normal Apply typing + type-param
    /// inference + req_insertion. `pos_count` / `named_keys` size the drain
    /// and rebuild the synthesized call's args from the (typed) child nodes.
    /// No match ⇒ a `DotDispatchNoMatch` diagnostic at the dot span.
    DotApply {
        occ: Rc<NodeOccurrence>,
        member: Symbol,
        pos_count: usize,
        named_keys: Vec<Symbol>,
        env: Rc<TypingEnv>,
        expected: Option<Value>,
        /// WI-283: fire-fuel inherited from this node's `Visit`; spent
        /// (`fuel - 1`) on the re-`Visit` of the synthesized call.
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
        annotation: Option<Value>,
        body_occ: Rc<NodeOccurrence>,
        body_expected: Option<Value>,
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
        value_effects: Vec<Value>,
    },
    /// Scrutinee finished; walk the branch patterns for coverage,
    /// compute each branch's env, schedule body Visits + a
    /// `MatchFinal` frame. `body_expected` flows to every branch body.
    MatchAfterScrutinee {
        occ: Rc<NodeOccurrence>,
        branches: Vec<MatchBranch>,
        outer_env: Rc<TypingEnv>,
        body_expected: Option<Value>,
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
        scr_effects: Vec<Value>,
        branch_envs: Vec<Rc<TypingEnv>>,
        branch_count: usize,
        outer_env: Rc<TypingEnv>,
        /// WI-342: the scrutinee type, carrier-agnostic (`Value`) — read for
        /// the exhaustiveness sort lookup below via [`TermView`].
        scr_ty: Option<Value>,
        covered_entities: Vec<Symbol>,
        has_wildcard: bool,
        /// WI-287: the match's own expected type (the parent's hint).
        /// `Some` ⇒ checked mode (every branch must conform); `None` ⇒
        /// synthesis mode (result is the join — a common supertype — of
        /// the branch types).
        body_expected: Option<Value>,
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
    LambdaBody { occ: Rc<NodeOccurrence>, param_type: Value, outer_env: Rc<TypingEnv> },
    /// WI-285: all three If sub-expressions finished (drained in
    /// `[condition, then, else]` order); merge their effects and return
    /// the if's `TypeResult`. WI-287: the type is the join of the then /
    /// else branch types (checked against `expected` when present), not
    /// just the then-branch type. Replaces the recursive-helper arm so a
    /// deep else-if chain stays on the heap.
    IfExpr { occ: Rc<NodeOccurrence>, env: Rc<TypingEnv>, expected: Option<Value> },
    /// WI-285: all list elements finished; drain `count`, infer the
    /// element type (`element_hint` when bound by an outer
    /// `List[T = X]`, else the first element's type), build
    /// `List[T = elem]` (former `check_list_literal`).
    ListLit { occ: Rc<NodeOccurrence>, env: Rc<TypingEnv>, element_hint: Option<Value>, count: usize },
    /// WI-285: as [`TypeBuildFrame::ListLit`], for `Set[T = elem]`.
    SetLit { occ: Rc<NodeOccurrence>, env: Rc<TypingEnv>, element_hint: Option<Value>, count: usize },
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
    expected: Option<Value>,
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
    expected: Option<Value>,
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
        return Ok(TypeResult::pure_value(ty, env.clone(), Rc::clone(occ)));
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

/// Resolve a binding by short (last-segment) name against an env's var
/// bindings. WI-279: a value-receiver `?x` interns to a plain symbol, while
/// a parameter is bound under a scope-qualified symbol — an exact
/// `lookup_var` then misses, so a `?x` naming a param resolves here by short
/// name. Within one operation body short names are unique, so the match is
/// unambiguous. Returns the first binding whose key's short name equals
/// `short_name_of(var_sym)`.
fn lookup_binding_by_short_name(
    kb: &KnowledgeBase,
    env: &TypingEnv,
    var_sym: Symbol,
) -> Option<Value> {
    // `resolve_sym` borrows `kb` immutably; the closure re-borrows it the same
    // way, so `target` and each key's name coexist as shared borrows (no clone).
    let target = short_name_of(kb.resolve_sym(var_sym));
    env.var_bindings
        .iter()
        .find(|(s, _)| short_name_of(kb.resolve_sym(**s)) == target)
        .map(|(_, t)| t.clone())
}

// ── WI-279 INC2: sort-specific `[simp]` dot-rule override ────────────────
//
// A dot rule like `dot_apply(?e, map, ?f) = either_map(?e, ?f) [simp]`
// (declared in a sort) OVERRIDES the default method fallback for receivers
// whose least sort conforms to that sort. A written dot rule LOADS as the
// reflect `Expr.dot_apply` ENTITY (`receiver:` / `name:` / `args:
// List[ApplyArg]`) — a different shape than a surface occurrence's
// `Expr::DotApply` (flattened `pos_args`, `name` as a Symbol field). Rather
// than teach the generic matcher both shapes, this dedicated path scans the
// `[simp]` dot equations, guards by the rule's enclosing sort (`rule_domain`),
// matches the entity LHS against the occurrence's receiver/args, and
// instantiates the RHS — reusing `simp_rewrite`'s opener + RHS builder. It
// handles a *var* receiver with *positional var* args (the Either-style
// case); a name mismatch, a non-var pattern, a named-arg dot call, or an arity
// mismatch makes it skip the rule, falling through to the default.

/// Fire a sort-specific `[simp]` dot rule at a DotApply, or `None` to fall to
/// the default. `recv_sort` is the receiver's least sort (the firing guard's
/// key); `from` is the DotApply occ (synthesized-RHS provenance).
fn try_fire_dot_rule(
    kb: &mut KnowledgeBase,
    recv_sort: Symbol,
    member: Symbol,
    receiver: &Rc<NodeOccurrence>,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    from: &Rc<NodeOccurrence>,
) -> Option<Rc<NodeOccurrence>> {
    let dot_apply_sym = kb.try_resolve_symbol("anthill.reflect.Expr.dot_apply")?;
    let eq_sym = kb.eq_functor();
    for rid in kb.rules_by_functor(eq_sym) {
        if !kb.is_equation(rid)
            || !super::load::meta_has_flag(kb, kb.rule_meta(rid), "simp")
            || super::simp_rewrite::stored_lhs_functor(kb, rid) != Some(dot_apply_sym)
        {
            continue;
        }
        // Enclosing-sort guard: a dot rule fires only where the receiver's
        // least sort conforms to the rule's defining sort — by identity or spec
        // satisfaction. `rule_domain` is the *sort term* (a nullary `Fn` / `Ref`
        // whose functor IS the sort), so read the functor directly;
        // `sort_functor_of` is for `sort_ref`-wrapped *type* terms and returns
        // `None` on a bare sort term. Without this guard one sort's `map` rule
        // would hijack the member name for every receiver (unsound).
        let encl = match kb.get_term(kb.rule_domain(rid)) {
            Term::Fn { functor, .. } => *functor,
            Term::Ref(s) => *s,
            _ => continue,
        };
        // `same_symbol` (not raw `==`): a sort can carry distinct Symbol ids
        // (bare-interned vs fully-qualified) — match the convention used by
        // `sort_provides` / sort widening. Identity OR spec satisfaction.
        if !same_symbol(kb, recv_sort, encl) && !sort_provides(kb, recv_sort, encl) {
            continue;
        }
        let Some((lhs, rhs)) = super::simp_rewrite::open_equation(kb, rid) else { continue };
        if let Some(subst) = match_dot_rule_lhs(kb, lhs, member, receiver, pos_args, named_args) {
            let pass = super::simp_rewrite::simp_pass(kb);
            return Some(super::simp_rewrite::substitute_to_occurrence(kb, rhs, &subst, from, pass));
        }
    }
    None
}

/// WI-281: spec-satisfaction method resolution. When `member` is not declared
/// directly on the receiver's sort, look for it on a spec the receiver's sort
/// *provides* (`fact Spec[Carrier = recv_sort]`): e.g. `(3).min(5)` resolves
/// `min` to `Ordered.min` because `Int` provides `Ordered`. Returns the spec
/// operation's fully-qualified symbol; the caller synthesizes the same
/// `Apply(op, [receiver, ...args])` as the direct-sort case, so the produced
/// call rides the normal spec-op dispatch + `req_insertion` — the requirement
/// (`Ordered[Int]`) is threaded by that machinery, not re-implemented here.
///
/// Walks `SortProvidesInfo` for the specs `recv_sort` provides (mirroring
/// `build_sort_ops_table`'s pass-2 snapshot) and resolves `member` within each
/// spec's scope via `find_operation_in_scope`. First match wins (a member name
/// shared across two provided specs is left for a later disambiguation pass).
fn find_spec_op_for_provided_sort(
    kb: &mut KnowledgeBase,
    recv_sort: Symbol,
    short: &str,
) -> Option<Symbol> {
    let provides_sym = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo")?;
    // Snapshot the provided specs first: the resolution loop below mutates `kb`
    // (`alloc` / `find_operation_in_scope`), so it can't run while iterating.
    let mut spec_syms: Vec<Symbol> = Vec::new();
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        // A value-fact SortProvidesInfo (denoted-bearing spec) carries no spec
        // base via the term-only path; occurrence dispatch is gated effect-
        // expressions-as-types work, so skip rather than panic on a value head.
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &named, "sort_ref") else { continue };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else { continue };
        // `same_symbol`, not `==`: a sort carries distinct Symbol ids
        // (bare-interned vs fully-qualified) — match `try_fire_dot_rule`.
        if !same_symbol(kb, carrier, recv_sort) {
            continue;
        }
        let Some(spec_t) = get_named_arg(kb, &named, "spec") else { continue };
        if let Some(spec_sym) = super::load::provides_spec_base_sym(kb, spec_t) {
            spec_syms.push(spec_sym);
        }
    }
    for spec_sym in spec_syms {
        let spec_term = kb.alloc(Term::Ref(spec_sym));
        if let Some(op) = super::load::find_operation_in_scope(kb, spec_term, short) {
            return Some(op);
        }
    }
    None
}

/// Match a reflect `dot_apply(receiver:, name:, args:List[ApplyArg])` rule LHS
/// against a DotApply occurrence's parts, binding the LHS's logical vars to the
/// (typed) receiver / arg occurrences. Handles a *var* receiver and *positional
/// var* args; returns `None` (skip → default) for a name mismatch, a non-var
/// pattern, a named-arg dot call, or an arity mismatch.
fn match_dot_rule_lhs(
    kb: &KnowledgeBase,
    lhs: TermId,
    member: Symbol,
    receiver: &Rc<NodeOccurrence>,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<Substitution> {
    if !named_args.is_empty() {
        return None; // named-arg dot calls: follow-up
    }
    let la = match kb.get_term(lhs) {
        Term::Fn { named_args, .. } => named_args.clone(),
        _ => return None,
    };
    let r_pat = get_named_arg(kb, &la, "receiver")?;
    let name_t = get_named_arg(kb, &la, "name")?;
    let args_t = get_named_arg(kb, &la, "args")?;
    // Member name — compared by short name, robust to interning differences
    // between the rule's `name:` field and the occurrence's member symbol.
    let rule_name = dot_member_sym(kb, name_t)?;
    if short_name_of(kb.resolve_sym(rule_name)) != short_name_of(kb.resolve_sym(member)) {
        return None;
    }
    let val_pats = collect_positional_arg_value_pats(kb, args_t)?;
    if val_pats.len() != pos_args.len() {
        return None;
    }
    let mut subst = Substitution::new();
    bind_var_pattern_to_node(&mut subst, kb, r_pat, receiver)?;
    for (pat, occ) in val_pats.iter().zip(pos_args.iter()) {
        bind_var_pattern_to_node(&mut subst, kb, *pat, occ)?;
    }
    // A non-linear LHS (a var repeated across receiver/args) implies an
    // equality constraint: `bind_value` flags a contradiction when the same
    // var is bound to two structurally-distinct occurrences. Honour it (the
    // generic `try_fire` does the same) — else the rule would fire unsoundly,
    // dropping the equality the pattern demanded.
    if subst.is_contradiction() {
        return None;
    }
    Some(subst)
}

/// Bind a logical-var pattern term to an occurrence as a `Value::Node` (so the
/// RHS builder substitutes the typed occurrence in). `None` for a non-var
/// pattern — the caller then skips the rule (constructor-pattern receivers are
/// a follow-up).
fn bind_var_pattern_to_node(
    subst: &mut Substitution,
    kb: &KnowledgeBase,
    pat: TermId,
    occ: &Rc<NodeOccurrence>,
) -> Option<()> {
    match kb.get_term(pat) {
        Term::Var(Var::Global(vid)) => {
            subst.bind_value(*vid, Value::Node(Rc::clone(occ)));
            Some(())
        }
        _ => None,
    }
}

/// The member symbol of a dot rule's `name:` field (a `Ref` / `Ident`, or a
/// nullary `Fn` functor).
fn dot_member_sym(kb: &KnowledgeBase, t: TermId) -> Option<Symbol> {
    match kb.get_term(t) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            Some(*functor)
        }
        _ => None,
    }
}

/// Collect a dot rule's positional arg value-patterns from its reflect
/// `args: List[ApplyArg]` field (`cons(head: ApplyArg(name: none, value: pat),
/// tail: …)` … `nil`). `None` (→ rule skipped) if the list is malformed or any
/// ApplyArg is named (`name: some(…)`) — named dot-rule args are a follow-up.
fn collect_positional_arg_value_pats(kb: &KnowledgeBase, args_t: TermId) -> Option<Vec<TermId>> {
    let mut out = Vec::new();
    // `list_to_vec` walks the `cons(head, tail) … nil` spine; each element is an
    // `ApplyArg(name: <none/some>, value: <pat>)`.
    for elem in list_to_vec(kb, args_t) {
        let aargs = match kb.get_term(elem) {
            Term::Fn { functor, named_args, .. }
                if short_name_of(kb.resolve_sym(*functor)) == "ApplyArg" =>
            {
                named_args.clone()
            }
            _ => return None,
        };
        // Positional only: `name` must be `none()` (a named arg is `some(...)`).
        let name_t = get_named_arg(kb, &aargs, "name")?;
        let name_functor = match kb.get_term(name_t) {
            Term::Fn { functor, .. } => *functor,
            _ => return None,
        };
        if short_name_of(kb.resolve_sym(name_functor)) != "none" {
            return None; // named arg → follow-up
        }
        out.push(get_named_arg(kb, &aargs, "value")?);
    }
    Some(out)
}

/// Dispatch a single Visit: produce a leaf TypeResult directly,
/// delegate to a recursive helper, or push a Build frame + child
/// Visits for the env-changing Let / Match / Lambda cases.
fn visit_type(
    kb: &mut KnowledgeBase,
    occ: Rc<NodeOccurrence>,
    env: Rc<TypingEnv>,
    expected: Option<Value>,
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
        NodeKind::RuleHead { .. } | NodeKind::Pattern(_)
        | NodeKind::Type(_) | NodeKind::EffectExpr(_) => {
            // RuleHead never appears in op/rule body position; Pattern
            // is reached via its parent Expr's pattern slot and handled
            // there, not as a typing target on its own (WI-318).
            // WI-342: Type/EffectExpr occurrences are type-level data,
            // not an expression typing target.
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
            let annotation = type_annotation.clone();
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
                annotation: annotation.clone(),
                body_occ,
                body_expected: expected,
                fuel,
            }));
            // WI-342 S4a: the let-annotation is a carrier-agnostic `Value` and IS
            // the value's expected type (WI-270) — thread it directly.
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
            // WI-342: the param type is carrier-agnostic (`Value`) — the env binds
            // it directly, and `LambdaBody` builds the arrow's param slot from it
            // (a `Value::Node` denoted-bearing param is carried, not re-grounded).
            let param_type: Value = extract_pattern_type_ann(kb, param)
                .map(Value::Term)
                .or_else(|| {
                    // Checking direction: the expected arrow's param slot, as-is.
                    expected.as_ref().and_then(|exp| extract_function_param_type(kb, exp))
                })
                .unwrap_or_else(|| {
                    let fresh = kb.intern("?param");
                    Value::Term(kb.make_type_var(fresh))
                });
            let mut lambda_env = (*env).clone();
            extend_env_from_pattern(kb, &mut lambda_env, param, Some(param_type.clone()));
            // WI-270: if expected is `arrow(param, result, effects)`,
            // decompose and pass `result` to the body. Mismatching
            // shapes (or `None`) leave the body without a hint. WI-342 S3a: the
            // body's expected hint is a carrier-agnostic `Value` — no re-ground.
            let body_expected = expected.as_ref().and_then(|exp| {
                extract_function_type_parts(kb, exp).map(|(ret, _)| ret)
            });
            work.push(TypeWorkOp::Build(TypeBuildFrame::LambdaBody {
                occ: Rc::clone(&occ),
                param_type,
                outer_env: env,
            }));
            push_visit(work, body_occ, Rc::new(lambda_env), body_expected, fuel);
        }

        // ── Leaf cases ──────────────────────────────────────────
        Expr::Const(Literal::Int(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("Int"), unwrap_env(env), Rc::clone(&occ)),
        )),
        // A `BigInt` literal is one that exceeded `i64` at parse — it cannot be
        // an `Int` value, so it types as `BigInt`. (Previously lumped with
        // `Int`; the WI-379 args-before-expected order made that mis-typing
        // visible — `100…0 + 100…0` declared `-> BigInt` pinned `Numeric.T` to
        // the literal's type from the argument, so a literal typed `Int` made
        // the sum `Int`, rejected against the `BigInt` return.)
        Expr::Const(Literal::BigInt(_)) => results.push(Ok(
            TypeResult::pure(kb.make_sort_ref_by_name("BigInt"), unwrap_env(env), Rc::clone(&occ)),
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
            work.push(TypeWorkOp::Build(TypeBuildFrame::IfExpr { occ: Rc::clone(&occ), env: Rc::clone(&env), expected: expected.clone() }));
            push_visit(work, else_branch, Rc::clone(&env), expected.clone(), fuel);
            push_visit(work, then_branch, Rc::clone(&env), expected, fuel);
            push_visit_no_hint(work, condition, env, fuel);
        }
        Expr::ListLit(elems) => {
            let elems = elems.clone();
            // WI-270: an outer `List[T = X]` makes X each element's
            // expected, and the empty-list fallback.
            let element_hint = expected.as_ref().and_then(|exp| extract_type_param(kb, exp, "T"));
            work.push(TypeWorkOp::Build(TypeBuildFrame::ListLit {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env),
                element_hint: element_hint.clone(),
                count: elems.len(),
            }));
            for e in elems.iter().rev() {
                push_visit(work, Rc::clone(e), Rc::clone(&env), element_hint.clone(), fuel);
            }
        }
        Expr::SetLit(elems) => {
            let elems = elems.clone();
            let element_hint = expected.as_ref().and_then(|exp| extract_type_param(kb, exp, "T"));
            work.push(TypeWorkOp::Build(TypeBuildFrame::SetLit {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env),
                element_hint: element_hint.clone(),
                count: elems.len(),
            }));
            for e in elems.iter().rev() {
                push_visit(work, Rc::clone(e), Rc::clone(&env), element_hint.clone(), fuel);
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

        // A surface `?x` whose name matches an in-scope binding (param /
        // let / lambda / match) *refers to* that binding — the same lookup
        // the `Ident` path does via `check_bare_ref`. WI-279: this is what
        // gives a value-receiver `?x.method()` a concrete type to dispatch
        // on (`?xs: List[Int]` ⇒ `min_sort` = List). Only `Var::Global`
        // carries a name; a genuinely-free `?x` (no matching binding), a
        // `DeBruijn`, or a `Rigid` falls back to a fresh type-var — not a
        // typer-level error, so the surrounding apply / let still
        // type-checks and declared signatures resolve it on the consumer
        // side.
        Expr::Var(var) => {
            // Exact-symbol lookup resolves let/lambda/match-bound `?x` (binder
            // and body var share an intern). A param binds under a
            // scope-qualified symbol while a body `?x` is a plain intern, so an
            // exact match misses — fall back to a short-name match (unique
            // within one body). A genuinely-free `?x` matches neither and gets
            // a fresh type-var.
            let bound = match var {
                Var::Global(vid) => env
                    .lookup_var(vid.name())
                    .or_else(|| lookup_binding_by_short_name(kb, &env, vid.name())),
                _ => None,
            };
            let ty = bound.unwrap_or_else(|| {
                let fresh = kb.intern("?logical_var");
                Value::Term(kb.make_type_var(fresh))
            });
            results.push(Ok(TypeResult::pure_value(ty, unwrap_env(env), Rc::clone(&occ))));
        }

        // WI-279: a value-receiver dot form `?x.member(args)` / `?x.member`.
        // Type the receiver + args (no hint), then a `DotApply` Build frame
        // resolves `member` against the receiver's least sort and synthesizes
        // the dispatched call. Running here (in the typer, env in hand) is what
        // lets a receiver referencing a let/lambda/match-bound local resolve.
        Expr::DotApply { receiver, name, pos_args, named_args } => {
            let member = *name;
            let receiver = Rc::clone(receiver);
            let pos_args = pos_args.clone();
            let named_args = named_args.clone();
            let named_keys: Vec<Symbol> = named_args.iter().map(|(k, _)| *k).collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::DotApply {
                occ: Rc::clone(&occ),
                member,
                pos_count: pos_args.len(),
                named_keys,
                env: Rc::clone(&env),
                expected,
                fuel,
            }));
            // Drain order is `[receiver, ...pos, ...named]` (matches
            // `for_each_child`): push reversed so the receiver pops first.
            for (_, arg) in named_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env), fuel);
            }
            for arg in pos_args.iter().rev() {
                push_visit_no_hint(work, Rc::clone(arg), Rc::clone(&env), fuel);
            }
            push_visit_no_hint(work, receiver, env, fuel);
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
                // WI-342: `inferred_type` is carrier-agnostic — stamp the `ty`
                // directly (a `Value::Node` denoted-bearing type is preserved,
                // not re-grounded). `min_sort` widens it via `sort_functor_of_view`.
                r.node.set_inferred_type(r.ty.clone());
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
        TypeBuildFrame::DotApply { occ, member, pos_count, named_keys, env, expected, fuel } => {
            // Children were drained in `[receiver, ...pos, ...named]` order.
            let total = 1 + pos_count + named_keys.len();
            let drain_start = results.len() - total;
            let child_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            // Surface an ill-typed child first — `Ok` children are needed to
            // read their result `.node` / `.ty`.
            if let Err(e) = collect_arg_errors(child_results.iter()) {
                results.push(Err(e));
                return;
            }
            let recv = child_results[0].as_ref().expect("DotApply: Ok receiver");
            let receiver_node = Rc::clone(&recv.node);
            // `min_sort`: widen the receiver to its least declared sort. Read
            // the child's result type directly (don't depend on the receiver's
            // `Stamp` frame ordering). WI-342: widen the carrier-agnostic `ty`
            // in place — a `Value::Node` receiver type need not be re-grounded.
            let recv_sort = sort_functor_of_view(kb, &recv.ty);
            let dot_span = Some(occ.span.span);
            // The (typed) arg occurrences — used by both the dot-rule override
            // and the default method fallback.
            let pos_nodes: Vec<Rc<NodeOccurrence>> = child_results[1..1 + pos_count]
                .iter()
                .map(|r| Rc::clone(&r.as_ref().expect("DotApply: Ok positional arg").node))
                .collect();
            let named_nodes: Vec<(Symbol, Rc<NodeOccurrence>)> = named_keys
                .iter()
                .zip(&child_results[1 + pos_count..])
                .map(|(k, r)| (*k, Rc::clone(&r.as_ref().expect("DotApply: Ok named arg").node)))
                .collect();

            // INC2: a sort-specific `[simp]` dot rule (declared in the
            // receiver's sort) OVERRIDES the default. Fire it first; only fall
            // to the default fallback when none fires. Gated on remaining
            // fire-fuel (bounds the fire→re-Visit chain, as the Apply/Ctor arms
            // do), `[simp]` rules existing, and a resolved receiver sort (the
            // firing guard's key).
            if fuel > 0 && simp_enabled {
                if let Some(rs) = recv_sort {
                    if let Some(synth) = try_fire_dot_rule(
                        kb, rs, member, &receiver_node, &pos_nodes, &named_nodes, &occ,
                    ) {
                        push_visit(work, synth, env, expected, fuel - 1);
                        return;
                    }
                }
            }

            // DEFAULT method fallback: resolve `member` to an operation declared
            // on the receiver's sort, then synthesize `op(receiver, ...args)` —
            // `x.m(a)` becomes `m(x, a)`. This is engine logic (functor resolved
            // dynamically), not a writable rule.
            // Owned: `kb` is mutated below (alloc / find_operation_in_scope),
            // so the borrowed name can't be held across it.
            let short = short_name_of(kb.resolve_sym(member)).to_string();
            let op_sym = recv_sort.and_then(|s| {
                // `find_operation_in_scope` reads the sort symbol from a bare
                // `Ref(sort)` / `sort(args)` head — not the `sort_ref(name:…)`
                // wrapper `make_sort_ref` builds (whose functor is `sort_ref`).
                let sort_term = kb.alloc(Term::Ref(s));
                super::load::find_operation_in_scope(kb, sort_term, &short)
                    // WI-281: spec-satisfaction fallback — `member` may be an
                    // operation on a spec `s` *provides* (e.g. `(3).min(5)` →
                    // `Ordered.min` via `fact Ordered[Int]`), not declared on
                    // `s` itself. The synthesized `Apply` below is identical;
                    // re-typing it rides the normal spec-op dispatch +
                    // `req_insertion`, which threads the requirement.
                    .or_else(|| find_spec_op_for_provided_sort(kb, s, &short))
            });
            if let Some(op_sym) = op_sym {
                let mut synth_pos: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(1 + pos_count);
                synth_pos.push(receiver_node);
                synth_pos.extend(pos_nodes);
                let pass = super::simp_rewrite::simp_pass(kb);
                let synth = NodeOccurrence::synthesized_expr(
                    Expr::Apply {
                        functor: op_sym,
                        pos_args: synth_pos,
                        named_args: named_nodes,
                        type_args: Vec::new(),
                    },
                    Rc::clone(&occ),
                    pass,
                    occ.owner,
                );
                // Re-type the synthesized call: it rides normal Apply typing +
                // type-param inference + req_insertion, and its result becomes
                // this DotApply node's result.
                push_visit(work, synth, env, expected, fuel.saturating_sub(1));
                return;
            }

            // No match → clear diagnostic at the dot span. (INC 1b — a zero-arg
            // member resolving to a field on a free-standing-entity receiver —
            // is a follow-up; until then a field dot also lands here.)
            results.push(Err(TypeError::DotDispatchNoMatch {
                span: dot_span,
                member,
                receiver_sort: recv_sort,
            }));
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
            // WI-342: the env binds a carrier-agnostic `Value` — carry the let
            // value's `ty` (and a `Value` annotation) without re-grounding.
            let value_ty = Some(r.ty);
            let (value_effects, mut ext_env) = (r.effects, r.env);
            // WI-379: a let with an explicit annotation must have its value
            // CONFORM to that annotation — the let-binding counterpart of the
            // operation-return check in `check_operation_bodies`. The
            // args-before-expected reorder makes the value's inferred type
            // authoritative, so a contradicting annotation
            // (`let v: List[String] = id_list(ys: List[Int])`) is a real
            // mismatch and must be rejected rather than silently rebinding the
            // value as the annotated type. (When the annotation merely fills a
            // still-free param it was threaded in as `expected` when the value
            // was typed, so `value_ty` already matches and this check passes.)
            if let (Some(ann), Some(vty)) = (annotation.as_ref(), value_ty.as_ref()) {
                let mut subst = Substitution::new();
                if !types_compatible(kb, &mut subst, vty, ann) {
                    let var = extract_pattern_var_name(kb, pattern)
                        .unwrap_or_else(|| kb.intern("_"));
                    results.push(Err(TypeError::TypeMismatch {
                        span: None,
                        context: TypeErrorContext::LetBinding { var },
                        expected: ann.clone(),
                        actual: vty.clone(),
                    }));
                    return;
                }
            }
            // Prefer an explicit annotation (already `Value`, S4a) over the value type.
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
            // WI-342: carry the scrutinee's `ty` as a `Value` — the sort lookup
            // and pattern env binding read it carrier-agnostically (no re-ground).
            let scr_ty = scr_r.as_ref().ok().map(|r| r.ty.clone());
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
                .as_ref()
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
                extend_env_from_pattern(kb, &mut branch_env, pattern_tid, scr_ty.clone());
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
                body_expected: body_expected.clone(),
            }));
            for (branch, env) in branches.iter().zip(visit_envs.into_iter()).rev() {
                push_visit(work, Rc::clone(&branch.body), env, body_expected.clone(), fuel);
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
            // WI-342: branch types are carrier-agnostic `Value`s — a branch may be
            // a `Value::Node` lambda arrow; the join carries it (no re-grounding).
            let mut branch_tys: Vec<(Value, Option<Span>)> =
                Vec::with_capacity(branch_count);
            for (i, body_r) in branch_results.into_iter().enumerate() {
                let body_r = body_r.expect("aggregator");
                branch_tys.push((body_r.ty.clone(), Some(body_r.node.span.span)));
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
            let result_ty: Value = match compute_branch_join_type(kb, &branch_tys, body_expected, "match") {
                Ok(ty) => ty,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };

            let mut result_env = (*outer_env).clone();
            if !has_wildcard {
                if let Some(sty) = scr_ty {
                    if let Some(sort_sym) = extract_sort_ref_sym(kb, &sty) {
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
            let body_ty: Value = body_r.as_ref().ok().map(|r| r.ty.clone()).unwrap_or_else(|| {
                let fresh = kb.intern("?result");
                Value::Term(kb.make_type_var(fresh))
            });
            let body_effects = body_r
                .as_ref()
                .ok()
                .map(|r| r.effects.clone())
                .unwrap_or_default();
            // WI-342: build the arrow carrier-agnostically. When a child (param,
            // result, or a body effect) is carrier-poisoned (a denoted-bearing
            // `Modify[c]` rode in as `Value::Node`), the arrow is minted as a
            // `Value::Node` so the effect is CARRIED on the lambda's type rather
            // than re-grounded; the op-boundary return check compares it
            // cross-carrier. A fully-ground lambda still builds a hash-consed arrow.
            let fn_ty = make_arrow_value(kb, &param_type, &body_ty, &body_effects, occ.span, occ.owner);
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
                    results.push(Ok(TypeResult {
                        ty: fn_ty,
                        env: unwrap_env(outer_env),
                        effects: Vec::new(),
                        node,
                    }))
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
            // WI-342: branch types are carrier-agnostic `Value`s (a branch may be
            // a `Value::Node` lambda arrow); the join carries it (no re-grounding).
            let branch_tys = [
                (then_r.ty.clone(), Some(then_r.node.span.span)),
                (else_r.ty.clone(), Some(else_r.node.span.span)),
            ];
            let ty: Value = match compute_branch_join_type(kb, &branch_tys, expected, "if") {
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
            let (span, owner) = (occ.span, occ.owner);
            let mut effects = Vec::new();
            // WI-342: keep the element type carrier-agnostic so a `Value::Node`
            // element (e.g. a list of effectful lambdas) is CARRIED, not re-grounded.
            let mut element_type: Option<Value> = element_hint;
            for r in group {
                let r = r.expect("aggregator");
                if element_type.is_none() {
                    element_type = Some(r.ty.clone());
                }
                effects = merge_effects(&effects, &r.effects);
            }
            let t_val = element_type.unwrap_or_else(|| {
                let fresh = kb.intern("?T");
                Value::Term(kb.make_type_var(fresh))
            });
            // WI-393: the QUALIFIED sort name. A bare `"List"` interns a symbol
            // whose qualified name is `"List"`, which `canonical_sort_sym` (keyed
            // on qualified name) never folds onto `anthill.prelude.List` — so a
            // list LITERAL consumed as a Stream (`collect([1,2,3])`) failed the
            // carrier provider lookup that a written `List[T]` param passes. The
            // canonical sort makes the literal's carrier match the provider fact.
            let list_base = kb.make_sort_ref_by_name("anthill.prelude.List");
            let t_sym = kb.intern("T");
            let list_type = parameterized_value(kb, list_base, &[(t_sym, t_val)], span, owner);
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
            let (span, owner) = (occ.span, occ.owner);
            let mut effects = Vec::new();
            // WI-342: carrier-agnostic element type (carry a `Value::Node` element).
            let mut element_type: Option<Value> = element_hint;
            for r in group {
                let r = r.expect("aggregator");
                if element_type.is_none() {
                    element_type = Some(r.ty.clone());
                }
                effects = merge_effects(&effects, &r.effects);
            }
            let t_val = element_type.unwrap_or_else(|| {
                let fresh = kb.intern("?T");
                Value::Term(kb.make_type_var(fresh))
            });
            // WI-393: QUALIFIED, like the `ListLit` frame and the `SetLiteral`
            // constructor path — a bare `"Set"` never canonicalizes for the
            // carrier provider lookup. Keeps the two set-literal forms agreeing on
            // the carrier symbol.
            let set_base = kb.make_sort_ref_by_name("anthill.prelude.Set");
            let t_sym = kb.intern("T");
            let set_type = parameterized_value(kb, set_base, &[(t_sym, t_val)], span, owner);
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
            let (span, owner) = (occ.span, occ.owner);
            let mut effects = Vec::new();
            // WI-342: keep field types carrier-agnostic so a `Value::Node` field
            // (a tuple element that is an effectful lambda) is CARRIED, not re-grounded.
            let mut field_types: Vec<(Symbol, Value)> = Vec::new();
            let mut it = group.into_iter();
            for i in 0..pos_count {
                let r = it.next().unwrap().expect("aggregator");
                // WI-355: positional field names are 1-based `_1`, `_2`, … (spec
                // §4.5), matching the type surface (`convert.rs`) and arrow params
                // so `unify_named_tuple` (name-based) unifies a tuple value's type
                // against a tuple-typed / multi-param-arrow param. Eval/patterns
                // treat `_N` positionally, so the base is invisible to them.
                let field_name = kb.intern(&format!("_{}", i + 1));
                field_types.push((field_name, r.ty.clone()));
                effects = merge_effects(&effects, &r.effects);
            }
            for name in named_names {
                let r = it.next().unwrap().expect("aggregator");
                field_types.push((name, r.ty.clone()));
                effects = merge_effects(&effects, &r.effects);
            }
            let tuple_type = named_tuple_value(kb, &field_types, span, owner);
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
    expected: Option<Value>,
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
        // WI-367: a self-receiver spec op consumed on a CONCRETE carrier takes
        // its element type-params from that carrier — the receiver argument is
        // the ground truth for the element. Bind them BEFORE the WI-270
        // expected-seeding below. Otherwise a caller's wrong return claim
        // (`drain(xs: List[Int]) -> List[String] = collect(xs)`) would let
        // `unify_types(op.return_type, expected)` pre-seed `Stream.T := String`,
        // after which the carrier pass (which only fills empty slots) skips and
        // the unsound element survives — `collect` over a `List[Int]` is
        // `List[Int]`, not the caller's `List[String]`. Binding from the carrier
        // first pins `Stream.T := Int`; the expected-seeding `unify_types` then
        // fails silently against the carrier-pinned slot for a differing claim
        // (it binds nothing and its boolean is already discarded) and only fills
        // the still-free params. `resolved_ret` therefore carries the carrier
        // element, and the outer return-type check rejects the differing
        // declared return. `carrier_bound` is reused below to gate the WI-357
        // effect-close, which the early bind would otherwise steal.
        let carrier_bound = match self_receiver_spec_sort(kb, &op, fn_sym) {
            Some(spec_sort) => match receiver_carrier(
                kb, &op, spec_sort, named_args, pos_results, named_results,
            ) {
                ReceiverCarrier::Concrete(carrier_sym) => bind_spec_params_from_carrier(
                    kb, &mut subst, &op, spec_sort, carrier_sym,
                    named_args, pos_results, named_results,
                ),
                _ => false,
            },
            None => false,
        };
        // WI-379: synthesize from the ARGUMENTS first (the two loops below);
        // the caller-side `expected` is consulted only AFTER (moved below the
        // arg loops), so it fills still-free type params without overriding any
        // that an argument pinned.
        let mut arg_effects: Vec<Value> = Vec::new();
        let mut param_to_arg_sym: HashMap<Symbol, Symbol> = HashMap::new();

        for (i, arg_occ) in pos_args.iter().enumerate() {
            if let Some(arg_var_sym) = extract_var_ref_sym_node(arg_occ) {
                if let Some((param_sym, _)) = op.params.get(i) {
                    param_to_arg_sym.insert(*param_sym, arg_var_sym);
                }
            }
            if let Ok(ref arg_result) = pos_results[i] {
                // WI-341 Stage A: the param type is `Value` (`Value::TermView`),
                // unified carrier-agnostically — no `TermIdView` wrap.
                if let Some((_, param_type)) = op.params.get(i) {
                    unify_types(kb, &mut subst, &arg_result.ty, param_type);
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
                    .map(|(_, t)| t)
                {
                    unify_types(kb, &mut subst, &arg_result.ty, param_type);
                }
                arg_effects = merge_effects(&arg_effects, &arg_result.effects);
            }
        }

        // WI-270 / WI-379: now that the arguments have been synthesized,
        // consult the caller-side `expected` type via `op.return_type`. Running
        // it AFTER argument inference (it used to run before) makes it fill only
        // STILL-FREE type params: a param an argument already pinned resists the
        // override — the `unify_types` against the pinned slot fails for a
        // differing claim and its boolean is discarded, binding nothing — so a
        // wrong declared return no longer masks a contradicting argument
        // (WI-379 soundness gap (a)). A genuinely free param
        // (`empty() -> List[Elem]`, `term_as_entity[E] -> Option[E]`) is still
        // filled from `expected` (WI-270's legitimate case). The synthesized
        // `resolved_ret` is then checked against `expected` at the use site
        // (`check_operation_bodies` return check / let conformance), which is
        // what actually rejects the wrong declared return.
        if let Some(exp) = expected {
            unify_types(kb, &mut subst, &op.return_type, &exp);
        }

        // Apply param-name substitution to op.effects (WI-209), then
        // walk each through `walk_type_deep` so type-var bindings from
        // arg-unification propagate into nested positions in the effect
        // (e.g. `Stream.head`'s `effects E` → `Error` once `vid_E` is
        // bound by `unify_parameterized_with_sort_ref`). Skip the
        // param-name walk when no var_ref args were seen.
        let pre_substituted: Vec<Value> = if param_to_arg_sym.is_empty() {
            op.effects.clone()
        } else {
            op.effects
                .iter()
                .map(|e| substitute_ref_syms_value(kb, e, &param_to_arg_sym))
                .collect()
        };
        // Walk each effect through `walk_type_deep` so arg-unification bindings
        // propagate, then FLATTEN any element that resolved to a concrete effect-
        // ROW wrapper. WI-375: `effects E` with E bound to a WRITTEN
        // `effects_rows(…)` — from a producer's `Stream[E = {…}]` return threaded
        // into a bare-`Stream` param by `unify_parameterized_with_sort_ref` —
        // resolves to the row WRAPPER as a single effect element. Decompose it to
        // its present labels (+ open tail) so the effect machinery (propagation,
        // the pure-context check in `check_operation_bodies`, the WI-365 close
        // below) sees flat labels, not the wrapper as one opaque effect (which
        // rendered as a spurious `undeclared effect: {empty_row}`). A bare label
        // (`Modify[c]`) or an unbound row var (the WI-365 concrete-carrier path,
        // closed below) is not an `EffectsRows` head and passes through unchanged.
        let mut substituted_op_effects: Vec<Value> = Vec::new();
        for e in &pre_substituted {
            // Deep-walk to propagate arg-unification bindings into nested effect
            // positions, then `walk_value_to_resolved` to SURFACE a top-level var
            // bound to a `Value::Node` — the term-deep walk stops at non-`Term`
            // bindings (walk_type keeps the var; its doc names `walk_term_to_
            // resolved` as the surfacing helper), so a written row threaded via
            // `bind_value` (WI-375, the `E = {Modify[c]}` path) would otherwise
            // leak as `?_`. The compose keeps the deep walk (for nested term vars)
            // and adds the recursive Node surface (chained var→…→Node bindings).
            let deep = walk_type_deep_value(kb, &subst, e);
            let walked = walk_value_to_resolved(kb, &subst, deep);
            if matches!(type_head(kb, &walked), TypeHead::EffectsRows) {
                substituted_op_effects.extend(effect_row_present_values(kb, &walked));
            } else {
                substituted_op_effects.push(walked);
            }
        }
        // `mut`: a concretely-dispatched self-receiver spec op closes its
        // polymorphic effect row at the carrier below (WI-357).
        let mut effects = merge_effects(&substituted_op_effects, &arg_effects);

        // Resolve return type deeply so `Option[T = Var(vid_T)]`
        // collapses to `Option[T = Term]` once `vid_T` is bound. WI-341:
        // carrier-agnostic walk (the return type is a `Value`). `mut`: a
        // concretely-dispatched self-receiver spec op re-walks it below once
        // the carrier pins the spec's element params (WI-357).
        let mut resolved_ret = walk_type_deep_value(kb, &subst, &op.return_type);

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

        // WI-365 (call-side): a self-receiver spec op WITH a default body
        // (`Stream.collect` / `takeN`) is consumed as a NORMAL op —
        // `lookup_spec_op_dispatch` (body-less only) returns `None` for it, so
        // the WI-357 carrier element/effect threading in the dispatch block
        // below never runs. When such an op is consumed on a concrete carrier
        // (a `List` walked as a `Stream`), its `effects E` row variable — the
        // enclosing sort's own effect param — stays an unbound `?_` (a provider
        // fact cannot bind an effect parameter; effects aren't expressible as
        // type arguments — WI-301), spuriously surfacing as `undeclared effect:
        // ?_` at a pure consumption site (`length(collect([1,2,3]))`). Thread
        // the element from the carrier and close the row the same way the
        // body-less path does. (The element usually already threads via
        // argument unification binding the sort param; the effect-close is the
        // load-bearing part and is NOT gated on the bind, so a pure carrier
        // still closes `E` even when the element bound separately.)
        if lookup_spec_op_dispatch(kb, fn_sym).is_none() {
            if let Some(spec_sort) = self_receiver_spec_sort(kb, &op, fn_sym) {
                if let ReceiverCarrier::Concrete(carrier_sym) = receiver_carrier(
                    kb, &op, spec_sort, named_args, pos_results, named_results,
                ) {
                    if bind_spec_params_from_carrier(
                        kb, &mut subst, &op, spec_sort, carrier_sym,
                        named_args, pos_results, named_results,
                    ) {
                        resolved_ret = walk_type_deep_value(kb, &subst, &op.return_type);
                    }
                    let closed_op_effects: Vec<Value> = substituted_op_effects
                        .iter()
                        .filter(|e| !effect_is_unresolved_var(kb, e))
                        .cloned()
                        .collect();
                    effects = merge_effects(&closed_op_effects, &arg_effects);
                }
            }
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
            let enclosing_sort = env.enclosing_sort();

            // WI-350: classify the receiver to pick the dispatch carrier.
            // A self-receiver spec (`head(s: Stream)`) needs the receiver
            // argument's concrete carrier sort to disambiguate ≥2 impls
            // (its carrier is not a type-parameter, so the per-call subst
            // never pins it); an abstract spec value (`s : Stream[T]`)
            // carries no concrete impl and types through the interface.
            let carrier = receiver_carrier(
                kb, &op, spec_sort, named_args, pos_results, named_results,
            );

            // WI-357: a concretely-dispatched self-receiver spec op (e.g.
            // `Stream.splitFirst` on a `List[Int]`) binds none of the spec's
            // own type parameters through argument unification — the argument
            // matched the *bare* `Stream` parameter, not `Stream[T]`. The
            // unbound `Stream.T` both leaves the return `?_` (a destructured
            // `pair(h, _)` gets `h : ?_`) and makes the dispatch goal abstract
            // (no impl matches → a spurious `requires Stream[…]` demand on the
            // caller). Recover the spec params from the receiver carrier's
            // provider fact (`List` provides `fact Stream[T = T]` ⇒ a
            // `List[Int]` as a `Stream` has `Stream.T = Int`) and re-walk the
            // return type so the element threads through and the dispatch goal
            // below is concrete.
            if let ReceiverCarrier::Concrete(carrier_sym) = carrier {
                // WI-367: the spec params are usually already bound from this
                // carrier before expected-seeding (the early pass keys on the
                // op's PARENT sort), so this pass — keying on the dispatch-
                // resolved `spec_sort` — normally finds them filled and re-binds
                // nothing. It still runs as a fallback for the case where the
                // two resolve the spec to different symbols. `late_bound` records
                // whether it bound anything here.
                let late_bound = bind_spec_params_from_carrier(
                    kb, &mut subst, &op, spec_sort, carrier_sym,
                    named_args, pos_results, named_results,
                );
                if late_bound {
                    resolved_ret = walk_type_deep_value(kb, &subst, &op.return_type);
                }
                // Close the spec op's OWN polymorphic effect row at this
                // concrete carrier. The provider fact cannot yet bind the
                // effect parameter (effects aren't expressible as type
                // arguments — WI-301 / WI-320), so the spec op's `effects E`
                // walked to an unresolved row variable above. A concrete
                // carrier that provides the spec realizes that row as its
                // own effect; the only expressible case today is a pure
                // provider (`List`), so drop the still-unresolved row var
                // rather than surface it as a spurious `undeclared effect:
                // ?_`. Self-disabling: once a provider CAN bind `E`, the
                // label resolves and is no longer a bare var, so it is kept.
                //
                // Re-merge with the UNTOUCHED `arg_effects` rather than
                // filtering the merged set, so a genuinely polymorphic
                // effect contributed by the receiver argument itself is
                // never erased — only the spec op's own row is closed.
                //
                // WI-367: gate on the carrier binding succeeding EITHER here or
                // in the early pass (`carrier_bound`), not on `late_bound`
                // alone — the early pass now usually consumes the binding, but
                // the row still needs closing. This reproduces the pre-WI-367
                // condition exactly (effect-close ran iff the carrier bound a
                // spec param) while letting the element bind move earlier.
                if carrier_bound || late_bound {
                    let closed_op_effects: Vec<Value> = substituted_op_effects
                        .iter()
                        .filter(|e| !effect_is_unresolved_var(kb, e))
                        .cloned()
                        .collect();
                    effects = merge_effects(&closed_op_effects, &arg_effects);
                }
            }

            // WI-239: defer-to-requirement takes priority over provider-
            // based dispatch. If the spec op is reachable through the
            // enclosing sort's `requires` tree — directly (a frame slot)
            // or transitively (nested inside a direct requirement's
            // value) — the impl is selected at runtime from the threaded
            // requirement, so classify the deferral and skip dispatch.
            // The path's head is the direct frame slot; its tail is the
            // `requirement_at_sort` projection path (empty for a direct
            // require). The pre-WI-239 flat chain made transitive specs
            // direct slots, so `dispatch_spec_op_cached`'s direct-only
            // trigger covered them; under the direct-chain ABI the nested
            // case needs this tree walk.
            if !enclosing_requires.is_empty() {
                if let Some(path) = enclosing_sort
                    .and_then(|encl| find_requires_location(kb, &subst, spec_sort, encl))
                {
                    // `path` is non-empty on `Some`. Head = direct frame
                    // slot; tail = projection path into its bundled value.
                    let slot = path[0];
                    let proj_path: SmallVec<[usize; 2]> = path[1..].iter().copied().collect();
                    // WI-232: capture the matched direct-require entry so
                    // req_insertion::run can read it without re-indexing.
                    let resolved_spec = enclosing_requires[slot].clone();
                    classify(
                        kb,
                        occ,
                        CallClass::DeferToRequirement {
                            spec_op_sym: fn_sym,
                            op_short_sym,
                            resolved_spec,
                            slot,
                            proj_path,
                            enclosing_sort,
                        },
                    );
                    return Ok(TypeResult {
                        ty: resolved_ret.clone(),
                        env: env.clone(),
                        effects,
                        node: Rc::clone(occ),
                    });
                }
            }

            // WI-350: an abstract spec receiver (`s : Stream[T]`, or an
            // unresolved receiver type) that the `requires` pre-check above
            // did not cover pins no concrete impl. Type through the spec
            // op's interface signature (`resolved_ret`, already walked
            // through the per-call subst) and leave the call as the spec
            // op — eval resolves the impl from the runtime value's own
            // sort. Skipping concrete dispatch is what keeps a ≥2-impl
            // self-receiver spec from resolving `Ambiguous` for a
            // legitimately abstract call.
            if carrier == ReceiverCarrier::Abstract {
                // WI-325 exception: a spec that warrants the abstract check but
                // has NO provider at all (a user-defined, wholly-unimplemented
                // spec) has no runtime witness to defer to — every call will
                // fail at first dispatch. Fall through to the dispatch
                // `NoCandidates` arm so that case is surfaced at type-check
                // (that arm still returns the same interface type, just with the
                // diagnostic attached). Specs with ≥1 provider — and host
                // built-ins, which deliberately have none and don't warrant the
                // check — take the deferring early return.
                let has_witness = spec_has_any_providers(kb, spec_sort)
                    || !spec_warrants_abstract_check(kb, spec_sort);
                if has_witness {
                    return Ok(TypeResult {
                        ty: resolved_ret.clone(),
                        env: env.clone(),
                        effects,
                        node: Rc::clone(occ),
                    });
                }
            }
            let carrier_sym = match carrier {
                ReceiverCarrier::Concrete(c) => Some(c),
                ReceiverCarrier::NotApplicable | ReceiverCarrier::Abstract => None,
            };

            let (outcome, resolved_tree) = dispatch_spec_op_cached(
                kb, &subst, spec_sort, op_short_sym, enclosing_requires, carrier_sym,
            );
            match outcome {
                DispatchOutcome::NoCandidates => {
                    // WI-325: distinguish concrete-binding NoCandidates
                    // (legitimate pass-through — host builtin / spec-derived
                    // rule may resolve at runtime) from abstract-binding
                    // NoCandidates with no covering `requires` (unsafe —
                    // dispatch will fail at first call site). Concrete:
                    // leave untagged so the call stays as the spec op.
                    // Abstract: tag the occurrence so `req_insertion::run`
                    // can emit a `MissingRequiresForSpecOp` diagnostic.
                    //
                    // Gate on `spec_warrants_abstract_check`: stdlib specs
                    // like `Map`, `List`, `Stream`, `Collection`, `Iteration`,
                    // … deliberately have zero `fact Spec[…]` records —
                    // they're host built-ins where the runtime resolves
                    // operations directly. Abstract calls against such
                    // specs are intentionally allowed (the `NoCandidates`
                    // doc comment names them). User-defined specs (outside
                    // the `anthill.*` namespace) without providers are NOT
                    // host-builtin — they're the WI-324 'forgot to register
                    // an impl' case and warrant the diagnostic. Stdlib
                    // specs with at least one provider (Eq, Numeric, Ordered,
                    // …) also warrant it — the spec_has_any_providers leg.
                    //
                    // Detection lives here because the per-call substitution
                    // is still in scope; `req_insertion::run` only sees the
                    // IR shape, not the typer's subst.
                    //
                    // Why we walk type_params directly instead of consuming
                    // `sort_goal_from_subst`: `sort_goal_from_subst` only
                    // emits a binding when the spec var resolves to a
                    // `Value::Term` — but unification often binds the
                    // *caller's* var to the spec's var (e.g. `Container.T
                    // → Eq.T`), leaving the spec's var as the equivalence-
                    // class root with no direct binding. Resolving the
                    // spec's var then returns `None`, and the goal has zero
                    // bindings even though `T` is plainly abstract. The
                    // direct walk treats `None`-resolved AND
                    // `Var`-resolved as abstract.
                    //
                    // Loader-inconsistency arms (the three former silent
                    // `continue`s) now treat the param as abstract: if we
                    // can't introspect the param's alias var, we can't
                    // prove it's concrete either, so the conservative
                    // outcome is to surface the diagnostic. This guards
                    // against a future spec representation (e.g. denoted
                    // / value-in-type params per WI-302) silently disabling
                    // the WI-325 protection.
                    if spec_warrants_abstract_check(kb, spec_sort) {
                        let spec_qn = kb.qualified_name_of(spec_sort).to_string();
                        // WI-387 FIX 3: the receiver carrier's provider fact may
                        // bind a spec param to a GROUND value (`List provides
                        // Stream[E = {}]`). `bind_spec_params_from_carrier`
                        // threads only type-param-REF provider bindings (`Stream.T
                        // ↦ List.T`) into the subst, so a written ground row never
                        // reaches the per-param subst resolution below and would be
                        // wrongly flagged abstract — regressing delivered
                        // wi357/wi210 once `List` writes `E = {}`. Such a param is
                        // concrete → COVERED, so skip it; a provider binding that
                        // mentions a type-param stays abstract (still demands a
                        // `requires`, e.g. a `C provides Iterable[Element = C.T]`).
                        let provider_bindings = carrier_sym
                            .and_then(|c| provider_spec_view_bindings(kb, c, spec_sort));
                        let mut abstract_params: SmallVec<[Symbol; 2]> = SmallVec::new();
                        for short in kb.type_params_of_sort(spec_sort) {
                            if provider_bindings.as_ref().is_some_and(|binds| {
                                binds.iter().any(|(p, v)| {
                                    short_name_of(kb.resolve_sym(*p)) == short.as_str()
                                        && type_value_is_ground(kb, *v)
                                })
                            }) {
                                continue;
                            }
                            let short_qn = format!("{spec_qn}.{short}");
                            let short_qn_sym = match kb.try_resolve_symbol(&short_qn) {
                                Some(s) => s,
                                None => {
                                    // Loader inconsistency — qualified param
                                    // name missing. Conservatively report.
                                    abstract_params.push(kb.intern(&short));
                                    continue;
                                }
                            };
                            let alias_target = match resolve_sort_alias(kb, short_qn_sym) {
                                Some(t) => t,
                                None => {
                                    // No SortAlias fact — can't introspect.
                                    abstract_params.push(short_qn_sym);
                                    continue;
                                }
                            };
                            let vid = match kb.get_term(alias_target) {
                                Term::Var(Var::Global(v)) => *v,
                                _ => {
                                    // Future-shape alias (denoted/value-
                                    // dependent) — assume abstract.
                                    abstract_params.push(short_qn_sym);
                                    continue;
                                }
                            };
                            let is_abstract = match subst.resolve_as_value(vid) {
                                None => true,
                                Some(Value::Term(bound)) => is_type_param_value(kb, *bound),
                                // A non-`Term` carrier (a denoted `Value::Node`
                                // / value-in-type param, WI-302) can't be
                                // introspected for type-param-ness here, so —
                                // like the loader-inconsistency arms above and
                                // per this loop's documented stance — assume
                                // abstract rather than silently disable the
                                // WI-325 protection. Carrier-agnostic
                                // introspection is WI-348 Phase C.
                                Some(_) => true,
                            };
                            if is_abstract {
                                abstract_params.push(short_qn_sym);
                            }
                        }
                        if !abstract_params.is_empty() {
                            classify(
                                kb,
                                occ,
                                CallClass::UnresolvedSpecOp {
                                    spec_op_sym: fn_sym,
                                    spec_sort_sym: spec_sort,
                                    abstract_params,
                                    span,
                                    enclosing_sort,
                                },
                            );
                        }
                    }
                }
                DispatchOutcome::Unique(impl_op_sym) => {
                    // WI-365: ground the spec op's polymorphic effect ROW to the
                    // dispatched impl's real effects (the effect dual of WI-357's
                    // element threading). The pre-dispatch effect-close dropped
                    // the unresolved row as if the carrier were pure; a concrete
                    // impl that overrides the op with a genuine effect
                    // (`MutBox.peek effects Modify[b]`) must surface it at the
                    // consumption site so a pure consumer is rejected, exactly as
                    // a DIRECT call to the impl op is. A pure override (empty or
                    // wholly-unresolved effects) contributes nothing, so the
                    // `List`-as-`Stream` pure path is unchanged. Only a real
                    // override (`impl_op_sym != fn_sym`) can carry an effect the
                    // spec signature didn't.
                    if impl_op_sym != fn_sym {
                        let derived = dispatched_impl_effects(
                            kb, impl_op_sym, &op.params, &subst, pos_args, named_args,
                        );
                        // The spec op's polymorphic effect row is GROUNDED by
                        // this concrete dispatch. Drop the still-unresolved row
                        // var from the SPEC OP's OWN effects only — the
                        // pre-dispatch effect-close fires only for a type-param
                        // carrier binding, so an effect-only spec (`Box`:
                        // `effects Effect = ?`, no type-arg binding) still carries
                        // its `?_` here — substitute the impl's real effects in
                        // its place, then re-merge the UNTOUCHED `arg_effects`. We
                        // filter `substituted_op_effects`, not the merged
                        // `effects`, for the same reason the pre-dispatch close
                        // does (line above): a genuinely-polymorphic effect a
                        // receiver argument contributes must never be erased. A
                        // pure impl grounds the row to {} (`derived` empty); a
                        // non-pure one contributes its `Modify[b]`, so a pure
                        // consumer is rejected.
                        let closed_op_effects: Vec<Value> = substituted_op_effects
                            .iter()
                            .filter(|e| !effect_is_unresolved_var(kb, e))
                            .cloned()
                            .collect();
                        let op_and_impl = merge_effects(&closed_op_effects, &derived);
                        effects = merge_effects(&op_and_impl, &arg_effects);
                    }
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
                    // Fallback: the WI-239 pre-check above already caught
                    // every spec reachable via `find_requires_location`
                    // (a superset of `find_requires_slot`), so this fires
                    // only when `resolve_at_goal` deferred via a path the
                    // tree walk's matcher missed. It can only resolve a
                    // DIRECT slot, hence an empty `proj_path`.
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
                                proj_path: SmallVec::new(),
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

    // Path 2: variable with arrow type. WI-341 Stage A: the env carries `Value`.
    // WI-361/WI-342: one carrier-agnostic read — a ground (`Value::Term`) and a
    // `Value::Node` callback arrow (denoted-bearing effect, e.g. `Modify[a]`)
    // both flow through `extract_function_type_parts`, the occurrence never
    // re-grounded.
    if let Some(fn_type) = env.lookup_var(fn_sym) {
        if let Some((ret_ty, effects)) = extract_function_type_parts(kb, &fn_type) {
            return Ok(TypeResult { ty: ret_ty, env: env.clone(), effects, node: Rc::clone(occ) });
        }
    }

    // Path 3: unknown functor — collect arg effects (from pre-computed
    // results) and fall back to the declared return type if any.
    let mut effects: Vec<Value> = Vec::new();
    for r in pos_results.iter().chain(named_results.iter()) {
        if let Ok(r) = r {
            effects = merge_effects(&effects, &r.effects);
        }
    }
    let _ = pos_args;
    let _ = named_args;
    lookup_operation_return_type(kb, fn_sym)
        .map(|ty| TypeResult { ty: Value::Term(ty), env: env.clone(), effects, node: Rc::clone(occ) })
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
    // WI-239: the callee's DIRECT requires — one projection per slot the
    // callee body reads by `__req_<spec>` name. Matches `synth_req_names`
    // (also direct) so the constructed dict's arity equals the callee's
    // direct-require count, satisfying eval's `expand_dispatching_dict`
    // arity invariant. Transitive callee requires are bundled recursively
    // inside each direct projection, not flattened into this list.
    let callee_chain = direct_requires_chain(kb, callee_spec_sort);
    // Hoist Strategy 2's per-slot direct-requires walk out of the dep
    // loop: it depends only on `caller_requires`, not on the current
    // dep, so the worst-case cost drops from O(deps × slots × |SortRequiresInfo|)
    // to O(slots × |SortRequiresInfo|).
    //
    // WI-239: DIRECT (not transitive). A requirement value bundles only
    // its own direct sub-requires, so `requirement_at_sort(__req_i, k)`'s
    // `k` indexes the i-th caller require's *direct* sub-chain. A deeper
    // dep (reachable only past two levels) is not found by Strategy 2 and
    // falls through to Strategy 3's SLD construction.
    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| direct_requires_chain(kb, ar.required_sort))
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
/// `[direct_requires_chain(c.required_sort) for c in caller_requires]`
/// (WI-239) — the nested-search index, computed once by the caller. It
/// is the *direct* sub-chain because a requirement value bundles only
/// its own direct sub-requires, so a single `requirement_at_sort`
/// projection indexes it.
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

    // Strategy 2 — nested via caller slots' DIRECT requires (WI-239),
    // binding-aware. The slot's runtime requirement value bundles its
    // own direct sub-requires in the same order, so a single
    // `requirement_at_sort` projects them. A dep reachable only past a
    // second level is not found here and falls through to Strategy 3's
    // SLD construction.
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
fn entries_cover(kb: &mut KnowledgeBase, caller: &RequiresEntry, dep: &RequiresEntry) -> bool {
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
        // A `requires` entry resolves by its declared bindings; carrier
        // discrimination is a call-site concern (WI-350).
        carrier: None,
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

/// WI-222 Phase C+D / WI-237 (names model) / WI-239: defer-to-requirement
/// rewrite. Emits `apply_within(fn = Ref(spec_op_sym), args = <orig>,
/// requirements = [<dispatching dict>])`. Dispatch from spec-op to
/// impl-op happens at the apply_within reduction by reading the
/// dispatching dict's functor. `slot` is the DIRECT requirement's
/// position in `enclosing_sort`'s requires chain, mapped to the
/// synthesized `__req_*` param name via `req_name_for_chain_index`.
///
/// WI-239: `proj_path` descends into that direct requirement's bundled
/// value. Empty ⇒ the dispatching dict is the bare
/// `var_ref(name = __req_<slot>)` (the original WI-222 direct case);
/// non-empty ⇒ the spec is nested, so wrap the `var_ref` in one
/// `requirement_at_sort(chain, slot = k)` per `proj_path` index
/// (outermost last) — the same shape `build_dep_projection` Strategy 2
/// emits, here driven by the resolved tree path.
pub(crate) fn record_apply_within_rewrite(
    kb: &mut KnowledgeBase,
    original_apply: TermId,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    pos_args: &SmallVec<[TermId; 4]>,
    spec_op_sym: Symbol,
    enclosing_sort: Option<Symbol>,
    slot: usize,
    proj_path: &[usize],
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
    // var_ref(__req_<slot>), then one requirement_at_sort step per
    // projection index for the nested case (no-op when proj_path empty).
    let mut dict_expr = build_req_var_ref(kb, &syms, name);
    for &k in proj_path {
        dict_expr = build_req_at_sort(kb, &syms, dict_expr, k);
    }
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
    params: Vec<(Symbol, Value)>,  // (param_name, param_type); WI-341 carrier-agnostic
    return_type: Value,            // WI-341 carrier-agnostic
    effects: Vec<Value>,
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
        // WI-342 S4b: a type-arg is a carrier-agnostic `Value` (`Value: TermView`),
        // so unify it directly — a value-in-type arg (`Value::Node`) unifies
        // cross-carrier through the typer's view dispatch, no re-ground.
        unify_types(kb, subst, &TermIdView(target), value);
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
        // Carrier-agnostic resolve over [`TermView`]: `walk_view` returns a
        // `Value`, so a var bound to a `Value::Node` (a WRITTEN effect row
        // `E = {Modify[p]}` threaded into an op's `Eff` param by the same-sort
        // arg-unification, WI-393) is SURFACED, not lost. The term-only
        // `walk_type`/`walk_type_deep` cannot: their `TermId` return has nowhere
        // to put a non-`Term` carrier, so they keep the var and a row-bound
        // effect param was falsely flagged unconstrained. A genuinely unbound
        // param still resolves to a bare var.
        let resolved = walk_view(kb, subst, &TermIdView(*var_term));
        if resolved_var(kb, &resolved).is_some() {
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
    ///
    /// WI-239: `slot` is always a DIRECT requirement slot. `proj_path`
    /// descends into that direct requirement's tree-shaped value: empty
    /// when the spec *is* the direct requirement (read the frame slot
    /// directly — the original WI-222 case), non-empty when the spec is
    /// reached transitively, by applying one `requirement_at_sort`
    /// projection per index. The pre-WI-239 flat `requires` chain made
    /// every transitive spec a top-level slot, so `proj_path` was always
    /// empty; the direct-chain ABI moves transitive specs inside their
    /// direct parent's bundled value.
    DeferToRequirement {
        spec_op_sym: Symbol,
        op_short_sym: Symbol,
        resolved_spec: RequiresEntry,
        slot: usize,
        proj_path: SmallVec<[usize; 2]>,
        enclosing_sort: Option<Symbol>,
    },
    /// WI-325: dispatch returned `NoCandidates` AND the call's per-call
    /// substitution leaves at least one of the spec's type parameters
    /// abstract (`is_type_param_value`). The typer detects the abstract
    /// case here (where the subst is still in scope) and tags the
    /// occurrence; `req_insertion::run` translates the tag into a
    /// `MissingRequiresForSpecOp` error. Concrete-binding `NoCandidates`
    /// is **not** classified — it remains a legitimate pass-through
    /// (host builtin / spec-derived rule may resolve at runtime).
    ///
    /// `abstract_params` lists the spec's short type-param names
    /// (e.g. `T`) that the call left abstract. `enclosing_sort` is
    /// `Some(spec_sort_sym)` only for self-recursive calls inside the
    /// spec's own body — `req_insertion::run` filters those out.
    UnresolvedSpecOp {
        spec_op_sym: Symbol,
        spec_sort_sym: Symbol,
        abstract_params: SmallVec<[Symbol; 2]>,
        span: Option<Span>,
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
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    chain: &[RequiresEntry],
) -> Option<usize> {
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    chain
        .iter()
        .position(|entry| entry_matches_subst(kb, subst, spec_sort, &spec_qn, entry))
}

/// WI-221/WI-222 — true iff `entry` is a `requires` for `spec_sort`
/// whose bindings are consistent with the per-call substitution `subst`
/// (the defer-to-requirement match). Extracted from `find_requires_slot`
/// (WI-239) so the same predicate drives both the flat-chain slot search
/// and the tree walk in `find_requires_location`. `spec_qn` is
/// `qualified_name_of(spec_sort)`, hoisted by callers that test many
/// entries.
fn entry_matches_subst(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    spec_qn: &str,
    entry: &RequiresEntry,
) -> bool {
    if entry.required_sort != spec_sort {
        return false;
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
                return false;
            }
        }
        Term::Ref(_) | Term::Ident(_) => SmallVec::new(),
        _ => return false,
    };

    if bindings.is_empty() {
        return true;
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
        let per_call_value = match subst.resolve_as_value(vid) {
            // Unbound spec param: this is the OPEN-T defer trigger.
            // The call's binding was not constrained to a concrete
            // carrier (often because the typer unified two free Vars
            // and bound the *other* direction). Per
            // `docs/design/operation-call-model.md` §"Defer-to-
            // requirement detection", an open type-var in the goal
            // means defer — the impl is determined at runtime by the
            // requirement value the caller passed. Match this entry.
            None => continue,
            Some(Value::Term(v)) => *v,
            // A denoted `Value::Node` param: matching it against the requires
            // entry needs the symmetric `TermId` match below to go
            // carrier-agnostic (WI-348 Phase C). Until then, conservatively
            // defer (sound — the impl is resolved at runtime), but flag loudly
            // in debug so the gap surfaces the moment a denoted carrier reaches
            // here.
            Some(other) => {
                debug_assert!(
                    false,
                    "WI-348: denoted {} spec param in defer-match — carrier-agnostic entry match is Phase C",
                    other.type_name(),
                );
                continue;
            }
        };
        // Either side may be a wildcard (a type-param value): the
        // requires entry might use the enclosing sort's open T
        // (`requires Eq[T]`) or a concrete carrier (`requires Eq[T=Int]`).
        // Symmetric match — try both directions.
        if !dispatch_values_match(kb, per_call_value, *entry_value)
            && !dispatch_values_match(kb, *entry_value, per_call_value)
        {
            return false;
        }
    }
    true
}

/// WI-239 — locate the spec a deferred call needs within `sort_sym`'s
/// `requires` **tree** (substitution-composed). Pre-order DFS; returns
/// the path of child indices to the first node whose entry matches
/// `subst` at `spec_sort`, or `None` if unreachable. The path is always
/// non-empty on `Some`: its head is the DIRECT (frame-slot) index, and
/// any tail indices are the `requirement_at_sort` projection path into
/// that direct requirement's bundled value (empty tail = the spec *is*
/// the direct requirement).
///
/// Reproduces — on the DIRECT chain plus its tree — the reachability the
/// pre-WI-239 flat `requires_chain` gave `find_requires_slot` for free
/// (the flat chain spliced transitive entries inline as top-level slots).
/// Under the tree-native ABI a transitive entry is no longer a frame
/// slot, so the typer's classification consults this to recover the
/// `(slot, proj_path)` encoding for `CallClass::DeferToRequirement`.
pub fn find_requires_location(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    sort_sym: Symbol,
) -> Option<SmallVec<[usize; 2]>> {
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let tree = requires_tree(kb, sort_sym);
    let mut path: SmallVec<[usize; 2]> = SmallVec::new();
    if find_in_requires_nodes(kb, subst, spec_sort, &spec_qn, &tree, &mut path) {
        Some(path)
    } else {
        None
    }
}

/// WI-239 — pre-order DFS helper for [`find_requires_location`]. Pushes
/// each node's index onto `path` before testing; on a match leaves
/// `path` holding the full path to the matched node. `nodes` comes from
/// the substitution-composed `requires_tree`, so it does not alias `kb`.
fn find_in_requires_nodes(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    spec_qn: &str,
    nodes: &[RequiresNode],
    path: &mut SmallVec<[usize; 2]>,
) -> bool {
    for (i, node) in nodes.iter().enumerate() {
        path.push(i);
        if entry_matches_subst(kb, subst, spec_sort, spec_qn, &node.entry) {
            return true;
        }
        if find_in_requires_nodes(kb, subst, spec_sort, spec_qn, &node.sub_requires, path) {
            return true;
        }
        path.pop();
    }
    false
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
    /// WI-350 — the receiver's concrete carrier sort, when the spec op
    /// has a *self-receiver* parameter (one declared with the spec sort
    /// itself, e.g. `head(s: Stream)`). For such specs the carrier is
    /// NOT a type parameter (Stream's only param `T` is the element),
    /// so the per-call `bindings` never pin which impl provides the op
    /// — every impl's universally-quantified `fact Stream[T]` matches,
    /// and a ≥2-impl spec would resolve `Ambiguous` for even a fully
    /// concrete call. The carrier (the receiver argument's base sort —
    /// `List`, `LogicalStream`) discriminates: `collect_provides_candidates`
    /// keeps only candidates whose `impl_sort` equals it. `None` for
    /// the common type-parameter-carrier specs (`Eq`/`Numeric`/`Iterable`,
    /// where the carrier IS a binding and dispatch is already pinned) and
    /// for transitive sub-goals — those resolve by binding alone.
    pub carrier: Option<Symbol>,
}

/// WI-350 — classification of a spec op's receiver at a call site,
/// driving carrier-aware dispatch. Computed by [`receiver_carrier`] from
/// the spec op's *self-receiver* parameter (the one declared with the
/// spec sort itself, e.g. `head(s: Stream)`) and that argument's actual
/// inferred type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReceiverCarrier {
    /// No self-receiver parameter — the op's carrier arguments are typed
    /// with the spec's own type-parameter (`Eq.eq(a: T, b: T)`,
    /// `Iterable.iterator(c: C)`). The carrier is a binding, so the
    /// per-call substitution already pins it; dispatch proceeds by
    /// binding (the pre-WI-350 behaviour, including legitimate `Ambiguous`
    /// for two impls at the same binding).
    NotApplicable,
    /// A self-receiver parameter exists and its argument's base sort IS
    /// the spec sort (`s : Stream[T = …]`) — an abstract spec value — or
    /// its type is still unresolved. No concrete impl is pinnable here;
    /// the call types through the spec op's interface signature and the
    /// impl is resolved at runtime from the value's own witness (or, if
    /// earlier `find_requires_location` matched, from a `requires` slot).
    Abstract,
    /// A self-receiver parameter exists and its argument has a concrete
    /// carrier sort (`s : List[Int]` → `List`). Dispatch keeps only the
    /// candidate whose `impl_sort` equals this carrier.
    Concrete(Symbol),
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
/// WI-325 — true iff abstract-binding `NoCandidates` on this spec
/// should fire the `MissingRequiresForSpecOp` diagnostic. Two cases
/// warrant it:
///
/// 1. Spec has at least one declared provider (Eq, Numeric, Ordered,
///    …): the user clearly intends per-carrier dispatch and forgot
///    either the `requires` clause or to specialize the call.
/// 2. Spec is user-defined (outside the stdlib `anthill.*` namespace
///    prefix) and has zero providers: the WI-324 'forgot to register
///    an impl' case. Without this leg, a user who defines `sort MySpec
///    { … }` and calls a MySpec op on abstract T silently slips through
///    just because no `fact MySpec[T = …]` has been written yet — the
///    exact phantom WI-325 set out to eliminate.
///
/// Stdlib specs with no providers (Map, List, Stream, Collection,
/// Iteration, IndexedSeq, Field, Lattice, BoundedLattice, Algebra, …)
/// are host-builtin: the runtime resolves their operations directly,
/// no `fact Spec[…]` ever appears, and abstract calls against them
/// (e.g. `Map.empty()` at unbound K, V) are legitimate pass-through.
fn spec_warrants_abstract_check(kb: &KnowledgeBase, spec_sort: Symbol) -> bool {
    if spec_has_any_providers(kb, spec_sort) {
        return true;
    }
    // User-defined spec without providers: still warrants the check.
    !kb.qualified_name_of(spec_sort).starts_with("anthill.")
}

/// WI-325 — true iff at least one `SortProvidesInfo` fact exists whose
/// spec base matches `spec_sort`, regardless of whether the bindings
/// match any particular per-call goal. Used as one leg of
/// `spec_warrants_abstract_check`.
fn spec_has_any_providers(kb: &KnowledgeBase, spec_sort: Symbol) -> bool {
    let provides_sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return false,
    };
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) { continue; }
        // A value-fact SortProvidesInfo (denoted-bearing spec) is skipped here;
        // occurrence-based provider lookup is gated effect-expressions-as-types
        // work (avoid the term-only `rule_head` panic on a value head).
        let Some(head_named) = kb.fact_head_named_args(rid) else { continue };
        let spec_view_tid = match get_named_arg(kb, &head_named, "spec") {
            Some(t) => t,
            None => continue,
        };
        if let Some((view_base_sym, _)) = unwrap_spec_view(kb, spec_view_tid) {
            if view_base_sym == spec_sort {
                return true;
            }
        }
    }
    false
}

fn collect_provides_candidates(
    kb: &mut KnowledgeBase,
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
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        // A value-fact SortProvidesInfo (denoted-bearing spec) is skipped from
        // dispatch-candidate collection; occurrence-based dispatch is gated
        // effect-expressions-as-types work (avoid the term-only `rule_head`
        // panic on a value head).
        let Some(head_named) = kb.fact_head_named_args(rid) else { continue };
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

        // WI-350: when the call supplies a concrete receiver carrier (a
        // self-receiver spec — `head(s: Stream)` with `s : List[…]`),
        // keep only the impl that carrier provides. Without this, a spec
        // whose carrier is not a type parameter (Stream's only param is
        // the *element*) matches every impl's universally-quantified
        // `fact Stream[T]` and resolves `Ambiguous` for ≥2 impls — even a
        // fully concrete call. For type-parameter-carrier specs (`Eq`,
        // `Numeric`, `Iterable`) `goal.carrier` is `None` and binding
        // matching below does the discrimination. Canonicalize both sides:
        // `impl_sort` (a `SortProvidesInfo.sort_ref` functor) and the carrier
        // may be interned under different copies of the same logical sort —
        // the same normalization `sort_ops_lookup` applies to `impl_sort`.
        if let Some(carrier) = goal.carrier {
            if kb.canonical_sort_sym(impl_sort) != kb.canonical_sort_sym(carrier) {
                continue;
            }
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
                    // WI-387: the goal under-constrains this spec param (no
                    // per-call value). On the CARRIER-LESS compat path (provider
                    // admissibility — "does some carrier provide Stream?"), a
                    // written EFFECT-ROW binding (`E = {}` on `List provides
                    // Stream[E = {}]`) is NON-discriminating for dispatch — it
                    // carries the observation effect, not the carrier identity —
                    // so it must not drop the candidate, and two providers still
                    // resolve `Ambiguous` (the dispatch analogue of FIX 3: a
                    // provided concrete `E` covers, it does not demand). A TYPE
                    // binding the goal omits (a concrete `T = Int` on `fact
                    // Eq[T = Int]`) IS discriminating and keeps the strict reject —
                    // else every concrete `Eq` impl would match a bare `Eq` goal
                    // (a coherence violation: wi325 / wi237). The CONCRETE
                    // self-receiver path (`goal.carrier = Some`) also keeps the
                    // strict reject: its carrier filter already selected the impl
                    // and WI-357's pre-dispatch element re-walk threads the type,
                    // so altering its outcome would regress element threading
                    // (wi357).
                    let is_effect_row = matches!(
                        type_dispatch_name_view(kb, &TermIdView(*candidate_value)),
                        Some("effects_rows")
                    );
                    if goal.carrier.is_none() && is_effect_row {
                        continue;
                    }
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
    kb: &mut KnowledgeBase,
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
            let f_qn = kb.qualified_name_of(*functor);
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
            // WI-361: a parameterized type is the term backing `Fn{S, named}` (base
            // sort IS the functor, bindings ARE the named args) — handled by the
            // generic-Fn arm below as `(S, named_args)`, no `parameterized(base,
            // bindings)` wrapper to translate.
            // WI-320: `effects_rows(effects_expr = E)` is a structural Type
            // variant (wraps an EffectExpression), not a parametric spec
            // carrier — `effects_expr` is a *field*, not a spec parameter.
            // Without this explicit None, the generic-Fn catch-all below
            // would falsely classify it as a parametric instance with a
            // phantom (param = effects_expr, value = E) binding, leading
            // spec-resolution and `values_structurally_equal` to treat it
            // as a satisfaction site.
            if f_qn == "EffectsRows" || f_qn.ends_with(".EffectsRows") {
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
/// the impl-side substitution into the impl sort's **direct** `requires`
/// (WI-239). Filters out op-bindings (which the loader stores alongside
/// type-param bindings on a `SortView` — see `find_requires_slot`'s same
/// distinction) — only type-param bindings drive resolution.
///
/// WI-239: direct, not transitive. The resolution tree mirrors the
/// runtime requirement-value tree: each `Conditional` node bundles one
/// `sub_resolution` per *direct* require, and transitive requires are
/// resolved recursively when those sub-resolutions are themselves
/// `Conditional`. This keeps a constructed requirement value's arity
/// equal to `synth_req_names(impl_sort)` (also direct) — the invariant
/// eval's `expand_dispatching_dict` cross-checks. A flat chain here
/// would over-count the sub-resolutions (the duplicated-subtree problem)
/// and break that arity check.
fn candidate_sub_goals_owned(
    kb: &mut KnowledgeBase,
    impl_sort: Symbol,
    impl_subst: &[(Symbol, TermId)],
) -> Vec<SortGoal> {
    let chain = direct_requires_chain(kb, impl_sort);
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
            // Transitive `requires` sub-goals resolve by binding; the
            // receiver carrier discriminates only the top-level call (WI-350).
            carrier: None,
        });
    }
    out
}

/// WI-343/WI-356 — provider-side requires coverage. For every satisfaction
/// fact `fact Spec[sort_ref = X, spec = Spec[σ]]`, each spec-level `requires`
/// of `Spec`, **instantiated at the provision's bindings σ**, must itself
/// resolve. An unsatisfied requirement means the fact is unsound: `X` is
/// declared to provide `Spec`, yet `Spec`'s contract (its `requires`) does
/// not hold at `X`'s bindings.
///
/// Binding-precise and transitive where the representation allows it
/// (WI-356). `provider_requires_subgoals` substitutes σ into each `requires
/// R[…]` clause (σ keyed by short *name* — see there). Then, per clause:
///
///  - If σ grounded every binding to a **concrete** value, resolve the exact
///    instance via `spec_resolves_at_bindings` — binding-precise (a provider
///    satisfying `R` at the *wrong* bindings now fails) AND transitive (the
///    resolver recurses into `R`'s own `requires`). This is the case the WI
///    targets: `Ordered[T=Int] requires Eq[T]` is checked as `Eq[T=Int]`.
///  - If a binding stays an abstract type-param, fall back to v0's base-level
///    existence check (some sort named in the provision provides `R`). Two
///    stdlib realities force this: the shorthand `requires Ring[F]` drops the
///    `F`→`Ring.T` binding when the names differ (Ring's param is `T`), so σ
///    can't ground it; and an unbound goal value can't be matched against a
///    ground `fact` (`dispatch_values_match` only treats the *candidate* as a
///    wildcard). Recovering precision for that shape needs the loader to
///    record the cross-param binding — a separate change.
///
/// The `EffectsRuntime` kind-anchor (synthesized from `effects E = ?`) is
/// skipped: it is satisfied structurally by the effect-row machinery, never
/// by a carrier `fact`.
pub fn check_provider_requires(kb: &mut KnowledgeBase) -> Vec<super::load::LoadError> {
    use super::load::LoadError;
    let Some(provides_sym) = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") else {
        return Vec::new();
    };
    let effects_runtime = kb.try_resolve_symbol("anthill.prelude.EffectsRuntime");

    // Snapshot each provision before the requires walk, which mutates `kb`
    // (`provider_requires_subgoals` allocates substituted terms).
    struct Provision {
        carrier: Symbol,
        spec: Symbol,
        /// σ — the spec's type-param **short name** → the provision's
        /// binding value (`"F" → Float`). Keyed by short name, not symbol:
        /// the stdlib shorthand `requires Eq[T]` stores the requires-binding
        /// value as the *required* spec's own param (`Eq.T`), linked to the
        /// enclosing param only by the shared short name, so a symbol-keyed
        /// σ would never reach it.
        sigma: SmallVec<[(String, TermId); 2]>,
    }
    let mut provisions: Vec<Provision> = Vec::new();
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        // A value-fact SortProvidesInfo (denoted-bearing spec) is skipped from
        // ops-coverage checking; occurrence-based coverage is gated effect-
        // expressions-as-types work (avoid the term-only `rule_head` panic).
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &named, "sort_ref") else { continue };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else { continue };
        let Some(spec_view) = get_named_arg(kb, &named, "spec") else { continue };
        let Some((spec_base, _)) = unwrap_spec_view(kb, spec_view) else { continue };

        let spec_qn = kb.qualified_name_of(spec_base).to_string();
        let mut sigma: SmallVec<[(String, TermId); 2]> = SmallVec::new();
        if let Term::Fn { functor, pos_args, named_args } = kb.get_term(spec_view).clone() {
            let is_sortview = kb.qualified_name_of(functor).ends_with("SortView");
            // Named bindings (`F = Float`, `C = List[T]`).
            for (k, v) in &named_args {
                if is_type_param_binding(kb, *k, &spec_qn) {
                    sigma.push((kb.resolve_sym(*k).to_string(), *v));
                }
            }
            // Positional bindings (`VectorSpace[Vec3, Float]`): `unwrap_spec_view`
            // keeps only named args, so map the view's positional args to the
            // spec's params by declaration order. A `SortView` wrapper carries
            // the spec base in `pos_args[0]`; a bare parameterized term does not.
            // Fill only params not already pinned by a named binding, so a mixed
            // `Spec[V = Vec3, Float]` assigns the positional to the next free param.
            let skip = if is_sortview { 1 } else { 0 };
            if pos_args.len() > skip {
                let unbound: Vec<String> = kb.type_params_of_sort(spec_base)
                    .into_iter()
                    .filter(|p| !sigma.iter().any(|(n, _)| n == p))
                    .collect();
                for (val, name) in pos_args.iter().skip(skip).zip(unbound.iter()) {
                    sigma.push((name.clone(), *val));
                }
            }
        }
        provisions.push(Provision { carrier, spec: spec_base, sigma });
    }

    let mut errors = Vec::new();
    for p in &provisions {
        for goal in provider_requires_subgoals(kb, p.spec, &p.sigma) {
            let required = goal.spec_sort;
            if Some(required) == effects_runtime {
                continue;
            }
            // Binding-precise where the representation allows it: when σ
            // grounded every binding to a concrete value, resolve the exact
            // instance through the canonical resolver (binding-precise AND
            // transitive — `resolve` recurses into R's own `requires`). When
            // a binding stays an abstract type-param — the stdlib shorthand
            // `requires Ring[F]` drops the `F`→`Ring.T` link (Ring's param is
            // `T`), and an unbound value can't match a ground fact
            // (`dispatch_values_match`) — fall back to v0's base-level
            // existence check (some sort named in the provision provides R).
            let concrete = goal.bindings.iter().all(|(_, v)| !contains_type_param(kb, *v));
            let satisfied = if concrete {
                spec_resolves_at_bindings(kb, required, goal.bindings)
            } else {
                let mut cands: SmallVec<[Symbol; 4]> = SmallVec::from_elem(p.carrier, 1);
                for (_, v) in &p.sigma {
                    if let Some(s) = sort_sym_of_term(kb, *v) {
                        cands.push(s);
                    }
                }
                cands.iter().any(|&c| sort_provides(kb, c, required))
            };
            if !satisfied {
                errors.push(LoadError::UnsatisfiedProviderRequires {
                    carrier: kb.qualified_name_of(p.carrier).to_string(),
                    spec: kb.qualified_name_of(p.spec).to_string(),
                    required: kb.qualified_name_of(required).to_string(),
                });
            }
        }
    }
    errors
}

/// WI-363: provider-side **operation** coverage — the op-level twin of
/// [`check_provider_requires`]. For each `fact Spec[X]` (a `SortProvidesInfo`
/// fact), every operation `Spec` declares must be *backed* for `X`: either a
/// spec-level default on `Spec` (an `operation … = …` body, a derivation rule,
/// or a registered builtin) OR an operation `X` itself supplies. An op with
/// neither resolves to nothing at runtime, so the satisfaction fact is unsound
/// — reported as a load-blocking [`LoadError::UnbackedProviderOperation`].
///
/// Backing detection is deliberately *conservative* (it errs toward "backed").
/// The goal is the egregious gap — an op with no implementation anywhere (e.g.
/// `Stream.takeN` before WI-362, or a carrier that forgot the `splitFirst`
/// primitive) — without false-positiving on the many legitimate shapes a
/// definition takes:
///   - **host carriers** (`Int`/`Float`/… via `provides X language rust`): their
///     ops are backed by the host artifact (`Int.compare` is `i64`'s `Ord`), so
///     the whole provision is skipped — detected by an
///     `anthill.realization.Implementation` fact targeting `X`. Mirrors how
///     [`check_provider_requires`] skips `EffectsRuntime`.
///   - **spec/carrier op body**: a runnable `operation … = …` on `Spec` or `X`
///     (resolved via `sort_ops` + `op_has_runnable_body`).
///   - **equational rule** `op(args) = rhs` (guarded or not): stored under the
///     `eq` functor with `op` as the LHS head — covers `Stream.head/tail`,
///     `Ordered.gt`, the spec laws, etc.
///   - **relational rule** `op(args, result) :- body`: stored under `op`'s own
///     functor — covers `anthill.geometry.vec_add` & friends, whose head functor
///     is the *namespace*-level `vec_add`, distinct from the spec op
///     `VectorSpace.vec_add` (so it's found by resolving `{X-namespace}.op`).
///   - **builtin**: an op mapped to a resolver builtin (`Eq.eq`, `Numeric.add`).
pub fn check_provider_operations(kb: &mut KnowledgeBase) -> Vec<super::load::LoadError> {
    use super::load::LoadError;
    let Some(provides_sym) = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") else {
        return Vec::new();
    };
    let effects_runtime = kb.try_resolve_symbol("anthill.prelude.EffectsRuntime");

    // Host-provided carriers (`Implementation.target` QNs). Their operations are
    // backed by the host artifact, not an anthill body/rule, so the provision is
    // skipped wholesale — the op-level peer of WI-343's `EffectsRuntime` skip.
    let mut host_targets: std::collections::HashSet<String> = std::collections::HashSet::new();
    if let Some(impl_sym) = kb.try_resolve_symbol("anthill.realization.Implementation") {
        for rid in kb.rules_by_functor(impl_sym) {
            if !kb.is_fact(rid) { continue; }
            let Some(named) = kb.fact_head_named_args(rid) else { continue };
            let Some(target) = get_named_arg(kb, &named, "target") else { continue };
            if let Some(qn) = impl_target_qn(kb, target) {
                host_targets.insert(qn);
            }
        }
    }

    // Op symbols that have an EQUATIONAL definition. A rule `op(args) = rhs`
    // (guarded or not) has head `eq(op(args), rhs)` — collect each LHS head
    // functor. Must walk ALL rules, not `rules_by_functor`: WI-139 unindexes
    // equational rules from the functor index (they're cite-required), so a
    // functor walk would miss every one. `is_equation` is likewise unusable —
    // it rejects guarded equations (`rule head(?s) = … :- …`), real definitions.
    let mut eq_defined: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    for rid in kb.live_rule_ids() {
        let Value::Term(head) = *kb.rule_head_value(rid) else { continue };
        if !super::load::is_equational_head(kb, head) { continue; }
        if let Term::Fn { pos_args, .. } = kb.get_term(head) {
            if let Some(&lhs) = pos_args.first() {
                if let Some(op) = head_functor_sym(kb, lhs) {
                    eq_defined.insert(op);
                }
            }
        }
    }

    // Every sort's own declared operations (one shared `SortInfo` scan).
    let own_ops: HashMap<Symbol, Vec<Symbol>> =
        super::load::sorts_and_own_ops(kb).into_iter().collect();
    // Concrete carriers (have constructors). An *abstract* carrier providing
    // `fact Spec[Self]` (e.g. `LogicalStream`, `Stream`-provides-`Iterable`) is a
    // sub-interface whose ops may stay primitives — only concrete carriers must
    // back every op (they are the runtime witnesses).
    let concrete = super::load::sorts_with_constructors(kb);

    // Snapshot the provisions before the per-op walk (which interns short names,
    // mutating `kb` — can't overlap the `rules_by_functor` borrow).
    struct Provision { carrier: Symbol, spec: Symbol }
    let mut provisions: Vec<Provision> = Vec::new();
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) { continue; }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &named, "sort_ref") else { continue };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else { continue };
        let Some(spec_view) = get_named_arg(kb, &named, "spec") else { continue };
        let Some(spec) = super::load::provides_spec_base_sym(kb, spec_view) else { continue };
        provisions.push(Provision { carrier, spec });
    }

    let mut errors = Vec::new();
    for p in &provisions {
        if Some(p.spec) == effects_runtime { continue; }
        // Abstract carrier (no constructors) → sub-interface, ops may stay
        // primitives. Only concrete carriers are checked.
        if !concrete.contains(&p.carrier) { continue; }
        let carrier_qn = kb.qualified_name_of(p.carrier).to_string();
        if host_targets.contains(&carrier_qn) { continue; }
        let carrier_ns = carrier_qn.rsplit_once('.').map(|(ns, _)| ns.to_string());
        let Some(spec_ops) = own_ops.get(&p.spec) else { continue };
        for &spec_op in spec_ops {
            let op_short = kb.qualified_name_of(spec_op)
                .rsplit('.').next().unwrap_or("").to_string();
            if op_backed(kb, p.carrier, &carrier_qn, carrier_ns.as_deref(),
                spec_op, &op_short, &eq_defined)
            {
                continue;
            }
            errors.push(LoadError::UnbackedProviderOperation {
                carrier: carrier_qn.clone(),
                spec: kb.qualified_name_of(p.spec).to_string(),
                op: op_short,
            });
        }
    }
    errors
}

/// True iff the operation `op_short` (declared by the provided spec, as
/// `spec_op`) is backed for carrier `X`. See [`check_provider_operations`] for
/// the backing kinds. Conservative: any one source suffices.
fn op_backed(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    carrier_qn: &str,
    carrier_ns: Option<&str>,
    spec_op: Symbol,
    op_short: &str,
    eq_defined: &std::collections::HashSet<Symbol>,
) -> bool {
    // Candidate definition symbols: the spec op itself, the carrier's resolved
    // op (own override or inherited spec default, via `sort_ops`), the carrier's
    // own op by QN, and the carrier-namespace op (the geometry relational-rule
    // shape, whose head functor is `{namespace}.op`, not `{Spec}.op`).
    let mut cands: SmallVec<[Symbol; 6]> = SmallVec::new();
    cands.push(spec_op);
    let short_sym = kb.intern(op_short);
    if let Some(t) = kb.sort_ops_lookup(carrier, short_sym) {
        cands.push(t);
    }
    let mut qns: SmallVec<[String; 2]> = SmallVec::new();
    qns.push(format!("{carrier_qn}.{op_short}"));
    if let Some(ns) = carrier_ns {
        qns.push(format!("{ns}.{op_short}"));
    }
    for qn in &qns {
        if let Some(s) = kb.try_resolve_symbol(qn) {
            cands.push(s);
        }
    }
    for &c in &cands {
        if op_has_runnable_body(kb, c) { return true; }
        if eq_defined.contains(&c) { return true; }
        if kb.is_builtin(c) { return true; }
        // Relational definition: a non-fact rule (`op(args, r) :- body`) whose
        // head functor is `c`.
        if kb.rules_by_functor(c).iter().any(|&r| !kb.is_fact(r)) { return true; }
    }
    false
}

/// Top functor symbol of a term head — a `Fn` functor, or a bare `Ref`/`Ident`.
fn head_functor_sym(kb: &KnowledgeBase, tid: TermId) -> Option<Symbol> {
    match kb.get_term(tid) {
        Term::Fn { functor, .. } => Some(*functor),
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// Qualified name an `Implementation.target` field points at — a `String`
/// literal (`emit_implementation_fact`'s shape) or a sort reference.
fn impl_target_qn(kb: &KnowledgeBase, target: TermId) -> Option<String> {
    match kb.get_term(target) {
        Term::Const(Literal::String(s)) => Some(s.clone()),
        Term::Ref(s) | Term::Ident(s) => Some(kb.qualified_name_of(*s).to_string()),
        Term::Fn { functor, .. } => Some(kb.qualified_name_of(*functor).to_string()),
        _ => None,
    }
}

/// Build the `requires` sub-goals for the provider-side check (WI-356).
/// Walks `spec`'s **direct** `requires`, instantiating each clause at the
/// provision's σ. Distinct from `candidate_sub_goals_owned` (the resolver's
/// impl-side template) in that σ is keyed by short **name**, not symbol: the
/// stdlib shorthand `requires Eq[T]` stores the binding value as the
/// *required* spec's own param (`Eq.T`), tied to the enclosing param only by
/// the shared short name `T`; a symbol-keyed substitution (what the resolver
/// uses, where the requires values reference the impl's *own* params) never
/// reaches it. Matching by name grounds `Eq[T] → Eq[T=Int]` from an
/// `Ordered[T=Int]` provision. A requires-param the provision leaves unbound
/// stays as its original type-param ref — the caller (`check_provider_requires`)
/// inspects each goal and only resolves the *fully concrete* ones precisely,
/// falling back to a base-level existence check otherwise (the unbound shape
/// can't be matched against ground facts — see `dispatch_values_match`). The
/// carrier never discriminates here (WI-350): these are by-binding sub-goals,
/// so `carrier` is `None`.
fn provider_requires_subgoals(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    sigma: &[(String, TermId)],
) -> Vec<SortGoal> {
    let chain = direct_requires_chain(kb, spec);
    let mut out: Vec<SortGoal> = Vec::with_capacity(chain.len());
    for entry in &chain {
        let required = entry.required_sort;
        let Some((_, entry_bindings)) = unwrap_spec_view(kb, entry.spec) else {
            continue;
        };
        let r_qn = kb.qualified_name_of(required).to_string();
        let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for (k, v) in &entry_bindings {
            if !is_type_param_binding(kb, *k, &r_qn) {
                continue;
            }
            let nv = subst_requires_value(kb, *v, sigma);
            bindings.push((*k, nv));
        }
        out.push(SortGoal { spec_sort: required, bindings, carrier: None });
    }
    out
}

/// Substitute σ into one `requires`-clause binding value (by short name);
/// leave anything σ doesn't ground unchanged. Recurses through `Fn`
/// children (`List[T]`, `Pair[A, B]`).
fn subst_requires_value(
    kb: &mut KnowledgeBase,
    v: TermId,
    sigma: &[(String, TermId)],
) -> TermId {
    match kb.get_term(v).clone() {
        Term::Ref(s) | Term::Ident(s) => map_requires_name(kb, s, v, sigma),
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            // Nullary Fn — `convert_term`'s shape for a bare name.
            map_requires_name(kb, functor, v, sigma)
        }
        Term::Fn { functor, pos_args, named_args } => {
            let mut changed = false;
            let new_pos: SmallVec<[TermId; 4]> = pos_args.iter().map(|t| {
                let nt = subst_requires_value(kb, *t, sigma);
                if nt != *t { changed = true; }
                nt
            }).collect();
            let new_named: SmallVec<[(Symbol, TermId); 2]> = named_args.iter().map(|(k, t)| {
                let nt = subst_requires_value(kb, *t, sigma);
                if nt != *t { changed = true; }
                (*k, nt)
            }).collect();
            if !changed { return v; }
            kb.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named })
        }
        _ => v,
    }
}

/// σ-ground a bare name in a `requires` value by short name; otherwise keep
/// it as-is. See [`provider_requires_subgoals`].
fn map_requires_name(
    kb: &KnowledgeBase,
    s: Symbol,
    orig: TermId,
    sigma: &[(String, TermId)],
) -> TermId {
    let short = kb.resolve_sym(s);
    sigma.iter().find(|(n, _)| n == short).map_or(orig, |(_, val)| *val)
}

/// True iff `value` mentions any abstract type-parameter anywhere in its
/// structure — a `Var`, a `Ref`/`Ident` to a `sort T = ?` param, or that
/// param as a nullary `Fn` functor (the `make_name_term` shape the loader
/// emits for a bare name, e.g. the unbound `E` left by `requires
/// Iterable[…, E = Effect]`). Used to decide whether a σ-instantiated
/// `requires` goal is concrete enough to resolve precisely against ground
/// facts, vs. falling back to the base-level existence check (WI-356).
fn contains_type_param(kb: &KnowledgeBase, value: TermId) -> bool {
    if is_type_param_value(kb, value) {
        return true;
    }
    match kb.get_term(value) {
        Term::Fn { functor, pos_args, named_args } => {
            // A `Fn` functor that is itself a param (`Fn{Effect}` nullary, or a
            // param used as a head) makes the value abstract.
            if is_sort_param_symbol(kb, *functor) {
                return true;
            }
            let pos: SmallVec<[TermId; 4]> = pos_args.clone();
            let named: SmallVec<[(Symbol, TermId); 2]> = named_args.clone();
            pos.iter().any(|t| contains_type_param(kb, *t))
                || named.iter().any(|(_, t)| contains_type_param(kb, *t))
        }
        _ => false,
    }
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

/// WI-347 — operation-override refinement check. A carrier's own operation
/// that implements/overrides a spec operation (own-op-beats-inherited, §8.7)
/// must REFINE the spec op: effects no wider, precondition no stronger,
/// postcondition no weaker. The soundness twin of the provider/call-site
/// checks — a caller programs against the SPEC's contract, so an override that
/// raises an effect the spec doesn't cover (or strengthens a precondition /
/// weakens a postcondition) would surprise it.
///
/// EFFECTS: `∀ ie ∈ impl_effects. ∃ se ∈ spec_effects[σ]. ie <: se`
/// (`types_compatible`, the relation `spec-instance-dispatch.md §"Effect
/// compatibility"` specifies). Enforced only when the comparison is
/// *confident* — every impl and σ-substituted spec effect is a ground
/// `Value::Term` (no unbound type-param, no `denoted` `Value::Node`).
/// Otherwise the op's effect check is skipped (fail-open): parametric
/// (`effects E`) / denoted (`Modify[c]`) effect refinement is deferred, which
/// keeps the stdlib's polymorphic-effect providers from false-positiving while
/// still catching a ground effect-widening (the doc's `Network`-vs-`Error`
/// case). Contract (`requires`/`ensures`) refinement is added on this same
/// pass next.
pub fn check_override_refinement(kb: &mut KnowledgeBase) -> Vec<super::load::LoadError> {
    use super::load::LoadError;
    let Some(provides_sym) = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") else {
        return Vec::new();
    };
    // Own declared ops per sort — owned snapshot, no `kb` borrow held in the loop.
    let own: std::collections::HashMap<Symbol, Vec<Symbol>> =
        super::load::sorts_and_own_ops(kb).into_iter().collect();
    let short = |kb: &KnowledgeBase, s: Symbol| -> String {
        kb.qualified_name_of(s).rsplit('.').next().unwrap_or("").to_string()
    };

    // Snapshot provisions before the (mutating) refinement walk:
    // (carrier, spec base, σ = spec type-param symbol → provision binding value).
    struct Prov { carrier: Symbol, spec: Symbol, sigma: Vec<(Symbol, TermId)> }
    let mut provs: Vec<Prov> = Vec::new();
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) { continue; }
        // A value-fact SortProvidesInfo (denoted-bearing spec) is skipped from
        // override-refinement coverage; occurrence-based coverage is gated
        // effect-expressions-as-types work (avoid the term-only `rule_head` panic).
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &named, "sort_ref") else { continue };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else { continue };
        let Some(spec_view) = get_named_arg(kb, &named, "spec") else { continue };
        let Some((spec_base, _)) = unwrap_spec_view(kb, spec_view) else { continue };
        let spec_qn = kb.qualified_name_of(spec_base).to_string();
        let mut sigma: Vec<(Symbol, TermId)> = Vec::new();
        if let Term::Fn { named_args, .. } = kb.get_term(spec_view).clone() {
            for (k, v) in &named_args {
                if is_type_param_binding(kb, *k, &spec_qn) {
                    sigma.push((*k, *v));
                }
            }
        }
        provs.push(Prov { carrier, spec: spec_base, sigma });
    }

    let mut errors = Vec::new();
    for p in &provs {
        let (Some(spec_ops), Some(carrier_ops)) = (own.get(&p.spec), own.get(&p.carrier))
        else { continue };
        for &spec_op in spec_ops {
            let sn = short(kb, spec_op);
            // The carrier's own op of the same short name is its override/impl.
            let Some(&impl_op) = carrier_ops.iter().find(|&&o| short(kb, o) == sn)
            else { continue };
            let Some(spec_info) = super::op_info::lookup_operation_info(kb, spec_op) else { continue };
            let Some(impl_info) = super::op_info::lookup_operation_info(kb, impl_op) else { continue };

            // ── effects-⊆ (confident-ground only; fail-open otherwise) ──────
            let spec_effs: Vec<Value> = spec_info.effects.iter()
                .map(|se| sigma_subst_effect(kb, se, &p.sigma))
                .collect();
            let ground = |kb: &KnowledgeBase, e: &Value|
                matches!(e, Value::Term(t) if !contains_type_param(kb, *t));
            let confident = impl_info.effects.iter().all(|e| ground(kb, e))
                && spec_effs.iter().all(|e| ground(kb, e));
            if confident {
                for ie in &impl_info.effects {
                    let covered = spec_effs.iter().any(|se| {
                        let mut subst = Substitution::new();
                        types_compatible(kb, &mut subst, ie, se)
                    });
                    if !covered {
                        errors.push(LoadError::IncompatibleOverride {
                            carrier: kb.qualified_name_of(p.carrier).to_string(),
                            spec: kb.qualified_name_of(p.spec).to_string(),
                            op: sn.clone(),
                            reason: format!(
                                "the override declares effect `{}`, which is not covered by \
                                 any effect the spec operation declares (effects must not widen)",
                                type_display_name_value(kb, ie)),
                        });
                    }
                }
            }

            // ── contract refinement (requires/ensures, structural subset) ───
            // Compare in the spec op's param vocabulary: align the impl op's
            // params to the spec's positionally (contracts are predicates over
            // op params, not the spec type-param, so σ is not applied). The
            // loader's auto-`EffectsRuntime` requires are filtered out — those
            // are the effects check's concern. Conservative: clauses match by
            // carrier-agnostic structural equality (`views_structurally_equal`;
            // for the ground clauses here == hash-consed `TermId` equality); a
            // logically-equivalent but syntactically-different refinement is not
            // yet recognized (a future SMT-backed entailment check would subsume
            // this).
            let align: Vec<(Symbol, TermId)> = {
                let mut a = Vec::new();
                for ((ip, _), (sp, _)) in impl_info.params.iter().zip(spec_info.params.iter()) {
                    if ip != sp {
                        let sp_ref = kb.alloc(Term::Ref(*sp));
                        a.push((*ip, sp_ref));
                    }
                }
                a
            };
            // precondition no-stronger: every impl precondition must be one the
            // spec also requires (the override demands no more than the spec).
            let spec_pre = user_precondition_clauses(kb, &spec_info.requires);
            for ic in user_precondition_clauses(kb, &impl_info.requires) {
                let ic = substitute_clause(kb, &ic, &align);
                if !spec_pre.iter().any(|sp| views_structurally_equal(kb, sp, &ic)) {
                    errors.push(LoadError::IncompatibleOverride {
                        carrier: kb.qualified_name_of(p.carrier).to_string(),
                        spec: kb.qualified_name_of(p.spec).to_string(),
                        op: sn.clone(),
                        reason: "it strengthens the precondition — the override `requires` a \
                                 condition the spec operation does not".to_string(),
                    });
                }
            }
            // postcondition no-weaker: every spec postcondition must be one the
            // impl also ensures (the override promises no less than the spec).
            let impl_post: Vec<Value> = impl_info.ensures.iter()
                .map(|c| substitute_clause(kb, c, &align))
                .collect();
            for sc in &spec_info.ensures {
                if !impl_post.iter().any(|ip| views_structurally_equal(kb, ip, sc)) {
                    errors.push(LoadError::IncompatibleOverride {
                        carrier: kb.qualified_name_of(p.carrier).to_string(),
                        spec: kb.qualified_name_of(p.spec).to_string(),
                        op: sn.clone(),
                        reason: "it weakens the postcondition — the override does not `ensure` a \
                                 condition the spec operation promises".to_string(),
                    });
                }
            }
        }
    }
    errors
}

/// User precondition clauses of an operation — its `requires` field minus the
/// loader's auto-inferred `EffectsRuntime[Effects=E]` entries (WI-320), which
/// track the effect row, not a caller-facing precondition. WI-347. WI-366 B2:
/// carrier-agnostic `Value` clauses (read through `TermView`).
fn user_precondition_clauses(kb: &KnowledgeBase, clauses: &[Value]) -> Vec<Value> {
    clauses.iter().filter(|c| !is_effects_runtime_clause(kb, c)).cloned().collect()
}

/// Is `clause` an auto-inferred `EffectsRuntime[Effects=…]` requires clause?
/// Such clauses are `Fn{ functor: EffectsRuntime, … }` (see
/// `infer_effects_row_requires`); they ride in the `requires` list but are not
/// user preconditions, so the override contract check skips them. WI-366 B2: the
/// functor is read through [`TermView`] so the check is carrier-agnostic (a
/// denoted-bearing user precondition rides as a `Value::Node`).
fn is_effects_runtime_clause(kb: &KnowledgeBase, clause: &Value) -> bool {
    matches!(clause.head(kb),
        ViewHead::Functor { functor: Some(f), .. }
            if kb.qualified_name_of(f) == "anthill.prelude.EffectsRuntime")
}

/// Apply a spec↔impl param-alignment `subst` to a carrier-agnostic
/// precondition/postcondition clause for the override-refinement comparison
/// (WI-366 B2). A ground `Value::Term` clause is rewritten via
/// [`substitute_impl_params_alloc`]; a denoted-bearing `Value::Node` clause is
/// returned verbatim — substituting into the occurrence is deferred parametric
/// handling, so the structural comparison treats it as un-rewritten
/// (conservative: a denoted precondition that needed alignment would not be
/// recognized as covered, never falsely accepted).
fn substitute_clause(kb: &mut KnowledgeBase, clause: &Value, subst: &[(Symbol, TermId)]) -> Value {
    match clause {
        Value::Term(t) => Value::Term(substitute_impl_params_alloc(kb, *t, subst)),
        other => other.clone(),
    }
}

/// Apply a provision's σ (spec param symbol → binding) to a spec operation's
/// effect label. A ground `Value::Term` is rewritten via
/// [`substitute_impl_params_alloc`]; a `denoted` `Value::Node` (e.g.
/// `Modify[c]`) is returned verbatim — its σ-instantiation is part of the
/// deferred parametric-effect handling, and the caller's confidence gate skips
/// any op whose effects stay non-ground.
fn sigma_subst_effect(kb: &mut KnowledgeBase, eff: &Value, sigma: &[(Symbol, TermId)]) -> Value {
    match eff {
        Value::Term(t) if !sigma.is_empty() => Value::Term(substitute_impl_params_alloc(kb, *t, sigma)),
        other => other.clone(),
    }
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
    kb: &mut KnowledgeBase,
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
    if let Some(sym) = extract_sort_ref_sym(kb, &TermIdView(t)) {
        return kb.qualified_name_of(sym).to_string();
    }
    match kb.get_term(t) {
        // bare `Ref` is named above via `extract_sort_ref_sym` (WI-361); a still-
        // unresolved `Ident` falls here.
        Term::Ident(s) => kb.qualified_name_of(*s).to_string(),
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
    carrier: Option<Symbol>,
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
        match subst.resolve_as_value(vid) {
            Some(Value::Term(val)) => {
                let val = *val;
                let short_intern = kb.try_resolve_symbol(&short).unwrap_or_else(|| {
                    // Spec param's *short* name (e.g. "T") may not be registered
                    // as a top-level symbol; fall back to its qualified form.
                    short_sym
                });
                // WI-361: a binding value is already canonical (`Ref(S)` / `Fn{S, named}`)
                // — no `parameterized(base, bindings)` wrapper left to unwrap.
                bindings.push((short_intern, val));
            }
            // A denoted `Value::Node` binding can't ride in the `TermId`-keyed
            // `SortGoal.bindings`; carrying it is WI-348 Phase C. Omitting it is
            // sound (the dispatch goal sees one fewer constraint — a safe
            // over-approximation), but flag loudly in debug.
            Some(other) => debug_assert!(
                false,
                "WI-348: denoted {} in SortGoal bindings — carrier-agnostic SortGoal is Phase C",
                other.type_name(),
            ),
            None => {}
        }
    }
    SortGoal {
        spec_sort,
        bindings,
        carrier,
    }
}


/// WI-350 — classify a spec op's receiver at a call site to drive
/// carrier-aware dispatch. Finds the op's *self-receiver* parameter — the
/// first one declared with the spec sort itself (`head(s: Stream)`; vs
/// `Eq.eq(a: T, b: T)`, whose params are typed with the spec's type-
/// parameter `T`) — and reads that argument's inferred base sort.
///
/// - No self-receiver parameter ⇒ [`ReceiverCarrier::NotApplicable`]: the
///   carrier is a type-parameter binding, already pinned by the subst.
/// - Receiver's base sort is the spec sort (`s : Stream[T]`) or its type
///   is unresolved ⇒ [`ReceiverCarrier::Abstract`]: no concrete impl.
/// - Receiver's base sort is a concrete carrier (`s : List[Int]` → `List`)
///   ⇒ [`ReceiverCarrier::Concrete`].
fn receiver_carrier(
    kb: &KnowledgeBase,
    op: &OperationInfoFull,
    spec_sort: Symbol,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> ReceiverCarrier {
    let Some(idx) = self_receiver_param_index(kb, &op.params, spec_sort) else {
        return ReceiverCarrier::NotApplicable;
    };
    let param_name = op.params[idx].0;
    // The argument may be supplied positionally (matched by declaration
    // index, as `check_apply_iter`'s unify loop does) or by name.
    let arg_ty: Option<&Value> = pos_results
        .get(idx)
        .and_then(|r| r.as_ref().ok())
        .map(|r| &r.ty)
        .or_else(|| {
            named_args
                .iter()
                .position(|(n, _)| *n == param_name)
                .and_then(|j| named_results.get(j))
                .and_then(|r| r.as_ref().ok())
                .map(|r| &r.ty)
        });
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    match arg_ty.and_then(|v| carrier_sort_of_value(kb, v)) {
        // A concrete carrier distinct from the spec sort itself. Store the
        // canonical sort symbol so the candidate filter (which canonicalizes
        // `impl_sort`) compares like-for-like.
        Some(base) if kb.canonical_sort_sym(base) != spec_canon => {
            ReceiverCarrier::Concrete(kb.canonical_sort_sym(base))
        }
        // Base == spec sort (abstract spec value) or unresolved type: no
        // concrete impl is pinnable.
        _ => ReceiverCarrier::Abstract,
    }
}

/// WI-350 — index of a spec op's *self-receiver* parameter: the first one
/// declared with the spec sort itself (`head(s: Stream)`), as opposed to a
/// type-parameter-carrier parameter (`Eq.eq(a: T, b: T)`, whose type is the
/// spec's own type-parameter). `None` when the op has no self-receiver
/// parameter. Shared by the typer's [`receiver_carrier`] and the
/// interpreter's value-directed dispatch so the two never disagree about
/// which argument names the carrier. Compares canonical sort symbols (the
/// same logical sort may be interned under several `Symbol`s).
pub(crate) fn self_receiver_param_index(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    spec_sort: Symbol,
) -> Option<usize> {
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    params.iter().position(|(_, pty)| {
        // WI-341 Stage A: carrier-agnostic. A `Value::Node` (denoted-bearing
        // callback) param type is never a spec carrier sort → `None`.
        carrier_sort_of_value(kb, pty).map(|s| kb.canonical_sort_sym(s)) == Some(spec_canon)
    })
}

/// WI-350 — the base sort symbol of a value standing in *type* position
/// (an argument's inferred `TypeResult.ty`). Type results are carried as
/// `Value::Term` of a typer-reflect Type shape, read by [`sort_functor_of`].
fn carrier_sort_of_value(kb: &KnowledgeBase, v: &Value) -> Option<Symbol> {
    sort_functor_of(kb, v.as_term()?)
}

/// WI-365 — the parametric sort a self-receiver op belongs to, whether or not
/// it has a default body. [`lookup_spec_op_dispatch`] returns the parent only
/// for body-LESS spec ops (the dispatch candidates); a default-bodied spec op
/// (`Stream.collect`) is a normal op for dispatch but still carries the sort's
/// element / effect parameters, which must be grounded from the carrier when
/// the op is consumed on a concrete provider. `None` unless the parent is a
/// parametric sort AND the op has a self-receiver parameter (one typed as the
/// sort itself, e.g. `s: Stream`) — the same shape [`receiver_carrier`] keys on.
fn self_receiver_spec_sort(
    kb: &KnowledgeBase,
    op: &OperationInfoFull,
    fn_sym: Symbol,
) -> Option<Symbol> {
    let op_qn = kb.qualified_name_of(fn_sym);
    let (parent_qn, _short) = op_qn.rsplit_once('.')?;
    let parent_sym = kb.try_resolve_symbol(parent_qn)?;
    if kb.type_params_of_sort(parent_sym).is_empty() {
        return None;
    }
    self_receiver_param_index(kb, &op.params, parent_sym)?;
    Some(parent_sym)
}

/// WI-357 — bind a self-receiver spec op's own type parameters from the
/// concrete receiver carrier, so a dispatched call threads the element
/// type. `Stream.splitFirst(s: Stream) -> Option[T = Pair[A = T, …]]`
/// invoked on `s : List[Int]` unifies the argument against the *bare*
/// `Stream` parameter, which binds none of the spec's own type
/// parameters (`Stream.T`). The unbound `Stream.T` then both (a) leaves
/// the return `Option[T = Pair[A = ?_, …]]` — a destructured `pair(h, _)`
/// gets `h : ?_` — and (b) makes the dispatch goal abstract, so no impl
/// matches and the typer demands a `requires Stream[…]` on the caller.
///
/// Recover the spec params from the carrier's provider fact: `List`
/// provides `fact Stream[T = T]`, so a `List[Int]` viewed as a `Stream`
/// has `Stream.T = List.T = Int`. The element value is read by SHORT NAME
/// from the receiver's own type arguments — robust to whether the
/// provider fact stores the carrier param as a `Var` / `Ref` / nullary
/// `Fn`. Returns true iff at least one spec parameter was bound (the
/// caller then re-walks the return type through the updated subst).
fn bind_spec_params_from_carrier(
    kb: &KnowledgeBase,
    subst: &mut Substitution,
    op: &OperationInfoFull,
    spec_sort: Symbol,
    carrier_sym: Symbol,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> bool {
    // The self-receiver argument's inferred type (e.g. `List[T = Int]`).
    let Some(idx) = self_receiver_param_index(kb, &op.params, spec_sort) else {
        return false;
    };
    let param_name = op.params[idx].0;
    let recv_ty = pos_results
        .get(idx)
        .and_then(|r| r.as_ref().ok())
        .and_then(|r| r.ty.as_term())
        .or_else(|| {
            named_args
                .iter()
                .position(|(n, _)| *n == param_name)
                .and_then(|j| named_results.get(j))
                .and_then(|r| r.as_ref().ok())
                .and_then(|r| r.ty.as_term())
        });
    let Some(recv_ty) = recv_ty else {
        return false;
    };

    // The receiver's own type arguments, keyed by carrier-param short name.
    let recv_bindings = parameterized_short_bindings(kb, recv_ty);
    if recv_bindings.is_empty() {
        return false;
    }

    // The carrier's provider fact maps each spec parameter to a
    // carrier-side value (`fact Stream[T = T]` ⇒ spec `T` ↦ carrier `T`).
    let Some(view_bindings) = provider_spec_view_bindings(kb, carrier_sym, spec_sort) else {
        return false;
    };

    // WI-393: the CONSUMING op's self-receiver param type maps each spec
    // parameter (by short name) to the op's OWN type-param var — `collect[Elem,
    // Eff](s: Stream[T = Elem, E = Eff])` gives {T ↦ Elem, E ↦ Eff}. An op
    // rewritten to explicit `[Elem, Eff]` params (042) no longer uses the spec
    // sort's own `Stream.T` / `Stream.E`, so binding only those (below) leaves the
    // op's `Elem` / `Eff` free → element `?_` / `Eff unconstrained` at a cross-sort
    // consumption site. Bind the op's params from the same carrier view. Empty for
    // a bare-`Stream` param (the pre-rewrite ops) — then only the spec sort's
    // params bind, exactly as before.
    let op_param_map: Vec<(String, Value)> = match extract_type(kb, &op.params[idx].1) {
        TypeExtractor::Parameterized { bindings, .. } => bindings
            .into_iter()
            .map(|(p, v)| (short_name_of(kb.resolve_sym(p)).to_string(), v))
            .collect(),
        _ => Vec::new(),
    };

    let mut any = false;
    for (spec_param_sym, carrier_value) in view_bindings {
        let spec_short = short_name_of(kb.resolve_sym(spec_param_sym)).to_string();
        let is_ref = typaram_ref_short_name(kb, carrier_value);
        // The carrier-side CONCRETE value for this spec parameter, as a ground
        // hash-consed term:
        //  - a type-param ref (`Stream.T` ↦ `List.T`): the receiver's binding for
        //    that carrier param (`List[T = Int]` ⇒ `Int`). Threaded even if itself
        //    a var (an unbound receiver element legitimately aliases the op param).
        //  - a GROUND provider row (`Stream.E` ↦ `{}`, the WRITTEN pure row of
        //    `List provides Stream[E = {}]`): the value itself. The pre-WI-393
        //    code `continue`-skipped this (only a ref mapped), dropping the `{}`
        //    so a cross-sort `collect`'s `Eff` never grounded.
        // The `type_value_is_ground` guard on the non-ref arm is load-bearing: a
        // non-ref provider binding that still mentions the carrier's OWN params
        // (`provides Stream[T = Pair[A = C.T, B = C.T]]`) is not ground, and
        // binding it verbatim would pin the op param to a carrier-relative `?_`
        // (the receiver's actual argument is never substituted in) — silently
        // wrong. Skip it: the op param stays unbound and surfaces a LOUD
        // `unconstrained` instead. (Threading such a compound through
        // `recv_bindings` is future work — see WI-380 follow-ups.)
        let concrete: Option<TermId> = match &is_ref {
            Some(carrier_short) => recv_bindings.iter().find(|e| e.0 == *carrier_short).map(|e| e.1),
            None if type_value_is_ground(kb, carrier_value) => Some(carrier_value),
            None => None,
        };
        let Some(concrete) = concrete else { continue };

        // (a) The spec sort's OWN alias var — kept for the WI-325 abstract-
        //     coverage check on a dispatched body-less op (it resolves the spec
        //     param's alias var in the subst, and the dispatch goal is built from
        //     it). Only a type-param-ref binding (the element); a written effect
        //     row is not bound onto the spec alias (effects aren't expressible
        //     there — WI-301; the coverage check reads the provider view's
        //     groundness directly for that). Only fill a genuinely-empty slot:
        //     `bind_term` flags a CONTRADICTION against a differing existing
        //     binding (it does not rebind), and an alias whose root is bound
        //     resolves anyway.
        if is_ref.is_some() {
            if let Some(spec_vid) = type_param_vid_in_sort(kb, spec_sort, spec_param_sym) {
                if subst.resolve_as_value(spec_vid).is_none() && !occurs_in(kb, spec_vid, concrete) {
                    subst.bind_term(spec_vid, concrete);
                    any = true;
                }
            }
        }

        // (b) The consuming op's OWN type-param var (WI-393), matched by short
        //     name through `op_param_map`. `concrete` is a ground hash-consed term
        //     (the receiver's element, or a ground provider row like `{}`); bind
        //     it occurs-checked into the op's own `Elem` / `Eff`. Same empty-slot
        //     guard as (a).
        if let Some((_, op_param_val)) = op_param_map.iter().find(|(s, _)| *s == spec_short) {
            if let Some(op_vid) = resolved_var(kb, op_param_val) {
                if subst.resolve_as_value(op_vid).is_none() && !occurs_in(kb, op_vid, concrete) {
                    subst.bind_term(op_vid, concrete);
                    any = true;
                }
            }
        }
    }
    any
}

/// A `parameterized` type's bindings as `(carrier-param short name, value)` pairs
/// — the receiver-side reader for [`bind_spec_params_from_carrier`]. Reads via
/// [`extract_type`], re-keys by short name (the form `bind_spec_params_from_carrier`
/// matches against), and keeps only `Value::Term` values (a parameterized type's
/// bindings are ground terms).
fn parameterized_short_bindings(kb: &KnowledgeBase, ty: TermId) -> Vec<(String, TermId)> {
    // WI-361: a parameterized type is the term backing `Fn{S, named}`
    // (`List[T = Int]` = `Fn{List, named:[(T, Int)]}`).
    let TypeExtractor::Parameterized { bindings, .. } = extract_type(kb, &TermIdView(ty)) else {
        return Vec::new();
    };
    bindings
        .into_iter()
        .filter_map(|(param, value)| {
            value
                .as_term()
                .map(|t| (short_name_of(kb.resolve_sym(param)).to_string(), t))
        })
        .collect()
}

/// The spec-view bindings of the `SortProvidesInfo` fact recording that
/// `carrier_sym` provides `spec_sort` — `(spec param symbol, carrier-side
/// value)` pairs (`fact Stream[T = T]` on `List` ⇒ `[(Stream.T, List.T)]`).
/// First matching provider wins. `None` when the carrier declares no such
/// provision.
fn provider_spec_view_bindings(
    kb: &KnowledgeBase,
    carrier_sym: Symbol,
    spec_sort: Symbol,
) -> Option<SmallVec<[(Symbol, TermId); 2]>> {
    let provides_sym = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo")?;
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        // A value-fact SortProvidesInfo (denoted-bearing spec) is skipped;
        // occurrence-based provides lookup is gated effect-expressions-as-types
        // work (avoid the term-only `rule_head` panic on a value head).
        let Some(head_named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &head_named, "sort_ref") else {
            continue;
        };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else {
            continue;
        };
        if kb.canonical_sort_sym(carrier) != kb.canonical_sort_sym(carrier_sym) {
            continue;
        }
        let Some(spec_t) = get_named_arg(kb, &head_named, "spec") else {
            continue;
        };
        let Some((base, bindings)) = unwrap_spec_view(kb, spec_t) else {
            continue;
        };
        // Canonicalize both sides — the spec base in the provider fact's
        // `SortView` is resolved in the carrier's import scope and may be a
        // different `Symbol` id than `spec_sort` (resolved in the caller's
        // scope) even for the same logical sort. Matches the carrier compare
        // above; a raw `==` would silently no-op this binding.
        if kb.canonical_sort_sym(base) == kb.canonical_sort_sym(spec_sort) {
            return Some(bindings);
        }
    }
    None
}

/// WI-357 — true iff an effect label is still an unresolved type/row
/// variable (a bare `?_`). Used to close a spec op's polymorphic effect
/// row when it dispatches to a concrete carrier whose provider fact does
/// not (yet) bind the effect parameter.
fn effect_is_unresolved_var(kb: &KnowledgeBase, e: &Value) -> bool {
    match e {
        Value::Term(t) => matches!(kb.get_term(*t), Term::Var(_)),
        _ => false,
    }
}

/// WI-365 — the EFFECT dual of WI-357's element threading. When a body-less
/// self-receiver spec op (`Box.peek`, polymorphic `effects Effect`) dispatches
/// to a concrete impl that OVERRIDES it with a genuine effect
/// (`MutBox.peek effects Modify[b]`), the spec op's effect ROW must be GROUNDED
/// to the impl's real effects at the consumption site — not dropped as if the
/// carrier were pure. The pre-dispatch effect-close drops the still-unresolved
/// row var (correct for a pure provider / host builtin — a provider fact cannot
/// bind an effect parameter, WI-301); once dispatch resolves the concrete impl,
/// this re-derives its effects so a pure consumer is rejected exactly as a
/// DIRECT call to the impl op is.
///
/// Each impl effect is param-substituted (the IMPL op's params → the call's
/// argument vars) so `Modify[b]` re-keys to the caller's actual argument — the
/// same rewrite the spec op's own effects get at the call site
/// (`substitute_ref_syms_value`, WI-342 E2 re-keys a `Value::Node` label's
/// `Ref` spine). It is then walked through the per-call subst and filtered to
/// CONCRETE effects: an impl whose own effect row is itself an unbound var is
/// effectively pure here, so it contributes nothing — keeping the
/// `List`-as-`Stream` pure path unchanged. Returns `[]` for a pure override
/// (empty or wholly-unresolved effects).
///
/// The map keys on the IMPL op's parameter names (the impl's effects reference
/// the impl's own params, which may be renamed vs the spec op's). Parameters
/// align positionally across a spec op and its override (the override-refinement
/// check enforces this) and the call was matched against the SPEC op, so the
/// arg for impl param `i` is the positional arg at `i`, or — for a named call —
/// the arg named with the SPEC op's param[i] name (`spec_params`).
fn dispatched_impl_effects(
    kb: &mut KnowledgeBase,
    impl_op_sym: Symbol,
    spec_params: &[(Symbol, Value)],
    subst: &Substitution,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Vec<Value> {
    let Some(impl_op) = lookup_operation_info_full(kb, impl_op_sym) else {
        return Vec::new();
    };
    if impl_op.effects.is_empty() {
        return Vec::new();
    }
    let mut param_to_arg: HashMap<Symbol, Symbol> = HashMap::new();
    for (i, (impl_param_sym, _)) in impl_op.params.iter().enumerate() {
        // Positional arg at this index, else the named arg carrying the spec
        // op's param[i] name (the caller names spec-op params, not impl params).
        let mut arg_sym = pos_args.get(i).and_then(extract_var_ref_sym_node);
        if arg_sym.is_none() {
            if let Some((spec_name, _)) = spec_params.get(i) {
                for (n, occ) in named_args.iter() {
                    if n == spec_name {
                        arg_sym = extract_var_ref_sym_node(occ);
                        break;
                    }
                }
            }
        }
        if let Some(s) = arg_sym {
            param_to_arg.insert(*impl_param_sym, s);
        }
    }
    let mut out: Vec<Value> = Vec::new();
    for e in &impl_op.effects {
        let sub = if param_to_arg.is_empty() {
            e.clone()
        } else {
            substitute_ref_syms_value(kb, e, &param_to_arg)
        };
        let walked = walk_type_deep_value(kb, subst, &sub);
        if !effect_is_unresolved_var(kb, &walked) {
            out.push(walked);
        }
    }
    out
}

/// The short name of a type-parameter reference as a provider fact stores
/// it in a spec view — tolerant of every shape a bare param name takes
/// (`sort_ref(name: S)` / `Ref` / `Ident` / a nullary `Fn` / `Var`).
fn typaram_ref_short_name(kb: &KnowledgeBase, tid: TermId) -> Option<String> {
    if let Some(s) = extract_sort_ref_sym(kb, &TermIdView(tid)) {
        return Some(short_name_of(kb.resolve_sym(s)).to_string());
    }
    match kb.get_term(tid) {
        // bare `Ref` handled above via `extract_sort_ref_sym` (WI-361); `Ident` here.
        Term::Ident(s) => Some(short_name_of(kb.resolve_sym(*s)).to_string()),
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            Some(short_name_of(kb.resolve_sym(*functor)).to_string())
        }
        Term::Var(Var::Global(v)) => Some(short_name_of(kb.resolve_sym(v.name())).to_string()),
        _ => None,
    }
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
    // Compat entry — no call-site receiver, so no carrier discrimination.
    dispatch_spec_op_cached(kb, subst, spec_sort, op_short_sym, enclosing_requires, None)
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
    carrier: Option<Symbol>,
) -> (DispatchOutcome, Option<ResolvedRequiresNode>) {
    // Direct defer trigger: a spec that is a *direct* `requires` of the
    // enclosing sort (i.e. present in `enclosing_requires`) is dispatched
    // at runtime from the threaded requirement value. The typer arm
    // (WI-239) handles transitive (nested) reachability separately via
    // `find_requires_location` before reaching here, so this trigger only
    // needs the direct chain. The compat API (`find_unique_impl_op`,
    // exercised by the WI-221 tests with synthetic chains) relies on it.
    if !enclosing_requires.is_empty()
        && find_requires_slot(kb, subst, spec_sort, enclosing_requires).is_some()
    {
        return (DispatchOutcome::Deferred, None);
    }
    // WI-350: `carrier` rides inside the goal so it participates in the
    // resolve-cache key (a `List` call and a `LogicalStream` call on the
    // same `Stream[T = Int]` goal must not share a memo entry) and reaches
    // `collect_provides_candidates`' impl-sort filter.
    let goal = sort_goal_from_subst(kb, subst, spec_sort, carrier);
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
    kb: &mut KnowledgeBase,
    per_call_value: TermId,
    candidate_value: TermId,
) -> bool {
    // A universally-quantified candidate matches any per-call value. The
    // fact-loading path stores type-params as `Term::Ref`, the op-signature
    // path as `Term::Var`; both shapes mean "for any T."
    if is_type_param_value(kb, candidate_value) {
        return true;
    }
    // WI-335: dispatch decisions are independent of each other (dispatch
    // values are typically nominal sort_refs; row reasoning is rare).
    // Each call gets a fresh scratch substitution.
    let mut subst = Substitution::new();
    if types_lesseq(kb, &mut subst, per_call_value, candidate_value) {
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
        // WI-359: a bare param name also surfaces as a nullary `Fn` (the
        // `make_name_term` shape — e.g. an enclosing sort's open param
        // captured into a `requires` SortView). Treat `Fn{param}` like
        // `Ref(param)` so defer-to-requirement matching and candidate
        // leniency see it as the wildcard it is.
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            is_sort_param_symbol(kb, *functor)
        }
        _ => false,
    }
}

/// WI-387 (FIX 3) — true iff `tid` is a fully-ground type value: no logic var
/// and no sort-parameter reference ANYWHERE in its structure. The recursive
/// dual of [`is_type_param_value`] (which tests only the head). A carrier's
/// provider-fact binding that is ground (the written empty row `{}` for a pure
/// carrier's `Stream.E`) COVERS its spec param in the abstract/requires-coverage
/// check, whereas a binding that mentions a type-param (`Stream.T ↦ List.T`, or
/// a nested `C = List[T]`) stays abstract and still demands a `requires`.
fn type_value_is_ground(kb: &KnowledgeBase, tid: TermId) -> bool {
    match kb.get_term(tid) {
        Term::Var(_) => false,
        Term::Ref(sym) | Term::Ident(sym) => !is_sort_param_symbol(kb, *sym),
        Term::Fn { functor, pos_args, named_args } => {
            !is_sort_param_symbol(kb, *functor)
                && pos_args.iter().all(|a| type_value_is_ground(kb, *a))
                && named_args.iter().all(|(_, a)| type_value_is_ground(kb, *a))
        }
        Term::Const(_) | Term::Bottom => true,
        Term::ParseAux(_) => false,
    }
}

/// Extract the underlying sort symbol from a term in any of the
/// shapes a binding value may take: `sort_ref(name: Ref(X))`,
/// bare `Ref(X)` / `Ident(X)`, or a nullary `Fn { functor: X, … }`.
fn sort_sym_of_term(kb: &KnowledgeBase, t: TermId) -> Option<Symbol> {
    if let Some(s) = extract_sort_ref_sym(kb, &TermIdView(t)) {
        return Some(s);
    }
    match kb.get_term(t) {
        // bare `Ref` handled above via `extract_sort_ref_sym` (WI-361); `Ident` here.
        Term::Ident(s) => Some(*s),
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

    // Collect (field label, result) eagerly — interning the positional `_i`
    // labels here releases the `kb` borrow before the `named_tuple_value` build
    // below also needs `&mut kb` (WI-342).
    // WI-355: 1-based positional names `_1`, `_2`, … (spec §4.5) so the tuple
    // value's type unifies (by name) against a tuple-typed / arrow param.
    let mut labeled: Vec<(Symbol, &TypeResult)> = Vec::new();
    for (i, r) in pos_results.iter().enumerate() {
        labeled.push((kb.intern(&format!("_{}", i + 1)), r.as_ref().expect("aggregator")));
    }
    for ((name, _), r) in named_args.iter().zip(named_results.iter()) {
        labeled.push((*name, r.as_ref().expect("aggregator")));
    }

    let mut effects: Vec<Value> = Vec::new();
    // WI-342: carrier-agnostic field types (carry a `Value::Node` field).
    let mut tuple_fields: Vec<(Symbol, Value)> = Vec::new();
    for (label, r) in labeled {
        tuple_fields.push((label, r.ty.clone()));
        effects = merge_effects(&effects, &r.effects);
    }
    let tuple_ty = named_tuple_value(kb, &tuple_fields, occ.span, occ.owner);
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
    expected: Option<Value>,
    occ: &Rc<NodeOccurrence>,
    base_name: &str,
) -> Result<TypeResult, TypeError> {
    // Defensive (the constructor checker already surfaced arg errors before
    // routing here): never `.expect` an `Err` element result.
    collect_arg_errors(pos_results.iter())?;
    // WI-342: carrier-agnostic element type — a `Value::Node` element (an
    // effectful lambda) is carried into the `List`/`Set` parameterization.
    let mut element_type: Option<Value> =
        expected.and_then(|e| extract_type_param(kb, &e, "T"));
    let mut effects: Vec<Value> = Vec::new();
    for r in pos_results {
        let r = r.as_ref().expect("aggregator");
        if element_type.is_none() {
            element_type = Some(r.ty.clone());
        }
        effects = merge_effects(&effects, &r.effects);
    }
    let t_val = element_type.unwrap_or_else(|| {
        let fresh = kb.intern("?T");
        Value::Term(kb.make_type_var(fresh))
    });
    let base = kb.make_sort_ref_by_name(base_name);
    let t_sym = kb.intern("T");
    let seq_type = parameterized_value(kb, base, &[(t_sym, t_val)], occ.span, occ.owner);
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
    expected: Option<Value>,
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
    // WI-393: QUALIFIED base names — a bare `"List"`/`"Set"` interns a symbol
    // whose qualified name is itself, which `canonical_sort_sym` never folds onto
    // the prelude sort, so a literal consumed as a Stream (`collect([1,2,3])`)
    // missed the carrier provider lookup. See the `ListLit` build frame.
    if kb.qualified_name_of(ctor_sym) == "anthill.reflect.ListLiteral" {
        return check_seq_literal_constructor(kb, env, pos_results, expected, occ, "anthill.prelude.List");
    }
    if kb.qualified_name_of(ctor_sym) == "anthill.reflect.SetLiteral" {
        return check_seq_literal_constructor(kb, env, pos_results, expected, occ, "anthill.prelude.Set");
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
    //
    // WI-379 note: unlike `check_apply_iter`, this expected-seeding is NOT
    // safely movable below the field loops. The constructor builds its result
    // type by reading each param Var's binding out of `subst` (below), and
    // DROPS a param whose Var resolves to `None`. Seeding `expected` first binds
    // the params to concrete values so they survive the build; with fields
    // first, a field that is an unbound element var aliases the param to an
    // unbound var (→ `None` → dropped), e.g. `pair(h, t)` builds `Pair[B=List]`
    // losing `A`. So the args-before-expected soundness fix (rejecting
    // `f() -> Option[String] = some(42)`) needs the build made robust to
    // unbound-var params first — tracked as its own follow-up, not this reorder.
    if let Some(exp) = expected {
        unify_types(kb, &mut subst, &TermIdView(parent_type), &exp);
    }

    // WI-342: `declared_type` is a carrier-agnostic `Value` (a value-in-type
    // field rides as `Value::Node`); pass it directly to `unify_types`.
    for (field_sym, declared_type) in &field_types {
        if let Some((idx, _)) = named_args.iter().enumerate().find(|(_, (s, _))| s == field_sym) {
            if let Ok(ref r) = named_results[idx] {
                unify_types(kb, &mut subst, &r.ty, declared_type);
                effects = merge_effects(&effects, &r.effects);
            }
        }
    }

    for (i, r_opt) in pos_results.iter().enumerate() {
        if let Some((_, declared_type)) = field_types.get(i) {
            if let Ok(r) = r_opt {
                unify_types(kb, &mut subst, &r.ty, declared_type);
                effects = merge_effects(&effects, &r.effects);
            }
        }
    }

    if subst.bindings.is_empty() {
        return Ok(TypeResult { ty: Value::Term(parent_type), env: env.clone(), effects, node: Rc::clone(occ) });
    }

    // Build parameterized type from the sort's type params + substitution bindings.
    // Look up SortAlias facts for the parent sort's scope to find param names → Var mappings.
    // For free-standing entities there is no parent sort to walk; the entity's
    // own symbol is the type — no type params to discover, so return the
    // simple sort_ref directly.
    let parent_sym = match parent_sort {
        Some(parent_tid) => match kb.get_term(parent_tid) {
            Term::Fn { functor, .. } => *functor,
            _ => return Ok(TypeResult { ty: Value::Term(parent_type), env: env.clone(), effects, node: Rc::clone(occ) }),
        },
        None => return Ok(TypeResult { ty: Value::Term(parent_type), env: env.clone(), effects, node: Rc::clone(occ) }),
    };

    let alias_sym = kb.try_resolve_symbol("SortAlias");
    let mut param_bindings: Vec<(Symbol, TermId)> = Vec::new();

    if let Some(a_sym) = alias_sym {
        let parent_name = kb.qualified_name_of(parent_sym).to_string();
        // Collect alias info: (param_short_name, VarId, bound_type)
        let mut alias_info: Vec<(String, TermId)> = Vec::new();
        for rid in kb.rules_by_functor(a_sym) {
            if !kb.is_fact(rid) { continue; }
            // A value-fact SortAlias (denoted-bearing target, e.g.
            // `sort T = Foo[Int, 3]`) never has a logic `Var` target, so it is not
            // a type-param indirection — skip it (and avoid the term-only
            // `rule_head` panic on a `Value::Node`/`Entity` head).
            let Some(head) = kb.fact_head_term(rid) else { continue };
            if let Term::Fn { pos_args, .. } = kb.get_term(head) {
                if pos_args.len() >= 2 {
                    let sort_tid = pos_args[0];
                    let target_tid = pos_args[1];
                    if let Term::Fn { functor: alias_functor, .. } = kb.get_term(sort_tid) {
                        let alias_name = kb.qualified_name_of(*alias_functor).to_string();
                        if alias_name.starts_with(&parent_name) && alias_name.len() > parent_name.len() {
                            let param_short = alias_name[parent_name.len() + 1..].to_string();
                            if let Term::Var(Var::Global(vid)) = kb.get_term(target_tid) {
                                match subst.resolve_as_value(*vid) {
                                    Some(Value::Term(bound_type)) => {
                                        alias_info.push((param_short, *bound_type))
                                    }
                                    // denoted Node alias binding: `alias_info`
                                    // is TermId-keyed — WI-348 Phase C.
                                    Some(other) => debug_assert!(
                                        false,
                                        "WI-348: denoted {} alias binding — carrier-agnostic alias_info is Phase C",
                                        other.type_name(),
                                    ),
                                    None => {}
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
        Ok(TypeResult { ty: Value::Term(parent_type), env: env.clone(), effects, node: Rc::clone(occ) })
    } else {
        let base = kb.make_sort_ref(parent_sym);
        let param_type = kb.make_parameterized_type(base, &param_bindings);
        Ok(TypeResult { ty: Value::Term(param_type), env: env.clone(), effects, node: Rc::clone(occ) })
    }
}

/// Decompose a callable type into `(param, result, effects-row)` — carrier-
/// agnostic over [`TermView`], outputs owned [`Value`]s (WI-361/WI-342: input
/// `TermView`, output `Value`; never re-grounds, so a `Value::Node` callback
/// arrow with a denoted-bearing effect flows through losslessly).
///
/// The typer's canonical function type is `arrow(param, result, effects)`; the
/// stdlib surface type `Function[A, B, E]` is the *same* type — `arrow` is its
/// shorthand (`A` = param, `B` = result, `E` = effects). Both decompose here so
/// a `Function`-typed operation parameter is callable
/// (`operation map(l, f: Function[A, B]) = ... f(h) ...`) just like a
/// lambda-bound arrow. `param` is `None` when the source omits it; the effects
/// row is `None` when omitted (a bare `Function` without `E` → polymorphic).
/// The third element is the RAW effects child — a canonical `effects_rows(...)`
/// for an arrow, or a `Function.E` binding that may still be a legacy
/// `List[Type]` (pre-WI-331); callers normalize/flatten as they need via
/// [`canonical_effects_row`] / [`effect_row_present_values`]. Returns `None` for
/// non-callable types. (WI-289)
fn arrow_parts<V: TermView>(
    kb: &mut KnowledgeBase,
    ty: &V,
) -> Option<(Option<Value>, Value, Option<Value>)> {
    // `extract_type` reads an `arrow`'s param/result/effects children and a
    // `Function`'s A/B/E bindings carrier-agnostically. Pre-intern the child
    // keys so a `Value::Node` carrier's named-child lookups resolve even in a
    // minimal KB (the term builders intern them; cf. WI-361 slice 4's `base`).
    for key in ["param", "result", "effects", "base"] {
        kb.intern(key);
    }
    match extract_type(kb, ty) {
        TypeExtractor::Arrow { param, result, effects } => {
            Some((Some(param), result, Some(effects)))
        }
        TypeExtractor::Parameterized { base, bindings }
            if kb.qualified_name_of(base) == "anthill.prelude.Function" =>
        {
            let find = |name: &str| {
                bindings
                    .iter()
                    .find(|(p, _)| kb.resolve_sym(*p) == name)
                    .map(|(_, v)| v.clone())
            };
            let result = find("B")?;
            Some((find("A"), result, find("E")))
        }
        _ => None,
    }
}

/// Normalize a raw effects-row [`Value`] (the third element of [`arrow_parts`])
/// into a canonical `effects_rows(...)` carrier the row machinery
/// ([`subtype_effect_rows`] / [`unify_effect_rows`]) consumes. An arrow's
/// `effects` child and a `Value::Node` row are already canonical and pass
/// through untouched; only a legacy `List[Type]` `Function.E` binding (a
/// `TermId` carrier) is flattened and re-canonicalized.
fn canonical_effects_row(kb: &mut KnowledgeBase, row: &impl TermView) -> Value {
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
    match row.as_bind_value() {
        // Ground carrier: a canonical `effects_rows(...)` passes through; a
        // legacy `List[Type]` (Function.E pre-WI-331) is flattened + re-
        // canonicalized so the row machinery sees one shape.
        BindValue::Term(t) => {
            let is_canonical = matches!(
                (kb.get_term(t), effects_rows_sym),
                (Term::Fn { functor, .. }, Some(er)) if *functor == er
            );
            if is_canonical {
                Value::Term(t)
            } else {
                let flat = list_to_vec(kb, t);
                Value::Term(kb.build_canonical_effects_rows(&flat))
            }
        }
        // A `Value::Node` effects row is always the canonical occurrence form.
        BindValue::Value(v) => v,
        // An effects row is never carried as a deferred query path; the empty
        // row is a safe (unreachable) fallback.
        BindValue::Path(_) => Value::Term(kb.build_canonical_effects_rows(&[])),
    }
}

/// Flatten a raw effects-row [`Value`] into its present effect labels (plus an
/// open-row tail var, matching the ground `effects_rows_to_flat_list` and the
/// WI-341 `Value` path) — the carrier-agnostic effects a call site incurs.
/// Carrier-agnostic; a `Value::Node` row's occurrence labels are never
/// re-grounded. A legacy `List[Type]` binding's elements ARE the labels.
fn effect_row_present_values(kb: &mut KnowledgeBase, row: &impl TermView) -> Vec<Value> {
    match row.as_bind_value() {
        // Ground carrier: the established flat-list walk (exact pre-WI-361
        // behavior; its non-wrapper fallback also handles a legacy `List[Type]`
        // Function.E binding pre-WI-331).
        BindValue::Term(t) => {
            effects_rows_to_flat_list(kb, t).into_iter().map(Value::Term).collect()
        }
        // `Value::Node` carrier: decompose the occurrence row into its present
        // labels (plus an open-row tail), the occurrence never re-grounded
        // (WI-341) — matching the former `extract_function_type_parts_value`.
        _ => {
            let subst = Substitution::new();
            match decompose_effect_row(kb, &subst, row) {
                Some((mut present, tail, _absent)) => {
                    if let Some(tail_tid) = tail {
                        present.push(Value::Term(tail_tid));
                    }
                    present
                }
                None => Vec::new(),
            }
        }
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
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
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

/// Result + effects of a callable type (`arrow` or `Function[A, B, E]`), used
/// when applying a function value — `f(x)` yields the result type. Carrier-
/// agnostic over [`TermView`] (WI-361/WI-342): a ground `TermId` arrow and a
/// `Value::Node` callback arrow (a denoted-bearing effect like `Modify[a]`)
/// take one path — the result is the `Value` carrier and the effects are the
/// row's present labels (plus an open-row tail var), the occurrence never
/// re-grounded. Folds the former TermId / `_value` twins into one.
fn extract_function_type_parts<V: TermView>(
    kb: &mut KnowledgeBase,
    fn_type: &V,
) -> Option<(Value, Vec<Value>)> {
    let (_, result, eff) = arrow_parts(kb, fn_type)?;
    let effects = eff.map(|row| effect_row_present_values(kb, &row)).unwrap_or_default();
    Some((result, effects))
}

/// The param type of a callable (`arrow` or `Function[A, B, E]`), used to type a
/// lambda's parameter from the checking direction (an expected `Function[A, B]`
/// tells us the param is `A`). Carrier-agnostic over [`TermView`], `Value` out.
fn extract_function_param_type<V: TermView>(kb: &mut KnowledgeBase, fn_type: &V) -> Option<Value> {
    arrow_parts(kb, fn_type)?.0
}

/// Ordered component types of a `named_tuple(fields: [TypeField(name,
/// type), …])` type. Used to bind a tuple-destructuring pattern's
/// sub-patterns positionally (`lambda (a, b) -> ...` checked against
/// `Function[(A, B), R]` types `a: A`, `b: B`). Returns `None` for a
/// non-tuple type.
/// Component types of a named-tuple type, in field order, carrier-agnostically
/// (WI-342 env data-flow): reads via [`extract_type`] so a `Value::Node` tuple (a
/// component that is a denoted-bearing lambda arrow) is handled too, and yields
/// each component as a carrier-agnostic [`Value`]. A non-tuple type yields `None`.
fn named_tuple_field_types<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<Vec<Value>> {
    match extract_type(kb, ty) {
        TypeExtractor::NamedTuple(fields) => Some(fields.into_iter().map(|(_, v)| v).collect()),
        _ => None,
    }
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


/// Extract a named type parameter from a parameterized type, carrier-agnostically
/// (WI-342 S3a): reads via [`extract_type`] so a `Value::Node` parameterized (a
/// denoted-bearing binding) is handled too, and returns the binding as a
/// carrier-agnostic [`Value`]. WI-361: a parameterized type is `Fn{S, named}`
/// (base sort = functor, bindings = named args), so the lookup is over those
/// bindings — `extract_type_param(List[T = Int], "T") → Some(Value::Term(Int))`.
pub(crate) fn extract_type_param<V: TermView>(kb: &KnowledgeBase, ty: &V, param: &str) -> Option<Value> {
    if let TypeExtractor::Parameterized { bindings, .. } = extract_type(kb, ty) {
        bindings.into_iter()
            .find(|(s, _)| kb.resolve_sym(*s) == param)
            .map(|(_, v)| v)
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
    scrutinee_type: &impl TermView,
    parent_sort: Symbol,
) -> Option<Substitution> {
    // WI-361: read the bindings form-agnostically — deep `parameterized(base,
    // bindings)` or term-backed `Fn{S, named}`. A non-parameterized scrutinee
    // (bare sort, arrow, …) yields no pattern subst. WI-342: carrier-agnostic
    // over [`TermView`] so a `Value::Node` scrutinee builds the subst too.
    let TypeExtractor::Parameterized { bindings, .. } =
        extract_type(kb, scrutinee_type)
    else {
        return None;
    };

    let mut subst = Substitution::new();
    let mut any = false;
    for (param, value) in &bindings {
        if let Some(vid) = type_param_vid_in_sort(kb, parent_sort, *param) {
            // WI-342: bind the type-param value carrier-agnostically (`bind_value`),
            // so a `Value::Node` (denoted-bearing) type-param is preserved rather
            // than re-grounded. `walk_type_value` resolves a field type through this
            // binding via `resolve_as_value` (it may surface the Node); a ground
            // `Value::Term` binding is still read by `walk_type` (which narrows
            // to `Value::Term`).
            subst.bind_value(vid, value.clone());
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
    scrutinee_type: Option<Value>,
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
                    // WI-342: the env binds a carrier-agnostic `Value`, so a
                    // `Value::Node` component type is preserved, not re-grounded.
                    let ty = scrutinee_type.unwrap_or_else(|| {
                        let fresh = kb.intern("?pat");
                        Value::Term(kb.make_type_var(fresh))
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
                            .as_ref()
                            .zip(parent_sort)
                            .and_then(|(st, p)| build_pattern_subst(kb, st, p));
                        for (i, sub_pat) in sub_patterns.iter().enumerate() {
                            // WI-342: the field type is a carrier-agnostic `Value`
                            // (`entity_field_types`); resolve its sort-level type
                            // params through the pattern subst without re-grounding.
                            let field_type = fields.get(i).map(|(_, ty)| {
                                match &subst {
                                    Some(s) => walk_type_value(kb, s, ty),
                                    None => ty.clone(),
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
                    let components = scrutinee_type
                        .as_ref()
                        .and_then(|t| named_tuple_field_types(kb, t));
                    for (i, sub_pat) in sub_patterns.iter().enumerate() {
                        let comp = components.as_ref().and_then(|c| c.get(i).cloned());
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
    // WI-348: carrier-agnostic — the OperationInfo head may be a value fact
    // (Node-carrying) for ops with a `denoted` effect. Read fields through the
    // shared `op_info` helpers, which view either carrier. This path serves
    // `lookup_operation_return_type`, whose `field` is always ground.
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")?;
    for rid in kb.rules_by_functor(op_info_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head_value(rid);
        if super::op_info::head_name_ref(kb, head) == Some(functor) {
            return super::op_info::head_field_term(kb, head, field);
        }
    }
    None
}

// ── Type unification ───────────────────────────────────────────

use super::subst::Substitution;

/// Unify two types **carrier-agnostically** (WI-342 P3): each side is any
/// [`TermView`] — a `TermId` (wrap in [`TermIdView`]) or a `Value`-carried type
/// (a `Value::Node` occurrence from `make_*_occ`, a `Value::Var`, …). This is
/// the migrated entry point — there is no `TermId`-only facade; callers holding
/// a `TermId` pass `&TermIdView(t)`.
///
/// Each side is resolved through the substitution to a `Value` — the same
/// carrier-agnostic representation [`Substitution`] already stores bindings in
/// (`Value::Term` is the hash-consed carrier; `Value::Node` an occurrence type;
/// `Value::Var` a logic var). This slice (P3) carries the var-bind + `denoted`
/// paths; the structural arms (`unify_parameterized`/`unify_arrow`/rows) are
/// still `TermId`-only and are reached only when BOTH sides resolve to
/// `Value::Term` — full structural unification of `Value`-carried
/// arrows/parameterized/rows is P4 (slice b).
///
/// WI-307 v1a: `kb` is `&mut` for fresh tail-variable allocation in the row
/// arms; all type-checker call sites already hold `&mut KnowledgeBase`.
pub fn unify_types<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    let a = walk_view(kb, subst, a);
    let b = walk_view(kb, subst, b);

    // Identity fast-path — only hash-consed TermId carriers have O(1) eq.
    if let (Value::Term(x), Value::Term(y)) = (&a, &b) {
        if x == y {
            return true;
        }
    }

    // Var arms — a logic var may be a hash-consed `Term::Var(Global)` or a
    // `Value::Var(Global)`; bind the other side by its carrier.
    if let Some(vid) = resolved_var(kb, &a) {
        return bind_resolved(kb, subst, vid, b);
    }
    if let Some(vid) = resolved_var(kb, &b) {
        return bind_resolved(kb, subst, vid, a);
    }

    match (&a, &b) {
        // Both hash-consed → today's `TermId` structural dispatch. This is the
        // hot path (no producer mints `Value`-carried types yet) and stays free
        // of the carrier-agnostic `denoted` check: two `TermId` `denoted`s with
        // distinct refs have distinct TermIds (→ `false` via the dispatch) and
        // equal ones share a TermId (→ the identity fast-path above), so the
        // `denoted` Ref-compare is only needed when hash-cons identity is lost
        // (a `Value` carrier on at least one side).
        (Value::Term(x), Value::Term(y)) => unify_term_dispatch(kb, subst, *x, *y),
        // At least one `Value` carrier (hash-cons identity is lost). Dispatch
        // structurally through the carrier-agnostic [`TermView`] arms (WI-342
        // P4): a `Value`-carried `denoted` / `parameterized` unifies against its
        // ground twin (cross-carrier) or another `Value` carrier. Forms not yet
        // wired return `false` (sound: refuses rather than mis-unifies).
        _ => unify_view_structural(kb, subst, &a, &b),
    }
}

/// WI-342 P4: carrier-agnostic structural dispatch — the [`TermView`] analog of
/// [`unify_term_dispatch`], reached from [`unify_types`] when at least one side
/// is a non-hash-consed carrier (a `Value::Node`). Reads each side's functor
/// name and immediate children through [`TermView`] and recurses via the generic
/// [`unify_types`], so a child of any carrier unifies uniformly.
///
/// This is deliberately a *separate* dispatch from [`unify_term_dispatch`]
/// rather than a single generic one folded over both arms: the `(Term, Term)`
/// path is the hot, heavily row-tested path (WI-307/328) and stays byte-
/// identical. Consolidating the two dispatches once the row machinery is fully
/// carrier-agnostic (P4-B) is a follow-up.
fn unify_view_structural<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    // WI-361: dispatch on the CANONICAL type tag (`type_head`), not the raw
    // functor — a flipped parameterized carrier / term-backed `Fn{S, named}`
    // reports its base sort as the raw functor, so raw-functor dispatch would miss
    // the `parameterized` arm (and the `denoted` alpha-equivalence path beneath it).
    // WI-342: every arm of `unify_term_dispatch` has a carrier-agnostic peer here,
    // so the dispatch is wired natively for both carriers with no re-ground bridge.
    // The arms below mirror `unify_term_dispatch`'s exactly (same functor pairs,
    // same helpers); the final `_` mirrors its `_ => types_compatible` fallback.
    match (type_dispatch_name_view(kb, a), type_dispatch_name_view(kb, b)) {
        (Some("denoted"), Some("denoted")) => unify_denoted_view(kb, a, b),
        (Some("parameterized"), Some("parameterized")) => {
            unify_parameterized_view(kb, subst, a, b)
        }
        (Some("parameterized"), Some("sort_ref")) => {
            unify_parameterized_with_sort_ref(kb, subst, a, b)
        }
        (Some("sort_ref"), Some("parameterized")) => {
            unify_parameterized_with_sort_ref(kb, subst, b, a)
        }
        (Some("arrow"), Some("arrow")) => unify_arrow_view(kb, subst, a, b),
        (Some("named_tuple"), Some("named_tuple")) => unify_named_tuple(kb, subst, a, b),
        // The same weaker WI-320 structural unify of the inner `effects_expr` that
        // `unify_term_dispatch` does for a top-level `effects_rows` pair (NOT the
        // full row algorithm — the arrow arm handles rows inside arrows via
        // `unify_effect_rows`). Read each `effects_expr` child carrier-agnostically.
        (Some("effects_rows"), Some("effects_rows")) => {
            let ee = kb.intern("effects_expr");
            match (named_child_value(kb, a, ee), named_child_value(kb, b, ee)) {
                (Some(x), Some(y)) => unify_types(kb, subst, &x, &y),
                _ => false,
            }
        }
        // Mirrors `unify_term_dispatch`'s `_ => types_compatible(...)` — a unify of
        // any other (form-mismatched) pair falls back to the subtype check, which is
        // itself carrier-agnostic (no re-ground).
        _ => types_compatible(kb, subst, a, b),
    }
}

/// WI-342: the sole `parameterized` unification, carrier-agnostic over
/// [`TermView`] — both the `TermId` dispatch (via [`TermIdView`]) and the
/// `Value` carrier route here. Bases unify via the generic [`unify_types`];
/// bindings are matched by param name (a-side bindings present on the b-side
/// must unify; b-only bindings are width-ignored).
fn unify_parameterized_view<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    // WI-361: read base + bindings via `extract_type` — both carriers present the
    // term backing `Fn{S, named}` (base = functor, bindings = named args). Each
    // base is a sort; present it as a bare `Ref(S)` and recurse `unify_types`,
    // preserving the full base relation (incl. WI-344 provider admissibility),
    // not a sort-symbol shortcut.
    let (a_base, a_bindings) = match extract_type(kb, a) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return false,
    };
    let (b_base, b_bindings) = match extract_type(kb, b) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return false,
    };
    let a_base_ty = kb.alloc(Term::Ref(a_base));
    let b_base_ty = kb.alloc(Term::Ref(b_base));
    if !unify_types(kb, subst, &TermIdView(a_base_ty), &TermIdView(b_base_ty)) {
        return false;
    }
    for (param, av) in &a_bindings {
        if let Some((_, bv)) = b_bindings.iter().find(|(p, _)| p == param) {
            if !unify_types(kb, subst, av, bv) {
                return false;
            }
        }
    }
    true
}

/// WI-342: the sole `arrow` unification, carrier-agnostic over [`TermView`]
/// (both the `TermId` dispatch via [`TermIdView`] and the `Value` carrier route
/// here). `param`/`result` unify via the generic [`unify_types`]; `effects` via
/// the carrier-agnostic [`unify_effect_rows`]. A missing effects field is
/// treated as the empty row.
fn unify_arrow_view<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    let param_sym = kb.intern("param");
    let result_sym = kb.intern("result");
    let effects_sym = kb.intern("effects");

    match (named_child_value(kb, a, param_sym), named_child_value(kb, b, param_sym)) {
        (Some(x), Some(y)) => {
            if !unify_types(kb, subst, &x, &y) {
                return false;
            }
        }
        _ => return false,
    }
    match (named_child_value(kb, a, result_sym), named_child_value(kb, b, result_sym)) {
        (Some(x), Some(y)) => {
            if !unify_types(kb, subst, &x, &y) {
                return false;
            }
        }
        _ => return false,
    }

    match (named_child_value(kb, a, effects_sym), named_child_value(kb, b, effects_sym)) {
        (Some(x), Some(y)) => unify_effect_rows(kb, subst, &x, &y),
        (None, None) => true,
        (Some(x), None) => match kb.try_make_empty_effects_rows() {
            Some(er) => unify_effect_rows(kb, subst, &x, &TermIdView(er)),
            None => false,
        },
        (None, Some(y)) => match kb.try_make_empty_effects_rows() {
            Some(er) => unify_effect_rows(kb, subst, &TermIdView(er), &y),
            None => false,
        },
    }
}

/// Decode a `List[record]` of two-field records into `(symbol-field, value-field)`
/// pairs, carrier-agnostic over [`TermView`] — a hash-consed `Term` cons-list OR a
/// `Value::Entity` cons-list (the WI-361 poisoned `named_tuple` `fields` carrier).
/// Shared by a `parameterized`'s `bindings` (`TypeBinding{param, value}`) and a
/// `named_tuple`'s `fields` (`TypeField{name, type}`). `sym_key` names the
/// `Ref`-valued field (read as a `Symbol`), `val_key` the type-valued field (read
/// as a `Value`); a cell that is not a `cons` record or is missing either field is
/// skipped.
pub(crate) fn list_records_to_pairs<V: TermView>(
    kb: &KnowledgeBase,
    list: &V,
    sym_key: &str,
    val_key: &str,
) -> Vec<(Symbol, Value)> {
    let (Some(head_key), Some(tail_key)) = (kb.lookup_symbol("head"), kb.lookup_symbol("tail"))
    else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut next = decode_cons_cell(kb, list, head_key, tail_key, sym_key, val_key, &mut out);
    while let Some(cell) = next {
        next = decode_cons_cell(kb, &cell, head_key, tail_key, sym_key, val_key, &mut out);
    }
    out
}

/// One step of [`list_records_to_pairs`]: if `cell` is a `cons` record, push its
/// `head` record's `(sym_key, val_key)` pair into `out` and return its `tail` as a
/// [`Value`]; otherwise (nil / non-cons) `None`.
fn decode_cons_cell<V: TermView>(
    kb: &KnowledgeBase,
    cell: &V,
    head_key: Symbol,
    tail_key: Symbol,
    sym_key: &str,
    val_key: &str,
    out: &mut Vec<(Symbol, Value)>,
) -> Option<Value> {
    match cell.head(kb) {
        ViewHead::Functor { functor: Some(f), .. }
            if kb.qualified_name_of(f) == "anthill.prelude.List.cons" => {}
        _ => return None,
    }
    if let Some(rec) = named_child_value(kb, cell, head_key) {
        if let (Some(s), Some(v)) =
            (view_child_sym(kb, &rec, sym_key), view_child_value(kb, &rec, val_key))
        {
            out.push((s, v));
        }
    }
    named_child_value(kb, cell, tail_key)
}

/// A [`ViewItem`] (which may borrow `kb`) as an owned [`Value`], freeing the
/// caller's `kb` borrow before a `&mut kb` recursion.
fn view_item_value(item: &ViewItem) -> Value {
    match item {
        ViewItem::Term(t) => Value::Term(*t),
        ViewItem::Value(v) => (*v).clone(),
        ViewItem::Node(rc) => Value::Node(Rc::clone(rc)),
    }
}

/// WI-342 P3: resolve a view through the substitution to a `Value` (the
/// carrier-agnostic resolved type). The concrete carrier is recovered via
/// [`TermView::as_bind_value`] — a `TermId` carrier runs the existing
/// `walk_type` (var + sort-alias resolution); a `Value` carrier walks
/// `Value::Term`/`Value::Var` and surfaces the rest (`Value::Node`, entities).
fn walk_view(kb: &KnowledgeBase, subst: &Substitution, v: &impl TermView) -> Value {
    match v.as_bind_value() {
        BindValue::Term(t) => walk_term_to_resolved(kb, subst, t),
        BindValue::Value(val) => walk_value_to_resolved(kb, subst, val),
        BindValue::Path(_) => {
            // A discrim-tree var-path is not a type carrier — refuse rather than
            // fabricate one (`Unit` unifies with nothing meaningful here).
            debug_assert!(false, "unify_types: Path carrier in a type position");
            Value::Unit
        }
    }
}

/// Walk a `TermId`-carried type, then surface a non-`Term` `Value` binding the
/// `TermId` walk can't see (`walk_type` narrows to `Value::Term`, skipping
/// non-`Term` bindings).
fn walk_term_to_resolved(kb: &KnowledgeBase, subst: &Substitution, t: TermId) -> Value {
    let t2 = walk_type(kb, subst, t);
    if let Term::Var(Var::Global(vid)) = kb.get_term(t2) {
        if let Some(v) = subst.resolve_as_value(*vid) {
            if !matches!(v, Value::Term(_)) {
                return walk_value_to_resolved(kb, subst, v.clone());
            }
        }
    }
    Value::Term(t2)
}

/// Walk a `Value`-carried type through the substitution. `Value::Term` defers to
/// the `TermId` walk; an unbound `Value::Var` resolves through `subst`; every
/// other form (`Value::Node`, entities) is already resolved.
fn walk_value_to_resolved(kb: &KnowledgeBase, subst: &Substitution, val: Value) -> Value {
    match val {
        Value::Term(t) => walk_term_to_resolved(kb, subst, t),
        Value::Var(Var::Global(vid)) => match subst.resolve_as_value(vid) {
            Some(bound) => walk_value_to_resolved(kb, subst, bound.clone()),
            None => Value::Var(Var::Global(vid)),
        },
        other => other,
    }
}

/// The logic-var id a resolved type *is*, if any — a hash-consed
/// `Term::Var(Global)` or a `Value::Var(Global)`.
fn resolved_var(kb: &KnowledgeBase, r: &Value) -> Option<VarId> {
    match r {
        Value::Term(t) => match kb.get_term(*t) {
            Term::Var(Var::Global(vid)) => Some(*vid),
            _ => None,
        },
        Value::Var(Var::Global(vid)) => Some(*vid),
        _ => None,
    }
}

/// Bind `vid` to a resolved type by its carrier (WI-342 P3): `bind_term` for a
/// hash-consed `TermId`, `bind_value` for any other `Value` carrier.
fn bind_resolved(kb: &mut KnowledgeBase, subst: &mut Substitution, vid: VarId, other: Value) -> bool {
    match other {
        Value::Term(t) => {
            if occurs_in(kb, vid, t) {
                return false;
            }
            subst.bind_term(vid, t);
        }
        other => {
            if occurs_in_view(kb, vid, &other) {
                return false;
            }
            subst.bind_value(vid, other);
        }
    }
    !subst.is_contradiction()
}

/// Short functor name of a resolved type, carrier-agnostically (via [`TermView`]).
fn resolved_functor_name<'a>(kb: &'a KnowledgeBase, r: &impl TermView) -> Option<&'a str> {
    match r.head(kb) {
        ViewHead::Functor { functor: Some(sym), .. } => Some(kb.resolve_sym(sym)),
        _ => None,
    }
}

/// WI-342 P3: unify two `denoted` types by their carried value. For the value
/// forms produced today the carried value is an `Expr::Ref(sym)` / `Term::Ref`
/// occurrence — both expose `ViewHead::Ref` — so two `denoted` unify iff their
/// value refers to the same symbol. Works cross-carrier (a ground
/// `denoted(Ref(c))` unifies with a `Value`-carried `denoted(Node(Ref(c)))`),
/// which is what lets P3 run while loaders stay on the legacy path.
fn unify_denoted_view<A: TermView, B: TermView>(kb: &mut KnowledgeBase, a: &A, b: &B) -> bool {
    // Sequential (not a single tuple) so each `&mut kb` borrow is released
    // before the next — `denoted_ref_sym` interns the `value` field symbol.
    let sa = denoted_ref_sym(kb, a);
    let sb = denoted_ref_sym(kb, b);
    match (sa, sb) {
        (Some(sa), Some(sb)) => {
            if sa == sb {
                return true;
            }
            // WI-341 ALPHA-EQUIVALENCE. A callback's own arrow param (a
            // `CallbackParam` place, `f.a`) is a binder: its alpha-canonical
            // identity is its POSITION among the callback's params (the doc's De
            // Bruijn view, computed from the place). So `(a) -> R @ Modify[a]`
            // and `(c) -> R @ Modify[c]` are the same type up to renaming — their
            // binders compare equal because the arrow being unified aligns the
            // i-th param of each. (A free reference — an op param `Modify[s]`,
            // the result — is not a CallbackParam, so it falls back to symbol
            // identity above, never alpha-equated.)
            //
            // SOUNDNESS INVARIANT (position-only comparison): a raw
            // `Modify[CallbackParam]` label exists ONLY inside its own callback
            // arrow's `effects` child — the binder is meaningless outside its
            // arrow's scope, and `region::op_boundary_effects` re-keys any
            // callback Modify to a concrete op place (input / result) before it
            // reaches a top-level op effect row. So two `CallbackParam` denoteds
            // only ever meet here through `arrow_compatible_view`, which has
            // ALREADY aligned the two arrows (param children unified first) — i.e.
            // they are corresponding binders, so equal position ⇒ same binder.
            // A future caller comparing two binders NOT through aligned-arrow
            // unify would break this — keep callback-Modify labels arrow-local.
            match (callback_binder_position(kb, sa), callback_binder_position(kb, sb)) {
                (Some(pa), Some(pb)) => pa == pb,
                _ => false,
            }
        }
        // A non-`Ref` carried value that is not a plain binder reference
        // (a nested apply, a literal) is not yet comparable — refuse.
        _ => false,
    }
}

/// WI-341 alpha-equivalence: the 0-based position of a `CallbackParam` binder
/// among its callback's parameters — its alpha-canonical identity. `None` for a
/// non-binder symbol (an op param / result / sort), which is compared by
/// identity instead. The parent callable is the place's qualified name minus its
/// last segment (`<op>.f.a` → `<op>.f`), and its ordered params are on its symbol
/// (`SymbolTable::arg_places`).
fn callback_binder_position(kb: &KnowledgeBase, sym: Symbol) -> Option<usize> {
    if kb.kind_of(sym) != Some(crate::intern::SymbolKind::CallbackParam) {
        return None;
    }
    let qn = kb.qualified_name_of(sym);
    let parent_qn = qn.rsplit_once('.').map(|(p, _)| p)?;
    let callback = kb.try_resolve_symbol(parent_qn)?;
    kb.symbols.arg_places(callback).iter().position(|&p| p == sym)
}

/// The symbol a `denoted`'s `value` child refers to, if it is a `Ref`-shaped
/// occurrence — read carrier-agnostically through [`TermView`]. `intern` (not
/// `lookup_symbol`) so the read is robust in a KB that hasn't interned the
/// well-known `value` field symbol (a production KB always has via stdlib load).
fn denoted_ref_sym(kb: &mut KnowledgeBase, r: &impl TermView) -> Option<Symbol> {
    let value_key = kb.intern("value");
    let child = r.named_arg(kb, value_key)?;
    match child.head(kb) {
        ViewHead::Ref(s) => Some(s),
        _ => None,
    }
}

/// Occurs check over a [`TermView`] (the `Value`-carried analog of
/// [`occurs_in`]): does `vid` appear anywhere inside `v`?
///
/// A `Value::Node` type is walked completely via [`occ_contains_var`] (which reads
/// the occurrence storage directly), not through the view alone — belt-and-braces
/// so a var nested in a parameterized binding / named-tuple field can't be missed,
/// which would let `bind_resolved` create a cyclic binding. So a `Value::Node` is
/// walked completely via [`occ_contains_var`]
/// over the occurrence spine; every other carrier (a `TermId`, which exposes all
/// children) uses the view walk.
fn occurs_in_view(kb: &KnowledgeBase, vid: VarId, v: &impl TermView) -> bool {
    if let BindValue::Value(Value::Node(occ)) = v.as_bind_value() {
        return occ_contains_var(kb, vid, &occ);
    }
    match v.head(kb) {
        ViewHead::Var(x) => x == vid,
        ViewHead::Functor { pos_arity, .. } => {
            for i in 0..pos_arity {
                if let Some(c) = v.pos_arg(kb, i) {
                    if occurs_in_view(kb, vid, &c) {
                        return true;
                    }
                }
            }
            for k in v.named_keys(kb) {
                if let Some(c) = v.named_arg(kb, k) {
                    if occurs_in_view(kb, vid, &c) {
                        return true;
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Complete occurs-check over a `Value::Node` occurrence spine — walks ALL
/// children (including the bindings/fields the [`TermView`] doesn't expose for
/// Rep-A `parameterized`/`named_tuple`). A ground `TypeChild` defers to the
/// hash-consed [`occurs_in`]; a poisoned child recurses.
fn occ_contains_var(kb: &KnowledgeBase, vid: VarId, occ: &Rc<NodeOccurrence>) -> bool {
    let child = |kb: &KnowledgeBase, c: &TypeChild| match c {
        TypeChild::Ground(t) => occurs_in(kb, vid, *t),
        TypeChild::Node(n) => occ_contains_var(kb, vid, n),
    };
    if let Some(tn) = occ.as_type() {
        return match tn {
            // A `denoted`'s carried value is an `Expr::Ref` (a value ref), never a
            // type var, so it cannot capture `vid`.
            TypeNode::Denoted { .. } => false,
            TypeNode::Parameterized { base, bindings } => {
                child(kb, base) || bindings.iter().any(|(_, c)| child(kb, c))
            }
            TypeNode::EffectsRows { effects_expr } => child(kb, effects_expr),
            TypeNode::Arrow { param, result, effects } => {
                child(kb, param) || child(kb, result) || child(kb, effects)
            }
            // WI-361: `fields` is the `Value`-carried `List[TypeField]`; the
            // view-walking `occurs_in_view` descends its cons cells + records and
            // into any poisoned (`Value::Node`) field type via `occ_contains_var`.
            TypeNode::NamedTuple { fields } => occurs_in_view(kb, vid, fields),
        };
    }
    if let Some(en) = occ.as_effect_expr() {
        return match en {
            EffectExprNode::Present { label } | EffectExprNode::Absent { label } => child(kb, label),
            EffectExprNode::Merge { left, right } => child(kb, left) || child(kb, right),
            EffectExprNode::Open { tail } => child(kb, tail),
            EffectExprNode::EmptyRow => false,
        };
    }
    false
}

/// The `TermId`-only structural dispatch (functor-pair match) — reached from
/// [`unify_types`] only when both sides resolve to a hash-consed `Term`.
///
/// WI-342 dispatch consolidation: the `parameterized` and `arrow` arms now route
/// through the carrier-agnostic [`unify_parameterized_view`] / [`unify_arrow_view`]
/// (wrapping each ground `TermId` in [`TermIdView`]) — one implementation per
/// relation, shared with the `Value`-carrier path in [`unify_view_structural`].
/// The remaining arms stay `TermId`-specific because they have no `Value`-carried
/// counterpart yet (`unify_parameterized_with_sort_ref`, `unify_named_tuple`) or
/// are deliberately weaker here than the row algorithm
/// (`effects_rows`-vs-`effects_rows`, see [`unify_view_structural`]).
fn unify_term_dispatch(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_resolved: TermId,
    b_resolved: TermId,
) -> bool {
    // WI-361: dispatch on the canonical form tag so a term-backed `Ref(S)` /
    // `Fn{S,named}` routes through the same arms as the deep `sort_ref` /
    // `parameterized` (identical to the raw functor name on the deep form).
    let a_functor = type_dispatch_name(kb, a_resolved);
    let b_functor = type_dispatch_name(kb, b_resolved);

    match (a_functor, b_functor) {
        // WI-342 dispatch consolidation: the `parameterized` / `arrow` arms route
        // through the carrier-agnostic `*_view` relations (wrapping each ground
        // `TermId` in `TermIdView`) — one implementation per relation, no
        // term-specific twin to drift from. The `*_view` fns are byte-equivalent
        // to the deleted `unify_parameterized` / `unify_arrow` for the TermId
        // carrier (same base/param/result/binding logic + empty-row synthesis).
        (Some("parameterized"), Some("parameterized")) => {
            unify_parameterized_view(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        (Some("parameterized"), Some("sort_ref")) => {
            unify_parameterized_with_sort_ref(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        (Some("sort_ref"), Some("parameterized")) => {
            unify_parameterized_with_sort_ref(kb, subst, &TermIdView(b_resolved), &TermIdView(a_resolved))
        }
        (Some("arrow"), Some("arrow")) => {
            unify_arrow_view(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        (Some("named_tuple"), Some("named_tuple")) => {
            unify_named_tuple(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        (Some("effects_rows"), Some("effects_rows")) => {
            // WI-320 substrate: structural unification on the wrapped
            // EffectExpression. The hash-cons short-circuit already caught the
            // both-ground identical case; this arm covers post-walk wrappers
            // pointing at structurally-equivalent but distinct TermIds. Row
            // unification proper (Rémy / Lindley-Cheney) is WI-307.
            let a_inner = match kb.get_term(a_resolved) {
                Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "effects_expr"),
                _ => return false,
            };
            let b_inner = match kb.get_term(b_resolved) {
                Term::Fn { named_args, .. } => get_named_arg(kb, named_args, "effects_expr"),
                _ => return false,
            };
            match (a_inner, b_inner) {
                (Some(x), Some(y)) => unify_types(kb, subst, &TermIdView(x), &TermIdView(y)),
                _ => false,
            }
        }
        _ => types_compatible(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved)),
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
fn unify_parameterized_with_sort_ref<P: TermView, S: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    parameterized: &P,
    sort_ref: &S,
) -> bool {
    // WI-361: read base + bindings form-agnostically — deep `parameterized(base,
    // bindings)` OR term-backed `Fn{S, named}`. A non-parameterized side, a base
    // mismatch, or a non-`sort_ref` falls back to the plain compat relation.
    // WI-342: carrier-agnostic over [`TermView`] (both sides may be a `Value::Node`).
    let TypeExtractor::Parameterized { base: pbase_sym, bindings } =
        extract_type(kb, parameterized)
    else {
        return types_compatible(kb, subst, parameterized, sort_ref);
    };
    let Some(sref_sym) = extract_sort_ref_sym(kb, sort_ref) else {
        return types_compatible(kb, subst, parameterized, sort_ref);
    };
    if pbase_sym != sref_sym {
        return types_compatible(kb, subst, parameterized, sort_ref);
    }

    for (psym, value) in &bindings {
        // Classify the binding value up front so the `format!` + symbol-resolve
        // below runs ONLY for a value that actually binds the alias Var. Two bind:
        //  - a ground (`Value::Term`) value;
        //  - WI-375: a Node-carried EFFECT-ROW — a WRITTEN row `E = {Modify[c]}`
        //    whose `effects_rows(…)` carries the `c` occurrence (the whole binding
        //    is a `Value::Node`). Bound via `bind_value` so the row threads into a
        //    bare-`Stream` consumer param instead of being dropped, which left `E`
        //    an unresolved `?_` that leaked as a spurious `undeclared effect`.
        // Every other carrier (a non-effect-row value-in-type `Value::Node` — a
        // denoted `Vector[Int, 3]` size — a `Var`, a scalar) binds nothing here:
        // skip it without the symbol work (the pre-WI-375 leading-`continue`
        // early-out). Out of WI-375 scope, those ride on their own SortRequiresInfo
        // / SortAlias value fact (WI-366); binding them here would perturb it.
        let is_effect_row_node = matches!(value, Value::Node(_))
            && matches!(type_head(kb, value), TypeHead::EffectsRows);
        if !matches!(value, Value::Term(_)) && !is_effect_row_node {
            continue;
        }
        let qualified = format!(
            "{}.{}",
            kb.qualified_name_of(pbase_sym),
            kb.resolve_sym(*psym),
        );
        let Some(qualified_sym) = kb.try_resolve_symbol(&qualified) else { continue };
        let Some(alias_target) = resolve_sort_alias(kb, qualified_sym) else { continue };
        let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) else { continue };
        let vid = *vid;
        match value {
            // Ground (term-carried): bind after the occurs-check guards a cycle.
            Value::Term(t) => {
                if !occurs_in(kb, vid, *t) {
                    subst.bind(vid, *t);
                }
            }
            // Guaranteed an effect-row Node by `is_effect_row_node` above. (The
            // occurs-check is term-only; a freshly-opened alias Var never occurs
            // inside a user-written row, so no cycle arises here.)
            _ => {
                subst.bind_value(vid, value.clone());
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
    if let Term::Var(Var::Global(vid)) = kb.get_term(ty) {
        return match subst.resolve_as_value(*vid) {
            Some(Value::Term(bound)) => walk_type(kb, subst, *bound),
            // Non-`Term` (a denoted `Value::Node`) or unbound: keep the var.
            // This term-only walker deliberately stops here; its carrier-aware
            // caller `walk_term_to_resolved` surfaces a `Value::Node` binding
            // afterward via `resolve_as_value`.
            _ => ty,
        };
    }
    // WI-361: a bare sort is `Ref(S)` (term backing) or `sort_ref(name: Ref(S))`
    // (deep); `extract_sort_ref_sym` recognizes both. Any other shape (a
    // parameterized / arrow / non-type term) is left unchanged.
    let sym = match extract_sort_ref_sym(kb, &TermIdView(ty)) {
        Some(s) => s,
        None => return ty,
    };
    // Only resolve the sort ref through its SortAlias-to-Var if the symbol is
    // a *sort-level type parameter* (registered via `sort T = ?` inside a sort
    // body). Top-level abstract sorts like `sort Term = ?` in anthill.reflect
    // also have a SortAlias-to-Var entry, but they're concrete-but-opaque types
    // from a typer perspective — collapsing every `sort_ref(Term)` into Term's
    // alias Var would lose the sort-ref form and surface as `TermId(N)` in
    // diagnostics.
    if !is_sort_param_symbol(kb, sym) {
        return ty;
    }
    let alias_target = match resolve_sort_alias(kb, sym) {
        Some(t) => t,
        None => return ty,
    };
    if let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) {
        subst
            .resolve_as_value(*vid)
            .and_then(|v| v.as_term())
            .map_or(alias_target, |bound| walk_type(kb, subst, bound))
    } else {
        alias_target
    }
}

/// True iff `sym` is a sort-level type parameter — i.e., its short
/// name is registered in the type_params set of its defining scope's
/// parent sort. Distinguishes `sort T = ?` inside `sort Stream { … }`
/// (which IS a type-param) from `sort Term = ?` at namespace level
/// (which is a top-level abstract sort, not a type parameter).
pub(crate) fn is_sort_param_symbol(kb: &KnowledgeBase, sym: Symbol) -> bool {
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
/// alias appeared first in rules_by_functor order, causing proposal-038 / WI-210
/// dispatch to resolve the wrong logical Var.
fn resolve_sort_alias(kb: &KnowledgeBase, sym: Symbol) -> Option<TermId> {
    let alias_sym = kb.try_resolve_symbol("SortAlias")?;
    let sort_name = kb.resolve_sym(sym);
    let find = |matches: fn(&KnowledgeBase, Symbol, Symbol, &str) -> bool| {
        for rid in kb.rules_by_functor(alias_sym) {
            if !kb.is_fact(rid) { continue; }
            // A value-fact SortAlias (denoted-bearing target) carries no ground
            // target `TermId` — skip it (callers want a ground `Var`/alias term),
            // and avoid the term-only `rule_head` panic on a `Value::Node` head.
            let Some(head) = kb.fact_head_term(rid) else { continue };
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
/// `absent_labels` (the `-e` lacks-constraint slot) is consumed by
/// [`unify_effect_rows`] / [`subtype_effect_rows`] (WI-328): each side's
/// absents are registered as `lacks` constraints on that side's tail var
/// (`Substitution::add_lacks`) before the tail-binding step. A within-row
/// `present`/`absent` clash on the same label is rejected here (see the
/// end of the function).
///
/// **WI-339 F13** — returns `None` on **malformed input**:
/// - a second row-tail `Var` encountered after one was already recorded
///   (e.g. `merge(open(?ρ_1), open(?ρ_2))` — semantically nonsensical;
///   pre-WI-339 we kept the first and dropped subsequent ones silently);
/// - an unexpected functor inside the EffectExpression algebra (not
///   `empty_row` / `present` / `absent` / `open` / `merge`);
/// - an unexpected term shape (not `Term::Var` or `Term::Fn`).
///
/// Per `CLAUDE.md` *avoid fallbacks, know about errors early* — callers
/// translate `None` into a sub/unify rejection rather than proceeding
/// on incomplete decomposition. The well-formed inputs the typer
/// produces today never trip this; the hard-reject closes the door on
/// external producers (loader bugs, hand-built test terms) leaking
/// silent miscompares.
fn decompose_effect_row(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    effects: &impl TermView,
) -> Option<(Vec<Value>, Option<TermId>, Vec<Value>)> {
    // WI-342 P4-B (B2): carrier-agnostic walk over the `EffectExpression`
    // algebra via [`TermView`], so a `Value`-carried (denoted-bearing) row
    // decomposes by the same code as a hash-consed `TermId` row. Field-name
    // symbols are interned up front (idempotent; the view's `effect_expr_named`
    // resolves the same names via `lookup_symbol`) so the rest of the walk is
    // read-only. Labels surface as owned `Value`s; the tail materializes to a
    // hash-consed `TermId` Var (row tails are always plain logic vars).
    let effects_expr_key = kb.intern("effects_expr");
    let label_key = kb.intern("label");
    let tail_key = kb.intern("tail");
    let left_key = kb.intern("left");
    let right_key = kb.intern("right");

    let walked = walk_view(kb, subst, effects);
    // Match the wrapper by its fully-qualified symbol (not the short name), as
    // the pre-P4 `TermId` walk did — a same-short-named functor in another
    // namespace must NOT be mistaken for the prelude `Type.effects_rows`.
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
    let is_effects_rows = matches!(
        walked.head(kb),
        ViewHead::Functor { functor: Some(f), .. } if Some(f) == effects_rows_sym
    );
    let expr: Value = if is_effects_rows {
        match named_child_value(kb, &walked, effects_expr_key) {
            Some(e) => e,
            None => return Some((Vec::new(), None, Vec::new())),
        }
    } else {
        // Not an effects_rows wrapper — a bare row Var is itself an open-tail
        // row (mostly partial arrows in tests); anything else is empty.
        match row_tail_termid(kb, &walked) {
            Some(t) => return Some((Vec::new(), Some(t), Vec::new())),
            None => return Some((Vec::new(), None, Vec::new())),
        }
    };

    let mut present: Vec<Value> = Vec::new();
    let mut absent: Vec<Value> = Vec::new();
    let mut tail: Option<TermId> = None;
    let mut stack: Vec<Value> = vec![expr];
    while let Some(node_raw) = stack.pop() {
        let node = walk_value_to_resolved(kb, subst, node_raw);

        // Unbound Var directly inside the algebra — a row-tail (any flavor;
        // a `TermId`-carried Rigid/DeBruijn is preserved as before).
        if let Some(node_tail) = row_tail_termid(kb, &node) {
            // WI-339 F13: a second distinct row-tail var is a malformed-row
            // signal (e.g. `merge(open(?ρ_1), open(?ρ_2))`) — reject hard so
            // the caller propagates the row-shape error.
            match tail {
                None => tail = Some(node_tail),
                Some(existing) if existing == node_tail => {}
                Some(_) => return None,
            }
            continue;
        }

        match resolved_functor_name(kb, &node) {
            Some("empty_row") => {}
            Some("present") => {
                if let Some(l) = named_child_value(kb, &node, label_key) {
                    present.push(l);
                }
            }
            Some("absent") => {
                if let Some(l) = named_child_value(kb, &node, label_key) {
                    absent.push(l);
                }
            }
            Some("open") => {
                if let Some(t) = named_child_value(kb, &node, tail_key) {
                    // Re-walk through the open-tail: a bound row variable
                    // resolves to a concrete EffectExpression here.
                    stack.push(t);
                }
            }
            Some("merge") => {
                if let Some(r) = named_child_value(kb, &node, right_key) {
                    stack.push(r);
                }
                if let Some(l) = named_child_value(kb, &node, left_key) {
                    stack.push(l);
                }
            }
            // WI-339 F13: unknown functor / unexpected shape — hard reject.
            _ => return None,
        }
    }

    // WI-328 (piece d / proposal §7.2): a row presenting and absenting the
    // SAME label (`{ e, - e }`) is malformed. Compared through the substitution
    // (carrier-agnostically): two ground labels match by resolved `TermId`, two
    // occurrence labels by `occurrence_structural_eq`.
    for p in &present {
        for a in &absent {
            if resolved_labels_equal(kb, subst, p, a) {
                return None;
            }
        }
    }

    Some((present, tail, absent))
}

/// A row-tail [`TermId`] if `node` resolves to a logic var, else `None`. A
/// `TermId`-carried var (any flavor — Global/Rigid/DeBruijn) returns its own
/// hash-consed id (preserving the pre-P4 tail classification); a `Value::Var`
/// materializes to a hash-consed `Term::Var` (row tails are plain vars).
fn row_tail_termid(kb: &mut KnowledgeBase, node: &Value) -> Option<TermId> {
    match node {
        Value::Term(t) => match kb.get_term(*t) {
            Term::Var(_) => Some(*t),
            _ => None,
        },
        Value::Var(v) => Some(kb.alloc(Term::Var(*v))),
        _ => None,
    }
}

/// A view's named child as an owned [`Value`] (frees the `kb` borrow). `key`
/// must already be interned (the caller interns the well-known field names).
fn named_child_value(kb: &KnowledgeBase, v: &impl TermView, key: Symbol) -> Option<Value> {
    v.named_arg(kb, key).map(|it| view_item_value(&it))
}

/// Resolve two effect-row labels through `subst` and compare structurally,
/// carrier-agnostically: ground labels by `TermId` identity, occurrence labels
/// by [`occurrence_structural_eq`]. Used for the present/absent same-label
/// malformed-row check (NOT a unification — it must not bind variables).
fn resolved_labels_equal(kb: &KnowledgeBase, subst: &Substitution, a: &Value, b: &Value) -> bool {
    let ra = walk_value_to_resolved(kb, subst, a.clone());
    let rb = walk_value_to_resolved(kb, subst, b.clone());
    match (&ra, &rb) {
        (Value::Term(x), Value::Term(y)) => x == y,
        (Value::Node(x), Value::Node(y)) => occurrence_structural_eq(x, y),
        _ => false,
    }
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
    a_present: &[Value],
    b_present: &[Value],
) -> (Vec<Value>, Vec<Value>) {
    // WI-338 F11: each unify_types attempt may bind variables in `subst`
    // *before* it determines it can't complete the unification (partial
    // structural success that fails on a downstream sub-term). Snapshot
    // the substitution before each attempt and roll back on failure so
    // failed pairings don't leak bindings into the substitution. Required
    // for callers that share `subst` with downstream reasoning
    // (`unify_effect_rows` from inside `unify_arrow` does — its subst
    // propagates into the typer's main state).
    //
    // WI-338 F8: the pre-WI-338 implementation rejected pairings whose
    // functors differed (sort_ref vs parameterized) before calling
    // `unify_types`. That rejected legitimate cross-functor compatible
    // labels (a bare sort vs its instantiation). The pre-filter
    // existed to limit subst pollution from doomed attempts — now
    // unnecessary with the per-attempt snapshot/restore — and is
    // removed. `unify_types`' return value is authoritative.
    let mut b_matched = vec![false; b_present.len()];
    let mut only_a: Vec<Value> = Vec::new();
    for al in a_present {
        let mut paired = false;
        for (i, bl) in b_present.iter().enumerate() {
            if b_matched[i] {
                continue;
            }
            let snapshot = subst.clone();
            if unify_types(kb, subst, al, bl) {
                b_matched[i] = true;
                paired = true;
                break;
            }
            // Restore — discard partial bindings from the failed attempt.
            *subst = snapshot;
        }
        if !paired {
            only_a.push(al.clone());
        }
    }
    let only_b: Vec<Value> = b_present
        .iter()
        .enumerate()
        .filter(|(i, _)| !b_matched[*i])
        .map(|(_, t)| t.clone())
        .collect();
    (only_a, only_b)
}

/// WI-326 subtype variant of [`pair_present_labels`] — existential
/// covering instead of 1-to-1 pairing. A single expected label can cover
/// multiple actuals (set-with-subtyping semantics), so `b_covered[i]` is
/// recorded for the `only_b` computation but NEVER excludes a later
/// pairing attempt.
///
/// Rationale (code-review F1): the pre-WI-326 `arrow_compatible` did
/// `for ae in actual { expected.any(|ee| types_compatible(ae, ee)) }` —
/// exists-quantified. Replacing that with the unify-shaped 1-to-1
/// `pair_present_labels` introduced a regression: `{red, blue} <:
/// {Color}` (two actual entities of a single expected sort) was rejected
/// because `Color` got marked matched after pairing with `red`, leaving
/// `blue` un-paired. Set semantics with element subtyping needs
/// existential pairing; unify needs strict 1-to-1.
///
/// **Returns** `(only_a, only_b)` where:
/// - `only_a` are actual labels that no expected covered (genuine extras
///   on the actual side; under subtype these must be empty or absorbed
///   by expected's open tail).
/// - `only_b` are expected labels that NO actual matched (allowed under
///   subset semantics; they're effects expected may have that actual
///   doesn't use). The tail-binding step still wants these when
///   expected is open and the algorithm needs to bind actual's tail to
///   reach them — same shape as the unify case.
fn cover_present_labels(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_present: &[Value],
    b_present: &[Value],
) -> (Vec<Value>, Vec<Value>) {
    // WI-338 F11: snapshot/restore around each unify_types attempt to
    // avoid partial-bind leakage on failed pairings. WI-338 F8: dropped
    // the pre-WI-338 functor-name pre-filter so cross-arm
    // (sort_ref vs parameterized) pairings unify_types can decide.
    // See `pair_present_labels` above for the soundness argument.
    let mut b_covered = vec![false; b_present.len()];
    let mut only_a: Vec<Value> = Vec::new();
    for al in a_present {
        let mut paired = false;
        for (i, bl) in b_present.iter().enumerate() {
            let snapshot = subst.clone();
            if unify_types(kb, subst, al, bl) {
                b_covered[i] = true;
                paired = true;
                break;
            }
            *subst = snapshot;
        }
        if !paired {
            only_a.push(al.clone());
        }
    }
    let only_b: Vec<Value> = b_present
        .iter()
        .enumerate()
        .filter(|(i, _)| !b_covered[*i])
        .map(|(_, t)| t.clone())
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
///
/// **WI-336 — Var-variant gating**. Only `Var::Global` row tails are
/// bindable:
///
/// - `Var::Rigid` represents a forall-Skolem — the universally-quantified
///   row whose contents are unknown to this scope. We can't bind it (it's
///   a constant to the unifier) and we can't safely claim it equals
///   `empty_row` or any specific shape on the basis of a "no-op" binding;
///   either side could instantiate `Rigid` to a row that contradicts the
///   caller's claim. Reject.
/// - `Var::DeBruijn` shouldn't appear in a resolved (post-`with_fresh_vars`)
///   context; the typer opens binders before this is reached. Treat as a
///   schema error and reject.
/// - A non-`Var` tail is defensive only — `decompose_effect_row` returns
///   `Some(tail)` only for `Term::Var` nodes. If a malformed input
///   somehow reaches here, accept only the literal no-op (no extras, no
///   final_tail) so the algorithm degrades gracefully.
///
/// Currently latent for v1a (the typer never produces Rigid/DeBruijn
/// effect-row tails), but the v1b lacks-constraint + polymorphic-row work
/// will introduce universally-quantified row variables in arrow.effects
/// positions — at which point the pre-WI-336 fallback would silently
/// accept unsoundly.
fn bind_row_tail(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    tail: TermId,
    extra_labels: &[Value],
    final_tail: Option<TermId>,
) -> bool {
    let vid = match kb.get_term(tail) {
        Term::Var(Var::Global(vid)) => *vid,
        // WI-336: forall-quantified (Rigid) or unopened DeBruijn tail —
        // not bindable, and the "would-be-no-op" assumption isn't safe.
        Term::Var(Var::Rigid(_)) | Term::Var(Var::DeBruijn(_)) => return false,
        // Non-Var tail: decompose_effect_row only returns Var for the
        // tail slot, so this is defensive against a malformed input.
        // Accept only a literal no-op.
        _ => return extra_labels.is_empty() && final_tail.is_none(),
    };

    // WI-328: lacks-constraint check. Any present label flowing INTO this
    // tail (via `extra_labels`) must not be one the tail is constrained to
    // lack (`ρ lacks e`). If `vid lacks e` and the binding would present
    // `e`, the row would carry a forbidden effect — reject the binding
    // (this is the "{Error | ρ} with ρ-lacks-Error fails" impossibility).
    let vid_lacks = subst.lacks_of(vid);
    if !vid_lacks.is_empty() {
        for l in extra_labels {
            if label_violates_lacks(kb, subst, l, &vid_lacks) {
                return false;
            }
        }
    }

    // WI-342 P4-B: a denoted-bearing extra label (`Value::Node`) would require
    // synthesizing a *Value-carried* row occurrence (`make_present_occ` …) and
    // binding the tail via `bind_value`. That path (open rows carrying a
    // denoted-bearing label, e.g. `{Modify[c] | ρ}`) is deferred — refuse
    // rather than mis-bind (sound). The ground extras below cover the closed-row
    // cross-carrier target this slice validates. In B1 `decompose_effect_row`
    // walks a `TermId` row, so every extra is already `Value::Term` here.
    let mut ground_extras: Vec<TermId> = Vec::with_capacity(extra_labels.len());
    for l in extra_labels {
        match l {
            Value::Term(t) => ground_extras.push(*t),
            _ => return false,
        }
    }

    // WI-337: bootstrap-safety — `decompose_effect_row`'s bare-Var
    // path (line ~5535) returns a `Var::Global` tail without ever
    // resolving any `EffectExpression` symbol, so we can reach here
    // on a KB whose prelude isn't registered. The builders below all
    // call panic-on-miss `resolve_symbol`. Probe the symbols first;
    // if any are missing, reject the binding (sound — we can't
    // synthesize the inner term, so we can't claim the bind holds).
    if kb.try_resolve_symbol("anthill.prelude.EffectExpression.empty_row").is_none()
        || kb.try_resolve_symbol("anthill.prelude.EffectExpression.open").is_none()
        || kb.try_resolve_symbol("anthill.prelude.EffectExpression.present").is_none()
        || kb.try_resolve_symbol("anthill.prelude.EffectExpression.merge").is_none()
    {
        return false;
    }

    // Build the inner tail: open(fresh) if shared, empty_row if closed.
    let inner = match final_tail {
        Some(ft) => kb.make_effect_expression_open(ft),
        None => kb.make_effect_expression_empty_row(),
    };
    // Right-fold extras into the inner tail.
    let mut acc = inner;
    for &l in ground_extras.iter().rev() {
        let p = kb.make_effect_expression_present(l);
        acc = kb.make_effect_expression_merge(p, acc);
    }

    if occurs_in(kb, vid, acc) {
        return false;
    }
    subst.bind(vid, acc);
    if subst.is_contradiction() {
        return false;
    }

    // WI-328: propagate this tail's lacks set onto the fresh continuation.
    // `ρ = extra_labels ∪ open(fresh)` and `ρ lacks L` (the extras were
    // already checked clean above) implies `fresh lacks L` — otherwise a
    // later binding of `fresh` could smuggle a forbidden effect back into
    // the row through the shared tail. Closed continuations (`final_tail =
    // None`) have no tail to carry the constraint, and that's sound: the
    // row is now fully determined and the extras passed the lacks check.
    if !vid_lacks.is_empty() {
        if let Some(ft) = final_tail {
            if let Term::Var(Var::Global(fresh_vid)) = kb.get_term(ft) {
                let fresh_vid = *fresh_vid;
                subst.add_lacks(fresh_vid, vid_lacks.iter().cloned());
            }
        }
    }
    true
}

/// WI-328 — does presenting `label` violate any `lacks` constraint in
/// `lacked`? A present label conflicts with a lacked label when the two
/// effect types unify (`Error` vs `Error`; `Modify[c]` vs `Modify[c]`; a
/// parameterized `Modify[?x]` lacked vs a concrete `Modify[c]` presented).
/// The probe unifies on a CLONE of `subst` so a match leaves no bindings
/// behind — the caller is deciding whether to reject the row, not
/// committing the label pairing.
///
/// **WI-341 coupling**: for a value-carrying label like `Modify[c]`, this
/// comparison (and v1a's `pair_present_labels`/`cover_present_labels`) works
/// only because the value occurrence `c` is currently flattened to a
/// hash-consed `denoted(value: Ref(c))`, so two `Modify[c]` share a TermId
/// and `unify_types` matches them. When `denoted` migrates to carry a real
/// `Rc<NodeOccurrence>` (per its `sort.anthill` schema), this must become
/// occurrence-aware — same change for the v1a label sites. See WI-341.
fn label_violates_lacks(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    label: &Value,
    lacked: &[Value],
) -> bool {
    for l in lacked {
        let mut probe = subst.clone();
        if unify_types(kb, &mut probe, label, l) {
            return true;
        }
    }
    false
}

/// WI-328 — register a row side's `absent` labels as `lacks` constraints on
/// that side's tail variable. Absents on a *closed* row (no tail) are
/// dropped: there is no tail to carry the constraint, and any cross-row
/// attempt to present a label the closed row forbids is already rejected by
/// the presence-pairing step (a forbidden label appears as an unabsorbable
/// extra). Only `Var::Global` tails carry lacks (Rigid/DeBruijn are
/// non-bindable per WI-336, so a lacks on them is unobservable).
fn register_row_lacks(
    kb: &KnowledgeBase,
    subst: &mut Substitution,
    tail: Option<TermId>,
    absent: &[Value],
) {
    if absent.is_empty() {
        return;
    }
    if let Some(t) = tail {
        if let Term::Var(Var::Global(vid)) = kb.get_term(t) {
            subst.add_lacks(*vid, absent.iter().cloned());
        }
    }
}

/// Allocate a fresh row-tail variable for the both-open arm of
/// [`unify_effect_rows`] / [`subtype_effect_rows`].
///
/// **WI-338 F9 known cost**: each call permanently increments
/// `kb.next_var` and inserts a new `Term::Var` into the hash-cons store.
/// The fresh var is bound in a local substitution that is typically
/// discarded after `arrow_compatible` returns — so the var ends up
/// orphaned but never observable. For long-running typer sessions
/// (language server, repeated batch checks) the VarId space grows
/// monotonically. Acceptable in practice today; if it ever becomes a
/// measured concern, possible mitigations:
///
/// - **memoize** `subtype_effect_rows` / `unify_effect_rows` results on
///   `(actual_effects, expected_effects)` so repeat queries don't
///   re-allocate;
/// - maintain a **free-list** of fresh row-tail vars on `KnowledgeBase`,
///   returning to the pool when a local substitution is dropped.
///
/// Both are out of scope for v1a hardening. This helper consolidates
/// the four pre-WI-338 inline allocation sites into one place so the
/// future fix has a single point of change.
fn fresh_row_tail_var(kb: &mut KnowledgeBase) -> TermId {
    let fresh_sym = kb.intern("?rho");
    let fresh_vid = kb.fresh_var(fresh_sym);
    kb.alloc(Term::Var(Var::Global(fresh_vid)))
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
/// **Lacks-constraints (WI-328 / v1b)** — `absent` labels (`-e`) are
/// registered as `lacks` constraints on each side's tail
/// (`register_row_lacks`) before step 3; `bind_row_tail` then rejects any
/// present label flowing into a tail that lacks it, and propagates the
/// lacks set onto fresh shared tails so the constraint survives further
/// unification.
fn unify_effect_rows<EA: TermView, EB: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_effects: &EA,
    b_effects: &EB,
) -> bool {
    // Fast path: identical hash-consed `TermId` carriers — covers the canonical
    // case where both arrows shared an effects field. (`Value::Node` carriers
    // have no O(1) identity → fall through to the structural decompose.)
    if let (BindValue::Term(x), BindValue::Term(y)) =
        (a_effects.as_bind_value(), b_effects.as_bind_value())
    {
        if x == y {
            return true;
        }
    }

    // WI-339 F13: decompose returns None on malformed input — propagate
    // as a unify rejection so the typer surfaces the row-shape error
    // instead of proceeding on incomplete decomposition.
    let (a_present, a_tail, a_absent) = match decompose_effect_row(kb, subst, a_effects) {
        Some(p) => p,
        None => return false,
    };
    let (b_present, b_tail, b_absent) = match decompose_effect_row(kb, subst, b_effects) {
        Some(p) => p,
        None => return false,
    };

    // WI-328: register each side's `- e` absents as `lacks` constraints on
    // that side's tail BEFORE the tail-binding step, so `bind_row_tail`
    // sees them when it checks the labels flowing into each tail.
    register_row_lacks(kb, subst, a_tail, &a_absent);
    register_row_lacks(kb, subst, b_tail, &b_absent);

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
            // Both open. If tails are already the same Var, the
            // extras must merge into ONE binding to avoid the
            // contradicting double-bind (WI-334) — see analogous arm
            // in subtype_effect_rows for the soundness argument.
            let a_walked = walk_type(kb, subst, a_t);
            let b_walked = walk_type(kb, subst, b_t);
            if a_walked == b_walked {
                if only_a.is_empty() && only_b.is_empty() {
                    return true;
                }
                let fresh_var = fresh_row_tail_var(kb);
                let mut all_extras: Vec<Value> =
                    Vec::with_capacity(only_a.len() + only_b.len());
                all_extras.extend(only_a.iter().cloned());
                all_extras.extend(only_b.iter().cloned());
                return bind_row_tail(kb, subst, a_walked, &all_extras, Some(fresh_var));
            }
            // Distinct tails: fresh shared tail var ρ'. Both sides extend
            // their respective labels and end in `open(ρ')` — afterward a
            // future decompose_effect_row reveals (only_a + only_b) as
            // present labels with shared tail ρ'.
            let fresh_var = fresh_row_tail_var(kb);
            bind_row_tail(kb, subst, a_t, &only_b, Some(fresh_var))
                && bind_row_tail(kb, subst, b_t, &only_a, Some(fresh_var))
        }
    }
}

/// WI-326 v1a row subtyping — the covariant directional analog of
/// [`unify_effect_rows`], mirroring its decompose/pair/tail-bind pipeline
/// ([`decompose_effect_row`], [`pair_present_labels`], [`bind_row_tail`])
/// but asymmetric: `actual <: expected` iff actual's effect *set* is a
/// subset of expected's. Specifically:
///
/// - `only_a` (labels actual has but expected doesn't) must be absorbed
///   by expected's open tail; with expected closed, that's a hard reject.
/// - `only_e` (labels expected has but actual doesn't) are always fine
///   under subset — expected can advertise effects the actual doesn't use.
///   If actual is open, expected's extras are absorbed by actual's tail
///   (the row-rewrite equation that makes actual reach expected's labels).
/// - Actual open + expected closed: actual's tail must close to
///   `empty_row` (actual can't carry unknown extras beyond expected's
///   finite set).
/// - Both open: the unify case applies as-is — a fresh shared tail
///   accommodates either side's extras; once both rows extend through it,
///   the sub relation holds.
///
/// The `subst` argument is intended to be a **local scratch** substitution
/// (allocated by [`arrow_compatible_view`]) — bindings are reasoning witnesses,
/// not committed into the caller's typing context.
fn subtype_effect_rows<EA: TermView, EB: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual_effects: &EA,
    expected_effects: &EB,
) -> bool {
    // Fast path: identical hash-consed `TermId` carriers (hash-cons identity).
    // `Value::Node` carriers have no O(1) identity → structural decompose.
    if let (BindValue::Term(x), BindValue::Term(y)) =
        (actual_effects.as_bind_value(), expected_effects.as_bind_value())
    {
        if x == y {
            return true;
        }
    }

    // WI-339 F13: decompose returns None on malformed input — propagate
    // as a sub rejection.
    let (a_present, a_tail, a_absent) =
        match decompose_effect_row(kb, subst, actual_effects) {
            Some(p) => p,
            None => return false,
        };
    let (e_present, e_tail, e_absent) =
        match decompose_effect_row(kb, subst, expected_effects) {
            Some(p) => p,
            None => return false,
        };

    // WI-328: register `- e` absents as `lacks` on each side's tail before
    // the tail-binding step (same as the unify path). Directional subtyping
    // reuses the symmetric `bind_row_tail` lacks check: a label absorbed
    // into a tail that lacks it is rejected on either side. This is **sound
    // but conservative** on the open/open arm: when expected presents `e`
    // and actual's tail lacks `e` (`{-e | ρa} <: {e | ρe}`), the shared-tail
    // step would bind `ρa` to absorb `e`, which the lacks check rejects —
    // so the pair is reported incompatible. Rejecting is the safe direction
    // (binding a lacked label into the tail would be unsound); the rare
    // genuinely-compatible directional case (route `e` only into the
    // expected side) is left for a later refinement.
    register_row_lacks(kb, subst, a_tail, &a_absent);
    register_row_lacks(kb, subst, e_tail, &e_absent);

    // WI-326 F1 (code-review): use the covering variant (existential), NOT
    // the unify-shaped 1-to-1 [`pair_present_labels`]. Set semantics with
    // element subtyping lets one expected label cover multiple actuals —
    // e.g. `{red, blue} <: {Color}` where both `red`, `blue` are entities
    // of `Color`. The 1-to-1 pairing would mark `Color` matched after the
    // first hit and reject the second.
    let (only_a, only_e) = cover_present_labels(kb, subst, &a_present, &e_present);

    match (a_tail, e_tail) {
        // Both closed. actual's extras must be empty (actual ⊆ expected
        // labels); expected's extras are fine under subset semantics.
        (None, None) => only_a.is_empty(),
        // Actual closed, expected open. actual's extras flow into
        // expected's tail, closing it; expected's extras are already
        // present in expected's known set — no constraint on actual.
        (None, Some(e_t)) => bind_row_tail(kb, subst, e_t, &only_a, None),
        // Actual open, expected closed. expected can't absorb anything
        // through a tail. actual's open tail must close to empty_row and
        // actual must have no extras.
        (Some(a_t), None) => {
            if !only_a.is_empty() {
                return false;
            }
            bind_row_tail(kb, subst, a_t, &[], None)
        }
        // Both open. Mirrors the unify case — once both tails link
        // through a fresh shared row var, the sub relation holds
        // (the two rows agree on the same set after extension).
        (Some(a_t), Some(e_t)) => {
            let a_walked = walk_type(kb, subst, a_t);
            let e_walked = walk_type(kb, subst, e_t);
            // WI-334: shared row var (a_walked == e_walked). The two
            // distinct bind_row_tail calls below would each try to bind
            // the same VarId to two structurally different terms
            // (`only_e ++ open(fresh)` vs `only_a ++ open(fresh)`) —
            // contradicting subst.bind, returning false even for valid
            // subtypes. Bind once with the union of both extras instead:
            // A's set = a_present ∪ K, B's set = e_present ∪ K, where K
            // is the shared tail. Binding K to {only_a ∪ only_e | fresh}
            // makes both rows agree on the same set (paired_a unifies
            // with paired_e via pair_present_labels), satisfying
            // actual <: expected.
            if a_walked == e_walked {
                if only_a.is_empty() && only_e.is_empty() {
                    return true;
                }
                let fresh_var = fresh_row_tail_var(kb);
                let mut all_extras: Vec<Value> =
                    Vec::with_capacity(only_a.len() + only_e.len());
                all_extras.extend(only_a.iter().cloned());
                all_extras.extend(only_e.iter().cloned());
                return bind_row_tail(kb, subst, a_walked, &all_extras, Some(fresh_var));
            }
            // Distinct tails: each side's tail absorbs the other's
            // extras + a fresh shared continuation. Symmetric Rémy
            // fresh-tail step.
            let fresh_var = fresh_row_tail_var(kb);
            bind_row_tail(kb, subst, a_t, &only_e, Some(fresh_var))
                && bind_row_tail(kb, subst, e_t, &only_a, Some(fresh_var))
        }
    }
}

/// Unify two named tuple types: matching fields must unify.
/// WI-342: the sole `named_tuple` unification, carrier-agnostic over [`TermView`]
/// (both the `TermId` dispatch via [`TermIdView`] and the `Value` carrier route
/// here). Fields are read by name via [`named_tuple_fields`] on each carrier; every
/// `b` field must have a matching `a` field whose type unifies.
fn unify_named_tuple<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    let a_fields = named_tuple_fields(kb, a);
    let b_fields = named_tuple_fields(kb, b);
    for (b_name, b_type) in &b_fields {
        match a_fields.iter().find(|(n, _)| n == b_name) {
            Some((_, a_type)) => {
                if !unify_types(kb, subst, a_type, b_type) {
                    return false;
                }
            }
            None => return false,
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
///
/// WI-326: takes `&mut KnowledgeBase` because [`arrow_compatible_view`] now
/// invokes row subtyping, which allocates fresh row-tail vars in the
/// both-open case.
///
/// WI-335: takes `&mut Substitution` so nested arrow checks (e.g.
/// `arrow_compatible`'s param + result + effects sub-checks, plus any
/// recursive descent through [`parameterized_compatible_view`] /
/// [`named_tuple_compatible`] / [`arrow_function_compatible`]) thread
/// **one** substitution through the whole sub-tree. This makes row-var
/// bindings from one sub-position visible to sibling positions —
/// fixing the soundness gap where nested arrows sharing a row var
/// across positions got inconsistent bindings under independent local
/// substitutions.
///
/// **Caller contract**: most call sites want each check independent of
/// any other check; they allocate `Substitution::new()` per call. Call
/// sites in a row-aware chain (e.g. inside another `types_compatible`
/// frame) thread the same subst through.
///
/// **Failure semantics**: when this function returns `false`, the
/// substitution may carry partial bindings from sub-checks that
/// succeeded before a sibling failed (and may even be marked
/// `is_contradiction()`). Callers that intend to make a subsequent
/// independent decision after a `false` result MUST discard the
/// substitution (or snapshot before the call). Threading-through
/// callers in this module rely on the early-return-on-false discipline
/// and never re-use a failed subst.
pub fn types_lesseq(kb: &mut KnowledgeBase, subst: &mut Substitution, actual: TermId, expected: TermId) -> bool {
    types_compatible(kb, subst, &TermIdView(actual), &TermIdView(expected))
}

/// WI-342 P4-B2: subtype/compatibility, carrier-agnostically. Mirrors
/// [`unify_types`]'s split — the hot `(TermId, TermId)` path stays byte-identical
/// in [`types_compatible_term_dispatch`]; a `Value`-carrier side routes to
/// [`types_compatible_view_structural`] (the unify/subtype lockstep, so a
/// denoted-bearing type compares consistently in both directions). Note the
/// term dispatch does NOT walk its inputs through `subst` at the top (unlike
/// `unify_types`) — callers pass already-resolved types — so the entry only
/// dispatches on the carrier, preserving that contract.
pub fn types_compatible<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    match (actual.as_bind_value(), expected.as_bind_value()) {
        (BindValue::Term(a), BindValue::Term(e)) => {
            types_compatible_term_dispatch(kb, subst, a, e)
        }
        _ => types_compatible_view_structural(kb, subst, actual, expected),
    }
}

/// The `TermId`-only subtype dispatch — byte-identical to the pre-P4-B2
/// `types_compatible` body. Reached when both sides are hash-consed carriers.
fn types_compatible_term_dispatch(kb: &mut KnowledgeBase, subst: &mut Substitution, actual: TermId, expected: TermId) -> bool {
    if actual == expected {
        return true;
    }

    // WI-361: dispatch on the canonical form tag (see `type_dispatch_name`) so a
    // term-backed `Ref(S)` / `Fn{S,named}` routes through the same arms as the
    // deep `sort_ref` / `parameterized`.
    let actual_functor = type_dispatch_name(kb, actual);
    let expected_functor = type_dispatch_name(kb, expected);

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
            // Nominal / entity-subtyping / refines, then WI-344 provider
            // admissibility: a value of a bare carrier sort is usable
            // where a bare spec it provides is expected. Confined to the
            // bare↔bare arm so it never rides the `sort_ref ↔ parameterized`
            // base check and drops a parameterized spec's bindings — see
            // `sort_provides_admissibly`.
            sort_ref_compatible(kb, actual, expected)
                || match (extract_sort_ref_sym(kb, &TermIdView(actual)), extract_sort_ref_sym(kb, &TermIdView(expected))) {
                    (Some(a), Some(e)) => sort_provides_admissibly(kb, a, e),
                    _ => false,
                }
        }
        (Some("parameterized"), Some("parameterized")) => {
            // WI-342 dispatch consolidation: route through the carrier-agnostic
            // subtype relation (TermId wrapped in TermIdView) — one impl, no
            // term-specific twin to drift from.
            parameterized_compatible_view(kb, subst, &TermIdView(actual), &TermIdView(expected))
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
            // bare `S` vs `B[…]`: nominal base-sort compatibility only (provider
            // admissibility is confined to the bare↔bare arm above). WI-361:
            // `parameterized_base_sym` reads the base sort form-agnostically
            // (deep `base` field or the term-backed functor).
            match (extract_sort_ref_sym(kb, &TermIdView(actual)), parameterized_base_sym(kb, expected)) {
                (Some(a), Some(eb)) => sort_sym_compatible(kb, a, eb),
                _ => false,
            }
        }
        (Some("parameterized"), Some("sort_ref")) => {
            match (extract_sort_ref_sym(kb, &TermIdView(expected)), parameterized_base_sym(kb, actual)) {
                (Some(e), Some(ab)) => sort_sym_compatible(kb, e, ab),
                _ => false,
            }
        }
        (Some("arrow"), Some("arrow")) => {
            arrow_compatible_view(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        // `arrow` is the typer's shorthand for the stdlib `Function[A, B, E]`
        // (see `arrow_parts`), so a lambda's `arrow(Int, Int)` body satisfies
        // a declared `Function[Int, Int]` return and vice versa. (WI-289)
        (Some("arrow"), Some("parameterized")) | (Some("parameterized"), Some("arrow")) => {
            arrow_function_compatible(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        (Some("named_tuple"), Some("named_tuple")) => {
            named_tuple_compatible(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        (Some("effects_rows"), Some("effects_rows")) => {
            // WI-333: row subsumption via [`subtype_effect_rows`]. The
            // identical-TermId case is already short-circuited by
            // [`KnowledgeBase`]'s hash-consing at the top of
            // [`types_compatible`]; this arm reaches when both sides are
            // effects_rows wrappers with structurally-distinct payloads.
            //
            // WI-335: uses the threaded subst so row-var bindings from
            // sibling positions are visible. This affects multiple
            // entry paths into this arm:
            //   - direct (effects_rows, effects_rows) comparison;
            //   - parameterized_compatible recursing on Function[E]
            //     bindings (the WI-333 path);
            //   - any nested types_compatible inside an arrow's param /
            //     result / effects sub-check.
            // Pre-WI-335 a local scratch subst meant each invocation
            // reasoned in isolation, accepting nested arrows /
            // parameterized bindings whose shared row var had no
            // consistent global binding across sibling positions.
            subtype_effect_rows(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        _ => false,
    }
}

/// WI-342 P4-B2: carrier-agnostic subtype dispatch — the [`TermView`] analog of
/// [`types_compatible_term_dispatch`], reached when at least one side is a
/// `Value` carrier (a `Value::Node`). Resolves both through `subst`; if both
/// land on a hash-consed `Term`, hands back to the term dispatch. Otherwise
/// dispatches the forms `unify_types` already handles cross-carrier, keeping the
/// two relations in lockstep: `denoted` (value-in-type subtyping IS equality →
/// the same Ref-compare unify uses), `arrow` (contravariant param / covariant
/// result / covariant effects), `effects_rows`, `parameterized`. Forms not yet
/// wired (e.g. `parameterized`-vs-`sort_ref`, `named_tuple`) refuse — sound.
fn types_compatible_view_structural<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    let a = walk_view(kb, subst, actual);
    let e = walk_view(kb, subst, expected);
    if let (Value::Term(x), Value::Term(y)) = (&a, &e) {
        return types_compatible_term_dispatch(kb, subst, *x, *y);
    }

    // WI-361: canonical type tag, not raw functor (see `unify_view_structural`) —
    // a flipped parameterized / term-backed `Fn{S, named}` routes to the
    // `parameterized` arms instead of falling through to the re-grounding bridge.
    let af = type_dispatch_name_view(kb, &a);
    let ef = type_dispatch_name_view(kb, &e);
    // type_var is the inference wildcard; nothing is bottom (subtype of all).
    if af == Some("type_var") || ef == Some("type_var") {
        return true;
    }
    if af == Some("nothing") {
        return true;
    }

    match (af, ef) {
        // value-in-type: `denoted(c) <: denoted(d)` iff `c == d` (no proper
        // subtyping between distinct carried values) — the same relation unify
        // computes, so the two directions agree.
        (Some("denoted"), Some("denoted")) => unify_denoted_view(kb, &a, &e),
        (Some("arrow"), Some("arrow")) => arrow_compatible_view(kb, subst, &a, &e),
        (Some("effects_rows"), Some("effects_rows")) => {
            subtype_effect_rows(kb, subst, &a, &e)
        }
        (Some("parameterized"), Some("parameterized")) => {
            parameterized_compatible_view(kb, subst, &a, &e)
        }
        // WI-361/WI-342: `arrow` and `Function[A,B,E]` denote the same callable
        // type. Read the parts carrier-agnostically (no re-ground) so a
        // `Value::Node` arrow checks against a `Function` without a lossy bridge.
        // Dispatch is now canonical (`type_head`), so a term-backed `Fn{Function,
        // named}` reports `parameterized` and hits this arm directly too.
        (Some("arrow"), Some("parameterized")) | (Some("parameterized"), Some("arrow")) => {
            arrow_function_compatible(kb, subst, &a, &e)
        }
        (Some("named_tuple"), Some("named_tuple")) => named_tuple_compatible(kb, subst, &a, &e),
        // Bare `S` vs `B[…]`: nominal base-sort compatibility only (mirrors
        // `types_compatible_term_dispatch`). `sort_sym_compatible` takes
        // (sort_ref-side sym, parameterized-side base); `sort_functor_of_view`
        // surfaces the head sym for a `sort_ref` and the base for a `parameterized`.
        (Some("sort_ref"), Some("parameterized")) => {
            match (sort_functor_of_view(kb, &a), sort_functor_of_view(kb, &e)) {
                (Some(av), Some(eb)) => sort_sym_compatible(kb, av, eb),
                _ => false,
            }
        }
        (Some("parameterized"), Some("sort_ref")) => {
            match (sort_functor_of_view(kb, &e), sort_functor_of_view(kb, &a)) {
                (Some(ev), Some(ab)) => sort_sym_compatible(kb, ev, ab),
                _ => false,
            }
        }
        // WI-342: every non-false arm of `types_compatible_term_dispatch` now has a
        // carrier-agnostic peer above; any other pair is a form mismatch, which the
        // term dispatch also rejects (`_ => false`). No re-ground bridge.
        _ => false,
    }
}

/// WI-342: the sole arrow subtyping, carrier-agnostic over [`TermView`] (both
/// the `TermId` dispatch via [`TermIdView`] and the `Value` carrier route here).
/// Contravariant param (`expected.param <: actual.param`), covariant result,
/// covariant effects via the carrier-agnostic [`subtype_effect_rows`]. A missing
/// effects field is the empty (pure) row.
fn arrow_compatible_view<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    let param_sym = kb.intern("param");
    let result_sym = kb.intern("result");
    let effects_sym = kb.intern("effects");

    // Contravariant param: expected.param <: actual.param.
    match (
        named_child_value(kb, actual, param_sym),
        named_child_value(kb, expected, param_sym),
    ) {
        (Some(ap), Some(ep)) => {
            if !types_compatible(kb, subst, &ep, &ap) {
                return false;
            }
        }
        _ => return false,
    }
    // Covariant result: actual.result <: expected.result.
    match (
        named_child_value(kb, actual, result_sym),
        named_child_value(kb, expected, result_sym),
    ) {
        (Some(ar), Some(er)) => {
            if !types_compatible(kb, subst, &ar, &er) {
                return false;
            }
        }
        _ => return false,
    }
    // Covariant effects: actual ⊆ expected (open-tail subsumption). A missing
    // side is the empty row (mirrors `arrow_compatible`).
    match (
        named_child_value(kb, actual, effects_sym),
        named_child_value(kb, expected, effects_sym),
    ) {
        (Some(ae), Some(ee)) => subtype_effect_rows(kb, subst, &ae, &ee),
        (None, None) => true,
        (Some(ae), None) => match kb.try_make_empty_effects_rows() {
            Some(er) => subtype_effect_rows(kb, subst, &ae, &TermIdView(er)),
            None => false,
        },
        (None, Some(ee)) => match kb.try_make_empty_effects_rows() {
            Some(er) => subtype_effect_rows(kb, subst, &TermIdView(er), &ee),
            None => false,
        },
    }
}

/// Per-(sort, parameter) variance, read from the declared `Covariant` /
/// `Contravariant` facts (proposal 035; `stdlib/anthill/reflect/typing.anthill`).
/// No fact ⇒ invariant (the safe default); both ⇒ bivariant. WI-293.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Variance {
    Covariant,
    Contravariant,
    Invariant,
    Bivariant,
}

/// Look up the declared variance of `sort`'s parameter `param` from the KB
/// variance facts. Reads the facts directly via the per-functor rule index — the
/// idiom every other typer fact reader uses (`sort_provides` / `requires`), NOT
/// SLD: the `effective_*` / `check_variance` rules in the stdlib are retained-but-
/// unconsumed scaffolding for the future inference layer (WI-184), so matching the
/// fact index directly is the consistent choice. `same_symbol` tolerates the
/// bare/qualified split (a fact's `sort: List` resolves to `anthill.prelude.List`;
/// its `param: T` stays a bare name).
fn declared_variance(kb: &KnowledgeBase, sort: Symbol, param: Symbol) -> Variance {
    let cov = matches_variance_fact(kb, "anthill.reflect.typing.Covariant", sort, param);
    let con = matches_variance_fact(kb, "anthill.reflect.typing.Contravariant", sort, param);
    match (cov, con) {
        (true, true) => Variance::Bivariant,
        (true, false) => Variance::Covariant,
        (false, true) => Variance::Contravariant,
        (false, false) => Variance::Invariant,
    }
}

/// Whether a `Covariant`/`Contravariant` fact (named by `fact_qn`) is asserted for
/// `(sort, param)`. Walks `rules_by_functor` and matches the `sort` / `param`
/// named args by symbol. The `entity Covariant(sort: Symbol, param: Symbol)`
/// declaration also shows up under this functor, but its arg values are the field
/// metadata type (`Symbol`), so it never matches a real `(sort, param)` lookup.
fn matches_variance_fact(kb: &KnowledgeBase, fact_qn: &str, sort: Symbol, param: Symbol) -> bool {
    let Some(functor) = kb.try_resolve_symbol(fact_qn) else { return false };
    kb.rules_by_functor(functor).into_iter().any(|rid| {
        let Some(named) = kb.fact_head_named_args(rid) else { return false };
        let sort_ok = get_named_arg(kb, &named, "sort")
            .and_then(|t| super::load::sort_ref_functor(kb, t))
            .is_some_and(|s| same_symbol(kb, s, sort));
        let param_ok = get_named_arg(kb, &named, "param")
            .and_then(|t| super::load::sort_ref_functor(kb, t))
            .is_some_and(|p| same_symbol(kb, p, param));
        sort_ok && param_ok
    })
}

/// Check one parameterized binding by the parameter's DECLARED variance
/// (WI-293), keyed on the supertype's variance contract (`expected_base`):
/// covariant → actual <: expected (the prior unconditional check);
/// contravariant → expected <: actual (flipped); invariant (default) → both
/// directions (equal); bivariant → either. The two-direction arms run on a
/// CLONED subst and commit only on success, so a failed direction can't leave
/// partial row/var bindings in the threaded `subst` (the per-direction hygiene
/// `join_types` uses; matters for the `||` bivariant arm, where direction-2 must
/// see a clean subst). Shared by [`parameterized_compatible_view`]'s same-base
/// arm (the actual carries the param) and its cross-sort provider arm (WI-387
/// FIX 2: the actual-side value comes from the actual's provider fact).
fn check_binding_by_variance<A: TermView, E: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    expected_base: Symbol,
    param: Symbol,
    av: &A,
    ev: &E,
) -> bool {
    match declared_variance(kb, expected_base, param) {
        Variance::Covariant => types_compatible(kb, subst, av, ev),
        Variance::Contravariant => types_compatible(kb, subst, ev, av),
        Variance::Invariant => {
            let mut probe = subst.clone();
            if types_compatible(kb, &mut probe, av, ev) && types_compatible(kb, &mut probe, ev, av) {
                *subst = probe;
                true
            } else {
                false
            }
        }
        Variance::Bivariant => {
            let mut probe = subst.clone();
            if types_compatible(kb, &mut probe, av, ev) {
                *subst = probe;
                true
            } else {
                types_compatible(kb, subst, ev, av)
            }
        }
    }
}

/// WI-342: the sole `parameterized` subtyping, carrier-agnostic over [`TermView`]
/// (both the `TermId` dispatch via [`TermIdView`] and the `Value` carrier route
/// here). Base compatible, then every EXPECTED binding must have a matching (by
/// param name) actual binding whose value is compatible — by the parameter's
/// DECLARED variance (WI-293), not unconditionally covariantly.
///
/// Bindings are read via [`extract_type`], which skips a *malformed* binding (one
/// whose value is missing). The deleted `TermId`-specific `parameterized_compatible`
/// instead `return false`d on such a binding — so this consolidation is marginally
/// more permissive on a corrupt EXPECTED type. Unreachable in practice
/// (`make_parameterized_type` always builds complete bindings), and it brings the
/// subtype direction into line with unify, which has always *skipped* malformed
/// bindings — removing a prior asymmetry rather than introducing one.
fn parameterized_compatible_view<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    // WI-361: base + bindings form-agnostic via `extract_type` (see
    // `unify_parameterized_view`); the base subtype check recurses the full
    // `types_compatible` on `Ref(S)` (preserving provider admissibility), not a
    // sort-symbol shortcut.
    let (actual_base, actual_bindings) = match extract_type(kb, actual) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return false,
    };
    let (expected_base, expected_bindings) = match extract_type(kb, expected) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return false,
    };
    let actual_base_ty = kb.alloc(Term::Ref(actual_base));
    let expected_base_ty = kb.alloc(Term::Ref(expected_base));
    if !types_compatible(kb, subst, &TermIdView(actual_base_ty), &TermIdView(expected_base_ty)) {
        return false;
    }

    // WI-387 FIX 2: the actual's cross-sort provider view (`List` provides
    // `Stream`) — loop-invariant (`actual_base`/`expected_base` are fixed for the
    // whole check), so resolve it ONCE rather than per missing expected param
    // (mirrors FIX 3's hoist of `provider_bindings`; `provider_spec_view_bindings`
    // is a full scan of every `SortProvidesInfo` fact). `None` for a same-base
    // check (no cross-sort translation) or a non-provider actual.
    let cross_sort_provider = if actual_base != expected_base {
        provider_spec_view_bindings(kb, actual_base, expected_base)
    } else {
        None
    };
    for (param, ev) in &expected_bindings {
        // The actual-side value to check against the expected binding `ev`:
        // normally the actual's OWN binding for `param`. WI-387 FIX 2: when the
        // actual lacks it AND the actual is a CROSS-SORT provider of the expected
        // (`List` lacks `Stream.E` but provides `Stream`), fall back to the value
        // the actual's provider fact supplies for that param (matched by short
        // name) — so `List[Elem]` conforms to `Stream[T = Elem, E = {}]` via
        // `provides Stream[E = {}]`. The actual was never translated through its
        // provider into the expected sort's param space before, so the missing
        // expected param rejected unconditionally. A param absent on BOTH sides,
        // or a SAME-base actual genuinely missing the param (`cross_sort_provider`
        // is `None`), still rejects: this LOOSENS the cross-sort case only and
        // cannot newly-reject existing code.
        let ok = match actual_bindings.iter().find(|(p, _)| p == param) {
            Some((_, av)) => check_binding_by_variance(kb, subst, expected_base, *param, av, ev),
            None => {
                let short = short_name_of(kb.resolve_sym(*param));
                let pv = cross_sort_provider.as_ref().and_then(|view| {
                    view.iter()
                        .find(|(p, _)| short_name_of(kb.resolve_sym(*p)) == short)
                        .map(|(_, v)| *v)
                });
                match pv {
                    Some(pv) => {
                        check_binding_by_variance(kb, subst, expected_base, *param, &TermIdView(pv), ev)
                    }
                    None => false,
                }
            }
        };
        if !ok {
            return false;
        }
    }
    true
}

/// Compatibility between the typer's `arrow(param, result, effects)` and the
/// stdlib `Function[A, B, E]` (in either order) — they denote the same callable
/// type. Carrier-agnostic over [`TermView`] (WI-361/WI-342): routed here from
/// BOTH the `TermId` dispatch ([`types_compatible_term_dispatch`], via
/// [`TermIdView`]) AND the `Value`-carrier dispatch
/// ([`types_compatible_view_structural`]), so a `Value::Node` callback arrow
/// checks against a `Function[A, B, E]` directly — natively, with no re-grounding
/// bridge. Decomposes both via [`arrow_parts`] (which yields
/// `None` for a non-`Function` parameterized type, so `arrow` vs `List[T]` stays
/// incompatible), checks contravariant param + covariant result, and (WI-332)
/// covariant effects via the carrier-agnostic [`subtype_effect_rows`]. WI-289.
fn arrow_function_compatible<A: TermView, E: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &E,
) -> bool {
    let (a_param, a_result, a_eff) = match arrow_parts(kb, actual) {
        Some(parts) => parts,
        None => return false,
    };
    let (b_param, b_result, b_eff) = match arrow_parts(kb, expected) {
        Some(parts) => parts,
        None => return false,
    };

    // Param is contravariant (expected param <: actual param), result
    // covariant — matching `arrow_compatible`. A missing param on either side
    // (a bare `Function` without an `A` binding, polymorphic) is unconstrained.
    let params_ok = match (&a_param, &b_param) {
        (Some(ap), Some(bp)) => types_compatible(kb, subst, bp, ap),
        _ => true,
    };
    if !params_ok {
        return false;
    }
    if !types_compatible(kb, subst, &a_result, &b_result) {
        return false;
    }

    // WI-332: covariant effects via [`subtype_effect_rows`], consistent with
    // `arrow_compatible`. **Missing E** is treated symmetrically with missing A:
    // omitting the binding means *polymorphic* (accept any), NOT *empty* — so
    // `Function[A, B]` (no E) accepts an effectful actual, while the explicit
    // `Function[A=…, B=…, E={}]` form keeps the closed-empty semantic and rejects
    // effectful actuals (regression-tested). The arrow side always synthesizes an
    // `effects` field, so its `None` arm is defensive only.
    //
    // WI-335: the threaded subst is shared across the param/result/effects
    // sub-checks so a row var bound in one position is visible in the others.
    match (a_eff, b_eff) {
        // Either side polymorphic in E → accept.
        (None, _) | (_, None) => true,
        (Some(ae), Some(ee)) => {
            // Normalize a legacy `List[Type]` E binding to a canonical row; an
            // already-canonical row (or a `Value::Node` row) passes through.
            let ae = canonical_effects_row(kb, &ae);
            let ee = canonical_effects_row(kb, &ee);
            subtype_effect_rows(kb, subst, &ae, &ee)
        }
    }
}

/// The `base` sort_ref of a `parameterized(base, bindings)` type term.
/// The base sort symbol of a parameterized type, form-agnostic (WI-361): the
/// deep `parameterized(base: sort_ref(S), …)` base field or the term-backed
/// `Fn{S, …}` functor, via [`type_head`]. `None` if not a parameterized type.
fn parameterized_base_sym(kb: &KnowledgeBase, ty: TermId) -> Option<Symbol> {
    match type_head(kb, &TermIdView(ty)) {
        TypeHead::Parameterized { base, .. } => Some(base),
        _ => None,
    }
}

/// Strict subtype check: actual is a proper subtype of expected.
/// `is_subtype(A, A)` is false. `is_subtype(red, Color)` is true.
///
/// WI-326: takes `&mut KnowledgeBase` (transitively, via
/// [`types_compatible`] → [`arrow_compatible_view`] → row subtyping).
///
/// WI-335: does NOT take a `&mut Substitution` argument. Unlike
/// [`types_compatible`], `is_subtype` is a context-free lattice
/// question — "is sub strictly less than sup?" — that should not depend
/// on any caller's bindings. We allocate a fresh substitution internally
/// so the answer is purely a function of `(kb, sub, sup)`. Callers that
/// want row-binding propagation should use [`types_compatible`] directly.
pub fn is_subtype(kb: &mut KnowledgeBase, sub: TermId, sup: TermId) -> bool {
    if sub == sup {
        return false;
    }
    let mut subst = Substitution::new();
    types_compatible(kb, &mut subst, &TermIdView(sub), &TermIdView(sup))
}

/// WI-287: one step up the entity→enclosing-sort chain. `Some(parent
/// sort as a type)` when `t` is a `sort_ref` to an entity nested in a
/// sort; `None` for a top-level sort (no enclosing parent) or a
/// non-`sort_ref` type. Lets [`join_types`] find a common supertype of
/// two distinct entity-typed branches even when leaves weren't already
/// widened to their sort.
fn widen_to_parent_sort(kb: &mut KnowledgeBase, t: TermId) -> Option<TermId> {
    let sym = extract_sort_ref_sym(kb, &TermIdView(t))?;
    let parent = kb.constructor_parent_sort(sym)?;
    Some(sort_term_to_type(kb, parent))
}

/// WI-342: carrier-agnostic widen for [`join_types`]. Only a nominal sort widens
/// up the entity→sort lattice; a `Value::Node` (an arrow / denoted-bearing type)
/// has no parent sort, so two incomparable Node arrows correctly fail to join.
fn widen_value(kb: &mut KnowledgeBase, v: &Value) -> Option<Value> {
    match v {
        Value::Term(t) => widen_to_parent_sort(kb, *t).map(Value::Term),
        _ => None,
    }
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
fn join_types(kb: &mut KnowledgeBase, a: Value, b: Value) -> Option<Value> {
    // WI-342: carrier-agnostic — `a`/`b` are `Value`s (a branch may be a
    // `Value::Node` lambda arrow). The join only ever RETURNS one of its inputs
    // (or widens a nominal side up the lattice); it never constructs a new type,
    // so no occurrence-level lub is needed. `types_compatible` is already
    // carrier-agnostic; we pass the `Value`s directly rather than re-grounding.
    // WI-361: dispatch on the CANONICAL type tag (`type_dispatch_name_view`), not
    // the raw functor — a term-backed type_var is `Fn{TypeExtractor.TypeVar, …}`
    // whose raw functor name is "TypeVar", so a raw `== "type_var"` check would
    // miss the inference wildcard and force the full lattice climb (spurious clash).
    if type_dispatch_name_view(kb, &a) == Some("type_var") {
        return Some(b);
    }
    if type_dispatch_name_view(kb, &b) == Some("type_var") {
        return Some(a);
    }
    let (mut a, mut b) = (a, b);
    // Bound defensively against any pathological parent cycle; real
    // entity→sort chains are a single level.
    for _ in 0..64 {
        // WI-335: each direction of the lattice check is an independent
        // question — allocate per-direction substs so a binding made
        // checking `a <: b` doesn't influence the `b <: a` check.
        let mut subst_ab = Substitution::new();
        let mut subst_ba = Substitution::new();
        match (types_compatible(kb, &mut subst_ab, &a, &b), types_compatible(kb, &mut subst_ba, &b, &a)) {
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
            (true, true) => return Some(more_general_type(kb, &a, &b)),
            // Incomparable: widen the entity side(s) one level and retry.
            // WI-293/WI-382: for two same-base parameterized types
            // (`Option[T=Cat]` / `Option[T=Dog]`) the STRICT lub would recurse
            // into the bindings by variance — covariant `join(av,bv)`, invariant
            // `av==bv`, contravariant `meet(av,bv)` — yielding `Option[T=Animal]`.
            // That CONSTRUCTS a type (join never does today) and needs a `meet`
            // (absent), so it is deferred to the WI-382 per-sort ORDER-relation
            // framework (join/meet as registered order ops). Until then we widen
            // the nominal side — a sound common supertype, not the strict lub.
            (false, false) => {
                let wa = widen_value(kb, &a);
                let wb = widen_value(kb, &b);
                if wa.is_none() && wb.is_none() {
                    return None;
                }
                if let Some(x) = wa {
                    a = x;
                }
                if let Some(y) = wb {
                    b = y;
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
fn more_general_type(kb: &KnowledgeBase, a: &Value, b: &Value) -> Value {
    match (more_general_form(kb, a), more_general_form(kb, b)) {
        (Some("sort_ref"), Some("parameterized")) => a.clone(),
        (Some("parameterized"), Some("sort_ref")) => b.clone(),
        _ => a.clone(),
    }
}

/// The form tag of a branch type for [`more_general_type`]'s bare-vs-
/// parameterized normalization, via the canonical classifier ([`type_head`]) so
/// it is carrier-agnostic. WI-361: a `Value::Node` parameterized reports
/// `parameterized` even though its raw functor is now the base sort (the carrier
/// mirrors the term backing `Fn{S,named}`), exactly like a term-backed
/// `Fn{S,named}` / `Ref(S)` on the `TermId` side — a raw-functor read would miss
/// it and mis-normalize the join to the over-specific side.
fn more_general_form(kb: &KnowledgeBase, v: &Value) -> Option<&'static str> {
    type_dispatch_name_view(kb, v)
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
    branch_tys: &[(Value, Option<Span>)],
    expected: Option<Value>,
    construct: &str,
) -> Result<Value, TypeError> {
    // Intern once up front so the type-lattice borrows below can take
    // `kb` immutably without colliding with a deferred `kb.intern`.
    let branch_ctx = TypeErrorContext::Rule {
        name: kb.intern(construct),
        field: RuleField::Whole,
    };
    // WI-342: branch types are carrier-agnostic `Value`s (a branch may be a
    // `Value::Node` lambda arrow). The join returns one of them — no
    // re-grounding. `TypeError` fields are `Value` (S2), so the branch carrier
    // flows straight into any diagnostic below.
    let first_ty: Value = match branch_tys.first() {
        Some((b, _)) => b.clone(),
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
    if let Some(exp) = &expected {
        for (bt, span) in branch_tys {
            // WI-335: each branch's conformance check is independent.
            let mut subst = Substitution::new();
            if !types_compatible(kb, &mut subst, bt, exp) {
                return Err(TypeError::TypeMismatch {
                    span: *span,
                    context: branch_ctx,
                    expected: exp.clone(),
                    actual: bt.clone(),
                });
            }
        }
    }

    // Synthesized type: the join (common supertype) of the branch types. Track the
    // branch that breaks the join (no common supertype) for diagnostics.
    let mut acc = first_ty;
    let mut clash: Option<(Value, Option<Span>)> = None;
    for (bt, span) in &branch_tys[1..] {
        match join_types(kb, acc.clone(), bt.clone()) {
            Some(j) => acc = j,
            None => {
                clash = Some((bt.clone(), *span));
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
            let mut subst = Substitution::new();
            if types_compatible(kb, &mut subst, &acc, &exp) {
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
            if type_dispatch_name_view(kb, &exp) == Some("type_var") {
                Err(TypeError::TypeMismatch {
                    span,
                    context: branch_ctx,
                    expected: acc.clone(),
                    actual: bt.clone(),
                })
            } else {
                Ok(exp)
            }
        }
        // No expected type and no common supertype — the top-less lattice
        // has no join, so the branch types genuinely clash.
        (Some((bt, span)), None) => {
            Err(TypeError::TypeMismatch {
                span,
                context: branch_ctx,
                expected: acc.clone(),
                actual: bt.clone(),
            })
        }
    }
}

/// sort_ref(name: A) compatible with sort_ref(name: B)
/// if A == B, or A is_entity_of B, or A refines B via requires.
fn sort_ref_compatible(kb: &KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    let actual_sym = match extract_sort_ref_sym(kb, &TermIdView(actual)) {
        Some(s) => s,
        None => return false,
    };
    let expected_sym = match extract_sort_ref_sym(kb, &TermIdView(expected)) {
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

/// WI-344: provider admissibility — `actual_sym` (or, if it is an entity,
/// its parent sort) declares `fact expected_sym[carrier = …]`, so a value
/// of `actual_sym` is usable where the spec `expected_sym` is required.
/// The value-position twin of `requires`: `requires X` and `fact X[Y]` are
/// the demand and supply ends of one relation, so a position demanding the
/// spec is discharged by the supplying fact (the same `SortProvidesInfo`
/// that `requires`-resolution and field-membership checks consult — see
/// `check_value_sort_membership`).
///
/// Deliberately base-only and called ONLY from the `(sort_ref, sort_ref)`
/// arm of [`types_compatible`] — NOT from `sort_sym_compatible`, because
/// that is also reached from the `sort_ref ↔ parameterized` arms' base
/// check, which drops the parameterized side's bindings. A
/// base-only accept there would admit a binding mismatch (a `Widget`
/// providing `Comparable[T = Widget]` accepted where `Comparable[T =
/// Gadget]` is expected). Restricting to `(sort_ref, sort_ref)` keeps it
/// sound: a bare spec carries no bindings, and the same-parameter
/// parameterized case (`List[T]` vs `Stream[T]`) reaches here only through
/// `parameterized_compatible`'s base check — where its per-binding loop
/// validates the bindings separately. The bare-value-vs-parameterized-spec
/// case (`Widget` vs `Comparable[T = Widget]`) stays rejected, as before;
/// admitting it needs binding-precise resolution (a follow-up, cf. WI-274's
/// `spec_resolves_at_bindings` for field positions). The fact is trusted to
/// mean `actual` implements `expected` (WI-343 validates that separately).
fn sort_provides_admissibly(kb: &KnowledgeBase, actual_sym: Symbol, expected_sym: Symbol) -> bool {
    if sort_provides(kb, actual_sym, expected_sym) {
        return true;
    }
    // An entity value's provision comes from its parent sort.
    if let Some(parent_tid) = kb.constructor_parent_sort(actual_sym) {
        if let Term::Fn { functor: parent_functor, .. } = kb.get_term(parent_tid) {
            return sort_provides_admissibly(kb, *parent_functor, expected_sym);
        }
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

/// WI-239 — a sort's **direct** `requires` entries: the top-level
/// `requires_tree` nodes' entries, substitution-composed/root-scoped
/// (same per-entry form `requires_chain` produces, but without the
/// transitive descent and without the pre-order duplication of shared
/// subtrees).
///
/// This is the tree-native requirement ABI: under the names model a
/// body reads only its DIRECT requires by `__req_<spec>` name; a
/// transitive require lives inside a direct requirement's tree-shaped
/// dict value, reached at runtime via `requirement_at_sort`. The
/// duplication the flat chain suffers — `requires Eq, Ordered` with
/// `Ordered requires Eq` flattening to `[Eq, Ordered, Eq]` — does not
/// arise here: the result is exactly `[Eq, Ordered]`.
///
/// Consumers that must remain transitive (resolution-tree subgoals are
/// recursive per-level, obligation checks, the `sort_refines` reach
/// relation) use `requires_chain` / `requires_chain_flat` instead.
pub fn direct_requires_chain(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Vec<RequiresEntry> {
    let tree = requires_tree(kb, sort_sym);
    tree.iter().map(|n| n.entry.clone()).collect()
}

/// Synthesize the requirement-param name for each entry of
/// `parent_sort`'s **direct** `requires` chain (WI-239). Returns
/// `Rc<Vec<Symbol>>` in chain order — index `k` is direct-require slot
/// `k`. Memoized on `synth_req_names_cache`; invalidated alongside
/// `requires_chain` caches when new `SortRequiresInfo` facts are
/// asserted.
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
/// WI-239: walks the DIRECT requires (top-level `requires_tree` nodes),
/// not the flattened transitive chain. The flat chain duplicated shared
/// subtrees — `requires Eq, Ordered` with `Ordered requires Eq` flattened
/// to `[Eq, Ordered, Eq]`, yielding a benign `__req_eq` name collision —
/// whereas the direct chain is exactly `[Eq, Ordered]`. A transitive
/// require is not a frame slot under this model; it lives inside a direct
/// requirement's tree-shaped dict value, reached via `requirement_at_sort`.
///
/// Uses `direct_requires_chain` (always substitution-composed) so the
/// names are deterministic across the typer and eval passes.
pub fn synth_req_names(kb: &mut KnowledgeBase, parent_sort: Symbol) -> Rc<Vec<Symbol>> {
    if let Some(cached) = kb.synth_req_names_cache.borrow().get(&parent_sort) {
        return cached.clone();
    }
    let chain = direct_requires_chain(kb, parent_sort);
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
/// `seed_entry_requirements`, etc.
///
/// WI-326 / WI-339: takes `&KnowledgeBase` because this function does
/// no mutation. The `types_compatible` chain moved to `&mut
/// KnowledgeBase` for row subtyping, but this site is independent of
/// that chain and reads the cached `requires_tree` immutably. Pre-WI-326
/// the doc-comment argued for `&KB` "so callers up the types_compatible
/// chain don't need to convert to &mut"; that rationale is stale now
/// that the chain is &mut everywhere — keeping & here is justified
/// purely on "the function is read-only".
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

    for rid in kb.rules_by_functor(requires_sym) {
        if !kb.is_fact(rid) { continue; }
        // A value-fact SortRequiresInfo (denoted-bearing spec) cannot yield a
        // term-form `RequiresEntry.spec` (a `TermId` consumed by the term-only
        // spec walks `unwrap_spec_view` / `substitute_in_spec`); occurrence-based
        // requires-chain resolution is gated effect-expressions-as-types work, so
        // skip it here. The spec is preserved faithfully on the fact for that pass
        // (rather than hit the term-only `rule_head` panic on a value head).
        let Some(named_args) = kb.fact_head_named_args(rid) else { continue };

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

    for rid in kb.rules_by_functor(sort_info_sym) {
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
pub fn extract_sort_ref_sym<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<Symbol> {
    // WI-361 stage 2: a bare sort is `Ref(S)` (term backing) or `sort_ref(name:
    // Ref(S))` (deep) — `type_head` classifies both as `SortRef`. Parameterized /
    // structural variants are not bare sorts → `None` (unchanged).
    // WI-342: carrier-agnostic over `TermView` (input principle) so a `Value`
    // sort type reads identically without re-grounding.
    match type_head(kb, ty) {
        TypeHead::SortRef(s) => Some(s),
        _ => None,
    }
}

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
    Parameterized { base: Symbol, bindings: Vec<(Symbol, Value)> },
    /// An arrow type — `arrow(param, result, effects)`.
    Arrow { param: Value, result: Value, effects: Value },
    /// A value standing in a type-argument position (`Modify[c]`) —
    /// `denoted(value)`; carries the value occurrence.
    Denoted(Value),
    /// WI-376: an expression-carried projection `s.T` / `s.Sort` — `value` is the
    /// receiver type occurrence (a param/local ref, or any typed expression),
    /// `member` the projected type-member name (`T`, `Sort`, `E`). The type-member
    /// sibling of [`TypeExtractor::Denoted`]; eliminated at the unify boundary by
    /// projecting the receiver's synthesized type (a `Denoted` value-in-type stays).
    ExprCarried { value: Value, member: Symbol },
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
    Error,
}

/// The structural kind of a type carrier WITHOUT materializing its children —
/// the cheap classification shared by [`extract_type`] (which adds the child
/// payloads) and the dispatch-key readers ([`sort_functor_of`], the callable
/// decomposition in [`arrow_parts`]) that only need the head. Dual-form:
/// recognizes both the deep representation
/// (`sort_ref` / `parameterized` / …) and the term backing (`Ref(S)` /
/// `Fn{S, named}`).
enum TypeHead {
    SortRef(Symbol),
    TypeVar(Symbol),
    /// `base` is the base sort symbol. WI-361: a parameterized type is the term
    /// backing `Fn{S, named}` (the base sort IS the functor, bindings ARE the named
    /// args) on both carriers — there is no `parameterized(base, bindings)` wrapper.
    Parameterized { base: Symbol },
    Arrow,
    Denoted,
    ExprCarried,
    EffectsRows,
    NamedTuple,
    Nothing,
    Error,
}

/// Classify a type carrier's head — see [`TypeHead`]. Cheap: reads at most the
/// `type_var` name, never the bindings / fields / arrow children. WI-361: a bare
/// sort is `Ref(S)` and a parameterized type is `Fn{S, named}` (functor = base
/// sort) on both carriers — there is no deep `sort_ref`/`parameterized` wrapper.
fn type_head<V: TermView>(kb: &KnowledgeBase, ty: &V) -> TypeHead {
    match ty.head(kb) {
        // Term-backed bare sort `Ref(S)`.
        ViewHead::Ref(s) => TypeHead::SortRef(s),
        ViewHead::Functor { functor: Some(f), named_arity, .. } => {
            match kb.qualified_name_of(f) {
                "anthill.prelude.TypeExtractor.TypeVar" => match view_child_sym(kb, ty, "name") {
                    Some(s) => TypeHead::TypeVar(s),
                    None => TypeHead::Error,
                },
                "anthill.prelude.TypeExtractor.Nothing" => TypeHead::Nothing,
                "anthill.prelude.TypeExtractor.Denoted" => TypeHead::Denoted,
                "anthill.prelude.TypeExtractor.ExprCarried" => TypeHead::ExprCarried,
                "anthill.prelude.TypeExtractor.EffectsRows" => TypeHead::EffectsRows,
                "anthill.prelude.TypeExtractor.Arrow" => TypeHead::Arrow,
                "anthill.prelude.TypeExtractor.NamedTuple" => TypeHead::NamedTuple,
                // Parameterized: the functor IS the base sort, the named args ARE
                // the bindings. A no-arg `Fn{f}` is malformed (a bare sort is
                // `Ref(S)`, never `Fn{S}`).
                _ if named_arity > 0 => TypeHead::Parameterized { base: f },
                _ => TypeHead::Error,
            }
        }
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
fn type_dispatch_name(kb: &KnowledgeBase, ty: TermId) -> Option<&'static str> {
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
fn type_dispatch_name_view<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<&'static str> {
    match type_head(kb, ty) {
        TypeHead::SortRef(_) => Some("sort_ref"),
        TypeHead::TypeVar(_) => Some("type_var"),
        TypeHead::Parameterized { .. } => Some("parameterized"),
        TypeHead::Arrow => Some("arrow"),
        TypeHead::Denoted => Some("denoted"),
        TypeHead::ExprCarried => Some("expr_carried"),
        TypeHead::EffectsRows => Some("effects_rows"),
        TypeHead::NamedTuple => Some("named_tuple"),
        TypeHead::Nothing => Some("nothing"),
        TypeHead::Error => None,
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
        TypeHead::EffectsRows => match view_child_value(kb, ty, "effects_expr") {
            Some(e) => TypeExtractor::EffectsRows(e),
            None => TypeExtractor::Error,
        },
        TypeHead::Arrow => match (
            view_child_value(kb, ty, "param"),
            view_child_value(kb, ty, "result"),
            view_child_value(kb, ty, "effects"),
        ) {
            (Some(param), Some(result), Some(effects)) => {
                TypeExtractor::Arrow { param, result, effects }
            }
            _ => TypeExtractor::Error,
        },
        TypeHead::NamedTuple => TypeExtractor::NamedTuple(named_tuple_fields(kb, ty)),
        TypeHead::Parameterized { base } => {
            // The named args ARE the bindings on both carriers (WI-361).
            TypeExtractor::Parameterized { base, bindings: term_backed_bindings(kb, ty) }
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
fn named_tuple_fields<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Vec<(Symbol, Value)> {
    match view_child_value(kb, ty, "fields") {
        Some(fields) => list_records_to_pairs(kb, &fields, "name", "type"),
        None => Vec::new(),
    }
}

/// A view's named child (keyed by short field name) as an owned [`Value`].
fn view_child_value<V: TermView>(kb: &KnowledgeBase, ty: &V, key: &str) -> Option<Value> {
    let sym = kb.lookup_symbol(key)?;
    named_child_value(kb, ty, sym)
}

/// A view's named child as the `Symbol` it references (`Ref(s)` / `Ident(s)`).
fn view_child_sym<V: TermView>(kb: &KnowledgeBase, ty: &V, key: &str) -> Option<Symbol> {
    match view_child_value(kb, ty, key)? {
        Value::Term(t) => match kb.get_term(t) {
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            _ => None,
        },
        _ => None,
    }
}

/// The "sort head" of an inferred type — the least declared sort it
/// widens to, as a `Symbol` (WI-284). It reads the typer-reflect Type
/// shapes (the form the typer stores in `inferred_type`, which is what
/// `min_sort` feeds it) and unwraps them to the underlying sort symbol:
///   - bare `Ref(S)`                    → `S`
///   - `Fn{S, named}` (parameterized)   → `S` (params dropped)
///   - everything else                  → `None`
/// `None` is the unresolved-type-variable case (dispatch-undecidable for the
/// type-directed `[simp]` engine) and the structural variants (arrow / named_tuple
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
/// widen to — `None` means `min_sort` is undefined for an occurrence typed as one
/// of them, the correct conservative answer (no `[simp]` rule targets those
/// positions yet).
pub fn sort_functor_of_view<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<Symbol> {
    match type_head(kb, ty) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s, .. } => Some(s),
        _ => None,
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
    sort_functor_of_view(kb, &occ.inferred_type()?)
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
        // WI-341 Stage A: carrier-agnostic read of the (now `Value`) param type.
        let is_carrier = carrier_sort_of_value(kb, param_type)
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

/// named_tuple(fields: [...]) <: named_tuple(fields: [...])
/// Width subtyping: actual may have more fields than expected.
/// Depth subtyping: each expected field's type must be a supertype of actual's.
/// WI-342: the sole `named_tuple` subtyping, carrier-agnostic over [`TermView`].
/// Width subtyping: every `expected` field must have a matching `actual` field
/// whose type is compatible. Fields are read by name via [`named_tuple_fields`].
fn named_tuple_compatible<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    let actual_fields = named_tuple_fields(kb, actual);
    let expected_fields = named_tuple_fields(kb, expected);
    for (exp_name, exp_type) in &expected_fields {
        match actual_fields.iter().find(|(n, _)| n == exp_name) {
            Some((_, act_type)) => {
                if !types_compatible(kb, subst, act_type, exp_type) {
                    return false;
                }
            }
            None => return false,
        }
    }
    true
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
    for rid in kb.rules_by_functor(sort_info_sym) {
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
    declared_type: &Value,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    // WI-361: dispatch on the canonical form tag so a term-backed `Ref(S)` /
    // `Fn{S,named}` routes to the same arms as the deep `sort_ref` / `parameterized`.
    // WI-342: the declared type is carrier-agnostic — read it through [`TermView`]
    // (a `Value::Node` denoted-bearing field type is handled, not re-grounded).
    let type_functor = type_dispatch_name_view(kb, declared_type);

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
    declared_type: &Value,
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
                    expected: type_display_name_value(kb, declared_type),
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
    declared_type: &Value,
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
        expected: type_display_name_value(kb, declared_type),
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
    declared_type: &Value,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    // WI-361: read base + bindings form-agnostically — deep
    // `parameterized(base: sort_ref(S), bindings)` or term-backed `Fn{S, named}`.
    // WI-342: carrier-agnostic over [`TermView`] (the declared type is a `Value`).
    let TypeExtractor::Parameterized { base: base_sym, bindings } =
        extract_type(kb, declared_type)
    else {
        return None;
    };

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
            let goal_bindings = declared_type_goal_bindings(kb, &bindings);
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
                expected: type_display_name_value(kb, declared_type),
                actual: extract_parent_name(kb, parent),
            });
        }
    }

    // Build substitution from type bindings (T → Int). Look up each
    // param's `Var` scoped to `base_sym` — the SortAlias index has
    // multiple entries for short names like "T" (List, Option, Stream,
    // …), and an unscoped short-name lookup may return the wrong sort's
    // `Var`, leaving `walk_type` on the entity's field types
    // unsubstituted. WI-361: bindings come carrier-agnostic from `extract_type`.
    let mut subst = Substitution::new();
    for (psym, value_type) in &bindings {
        if let Some(vid) = type_param_vid_in_sort(kb, base_sym, *psym) {
            // WI-342: bind carrier-agnostically (`bind_value`) so a `Value::Node`
            // binding is carried; `walk_type_value` resolves a field type through it.
            subst.bind_value(vid, value_type.clone());
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

    for (fsym, declared_field_type) in &ctor_field_types {
        let fval = match val_named_args.iter().find(|(s, _)| s == fsym) {
            Some((_, v)) => *v,
            None => continue,
        };
        if matches!(kb.get_term(fval), Term::Var(_)) { continue; }

        // Walk the field type through the substitution to resolve type params,
        // carrier-agnostically (WI-342) — a `Value::Node` field type is carried.
        let instantiated_type = walk_type_value(kb, &subst, declared_field_type);

        if let Some(err) = check_value_against_type(kb, fval, &instantiated_type, entity_sym, *fsym, span) {
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
    bindings: &[(Symbol, Value)],
) -> SmallVec<[(Symbol, TermId); 2]> {
    // WI-361: `bindings` are the carrier-agnostic `(param, value-type)` pairs from
    // [`extract_type`]; a `Value::Term` value canonicalizes into the bare-sort-ref
    // shape the instance resolver matches against.
    bindings
        .iter()
        .filter_map(|(p, v)| match v {
            Value::Term(t) => Some((*p, canonicalize_goal_value(kb, *t))),
            _ => None,
        })
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
    if let Some(s) = extract_sort_ref_sym(kb, &TermIdView(value)) {
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
    // Field validation resolves a spec at declared bindings — no call-site
    // receiver, so no carrier discrimination (WI-350).
    let goal = SortGoal { spec_sort, bindings, carrier: None };
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

        for rid in kb.rules_by_functor(ctor_sym) {
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

            for (field_sym, declared_type) in &field_types {
                let field_sym = *field_sym;
                let field_value = match named_args.iter().find(|(s, _)| *s == field_sym) {
                    Some((_, v)) => *v,
                    None => continue,
                };

                if matches!(kb.get_term(field_value), Term::Var(Var::Global(_) | Var::DeBruijn(_))) {
                    continue;
                }

                // WI-342: the field type is a carrier-agnostic `Value` — checked in
                // place, no re-ground.
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
pub(crate) fn sort_provides(kb: &KnowledgeBase, carrier: Symbol, spec: Symbol) -> bool {
    let provides_sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return false,
    };
    for rid in kb.rules_by_functor(provides_sym) {
        // A value-fact SortProvidesInfo (denoted-bearing spec) is skipped;
        // occurrence-based provides lookup is gated effect-expressions-as-types
        // work (avoid the term-only `rule_head` panic on a value head).
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
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

/// WI-392: build a substitution that Skolemizes an operation's own declared type
/// parameters — each `Var::Global(vid)` ↦ a fresh `Var::Rigid`. Applied (via
/// `walk_type_deep_value`) to the op's param types / return / effects before its
/// body is checked, so the body sees its type parameters as rigid
/// (fixed-but-abstract) constants: usable but not solvable. Mirrors the
/// resolver's `forall_impl` skolemisation (`resolve.rs` `step_forall_impl`), the
/// only other site that mints `Var::Rigid`.
fn rigidify_op_type_params(
    kb: &mut KnowledgeBase,
    type_params: &[(Symbol, TermId)],
) -> Substitution {
    let mut rigidify = Substitution::new();
    for (_, var_tid) in type_params {
        if let Term::Var(Var::Global(vid)) = kb.get_term(*var_tid) {
            let vid = *vid;
            let fresh = kb.fresh_var(vid.name());
            let rigid_term = kb.alloc(Term::Var(Var::Rigid(fresh)));
            rigidify.bind_term(vid, rigid_term);
        }
    }
    rigidify
}

/// Check operation bodies against their declared return types.
fn check_operation_bodies(kb: &mut KnowledgeBase, op_syms: &[Symbol], errors: &mut Vec<TypeError>) {
    struct OpInfo {
        op_sym: Symbol,
        return_type: Value,  // WI-341 carrier-agnostic
        declared_effects: Vec<Value>,
        body_node: Rc<NodeOccurrence>,
        params: Vec<(Symbol, Value)>,
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
        // WI-392: while CHECKING this operation's body, its OWN declared type
        // parameters are universally quantified — Skolemize them to `Var::Rigid`
        // so the body may USE them but never CONSTRAIN them (a `Rigid` unifies
        // only with itself, so e.g. `add(h, 1)` on `h: Elem` is correctly
        // rejected; the body must type-check for ALL `Elem`). Inner calls keep
        // their own FLEXIBLE `Global` type params, which solve TO these rigids
        // (rigid ⇒ global; `resolved_var` matches only `Global`), and
        // `check_unconstrained_type_params` passes them unchanged (it flags only
        // bare `Global`s) — so a self-receiver / recursive call whose type param
        // resolves to the enclosing rigid is no longer a false "unconstrained"
        // leak. Declared ⇒ check-mode ⇒ rigid; an *inferred* param would stay
        // flexible (you cannot infer a rigid), but operation type params are
        // always declared. A rigid in an effect-row position is CHECKED
        // structurally, never *bound* (`bind_row_tail` is the binding path), so
        // its WI-336 rigid-tail rejection is not on the checking path.
        let (params, return_type, declared_effects) = if rec.type_params.is_empty() {
            (rec.params, rec.return_type, rec.effects)
        } else {
            let rigidify = rigidify_op_type_params(kb, &rec.type_params);
            let params = rec
                .params
                .iter()
                .map(|(n, t)| (*n, walk_type_deep_value(kb, &rigidify, t)))
                .collect();
            let return_type = walk_type_deep_value(kb, &rigidify, &rec.return_type);
            let declared_effects = rec
                .effects
                .iter()
                .map(|e| walk_type_deep_value(kb, &rigidify, e))
                .collect();
            (params, return_type, declared_effects)
        };
        ops_to_check.push(OpInfo {
            op_sym: rec.op_sym,
            return_type,
            declared_effects,
            body_node,
            params,
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
            // WI-341 Stage A: op param types are carrier-agnostic `Value`. A
            // callback param whose arrow effect is denoted-bearing binds as a
            // `Value::Node` arrow; a ground param as `Value::Term`.
            env.bind_var(*name, ty.clone());
        }

        // WI-270: thread the declared return type as the body's
        // top-down `expected`. The body's `let v: T = …`-style
        // annotations and inner Apply/Constructor calls then see a
        // caller-side hint that pins otherwise-free type-params.
        // WI-341: `type_check_node`'s top-down hint is a ground `TermId`; pass it
        // for a ground return type, drop it (`None`) for a `Value::Node` (denoted-
        // bearing) return — never materialize the occurrence into the hint.
        match type_check_node(kb, &env, &op.body_node, Some(op.return_type.clone())) {
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
                let mut subst = Substitution::new();
                // WI-341/342: both sides are carrier-agnostic `Value` — the
                // subtype check takes them directly (`Value: TermView`), where a
                // lambda's `Value::Node` arrow flows cross-carrier against the
                // declared return arrow. `TypeError` fields are `Value` (S2), so
                // the carrier flows straight into the diagnostic (no re-grounding).
                if !types_compatible(kb, &mut subst, &result.ty, &op.return_type) {
                    errors.push(TypeError::TypeMismatch {
                        span: None,
                        context: TypeErrorContext::OperationReturn { op_name: op.op_sym },
                        expected: op.return_type.clone(),
                        actual: result.ty.clone(),
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
                    &op.return_type,
                    op.op_sym,
                    op_result_sym,
                    &region_sorts,
                    &result.effects,
                );
                // Validate every effect the body produces was declared. WI-365:
                // compare by representation-independent STRUCTURAL IDENTITY
                // (`views_structurally_equal`), not by rendered display name. A
                // name compare is fragile in both directions — distinct effects
                // can share a name, and one effect can render two ways across
                // representations. The concrete failure: an abstract sort's
                // `effects E` row variable is stored as `Ref(S.E)` in the
                // signature, but a body call — the abstract self-receiver spec
                // op (`splitFirst(s)`) or the recursive op itself
                // (`collect(rest)`) — has that row variable resolved through its
                // `SortAlias` to the (anonymous) alias `Var`. As names those are
                // `"E"` vs `"?_"` and never match, so a pure-`effects E` body
                // spuriously reported `undeclared effect: ?_`.
                //
                // Canonicalize first, then compare structurally — mirroring how
                // the return-type check above (`types_compatible`) already walks
                // both sides. The (empty) `canon_subst` walk collapses a
                // sort-parameter `Ref(S.E)` to its alias `Var` on both the
                // declared and the body side, so the row variable's two encodings
                // agree; a concrete effect sort (`Error`) is not a sort param and
                // walks to itself; a denoted `Modify[c]` (a `Value::Node`)
                // compares structurally against another via the same `TermView`
                // recursion. Diagnostics still render the raw (readable) names.
                let canon_subst = Substitution::new();
                let declared_canon: Vec<Value> = op.declared_effects.iter()
                    .map(|e| walk_type_deep_value(kb, &canon_subst, e))
                    .collect();
                let declared_display: Vec<String> = op.declared_effects.iter()
                    .map(|e| type_display_name_value(kb, e))
                    .collect();
                for effect in &ext_effects {
                    let effect_canon = walk_type_deep_value(kb, &canon_subst, effect);
                    let declared = declared_canon.iter()
                        .any(|d| views_structurally_equal(kb, &effect_canon, d));
                    if !declared {
                        errors.push(TypeError::Other {
                            span: op.span,
                            context: TypeErrorContext::OperationEffects { op_name: op.op_sym },
                            expected: format!("declared: [{}]", declared_display.join(", ")),
                            actual: format!("undeclared effect: {}", type_display_name_value(kb, effect)),
                        });
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
        // WI-342 P3: keyed by var id → its constrained type, carried
        // carrier-agnostically as `Value` (today every entry is `Value::Term`
        // from `OperationInfo`/entity-field metadata; it holds a `Value::Node`
        // type unchanged once those producers migrate in P4).
        let mut var_types: HashMap<u32, Value> = std::collections::HashMap::new();

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
    var_types: &mut HashMap<u32, Value>,
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
                    // WI-341 Stage A: seed inference from the param type
                    // carrier-agnostically (a `Value::Node` callback-arrow param too).
                    if let Some((_, param_type)) = op.params.get(i) {
                        constrain_var_type(kb, arg, param_type, var_types, subst);
                    }
                }
            } else if let Some(field_types) = kb.entity_field_types(functor) {
                // Entity constructor: match named args to field types
                let field_types = field_types.to_vec();
                for (field_sym, field_type) in &field_types {
                    if let Some((_, arg_tid)) = named_args.iter().find(|(s, _)| s == field_sym) {
                        let arg_tid = *arg_tid;
                        // WI-341 Stage A: field type is a carrier-agnostic `Value` —
                        // constrain directly, no re-grounding to a term.
                        constrain_var_type(kb, arg_tid, field_type, var_types, subst);
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
    expected_type: &Value,
    var_types: &mut HashMap<u32, Value>,
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
    expected_type: &Value,
    var_types: &mut HashMap<u32, Value>,
    subst: &mut Substitution,
) {
    if let Some(existing) = var_types.get(&vid) {
        if !unify_types(kb, subst, existing, expected_type) {
            subst.contradiction = true;
        }
    } else {
        var_types.insert(vid, expected_type.clone());
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
    var_types: &mut HashMap<u32, Value>,
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
            // WI-342: a ground `Value::Term` annotation can carry nested op/entity
            // calls to constrain; a `Value::Node` (denoted) annotation is a pure
            // type occurrence with none, so it contributes no constraints.
            if let Some(Value::Term(t)) = type_annotation {
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
    var_types: &mut HashMap<u32, Value>,
    subst: &mut Substitution,
) {
    if let Some(op) = lookup_operation_info_full(kb, functor) {
        for (i, arg) in pos_args.iter().enumerate() {
            // WI-341 Stage A: seed inference from the param type carrier-agnostically.
            if let Some((_, param_type)) = op.params.get(i) {
                constrain_occ_var_type(kb, arg, param_type, var_types, subst);
            }
        }
    } else if let Some(field_types) = kb.entity_field_types(functor) {
        let field_types = field_types.to_vec();
        for (field_sym, field_type) in &field_types {
            if let Some((_, arg)) = named_args.iter().find(|(s, _)| s == field_sym) {
                // WI-341 Stage A: field type is a carrier-agnostic `Value` —
                // constrain directly, no re-grounding to a term.
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
    expected_type: &Value,
    var_types: &mut HashMap<u32, Value>,
    subst: &mut Substitution,
) {
    let vid = match occ.as_expr() {
        Some(Expr::Var(Var::Global(vid))) => vid.raw(),
        Some(Expr::Var(Var::DeBruijn(idx))) => *idx,
        _ => return,
    };
    constrain_vid(kb, vid, expected_type, var_types, subst);
}

#[cfg(test)]
mod p3_tests {
    //! WI-342 P3 — carrier-agnostic `unify_types` over `TermView`.
    use super::unify_types;
    use crate::eval::value::Value;
    use crate::kb::load::register_prelude;
    use crate::kb::node_occurrence::TypeNode;
    use crate::kb::subst::Substitution;
    use crate::kb::term::{Term, Var};
    use crate::kb::term_view::TermIdView;
    use crate::kb::KnowledgeBase;
    use crate::span::{SourceId, SourceSpan};
    use std::rc::Rc;

    fn kb_with_prelude() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        kb
    }

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 1)
    }

    fn fresh_vid(kb: &mut KnowledgeBase, name: &str) -> crate::kb::term::VarId {
        let sym = kb.intern(name);
        kb.fresh_var(sym)
    }

    /// A fresh inference var `?T` binds to a `Value`-carried `denoted` and
    /// resolves back to it (identity preserved) — the var↔Value-carried path.
    #[test]
    fn unify_var_with_value_carried_denoted() {
        let mut kb = kb_with_prelude();
        let c = kb.intern("c");
        let denoted_occ = kb.make_denoted_occ_ref(c, span(), None);
        let tname = kb.intern("T");
        let vid = kb.fresh_var(tname);
        let var_t = kb.alloc(Term::Var(Var::Global(vid)));

        let mut subst = Substitution::new();
        assert!(unify_types(&mut kb, &mut subst, &TermIdView(var_t), &denoted_occ));

        match subst.resolve_as_value(vid) {
            Some(Value::Node(occ)) => {
                assert!(Rc::ptr_eq(occ, &denoted_occ), "binding preserves occurrence identity");
                assert!(matches!(occ.as_type(), Some(TypeNode::Denoted { .. })));
            }
            other => panic!("expected ?T → Value::Node(denoted), got {other:?}"),
        }
    }

    // WI-366: `cross_carrier_denoted_unify` / `ground_denoted_unchanged` deleted
    // with `make_denoted` — they built a GROUND `denoted` term, a carrier no
    // production path produces (every value-in-type mints a `Value::Node` via
    // `make_denoted_occ`). The live Node-denoted unify is covered by
    // `value_value_parameterized_denoted_unify`; mixed TermId-vs-Node dispatch by
    // `occurs_check_var_in_node_tuple_field`.

    /// `bind_value` contradiction via the extended `occurrence_structural_eq`:
    /// binding a var twice to structurally-equal (distinct `Rc`) Value-carried
    /// types must NOT contradict; to a different one must.
    #[test]
    fn bind_value_structural_eq_no_false_contradiction() {
        let mut kb = kb_with_prelude();
        let vid = fresh_vid(&mut kb, "T");
        let c = kb.intern("c");
        let d = kb.intern("d");
        let occ_c1 = kb.make_denoted_occ_ref(c, span(), None);
        let occ_c2 = kb.make_denoted_occ_ref(c, span(), None); // equal, distinct Rc
        let occ_d = kb.make_denoted_occ_ref(d, span(), None);

        let mut s = Substitution::new();
        s.bind_value(vid, Value::Node(occ_c1));
        s.bind_value(vid, Value::Node(occ_c2));
        assert!(!s.is_contradiction(), "equal Value-carried types must not contradict");
        s.bind_value(vid, Value::Node(occ_d));
        assert!(s.is_contradiction(), "a distinct Value-carried type contradicts");
    }
}

#[cfg(test)]
mod wi361_reader_tests {
    //! WI-361 stage 2: the dispatch-key reader `sort_functor_of` classifies via
    //! `type_head`, so it reads the TERM-BACKED form (`Ref(S)` bare sort,
    //! `Fn{S, named}` parameterized — base sort IS the functor) identically to
    //! the deep `sort_ref`/`parameterized` form. Producers still build the deep
    //! form today, so the test manually constructs the term backing to exercise
    //! the migrated path. (The deep-form path stays covered by the wider suite;
    //! the carrier-agnostic classifier itself by `type_extract_test`.)
    use super::{extract_sort_ref_sym, sort_functor_of};
    use crate::kb::term_view::TermIdView;
    use crate::intern::Symbol;
    use crate::kb::load::register_prelude;
    use crate::kb::term::{Term, TermId};
    use crate::kb::KnowledgeBase;
    use smallvec::SmallVec;

    fn kb_with_prelude() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        kb
    }

    /// Term backing `Fn{base, named:[(param, Ref(arg))]}` — a parameterized type
    /// whose base sort IS the functor (no deep `parameterized` wrapper).
    fn term_backed_param(kb: &mut KnowledgeBase, base: Symbol, param: Symbol, arg: Symbol) -> TermId {
        let arg_ref = kb.alloc(Term::Ref(arg));
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named.push((param, arg_ref));
        kb.alloc(Term::Fn { functor: base, pos_args: SmallVec::new(), named_args: named })
    }

    #[test]
    fn sort_functor_of_reads_term_backed_parameterized() {
        let mut kb = kb_with_prelude();
        let list = kb.intern("List");
        let int = kb.intern("Int");
        let t = kb.intern("T");

        // Term-backed `List[T = Int]` == `Fn{List, named:[(T, Ref(Int))]}` — the
        // functor IS the base sort; pre-migration this returned None.
        let tb = term_backed_param(&mut kb, list, t, int);
        assert_eq!(sort_functor_of(&kb, tb), Some(list), "term-backed Fn{{List,..}} -> List");

        // The same via the real builder `make_parameterized_type` (also term-backed).
        let int_ref = kb.make_sort_ref(int);
        let base = kb.make_sort_ref(list);
        let built = kb.make_parameterized_type(base, &[(t, int_ref)]);
        assert_eq!(sort_functor_of(&kb, built), Some(list), "make_parameterized_type -> List");

        // Term-backed bare sort `Ref(Int)`.
        let bare = kb.alloc(Term::Ref(int));
        assert_eq!(sort_functor_of(&kb, bare), Some(int), "bare Ref(Int) -> Int");

        // A structural variant (arrow) has no sort head.
        let unit = kb.intern("Unit");
        let unit_ref = kb.make_sort_ref(unit);
        let arrow = kb.make_arrow_type(unit_ref, unit_ref, &[]);
        assert_eq!(sort_functor_of(&kb, arrow), None, "arrow has no sort head");
    }

    #[test]
    fn extract_sort_ref_sym_reads_term_backed_bare_ref() {
        let mut kb = kb_with_prelude();
        let int = kb.intern("Int");
        let list = kb.intern("List");
        let t = kb.intern("T");

        // Term-backed bare sort `Ref(Int)` — pre-migration this returned None.
        let bare = kb.alloc(Term::Ref(int));
        assert_eq!(extract_sort_ref_sym(&kb, &TermIdView(bare)), Some(int), "bare Ref(Int) -> Int");

        // The same via the real builder `make_sort_ref` (also `Ref(Int)`).
        let built = kb.make_sort_ref(int);
        assert_eq!(extract_sort_ref_sym(&kb, &TermIdView(built)), Some(int), "make_sort_ref(Int) -> Int");

        // A parameterized type is NOT a bare sort ref.
        let tb = term_backed_param(&mut kb, list, t, int);
        assert_eq!(extract_sort_ref_sym(&kb, &TermIdView(tb)), None, "Fn{{List,..}} is not a bare sort ref");
    }

    /// The unify/subtype STRUCTURAL dispatch reads a term-backed `Fn{S, named}` as
    /// a parameterized type (via `type_dispatch_name`/`extract_type`): the same
    /// instantiation unifies and subtypes, a differing binding is rejected.
    #[test]
    fn parameterized_unify_subtype_term_backed() {
        use super::{types_compatible, unify_types};
        use crate::kb::subst::Substitution;
        use crate::kb::term_view::TermIdView;

        let mut kb = kb_with_prelude();
        let list = kb.intern("List");
        let int = kb.intern("Int");
        let string = kb.intern("String");
        let t = kb.intern("T");

        let tb_int = term_backed_param(&mut kb, list, t, int);
        let tb_int2 = term_backed_param(&mut kb, list, t, int);
        let tb_str = term_backed_param(&mut kb, list, t, string);

        // Same instantiation unifies; a differing binding is rejected.
        let mut s = Substitution::new();
        assert!(
            unify_types(&mut kb, &mut s, &TermIdView(tb_int), &TermIdView(tb_int2)),
            "List[T=Int] unifies with itself"
        );
        let mut s2 = Substitution::new();
        assert!(
            !unify_types(&mut kb, &mut s2, &TermIdView(tb_int), &TermIdView(tb_str)),
            "List[T=Int] vs List[T=String] rejected at the binding"
        );

        // Subtype: same accept; differing reject.
        let mut s4 = Substitution::new();
        assert!(
            types_compatible(&mut kb, &mut s4, &TermIdView(tb_int), &TermIdView(tb_int2)),
            "List[T=Int] <: List[T=Int]"
        );
        let mut s5 = Substitution::new();
        assert!(
            !types_compatible(&mut kb, &mut s5, &TermIdView(tb_int), &TermIdView(tb_str)),
            "List[T=Int] is not <: List[T=String]"
        );
    }

    /// WI-361 PRODUCER FLIP: `make_sort_ref` emits the bare term `Ref(S)` and
    /// `make_parameterized_type` the term backing `Fn{S, named}` (base sort IS the
    /// functor, no `sort_ref`/`parameterized` wrapper); the readers classify the
    /// flipped producers' output, and empty bindings collapse to the bare `Ref(S)`.
    #[test]
    fn producer_flip_emits_term_backing() {
        use super::{extract_type, sort_functor_of, TypeExtractor};
        use crate::kb::term_view::TermIdView;
        let mut kb = kb_with_prelude();
        let int = kb.intern("Int");
        let list = kb.intern("List");
        let t = kb.intern("T");

        // make_sort_ref(Int) -> the bare term `Ref(Int)`, NOT `sort_ref(name: …)`.
        let sr = kb.make_sort_ref(int);
        assert!(matches!(kb.get_term(sr), Term::Ref(s) if *s == int),
            "make_sort_ref flips to Ref(S); got {:?}", kb.get_term(sr));

        // make_parameterized_type(make_sort_ref(List), [T = Ref(Int)]) ->
        // `Fn{List, named:[(T, Ref(Int))]}` — the base sort IS the functor.
        let base = kb.make_sort_ref(list);
        let int_ref = kb.make_sort_ref(int);
        let p = kb.make_parameterized_type(base, &[(t, int_ref)]);
        match kb.get_term(p).clone() {
            Term::Fn { functor, named_args, pos_args } => {
                assert_eq!(functor, list, "functor IS the base sort (List)");
                assert!(pos_args.is_empty());
                assert_eq!(named_args.len(), 1);
                assert_eq!(named_args[0].0, t, "the binding is the `T` named arg");
            }
            other => panic!("make_parameterized_type flips to Fn{{S, named}}; got {other:?}"),
        }

        // make_parameterized_type with NO bindings collapses to the bare sort
        // `Ref(S)` — a no-binding parameterized IS the bare sort, never a
        // degenerate no-arg `Fn{S}` (which would classify as `Error`).
        let empty_base = kb.make_sort_ref(list);
        let empty_param = kb.make_parameterized_type(empty_base, &[]);
        assert!(matches!(kb.get_term(empty_param), Term::Ref(s) if *s == list),
            "empty-bindings parameterized collapses to bare Ref(S); got {:?}", kb.get_term(empty_param));

        // Readers classify the flipped producers' output.
        assert!(matches!(extract_type(&kb, &TermIdView(sr)), TypeExtractor::SortRef(s) if s == int));
        assert!(matches!(extract_type(&kb, &TermIdView(p)), TypeExtractor::Parameterized { base, .. } if base == list));
        assert_eq!(sort_functor_of(&kb, p), Some(list), "term-backed Fn{{List,..}} -> List");
    }
}

#[cfg(test)]
mod p4_tests {
    //! WI-342 P4-A — carrier-agnostic structural unification of a
    //! `Value`-carried `parameterized` (the denoted-bearing effect label),
    //! standalone (not yet inside a row — that's P4-B).
    use super::unify_types;
    use crate::kb::load::register_prelude;
    use crate::kb::node_occurrence::{NodeOccurrence, TypeChild};
    use crate::kb::subst::Substitution;
    use crate::kb::term::{Term, TermId};
    use crate::kb::term_view::TermIdView;
    use crate::kb::KnowledgeBase;
    use crate::span::{SourceId, SourceSpan};
    use std::rc::Rc;

    fn kb_with_prelude() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        kb
    }

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 1)
    }

    /// `Value`-carried `parameterized(sort_ref(Modify), [p = denoted(Ref sym)])`
    /// — a ground `sort_ref` base, a poisoned (denoted-bearing) binding value.
    fn occ_param(kb: &mut KnowledgeBase, modify: crate::intern::Symbol, p: crate::intern::Symbol, sym: crate::intern::Symbol) -> Rc<NodeOccurrence> {
        let base = kb.make_sort_ref(modify);
        let denoted_occ = kb.make_denoted_occ_ref(sym, span(), None);
        kb.make_parameterized_occ(
            TypeChild::Ground(base),
            vec![(p, TypeChild::Node(denoted_occ))],
            span(),
            None,
        )
    }

    /// WI-361 regression: `more_general_type`'s bare-vs-parameterized join
    /// normalization must classify a `Value::Node` parameterized via the canonical
    /// `type_head` tag, not its raw functor. After the carrier flip the Node's raw
    /// functor is the base sort (`Modify`), not `parameterized`; a raw-functor read
    /// tags it `None` and the join returns the OVER-SPECIFIC parameterized side
    /// instead of the more-general bare sort. Both orderings must yield the bare.
    #[test]
    fn more_general_type_prefers_bare_over_value_node_parameterized() {
        use crate::eval::value::Value;
        let mut kb = kb_with_prelude();
        let modify = kb.intern("Modify");
        let p = kb.intern("resource");
        let c = kb.intern("c");

        // `Value::Node` `Modify[resource = denoted(c)]` (head functor = base sort
        // `Modify` post-flip) vs the bare sort `Modify` (`Ref(Modify)`).
        let node_param = Value::Node(occ_param(&mut kb, modify, p, c));
        let bare_tid = kb.make_sort_ref(modify);
        let bare = Value::Term(bare_tid);

        let node_first = super::more_general_type(&kb, &node_param, &bare);
        let bare_first = super::more_general_type(&kb, &bare, &node_param);
        assert!(
            matches!(node_first, Value::Term(t) if t == bare_tid),
            "join should pick the more-general bare sort, got {node_first:?}",
        );
        assert!(
            matches!(bare_first, Value::Term(t) if t == bare_tid),
            "join must be commutative (bare sort either way), got {bare_first:?}",
        );
    }

    /// Value-vs-Value: two distinct-`Rc` `Value`-carried `Modify[c]` unify;
    /// `Modify[c]` vs `Modify[d]` is rejected.
    #[test]
    fn value_value_parameterized_denoted_unify() {
        let mut kb = kb_with_prelude();
        let modify = kb.intern("Modify");
        let p = kb.intern("resource");
        let c = kb.intern("c");
        let d = kb.intern("d");

        let occ_c1 = occ_param(&mut kb, modify, p, c);
        let occ_c2 = occ_param(&mut kb, modify, p, c);
        let mut s = Substitution::new();
        assert!(unify_types(&mut kb, &mut s, &occ_c1, &occ_c2), "Value Modify[c] vs Value Modify[c]");

        let occ_d = occ_param(&mut kb, modify, p, d);
        let mut s2 = Substitution::new();
        assert!(!unify_types(&mut kb, &mut s2, &occ_c1, &occ_d), "Value Modify[c] vs Value Modify[d]");
    }

    /// `Value`-carried arrow `Unit -> Unit` with a single present effect label
    /// `Modify[sym]`: arrow → effects_rows → present → parameterized(Modify,
    /// denoted(Ref sym)). Param/result are ground; the effect label is poisoned.
    fn value_modify_arrow(
        kb: &mut KnowledgeBase,
        modify: crate::intern::Symbol,
        p: crate::intern::Symbol,
        unit_ref: TermId,
        sym: crate::intern::Symbol,
    ) -> Rc<NodeOccurrence> {
        let label = occ_param(kb, modify, p, sym);
        let present = kb.make_present_occ(TypeChild::Node(label), span(), None);
        let rows = kb.make_effects_rows_occ(TypeChild::Node(present), span(), None);
        kb.make_arrow_occ(
            TypeChild::Ground(unit_ref),
            TypeChild::Ground(unit_ref),
            TypeChild::Node(rows),
            span(),
            None,
        )
    }

    /// WI-361: a `Value::Node` named tuple now exposes the SAME single `fields`
    /// child as its term twin, so `TermView` reads both alike — and
    /// `named_tuple_fields` returns its fields (previously EMPTY for a `Value::Node`
    /// tuple: the closed gap). A ground field reads as `Value::Term`, the poisoned
    /// one as `Value::Node`.
    #[test]
    fn node_named_tuple_reads_fields_through_termview() {
        use crate::eval::value::Value;
        use crate::kb::term_view::{TermView, ViewHead};
        let mut kb = kb_with_prelude();
        let modify = kb.intern("Modify");
        let p = kb.intern("resource");
        let c = kb.intern("c");
        let unit = kb.intern("Unit");
        let unit_ref = kb.make_sort_ref(unit);
        let int = kb.intern("Int");
        let int_ref = kb.make_sort_ref(int);
        let f = kb.intern("f");
        let n = kb.intern("n");
        let fields_key = kb.intern("fields");

        // `(f: Unit -> Unit {Modify[c]}, n: Int)` as a `Value::Node` (poisoned `f`).
        let value_arrow_c = value_modify_arrow(&mut kb, modify, p, unit_ref, c);
        let tuple = Value::Node(kb.make_named_tuple_occ(
            vec![(f, TypeChild::Node(value_arrow_c)), (n, TypeChild::Ground(int_ref))],
            span(),
            None,
        ));

        // View surface mirrors the term form: one `fields` named child.
        assert!(
            matches!(tuple.head(&kb), ViewHead::Functor { named_arity: 1, .. }),
            "Node named tuple exposes one `fields` child, got {:?}",
            tuple.head(&kb),
        );
        assert!(tuple.named_arg(&kb, fields_key).is_some(), "the `fields` child is exposed");

        // The closed gap: `named_tuple_fields` decodes BOTH fields for a Node tuple.
        let by: std::collections::HashMap<_, _> =
            super::named_tuple_fields(&kb, &tuple).into_iter().collect();
        assert_eq!(by.len(), 2, "two fields decoded, got {by:?}");
        assert!(matches!(by.get(&n), Some(Value::Term(_))), "`n: Int` rides as Value::Term");
        assert!(matches!(by.get(&f), Some(Value::Node(_))), "poisoned `f` rides as Value::Node");
    }

    /// WI-342 occurs-check over a `Value::Node` Rep-A type: binding `?v` to a Node
    /// `named_tuple` whose field mentions `?v` must be REJECTED (the view hides
    /// fields, so `occurs_in_view` walks the occurrence spine via
    /// `occ_contains_var`). Without the complete walk this would create a cyclic
    /// binding `?v = (f: ?v -> …)`.
    #[test]
    fn occurs_check_var_in_node_tuple_field() {
        use crate::kb::term::Var;
        let mut kb = kb_with_prelude();
        let unit = kb.intern("Unit");
        let unit_ref = kb.make_sort_ref(unit);
        let modify = kb.intern("Modify");
        let p = kb.intern("resource");
        let c = kb.intern("c");
        let f = kb.intern("f");
        let vsym = kb.intern("v");
        let vid = kb.fresh_var(vsym);
        let v_term = kb.alloc(Term::Var(Var::Global(vid)));

        // Node arrow `?v -> Unit {Modify[c]}` (Node because of the effect label),
        // with `?v` as its param; wrapped as the single field of a Node tuple.
        let label = occ_param(&mut kb, modify, p, c);
        let present = kb.make_present_occ(TypeChild::Node(label), span(), None);
        let rows = kb.make_effects_rows_occ(TypeChild::Node(present), span(), None);
        let arrow = kb.make_arrow_occ(
            TypeChild::Ground(v_term),
            TypeChild::Ground(unit_ref),
            TypeChild::Node(rows),
            span(),
            None,
        );
        let tuple = kb.make_named_tuple_occ(vec![(f, TypeChild::Node(arrow))], span(), None);

        let mut s = Substitution::new();
        assert!(
            !unify_types(&mut kb, &mut s, &TermIdView(v_term), &tuple),
            "occurs-check must reject binding ?v to a Node tuple whose field mentions ?v"
        );
    }

}

/// WI-341 Stage B — alpha-equivalence of callback-arrow binders. A callback's
/// own param (`Modify[a]`) is a binder whose alpha-canonical identity is its
/// POSITION; two callbacks' i-th params are the same up to renaming.
#[cfg(test)]
mod wi341_alpha_tests {
    use crate::kb::load::{self, NullResolver};
    use crate::kb::subst::Substitution;
    use crate::kb::KnowledgeBase;
    use crate::parse;
    use std::path::{Path, PathBuf};

    fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
        if dir.is_dir() {
            for e in std::fs::read_dir(dir).unwrap() {
                let p = e.unwrap().path();
                if p.is_dir() {
                    collect(&p, out);
                } else if p.extension().is_some_and(|x| x == "anthill") {
                    out.push(p);
                }
            }
        }
    }

    fn load_ops(src: &str) -> KnowledgeBase {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill");
        let mut files = Vec::new();
        collect(&dir, &mut files);
        let mut parsed: Vec<_> = files
            .iter()
            .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
            .collect();
        parsed.push(parse::parse(src).expect("parse ops"));
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        let _ = load::load_all(&mut kb, &refs, &NullResolver);
        kb
    }

    /// The (`Value`) type of an op's first parameter — a callback arrow.
    fn first_param_type(kb: &KnowledgeBase, op_qn: &str) -> crate::eval::value::Value {
        let op = kb.try_resolve_symbol(op_qn).unwrap_or_else(|| panic!("resolve {op_qn}"));
        let rec = crate::kb::op_info::lookup_operation_info(kb, op)
            .unwrap_or_else(|| panic!("opinfo {op_qn}"));
        rec.params.into_iter().next().expect("a param").1
    }

    #[test]
    fn same_position_callback_binders_are_alpha_equivalent() {
        let src = r#"
namespace anthill.test.wi341alpha
  import anthill.prelude.{Unit, Cell}
  operation op1(f: (a: Cell) -> Unit @ Modify[a]) -> Unit
  operation op2(g: (c: Cell) -> Unit @ Modify[c]) -> Unit
end
"#;
        let mut kb = load_ops(src);
        let f_arrow = first_param_type(&kb, "anthill.test.wi341alpha.op1");
        let g_arrow = first_param_type(&kb, "anthill.test.wi341alpha.op2");
        // The denoted-bearing callback arrows are `Value::Node` (Stage A).
        assert!(matches!(f_arrow, crate::eval::value::Value::Node(_)), "op1.f must be Value::Node");
        assert!(matches!(g_arrow, crate::eval::value::Value::Node(_)), "op2.g must be Value::Node");
        let mut subst = Substitution::new();
        assert!(
            super::unify_types(&mut kb, &mut subst, &f_arrow, &g_arrow),
            "`(a) -> Unit @ Modify[a]` and `(c) -> Unit @ Modify[c]` are alpha-equivalent"
        );
    }

    #[test]
    fn different_position_callback_binders_do_not_unify() {
        let src = r#"
namespace anthill.test.wi341alpha2
  import anthill.prelude.{Unit, Cell}
  operation op3(f: (a: Cell, b: Cell) -> Unit @ Modify[a]) -> Unit
  operation op4(g: (c: Cell, d: Cell) -> Unit @ Modify[d]) -> Unit
end
"#;
        let mut kb = load_ops(src);
        let f_arrow = first_param_type(&kb, "anthill.test.wi341alpha2.op3");
        let g_arrow = first_param_type(&kb, "anthill.test.wi341alpha2.op4");
        let mut subst = Substitution::new();
        assert!(
            !super::unify_types(&mut kb, &mut subst, &f_arrow, &g_arrow),
            "a modify on param 0 vs param 1 must NOT unify (binder positions differ)"
        );
    }
}


