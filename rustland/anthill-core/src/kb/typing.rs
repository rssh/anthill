/// Typing pass — type-check expressions following typing_pass_spec.anthill.
///
/// Rust implementation of TypingEnv, TypeResult, TypeError, and type_check.
/// Types are TermId values in the KB (types are terms in anthill).
/// Effects are tracked as List[Type] alongside the value type.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use smallvec::SmallVec;

use super::term::{Term, TermId, Literal, Var, VarId};
use super::node_occurrence::{
    for_each_child, for_each_pattern_child, materialize_from_handle, occurrence_structural_eq,
    EffectExprNode, Expr, MatchBranch, NodeKind, NodeOccurrence, Pattern, TypeChild, TypeNode,
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
    /// WI-385: an operation ARGUMENT whose inferred type does not conform to
    /// the declared parameter type. `op_name` is the called operation,
    /// `param` the declared parameter the argument was bound to.
    OperationArgument { op_name: Symbol, param: Symbol },
    OperationReturn { op_name: Symbol },
    OperationEffects { op_name: Symbol },
    OperationMatch { op_name: Symbol },
    Rule { name: Symbol, field: RuleField },
    LetBinding { var: Symbol },
    /// WI-420: a bare operation reference rejected as a first-class function
    /// value (eta-expansion) because its enclosing sort carries a `requires`
    /// chain — the runtime `Value::OpRef` cannot carry the requirement
    /// dictionary yet, so it would crash at eval on an unbound `__req_*`.
    OperationAsFunctionValue { op_name: Symbol },
    /// WI-374: a call whose arguments bind a SHARED type parameter
    /// inconsistently — the §3 parametricity tie, enforced:
    /// `append(intList, strList)` binds `List.T` to both elements.
    OperationTypeParams { op_name: Symbol },
}

impl TypeErrorContext {
    pub fn entity_name(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeErrorContext::EntityField { entity, .. } => kb.resolve_sym(*entity).to_string(),
            TypeErrorContext::OperationArgument { op_name, .. } => kb.resolve_sym(*op_name).to_string(),
            TypeErrorContext::OperationReturn { op_name }
            | TypeErrorContext::OperationEffects { op_name }
            | TypeErrorContext::OperationMatch { op_name } => kb.resolve_sym(*op_name).to_string(),
            TypeErrorContext::Rule { name, .. } => kb.resolve_sym(*name).to_string(),
            TypeErrorContext::LetBinding { var } => kb.resolve_sym(*var).to_string(),
            TypeErrorContext::OperationAsFunctionValue { op_name }
            | TypeErrorContext::OperationTypeParams { op_name } => {
                kb.resolve_sym(*op_name).to_string()
            }
        }
    }

    pub fn field_name(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeErrorContext::EntityField { field, .. } => kb.resolve_sym(*field).to_string(),
            TypeErrorContext::OperationArgument { param, .. } => kb.resolve_sym(*param).to_string(),
            TypeErrorContext::OperationReturn { .. } => "return".to_string(),
            TypeErrorContext::OperationEffects { .. } => "effects".to_string(),
            TypeErrorContext::OperationMatch { .. } => "match".to_string(),
            TypeErrorContext::Rule { field, .. } => field.name().to_string(),
            TypeErrorContext::LetBinding { .. } => "annotation".to_string(),
            TypeErrorContext::OperationAsFunctionValue { .. } => "function-value".to_string(),
            TypeErrorContext::OperationTypeParams { .. } => "type_args".to_string(),
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
    /// WI-400 increment C (eager let-alias): the canonical receiver PATH a let-bound
    /// name aliases. `let y = z` records `y → [z]`; `let y = s.provider` records
    /// `y → [s, provider]` — populated only for a STABLE receiver path (a value reference
    /// / field-access chain; immutable `let` ⟹ the aliased names denote one runtime
    /// value, the §3 soundness note). A projection `y.M` formed at the env-bearing let
    /// site is canonicalized through this map (`canonicalize_projection_receivers`) so it
    /// carries the SAME receiver as `z.M` / `s.provider.M` and the ζ arm equates them
    /// (`let y = z ⟹ y.M ≡ z.M`, the Scala divergence). Heads are stored already
    /// de-aliased (transitive `let y = z; let w = y` ⟹ `w → [z]`).
    receiver_aliases: HashMap<Symbol, Vec<Symbol>>,
    /// WI-424 — the enclosing sort's type-param canonical vars, each mapped to
    /// the per-body `Var::Rigid` term minted by `check_operation_bodies` (the
    /// WI-392 skolemization extended to the ENCLOSING SORT's params).
    /// `check_apply_iter` seeds a SAME-SORT sibling call's substitution with
    /// these, so the callee's signature — which references the same canonical
    /// vars — threads THIS instance's params: `iterator(c)` inside an
    /// `Iterable` member body returns `Stream[Element, E]` at the enclosing
    /// rigids instead of dangling fresh `?_`. Empty outside a parametric
    /// sort's member-body check. `Rc`: the env is cloned on every Visit push
    /// of the iterative typer and this is set once per body, so clones are a
    /// refcount bump, not a Vec copy.
    enclosing_sort_param_rigids: Rc<Vec<(VarId, TermId)>>,
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
            receiver_aliases: HashMap::new(),
            enclosing_sort_param_rigids: Rc::new(Vec::new()),
            local_resources: Vec::new(),
            enclosing: None,
            diagnostics: Vec::new(),
        }
    }

    /// WI-424 — install the enclosing sort's param-var → rigid map for the
    /// member body about to be checked (see the field doc).
    pub fn set_enclosing_sort_param_rigids(&mut self, rigids: Rc<Vec<(VarId, TermId)>>) {
        self.enclosing_sort_param_rigids = rigids;
    }

    fn enclosing_sort_param_rigids(&self) -> &[(VarId, TermId)] {
        &self.enclosing_sort_param_rigids
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

    /// WI-400 increment C: record that `name` aliases the canonical receiver `path`
    /// (`let y = z` ⟹ `name = y`, `path = [z]`). The path's head is de-aliased first, so
    /// the stored path is fully canonical (transitive `let w = y` resolves to `y`'s
    /// target). A path that is already the name itself (`let y = y`, degenerate) records
    /// nothing — and **clears** any stale alias under `name`, since a re-bind of a
    /// previously-aliased name must not keep pointing at the old receiver (soundness: a
    /// shadowing `let y = …` rebinds `y`'s identity).
    fn bind_receiver_alias(&mut self, name: Symbol, path: Vec<Symbol>) {
        let canon = self.canonicalize_receiver_path(path);
        if canon.first() == Some(&name) && canon.len() == 1 {
            self.receiver_aliases.remove(&name);
            return;
        }
        self.receiver_aliases.insert(name, canon);
    }

    /// WI-400 increment C: drop any receiver alias under `name`. Called when `name` is
    /// re-bound to an UNSTABLE value (`let y = f()`): the old alias is stale and keeping it
    /// would canonicalize `y`'s projection to the previous receiver — a false accept.
    fn clear_receiver_alias(&mut self, name: Symbol) {
        self.receiver_aliases.remove(&name);
    }

    /// WI-400 increment C: rewrite a receiver path's HEAD through the alias map (the head
    /// is replaced by its canonical path, the trailing field segments preserved):
    /// `[y, f]` with `y → [s, provider]` ⟹ `[s, provider, f]`. One hop suffices because
    /// stored aliases are already de-aliased at record time.
    fn canonicalize_receiver_path(&self, path: Vec<Symbol>) -> Vec<Symbol> {
        let Some((head, rest)) = path.split_first() else {
            return path;
        };
        match self.receiver_aliases.get(head) {
            Some(canon_head) => {
                let mut out = canon_head.clone();
                out.extend_from_slice(rest);
                out
            }
            None => path,
        }
    }

    fn receiver_aliases(&self) -> &HashMap<Symbol, Vec<Symbol>> {
        &self.receiver_aliases
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
    // WI-470 scope: a parameterized type stays HASH-CONSED when closed — a `TermId`
    // `Fn{S, named}` carries its bindings fully (no erasure) and is the load-bearing
    // index key (`by_sort`/`fact_dedup`), exactly the "nominal, heavily-shared"
    // structure the representation note keeps hash-consed. Only a POISONED binding
    // value (a `denoted` that cannot hash-cons) forces the `Value::Node` carrier; the
    // arrow→effect-row spine is what this migration moves to occurrence-primary, not
    // `List[T]`. (Flipping closed parameterizeds to `Node` added erasure risk at every
    // `.as_term()` consumer for no payoff — reverted.)
    if bindings.iter().any(|(_, v)| matches!(v, Value::Node(_))) {
        let mut children: Vec<(Symbol, TypeChild)> = Vec::with_capacity(bindings.len());
        for (s, v) in bindings {
            children.push((*s, value_to_type_child(kb, v)));
        }
        Value::Node(kb.make_parameterized_occ(TypeChild::Ground(base), children, span, owner))
    } else {
        // Closed: every binding is a `Value::Term` (checked above) — hash-consed.
        let mut terms: Vec<(Symbol, TermId)> = Vec::with_capacity(bindings.len());
        for (s, v) in bindings {
            terms.push((*s, v.expect_term()));
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
            terms.push((*s, v.expect_term()));
        }
        Value::Term(kb.make_named_tuple_type(&terms))
    }
}

/// WI-462: thread one tuple-literal component's EXPECTED type into its inferred type.
/// If `exp_fields` (the expected named-tuple's component types) has an entry whose SHORT
/// name matches `field_name`, unify the component's inferred `ty` against it (binding a free
/// element var — `h : ?_` ⟹ `xs.T`) and return the σ-walked result; otherwise return `ty`
/// unchanged. Matched by short name so the `_1`/`_2` positional convention and any declared
/// names line up regardless of symbol identity (mirrors `named_tuple_compatible`).
fn thread_expected_tuple_field(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    exp_fields: &[(Symbol, Value)],
    field_name: Symbol,
    ty: &Value,
) -> Value {
    let short = short_name_of(kb.resolve_sym(field_name)).to_owned();
    let exp_ty = exp_fields
        .iter()
        .find(|(n, _)| short_name_of(kb.resolve_sym(*n)) == short)
        .map(|(_, v)| v.clone());
    match exp_ty {
        Some(exp_ty) => {
            unify_types(kb, subst, ty, &exp_ty);
            walk_type_deep_value(kb, subst, ty)
        }
        None => ty.clone(),
    }
}

/// WI-470: build an `arrow(param, result, effects)` type as an occurrence —
/// always a `Value::Node` (occurrence-primary; the representation note disclaims
/// hash-consing for arrows/binders). A ground child rides as `TypeChild::Ground`
/// (poison flows up, not down), so a fully-ground arrow is a Node spine over
/// interned leaves; a denoted-bearing child (e.g. a lambda body effect `Modify[c]`)
/// is CARRIED as a poisoned `TypeChild::Node`. Consumers read either through
/// `TermView` (`arrow_compatible_view` / `subtype_effect_rows` at the op-boundary
/// return check); a genuine TermId demand recovers identity via `cached_term`
/// (WI-471). Label order is not load-bearing — row unify/subtype compare label
/// sets. `span`/`owner` stamp the occurrences. (WI-342 introduced the Node arm for
/// poisoned arrows; WI-470 made it the sole arm.)
fn make_arrow_value(
    kb: &mut KnowledgeBase,
    param: &Value,
    result: &Value,
    effects: &[Value],
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    // WI-470 (occurrence-primary): an inferred arrow is minted unconditionally as
    // a `Value::Node` occurrence — the representation note disclaims hash-consing
    // for arrows/binders, so the typer no longer chooses the hash-consed
    // `make_arrow_type` for the ground case. A ground child still rides as
    // `TypeChild::Ground(TermId)` (poison flows up, not down), so a fully-ground
    // arrow is a Node spine over interned leaves; consumers read it through
    // `TermView` (already carrier-agnostic — `unify_*`, `extract_type`,
    // `decompose_effect_row`), and a genuine TermId demand recovers identity via
    // `cached_term` (WI-471). Label order is not load-bearing (rows compare as
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
            Value::Term(t) if kb.row_tail_var_of(*t).is_some() => {
                let tail = kb.row_tail_var_of(*t).expect("checked is_some");
                kb.make_open_occ(TypeChild::Ground(tail), span, owner)
            }
            _ => {
                let label_child = value_to_type_child(kb, label);
                kb.make_present_occ(label_child, span, owner)
            }
        };
        row = kb.make_merge_occ(TypeChild::Node(atom), TypeChild::Node(row), span, owner);
    }
    let effects_child =
        TypeChild::Node(kb.make_effects_rows_occ(TypeChild::Node(row), span, owner));
    let param_child = value_to_type_child(kb, param);
    let result_child = value_to_type_child(kb, result);
    let arrow = kb.make_arrow_occ(param_child, result_child, effects_child, span, owner);
    Value::Node(arrow)
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
    walk_type_deep_value_g(kb, subst, e, false)
}

/// The grounding sibling of [`walk_type_deep_value`] — see [`walk_type_deep_g`]. δ-grounds
/// a concrete-subject `RigidProjection` (incl. one nested in a `Value::Node` binding) at
/// the call-site result-resolve points; otherwise identical pure-σ propagation.
fn resolve_type_deep_value(kb: &mut KnowledgeBase, subst: &Substitution, e: &Value) -> Value {
    walk_type_deep_value_g(kb, subst, e, true)
}

/// Shared body of [`walk_type_deep_value`] (`ground = false`, pure σ) and
/// [`resolve_type_deep_value`] (`ground = true`, σ + call-time concrete-fill).
fn walk_type_deep_value_g(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    e: &Value,
    ground: bool,
) -> Value {
    match e {
        Value::Term(t) => Value::Term(walk_type_deep_g(kb, subst, *t, ground)),
        // WI-441: a NODE-carried type DOES carry type-param vars — a callback
        // arrow's effect-row tail (`@ {EffP, -Modify[x]}`) is a GROUND child
        // Var inside the occurrence tree. The old "Nodes carry Refs, not
        // type-param vars" assumption left those un-walked, so the rigidify
        // pass missed them (the body then unified/leaked the raw Global).
        // Rebuild share-preservingly: unchanged subtrees keep their Rc.
        Value::Node(occ) => Value::Node(rewrite_type_occ_deep(kb, subst, occ, ground)),
        other => other.clone(),
    }
}

/// WI-441: deep-resolve vars inside a NODE-carried type occurrence by
/// rebuilding it with every `TypeChild::Ground` mapped through
/// [`walk_type_deep`] and every `TypeChild::Node` recursed. Share-preserving:
/// an unchanged subtree returns its original `Rc` (so an all-ground-stable
/// tree costs only the traversal). `Denoted` (a VALUE occurrence — no type
/// vars), `NamedTuple` (Value-carried fields list) and `ExprCarried` (an
/// expression receiver) are returned as-is — none of them can embed a row
/// var today; extend when one does.
fn rewrite_type_occ_deep(
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
            TypeChild::Ground(t) => {
                let w = walk_type_deep_g(kb, subst, *t, ground);
                if w != *t {
                    *changed = true;
                }
                TypeChild::Ground(w)
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
            TypeNode::Arrow { param, result, effects } => {
                let (p, r, e) = (
                    child(kb, subst, param, ground, &mut changed),
                    child(kb, subst, result, ground, &mut changed),
                    child(kb, subst, effects, ground, &mut changed),
                );
                Some(NodeKind::Type(TypeNode::Arrow { param: p, result: r, effects: e }))
            }
            TypeNode::Parameterized { base, bindings } => {
                let b = child(kb, subst, base, ground, &mut changed);
                let bs: Vec<(Symbol, TypeChild)> = bindings
                    .iter()
                    .map(|(s, c)| (*s, child(kb, subst, c, ground, &mut changed)))
                    .collect();
                Some(NodeKind::Type(TypeNode::Parameterized { base: b, bindings: bs }))
            }
            TypeNode::EffectsRows { effects_expr } => {
                let e = child(kb, subst, effects_expr, ground, &mut changed);
                Some(NodeKind::Type(TypeNode::EffectsRows { effects_expr: e }))
            }
            TypeNode::Denoted { .. } | TypeNode::NamedTuple { .. } | TypeNode::ExprCarried { .. } => None,
        },
        NodeKind::EffectExpr(node) => match node {
            EffectExprNode::Merge { left, right } => {
                let (l, r) = (
                    child(kb, subst, left, ground, &mut changed),
                    child(kb, subst, right, ground, &mut changed),
                );
                Some(NodeKind::EffectExpr(EffectExprNode::Merge { left: l, right: r }))
            }
            EffectExprNode::Present { label } => {
                let l = child(kb, subst, label, ground, &mut changed);
                Some(NodeKind::EffectExpr(EffectExprNode::Present { label: l }))
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
            term_cache: std::cell::Cell::new(None),
        }),
        _ => Rc::clone(occ),
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
            Value::Term(t) => *t,
            _ => return cur,
        };
        let vid = match kb.get_term(t) {
            Term::Var(Var::Global(vid)) => *vid,
            _ => return Value::Term(walk_type(kb, subst, t)),
        };
        if visited.contains(&vid) {
            return cur;
        }
        match subst.resolve_as_value(vid) {
            Some(bound) => {
                visited.push(vid);
                cur = bound.clone();
            }
            None => return Value::Term(walk_type(kb, subst, t)),
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
fn walk_pattern_field_type_deep(
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
        let Value::Term(t) = &cur else { break };
        let Term::Var(Var::Global(vid)) = kb.get_term(*t) else { break };
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
/// Render a `denoted`'s carried VALUE occurrence to a display string: a single
/// `Ref(c)` shows `c`; a WI-302 field path `DotApply(Ref(c), contents)` shows
/// `c.contents` (recursing the receiver spine), so a diagnostic naming a compound
/// value-in-type label is legible instead of the bare `?`. Mirrors how
/// `persistence::print` renders the same occurrence (the carrier-paired-display
/// contract). An unrecognized carried shape stays `?`.
fn denoted_value_display(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> String {
    match &occ.kind {
        NodeKind::Expr { expr: Expr::Ref(s), .. } => kb.resolve_sym(*s).to_string(),
        NodeKind::Expr { expr: Expr::DotApply { receiver, name, .. }, .. } => {
            format!("{}.{}", denoted_value_display(kb, receiver), kb.resolve_sym(*name))
        }
        _ => "?".to_string(),
    }
}

fn type_display_name_occ(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> String {
    match &occ.kind {
        NodeKind::Type(TypeNode::Denoted { value }) => denoted_value_display(kb, value),
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
        // WI-397: a compound-receiver projection `(a.b).M` — render `receiver.member`
        // rather than the `?` fallthrough, so a type error naming it is legible.
        NodeKind::Type(TypeNode::ExprCarried { value, member }) => format!(
            "{}.{}",
            type_child_display_name(kb, value),
            type_child_display_name(kb, member)
        ),
        // WI-400: a receiver-expression occurrence inside a projection's neutral type — a
        // value reference (`s`) or a field-access path (`s.provider`) — so the neutral
        // prints legibly (`s.provider.K`, not `?.K`) in a type error.
        NodeKind::Expr { expr: Expr::Ref(s) | Expr::Ident(s), .. } => {
            kb.resolve_sym(*s).to_string()
        }
        NodeKind::Expr {
            expr: Expr::DotApply { receiver, name, pos_args, named_args },
            ..
        } if pos_args.is_empty() && named_args.is_empty() => {
            format!("{}.{}", type_display_name_occ(kb, receiver), kb.resolve_sym(*name))
        }
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
                // WI-400: a single-ref expression-carried projection (`l.T`) — render
                // `receiver.member`, not the generic `ExprCarried[value = …]` fallback, so
                // a neutral-projection type error reads legibly (mirrors the Node-carrier
                // `type_display_name_occ` arm for the compound `s.provider.K` form).
                "ExprCarried" => {
                    let v = get_named_arg(kb, named_args, "value")
                        .map(|t| type_display_name(kb, t))
                        .unwrap_or_else(|| "?".to_string());
                    let m = get_named_arg(kb, named_args, "member")
                        .map(|t| type_display_name(kb, t))
                        .unwrap_or_else(|| "?".to_string());
                    format!("{v}.{m}")
                }
                // WI-428: a rigid type-receiver projection — render `subject.member`
                // (`P.Key` / `MemStore.Key`), mirroring the `ExprCarried` arm.
                "RigidTypeProjection" => {
                    let v = get_named_arg(kb, named_args, "var")
                        .map(|t| type_display_name(kb, t))
                        .unwrap_or_else(|| "?".to_string());
                    let m = get_named_arg(kb, named_args, "member")
                        .map(|t| type_display_name(kb, t))
                        .unwrap_or_else(|| "?".to_string());
                    format!("{v}.{m}")
                }
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
    /// WI-279: the DotApply RECEIVER finished (the only pre-typed child).
    /// Resolve `member` against the receiver's least sort (`min_sort`, read
    /// from the receiver child's result type), then synthesize the
    /// dispatched `Apply` from the RAW arg occurrences carried here and
    /// re-`Visit` it — so the produced call rides normal Apply typing +
    /// type-param inference + req_insertion. WI-443: the args are
    /// deliberately NOT pre-typed at this frame — a callback argument (a
    /// lambda) needs the callee's param-type hint, which exists only inside
    /// the synthesized call; pre-typing it hintless mis-fired dispatch
    /// (`gt` coherence on an untyped lambda param). No match ⇒ a
    /// `DotDispatchNoMatch` diagnostic at the dot span.
    DotApply {
        occ: Rc<NodeOccurrence>,
        member: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
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
    // WI-283: gate the in-typer `[simp]` firing on whether any rule can fire —
    // read once per walk. WI-443: a loaded `dot_apply` also enables the gate —
    // DotApply nodes are always rewritten (to the dispatched call). Tree
    // REASSEMBLY is no longer gated on this (WI-408): the typer itself now
    // synthesizes rewrites (`some(...)` coercion insertion), so every wrapper
    // frame reassembles from its children's `TypeResult.node`s unconditionally
    // — `reassemble`'s ptr-eq short-circuit keeps the no-rewrite case
    // allocation-free.
    let simp_enabled = super::simp_rewrite::has_simp_equations(kb) || kb.has_dot_applies;
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
    expected: Option<&Value>,
) -> Result<TypeResult, TypeError> {
    if let Some(ty) = env.lookup_var(sym) {
        return Ok(TypeResult::pure_value(ty, env.clone(), Rc::clone(occ)));
    }
    if kb.is_constructor_symbol(sym) {
        return check_constructor_iter(kb, env, sym, &[], &[], &[], &[], span, None, occ);
    }
    // WI-275: a bare operation reference used where a function type is expected
    // denotes the operation as a first-class function value (eta-expansion) —
    // its `Function[A, B, E]` arrow type, not its return type. Fires only in a
    // function-typed context; elsewhere a bare op name keeps denoting its return
    // type (the zero-arg-call reading below), unchanged.
    if let Some(exp) = expected {
        if arrow_parts(kb, exp).is_some() {
            if let Some(fn_ty) = operation_as_function_value(kb, sym, occ) {
                // WI-420: resolve + attach the op's requirement dispatch dict
                // (the `expected` arrow pins its element type) so eval captures
                // it on the OpRef. A cross-sort unsatisfiable requirement is a
                // loud error here.
                attach_eta_dispatch_dict(kb, env, sym, occ, &fn_ty, exp)?;
                return Ok(TypeResult::pure_value(fn_ty, env.clone(), Rc::clone(occ)));
            }
        }
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

/// WI-275: the arrow type of an operation referenced as a first-class function
/// value (eta-expansion). `inc(n: Int) -> Int` becomes `Int -> Int`; a
/// multi-param `lt(a: T, b: T) -> Bool` becomes `(T, T) -> Bool` — a positional
/// `_1`/`_2` named-tuple param (the WI-355 tuple convention) so it unifies
/// against a `Function[(T, T), Bool]` slot, matching how a `lambda (a, b) -> ...`
/// is typed and an `f((a, b))` applied. Returns `None` when `sym` is not an eta
/// candidate (no operation, nullary, body-less, or type-parameterized) so the
/// caller falls back to the return-type reading. A `requires`-carrying op's
/// dispatch dict is resolved + attached separately by `attach_eta_dispatch_dict`
/// (WI-420), which has the `expected` arrow that pins the element type.
fn operation_as_function_value(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    occ: &Rc<NodeOccurrence>,
) -> Option<Value> {
    // Only eta-lift an operation the runtime can actually run as a function
    // value, keeping the typer's accepted set a subset of the evaluator's:
    //   * it must have a runnable anthill body — the evaluator's `reduce_var`
    //     mints a `Value::OpRef` only for body-having ops, so a body-less
    //     builtin / spec declaration would type-check here yet crash at eval as
    //     a zero-arg call (`ArityMismatch`);
    //   * it must be monomorphic — a type-parameterized op's arrow would carry
    //     its type-param vars verbatim (no per-use freshening), which alias
    //     across multiple eta-lifts of the same op.
    // A reference that fails either gate stays a loud type error, not a silent
    // runtime failure.
    if !op_has_runnable_body(kb, sym) {
        return None;
    }
    let op = lookup_operation_info_full(kb, sym)?;
    if op.params.is_empty() || !op.type_params.is_empty() {
        return None;
    }
    let (span, owner) = (occ.span, occ.owner);
    let param = if op.params.len() == 1 {
        op.params[0].1.clone()
    } else {
        let fields: Vec<(Symbol, Value)> = op
            .params
            .iter()
            .enumerate()
            .map(|(i, (_, t))| (kb.intern(&format!("_{}", i + 1)), t.clone()))
            .collect();
        named_tuple_value(kb, &fields, span, owner)
    };
    Some(make_arrow_value(kb, &param, &op.return_type, &op.effects, span, owner))
}

/// WI-420: at a bare-op eta site, resolve the operation's requirement dispatch
/// dict and attach it (`CallClass::EtaOpRef`) to the occurrence so eval captures
/// it on the `Value::OpRef` at mint. `fn_ty` is the op's eta arrow, `expected`
/// the arrow type it is checked against; unifying them pins the op's element
/// type (e.g. `member`'s `List.T := Int` from a `Function[(Int, List[Int]),
/// Bool]` slot), which `build_concrete_dispatch_dict` needs to resolve a
/// concrete dep (`Eq[Int]` from its `fact`) or forward an abstract one the
/// enclosing sort's own `requires` covers (a caller-frame `var_ref`). A
/// requires-free or same-sort op needs no dict (eval forwards the caller's
/// requirements). A cross-sort op whose requirement is neither concretely
/// resolvable nor covered by the enclosing scope is a loud error — the eta
/// analogue of `MissingRequiresForSpecOp` for a direct call.
fn attach_eta_dispatch_dict(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    sym: Symbol,
    occ: &Rc<NodeOccurrence>,
    fn_ty: &Value,
    expected: &Value,
) -> Result<(), TypeError> {
    let Some(parent) = impl_parent_of_op(kb, sym) else {
        return Ok(()); // namespace-level op — no enclosing sort `requires`
    };
    if direct_requires_chain(kb, parent).is_empty() {
        return Ok(()); // requires-free op — eval forwards the caller's reqs
    }
    if env.enclosing_sort() == Some(parent) {
        // Same-sort eta: the op needs its OWN sort's dispatching dict. A DIRECT
        // same-sort call inherits the enclosing frame at eval, but an eta'd
        // `OpRef` ESCAPES to a foreign apply frame (the HOF's), which forwards an
        // empty requirements channel — so the op's `__req_*` would be unbound
        // (a typecheck-clean eval crash). Capture the enclosing frame's
        // `__req_self` (the sort's own dispatching dict, identical to what this
        // op needs) at mint via a `var_ref`, and install it at apply. (WI-420)
        let Some(syms) = ProjectionSyms::resolve(kb) else {
            return Ok(());
        };
        let req_self = kb.intern("__req_self");
        let dict = build_req_var_ref(kb, &syms, req_self);
        occ.set_classification(CallClass::EtaOpRef { dict });
        return Ok(());
    }
    // Pin the op's element type(s) by unifying its eta arrow against the
    // expected arrow (best-effort: a non-unifiable expected leaves a dep
    // abstract, which `build_concrete_dispatch_dict` then forwards or rejects).
    let mut subst = Substitution::new();
    // Pin the op's element type by unifying the expected and eta-arrow PARAM
    // types (carrier-agnostic via `arrow_parts`: `expected` is a `Function[...]`
    // sort-ref, the eta arrow an `arrow` form — unifying the whole types across
    // those two carriers does not decompose). Concrete-first so a bare self-sort
    // ref (e.g. member's `l: List`) on the op side stays open while the concrete
    // expected param pins the element (`List.T := Int`) — mirroring the direct
    // call's arg-first unify order.
    let exp_param = arrow_parts(kb, expected).and_then(|(p, _, _)| p);
    let fn_param = arrow_parts(kb, fn_ty).and_then(|(p, _, _)| p);
    if let (Some(ep), Some(fp)) = (exp_param, fn_param) {
        unify_types(kb, &mut subst, &ep, &fp);
    }
    let caller_requires: Vec<RequiresEntry> =
        env.enclosing_requires().map(|r| r.to_vec()).unwrap_or_default();
    match build_concrete_dispatch_dict(kb, &subst, parent, env.enclosing_sort(), &caller_requires) {
        Some(dict) => {
            occ.set_classification(CallClass::EtaOpRef { dict });
            Ok(())
        }
        None => {
            // Cross-sort op with a non-empty direct `requires` chain that we
            // could resolve neither concretely (no `fact`) nor by forwarding
            // from the enclosing scope: unsatisfiable in this eta context.
            let op_qn = kb.qualified_name_of(sym).to_string();
            let parent_qn = kb.qualified_name_of(parent).to_string();
            Err(TypeError::Other {
                span: Some(occ.span.span),
                context: TypeErrorContext::OperationAsFunctionValue { op_name: sym },
                expected: format!(
                    "`{}` used as a function value to have a satisfiable `requires` — \
                     have the enclosing sort `requires` it, or use `{}` at a concrete type",
                    op_qn, op_qn,
                ),
                actual: format!(
                    "unsatisfiable `{}` requirement for bare operation `{}` (WI-420)",
                    parent_qn, op_qn,
                ),
            })
        }
    }
}

/// WI-275: the expected-type hint for a higher-order argument occurrence. Only a
/// lambda or a bare reference needs a top-down function type — to type a lambda's
/// parameter, or to eta-lift an operation name to a function value — so those, in
/// a function-typed parameter slot (`arrow` / `Function[A, B, E]`), get that type
/// as their hint; every other argument gets `None`, preserving the WI-379
/// args-before-expected synthesis order.
fn hof_arg_hint(
    kb: &mut KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    param_type: Option<Value>,
) -> Option<Value> {
    let pt = param_type?;
    let is_hof_arg = matches!(
        &arg.kind,
        NodeKind::Expr { expr: Expr::Lambda { .. } | Expr::VarRef { .. }, .. }
    );
    if is_hof_arg && arrow_parts(kb, &pt).is_some() {
        Some(pt)
    } else {
        None
    }
}

/// WI-427: true iff the type term mentions a `TypeExtractor.TypeVar` form
/// anywhere — an operation's own type parameter, which is out of scope as a
/// top-down hint for a *different* call (and a wildcard in the subtype
/// relation, so it could never pin by equality anyway). The recursive
/// complement of [`type_value_is_ground`], which catches logic vars and
/// SORT-param refs but keys its functor test on sort-param symbols only.
fn type_term_mentions_type_var(kb: &KnowledgeBase, tid: TermId) -> bool {
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, named_args } => {
            kb.qualified_name_of(*functor) == "anthill.prelude.TypeExtractor.TypeVar"
                || pos_args.iter().any(|a| type_term_mentions_type_var(kb, *a))
                || named_args.iter().any(|(_, a)| type_term_mentions_type_var(kb, *a))
        }
        _ => false,
    }
}

/// WI-427: the expected-type hint for a nested-call argument — the
/// `expected → argument` half of bidirectional inference (WI-379 delivered
/// the `argument → expected` half). The declared param type flows *down*
/// into an argument that is itself a call, so a callee type-param that
/// appears ONLY in the argument's return type
/// (`poly[X]() -> Wrapper[P = Inner[T = X]]` in a
/// `Wrapper[P = Inner[T = String]]` slot) is pinned by the call context
/// instead of failing "X unconstrained".
///
/// SOUNDNESS (the WI-379 variance sidestep, expansion-during-unification.md):
/// the hint is pushed only where it pins by EQUALITY — a fully-GROUND
/// declared param type (no logic var, no sort-param ref, no TypeVar
/// anywhere). A projection param type (`k: s.cell.T`) rides a non-`Term`
/// carrier and is skipped by the same gate (its elimination is the
/// call-site's job, after the args are typed). Inside the argument's own
/// `check_apply_iter` the hint is consulted only AFTER its arguments pinned
/// the params (the WI-270/379 fill-only-still-free order) and a
/// contradicting hint binds nothing — so a wrong hint cannot mask the
/// normal arg-vs-param mismatch diagnostic, and no metavariable is ever
/// solved through a `<:` constraint.
fn nested_call_arg_hint(
    kb: &KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    param_type: Option<&Value>,
) -> Option<Value> {
    let pt = param_type?;
    let is_call_arg = matches!(
        &arg.kind,
        NodeKind::Expr { expr: Expr::Apply { .. }, .. }
    );
    let pins_by_equality = resolved_type_is_ground(kb, pt)
        && !matches!(pt, Value::Term(t) if type_term_mentions_type_var(kb, *t));
    if is_call_arg && pins_by_equality {
        Some(pt.clone())
    } else {
        None
    }
}

/// WI-462: the expected type a TUPLE-LITERAL constructor field value should receive — the
/// `expected → field-value` push the constructor BUILD already performs via unify, surfaced
/// here as a top-down hint. A tuple literal carries no constructor of its own, so the
/// constructor's expected-seed binds its component vars only AFTER it is typed (too late to
/// shape the built tuple type). Here we replay that seed in a SCRATCH subst — unify the
/// parent sort type against the constructor's `expected`, then walk the field's declared
/// type through it — to derive the field value's expected (`some(...)` whose declared field
/// is `value: T` and whose expected is `Option[T = (xs.T, …)]` yields `(xs.T, …)`). `None`
/// unless `expected` is a parameterized type of the constructor's parent sort and the walk
/// SPECIALIZES the field type to a `named_tuple` (the only shape a tuple literal threads).
fn tuple_field_expected_from_ctor(
    kb: &mut KnowledgeBase,
    ctor_sym: Symbol,
    field_sym: Symbol,
    expected: &Option<Value>,
) -> Option<Value> {
    let exp = expected.as_ref()?;
    let field_types = kb.entity_field_types(ctor_sym)?.to_vec();
    let (_, field_decl) = field_types.iter().find(|(s, _)| *s == field_sym)?;
    let field_decl = field_decl.clone();
    let parent_tid = kb.constructor_parent_sort(ctor_sym)?;
    let parent_type = sort_term_to_type(kb, parent_tid);
    let mut subst = Substitution::new();
    if !unify_types(kb, &mut subst, &TermIdView(parent_type), exp) {
        return None;
    }
    let walked = walk_type_deep_value(kb, &subst, &field_decl);
    // Only a useful hint if the walk produced a concrete tuple type (a still-abstract
    // field param, or a non-tuple field, leaves a tuple literal nothing to thread).
    matches!(extract_type(kb, &walked), TypeExtractor::NamedTuple(_)).then_some(walked)
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
    let recv_canon = kb.canonical_sort_sym(recv_sort);
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
        let Some(spec_t) = get_named_arg(kb, &named, "spec") else { continue };
        let Some(spec_sym) = super::load::provides_spec_base_sym(kb, spec_t) else { continue };
        // Carrier-keyed: the receiver's sort IS the provider — `(3).min(5)` →
        // `Ordered.min` via `fact Ordered[Int]`. `same_symbol`, not `==`: a sort
        // carries distinct Symbol ids (bare-interned vs fully-qualified).
        let carrier_match = same_symbol(kb, carrier, recv_sort);
        // WI-450 witness: the receiver's sort is the spec's CARRIER-PARAM VALUE of a
        // provider whose `sort_ref` is some OTHER (witness) sort — `tag.combine(t)`
        // → `Combiner.combine` via `sort TagCombiner provides Combiner[T = Tag]`. The
        // dot-call synthesises a `combine(tag, t)` Apply that then value-directs to
        // the witness impl at eval (param-agnostic, like the non-dot call form).
        let witness_match = !carrier_match
            && provision_carrier_sort(kb, spec_sym, spec_t)
                .map(|c| kb.canonical_sort_sym(c) == recv_canon)
                .unwrap_or(false);
        if carrier_match || witness_match {
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
            // WI-399: discharge an expression-carried projection (`s.cell.T`) in the
            // let annotation HERE, where `env` resolves the receiver's type — the
            // let-binding peer of the op-call elimination in `check_apply_iter`. The
            // eliminated type then feeds BOTH the value's expected (below) and the
            // value-vs-annotation conformance at `LetAfterValue`, so a concrete
            // projection annotation (`s.cell.T` = `String`) checks the value against
            // `String`, not the opaque projection. A projection whose receiver type is
            // NOT concretely known in scope (a bare / abstract receiver, a missing
            // member) is a LOUD error here — never silently leaked to `unify_types`
            // (which now refuses an un-eliminated projection head, the WI-399 safety
            // net). The env's `var_bindings` is exactly the `Symbol -> type` resolver
            // `eliminate_type_projections` needs (the analog of `param_to_arg_type`).
            let annotation = match annotation {
                Some(ann) if value_contains_projection(kb, &ann) => {
                    // WI-400 increment C (eager let-alias): canonicalize the annotation's
                    // projection receiver through the env's let-aliases BEFORE elimination,
                    // so `let y = z; let k: y.M` resolves `y.M` against the SAME receiver as
                    // `z.M` (`let y = z ⟹ y.M ≡ z.M`). A no-op when no alias applies.
                    let ann = canonicalize_projection_receivers(
                        kb,
                        env.receiver_aliases(),
                        &ann,
                        occ.span,
                    );
                    let var =
                        extract_pattern_var_name(kb, pattern).unwrap_or_else(|| kb.intern("_"));
                    let ctx = TypeErrorContext::LetBinding { var };
                    // WI-459: a let-annotation is a BODY-site projection — the receiver is
                    // the in-scope value itself, there is no call argument to re-key to
                    // (`None`).
                    match eliminate_type_projections(kb, &ann, &env.var_bindings, None, &ctx, occ_span) {
                        Ok(elim) => Some(elim),
                        Err(e) => {
                            results.push(Err(e));
                            return;
                        }
                    }
                }
                other => other,
            };
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
            TypeResult::pure(kb.make_sort_ref_by_name("Int64"), unwrap_env(env), Rc::clone(&occ)),
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
            let r = check_bare_ref(kb, &*env, *sym, occ_span, &occ, expected.as_ref());
            results.push(r);
        }
        Expr::Ident(sym) => {
            let r = check_bare_ref(kb, &*env, *sym, occ_span, &occ, expected.as_ref());
            results.push(r);
        }
        Expr::VarRef { name } => {
            // WI-275: thread the expected type so a bare operation reference in a
            // function-typed position is eta-lifted to a function value rather than
            // denoting its return type.
            let r = check_bare_ref(kb, &*env, *name, occ_span, &occ, expected.as_ref());
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
            // WI-275: bidirectional inference for higher-order arguments. Look up
            // the callee's declared parameter types; a lambda or bare operation
            // reference in a function-typed slot gets that `Function[A, B, E]`
            // pushed in as its expected type (`hof_arg_hint`). The lambda then
            // types its parameter from `A` instead of leaving it an unconstrained
            // var (which makes an overloaded body call like `add(x, 1)` dispatch-
            // ambiguous), and a bare op name is eta-lifted to a function value.
            // Value/literal args take no hint, preserving the WI-379
            // args-before-expected order that lets their own type drive
            // dispatch. WI-427: a NESTED-CALL argument additionally gets the
            // declared param type as its hint when that type pins by equality
            // (fully ground) — the `expected → argument` half of bidirectional
            // inference (`nested_call_arg_hint`). The lookup is gated on the
            // call actually having a lambda/ref or nested-call argument.
            let has_hof_arg = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| matches!(
                    &a.kind,
                    NodeKind::Expr { expr: Expr::Lambda { .. } | Expr::VarRef { .. }, .. }
                ));
            let has_call_arg = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| matches!(&a.kind, NodeKind::Expr { expr: Expr::Apply { .. }, .. }));
            let op_params = if has_hof_arg || has_call_arg {
                lookup_operation_info_full(kb, functor).map(|op| op.params)
            } else {
                None
            };
            let pos_hints: Vec<Option<Value>> = pos_args
                .iter()
                .enumerate()
                .map(|(i, arg)| {
                    let pt = op_params.as_ref().and_then(|ps| ps.get(i)).map(|(_, t)| t.clone());
                    hof_arg_hint(kb, arg, pt.clone())
                        .or_else(|| nested_call_arg_hint(kb, arg, pt.as_ref()))
                })
                .collect();
            let named_hints: Vec<Option<Value>> = named_args
                .iter()
                .map(|(name, arg)| {
                    let pt = op_params
                        .as_ref()
                        .and_then(|ps| ps.iter().find(|(s, _)| s == name))
                        .map(|(_, t)| t.clone());
                    hof_arg_hint(kb, arg, pt.clone())
                        .or_else(|| nested_call_arg_hint(kb, arg, pt.as_ref()))
                })
                .collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::Apply {
                occ: occ_clone,
                fn_sym: functor,
                pos_args: pos_args.clone(),
                named_args: named_args.clone(),
                env: Rc::clone(&env),
                expected,
                fuel,
            }));
            for ((_, arg), hint) in named_args.iter().zip(named_hints.iter()).rev() {
                push_visit(work, Rc::clone(arg), Rc::clone(&env), hint.clone(), fuel);
            }
            for (arg, hint) in pos_args.iter().zip(pos_hints.iter()).rev() {
                push_visit(work, Rc::clone(arg), Rc::clone(&env), hint.clone(), fuel);
            }
        }
        Expr::Constructor { name, pos_args, named_args } => {
            let name = *name;
            let pos_args = pos_args.clone();
            let named_args = named_args.clone();
            // WI-427: the constructor-field twin of the nested-call hint — a
            // GROUND declared field type flows down into a field value that is
            // itself a call, so `hold(poly())` pins poly's return-only type
            // param exactly like an operation param slot does. Same gate, same
            // soundness argument (`nested_call_arg_hint`); a field type that
            // mentions the sort's own params (`cell: P`) is non-ground and
            // takes no hint. Other field values stay unhinted.
            // WI-462: a positional/named tuple `(h, t)` lowers to a `Constructor{TupleLiteral}`
            // (named `_1`/`_2`/declared fields) — that, not `Expr::TupleLit`, is the surface
            // form (`convert.rs` `TupleLiteral` build) and the one `check_tuple_literal_-
            // constructor` threads. (The `Expr::TupleLit` IR is a non-surface shape whose build
            // frame takes no expected, so a hint on it would be dropped — not recognized here.)
            fn is_tuple_lit(kb: &KnowledgeBase, arg: &Rc<NodeOccurrence>) -> bool {
                matches!(
                    &arg.kind,
                    NodeKind::Expr { expr: Expr::Constructor { name, .. }, .. }
                        if kb.qualified_name_of(*name) == "anthill.reflect.TupleLiteral"
                )
            }
            let has_call_field = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| matches!(&a.kind, NodeKind::Expr { expr: Expr::Apply { .. }, .. }));
            // WI-462: a TUPLE-LITERAL field value gets the constructor's expected pushed
            // down to its component types (so `some((h, t))` under `Option[(xs.T, …)]`
            // threads `h ⟹ xs.T`); other field values keep the nested-call hint.
            let has_tuple_field = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| is_tuple_lit(kb, a));
            // Owned field-type list (Symbol + declared Value), looked up once when any
            // field needs a hint — used both for the nested-call hint and to find a
            // tuple-literal field's declared symbol for the WI-462 expected derivation.
            let field_types: Option<Vec<(Symbol, Value)>> = if has_call_field || has_tuple_field {
                kb.entity_field_types(name).map(|ft| ft.to_vec())
            } else {
                None
            };
            let pos_hints: Vec<Option<Value>> = pos_args
                .iter()
                .enumerate()
                .map(|(i, arg)| {
                    let field = field_types.as_ref().and_then(|fs| fs.get(i)).cloned();
                    if is_tuple_lit(kb, arg) {
                        if let Some((fs, _)) = &field {
                            if let Some(h) = tuple_field_expected_from_ctor(kb, name, *fs, &expected) {
                                return Some(h);
                            }
                        }
                    }
                    nested_call_arg_hint(kb, arg, field.as_ref().map(|(_, t)| t))
                })
                .collect();
            let named_hints: Vec<Option<Value>> = named_args
                .iter()
                .map(|(fname, arg)| {
                    if is_tuple_lit(kb, arg) {
                        if let Some(h) = tuple_field_expected_from_ctor(kb, name, *fname, &expected) {
                            return Some(h);
                        }
                    }
                    let ft = field_types
                        .as_ref()
                        .and_then(|fs| fs.iter().find(|(s, _)| s == fname))
                        .map(|(_, t)| t.clone());
                    nested_call_arg_hint(kb, arg, ft.as_ref())
                })
                .collect();
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
            for ((_, arg), hint) in named_args.iter().zip(named_hints.iter()).rev() {
                push_visit(work, Rc::clone(arg), Rc::clone(&env), hint.clone(), fuel);
            }
            for (arg, hint) in pos_args.iter().zip(pos_hints.iter()).rev() {
                push_visit(work, Rc::clone(arg), Rc::clone(&env), hint.clone(), fuel);
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
            // WI-443: only the receiver is pre-typed (its sort drives the
            // dispatch); the raw arg occurrences ride on the frame and are
            // typed exactly once — with the callee's param hints — inside
            // the synthesized call.
            work.push(TypeWorkOp::Build(TypeBuildFrame::DotApply {
                occ: Rc::clone(&occ),
                member,
                pos_args: pos_args.clone(),
                named_args: named_args.clone(),
                env: Rc::clone(&env),
                expected,
                fuel,
            }));
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
/// `for_each_child`-ordered `group` the wrapper frames drain). WI-408:
/// unconditional — the typer itself produces rewrites (`some(...)` coercion
/// insertion), not just `[simp]` firings, so a rewritten child must always
/// propagate; `reassemble`'s ptr-eq short-circuit keeps the unchanged case
/// allocation-free.
fn reassemble_group(
    occ: &Rc<NodeOccurrence>,
    child_results: &[Result<TypeResult, TypeError>],
) -> Rc<NodeOccurrence> {
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

/// WI-374 (kernel-language §8.1 expansion, let-annotation site): rewrite a bare
/// or PARTIAL parametric-sort annotation to KEEP the value's inferred
/// parameters instead of erasing them. Annotation-written bindings stay
/// authoritative; every param the annotation leaves unwritten takes the
/// value's inferred binding: `let s : Stream = List.iterator(xs)` binds `s` at
/// `Stream[T = Int64, E = {}]`, and `let s : Stream[T = Int64] = …` keeps its
/// written `T` while taking `E` from the value. A defined-type / alias
/// annotation resolves to its shape FIRST (WI-381), so its definition-fixed
/// bindings count as written.
///
/// This is the site-scoped form of §8.1: the annotation occurrence is the
/// per-occurrence identity, and the value's type supplies the bindings the
/// expansion's fresh vars would have unified against — no transient vars
/// needed. Returns `None` (annotation kept as written, today's behavior) when
/// there is nothing to keep: a non-sort-application annotation, a value type
/// carrying no parameters, or a CROSS-SORT pair (the value's base merely
/// *provides* the annotated spec — enrichment there must read the provider
/// fact's view, not name-aligned params; conformance was already checked by
/// the caller either way).
fn unroll_annotation_with_inferred(
    kb: &mut KnowledgeBase,
    ann: &Value,
    vty: &Value,
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Option<Value> {
    // Value side FIRST — cheap (no KB scan): nothing to keep unless the value's
    // type is a sort application carrying bindings. The annotation side may pay
    // a SortAlias fact scan (`resolve_alias_shape`), so it only runs after this
    // gate — `let n : Int64 = 5` never reaches it.
    let (v_base, v_bindings) = match extract_type(kb, vty) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return None,
    };
    // Annotation side: bare ref (alias-shape resolved, WI-381) or partial
    // application; its bindings seed the merge as the written-authoritative set.
    let (ann_base, mut merged) = sort_application_parts(kb, ann)?;
    if kb.canonical_sort_sym(ann_base) != kb.canonical_sort_sym(v_base) {
        return None;
    }
    let mut changed = false;
    for (p, v) in &v_bindings {
        match merged.iter_mut().find(|(q, _)| q == p) {
            // A written ANONYMOUS wildcard (`Stream[T = ?]`) pins nothing —
            // the value's inferred binding replaces it instead of being
            // erased under it (the wildcard already passed conformance
            // against anything). A NAMED var (`Pair[A = ?t, B = ?t]`) is NOT
            // replaced: independently overwriting each slot would silently
            // lose the same-var tie the user wrote.
            Some(slot)
                if matches!(
                    extract_type(kb, &slot.1),
                    TypeExtractor::TypeVar(name)
                        if matches!(kb.resolve_sym(name), "?" | "?_")
                ) =>
            {
                slot.1 = v.clone();
                changed = true;
            }
            Some(_) => {}
            None => {
                merged.push((*p, v.clone()));
                changed = true;
            }
        }
    }
    if !changed {
        return None;
    }
    let base = kb.make_sort_ref(ann_base);
    Some(parameterized_value(kb, base, &merged, span, owner))
}

/// WI-374: read a type as a SORT APPLICATION — `(base sort, written
/// bindings)` — resolving a defined-type / alias to its shape first (WI-381),
/// so a structured alias contributes its definition-fixed bindings and a bare
/// alias OF a bare sort reports the UNDERLYING base (`sort MyList = List`
/// participates like `List`). `None` when the type is not a sort application
/// (arrow, tuple, projection, var, …). Shared by the let-annotation merge and
/// the signature expansion so WI-381 alias semantics live in one place.
fn sort_application_parts(
    kb: &mut KnowledgeBase,
    ty: &Value,
) -> Option<(Symbol, Vec<(Symbol, Value)>)> {
    if let Some(s) = extract_sort_ref_sym(kb, ty) {
        // A parametric sort is never an alias: a non-empty memoized param set
        // (WI-424 cache) skips the alias-shape fact scans on the hot path.
        if !sort_type_params_as_pairs(kb, s).is_empty() {
            return Some((s, vec![]));
        }
        match resolve_alias_shape(kb, s) {
            Some(shape) => match extract_type(kb, &TermIdView(shape)) {
                TypeExtractor::Parameterized { base, bindings } => Some((base, bindings)),
                _ => Some((
                    extract_sort_ref_sym(kb, &TermIdView(shape)).unwrap_or(s),
                    vec![],
                )),
            },
            None => Some((s, vec![])),
        }
    } else {
        match extract_type(kb, ty) {
            TypeExtractor::Parameterized { base, bindings } => Some((base, bindings)),
            _ => None,
        }
    }
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
            // WI-283: reassemble this Apply from its children's (possibly-
            // rewritten) `.node`s, then — when `[simp]` rules exist — fire a
            // rule at it *before* classifying (a fired node is discarded, so
            // classifying it would be wasted); on a fire, re-type the RHS so
            // chains/cascades reach fixpoint and the produced apply gets
            // classified for req_insertion. WI-408: the reassembly itself is
            // unconditional (a typer-inserted `some(...)` coercion below must
            // propagate even with no `[simp]` rules); `reassemble`'s ptr-eq
            // short-circuit keeps the unchanged case allocation-free.
            let node = {
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
                if simp_enabled && fuel > 0 {
                    if let Some(rhs) = fire_simp(kb, &node) {
                        push_visit(work, rhs, env, expected, fuel - 1);
                        return;
                    }
                }
                node
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
            let node = {
                if let Err(e) = collect_arg_errors(pos_results.iter().chain(named_results.iter())) {
                    results.push(Err(e));
                    return;
                }
                let child_refs: Vec<&Result<TypeResult, TypeError>> =
                    pos_results.iter().chain(named_results.iter()).collect();
                let node = reassemble_children(&occ, &child_refs);
                if simp_enabled && fuel > 0 {
                    if let Some(rhs) = fire_simp(kb, &node) {
                        push_visit(work, rhs, env, expected, fuel - 1);
                        return;
                    }
                }
                node
            };
            let r = check_constructor_iter(
                kb, &*env, ctor_sym, &pos_args, &named_args,
                &pos_results, &named_results, span, expected, &node,
            );
            results.push(r);
        }
        TypeBuildFrame::DotApply {
            occ, member, pos_args: pos_nodes, named_args: named_nodes, env, expected, fuel,
        } => {
            // Only the receiver was pre-typed (WI-443) — pop its result.
            let recv = match results.pop().expect("DotApply: missing receiver result") {
                Ok(r) => r,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };
            let receiver_node = Rc::clone(&recv.node);
            // `min_sort`: widen the receiver to its least declared sort. Read
            // the child's result type directly (don't depend on the receiver's
            // `Stamp` frame ordering). WI-342: widen the carrier-agnostic `ty`
            // in place — a `Value::Node` receiver type need not be re-grounded.
            let recv_sort = sort_functor_of_view(kb, &recv.ty);
            let dot_span = Some(occ.span.span);
            // `pos_nodes` / `named_nodes` are the RAW arg occurrences — used
            // by both the dot-rule override and the default method fallback,
            // and typed once inside the synthesized call (with the callee's
            // param hints).

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
                let mut synth_pos: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(1 + pos_nodes.len());
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

            // INC 1b: a zero-arg member naming a FIELD of the receiver's sort.
            // The method fallback ran first (an operation of that name wins), so
            // only a non-operation member reaches here. Synthesize
            // `field_access(receiver, "field")` — the reflect field-access
            // desugaring (reflect.anthill) whose eval-side twin reads the named
            // field off the runtime `Value::Entity`. The result type is the
            // field's type with the receiver's type-args substituted
            // (`resolve_field_type`, the same projection pattern field types use).
            // The synthesized call has no field-specific signature to re-type
            // against, so the type is set DIRECTLY rather than via `push_visit`.
            if pos_nodes.is_empty() && named_nodes.is_empty() {
                if let Some(rs) = recv_sort {
                    // The surface `?o.value` interns `value` in the use-site
                    // scope, which need not equal the declaring entity's field
                    // symbol — `resolve_field_type` matches the field by symbol
                    // identity. Resolve `member` to the receiver sort's actual
                    // field symbol by SHORT name first. (Inherits
                    // `resolve_field_type`'s contract that a given field name is
                    // the same symbol across a sort's constructors; a multi-
                    // variant short-name collision resolves via the first.)
                    let member_short = short_name_of(kb.resolve_sym(member)).to_string();
                    let field_sym = kb.constructors_of_sort(rs).into_iter().find_map(|ctor| {
                        kb.entity_field_types(ctor).and_then(|fields| {
                            fields.iter()
                                .find(|(f, _)| short_name_of(kb.resolve_sym(*f)) == member_short)
                                .map(|(f, _)| *f)
                        })
                    });
                    if let Some((field_ty, fa_sym)) = field_sym.and_then(|fsym| {
                        let ctx = TypeErrorContext::EntityField { entity: rs, field: fsym };
                        let field_ty = resolve_field_type(kb, &recv.ty, fsym, &ctx, dot_span).ok()?;
                        let fa_sym = kb.try_resolve_symbol("anthill.reflect.field_access")?;
                        Some((field_ty.0, fa_sym))
                    }) {
                        let field_name_node = NodeOccurrence::new_expr(
                            Expr::Const(Literal::String(member_short)),
                            occ.span,
                            occ.owner,
                        );
                        let pass = super::simp_rewrite::simp_pass(kb);
                        let synth = NodeOccurrence::synthesized_expr(
                            Expr::Apply {
                                functor: fa_sym,
                                pos_args: vec![receiver_node, field_name_node],
                                named_args: Vec::new(),
                                type_args: Vec::new(),
                            },
                            Rc::clone(&occ),
                            pass,
                            occ.owner,
                        );
                        // The synth isn't re-typed (no field-specific signature
                        // to re-type against), so stamp its inferred type here —
                        // downstream passes shouldn't see an untyped node. Eval
                        // dispatches the builtin via the functor with no
                        // classification, so none is needed.
                        synth.set_inferred_type(field_ty.clone());
                        results.push(Ok(TypeResult {
                            ty: field_ty,
                            env: recv.env,
                            effects: recv.effects.clone(),
                            node: synth,
                        }));
                        return;
                    }
                }
            }

            // No method and no field matched → clear diagnostic at the dot span.
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
            // Prefer an explicit annotation (already `Value`, S4a) over the value type —
            // but a bare/partial parametric annotation is first REWRITTEN to keep the
            // value's inferred params (WI-374; conformance already checked above).
            let bound_ty = match (annotation, value_ty) {
                (Some(ann), Some(vty)) => Some(
                    unroll_annotation_with_inferred(kb, &ann, &vty, occ.span, occ.owner)
                        .unwrap_or(ann),
                ),
                (ann, vty) => ann.or(vty),
            };
            extend_env_from_pattern(kb, &mut ext_env, pattern, bound_ty);
            if let Some(var_name) = extract_pattern_var_name(kb, pattern) {
                ext_env.declare_local_resource(var_name);
                // WI-400 increment C (eager let-alias): if the value is a STABLE receiver
                // path (a var / field-access chain — immutable `let` ⟹ one runtime value),
                // record `var_name`'s canonical receiver, so a later projection off
                // `var_name` canonicalizes to the aliased receiver (`let y = z ⟹
                // y.M ≡ z.M`). An unstable value (`let y = f()`) records nothing — it is
                // its own neutral receiver.
                match stable_receiver_path(&value_node) {
                    Some(path) => ext_env.bind_receiver_alias(var_name, path),
                    // A re-bind to an UNSTABLE value must CLEAR any stale alias from an
                    // outer `let` of the same name — else `let y = p; let y = f(); … : y.M`
                    // would wrongly canonicalize `y.M` to `p.M` (a false accept).
                    None => ext_env.clear_receiver_alias(var_name),
                }
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
            let node = {
                let pattern_clone = match occ.as_expr() {
                    Some(Expr::Let { pattern, .. }) => Rc::clone(pattern),
                    _ => Rc::clone(&occ), // defensive; unreachable for Let frame
                };
                super::simp_rewrite::reassemble(
                    &occ,
                    &[pattern_clone, value_node, Rc::clone(&body_r.node)],
                )
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
            // WI-374: read the BASE sort through `sort_functor_of_view`, not
            // `extract_sort_ref_sym` — a parameterized scrutinee type
            // (`Option[T = Int64]`, now also produced by the let-annotation
            // rewrite) must resolve its constructor set exactly like a bare
            // one; the bare-ref-only read silently skipped it.
            let scrutinee_ctors: Vec<Symbol> = scr_ty
                .as_ref()
                .and_then(|sty| sort_functor_of_view(kb, sty))
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
            let node = reassemble_match(&occ, &scr_node, &branch_results);
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
                    // WI-374: base sort via `sort_functor_of_view` so a
                    // PARAMETERIZED scrutinee keeps its exhaustiveness check
                    // (the bare-ref-only read silently skipped it).
                    if let Some(sort_sym) = sort_functor_of_view(kb, &sty) {
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
            // WI-470: the lambda's arrow type is minted as an occurrence
            // (`Value::Node`, occurrence-primary). A denoted-bearing child (a
            // `Modify[c]` body effect) is CARRIED as a poisoned child rather than
            // re-grounded; a ground child rides as `TypeChild::Ground`. The
            // op-boundary return check compares it cross-carrier via `TermView`.
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
                    let node = {
                        let param_clone = match occ.as_expr() {
                            Some(Expr::Lambda { param, .. }) => Rc::clone(param),
                            _ => Rc::clone(&occ), // defensive; unreachable
                        };
                        super::simp_rewrite::reassemble(&occ, &[param_clone, Rc::clone(&r.node)])
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
            let node = reassemble_group(&occ, &group);
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
            let node = reassemble_group(&occ, &group);
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
            let node = reassemble_group(&occ, &group);
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
            let node = reassemble_group(&occ, &group);
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
    if let Some(mut op) = lookup_operation_info_full(kb, fn_sym) {
        // WI-374 (§8.1, site-scoped): expand FOREIGN bare/partial parametric
        // sort applications in the callee's signature to per-call fresh-var
        // applications, so two foreign occurrences never alias and the
        // foreign sort's canonical vars are no longer touched by this call's
        // argument unification. Member self-sort refs are left bare — the §3
        // bullet-1 parametricity tie keeps riding the canonical channel
        // (`unify_parameterized_with_sort_ref` + the per-call subst).
        //
        // The expansion serves INFERENCE only: the WI-385 validation below
        // keeps checking each argument against the param type AS WRITTEN
        // (`written_params`) — an expanded param whose fresh var an
        // incompatible argument failed to bind is non-ground, and the
        // validation's groundness gate would silently skip the rejection
        // (`Function[Int64, Int64]` with open `E` vs a `String -> Bool`
        // argument must still be a loud mismatch).
        let written_params = op.params.clone();
        {
            let callee_parent_canon = impl_parent_of_op(kb, fn_sym)
                .filter(|p| matches!(kb.kind_of(*p), Some(crate::intern::SymbolKind::Sort)))
                .map(|p| kb.canonical_sort_sym(p));
            for i in 0..op.params.len() {
                if let Some(exp) =
                    expand_foreign_sort_application(kb, &op.params[i].1, callee_parent_canon)
                {
                    op.params[i].1 = exp;
                }
            }
            // The RETURN is deliberately NOT expanded: a bare return is an
            // ERASED relationship (§5 — variables reconstruct nothing), and
            // carrying unbound fresh vars in `resolved_ret` would un-ground
            // the ARGUMENT side of a downstream WI-385 validation (silent
            // skip where bare was a loud mismatch) and stamp dangling vars
            // into annotated-let merges.
        }
        let mut subst = Substitution::new();
        // WI-269 Phase D: explicit call-site `op[bindings]` bindings
        // seed the substitution first. Returns `NoSuchTypeParam` on
        // an unknown binding name.
        seed_op_type_args(kb, &mut subst, &op, occ, fn_sym, span)?;
        // WI-424: a SAME-SORT sibling call inside a member body shares the
        // enclosing instance's sort params — seed the callee's canonical param
        // vars with the body's rigids (the WI-392 skolems, extended to sort
        // params) BEFORE argument unification. The callee's signature references
        // the same canonical vars, so its return/effects then thread the
        // enclosing instance: `iterator(c)` inside `Iterable.find` returns
        // `Stream[Element, E]` at the body's rigids rather than dangling vars.
        // Within the sort's own definition this is exactly the parametricity tie
        // (type-parameter-scoping.md §3) — `C`/`Element`/`E` denote ONE instance
        // across all members; a different-instance argument is correctly
        // rejected against the rigid.
        if !env.enclosing_sort_param_rigids().is_empty() {
            let same_sort = impl_parent_of_op(kb, fn_sym)
                .zip(env.enclosing_sort())
                .is_some_and(|(callee_parent, enclosing)| {
                    kb.canonical_sort_sym(callee_parent) == kb.canonical_sort_sym(enclosing)
                });
            if same_sort {
                for (vid, rigid) in env.enclosing_sort_param_rigids().iter() {
                    if subst.resolve_as_value(*vid).is_none() {
                        subst.bind_term(*vid, *rigid);
                    }
                }
            }
        }
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
        let self_recv_spec = self_receiver_spec_sort(kb, &op, fn_sym);
        // WI-383 B: capture the CARRIER-PARAM provision (the `Iterable.find(c: C)` /
        // `ModifyRuntime.get(target: T)` shape — receiver typed by the spec's own carrier
        // param, not the spec sort) so the LATE ground-value bind below can reuse its
        // `view` without re-scanning the provider facts. Only when there is no
        // self-receiver (the two shapes are mutually exclusive).
        let carrier_param_info = if self_recv_spec.is_some() {
            None
        } else {
            carrier_param_receiver(kb, &op, fn_sym, named_args, pos_results, named_results)
        };
        let carrier_bound = match self_recv_spec {
            Some(spec_sort) => match receiver_carrier(
                kb, &op, spec_sort, named_args, pos_results, named_results,
            ) {
                ReceiverCarrier::Concrete(carrier_sym) => bind_spec_params_from_carrier(
                    kb, &mut subst, &op, spec_sort, carrier_sym,
                    named_args, pos_results, named_results,
                ),
                _ => false,
            },
            // WI-424: no spec-sort-typed receiver — try the CARRIER-PARAM shape
            // (`Iterable.find(c: C, …)`): ground the spec's params (`Element`,
            // the written `E` row) from the concrete carrier's provision, with
            // the same bind-before-expected-seeding rationale as the arm above.
            None => match &carrier_param_info {
                Some((spec_sort, _carrier_sym, recv_ty, view)) => {
                    bind_spec_params_from_carrier_param(
                        kb, &mut subst, *spec_sort, recv_ty, view.clone(),
                    )
                }
                None => false,
            },
        };
        // WI-379: synthesize from the ARGUMENTS first (the two loops below);
        // the caller-side `expected` is consulted only AFTER (moved below the
        // arg loops), so it fills still-free type params without overriding any
        // that an argument pinned.
        let mut arg_effects: Vec<Value> = Vec::new();
        let mut param_to_arg_sym: HashMap<Symbol, Symbol> = HashMap::new();
        // WI-376/398: only ops whose signature actually carries a projection pay for the
        // per-call elimination — the >99% that don't skip the param_to_arg_type clones
        // and the rewrite walk entirely. WI-398 adds the PARAMETER positions: a param
        // whose type projects another param (`check(s: State, k: s.provider.K)`).
        let params_have_projection =
            op.params.iter().any(|(_, t)| value_contains_projection(kb, t));
        let op_has_projection = params_have_projection
            || value_contains_projection(kb, &op.return_type)
            || op.effects.iter().any(|e| value_contains_projection(kb, e));
        // Each param symbol → the inferred type of the argument bound to it, so a
        // projection `param.M` in the return / effects / a LATER param can read the
        // receiver's actual per-call type (the synthesis-time discharge point).
        // Populated only when the op has a projection.
        let mut param_to_arg_type: HashMap<Symbol, Value> = HashMap::new();

        for (i, arg_occ) in pos_args.iter().enumerate() {
            if let Some(arg_var_sym) = extract_var_ref_sym_node(arg_occ) {
                if let Some((param_sym, _)) = op.params.get(i) {
                    param_to_arg_sym.insert(*param_sym, arg_var_sym);
                }
            }
            if let Ok(ref arg_result) = pos_results[i] {
                // WI-341 Stage A: the param type is `Value` (`Value::TermView`),
                // unified carrier-agnostically — no `TermIdView` wrap.
                if let Some((param_sym, param_type)) = op.params.get(i) {
                    // WI-398: a param whose declared type IS / CONTAINS a projection
                    // (`k: s.cell.T`) cannot be unified against its raw `ExprCarried` —
                    // the receiver param's type-args are not yet projected, and an
                    // unbound arg-var must never bind to a projection. Defer it to the
                    // post-synthesis elimination pass below; the argument type is still
                    // recorded so a LATER param projecting THIS one can read it.
                    if !(op_has_projection && value_contains_projection(kb, param_type)) {
                        unify_types(kb, &mut subst, &arg_result.ty, param_type);
                    }
                    if op_has_projection {
                        param_to_arg_type.insert(*param_sym, arg_result.ty.clone());
                    }
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
                    // WI-398: defer a projection param's unify (see the positional loop).
                    if !(op_has_projection && value_contains_projection(kb, param_type)) {
                        unify_types(kb, &mut subst, &arg_result.ty, param_type);
                    }
                    if op_has_projection {
                        param_to_arg_type.insert(*arg_name, arg_result.ty.clone());
                    }
                }
                arg_effects = merge_effects(&arg_effects, &arg_result.effects);
            }
        }

        // WI-398: CROSS-PARAMETER projection. With every argument now synthesized
        // (`param_to_arg_type` fully populated above), discharge each projection-bearing
        // PARAMETER type by projecting the receiver param's argument type — the same
        // elimination the return / effects positions use (below). A projection reads the
        // receiver's ARGUMENT type (recorded above; a concrete value, hence ground), so
        // the discharge is order-independent here; a CYCLIC projection signature
        // (`f(a: b.T, b: a.T)`) has no synthesis order and is rejected at LOAD
        // (`check_operation_bodies`), so what reaches a call is always a DAG. The
        // resolved type is unified against the argument and recorded so the WI-385
        // VALIDATION below checks the argument against `String`, not the un-eliminated
        // `s.cell.T`. A projection that cannot resolve (abstract receiver, missing
        // member) is a loud error here, never a silent skip.
        // WI-374: eliminate from the WRITTEN params, not the expanded copies —
        // an expanded partial application's unbound fresh var would make the
        // eliminated type non-ground, and the WI-385 groundness gate below
        // would silently skip a mismatch the written form rejects loudly.
        let mut effective_param_types: HashMap<Symbol, Value> = HashMap::new();
        if params_have_projection {
            // WI-459: re-key a cross-param projection NEUTRAL to the caller's argument too.
            let arg_syms = (!param_to_arg_sym.is_empty()).then_some(&param_to_arg_sym);
            for (param_sym, param_type) in &written_params {
                if !value_contains_projection(kb, param_type) {
                    continue;
                }
                let eff = eliminate_type_projections(
                    kb, param_type, &param_to_arg_type, arg_syms,
                    &TypeErrorContext::OperationReturn { op_name: fn_sym }, span,
                )?;
                // `unify_types` borrows the arg type (it is `A: TermView`), so no clone.
                if let Some(arg_ty) = param_to_arg_type.get(param_sym) {
                    unify_types(kb, &mut subst, arg_ty, &eff);
                }
                effective_param_types.insert(*param_sym, eff);
            }
        }

        // WI-385: VALIDATE each argument against its declared parameter type.
        // The unify loops above pin type-parameters for INFERENCE and DISCARD
        // their boolean — so before this check a caller could pass an argument
        // of any type and the typer stayed silent (`f(x: Int) -> Int` called as
        // `f("hello")` loaded clean). Now that the arguments are synthesized and
        // the type-params bound, subtype-check each argument against its param
        // type — the ARGUMENT direction, peer to the RETURN direction WI-379 made
        // authoritative. GATED on `resolved_type_is_ground` for BOTH the
        // (subst-walked) arg type and param type: a polymorphic position (`add(a:
        // T, b: T)`, an inference-`?_` arg) stays unchecked so the spec-op
        // dispatch / return-conformance path settles it — only a concrete arg
        // against a concrete param can fail here. A param a prior argument GROUND
        // by inference (`f[T](a: T, b: T)` with `a:Int`) is then checkable, so a
        // contradicting `b:"x"` is still caught. Bail on an ill-typed call
        // (aggregating sibling mismatches) rather than building its return type.
        let mut arg_type_errors: Vec<TypeError> = Vec::new();
        // WI-408: bare-`T`-vs-`Option[T]` args accepted via some-coercion —
        // (child-index, declared Option type), materialized after the loops.
        let mut some_wraps: Vec<(usize, Value)> = Vec::new();
        for (i, _) in pos_args.iter().enumerate() {
            if let Ok(ref arg_result) = pos_results[i] {
                // WI-374: validate against the param AS WRITTEN, not the
                // inference-expanded copy (see `written_params` above).
                if let Some((param_sym, param_type)) = written_params.get(i) {
                    // WI-398: validate against the ELIMINATED type for a projection param
                    // (`s.cell.T` → `String`); the raw type for a non-projection param.
                    let param_type = effective_param_types.get(param_sym).unwrap_or(param_type);
                    // WI-440: the lacks/closed-row CHECKING direction for an
                    // eta'd callback argument (binder-aligned row validation).
                    // Runs FIRST: when both it and the generic subtype check
                    // would reject (e.g. a ground `@ {}` arrow), this one names
                    // the offending effect label, where the generic mismatch
                    // prints two identically-displayed arrow types.
                    if let Some(err) = validate_callback_effect_row(
                        kb, &subst, fn_sym, *param_sym, param_type,
                        &pos_args[i], &arg_result.ty, span,
                    ) {
                        arg_type_errors.push(err);
                    } else {
                        match validate_arg_against_param(
                            kb, &mut subst, &arg_result.ty, param_type, span,
                            TypeErrorContext::OperationArgument { op_name: fn_sym, param: *param_sym },
                        ) {
                            ArgValidation::Ok => {}
                            ArgValidation::WrapSome { declared } => some_wraps.push((i, declared)),
                            ArgValidation::Fail(err) => arg_type_errors.push(err),
                        }
                    }
                }
            }
        }
        for (i, (arg_name, arg_occ)) in named_args.iter().enumerate() {
            if let Ok(ref arg_result) = named_results[i] {
                // WI-374: validate against the param AS WRITTEN (see above).
                if let Some((param_sym, param_type)) =
                    written_params.iter().find(|(s, _)| *s == *arg_name)
                {
                    // WI-398: validate against the eliminated projection type (above).
                    let param_type = effective_param_types.get(param_sym).unwrap_or(param_type);
                    // WI-440: callback row check first — see the positional loop.
                    if let Some(err) = validate_callback_effect_row(
                        kb, &subst, fn_sym, *param_sym, param_type,
                        arg_occ, &arg_result.ty, span,
                    ) {
                        arg_type_errors.push(err);
                    } else {
                        match validate_arg_against_param(
                            kb, &mut subst, &arg_result.ty, param_type, span,
                            TypeErrorContext::OperationArgument { op_name: fn_sym, param: *param_sym },
                        ) {
                            ArgValidation::Ok => {}
                            ArgValidation::WrapSome { declared } => {
                                some_wraps.push((pos_args.len() + i, declared));
                            }
                            ArgValidation::Fail(err) => arg_type_errors.push(err),
                        }
                    }
                }
            }
        }
        if !arg_type_errors.is_empty() {
            return Err(aggregate_errors(arg_type_errors));
        }
        // WI-374 (user-decided 2026-06-12): ENFORCE the §3 parametricity tie.
        // The argument loops bind a sort's canonical param vars through bare
        // member params (`append(xs: List, ys: List)` both bind `List.T`); a
        // conflicting rebind records a contradiction that was never consulted,
        // so `append(intList, strList)` was silently accepted with
        // first-binding-wins threading. Checked HERE — after the WI-385
        // per-argument validation (whose precise diagnostics take precedence)
        // and BEFORE the expected-seeding below, whose failed unify against a
        // pinned slot is a DELIBERATE silent no-op (WI-367/WI-379) that must
        // not trip this. Scoping (review round, same day):
        //  - the callee's parent must be a SORT — `impl_parent_of_op` yields
        //    the NAMESPACE symbol for a top-level op, and a namespace prefix
        //    would sweep in every sort it contains, enforcing a "member tie"
        //    on §3-bullet-2 foreign refs;
        //  - EVERY per-var detail is scanned (a single first-detail would let
        //    an earlier benign foreign conflict mask a member violation);
        //  - a conflict whose prior binding is the body's WI-424 seeded rigid
        //    is exempt — a same-sort sibling call at a different instance
        //    keeps its pre-WI-374 acceptance (enforcing the rigid tie is a
        //    separate decision);
        //  - a UNIFIABLE pair (bare `List` vs `List[T = Int64]`, a `?_`
        //    wildcard vs a concrete, equal rows in different carriers/orders)
        //    is refinement, not violation — bind-level TermId/structural
        //    inequality over-reports, so re-test through the real relation.
        // A FOREIGN sort's var contradicted through two independent bare refs
        // (§3 bullet 2: independent) is not scanned — and with the signature
        // expansion above, foreign refs no longer touch canonical vars at all.
        let op_parent_sort = impl_parent_of_op(kb, fn_sym)
            .filter(|p| matches!(kb.kind_of(*p), Some(crate::intern::SymbolKind::Sort)));
        if let Some(parent) = op_parent_sort {
            enforce_member_tie(
                kb, &subst, parent, fn_sym, span,
                env.enclosing_sort_param_rigids(),
            )?;
        }
        // WI-408: materialize the recorded some-coercions — wrap each flagged
        // argument's typed node in a synthesized `some(...)` and reassemble
        // this apply from the new children. MUST run before any annotation
        // write (`set_resolved_type_args` / `classify` below): the rebuilt
        // node starts with fresh annotation cells. The parent reassembles in
        // turn from `TypeResult.node` (WI-283), and the root reaches the
        // stored body via `set_op_body_node`.
        let rebuilt_occ;
        let occ = if some_wraps.is_empty() {
            occ
        } else {
            rebuilt_occ = wrap_some_children(kb, occ, &some_wraps, pos_results, named_results);
            &rebuilt_occ
        };

        // WI-376: discharge expression-carried type projections (`s.T` / `s.Sort`) in
        // the declared return type — and any effect rows that carry one — by projecting
        // the RECEIVER param's argument type, resolved here where the arguments are
        // synthesized. Concrete member → the projected type (`List[Int].T = Int`); a
        // member the receiver's sort does not declare, or one it declares but the
        // receiver left unbound (a bare / abstract receiver) → loud `TypeError`. Only
        // ops that actually carry a projection (`op_has_projection`) run the rewrite.
        // WI-396: EFFECT-POSITION projection `effects s.E` rides this same loop — it
        // lowers to an `ExprCarried` (`type_expr_to_value`, once `infer_effects_row_-
        // requires` stopped strict-resolving the dotted name) and `project_type_member`
        // reads the `E` member off the receiver's type, threading the observation effect
        // row. `l.E` on a sort with no effect member is the same loud missing-member
        // error — `E` is never silently defaulted to pure (design §5).
        let (proj_return_type, proj_effects): (Value, Vec<Value>) = if op_has_projection {
            let ret_ctx = TypeErrorContext::OperationReturn { op_name: fn_sym };
            // WI-459: pass the formal→argument value-reference map so a projection NEUTRAL
            // formed off a formal param is RE-KEYED to the caller's actual receiver (see
            // `rewrite_term_projections`).
            let arg_syms = (!param_to_arg_sym.is_empty()).then_some(&param_to_arg_sym);
            let rt = eliminate_type_projections(
                kb, &op.return_type, &param_to_arg_type, arg_syms, &ret_ctx, span)?;
            let mut effs: Vec<Value> = Vec::with_capacity(op.effects.len());
            for e in &op.effects {
                effs.push(eliminate_type_projections(
                    kb, e, &param_to_arg_type, arg_syms, &ret_ctx, span)?);
            }
            (rt, effs)
        } else {
            (op.return_type.clone(), op.effects.clone())
        };

        // WI-383 B (Modify provider-fact GROUND value bind): bind a still-FREE spec
        // value-param from the carrier's GROUND provider-fact binding
        // (`fact Box[T = IntCell, V = Int64]` ⟹ `Box.V := Int64`, the entity-resource
        // Modify tie). Runs HERE — AFTER the argument loops (so a param threaded by an
        // argument, e.g. Iterable's `Element` via the predicate, is already bound and the
        // still-FREE gate skips it; binding it EARLY regresses WI-424/441 effect-row
        // threading) and BEFORE expected-seeding (so the resource's declared value type
        // wins over the caller's `-> String` claim — the value-untied soundness hole the
        // Modify model names). The REF-shaped binding (`V ↦ Cell.V`) is already threaded
        // by `bind_spec_params_from_carrier_param` above; this closes only the
        // GROUND-valued case it skips.
        if let Some((spec_sort, _carrier_sym, _recv_ty, view)) = &carrier_param_info {
            bind_ground_value_params_from_provider(kb, &mut subst, *spec_sort, view);
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
            unify_types(kb, &mut subst, &proj_return_type, &exp);
        }

        // Apply param-name substitution to op.effects (WI-209), then
        // walk each through `walk_type_deep` so type-var bindings from
        // arg-unification propagate into nested positions in the effect
        // (e.g. `Stream.head`'s `effects E` → `Error` once `vid_E` is
        // bound by `unify_parameterized_with_sort_ref`). Skip the
        // param-name walk when no var_ref args were seen.
        let pre_substituted: Vec<Value> = if param_to_arg_sym.is_empty() {
            proj_effects.clone()
        } else {
            proj_effects
                .iter()
                .map(|e| {
                    // WI-459: a PROJECTION-bearing effect (`s.E`) was already eliminated
                    // AND re-keyed surgically by `eliminate_type_projections` (its Neutral
                    // branch re-forms the projection off the CALLER's argument). A blanket
                    // `Ref`-substitution here would WRONGLY re-key a δ-REDUCED projection
                    // receiver: the self-recursive `count(rest)` grounds `s.E` to the
                    // enclosing `count.s.E`, whose receiver IS the callee formal `s` — so
                    // the blanket map (`s ↦ rest`) would corrupt it to `rest.E` (exactly the
                    // ticket's "undeclared effect: s.E, body's s.E = rest.E"). Re-key only
                    // the GROUND effect labels (`Modify[c]` → `Modify[s]`, WI-209), which
                    // carry no projection and which the surgical pass never touches.
                    if value_contains_projection(kb, e) {
                        e.clone()
                    } else {
                        substitute_ref_syms_value(kb, e, &param_to_arg_sym)
                    }
                })
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
            //
            // PURE σ here (NOT the grounding `resolve_type_deep_value` used for
            // `resolved_ret`): the effect row carries no δ-groundable projection. An
            // effect-position projection is an `ExprCarried` (`effects s.E`, WI-396),
            // already eliminated when `proj_effects` was built above; and an
            // op-type-param `RigidProjection` δ-grounds VALUE members only — the
            // concrete-fill is Sort-kind-gated and a provider fact cannot bind an effect
            // member (effects aren't expressible as type args, WI-301) — so there is
            // nothing in the effect row for the grounding variant to reduce. (Revisit if
            // effect members ever become δ-groundable.)
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
        let mut resolved_ret = resolve_type_deep_value(kb, &subst, &proj_return_type);

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
                        resolved_ret = resolve_type_deep_value(kb, &subst, &proj_return_type);
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
        // whether referenced bare or via anthill.prelude.Int64) makes
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
            // WI-453 (§5.4 requirement-discharge): if a STRUCTURED carrier param
            // (`CpsMonad`'s `F` — the higher-kinded one, which has its own members)
            // has FILLED to a concrete sort through the arg/expected unify, THAT sort
            // is the dispatch carrier. Discharging the implicit `Spec[F = C]`
            // obligation IS confirming `C` provides the spec (the WI-431 instance
            // fact): no provision ⟹ a loud no-instance error here (closing the
            // otherwise-silent accept of `unit(42) : MyBox`); a provision ⟹
            // `dispatch_spec_op_cached` below routes to the instance's bound impl —
            // ONE mechanism for the arg-carrier (`flatMap(o:Option,…)`) and the
            // result-carrier (`unit(42):Option`, carrier only in the return). A
            // first-order carrier param has no members, so it keeps the
            // receiver-carrier / value-directed path unchanged.
            // PERF gate: the HK fill only applies to an op whose signature USES a
            // higher-kinded carrier — i.e. has a parameterized type (`F[T=A]`) in the
            // return or a param. A bare first-order op (`combine(x:T, y:T) -> T`) skips
            // the probe entirely, so the common case never pays the `type_params_of_sort`
            // / `sort_type_params_as_pairs` scans below.
            let op_has_parameterized_sig =
                matches!(type_head(kb, &op.return_type), TypeHead::Parameterized { .. })
                    || op.params.iter().any(|(_, t)| {
                        matches!(type_head(kb, t), TypeHead::Parameterized { .. })
                    });
            let hk_carrier = op_has_parameterized_sig
                .then(|| {
                    sort_type_params_as_pairs(kb, spec_sort)
                        .iter()
                        .filter(|(p, _)| !kb.type_params_of_sort(*p).is_empty())
                        .find_map(|(_, var)| {
                            let walked = walk_type(kb, &subst, *var);
                            let c = extract_sort_ref_sym(kb, &TermIdView(walked))?;
                            (!is_sort_param_symbol(kb, c)
                                && kb.kind_of(c) == Some(crate::intern::SymbolKind::Sort))
                            .then_some(c)
                        })
                })
                .flatten();
            if let Some(c) = hk_carrier {
                // DISCHARGE the implicit `Spec[F = C]` obligation: confirm `C` provides
                // the spec (the WI-431 instance fact). No provision ⟹ undischarged: a
                // USER spec (warrants the abstract check) is a loud no-instance error
                // (never a silent accept of `unit(42):MyBox`); a host-builtin spec (no
                // fact by design) leaves the call as the spec op for the runtime to
                // resolve — the same escape the normal `NoCandidates` arm takes.
                if provider_spec_view_bindings(kb, c, spec_sort).is_none() {
                    if spec_warrants_abstract_check(kb, spec_sort) {
                        return Err(TypeError::DispatchNoMatch { span, op: fn_sym });
                    }
                    return Ok(TypeResult {
                        ty: resolved_ret.clone(),
                        env: env.clone(),
                        effects,
                        node: Rc::clone(occ),
                    });
                }
                // DISPATCH to the instance's bound impl (`unit ↦ optionUnit`). The
                // result-carrier `unit` has no carrier VALUE to value-direct on (F is
                // only in the return), so the typer-resolved dispatch is the route; the
                // arg-carrier shares it. A spec-DEFAULT op (not bound in the fact) keeps
                // its body. `dispatch_spec_op_cached`'s SLD does not read instance-fact
                // op-bindings (WI-431 inc 2), so the impl is read straight from the fact.
                if let Some(impl_op) = instance_fact_op_binding(kb, c, spec_sort, short_name_of(&op_qn)) {
                    // WI-453 effect soundness (the WI-365 dual): surface the impl's real
                    // effects — the instance signature validator checks arity/param/return
                    // but NOT effects, so an effectful impl bound to a pure-declared spec
                    // op would otherwise mask its effect at the consumption site.
                    if impl_op != fn_sym {
                        let derived = dispatched_impl_effects(
                            kb, impl_op, &op.params, &subst, pos_args, named_args,
                        );
                        effects = merge_effects(&effects, &derived);
                    }
                    // PinNow, or ConcreteApplyWithin when the impl's OWN sort declares
                    // `requires` (so its dict threads) — the Unique-arm discipline. Only
                    // a runnable impl is rewritten (a body-less one stays the spec op).
                    if op_has_runnable_body(kb, impl_op) {
                        let impl_sort = impl_parent_of_op(kb, impl_op);
                        let needs_reqs =
                            impl_sort.map(|s| !requires_chain(kb, s).is_empty()).unwrap_or(false);
                        let class = if needs_reqs {
                            CallClass::ConcreteApplyWithin {
                                fn_target_sym: impl_op,
                                callee_spec_sort: impl_sort.unwrap(),
                                spec_op_sym: fn_sym,
                                enclosing_sort,
                                resolved_tree: None,
                                dispatch_dict: None,
                            }
                        } else {
                            CallClass::PinNow { spec_op_sym: fn_sym, impl_op_sym: impl_op }
                        };
                        classify(kb, occ, class);
                    }
                }
                return Ok(TypeResult {
                    ty: resolved_ret.clone(),
                    env: env.clone(),
                    effects,
                    node: Rc::clone(occ),
                });
            }
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
                    resolved_ret = resolve_type_deep_value(kb, &subst, &proj_return_type);
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
                                // Pin-now path: the resolved_tree (when threaded
                                // by eval) carries the requirement; WI-415's
                                // compile-built dict is the Direct-call dual.
                                dispatch_dict: None,
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
                    // WI-415: build the parent-bundle dispatching dict NOW,
                    // while the per-call subst still pins `parent_sym`'s type
                    // params (`member(2, …)` ⇒ `List.T := Int`). A cross-sort /
                    // no-enclosing-sort call then threads the CONCRETE
                    // requirement (`Eq[Int]`) into the callee's frame; eval
                    // installs the pre-built dict without re-resolving. `None`
                    // when no param binds concretely: an in-sort call inherits
                    // the enclosing frame's requirement at eval, while a
                    // cross-sort abstract call has no covering requirement at
                    // all (a pre-existing gap WI-415 does not address).
                    let enclosing_sort = env.enclosing_sort();
                    let caller_requires: Vec<RequiresEntry> =
                        env.enclosing_requires().unwrap_or(&[]).to_vec();
                    let dispatch_dict = build_concrete_dispatch_dict(
                        kb, &subst, parent_sym, enclosing_sort, &caller_requires,
                    );
                    classify(
                        kb,
                        occ,
                        CallClass::ConcreteApplyWithin {
                            fn_target_sym: fn_sym,
                            callee_spec_sort: parent_sym,
                            spec_op_sym: fn_sym,
                            enclosing_sort,
                            resolved_tree: None,
                            dispatch_dict,
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
    build_dispatching_dict_from_chain(
        kb, callee_spec_sort, &callee_chain, caller_sort, caller_requires, syms, false,
    )
}

/// Shared core of the Direct-path dict build (`build_dispatching_dict_direct`)
/// and the WI-415 concrete build (`build_concrete_dispatch_dict`): emit
/// `construct_requirement(callee_spec_sort, [<one projection per `chain`
/// entry>])`, sourcing each projection from `caller_requires` via the
/// three-strategy search in `build_dep_projection`.
///
/// `chain` is the callee's DIRECT requires — one projection per slot the
/// callee body reads by `__req_<spec>` name, matching `synth_req_names` (also
/// direct) so the dict's arity equals the callee's direct-require count
/// (eval's `expand_dispatching_dict` invariant). Transitive requires are
/// bundled recursively inside each direct projection, not flattened. The
/// Direct path passes `direct_requires_chain` verbatim; WI-415 passes a copy
/// with the call-site bindings substituted in so each entry resolves
/// concretely.
///
/// `require_complete`: when true, a dep that fails to project aborts the whole
/// dict (`None`) — WI-415 needs every slot present (a short dict fails eval's
/// arity check), so it emits no dict and falls back rather than a broken one.
/// The Direct path passes false and silently drops un-projected deps (its
/// output is the diagnostic-only `dispatch_rewrites` term).
fn build_dispatching_dict_from_chain(
    kb: &mut KnowledgeBase,
    callee_spec_sort: Symbol,
    chain: &[RequiresEntry],
    caller_sort: Option<Symbol>,
    caller_requires: &[RequiresEntry],
    syms: &ProjectionSyms,
    require_complete: bool,
) -> Option<TermId> {
    // Hoist Strategy 2's per-slot direct-requires walk out of the dep loop:
    // it depends only on `caller_requires`, not on the current dep, so the
    // worst-case cost drops from O(deps × slots × |SortRequiresInfo|) to
    // O(slots × |SortRequiresInfo|). DIRECT (not transitive, WI-239): a
    // requirement value bundles only its own direct sub-requires, so
    // `requirement_at_sort(__req_i, k)`'s `k` indexes the i-th caller
    // require's *direct* sub-chain; a deeper dep falls through to Strategy 3.
    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| direct_requires_chain(kb, ar.required_sort))
        .collect();
    let mut proj_terms: Vec<TermId> = Vec::with_capacity(chain.len());
    for dep in chain {
        match build_dep_projection(
            kb, dep, caller_sort, caller_requires, &caller_sub_chains, syms,
        ) {
            Some(t) => proj_terms.push(t),
            None if require_complete => return None,
            None => {}
        }
    }
    let sub_reqs_list = super::load::build_cons_list(
        kb, &proj_terms, syms.nil, syms.cons, syms.head, syms.tail,
    );
    Some(build_construct_requirement(kb, syms, callee_spec_sort, sub_reqs_list))
}

/// WI-415/WI-418: build, at COMPILE stage, the parent-bundle dispatching dict a
/// directly-called op needs in its frame when it is called from OUTSIDE its sort
/// (so the same-sort requirement-inheritance path does not apply). The op's
/// parent sort `requires Spec[T]`; each direct requirement is projected into the
/// dict two ways, per the call site:
///
/// - **Concrete (WI-415):** the per-call `subst` pins `T` (`member(2, [1,2,3])`
///   ⇒ `List.T := Int`), so the abstract `Eq[T]` requirement substitutes to the
///   concrete `Eq[Int]` and resolves against `fact Eq[Int]` (Strategy 3).
/// - **Abstract cross-sort (WI-418):** the element stays abstract but the
///   ENCLOSING sort's own `requires` covers the dep (a sort `Coll requires
///   Eq[T]` whose op delegates to `List.member` on its abstract element), so the
///   dep is FORWARDED via a Strategy-1/2 `var_ref` that reads the caller frame's
///   `__req_*` at eval — threading `Coll`'s `__req_eq` onward to `member`.
///
/// Reuses the exact projection/construction helpers `build_dispatching_dict_direct`
/// (the requirement-insertion pass) uses; the difference is the call-site
/// bindings are substituted into the callee chain FIRST — which is why this runs
/// here, in the typer, where the subst is alive (it is gone by `req_insertion`).
///
/// Returns `None` (⇒ no dict; eval keeps its same-sort-inherit / plain-apply
/// behavior) for a SAME-SORT call (eval inherits the enclosing frame's
/// requirements) or when any requirement fails to project — neither a concrete
/// `fact` nor a covering caller `requires` — rather than emit an under-arity
/// dict eval would reject.
fn build_concrete_dispatch_dict(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    callee_spec_sort: Symbol,
    caller_sort: Option<Symbol>,
    caller_requires: &[RequiresEntry],
) -> Option<TermId> {
    // WI-418: a SAME-SORT call inherits the enclosing frame's requirements at
    // eval (`start_apply_same_sort` checks `inherit` — callee parent == caller
    // sort — first), so any dict built here would be ignored. Skip it. Every
    // other call (cross-sort, or no enclosing sort) builds a dict: a CONCRETE
    // dep resolves against its `fact` via Strategy 3 (WI-415); an ABSTRACT dep
    // the enclosing sort's own `requires` covers is FORWARDED via a Strategy-1/2
    // `var_ref` reading the caller frame's `__req_*` (WI-418 — e.g. a sort
    // `Coll requires Eq[T]` whose op delegates to `List.member` on its abstract
    // element, so `member` needs `Coll`'s `__req_eq` threaded onward).
    if caller_sort == Some(callee_spec_sort) {
        return None;
    }
    let abstract_chain = direct_requires_chain(kb, callee_spec_sort);
    if abstract_chain.is_empty() {
        return None;
    }
    // Substitute the call-site bindings into each direct requirement so a
    // concretely-pinned dep (`Eq[T]` ⇒ `Eq[Int]`) resolves against its `fact`;
    // an abstract dep is left open for the caller-frame `var_ref` forwarding.
    let concrete_chain: Vec<RequiresEntry> = abstract_chain
        .iter()
        .map(|entry| RequiresEntry {
            required_sort: entry.required_sort,
            spec: substitute_spec_via_subst(kb, entry.spec, subst),
        })
        .collect();
    let syms = ProjectionSyms::resolve(kb)?;
    // `require_complete = true`: every direct requirement must project into the
    // dict, else fall back to no dict (a short dict fails eval's arity check).
    build_dispatching_dict_from_chain(
        kb, callee_spec_sort, &concrete_chain, caller_sort, caller_requires, &syms, true,
    )
}

/// WI-415: substitute the per-call type bindings into a `requires`-entry spec
/// term. A sort-parameter `Ref` (e.g. the `Ref(List.T)` inside
/// `Eq[T = Ref(List.T)]`) whose logical variable the call-site `subst` bound
/// to a CONCRETE type (`List.T := Int`) is replaced by that type — turning
/// the enclosing sort's abstract `Eq[T]` requirement into the concrete
/// `Eq[Int]` the call actually needs. Mirrors `substitute_in_spec`'s
/// structural walk, but resolves the param→value mapping through
/// `resolve_sort_alias` + the live `subst` (no precomputed qualified-name
/// map, so it makes no assumption about how the param symbol is spelled). A
/// param left abstract (`is_type_param_value`) or unbound is preserved.
fn substitute_spec_via_subst(
    kb: &mut KnowledgeBase,
    spec: TermId,
    subst: &Substitution,
) -> TermId {
    match kb.get_term(spec).clone() {
        Term::Ref(s) => resolve_param_value_via_subst(kb, s, subst).unwrap_or(spec),
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            // Nullary Fn — the loader's alternative encoding for a bare name.
            resolve_param_value_via_subst(kb, functor, subst).unwrap_or(spec)
        }
        Term::Fn { .. } => {
            kb.map_fn_children(spec, |kb, child| substitute_spec_via_subst(kb, child, subst))
        }
        _ => spec,
    }
}

/// WI-415: the concrete type a sort-parameter symbol's logical variable is
/// bound to in `subst`, or `None` when `sym` is not a sort parameter, is
/// unbound, or is bound to another abstract type parameter (the call is not
/// concrete in that position — the enclosing sort's own `requires` carries
/// it). Mirrors how `sort_goal_from_subst` reads a binding: alias → `Global`
/// var → subst value.
fn resolve_param_value_via_subst(
    kb: &KnowledgeBase,
    sym: Symbol,
    subst: &Substitution,
) -> Option<TermId> {
    let alias_target = resolve_sort_alias(kb, sym)?;
    let vid = match kb.get_term(alias_target) {
        Term::Var(Var::Global(v)) => *v,
        _ => return None,
    };
    match subst.resolve_as_value(vid) {
        Some(Value::Term(val)) => {
            let val = *val;
            if is_type_param_value(kb, val) {
                None
            } else {
                Some(val)
            }
        }
        _ => None,
    }
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
    // WI-424: the `EffectsRuntime` kind-anchor (synthesized from `effects
    // E = ?`) is satisfied STRUCTURALLY by the effect-row machinery — there is
    // no carrier `fact` to resolve it against and no runtime dispatch ever
    // consults it (the same convention `check_provider_requires` and the
    // override-contract check follow). Project it as a synthetic structural
    // leaf so a chain containing it still completes: without this, a
    // `require_complete` dict build aborts on the un-projectable anchor and
    // the callee's frame slot stays unfilled, while a forwarded
    // `var_ref(__req_effectsruntime)` read (a cross-sort delegating body —
    // `Iterable.find` → `Stream.find`) then dies "unbound in requirement
    // position" at eval.
    if kb.qualified_name_of(dep.required_sort) == "anthill.prelude.EffectsRuntime" {
        let nil_list = super::load::build_cons_list(
            kb, &[], syms.nil, syms.cons, syms.head, syms.tail,
        );
        return Some(build_construct_requirement(kb, syms, dep.required_sort, nil_list));
    }

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
    // WI-420: bridge qualified↔short spec symbols (e.g. a not-yet-fully-resolved
    // `requires Eq` on a user sort vs the qualified `anthill.prelude.Eq` from a
    // loaded sort's direct-requires chain). `same_symbol` matches a bare short
    // name against a qualified name's last segment but NOT two distinct
    // fully-qualified specs that merely share a last segment, so it cannot
    // over-match. Plain `!=` here silently failed cross-sort requirement
    // forwarding when the two sides' spec symbols differed in qualification.
    if !same_symbol(kb, caller.required_sort, dep.required_sort) {
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
        /// WI-415: the parent-bundle dispatching dict
        /// (`construct_requirement(callee_parent, [<resolved sub-reqs>])`),
        /// built at COMPILE stage by the typer when the call-site
        /// substitution pinned the callee parent sort's type params
        /// concretely — a cross-sort / no-enclosing-sort direct call such
        /// as `member(2, [1,2,3])` from a plain namespace, where the
        /// same-sort requirement-inheritance path cannot supply the
        /// callee's `requires`. Eval installs it into the callee's frame
        /// via the same path an explicit `apply_within` dict takes, with
        /// no requirement re-resolution at runtime. `None` when no param
        /// binds concretely (an in-sort call inherits the enclosing frame's
        /// requirement at eval; a cross-sort abstract call has no covering
        /// requirement — a pre-existing gap) and for the Pin-now path.
        dispatch_dict: Option<TermId>,
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
    /// WI-420: a bare operation reference eta-lifted to a `Value::OpRef` whose
    /// op needs a requirement dictionary. `dict` is the dispatching dict
    /// (`construct_requirement(callee_parent, [...])` for a concrete dep, or a
    /// caller-frame `var_ref` projection for an abstract one — built by
    /// `build_concrete_dispatch_dict` at the eta site from the expected arrow's
    /// pinning). Eval evaluates it IN THE ETA-SITE FRAME at mint and stores the
    /// resulting requirement on the `OpRef`, then installs it into the callee
    /// frame at apply. Set only when the op has a satisfiable, non-inherited
    /// requirement; a requires-free or same-sort eta carries no classification
    /// and forwards the caller's requirements.
    EtaOpRef {
        dict: TermId,
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
        // WI-414: a CONCRETE per-call value (e.g. `Eq.T := Int` from
        // `eq(i: Int, 0)`) must NOT defer to an OPEN-T requirement entry
        // (`requires Eq[T]`, the enclosing sort's abstract element) — such a call
        // is not "the enclosing T", so it dispatches concretely to the available
        // `fact Eq[Int]`. Without this the wildcard match below treated `Int` vs
        // the open `T` as a match, deferring a concretely-dispatchable call to a
        // `__req` slot that an external caller never binds (a compile-clean call
        // that then aborts at runtime). An ABSTRACT per-call value (the enclosing
        // T itself) still defers below — its impl IS the requirement; and a
        // concrete call to a CONCRETE requirement (`requires Eq[T=Int]`) still
        // defers via the dispatch match (entry not a wildcard).
        if !is_type_param_value(kb, per_call_value) && is_type_param_value(kb, *entry_value) {
            return false;
        }
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
/// WI-429: end-of-load formation validation for STORED `RigidTypeProjection`
/// terms. The typer validates a projection where it ELIMINATES one (op
/// signatures, call sites, let annotations — `resolve_rigid_projection`), but
/// a projection stored in a position the typer never eliminates (an entity
/// FIELD type, a fact / constraint / rule type slot) previously loaded
/// SILENTLY — a typo'd member (`MemStore.Kye`) or a bare-spec subject
/// (`Storage.Key` outside the sort) sat in the KB as a malformed type. The
/// loader records every formation (`kb.rigid_projection_formations`, with
/// source spans); this sweep re-runs the eliminator's own
/// `resolve_rigid_projection` on each — requires/provides info is complete by
/// this point in the load pipeline — and surfaces any rejection as a
/// load-blocking error. Valid outcomes (`Grounded` / `Neutral`) pass; the
/// sweep validates formation only and stores nothing, so a projection in an
/// eliminated position is at worst validated twice with the same verdict.
pub fn validate_rigid_projection_formations(
    kb: &mut KnowledgeBase,
) -> Vec<super::load::LoadError> {
    let formations = std::mem::take(&mut kb.rigid_projection_formations);
    let mut errors = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::new();
    for (tid, source_span) in formations {
        // One hash-consed projection can be formed at many sites; one verdict
        // suffices (the first formation's span reports it).
        if !seen.insert(tid) {
            continue;
        }
        let TypeExtractor::RigidTypeProjection { sort, subject, member } =
            extract_type(kb, &TermIdView(tid))
        else {
            unreachable!(
                "rigid_projection_formations holds a non-RigidTypeProjection term \
                 — loader recording bug"
            );
        };
        let ctx = TypeErrorContext::EntityField { entity: sort, field: member };
        let span = Some(Span::new(source_span.start(), source_span.end()));
        if let Err(te) = resolve_rigid_projection(kb, sort, &subject, member, &ctx, span) {
            errors.push(te.to_load_error(kb));
        }
    }
    errors
}

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
    // `spec_view` is the full `SortView` term — kept so the op-coverage check
    // can read an INSTANCE FACT's op-valued bindings (`pure = optionPure`), the
    // dictionary entries that back a spec op without the carrier owning it
    // (WI-431).
    struct Provision { carrier: Symbol, spec: Symbol, spec_view: TermId }
    let mut provisions: Vec<Provision> = Vec::new();
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) { continue; }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &named, "sort_ref") else { continue };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else { continue };
        let Some(spec_view) = get_named_arg(kb, &named, "spec") else { continue };
        let Some(spec) = super::load::provides_spec_base_sym(kb, spec_view) else { continue };
        provisions.push(Provision { carrier, spec, spec_view });
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
            // WI-431: a retroactive INSTANCE FACT (`fact CpsMonad[F = Option,
            // pure = optionPure, …]`) backs a spec op by BINDING it in the fact
            // — the op-valued binding IS the dictionary entry. Coverage moves to
            // the fact: an op bound here (to an operation) is backed without the
            // carrier owning it or the spec defaulting it. A type-only provision
            // (`provides Stream[T = X]`) has no op-valued binding, so this never
            // matches and pre-WI-431 coverage is unchanged.
            if op_bound_in_instance_fact(kb, p.spec_view, &op_short) {
                continue;
            }
            errors.push(LoadError::UnbackedProviderOperation {
                carrier: carrier_qn.clone(),
                spec: kb.qualified_name_of(p.spec).to_string(),
                op: op_short,
            });
        }
    }

    // WI-431 rule 2 — COHERENCE. Two DISTINCT instance facts (op-valued
    // provisions) for the same (spec, carrier) each supply a different
    // dictionary; with no scoped/named instance selection yet, dispatch would
    // silently pick the first (the `provider_spec_view_bindings`
    // first-provider-wins contract honored by increment 2's eval dispatch). Make
    // it loud at load. Identity is the full canonical application (the WI-419 /
    // §5.4 rule): spec views hash-cons, so identical instance facts share one
    // `spec_view` (idempotent — collapsed by the per-group distinctness check)
    // and only genuinely-differing facts collide. Restricted to op-binding
    // provisions: a type-only provision (`provides Stream[T = X]`) supplies no
    // dictionary and never participates, so existing `provides` / type-only
    // `fact`s (e.g. `fact ModifyRuntime[T = Cell, V = V]`) are never
    // over-rejected. Insertion-order grouping keeps the diagnostics deterministic.
    //
    // Symbol identity: the `(spec, carrier)` key and the `spec_view` are compared
    // RAW (no `canonical_sort_sym`). Sound because this is a PROVIDER-to-PROVIDER
    // comparison — both come from `SortProvidesInfo` facts resolved post-load, so
    // two providers for one logical instance share the same canonical symbols and
    // hash-cons to the same `spec_view` (verified across namespaces by
    // `cross_namespace_{distinct,identical}_instances_*`). This differs from
    // `provider_spec_view_bindings`, which compares a CALLER's spec symbol
    // (resolved in a different scope) to providers and so must canonicalize;
    // canonicalizing only the key here (without the `spec_view`) would instead
    // FALSE-flag copy-divergent-but-identical facts.
    let mut coherence_groups: Vec<((Symbol, Symbol), SmallVec<[TermId; 2]>)> = Vec::new();
    for p in &provisions {
        if !provision_binds_any_op(kb, p.spec_view) {
            continue;
        }
        match coherence_groups
            .iter_mut()
            .find(|(key, _)| *key == (p.spec, p.carrier))
        {
            Some((_, views)) => {
                if !views.contains(&p.spec_view) {
                    views.push(p.spec_view);
                }
            }
            None => coherence_groups.push(((p.spec, p.carrier), SmallVec::from_elem(p.spec_view, 1))),
        }
    }
    for ((spec, carrier), views) in &coherence_groups {
        if views.len() > 1 {
            errors.push(LoadError::AmbiguousInstanceFact {
                carrier: kb.qualified_name_of(*carrier).to_string(),
                spec: kb.qualified_name_of(*spec).to_string(),
                count: views.len(),
            });
        }
    }

    // WI-450 witness coherence (rule 2, witness flavor): two distinct WITNESS sorts
    // that provide the SAME spec application supply conflicting dictionaries through
    // their member ops. Unlike an instance fact — whose op-valued binding makes two
    // conflicting instances DIFFER in their `spec_view` (caught above) — a witness's
    // op lives in the provider SORT, so two witnesses for one application share ONE
    // hash-consed `spec_view`. Group by (spec, dispatch carrier) and flag >1 distinct
    // PROVIDER.
    //
    // A provision is a WITNESS only when the spec's carrier param (its first type
    // parameter) is bound to a concrete sort DISTINCT from the provider — `sort
    // TagCombiner provides Combiner[T = Tag]` (carrier `Tag` ≠ provider
    // `TagCombiner`). This excludes (a) instance facts and normal self-providers,
    // whose derived/own carrier IS the provider (so they never collide here — facts
    // ride the spec_view rule above), and (b) bare / carrier-less provisions
    // (`provides Store`), which name no dispatch carrier. An idempotent re-record of
    // one witness shares its provider and collapses.
    let mut witness_groups: Vec<((Symbol, Symbol), SmallVec<[Symbol; 2]>)> = Vec::new();
    for p in &provisions {
        // Only a spec that declares OPS has a dictionary to be ambiguous about — a
        // bare carrier spec (`sort W449Outer { sort C = ? }`, no ops) provided by two
        // carriers is binding-extraction plumbing, not a dispatch conflict. (Mirrors
        // the `provision_binds_any_op` gate the instance-fact rule above applies.)
        if own_ops.get(&p.spec).map_or(true, |ops| ops.is_empty()) {
            continue;
        }
        // A pure DICTIONARY witness has no constructors — its only role is to back
        // the spec's ops for the carrier. A CONCRETE provider (with constructors) is
        // a backend whose VALUES carry their own sort, so value-directed dispatch
        // distinguishes them by the value (a self-receiver spec, OUT OF SCOPE): two
        // concrete backends providing one spec at the same bindings is the existential
        // / manifest-provider pattern (`MemStore` / `DiskStore` provide `KVStore[K =
        // String]`, design §5 — selected by the `ensures` return), NOT an ambiguity.
        if concrete.contains(&p.carrier) {
            continue;
        }
        let Some(carrier) = provision_carrier_sort(kb, p.spec, p.spec_view) else { continue };
        let carrier_canon = kb.canonical_sort_sym(carrier);
        // Provider IS the carrier ⇒ a fact / normal self-provider, not a witness.
        if kb.canonical_sort_sym(p.carrier) == carrier_canon {
            continue;
        }
        let key = (kb.canonical_sort_sym(p.spec), carrier_canon);
        match witness_groups.iter_mut().find(|(k, _)| *k == key) {
            Some((_, providers)) => {
                let pc = kb.canonical_sort_sym(p.carrier);
                if !providers.iter().any(|q| kb.canonical_sort_sym(*q) == pc) {
                    providers.push(p.carrier);
                }
            }
            None => witness_groups.push((key, SmallVec::from_elem(p.carrier, 1))),
        }
    }
    for ((spec, carrier), providers) in &witness_groups {
        if providers.len() > 1 {
            errors.push(LoadError::AmbiguousWitness {
                carrier: kb.qualified_name_of(*carrier).to_string(),
                spec: kb.qualified_name_of(*spec).to_string(),
                count: providers.len(),
            });
        }
    }

    errors
}

/// WI-450 — the concrete SORT the spec's carrier param (its first type parameter)
/// is bound to in a provision's `spec_view` (`Combiner[T = Tag]` ⇒ `Tag`), or
/// `None` for a bare / carrier-less provision or a non-sort binding. Used by witness
/// coherence to tell a WITNESS (carrier ≠ provider sort) from a fact / self-provider
/// (carrier IS the provider).
fn provision_carrier_sort(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    spec_view: TermId,
) -> Option<Symbol> {
    let params = sort_type_params_as_pairs(kb, spec_sort);
    let carrier_param = params.first()?.0;
    let carrier_short = short_name_of(kb.resolve_sym(carrier_param));
    let (_, bindings) = unwrap_spec_view(kb, spec_view)?;
    let val = bindings
        .iter()
        .find_map(|(k, v)| (short_name_of(kb.resolve_sym(*k)) == carrier_short).then_some(*v))?;
    super::load::provides_spec_base_sym(kb, val)
        .filter(|s| matches!(kb.kind_of(*s), Some(crate::intern::SymbolKind::Sort)))
}

/// WI-431: the OPERATION symbol an instance fact binds for `op_short` among a
/// provision's `SortView` `bindings` (`pure = optionPure` ⇒ `optionPure`), or
/// `None` if `op_short` is not bound to an operation. The op-valued binding IS
/// the dictionary entry that backs the spec op — read at the fact-coverage check
/// (loader) and at spec-op dispatch (eval) through this one accessor. The bound
/// value's base symbol is read via `provides_spec_base_sym` (the same
/// op-discriminator [`sort_view_substitution`](super::load) uses, which also
/// unwraps a `SortView`-wrapped parameterized value); a type-valued binding
/// (`F = Option`, a `Sort`) yields `None`, so a plain type-only provision
/// (`provides Stream[T = X]`) never matches.
fn instance_fact_op_in_bindings(
    kb: &KnowledgeBase,
    bindings: &[(Symbol, TermId)],
    op_short: &str,
) -> Option<Symbol> {
    bindings.iter().find_map(|(key, value)| {
        if short_name_of(kb.qualified_name_of(*key)) != op_short {
            return None;
        }
        binding_op_symbol(kb, *value)
    })
}

/// WI-431: the OPERATION symbol an instance-fact binding `value` denotes
/// (`pure = optionPure` ⇒ `optionPure`), or `None` when the binding is not
/// op-valued (a type binding `F = Option`, a `Sort`). The single op-discriminator
/// shared by fact-coverage (rule 1), eval dispatch (increment 2), and coherence
/// (rule 2): a binding backs a spec op iff its base symbol — read via
/// `provides_spec_base_sym`, which also unwraps a parameterized `SortView` — is an
/// `Operation`. Folding all three callers through this one predicate keeps them
/// from disagreeing about what an op-valued binding is.
pub(crate) fn binding_op_symbol(kb: &KnowledgeBase, value: TermId) -> Option<Symbol> {
    super::load::provides_spec_base_sym(kb, value)
        .filter(|s| matches!(kb.kind_of(*s), Some(crate::intern::SymbolKind::Operation)))
}

/// WI-431 coherence (rule 2): true iff the provision's spec view binds AT LEAST
/// ONE operation — i.e. it is an INSTANCE FACT supplying a dictionary, not a
/// type-only provision (`provides Stream[T = X]`). Only instance facts
/// participate in dictionary coherence: a type-only provision contributes no
/// dispatch target, so it can never be the ambiguous one (and an existing
/// `provides` / type-only `fact` is never over-rejected).
fn provision_binds_any_op(kb: &KnowledgeBase, spec_view: TermId) -> bool {
    match unwrap_spec_view(kb, spec_view) {
        Some((_, bindings)) => bindings
            .iter()
            .any(|(_, value)| binding_op_symbol(kb, *value).is_some()),
        None => false,
    }
}

/// WI-431 loader coverage: true iff the provision's spec view binds `op_short`
/// to an operation — the instance-fact backing for that spec op.
fn op_bound_in_instance_fact(kb: &KnowledgeBase, spec_view: TermId, op_short: &str) -> bool {
    match unwrap_spec_view(kb, spec_view) {
        Some((_, bindings)) => instance_fact_op_in_bindings(kb, &bindings, op_short).is_some(),
        None => false,
    }
}

/// WI-431 eval dispatch: the operation backing spec op `op_short` for `carrier`
/// through an instance fact `SortProvidesInfo(carrier, Spec[…, op_short = op])`.
/// The dispatch fallback when `carrier` owns no `op_short` of its own — a
/// retroactive instance binds the op in the fact instead of on the carrier.
pub(crate) fn instance_fact_op_binding(
    kb: &KnowledgeBase,
    carrier: Symbol,
    spec_sort: Symbol,
    op_short: &str,
) -> Option<Symbol> {
    let bindings = provider_spec_view_bindings(kb, carrier, spec_sort)?;
    instance_fact_op_in_bindings(kb, &bindings, op_short)
}

/// WI-450: the first WITNESS provision of `spec_sort` for `carrier` — a provider
/// whose `sort_ref` is NOT the carrier but which binds `carrier` as a spec
/// type-param VALUE (`sort TagCombiner provides Combiner[T = Tag]` ⇒ provider
/// `TagCombiner`, carrier `Tag` bound to `T`). Returns `(provider sort, the
/// provision's type-param bindings)`.
///
/// This is the param-agnostic dual of the carrier-keyed
/// [`provider_spec_view_bindings`] (which keys `sort_ref == carrier`): a witness's
/// `sort_ref` is the witness sort, not the carrier, so the carrier-keyed path
/// cannot see it — a `fact Combiner[T = Tag, …]` works only because its DERIVED
/// carrier IS `Tag`. Coherence (two witnesses for one application) is rejected at
/// load by [`check_provider_operations`], so first-match is the sole instance.
fn witness_provision(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    carrier: Symbol,
) -> Option<(Symbol, SmallVec<[(Symbol, TermId); 2]>)> {
    let provides_sym = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo")?;
    let carrier_canon = kb.canonical_sort_sym(carrier);
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &named, "sort_ref") else { continue };
        let Some(provider) = super::load::sort_ref_functor(kb, sr) else { continue };
        // Witness = provider distinct from the carrier. `provider == carrier`
        // (facts whose carrier IS the sort_ref, normal providers) is the
        // carrier-keyed path's job — never re-handled here.
        if kb.canonical_sort_sym(provider) == carrier_canon {
            continue;
        }
        let Some(spec_t) = get_named_arg(kb, &named, "spec") else { continue };
        let Some((base, bindings)) = unwrap_spec_view(kb, spec_t) else { continue };
        if kb.canonical_sort_sym(base) != spec_canon {
            continue;
        }
        // The CARRIER PARAM (the spec's first type parameter — `Combiner.T`) must be
        // bound to the dispatch carrier. Uses the SAME `provision_carrier_sort` the
        // coherence pass and `find_spec_op_for_provided_sort` use, so witness
        // detection is identical across dispatch / classification / coherence — a
        // NON-carrier param of a multi-param spec that merely happens to bind the
        // carrier sort (`Spec[A = Other, B = Tag]` for carrier `Tag`) does not
        // spuriously match.
        let binds_carrier = provision_carrier_sort(kb, spec_sort, spec_t)
            .map(|c| kb.canonical_sort_sym(c) == carrier_canon)
            .unwrap_or(false);
        if binds_carrier {
            return Some((provider, bindings));
        }
    }
    None
}

/// WI-450: resolve a spec op through a WITNESS SORT — the param-agnostic dual of
/// [`instance_fact_op_binding`]. The witness owns the impl (`combine`) as a MEMBER
/// of the witness sort (`TagCombiner.combine`), resolved through the sort_ops table
/// like any provider's own op. The ADDITIVE fallback for the `sort_ref != carrier`
/// case — the carrier-keyed path stays primary, so the hot path is undisturbed.
pub(crate) fn witness_op_for_carrier(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    carrier: Symbol,
    op_short: Symbol,
) -> Option<Symbol> {
    let (provider, _) = witness_provision(kb, spec_sort, carrier)?;
    kb.sort_ops_lookup(provider, op_short)
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
    type_param_sym_of_binding(kb, short, spec_qn).is_some()
}

/// WI-431 (B): if `short` (a provision binding key) names a type parameter of the
/// spec `spec_qn`, return the RESOLVED spec-parameter symbol — the one the spec
/// operations' types actually reference (`Combiner.combine`'s `Ref(Combiner.T)`)
/// — so a σ keyed on it actually substitutes. The raw binding key can be a
/// different `Symbol` copy (resolved in the fact's scope), against which
/// `substitute_impl_params_alloc`'s `Symbol`-equality match is a silent no-op.
fn type_param_sym_of_binding(kb: &KnowledgeBase, short: Symbol, spec_qn: &str) -> Option<Symbol> {
    let short_name = kb.resolve_sym(short).to_string();
    let qn = format!("{spec_qn}.{short_name}");
    let s = kb.try_resolve_symbol(&qn)?;
    resolve_sort_alias(kb, s).map(|_| s)
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

/// WI-431 (B) — INSTANCE-FACT op-binding SIGNATURE validation. An instance fact
/// `fact Spec[<carrier param> = C, op = boundOp, …]` makes `boundOp` back the
/// spec op `Spec.op` for carrier `C` (rule 1 coverage + increments 2/4 dispatch).
/// Nothing else checks `boundOp`'s SIGNATURE against `Spec.op`'s, so a mis-bound
/// op (`combine = unrelatedOp`) would load and then dispatch to a wrongly-typed
/// impl. This pass checks, with σ (the spec's type parameter → its provision
/// binding) applied to the spec op's types: same param ARITY; each PARAM type
/// contravariantly compatible (the bound op accepts the spec's arg type); the
/// RETURN type covariantly compatible. Type comparisons are GROUND-GATED — only
/// when the σ-substituted spec type and the bound type are both ground
/// `Value::Term` — so a higher-kinded binding whose param stays parametric
/// (`pure : F[T = A]`) fails open, deferred to WI-383. Arity is always checked.
/// A dedicated pass (not folded into [`check_override_refinement`]) so the
/// carrier-own override path is untouched; instance facts have no stdlib presence
/// yet, so this can be strict without regressing existing providers.
pub fn check_instance_fact_op_signatures(kb: &mut KnowledgeBase) -> Vec<super::load::LoadError> {
    use super::load::LoadError;
    let Some(provides_sym) = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") else {
        return Vec::new();
    };
    // Spec's own declared ops, to resolve a binding key's short name → the spec op.
    let own: HashMap<Symbol, Vec<Symbol>> =
        super::load::sorts_and_own_ops(kb).into_iter().collect();

    // Snapshot the INSTANCE-FACT provisions before the (mutating) type checks:
    // carrier, spec base, σ (type-param bindings), and the op-valued bindings
    // (binding-key short name → bound operation). A provision with no op binding
    // is a plain type-only provision and is skipped.
    struct Prov {
        carrier: Symbol,
        spec: Symbol,
        sigma: Vec<(Symbol, TermId)>,
        ops: Vec<(String, Symbol)>,
    }
    let mut provs: Vec<Prov> = Vec::new();
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &named, "sort_ref") else { continue };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else { continue };
        let Some(spec_view) = get_named_arg(kb, &named, "spec") else { continue };
        let Some((spec_base, bindings)) = unwrap_spec_view(kb, spec_view) else { continue };
        let spec_qn = kb.qualified_name_of(spec_base).to_string();
        let mut sigma: Vec<(Symbol, TermId)> = Vec::new();
        let mut ops: Vec<(String, Symbol)> = Vec::new();
        for (k, v) in &bindings {
            // σ keys on the RESOLVED spec-param symbol (the one the spec op types
            // reference), not the raw binding key copy — else the substitution
            // silently no-ops and every type check falls open.
            if let Some(param_sym) = type_param_sym_of_binding(kb, *k, &spec_qn) {
                sigma.push((param_sym, *v));
            } else if let Some(bound_op) = binding_op_symbol(kb, *v) {
                ops.push((short_name_of(kb.qualified_name_of(*k)).to_string(), bound_op));
            }
        }
        if ops.is_empty() {
            continue;
        }
        provs.push(Prov { carrier, spec: spec_base, sigma, ops });
    }

    let mut errors = Vec::new();
    for p in &provs {
        let Some(spec_ops) = own.get(&p.spec) else { continue };
        // Per-provision invariants — hoisted out of the per-binding loop.
        let carrier_qn = kb.qualified_name_of(p.carrier).to_string();
        let spec_qn = kb.qualified_name_of(p.spec).to_string();
        for (op_short, bound_op) in &p.ops {
            // The spec op the binding key names. A key naming no spec op is the
            // coverage check's concern, not this one.
            let Some(&spec_op) = spec_ops
                .iter()
                .find(|&&o| short_name_of(kb.qualified_name_of(o)) == *op_short)
            else {
                continue;
            };
            let Some(spec_info) = super::op_info::lookup_operation_info(kb, spec_op) else { continue };
            let Some(bound_info) = super::op_info::lookup_operation_info(kb, *bound_op) else { continue };
            let bound_qn = kb.qualified_name_of(*bound_op).to_string();

            // ── arity (always checkable) ────────────────────────────────────
            if spec_info.params.len() != bound_info.params.len() {
                errors.push(LoadError::IncompatibleInstanceBinding {
                    carrier: carrier_qn.clone(),
                    spec: spec_qn.clone(),
                    op: op_short.clone(),
                    reason: format!(
                        "the spec operation takes {} parameter(s) but the bound operation '{}' takes {}",
                        spec_info.params.len(), bound_qn, bound_info.params.len()),
                });
                continue;
            }

            // ── per-param type (contravariant: σ(spec_param) <: bound_param) ─
            for (i, ((_, spec_pty), (_, bound_pty))) in spec_info
                .params
                .iter()
                .zip(bound_info.params.iter())
                .enumerate()
            {
                if instance_binding_type_ok(kb, spec_pty, bound_pty, &p.sigma, false) == Some(false) {
                    let bound_disp = type_display_name_value(kb, bound_pty);
                    let spec_disp = type_display_name_value(kb, spec_pty);
                    errors.push(LoadError::IncompatibleInstanceBinding {
                        carrier: carrier_qn.clone(),
                        spec: spec_qn.clone(),
                        op: op_short.clone(),
                        reason: format!(
                            "parameter {} of the bound operation has type `{}`, incompatible with the spec parameter type `{}`",
                            i + 1, bound_disp, spec_disp),
                    });
                }
            }

            // ── return type (covariant: bound_ret <: σ(spec_ret)) ───────────
            if instance_binding_type_ok(kb, &spec_info.return_type, &bound_info.return_type, &p.sigma, true)
                == Some(false)
            {
                let bound_disp = type_display_name_value(kb, &bound_info.return_type);
                let spec_disp = type_display_name_value(kb, &spec_info.return_type);
                errors.push(LoadError::IncompatibleInstanceBinding {
                    carrier: carrier_qn.clone(),
                    spec: spec_qn.clone(),
                    op: op_short.clone(),
                    reason: format!(
                        "the bound operation returns `{}`, incompatible with the spec return type `{}`",
                        bound_disp, spec_disp),
                });
            }
        }
    }
    errors
}

/// WI-431 (B): compare one bound-op type against the σ-substituted spec-op type.
/// `Some(true)` confidently compatible, `Some(false)` a confident GROUND mismatch
/// (→ a loud error), `None` not confident (a non-ground / `Value::Node`
/// parametric type — fail open, the higher-kinded case deferred to WI-383).
/// `bound_is_subtype`: the return is covariant (`bound <: σ(spec)`), a param is
/// contravariant (`σ(spec) <: bound` — the bound op must accept the spec's arg).
fn instance_binding_type_ok(
    kb: &mut KnowledgeBase,
    spec_ty: &Value,
    bound_ty: &Value,
    sigma: &[(Symbol, TermId)],
    bound_is_subtype: bool,
) -> Option<bool> {
    let Value::Term(spec_t) = spec_ty else { return None };
    let Value::Term(bound_t) = bound_ty else { return None };
    let spec_sub = if sigma.is_empty() {
        *spec_t
    } else {
        substitute_impl_params_alloc(kb, *spec_t, sigma)
    };
    // Confident only when both sides are ground — no spec/op type parameter left.
    if contains_type_param(kb, spec_sub) || contains_type_param(kb, *bound_t) {
        return None;
    }
    let spec_v = Value::Term(spec_sub);
    let bound_v = Value::Term(*bound_t);
    let mut subst = Substitution::new();
    Some(if bound_is_subtype {
        types_compatible(kb, &mut subst, &bound_v, &spec_v)
    } else {
        types_compatible(kb, &mut subst, &spec_v, &bound_v)
    })
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
/// (an argument's inferred `TypeResult.ty`). WI-477: read carrier-agnostically
/// through `sort_functor_of_view` — an occurrence-primary type result is a
/// `Value::Node`, and `.as_term()` would drop it; a structural carrier (arrow /
/// effect-row / denoted) has no sort head and yields `None` here, as before.
fn carrier_sort_of_value(kb: &KnowledgeBase, v: &Value) -> Option<Symbol> {
    sort_functor_of_view(kb, v)
}

/// WI-424 — the canonical param `VarId` a declared parameter type stands for:
/// either the alias var directly (`Term::Var(Global)`) or a `Ref`/`Ident` to a
/// sort type-param resolved through its `SortAlias` — the form a signature
/// stores (`c: C` is `Ref(S.C)`, exactly as `effects E` is `Ref(S.E)`).
fn declared_type_param_vid(kb: &KnowledgeBase, pty: &Value) -> Option<VarId> {
    if let Some(v) = resolved_var(kb, pty) {
        return Some(v);
    }
    // WI-477: read the head carrier-agnostically — a sort type-param ref (`c: C`
    // ⇒ `Ref(S.C)`) reads as `ViewHead::Ref`/`Ident` whether the param type rides
    // as a `TermId` or a `Value::Node`; a structural carrier (arrow/row) has no
    // such head → `None`, as before.
    let sym = match pty.head(kb) {
        ViewHead::Ref(s) | ViewHead::Ident(s) => s,
        _ => return None,
    };
    match kb.get_term(resolve_sort_alias(kb, sym)?) {
        Term::Var(Var::Global(v)) => Some(*v),
        _ => None,
    }
}

/// WI-424 — the gate distinguishing a spec's CARRIER param from an
/// element-like param: does `carrier_sym`'s provision of `spec_sort` bind the
/// spec param whose canonical var is `pvid` to an application of the carrier
/// itself (`provides Iterable[C = List[T], …]` ⇒ true for `C`'s vid with
/// carrier `List`; false for `Element`'s)? Shared by the typer's
/// [`carrier_param_receiver`] and eval's [`carrier_param_receiver_for_values`]
/// so the two classifications cannot disagree about which argument names the
/// carrier. The binding value rides a `SortView(List[T], …)` wrapper — unwrap
/// via the same reader the provider machinery uses.
fn provision_binds_param_to_carrier(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    pvid: VarId,
    carrier_sym: Symbol,
) -> Option<SmallVec<[(Symbol, TermId); 2]>> {
    let carrier_canon = kb.canonical_sort_sym(carrier_sym);
    let binds_pvid_to_carrier = |view: &SmallVec<[(Symbol, TermId); 2]>| {
        view.iter().any(|(sp_sym, sp_val)| {
            type_param_vid_in_sort(kb, spec_sort, *sp_sym) == Some(pvid)
                && super::load::provides_spec_base_sym(kb, *sp_val)
                    .map(|b| kb.canonical_sort_sym(b))
                    == Some(carrier_canon)
        })
    };
    // Primary: the carrier-keyed provision (`sort_ref == carrier`) — a fact whose
    // derived carrier IS the value's sort, or a normal provider whose own sort IS
    // the carrier. Unchanged hot path (Iterable.iterator on a List, Eq on Int64).
    if let Some(view) = provider_spec_view_bindings(kb, carrier_sym, spec_sort) {
        if binds_pvid_to_carrier(&view) {
            return Some(view);
        }
    }
    // WI-450: a WITNESS provision (`sort_ref != carrier`) of `spec_sort` that binds
    // this param to the carrier — `sort TagCombiner provides Combiner[T = Tag]`
    // classifies a `T`-typed arg valued `Tag` as the carrier param even though the
    // provider sort is `TagCombiner`, not `Tag`.
    if let Some((_, view)) = witness_provision(kb, spec_sort, carrier_sym) {
        if binds_pvid_to_carrier(&view) {
            return Some(view);
        }
    }
    None
}

/// WI-424 — eval-side CARRIER-PARAM receiver: among the params typed as one of
/// `spec_sort`'s own type-param vars (`Iterable.iterator(c: C)`), the first
/// whose RUNTIME value's carrier sort (`carrier_of(i)`) provides the spec WITH
/// that param bound to the carrier application — the same
/// [`provision_binds_param_to_carrier`] gate the typer applies, so an
/// element-typed param never dispatches (the value-directed dual of
/// [`self_receiver_param_index`]'s deliberate type-param-carrier exclusion).
/// Returns the param index and the value's carrier sort.
pub(crate) fn carrier_param_receiver_for_values(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    spec_sort: Symbol,
    carrier_of: &dyn Fn(usize) -> Option<Symbol>,
) -> Option<(usize, Symbol)> {
    let spec_params = sort_type_params_as_pairs(kb, spec_sort);
    if spec_params.is_empty() {
        return None;
    }
    for (i, (_, pty)) in params.iter().enumerate() {
        let Some(pvid) = declared_type_param_vid(kb, pty) else { continue };
        if !spec_params.iter().any(|(_, t)| {
            matches!(kb.get_term(*t), Term::Var(Var::Global(v)) if *v == pvid)
        }) {
            continue;
        }
        let Some(carrier_sym) = carrier_of(i) else { continue };
        if provision_binds_param_to_carrier(kb, spec_sort, pvid, carrier_sym).is_some() {
            return Some((i, carrier_sym));
        }
    }
    None
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
    // WI-470: read the receiver's inferred type as a carrier-agnostic `Value`, NOT via
    // `.as_term()` — an occurrence-primary `List[T = Int]` is a `Value::Node`, and
    // `.as_term()` would return `None` and drop the carrier (erasing its `T`/`Eff`
    // bindings → a spurious `Eff unconstrained`). The binding is read below through
    // `parameterized_short_bindings` (carrier-agnostic), so it is preserved.
    let recv_ty: Option<Value> = pos_results
        .get(idx)
        .and_then(|r| r.as_ref().ok())
        .map(|r| r.ty.clone())
        .or_else(|| {
            named_args
                .iter()
                .position(|(n, _)| *n == param_name)
                .and_then(|j| named_results.get(j))
                .and_then(|r| r.as_ref().ok())
                .map(|r| r.ty.clone())
        });
    let Some(recv_ty) = recv_ty else {
        return false;
    };

    // The receiver's own type arguments, keyed by carrier-param short name.
    let recv_bindings = parameterized_short_bindings(kb, &recv_ty);
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

/// WI-424 — classify a CARRIER-PARAM receiver: a spec op that takes its carrier
/// through a parameter typed as the spec's own carrier type-param
/// (`Iterable.find(c: C, …)`, `sort C = ?` on Iterable) rather than as the spec
/// sort itself (`Stream.find(s: Stream, …)`). [`self_receiver_param_index`]
/// deliberately skips such params (a type-param-typed param is not a
/// self-receiver for value dispatch), so the WI-357/393 carrier grounding never
/// engages and the spec's OTHER params (`Element`, the written `E` row) stay
/// unbound at a concrete consumption site — `find(xs, pred)` on a `List[Int64]`
/// leaks `?_` for the effect row.
///
/// A param classifies when: its declared type IS one of the spec's own
/// type-param vars; its argument's inferred type names a sort that PROVIDES the
/// spec; and the provision binds THAT spec param to an application of the
/// carrier itself ([`provision_binds_param_to_carrier`] — distinguishing the
/// carrier param from an element-like param). First match wins. Returns
/// `(spec sort, carrier sort, receiver's inferred type, the provision's view
/// bindings)` — the view rides along so the binder does not re-scan the
/// provider facts.
fn carrier_param_receiver(
    kb: &KnowledgeBase,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> Option<(Symbol, Symbol, Value, SmallVec<[(Symbol, TermId); 2]>)> {
    let spec_sort = impl_parent_of_op(kb, fn_sym)?;
    let spec_params = sort_type_params_as_pairs(kb, spec_sort);
    if spec_params.is_empty() {
        return None;
    }
    for (i, (pname, pty)) in op.params.iter().enumerate() {
        let Some(pvid) = declared_type_param_vid(kb, pty) else { continue };
        if !spec_params.iter().any(|(_, t)| {
            matches!(kb.get_term(*t), Term::Var(Var::Global(v)) if *v == pvid)
        }) {
            continue;
        }
        // WI-477: read the receiver's inferred type as a carrier-agnostic `Value`
        // (NOT `.as_term()`) — an occurrence-primary `List[T = …]` is a `Value::Node`
        // whose `T`/`E` bindings live in the node; `.as_term()` would drop the carrier
        // and leak `Eff unconstrained`. The bindings are read below through the
        // carrier-agnostic `parameterized_short_bindings`. Mirrors the self-receiver
        // twin `bind_spec_params_from_carrier` (WI-470 d42682c).
        let recv_ty = pos_results
            .get(i)
            .and_then(|r| r.as_ref().ok())
            .map(|r| r.ty.clone())
            .or_else(|| {
                named_args
                    .iter()
                    .position(|(n, _)| n == pname)
                    .and_then(|j| named_results.get(j))
                    .and_then(|r| r.as_ref().ok())
                    .map(|r| r.ty.clone())
            });
        let Some(recv_ty) = recv_ty else { continue };
        let Some(carrier_sym) = sort_functor_of_view(kb, &recv_ty) else { continue };
        let Some(view) = provision_binds_param_to_carrier(kb, spec_sort, pvid, carrier_sym)
        else {
            continue;
        };
        return Some((spec_sort, carrier_sym, recv_ty, view));
    }
    None
}

/// WI-424 — ground a spec's sort params from the carrier's provision for a
/// CARRIER-PARAM receiver call (`find(xs, pred)` on a `List[Int64]` via
/// `provides Iterable[C = List[T], Element = T, E = {}]`): a provision binding
/// that is a carrier-param REF reads the receiver's own type-arg
/// (`Element ↦ T ↦ Int64`); a GROUND binding (the written `{}` row) binds
/// verbatim. Unlike [`bind_spec_params_from_carrier`] part (a), a ground row
/// DOES bind onto the spec's own param var here: for the carrier-param shape
/// the spec's `E` IS the op's declared effect row (`find … effects E`), and
/// leaving it unbound is exactly the `?_` leak this closes. A non-ground
/// non-ref binding (the carrier application `C ↦ List[T]` itself, or a
/// compound still mentioning carrier params) is skipped — `C` binds from
/// ordinary argument unification.
fn bind_spec_params_from_carrier_param(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    spec_sort: Symbol,
    recv_ty: &Value,
    view_bindings: SmallVec<[(Symbol, TermId); 2]>,
) -> bool {
    let recv_bindings = parameterized_short_bindings(kb, recv_ty);
    let mut any = false;
    for (spec_param_sym, carrier_value) in view_bindings {
        let concrete: Option<TermId> = match typaram_ref_short_name(kb, carrier_value) {
            Some(carrier_short) => recv_bindings
                .iter()
                .find(|e| e.0 == carrier_short)
                .map(|e| e.1),
            None if type_value_is_ground(kb, carrier_value) => Some(carrier_value),
            None => None,
        };
        let Some(concrete) = concrete else { continue };
        if let Some(spec_vid) = type_param_vid_in_sort(kb, spec_sort, spec_param_sym) {
            if subst.resolve_as_value(spec_vid).is_none() && !occurs_in(kb, spec_vid, concrete) {
                subst.bind_term(spec_vid, concrete);
                any = true;
            }
        }
    }
    any
}

/// WI-383 B — the LATE, GROUND-valued companion to [`bind_spec_params_from_carrier_param`].
/// Binds a spec value-param that is STILL FREE after the argument loops to its GROUND
/// provider-fact value (`fact Box[T = IntCell, V = Int64]` ⟹ `Box.V := Int64`). This is the
/// entity-resource Modify tie: `ModifyRuntime.get(target: T) -> V` consumed on a resource
/// whose provider fact pins `V` to a concrete sort. `V` appears only in the RETURN, so no
/// argument ever threads it; left free, the value-untied return is filled from the caller's
/// `expected`, accepting ANY declared return (the soundness hole the Modify model names).
///
/// Why it is a SEPARATE late pass, not folded into the early
/// [`bind_spec_params_from_carrier_param`]:
///  - a leaf sort ref (`Int64`) is indistinguishable from a type-param ref by
///    [`typaram_ref_short_name`], so it takes the receiver-type-arg lookup path and misses
///    (a bare entity carrier has no type args) — never reaching that fn's ground arm;
///  - binding such a ground value EARLY (before the argument loops) pre-empts the WI-424/441
///    carrier threading — an Iterable's GROUND `Element` would bind before the predicate's
///    effect row threads, leaving the effect param unconstrained.
///
/// The STILL-FREE gate is the discriminator: a param an argument pinned (Iterable's
/// `Element` via the callback, the carrier param via the receiver arg) is bound by now and
/// skipped; only a never-threaded return-only value-param (`V`) is free. WI-391: the
/// provider binding is the canonical `Ref(S)` shape (a bare sort lowers to `Ref(S)` at the
/// producer, `sort_binding_to_value`), so the bound `Ref(Int64)` unifies with the declared
/// return's `Ref(Int64)` directly — no late leaf normalization.
fn bind_ground_value_params_from_provider(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    spec_sort: Symbol,
    view_bindings: &SmallVec<[(Symbol, TermId); 2]>,
) -> bool {
    let mut any = false;
    for (spec_param_sym, carrier_value) in view_bindings {
        // GROUND value only (a concrete sort `Int64`): a type-param ref (`V ↦ Cell.V`) is
        // threaded by the early `bind_spec_params_from_carrier_param`, and the carrier
        // application / a still-abstract binding is filled by argument unification.
        if !type_value_is_ground(kb, *carrier_value) {
            continue;
        }
        let Some(spec_vid) = type_param_vid_in_sort(kb, spec_sort, *spec_param_sym) else {
            continue;
        };
        // STILL-FREE gate (see the fn doc): only a never-threaded value-param is bound; a
        // param an argument already pinned (the carrier param, an Iterable `Element`) is
        // left untouched.
        if subst.resolve_as_value(spec_vid).is_some() {
            continue;
        }
        // WI-391: the producer emits the canonical `Ref(S)` binding shape (a bare sort is
        // `Ref(S)`, never the former nullary `Fn{S}` that extracted as `Error`), so the
        // carrier value binds directly — no late `Fn{S}→Ref(S)` normalization needed.
        let bound = *carrier_value;
        if !occurs_in(kb, spec_vid, bound) {
            subst.bind_term(spec_vid, bound);
            any = true;
        }
    }
    any
}

/// A `parameterized` type's bindings as `(carrier-param short name, value)` pairs
/// — the receiver-side reader for [`bind_spec_params_from_carrier`]. Reads via
/// [`extract_type`], re-keys by short name (the form `bind_spec_params_from_carrier`
/// matches against), and keeps only `Value::Term` values (a parameterized type's
/// bindings are ground terms).
fn parameterized_short_bindings(kb: &KnowledgeBase, ty: &impl TermView) -> Vec<(String, TermId)> {
    // WI-361: a parameterized type's bindings (`List[T = Int]` ⇒ `[(T, Int)]`), read
    // carrier-agnostically through `extract_type` (WI-470: the receiver type is now a
    // `Value::Node` for an occurrence-primary `List[T = …]`, but its binding `T = Int`
    // is CARRIED in the node — never erased; `extract_type` reads it the same as the
    // hash-consed `Fn{S, named}` twin, so the spec-param grounding stays sound).
    let TypeExtractor::Parameterized { bindings, .. } = extract_type(kb, ty) else {
        return Vec::new();
    };
    bindings
        .into_iter()
        .filter_map(|(param, value)| match value {
            // A concrete parameterized carrier's binding is a ground sort term
            // (`List[T = Int]` ⇒ `Int`) — thread it. WI-477: a non-`Term` (Node)
            // binding — a carrier parameterized by a poisoned/occurrence type — is
            // not the ground `TermId` the carrier-grounding consumers `bind_term`;
            // leaving it unthreaded surfaces a LOUD `unconstrained` downstream (cf.
            // the `type_value_is_ground` guard in `bind_spec_params_from_carrier`)
            // rather than a silently-wrong bind. Threading such a compound is WI-380
            // follow-up work.
            Value::Term(t) => Some((short_name_of(kb.resolve_sym(param)).to_string(), t)),
            _ => None,
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

/// WI-385: groundness of a substitution-RESOLVED type `Value` — the gate for
/// argument / field type validation. Only a fully-concrete declared type
/// checked against a fully-concrete actual type may fail; a type-parameter
/// position (`T`), an unresolved inference var (`?_` / `Value::Var`), or a
/// carrier whose groundness the term predicate can't read stays UNCHECKED.
/// This is what keeps the validation from false-positiving on the pervasive
/// polymorphic signatures (`add(a: T, b: T)`, `some(value: T)`, `cons(head: T,
/// …)`): those param/field types resolve to a sort-param or a still-free var,
/// whose conformance the spec-op dispatch / return-conformance path settles, not
/// this check. Conservative by design — a non-`Term` carrier returns `false`
/// (skip) rather than risk an unsound pass or a false reject.
fn resolved_type_is_ground(kb: &KnowledgeBase, v: &Value) -> bool {
    match v {
        Value::Term(t) => type_value_is_ground(kb, *t),
        // WI-470: an occurrence-primary type (the flipped arrow / row / parameterized
        // form) is ground exactly when its spine carries no free type-var / sort-param
        // / row-tail leaf — the same predicate `type_value_is_ground` applies to the
        // hash-consed twin, walked structurally so a flipped GROUND arrow reads as
        // ground (and is WI-385-checked) instead of being skipped as "non-Term".
        Value::Node(occ) => node_type_is_ground(kb, occ),
        _ => false,
    }
}

/// WI-470: groundness of a `Value::Node`-carried type, walking the occurrence
/// `Type`/`EffectExpression` spine directly (no interning / materialization, so it
/// stays on the immutable `&KnowledgeBase` `resolved_type_is_ground` runs on).
/// Carrier-symmetric with the hash-consed twin [`type_value_is_ground`]: a ground
/// `TypeChild` defers to it (which rejects `Var` / sort-param leaves — so a row's
/// open `tail` Var makes the row non-ground), a poisoned child recurses, and a
/// `denoted` is ground iff its carried value has no free logical var (the same
/// answer `type_value_is_ground(make_denoted(value))` gives). Nothing is skipped:
/// every form's true groundness is computed.
fn node_type_is_ground(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> bool {
    let child_ground = |c: &TypeChild| match c {
        TypeChild::Ground(t) => type_value_is_ground(kb, *t),
        TypeChild::Node(n) => node_type_is_ground(kb, n),
    };
    match &occ.kind {
        NodeKind::Type(tn) => match tn {
            // WI-470: a denoted (value-in-type) is ground for THIS gate iff its value
            // is CLOSED — see [`denoted_value_is_closed`]. A closed denoted
            // (`Vector[Int64, 3]`, `Modify[store]`) is conformance-checked; a var-bearing
            // (`Vector[Int64, ?n]`) or binder-relative (`Modify[c]`, `c` a callback param)
            // denoted is deferred to the validator that can decide it (unification /
            // the alignment-aware `validate_callback_effect_row`). Nothing is skipped.
            TypeNode::Denoted { value } => denoted_value_is_closed(kb, value),
            TypeNode::Parameterized { base, bindings } => {
                child_ground(base) && bindings.iter().all(|(_, c)| child_ground(c))
            }
            TypeNode::EffectsRows { effects_expr } => child_ground(effects_expr),
            TypeNode::Arrow { param, result, effects } => {
                child_ground(param) && child_ground(result) && child_ground(effects)
            }
            TypeNode::ExprCarried { value, member } => child_ground(value) && child_ground(member),
            TypeNode::NamedTuple { fields } => list_records_to_pairs(kb, fields, "name", "type")
                .iter()
                .all(|(_, t)| resolved_type_is_ground(kb, t)),
        },
        NodeKind::EffectExpr(en) => match en {
            EffectExprNode::Merge { left, right } => child_ground(left) && child_ground(right),
            EffectExprNode::Present { label } | EffectExprNode::Absent { label } => {
                child_ground(label)
            }
            // An open row carries a row-tail Var ⇒ not ground.
            EffectExprNode::Open { tail } => child_ground(tail),
            EffectExprNode::EmptyRow => true,
        },
        // Not a type occurrence (an Expr/Pattern/RuleHead node never stands in a
        // type slot here) — conservatively unground (skip), as before.
        _ => false,
    }
}

/// WI-470: is a `denoted`'s carried VALUE closed — i.e. decidable by the generic
/// closed-type conformance check? Closed iff the value occurrence has NO free
/// logical var and NO reference to a binder-local parameter (`SymbolKind::Param`).
/// The non-closed shapes each route to the validator that CAN decide them, so
/// nothing is skipped:
///   * a free `Var` (`Vector[Int64, ?n]`) → inference (`unify_types`), not this gate;
///   * a binder-local param ref (`Modify[c]`, `c` the callback's OWN param) → the
///     label is meaningful only up to BINDER ALIGNMENT, which the generic structural
///     comparison cannot perform — `validate_callback_effect_row` owns it (it builds
///     the actual↔declared place map and compares aligned), so the generic gate must
///     defer rather than reject the alpha-equivalent `Modify[c]` vs `Modify[a]`;
///   * a closed value (`Vector[Int64, 3]` literal, `Modify[store]` global resource)
///     → IS closed → ground → conformance-checked here.
/// (A `denoted` always poisons to `Value::Node`, so it reaches the gate only through
/// [`node_type_is_ground`], never the term-side `type_value_is_ground` — the
/// param-relative refinement lives on the one carrier it flows through.)
fn denoted_value_is_closed(kb: &KnowledgeBase, value: &Rc<NodeOccurrence>) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(value)];
    while let Some(occ) = stack.pop() {
        match occ.as_expr() {
            // Any logic var ⇒ not closed — matching the term-side `type_value_is_ground`,
            // which rejects every `Term::Var` (Global = inference, deferred to unify;
            // DeBruijn/Rigid are not concrete either).
            Some(Expr::Var(_)) => return false,
            // A value-PLACE reference (op/callback param, result, field, let-local) is
            // binder-relative — meaningful only up to BINDER ALIGNMENT, which the generic
            // structural compare cannot do — so it is NOT closed; the alignment-aware
            // `validate_callback_effect_row` owns it. `is_value_place` is the shared
            // set the loader's `symbol_is_value_place` uses (no drift — the CallbackParam
            // own-param case `Modify[a]` is the one this gate must defer).
            Some(Expr::Ref(s)) | Some(Expr::Ident(s))
                if kb.kind_of(*s).is_some_and(|k| k.is_value_place()) =>
            {
                return false;
            }
            // A bare local-binder read (`?x` — a let/lambda binder) is binder-relative too.
            Some(Expr::VarRef { .. }) => return false,
            // A literal / global ref (Sort/Entity/Operation) / compound value — recurse
            // children (a field-path receiver may still reach a value-place ref).
            Some(e) => for_each_child(e, |c| stack.push(Rc::clone(c))),
            // A denoted's value is always an `Expr` occurrence; a non-`Expr` here is a
            // construction bug — surface it (loud) and conservatively defer, rather than
            // silently judging it closed.
            None => {
                debug_assert!(false, "denoted value occurrence is not an Expr: {:?}", occ.kind);
                return false;
            }
        }
    }
    true
}

/// WI-385: is this resolved type the reflect `Term` sort (`anthill.reflect.Term`)?
/// The value↔Term boundary is a CONVERSION, not subtyping. Reflection
/// (value → Term) is TOTAL — every value has a Term representation
/// (`as_term[E](e) -> Term`, WI-406) — so ANY `actual` type conforms to a
/// declared `Term`. (Reification, Term → value, is PARTIAL and stays explicit
/// via the `term_as_entity` family, so the reverse is NOT accepted by the
/// validation.) `Term` is representation-specific, NOT a top type — keying the
/// type lattice on it would make it the universal default on every term (see the
/// note in `stdlib/anthill/prelude/sort.anthill`) — so this acceptance lives in
/// the WI-385 validation, never in `types_compatible` / the subtype relation.
fn is_reflect_term_type<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    // `type_head` reads only the head (no binding materialization), enough here.
    matches!(type_head(kb, ty),
        TypeHead::SortRef(s) if kb.qualified_name_of(s) == "anthill.reflect.Term")
}

/// WI-385: is this resolved type an `anthill.prelude.Option` — bare `Option` or
/// applied `Option[T = …]`? The element peel for the WI-408 some-coercion
/// (`pub(crate)`: the loader's fact-field wrap tests field types with it).
pub(crate) fn is_option_type<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    match type_head(kb, ty) {
        TypeHead::Parameterized { base } => kb.qualified_name_of(base) == "anthill.prelude.Option",
        TypeHead::SortRef(s) => kb.qualified_name_of(s) == "anthill.prelude.Option",
        _ => false,
    }
}

/// WI-385: the base/head sort symbol of a ground type — `S` for a bare `S`, the
/// base `S` for an application `S[…]`; `None` for a structural form (arrow,
/// named_tuple, …). Used to test provider admissibility against a bare spec.
fn type_base_sort_view<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<Symbol> {
    match type_head(kb, ty) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => Some(s),
        _ => None,
    }
}

/// WI-408: outcome of validating one supplied argument / field value against
/// its declared type.
enum ArgValidation {
    /// Conforms as-is, or unchecked (a non-ground / polymorphic position is
    /// left for spec-op dispatch / return conformance).
    Ok,
    /// Bare `T` supplied for a declared `Option[T]`: accepted by INSERTING a
    /// `some(...)` coercion around the argument occurrence (the WI-408
    /// some-insertion pass — first slice of the implicit-conversion
    /// framework). The payload is the resolved declared `Option` type, which
    /// the caller stamps onto the synthesized wrapper node.
    WrapSome { declared: Value },
    /// Concrete, ground, and non-conforming.
    Fail(TypeError),
}

/// WI-385: subtype-check one supplied value's type (`actual`) against a declared
/// parameter / field type (`declared`), GATED on groundness. Both sides are
/// first walked through the inference `subst` (so a param a prior argument
/// already pinned reads as its concrete type); the check fires ONLY when both
/// resolve to a fully-concrete type (`resolved_type_is_ground`) — a polymorphic
/// or still-free position is left for spec-op dispatch / return conformance.
/// `Fail` carries the RESOLVED forms (a clean "expected Int, got String",
/// never a raw `?_`) when the concrete actual does not conform. The shared
/// core of the operation-argument (`check_apply_iter`) and entity-field
/// (`check_constructor_iter`) validation.
///
/// Two boundary CONVERSIONS are accepted rather than flagged:
///  - **value→Term reflection** (`is_reflect_term_type`): total, both positions.
///  - **some-coercion** (WI-408, both positions): a bare `T` against a declared
///    `Option[T]` validates `actual` against the element `T` and, on success,
///    returns `WrapSome` — the caller wraps the argument occurrence in a
///    synthesized `some(...)`, so the value is PROPERLY Option-typed at
///    runtime (replaces WI-385's lenient-accept interim, under which the
///    value stayed bare in memory). A bare value that would need a NESTED
///    insertion (`Option[Option[T]]` supplied a bare `T`) is rejected loudly —
///    one wrap is inserted, never a silent double-wrap.
fn validate_arg_against_param(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &Value,
    declared: &Value,
    span: Option<Span>,
    context: TypeErrorContext,
) -> ArgValidation {
    let actual_g = walk_view(kb, subst, actual);
    let declared_g = walk_view(kb, subst, declared);
    if !resolved_type_is_ground(kb, &actual_g) || !resolved_type_is_ground(kb, &declared_g) {
        // WI-469: a denoted-bearing arrow callback param whose EFFECTS row is
        // non-ground (it carries the op's `EffP` type-param and a binder-relative
        // `-Modify[x]`) makes the WHOLE arrow non-ground, so the gate above would
        // skip it — silently accepting a callback whose CONCRETE param/result
        // element type is wrong (a `(String) -> Bool` where `(Int64) -> Bool` is
        // declared). When the arrow's param/result ARE concrete, validate them
        // here (contravariant param, covariant result); the effects-row alignment
        // stays deferred to dispatch / `validate_callback_effect_row`. A genuinely
        // polymorphic param/result (a free type-var) stays non-ground and is left
        // for dispatch — distinguishing polymorphic-non-ground from denoted-but-
        // concrete, the WI-385 groundness discipline.
        if let Some(err) =
            validate_arrow_param_result(kb, subst, &actual_g, &declared_g, span, &context)
        {
            return ArgValidation::Fail(err);
        }
        return ArgValidation::Ok;
    }
    // value→Term reflection: total conversion, accept any actual vs declared Term.
    if is_reflect_term_type(kb, &declared_g) {
        return ArgValidation::Ok;
    }
    if types_compatible(kb, subst, &actual_g, &declared_g) {
        return ArgValidation::Ok;
    }
    // WI-408 some-coercion: a non-conforming value against `Option[T]`
    // re-checks against the element `T` (so `description: "…"` peels to a
    // Term and the reflection above accepts it) and reports the wrap. Runs
    // AFTER `types_compatible` so an already-conforming Option is never
    // re-wrapped; an `Option[T]` actual against `Option[Option[T]]` declared
    // is a valid PAYLOAD and takes the one outer wrap.
    if is_option_type(kb, &declared_g) {
        match extract_type_param(kb, &declared_g, "T") {
            Some(inner) => {
                return match validate_arg_against_param(
                    kb, subst, &actual_g, &inner, span, context.clone(),
                ) {
                    ArgValidation::Ok => ArgValidation::WrapSome { declared: declared_g },
                    // WrapSome: the value is bare at BOTH depths of a nested
                    // Option — a single wrap cannot repair it; demand the
                    // explicit inner `some(...)` rather than silently
                    // guessing the nesting depth. Fail: report the OUTER
                    // expected/actual pair (clearer than the peeled element
                    // mismatch).
                    ArgValidation::WrapSome { .. } | ArgValidation::Fail(_) => {
                        ArgValidation::Fail(TypeError::TypeMismatch {
                            span,
                            context,
                            expected: declared_g,
                            actual: actual_g,
                        })
                    }
                };
            }
            // A bare `Option` (unconstrained element) has no element to
            // re-check — any value is its `some` payload.
            None => return ArgValidation::WrapSome { declared: declared_g },
        }
    }
    // WI-385: a concrete carrier conforms to a BARE spec it PROVIDES — e.g.
    // `List[Int]` passed where `Stream` is declared (`List provides Stream`).
    // `types_compatible` confines provider-admissibility to its bare↔bare arm (so
    // it never drops a PARAMETERIZED spec's bindings), so a parameterized-carrier-
    // vs-bare-spec pairing reaches here unaccepted. The declared spec here is bare
    // (no bindings to drop), so an admissible provider is sound to accept —
    // restoring the pre-WI-385 behavior (no arg/field check rejected it) for the
    // concrete-provider→bare-spec case.
    if let (Some(actual_base), Some(declared_sort)) =
        (type_base_sort_view(kb, &actual_g), extract_sort_ref_sym(kb, &declared_g))
    {
        if sort_provides_admissibly(kb, actual_base, declared_sort) {
            return ArgValidation::Ok;
        }
    }
    ArgValidation::Fail(TypeError::TypeMismatch {
        span,
        context,
        expected: declared_g,
        actual: actual_g,
    })
}

/// WI-469: validate a callback argument's CONCRETE arrow param/result element
/// types against the declared arrow param, for the case the
/// [`validate_arg_against_param`] groundness gate skips: a denoted-bearing arrow
/// whose EFFECTS row is non-ground (an `EffP` type-param + a binder-relative
/// `-Modify[x]`) but whose PARAM and RESULT types are concrete. Returns
/// `Some(error)` when a concrete component is decisively incompatible; `None`
/// when neither side is an arrow, or a relevant component is non-ground (left for
/// dispatch / unification — a genuinely polymorphic callback must NOT be rejected
/// here).
///
/// Variance follows function subtyping (the same relation [`arrow_compatible_view`]
/// uses, but component-wise so the non-ground effects row is left untouched):
///   * param is CONTRAVARIANT — the callback must accept the value the declared
///     arrow is called with (`declared.param <: actual.param`);
///   * result is COVARIANT — the callback's result must satisfy the declared
///     result (`actual.result <: declared.result`).
/// Each component check fires only when BOTH sides of it are ground, so a
/// polymorphic actual / declared component is conservatively skipped.
fn validate_arrow_param_result(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &Value,
    declared: &Value,
    span: Option<Span>,
    context: &TypeErrorContext,
) -> Option<TypeError> {
    let (Some((Some(d_param), d_result, _)), Some((Some(a_param), a_result, _))) =
        (arrow_parts(kb, declared), arrow_parts(kb, actual))
    else {
        // Not both arrows (or a param-less form) — nothing this helper can decide.
        return None;
    };
    let mismatch = || TypeError::TypeMismatch {
        span,
        context: context.clone(),
        expected: declared.clone(),
        actual: actual.clone(),
    };
    // Contravariant param: `declared.param <: actual.param`.
    if resolved_type_is_ground(kb, &d_param)
        && resolved_type_is_ground(kb, &a_param)
        && !types_compatible(kb, subst, &d_param, &a_param)
    {
        return Some(mismatch());
    }
    // Covariant result: `actual.result <: declared.result`.
    if resolved_type_is_ground(kb, &d_result)
        && resolved_type_is_ground(kb, &a_result)
        && !types_compatible(kb, subst, &a_result, &d_result)
    {
        return Some(mismatch());
    }
    None
}

/// WI-408: the synthesized `some(value)` constructor occurrence around a
/// coerced argument / field node. `declared` (the resolved `Option[T]`) is
/// stamped as the wrapper's inferred type here — the `Stamp` frame only
/// stamps the enclosing node's own result, never an inserted child.
fn synthesize_some_wrap(
    kb: &mut KnowledgeBase,
    child: &Rc<NodeOccurrence>,
    declared: &Value,
) -> Rc<NodeOccurrence> {
    let some_sym = kb.resolve_symbol("anthill.prelude.Option.some");
    let value_sym = kb.intern("value");
    let pass = super::simp_rewrite::simp_pass(kb);
    // Named form `some(value: child)` — the canonical `some` shape (the
    // loader canonicalizes source-written positional `some(x)` to it too).
    let node = NodeOccurrence::synthesized_expr(
        Expr::Constructor {
            name: some_sym,
            pos_args: Vec::new(),
            named_args: vec![(value_sym, Rc::clone(child))],
        },
        Rc::clone(child),
        pass,
        child.owner,
    );
    node.set_inferred_type(declared.clone());
    node
}

/// WI-408: rebuild `occ` with `some(...)` wrappers around the flagged
/// children. `wraps` carries `(child-index, declared-Option-type)` pairs —
/// indices in reassembly order (positional args, then named args); every
/// other slot takes the child's TYPED result node (itself possibly
/// rewritten). The rebuilt node starts with fresh annotation cells, so the
/// caller must rebuild BEFORE writing `classification` /
/// `resolved_type_args` onto the apply/constructor occurrence.
fn wrap_some_children(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    wraps: &[(usize, Value)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> Rc<NodeOccurrence> {
    let mut children: Vec<Rc<NodeOccurrence>> = pos_results
        .iter()
        .chain(named_results.iter())
        .map(|r| Rc::clone(&r.as_ref().expect("wrap_some_children: Ok child").node))
        .collect();
    for (idx, declared) in wraps {
        children[*idx] = synthesize_some_wrap(kb, &children[*idx], declared);
    }
    super::simp_rewrite::reassemble(occ, &children)
}

/// WI-441: explode a ROW-shaped effect value into its component atoms —
/// the present labels plus the row-tail var (as a bare `Value::Term` Var
/// atom). Returns `None` when `effect` is not row-shaped (an ordinary
/// label like `Modify[c]` / `Error` / a bare row var — those compare
/// atom-to-atom as before). Row-shaped = the `effects_rows` wrapper OR a
/// bare `EffectExpression` node (`merge`/`present`/`absent`/`open`/
/// `empty_row`, matched by QUALIFIED functor so a user sort named `merge`
/// is not misclassified) — a bound row var walks to the bare form.
/// Absent atoms are DROPPED: they are constraints on the row, not effects
/// the body incurs.
fn explode_incurred_effect_row(kb: &mut KnowledgeBase, effect: &Value) -> Option<Vec<Value>> {
    let is_rows_wrapper = matches!(type_dispatch_name_view(kb, effect), Some("effects_rows"));
    let head_is_row_expr = match effect.head(kb) {
        ViewHead::Functor { functor: Some(sym), .. } => {
            let qn = kb.qualified_name_of(sym);
            matches!(
                qn.strip_prefix("anthill.prelude.EffectExpression."),
                Some("merge" | "present" | "absent" | "open" | "empty_row")
            )
        }
        _ => false,
    };
    if !is_rows_wrapper && !head_is_row_expr {
        return None;
    }
    let row: Value = if is_rows_wrapper {
        effect.clone()
    } else {
        // Wrap the bare EffectExpression so `decompose_effect_row` sees the
        // canonical `effects_rows(…)` shape.
        match effect {
            Value::Term(t) => Value::Term(kb.make_effects_rows_type(*t)),
            Value::Node(occ) => Value::Node(kb.make_effects_rows_occ(
                TypeChild::Node(Rc::clone(occ)),
                occ.span,
                occ.owner,
            )),
            _ => return None,
        }
    };
    let subst = Substitution::new();
    let (present, tails, _absent) = decompose_effect_row(kb, &subst, &row)?;
    let mut atoms = present;
    for t in tails {
        atoms.push(Value::Term(t));
    }
    Some(atoms)
}

/// WI-440: two effect labels match modulo POSITIONAL binder alignment.
/// Direct structural equality first ([`resolved_labels_equal`]); otherwise an
/// applied-effect pair (`Modify[c]` vs `Modify[x]`) matches when the base
/// effect sorts are EQUAL and the resources are corresponding places under
/// `place_map` (actual-side place → declared-side place) — the positional
/// binder correspondence between an eta'd op's own params and the declared
/// callback's registered `CallbackParam` places.
fn labels_match_aligned(
    kb: &KnowledgeBase,
    subst: &Substitution,
    place_map: &HashMap<Symbol, Symbol>,
    a: &Value,
    e: &Value,
) -> bool {
    if resolved_labels_equal(kb, subst, a, e) {
        return true;
    }
    let (
        TypeExtractor::Parameterized { base: a_base, .. },
        TypeExtractor::Parameterized { base: e_base, .. },
    ) = (extract_type(kb, a), extract_type(kb, e))
    else {
        return false;
    };
    if a_base != e_base {
        return false;
    }
    match (extract_effect_resource_sym(kb, a), extract_effect_resource_sym(kb, e)) {
        (Some(ar), Some(er)) => ar == er || place_map.get(&ar) == Some(&er),
        _ => false,
    }
}

/// WI-440 — the `-Modify[binder]` CHECKING direction: validate a callback
/// argument's effect row against the declared callback parameter's row,
/// aligning the two binder spaces positionally. The declared row's labels
/// name the callback's registered `CallbackParam` places (`<op>.f.x`, the
/// WI-341 binder→place resolution); an eta'd operation argument's row names
/// that op's OWN param places (`<pred>.c`) — param i of one corresponds to
/// param i of the other (`arg_places` order on both symbols).
///
/// For each PRESENT label of the actual row:
///   * covered by a declared PRESENT label (mod alignment) → ok;
///   * matching a declared ABSENT label (mod alignment) → REJECT — the
///     lacks-constraint violation (`Modify[c]` against `-Modify[x]`);
///   * otherwise: declared row OPEN → absorbed; CLOSED → REJECT — an effect
///     the declared row does not admit, which would escape the WI-352/353
///     boundary propagation (that derives from the DECLARED callback row,
///     not from the argument actually passed).
///
/// Conservative skips (return `None`, no check): a non-arrow/`Function`
/// declared or actual type, a missing effects child, a non-eta argument
/// (a lambda synthesizes its row against the declared hint elsewhere), an
/// actual row that is OPEN or carries its own absents, or a row that fails
/// to decompose. VALIDATION-only: `subst` is read (label walking / bound
/// row-tail resolution) and never extended — inference stays with the
/// `unify_types` pass that precedes this check.
fn validate_callback_effect_row(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    fn_sym: Symbol,
    param_sym: Symbol,
    declared: &Value,
    arg_occ: &Rc<NodeOccurrence>,
    actual: &Value,
    span: Option<Span>,
) -> Option<TypeError> {
    let arg_op_sym = extract_var_ref_sym_node(arg_occ)?;
    // Cheap head gate before `arrow_parts` (which interns its child keys on
    // every call): most var-ref args land in non-callable param slots.
    let head_is_callable = match type_head(kb, declared) {
        TypeHead::Arrow => true,
        TypeHead::Parameterized { base } => {
            kb.qualified_name_of(base) == "anthill.prelude.Function"
        }
        _ => false,
    };
    if !head_is_callable {
        return None;
    }
    let (_, _, act_eff) = arrow_parts(kb, actual)?;
    let act_eff = act_eff?;
    let act_row = canonical_effects_row(kb, &act_eff);
    let (a_present, a_tails, a_absent) = decompose_effect_row(kb, subst, &act_row)?;
    if a_present.is_empty() || !a_tails.is_empty() || !a_absent.is_empty() {
        // A pure actual row conforms to any declared row (subset semantics);
        // an open / absent-carrying actual is left to the unify path (v1).
        return None;
    }
    let (_, _, decl_eff) = arrow_parts(kb, declared)?;
    let decl_eff = decl_eff?;
    let decl_row = canonical_effects_row(kb, &decl_eff);
    let (e_present, e_tails, e_absent) = decompose_effect_row(kb, subst, &decl_row)?;
    let actual_places = kb.symbols.arg_places(arg_op_sym);
    let declared_places = kb.symbols.arg_places(param_sym);
    // Positional alignment is meaningful only for EQUAL arities — a mismatch
    // (which the generic arg validation rejects on the param type) must not
    // silently truncate the map and mis-align the surviving places.
    if actual_places.len() != declared_places.len() {
        return None;
    }
    let place_map: HashMap<Symbol, Symbol> = actual_places
        .iter()
        .copied()
        .zip(declared_places.iter().copied())
        .collect();
    for la in &a_present {
        if e_present.iter().any(|le| labels_match_aligned(kb, subst, &place_map, la, le)) {
            continue;
        }
        if let Some(viol) =
            e_absent.iter().find(|le| labels_match_aligned(kb, subst, &place_map, la, le))
        {
            return Some(TypeError::Other {
                span,
                context: TypeErrorContext::OperationArgument { op_name: fn_sym, param: param_sym },
                expected: format!(
                    "callback for parameter `{}` of `{}` to lack `{}` (its `-…` lacks-constraint)",
                    kb.resolve_sym(param_sym),
                    kb.qualified_name_of(fn_sym),
                    type_display_name_value(kb, viol),
                ),
                actual: format!(
                    "operation `{}` declares `{}` on the corresponding parameter",
                    kb.qualified_name_of(arg_op_sym),
                    type_display_name_value(kb, la),
                ),
            });
        }
        if e_tails.is_empty() {
            return Some(TypeError::Other {
                span,
                context: TypeErrorContext::OperationArgument { op_name: fn_sym, param: param_sym },
                expected: format!(
                    "callback effects admitted by parameter `{}` of `{}` (a closed row)",
                    kb.resolve_sym(param_sym),
                    kb.qualified_name_of(fn_sym),
                ),
                actual: format!(
                    "operation `{}` declares `{}`, which the closed row does not admit",
                    kb.qualified_name_of(arg_op_sym),
                    type_display_name_value(kb, la),
                ),
            });
        }
    }
    None
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
    expected: Option<Value>,
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

    // WI-462: thread the EXPECTED tuple component types into the elements. A component's
    // inferred type can be a free var (`cons(h, t)` over a bare `xs : List` binds `h` to a
    // fresh `?_`); the declared return `(xs.T, …)` carries the real type, but the later
    // conformance check (`types_compatible`) does NOT bind a var — it only subtype-checks,
    // and a raw `Var::Global` is not a wildcard there. So unify each element's type against
    // its expected component (matched by `_1`/`_2`/name), binding the free var (`h ⟹ xs.T`),
    // then walk it into the built tuple type. (A `pair(h, t)` constructor threads this way
    // for free — its build seeds the expected; a tuple literal has no constructor to do so.)
    // No / non-tuple expected leaves the inferred types unchanged.
    let exp_fields: Vec<(Symbol, Value)> = match &expected {
        Some(e) if matches!(extract_type(kb, e), TypeExtractor::NamedTuple(_)) => {
            named_tuple_fields(kb, e)
        }
        _ => Vec::new(),
    };
    let mut tsubst = Substitution::new();
    let mut effects: Vec<Value> = Vec::new();
    // WI-342: carrier-agnostic field types (carry a `Value::Node` field).
    let mut tuple_fields: Vec<(Symbol, Value)> = Vec::new();
    for (label, r) in labeled {
        let ty = thread_expected_tuple_field(kb, &mut tsubst, &exp_fields, label, &r.ty);
        tuple_fields.push((label, ty));
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
            kb, env, named_args, pos_results, named_results, expected, occ,
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

    // WI-384: fields unify FIRST so each argument pins its param, THEN the caller
    // `expected` fills only the still-free params (the args-before-expected order of
    // `check_apply_iter`, WI-379). A field that CONTRADICTS `expected` then wins in the
    // built type and the use-site return-conformance check rejects it
    // (`make() -> Option[String] = some(42)` builds `Option[Int]`, rejected) instead of
    // `expected` masking the contradiction. The expected-seed is moved BELOW the field
    // loops (but kept ABOVE the empty-bindings early-return, so 0-arg constructors
    // `nil()` / `Map.empty()` still pick up the hint). Sound only because the build
    // (below) is now robust to a param the fields left unbound — it includes it as a
    // fresh `?_` rather than DROPPING it (which had made `pair(h, t)` build
    // `Pair[B=List]`, losing `A`).

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

    // WI-385: VALIDATE each supplied field value against its declared field type
    // — the FIELD peer of the operation-argument check in `check_apply_iter`. The
    // field unify loops above pin type-params for INFERENCE and DISCARD their
    // boolean, so before this a `fact Counter(n: "hello")` with `entity
    // Counter(n: Int)` loaded clean (a String in an Int field). `validate_arg_-
    // against_param` subtype-checks each supplied field value against its declared
    // type, GATED on groundness (a polymorphic field `some(value: T)` /
    // `pair(fst: A, …)` stays unchecked — the return-conformance path settles it),
    // emitting a loud `TypeMismatch` under the existing `EntityField` context. Run
    // BEFORE the expected-seed and bail before the type is built for a constructor
    // we've proven ill-formed. WI-408: a bare `T` in an `Option[T]` field is
    // accepted by RECORDING a some-coercion, materialized below.
    let mut field_type_errors: Vec<TypeError> = Vec::new();
    let mut some_wraps: Vec<(usize, Value)> = Vec::new();
    for (field_sym, declared_type) in &field_types {
        if let Some((idx, _)) = named_args.iter().enumerate().find(|(_, (s, _))| s == field_sym) {
            if let Ok(ref r) = named_results[idx] {
                match validate_arg_against_param(
                    kb, &mut subst, &r.ty, declared_type, span,
                    TypeErrorContext::EntityField { entity: ctor_sym, field: *field_sym },
                ) {
                    ArgValidation::Ok => {}
                    ArgValidation::WrapSome { declared } => {
                        some_wraps.push((pos_results.len() + idx, declared));
                    }
                    ArgValidation::Fail(err) => field_type_errors.push(err),
                }
            }
        }
    }
    for (i, r_opt) in pos_results.iter().enumerate() {
        if let Some((field_sym, declared_type)) = field_types.get(i) {
            if let Ok(r) = r_opt {
                match validate_arg_against_param(
                    kb, &mut subst, &r.ty, declared_type, span,
                    TypeErrorContext::EntityField { entity: ctor_sym, field: *field_sym },
                ) {
                    ArgValidation::Ok => {}
                    ArgValidation::WrapSome { declared } => some_wraps.push((i, declared)),
                    ArgValidation::Fail(err) => field_type_errors.push(err),
                }
            }
        }
    }
    if !field_type_errors.is_empty() {
        return Err(aggregate_errors(field_type_errors));
    }
    // WI-374 (user-decided 2026-06-12): ENFORCE the §3 parametricity tie for
    // CONSTRUCTOR fields — the field loops bind the parent sort's canonical
    // param vars through `T`-typed and bare-self-sort fields, and a
    // conflicting rebind was recorded but never consulted: `cons(head: 1,
    // tail: strList)` built `List[T = Int64]` with a String inside. Same
    // shared gate as the op-call check (per-var details, refinement
    // re-unified, parent's own params only); no rigid exemption — a rigid
    // reaches this subst only through a real field argument, where the
    // conflict is a genuine parametricity violation. Runs BEFORE the
    // expected-seed below, whose contradicting-hint unify is a deliberate
    // ignored no-op.
    if let Some(parent_tid) = parent_sort {
        if let Term::Fn { functor, .. } = kb.get_term(parent_tid) {
            let parent_sym = *functor;
            enforce_member_tie(kb, &subst, parent_sym, ctor_sym, span, &[])?;
        }
    }
    // WI-408: materialize the recorded some-coercions (see check_apply_iter) —
    // every return below reads the (possibly rebuilt) `occ`.
    let rebuilt_occ;
    let occ = if some_wraps.is_empty() {
        occ
    } else {
        rebuilt_occ = wrap_some_children(kb, occ, &some_wraps, pos_results, named_results);
        &rebuilt_occ
    };

    // WI-384 / WI-270: now seed the caller `expected` — it fills params the fields left
    // free (so a 0-arg `nil()` with a `List[Int]` hint still gets `T = Int`), and a
    // contradicting hint does NOT overwrite a field-pinned param: that param already
    // holds a concrete type, so unifying it against the hint just fails and is ignored,
    // leaving the field type in the build (→ use-site rejection of the contradiction).
    if let Some(exp) = expected {
        unify_types(kb, &mut subst, &TermIdView(parent_type), &exp);
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
        // Collect alias info: (param_short_name, bound_type). `None` = the param's Var
        // was left UNBOUND by the field + expected unification — WI-384 keeps it
        // (freshened below) rather than dropping it.
        let mut alias_info: Vec<(String, Option<TermId>)> = Vec::new();
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
                        // The next char after the parent name MUST be `.` — without this
                        // a sibling sort whose qualified name merely starts with the
                        // parent's (`Modify` ⊂ `ModifyRuntime`, `Effect` ⊂ `Effects`)
                        // matches, slicing a GARBAGE param name. Harmless when the param
                        // is then DROPPED, but WI-384 KEEPS an unbound param as `?_`, so
                        // an unchecked prefix would inject a spurious `garbage = ?_`
                        // binding into the built type.
                        if alias_name.starts_with(&parent_name)
                            && alias_name.as_bytes().get(parent_name.len()) == Some(&b'.')
                        {
                            let param_short = alias_name[parent_name.len() + 1..].to_string();
                            if let Term::Var(Var::Global(vid)) = kb.get_term(target_tid) {
                                match subst.resolve_as_value(*vid) {
                                    Some(Value::Term(bound_type)) => {
                                        alias_info.push((param_short, Some(*bound_type)))
                                    }
                                    // denoted Node alias binding: `alias_info` is
                                    // TermId-keyed — WI-348 Phase C, asserted unreachable.
                                    // NOT pushed as a `?_` wildcard: that would lose the
                                    // concrete denoted value-in-type (e.g. the `3` in
                                    // `Vector[Int, 3]`) and over-accept, so this path
                                    // stays a (release-only, unreached) drop until Phase C.
                                    Some(other) => debug_assert!(
                                        false,
                                        "WI-348: denoted {} alias binding — carrier-agnostic alias_info is Phase C",
                                        other.type_name(),
                                    ),
                                    // WI-384: a param the fields + expected left UNBOUND
                                    // is present-but-unconstrained — record it (a fresh
                                    // `?_` is minted below) rather than DROPPING it, which
                                    // shrank the built type's arity (`pair(h, t)` →
                                    // `Pair[B=List]`, losing `A`).
                                    None => alias_info.push((param_short, None)),
                                }
                            }
                        }
                    }
                }
            }
        }
        for (param_short, bound_opt) in alias_info {
            let param_sym = kb.intern(&param_short);
            // WI-384: an unbound param becomes a `type_var` WILDCARD so the built type
            // keeps the sort's full param arity while staying compatible with whatever
            // the use-site declares — exactly the leniency the old DROP relied on
            // (width subtyping), but with the param PRESENT so the arity matches. It
            // must be a `type_var` (not a bare logic `Var`), since only `type_var` is
            // the inference wildcard the unify/subtype dispatch treats as compatible
            // with anything; a bare `Var` reads as an incompatible head.
            let bound_type = match bound_opt {
                Some(t) => t,
                None => {
                    let name = kb.intern("?_");
                    kb.make_type_var(name)
                }
            };
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
                Some((mut present, tails, _absent)) => {
                    for tail_tid in tails {
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

// ── WI-376: expression-carried projection elimination ──────────

/// WI-376: does a type [`Value`] contain an expression-carried projection
/// (`ExprCarried`) anywhere in its structure? Carrier-agnostic (reads via
/// [`extract_type`], so a `Value::Node` parameterized type is walked too). Used both
/// to GATE the per-call elimination (skip the work for the >99% of signatures with no
/// projection) and to DETECT a projection nested inside a denoted-bearing `Value::Node`
/// — which the Node-carrier rewrite does not yet handle, so it is a loud error rather
/// than a silent leak.
fn value_contains_projection(kb: &KnowledgeBase, ty: &Value) -> bool {
    match extract_type(kb, ty) {
        TypeExtractor::ExprCarried { .. } | TypeExtractor::RigidTypeProjection { .. } => true,
        TypeExtractor::Parameterized { bindings, .. } => {
            bindings.iter().any(|(_, v)| value_contains_projection(kb, v))
        }
        TypeExtractor::Arrow { param, result, effects } => {
            value_contains_projection(kb, &param)
                || value_contains_projection(kb, &result)
                || value_contains_projection(kb, &effects)
        }
        TypeExtractor::NamedTuple(fields) => {
            fields.iter().any(|(_, v)| value_contains_projection(kb, v))
        }
        TypeExtractor::EffectsRows(e) => value_contains_projection(kb, &e),
        TypeExtractor::Denoted(_)
        | TypeExtractor::SortRef(_)
        | TypeExtractor::TypeVar(_)
        | TypeExtractor::Nothing
        | TypeExtractor::Error => false,
    }
}

/// WI-398: the head parameter symbol of an expression-carried projection's RECEIVER
/// path. A single value reference `Ref(s)` is `s`; a field-access chain `s.f.g` bottoms
/// out in `Ref(s)`, so the head is `s`. Any other shape (not a value-reference path) is
/// `None`. Mirrors the descent in [`resolve_receiver_path_type`], returning the path's
/// bottom symbol rather than its type.
fn receiver_path_head_sym(kb: &KnowledgeBase, receiver: &Value) -> Option<Symbol> {
    if let Some(head) = extract_sort_ref_sym(kb, receiver) {
        return Some(head);
    }
    if let Value::Node(occ) = receiver {
        if let Some(Expr::DotApply { receiver: base, pos_args, named_args, .. }) = occ.as_expr() {
            if pos_args.is_empty() && named_args.is_empty() {
                return receiver_path_head_sym(kb, &Value::Node(std::rc::Rc::clone(base)));
            }
        }
    }
    None
}

/// WI-400 increment C: the full receiver-path SEGMENTS of a projection receiver value, in
/// outermost-head-first order — `Ref(s)` ⟹ `[s]`, `s.provider` (a `DotApply` chain) ⟹
/// `[s, provider]`. The path twin of [`receiver_path_head_sym`] (which returns only the
/// head). `None` for a non-value-reference receiver. Used by the eager-let-alias
/// canonicalization to rewrite a receiver whose head is aliased.
fn receiver_path_segs(kb: &KnowledgeBase, receiver: &Value) -> Option<Vec<Symbol>> {
    if let Some(head) = extract_sort_ref_sym(kb, receiver) {
        return Some(vec![head]);
    }
    if let Value::Node(occ) = receiver {
        if let Some(Expr::DotApply { receiver: base, name, pos_args, named_args }) = occ.as_expr() {
            if pos_args.is_empty() && named_args.is_empty() {
                let mut segs =
                    receiver_path_segs(kb, &Value::Node(std::rc::Rc::clone(base)))?;
                segs.push(*name);
                return Some(segs);
            }
        }
    }
    None
}

/// WI-400 increment C: the stable receiver PATH a `let`-bound value occurrence denotes,
/// if any. A value reference (`let y = z`) ⟹ `[z]`; a field-access chain
/// (`let y = s.provider`) ⟹ `[s, provider]`. Returns `None` for anything NOT a stable
/// path — a call (`let y = f()`), a literal, a constructor — so an unstable binding mints
/// its OWN neutral receiver rather than aliasing (the §4.1 stability rule). The occurrence
/// twin of [`receiver_path_segs`] (which reads a type-level receiver value).
fn stable_receiver_path(occ: &Rc<NodeOccurrence>) -> Option<Vec<Symbol>> {
    match occ.as_expr()? {
        // A value reference is an `Expr::VarRef` (an unqualified let/lambda/param binder
        // read) or a `Ref`/`Ident` (a resolved reference); all denote a stable name.
        Expr::VarRef { name } => Some(vec![*name]),
        Expr::Ref(s) | Expr::Ident(s) => Some(vec![*s]),
        Expr::DotApply { receiver, name, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            let mut segs = stable_receiver_path(receiver)?;
            segs.push(*name);
            Some(segs)
        }
        _ => None,
    }
}

/// WI-400 increment C (eager let-alias): rewrite a projection type's receiver to its
/// CANONICAL path BEFORE elimination, when its head is a let-aliased variable — so `y.M`
/// (`let y = z`) carries the same receiver as `z.M` and the ζ arm equates them
/// (`let y = z ⟹ y.M ≡ z.M`, the Scala divergence). A no-op when `aliases` is empty (the
/// common case) or the receiver head is not aliased. Handles the TOP-LEVEL projection
/// (the let-annotation shape `let k: y.M`); a projection NESTED inside a parameterized /
/// denoted type is left unchanged — the same carrier-promotion boundary `eliminate_type_-
/// projections` already documents as a follow-on.
fn canonicalize_projection_receivers(
    kb: &mut KnowledgeBase,
    aliases: &HashMap<Symbol, Vec<Symbol>>,
    ty: &Value,
    span: crate::span::SourceSpan,
) -> Value {
    if aliases.is_empty() {
        return ty.clone();
    }
    let TypeExtractor::ExprCarried { value, member } = extract_type(kb, ty) else {
        return ty.clone();
    };
    let Some(segs) = receiver_path_segs(kb, &value) else {
        return ty.clone();
    };
    let (head, fields) = segs.split_first().expect("receiver path is non-empty");
    let Some(canon_head) = aliases.get(head) else {
        return ty.clone();
    };
    // Canonical receiver path = the head's alias path, then the trailing field segments.
    let mut canon_segs = canon_head.clone();
    canon_segs.extend_from_slice(fields);
    build_projection_from_segs(kb, &canon_segs, member, span)
}

/// WI-400 increment C: build a projection type [`Value`] from a receiver path's segments
/// plus the projected `member`, mirroring the loader's two carriers
/// (`try_expr_carried_projection`): a single-segment receiver rides the ground
/// `Fn{ExprCarried, value: Ref(s), member: Ref(M)}` term; a compound receiver rides the
/// `TypeNode::ExprCarried` Node over a `DotApply` chain. `span` is the originating
/// annotation's span (the canonical receiver has no source span of its own); `owner` is
/// `None`.
fn build_projection_from_segs(
    kb: &mut KnowledgeBase,
    segs: &[Symbol],
    member: Symbol,
    span: crate::span::SourceSpan,
) -> Value {
    debug_assert!(!segs.is_empty(), "projection receiver path is non-empty");
    if segs.len() == 1 {
        let receiver_term = kb.alloc(Term::Ref(segs[0]));
        return Value::Term(kb.make_expr_carried(receiver_term, member));
    }
    let mut receiver = NodeOccurrence::new_expr(Expr::Ref(segs[0]), span, None);
    for &field in &segs[1..] {
        receiver = NodeOccurrence::new_expr(
            Expr::DotApply { receiver, name: field, pos_args: Vec::new(), named_args: Vec::new() },
            span,
            None,
        );
    }
    Value::Node(kb.make_expr_carried_occ(receiver, member, span, None))
}

/// WI-398: collect the receiver-head symbols of every expression-carried projection
/// (`ExprCarried`) in a type [`Value`] — the parameters this type PROJECTS. A single-ref
/// `s.M` contributes `s`; a compound `s.f.M` contributes the chain's bottom head `s`.
/// Carrier-agnostic (walks via [`extract_type`], so a `Value::Node` parameterized type
/// is descended too). Builds the cross-parameter dependency graph in
/// [`param_projection_cycle`].
fn collect_projection_receivers(kb: &KnowledgeBase, ty: &Value, out: &mut Vec<Symbol>) {
    match extract_type(kb, ty) {
        TypeExtractor::ExprCarried { value, .. } => {
            if let Some(head) = receiver_path_head_sym(kb, &value) {
                out.push(head);
            }
        }
        TypeExtractor::Parameterized { bindings, .. } => {
            for (_, v) in &bindings {
                collect_projection_receivers(kb, v, out);
            }
        }
        TypeExtractor::Arrow { param, result, effects } => {
            collect_projection_receivers(kb, &param, out);
            collect_projection_receivers(kb, &result, out);
            collect_projection_receivers(kb, &effects, out);
        }
        TypeExtractor::NamedTuple(fields) => {
            for (_, v) in &fields {
                collect_projection_receivers(kb, v, out);
            }
        }
        TypeExtractor::EffectsRows(e) => collect_projection_receivers(kb, &e, out),
        // WI-428: a rigid type-receiver projection has a TYPE subject, not a value
        // parameter — it contributes no cross-parameter dependency edge.
        TypeExtractor::RigidTypeProjection { .. }
        | TypeExtractor::Denoted(_)
        | TypeExtractor::SortRef(_)
        | TypeExtractor::TypeVar(_)
        | TypeExtractor::Nothing
        | TypeExtractor::Error => {}
    }
}

/// WI-398: detect a cyclic CROSS-PARAMETER projection in an operation signature. Param
/// `q` depends on param `p` when `q`'s declared type projects `p` via an `ExprCarried`
/// receiver (`q: p.M`, `q: p.f.M`). The synthesis order is a topological order of those
/// edges; a cycle (`f(a: b.T, b: a.T)`, or the length-1 self-projection `f(a: a.T)`) has
/// NO synthesis order, so the signature is ill-formed — a loud error at LOAD per the
/// projection's definitional content (design path-dependent-types.md §6, WI-398).
/// Returns the cyclic parameter symbols (in cycle order) when the dependencies form a
/// cycle, else `None`.
fn param_projection_cycle(kb: &KnowledgeBase, params: &[(Symbol, Value)]) -> Option<Vec<Symbol>> {
    // Fast path: no parameter type carries a projection ⇒ no edges ⇒ no cycle.
    if !params.iter().any(|(_, t)| value_contains_projection(kb, t)) {
        return None;
    }
    let sym_to_idx: HashMap<Symbol, usize> =
        params.iter().enumerate().map(|(i, (s, _))| (*s, i)).collect();
    // prereqs[q] = the param indices q's type projects (its receivers that are params).
    let mut prereqs: Vec<Vec<usize>> = vec![Vec::new(); params.len()];
    for (q, (_, ty)) in params.iter().enumerate() {
        let mut recv: Vec<Symbol> = Vec::new();
        collect_projection_receivers(kb, ty, &mut recv);
        for r in recv {
            if let Some(&p) = sym_to_idx.get(&r) {
                if !prereqs[q].contains(&p) {
                    prereqs[q].push(p);
                }
            }
        }
    }
    // DFS cycle detection (0 = unvisited, 1 = on the current path, 2 = done).
    let mut color = vec![0u8; params.len()];
    let mut stack: Vec<usize> = Vec::new();
    for start in 0..params.len() {
        if color[start] == 0 {
            if let Some(cycle) = dfs_projection_cycle(start, &prereqs, &mut color, &mut stack) {
                return Some(cycle.into_iter().map(|i| params[i].0).collect());
            }
        }
    }
    None
}

/// DFS helper for [`param_projection_cycle`]: returns the cycle (param indices in path
/// order) when a back-edge to a node already on the current path is found.
fn dfs_projection_cycle(
    u: usize,
    prereqs: &[Vec<usize>],
    color: &mut [u8],
    stack: &mut Vec<usize>,
) -> Option<Vec<usize>> {
    color[u] = 1;
    stack.push(u);
    for &v in &prereqs[u] {
        if color[v] == 1 {
            // Back-edge to a node on the current path: the cycle is the stack suffix
            // from v's first occurrence onward.
            let pos = stack.iter().position(|&x| x == v).expect("on-path node is on the stack");
            return Some(stack[pos..].to_vec());
        }
        if color[v] == 0 {
            if let Some(cycle) = dfs_projection_cycle(v, prereqs, color, stack) {
                return Some(cycle);
            }
        }
    }
    stack.pop();
    color[u] = 2;
    None
}

/// WI-376: replace every expression-carried projection (`s.T` / `s.Sort`) in a type
/// [`Value`] by projecting the RECEIVER param's argument type. `arg_types` maps each
/// operation parameter symbol to the inferred type of the argument bound to it (built
/// in [`check_apply_iter`]'s argument loops). This is the synthesis-time discharge of
/// the projection constraint — the arguments are already synthesized, so the receiver's
/// static type is known. A projection whose receiver is not an argument-bound
/// parameter, names a member the receiver's concrete sort does not declare, or whose
/// member is not concretely known (a bare / abstract receiver), is a loud
/// [`TypeError`] — never a silent fresh var, which would unsoundly absorb any demand
/// downstream. Non-projection types pass through unchanged.
fn eliminate_type_projections(
    kb: &mut KnowledgeBase,
    ty: &Value,
    arg_types: &HashMap<Symbol, Value>,
    arg_syms: Option<&HashMap<Symbol, Symbol>>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<Value, TypeError> {
    match ty {
        Value::Term(t) => {
            Ok(Value::Term(rewrite_term_projections(kb, *t, arg_types, arg_syms, ctx, span)?))
        }
        Value::Node(occ) => {
            // WI-397: a top-level COMPOUND-receiver projection (`a.b.T`) rides a
            // `TypeNode::ExprCarried` Node carrier (its receiver is a field-access
            // occurrence). Resolve the receiver path's static type and project the
            // member — the Node twin of the `Value::Term` path above.
            if let TypeExtractor::ExprCarried { value, member } = extract_type(kb, ty) {
                return match resolve_compound_projection(kb, &value, member, arg_types, ctx, span)? {
                    ProjResult::Grounded(v) => Ok(v),
                    // WI-400: abstract receiver, member declared — keep the original
                    // compound `ExprCarried` Node as the rigid neutral. WI-459 NOTE: unlike
                    // the single-`Ref` `Value::Term` path, this compound (`a.b.T`) neutral is
                    // NOT re-keyed to the caller's argument (`arg_syms` is not threaded into
                    // `resolve_compound_projection`). A forwarded compound projection through
                    // a call therefore stays callee-keyed and fails the ζ identity check —
                    // a LOUD over-rejection (sound, never a wrong accept), not a regression
                    // (the compound path never re-keyed). The WI-447 stdlib threading uses
                    // only single-`Ref` receivers (`s`/`xs`/`rest`); compound-receiver
                    // re-keying is a recorded follow-on.
                    ProjResult::Neutral => Ok(ty.clone()),
                };
            }
            // WI-460: a projection nested INSIDE a denoted-bearing `Value::Node` — e.g.
            // `s.T` in the param of a callback arrow `(x: s.T) -> Bool @ {EffP, -Modify[x]}`,
            // or `l.T` in `Stream[T = l.T, E = {Modify[c]}]` — is rewritten THROUGH the Node
            // carrier rather than bailed: descend the occurrence tree, eliminate each
            // projection child against the receiver's argument type (the same discharge the
            // `Value::Term` path does), and rebuild the carrier with the denoted children
            // (`-Modify[x]`, `Modify[c]`) preserved. A Node with no projection is a plain
            // denoted type, returned as-is. An UNSUPPORTED nested shape (a projection inside a
            // `named_tuple` carrier) still bails loudly in the descent — never a silent leak.
            if value_contains_projection(kb, ty) {
                return eliminate_node_projections(kb, occ, arg_types, arg_syms, ctx, span);
            }
            Ok(ty.clone())
        }
        other => Ok(other.clone()),
    }
}

/// WI-460: eliminate expression-carried projections nested INSIDE a denoted-bearing
/// `Value::Node` carrier — an arrow / parameterized / effect-row occurrence that also
/// carries a `denoted` value-in-type, e.g. the callback param `(x: s.T) -> Bool @
/// {EffP, -Modify[x]}` or `Stream[T = l.T, E = {Modify[c]}]`. The Node twin of
/// [`rewrite_term_projections`]'s recursion into `Term::Fn` children: descend the
/// occurrence tree, route each GROUND (`TypeChild::Ground`) child through
/// `rewrite_term_projections` and each NODE child through this function, then rebuild the
/// carrier with the `make_*_occ` builders. A child that GROUNDS from a Node to a concrete
/// `Term` (a compound `a.b.T` reducing to `Int64`) collapses to `TypeChild::Ground` via
/// [`value_to_type_child`]. `denoted` values (`Modify[c]`, `-Modify[x]`) carry no type
/// projection and are returned untouched. A `named_tuple` carrier holding a projection is
/// NOT yet rewritten (its fields ride a `Value`-carried list the `TypeChild` descent does
/// not reach) — it bails loudly, never leaking an un-eliminated projection.
fn eliminate_node_projections(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    arg_types: &HashMap<Symbol, Value>,
    arg_syms: Option<&HashMap<Symbol, Symbol>>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<Value, TypeError> {
    // Eliminate one structural child: a ground term rewrites via the `Term` path; a Node
    // child recurses (and may collapse Node→Term when a compound projection grounds).
    fn elim_child(
        kb: &mut KnowledgeBase,
        c: &TypeChild,
        arg_types: &HashMap<Symbol, Value>,
        arg_syms: Option<&HashMap<Symbol, Symbol>>,
        ctx: &TypeErrorContext,
        span: Option<Span>,
    ) -> Result<TypeChild, TypeError> {
        match c {
            TypeChild::Ground(t) => Ok(TypeChild::Ground(rewrite_term_projections(
                kb, *t, arg_types, arg_syms, ctx, span,
            )?)),
            TypeChild::Node(n) => {
                let v = eliminate_node_projections(kb, n, arg_types, arg_syms, ctx, span)?;
                Ok(value_to_type_child(kb, &v))
            }
        }
    }
    let sp = occ.span;
    let owner = occ.owner;
    match &occ.kind {
        NodeKind::Type(node) => match node {
            TypeNode::Arrow { param, result, effects } => {
                let p = elim_child(kb, param, arg_types, arg_syms, ctx, span)?;
                let r = elim_child(kb, result, arg_types, arg_syms, ctx, span)?;
                let e = elim_child(kb, effects, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_arrow_occ(p, r, e, sp, owner)))
            }
            TypeNode::Parameterized { base, bindings } => {
                let b = elim_child(kb, base, arg_types, arg_syms, ctx, span)?;
                let mut bs: Vec<(Symbol, TypeChild)> = Vec::with_capacity(bindings.len());
                for (s, c) in bindings {
                    bs.push((*s, elim_child(kb, c, arg_types, arg_syms, ctx, span)?));
                }
                Ok(Value::Node(kb.make_parameterized_occ(b, bs, sp, owner)))
            }
            TypeNode::EffectsRows { effects_expr } => {
                let e = elim_child(kb, effects_expr, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_effects_rows_occ(e, sp, owner)))
            }
            // A `denoted` value-in-type (`Modify[c]`) carries no type projection — as-is.
            TypeNode::Denoted { .. } => Ok(Value::Node(Rc::clone(occ))),
            // A nested COMPOUND projection (`a.b.T`) Node — resolve it exactly as the
            // top-level `ExprCarried` arm of `eliminate_type_projections` does (callee-keyed;
            // the WI-459 re-key is single-`Ref` only, see that arm's note).
            TypeNode::ExprCarried { .. } => {
                if let TypeExtractor::ExprCarried { value, member } =
                    extract_type(kb, &Value::Node(Rc::clone(occ)))
                {
                    match resolve_compound_projection(kb, &value, member, arg_types, ctx, span)? {
                        ProjResult::Grounded(v) => Ok(v),
                        ProjResult::Neutral => Ok(Value::Node(Rc::clone(occ))),
                    }
                } else {
                    // An `ExprCarried` carrier whose `member` is not a ground `Ref` is
                    // malformed (the builders always store a ground `Ref` member). Bail
                    // loudly rather than silently passing the projection through — `value_-
                    // contains_projection` already classified this node as projection-bearing.
                    Err(projection_type_error(
                        ctx,
                        span,
                        "a type projection nested in a denoted-bearing type has a non-Ref \
                         projection member (malformed carrier)",
                    ))
                }
            }
            // A projection inside a `named_tuple` carrier is the remaining follow-on: its
            // `fields` ride a `Value`-carried list (not `TypeChild` children), so the
            // structural descent above does not reach them. Bail loudly rather than leak.
            TypeNode::NamedTuple { .. } => Err(projection_type_error(
                ctx,
                span,
                "a type projection nested in a named-tuple denoted-bearing type is not yet supported",
            )),
        },
        NodeKind::EffectExpr(node) => match node {
            EffectExprNode::Merge { left, right } => {
                let l = elim_child(kb, left, arg_types, arg_syms, ctx, span)?;
                let r = elim_child(kb, right, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_merge_occ(l, r, sp, owner)))
            }
            EffectExprNode::Present { label } => {
                let l = elim_child(kb, label, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_present_occ(l, sp, owner)))
            }
            EffectExprNode::Absent { label } => {
                let l = elim_child(kb, label, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_absent_occ(l, sp, owner)))
            }
            EffectExprNode::Open { tail } => {
                let t = elim_child(kb, tail, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_open_occ(t, sp, owner)))
            }
            EffectExprNode::EmptyRow => Ok(Value::Node(Rc::clone(occ))),
        },
        // A non-type / non-effect occurrence (Expr / Pattern) in a type position is not a
        // projection carrier — return as-is (defensive; the descent never targets one).
        _ => Ok(Value::Node(Rc::clone(occ))),
    }
}

/// WI-397: resolve a COMPOUND-receiver projection (`a.b.T`) — the receiver `value`
/// is a field-access occurrence (`Value::Node`), not a single value reference.
/// Resolve the receiver path's static type, then project the `member` off it. The
/// Node twin of the single-`Ref` path in [`rewrite_term_projections`].
fn resolve_compound_projection(
    kb: &mut KnowledgeBase,
    receiver: &Value,
    member: Symbol,
    arg_types: &HashMap<Symbol, Value>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<ProjResult, TypeError> {
    let (recv_ty, recv_decl_sort) =
        resolve_receiver_path_type(kb, receiver, arg_types, ctx, span)?;
    let member_str = kb.resolve_sym(member).to_owned();
    project_type_member(kb, &recv_ty, &member_str, recv_decl_sort, ctx, span)
}

/// Resolve the static TYPE of a field-access receiver path occurrence (WI-397). A
/// single value reference `Ref(s)` is the type of the argument bound to param `s`;
/// a field access `base.field` is the type of `field` in the (recursively resolved)
/// `base` type. Any other shape is a loud error (never a silent fresh var).
///
/// WI-400: also returns the **declaring sort** of an ABSTRACT result — the sort whose
/// `requires` chain lends an abstract type-parameter result its interface (`s.provider :
/// P` resolves to `(P-var, Some(State))`, since `State` declares the field `provider : P`
/// and `State requires DataProvider[P]`). `None` for a concrete result.
fn resolve_receiver_path_type(
    kb: &mut KnowledgeBase,
    receiver: &Value,
    arg_types: &HashMap<Symbol, Value>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<(Value, Option<Symbol>), TypeError> {
    // Innermost head: a value reference `Ref(s)` (the DotApply chain bottoms out in
    // it). The receiver is the argument bound to param `s` — a top-level reference, not a
    // field projection, so no declaring sort is attached here.
    if let Some(head) = extract_sort_ref_sym(kb, receiver) {
        let ty = arg_types.get(&head).cloned().ok_or_else(|| {
            projection_type_error(ctx, span, &format!(
                "type projection receiver '{}' is not an argument-bound parameter of this call",
                kb.resolve_sym(head),
            ))
        })?;
        return Ok((ty, None));
    }
    // A field access `base.field` — a `DotApply` with no call args. Resolve `base`,
    // then project `field`'s type off it.
    if let Value::Node(occ) = receiver {
        if let Some(Expr::DotApply { receiver: base, name, pos_args, named_args }) = occ.as_expr() {
            if pos_args.is_empty() && named_args.is_empty() {
                let base_val = Value::Node(std::rc::Rc::clone(base));
                let field = *name;
                let (base_ty, _) = resolve_receiver_path_type(kb, &base_val, arg_types, ctx, span)?;
                return resolve_field_type(kb, &base_ty, field, ctx, span);
            }
        }
    }
    Err(projection_type_error(ctx, span,
        "type projection receiver is not a value-reference field path (`s.field…`)"))
}

/// Resolve field `field_sym`'s type given a receiver's sort type (WI-397): find the
/// receiver sort's constructor declaring the field, take its declared field type,
/// and substitute the receiver's type-args — the same subst pattern field types use
/// (design path-dependent-types.md §1 step 2). A receiver with no concrete sort, or
/// a field no constructor declares, is a loud error.
///
/// WI-400: returns `(field-type, declaring-sort)`. The declaring sort is `Some(sort_sym)`
/// when the field's resolved type is ABSTRACT (no concrete sort functor — an unbound
/// type-parameter of `sort_sym`), so `project_type_member` can read its declared
/// interface off `sort_sym`'s `requires` chain; `None` for a concrete field type.
fn resolve_field_type(
    kb: &mut KnowledgeBase,
    recv_ty: &Value,
    field_sym: Symbol,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<(Value, Option<Symbol>), TypeError> {
    let sort_sym = sort_functor_of_view(kb, recv_ty).ok_or_else(|| {
        projection_type_error(ctx, span, &format!(
            "cannot access field '{}' on a receiver with no concrete sort",
            kb.resolve_sym(field_sym),
        ))
    })?;
    // The receiver's type-arg substitution is the same for every constructor.
    let subst = build_pattern_subst(kb, recv_ty, sort_sym);
    // Collect the field's resolved type from EVERY constructor that declares it, so the
    // result is INDEPENDENT of `constructors_of_sort`'s (HashMap) iteration order. Field
    // access on a multi-variant sort is well-defined only when all variants agree on the
    // field's type; a divergence is a LOUD error, never an order-dependent pick.
    let mut resolved: Option<Value> = None;
    for ctor in kb.constructors_of_sort(sort_sym) {
        // Scope the `entity_field_types` borrow so the `&mut kb` subst call below is
        // free; `continue` to the next constructor if this one lacks the field.
        let declared = {
            let Some(fields) = kb.entity_field_types(ctor) else { continue };
            match fields.iter().find(|(f, _)| *f == field_sym) {
                Some((_, d)) => d.clone(),
                None => continue,
            }
        };
        let this = match &subst {
            Some(s) => walk_pattern_field_type_deep(kb, s, &declared),
            None => declared,
        };
        match &resolved {
            None => resolved = Some(this),
            Some(prev) if prev.structural_eq(&this) => {}
            Some(_) => {
                return Err(projection_type_error(ctx, span, &format!(
                    "field '{}' is declared with differing types across the constructors of \
                     '{}'; a compound projection off it is ambiguous",
                    kb.resolve_sym(field_sym),
                    kb.qualified_name_of(sort_sym).to_owned(),
                )));
            }
        }
    }
    let resolved = resolved.ok_or_else(|| projection_type_error(ctx, span, &format!(
        "type '{}' has no field '{}'",
        kb.qualified_name_of(sort_sym).to_owned(),
        kb.resolve_sym(field_sym),
    )))?;
    // The field's resolved type is an ABSTRACT type-parameter of `sort_sym` (an unbound
    // `sort P = ?` left as a logic var, not a concrete sort / arrow / tuple) iff it is a
    // bare type-param value. Then `sort_sym`'s `requires` chain is what lends it an
    // interface for a downstream projection (`s.provider : P`, `State requires
    // DataProvider[P]`). A concrete field type carries no declaring sort.
    let decl_sort = match &resolved {
        Value::Term(t) if is_type_param_value(kb, *t) => Some(sort_sym),
        _ => None,
    };
    Ok((resolved, decl_sort))
}

/// Recursive term rewrite for [`eliminate_type_projections`]: an `ExprCarried` head is
/// projected and replaced; any other `Fn` is rebuilt only if a child changed; leaves
/// pass through.
fn rewrite_term_projections(
    kb: &mut KnowledgeBase,
    t: TermId,
    arg_types: &HashMap<Symbol, Value>,
    arg_syms: Option<&HashMap<Symbol, Symbol>>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<TermId, TypeError> {
    // WI-428: a rigid type-receiver projection (`P.Key` / `MemStore.Key`) — validated
    // and δ-grounded (or kept as the rigid neutral) against the declaring sort's
    // `requires` chain / the subject's own manifest bindings; no `arg_types` receiver
    // lookup (the subject is a TYPE, not a value parameter).
    if matches!(type_head(kb, &TermIdView(t)), TypeHead::RigidProjection) {
        let TypeExtractor::RigidTypeProjection { sort, subject, member } =
            extract_type(kb, &TermIdView(t))
        else {
            return Ok(t);
        };
        return match resolve_rigid_projection(kb, sort, &subject, member, ctx, span)? {
            ProjResult::Grounded(Value::Term(pt)) => Ok(pt),
            ProjResult::Grounded(_) => Err(projection_type_error(ctx, span,
                "type projection resolved to a non-term carrier, which is not yet supported")),
            ProjResult::Neutral => Ok(t),
        };
    }
    if matches!(type_head(kb, &TermIdView(t)), TypeHead::ExprCarried) {
        let TypeExtractor::ExprCarried { value, member } = extract_type(kb, &TermIdView(t)) else {
            return Ok(t);
        };
        // A supported projection's receiver is a single value reference `Ref(s)`
        // (classified as `SortRef`); a compound receiver is rejected at load, so this
        // is defensive.
        let receiver = extract_sort_ref_sym(kb, &value).ok_or_else(|| {
            projection_type_error(ctx, span, "type projection receiver is not a simple value reference")
        })?;
        let arg_ty = match arg_types.get(&receiver) {
            Some(v) => v.clone(),
            None => {
                return Err(projection_type_error(ctx, span, &format!(
                    "type projection receiver '{}' is not an argument-bound parameter of this call",
                    kb.resolve_sym(receiver),
                )));
            }
        };
        let member_str = kb.resolve_sym(member).to_owned();
        // Single-ref receiver: the arg's inferred type (a concrete sort, or a bound
        // type-param). No abstract-type-param declaring sort is in hand here (that arises
        // only on the compound field-projection path) — `None`.
        return match project_type_member(kb, &arg_ty, &member_str, None, ctx, span)? {
            ProjResult::Grounded(Value::Term(pt)) => Ok(pt),
            // A projection resolving to a Node carrier (e.g. `s.Sort` of a denoted-
            // bearing argument) would poison the enclosing return type to a Node — the
            // follow-on; loud rather than silently dropped.
            ProjResult::Grounded(_) => Err(projection_type_error(ctx, span,
                "type projection resolved to a non-term carrier, which is not yet supported")),
            // WI-400: the receiver is abstract but the member is declared — the rigid
            // NEUTRAL (path-identity). WI-459: RE-KEY its receiver from the callee's formal
            // parameter to the CALLER's argument value-reference when this is a call-site
            // elimination (`arg_syms` present) and the argument is a simple value reference.
            // The projection stayed abstract precisely because the argument's TYPE did not
            // bind the member (`sfd(xs)` with the bare `xs : List`), so the receiver VALUE
            // is exactly that argument — `sfd.xs.T` is definitionally `collectd.xs.T`. The
            // grounded arms above never reach here, so a member the argument's type DID bind
            // (the recursive `collectd(rest)`, where `rest : List[T = xs.T]` δ-reduces `T`
            // to `xs.T`) keeps its δ-reduced value un-re-keyed. A non-value-ref argument has
            // no `arg_syms` entry → left as the callee-keyed neutral (deferred-receiver
            // follow-on). Re-forming `ExprCarried{Ref(arg_sym), member}` here is what makes
            // the SAME definitional projection compare EQUAL under the non-decomposing ζ arm
            // (WI-400) instead of two identically-printed-yet-distinct neutrals.
            ProjResult::Neutral => Ok(match arg_syms.and_then(|m| m.get(&receiver)) {
                Some(&arg_sym) => {
                    let recv_term = kb.alloc(Term::Ref(arg_sym));
                    kb.make_expr_carried(recv_term, member)
                }
                None => t,
            }),
        };
    }
    // Recurse into `Fn` children, rebuilding only if a child changed. Index-based so
    // each child is read (a `Copy` `TermId`) before the `&mut kb` recursive call and
    // written after — no borrow of the owned (cloned) arg vectors across the call.
    if let Term::Fn { functor, pos_args, named_args } = kb.get_term(t).clone() {
        let mut changed = false;
        let mut new_pos = pos_args;
        for i in 0..new_pos.len() {
            let nc = rewrite_term_projections(kb, new_pos[i], arg_types, arg_syms, ctx, span)?;
            if nc != new_pos[i] {
                new_pos[i] = nc;
                changed = true;
            }
        }
        let mut new_named = named_args;
        for i in 0..new_named.len() {
            let nc = rewrite_term_projections(kb, new_named[i].1, arg_types, arg_syms, ctx, span)?;
            if nc != new_named[i].1 {
                new_named[i].1 = nc;
                changed = true;
            }
        }
        if changed {
            return Ok(kb.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named }));
        }
    }
    Ok(t)
}

/// WI-400: outcome of projecting a member off a receiver's type. A projection either
/// **grounds** (δ — the receiver's type makes the member manifest, `List[Int64].T =
/// Int64`) or **stays neutral** (the receiver's type is abstract — a bare type-parameter
/// the receiver leaves unbound, or an abstract type-variable receiver — but the member
/// *is* declared on the receiver's interface, so the projection is a well-formed RIGID
/// type keyed by `receiver` + `member`). A neutral is NOT an error: it is the
/// abstract-stays-poly form (WI-376), usable by path-identity (the ζ arm of
/// [`unify_types`]). The caller keeps the ORIGINAL `ExprCarried` for a neutral — already
/// the canonical form — rather than reconstructing it.
enum ProjResult {
    /// The member is manifest: the projected type.
    Grounded(Value),
    /// The receiver is abstract but the member is declared on its interface: keep the
    /// projection as a rigid neutral.
    Neutral,
}

/// Project a single type member (`T`, `E`, `Sort`, …) off the receiver's argument
/// type for [`rewrite_term_projections`].
///
/// `recv_decl_sort` is the sort whose `requires` chain lends an ABSTRACT type-variable
/// receiver its declared interface — supplied by [`resolve_field_type`] when the
/// receiver's type resolved to an (abstract) type-parameter of that sort (`s.provider : P`
/// ⟹ `State`, since `State requires DataProvider[P]`). `None` for a concrete receiver or
/// where no declaring sort is in hand; then an abstract member that is not a declared
/// type-parameter cannot be confirmed and is a loud error.
fn project_type_member(
    kb: &mut KnowledgeBase,
    arg_ty: &Value,
    member: &str,
    recv_decl_sort: Option<Symbol>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<ProjResult, TypeError> {
    // WI-381: resolve a defined-type / alias receiver to its underlying shape first, so
    // every projection reads off the resolved structure (`sort IntStream =
    // Stream[T = Int]` ⟹ project off `Stream[T = Int]`), never the opaque alias — which
    // declares no members, so `s.T` would spuriously fail. A non-alias / opaque /
    // parametric receiver is left unchanged.
    let resolved_recv: Value = match extract_type(kb, arg_ty) {
        TypeExtractor::SortRef(s) => match resolve_alias_shape(kb, s) {
            Some(shape) => Value::Term(shape),
            None => arg_ty.clone(),
        },
        _ => arg_ty.clone(),
    };
    let arg_ty = &resolved_recv;
    // `s.Sort` — the whole parameterized sort of the receiver (captures every
    // parameter, wide-sort safe).
    if member == "Sort" {
        return Ok(ProjResult::Grounded(arg_ty.clone()));
    }
    // Concrete: the receiver's type binds the member directly (`List[Int].T = Int`).
    if let Some(p) = extract_type_param(kb, arg_ty, member) {
        return Ok(ProjResult::Grounded(p));
    }
    // The member is not concretely bound. WI-400 (abstract-stays-poly, co-delivering
    // WI-376): a projection off an abstract receiver no longer errors — it STAYS NEUTRAL
    // (a rigid type keyed by receiver + member, compared by the ζ arm of `unify_types`),
    // PROVIDED the member is DECLARED on the receiver's interface. Distinguish:
    //
    //   - a CONCRETE-sort receiver with the member as a declared-but-UNBOUND type
    //     parameter (`peek(l: List) -> l.T`, bare `List` — `T` is `List`'s param, just
    //     not pinned) ⟹ neutral;
    //   - an abstract TYPE-VARIABLE receiver whose declared interface (the enclosing
    //     sort's `requires Spec[recv]`) provides the member (`s.provider.K` where
    //     `s.provider : P` and `State requires DataProvider[P]`, `K` a member of
    //     DataProvider) ⟹ neutral, via [`abstract_var_declares_member`];
    //   - a member NO interface declares (a typo, `l.Nonesuch`) ⟹ a LOUD error.
    //
    // Minting an unconstrained var here (instead of a neutral) would be unsound — it
    // would absorb any demand downstream (`peek(l)` usable as both `Int64` and `String`);
    // the neutral cannot, since the ζ arm only equates it with an IDENTICAL neutral.
    if let Some(s) = sort_functor_of_view(kb, arg_ty) {
        if kb.type_params_of_sort(s).iter().any(|d| d.as_str() == member) {
            return Ok(ProjResult::Neutral);
        }
        // WI-376 (cross-sort provider DIVERGENT member name): the receiver's sort does not
        // declare `member` ITSELF, but may PROVIDE a spec that declares it under a
        // different carrier-side name (`List provides Iterable[List[T], T]` ⟹ Iterable's
        // `Element` maps to `List`'s `T`). Map `member` through the provides binding to the
        // carrier-side type and ground/neutralize THAT against the receiver — so one
        // signature written in the spec's vocabulary (`c.Element`) grounds on a concrete
        // carrier (`List[T = Int64].Element = Int64`) and stays neutral on a bare one.
        if let Some(r) = project_via_provided_spec(kb, arg_ty, s, member) {
            return r;
        }
        return Err(projection_type_error(ctx, span, &format!(
            "type '{}' has no member '{member}'",
            kb.qualified_name_of(s).to_owned(),
        )));
    }
    // No concrete sort: an abstract type-variable receiver (a sort type-parameter, e.g.
    // `s.provider : P` — opened to a logic var whose source identity is erased). Neutral
    // iff the param's DECLARED INTERFACE provides the member — the `requires Spec[param]`
    // bounds on the sort that DECLARES the param (`recv_decl_sort`, supplied by
    // `resolve_field_type`). Each such `Spec` lends the param its members
    // (`State requires DataProvider[P]` ⟹ `P` has DataProvider's `K`). A member no bound
    // declares (or no declaring sort in hand) is a loud error, never a silent neutral.
    if let Some(decl_sort) = recv_decl_sort {
        // WI-430: carrier-precise neutral formation. The abstract receiver IS one of
        // `decl_sort`'s type-parameters (`s.provider : P`); only a `requires` bound whose
        // CARRIER is THIS param lends it the member. Consulting the whole `requires` chain
        // (the pre-WI-430 behavior) over-accepts a member projection off the WRONG param
        // when a sort has several params each carrying their own `requires` (`State[P, Q]
        // requires DataProvider[P], OtherProvider[Q]` would wrongly accept `s.provider.M`,
        // `M` being `Q`'s member, off the `P`-typed `s.provider`). Match the receiver's
        // carrier key — the var-id all the param's spellings share (WI-428 `SubjectKey`) —
        // against each bound, the `ExprCarried`-side counterpart of `resolve_rigid_-
        // projection`'s candidate filter (`spec_mentions_key`).
        let carrier_key = match arg_ty {
            Value::Term(t) => subject_key_of_term(kb, *t),
            _ => None,
        };
        if let Some(key) = carrier_key {
            if abstract_member_declared_by_requires(kb, decl_sort, key, member) {
                return Ok(ProjResult::Neutral);
            }
        }
        return Err(projection_type_error(ctx, span, &format!(
            "no `requires` bound on '{}' whose carrier is this abstract type parameter \
             declares a member '{member}'; cannot project '{member}'",
            kb.qualified_name_of(decl_sort).to_owned(),
        )));
    }
    Err(projection_type_error(ctx, span, &format!(
        "cannot project '{member}' off an abstract receiver with no concrete sort",
    )))
}

/// WI-400/430: does ANY `requires Spec[…]` bound on `decl_sort` lend the abstract type
/// parameter identified by `carrier_key` the member `member`? Consults `decl_sort`'s whole
/// (transitive) `requires` chain, accepting iff some entry [`requires_entry_lends_member`]
/// — i.e. declares `member` AND carries `carrier_key`. The `ExprCarried` neutral-formation
/// gate for an abstract-receiver projection (`s.provider.K`, `s.provider : P` an abstract
/// type-parameter of `decl_sort`); design path-dependent-types.md §1, §4.1.
fn abstract_member_declared_by_requires(
    kb: &mut KnowledgeBase,
    decl_sort: Symbol,
    carrier_key: SubjectKey,
    member: &str,
) -> bool {
    requires_chain(kb, decl_sort)
        .iter()
        .any(|entry| requires_entry_lends_member(kb, entry, carrier_key, member))
}

/// WI-400/428/430 — THE carrier-precise candidate predicate: does a single `requires`
/// entry lend `member` to the type parameter identified by `carrier_key`? Both halves must
/// hold: (a) the required spec DECLARES `member` as one of its type-parameters
/// (`DataProvider` declares `K`), and (b) the spec application MENTIONS `carrier_key` among
/// its binding values — so the bound's carrier IS this param. `requires DataProvider[P]`
/// auto-completes (WI-359 loader normalization) to a named binding carrying `P`, which
/// [`spec_mentions_key`] reads; a positional carrier never survives to here.
///
/// Shared by the two pure-filter sites — the `ExprCarried` neutral gate
/// ([`abstract_member_declared_by_requires`], WI-430) and [`resolve_rigid_projection`]'s
/// rigid-projection candidate collection (WI-428) — so the carrier-precision rule has ONE
/// source of truth: both decide the same soundness question (which bound's carrier is this
/// subject), and a refinement to either half must move both at once.
/// (`ground_rigid_projection_if_concrete` calls the two component checks SEPARATELY — it
/// needs the carrier-mention outcome on its own to drive a self-carrier fallback — so it is
/// deliberately not routed through this helper.)
///
/// NB `spec_mentions_key` matches `carrier_key` in ANY top-level binding value, not strictly
/// the spec's carrier slot — the documented WI-428 conservative reading (a param mentioned
/// as a non-carrier binding still licenses); exact carrier-slot precision is the §5.3
/// normalization end-state, shared with the rigid path.
fn requires_entry_lends_member(
    kb: &KnowledgeBase,
    entry: &RequiresEntry,
    carrier_key: SubjectKey,
    member: &str,
) -> bool {
    kb.type_params_of_sort(entry.required_sort)
        .iter()
        .any(|d| d.as_str() == member)
        && spec_mentions_key(kb, entry.spec, carrier_key)
}

/// WI-376 (cross-sort provider divergent member name): project `member` off a CONCRETE
/// receiver `recv_ty` (sort `recv_sort`) that does not declare `member` itself but PROVIDES
/// a spec that does — under a possibly-different carrier-side name. Reads the carrier's
/// `provides Spec[…]` binding for the spec's `member` parameter (`List provides
/// Iterable[List[T], T]` ⟹ Iterable's `Element` ↦ `List`'s `T`), then grounds that
/// carrier-side type against the receiver's own type-args (`build_pattern_subst`, the same
/// substitution field-type resolution uses). A binding that grounds to a concrete type is
/// `Grounded`; one still resting on an unbound carrier parameter (a BARE receiver) stays
/// `Neutral` — abstract-stays-poly, exactly as a direct unbound type-param would. Returns
/// `None` when no provided spec declares `member` (the caller then surfaces the loud
/// no-member error). First provided spec that declares `member` wins (a member shared
/// across two provided specs is left to a later disambiguation pass, mirroring
/// `find_spec_op_for_provided_sort`).
fn project_via_provided_spec(
    kb: &mut KnowledgeBase,
    recv_ty: &Value,
    recv_sort: Symbol,
    member: &str,
) -> Option<Result<ProjResult, TypeError>> {
    for spec in provided_spec_base_syms(kb, recv_sort) {
        if !kb.type_params_of_sort(spec).iter().any(|d| d.as_str() == member) {
            continue;
        }
        let Some(bindings) = provider_spec_view_bindings(kb, recv_sort, spec) else {
            continue;
        };
        let Some((_, carrier_val)) =
            bindings.iter().find(|(p, _)| kb.resolve_sym(*p) == member).copied()
        else {
            continue;
        };
        // WI-396: an EFFECT-row member (`E`) is NEVER projected via `provides` — the
        // written row is its route, never a silent pure default (`List provides
        // Stream[T, {}]` must NOT make `l.E` ground to `{}`). The carrier binding for an
        // effect member is an effect row; skip it, leaving the loud missing-member error.
        if matches!(type_head(kb, &Value::Term(carrier_val)), TypeHead::EffectsRows) {
            continue;
        }
        // Ground the carrier-side type (`List`'s `T`) against the receiver's type-args, so
        // a concrete `List[T = Int64]` grounds `Element` to `Int64`; a bare `List` leaves
        // it an unbound `T` ⟹ neutral.
        let grounded = match build_pattern_subst(kb, recv_ty, recv_sort) {
            Some(s) => walk_pattern_field_type_deep(kb, &s, &Value::Term(carrier_val)),
            None => Value::Term(carrier_val),
        };
        // Grounded ONLY when the result is FULLY concrete (deep `resolved_type_is_ground`,
        // not a head-only check): a structured binding still resting on an unbound carrier
        // param (`Element = Pair[A, B]` on a bare receiver) stays NEUTRAL, never a Grounded
        // type that would absorb demand downstream. A non-Term carrier is conservatively
        // neutral too.
        return Some(if resolved_type_is_ground(kb, &grounded) {
            Ok(ProjResult::Grounded(grounded))
        } else {
            Ok(ProjResult::Neutral)
        });
    }
    None
}

/// WI-383: the `requires`-clause specs of an OPERATION, decoded to `RequiresEntry`s —
/// the op-type-param analogue of [`requires_chain`] (which reads a SORT's
/// `SortRequiresInfo`). An op type-param `getV.T` is lent its members by the operation's
/// OWN `requires Spec[C = T]` clause, stored on `OperationInfo.requires`. Each spec
/// application becomes one entry (`required_sort` = the spec base functor).
///
/// LIMITATION (vs the sort path): this reads the op's DIRECT requires only — it does NOT
/// transitively close (a member declared by a *transitively* required spec, e.g.
/// `requires Ordered[T]` lending `Eq`'s members, is not reached). The candidate filter
/// then finds no bound, so the projection is conservatively rejected (sound — never a
/// wrong ground type). Transitive op-requires lending is deferred (no motivating driver).
fn op_requires_entries(kb: &KnowledgeBase, op_sym: Symbol) -> Vec<RequiresEntry> {
    let Some(rec) = super::op_info::lookup_operation_info(kb, op_sym) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for v in &rec.requires {
        if let Value::Term(tid) = v {
            push_op_requires_clause(kb, *tid, &mut out);
        }
    }
    out
}

/// Decode one operation `requires` clause term into [`RequiresEntry`]s. A multi-goal
/// clause (`requires A, B`) lowers to `conjunction(A, B)` (load's `convert_clause_list`),
/// so flatten it into its conjuncts — otherwise the conjunction functor would mask both
/// specs and silently drop them. A single spec application is itself one entry; a clause
/// with no resolvable spec functor carries no projectable members (skipped — it can never
/// satisfy the member-declared + mentions-subject candidate filter regardless).
fn push_op_requires_clause(kb: &KnowledgeBase, tid: TermId, out: &mut Vec<RequiresEntry>) {
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, .. } if kb.resolve_sym(*functor) == "conjunction" => {
            let conjuncts: Vec<TermId> = pos_args.iter().copied().collect();
            for c in conjuncts {
                push_op_requires_clause(kb, c, out);
            }
        }
        Term::Fn { functor, .. } | Term::Ref(functor) => {
            out.push(RequiresEntry { required_sort: *functor, spec: tid });
        }
        _ => {}
    }
}

/// WI-428: resolve a RIGID type-receiver projection (`P.Key` / `MemStore.Key`) at an
/// elimination site — the formation-validation rules of design §5.3, run in the typer
/// (where the `requires` chain is complete regardless of source order), not the loader
/// (which only classifies).
///
///   - **Concrete / bare sort subject** (`sort == subject`, e.g. `MemStore.Key`): must
///     δ-ground fully via [`project_type_member`] (a manifest binding, an alias shape,
///     or a provided spec's binding). A declared-but-unbound member (`Storage.Key` —
///     the spec sort itself) is the `T#K` carrier-conflation and is LOUDLY rejected:
///     a type-keyed neutral over a bare spec would equate the members of two distinct
///     carriers.
///   - **Rigid type-parameter subject** (`P.Key`): carrier-precise bound lookup — the
///     candidates are the `requires` entries of the declaring sort that DECLARE the
///     member AND MENTION the subject param among their binding values. No candidate →
///     loud error; several → loud ambiguity error (so `(var, member)` determines the
///     bound uniquely — the §5.3 deferred-equivalent identity); exactly one →
///     δ-THROUGH-THE-BOUND when the entry binds the member (`requires Storage[C = P,
///     Key = String]` ⟹ `P.Key = String`), else the projection stays the rigid NEUTRAL
///     (compared by the ζ arm of [`expr_carried_zeta`]).
fn resolve_rigid_projection(
    kb: &mut KnowledgeBase,
    decl_sort: Symbol,
    subject: &Value,
    member: Symbol,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<ProjResult, TypeError> {
    let member_str = kb.resolve_sym(member).to_owned();
    let Value::Term(subject_term) = subject else {
        return Err(projection_type_error(ctx, span,
            "rigid type projection subject is not a sort / type-parameter reference"));
    };
    let key = subject_key_of_term(kb, *subject_term).ok_or_else(|| {
        projection_type_error(ctx, span,
            "rigid type projection subject is not a sort / type-parameter reference")
    })?;
    // Concrete / bare sort subject: keyed by the declaring-sort symbol itself (the
    // loader's `sort slot == var slot` discriminator).
    if let SubjectKey::Sym(subject_sym) = key {
        if same_symbol(kb, subject_sym, decl_sort) {
            let recv = Value::Term(kb.make_sort_ref(subject_sym));
            return match project_type_member(kb, &recv, &member_str, None, ctx, span)? {
                // WI-391: a ground member projects to the canonical `Ref(s)` shape (the
                // producer no longer emits a nullary `Fn{s}` binding here).
                ProjResult::Grounded(v) => Ok(ProjResult::Grounded(v)),
                ProjResult::Neutral => {
                    let sort_name = kb.qualified_name_of(subject_sym).to_owned();
                    let short = kb.resolve_sym(subject_sym).to_owned();
                    Err(projection_type_error(ctx, span, &format!(
                        "'{short}.{member_str}' is not manifest: '{sort_name}' declares \
                         '{member_str}' but does not bind it — a projection off the spec sort \
                         itself would conflate distinct carriers; project off a value \
                         (`s.{member_str}`) or a `requires`-bounded type parameter \
                         (`P.{member_str}`)",
                    )))
                }
            };
        }
    }
    // Rigid type-parameter subject: carrier-precise bound lookup, keyed by the
    // canonical SubjectKey (the param's alias-var id — stable across the param's
    // symbol registrations and the deep walk's alias resolution / rigidification).
    // WI-383: when the subject is an OPERATION type-parameter, the licensing bound is
    // the operation's OWN `requires Spec[C = T]` clause (on `OperationInfo.requires`),
    // NOT a sort-level `SortRequiresInfo` chain — so consult the op's requires there.
    let chain = if kb.kind_of(decl_sort) == Some(crate::intern::SymbolKind::Operation) {
        op_requires_entries(kb, decl_sort)
    } else {
        requires_chain(kb, decl_sort)
    };
    // WI-428/430: the carrier-precise candidate filter — the SAME `requires_entry_lends_-
    // member` predicate the `ExprCarried` neutral gate uses (one source of truth for which
    // bound's carrier is this subject).
    let candidates: Vec<&RequiresEntry> = chain
        .iter()
        .filter(|e| requires_entry_lends_member(kb, e, key, &member_str))
        .collect();
    match candidates.as_slice() {
        [] => {
            // WI-383 SELF-CARRIER (implicit licensing): an OPERATION type-param projection
            // `T.member` whose op has NO `requires` bound mentioning the subject is
            // SELF-LICENSED — the obligation "the carrier bound to T has member `member`"
            // is forwarded, discharged at a concrete call against the carrier's OWN
            // declared `sort <member>` (ground_rigid_projection_if_concrete's self-carrier
            // arm). It stays the rigid NEUTRAL here. A bound that DOES mention the subject
            // but fails to declare `member` is a typo (or a sort-type-param projection),
            // not self-carrier → keep the loud error.
            let is_op = kb.kind_of(decl_sort) == Some(crate::intern::SymbolKind::Operation);
            let mentions_subject = chain.iter().any(|e| spec_mentions_key(kb, e.spec, key));
            if is_op && !mentions_subject {
                Ok(ProjResult::Neutral)
            } else {
                Err(projection_type_error(ctx, span, &format!(
                    "no `requires` bound on '{}' mentioning '{}' declares a member '{member_str}'; \
                     cannot project '{}.{member_str}'",
                    kb.qualified_name_of(decl_sort).to_owned(),
                    type_display_name_value(kb, subject),
                    type_display_name_value(kb, subject),
                )))
            }
        }
        [entry] => match spec_binding_value(kb, entry.spec, &member_str) {
            // δ-through-the-bound. The stored application is AUTO-COMPLETED: an
            // unwritten member's binding is a placeholder ref to the SPEC'S OWN param
            // (`Key = Storage.Key`) — only THAT binding means "bound-open" (the rigid
            // NEUTRAL). Any other leaf is a user-written binding and grounds: a
            // concrete sort (`Key = String`), an opaque nominal (`Key = Token`), or a
            // sibling param of the declaring sort (`Key = K` — grounds to `K`'s ref,
            // resolved by the ordinary alias machinery downstream).
            Some(v) => {
                let binding_key = subject_key_of_term(kb, v);
                let placeholder_key =
                    spec_member_param_key(kb, entry.required_sort, &member_str);
                let is_placeholder = match (binding_key, placeholder_key) {
                    (Some(b), Some(p)) => subject_keys_equal(kb, b, p),
                    // The spec's own param symbol is not identifiable: conservatively
                    // treat a var-keyed leaf as the placeholder (sound — stays rigid).
                    (Some(SubjectKey::Var(_)), None) => true,
                    _ => false,
                };
                // A binding to ANOTHER param of the DECLARING sort (`Key = K`, the
                // carrier `C = P` included) stays rigid too: cross-param δ needs the
                // rigid-substitution coherence of the call/body world (increment B) —
                // grounding to the sibling's bare ref here mis-compares against the
                // rigidified forms the signature walk produces. Sound: at most
                // over-rejection, never a wrong ground type.
                let is_sibling_param = binding_key.is_some_and(|b| {
                    kb.type_params_of_sort(decl_sort).iter().any(|p| {
                        spec_member_param_key(kb, decl_sort, p)
                            .is_some_and(|k| subject_keys_equal(kb, b, k))
                    })
                });
                if is_placeholder || is_sibling_param {
                    Ok(ProjResult::Neutral)
                } else {
                    match normalize_spec_binding_type(kb, v) {
                        Some(ty) => Ok(ProjResult::Grounded(Value::Term(ty))),
                        None => Err(projection_type_error(ctx, span, &format!(
                            "'{}.{member_str}' is bound by its `requires` application to \
                             a structured type; δ through a structured bound binding is \
                             not yet supported",
                            type_display_name_value(kb, subject),
                        ))),
                    }
                }
            }
            // No binding slot at all: the projection is the rigid neutral.
            None => Ok(ProjResult::Neutral),
        },
        _ => Err(projection_type_error(ctx, span, &format!(
            "ambiguous projection '{}.{member_str}': several `requires` bounds on '{}' \
             mentioning it declare '{member_str}'; multi-bound projection is not yet \
             supported",
            type_display_name_value(kb, subject),
            kb.qualified_name_of(decl_sort).to_owned(),
        ))),
    }
}

/// WI-428: the [`SubjectKey`] of a spec's OWN member param (`Storage.Key`) — the
/// identity the requires-tree's auto-completed placeholder binding carries for an
/// unwritten member. `None` when the spec's param symbol is not registered under the
/// expected qualified name.
fn spec_member_param_key(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    member: &str,
) -> Option<SubjectKey> {
    let qn = format!("{}.{member}", kb.qualified_name_of(spec_sort));
    let sym = *kb.symbols.by_qualified_name.get(&qn)?;
    Some(sym_subject_key(kb, sym))
}

/// WI-428: the canonical identity KEY of a rigid-projection subject / a
/// `requires`-binding leaf. A type-parameter (`sort P = ?`) is keyed by its ALIAS-VAR
/// id: the deep walks resolve a param `Ref` into that var (possibly rigidified by
/// WI-392/424), and the `requires` bindings may name a different symbol registration
/// of the same param — the var id is the one identity all spellings share. A
/// non-alias sort is keyed by its symbol (compared via [`same_symbol`]).
#[derive(Clone, Copy)]
enum SubjectKey {
    Var(u32),
    Sym(Symbol),
}

fn subject_key_of_term(kb: &KnowledgeBase, t: TermId) -> Option<SubjectKey> {
    match kb.get_term(t) {
        Term::Var(Var::Global(v) | Var::Rigid(v)) => Some(SubjectKey::Var(v.raw())),
        _ => spec_binding_head_sym(kb, t).map(|s| sym_subject_key(kb, s)),
    }
}

fn sym_subject_key(kb: &KnowledgeBase, s: Symbol) -> SubjectKey {
    if let Some(target) = resolve_sort_alias(kb, s) {
        if let Term::Var(Var::Global(v) | Var::Rigid(v)) = kb.get_term(target) {
            return SubjectKey::Var(v.raw());
        }
    }
    SubjectKey::Sym(s)
}

fn subject_keys_equal(kb: &KnowledgeBase, a: SubjectKey, b: SubjectKey) -> bool {
    match (a, b) {
        (SubjectKey::Var(x), SubjectKey::Var(y)) => x == y,
        (SubjectKey::Sym(x), SubjectKey::Sym(y)) => same_symbol(kb, x, y),
        _ => false,
    }
}

/// WI-428: does a `requires` spec application mention the subject KEY among its
/// TOP-LEVEL binding values (`requires Storage[C = P]` mentions `P`)? Nested mentions
/// (`Storage[C = List[P]]`) are not yet read — the candidate filter is conservative
/// (an unmentioned subject surfaces the loud no-bound error, never a silent pick).
fn spec_mentions_key(kb: &KnowledgeBase, spec: TermId, key: SubjectKey) -> bool {
    let Term::Fn { named_args, .. } = kb.get_term(spec) else { return false };
    named_args.iter().any(|(_, v)| {
        subject_key_of_term(kb, *v).is_some_and(|k| subject_keys_equal(kb, k, key))
    })
}

/// The head symbol of a `requires`-application binding VALUE leaf, across the shapes
/// the loader stores: `Ref(s)` (a type-param binding, `make_sort_ref`), a NULLARY
/// `Fn{s}` (a plain sort name via `name_to_sort_term`), or the deep
/// `sort_ref(name: Ref(s))`. A structured binding (a nested application) is not a
/// leaf → `None`.
fn spec_binding_head_sym(kb: &KnowledgeBase, v: TermId) -> Option<Symbol> {
    match kb.get_term(v) {
        Term::Ref(s) => Some(*s),
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            Some(*functor)
        }
        _ => extract_sort_ref_sym(kb, &TermIdView(v)),
    }
}

/// The binding VALUE a `requires` application carries for `member`, when bound
/// (`requires Storage[C = P, Key = String]` binds `Key`).
fn spec_binding_value(kb: &KnowledgeBase, spec: TermId, member: &str) -> Option<TermId> {
    let Term::Fn { named_args, .. } = kb.get_term(spec) else { return None };
    named_args.iter().find(|(p, _)| kb.resolve_sym(*p) == member).map(|(_, v)| *v)
}

/// Normalize a `requires`-binding value LEAF to the plain TYPE shape (`Ref(s)`). A
/// structured binding has no plain normalization yet → `None` (the caller surfaces a
/// loud not-yet-supported error, never a silently wrong shape).
fn normalize_spec_binding_type(kb: &mut KnowledgeBase, v: TermId) -> Option<TermId> {
    let s = spec_binding_head_sym(kb, v)?;
    if matches!(kb.get_term(v), Term::Ref(_)) {
        return Some(v);
    }
    Some(kb.alloc(Term::Ref(s)))
}

/// WI-376: the base sort symbols of every spec a sort PROVIDES (`fact Spec[…]` /
/// `provides Spec[…]` → a `SortProvidesInfo` fact). Snapshot (the caller mutates `kb`), so
/// it returns owned symbols. Mirrors the provider-snapshot loop in
/// [`find_spec_op_for_provided_sort`].
fn provided_spec_base_syms(kb: &KnowledgeBase, recv_sort: Symbol) -> Vec<Symbol> {
    let mut specs: Vec<Symbol> = Vec::new();
    let Some(provides_sym) = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") else {
        return specs;
    };
    for rid in kb.rules_by_functor(provides_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &named, "sort_ref") else { continue };
        let Some(carrier) = super::load::sort_ref_functor(kb, sr) else { continue };
        if !same_symbol(kb, carrier, recv_sort) {
            continue;
        }
        let Some(spec_t) = get_named_arg(kb, &named, "spec") else { continue };
        if let Some(spec_sym) = super::load::provides_spec_base_sym(kb, spec_t) {
            if !specs.contains(&spec_sym) {
                specs.push(spec_sym);
            }
        }
    }
    specs
}

/// A loud [`TypeError`] for an ill-formed / unsupported type projection.
/// WI-399: the error context is now THREADED (was hardcoded `OperationReturn`) so a
/// projection eliminated at a non-call site reports the right place — a `let`-binding
/// annotation (`LetBinding`), not a phantom operation return. The op-call callers
/// (`check_apply_iter`) still pass `OperationReturn`, preserving their message.
fn projection_type_error(ctx: &TypeErrorContext, span: Option<Span>, msg: &str) -> TypeError {
    TypeError::Other {
        span,
        context: ctx.clone(),
        expected: "a well-formed type projection".to_owned(),
        actual: msg.to_owned(),
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
/// WI-424 — a parametric sort's declared type parameters as `(param symbol,
/// canonical Var term)` pairs, source order — the same shape an operation's own
/// `type_params` take, so [`rigidify_op_type_params`] consumes either. The Var
/// term is the loader-cached canonical param var (`resolve_sort_alias` of the
/// qualified param name); a param whose alias is not a plain `Global` var
/// (a constrained / structured param) is skipped. Empty for a non-sort or
/// non-parametric `sort_sym`. Memoized on `kb.sort_param_pairs_cache` — the
/// uncached computation walks the symbol table per call, and this is consulted
/// per apply call site (receiver classification) and per eval dispatch.
fn sort_type_params_as_pairs(kb: &KnowledgeBase, sort_sym: Symbol) -> Rc<Vec<(Symbol, TermId)>> {
    if let Some(cached) = kb.sort_param_pairs_cache.borrow().get(&sort_sym) {
        return cached.clone();
    }
    let qn = kb.qualified_name_of(sort_sym).to_string();
    let pairs: Vec<(Symbol, TermId)> = kb
        .type_params_of_sort(sort_sym)
        .iter()
        .filter_map(|name| {
            let qualified_sym = kb.try_resolve_symbol(&format!("{qn}.{name}"))?;
            let target = resolve_sort_alias(kb, qualified_sym)?;
            matches!(kb.get_term(target), Term::Var(Var::Global(_)))
                .then_some((qualified_sym, target))
        })
        .collect();
    let rc = Rc::new(pairs);
    kb.sort_param_pairs_cache.borrow_mut().insert(sort_sym, rc.clone());
    rc
}

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
                    // Substitute the scrutinee's type args into the
                    // constructor's declared field types. For `case some(name)`
                    // over `Option[T = String]`, `some.value`'s declared type
                    // `T` resolves to `String` — without this `name` binds to
                    // the raw type-param term and surfaces as a bare `TermId`
                    // in later return-type checks.
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
                    // POSITIONAL sub-patterns: zip against field types by index.
                    for (i, sub_pat) in sub_patterns.iter().enumerate() {
                        // WI-342: the field type is a carrier-agnostic `Value`
                        // (`entity_field_types`); resolve its sort-level type
                        // params through the pattern subst without re-grounding.
                        // Deep-walk: a parameterized field type
                        // (`source: Stream[T = T, E = E]`) carries its type
                        // params NESTED in the `Fn`, which the shallow
                        // `walk_type_value` left unsubstituted — so the
                        // destructure did not thread the scrutinee's element /
                        // effect into the sub-pattern var (WI-413).
                        let field_type = match (field_types.as_ref().and_then(|f| f.get(i)), &subst) {
                            (Some((_, ty)), Some(s)) => Some(walk_pattern_field_type_deep(kb, s, ty)),
                            (Some((_, ty)), None) => Some(ty.clone()),
                            (None, _) => None,
                        };
                        extend_env_from_pattern(kb, env, *sub_pat, field_type);
                    }
                    // WI-445: NAMED sub-patterns (`case Box(v: some(x))`) bind by
                    // FIELD NAME — order-independent, so robust to declaration
                    // order. The loader preserves them as `named:
                    // List[NamedPattern]` (raw at load, since the entity's fields
                    // may not be registered yet); the field type is resolved here,
                    // where the typer pass always has the entity in hand.
                    if let Some(named_tid) = get_named_arg(kb, &named_args, "named") {
                        for np in list_to_vec(kb, named_tid) {
                            let Some((field_sym, sub_pat)) =
                                super::node_occurrence::read_named_pattern_term(kb, np)
                            else { continue };
                            let found = field_types
                                .as_ref()
                                .and_then(|fields| fields.iter().find(|(fname, _)| *fname == field_sym));
                            let field_type = match (found, &subst) {
                                (Some((_, ty)), Some(s)) => Some(walk_pattern_field_type_deep(kb, s, ty)),
                                (Some((_, ty)), None) => Some(ty.clone()),
                                (None, _) => None,
                            };
                            extend_env_from_pattern(kb, env, sub_pat, field_type);
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
/// WI-400 — the ζ (receiver σ-equality) decision for an expression-carried projection
/// at the type-relation boundary, shared by `unify_types` and the `types_compatible`
/// (subtype) dispatchers so the two relations treat a neutral identically (the design's
/// "refuse a bare projection symmetrically").
///
/// A projection that reaches a type relation is a NEUTRAL: δ-grounding already ran at the
/// env-bearing site (operation call / `let` / operation body-binding) and could not make
/// the member manifest (an abstract receiver), so the rigid `ExprCarried` survived. Returns
/// `Some(verdict)` when at least one side is an `ExprCarried` head, `None` when neither is
/// (the caller continues its ordinary structural dispatch). The verdict:
///
///   - **both neutral** — equal iff they project the SAME member off σ-EQUAL receivers: a
///     structural CHECK, never a binding. `ExprCarried` is a NON-INJECTIVE head
///     (`peek(a).T` and `peek(b).T` may both be `Int64` without `a = b`), so the relation
///     must NOT decompose `p.M =?= q.M` into `p =?= q`. The base scope compares receivers
///     structurally (eager let-alias canonicalization at the formation site is the deferred
///     increment that makes `let y = z ⟹ y.M ≡ z.M`; the union-find-over-σ generality is
///     the deferred flexible / rule-body case);
///   - **one neutral, one concrete** — a rigid abstract type is neither sub- nor
///     super-type of a concrete type, so refused (`expected String, got s.cell.T`). The
///     inference wildcards (`type_var` / `nothing`) are handled by the callers BEFORE this,
///     so a neutral still flows into an unconstrained var for inference.
///
/// Design: path-dependent-types.md §4 (ζ/δ/η), §4.1.
fn expr_carried_zeta<A: TermView, B: TermView>(kb: &KnowledgeBase, a: &A, b: &B) -> Option<bool> {
    // WI-428: a `RigidTypeProjection` (`P.Key`, the type-keyed neutral) is the second
    // neutral kind, treated exactly like `ExprCarried` at the relation boundary: two
    // rigid projections are equal iff same member off the same subject under the same
    // declaring sort (a structural CHECK — non-injective, never decomposed into a
    // subject unification); a neutral never equals a concrete type; the two neutral
    // KINDS never equal each other (an expression-keyed and a type-keyed neutral have
    // no conversion in the base scope — δ-normalization across kinds is the recorded
    // §5.3 convergence).
    let a_neutral = matches!(type_head(kb, a), TypeHead::ExprCarried | TypeHead::RigidProjection);
    let b_neutral = matches!(type_head(kb, b), TypeHead::ExprCarried | TypeHead::RigidProjection);
    if !a_neutral && !b_neutral {
        return None;
    }
    if a_neutral && b_neutral {
        match (extract_type(kb, a), extract_type(kb, b)) {
            (
                TypeExtractor::ExprCarried { value: va, member: ma },
                TypeExtractor::ExprCarried { value: vb, member: mb },
            ) => {
                return Some(same_symbol(kb, ma, mb) && va.structural_eq(&vb));
            }
            (
                TypeExtractor::RigidTypeProjection { sort: sa, subject: va, member: ma },
                TypeExtractor::RigidTypeProjection { sort: sb, subject: vb, member: mb },
            ) => {
                // Subject identity via [`SubjectKey`] (the param's alias-var id), NOT
                // raw term identity: two occurrences of one projection may carry Refs
                // to DIFFERENT symbol registrations of the same param (the inner
                // self-named `ns.W.P.P` vs the outer `ns.W.P`).
                let subjects_eq = match (&va, &vb) {
                    (Value::Term(ta), Value::Term(tb)) => {
                        match (subject_key_of_term(kb, *ta), subject_key_of_term(kb, *tb)) {
                            (Some(ka), Some(kb2)) => subject_keys_equal(kb, ka, kb2),
                            _ => va.structural_eq(&vb),
                        }
                    }
                    _ => va.structural_eq(&vb),
                };
                return Some(
                    same_symbol(kb, ma, mb) && same_symbol(kb, sa, sb) && subjects_eq,
                );
            }
            _ => return Some(false),
        }
    }
    Some(false)
}

pub fn unify_types<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    let a = walk_view(kb, subst, a);
    let b = walk_view(kb, subst, b);

    // Identity fast-path. A hash-consed `TermId` carrier has O(1) structural eq
    // (shared id ⇒ equal). WI-470: an occurrence-carried type (now the primary
    // arrow/row form) recovers a cheap fast-path via `Rc::ptr_eq` — two slots
    // holding the SAME occurrence are trivially unifiable. This catches shared
    // spines (the common case: one inferred type threaded to two sites) without
    // materializing; structurally-distinct-but-equal Node arrows fall through to
    // the carrier-agnostic structural arms below (correct, just not O(1)).
    match (&a, &b) {
        (Value::Term(x), Value::Term(y)) if x == y => return true,
        (Value::Node(x), Value::Node(y)) if Rc::ptr_eq(x, y) => return true,
        _ => {}
    }

    // Var arms — a logic var may be a hash-consed `Term::Var(Global)` or a
    // `Value::Var(Global)`; bind the other side by its carrier.
    if let Some(vid) = resolved_var(kb, &a) {
        return bind_resolved(kb, subst, vid, b);
    }
    if let Some(vid) = resolved_var(kb, &b) {
        return bind_resolved(kb, subst, vid, a);
    }

    // WI-399: an un-eliminated expression-carried projection (`s.T` / `s.cell.T`)
    // must NEVER reach unification. Every projection is discharged at its typing
    // SITE — where the env resolves the receiver's type: an operation call
    // (`check_apply_iter`, via `param_to_arg_type`) or a `let` annotation
    // (`visit_type`, via the env's `var_bindings`). A projection head that survives
    // to here was reached from a site that does NOT yet eliminate (a rule body, a
    // higher-order apply) — so the receiver's type is not known at unification. Refuse
    // EXPLICITLY here rather than rely on the structural fallback below, which would
    // reach `types_compatible`'s `_ => false` only after treating the opaque
    // `ExprCarried` head as a plain term — making the "no un-eliminated projection
    // passes a type relation" invariant legible at the unify boundary the WI-399
    // design names. Placed AFTER the var arms so a var still binds (mirroring how the
    // subtype sibling `types_compatible` lets `type_var`/`nothing` win first): the two
    // relations refuse a bare projection symmetrically — there it is `_ => false` by
    // construction, here it is this guard.
    // WI-400 (ζ — the σ-equality arm, replacing the WI-399 safety-net guard).
    if let Some(verdict) = expr_carried_zeta(kb, &a, &b) {
        return verdict;
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
        // WI-441 (was the weaker WI-320 structural unify): a top-level row
        // pair takes the FULL row algorithm — the structural inner-unify was
        // order-sensitive over `merge`, rejecting equal rows written in
        // different binding orders (the two-row carriers' `{ES, EF}`).
        (Some("effects_rows"), Some("effects_rows")) => {
            unify_effect_rows(kb, subst, a, b)
        }
        // Mirrors `unify_term_dispatch`'s `_ => types_compatible(...)` — a unify of
        // any other (form-mismatched) pair falls back to the subtype check, which is
        // itself carrier-agnostic (no re-ground). WI-441: a pair with ONE
        // row-shaped side (a bare `open(?ρ)` row-var binding vs a rigid row
        // var; an `effects_rows` vs a bare expression) is a ROW comparison —
        // the generic fallback cannot equate `?ρ` with `open(?ρ)`.
        _ => {
            if value_is_row_shaped(kb, a) || value_is_row_shaped(kb, b) {
                unify_effect_rows(kb, subst, a, b)
            } else {
                types_compatible(kb, subst, a, b)
            }
        }
    }
}

/// WI-342: the sole `parameterized` unification, carrier-agnostic over
/// [`TermView`] — both the `TermId` dispatch (via [`TermIdView`]) and the
/// `Value` carrier route here. Bases unify via the generic [`unify_types`];
/// bindings are matched by param name (a-side bindings present on the b-side
/// must unify; b-only bindings are width-ignored).
/// The base of a parameterized type as a unifiable term (WI-453). A type-param base
/// — the marked carrier `F` of a `sort Spec[F[T]]`, var-backed by WI-452's
/// `SortAlias` — resolves to its backing `Var` so the parameterized unify can FILL
/// it (`F[T=A] ≟ Option[T=X]` ⟹ `F := Option` at a use-site; `F → skolem` at a
/// def-site, so `F[T=A] ≟ F[T=B]` stays a rigid decomposition). A concrete base
/// (`Option`, `List`) has no var-target SortAlias and stays `Ref(base)`. Only
/// reached when the two bases DIFFER (same-functor unify never needs the alias scan).
fn parameterized_base_term(kb: &mut KnowledgeBase, base: Symbol) -> TermId {
    let var = resolve_sort_alias(kb, base)
        .filter(|t| matches!(kb.get_term(*t), Term::Var(Var::Global(_))));
    var.unwrap_or_else(|| kb.alloc(Term::Ref(base)))
}

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
    // WI-453 (§5.4): when the two bases DIFFER, a type-param base (the marked
    // carrier `F`) resolves to its backing Var so `F[T=A] ≟ Option[T=X]` FILLS
    // `F := Option` (use-site) / skolem-compares (def-site). Same-functor unify
    // (`List ≟ List`, `F ≟ F`) takes the trivial Ref path — no alias scan.
    let (a_base_ty, b_base_ty) = if a_base == b_base {
        (kb.alloc(Term::Ref(a_base)), kb.alloc(Term::Ref(b_base)))
    } else {
        (parameterized_base_term(kb, a_base), parameterized_base_term(kb, b_base))
    };
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
    // Iterative + cycle-guarded (WI-417): follow a `Value::Var` binding chain via
    // `resolve_as_value`. A `Value::Term` defers to the (guarded) `walk_type`
    // path; an unbound var / non-var carrier ends the chain. A cyclic `Value::Var`
    // substitution returns a representative instead of recursing forever.
    let mut cur = val;
    let mut visited: SmallVec<[VarId; 4]> = SmallVec::new();
    loop {
        match cur {
            Value::Term(t) => return walk_term_to_resolved(kb, subst, t),
            Value::Var(Var::Global(vid)) => {
                if visited.contains(&vid) {
                    return Value::Var(Var::Global(vid));
                }
                match subst.resolve_as_value(vid) {
                    Some(bound) => {
                        visited.push(vid);
                        cur = bound.clone();
                    }
                    None => return Value::Var(Var::Global(vid)),
                }
            }
            other => return other,
        }
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
        // WI-302: a non-`Ref` carried value — a COMPOUND value FIELD-PATH
        // (`c.contents` / `result.a`, a `DotApply` chain) — compares by STRUCTURAL
        // equality of the two carried value occurrences. The value is opaque (it
        // INDEXES the type; there is no binding to unify, exactly as the `sa == sb`
        // Ref arm is plain identity), so two such denoteds are the same type iff their
        // value paths are structurally identical — `Modify[c.contents]` unifies with
        // `Modify[c.contents]` but not `Modify[d.contents]`. (A literal carried value
        // compares structurally too; a bound-name nested apply still needs alpha-aware
        // comparison — deferred, and `views_structurally_equal` conservatively refuses
        // it, never a wrong accept.)
        _ => {
            let value_key = kb.intern("value");
            match (a.named_arg(kb, value_key), b.named_arg(kb, value_key)) {
                (Some(va), Some(vb)) => views_structurally_equal(kb, &va, &vb),
                _ => false,
            }
        }
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
            // A `denoted`'s carried value is a VALUE reference — an `Expr::Ref` or a
            // WI-302 field-access path (`c.contents`, a `DotApply` chain over value
            // Refs + field names) — never a type var, so it cannot capture `vid`.
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
            // WI-397: the receiver occurrence + the ground `member` ref.
            TypeNode::ExprCarried { value, member } => child(kb, value) || child(kb, member),
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
            // WI-441 (was the WI-320 structural inner-unify): the FULL row
            // algorithm — the structural form was order-sensitive over
            // `merge`, rejecting equal rows written in different orders.
            unify_effect_rows(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        _ => {
            // WI-441: a pair with one ROW-shaped side (a bare `open(?ρ)`
            // binding vs a rigid row var, etc.) is a row comparison — see
            // the view-dispatch twin.
            if value_is_row_shaped(kb, &TermIdView(a_resolved))
                || value_is_row_shaped(kb, &TermIdView(b_resolved))
            {
                unify_effect_rows(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
            } else {
                types_compatible(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
            }
        }
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
    // WI-381: a sort_ref to a structured (ground) defined-type / alias resolves to its
    // underlying shape first — `IntStream` ⟹ `Stream[T = Int]` — so the alias's fixed
    // bindings are ENFORCED against the parameterized side instead of the bare ref
    // going all-fresh and silently dropping them. Re-dispatch through `unify_types`.
    if let Some(shape) = resolve_alias_shape(kb, sref_sym) {
        return unify_types(kb, subst, parameterized, &TermIdView(shape));
    }
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

/// Like [`walk_type`] but recurses into `Term::Fn` children so Var bindings propagate
/// into nested positions like `Option[T = Var(vid)]`. PURE σ-propagation: a NEUTRAL head
/// (`RigidProjection` / `ExprCarried`) is an inert leaf — the walk never σ-substitutes or
/// δ-grounds it (see [`walk_type_deep_g`]). The call-site result-resolve points use the
/// grounding sibling [`resolve_type_deep_value`]; internal unification keeps using the shallow
/// `walk_type` since the per-functor `unify_parameterized` / `unify_arrow` arms already
/// recurse structurally.
fn walk_type_deep(kb: &mut KnowledgeBase, subst: &Substitution, ty: TermId) -> TermId {
    walk_type_deep_g(kb, subst, ty, false)
}

/// WI-453 (§5.4 concrete fill): if `functor` is a marked carrier (a type-param with a
/// `SortAlias → Var`, WI-452) that has FILLED to a CONCRETE sort through `subst`
/// (`F := Option`), return that sort. An unfilled / abstract / skolemized carrier — the
/// var resolves to itself, a rigid skolem, or another sort-param — yields `None`, so the
/// application keeps its symbol functor (def-site decomposition unaffected; the
/// undischarged fill surfaces as a loud no-instance error at dispatch, not here).
fn filled_carrier_sort(kb: &KnowledgeBase, subst: &Substitution, functor: Symbol) -> Option<Symbol> {
    let var_t = resolve_sort_alias(kb, functor)
        .filter(|t| matches!(kb.get_term(*t), Term::Var(Var::Global(_))))?;
    let walked = walk_type(kb, subst, var_t);
    let s = extract_sort_ref_sym(kb, &TermIdView(walked))?;
    if is_sort_param_symbol(kb, s) || kb.kind_of(s) != Some(crate::intern::SymbolKind::Sort) {
        return None;
    }
    Some(s)
}

/// Shared body of [`walk_type_deep`] (`ground = false`, pure σ) and the grounding entry
/// [`resolve_type_deep_value`] (`ground = true`). When `ground` is set, the call-time
/// concrete-fill (δ-reduction) applies: a `RigidProjection` whose subject has resolved
/// (through `subst`) to a CONCRETE sort grounds via [`ground_rigid_projection_if_concrete`]
/// (the §5.4 concrete fill ⟹ CHECK); an abstract-subject projection stays the rigid
/// neutral. Keeping that grounding OUT of the `ground = false` walk is what lets the
/// ordinary σ-walk (rigidify, effect resolution, goal canonicalization) never accidentally
/// ground — or σ-substitute through — a projection's identity slot.
fn walk_type_deep_g(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    ty: TermId,
    ground: bool,
) -> TermId {
    let resolved = walk_type(kb, subst, ty);
    match kb.get_term(resolved) {
        Term::Fn { .. } => {
            // PURE σ STOPS AT A NEUTRAL HEAD. A `RigidProjection`'s `subject` and an
            // `ExprCarried`'s receiver are IDENTITY slots — `expr_carried_zeta` compares
            // two neutrals by them STRUCTURALLY, never a unification position — and the
            // WI-392/424 rigidify pass must not rewrite them either (that would erase the
            // identity and the WI-400 non-injectivity `P.K ≢ Q.K`). So the deep walk
            // treats both as inert leaves. δ-grounding a CONCRETE-subject `RigidProjection`
            // (`P.V` with `P := CounterState` ⟹ `CounterState.V`, the §5.4 concrete fill ⟹
            // CHECK) happens ONLY when `ground` is set — i.e. through [`resolve_type_deep_value`]
            // at the call-site result-resolve points — never as a side effect of an
            // ordinary σ-walk.
            let head = type_head(kb, &TermIdView(resolved));
            if matches!(head, TypeHead::RigidProjection) {
                return if ground {
                    ground_rigid_projection_if_concrete(kb, subst, resolved).unwrap_or(resolved)
                } else {
                    resolved
                };
            }
            if matches!(head, TypeHead::ExprCarried) {
                return resolved;
            }
            // WI-453 (§5.4 concrete fill, INJECTIVE application): when grounding, a
            // parameterized type whose FUNCTOR is a marked carrier `F` filled to a
            // concrete sort `C` grounds its base — `F[T=A]` with `F := Option` ⟹
            // `Option[T=A]` (the table's `F := List` decomposition). Gated on `ground`
            // (the call-site result-resolve points), like the RigidProjection fill: a
            // pure σ walk leaves the symbol functor alone, so the def-site
            // `F[T=A] ≟ F[T=B]` decomposition (base-symbol equality) is untouched. Sound
            // because the application is injective — there is no non-injective neutral
            // identity to protect (that is the §5.3 projection, handled above).
            if ground {
                let functor = match kb.get_term(resolved) {
                    Term::Fn { functor, .. } => Some(*functor),
                    _ => None,
                };
                if let Some(c) = functor.and_then(|f| filled_carrier_sort(kb, subst, f)) {
                    let named: Vec<(Symbol, TermId)> = match kb.get_term(resolved) {
                        Term::Fn { named_args, .. } => {
                            named_args.iter().map(|(s, t)| (*s, *t)).collect()
                        }
                        _ => Vec::new(),
                    };
                    let walked: Vec<(Symbol, TermId)> = named
                        .into_iter()
                        .map(|(s, t)| (s, walk_type_deep_g(kb, subst, t, ground)))
                        .collect();
                    let base = kb.alloc(Term::Ref(c));
                    return kb.make_parameterized_type(base, &walked);
                }
            }
            kb.map_fn_children(resolved, |kb, child| walk_type_deep_g(kb, subst, child, ground))
        }
        _ => resolved,
    }
}

/// WI-383: δ-ground a `RigidProjection` when its subject has resolved (through `subst`) to
/// a CONCRETE sort — the call-time concrete-fill CHECK. The member resolves off the
/// carrier via [`project_type_member`] (including through the carrier's `provides` facts,
/// the WI-376 path). Returns `None` — leaving the projection the opaque rigid neutral —
/// when the subject is still abstract (a var / rigidify-pass rigid var / an enclosing
/// sort-param carrier, i.e. the §5.4 abstract fill ⟹ ADD/forward case) or when the member
/// does not ground off the carrier (the un-discharged requirement surfaces at the call's
/// own `requires` check, not here). Soundness: WI-400's rule forbids BINDING vars to force
/// `P.K ≡ Q.K`; reading a member off an ALREADY-concrete subject binds nothing.
fn ground_rigid_projection_if_concrete(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    proj: TermId,
) -> Option<TermId> {
    let TypeExtractor::RigidTypeProjection { sort, subject, member } =
        extract_type(kb, &TermIdView(proj))
    else {
        return None;
    };
    // WI-383: only an OPERATION-type-param projection grounds here (decl_sort = the op). A
    // SORT-type-param projection (decl_sort = a sort) keeps the WI-428 opacity untouched —
    // its grounding rides the existing eliminator path.
    if kb.kind_of(sort) != Some(crate::intern::SymbolKind::Operation) {
        return None;
    }
    // The subject `Ref` is a DISTINCT registration of the op type-param from the canonical
    // inference var the call binds (there is no `SortAlias` bridge for op type-params, so
    // `walk_type(subject)` lands on an unbound sibling var). Bridge by name to the op's own
    // `OperationInfo.type_params`, whose var IS the one arg-inference binds.
    let Value::Term(subj_t) = subject else { return None };
    let subj_sym = extract_sort_ref_sym(kb, &TermIdView(subj_t))?;
    let subj_name = kb.resolve_sym(subj_sym).to_owned();
    let rec = super::op_info::lookup_operation_info(kb, sort)?;
    let tp_var = rec
        .type_params
        .iter()
        .find(|(n, _)| kb.resolve_sym(*n) == subj_name)
        .map(|(_, v)| *v)?;
    let walked = walk_type(kb, subst, tp_var);
    let s = extract_sort_ref_sym(kb, &TermIdView(walked))?;
    // A genuine concrete sort only: never a sort-type-param (abstract carrier → forward),
    // and not an operation / other kind.
    if is_sort_param_symbol(kb, s)
        || kb.kind_of(s) != Some(crate::intern::SymbolKind::Sort)
    {
        return None;
    }
    // SOUND grounding (WI-383 /code-review): read `member` ONLY through a spec that
    // LICENSES this projection — an op `requires Spec[C = subject]` clause that declares
    // `member` and mentions the subject — AND that the carrier `s` actually PROVIDES; then
    // read `member`'s binding from THAT provision. NOT the spec-agnostic
    // `project_type_member` first-match over the carrier's provides: that read the member
    // off an arbitrary (possibly UNLICENSED) provided spec and made the result depend on
    // `provides` declaration order (two soundness holes). A carrier that does not provide
    // the licensing spec leaves the projection the opaque neutral — the requirement is
    // unmet and the call is rejected downstream, never silently ground to a wrong member.
    let member_str = kb.resolve_sym(member).to_owned();
    let key = subject_key_of_term(kb, subj_t)?;
    let mut mentions_subject = false;
    for e in op_requires_entries(kb, sort) {
        if !spec_mentions_key(kb, e.spec, key) {
            continue;
        }
        mentions_subject = true;
        if !kb.type_params_of_sort(e.required_sort).iter().any(|d| d.as_str() == member_str) {
            continue;
        }
        let Some(bindings) = provider_spec_view_bindings(kb, s, e.required_sort) else {
            continue;
        };
        let Some(bound) = bindings
            .iter()
            .find(|(n, _)| kb.resolve_sym(*n) == member_str)
            .map(|(_, b)| *b)
        else {
            continue;
        };
        // WI-391: the provider binding is the canonical `Ref(S)` shape, so the grounded
        // member walks directly (the late nullary-`Fn` normalization is retired).
        return Some(walk_type_deep(kb, subst, bound));
    }
    // WI-383 SELF-CARRIER (implicit licensing): no `requires` bound mentions the subject,
    // so the projection is self-licensed — `T.member` reads the carrier's OWN declared
    // `sort <member>` (the resource-declares-its-value-type tie). Ground only a MANIFEST
    // member (`sort V = Int64`, whose SortAlias target is a concrete sort); an abstract
    // `sort V = ?` (target a Var) or a carrier lacking the member stays the neutral
    // (rejected downstream). Gated on `!mentions_subject` so an EXTERNAL licensing bound
    // the carrier failed to provide is NEVER bypassed by reading the carrier's own member
    // (the Q3 soundness rule).
    if !mentions_subject {
        let member_qn = format!("{}.{}", kb.qualified_name_of(s).to_owned(), member_str);
        if let Some(member_sym) = kb.symbols.by_qualified_name.get(&member_qn).copied() {
            // Must be the carrier's OWN declared abstract-sort member (`sort <member> = …`):
            // a Sort symbol with an EXACT `SortAlias`. `resolve_sort_alias`'s short-name
            // FALLBACK is deliberately NOT used here — it would return an UNRELATED sort's
            // same-named member when this child is an entity/operation/body-sort that merely
            // shares the name (a soundness hole). `sort_alias_target_exact` matches only this
            // symbol.
            if kb.kind_of(member_sym) == Some(crate::intern::SymbolKind::Sort) {
                if let Some(target) = sort_alias_target_exact(kb, member_sym) {
                    let g = walk_type_deep(kb, subst, target);
                    // Ground ONLY a manifest member (`sort V = Int64`). An abstract
                    // `sort V = ?` (resolves to a Var) or a sibling-param alias
                    // (`sort V = W`, resolves to a sort-param ref) is NOT ground and stays
                    // the neutral (rejected downstream).
                    if type_value_is_ground(kb, g) {
                        // WI-391: the SortAlias target is the canonical `Ref(S)` shape
                        // (`type_expr_to_value`), so the manifest member grounds directly.
                        return Some(g);
                    }
                }
            }
        }
    }
    None
}

/// The `SortAlias` target for EXACTLY `sym` — the exact-match half of
/// [`resolve_sort_alias`] WITHOUT its short-name fallback. The self-carrier projection
/// grounding (`ground_rigid_projection_if_concrete`) must read the carrier's OWN declared
/// member; the fallback would return an unrelated sort's same-named member when the looked-
/// up child is not itself a `sort X = …` alias, grounding `T.member` to a wrong type.
fn sort_alias_target_exact(kb: &KnowledgeBase, sym: Symbol) -> Option<TermId> {
    let alias_sym = kb.try_resolve_symbol("SortAlias")?;
    for rid in kb.rules_by_functor(alias_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(head) = kb.fact_head_term(rid) else { continue };
        if let Term::Fn { pos_args, .. } = kb.get_term(head) {
            if pos_args.len() >= 2 {
                if let Term::Fn { functor, .. } = kb.get_term(pos_args[0]) {
                    if *functor == sym {
                        return Some(pos_args[1]);
                    }
                }
            }
        }
    }
    None
}

/// Walk a type term through the substitution, resolving Vars and type params.
///
/// Iterative (not recursive) so a CYCLIC substitution cannot overflow the host
/// stack. A cycle arises (WI-416) when two distinct `Var` instances of the
/// SAME sort-parameter cross-bind — e.g. typing `member(x, items)` from inside
/// a sort whose element unifies with `List.T` can leave `subst[a] = Var(b)`,
/// `subst[b] = Ref(Coll.T)`, and `SortAlias(Coll.T) = Var(a)`, so the chain
/// `a -> Ref -> a` never terminates. Every var in such a cycle is unified to
/// the same (here abstract) type, so on revisiting a var we stop and return the
/// current term — a sound representative of the equivalence class. The
/// `visited` set is a stack-local `SmallVec`; the overwhelmingly common chain
/// is 0–2 hops, so it never allocates and the linear `contains` is trivial.
fn walk_type(kb: &KnowledgeBase, subst: &Substitution, ty: TermId) -> TermId {
    let mut ty = ty;
    // 0–2 hops in practice; inline-4 never spills for any realistic alias chain.
    let mut visited: SmallVec<[VarId; 4]> = SmallVec::new();
    loop {
        if let Term::Var(Var::Global(vid)) = kb.get_term(ty) {
            let vid = *vid;
            if visited.contains(&vid) {
                return ty; // WI-416: cycle — `ty` is a representative.
            }
            match subst.resolve_as_value(vid) {
                Some(Value::Term(bound)) => {
                    visited.push(vid);
                    ty = *bound;
                    continue;
                }
                // Non-`Term` (a denoted `Value::Node`) or unbound: keep the var.
                // This term-only walker deliberately stops here; its carrier-aware
                // caller `walk_term_to_resolved` surfaces a `Value::Node` binding
                // afterward via `resolve_as_value`.
                _ => return ty,
            }
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
        let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) else {
            return alias_target;
        };
        let vid = *vid;
        if visited.contains(&vid) {
            return alias_target; // WI-416: cycle — the alias var represents it.
        }
        match subst.resolve_as_value(vid) {
            // Term-narrow (term-world alias chase): only a `Value::Term` binding
            // is a `TermId` this loop can chase; a non-`Term` carrier (a `Value::Node`
            // effect-row/occurrence binding) is not representable here, so the alias
            // var represents it — as before.
            Some(Value::Term(bound)) => {
                let bound = *bound;
                visited.push(vid);
                ty = bound;
                continue;
            }
            _ => return alias_target,
        }
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
pub(crate) fn resolve_sort_alias(kb: &KnowledgeBase, sym: Symbol) -> Option<TermId> {
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

/// WI-374 (§8.1, site-scoped): expand a FOREIGN bare/partial parametric sort
/// application in a callee-signature position to its full application form,
/// minting a FRESH logic var per unwritten declared parameter (type params
/// and effect-row params alike — an unbound plain var IS a row var). Runs
/// per call, so freshness is per application — two occurrences never alias
/// and the foreign sort's canonical vars stay untouched (§3 bullet 2).
///
/// Returns `None` (keep the form as written — today's behavior) when:
/// - the type is `Value::Node`-carried (rebuilding needs occurrence span
///   plumbing; the canonical channel still serves it),
/// - it is not a sort application, or the sort declares no parameters,
/// - it is the callee's OWN sort (the §3-bullet-1 member tie stays on the
///   canonical channel),
/// - every declared parameter is already written.
///
/// Scope: the TOP-LEVEL form of a param/return position only — a bare ref
/// NESTED inside a written binding (`Pair[B = List]`) is not yet expanded
/// (deliberate; deep expansion is follow-on scope). An alias resolves to its
/// shape first (WI-381), so only genuinely-open positions get fresh vars.
fn expand_foreign_sort_application(
    kb: &mut KnowledgeBase,
    ty: &Value,
    callee_parent_canon: Option<Symbol>,
) -> Option<Value> {
    if !matches!(ty, Value::Term(_)) {
        return None;
    }
    let (base, written) = sort_application_parts(kb, ty)?;
    if callee_parent_canon.is_some_and(|p| p == kb.canonical_sort_sym(base)) {
        return None;
    }
    // The WI-424 memoized pairs — `(qualified param sym, canonical Var term)`
    // — double as the declared-param list, so the per-call path never walks
    // the symbol table or SortAlias facts for an already-seen sort.
    let declared = sort_type_params_as_pairs(kb, base);
    if declared.is_empty() {
        return None;
    }
    let declared_syms: Vec<Symbol> = declared.iter().map(|(q, _)| *q).collect();
    let mut bindings: Vec<(Symbol, TermId)> = Vec::with_capacity(declared_syms.len());
    let mut filled = false;
    for qsym in declared_syms {
        let short = kb.resolve_sym(qsym).to_string();
        match written.iter().find(|(k, _)| kb.resolve_sym(*k) == short) {
            Some((k, v)) => match v {
                Value::Term(t) => bindings.push((*k, *t)),
                // A Term carrier's children are Term-carried; guard anyway.
                _ => return None,
            },
            None => {
                let var_sym = kb.intern(&format!("?{short}"));
                let vid = kb.fresh_var(var_sym);
                let var_t = kb.alloc(Term::Var(Var::Global(vid)));
                // The SHORT symbol — the named-arg key convention the
                // (parameterized, parameterized) unify matches on.
                let short_sym = kb.intern(&short);
                bindings.push((short_sym, var_t));
                filled = true;
            }
        }
    }
    if !filled {
        return None;
    }
    let base_ref = kb.make_sort_ref(base);
    Some(Value::Term(kb.make_parameterized_type(base_ref, &bindings)))
}

/// WI-374 (user-decided 2026-06-12): ENFORCE the §3-bullet-1 parametricity
/// tie — shared by the operation-call and constructor checkers. Scans the
/// per-var contradiction details recorded during argument/field unification;
/// a conflict on one of `owner_sort`'s OWN canonical param vars is an error
/// unless (a) its prior binding is one of the `exempt_rigids` (the WI-424
/// seeded body rigids — a same-sort sibling call at a different instance
/// keeps its pre-WI-374 acceptance; enforcing the rigid tie is a separate
/// decision), or (b) the pair RE-UNIFIES through the real relation (bare
/// `List` vs `List[T = Int64]`, wildcards, equal rows in different
/// carriers/orders are refinement — raw bind-level inequality over-reports).
/// A FOREIGN sort's var conflicting through two foreign-typed positions is
/// not scanned (§3 bullet 2: independent).
fn enforce_member_tie(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    owner_sort: Symbol,
    error_name: Symbol,
    span: Option<Span>,
    exempt_rigids: &[(VarId, TermId)],
) -> Result<(), TypeError> {
    if !subst.is_contradiction() || subst.contradiction_details.is_empty() {
        return Ok(());
    }
    // The WI-424 memoized pairs supply the owner's canonical param vids.
    let member_vids: SmallVec<[VarId; 4]> = sort_type_params_as_pairs(kb, owner_sort)
        .iter()
        .filter_map(|(_, target)| match kb.get_term(*target) {
            Term::Var(Var::Global(v)) => Some(*v),
            _ => None,
        })
        .collect();
    if member_vids.is_empty() {
        return Ok(());
    }
    let details = subst.contradiction_details.clone();
    for (vid, prior, attempted) in &details {
        if !member_vids.contains(vid) {
            continue;
        }
        if exempt_rigids
            .iter()
            .any(|(v, r)| v == vid && matches!(prior, Value::Term(t) if t == r))
        {
            continue;
        }
        // Walk both sides through the LIVE subst first — a recorded pair may
        // contain a var the call has since pinned (`Box[T = ?x]` with `?x`
        // later bound to Int64); re-testing the unwalked pair in an empty
        // scratch would spuriously re-unify and skip a genuine violation.
        let prior_w = walk_type_deep_value(kb, subst, prior);
        let attempted_w = walk_type_deep_value(kb, subst, attempted);
        let mut scratch = Substitution::new();
        if unify_types(kb, &mut scratch, &prior_w, &attempted_w) {
            continue;
        }
        return Err(TypeError::Other {
            span,
            context: TypeErrorContext::OperationTypeParams { op_name: error_name },
            expected: format!(
                "consistent bindings for the sort's shared type parameter (first bound to {})",
                type_display_name_value(kb, &prior_w),
            ),
            actual: type_display_name_value(kb, &attempted_w),
        });
    }
    Ok(())
}

/// WI-381: resolve a defined-type / alias reference (`SortRef(S)`) to its underlying
/// SHAPE — following alias chains to a finite shape — so the typer judges members and
/// ungrounded positions on the *resolved* shape, not the opaque alias
/// (`docs/design/expansion-during-unification.md` §1, §6 OQ6). `sort IntStream =
/// Stream[T = Int]` resolves to `Stream[T = Int]` (so `T = Int` is KEPT and the
/// unwritten `E` stays open); a chain `Top = Mid`, `Mid = List[T = Int]` follows
/// through to `List[T = Int]`.
///
/// Returns `None` — the alias stays opaque — when `sym` is NOT a structured alias to a
/// GROUND shape:
///   - it has no `SortAlias` fact (a plain sort);
///   - the target is a bare logical `Var` — an opaque sort (`sort Term = ?`) or a type
///     parameter (`sort T = ?`); collapsing it would lose the sort-ref form (cf.
///     [`walk_type`]);
///   - the alias chain CYCLES (`sort A = A`, `A = B`/`B = A`) — a malformed definition;
///     refuse rather than loop (callers re-dispatch on the result, so a partial cyclic
///     result would not terminate);
///   - the resolved shape is NOT ground — a PARAMETRIC alias (`sort PairKey =
///     Pair[?X1, ?X2]`) with open `?` leaves, or one mentioning a sort parameter. Its
///     per-use fresh-leaf instantiation is WI-374's per-call scheme machinery; until
///     then it stays opaque, which is sound (a conservative compat / abstract-receiver
///     result, never a wrong ground bind).
fn resolve_alias_shape(kb: &KnowledgeBase, sym: Symbol) -> Option<TermId> {
    let mut visited: Vec<Symbol> = vec![sym];
    let shape = resolve_alias_shape_chain(kb, sym, &mut visited)?;
    if !type_value_is_ground(kb, shape) {
        return None;
    }
    // WI-405: refuse a NON-WELL-FOUNDED alias — one whose ground shape transitively
    // references itself through a binding (`sort A = List[T = B]; sort B = List[T =
    // A]`). It has no finite expansion, so resolving it to a one-step shape and
    // re-dispatching through `types_compatible` (the WI-381 / WI-405 alias arms)
    // would recurse forever (a stack overflow on load). This generalizes
    // `resolve_alias_shape_chain`'s bare-ref cycle guard to DEEP structural cycles;
    // such an alias stays OPAQUE (a sound, terminating nominal comparison) exactly
    // as a bare-ref cycle does.
    if !alias_shape_well_founded(kb, shape, &mut vec![sym]) {
        return None;
    }
    Some(shape)
}

/// WI-405: a ground alias shape is WELL-FOUNDED iff fully expanding the aliases it
/// references — through bindings, recursively — terminates. `path` holds the alias
/// names on the current expansion path; encountering one already on the path is a
/// structural cycle (`sort A = List[T = B]; sort B = List[T = A]`), so the alias has
/// no finite shape. A non-alias sort-ref leaf, a logic var, or an atom is trivially
/// well-founded. The walk re-expands each alias reference with its own cycle
/// tracking, so it is robust to a bare-ref CHAIN that skipped intermediate names.
fn alias_shape_well_founded(kb: &KnowledgeBase, tid: TermId, path: &mut Vec<Symbol>) -> bool {
    // A bare sort-ref leaf (`Ref(S)` / nullary `Fn{S}`): expand if it names an alias.
    if let Some(s) = extract_sort_ref_sym(kb, &TermIdView(tid)) {
        return alias_sym_well_founded(kb, s, path);
    }
    // A parameterized / structural type: its base (the `Fn` functor) AND every
    // binding can name an alias, so check all of them. Collect the functor symbol
    // and child `TermId`s (cheap, `Copy`) so the immutable `kb` borrow from
    // `get_term` is released before the recursive calls re-borrow `kb`.
    let (functor, children): (Option<Symbol>, Vec<TermId>) = match kb.get_term(tid) {
        Term::Fn { functor, pos_args, named_args } => (
            Some(*functor),
            pos_args.iter().copied().chain(named_args.iter().map(|(_, a)| *a)).collect(),
        ),
        _ => return true,
    };
    if let Some(f) = functor {
        if !alias_sym_well_founded(kb, f, path) {
            return false;
        }
    }
    children.iter().all(|c| alias_shape_well_founded(kb, *c, path))
}

/// Expand a single sort symbol for [`alias_shape_well_founded`]: a non-alias name
/// bottoms out as well-founded; an alias is expanded under the path cycle guard
/// (revisiting a name already on the path = a structural cycle ⟹ not well-founded).
fn alias_sym_well_founded(kb: &KnowledgeBase, s: Symbol, path: &mut Vec<Symbol>) -> bool {
    let Some(target) = resolve_sort_alias(kb, s) else {
        return true;
    };
    if path.contains(&s) {
        return false;
    }
    path.push(s);
    let wf = alias_shape_well_founded(kb, target, path);
    path.pop();
    wf
}

/// The structural half of [`resolve_alias_shape`]: follow `SortAlias` (and bare-ref
/// chains) to a finite shape `TermId`. `None` for a non-alias, an alias whose target is
/// a logical `Var`, or a cyclic chain (`visited` guards revisits). A bare-ref target
/// to a NON-alias sort (`sort Top = List`) is itself the final shape.
fn resolve_alias_shape_chain(
    kb: &KnowledgeBase,
    sym: Symbol,
    visited: &mut Vec<Symbol>,
) -> Option<TermId> {
    let target = resolve_sort_alias(kb, sym)?;
    if matches!(kb.get_term(target), Term::Var(_)) {
        return None;
    }
    // A bare-ref target that NAMES another sort: if that sort is itself an alias, follow
    // the chain (`sort Top = Mid`); a revisit is a cycle → refuse. If it is NOT an alias
    // (`sort Top = List`), `target` (the bare ref) is the final shape. A parameterized
    // target (`List[T = Int]`) names its base sort, which is not an alias — same path
    // keeps `target`.
    if let Some(next) = extract_sort_ref_sym(kb, &TermIdView(target)) {
        if resolve_sort_alias(kb, next).is_some() {
            if visited.contains(&next) {
                return None;
            }
            visited.push(next);
            return resolve_alias_shape_chain(kb, next, visited);
        }
    }
    Some(target)
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
) -> Option<(Vec<Value>, Vec<TermId>, Vec<Value>)> {
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
            None => return Some((Vec::new(), Vec::new(), Vec::new())),
        }
    } else if value_is_bare_effect_expr(kb, &walked) {
        // WI-441: a BARE EffectExpression node (`open(?ρ)` — a row var's
        // BINDING shape from `bind_row_tail`; a `merge(…)` a bound row var
        // walked to) is the row's inner expression itself.
        walked.clone()
    } else {
        // Not an effects_rows wrapper — a bare row Var is itself an open-tail
        // row (mostly partial arrows in tests); anything else is empty.
        match row_tail_termid(kb, &walked) {
            Some(t) => return Some((Vec::new(), vec![t], Vec::new())),
            None => return Some((Vec::new(), Vec::new(), Vec::new())),
        }
    };

    let mut present: Vec<Value> = Vec::new();
    let mut absent: Vec<Value> = Vec::new();
    let mut tails: Vec<TermId> = Vec::new();
    let mut stack: Vec<Value> = vec![expr];
    while let Some(node_raw) = stack.pop() {
        let node = walk_value_to_resolved(kb, subst, node_raw);

        // Unbound Var directly inside the algebra — a row-tail (any flavor;
        // a `TermId`-carried Rigid/DeBruijn is preserved as before).
        if let Some(node_tail) = row_tail_termid(kb, &node) {
            // WI-441 (supersedes the WI-339 F13 two-tail reject): MULTIPLE
            // distinct row tails are a legitimate row UNION — the merge of
            // two row variables (`{E, EffP}`, the lazy combinators' result
            // row). Collected deduped; the unify/subtype arms decide what
            // they can soundly do with a multi-tail row.
            if !tails.contains(&node_tail) {
                tails.push(node_tail);
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

    Some((present, tails, absent))
}

/// WI-441: the multi-tail arm shared by [`unify_effect_rows`] and
/// [`subtype_effect_rows`] — at least one side decomposed to ≥ 2 row tails
/// (a row UNION like `{E, EffP}`). Two sound moves, else reject:
///
/// 1. **Equal tail sets** (walked): the rows agree on the open part; the
///    relation holds iff the label extras allow it (`only_a` empty; for the
///    symmetric unify also `only_b`).
/// 2. **Bare-flexible absorb**: a side that is a SINGLE flexible tail with
///    no labels/absents binds WHOLESALE to the other row's inner expression
///    (the receiver-binding shape: `collect`'s `Eff` := `{E, EffP}`).
///    Guarded by occurs (the other side's tails must not contain the var)
///    and the var's `lacks` (each absorbed present label is checked; lacks
///    are propagated onto the absorbed row's flexible tails).
fn multi_tail_rows_compat(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_inner: Option<Value>,
    b_inner: Option<Value>,
    a_parts: (&[Value], &[TermId], &[Value]),
    b_parts: (&[Value], &[TermId], &[Value]),
    only_a: &[Value],
    only_b: &[Value],
    directional: bool,
) -> bool {
    let (a_present, a_tails, a_absent) = a_parts;
    let (b_present, b_tails, b_absent) = b_parts;
    let mut a_set: Vec<TermId> = a_tails.iter().map(|t| walk_type(kb, subst, *t)).collect();
    let mut b_set: Vec<TermId> = b_tails.iter().map(|t| walk_type(kb, subst, *t)).collect();
    a_set.sort_unstable_by_key(|t| t.raw());
    a_set.dedup();
    b_set.sort_unstable_by_key(|t| t.raw());
    b_set.dedup();
    if a_set == b_set {
        return if directional {
            only_a.is_empty()
        } else {
            only_a.is_empty() && only_b.is_empty()
        };
    }
    let absorb = |kb: &mut KnowledgeBase,
                  subst: &mut Substitution,
                  bare_tail: TermId,
                  other_inner: &Option<Value>,
                  other_present: &[Value],
                  other_tails: &[TermId]|
     -> bool {
        let Term::Var(Var::Global(vid)) = kb.get_term(bare_tail) else {
            return false;
        };
        let vid = *vid;
        if other_tails.iter().any(|t| walk_type(kb, subst, *t) == bare_tail) {
            return false; // occurs guard
        }
        let Some(inner) = other_inner else { return false };
        let lacks = subst.lacks_of(vid);
        if !lacks.is_empty() {
            for l in other_present {
                if label_violates_lacks(kb, subst, l, &lacks) {
                    return false;
                }
            }
            for t in other_tails {
                if let Term::Var(Var::Global(tvid)) = kb.get_term(*t) {
                    let tvid = *tvid;
                    subst.add_lacks(tvid, lacks.iter().cloned());
                }
                // A rigid tail can't carry the lacks — enforced at its own
                // instantiation site (same conservatism as the rigid-alias
                // arm in the single-tail case).
            }
        }
        subst.bind_value(vid, inner.clone());
        !subst.is_contradiction()
    };
    if a_present.is_empty() && a_absent.is_empty() && a_set.len() == 1 {
        return absorb(kb, subst, a_set[0], &b_inner, b_present, b_tails);
    }
    if b_present.is_empty() && b_absent.is_empty() && b_set.len() == 1 {
        return absorb(kb, subst, b_set[0], &a_inner, a_present, a_tails);
    }
    false
}

/// WI-441: is this value a BARE `EffectExpression` node (`merge` / `present` /
/// `absent` / `open` / `empty_row`, matched by QUALIFIED functor)? A row var's
/// binding (`open(?ρ)` from `bind_row_tail`) and a walked bound row are bare
/// expressions, not `effects_rows` wrappers.
fn value_is_bare_effect_expr(kb: &KnowledgeBase, v: &impl TermView) -> bool {
    match v.head(kb) {
        ViewHead::Functor { functor: Some(sym), .. } => {
            let qn = kb.qualified_name_of(sym);
            matches!(
                qn.strip_prefix("anthill.prelude.EffectExpression."),
                Some("merge" | "present" | "absent" | "open" | "empty_row")
            )
        }
        _ => false,
    }
}

/// WI-441: row-shaped = an `effects_rows` wrapper OR a bare `EffectExpression`
/// node. A pair with a row-shaped side must compare via the FULL row algebra
/// (`unify_effect_rows` / `subtype_effect_rows`) — the structural fallback is
/// order-sensitive over `merge` and cannot equate `?ρ` with `open(?ρ)`.
fn value_is_row_shaped(kb: &KnowledgeBase, v: &impl TermView) -> bool {
    if value_is_bare_effect_expr(kb, v) {
        return true;
    }
    matches!(
        v.head(kb),
        ViewHead::Functor { functor: Some(sym), .. }
            if kb.qualified_name_of(sym) == "anthill.prelude.TypeExtractor.EffectsRows"
    )
}

/// WI-441: a row value's INNER `EffectExpression` (the `effects_expr` child of
/// the `effects_rows` wrapper; a bare row Var / bare expression is itself the
/// inner). Used by the multi-tail wholesale absorb to bind a bare row var to
/// the OTHER row as-is — reassembling from decomposed parts cannot represent
/// two tails canonically.
fn row_inner_value(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    row: &impl TermView,
) -> Option<Value> {
    let effects_expr_key = kb.intern("effects_expr");
    let walked = walk_view(kb, subst, row);
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
    let is_wrapper = matches!(
        walked.head(kb),
        ViewHead::Functor { functor: Some(f), .. } if Some(f) == effects_rows_sym
    );
    if is_wrapper {
        named_child_value(kb, &walked, effects_expr_key)
    } else {
        Some(walked)
    }
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
    let (a_present, a_tails, a_absent) = match decompose_effect_row(kb, subst, a_effects) {
        Some(p) => p,
        None => return false,
    };
    let (b_present, b_tails, b_absent) = match decompose_effect_row(kb, subst, b_effects) {
        Some(p) => p,
        None => return false,
    };

    // WI-328: register each side's `- e` absents as `lacks` constraints on
    // that side's tail(s) BEFORE the tail-binding step, so `bind_row_tail`
    // sees them when it checks the labels flowing into each tail.
    for &t in &a_tails {
        register_row_lacks(kb, subst, Some(t), &a_absent);
    }
    for &t in &b_tails {
        register_row_lacks(kb, subst, Some(t), &b_absent);
    }

    let (only_a, only_b) = pair_present_labels(kb, subst, &a_present, &b_present);

    // WI-441: a row UNION (≥ 2 tails, `{E, EffP}`) takes the dedicated
    // multi-tail arm — equal tail sets or the bare-flexible wholesale absorb.
    if a_tails.len() > 1 || b_tails.len() > 1 {
        let a_inner = row_inner_value(kb, subst, a_effects);
        let b_inner = row_inner_value(kb, subst, b_effects);
        return multi_tail_rows_compat(
            kb, subst, a_inner, b_inner,
            (&a_present, &a_tails, &a_absent),
            (&b_present, &b_tails, &b_absent),
            &only_a, &only_b, false,
        );
    }
    let a_tail = a_tails.first().copied();
    let b_tail = b_tails.first().copied();

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
            // WI-441: tail-to-tail aliasing when ONE side's tail is a RIGID
            // (forall-Skolem) row var — the FORWARDING shape (`find(rest,
            // pred)` / `Stream.find(iterator(c), pred)` passes the enclosing
            // op's callback straight through, its row tail rigidified by the
            // body check). The rigid is un-bindable (WI-336), so the
            // symmetric fresh-tail step below would fail and leave the
            // callee's row param unconstrained. With no extras to push INTO
            // the rigid side, the flexible tail simply ALIASES the rigid
            // (a flexible var solves TO a rigid, the ordinary direction).
            // Note: the flexible side's lacks are not propagated onto the
            // rigid continuation (`bind_row_tail` propagates onto `Global`
            // continuations only) — the rigid's constraints are enforced at
            // its own instantiation site.
            let a_rigid = matches!(kb.get_term(a_walked), Term::Var(Var::Rigid(_)));
            let b_rigid = matches!(kb.get_term(b_walked), Term::Var(Var::Rigid(_)));
            match (a_rigid, b_rigid) {
                (true, false) if only_b.is_empty() => {
                    return bind_row_tail(kb, subst, b_walked, &only_a, Some(a_walked));
                }
                (false, true) if only_a.is_empty() => {
                    return bind_row_tail(kb, subst, a_walked, &only_b, Some(b_walked));
                }
                // Two DISTINCT rigids (the a_walked == b_walked case returned
                // above) never alias; a rigid that must absorb extras fails.
                (true, _) | (_, true) => return false,
                (false, false) => {}
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
    let (a_present, a_tails, a_absent) =
        match decompose_effect_row(kb, subst, actual_effects) {
            Some(p) => p,
            None => return false,
        };
    let (e_present, e_tails, e_absent) =
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
    for &t in &a_tails {
        register_row_lacks(kb, subst, Some(t), &a_absent);
    }
    for &t in &e_tails {
        register_row_lacks(kb, subst, Some(t), &e_absent);
    }

    // WI-326 F1 (code-review): use the covering variant (existential), NOT
    // the unify-shaped 1-to-1 [`pair_present_labels`]. Set semantics with
    // element subtyping lets one expected label cover multiple actuals —
    // e.g. `{red, blue} <: {Color}` where both `red`, `blue` are entities
    // of `Color`. The 1-to-1 pairing would mark `Color` matched after the
    // first hit and reject the second.
    let (only_a, only_e) = cover_present_labels(kb, subst, &a_present, &e_present);

    // WI-441: row UNIONS (≥ 2 tails) take the multi-tail arm (directional).
    if a_tails.len() > 1 || e_tails.len() > 1 {
        let a_inner = row_inner_value(kb, subst, actual_effects);
        let e_inner = row_inner_value(kb, subst, expected_effects);
        return multi_tail_rows_compat(
            kb, subst, a_inner, e_inner,
            (&a_present, &a_tails, &a_absent),
            (&e_present, &e_tails, &e_absent),
            &only_a, &only_e, true,
        );
    }
    let a_tail = a_tails.first().copied();
    let e_tail = e_tails.first().copied();

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
            // WI-441: tail-to-tail aliasing when one tail is RIGID — see the
            // analogous arm in `unify_effect_rows` (the forwarding shape).
            // actual ⊆ expected: a rigid ACTUAL tail can't absorb expected's
            // extras (require none), the flexible expected tail aliases it;
            // symmetric for a rigid EXPECTED tail.
            let a_rigid = matches!(kb.get_term(a_walked), Term::Var(Var::Rigid(_)));
            let e_rigid = matches!(kb.get_term(e_walked), Term::Var(Var::Rigid(_)));
            match (a_rigid, e_rigid) {
                (true, false) if only_e.is_empty() => {
                    return bind_row_tail(kb, subst, e_walked, &only_a, Some(a_walked));
                }
                (false, true) if only_a.is_empty() => {
                    return bind_row_tail(kb, subst, a_walked, &only_e, Some(e_walked));
                }
                (true, _) | (_, true) => return false,
                (false, false) => {}
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

    // WI-400 (ζ): a neutral projection is its own rigid type — equal only to an identical
    // neutral, never to a concrete type. Placed AFTER the type_var / nothing wildcards so
    // a neutral still flows into an unconstrained var for inference.
    if let Some(verdict) = expr_carried_zeta(kb, &TermIdView(actual), &TermIdView(expected)) {
        return verdict;
    }

    match (actual_functor, expected_functor) {
        (Some("sort_ref"), Some("sort_ref")) => {
            // Nominal / entity-subtyping / refines, then WI-344 provider
            // admissibility: a value of a bare carrier sort is usable
            // where a bare spec it provides is expected. Confined to the
            // bare↔bare arm so it never rides the `sort_ref ↔ parameterized`
            // base check and drops a parameterized spec's bindings — see
            // `sort_provides_admissibly`.
            if sort_ref_compatible(kb, actual, expected) {
                return true;
            }
            if let (Some(a), Some(e)) = (
                extract_sort_ref_sym(kb, &TermIdView(actual)),
                extract_sort_ref_sym(kb, &TermIdView(expected)),
            ) {
                if sort_provides_admissibly(kb, a, e) {
                    return true;
                }
            }
            // WI-405 FACET B: resolve a structured (ground) alias on EITHER side and
            // re-dispatch — so two aliases of the same shape (`sort IntList = List[T =
            // Int64]; sort IntList2 = List[T = Int64]`) compare by their underlying shapes,
            // not by nominal NAME only. WI-381 wired alias resolution into the
            // bare↔parameterized arms but NOT here; this applies it UNIFORMLY (the WI-405
            // root cause). Reached only after the nominal + provider checks fail (a pure
            // loosening). Each re-dispatch runs on a PROBE clone committed only on success,
            // so a failed branch can never leak partial bindings into the next branch or the
            // caller (mirrors `bare_provider_binding_precise`); the bare↔bare comparison is
            // ground-vs-ground, so a success commits no new bindings anyway. Termination:
            // `resolve_alias_shape` is `None` for a non-alias AND (WI-405) for a
            // non-well-founded recursive alias, so the recursion bottoms out.
            for (shape_side, other, shape_is_actual) in [
                (actual, expected, true),
                (expected, actual, false),
            ] {
                if let Some(shape) =
                    extract_sort_ref_sym(kb, &TermIdView(shape_side)).and_then(|s| resolve_alias_shape(kb, s))
                {
                    let mut probe = subst.clone();
                    let ok = if shape_is_actual {
                        types_compatible(kb, &mut probe, &TermIdView(shape), &TermIdView(other))
                    } else {
                        types_compatible(kb, &mut probe, &TermIdView(other), &TermIdView(shape))
                    };
                    if ok {
                        *subst = probe;
                        return true;
                    }
                }
            }
            false
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
            // WI-381: a structured (ground) defined-type / alias on the bare side
            // resolves to its underlying shape and re-dispatches as parameterized — so
            // `IntList` vs `List[T = Int]` CHECKS the bindings (`T = Int` kept) and an
            // `IntList` value conforms to its own definition. Without this, the
            // bare↔param arm below checks base-sort nominal compat ONLY, dropping the
            // alias's fixed bindings.
            if let Some(shape) =
                extract_sort_ref_sym(kb, &TermIdView(actual)).and_then(|s| resolve_alias_shape(kb, s))
            {
                return types_compatible(kb, subst, &TermIdView(shape), &TermIdView(expected));
            }
            // bare `S` vs `B[…]`: nominal base-sort compatibility, then (WI-402)
            // BINDING-PRECISE provider admissibility — a concrete carrier vs a
            // parameterized spec it provides checks every expected binding against
            // the provider fact's value, so the bindings are never dropped (the
            // hazard that confines the bare-spec accept to the bare↔bare arm
            // above). WI-361: `parameterized_base_sym` reads the base sort
            // form-agnostically (deep `base` field or the term-backed functor).
            match (extract_sort_ref_sym(kb, &TermIdView(actual)), parameterized_base_sym(kb, expected)) {
                (Some(a), Some(eb)) => {
                    sort_sym_compatible(kb, a, eb)
                        || bare_provider_binding_precise(kb, subst, a, &TermIdView(expected))
                }
                _ => false,
            }
        }
        (Some("parameterized"), Some("sort_ref")) => {
            // WI-381: mirror — resolve a structured alias on the bare (expected) side.
            if let Some(shape) =
                extract_sort_ref_sym(kb, &TermIdView(expected)).and_then(|s| resolve_alias_shape(kb, s))
            {
                return types_compatible(kb, subst, &TermIdView(actual), &TermIdView(shape));
            }
            match (extract_sort_ref_sym(kb, &TermIdView(expected)), parameterized_base_sym(kb, actual)) {
                // WI-405 FACET A: a parameterized carrier `S[bindings]` — including a
                // PARTIAL form such as a constructor result `S[A = ?_]` — conforms to a
                // BARE provider spec it provides. `sort_provides_admissibly` is base-only,
                // which is sound here precisely because the expected spec is bare (it
                // carries no bindings to drop) — the same reasoning that confines the
                // WI-344 accept to the bare↔bare arm. Applying it here too makes provider
                // admissibility UNIFORM across the dispatch arms (the WI-405 root cause).
                //
                // WI-466: the parameterized side is the ACTUAL, the sort_ref side the
                // EXPECTED, so the nominal check is `sort_sym_compatible(actual=ab,
                // expected=e)` — matching the `(sort_ref, parameterized)` sibling arm and
                // the `sort_provides_admissibly(ab, e)` beside it. The pre-WI-466 call
                // passed `(e, ab)` (swapped): it (1) false-REJECTED a parameterized actual
                // whose base refines/is-entity-of the bare expected (`Refined[T=Int64]` vs
                // `Base` where `Refined requires Base`), and (2) false-ACCEPTED the reverse
                // (a `Base[..]` where an expected spec that refines `Base` was demanded) —
                // a soundness hole.
                (Some(e), Some(ab)) => {
                    sort_sym_compatible(kb, ab, e) || sort_provides_admissibly(kb, ab, e)
                }
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
        _ => {
            // WI-441: a pair with one ROW-shaped side (a bare `open(?ρ)` row
            // binding vs a rigid row var, a wrapper vs a bare expression) is
            // a row comparison — see the unify-dispatch twin.
            if value_is_row_shaped(kb, &TermIdView(actual))
                || value_is_row_shaped(kb, &TermIdView(expected))
            {
                subtype_effect_rows(kb, subst, &TermIdView(actual), &TermIdView(expected))
            } else {
                false
            }
        }
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

    // WI-400 (ζ): neutral projection — same decision as the term dispatch, carrier-
    // agnostic (a compound `a.b.T` rides a `Value::Node` ExprCarried, so it reaches here).
    if let Some(verdict) = expr_carried_zeta(kb, &a, &e) {
        return verdict;
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
        // Bare `S` vs `B[…]`: nominal base-sort compatibility, then WI-402
        // binding-precise provider admissibility (mirrors
        // `types_compatible_term_dispatch`). `sort_sym_compatible` takes
        // (sort_ref-side sym, parameterized-side base); `sort_functor_of_view`
        // surfaces the head sym for a `sort_ref` and the base for a `parameterized`.
        (Some("sort_ref"), Some("parameterized")) => {
            // WI-381: resolve a structured (ground) alias on the bare side and
            // re-dispatch — mirrors `types_compatible_term_dispatch` so the subtype
            // relation stays carrier-symmetric (the Node-carrier path must resolve
            // aliases just as the term path does, or an alias compared against a
            // denoted-bearing parameterized type would drop its fixed bindings).
            if let Some(shape) = sort_functor_of_view(kb, &a).and_then(|s| resolve_alias_shape(kb, s)) {
                return types_compatible(kb, subst, &TermIdView(shape), &e);
            }
            match (sort_functor_of_view(kb, &a), sort_functor_of_view(kb, &e)) {
                // Nominal base, then (WI-402) binding-precise provider admissibility —
                // mirrors the term dispatch so the relation stays carrier-symmetric.
                (Some(av), Some(eb)) => {
                    sort_sym_compatible(kb, av, eb)
                        || bare_provider_binding_precise(kb, subst, av, &e)
                }
                _ => false,
            }
        }
        (Some("parameterized"), Some("sort_ref")) => {
            // WI-381: mirror — resolve a structured alias on the bare (expected) side.
            if let Some(shape) = sort_functor_of_view(kb, &e).and_then(|s| resolve_alias_shape(kb, s)) {
                return types_compatible(kb, subst, &a, &TermIdView(shape));
            }
            match (sort_functor_of_view(kb, &e), sort_functor_of_view(kb, &a)) {
                // WI-405 FACET A: parameterized carrier vs bare provider spec — mirror the
                // term dispatch so provider admissibility stays carrier-symmetric.
                // WI-466: nominal check is `(actual=ab, expected=ev)` — the parameterized
                // side is the ACTUAL, the sort_ref the EXPECTED (the pre-WI-466 `(ev, ab)`
                // was swapped; see the term-dispatch twin for the two latent defects).
                (Some(ev), Some(ab)) => {
                    sort_sym_compatible(kb, ab, ev) || sort_provides_admissibly(kb, ab, ev)
                }
                _ => false,
            }
        }
        // WI-342: every non-false arm of `types_compatible_term_dispatch` now has a
        // carrier-agnostic peer above; any other pair is a form mismatch, which the
        // term dispatch also rejects (`_ => false`). No re-ground bridge.
        // WI-441 exception: one ROW-shaped side ⇒ a row comparison (see the
        // term-dispatch twin).
        _ => {
            if value_is_row_shaped(kb, &a) || value_is_row_shaped(kb, &e) {
                subtype_effect_rows(kb, subst, &a, &e)
            } else {
                false
            }
        }
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
    // WI-441: the provider view's binding values carry the CARRIER's canonical
    // param vars (`provides Stream[T = T, E = {ES, EF}]` holds MappedStream's
    // own ES/EF alias vars). Instantiate them through THIS actual instance's
    // bindings (ES := the instance's ES value, …) in the scratch subst, so the
    // per-param comparison below sees the instance's row, not the canon vars
    // (a two-row provision `{ES, EF}` cannot pair against the expected row's
    // tails without it — two-tail-to-two-tail pairing is ambiguous).
    if cross_sort_provider.is_some() {
        for (ap, av) in &actual_bindings {
            let q = format!(
                "{}.{}",
                kb.qualified_name_of(actual_base),
                kb.resolve_sym(*ap)
            );
            let Some(qsym) = kb.try_resolve_symbol(&q) else { continue };
            let Some(target) = resolve_sort_alias(kb, qsym) else { continue };
            let Term::Var(Var::Global(vid)) = kb.get_term(target) else { continue };
            let vid = *vid;
            if subst.resolve_as_value(vid).is_none() {
                subst.bind_value(vid, av.clone());
            }
        }
    }
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
                        // WI-461: the provider value carries the carrier's canonical param
                        // refs (`provides Stream[T, {}]` holds List's `T`), which the
                        // instantiation above bound to THIS instance's bindings. Resolve it
                        // through `subst` — deeply, so a `Ref(<carrier>.P)` chases its
                        // `SortAlias` var to the bound value (`l.T`) — before the variance
                        // check, so a concrete / NEUTRAL expected (`l.T`) compares against
                        // the instance's value, not the raw canon ref. (A type-VAR expected
                        // short-circuits via the wildcard either way, so the delivered
                        // cross-sort cases — wi387/wi424/wi441 — are unaffected; their
                        // expected bindings are vars.) Try the raw value first so this is
                        // strictly additive: the resolved form is a fallback that can only
                        // ACCEPT more, never reject what the raw value already accepted.
                        let mut probe = subst.clone();
                        if check_binding_by_variance(kb, &mut probe, expected_base, *param, &TermIdView(pv), ev) {
                            *subst = probe;
                            true
                        } else {
                            let pvr = walk_type_deep(kb, subst, pv);
                            pvr != pv
                                && check_binding_by_variance(kb, subst, expected_base, *param, &TermIdView(pvr), ev)
                        }
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
/// decides; failing both, two SAME-BASE parameterized types get a real
/// parameterized LUB built per-binding by declared variance (WI-464,
/// [`join_parameterized_same_base`]), and otherwise the nominal sides are widened
/// one level up the entity→enclosing-sort chain and retried. The climb is bounded
/// — each step strictly ascends or a side stops widening — so it terminates.
fn join_types(kb: &mut KnowledgeBase, a: Value, b: Value) -> Option<Value> {
    // WI-342: carrier-agnostic — `a`/`b` are `Value`s (a branch may be a
    // `Value::Node` lambda arrow). WI-464: the join RETURNS one of its inputs, or
    // (for two same-base parameterized types) CONSTRUCTS the parameterized LUB
    // recursively, or widens a nominal side up the lattice. `types_compatible` is
    // already carrier-agnostic; we pass the `Value`s directly rather than re-grounding.
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
            // Incomparable. WI-464: two same-base parameterized types
            // (`Option[T=Cat]` / `Option[T=Dog]`) get a real parameterized LUB —
            // recurse per binding by the parameter's DECLARED variance (covariant
            // `join(av,bv)`, contravariant `meet(av,bv)`, invariant `av≡bv`),
            // yielding `Option[T=Animal]`. When a binding can't be combined (no
            // common supertype, or unequal invariant bindings) the helper falls
            // back to the bare base sort — still a sound common supertype. (The
            // earlier WI-382 deferral was wrong: `meet_types` is just `join_types`'s
            // dual over the same lattice, built directly in Rust like the WI-293
            // subtyping half — no per-sort-algorithm framework needed.)
            (false, false) => {
                if let Some(lub) = join_parameterized_same_base(kb, &a, &b) {
                    return Some(lub);
                }
                // Not same-base parameterized: widen the entity side(s) one level
                // (entity → enclosing sort) up the nominal lattice and retry.
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

/// WI-464: which lattice bound a per-binding combine computes — the least upper
/// bound (`Lub`, used by [`join_types`]) or the greatest lower bound (`Glb`, used
/// by [`meet_types`]). Threaded through [`combine_parameterized_same_base`] so the
/// shared per-binding-by-variance skeleton serves both; a CONTRAVARIANT parameter
/// flips it (the dual bound).
#[derive(Clone, Copy)]
enum LatticeDir {
    Lub,
    Glb,
}

impl LatticeDir {
    /// The dual direction — a contravariant parameter computes the opposite bound
    /// of its enclosing type (the LUB of `Fn[A=…]` meets the two `A`s).
    fn flip(self) -> Self {
        match self {
            LatticeDir::Lub => LatticeDir::Glb,
            LatticeDir::Glb => LatticeDir::Lub,
        }
    }
}

/// WI-464: the GREATEST LOWER BOUND of two branch types — the lattice DUAL of
/// [`join_types`]. The Type lattice has a bottom (`nothing`), so the meet is
/// TOTAL: two types always have a GLB (at worst `nothing`), unlike the top-less
/// join (which returns `None` for incomparable nominal types). Used for the
/// CONTRAVARIANT-parameter arm of the parameterized LUB (a contravariant param's
/// join is the meet of its two binding values) and, dually, for the covariant arm
/// of the parameterized GLB.
///
/// Mirrors [`join_types`] arm-for-arm with the order reversed: a `type_var`
/// wildcard meets to the other side; when one type conforms to the other the
/// SUBtype wins (vs the supertype for join); mutually-compatible types meet to the
/// MORE-SPECIFIC side ([`more_specific_type`], dual of [`more_general_type`]); two
/// same-base parameterized types recurse per declared variance; incomparable types
/// meet to `nothing`. Commutative, like [`join_types`].
fn meet_types(kb: &mut KnowledgeBase, a: Value, b: Value) -> Value {
    if type_dispatch_name_view(kb, &a) == Some("type_var") {
        return b;
    }
    if type_dispatch_name_view(kb, &b) == Some("type_var") {
        return a;
    }
    // WI-335: each direction of the lattice check is independent — per-direction
    // substs, exactly as [`join_types`].
    let mut subst_ab = Substitution::new();
    let mut subst_ba = Substitution::new();
    match (
        types_compatible(kb, &mut subst_ab, &a, &b),
        types_compatible(kb, &mut subst_ba, &b, &a),
    ) {
        // `a <: b`: `a` is the SUBtype, hence the lower bound (dual of join).
        (true, false) => a,
        // `b <: a`: `b` is the lower bound.
        (false, true) => b,
        // Mutually compatible (identical, or bare-vs-parameterized): the
        // more-SPECIFIC side is the GLB (dual of join's more-general choice).
        (true, true) => more_specific_type(kb, &a, &b),
        // Incomparable: a same-base parameterized GLB if both qualify, else the
        // bottom type — two incomparable nominal types share no lower bound but
        // `nothing`.
        (false, false) => meet_parameterized_same_base(kb, &a, &b)
            .unwrap_or_else(|| Value::Term(kb.make_nothing_type())),
    }
}

/// WI-464: dual of [`more_general_type`] — between two MUTUALLY-compatible types
/// (identical, or the bare-vs-parameterized normalization where each conforms to
/// the other) the GLB keeps the MORE-SPECIFIC side: `Option` meet `Option[T = Int]`
/// is `Option[T = Int]`. Returns `a` when neither side is parameterized (identical
/// types). Keeps [`meet_types`] commutative.
fn more_specific_type(kb: &KnowledgeBase, a: &Value, b: &Value) -> Value {
    match (more_general_form(kb, a), more_general_form(kb, b)) {
        (Some("sort_ref"), Some("parameterized")) => b.clone(),
        (Some("parameterized"), Some("sort_ref")) => a.clone(),
        _ => a.clone(),
    }
}

/// WI-464: two types are EQUIVALENT when each is a subtype of the other — the
/// equality an INVARIANT parameter demands of its two binding values for the
/// parameterized LUB/GLB to keep that binding (else the whole type falls back to
/// its conservative bound). Context-free, like [`is_subtype`]: a fresh subst per
/// direction.
fn types_equivalent(kb: &mut KnowledgeBase, a: &Value, b: &Value) -> bool {
    let mut s1 = Substitution::new();
    if !types_compatible(kb, &mut s1, a, b) {
        return false;
    }
    let mut s2 = Substitution::new();
    types_compatible(kb, &mut s2, b, a)
}

/// WI-464: combine two SAME-BASE parameterized types into their LUB (`Lub`) or GLB
/// (`Glb`), recursing per binding by the parameter's DECLARED variance ([`declared_variance`]).
/// The shared skeleton behind [`join_parameterized_same_base`] /
/// [`meet_parameterized_same_base`]: a COVARIANT parameter combines in the
/// enclosing `dir`, a CONTRAVARIANT one in the dual ([`LatticeDir::flip`]), an
/// INVARIANT one requires its two values be [`types_equivalent`], and a BIVARIANT
/// one (variance both ways ⇒ irrelevant to subtyping) takes `dir` for a sound,
/// commutative representative.
///
/// Returns `None` when the two are NOT same-base parameterized (the caller then
/// widens for a join, or bottoms-out for a meet). When a binding cannot be combined
/// — a covariant/contravariant sub-combine has no result, an invariant param's
/// values differ, or param sets don't line up — it returns the CONSERVATIVE
/// whole-type bound: the bare base sort `S` for the LUB (every `S[..] <: S`), the
/// bottom type for the GLB. Construction stays on the hash-consed term path (the
/// nominal, heavily-shared structure that should remain a `TermId`); a `Value::Node`
/// combined binding (an arrow / denoted type — exotic for a branch join) falls back
/// to the conservative bound rather than minting a Node-carried type.
fn combine_parameterized_same_base(
    kb: &mut KnowledgeBase,
    dir: LatticeDir,
    a: &Value,
    b: &Value,
) -> Option<Value> {
    let (a_base, a_binds) = match extract_type(kb, a) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return None,
    };
    let (b_base, b_binds) = match extract_type(kb, b) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return None,
    };
    // Different base sorts: not a same-base combine — let the caller widen (LUB)
    // or bottom-out (GLB).
    if a_base != b_base {
        return None;
    }
    // The conservative whole-type bound when a binding can't be combined.
    let fallback = |kb: &mut KnowledgeBase| -> Value {
        match dir {
            LatticeDir::Lub => Value::Term(kb.make_sort_ref(a_base)),
            LatticeDir::Glb => Value::Term(kb.make_nothing_type()),
        }
    };
    // Same base sort ⇒ same params; guard a malformed/partial binding set.
    if a_binds.len() != b_binds.len() {
        return Some(fallback(kb));
    }
    let mut result: Vec<(Symbol, TermId)> = Vec::with_capacity(a_binds.len());
    for (param, av) in &a_binds {
        let Some((_, bv)) = b_binds.iter().find(|(q, _)| q == param) else {
            return Some(fallback(kb));
        };
        let combined: Value = match declared_variance(kb, a_base, *param) {
            Variance::Covariant | Variance::Bivariant => {
                match combine_binding(kb, dir, av.clone(), bv.clone()) {
                    Some(v) => v,
                    None => return Some(fallback(kb)),
                }
            }
            Variance::Contravariant => {
                match combine_binding(kb, dir.flip(), av.clone(), bv.clone()) {
                    Some(v) => v,
                    None => return Some(fallback(kb)),
                }
            }
            Variance::Invariant => {
                if types_equivalent(kb, av, bv) {
                    av.clone()
                } else {
                    return Some(fallback(kb));
                }
            }
        };
        match combined {
            Value::Term(t) => result.push((*param, t)),
            // A Node-carried combined binding: stay off the Node path; bail.
            _ => return Some(fallback(kb)),
        }
    }
    let base_ref = kb.make_sort_ref(a_base);
    Some(Value::Term(kb.make_parameterized_type(base_ref, &result)))
}

/// WI-464: combine one binding's two values per the lattice `dir`. `Lub` is the
/// partial [`join_types`] (the Type lattice is top-less, so `None` propagates);
/// `Glb` is the total [`meet_types`] (a bottom exists, so always `Some`).
fn combine_binding(kb: &mut KnowledgeBase, dir: LatticeDir, a: Value, b: Value) -> Option<Value> {
    match dir {
        LatticeDir::Lub => join_types(kb, a, b),
        LatticeDir::Glb => Some(meet_types(kb, a, b)),
    }
}

/// WI-464: the parameterized LUB of two same-base parameterized types — the
/// `Lub` instance of [`combine_parameterized_same_base`]. `join(Option[T = Cat],
/// Option[T = Dog]) = Option[T = Animal]`.
fn join_parameterized_same_base(kb: &mut KnowledgeBase, a: &Value, b: &Value) -> Option<Value> {
    combine_parameterized_same_base(kb, LatticeDir::Lub, a, b)
}

/// WI-464: the parameterized GLB of two same-base parameterized types — the `Glb`
/// instance of [`combine_parameterized_same_base`].
fn meet_parameterized_same_base(kb: &mut KnowledgeBase, a: &Value, b: &Value) -> Option<Value> {
    combine_parameterized_same_base(kb, LatticeDir::Glb, a, b)
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
/// Deliberately base-only, and called only from arms of [`types_compatible`]
/// where the EXPECTED side is a BARE spec (carries no bindings to drop) — NOT
/// from `sort_sym_compatible`, because that is also reached from the
/// `sort_ref ↔ parameterized` arms' base check, where a base-only accept would
/// admit a binding mismatch (a `Widget` providing `Comparable[T = Widget]`
/// accepted where `Comparable[T = Gadget]` is expected). Two such bare-expected
/// call sites: the original `(sort_ref, sort_ref)` arm (WI-344), and — uniformly
/// since WI-405 FACET A — the `(parameterized, sort_ref)` arm (a parameterized
/// carrier `S[bindings]` vs a bare spec it provides) and its carrier-agnostic
/// peer in [`types_compatible_view_structural`]. The accept stays sound at every
/// site for the same reason: the spec is bare. The same-parameter parameterized
/// case (`List[T]` vs `Stream[T]`) reaches subtyping only through
/// `parameterized_compatible`'s base check — where its per-binding loop validates
/// the bindings separately. The bare-value-vs-PARAMETERIZED-spec case (`Widget`
/// vs `Comparable[T = Widget]`) is handled by the binding-PRECISE
/// [`bare_provider_binding_precise`] (WI-402), which checks every expected binding
/// against the provider fact instead of dropping them. The fact is trusted to
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

/// WI-402 (bound/manifest half): BINDING-PRECISE provider admissibility — a value of a
/// bare concrete carrier sort conforms to a PARAMETERIZED spec type when the carrier
/// (or, for an entity, its parent sort — `sort_provides_admissibly`'s hop) PROVIDES the
/// spec and every binding the expected type carries checks against the value the
/// provider fact supplies for that param (matched by short name, the provider-view
/// convention). This is the bare↔parameterized counterpart of
/// [`parameterized_compatible_view`]'s WI-387 FIX 2 cross-sort arm: a bare carrier has
/// no bindings of its own, so EVERY expected binding resolves through the provider
/// view. The case `sort_provides_admissibly`'s doc deferred ("admitting it needs
/// binding-precise resolution") — `SubscriberStore provides DataProvider[K = String]`
/// now conforms to `DataProvider[K = String]`, while `DataProvider[K = Int64]` (binding
/// contradicted) and a non-provider stay mismatches.
///
/// A param the provider leaves unbound REJECTS — never silently passes (the expected
/// binding is a demand; an unverifiable supply must not discharge it). Purely a
/// LOOSENING of the `(sort_ref, parameterized)` arms: reached only after
/// `sort_sym_compatible` refused, so no existing accept changes. The WI-401
/// abstracting-return gate is unaffected — it runs AFTER conformance and still rejects
/// a PARTIAL manifest (an expected type that omits some spec member entirely).
///
/// The binding loop runs on a PROBE substitution, committed only on success — the arm
/// was substitution-pure before WI-402, and a failed multi-binding check must not leak
/// the prefix's bindings (e.g. a row-tail var bound by an effects binding) into the
/// caller's threaded subst (the per-direction hygiene `check_binding_by_variance`'s own
/// Invariant arm uses, one level up).
fn bare_provider_binding_precise<E: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual_sym: Symbol,
    expected: &E,
) -> bool {
    let TypeExtractor::Parameterized { base: expected_base, bindings: expected_bindings } =
        extract_type(kb, expected)
    else {
        return false;
    };
    let mut carrier = actual_sym;
    let provider_view = loop {
        if let Some(view) = provider_spec_view_bindings(kb, carrier, expected_base) {
            break view;
        }
        // Entity → parent sort. The chain is acyclic (a parent is a sort, never a
        // constructor), mirroring `sort_provides_admissibly`'s recursion.
        let Some(parent_tid) = kb.constructor_parent_sort(carrier) else { return false };
        let Term::Fn { functor: parent_functor, .. } = kb.get_term(parent_tid) else {
            return false;
        };
        carrier = *parent_functor;
    };
    let mut probe = subst.clone();
    for (param, ev) in &expected_bindings {
        let short = short_name_of(kb.resolve_sym(*param));
        let Some(pv) = provider_view
            .iter()
            .find(|(p, _)| short_name_of(kb.resolve_sym(*p)) == short)
            .map(|(_, v)| *v)
        else {
            return false;
        };
        // WI-391: a plain-sort-name leaf binding is now the canonical `Ref(S)` (normalized
        // at the producer, `sort_binding_to_value`), so `normalize_spec_binding_type` is a
        // no-op for it; retained as a defensive leaf-normalizer for any non-`Ref` shape. A
        // STRUCTURED binding value (`K = List[T = Int64]`) still rides raw and today REJECTS
        // — the deep/positional canonicalization (and the §5.3 extractability of structured
        // shapes) is the deferred fact-path / structured-binding work. Conservative: a false
        // REJECT only, never a false accept — anchored by the `#[ignore]`d wi402
        // structured-accept test.
        let pv = normalize_spec_binding_type(kb, pv).unwrap_or(pv);
        if !check_binding_by_variance(kb, &mut probe, expected_base, *param, &TermIdView(pv), ev) {
            return false;
        }
    }
    *subst = probe;
    true
}

/// WI-401 — detect an ABSTRACTING (sealing) return so the base model stays escape-free
/// (docs/design/path-dependent-types.md §5). A return is interface-expressible — and so
/// admitted — when it is concrete, or rooted at the operation's own inputs (a param's
/// type, the op's type-params), or (the deferred WI-402 admit-form) made manifest by an
/// `ensures`. The ONE thing that escapes is a return whose abstract member is minted
/// *inside* the body: a concrete carrier UPCAST to the **bare abstract spec it provides**
/// (`seal(s: SubscriberStore) -> DataProvider = s` — the `K = String` is erased, so the
/// resulting `DataProvider.K` roots at nothing in scope, the ML avoidance problem). This
/// returns `Some(error)` for exactly that pattern. Called only after the body conforms to
/// the return type, so it never fires for a plain mismatch.
///
/// NOT flagged (each carries no NEW hidden-local abstraction):
///   - same base sort (`f(p: DataProvider) -> DataProvider = p`) — the return's
///     abstractness, if any, is the input `p`'s, interface-rooted;
///   - a return that is NOT a provider upcast (a concrete nominal/entity supertype, or a
///     type-variable return rooted at an op type-param — `sort_functor_of_view` is `None`);
///   - a MANIFEST spec return that binds every member (`-> DataProvider[K = String]`, or
///     `-> Stream[Elem, {}]` whose members root at the op's own type-params) — the members
///     are carried, nothing abstract escapes.
fn abstracting_return_error(
    kb: &KnowledgeBase,
    body_ty: &Value,
    ret_ty: &Value,
    op_sym: Symbol,
) -> Option<TypeError> {
    let body_sort = sort_functor_of_view(kb, body_ty)?;
    let ret_sort = sort_functor_of_view(kb, ret_ty)?;
    if same_symbol(kb, body_sort, ret_sort) {
        return None;
    }
    if !sort_provides_admissibly(kb, body_sort, ret_sort) {
        return None;
    }
    // WI-402 (existential half): admit this abstract `Spec` return iff the loader
    // existential-REWROTE it (`-> C ensures Spec[C, …]`) — the output dual of `requires`.
    // The operation then guarantees the result provides `Spec`, so the abstract members
    // are interface-rooted (not a hidden local) and the existential is escape-free. A bare
    // `-> Spec` return that merely carries an `ensures` was NOT rewritten (its written type
    // is a real sort, members unbound) — it stays the strict escape and is rejected below.
    if kb.existential_return_ops.contains(&op_sym) {
        return None;
    }
    // Manifest iff every one of the spec's members has a binding in the return type. A
    // binding to a concrete type OR to the op's own type-parameter (`Stream[Elem, {}]`,
    // `Elem` input-rooted) is interface-expressible; a member left wholly UNBOUND escapes
    // (a bare spec leaves them all unbound; a PARTIAL manifest leaves some unbound — §5: a
    // partial manifest still escapes).
    let unbound: Vec<String> = kb
        .type_params_of_sort(ret_sort)
        .into_iter()
        .filter(|p| extract_type_param(kb, ret_ty, p).is_none())
        .collect();
    if unbound.is_empty() {
        return None;
    }
    let ret_name = kb.qualified_name_of(ret_sort).to_owned();
    let members = unbound.iter().map(|m| format!("'{m}'")).collect::<Vec<_>>().join(", ");
    Some(TypeError::Other {
        span: None,
        context: TypeErrorContext::OperationReturn { op_name: op_sym },
        expected: "an interface-expressible return (concrete, input-rooted, or an `ensures` \
                   manifest)"
            .to_owned(),
        actual: format!(
            "an abstracting return: the body provides '{ret_name}' only by an upcast that leaves \
             its member(s) {members} unbound, so the abstract member would escape its scope \
             (the avoidance problem) — bind the member(s) (`{ret_name}[…]`), return a concrete \
             type, or root them at the operation's inputs",
        ),
    })
}

/// WI-457: the WI-401 escape gate applied to the LEAVES of a branching body.
///
/// A join body (`-> KVStore = if persistent then diskStore else memStore`) widens
/// divergent concrete providers up to the bare/partial spec, so the joined
/// `body_ty` equals the declared return sort. The DIRECT [`abstracting_return_error`]
/// short-circuits on `same_symbol(body_sort, ret_sort)` and so MISSES it — the
/// abstract member (`KVStore.K`) would escape via the join without an `ensures`
/// vouching for it, the gap WI-401 left for join bodies. We re-apply the gate to
/// each branch LEAF's own (typer-stamped) inferred type: a leaf that is itself a
/// provider-upcast to the bare spec is the escape, exactly as the direct
/// `-> KVStore = memStore` form is rejected.
///
/// This naturally honours WI-457's "must NOT reject" constraints, because every
/// leaf goes through the UNCHANGED [`abstracting_return_error`]: a same-sort leaf
/// (an input-rooted `KVStore` value) short-circuits on `same_symbol`; a leaf under
/// a fully-manifest return has no unbound member; an `ensures`-vouched op is in
/// `existential_return_ops`. It walks the TAIL positions of the body — both arms of
/// each `if`, every `match` arm body, and a `let` BODY — so a join nested or wrapped
/// by a `let` in tail position is reached. Runs only AFTER the direct gate passes;
/// a non-branching body's sole leaf is the body itself (already judged there).
///
/// WI-468 (let-value laundering, sibling vector): a join — or even a plain
/// concrete provider — bound to a `let` VALUE and returned through the variable
/// (`let s : Spec = if … ; s`, or `let s : Spec = concreteProvider ; s`) launders
/// its abstract type via the binding's ANNOTATION. The body env binds `s` to the
/// bare-spec annotation (`check_bare_ref` reads `env.lookup_var`), so the returned
/// tail leaf `s` is genuinely typed `Spec == ret_sort` and the per-leaf gate
/// short-circuits on `same_symbol` — yet the abstract member still escapes. The
/// fix is DATAFLOW: see through a returned let-bound variable to the binding's
/// VALUE node, which the typer stamped with its OWN synthesized type (`MemStore`,
/// the concrete provider), not the laundering annotation. Re-processing the value
/// node re-applies the UNCHANGED [`abstracting_return_error`] to that synthesized
/// type, so the launder is caught exactly as the direct `-> Spec = concreteProvider`
/// form is — and the value may itself be a join (`let s = if … ; s`), reached
/// because the value node is pushed back onto the walk.
///
/// This only flags a variable in TAIL (return) position — the walk reaches a
/// let-bound var only through the body's tail leaves, never through a value used
/// internally (`let s = m ; someOp(s)`, where the tail leaf is the `someOp(...)`
/// apply, not `s`). The see-through resolves each value in the scope in force
/// WHERE it was bound (an `Rc`-shared cons list), so a shadowing rebind
/// (`let x = m ; let s = x ; let x = other ; s`) resolves `s`'s `x` to `m`, not
/// `other`. The walk is ITERATIVE (an explicit stack) — op bodies nest `else if`
/// arbitrarily deep (cf. wi285_unrec), so host recursion here would risk the very
/// stack overflow the iterative typer avoids.
fn branch_leaf_abstracting_return_error(
    kb: &KnowledgeBase,
    body: &Rc<NodeOccurrence>,
    ret_ty: &Value,
    op_sym: Symbol,
) -> Option<TypeError> {
    // Only a branching / let body can hide a widened-provider join behind a
    // `body_ty == ret_sort` the direct gate skips; a plain body is fully judged there.
    if !matches!(
        body.as_expr(),
        Some(Expr::If { .. } | Expr::Match { .. } | Expr::Let { .. })
    ) {
        return None;
    }
    // Each entry pairs a tail node with the let-scope (name -> value node) in force.
    let mut stack: Vec<(Rc<NodeOccurrence>, Rc<LeafScope>)> =
        vec![(Rc::clone(body), Rc::new(LeafScope::Empty))];
    // Backstop: a malformed binding cycle (not reachable in well-typed scope, but
    // the leaf see-through follows value nodes) must terminate rather than spin.
    let mut hops = 0usize;
    const MAX_LEAF_HOPS: usize = 100_000;
    while let Some((node, scope)) = stack.pop() {
        match node.as_expr() {
            Some(Expr::If { then_branch, else_branch, .. }) => {
                stack.push((Rc::clone(then_branch), Rc::clone(&scope)));
                stack.push((Rc::clone(else_branch), Rc::clone(&scope)));
            }
            Some(Expr::Match { branches, .. }) => {
                for b in branches {
                    stack.push((Rc::clone(&b.body), Rc::clone(&scope)));
                }
            }
            Some(Expr::Let { pattern, value, body, .. }) => {
                // Record the binding (the value resolves in the scope BEFORE this
                // let), then descend into the BODY only — a let value is not itself
                // a tail position; it escapes solely via a returned reference.
                let body_scope = match let_bound_var_name(pattern) {
                    Some(name) => Rc::new(LeafScope::Bind {
                        name,
                        value: Rc::clone(value),
                        parent: Rc::clone(&scope),
                    }),
                    None => Rc::clone(&scope),
                };
                stack.push((Rc::clone(body), body_scope));
            }
            // A tail leaf.
            _ => {
                // WI-468: see through a returned let-bound variable to its value
                // node (carrying the value's own synthesized type), resolving in the
                // scope where it was bound. A free var (param / outer binder) is not
                // in scope here → fall through to its own stamped type.
                if let Some(name) = leaf_var_ref(&node) {
                    if let Some((value, value_scope)) = scope.resolve(kb, name) {
                        hops += 1;
                        if hops <= MAX_LEAF_HOPS {
                            stack.push((value, value_scope));
                            continue;
                        }
                    }
                }
                if let Some(leaf_ty) = node.inferred_type() {
                    if let Some(e) = abstracting_return_error(kb, &leaf_ty, ret_ty, op_sym) {
                        return Some(e);
                    }
                }
            }
        }
    }
    None
}

/// WI-468: the let-binding scope threaded through
/// [`branch_leaf_abstracting_return_error`]'s leaf walk — an `Rc`-shared cons list
/// mapping a let-bound variable to the binding's VALUE node. Immutable so each
/// branch push is O(1). A binding's `parent` is the scope in force BEFORE that
/// `let`, which is also the scope its value resolves in — so a reference to a
/// rebound name sees the value it was actually bound to, not a later shadow.
enum LeafScope {
    Empty,
    Bind { name: Symbol, value: Rc<NodeOccurrence>, parent: Rc<LeafScope> },
}

impl LeafScope {
    /// Resolve a tail-position variable to `(value node, the scope that value
    /// resolves in)`. `None` for a free variable (a parameter or outer binder),
    /// whose own stamped type is then read directly.
    fn resolve(
        self: &Rc<Self>,
        kb: &KnowledgeBase,
        name: Symbol,
    ) -> Option<(Rc<NodeOccurrence>, Rc<LeafScope>)> {
        let mut cur = self;
        loop {
            match cur.as_ref() {
                LeafScope::Empty => return None,
                LeafScope::Bind { name: n, value, parent } => {
                    if same_symbol(kb, *n, name) {
                        return Some((Rc::clone(value), Rc::clone(parent)));
                    }
                    cur = parent;
                }
            }
        }
    }
}

/// The variable a `let` pattern binds, for a plain `Pattern::Var` binder (the only
/// form that introduces a single name the leaf walk can see through). A
/// destructuring pattern binds no single name and yields `None`.
fn let_bound_var_name(pattern: &Rc<NodeOccurrence>) -> Option<Symbol> {
    match pattern.as_pattern() {
        Some(Pattern::Var { name, .. }) => Some(*name),
        _ => None,
    }
}

/// The variable a tail leaf references, if it is a bare value reference (the forms
/// `value_references` enumerates: `Ident` / `Ref` / `VarRef`).
fn leaf_var_ref(node: &Rc<NodeOccurrence>) -> Option<Symbol> {
    match node.as_expr() {
        Some(Expr::Ident(s)) | Some(Expr::Ref(s)) => Some(*s),
        Some(Expr::VarRef { name }) => Some(*name),
        _ => None,
    }
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
    /// WI-428: a RIGID type-receiver projection `P.Key` / `MemStore.Key` — the
    /// type-keyed sibling of [`TypeExtractor::ExprCarried`] (design §5.3). `subject`
    /// is the projection's receiver type term (`Ref(P)` for a rigid type-parameter,
    /// `Ref(S)` for a concrete sort); `sort` is the sort whose `requires` chain lends
    /// the subject its members (= the subject's own symbol for a concrete-sort
    /// subject); `member` the projected member name.
    RigidTypeProjection { sort: Symbol, subject: Value, member: Symbol },
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
                "anthill.prelude.TypeExtractor.RigidTypeProjection" => TypeHead::RigidProjection,
                "anthill.prelude.TypeExtractor.EffectsRows" => TypeHead::EffectsRows,
                "anthill.prelude.TypeExtractor.Arrow" => TypeHead::Arrow,
                "anthill.prelude.TypeExtractor.NamedTuple" => TypeHead::NamedTuple,
                // WI-425: a bare DotApply expression carrier (`s.cell` outside
                // an ExprCarried wrapper) is NOT a type — without this arm the
                // named_arity>0 fallthrough below would classify it as a
                // parameterized type over a phantom sort named `dot_apply`
                // (and `sort_functor_of_view` would report that as a real
                // sort head).
                "anthill.reflect.Expr.dot_apply" => TypeHead::Error,
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
        TypeHead::RigidProjection => Some("rigid_type_projection"),
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
        // WI-428: a rigid type-receiver projection — declaring sort (`sort`), the
        // subject type term (`var`), and the member name; all `Ref(sym)` ground
        // children except the subject, which rides as a value for uniform reading.
        TypeHead::RigidProjection => match (
            view_child_sym(kb, ty, "sort"),
            view_child_value(kb, ty, "var"),
            view_child_sym(kb, ty, "member"),
        ) {
            (Some(sort), Some(subject), Some(member)) => {
                TypeExtractor::RigidTypeProjection { sort, subject, member }
            }
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

    // WI-398: signature well-formedness over EVERY operation — independent of the
    // sort/body split above, so a body-less FREE spec is covered too.
    errors.extend(check_operation_signatures(kb));

    errors
}

/// WI-398: reject a CYCLIC cross-parameter type projection (`f(a: b.T, b: a.T)`, or the
/// length-1 self-projection `f(a: a.T)`) loudly at LOAD, for EVERY operation. Unlike
/// `check_operation_bodies` (keyed off `SortInfo` / `op_bodies`, so it skips body-less
/// FREE specs), this walks ALL `OperationInfo` facts, so no operation's signature escapes
/// the check. A cyclic signature has no synthesis order — it is ill-formed by the
/// projection's definitional content (design path-dependent-types.md §6, WI-398).
fn check_operation_signatures(kb: &KnowledgeBase) -> Vec<TypeError> {
    let mut errors: Vec<TypeError> = Vec::new();
    // One operation symbol may carry more than one `OperationInfo` fact (e.g. a spec and
    // its impl); report each cyclic signature once.
    let mut reported: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    for (op_sym, params) in super::op_info::all_operation_params(kb) {
        if !reported.insert(op_sym) {
            continue; // already reported this op (multiple OperationInfo facts)
        }
        if let Some(cycle_syms) = param_projection_cycle(kb, &params) {
            let mut names: Vec<String> =
                cycle_syms.iter().map(|s| kb.resolve_sym(*s).to_owned()).collect();
            // Close the cycle visually (`a -> b -> a`) so the diagnostic reads as one.
            if let Some(first) = names.first().cloned() {
                names.push(first);
            }
            let span = kb.functor_span(op_sym).map(|s| s.span);
            errors.push(projection_type_error(
                &TypeErrorContext::OperationReturn { op_name: op_sym }, span, &format!(
                "cyclic cross-parameter type projection among parameters: {} — a \
                 parameter's type may project an EARLIER parameter, not form a cycle",
                names.join(" -> "),
            )));
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
                Literal::Int(_) => is_prim(declared_sym, "Int64"),
                Literal::Float(_) => is_prim(declared_sym, "Float"),
                Literal::Bool(_) => is_prim(declared_sym, "Bool"),
                _ => true,
            };
            let actual = match lit {
                Literal::String(_) => "String",
                Literal::Int(_) => "Int64",
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

/// True if the primitive sort of a literal (`"Int64"`, `"String"`, …) provides
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

/// True if sort `carrier` provides spec `spec` — directly OR transitively.
///
/// A `SortProvidesInfo` fact records `carrier` as its `sort_ref` and a spec as
/// its base; `maybe_emit_fact_provides_info` normalizes both explicit `provides`
/// clauses and bare `fact Spec[T=X]` facts into `SortProvidesInfo`, so this one
/// query covers both. Used so a fact field declared with a spec sort accepts a
/// value whose own sort satisfies that spec (WI-036).
///
/// WI-385 (user decision "transitive everywhere") + WI-407: the `provides` /
/// `is-a` relation is TRANSITIVE over the `SortProvidesInfo` edge set. If `A`
/// provides `M` and `M` provides `spec`, then `A` provides `spec` —
/// `IndexedFileStore → BulkStore → Store`. Every `sort_provides` caller —
/// subtype admissibility (`types_compatible`), requires-coverage, the
/// receiver-sort checks, and the loader skip — sees the full chain rather than
/// just the first hop. WI-407 made the loader emit edges for non-parametric
/// `fact <Spec>` declarations so this closure has something to chase.
pub(crate) fn sort_provides(kb: &KnowledgeBase, carrier: Symbol, spec: Symbol) -> bool {
    let provides_sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return false,
    };
    // Extract the provider edge set ONCE as (carrier, spec) symbol pairs — it is
    // invariant across the transitive walk, so reading the facts inside the
    // recursion would re-scan + re-allocate the whole table at every hop. A
    // value-fact `SortProvidesInfo` (denoted-bearing spec) is skipped here;
    // occurrence-based provides lookup is gated effect-expressions-as-types work
    // (avoid the term-only `rule_head` panic on a value head).
    let mut edges: Vec<(Symbol, Symbol)> = Vec::new();
    for rid in kb.rules_by_functor(provides_sym) {
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(c) = get_named_arg(kb, &named, "sort_ref")
            .and_then(|t| super::load::sort_ref_functor(kb, t))
        else {
            continue;
        };
        let Some(s) = get_named_arg(kb, &named, "spec")
            .and_then(|t| super::load::provides_spec_base_sym(kb, t))
        else {
            continue;
        };
        edges.push((c, s));
    }
    let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
    sort_provides_reach(kb, &edges, carrier, spec, &mut visited)
}

/// Transitive-reachability worker for [`sort_provides`] over the pre-extracted
/// `(carrier, spec)` edge set. From `carrier`, follow each edge whose source is
/// `carrier`: succeed if its target IS `spec`, else recurse on the target.
/// `visited` is a cycle guard against a cyclic `provides` declaration (a sort
/// that transitively provides itself) — once a carrier has been explored
/// without reaching `spec` it is never revisited, so the walk terminates and
/// stays O(edges).
fn sort_provides_reach(
    kb: &KnowledgeBase,
    edges: &[(Symbol, Symbol)],
    carrier: Symbol,
    spec: Symbol,
    visited: &mut SmallVec<[Symbol; 8]>,
) -> bool {
    if visited.iter().any(|&v| same_symbol(kb, v, carrier)) {
        return false;
    }
    visited.push(carrier);
    for &(src, dst) in edges {
        if !same_symbol(kb, src, carrier) {
            continue;
        }
        // Direct hop, then the transitive chain through the intermediate spec.
        if same_symbol(kb, dst, spec) || sort_provides_reach(kb, edges, dst, spec, visited) {
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
    for (param_sym, var_tid) in type_params {
        if let Term::Var(Var::Global(vid)) = kb.get_term(*var_tid) {
            let vid = *vid;
            // Name the rigid after the PARAMETER's short name, not the alias var's name.
            // `sort A = ?` aliases to an ANONYMOUS `?` var, so inheriting `vid.name()`
            // renders every skolemized param as `?_` — a clash then reads the unhelpful
            // `expected F[T = ?_], got F[T = ?_]` (both rigids print identically). The
            // short name makes it `?A` vs `?B`. Purely cosmetic: a rigid's identity is its
            // fresh `VarId`, never its name (unification compares VarIds; `SubjectKey` keys
            // on `v.raw()`), so the rename cannot affect any judgement.
            let name = short_name_of(kb.resolve_sym(*param_sym)).to_owned();
            let name_sym = kb.intern(&name);
            let fresh = kb.fresh_var(name_sym);
            let rigid_term = kb.alloc(Term::Var(Var::Rigid(fresh)));
            rigidify.bind_term(vid, rigid_term);
        }
    }
    rigidify
}

/// WI-461: a bare self-receiver IDENTITY body — `operation iterator(l: List) -> … = l` —
/// infers the BARE carrier sort `List` as its body type, leaving the carrier's type params
/// unbound. But the returned VALUE is the receiver `l`, whose members ARE its projections
/// (`l.T`, the WI-374 member tie). Refine the bare body type to `List[T = l.T, …]` — pin
/// each of the carrier's type params to its projection off the receiver — so a declared
/// PROVIDED return that threads the projection (`Stream[T = l.T, E = {}]`) conforms via the
/// `parameterized` cross-sort-provider path (the same machinery the explicit
/// `iterator[Elem](l: List[Elem]) -> Stream[Elem, {}]` form already rides), while a
/// DIFFERENT receiver's projection (`Stream[T = xs.T]`) still fails (`l.T` ≠ `xs.T`, two
/// distinct neutrals) — sound. The caller applies this ONLY as a fallback after the
/// unrefined check fails, so it can never reject a body that conforms today.
///
/// `None` (no refinement) unless ALL hold: the body is a stable single-segment value
/// reference (`l` — not a call/literal/constructor/field path); its inferred type is a BARE
/// `sort_ref` (no bindings); the carrier declares ≥1 type param; and each param resolves to
/// a `<carrier>.<P>` symbol. The projection value is built byte-identical to the loader's
/// `l.T` (`make_expr_carried(Ref(recv), intern(short))`, the SHORT member name), and the
/// binding KEY is the carrier's own `<carrier>.<P>` param symbol so the cross-sort-provider
/// instantiation resolves its canonical var.
fn refine_self_receiver_body_type(
    kb: &mut KnowledgeBase,
    body: &Rc<NodeOccurrence>,
    body_ty: &Value,
) -> Option<Value> {
    let segs = stable_receiver_path(body)?;
    let [recv] = segs.as_slice() else { return None };
    let recv = *recv;
    let TypeExtractor::SortRef(carrier) = extract_type(kb, body_ty) else {
        return None;
    };
    let param_names = kb.type_params_of_sort(carrier);
    if param_names.is_empty() {
        return None;
    }
    let carrier_qn = kb.qualified_name_of(carrier).to_owned();
    let recv_term = kb.alloc(Term::Ref(recv));
    let mut bindings: Vec<(Symbol, TermId)> = Vec::with_capacity(param_names.len());
    for short in &param_names {
        let param_sym = kb.try_resolve_symbol(&format!("{carrier_qn}.{short}"))?;
        let member_sym = kb.intern(short);
        let proj = kb.make_expr_carried(recv_term, member_sym);
        bindings.push((param_sym, proj));
    }
    let base = kb.make_sort_ref(carrier);
    Some(Value::Term(kb.make_parameterized_type(base, &bindings)))
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
        /// WI-424 — the enclosing sort's param canonical vars → their per-body
        /// rigids; installed on the body env so same-sort sibling calls seed
        /// their substitution with the enclosing instance's params.
        sort_param_rigids: Rc<Vec<(VarId, TermId)>>,
        /// WI-441 — the full type-param rigidify substitution (op + enclosing
        /// sort params). The boundary effects check walks BOTH sides through
        /// it: `walk_type_deep_value` cannot rewrite inside a `Value::Node`
        /// carrier (occurrences are shared, not rebuilt), so a Node-carried
        /// callback arrow's row TAIL stays the original Global var while the
        /// declared atom was rigidified — the same param then compared
        /// unequal (`?Eff` vs `?Eff`). Resolving incurred components through
        /// this subst maps that Global to the same Rigid.
        rigidify: Rc<Substitution>,
    }

    let mut ops_to_check = Vec::new();

    for &op_sym in op_syms {
        let rec = match super::op_info::lookup_operation_info(kb, op_sym) {
            Some(r) => r,
            None => continue,
        };
        let span = kb.functor_span(rec.op_sym).map(|s| s.span);
        // WI-398: a CYCLIC cross-parameter projection signature is ill-formed; the loud
        // error is raised once, for EVERY op, by `check_operation_signatures` (which
        // covers body-less free specs this body-check pass never reaches). Here we only
        // SKIP body-checking such an op so its un-resolvable projection params do not
        // cascade into spurious secondary errors.
        if param_projection_cycle(kb, &rec.params).is_some() {
            continue;
        }
        // Body-less ops (specs) have no body to type-check.
        let body_node = match rec.body_node {
            Some(n) => n,
            None => continue,
        };
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
        //
        // WI-424: the ENCLOSING parametric sort's type params are skolemized the
        // same way — within a member body they denote THIS instance's parameters
        // (the parametricity tie, type-parameter-scoping.md §3), fixed-but-
        // abstract exactly like the op's own. The rigid asymmetry is what makes
        // the member-body threading land: a sibling call's flexible params solve
        // TO the rigids (a `Rigid` is never bound), so `iterator(c)`'s return
        // `Stream[Element, E]` carries the enclosing rigids through to an inner
        // `Stream.find`'s `[Elem, Eff]` and to the declared-effects check. The
        // (vid → rigid) map rides `OpInfo` onto the body env for the same-sort
        // sibling-call seeding in `check_apply_iter`.
        let parent_sort_params: Rc<Vec<(Symbol, TermId)>> = impl_parent_of_op(kb, rec.op_sym)
            .map(|p| sort_type_params_as_pairs(kb, p))
            .unwrap_or_default();
        let mut sort_param_rigids: Vec<(VarId, TermId)> = Vec::new();
        let mut rigidify_subst = Substitution::new();
        let (params, return_type, declared_effects) = if rec.type_params.is_empty()
            && parent_sort_params.is_empty()
        {
            (rec.params, rec.return_type, rec.effects)
        } else {
            let mut all_params = rec.type_params.clone();
            all_params.extend(parent_sort_params.iter().cloned());
            let rigidify = rigidify_op_type_params(kb, &all_params);
            for (_, var_tid) in parent_sort_params.iter() {
                if let Term::Var(Var::Global(vid)) = kb.get_term(*var_tid) {
                    let vid = *vid;
                    // `rigidify` binds each sort param to its fresh `Rigid` term — always
                    // a `Value::Term`; a non-`Term` binding would not be a rigid here.
                    if let Some(Value::Term(rigid)) = rigidify.resolve_as_value(vid) {
                        sort_param_rigids.push((vid, *rigid));
                    }
                }
            }
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
            rigidify_subst = rigidify;
            (params, return_type, declared_effects)
        };
        ops_to_check.push(OpInfo {
            op_sym: rec.op_sym,
            return_type,
            declared_effects,
            body_node,
            params,
            span,
            sort_param_rigids: Rc::new(sort_param_rigids),
            rigidify: Rc::new(rigidify_subst),
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
        // WI-424: same-sort sibling calls seed their substitution with the
        // enclosing sort's rigids (see the OpInfo field doc; Rc clone).
        env.set_enclosing_sort_param_rigids(Rc::clone(&op.sort_param_rigids));
        // WI-400 (body-site): a projection param type (`k: s.cell.T`) must be discharged
        // against the OTHER params' DECLARED types before it is bound into the body env —
        // the body-check peer of the call-site elimination (`check_apply_iter` / WI-398,
        // which discharges against ARGUMENT types). δ-grounding makes a MANIFEST receiver's
        // member concrete (`s: Wrapper[P = Inner[T = String]]` ⟹ `k : String`); an ABSTRACT
        // receiver (`s: State`, `P` open) whose declared interface provides the member
        // forms a rigid NEUTRAL (`k : ⟨s.provider⟩.K` — abstract-stays-poly), which the
        // body then path-identity-matches via the ζ arm of `unify_types`. Only a member NO
        // interface declares stays a loud error. Only ops whose params carry a projection
        // pay for the map + walk.
        if op.params.iter().any(|(_, t)| value_contains_projection(kb, t)) {
            // Order-INDEPENDENT elimination (matching the call-site, which discharges over
            // a fully-populated `param_to_arg_type`): iterate to a FIXPOINT — each pass
            // re-discharges every still-projection param against the current `decl` and
            // commits any param whose type CHANGED (a manifest receiver grounding, or a
            // receiver resolved by an earlier pass), so a receiver declared in ANY order
            // (forward OR backward) feeds its dependents. A pass with no change is the
            // fixpoint. `Ok` no longer implies "no projection remains" — a stable abstract
            // NEUTRAL eliminates to itself (`structural_eq`, no change) and legitimately
            // survives; an `Err` means the receiver is not YET resolved (retried) OR is
            // genuinely un-dischargeable (surfaced after the fixpoint).
            let mut decl: HashMap<Symbol, Value> =
                op.params.iter().map(|(n, t)| (*n, t.clone())).collect();
            loop {
                let mut changed = false;
                for (name, _) in &op.params {
                    let cur = decl.get(name).cloned().expect("param present in decl");
                    if value_contains_projection(kb, &cur) {
                        if let Ok(elim) = eliminate_type_projections(
                            kb,
                            &cur,
                            &decl,
                            None,
                            &TypeErrorContext::OperationArgument { op_name: op.op_sym, param: *name },
                            op.span,
                        ) {
                            if !elim.structural_eq(&cur) {
                                decl.insert(*name, elim);
                                changed = true;
                            }
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            // Fixpoint reached. A param that STILL eliminates to an `Err` is genuinely
            // un-dischargeable (missing member, non-param receiver); surface it and skip
            // this op's body-check to avoid cascading (mirrors the cyclic-signature skip).
            // A param that eliminates to `Ok` but still carries a projection is a sound
            // abstract NEUTRAL (abstract-stays-poly) — bound as-is for the ζ path-identity.
            let mut proj_failed = false;
            for (name, _) in &op.params {
                let cur = decl.get(name).cloned().expect("param present in decl");
                if value_contains_projection(kb, &cur) {
                    if let Err(e) = eliminate_type_projections(
                        kb,
                        &cur,
                        &decl,
                        None,
                        &TypeErrorContext::OperationArgument { op_name: op.op_sym, param: *name },
                        op.span,
                    ) {
                        errors.push(e);
                        proj_failed = true;
                    }
                }
            }
            if proj_failed {
                continue;
            }
            for (name, _) in &op.params {
                env.bind_var(*name, decl.remove(name).expect("param present in decl"));
            }
        } else {
            for (name, ty) in &op.params {
                // WI-341 Stage A: op param types are carrier-agnostic `Value`. A
                // callback param whose arrow effect is denoted-bearing binds as a
                // `Value::Node` arrow; a ground param as `Value::Term`.
                env.bind_var(*name, ty.clone());
            }
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
                // WI-461: a bare self-receiver identity body (`= l`) infers the bare
                // carrier sort; if it does not conform directly, retry with the body type
                // refined to the receiver's projections (`List` → `List[T = l.T]`) so a
                // provided return threading the projection conforms. Purely additive — only
                // attempted on the unrefined failure — so no delivered accept regresses.
                let conforms = types_compatible(kb, &mut subst, &result.ty, &op.return_type)
                    || match refine_self_receiver_body_type(kb, &result.node, &result.ty) {
                        Some(refined) => {
                            let mut probe = Substitution::new();
                            let ok = types_compatible(kb, &mut probe, &refined, &op.return_type);
                            if ok {
                                subst = probe;
                            }
                            ok
                        }
                        None => false,
                    };
                if !conforms {
                    errors.push(TypeError::TypeMismatch {
                        span: None,
                        context: TypeErrorContext::OperationReturn { op_name: op.op_sym },
                        expected: op.return_type.clone(),
                        actual: result.ty.clone(),
                    });
                } else if let Some(e) =
                    abstracting_return_error(kb, &result.ty, &op.return_type, op.op_sym)
                {
                    // WI-401: the body conforms, but only by a provider UPCAST to a bare
                    // abstract spec — the sealing return that would let an abstract member
                    // escape its scope. Forbidden so the base model stays escape-free (§5).
                    errors.push(e);
                } else if let Some(e) = branch_leaf_abstracting_return_error(
                    kb,
                    &result.node,
                    &op.return_type,
                    op.op_sym,
                ) {
                    // WI-457: a JOIN body widened divergent concrete providers up to the
                    // bare spec, so the joined `body_ty == ret_sort` slipped the direct
                    // gate above. Re-apply it per branch leaf — the same escape, hidden
                    // behind the branch join.
                    errors.push(e);
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
                // WI-441: the op's rigidify subst (not an empty one) — a
                // Node-carried callback arrow's row tail reaches here as the
                // ORIGINAL Global var (`walk_type_deep_value` does not rewrite
                // inside occurrence carriers), so resolving through the
                // rigidify maps it to the same Rigid the declared atom became.
                let canon_subst = (*op.rigidify).clone();
                let declared_canon: Vec<Value> = op.declared_effects.iter()
                    .map(|e| walk_type_deep_value(kb, &canon_subst, e))
                    .collect();
                let declared_display: Vec<String> = op.declared_effects.iter()
                    .map(|e| type_display_name_value(kb, e))
                    .collect();
                for effect in &ext_effects {
                    // WI-441: a ROW-shaped incurred effect — a callback's row
                    // value flowing into the body effects (applying a
                    // `@ {EffP, -…}` callback incurs its whole row; a declared
                    // row var bound at a call site walks to a `merge(…)`
                    // structure) — EXPLODES into its components: each present
                    // label and each row-tail var is checked against the
                    // declared atoms individually. Absences are constraints,
                    // not incurred effects, and `empty_row` contributes
                    // nothing. A non-row effect stays a single atom. Each
                    // component is canon-walked AFTER the explode: a
                    // Node-carried row's tail extracts as the raw Global var,
                    // which only the per-component walk maps to its Rigid.
                    let components: Vec<Value> =
                        match explode_incurred_effect_row(kb, effect) {
                            Some(atoms) => atoms,
                            None => vec![effect.clone()],
                        };
                    for comp in &components {
                        let comp_canon = walk_type_deep_value(kb, &canon_subst, comp);
                        let declared = declared_canon.iter()
                            .any(|d| views_structurally_equal(kb, &comp_canon, d));
                        if !declared {
                            errors.push(TypeError::Other {
                                span: op.span,
                                context: TypeErrorContext::OperationEffects { op_name: op.op_sym },
                                expected: format!("declared: [{}]", declared_display.join(", ")),
                                actual: format!("undeclared effect: {}", type_display_name_value(kb, &comp_canon)),
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
mod wi417_cycle_tests {
    //! WI-417: the typer's substitution-chain walkers must not overflow the
    //! host stack on a CYCLIC substitution. Normal unification does not mint a
    //! pure value-var cycle (WI-416's cycle closed through a sort-alias hop, now
    //! handled by the `walk_type` guard), so these tests build the cycle
    //! DIRECTLY in the `Substitution` — the level at which the defect is
    //! reproducible — and assert each walker terminates with a representative
    //! rather than recursing to a crash. Before WI-417 these recursed forever
    //! and aborted the test binary (an uncatchable stack overflow), so a
    //! regression here is a loud failure.
    use super::{walk_type, walk_type_value, walk_value_to_resolved, walk_pattern_field_type_deep};
    use crate::eval::value::Value;
    use crate::kb::subst::Substitution;
    use crate::kb::term::{Term, TermId, Var, VarId};
    use crate::kb::KnowledgeBase;

    fn fresh(kb: &mut KnowledgeBase, name: &str) -> VarId {
        let sym = kb.intern(name);
        kb.fresh_var(sym)
    }

    /// Two vars cross-bound through `Value::Term(Var(_))`: `a → b → a`.
    fn term_var_cycle(kb: &mut KnowledgeBase) -> (Substitution, TermId, VarId, VarId) {
        let a = fresh(kb, "A");
        let b = fresh(kb, "B");
        let ta = kb.alloc(Term::Var(Var::Global(a)));
        let tb = kb.alloc(Term::Var(Var::Global(b)));
        let mut subst = Substitution::new();
        subst.bind_value(a, Value::Term(tb));
        subst.bind_value(b, Value::Term(ta));
        (subst, ta, a, b)
    }

    #[test]
    fn walk_type_terminates_on_term_var_cycle() {
        let mut kb = KnowledgeBase::new();
        let (subst, ta, a, b) = term_var_cycle(&mut kb);
        match kb.get_term(walk_type(&kb, &subst, ta)) {
            Term::Var(Var::Global(v)) => assert!(*v == a || *v == b, "a cycle representative"),
            other => panic!("expected a cycle-representative var, got {other:?}"),
        }
    }

    #[test]
    fn walk_type_value_terminates_on_term_var_cycle() {
        let mut kb = KnowledgeBase::new();
        let (subst, ta, a, b) = term_var_cycle(&mut kb);
        match walk_type_value(&kb, &subst, &Value::Term(ta)) {
            Value::Term(t) => match kb.get_term(t) {
                Term::Var(Var::Global(v)) => assert!(*v == a || *v == b),
                other => panic!("expected a cycle-representative var, got {other:?}"),
            },
            other => panic!("expected Value::Term(var), got {other:?}"),
        }
    }

    #[test]
    fn walk_pattern_field_type_deep_terminates_on_term_var_cycle() {
        let mut kb = KnowledgeBase::new();
        let (subst, ta, _a, _b) = term_var_cycle(&mut kb);
        // Termination is the property under test (returns instead of crashing).
        let _ = walk_pattern_field_type_deep(&mut kb, &subst, &Value::Term(ta));
    }

    #[test]
    fn walk_value_to_resolved_terminates_on_value_var_cycle() {
        let mut kb = KnowledgeBase::new();
        let a = fresh(&mut kb, "A");
        let b = fresh(&mut kb, "B");
        let mut subst = Substitution::new();
        subst.bind_value(a, Value::Var(Var::Global(b)));
        subst.bind_value(b, Value::Var(Var::Global(a)));
        match walk_value_to_resolved(&kb, &subst, Value::Var(Var::Global(a))) {
            Value::Var(Var::Global(v)) => assert!(v == a || v == b, "a cycle representative"),
            other => panic!("expected a cycle-representative var, got {other:?}"),
        }
    }
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
        let int = kb.intern("Int64");
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
        assert_eq!(sort_functor_of(&kb, bare), Some(int), "bare Ref(Int64) -> Int64");

        // A structural variant (arrow) has no sort head.
        let unit = kb.intern("Unit");
        let unit_ref = kb.make_sort_ref(unit);
        let arrow = kb.make_arrow_type(unit_ref, unit_ref, &[]);
        assert_eq!(sort_functor_of(&kb, arrow), None, "arrow has no sort head");
    }

    #[test]
    fn extract_sort_ref_sym_reads_term_backed_bare_ref() {
        let mut kb = kb_with_prelude();
        let int = kb.intern("Int64");
        let list = kb.intern("List");
        let t = kb.intern("T");

        // Term-backed bare sort `Ref(Int)` — pre-migration this returned None.
        let bare = kb.alloc(Term::Ref(int));
        assert_eq!(extract_sort_ref_sym(&kb, &TermIdView(bare)), Some(int), "bare Ref(Int64) -> Int64");

        // The same via the real builder `make_sort_ref` (also `Ref(Int)`).
        let built = kb.make_sort_ref(int);
        assert_eq!(extract_sort_ref_sym(&kb, &TermIdView(built)), Some(int), "make_sort_ref(Int64) -> Int64");

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
        let int = kb.intern("Int64");
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
        let int = kb.intern("Int64");
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

    /// WI-470 regression: the occurrence-primary `make_arrow_value` must fold a
    /// row-tail `Var` (a row-polymorphic body's open tail) as `open(tail)`, NOT
    /// `present(var)`. The retired ground path got this from
    /// `build_canonical_effects_rows`; the always-Node path re-derives it. Without
    /// the fix the tail var is present-wrapped, so `decompose_effect_row` reads it
    /// as a present LABEL (the WI-441 bug class) — a closed row with a spurious var
    /// label instead of an open row.
    #[test]
    fn wi470_inferred_arrow_folds_row_tail_var_as_open_not_present() {
        use super::{arrow_parts, decompose_effect_row, make_arrow_value};
        use crate::eval::value::Value;
        use crate::kb::term::Var;
        let mut kb = kb_with_prelude();
        let int = Value::Term(kb.make_sort_ref_by_name("anthill.prelude.Int64"));
        let label_t = kb.make_sort_ref_by_name("anthill.prelude.Bool");
        // A bare Global logic var is a row tail (a row-polymorphic open tail).
        let rho = kb.intern("rho");
        let vid = kb.fresh_var(rho);
        let tail_t = kb.alloc(Term::Var(Var::Global(vid)));
        assert!(kb.row_tail_var_of(tail_t).is_some(), "sanity: bare Global is a row tail");

        // Inferred arrow `Int64 -> Int64 @ {Bool, ?rho}` — one present label + an
        // open tail. WI-470: occurrence-primary (`Value::Node`).
        let arrow = make_arrow_value(
            &mut kb,
            &int,
            &int,
            &[Value::Term(label_t), Value::Term(tail_t)],
            span(),
            None,
        );
        assert!(matches!(arrow, Value::Node(_)), "WI-470: inferred arrow is occurrence-primary");

        let (_, _, effects) = arrow_parts(&mut kb, &arrow).expect("arrow has effects parts");
        let effects = effects.expect("arrow synthesizes an effects child");
        let subst = Substitution::new();
        let (present, tails, _absent) =
            decompose_effect_row(&mut kb, &subst, &effects).expect("effects row decomposes");
        assert!(tails.contains(&tail_t), "row-tail var folds as open(tail); tails={tails:?}");
        assert_eq!(present.len(), 1, "exactly the real label is present (NOT the tail); present={present:?}");
        assert!(
            present.iter().any(|p| matches!(p, Value::Term(t) if *t == label_t)),
            "the present label is Bool; present={present:?}",
        );
    }

    /// WI-470: `denoted_value_is_closed` distinguishes the three value-in-type shapes
    /// so the WI-385 groundness gate routes each to the validator that can DECIDE it —
    /// a closed value is conformance-checked here; a free var defers to inference; a
    /// binder-local param ref defers to the alignment-aware `validate_callback_effect_row`.
    /// None is silently skipped.
    #[test]
    fn wi470_denoted_value_is_closed_distinguishes_binder_relative() {
        use super::denoted_value_is_closed;
        use crate::intern::SymbolKind;
        use crate::kb::node_occurrence::Expr;
        use crate::kb::term::{Literal, Var};
        let mut kb = kb_with_prelude();

        // Closed: a literal value-in-type (the `3` of `Vector[Int64, 3]`).
        let lit = NodeOccurrence::new_expr(Expr::Const(Literal::Int(3)), span(), None);
        assert!(denoted_value_is_closed(&kb, &lit), "a literal value is closed");

        // Not closed: a free logical var (the `?n` of `Vector[Int64, ?n]`) — inference.
        let n = kb.intern("n");
        let vid = kb.fresh_var(n);
        let var = NodeOccurrence::new_expr(Expr::Var(Var::Global(vid)), span(), None);
        assert!(!denoted_value_is_closed(&kb, &var), "a free var is not closed");

        // Not closed: each value-PLACE kind is binder-relative (deferred to the
        // alignment-aware checker). Crucially `CallbackParam` — the `a` of a declared
        // `(a) -> Unit @ Modify[a]` — is the production own-param case the gate MUST
        // defer (testing `Param` alone masked the original miss; see WI-470 review).
        for (i, kind) in [
            SymbolKind::Param,
            SymbolKind::CallbackParam,
            SymbolKind::CallbackResult,
            SymbolKind::OpResult,
            SymbolKind::Field,
            SymbolKind::LocalLet,
        ]
        .into_iter()
        .enumerate()
        {
            let s = kb.symbols.define(&format!("p{i}"), &format!("wi470.test.p{i}"), kind, 0);
            let r = NodeOccurrence::new_expr(Expr::Ref(s), span(), None);
            assert!(
                !denoted_value_is_closed(&kb, &r),
                "a value-place ref ({kind:?}) is binder-relative, not closed",
            );
        }

        // Closed: a ref to a GLOBAL identity (Sort/Entity/Operation) — the `store` of
        // `Modify[store]` (a global resource), compared by symbol identity, not alignment.
        let store = kb.symbols.define("store", "wi470.test.store", SymbolKind::Entity, 0);
        let global_ref = NodeOccurrence::new_expr(Expr::Ref(store), span(), None);
        assert!(denoted_value_is_closed(&kb, &global_ref), "a global (non-place) ref is closed");
    }

    /// WI-470: a parameterized type's binding is READ identically whether the type is a
    /// hash-consed `TermId` (`Fn{List,[T=Int64]}`) or a `Value::Node` occurrence (the
    /// poisoned-receiver shape) — the carrier never erases the binding. This is the
    /// invariant `bind_spec_params_from_carrier` relies on after switching from
    /// `.as_term()` (which dropped the binding of a Node carrier) to the carrier-
    /// agnostic `parameterized_short_bindings`.
    #[test]
    fn wi470_parameterized_short_bindings_reads_both_carriers() {
        use super::parameterized_short_bindings;
        use crate::eval::value::Value;
        use crate::kb::term_view::TermIdView;
        let mut kb = kb_with_prelude();
        let list = kb.intern("List");
        let t = kb.intern("T");
        let int = kb.intern("Int64");
        let int_ref = kb.make_sort_ref(int);
        let list_ref = kb.make_sort_ref(list);

        // Hash-consed (closed) carrier `List[T = Int64]` = `Fn{List, [T = Int64]}`.
        let term_ty = kb.make_parameterized_type(list_ref, &[(t, int_ref)]);
        let from_term = parameterized_short_bindings(&kb, &TermIdView(term_ty));

        // Occurrence carrier (the poisoned-receiver shape) `parameterized{List, [T = Int64]}`.
        let node = kb.make_parameterized_occ(
            TypeChild::Ground(list_ref),
            vec![(t, TypeChild::Ground(int_ref))],
            span(),
            None,
        );
        let from_node = parameterized_short_bindings(&kb, &Value::Node(node));

        assert_eq!(from_term, vec![("T".to_string(), int_ref)], "binding read from the TermId carrier");
        assert_eq!(from_node, from_term, "Node carrier yields the SAME binding (never erased)");
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
        let int = kb.intern("Int64");
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
        assert!(matches!(by.get(&n), Some(Value::Term(_))), "`n: Int64` rides as Value::Term");
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



/// WI-464 — variance-aware parameterized join (LUB) / meet (GLB). The join now
/// CONSTRUCTS a parameterized type per-binding by declared variance instead of only
/// widening the nominal side, and `meet_types` is its lattice dual (GLB down to the
/// `nothing` bottom). Loads the real stdlib (for the proposal-035 variance facts:
/// Option/Function covariance, Function.A contravariance) plus a small Animal/Box
/// fixture, then drives the private lattice ops directly.
#[cfg(test)]
mod wi464_variance_join_meet_tests {
    use super::{extract_sort_ref_sym, extract_type, join_types, meet_types, type_dispatch_name_view, TypeExtractor};
    use crate::eval::value::Value;
    use crate::intern::Symbol;
    use crate::kb::load::{self, NullResolver};
    use crate::kb::term::TermId;
    use crate::kb::KnowledgeBase;
    use crate::parse;
    use std::path::{Path, PathBuf};

    const SRC: &str = r#"namespace test.wi464
  import anthill.prelude.{Option, Function, Int64}

  sort Animal
    entity cat
    entity dog
  end

  -- No variance fact ⇒ INVARIANT in T (the safe default for a mutable-shaped sort).
  sort Box
    sort T = ?
    entity box(v: T)
  end
end
"#;

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

    fn load_kb() -> KnowledgeBase {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill");
        let mut files = Vec::new();
        collect(&dir, &mut files);
        let mut parsed: Vec<_> = files
            .iter()
            .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
            .collect();
        parsed.push(parse::parse(SRC).expect("parse fixture"));
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        if let Err(errs) = load::load_all(&mut kb, &refs, &NullResolver) {
            panic!(
                "fixture load errors: {:?}",
                errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
            );
        }
        kb
    }

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("resolve {qn}"))
    }

    /// A bare `sort_ref` Value for the sort named `qn`.
    fn bare(kb: &mut KnowledgeBase, qn: &str) -> Value {
        let s = sym(kb, qn);
        Value::Term(kb.make_sort_ref(s))
    }

    /// A parameterized Value `Base[param = arg, …]`, each arg a bare sort named by qn.
    fn param(kb: &mut KnowledgeBase, base_qn: &str, binds: &[(&str, &str)]) -> Value {
        let base_sym = sym(kb, base_qn);
        let base_ref = kb.make_sort_ref(base_sym);
        let term_binds: Vec<(Symbol, TermId)> = binds
            .iter()
            .map(|(p, arg_qn)| {
                let p_sym = kb.intern(p);
                let arg_sym = sym(kb, arg_qn);
                (p_sym, kb.make_sort_ref(arg_sym))
            })
            .collect();
        Value::Term(kb.make_parameterized_type(base_ref, &term_binds))
    }

    /// Decompose a parameterized result into (base sort, bindings).
    fn as_param(kb: &KnowledgeBase, v: &Value) -> (Symbol, Vec<(Symbol, Value)>) {
        match extract_type(kb, v) {
            TypeExtractor::Parameterized { base, bindings } => (base, bindings),
            other => panic!("expected a parameterized type, got {other:?}"),
        }
    }

    /// The value bound to the parameter whose short name is `name`.
    fn binding<'a>(kb: &KnowledgeBase, binds: &'a [(Symbol, Value)], name: &str) -> &'a Value {
        binds
            .iter()
            .find(|(p, _)| kb.resolve_sym(*p) == name)
            .map(|(_, v)| v)
            .unwrap_or_else(|| panic!("no `{name}` binding among the result bindings"))
    }

    fn is_sort(kb: &KnowledgeBase, v: &Value, want: Symbol) -> bool {
        extract_sort_ref_sym(kb, v) == Some(want)
    }
    fn is_nothing(kb: &KnowledgeBase, v: &Value) -> bool {
        type_dispatch_name_view(kb, v) == Some("nothing")
    }

    /// COVARIANT: `join(Option[T = cat], Option[T = dog]) = Option[T = Animal]` — the
    /// element parameter's two incomparable values join up the sort lattice to their
    /// common parent, and the result is a freshly CONSTRUCTED parameterized type (the
    /// behaviour join never had before WI-464).
    #[test]
    fn covariant_join_builds_parameterized_lub() {
        let mut kb = load_kb();
        let (animal, option) = (sym(&kb, "test.wi464.Animal"), sym(&kb, "anthill.prelude.Option"));
        let a = param(&mut kb, "anthill.prelude.Option", &[("T", "test.wi464.Animal.cat")]);
        let b = param(&mut kb, "anthill.prelude.Option", &[("T", "test.wi464.Animal.dog")]);
        let j = join_types(&mut kb, a, b).expect("Option[cat] and Option[dog] have a join");
        let (base, binds) = as_param(&kb, &j);
        assert_eq!(base, option, "join base sort is Option");
        assert!(is_sort(&kb, binding(&kb, &binds, "T"), animal), "T binding joins cat/dog to Animal");
    }

    /// INVARIANT: `Box` has no variance fact, so its `T` is invariant. The two
    /// binding values differ, so there is no parameterized LUB — the join falls back
    /// to the conservative common supertype, the bare base sort `Box`.
    #[test]
    fn invariant_join_falls_back_to_bare_base() {
        let mut kb = load_kb();
        let box_sym = sym(&kb, "test.wi464.Box");
        let a = param(&mut kb, "test.wi464.Box", &[("T", "test.wi464.Animal.cat")]);
        let b = param(&mut kb, "test.wi464.Box", &[("T", "test.wi464.Animal.dog")]);
        let j = join_types(&mut kb, a, b).expect("the bare base sort is a common supertype");
        assert!(is_sort(&kb, &j, box_sym), "an unequal invariant binding widens to bare Box, got {j:?}");
    }

    /// CONTRAVARIANT: `Function.A` is contravariant, so its arm of the join takes the
    /// MEET of the two argument types — `meet(cat, dog) = nothing` — while the
    /// covariant `B` joins normally: `join(Function[A=cat,B=Int], Function[A=dog,B=Int])
    /// = Function[A = nothing, B = Int]`.
    #[test]
    fn contravariant_join_uses_meet() {
        let mut kb = load_kb();
        let (function, int) = (sym(&kb, "anthill.prelude.Function"), sym(&kb, "anthill.prelude.Int64"));
        let a = param(&mut kb, "anthill.prelude.Function",
            &[("A", "test.wi464.Animal.cat"), ("B", "anthill.prelude.Int64")]);
        let b = param(&mut kb, "anthill.prelude.Function",
            &[("A", "test.wi464.Animal.dog"), ("B", "anthill.prelude.Int64")]);
        let j = join_types(&mut kb, a, b).expect("two Function types have a join");
        let (base, binds) = as_param(&kb, &j);
        assert_eq!(base, function, "join base sort is Function");
        assert!(is_nothing(&kb, binding(&kb, &binds, "A")), "contravariant A meets cat/dog to nothing");
        assert!(is_sort(&kb, binding(&kb, &binds, "B"), int), "covariant B joins Int/Int to Int");
    }

    /// GLB basics — `meet_types` is total (the lattice has a `nothing` bottom):
    /// `meet(Animal, cat) = cat` (the subtype), `meet(cat, dog) = nothing`
    /// (incomparable siblings), and a covariant parameterized meet recurses:
    /// `meet(Option[T=cat], Option[T=dog]) = Option[T = nothing]`.
    #[test]
    fn meet_glb_basics() {
        let mut kb = load_kb();
        let (cat, option) = (sym(&kb, "test.wi464.Animal.cat"), sym(&kb, "anthill.prelude.Option"));

        let animal_v = bare(&mut kb, "test.wi464.Animal");
        let cat_v = bare(&mut kb, "test.wi464.Animal.cat");
        let m1 = meet_types(&mut kb, animal_v, cat_v);
        assert!(is_sort(&kb, &m1, cat), "meet(Animal, cat) is the subtype cat, got {m1:?}");

        let cat_v = bare(&mut kb, "test.wi464.Animal.cat");
        let dog_v = bare(&mut kb, "test.wi464.Animal.dog");
        let m2 = meet_types(&mut kb, cat_v, dog_v);
        assert!(is_nothing(&kb, &m2), "meet(cat, dog) is the bottom type nothing, got {m2:?}");

        let oa = param(&mut kb, "anthill.prelude.Option", &[("T", "test.wi464.Animal.cat")]);
        let ob = param(&mut kb, "anthill.prelude.Option", &[("T", "test.wi464.Animal.dog")]);
        let m3 = meet_types(&mut kb, oa, ob);
        let (base, binds) = as_param(&kb, &m3);
        assert_eq!(base, option, "meet base sort is Option");
        assert!(is_nothing(&kb, binding(&kb, &binds, "T")), "covariant T meets cat/dog to nothing");
    }
}
