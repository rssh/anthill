//! Eval-time builtins for `anthill.reflect.KB.*` introspection operations.
//!
//! Scripts call `KB.sort_template`, `KB.sorts`, `KB.operations`, … and get
//! `Value`-typed results whose shapes match the sort declarations in
//! `stdlib/anthill/reflect/reflect.anthill`. The heavy lifting — walking KB
//! facts, extracting named args, collecting cons-lists — is inline here over
//! `&mut KnowledgeBase`. The sibling `bridge.rs` does the same for host-Rust
//! callers; consolidating the two paths is tracked separately.

use std::rc::Rc;

use anthill_core::eval::builtins::{expect_args, register_if_present, require_symbol};
use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term as CoreTerm, TermId, Var};

use crate::reflect::reader;

/// Symbols the reflect builtins need at runtime. Resolved once at registration
/// so per-call paths compare `Symbol`s instead of scanning strings.
#[derive(Debug)]
struct ReflectSyms {
    // List primitives
    cons: Symbol,
    nil: Symbol,
    head: Symbol,
    tail: Symbol,

    // Option primitives (used to check `none` via empty-named entity)
    // — no stored symbol needed; unwrap-by-shape.

    // Reflect entity functors
    sort_info: Symbol,
    operation_info: Symbol,
    field_info: Symbol,
    description_info: Symbol,
    sort_query: Symbol,

    // TermRepr + LiteralRepr functors
    const_repr: Symbol,
    var_repr: Symbol,
    fn_repr: Symbol,
    ref_repr: Symbol,
    int_lit: Symbol,
    bigint_lit: Symbol,
    float_lit: Symbol,
    str_lit: Symbol,
    bool_lit: Symbol,
    pair: Symbol,

    // Field-name symbols
    f_name: Symbol,
    f_kind: Symbol,
    f_definition: Symbol,
    f_constructors: Symbol,
    f_operations: Symbol,
    f_parameters: Symbol,
    f_requires: Symbol,
    f_ensures: Symbol,
    f_meta: Symbol,
    f_params: Symbol,
    f_return_type: Symbol,
    f_effects: Symbol,
    f_type_name: Symbol,
    f_target: Symbol,
    f_content: Symbol,
    f_index: Symbol,
    f_value: Symbol,
    f_args: Symbol,
    f_sort_name: Symbol,
    f_fst: Symbol,
    f_snd: Symbol,
}

impl ReflectSyms {
    /// Resolve every reflect symbol. Fails if the stdlib isn't loaded —
    /// surfacing as `EvalError::Internal` so the caller at `register_reflect_builtins`
    /// sees a clear single-point error rather than deferred per-builtin failures.
    fn resolve(kb: &mut KnowledgeBase) -> Result<Self, EvalError> {
        fn req(kb: &KnowledgeBase, qname: &'static str) -> Result<Symbol, EvalError> {
            kb.try_resolve_symbol(qname).ok_or_else(||
                EvalError::Internal(format!("{qname} not in scope — stdlib not loaded")))
        }
        Ok(Self {
            cons: req(kb, "anthill.prelude.List.cons")?,
            nil: req(kb, "anthill.prelude.List.nil")?,
            head: kb.intern("head"),
            tail: kb.intern("tail"),

            sort_info: req(kb, "anthill.reflect.SortInfo")?,
            operation_info: req(kb, "anthill.reflect.OperationInfo")?,
            field_info: req(kb, "anthill.reflect.FieldInfo")?,
            description_info: req(kb, "anthill.reflect.DescriptionInfo")?,
            sort_query: req(kb, "anthill.reflect.LogicalQuery.sort_query")?,

            const_repr: req(kb, "anthill.reflect.TermRepr.ConstRepr")?,
            var_repr: req(kb, "anthill.reflect.TermRepr.VarRepr")?,
            fn_repr: req(kb, "anthill.reflect.TermRepr.FnRepr")?,
            ref_repr: req(kb, "anthill.reflect.TermRepr.RefRepr")?,
            int_lit: req(kb, "anthill.reflect.LiteralRepr.IntLiteral")?,
            bigint_lit: req(kb, "anthill.reflect.LiteralRepr.BigIntLiteral")?,
            float_lit: req(kb, "anthill.reflect.LiteralRepr.FloatLiteral")?,
            str_lit: req(kb, "anthill.reflect.LiteralRepr.StringLiteral")?,
            bool_lit: req(kb, "anthill.reflect.LiteralRepr.BoolLiteral")?,
            pair: req(kb, "anthill.prelude.Pair.pair")?,

            f_name: kb.intern("name"),
            f_kind: kb.intern("kind"),
            f_definition: kb.intern("definition"),
            f_constructors: kb.intern("constructors"),
            f_operations: kb.intern("operations"),
            f_parameters: kb.intern("parameters"),
            f_requires: kb.intern("requires"),
            f_ensures: kb.intern("ensures"),
            f_meta: kb.intern("meta"),
            f_params: kb.intern("params"),
            f_return_type: kb.intern("return_type"),
            f_effects: kb.intern("effects"),
            f_type_name: kb.intern("type_name"),
            f_target: kb.intern("target"),
            f_content: kb.intern("content"),
            f_index: kb.intern("index"),
            f_value: kb.intern("value"),
            f_args: kb.intern("args"),
            f_sort_name: kb.intern("sort_name"),
            f_fst: kb.intern("fst"),
            f_snd: kb.intern("snd"),
        })
    }
}

/// Register every reflect builtin whose qualified name resolves in the KB.
/// Missing symbols (partial stdlib load) fail at resolve time, so callers
/// either have a full reflect stdlib or see one clear error.
pub fn register_reflect_builtins(interp: &mut Interpreter) -> Result<(), EvalError> {
    // If reflect symbols aren't present at all, skip registration silently —
    // matches `register_if_present` policy for partial-stdlib harnesses.
    if interp.kb().try_resolve_symbol("anthill.reflect.SortInfo").is_none() {
        return Ok(());
    }
    let syms = Rc::new(ReflectSyms::resolve(interp.kb_mut())?);

    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.sort_template",
        move |i, a| kb_sort_template(i, a, &s))?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.sorts",
        move |i, a| kb_sorts(i, a, &s))?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.operations",
        move |i, a| kb_operations(i, a, &s))?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.constructors",
        move |i, a| kb_constructors(i, a, &s))?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.fields",
        move |i, a| kb_fields(i, a, &s))?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.rules",
        move |i, a| kb_rules(i, a, &s))?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.descriptions",
        move |i, a| kb_descriptions(i, a, &s))?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.reify",
        move |i, a| kb_reify(i, a, &s))?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.reflect",
        move |i, a| kb_reflect(i, a, &s))?;

    // Namespace-level symbol ops (no cached syms needed beyond `_kb` sentinel).
    register_if_present(interp, "anthill.reflect.qualified_name", qualified_name)?;
    register_if_present(interp, "anthill.reflect.short_name", short_name_op)?;
    register_if_present(interp, "anthill.reflect.lookup_symbol", lookup_symbol_op)?;
    register_if_present(interp, "anthill.reflect.scope", scope_op)?;
    register_if_present(interp, "anthill.reflect.kind", kind_op)?;

    register_if_present(interp, "anthill.reflect.KB.nonvar", kb_nonvar)?;
    register_if_present(interp, "anthill.reflect.KB.ground", kb_ground)?;

    register_if_present(interp, "anthill.reflect.sort_as_term", sort_as_term)?;
    register_if_present(interp, "anthill.reflect.can_be_sort", can_be_sort)?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.term_as_sort",
        move |i, a| term_as_sort(i, a, &s))?;

    register_if_present(interp, "anthill.reflect.field_access", field_access)?;
    register_if_present(interp, "anthill.reflect.resolve_sort_instantiation_param",
        resolve_sort_instantiation_param)?;

    register_if_present(interp, "anthill.reflect.Substitution.apply", subst_apply)?;
    register_if_present(interp, "anthill.reflect.Substitution.compose", subst_compose)?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.Substitution.bindings",
        move |i, a| subst_bindings(i, a, &s))?;

    register_if_present(interp, "anthill.reflect.not", reflect_not)?;

    Ok(())
}

// ── KB introspection helpers ────────────────────────────────────
//
// The carrier-agnostic KB walks — `facts_by_sort_name`, `term_named_args`,
// `term_pos_args`, `term_display_name`, `short_of`, `collect_list_terms`,
// `members_of_kind`, and the per-op record readers — live in the shared
// `reader` module (WI-551). The builtins below map a `reader` record to a
// `Value` result; the host bridge maps the SAME record to a typed struct.

// ── Value helpers ──────────────────────────────────────────────

fn str_arg(v: Value) -> Result<String, EvalError> {
    match v {
        Value::Str(s) => Ok(s),
        other => Err(EvalError::TypeMismatch { expected: "String", got: other.type_name().to_string() }),
    }
}

/// Unwrap `Option.some(value: s)` / `Option.none` → `Option<String>`.
fn option_string_arg(v: Value) -> Result<Option<String>, EvalError> {
    match v {
        Value::Entity { named, .. } => {
            if let Some((_, inner)) = named.into_iter().next() {
                Ok(Some(str_arg(inner.clone())?))
            } else {
                Ok(None)
            }
        }
        other => Err(EvalError::TypeMismatch { expected: "Option[String]", got: other.type_name().to_string() }),
    }
}

/// Build a `cons(head:_, tail:_)` chain terminated by `nil()` as a `Value`.
fn build_list_value(syms: &ReflectSyms, elements: Vec<Value>) -> Value {
    let mut acc = Value::Entity { functor: syms.nil, pos: Vec::new().into(), named: Vec::new().into() };
    for elem in elements.into_iter().rev() {
        acc = Value::Entity {
            functor: syms.cons,
            pos: Vec::new().into(),
            named: vec![(syms.head, elem), (syms.tail, acc)].into(),
        };
    }
    acc
}

/// Build a `Value::Entity` with named fields, sorted into the canonical order
/// declared at entity registration time (Symbol::index fallback).
fn make_entity(kb: &KnowledgeBase, functor: Symbol, mut named: Vec<(Symbol, Value)>) -> Value {
    if named.len() >= 2 {
        match kb.entity_field_names(functor) {
            Some(order) => named.sort_by_key(|(s, _)|
                order.iter().position(|f| f == s).unwrap_or(usize::MAX)),
            None => named.sort_by_key(|(s, _)| s.index()),
        }
    }
    Value::Entity { functor, pos: Vec::new().into(), named: named.into() }
}

// ── Builtin handlers ───────────────────────────────────────────

fn kb_sort_template(
    _interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, name] = expect_args::<2>("KB.sort_template", args)?;
    let name_str = str_arg(name)?;
    Ok(Value::Entity {
        functor: syms.sort_query,
        pos: Vec::new().into(),
        named: vec![(syms.f_sort_name, Value::Str(name_str))].into(),
    })
}

fn kb_sorts(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, ns] = expect_args::<2>("KB.sorts", args)?;
    let namespace = option_string_arg(ns)?;
    let kb = interp.kb_mut();

    let mut entries: Vec<Value> = Vec::new();
    for rec in reader::read_sort_infos(kb, namespace.as_deref()) {
        let list = |ts: Vec<TermId>| build_list_value(syms, ts.into_iter().map(Value::Term).collect());
        let mut fields = vec![
            (syms.f_name, Value::Term(rec.name)),
            (syms.f_definition, Value::Term(rec.definition)),
            (syms.f_constructors, list(rec.constructors)),
            (syms.f_operations, list(rec.operations)),
            (syms.f_parameters, list(rec.parameters)),
            (syms.f_requires, list(rec.requires)),
        ];
        if let Some(k) = rec.kind {
            fields.push((syms.f_kind, Value::Term(k)));
        }
        entries.push(make_entity(kb, syms.sort_info, fields));
    }
    Ok(build_list_value(syms, entries))
}

fn kb_operations(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, sort_name] = expect_args::<2>("KB.operations", args)?;
    let sort_name = str_arg(sort_name)?;
    let kb = interp.kb_mut();

    // The shared reader walks the `OperationInfo` facts through the `op_info`
    // funnel (WI-348/548): `name` / `return_type` / `params` / `meta` are ground
    // `TermId`s, while `effects` / `requires` / `ensures` ride as carrier-faithful
    // `Value`s (a `Modify[c]` label or denoted precondition stays a `Value::Node`).
    // The interpreter is dynamically typed, so the spec's `List[NodeOccurrence]`
    // contract fields just hold those clause `Value`s directly. `requires` carries
    // the loader's synthetic `EffectsRuntime[Effects=E]` clause (WI-320); `ensures`
    // is user clauses only.
    let mut entries: Vec<Value> = Vec::new();
    for rec in reader::read_operations(kb, &sort_name) {
        let params_v = build_list_value(syms, rec.params.into_iter().map(Value::Term).collect());
        let effects_v = build_list_value(syms, rec.effects);
        let requires_v = build_list_value(syms, rec.requires);
        let ensures_v = build_list_value(syms, rec.ensures);
        let fields = vec![
            (syms.f_name, Value::Term(rec.name)),
            (syms.f_params, params_v),
            (syms.f_return_type, Value::Term(rec.return_type)),
            (syms.f_effects, effects_v),
            (syms.f_requires, requires_v),
            (syms.f_ensures, ensures_v),
            (syms.f_meta, Value::Term(rec.meta)),
        ];
        entries.push(make_entity(kb, syms.operation_info, fields));
    }
    Ok(build_list_value(syms, entries))
}

fn kb_constructors(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, sort_name] = expect_args::<2>("KB.constructors", args)?;
    let sort_name = str_arg(sort_name)?;
    let kb = interp.kb_mut();
    let items: Vec<Value> = reader::members_of_kind(kb, &sort_name, "Constructor")
        .into_iter()
        .map(|n| Value::Str(reader::short_of(&n).to_string()))
        .collect();
    Ok(build_list_value(syms, items))
}

fn kb_fields(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, name] = expect_args::<2>("KB.fields", args)?;
    let name = str_arg(name)?;
    let kb = interp.kb_mut();

    // The shared reader returns the matching entity's `(field_name, field_type)`
    // pairs carrier-agnostically (WI-342): a value-in-type field (`Vector[Int64,
    // 3]`) rides as its own `Value::Node` into the FieldInfo, surfaced verbatim.
    let mut items: Vec<Value> = Vec::new();
    if let Some(rec) = reader::read_entity_fields(kb, &name) {
        for (field_sym, field_type) in rec.fields {
            let name_val = Value::Str(kb.resolve_sym(field_sym).to_string());
            let fields = vec![
                (syms.f_name, name_val),
                (syms.f_type_name, field_type),
            ];
            items.push(make_entity(kb, syms.field_info, fields));
        }
    }
    Ok(build_list_value(syms, items))
}

fn kb_rules(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, sort_name] = expect_args::<2>("KB.rules", args)?;
    let sort_name = str_arg(sort_name)?;
    let kb = interp.kb_mut();

    let mut items: Vec<Value> = Vec::new();
    for head in reader::rule_heads_for_sort(kb, &sort_name) {
        // A `Rule` fact head is the rule's predicate term — always hash-consed
        // (rules are not value facts), so the carrier-agnostic head reifies via
        // its `TermId`.
        let head_tid = head.expect_term();
        items.push(reify_term_to_value(kb, syms, head_tid));
    }
    Ok(build_list_value(syms, items))
}

fn kb_descriptions(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, target] = expect_args::<2>("KB.descriptions", args)?;
    let target = option_string_arg(target)?;
    let kb = interp.kb_mut();

    // The reader yields `Description(target, content, index)` records; the index
    // is the STORED 0-based per-target index (WI-438), not a global enumeration.
    let mut items: Vec<Value> = Vec::new();
    for rec in reader::read_descriptions(kb, target.as_deref()) {
        let fields = vec![
            (syms.f_target, Value::Term(rec.target)),
            (syms.f_content, Value::Str(rec.content)),
            (syms.f_index, Value::Int(rec.index)),
        ];
        items.push(make_entity(kb, syms.description_info, fields));
    }
    Ok(build_list_value(syms, items))
}

fn kb_reify(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, t] = expect_args::<2>("KB.reify", args)?;
    let tid = match t {
        Value::Term(tid) => tid,
        other => return Err(EvalError::TypeMismatch {
            expected: "Term", got: other.type_name().to_string(),
        }),
    };
    Ok(reify_term_to_value(interp.kb_mut(), syms, tid))
}

/// Build a `TermRepr` `Value` from a hash-consed `TermId`. Mirrors
/// `bridge.rs::KbBridge::reify_term` but emits `Value::Entity` results.
fn reify_term_to_value(kb: &mut KnowledgeBase, syms: &ReflectSyms, id: TermId) -> Value {
    let wrap_literal = |ctor: Symbol, inner: Value| -> Value {
        Value::Entity {
            functor: syms.const_repr,
            pos: Vec::new().into(),
            named: vec![(syms.f_value, Value::Entity {
                functor: ctor,
                pos: Vec::new().into(),
                named: vec![(syms.f_value, inner)].into(),
            })].into(),
        }
    };

    let term = kb.get_term(id).clone();
    match term {
        CoreTerm::Const(Literal::Int(n)) => wrap_literal(syms.int_lit, Value::Int(n)),
        CoreTerm::Const(Literal::BigInt(n)) => wrap_literal(syms.bigint_lit, Value::BigInt(n)),
        CoreTerm::Const(Literal::Float(f)) => wrap_literal(syms.float_lit, Value::Float(f.into_inner())),
        CoreTerm::Const(Literal::String(s)) => wrap_literal(syms.str_lit, Value::Str(s)),
        CoreTerm::Const(Literal::Bool(b)) => wrap_literal(syms.bool_lit, Value::Bool(b)),
        CoreTerm::Const(Literal::Handle(_, raw)) => wrap_literal(syms.int_lit, Value::Int(raw as i64)),
        CoreTerm::Var(Var::Global(vid)) => {
            let name = kb.resolve_sym(vid.name()).to_string();
            Value::Entity {
                functor: syms.var_repr,
                pos: Vec::new().into(),
                named: vec![(syms.f_name, Value::Str(name))].into(),
            }
        }
        CoreTerm::Var(Var::DeBruijn(n)) => Value::Entity {
            functor: syms.var_repr,
            pos: Vec::new().into(),
            named: vec![(syms.f_name, Value::Str(format!("_{n}")))].into(),
        },
        CoreTerm::Var(Var::Rigid(vid)) => Value::Entity {
            functor: syms.var_repr,
            pos: Vec::new().into(),
            named: vec![(syms.f_name, Value::Str(format!("!{}", kb.resolve_sym(vid.name()))))].into(),
        },
        CoreTerm::Ref(sym) | CoreTerm::Ident(sym) => {
            let name_term = kb.alloc(CoreTerm::Ref(sym));
            Value::Entity {
                functor: syms.ref_repr,
                pos: Vec::new().into(),
                named: vec![(syms.f_name, Value::Term(name_term))].into(),
            }
        }
        CoreTerm::Fn { functor, pos_args, named_args } => {
            let name_term = kb.alloc(CoreTerm::Ref(functor));
            let pos: Vec<TermId> = pos_args.iter().copied().collect();
            let named: Vec<TermId> = named_args.iter().map(|&(_, id)| id).collect();
            let mut children: Vec<Value> = Vec::with_capacity(pos.len() + named.len());
            for child_id in pos.into_iter().chain(named) {
                children.push(reify_term_to_value(kb, syms, child_id));
            }
            let args_list = build_list_value(syms, children);
            Value::Entity {
                functor: syms.fn_repr,
                pos: Vec::new().into(),
                named: vec![(syms.f_name, Value::Term(name_term)), (syms.f_args, args_list)].into(),
            }
        }
        CoreTerm::Bottom => {
            let bottom_sym = kb.intern("⊥");
            let name_term = kb.alloc(CoreTerm::Ref(bottom_sym));
            Value::Entity {
                functor: syms.ref_repr,
                pos: Vec::new().into(),
                named: vec![(syms.f_name, Value::Term(name_term))].into(),
            }
        }
        CoreTerm::ParseAux(_) => unreachable!(
            "parse-only Term::ParseAux variant reached reify_term_to_value \
             (should never reach the KB reflection layer)",
        ),
    }
}

/// `KB.reflect(kb: KB, r: TermRepr) -> Term` — inverse of `reify`. Walks a
/// `TermRepr` `Value::Entity` tree and allocates the corresponding hash-consed
/// `TermId`, returned as `Value::Term`.
fn kb_reflect(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, repr] = expect_args::<2>("KB.reflect", args)?;
    let tid = reflect_value_to_term(interp.kb_mut(), syms, repr)?;
    Ok(Value::Term(tid))
}

fn reflect_value_to_term(
    kb: &mut KnowledgeBase,
    syms: &ReflectSyms,
    repr: Value,
) -> Result<TermId, EvalError> {
    let (functor, named) = match repr {
        Value::Entity { functor, named, .. } => (functor, named),
        other => return Err(EvalError::TypeMismatch {
            expected: "TermRepr", got: other.type_name().to_string(),
        }),
    };
    let lookup = |key: Symbol| -> Option<Value> {
        named.iter().find(|(s, _)| *s == key).map(|(_, v)| v.clone())
    };

    if functor == syms.const_repr {
        // ConstRepr { value: <LiteralRepr> } → Const(Literal)
        let inner = lookup(syms.f_value)
            .ok_or_else(|| EvalError::Internal("ConstRepr: missing `value`".into()))?;
        let (lit_ctor, lit_val) = match inner {
            Value::Entity { functor, named, .. } => {
                let v = named.iter().find(|(s, _)| *s == syms.f_value)
                    .map(|(_, v)| v.clone())
                    .ok_or_else(|| EvalError::Internal("LiteralRepr: missing `value`".into()))?;
                (functor, v)
            }
            other => return Err(EvalError::TypeMismatch {
                expected: "LiteralRepr", got: other.type_name().to_string(),
            }),
        };
        let lit = if lit_ctor == syms.int_lit {
            match lit_val {
                Value::Int(n) => Literal::Int(n),
                other => return Err(EvalError::TypeMismatch {
                    expected: "Int64", got: other.type_name().to_string(),
                }),
            }
        } else if lit_ctor == syms.bigint_lit {
            // BigIntLiteral is its own first-class case (WI-543); IntLiteral
            // stays Int64-only above.
            match lit_val {
                Value::BigInt(n) => Literal::BigInt(n),
                Value::Int(n) => Literal::BigInt(n.into()),
                other => return Err(EvalError::TypeMismatch {
                    expected: "BigInt", got: other.type_name().to_string(),
                }),
            }
        } else if lit_ctor == syms.float_lit {
            match lit_val {
                Value::Float(f) => Literal::Float(f.into()),
                other => return Err(EvalError::TypeMismatch {
                    expected: "Float", got: other.type_name().to_string(),
                }),
            }
        } else if lit_ctor == syms.str_lit {
            match lit_val {
                Value::Str(s) => Literal::String(s),
                other => return Err(EvalError::TypeMismatch {
                    expected: "String", got: other.type_name().to_string(),
                }),
            }
        } else if lit_ctor == syms.bool_lit {
            match lit_val {
                Value::Bool(b) => Literal::Bool(b),
                other => return Err(EvalError::TypeMismatch {
                    expected: "Bool", got: other.type_name().to_string(),
                }),
            }
        } else {
            return Err(EvalError::Internal(format!(
                "unknown LiteralRepr ctor: {}", kb.resolve_sym(lit_ctor))));
        };
        Ok(kb.alloc(CoreTerm::Const(lit)))
    } else if functor == syms.var_repr {
        let name = lookup(syms.f_name)
            .ok_or_else(|| EvalError::Internal("VarRepr: missing `name`".into()))?;
        let name_str = str_arg(name)?;
        let sym = kb.intern(&name_str);
        let vid = kb.fresh_var(sym);
        Ok(kb.alloc(CoreTerm::Var(Var::Global(vid))))
    } else if functor == syms.ref_repr {
        let name = lookup(syms.f_name)
            .ok_or_else(|| EvalError::Internal("RefRepr: missing `name`".into()))?;
        let tid = match name {
            Value::Term(t) => t,
            other => return Err(EvalError::TypeMismatch {
                expected: "Term (name symbol)", got: other.type_name().to_string(),
            }),
        };
        let sym = match kb.get_term(tid) {
            CoreTerm::Ref(s) | CoreTerm::Ident(s) => *s,
            _ => return Err(EvalError::Internal(
                "RefRepr.name must resolve to Ref/Ident".into())),
        };
        Ok(kb.alloc(CoreTerm::Ref(sym)))
    } else if functor == syms.fn_repr {
        let name = lookup(syms.f_name)
            .ok_or_else(|| EvalError::Internal("FnRepr: missing `name`".into()))?;
        let name_tid = match name {
            Value::Term(t) => t,
            other => return Err(EvalError::TypeMismatch {
                expected: "Term (functor symbol)", got: other.type_name().to_string(),
            }),
        };
        let functor_sym = match kb.get_term(name_tid) {
            CoreTerm::Ref(s) | CoreTerm::Ident(s) => *s,
            _ => return Err(EvalError::Internal(
                "FnRepr.name must resolve to Ref/Ident".into())),
        };
        let args_list = lookup(syms.f_args)
            .ok_or_else(|| EvalError::Internal("FnRepr: missing `args`".into()))?;
        let mut child_ids: Vec<TermId> = Vec::new();
        let mut cur = args_list;
        loop {
            match cur {
                Value::Entity { functor: f, named, .. } => {
                    if f == syms.nil { break; }
                    if f != syms.cons {
                        return Err(EvalError::Internal(format!(
                            "FnRepr.args: expected cons-list, got {}", kb.resolve_sym(f))));
                    }
                    let head = named.iter().find(|(s, _)| *s == syms.head)
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| EvalError::Internal("cons: missing head".into()))?;
                    let tail = named.into_iter().find(|(s, _)| *s == syms.tail)
                        .map(|(_, v)| v)
                        .ok_or_else(|| EvalError::Internal("cons: missing tail".into()))?;
                    child_ids.push(reflect_value_to_term(kb, syms, head)?);
                    cur = tail.clone();
                }
                other => return Err(EvalError::TypeMismatch {
                    expected: "cons-list", got: other.type_name().to_string(),
                }),
            }
        }
        Ok(kb.alloc(CoreTerm::Fn {
            functor: functor_sym,
            pos_args: child_ids.into(),
            named_args: Default::default(),
        }))
    } else {
        Err(EvalError::Internal(format!(
            "unknown TermRepr ctor: {}", kb.resolve_sym(functor))))
    }
}

// ── Symbol ops (namespace-level) ─────────────────────────────────

fn expect_symbol(kb: &KnowledgeBase, v: Value, _op: &'static str) -> Result<Symbol, EvalError> {
    match v {
        Value::Term(tid) => match kb.get_term(tid) {
            CoreTerm::Ref(s) | CoreTerm::Ident(s) => Ok(*s),
            _ => Err(EvalError::TypeMismatch {
                expected: "Symbol (Ref/Ident term)", got: "other Term".into(),
            }),
        },
        other => Err(EvalError::TypeMismatch {
            expected: "Symbol", got: other.type_name().to_string(),
        }),
    }
}

fn qualified_name(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("qualified_name", args)?;
    let sym = expect_symbol(interp.kb(), s, "qualified_name")?;
    Ok(Value::Str(interp.kb().qualified_name_of(sym).to_string()))
}

fn short_name_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("short_name", args)?;
    let sym = expect_symbol(interp.kb(), s, "short_name")?;
    Ok(Value::Str(interp.kb().resolve_sym(sym).to_string()))
}

fn lookup_symbol_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [name] = expect_args::<1>("lookup_symbol", args)?;
    let name_str = str_arg(name)?;
    let sym = interp.kb().try_resolve_symbol(&name_str)
        .ok_or_else(|| EvalError::Internal(format!("lookup_symbol: '{}' not in scope", name_str)))?;
    Ok(Value::Term(interp.kb_mut().alloc(CoreTerm::Ref(sym))))
}

fn scope_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("scope", args)?;
    let sym = expect_symbol(interp.kb(), s, "scope")?;
    let scope_sym = interp.kb().scope_of(sym);
    // Lookup Option.some / Option.none every call — not hot path; keeping
    // these out of ReflectSyms because this op is reachable even with a
    // stripped reflect stdlib (it's a namespace-level op, not a KB method).
    let some_sym = interp.kb().try_resolve_symbol("anthill.prelude.Option.some")
        .ok_or_else(|| EvalError::Internal("anthill.prelude.Option.some not in scope".into()))?;
    let none_sym = interp.kb().try_resolve_symbol("anthill.prelude.Option.none")
        .ok_or_else(|| EvalError::Internal("anthill.prelude.Option.none not in scope".into()))?;
    let value_field = interp.kb_mut().intern("value");
    Ok(match scope_sym {
        Some(sym) => {
            let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(sym));
            Value::Entity {
                functor: some_sym,
                pos: Vec::new().into(),
                named: vec![(value_field, Value::Term(ref_tid))].into(),
            }
        }
        None => Value::Entity { functor: none_sym, pos: Vec::new().into(), named: Vec::new().into() },
    })
}

fn kind_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use anthill_core::intern::SymbolKind;
    let [s] = expect_args::<1>("kind", args)?;
    let sym = expect_symbol(interp.kb(), s, "kind")?;
    let kind_str = match interp.kb().kind_of(sym) {
        Some(SymbolKind::Sort) => "Sort",
        Some(SymbolKind::Entity) => "Entity",
        Some(SymbolKind::Operation) => "Operation",
        Some(SymbolKind::Const) => "Const",
        Some(SymbolKind::Namespace) => "Namespace",
        Some(SymbolKind::Fact) => "Fact",
        Some(SymbolKind::Rule) => "Rule",
        Some(SymbolKind::Constraint) => "Constraint",
        Some(SymbolKind::Param) => "Param",
        Some(SymbolKind::Field) => "Field",
        Some(SymbolKind::Goal) => "Goal",
        Some(SymbolKind::OpResult) => "OpResult",
        Some(SymbolKind::CallbackParam) => "CallbackParam",
        Some(SymbolKind::CallbackResult) => "CallbackResult",
        Some(SymbolKind::LocalLet) => "LocalLet",
        None => "Unresolved",
    };
    Ok(Value::Str(kind_str.into()))
}

// ── Term-shape predicates (eval-side, no DELAY) ─────────────────

fn expect_term(v: Value, op: &'static str) -> Result<TermId, EvalError> {
    match v {
        Value::Term(tid) => Ok(tid),
        other => Err(EvalError::TypeMismatch {
            expected: "Term", got: format!("{} for {op}", other.type_name()),
        }),
    }
}

/// `KB.nonvar(kb, x: Term) -> Bool` — true if `x` is not a variable term.
/// Eval-time runs after SLD, so arguments are already grounded where they
/// will be; no DELAY semantics needed here.
fn kb_nonvar(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb, x] = expect_args::<2>("KB.nonvar", args)?;
    let tid = expect_term(x, "KB.nonvar")?;
    Ok(Value::Bool(!matches!(interp.kb().get_term(tid), CoreTerm::Var(_))))
}

/// `KB.ground(kb, x: Term) -> Bool` — true if `x` contains no variables.
fn kb_ground(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb, x] = expect_args::<2>("KB.ground", args)?;
    let tid = expect_term(x, "KB.ground")?;
    Ok(Value::Bool(interp.kb().collect_vars(tid).is_empty()))
}

// ── Sort ↔ Term (identity passthroughs — Types ARE Terms) ────────

/// `sort_as_term(s: Type) -> Term` — Type and Term are both `TermId` in the
/// kernel (see memory `project_sort_data_distinction` / architecture note).
/// The operation exists for documentation and API symmetry.
fn sort_as_term(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("sort_as_term", args)?;
    // Accept any Value::Term — the user wrote it in a sort/type position.
    match s {
        Value::Term(_) => Ok(s),
        other => Err(EvalError::TypeMismatch {
            expected: "Type (Term handle)", got: other.type_name().to_string(),
        }),
    }
}

/// `can_be_sort(t: Term) -> Bool` — every well-formed `Term` can stand in
/// type position (sorts are terms). Literals and `Bottom` are rejected.
fn can_be_sort(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [t] = expect_args::<1>("can_be_sort", args)?;
    let tid = expect_term(t, "can_be_sort")?;
    let ok = !matches!(interp.kb().get_term(tid),
        CoreTerm::Const(_) | CoreTerm::Bottom);
    Ok(Value::Bool(ok))
}

/// `term_as_sort(t: Term) -> Option[T = Type]` — `some(t)` if `t` can be a
/// sort, `none` otherwise. Leverages `can_be_sort`.
fn term_as_sort(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [t] = expect_args::<1>("term_as_sort", args)?;
    let tid = expect_term(t, "term_as_sort")?;
    let ok = !matches!(interp.kb().get_term(tid),
        CoreTerm::Const(_) | CoreTerm::Bottom);
    let some_sym = interp.kb().try_resolve_symbol("anthill.prelude.Option.some")
        .ok_or_else(|| EvalError::Internal("Option.some not in scope".into()))?;
    let none_sym = interp.kb().try_resolve_symbol("anthill.prelude.Option.none")
        .ok_or_else(|| EvalError::Internal("Option.none not in scope".into()))?;
    if ok {
        Ok(Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(syms.f_value, Value::Term(tid))].into(),
        })
    } else {
        Ok(Value::Entity { functor: none_sym, pos: Vec::new().into(), named: Vec::new().into() })
    }
}

// ── Field access / sort instantiation ────────────────────────────

/// `field_access(object: Term, field: Symbol) -> Term` — extract a named
/// field from an entity term. Errors if `object` isn't a `Fn` with the named
/// arg present.
fn field_access(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [object, field] = expect_args::<2>("field_access", args)?;
    let obj_tid = expect_term(object, "field_access")?;
    let field_sym = expect_symbol(interp.kb(), field, "field_access")?;
    let kb = interp.kb();
    match kb.get_term(obj_tid) {
        CoreTerm::Fn { named_args, .. } => {
            named_args.iter()
                .find(|(s, _)| *s == field_sym)
                .map(|(_, tid)| Value::Term(*tid))
                .ok_or_else(|| EvalError::Internal(format!(
                    "field_access: '{}' not found on entity '{}'",
                    kb.resolve_sym(field_sym),
                    match kb.get_term(obj_tid) {
                        CoreTerm::Fn { functor, .. } => kb.resolve_sym(*functor),
                        _ => "?",
                    })))
        }
        _ => Err(EvalError::TypeMismatch {
            expected: "entity Term", got: "other Term".into(),
        }),
    }
}

/// `resolve_sort_instantiation_param(inst: Term, param: Term) -> Term` —
/// given a `SortView(sort, param1=val1, …)` term and a `Ref(param)` term,
/// return the bound value. Currently implemented as a named-arg lookup
/// over the SortView's named args.
fn resolve_sort_instantiation_param(
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [inst, param] = expect_args::<2>("resolve_sort_instantiation_param", args)?;
    let inst_tid = expect_term(inst, "resolve_sort_instantiation_param")?;
    let param_sym = expect_symbol(interp.kb(), param, "resolve_sort_instantiation_param")?;
    let kb = interp.kb();
    match kb.get_term(inst_tid) {
        CoreTerm::Fn { named_args, .. } => {
            named_args.iter()
                .find(|(s, _)| *s == param_sym)
                .map(|(_, tid)| Value::Term(*tid))
                .ok_or_else(|| EvalError::Internal(format!(
                    "resolve_sort_instantiation_param: '{}' not bound",
                    kb.resolve_sym(param_sym))))
        }
        _ => Err(EvalError::TypeMismatch {
            expected: "SortView Term", got: "other Term".into(),
        }),
    }
}

// ── Substitution.apply / .compose ───────────────────────────────

/// `Substitution.apply(s: Substitution, t: Term, kb: KB) -> Term`.
/// Rewrites `t` by walking every variable binding in `s`. Borrows the
/// substitution through the arena — no clone of `s`.
fn subst_apply(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, t, _kb] = expect_args::<3>("Substitution.apply", args)?;
    let handle = match s {
        Value::Substitution(h) => h,
        other => return Err(EvalError::TypeMismatch {
            expected: "Substitution", got: other.type_name().to_string(),
        }),
    };
    let tid = expect_term(t, "Substitution.apply")?;
    // The arena is on `interp.substs`; the KB on `interp.kb`. These are
    // independent fields, so we can hold a shared borrow on the arena
    // (via the cloned Rc) while mutably borrowing the KB.
    let arena = interp.subst_arena();
    let kb = interp.kb_mut();
    let applied = arena.with_subst(&handle, |s| kb.apply_subst(tid, s));
    Ok(Value::Term(applied))
}

/// `Substitution.compose(s1: Substitution, s2: Substitution, kb: KB) -> Substitution`.
/// Produces a new substitution: s2 applied to every Term-valued binding of
/// s1, extended by s2's bindings where the variable doesn't already appear
/// in s1. Borrows both substitutions through the arena — no full clones.
fn subst_compose(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s1, s2, _kb] = expect_args::<3>("Substitution.compose", args)?;
    let h1 = match s1 {
        Value::Substitution(h) => h,
        other => return Err(EvalError::TypeMismatch {
            expected: "Substitution", got: other.type_name().to_string(),
        }),
    };
    let h2 = match s2 {
        Value::Substitution(h) => h,
        other => return Err(EvalError::TypeMismatch {
            expected: "Substitution", got: other.type_name().to_string(),
        }),
    };

    let arena = interp.subst_arena();
    let kb = interp.kb_mut();
    let composed = arena.with_subst(&h1, |s1| {
        arena.with_subst(&h2, |s2| {
            let mut result = anthill_core::kb::subst::Substitution::new();
            // (WI-569: `bindings` is an `imbl::HashMap` — persistent, no `reserve`.)
            for (var, val) in s1.bindings.iter() {
                let new_val = match val {
                    Value::Term(tid) => Value::Term(kb.apply_subst(*tid, s2)),
                    // WI-547: a bare value-level var binding chases through s2
                    // (reify_value resolves a bound var, recursively).
                    Value::Var(_) => kb.reify_value(val, s2),
                    other => other.clone(),
                };
                result.bindings.insert(*var, new_val);
            }
            for (var, val) in s2.bindings.iter() {
                result.bindings.entry(*var).or_insert_with(|| val.clone());
            }
            result
        })
    });

    let handle = interp.alloc_subst(composed);
    Ok(Value::Substitution(handle))
}

/// `Substitution.bindings(s: Substitution) -> List[Pair[Term, Term]]`.
/// Enumerate the substitution as (variable, value) pairs — the variable as a
/// var `Term` (`Value::Term(Var)`) so a consumer can recover its identity (the
/// full-walk dual of `lookup`'s single by-name read). Lets the host bridge's
/// `compose` merge by variable across the `&dyn Substitution` boundary, but is
/// a first-class reflect op.
fn subst_bindings(interp: &mut Interpreter, args: &[Value], syms: &ReflectSyms) -> Result<Value, EvalError> {
    let [subst_val] = expect_args::<1>("Substitution.bindings", args)?;
    let handle = match subst_val {
        Value::Substitution(h) => h,
        other => return Err(EvalError::TypeMismatch {
            expected: "Substitution", got: other.type_name().to_string(),
        }),
    };
    let arena = interp.subst_arena();
    let entries: Vec<_> = arena.with_subst(&handle, |s| {
        s.iter().map(|(vid, val)| (*vid, val.clone())).collect::<Vec<_>>()
    });
    let kb = interp.kb_mut();
    let pairs: Vec<Value> = entries.into_iter().map(|(vid, val)| {
        let var_tid = kb.alloc(CoreTerm::Var(Var::Global(vid)));
        make_entity(kb, syms.pair, vec![
            (syms.f_fst, Value::Term(var_tid)),
            (syms.f_snd, val),
        ])
    }).collect();
    Ok(build_list_value(syms, pairs))
}

// ── reflect.not (WI-080) ────────────────────────────────────────

/// `reflect.not(query: Term) -> Bool` — eval-time negation-as-failure.
/// Wraps `query` in a resolver `not(...)` goal and runs a fresh one-shot
/// SLD search. If the resolver surfaces a residual (floundering: query
/// has unbound variables), raises an error — NAF is unsound on ungrounded
/// goals and the eval context has no outer frame to resume on.
fn reflect_not(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [q] = expect_args::<1>("reflect.not", args)?;
    let goal_tid = expect_term(q, "reflect.not")?;
    let not_sym = require_symbol(interp, "anthill.reflect.not", "not")?;
    let not_goal = interp.kb_mut().alloc(CoreTerm::Fn {
        functor: not_sym,
        pos_args: vec![goal_tid].into(),
        named_args: Default::default(),
    });
    let kb = interp.kb_mut();
    let stream = kb.resolve_lazy(&[not_goal], &ResolveConfig::default());
    match stream.split_first(kb) {
        None => Ok(Value::Bool(false)),
        Some((sol, _rest)) if sol.residual.is_empty() => Ok(Value::Bool(true)),
        Some(_) => Err(EvalError::Internal(
            "reflect.not: floundering — query has unbound variables; bind them before calling".into())),
    }
}

// ── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    use anthill_core::eval::{self, Interpreter, Value};
    use anthill_core::kb::KnowledgeBase;
    use anthill_core::kb::load::{self, NullResolver};
    use anthill_core::parse;

    fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
        let mut files = Vec::new();
        if dir.is_dir() {
            for entry in std::fs::read_dir(dir).expect("read stdlib dir") {
                let entry = entry.expect("read dir entry");
                let path = entry.path();
                if path.is_dir() {
                    files.extend(collect_anthill_files(&path));
                } else if path.extension().is_some_and(|e| e == "anthill") {
                    files.push(path);
                }
            }
        }
        files.sort();
        files
    }

    fn load_stdlib_and_source(source: &str) -> Interpreter {
        let stdlib_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../stdlib/anthill");
        let files = collect_anthill_files(&stdlib_dir);
        assert!(!files.is_empty(), "stdlib empty");
        let mut parsed: Vec<_> = files.iter().map(|f| {
            let src = std::fs::read_to_string(f).expect("read stdlib");
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", f.display()))
        }).collect();
        parsed.push(parse::parse(source).expect("parse user source"));
        let refs: Vec<_> = parsed.iter().collect();

        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        load::load_all(&mut kb, &refs, &NullResolver)
            .unwrap_or_else(|errs| { for e in &errs { eprintln!("{}", e); } panic!("load failed"); });

        let mut interp = Interpreter::new(kb);
        eval::builtins::register_standard_builtins(&mut interp)
            .expect("register core builtins");
        register_reflect_builtins(&mut interp)
            .expect("register reflect builtins");
        interp
    }

    #[test]
    fn kb_sort_template_returns_sort_query_value() {
        let mut interp = load_stdlib_and_source(r#"
namespace test.reflect_sort_tmpl
  sort Color
    entity red
    entity green
  end
end
"#);
        let result = interp.call("anthill.reflect.KB.sort_template",
            &[Value::Unit, Value::Str("Color".into())])
            .expect("sort_template call");
        match result {
            Value::Entity { functor, named, .. } => {
                let name = interp.kb().resolve_sym(functor).to_string();
                assert_eq!(name, "sort_query");
                assert_eq!(named.len(), 1);
                match &named[0].1 {
                    Value::Str(s) => assert_eq!(s, "Color"),
                    other => panic!("expected Str, got {other:?}"),
                }
            }
            other => panic!("expected Entity, got {other:?}"),
        }
    }

    #[test]
    fn kb_sorts_lists_defined_sorts() {
        let mut interp = load_stdlib_and_source(r#"
namespace test.reflect_sorts
  sort Color
    entity red
  end
  sort Shape
    entity circle
  end
end
"#);
        let none_sym = interp.kb_mut().try_resolve_symbol("anthill.prelude.Option.none")
            .expect("Option.none");
        let none_val = Value::Entity { functor: none_sym, pos: Vec::new().into(), named: Vec::new().into() };
        let result = interp.call("anthill.reflect.KB.sorts", &[Value::Unit, none_val])
            .expect("sorts call");
        let mut count = 0;
        let mut cur = result;
        loop {
            match cur {
                Value::Entity { functor, ref named, .. } => {
                    let fname = interp.kb().resolve_sym(functor).to_string();
                    if fname == "nil" { break; }
                    if fname != "cons" { panic!("expected cons, got {fname}"); }
                    count += 1;
                    cur = named.iter().find(|(s, _)|
                        interp.kb().resolve_sym(*s) == "tail"
                    ).map(|(_, v)| v.clone()).expect("cons tail");
                }
                other => panic!("non-entity in list: {other:?}"),
            }
        }
        assert!(count >= 2, "expected at least 2 sorts (Color + Shape), got {count}");
    }

    #[test]
    fn kb_descriptions_index_is_per_target_not_global() {
        // WI-438: Description(target, text, index) stores a 0-based PER-TARGET
        // index (kb/load.rs emit_desc_fact). A target-filtered query must report
        // that stored index, not a global enumeration over ALL Description facts.
        // Alpha's two descriptions precede Beta's, so a global counter would give
        // Beta's descriptions indices [2, 3]; the stored per-target indices are
        // [0, 1]. The bug filled DescriptionInfo.index with the global enumerate
        // counter (and bridge.rs dropped the index entirely).
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.wi438
  sort Alpha = ?
  sort Beta = ?
  describe Alpha {< first alpha >}
  describe Alpha {< second alpha >}
  describe Beta {< first beta >}
  describe Beta {< second beta >}
end
"#,
        );
        let some_sym = interp
            .kb_mut()
            .try_resolve_symbol("anthill.prelude.Option.some")
            .expect("Option.some");
        let value_sym = interp.kb_mut().intern("value");
        let target = Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_sym, Value::Str("Beta".into()))].into(),
        };
        let result = interp
            .call("anthill.reflect.KB.descriptions", &[Value::Unit, target])
            .expect("descriptions call");

        // Walk the cons-list, collecting (content, index) per DescriptionInfo.
        let mut pairs: Vec<(String, i64)> = Vec::new();
        let mut cur = result;
        while let Value::Entity { functor, named, .. } = cur {
            let fname = interp.kb().resolve_sym(functor).to_string();
            if fname == "nil" {
                break;
            }
            assert_eq!(fname, "cons", "expected cons in result list");
            let head = named
                .iter()
                .find(|(s, _)| interp.kb().resolve_sym(*s) == "head")
                .map(|(_, v)| v.clone())
                .expect("cons head");
            let tail = named
                .iter()
                .find(|(s, _)| interp.kb().resolve_sym(*s) == "tail")
                .map(|(_, v)| v.clone())
                .expect("cons tail");
            match head {
                Value::Entity { named: dn, .. } => {
                    let content = dn
                        .iter()
                        .find(|(s, _)| interp.kb().resolve_sym(*s) == "content")
                        .and_then(|(_, v)| v.as_str().map(str::to_string))
                        .expect("content field");
                    let index = dn
                        .iter()
                        .find(|(s, _)| interp.kb().resolve_sym(*s) == "index")
                        .and_then(|(_, v)| v.as_int())
                        .expect("index field");
                    pairs.push((content, index));
                }
                other => panic!("expected DescriptionInfo entity, got {other:?}"),
            }
            cur = tail;
        }

        pairs.sort();
        assert_eq!(
            pairs,
            vec![
                ("first beta".to_string(), 0),
                ("second beta".to_string(), 1),
            ],
            "Beta's descriptions must carry the STORED per-target index [0, 1], \
             not a global enumeration [2, 3] (WI-438)",
        );
    }

    #[test]
    fn kb_reflect_roundtrips_a_ref_repr() {
        let mut interp = load_stdlib_and_source(r#"
namespace test.reflect_roundtrip
  sort Color
    entity red
  end
end
"#);
        let sym = interp.kb().try_resolve_symbol("test.reflect_roundtrip.Color.red")
            .expect("red symbol");
        let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(sym));
        // reify → TermRepr (Value::Entity); reflect → back to Term (Value::Term).
        let reified = interp.call("anthill.reflect.KB.reify",
            &[Value::Unit, Value::Term(ref_tid)])
            .expect("reify call");
        let reflected = interp.call("anthill.reflect.KB.reflect",
            &[Value::Unit, reified])
            .expect("reflect call");
        match reflected {
            Value::Term(tid) => {
                // Same symbol round-trip → same TermId (hash-consed).
                assert_eq!(tid, ref_tid);
            }
            other => panic!("expected Value::Term, got {other:?}"),
        }
    }

    #[test]
    fn kb_nonvar_and_ground_classify_terms() {
        let mut interp = load_stdlib_and_source(r#"
namespace test.reflect_nonvar
  sort Color
    entity red
  end
end
"#);
        // A Ref term is nonvar + ground.
        let sym = interp.kb().try_resolve_symbol("test.reflect_nonvar.Color.red")
            .expect("red symbol");
        let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(sym));
        let nv = interp.call("anthill.reflect.KB.nonvar",
            &[Value::Unit, Value::Term(ref_tid)]).expect("nonvar");
        assert!(matches!(nv, Value::Bool(true)));
        let g = interp.call("anthill.reflect.KB.ground",
            &[Value::Unit, Value::Term(ref_tid)]).expect("ground");
        assert!(matches!(g, Value::Bool(true)));

        // A fresh Var term is neither nonvar nor ground.
        let vsym = interp.kb_mut().intern("x");
        let vid = interp.kb_mut().fresh_var(vsym);
        let var_tid = interp.kb_mut().alloc(CoreTerm::Var(Var::Global(vid)));
        let nv = interp.call("anthill.reflect.KB.nonvar",
            &[Value::Unit, Value::Term(var_tid)]).expect("nonvar");
        assert!(matches!(nv, Value::Bool(false)));
        let g = interp.call("anthill.reflect.KB.ground",
            &[Value::Unit, Value::Term(var_tid)]).expect("ground");
        assert!(matches!(g, Value::Bool(false)));
    }

    #[test]
    fn field_access_extracts_named_arg() {
        let mut interp = load_stdlib_and_source(r#"
namespace test.reflect_field
  sort Point
    entity pt(x: Int64, y: Int64)
  end
end
"#);
        // Build pt(x: 1, y: 2) manually and ask for .x.
        let pt_sym = interp.kb().try_resolve_symbol("test.reflect_field.Point.pt")
            .expect("pt symbol");
        let x_sym = interp.kb_mut().intern("x");
        let y_sym = interp.kb_mut().intern("y");
        let one = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(1)));
        let two = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(2)));
        let pt_tid = interp.kb_mut().alloc(CoreTerm::Fn {
            functor: pt_sym,
            pos_args: Default::default(),
            named_args: vec![(x_sym, one), (y_sym, two)].into(),
        });
        let field_ref = interp.kb_mut().alloc(CoreTerm::Ref(x_sym));
        let result = interp.call("anthill.reflect.field_access",
            &[Value::Term(pt_tid), Value::Term(field_ref)])
            .expect("field_access");
        match result {
            Value::Term(tid) => {
                assert_eq!(interp.kb().get_term(tid), &CoreTerm::Const(Literal::Int(1)));
            }
            other => panic!("expected Value::Term, got {other:?}"),
        }
    }

    #[test]
    fn sort_passthrough_ops_work() {
        let mut interp = load_stdlib_and_source(r#"
namespace test.reflect_sort_pt
  sort Color
    entity red
  end
end
"#);
        let sym = interp.kb().try_resolve_symbol("test.reflect_sort_pt.Color")
            .expect("Color symbol");
        let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(sym));

        let same = interp.call("anthill.reflect.sort_as_term", &[Value::Term(ref_tid)])
            .expect("sort_as_term");
        assert!(matches!(same, Value::Term(t) if t == ref_tid));

        let ok = interp.call("anthill.reflect.can_be_sort", &[Value::Term(ref_tid)])
            .expect("can_be_sort");
        assert!(matches!(ok, Value::Bool(true)));

        // Int64 literal is NOT a sort.
        let lit = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(42)));
        let not_sort = interp.call("anthill.reflect.can_be_sort", &[Value::Term(lit)])
            .expect("can_be_sort (lit)");
        assert!(matches!(not_sort, Value::Bool(false)));

        let as_opt = interp.call("anthill.reflect.term_as_sort", &[Value::Term(lit)])
            .expect("term_as_sort");
        match as_opt {
            Value::Entity { functor, named, .. } => {
                let name = interp.kb().resolve_sym(functor).to_string();
                assert_eq!(name, "none");
                assert!(named.is_empty());
            }
            other => panic!("expected Option entity, got {other:?}"),
        }
    }

    #[test]
    fn reflect_not_on_satisfiable_goal_returns_false() {
        // A ground goal that has a fact → not(goal) should be Bool(false).
        let mut interp = load_stdlib_and_source(r#"
namespace test.not_sat
  sort Color
    entity red
    entity green
  end
  fact Color(entity: red)
end
"#);
        // Build the goal: Color(entity: red).
        let color_sym = interp.kb().try_resolve_symbol("test.not_sat.Color")
            .expect("Color sort symbol");
        let red_sym = interp.kb().try_resolve_symbol("test.not_sat.Color.red")
            .expect("red symbol");
        let entity_field = interp.kb_mut().intern("entity");
        let red_ref = interp.kb_mut().alloc(CoreTerm::Ref(red_sym));
        let goal = interp.kb_mut().alloc(CoreTerm::Fn {
            functor: color_sym,
            pos_args: Default::default(),
            named_args: vec![(entity_field, red_ref)].into(),
        });
        let result = interp.call("anthill.reflect.not", &[Value::Term(goal)])
            .expect("reflect.not");
        assert!(matches!(result, Value::Bool(false)),
            "satisfiable goal → not should be false, got {result:?}");
    }

    #[test]
    fn reflect_not_on_unsatisfiable_goal_returns_true() {
        // A ground goal with no matching fact → not(goal) should be Bool(true).
        let mut interp = load_stdlib_and_source(r#"
namespace test.not_unsat
  sort Color
    entity red
    entity green
  end
  fact Color(entity: red)
end
"#);
        let color_sym = interp.kb().try_resolve_symbol("test.not_unsat.Color")
            .expect("Color sort symbol");
        let green_sym = interp.kb().try_resolve_symbol("test.not_unsat.Color.green")
            .expect("green symbol");
        let entity_field = interp.kb_mut().intern("entity");
        let green_ref = interp.kb_mut().alloc(CoreTerm::Ref(green_sym));
        let goal = interp.kb_mut().alloc(CoreTerm::Fn {
            functor: color_sym,
            pos_args: Default::default(),
            named_args: vec![(entity_field, green_ref)].into(),
        });
        let result = interp.call("anthill.reflect.not", &[Value::Term(goal)])
            .expect("reflect.not");
        assert!(matches!(result, Value::Bool(true)),
            "unsatisfiable goal → not should be true, got {result:?}");
    }

    #[test]
    fn reflect_not_on_ungrounded_goal_flounders() {
        // Free variable in the query → NAF is unsound → error.
        let mut interp = load_stdlib_and_source(r#"
namespace test.not_flounder
  sort Color
    entity red
  end
  fact Color(entity: red)
end
"#);
        let color_sym = interp.kb().try_resolve_symbol("test.not_flounder.Color")
            .expect("Color sort");
        let entity_field = interp.kb_mut().intern("entity");
        let v_sym = interp.kb_mut().intern("v");
        let vid = interp.kb_mut().fresh_var(v_sym);
        let var_term = interp.kb_mut().alloc(CoreTerm::Var(Var::Global(vid)));
        let goal = interp.kb_mut().alloc(CoreTerm::Fn {
            functor: color_sym,
            pos_args: Default::default(),
            named_args: vec![(entity_field, var_term)].into(),
        });
        let result = interp.call("anthill.reflect.not", &[Value::Term(goal)]);
        match result {
            Err(EvalError::Internal(msg)) => {
                assert!(msg.contains("floundering"),
                    "expected floundering message, got: {msg}");
            }
            other => panic!("expected Err(Internal(floundering...)), got {other:?}"),
        }
    }

    #[test]
    fn split_first_yields_solution_values() {
        // Execute a simple pattern query via KB.execute → splitFirst → the
        // first element of the pair is a reflect `Solution` (WI-531):
        // `definite(subst)` here (the query is decidable), carrying the
        // Value::Substitution in its `subst` field — no longer a bare
        // Value::Substitution element (and never the pre-WI-047 Value::Unit).
        let mut interp = load_stdlib_and_source(r#"
namespace test.subst_stream
  sort Color
    entity red
  end
end
"#);
        // Build pattern_query(EntityInfo(name: ?n, fields: ?f)) as a Value.
        let ei_sym = interp.kb().try_resolve_symbol("anthill.reflect.EntityInfo")
            .expect("EntityInfo");
        let pq_sym = interp.kb().try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
            .expect("pattern_query");
        let name_field = interp.kb_mut().intern("name");
        let fields_field = interp.kb_mut().intern("fields");
        let term_field = interp.kb_mut().intern("term");
        let n_sym = interp.kb_mut().intern("n");
        let f_sym = interp.kb_mut().intern("f");
        let vn = interp.kb_mut().fresh_var(n_sym);
        let vf = interp.kb_mut().fresh_var(f_sym);
        let var_n = interp.kb_mut().alloc(CoreTerm::Var(Var::Global(vn)));
        let var_f = interp.kb_mut().alloc(CoreTerm::Var(Var::Global(vf)));
        let inner = Value::Entity {
            functor: ei_sym,
            pos: Vec::new().into(),
            named: vec![(name_field, Value::Term(var_n)), (fields_field, Value::Term(var_f))].into(),
        };
        let query = Value::Entity {
            functor: pq_sym,
            pos: Vec::new().into(),
            named: vec![(term_field, inner)].into(),
        };

        let stream = interp.call("anthill.reflect.KB.execute", &[Value::Unit, query])
            .expect("execute");
        let pumped = interp.call("anthill.prelude.LogicalStream.splitFirst", &[stream])
            .expect("splitFirst");

        // Unwrap Option.some → Pair.pair → fst = the Solution element.
        let fst = match pumped {
            Value::Entity { named: some_named, .. } => {
                let pair = &some_named[0].1;
                match pair {
                    Value::Entity { named: pair_named, .. } => {
                        pair_named.iter().find(|(s, _)|
                            interp.kb().resolve_sym(*s) == "fst"
                        ).map(|(_, v)| v.clone()).expect("fst")
                    }
                    other => panic!("expected pair, got {other:?}"),
                }
            }
            other => panic!("expected Option.some, got {other:?}"),
        };
        // WI-531: the element is a reflect `Solution` (definite | undecided),
        // not a bare Substitution. This fact-pattern query is decidable, so the
        // first answer is `definite(subst)`; assert the Solution shape and that
        // its `subst` field carries the Value::Substitution.
        match fst {
            Value::Entity { functor, named, .. } => {
                let ctor = interp.kb().resolve_sym(functor).to_string();
                assert!(
                    ctor.ends_with("definite") || ctor.ends_with("undecided"),
                    "expected a Solution (definite/undecided), got functor {ctor}",
                );
                let subst = named.iter().find(|(s, _)|
                    interp.kb().resolve_sym(*s) == "subst"
                ).map(|(_, v)| v.clone()).expect("subst field on Solution");
                match subst {
                    Value::Substitution(_) => { /* expected */ }
                    other => panic!("expected Solution.subst = Value::Substitution, got {other:?}"),
                }
            }
            other => panic!("expected a Solution entity, got {other:?}"),
        }
    }

    #[test]
    fn substitution_apply_rewrites_term() {
        use anthill_core::kb::subst::Substitution;
        let mut interp = load_stdlib_and_source(r#"
namespace test.subst_apply
  sort X
    entity x
  end
end
"#);
        // Build subst {?v → Int64(42)}, apply to ?v.
        let v_sym = interp.kb_mut().intern("v");
        let vid = interp.kb_mut().fresh_var(v_sym);
        let var_term = interp.kb_mut().alloc(CoreTerm::Var(Var::Global(vid)));
        let val_term = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(42)));

        let mut s = Substitution::new();
        s.bindings.insert(vid, Value::Term(val_term));
        let s_handle = interp.alloc_subst(s);

        let result = interp.call("anthill.reflect.Substitution.apply",
            &[Value::Substitution(s_handle), Value::Term(var_term), Value::Unit])
            .expect("apply");
        match result {
            Value::Term(tid) => {
                assert_eq!(tid, val_term, "?v → Int64(42) should rewrite the variable");
            }
            other => panic!("expected Value::Term, got {other:?}"),
        }
    }

    #[test]
    fn substitution_bindings_enumerates_pairs() {
        use anthill_core::kb::subst::Substitution;
        let mut interp = load_stdlib_and_source(r#"
namespace test.subst_bindings
  sort X
    entity x
  end
end
"#);
        // Build subst {?v → Int64(42)}, enumerate it.
        let v_sym = interp.kb_mut().intern("v");
        let vid = interp.kb_mut().fresh_var(v_sym);
        let val_term = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(42)));
        let mut s = Substitution::new();
        s.bindings.insert(vid, Value::Term(val_term));
        let s_handle = interp.alloc_subst(s);

        let result = interp.call("anthill.reflect.Substitution.bindings",
            &[Value::Substitution(s_handle)]).expect("bindings");
        // A cons-list with one Pair(fst: <var term>, snd: Int64(42)).
        let head = match result {
            Value::Entity { ref named, .. } => named.iter()
                .find(|(s, _)| interp.kb().resolve_sym(*s) == "head")
                .map(|(_, v)| v.clone())
                .expect("cons.head"),
            other => panic!("expected cons list, got {other:?}"),
        };
        match head {
            Value::Entity { named, .. } => {
                let field = |k: &str| named.iter()
                    .find(|(s, _)| interp.kb().resolve_sym(*s) == k)
                    .map(|(_, v)| v.clone());
                match field("snd").expect("pair.snd") {
                    Value::Term(tid) => assert_eq!(tid, val_term, "snd should be the bound value term"),
                    other => panic!("snd should be Value::Term, got {other:?}"),
                }
                match field("fst").expect("pair.fst") {
                    Value::Term(tid) => assert!(
                        matches!(interp.kb().get_term(tid), CoreTerm::Var(_)),
                        "fst should be a var term carrying the variable's identity"),
                    other => panic!("fst should be Value::Term(Var), got {other:?}"),
                }
            }
            other => panic!("expected Pair entity, got {other:?}"),
        }
    }

    #[test]
    fn subst_compose_chases_bare_value_var() {
        use anthill_core::kb::subst::Substitution;
        let mut interp = load_stdlib_and_source(r#"
namespace test.compose_var
  sort X
    entity x
  end
end
"#);
        // σ1 = {z ↦ Value::Var(w)} (BARE var), σ2 = {w ↦ Int64(7)}. compose must
        // chase z → w → 7, not leave z ↦ w dangling (WI-547).
        let sz = interp.kb_mut().intern("z");
        let vid_z = interp.kb_mut().fresh_var(sz);
        let sw = interp.kb_mut().intern("w");
        let vid_w = interp.kb_mut().fresh_var(sw);
        let seven = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(7)));
        let mut s1 = Substitution::new();
        s1.bindings.insert(vid_z, Value::Var(Var::Global(vid_w)));
        let mut s2 = Substitution::new();
        s2.bindings.insert(vid_w, Value::Term(seven));
        let h1 = interp.alloc_subst(s1);
        let h2 = interp.alloc_subst(s2);

        let composed = interp.call("anthill.reflect.Substitution.compose",
            &[Value::Substitution(h1), Value::Substitution(h2), Value::Unit])
            .expect("compose");
        let handle = match composed {
            Value::Substitution(h) => h,
            other => panic!("expected Value::Substitution, got {other:?}"),
        };
        let arena = interp.subst_arena();
        let z_binding = arena.with_subst(&handle, |s| s.bindings.get(&vid_z).cloned());
        match z_binding.expect("z should be bound") {
            Value::Term(t) => assert!(
                matches!(interp.kb().get_term(t), CoreTerm::Const(Literal::Int(7))),
                "z should chase to Int64(7)"),
            Value::Int(n) => assert_eq!(n, 7, "z should chase to 7"),
            other => panic!("z should chase through w to 7, got {other:?} (bare Var = unfixed bug)"),
        }
    }

    #[test]
    fn subst_arena_reclaims_on_drop() {
        // After running a stream-pumping program, all substitution slots
        // should be reclaimed — no leaks from the per-solution alloc.
        let interp = load_stdlib_and_source(r#"
namespace test.subst_reclaim
  sort Pt
    entity pt
  end
end
"#);
        assert_eq!(interp.subst_arena_live_count(), 0);

        use anthill_core::kb::subst::Substitution;
        let h = interp.alloc_subst(Substitution::new());
        assert_eq!(interp.subst_arena_live_count(), 1);
        drop(h);
        assert_eq!(interp.subst_arena_live_count(), 0);
    }

    #[test]
    fn symbol_ops_qualified_short_lookup_kind() {
        let mut interp = load_stdlib_and_source(r#"
namespace test.reflect_syms
  sort Color
    entity red
  end
end
"#);
        let sym = interp.kb().try_resolve_symbol("test.reflect_syms.Color.red")
            .expect("red symbol");
        let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(sym));

        let qn = interp.call("anthill.reflect.qualified_name", &[Value::Term(ref_tid)])
            .expect("qualified_name");
        assert!(matches!(qn, Value::Str(ref s) if s == "test.reflect_syms.Color.red"));

        let sn = interp.call("anthill.reflect.short_name", &[Value::Term(ref_tid)])
            .expect("short_name");
        assert!(matches!(sn, Value::Str(ref s) if s == "red"));

        let kn = interp.call("anthill.reflect.kind", &[Value::Term(ref_tid)])
            .expect("kind");
        assert!(matches!(kn, Value::Str(ref s) if s == "Entity"));

        let ls = interp.call("anthill.reflect.lookup_symbol",
            &[Value::Str("test.reflect_syms.Color.red".into())])
            .expect("lookup_symbol");
        assert!(matches!(ls, Value::Term(_)));
    }

    #[test]
    fn kb_constructors_lists_sort_entities() {
        let mut interp = load_stdlib_and_source(r#"
namespace test.reflect_ctors
  sort Fruit
    entity apple
    entity banana
    entity cherry
  end
end
"#);
        let result = interp.call("anthill.reflect.KB.constructors",
            &[Value::Unit, Value::Str("Fruit".into())])
            .expect("constructors call");
        let mut names: Vec<String> = Vec::new();
        let mut cur = result;
        loop {
            match cur {
                Value::Entity { functor, named, .. } => {
                    let fname = interp.kb().resolve_sym(functor).to_string();
                    if fname == "nil" { break; }
                    let head = named.iter().find(|(s, _)|
                        interp.kb().resolve_sym(*s) == "head").map(|(_, v)| v.clone());
                    let tail = named.iter().find(|(s, _)|
                        interp.kb().resolve_sym(*s) == "tail").map(|(_, v)| v.clone());
                    if let Some(Value::Str(s)) = head { names.push(s); }
                    cur = tail.expect("cons tail");
                }
                other => panic!("non-entity in list: {other:?}"),
            }
        }
        for expected in ["apple", "banana", "cherry"] {
            assert!(names.iter().any(|n| n == expected),
                "missing '{expected}' in {names:?}");
        }
    }

    /// Walk a value cons/nil list into its element `Value`s (test helper).
    fn list_values(interp: &Interpreter, mut cur: Value) -> Vec<Value> {
        let mut out = Vec::new();
        loop {
            match cur {
                Value::Entity { functor, named, .. } => {
                    let fname = interp.kb().resolve_sym(functor).to_string();
                    if fname.rsplit('.').next() == Some("nil") { break; }
                    let head = named.iter().find(|(s, _)|
                        interp.kb().resolve_sym(*s) == "head").map(|(_, v)| v.clone());
                    let tail = named.iter().find(|(s, _)|
                        interp.kb().resolve_sym(*s) == "tail").map(|(_, v)| v.clone());
                    match (head, tail) {
                        (Some(h), Some(t)) => { out.push(h); cur = t; }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        out
    }

    /// A named field of a `Value::Entity` by short name (test helper).
    fn entity_field(interp: &Interpreter, e: &Value, key: &str) -> Option<Value> {
        match e {
            Value::Entity { named, .. } => named.iter()
                .find(|(s, _)| interp.kb().resolve_sym(*s) == key)
                .map(|(_, v)| v.clone()),
            _ => None,
        }
    }

    #[test]
    fn kb_operations_surfaces_requires_ensures_and_meta() {
        // WI-548: the interpreter realization of `KB.operations` must match the
        // host bridge (WI-545) — an op's `requires`/`ensures` contract clauses and
        // `meta` term are surfaced in the OperationInfo value, not dropped.
        // `ensures` carries only user clauses (no synthetic EffectsRuntime), so an
        // empty `ensures` would be an unambiguous regression; `requires` also
        // carries the loader's `EffectsRuntime[Effects=E]` clause (WI-320).
        let mut interp = load_stdlib_and_source(r#"
namespace test.wi548_op_contract
  import anthill.prelude.Int64

  sort Tank
    entity tank(fuel: Int64)
    entity Full(t: Tank)
    operation fill(t: Tank) -> Tank requires Full(t) ensures Full(t)
      meta [Refuel, Profile: "cpp20-stl"]
  end
end
"#);
        let result = interp.call("anthill.reflect.KB.operations",
            &[Value::Unit, Value::Str("Tank".into())])
            .expect("operations call");

        // The op's `name` field is `Value::Term(Ref(sym))`; match by short name.
        let op_short = |interp: &Interpreter, op: &Value| -> Option<String> {
            match entity_field(interp, op, "name")? {
                Value::Term(tid) => match interp.kb().get_term(tid) {
                    CoreTerm::Ref(s) => {
                        let n = interp.kb().resolve_sym(*s).to_string();
                        Some(n.rsplit('.').next().unwrap_or(&n).to_string())
                    }
                    _ => None,
                },
                _ => None,
            }
        };

        let ops = list_values(&interp, result);
        let fill = ops.iter().find(|op| op_short(&interp, op).as_deref() == Some("fill"))
            .expect("fill OperationInfo entity");

        let requires = list_values(&interp,
            entity_field(&interp, fill, "requires").expect("requires field present"));
        let ensures = list_values(&interp,
            entity_field(&interp, fill, "ensures").expect("ensures field present"));
        assert!(!ensures.is_empty(), "fill should surface its user `ensures` clause");
        assert!(!requires.is_empty(),
            "fill should surface `requires` (incl. synthetic EffectsRuntime)");
        // Each ground contract clause rides as a goal-term Value (matching bridge).
        match &ensures[0] {
            Value::Term(_) => {}
            other => panic!("ensures clause should be a Value::Term goal, got {other:?}"),
        }

        // `meta` is surfaced (not omitted) — a non-empty `meta(...)` term here.
        let meta = entity_field(&interp, fill, "meta").expect("meta field present");
        match meta {
            Value::Term(tid) => assert!(
                matches!(interp.kb().get_term(tid),
                    CoreTerm::Fn { named_args, .. } if !named_args.is_empty()),
                "meta should be a non-empty meta(...) term",
            ),
            other => panic!("meta field should be a Value::Term, got {other:?}"),
        }
    }
}
