//! Eval-time builtins for `anthill.reflect.KB.*` introspection operations.
//!
//! Scripts call `KB.sort_template`, `KB.sorts`, `KB.operations`, … and get
//! `Value`-typed results whose shapes match the sort declarations in
//! `stdlib/anthill/reflect/reflect.anthill`. The heavy lifting — walking KB
//! facts, extracting named args, collecting cons-lists — is inline here over
//! `&mut KnowledgeBase`. The sibling `bridge.rs` does the same for host-Rust
//! callers; consolidating the two paths is tracked separately.
//!
//! A HANDFUL ARE NOT `KB` MEMBERS, and the difference is not cosmetic: an
//! operation whose question is about a KB (`sorts`, `rules`, `facts_of`) takes
//! it as a receiver, while one whose question is about a VALUE — `nonvar`,
//! `ground`, `qualified_name`, `kind` — is namespace-level, because a receiver
//! it never reads is dispatch ceremony that also captures the free name
//! (WI-982; proposal 059 R4). Where the resolver answers the same question as a
//! goal, this module must not re-derive it: it calls the resolver's own
//! predicate, so the two phases cannot drift.

use std::rc::Rc;

use anthill_core::eval::builtins::{
    expect_args, register_if_present, require_symbol, resolve_host_name,
};
use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term as CoreTerm, TermId, Var};
use anthill_core::kb::KnowledgeBase;

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
    f_sort: Symbol,
    f_fst: Symbol,
    f_snd: Symbol,
}

impl ReflectSyms {
    /// Resolve every reflect symbol. Fails if the stdlib isn't loaded —
    /// surfacing as `EvalError::Internal` so the caller at `register_reflect_builtins`
    /// sees a clear single-point error rather than deferred per-builtin failures.
    fn resolve(kb: &mut KnowledgeBase) -> Result<Self, EvalError> {
        fn req(kb: &KnowledgeBase, qname: &'static str) -> Result<Symbol, EvalError> {
            kb.try_resolve_symbol(qname).ok_or_else(|| {
                EvalError::Internal(format!("{qname} not in scope — stdlib not loaded"))
            })
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
            f_sort: kb.intern("sort"),
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
    if interp
        .kb()
        .try_resolve_symbol("anthill.reflect.SortInfo")
        .is_none()
    {
        return Ok(());
    }
    let syms = Rc::new(ReflectSyms::resolve(interp.kb_mut())?);

    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.sort_template", move |i, a| {
        kb_sort_template(i, a, &s)
    })?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.sorts", move |i, a| {
        kb_sorts(i, a, &s)
    })?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.operations", move |i, a| {
        kb_operations(i, a, &s)
    })?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.constructors", move |i, a| {
        kb_constructors(i, a, &s)
    })?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.fields", move |i, a| {
        kb_fields(i, a, &s)
    })?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.rules", move |i, a| {
        kb_rules(i, a, &s)
    })?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.descriptions", move |i, a| {
        kb_descriptions(i, a, &s)
    })?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.reify", move |i, a| {
        kb_reify(i, a, &s)
    })?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.KB.reflect", move |i, a| {
        kb_reflect(i, a, &s)
    })?;

    // Namespace-level symbol ops (no cached syms needed beyond `_kb` sentinel).
    register_if_present(interp, "anthill.reflect.qualified_name", qualified_name)?;
    register_if_present(interp, "anthill.reflect.short_name", short_name_op)?;
    register_if_present(interp, "anthill.reflect.lookup_symbol", lookup_symbol_op)?;
    register_if_present(interp, "anthill.reflect.scope", scope_op)?;
    register_if_present(interp, "anthill.reflect.kind", kind_op)?;

    // WI-982 — namespace-level and 1-ary, the SAME name and arity the resolver
    // dispatches as a goal. The `KB.nonvar(kb, x)` / `KB.ground(kb, x)` members
    // these replace took a receiver the implementation discarded.
    register_if_present(interp, "anthill.reflect.nonvar", nonvar_op)?;
    register_if_present(interp, "anthill.reflect.ground", ground_op)?;

    register_if_present(interp, "anthill.reflect.sort_as_term", sort_as_term)?;
    register_if_present(interp, "anthill.reflect.can_be_sort", can_be_sort)?;
    let s = syms.clone();
    register_if_present(interp, "anthill.reflect.term_as_sort", move |i, a| {
        term_as_sort(i, a, &s)
    })?;

    // NO `anthill.reflect.field_access` here — deliberately (WI-759). `anthill-core`'s
    // `register_standard_builtins` already binds that QN to the production implementation
    // (`eval::builtins::reflect_field_access`), the one every desugared `x.f` runs through.
    // This module used to bind it too, to the DECLARED-but-never-live shape
    // (`expect_term` + `expect_symbol`), which would reject every projection the typer
    // synthesizes — a `Value::Entity` / `Value::Tuple` receiver and a `String` selector.
    // `register_builtin` is a plain map insert, LAST WINS, and this module registers after
    // the standard set, so wiring these reflect builtins into any real driver would have
    // silently shadowed the working implementation with a broken one. It was harmless only
    // because nothing but this file's own tests ever called `register_reflect_builtins`.
    register_if_present(
        interp,
        "anthill.reflect.resolve_sort_instantiation_param",
        resolve_sort_instantiation_param,
    )?;

    register_if_present(interp, "anthill.reflect.Substitution.apply", subst_apply)?;
    register_if_present(
        interp,
        "anthill.reflect.Substitution.compose",
        subst_compose,
    )?;
    let s = syms.clone();
    register_if_present(
        interp,
        "anthill.reflect.Substitution.bindings",
        move |i, a| subst_bindings(i, a, &s),
    )?;

    register_if_present(interp, "anthill.kernel.not", kernel_not)?;

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
        other => Err(EvalError::TypeMismatch {
            expected: "String",
            got: other.type_name().to_string(),
        }),
    }
}

/// The already-resolved functor symbol of a by-reference sort/entity argument
/// (WI-632). A `sort`/`entity` reflect op takes the sort BY REFERENCE — a
/// `Value::Term(Ref)` / `Value::Entity` resolved to its qualified functor at the
/// caller's write site — so extraction is a pure `value_functor` read (the
/// `facts_of` precedent), loud on a non-reference. The interpreter twin of the
/// bridge's `value_functor(&kb, type.value())`.
fn sort_ref_functor(interp: &Interpreter, sort: &Value) -> Result<Symbol, EvalError> {
    anthill_core::eval::value_functor(interp.kb(), sort).ok_or_else(|| EvalError::TypeMismatch {
        expected: "Type (entity/sort reference)",
        got: sort.type_name().to_string(),
    })
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
        other => Err(EvalError::TypeMismatch {
            expected: "Option[String]",
            got: other.type_name().to_string(),
        }),
    }
}

/// Build a `cons(head:_, tail:_)` chain terminated by `nil()` as a `Value`.
fn build_list_value(syms: &ReflectSyms, elements: Vec<Value>) -> Value {
    let mut acc = Value::Entity {
        functor: syms.nil,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
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
            Some(order) => {
                named.sort_by_key(|(s, _)| order.iter().position(|f| f == s).unwrap_or(usize::MAX))
            }
            None => named.sort_by_key(|(s, _)| s.index()),
        }
    }
    Value::Entity {
        functor,
        pos: Vec::new().into(),
        named: named.into(),
    }
}

// ── Builtin handlers ───────────────────────────────────────────

fn kb_sort_template(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, sort] = expect_args::<2>("KB.sort_template", args)?;
    // WI-632: the sort is passed BY REFERENCE (e.g. `sort_template(kb(),
    // WorkItem)`) — a `Value::Term(Ref)` / `Value::Entity` already resolved to
    // its qualified functor at the caller's write site. Validate it names a
    // functor (loud on a non-reference, mirroring `kb_facts_of`), then store
    // the reference verbatim as the `sort_query.sort` payload.
    sort_ref_functor(interp, &sort)?;
    Ok(Value::Entity {
        functor: syms.sort_query,
        pos: Vec::new().into(),
        named: vec![(syms.f_sort, sort)].into(),
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
        let list =
            |ts: Vec<TermId>| build_list_value(syms, ts.into_iter().map(Value::term).collect());
        let mut fields = vec![
            (syms.f_name, Value::term(rec.name)),
            (syms.f_definition, Value::term(rec.definition)),
            (syms.f_constructors, list(rec.constructors)),
            (syms.f_operations, list(rec.operations)),
            (syms.f_parameters, list(rec.parameters)),
            (syms.f_requires, list(rec.requires)),
        ];
        if let Some(k) = rec.kind {
            fields.push((syms.f_kind, Value::term(k)));
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
    let [_kb, sort] = expect_args::<2>("KB.operations", args)?;
    let sort_sym = sort_ref_functor(interp, &sort)?;
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
    for rec in reader::read_operations(kb, sort_sym) {
        let params_v = build_list_value(syms, rec.params.into_iter().map(Value::term).collect());
        let effects_v = build_list_value(syms, rec.effects);
        let requires_v = build_list_value(syms, rec.requires);
        let ensures_v = build_list_value(syms, rec.ensures);
        let fields = vec![
            (syms.f_name, Value::term(rec.name)),
            (syms.f_params, params_v),
            (syms.f_return_type, Value::term(rec.return_type)),
            (syms.f_effects, effects_v),
            (syms.f_requires, requires_v),
            (syms.f_ensures, ensures_v),
            (syms.f_meta, Value::term(rec.meta)),
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
    let [_kb, sort] = expect_args::<2>("KB.constructors", args)?;
    let sort_sym = sort_ref_functor(interp, &sort)?;
    let kb = interp.kb_mut();
    let items: Vec<Value> = reader::members_of_kind(kb, sort_sym, "Constructor")
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
    let [_kb, entity] = expect_args::<2>("KB.fields", args)?;
    // WI-632: the entity is passed BY REFERENCE (e.g. `fields(kb(), WorkItem)`) —
    // a `Value::Term(Ref)` / `Value::Entity` already resolved to its qualified
    // functor at the caller's write site. Extract that functor via the shared
    // `value_functor` (the `facts_of` precedent); a non-reference is a caller
    // type error, surfaced loudly. No name-string resolution, so the WI-631
    // short-name ambiguity cannot arise here.
    let functor = sort_ref_functor(interp, &entity)?;
    let kb = interp.kb_mut();

    // The entity's declared `(field_name, field_type)` pairs, read
    // carrier-agnostically (WI-342): a value-in-type field (`Vector[Int64, 3]`)
    // rides as its own `Value::Node` into the FieldInfo, surfaced verbatim.
    // Cloned to release the registry borrow before building the entities.
    let declared: Option<Vec<(Symbol, Value)>> = kb.entity_field_types(functor).map(|f| f.to_vec());
    let mut items: Vec<Value> = Vec::new();
    if let Some(fields) = declared {
        for (field_sym, field_type) in fields {
            let name_val = Value::Str(kb.local_name_of(field_sym).to_string());
            let entry = vec![(syms.f_name, name_val), (syms.f_type_name, field_type)];
            items.push(make_entity(kb, syms.field_info, entry));
        }
    }
    Ok(build_list_value(syms, items))
}

fn kb_rules(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [_kb, sort] = expect_args::<2>("KB.rules", args)?;
    let sort_sym = sort_ref_functor(interp, &sort)?;
    let kb = interp.kb_mut();

    let mut items: Vec<Value> = Vec::new();
    for head in reader::rule_heads_for_sort(kb, sort_sym) {
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

    // The reader yields `DescriptionInfo(target, content, index)` records; the index
    // is the STORED 0-based per-target index (WI-438), not a global enumeration.
    let mut items: Vec<Value> = Vec::new();
    for rec in reader::read_descriptions(kb, target.as_deref()) {
        let fields = vec![
            (syms.f_target, Value::term(rec.target)),
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
        Value::Term { id: tid, .. } => tid,
        other => {
            return Err(EvalError::TypeMismatch {
                expected: "Term",
                got: other.type_name().to_string(),
            })
        }
    };
    Ok(reify_term_to_value(interp.kb_mut(), syms, tid))
}

/// Build a `TermRepr` `Value` from a hash-consed `TermId` — the interpreter
/// realization of the shared [`reader::reify_walk`], via [`ValueReprBuilder`].
/// Parity with `bridge.rs`'s generated-`TermRepr` reifier is now structural:
/// both drive the one `reader::reify_walk`.
fn reify_term_to_value(kb: &mut KnowledgeBase, syms: &ReflectSyms, id: TermId) -> Value {
    reader::reify_walk(kb, &id, &mut ValueReprBuilder { syms })
}

/// Interpreter realization of [`reader::ReifyBuilder`]: emits a `TermRepr`
/// `Value::Entity` tree. A `Ref`/`Fn` name rides as a `Ref` TERM (`Value::term`),
/// which [`ValueRepr`]'s inverse reads back.
struct ValueReprBuilder<'s> {
    syms: &'s ReflectSyms,
}

impl reader::ReifyBuilder for ValueReprBuilder<'_> {
    type Repr = Value;

    fn on_literal(&mut self, _kb: &mut KnowledgeBase, lit: Literal) -> Value {
        let syms = self.syms;
        // A `LiteralRepr` rides inside the `ConstRepr`'s `value` field.
        let (ctor, inner) = match lit {
            Literal::Int(n) => (syms.int_lit, Value::Int(n)),
            Literal::BigInt(n) => (syms.bigint_lit, Value::BigInt(n)),
            Literal::Float(f) => (syms.float_lit, Value::Float(f.into_inner())),
            Literal::String(s) => (syms.str_lit, Value::Str(s)),
            Literal::Bool(b) => (syms.bool_lit, Value::Bool(b)),
        };
        Value::Entity {
            functor: syms.const_repr,
            pos: Vec::new().into(),
            named: vec![(
                syms.f_value,
                Value::Entity {
                    functor: ctor,
                    pos: Vec::new().into(),
                    named: vec![(syms.f_value, inner)].into(),
                },
            )]
            .into(),
        }
    }

    fn on_var(&mut self, _kb: &mut KnowledgeBase, name: String) -> Value {
        Value::Entity {
            functor: self.syms.var_repr,
            pos: Vec::new().into(),
            named: vec![(self.syms.f_name, Value::Str(name))].into(),
        }
    }

    fn on_ref(&mut self, kb: &mut KnowledgeBase, name: Symbol) -> Value {
        let name_term = kb.alloc(CoreTerm::Ref(name));
        Value::Entity {
            functor: self.syms.ref_repr,
            pos: Vec::new().into(),
            named: vec![(self.syms.f_name, Value::term(name_term))].into(),
        }
    }

    fn on_fn(&mut self, kb: &mut KnowledgeBase, functor: Symbol, args: Vec<Value>) -> Value {
        let name_term = kb.alloc(CoreTerm::Ref(functor));
        let args_list = build_list_value(self.syms, args);
        Value::Entity {
            functor: self.syms.fn_repr,
            pos: Vec::new().into(),
            named: vec![
                (self.syms.f_name, Value::term(name_term)),
                (self.syms.f_args, args_list),
            ]
            .into(),
        }
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
    let tid = reader::reflect_walk(interp.kb_mut(), ValueRepr { value: repr, syms })?;
    Ok(Value::term(tid))
}

/// Interpreter realization of [`reader::ReflectReader`]: decodes a `TermRepr`
/// `Value::Entity` tree. A `Ref`/`Fn` name is read back off its in-band `Ref`
/// TERM carrier — the inverse of [`ValueReprBuilder`].
struct ValueRepr<'s> {
    value: Value,
    syms: &'s ReflectSyms,
}

impl reader::ReflectReader for ValueRepr<'_> {
    type Error = EvalError;

    fn classify(self, kb: &KnowledgeBase) -> Result<reader::ReflectShape<Self>, EvalError> {
        let syms = self.syms;
        let (functor, named) = match self.value {
            Value::Entity { functor, named, .. } => (functor, named),
            other => {
                return Err(EvalError::TypeMismatch {
                    expected: "TermRepr",
                    got: other.type_name().to_string(),
                })
            }
        };
        let lookup = |key: Symbol| -> Option<Value> {
            named
                .iter()
                .find(|(s, _)| *s == key)
                .map(|(_, v)| v.clone())
        };

        if functor == syms.const_repr {
            let inner = lookup(syms.f_value)
                .ok_or_else(|| EvalError::Internal("ConstRepr: missing `value`".into()))?;
            Ok(reader::ReflectShape::Const(decode_literal_repr(
                kb, syms, inner,
            )?))
        } else if functor == syms.var_repr {
            let name = lookup(syms.f_name)
                .ok_or_else(|| EvalError::Internal("VarRepr: missing `name`".into()))?;
            Ok(reader::ReflectShape::Var(str_arg(name)?))
        } else if functor == syms.ref_repr {
            let name = lookup(syms.f_name)
                .ok_or_else(|| EvalError::Internal("RefRepr: missing `name`".into()))?;
            Ok(reader::ReflectShape::Ref(ref_repr_symbol(kb, name)?))
        } else if functor == syms.fn_repr {
            let name = lookup(syms.f_name)
                .ok_or_else(|| EvalError::Internal("FnRepr: missing `name`".into()))?;
            let functor_sym = ref_repr_symbol(kb, name)?;
            let args_list = lookup(syms.f_args)
                .ok_or_else(|| EvalError::Internal("FnRepr: missing `args`".into()))?;
            let children = collect_repr_list(kb, syms, args_list)?
                .into_iter()
                .map(|v| ValueRepr { value: v, syms })
                .collect();
            Ok(reader::ReflectShape::Fn(functor_sym, children))
        } else {
            Err(EvalError::Internal(format!(
                "unknown TermRepr ctor: {}",
                kb.local_name_of(functor)
            )))
        }
    }
}

/// Decode a `LiteralRepr` `Value::Entity` (the inner of a `ConstRepr`) to a core
/// `Literal`. `BigIntLiteral` is its own first-class case (WI-543); `IntLiteral`
/// stays `Int64`-only.
fn decode_literal_repr(
    kb: &KnowledgeBase,
    syms: &ReflectSyms,
    inner: Value,
) -> Result<Literal, EvalError> {
    let (lit_ctor, lit_val) = match inner {
        Value::Entity { functor, named, .. } => {
            let v = named
                .iter()
                .find(|(s, _)| *s == syms.f_value)
                .map(|(_, v)| v.clone())
                .ok_or_else(|| EvalError::Internal("LiteralRepr: missing `value`".into()))?;
            (functor, v)
        }
        other => {
            return Err(EvalError::TypeMismatch {
                expected: "LiteralRepr",
                got: other.type_name().to_string(),
            })
        }
    };
    if lit_ctor == syms.int_lit {
        match lit_val {
            Value::Int(n) => Ok(Literal::Int(n)),
            other => Err(EvalError::TypeMismatch {
                expected: "Int64",
                got: other.type_name().to_string(),
            }),
        }
    } else if lit_ctor == syms.bigint_lit {
        match lit_val {
            Value::BigInt(n) => Ok(Literal::BigInt(n)),
            Value::Int(n) => Ok(Literal::BigInt(n.into())),
            other => Err(EvalError::TypeMismatch {
                expected: "BigInt",
                got: other.type_name().to_string(),
            }),
        }
    } else if lit_ctor == syms.float_lit {
        match lit_val {
            Value::Float(f) => Ok(Literal::Float(f.into())),
            other => Err(EvalError::TypeMismatch {
                expected: "Float",
                got: other.type_name().to_string(),
            }),
        }
    } else if lit_ctor == syms.str_lit {
        match lit_val {
            Value::Str(s) => Ok(Literal::String(s)),
            other => Err(EvalError::TypeMismatch {
                expected: "String",
                got: other.type_name().to_string(),
            }),
        }
    } else if lit_ctor == syms.bool_lit {
        match lit_val {
            Value::Bool(b) => Ok(Literal::Bool(b)),
            other => Err(EvalError::TypeMismatch {
                expected: "Bool",
                got: other.type_name().to_string(),
            }),
        }
    } else {
        Err(EvalError::Internal(format!(
            "unknown LiteralRepr ctor: {}",
            kb.local_name_of(lit_ctor)
        )))
    }
}

/// Read a `Ref`/`Fn` name off a `TermRepr`'s `name` field — the inverse of how
/// [`ValueReprBuilder`] emits one.
///
/// BY CONTENT, through the same [`expect_symbol`], because the field is DECLARED
/// `Symbol` (`entity RefRepr(name: Symbol)` / `FnRepr(name: Symbol, …)` in
/// `stdlib/anthill/reflect/reflect.anthill`), not "whatever `ValueReprBuilder`
/// happened to put there". Reading it as `Value::Term { id } → Term::Ref | Ident`
/// only worked because producer and consumer are both in this module and both
/// chose the interned carrier; a program writing `RefRepr(name: Dictionary.impl(d))`
/// supplies a perfectly well-typed `Symbol` that the old match rejected — and
/// after WI-1016 that op mints `Value::SymbolRef`, so the rejection became live.
fn ref_repr_symbol(kb: &KnowledgeBase, name: Value) -> Result<Symbol, EvalError> {
    expect_symbol(kb, name, "TermRepr name")
}

/// Collect the head `Value`s of a `FnRepr.args` prelude cons-list (a `List` of
/// `TermRepr`); each head is decoded lazily by [`reader::reflect_walk`]'s
/// recursion over the returned [`ValueRepr`]s.
fn collect_repr_list(
    kb: &KnowledgeBase,
    syms: &ReflectSyms,
    args_list: Value,
) -> Result<Vec<Value>, EvalError> {
    let mut out = Vec::new();
    let mut cur = args_list;
    loop {
        match cur {
            Value::Entity {
                functor: f, named, ..
            } => {
                if f == syms.nil {
                    break;
                }
                if f != syms.cons {
                    return Err(EvalError::Internal(format!(
                        "FnRepr.args: expected cons-list, got {}",
                        kb.local_name_of(f)
                    )));
                }
                let head = named
                    .iter()
                    .find(|(s, _)| *s == syms.head)
                    .map(|(_, v)| v.clone())
                    .ok_or_else(|| EvalError::Internal("cons: missing head".into()))?;
                let tail = named
                    .iter()
                    .find(|(s, _)| *s == syms.tail)
                    .map(|(_, v)| v.clone())
                    .ok_or_else(|| EvalError::Internal("cons: missing tail".into()))?;
                out.push(head);
                cur = tail;
            }
            other => {
                return Err(EvalError::TypeMismatch {
                    expected: "cons-list",
                    got: other.type_name().to_string(),
                })
            }
        }
    }
    Ok(out)
}

// ── Symbol ops (namespace-level) ─────────────────────────────────

/// The symbol a reflect `Symbol` argument names — read by CONTENT, through the
/// resolver's own [`KnowledgeBase::value_symbol`], NOT by carrier.
///
/// THE EVAL TWIN OF `builtin_qualified_name` / `builtin_short_name`, and that is
/// why it may not have its own match. Every op below (`qualified_name`,
/// `short_name`, `scope`, `kind`, `resolve_sort_instantiation_param`) has an SLD
/// twin that WI-1015 moved onto `value_symbol`; this reader stayed a hand-written
/// `Value::Term { id } → Term::Ref | Ident`, which is a by-CARRIER answer to a
/// by-CONTENT question. With `symbol_value` minting `Value::SymbolRef` (WI-1016)
/// that gap is observable: `qualified_name(Dictionary.impl(d))` would be a type
/// error at the eval entry and answer a string through the goal entry — ONE
/// operation, two answers, decided by which phase asked.
///
/// The widening is the same one the SLD twins took: `value_symbol` also answers
/// on a `Value::Node` ref occurrence and on a non-canonicalized nullary
/// constructor `Fn{c,[],[]}` (`resolve_qualified_name_term` mints those).
fn expect_symbol(kb: &KnowledgeBase, v: Value, _op: &'static str) -> Result<Symbol, EvalError> {
    kb.value_symbol(&v).ok_or_else(|| EvalError::TypeMismatch {
        expected: "Symbol",
        got: v.type_name().to_string(),
    })
}

fn qualified_name(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("qualified_name", args)?;
    let sym = expect_symbol(interp.kb(), s, "qualified_name")?;
    Ok(Value::Str(interp.kb().qualified_name_of(sym).to_string()))
}

fn short_name_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("short_name", args)?;
    let sym = expect_symbol(interp.kb(), s, "short_name")?;
    Ok(Value::Str(interp.kb().local_name_of(sym).to_string()))
}

/// WI-913 — the MESSAGE was the true half and the CODE was not: this said "'{name}'
/// not in scope" while `try_resolve_symbol` consulted no scope at all, so a bare
/// `cons` — a name the implicit tier answers — was reported as out of scope by a
/// lookup that had never looked. It now reads the shared host-name ladder
/// (`resolve_host_name` → `KnowledgeBase::resolve_name_in_global`, WI-908), which is
/// also what the SLD-side backing of this SAME declared operation
/// (`KnowledgeBase::builtin_lookup_symbol`) reads — one operation, one question, the
/// WI-984 rule.
fn lookup_symbol_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [name] = expect_args::<1>("lookup_symbol", args)?;
    let name_str = str_arg(name)?;
    let sym = resolve_host_name(interp, "lookup_symbol", &name_str)?;
    Ok(Value::term(interp.kb_mut().alloc(CoreTerm::Ref(sym))))
}

fn scope_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("scope", args)?;
    let sym = expect_symbol(interp.kb(), s, "scope")?;
    // WI-984 — THE DECLARED CONTRACT, which this did not implement: `reflect.anthill`
    // says "Symbol → enclosing scope symbol (None for top-level)". It used to call
    // `KnowledgeBase::scope_of`, a scan for a SIBLING sort/namespace/operation
    // sharing the symbol's scope — a different question with different answers.
    // MEASURED on `sort Tank { entity Full(litres: Int64); operation fill(…) }`:
    // this op answered `none` for `Tank.Full.litres`, `Tank.fill` and `Tank`, and
    // `Tank.fill` (a sibling operation!) for `Tank.Full`, while the SLD builtin
    // backing the SAME QN answered `Full`, `Tank`, `wi984s` and `Tank`. One
    // operation, two backings, no shared answer. Now both read the declaring scope.
    //
    // The global scope IS the top level, so it is the `None` the declaration promises —
    // the same rule `resolve::builtin_scope` applies.
    let global = interp.kb_mut().global_scope();
    let scope_sym = interp
        .kb()
        .declaring_scope_symbol(sym)
        .filter(|&owner| owner != global.owner());
    // Lookup Option.some / Option.none every call — not hot path; keeping
    // these out of ReflectSyms because this op is reachable even with a
    // stripped reflect stdlib (it's a namespace-level op, not a KB method).
    let some_sym = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Option.some")
        .ok_or_else(|| EvalError::Internal("anthill.prelude.Option.some not in scope".into()))?;
    let none_sym = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Option.none")
        .ok_or_else(|| EvalError::Internal("anthill.prelude.Option.none not in scope".into()))?;
    let value_field = interp.kb_mut().intern("value");
    Ok(match scope_sym {
        Some(sym) => {
            let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(sym));
            Value::Entity {
                functor: some_sym,
                pos: Vec::new().into(),
                named: vec![(value_field, Value::term(ref_tid))].into(),
            }
        }
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
        },
    })
}

fn kind_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use anthill_core::intern::SymbolKind;
    let [s] = expect_args::<1>("kind", args)?;
    let sym = expect_symbol(interp.kb(), s, "kind")?;
    // WI-898: the kind→string table lives on `SymbolKind` itself, shared with the
    // resolver's `kind` builtin, so the two cannot answer differently.
    let kind_str = interp
        .kb()
        .kind_of(sym)
        .map_or("Unresolved", SymbolKind::reflect_name);
    Ok(Value::Str(kind_str.into()))
}

// ── Term-shape predicates (eval-side, no DELAY) ─────────────────

fn expect_term(v: Value, op: &'static str) -> Result<TermId, EvalError> {
    match v {
        Value::Term { id: tid, .. } => Ok(tid),
        other => Err(EvalError::TypeMismatch {
            expected: "Term",
            got: format!("{} for {op}", other.type_name()),
        }),
    }
}

/// `nonvar(x: Term) -> Bool` — the EVAL-time reading of the resolver's
/// `nonvar(?x)` builtin, answered by the same predicate
/// ([`KnowledgeBase::value_is_unbound_var`]) rather than re-derived. WI-982.
///
/// TWO-VALUED BECAUSE IT SEES EVERY CARRIER, not because it cannot see one.
/// That distinction is the whole point: this used to be
/// `!matches!(get_term(tid), Var(_))` behind an `expect_term` that hard-rejected
/// every carrier but `Value::Term`, so it answered by CARRIER — a `Value::Node`
/// var occurrence (what WI-722 macro expansion binds a param to) was a
/// `TypeMismatch` here and a variable to the resolver. The delay the resolver
/// adds is a RESOLUTION concern — a goal can be re-asked once something binds it
/// — and there is nothing to re-ask at eval time, so `Bool` is the whole answer.
fn nonvar_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [x] = expect_args::<1>("nonvar", args)?;
    Ok(Value::Bool(!interp.kb().value_is_unbound_var(&x)))
}

/// `ground(x: Term) -> Bool` — the eval-time reading of the resolver's
/// `ground(?x)` builtin, answered by [`KnowledgeBase::value_is_ground_no_subst`].
/// See [`nonvar_op`] for why it is two-valued and what the TermId-only
/// derivation it replaces got wrong.
fn ground_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [x] = expect_args::<1>("ground", args)?;
    Ok(Value::Bool(interp.kb().value_is_ground_no_subst(&x)))
}

// ── Sort ↔ Term (identity passthroughs — Types ARE Terms) ────────

/// `sort_as_term(s: Type) -> Term` — Type and Term are both `TermId` in the
/// kernel (see memory `project_sort_data_distinction` / architecture note).
/// The operation exists for documentation and API symmetry.
fn sort_as_term(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("sort_as_term", args)?;
    // Accept any Value::Term — the user wrote it in a sort/type position.
    match s {
        Value::Term { .. } => Ok(s),
        other => Err(EvalError::TypeMismatch {
            expected: "Type (Term handle)",
            got: other.type_name().to_string(),
        }),
    }
}

/// `can_be_sort(t: Term) -> Bool` — every well-formed `Term` can stand in
/// type position (sorts are terms). Literals and `Bottom` are rejected.
fn can_be_sort(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [t] = expect_args::<1>("can_be_sort", args)?;
    let tid = expect_term(t, "can_be_sort")?;
    let ok = !matches!(
        interp.kb().get_term(tid),
        CoreTerm::Const(_) | CoreTerm::Bottom
    );
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
    let ok = !matches!(
        interp.kb().get_term(tid),
        CoreTerm::Const(_) | CoreTerm::Bottom
    );
    let some_sym = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Option.some")
        .ok_or_else(|| EvalError::Internal("Option.some not in scope".into()))?;
    let none_sym = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Option.none")
        .ok_or_else(|| EvalError::Internal("Option.none not in scope".into()))?;
    if ok {
        Ok(Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(syms.f_value, Value::term(tid))].into(),
        })
    } else {
        Ok(Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
        })
    }
}

// ── Field access / sort instantiation ────────────────────────────

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
        CoreTerm::Fn { named_args, .. } => named_args
            .iter()
            .find(|(s, _)| *s == param_sym)
            .map(|(_, tid)| Value::term(*tid))
            .ok_or_else(|| {
                EvalError::Internal(format!(
                    "resolve_sort_instantiation_param: '{}' not bound",
                    kb.local_name_of(param_sym)
                ))
            }),
        _ => Err(EvalError::TypeMismatch {
            expected: "SortView Term",
            got: "other Term".into(),
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
        other => {
            return Err(EvalError::TypeMismatch {
                expected: "Substitution",
                got: other.type_name().to_string(),
            })
        }
    };
    let tid = expect_term(t, "Substitution.apply")?;
    // The arena is on `interp.substs`; the KB on `interp.kb`. These are
    // independent fields, so we can hold a shared borrow on the arena
    // (via the cloned Rc) while mutably borrowing the KB.
    let arena = interp.subst_arena();
    let kb = interp.kb_mut();
    let applied = arena.with_subst(&handle, |s| kb.apply_subst(tid, s));
    Ok(Value::term(applied))
}

/// `Substitution.compose(s1: Substitution, s2: Substitution, kb: KB) -> Substitution`.
/// Produces a new substitution: s2 applied to every Term-valued binding of
/// s1, extended by s2's bindings where the variable doesn't already appear
/// in s1. Borrows both substitutions through the arena — no full clones.
fn subst_compose(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s1, s2, _kb] = expect_args::<3>("Substitution.compose", args)?;
    let h1 = match s1 {
        Value::Substitution(h) => h,
        other => {
            return Err(EvalError::TypeMismatch {
                expected: "Substitution",
                got: other.type_name().to_string(),
            })
        }
    };
    let h2 = match s2 {
        Value::Substitution(h) => h,
        other => {
            return Err(EvalError::TypeMismatch {
                expected: "Substitution",
                got: other.type_name().to_string(),
            })
        }
    };

    let arena = interp.subst_arena();
    let kb = interp.kb_mut();
    let composed = arena.with_subst(&h1, |s1| {
        arena.with_subst(&h2, |s2| {
            let mut result = anthill_core::kb::subst::Substitution::new();
            // (WI-569: `bindings` is an `imbl::HashMap` — persistent, no `reserve`.)
            for (var, val) in s1.bindings.iter() {
                let new_val = match val {
                    Value::Term { id: tid, .. } => Value::term(kb.apply_subst(*tid, s2)),
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
            // WI-502 Step 2 — carry BOTH operands' constraint stores; the prior
            // code built `result` from bindings only, silently dropping them
            // (M7(b) carry-through-merge, the reflect-interpreter analog of the
            // resolver's SuccessWithBindings lift).
            result.absorb_constraints(s1);
            result.absorb_constraints(s2);
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
fn subst_bindings(
    interp: &mut Interpreter,
    args: &[Value],
    syms: &ReflectSyms,
) -> Result<Value, EvalError> {
    let [subst_val] = expect_args::<1>("Substitution.bindings", args)?;
    let handle = match subst_val {
        Value::Substitution(h) => h,
        other => {
            return Err(EvalError::TypeMismatch {
                expected: "Substitution",
                got: other.type_name().to_string(),
            })
        }
    };
    let arena = interp.subst_arena();
    let entries: Vec<_> = arena.with_subst(&handle, |s| {
        s.iter()
            .map(|(vid, val)| (*vid, val.clone()))
            .collect::<Vec<_>>()
    });
    let kb = interp.kb_mut();
    let pairs: Vec<Value> = entries
        .into_iter()
        .map(|(vid, val)| {
            let var_tid = kb.alloc(CoreTerm::Var(Var::Global(vid)));
            make_entity(
                kb,
                syms.pair,
                vec![(syms.f_fst, Value::term(var_tid)), (syms.f_snd, val)],
            )
        })
        .collect();
    Ok(build_list_value(syms, pairs))
}

// ── kernel.not (WI-080) ────────────────────────────────────────
//
// The one non-`anthill.reflect` binding in this file, since WI-20260820-MH90F moved
// `not` to `anthill.kernel` where the rest of the resolver primitives live. It stays
// HERE rather than moving with its namespace: what it binds is an eval-time face over a
// reified `Term`, so it needs this module's `expect_term` / `require_symbol` substrate
// and shares its registration pass — and `anthill.kernel`'s other members have no
// eval-side binding at all for it to sit beside.

/// `kernel.not(query: Term) -> Bool` — eval-time negation-as-failure.
/// Wraps `query` in a resolver `not(...)` goal and runs a fresh one-shot
/// SLD search. If the resolver surfaces a residual (floundering: query
/// has unbound variables), raises an error — NAF is unsound on ungrounded
/// goals and the eval context has no outer frame to resume on.
fn kernel_not(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [q] = expect_args::<1>("kernel.not", args)?;
    let goal_tid = expect_term(q, "kernel.not")?;
    let not_sym = require_symbol(interp, "anthill.kernel.not", "not")?;
    let not_goal = interp.kb_mut().alloc(CoreTerm::Fn {
        functor: not_sym,
        pos_args: vec![goal_tid].into(),
        named_args: Default::default(),
    });
    let kb = interp.kb_mut();
    // An EXISTENCE question, not an answer set (WI-FFPGD): `split_first` takes the
    // first solution and drops the stream, so answer dedup cannot change the verdict
    // — it can only fingerprint on the way to it. Stated rather than left at the
    // default, because the default claims this resolution is enumerating answers.
    let config = ResolveConfig {
        dedup_answers: false,
        ..ResolveConfig::default()
    };
    let stream = kb.resolve_lazy(&[not_goal], &config);
    match stream.split_first(kb) {
        None => Ok(Value::Bool(false)),
        Some((sol, _rest)) if sol.residual.is_empty() => Ok(Value::Bool(true)),
        Some(_) => Err(EvalError::Internal(
            "kernel.not: floundering — query has unbound variables; bind them before calling"
                .into(),
        )),
    }
}

// ── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    use anthill_core::eval::{self, Interpreter, Value};
    use anthill_core::kb::load::{self, NullResolver};
    use anthill_core::kb::KnowledgeBase;
    use anthill_core::parse;

    // WI-747: the walk is the shared `anthill_core::fs_util`.
    fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
        anthill_core::fs_util::collect_files(dir, &["anthill"]).expect("collect stdlib")
    }

    /// The stdlib, read and parsed ONCE per test binary.
    ///
    /// `load_stdlib_and_source` has ~23 callers in this module and used to re-walk,
    /// re-read and re-parse every stdlib file at each one. The parsed files are
    /// immutable inputs to `load_all`, so sharing them is safe — the same shape
    /// `anthill-core/tests/common/mod.rs`'s `STDLIB_PARSED` already uses.
    static STDLIB_PARSED: std::sync::LazyLock<Vec<parse::ir::ParsedFile>> =
        std::sync::LazyLock::new(|| {
            let stdlib_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill");
            let files = collect_anthill_files(&stdlib_dir);
            assert!(!files.is_empty(), "stdlib empty");
            files
                .iter()
                .map(|f| {
                    let src = std::fs::read_to_string(f).expect("read stdlib");
                    parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", f.display()))
                })
                .collect()
        });

    fn load_stdlib_and_source(source: &str) -> Interpreter {
        let user = parse::parse(source).expect("parse user source");
        let refs: Vec<_> = STDLIB_PARSED.iter().chain(std::iter::once(&user)).collect();

        let mut kb = KnowledgeBase::new();
        load::load_all(&mut kb, &refs, &NullResolver).unwrap_or_else(|errs| {
            for e in load::LoadError::render_all(&errs) {
                eprintln!("{e}");
            }
            panic!("load failed");
        });

        let mut interp = Interpreter::new(kb);
        eval::builtins::register_standard_builtins(&mut interp).expect("register core builtins");
        register_reflect_builtins(&mut interp).expect("register reflect builtins");
        interp
    }

    #[test]
    fn kb_sort_template_returns_sort_query_value() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.reflect_sort_tmpl
  sort Color
    entity red
    entity green
  end
end
"#,
        );
        // WI-632: the sort is passed BY REFERENCE (a `Ref` term), the way the
        // loader lowers a written `sort_template(kb(), Color)` call.
        let color_ref = {
            let kb = interp.kb_mut();
            Value::term(kb.resolve_qualified_name_term("test.reflect_sort_tmpl.Color"))
        };
        let result = interp
            .call(
                "anthill.reflect.KB.sort_template",
                &[Value::Unit, color_ref],
            )
            .expect("sort_template call");
        match result {
            Value::Entity { functor, named, .. } => {
                let name = interp.kb().local_name_of(functor).to_string();
                assert_eq!(name, "sort_query");
                assert_eq!(named.len(), 1);
                // The `sort` payload rides as the by-reference term verbatim,
                // its functor the SAME symbol the qualified name resolves to.
                let field_name = interp.kb().local_name_of(named[0].0).to_string();
                assert_eq!(field_name, "sort");
                let sort_sym = anthill_core::eval::value_functor(interp.kb(), &named[0].1)
                    .expect("sort payload names a functor");
                let expected = interp
                    .kb()
                    .try_resolve_symbol("test.reflect_sort_tmpl.Color")
                    .expect("Color resolvable by qualified name");
                assert_eq!(
                    sort_sym, expected,
                    "sort payload references the real Color sort"
                );
            }
            other => panic!("expected Entity, got {other:?}"),
        }
    }

    #[test]
    fn kb_sorts_lists_defined_sorts() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.reflect_sorts
  sort Color
    entity red
  end
  sort Shape
    entity circle
  end
end
"#,
        );
        let none_sym = interp
            .kb_mut()
            .try_resolve_symbol("anthill.prelude.Option.none")
            .expect("Option.none");
        let none_val = Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
        };
        let result = interp
            .call("anthill.reflect.KB.sorts", &[Value::Unit, none_val])
            .expect("sorts call");
        let mut count = 0;
        let mut cur = result;
        loop {
            match cur {
                Value::Entity {
                    functor, ref named, ..
                } => {
                    let fname = interp.kb().local_name_of(functor).to_string();
                    if fname == "nil" {
                        break;
                    }
                    if fname != "cons" {
                        panic!("expected cons, got {fname}");
                    }
                    count += 1;
                    cur = named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "tail")
                        .map(|(_, v)| v.clone())
                        .expect("cons tail");
                }
                other => panic!("non-entity in list: {other:?}"),
            }
        }
        assert!(
            count >= 2,
            "expected at least 2 sorts (Color + Shape), got {count}"
        );
    }

    #[test]
    fn kb_descriptions_index_is_per_target_not_global() {
        // WI-438: DescriptionInfo(target, text, index) stores a 0-based PER-TARGET
        // index (kb/load.rs emit_desc_fact). A target-filtered query must report
        // that stored index, not a global enumeration over ALL DescriptionInfo facts.
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
            let fname = interp.kb().local_name_of(functor).to_string();
            if fname == "nil" {
                break;
            }
            assert_eq!(fname, "cons", "expected cons in result list");
            let head = named
                .iter()
                .find(|(s, _)| interp.kb().local_name_of(*s) == "head")
                .map(|(_, v)| v.clone())
                .expect("cons head");
            let tail = named
                .iter()
                .find(|(s, _)| interp.kb().local_name_of(*s) == "tail")
                .map(|(_, v)| v.clone())
                .expect("cons tail");
            match head {
                Value::Entity { named: dn, .. } => {
                    let content = dn
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "content")
                        .and_then(|(_, v)| v.as_str().map(str::to_string))
                        .expect("content field");
                    let index = dn
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "index")
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
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.reflect_roundtrip
  sort Color
    entity red
  end
end
"#,
        );
        let sym = interp
            .kb()
            .try_resolve_symbol("test.reflect_roundtrip.Color.red")
            .expect("red symbol");
        let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(sym));
        // reify → TermRepr (Value::Entity); reflect → back to Term (Value::Term).
        let reified = interp
            .call(
                "anthill.reflect.KB.reify",
                &[Value::Unit, Value::term(ref_tid)],
            )
            .expect("reify call");
        let reflected = interp
            .call("anthill.reflect.KB.reflect", &[Value::Unit, reified])
            .expect("reflect call");
        match reflected {
            Value::Term { id: tid, .. } => {
                // Same symbol round-trip → same TermId (hash-consed).
                assert_eq!(tid, ref_tid);
            }
            other => panic!("expected Value::Term, got {other:?}"),
        }
    }

    // `kb_nonvar_and_ground_classify_terms` (a `Ref` term is nonvar+ground, a
    // `Var` term is neither) is not deleted, it is the first two rows of the test
    // below — where they are labelled CONTROL, because those are exactly the two
    // carriers both owners always agreed on.

    /// WI-982 — the two owners of "is this a variable?" / "is this ground?" answer
    /// by CONTENT, on every carrier, not by whether the carrier happens to be a
    /// hash-consed `Value::Term`.
    ///
    /// WHAT FAILS WITHOUT THE CHANGE, and each of these was driven by putting the
    /// old body back:
    ///   * against the `expect_term` + raw-`TermId` host op — EVERY row but the
    ///     two controls, all with `Err(TypeMismatch { expected: "Term" })`, so
    ///     `host_says` panics on its `expect`. It could not see the carrier at all.
    ///   * against the third copy, `KbBridge::ground` (deleted here) — the
    ///     `Value::Entity` row, and only that one: no `Entity` arm, so a compound
    ///     with unbound children fell to `_ => true` and answered GROUND where the
    ///     resolver answers not-ground. Its `nonvar` twin had the same hole one
    ///     variant over — no `Value::Node` arm — so a var occurrence read as
    ///     nonvar. A wrong answer, not an error: nothing would have reported it.
    ///
    /// WHAT PASSES EITHER WAY, BY DESIGN — the CONTROLS, and the reason they are
    /// here: the two plain-`Value::Term` rows (`Ref` and `Var`). They agreed
    /// before this change and agree after. That is the finding this test pins:
    /// the owners agreed exactly on the one carrier the host could see, which is
    /// what "answers by carrier" means.
    ///
    /// WHAT THE RESOLVER ROWS ARE WORTH, stated so they are not over-read. After
    /// the change both doors reach ONE predicate, so `resolver_says` is not an
    /// independent second opinion — it is the assertion that the two doors are
    /// still wired to the same owner, and it fails the moment either grows its own
    /// derivation again. Before the change it WAS independent, which is how the
    /// divergence was found.
    #[test]
    fn nonvar_and_ground_answer_by_content_not_carrier() {
        use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
        use anthill_core::span::{SourceId, SourceSpan};

        let mut interp = load_stdlib_and_source(
            r#"
namespace test.wi982_carrier
  sort Color
    entity red
  end
end
"#,
        );
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 0);
        let red = interp
            .kb()
            .try_resolve_symbol("test.wi982_carrier.Color.red")
            .expect("red symbol");
        let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(red));
        let vsym = interp.kb_mut().intern("x");
        let vid = interp.kb_mut().fresh_var(vsym);
        let var_tid = interp.kb_mut().alloc(CoreTerm::Var(Var::Global(vid)));

        // The resolver's reading of the same question, over the same carrier: a
        // `Value::Entity` goal with the builtin's functor. Its answer is
        // THREE-valued, so collapse it the way the eval phase must — a delayed
        // goal survives as a residual, and nothing at eval time will ever bind it,
        // so "delayed" reads as "no".
        fn resolver_says(interp: &mut Interpreter, qn: &str, arg: &Value) -> bool {
            let sym = interp.kb().try_resolve_symbol(qn).expect("builtin symbol");
            let goal = Value::Entity {
                functor: sym,
                pos: vec![arg.clone()].into(),
                named: Vec::new().into(),
            };
            let sols = interp.kb_mut().resolve(&[goal], &ResolveConfig::default());
            sols.len() == 1 && sols[0].residual.is_empty()
        }
        fn host_says(interp: &mut Interpreter, qn: &str, arg: &Value) -> bool {
            match interp
                .call(qn, &[arg.clone()])
                .unwrap_or_else(|e| panic!("{qn} must ANSWER for this carrier, got {e:?}"))
            {
                Value::Bool(b) => b,
                other => panic!("{qn} must return Bool, got {other:?}"),
            }
        }

        // (label, value, is_nonvar, is_ground)
        let rows: Vec<(&str, Value, bool, bool)> = vec![
            ("CONTROL Value::Term(Ref)", Value::term(ref_tid), true, true),
            (
                "CONTROL Value::Term(Var)",
                Value::term(var_tid),
                false,
                false,
            ),
            ("Value::Int scalar", Value::Int(5), true, true),
            ("Value::Str scalar", Value::Str("hi".into()), true, true),
            ("Value::Bool scalar", Value::Bool(true), true, true),
            (
                "Value::Var (value-level logic var)",
                Value::Var(Var::Global(vid)),
                false,
                false,
            ),
            (
                "Value::Node var occurrence",
                Value::Node(NodeOccurrence::new_expr(
                    Expr::Var(Var::Global(vid)),
                    span,
                    None,
                )),
                false,
                false,
            ),
            (
                "Value::Node literal occurrence",
                Value::Node(NodeOccurrence::new_expr(
                    Expr::Const(anthill_core::kb::term::Literal::Int(7)),
                    span,
                    None,
                )),
                true,
                true,
            ),
            (
                "Value::Entity with an unbound child",
                Value::Entity {
                    functor: red,
                    pos: vec![Value::Var(Var::Global(vid))].into(),
                    named: Vec::new().into(),
                },
                true,
                false,
            ),
        ];

        for (label, v, want_nonvar, want_ground) in rows {
            assert_eq!(
                host_says(&mut interp, "anthill.reflect.nonvar", &v),
                want_nonvar,
                "host nonvar disagrees for {label}"
            );
            assert_eq!(
                host_says(&mut interp, "anthill.reflect.ground", &v),
                want_ground,
                "host ground disagrees for {label}"
            );
            assert_eq!(
                resolver_says(&mut interp, "anthill.reflect.nonvar", &v),
                want_nonvar,
                "resolver nonvar disagrees for {label}"
            );
            assert_eq!(
                resolver_says(&mut interp, "anthill.reflect.ground", &v),
                want_ground,
                "resolver ground disagrees for {label}"
            );
        }
    }

    /// WI-982 — `nonvar` / `ground` are reachable FROM ANTHILL, in an operation
    /// body, under the same name and arity a rule body uses as a goal.
    ///
    /// This is the row the ticket found unreachable and mis-diagnosed. Before the
    /// change the name existed only as a resolver builtin TAG — declared nowhere —
    /// so a body-position call had no operation to type against and the loader
    /// refused it, with a message that named `KB.nonvar` (the WI-565 hint keys on
    /// the SHORT name, and the member had the same one). Both spellings the ticket
    /// measured are driven here: the imported bare name and the fully-qualified
    /// one. A load-only assertion would not be evidence — the operations are
    /// CALLED and their values asserted, so a name that resolved to nothing would
    /// fail here rather than pass quietly.
    #[test]
    fn nonvar_and_ground_are_callable_from_an_operation_body() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.wi982_body
  import anthill.reflect.nonvar
  import anthill.reflect.ground

  -- bare, via import
  operation lit_is_nonvar() -> Bool = nonvar(42)
  -- fully qualified
  operation lit_is_ground() -> Bool = anthill.reflect.ground(42)
end
"#,
        );
        assert!(
            matches!(
                interp.call("test.wi982_body.lit_is_nonvar", &[]),
                Ok(Value::Bool(true))
            ),
            "a bare imported `nonvar(42)` in an operation body must answer true",
        );
        assert!(
            matches!(
                interp.call("test.wi982_body.lit_is_ground", &[]),
                Ok(Value::Bool(true))
            ),
            "a fully-qualified `anthill.reflect.ground(42)` in an operation body must answer true",
        );
    }

    /// WI-759 — this module must NOT re-register `anthill.reflect.field_access`.
    /// `register_builtin` is a plain map insert (LAST WINS) and `register_reflect_builtins`
    /// runs after the standard set, so a duplicate here silently shadows the production
    /// implementation for any driver that installs both. This test installs both in that
    /// order — the exact configuration that would have been shadowed — and asserts the
    /// PRODUCTION contract still answers: a `Value::Entity` receiver and a `String`
    /// selector, which the retired duplicate (`expect_term` + `expect_symbol`) rejected on
    /// both counts.
    #[test]
    fn field_access_is_not_shadowed_by_this_module() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.reflect_field
  sort Point
    entity pt(x: Int64, y: Int64)
  end
end
"#,
        );
        let pt_sym = interp
            .kb()
            .try_resolve_symbol("test.reflect_field.Point.pt")
            .expect("pt symbol");
        let x_sym = interp.kb_mut().intern("x");
        let y_sym = interp.kb_mut().intern("y");
        let pt = Value::Entity {
            functor: pt_sym,
            pos: Vec::new().into(),
            named: vec![(x_sym, Value::Int(1)), (y_sym, Value::Int(2))].into(),
        };
        let result = interp
            .call(
                "anthill.reflect.field_access",
                &[pt, Value::Str("x".to_string())],
            )
            .expect("field_access must still route to the production implementation");
        assert!(
            matches!(result, Value::Int(1)),
            "expected the projected field value 1, got {result:?}",
        );
    }

    #[test]
    fn sort_passthrough_ops_work() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.reflect_sort_pt
  sort Color
    entity red
  end
end
"#,
        );
        let sym = interp
            .kb()
            .try_resolve_symbol("test.reflect_sort_pt.Color")
            .expect("Color symbol");
        let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(sym));

        let same = interp
            .call("anthill.reflect.sort_as_term", &[Value::term(ref_tid)])
            .expect("sort_as_term");
        assert!(matches!(same, Value::Term { id: t, .. } if t == ref_tid));

        let ok = interp
            .call("anthill.reflect.can_be_sort", &[Value::term(ref_tid)])
            .expect("can_be_sort");
        assert!(matches!(ok, Value::Bool(true)));

        // Int64 literal is NOT a sort.
        let lit = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(42)));
        let not_sort = interp
            .call("anthill.reflect.can_be_sort", &[Value::term(lit)])
            .expect("can_be_sort (lit)");
        assert!(matches!(not_sort, Value::Bool(false)));

        let as_opt = interp
            .call("anthill.reflect.term_as_sort", &[Value::term(lit)])
            .expect("term_as_sort");
        match as_opt {
            Value::Entity { functor, named, .. } => {
                let name = interp.kb().local_name_of(functor).to_string();
                assert_eq!(name, "none");
                assert!(named.is_empty());
            }
            other => panic!("expected Option entity, got {other:?}"),
        }
    }

    /// Drive `qualified_name` / `short_name` / `kind` on one `Symbol` value and
    /// assert all three answers.
    ///
    /// Shared by the two tests that differ ONLY in the carrier they hand in —
    /// `symbol_ops_qualified_short_lookup_kind` (interned `Term::Ref`) and
    /// `a_minted_symbol_reads_through_the_host_symbol_ops` (minted
    /// `Value::SymbolRef`). The claim under test is that those answer identically,
    /// so the op set has to be one list: with two hand-copied blocks, an op added
    /// to one is silently absent from the other and the equality stops being
    /// checked without anything going red.
    fn assert_symbol_ops(
        interp: &mut Interpreter,
        sym: Value,
        qualified: &str,
        short: &str,
        kind: &str,
    ) {
        for (op, expected) in [
            ("anthill.reflect.qualified_name", qualified),
            ("anthill.reflect.short_name", short),
            ("anthill.reflect.kind", kind),
        ] {
            match interp.call(op, &[sym.clone()]) {
                Ok(Value::Str(got)) => {
                    assert_eq!(got, expected, "{op} on a {} carrier", sym.type_name(),)
                }
                other => panic!(
                    "{op} must answer a String on a {} carrier, got {other:?}",
                    sym.type_name(),
                ),
            }
        }
    }

    /// WI-1016 — THE SEAM between the two crates' halves of one reflect surface:
    /// a `Symbol` MINTED by an anthill-core op is READ by an anthill-stl one.
    ///
    /// `Dictionary.impl` / `OpRef.op` / `OpRef.named` now hand back
    /// `Value::SymbolRef`; `qualified_name` / `short_name` / `kind` / `scope` /
    /// `resolve_sort_instantiation_param` all read their `Symbol` argument through
    /// the one `expect_symbol`. Nothing in either crate's own tests crosses that
    /// line, which is why both halves were green while the composition was broken.
    ///
    /// TWO CONTROLS, both measured by backing the change out:
    ///  - revert `eval/builtins.rs::symbol_value` to `Value::term(alloc(Term::Ref))`
    ///    → the `Value::SymbolRef` assert fails; every other assert here still
    ///    passes, which is exactly why WI-1015 could revert the flip unnoticed.
    ///  - revert `expect_symbol` to its `Value::Term { id } → Term::Ref | Ident`
    ///    match → all five op calls below fail with `TypeMismatch`, while the
    ///    resolver's twins (`builtin_qualified_name`, …) go on answering. One
    ///    operation, two answers, decided by which phase asked.
    #[test]
    fn a_minted_symbol_reads_through_the_host_symbol_ops() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.wi1016_seam
  sort Color
    entity red
  end
  sort Shape
    entity circle
  end
end
"#,
        );
        let color = interp
            .kb()
            .try_resolve_symbol("test.wi1016_seam.Color")
            .expect("Color declared above");
        let dict = interp
            .alloc_dictionary_unchecked(color, [])
            .expect("the stdlib defines anthill.realization.runtime.Dictionary")
            .into_value();

        // The producer: `Dictionary.impl(d) -> Symbol`.
        let sym_val = interp
            .call("anthill.realization.runtime.Dictionary.impl", &[dict])
            .expect("Dictionary.impl");
        assert!(
            matches!(sym_val, Value::SymbolRef(s) if s == color),
            "the reflect Symbol answer rides the value carrier, got {sym_val:?}",
        );

        // The three string readers, through the SAME block that
        // `symbol_ops_qualified_short_lookup_kind` drives on the interned carrier
        // — the point of this test is that both carriers answer alike, so the two
        // must not be able to drift into checking different op sets.
        assert_symbol_ops(
            &mut interp,
            sym_val.clone(),
            "test.wi1016_seam.Color",
            "Color",
            "Sort",
        );

        // `scope` on the minted carrier — and since WI-984 it is worth pinning WHICH
        // symbol. This used to answer whatever `KnowledgeBase::scope_of` did, a scan
        // for a SIBLING sort/namespace/operation sharing the symbol's declaring
        // scope, so only the `some`/`none` shape could be asserted. It now answers
        // the DECLARING SCOPE its own stdlib signature promises ("Symbol → enclosing
        // scope symbol"), which for `Color` is the namespace that declares it.
        let scope_answer = interp
            .call("anthill.reflect.scope", &[sym_val.clone()])
            .expect("scope must answer on a minted Symbol");
        assert_eq!(
            anthill_core::eval::value_functor(interp.kb(), &scope_answer)
                .map(|f| interp.kb().local_name_of(f).to_string()),
            Some("some".to_string()),
        );
        let inner = match &scope_answer {
            Value::Entity { named, .. } => named[0].1.clone(),
            other => panic!("expected `some(value: …)`, got {other:?}"),
        };
        assert_eq!(
            anthill_core::eval::value_functor(interp.kb(), &inner)
                .map(|f| interp.kb().qualified_name_of(f).to_string()),
            Some("test.wi1016_seam".to_string()),
            "`scope` answers the DECLARING scope, not a sibling",
        );

        // The fifth reader, whose `param` argument is the Symbol: a `SortView`
        // instance term plus the param NAME as the minted carrier.
        let (inst, t_param) = {
            let t_param = interp.kb_mut().intern("T");
            let sort_view = interp.kb_mut().intern("SortView");
            let inst = interp
                .kb_mut()
                .alloc_from_value(&Value::Entity {
                    functor: sort_view,
                    pos: Vec::new().into(),
                    named: vec![(t_param, Value::Int(42))].into(),
                })
                .expect("a SortView instance lowers");
            (inst, t_param)
        };
        let bound = interp
            .call(
                "anthill.reflect.resolve_sort_instantiation_param",
                &[Value::term(inst), Value::SymbolRef(t_param)],
            )
            .expect("resolve_sort_instantiation_param must accept a minted Symbol param");
        assert!(
            matches!(bound, Value::Term { id, .. }
                if matches!(interp.kb().get_term(id), CoreTerm::Const(Literal::Int(42)))),
            "the param's binding comes back, got {bound:?}",
        );
    }

    #[test]
    fn kernel_not_on_satisfiable_goal_returns_false() {
        // A ground goal that has a fact → not(goal) should be Bool(false).
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.not_sat
  sort Color
    entity red
    entity green
  end
  fact Color(entity: red)
end
"#,
        );
        // Build the goal: Color(entity: red).
        let color_sym = interp
            .kb()
            .try_resolve_symbol("test.not_sat.Color")
            .expect("Color sort symbol");
        let red_sym = interp
            .kb()
            .try_resolve_symbol("test.not_sat.Color.red")
            .expect("red symbol");
        let entity_field = interp.kb_mut().intern("entity");
        let red_ref = interp.kb_mut().alloc(CoreTerm::Ref(red_sym));
        let goal = interp.kb_mut().alloc(CoreTerm::Fn {
            functor: color_sym,
            pos_args: Default::default(),
            named_args: vec![(entity_field, red_ref)].into(),
        });
        let result = interp
            .call("anthill.kernel.not", &[Value::term(goal)])
            .expect("kernel.not");
        assert!(
            matches!(result, Value::Bool(false)),
            "satisfiable goal → not should be false, got {result:?}"
        );
    }

    #[test]
    fn kernel_not_on_unsatisfiable_goal_returns_true() {
        // A ground goal with no matching fact → not(goal) should be Bool(true).
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.not_unsat
  sort Color
    entity red
    entity green
  end
  fact Color(entity: red)
end
"#,
        );
        let color_sym = interp
            .kb()
            .try_resolve_symbol("test.not_unsat.Color")
            .expect("Color sort symbol");
        let green_sym = interp
            .kb()
            .try_resolve_symbol("test.not_unsat.Color.green")
            .expect("green symbol");
        let entity_field = interp.kb_mut().intern("entity");
        let green_ref = interp.kb_mut().alloc(CoreTerm::Ref(green_sym));
        let goal = interp.kb_mut().alloc(CoreTerm::Fn {
            functor: color_sym,
            pos_args: Default::default(),
            named_args: vec![(entity_field, green_ref)].into(),
        });
        let result = interp
            .call("anthill.kernel.not", &[Value::term(goal)])
            .expect("kernel.not");
        assert!(
            matches!(result, Value::Bool(true)),
            "unsatisfiable goal → not should be true, got {result:?}"
        );
    }

    #[test]
    fn kb_fields_by_reference_disambiguates() {
        // WI-632: `KB.fields` takes the entity BY REFERENCE, so a short name two
        // sorts share (WI-631's ambiguity hazard) is a non-issue — `Beta.dup` and
        // `Alpha.dup` are distinct references, each answering its own schema.
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.wi632_interp
  sort Alpha { entity dup(x: Int64) }
  sort Beta { entity dup(y: String) }
end
"#,
        );
        // The one FieldInfo's `name` for the entity named `qname`. The result is
        // `cons(head: FieldInfo(name: <field>, ...), tail: nil)`.
        let field_name = |interp: &mut Interpreter, qname: &str| -> String {
            let entity = {
                let kb = interp.kb_mut();
                Value::term(kb.resolve_qualified_name_term(qname))
            };
            let result = interp
                .call("anthill.reflect.KB.fields", &[Value::Unit, entity])
                .expect("fields by reference never errors");
            let field_named = |v: &Value, key: &str| -> Option<Value> {
                match v {
                    Value::Entity { named, .. } => named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == key)
                        .map(|(_, v)| v.clone()),
                    _ => None,
                }
            };
            let head = field_named(&result, "head").expect("non-empty field list");
            assert!(
                matches!(field_named(&result, "tail"), Some(Value::Entity { functor, .. })
                    if interp.kb().local_name_of(functor) == "nil"),
                "dup has exactly one field",
            );
            match field_named(&head, "name") {
                Some(Value::Str(s)) => s,
                other => panic!("FieldInfo.name should be Str, got {other:?}"),
            }
        };
        assert_eq!(field_name(&mut interp, "test.wi632_interp.Beta.dup"), "y");
        assert_eq!(field_name(&mut interp, "test.wi632_interp.Alpha.dup"), "x");
    }

    #[test]
    fn kernel_not_on_ungrounded_goal_flounders() {
        // Free variable in the query → NAF is unsound → error.
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.not_flounder
  sort Color
    entity red
  end
  fact Color(entity: red)
end
"#,
        );
        let color_sym = interp
            .kb()
            .try_resolve_symbol("test.not_flounder.Color")
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
        let result = interp.call("anthill.kernel.not", &[Value::term(goal)]);
        match result {
            Err(EvalError::Internal(msg)) => {
                assert!(
                    msg.contains("floundering"),
                    "expected floundering message, got: {msg}"
                );
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
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.subst_stream
  sort Color
    entity red
  end
end
"#,
        );
        // Build pattern_query(EntityInfo(name: ?n, fields: ?f)) as a Value.
        let ei_sym = interp
            .kb()
            .try_resolve_symbol("anthill.reflect.EntityInfo")
            .expect("EntityInfo");
        let pq_sym = interp
            .kb()
            .try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
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
            named: vec![
                (name_field, Value::term(var_n)),
                (fields_field, Value::term(var_f)),
            ]
            .into(),
        };
        let query = Value::Entity {
            functor: pq_sym,
            pos: Vec::new().into(),
            named: vec![(term_field, inner)].into(),
        };

        let stream = interp
            .call("anthill.reflect.KB.execute", &[Value::Unit, query])
            .expect("execute");
        let pumped = interp
            .call("anthill.prelude.LogicalStream.splitFirst", &[stream])
            .expect("splitFirst");

        // Unwrap Option.some → Pair.pair → fst = the Solution element.
        let fst = match pumped {
            Value::Entity {
                named: some_named, ..
            } => {
                let pair = &some_named[0].1;
                match pair {
                    Value::Entity {
                        named: pair_named, ..
                    } => pair_named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "fst")
                        .map(|(_, v)| v.clone())
                        .expect("fst"),
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
                let ctor = interp.kb().local_name_of(functor).to_string();
                assert!(
                    ctor.ends_with("definite") || ctor.ends_with("undecided"),
                    "expected a Solution (definite/undecided), got functor {ctor}",
                );
                let subst = named
                    .iter()
                    .find(|(s, _)| interp.kb().local_name_of(*s) == "subst")
                    .map(|(_, v)| v.clone())
                    .expect("subst field on Solution");
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
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.subst_apply
  sort X
    entity x
  end
end
"#,
        );
        // Build subst {?v → Int64(42)}, apply to ?v.
        let v_sym = interp.kb_mut().intern("v");
        let vid = interp.kb_mut().fresh_var(v_sym);
        let var_term = interp.kb_mut().alloc(CoreTerm::Var(Var::Global(vid)));
        let val_term = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(42)));

        let mut s = Substitution::new();
        s.bindings.insert(vid, Value::term(val_term));
        let s_handle = interp.alloc_subst(s);

        let result = interp
            .call(
                "anthill.reflect.Substitution.apply",
                &[
                    Value::Substitution(s_handle),
                    Value::term(var_term),
                    Value::Unit,
                ],
            )
            .expect("apply");
        match result {
            Value::Term { id: tid, .. } => {
                assert_eq!(tid, val_term, "?v → Int64(42) should rewrite the variable");
            }
            other => panic!("expected Value::Term, got {other:?}"),
        }
    }

    #[test]
    fn substitution_bindings_enumerates_pairs() {
        use anthill_core::kb::subst::Substitution;
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.subst_bindings
  sort X
    entity x
  end
end
"#,
        );
        // Build subst {?v → Int64(42)}, enumerate it.
        let v_sym = interp.kb_mut().intern("v");
        let vid = interp.kb_mut().fresh_var(v_sym);
        let val_term = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(42)));
        let mut s = Substitution::new();
        s.bindings.insert(vid, Value::term(val_term));
        let s_handle = interp.alloc_subst(s);

        let result = interp
            .call(
                "anthill.reflect.Substitution.bindings",
                &[Value::Substitution(s_handle)],
            )
            .expect("bindings");
        // A cons-list with one Pair(fst: <var term>, snd: Int64(42)).
        let head = match result {
            Value::Entity { ref named, .. } => named
                .iter()
                .find(|(s, _)| interp.kb().local_name_of(*s) == "head")
                .map(|(_, v)| v.clone())
                .expect("cons.head"),
            other => panic!("expected cons list, got {other:?}"),
        };
        match head {
            Value::Entity { named, .. } => {
                let field = |k: &str| {
                    named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == k)
                        .map(|(_, v)| v.clone())
                };
                match field("snd").expect("pair.snd") {
                    Value::Term { id: tid, .. } => {
                        assert_eq!(tid, val_term, "snd should be the bound value term")
                    }
                    other => panic!("snd should be Value::Term, got {other:?}"),
                }
                match field("fst").expect("pair.fst") {
                    Value::Term { id: tid, .. } => assert!(
                        matches!(interp.kb().get_term(tid), CoreTerm::Var(_)),
                        "fst should be a var term carrying the variable's identity"
                    ),
                    other => panic!("fst should be Value::Term(Var), got {other:?}"),
                }
            }
            other => panic!("expected Pair entity, got {other:?}"),
        }
    }

    #[test]
    fn subst_compose_chases_bare_value_var() {
        use anthill_core::kb::subst::Substitution;
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.compose_var
  sort X
    entity x
  end
end
"#,
        );
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
        s2.bindings.insert(vid_w, Value::term(seven));
        let h1 = interp.alloc_subst(s1);
        let h2 = interp.alloc_subst(s2);

        let composed = interp
            .call(
                "anthill.reflect.Substitution.compose",
                &[
                    Value::Substitution(h1),
                    Value::Substitution(h2),
                    Value::Unit,
                ],
            )
            .expect("compose");
        let handle = match composed {
            Value::Substitution(h) => h,
            other => panic!("expected Value::Substitution, got {other:?}"),
        };
        let arena = interp.subst_arena();
        let z_binding = arena.with_subst(&handle, |s| s.bindings.get(&vid_z).cloned());
        match z_binding.expect("z should be bound") {
            Value::Term { id: t, .. } => assert!(
                matches!(interp.kb().get_term(t), CoreTerm::Const(Literal::Int(7))),
                "z should chase to Int64(7)"
            ),
            Value::Int(n) => assert_eq!(n, 7, "z should chase to 7"),
            other => {
                panic!("z should chase through w to 7, got {other:?} (bare Var = unfixed bug)")
            }
        }
    }

    #[test]
    fn subst_arena_reclaims_on_drop() {
        // After running a stream-pumping program, all substitution slots
        // should be reclaimed — no leaks from the per-solution alloc.
        let interp = load_stdlib_and_source(
            r#"
namespace test.subst_reclaim
  sort Pt
    entity pt
  end
end
"#,
        );
        assert_eq!(interp.subst_arena_live_count(), 0);

        use anthill_core::kb::subst::Substitution;
        let h = interp.alloc_subst(Substitution::new());
        assert_eq!(interp.subst_arena_live_count(), 1);
        drop(h);
        assert_eq!(interp.subst_arena_live_count(), 0);
    }

    #[test]
    fn symbol_ops_qualified_short_lookup_kind() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.reflect_syms
  sort Color
    entity red
  end
end
"#,
        );
        let sym = interp
            .kb()
            .try_resolve_symbol("test.reflect_syms.Color.red")
            .expect("red symbol");
        let ref_tid = interp.kb_mut().alloc(CoreTerm::Ref(sym));

        let qn = interp
            .call("anthill.reflect.qualified_name", &[Value::term(ref_tid)])
            .expect("qualified_name");
        assert!(matches!(qn, Value::Str(ref s) if s == "test.reflect_syms.Color.red"));

        let sn = interp
            .call("anthill.reflect.short_name", &[Value::term(ref_tid)])
            .expect("short_name");
        assert!(matches!(sn, Value::Str(ref s) if s == "red"));

        let kn = interp
            .call("anthill.reflect.kind", &[Value::term(ref_tid)])
            .expect("kind");
        assert!(matches!(kn, Value::Str(ref s) if s == "Entity"));

        let ls = interp
            .call(
                "anthill.reflect.lookup_symbol",
                &[Value::Str("test.reflect_syms.Color.red".into())],
            )
            .expect("lookup_symbol");
        assert!(matches!(ls, Value::Term { .. }));
    }

    /// The symbol a `lookup_symbol` result denotes, by qualified name.
    fn looked_up_name(interp: &mut Interpreter, name: &str) -> Result<String, EvalError> {
        let v = interp.call("anthill.reflect.lookup_symbol", &[Value::Str(name.into())])?;
        let sym = interp
            .kb()
            .value_symbol(&v)
            .expect("lookup_symbol answers a symbol reference");
        Ok(interp.kb().qualified_name_of(sym).to_string())
    }

    /// WI-913 — FAILS PRE-FIX with `lookup_symbol: 'cons' not in scope`, a message
    /// whose claim the code never checked: `try_resolve_symbol` is
    /// `by_qualified_name` and consults no scope. `cons` is the implicit tier's own
    /// name, so the message was wrong about a name that DOES denote something here.
    ///
    /// It asserts the same targets as `anthill-core`'s
    /// `wi913_host_name_ladder_test::sld_lookup_symbol_reads_the_implicit_tier`, and
    /// that pairing is the point: one declared operation, two backings, and after
    /// WI-984 they may not answer differently.
    #[test]
    fn lookup_symbol_reads_the_implicit_tier() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.wi913_stl
  sort Color
    entity red
  end
end
"#,
        );
        assert_eq!(
            looked_up_name(&mut interp, "cons").expect("cons denotes its target"),
            "anthill.prelude.List.cons",
        );
        assert_eq!(
            looked_up_name(&mut interp, "SortInfo").expect("SortInfo denotes its target"),
            "anthill.reflect.SortInfo",
        );
        // CONTROL — a qualified name resolves identically on both sides of the fix.
        assert_eq!(
            looked_up_name(&mut interp, "test.wi913_stl.Color.red").expect("qualified name"),
            "test.wi913_stl.Color.red",
        );
        // …and a short USER name still denotes nothing at `<global>`, before and
        // after: the ladder adds the implicit tier, not a global short-name scan
        // (WI-476). The error names the operation and the name.
        match looked_up_name(&mut interp, "Color") {
            Err(EvalError::Internal(msg)) => assert!(
                msg.contains("lookup_symbol") && msg.contains("Color"),
                "got: {msg}",
            ),
            other => panic!("expected a loud unknown-name error, got {other:?}"),
        }
    }

    #[test]
    fn kb_constructors_lists_sort_entities() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.reflect_ctors
  sort Fruit
    entity apple
    entity banana
    entity cherry
  end
end
"#,
        );
        let fruit = {
            let kb = interp.kb_mut();
            Value::term(kb.resolve_qualified_name_term("test.reflect_ctors.Fruit"))
        };
        let result = interp
            .call("anthill.reflect.KB.constructors", &[Value::Unit, fruit])
            .expect("constructors call");
        let mut names: Vec<String> = Vec::new();
        let mut cur = result;
        loop {
            match cur {
                Value::Entity { functor, named, .. } => {
                    let fname = interp.kb().local_name_of(functor).to_string();
                    if fname == "nil" {
                        break;
                    }
                    let head = named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "head")
                        .map(|(_, v)| v.clone());
                    let tail = named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "tail")
                        .map(|(_, v)| v.clone());
                    if let Some(Value::Str(s)) = head {
                        names.push(s);
                    }
                    cur = tail.expect("cons tail");
                }
                other => panic!("non-entity in list: {other:?}"),
            }
        }
        for expected in ["apple", "banana", "cherry"] {
            assert!(
                names.iter().any(|n| n == expected),
                "missing '{expected}' in {names:?}"
            );
        }
    }

    /// Walk a value cons/nil list into its element `Value`s (test helper).
    fn list_values(interp: &Interpreter, mut cur: Value) -> Vec<Value> {
        let mut out = Vec::new();
        loop {
            match cur {
                Value::Entity { functor, named, .. } => {
                    let fname = interp.kb().local_name_of(functor).to_string();
                    if fname.rsplit('.').next() == Some("nil") {
                        break;
                    }
                    let head = named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "head")
                        .map(|(_, v)| v.clone());
                    let tail = named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "tail")
                        .map(|(_, v)| v.clone());
                    match (head, tail) {
                        (Some(h), Some(t)) => {
                            out.push(h);
                            cur = t;
                        }
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
            Value::Entity { named, .. } => named
                .iter()
                .find(|(s, _)| interp.kb().local_name_of(*s) == key)
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
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.wi548_op_contract
  import anthill.prelude.Int64

  sort Tank
    entity tank(fuel: Int64)
    entity Full(t: Tank)
    operation fill(t: Tank) -> Tank requires Full(t) ensures Full(t)
      meta [Refuel, Profile: "cpp20-stl"]
  end
end
"#,
        );
        let tank = {
            let kb = interp.kb_mut();
            Value::term(kb.resolve_qualified_name_term("test.wi548_op_contract.Tank"))
        };
        let result = interp
            .call("anthill.reflect.KB.operations", &[Value::Unit, tank])
            .expect("operations call");

        // The op's `name` field is `Value::Term(Ref(sym))`; match by short name.
        let op_short = |interp: &Interpreter, op: &Value| -> Option<String> {
            match entity_field(interp, op, "name")? {
                Value::Term { id: tid, .. } => match interp.kb().get_term(tid) {
                    CoreTerm::Ref(s) => {
                        let n = interp.kb().local_name_of(*s).to_string();
                        Some(n.rsplit('.').next().unwrap_or(&n).to_string())
                    }
                    _ => None,
                },
                _ => None,
            }
        };

        let ops = list_values(&interp, result);
        let fill = ops
            .iter()
            .find(|op| op_short(&interp, op).as_deref() == Some("fill"))
            .expect("fill OperationInfo entity");

        let requires = list_values(
            &interp,
            entity_field(&interp, fill, "requires").expect("requires field present"),
        );
        let ensures = list_values(
            &interp,
            entity_field(&interp, fill, "ensures").expect("ensures field present"),
        );
        assert!(
            !ensures.is_empty(),
            "fill should surface its user `ensures` clause"
        );
        assert!(
            !requires.is_empty(),
            "fill should surface `requires` (incl. synthetic EffectsRuntime)"
        );
        // Each ground contract clause rides as a goal-term Value (matching bridge).
        match &ensures[0] {
            Value::Term { .. } => {}
            other => panic!("ensures clause should be a Value::Term goal, got {other:?}"),
        }

        // `meta` is surfaced (not omitted) — a non-empty `meta(...)` term here.
        let meta = entity_field(&interp, fill, "meta").expect("meta field present");
        match meta {
            Value::Term { id: tid, .. } => assert!(
                matches!(interp.kb().get_term(tid),
                    CoreTerm::Fn { named_args, .. } if !named_args.is_empty()),
                "meta should be a non-empty meta(...) term",
            ),
            other => panic!("meta field should be a Value::Term, got {other:?}"),
        }
    }
}
