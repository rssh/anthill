//! Eval-time builtins for the `anthill.reflect` introspection surface —
//! `KB.sorts` / `operations` / `constructors` / `fields` / `rules` /
//! `descriptions` / `sort_template` / `reify` / `reflect`, the namespace-level
//! symbol and term-shape ops, `Substitution.apply` / `compose` / `bindings` — and
//! `anthill.kernel.not`'s eval face.
//!
//! Scripts call `KB.sort_template`, `KB.sorts`, `KB.operations`, … and get
//! `Value`-typed results whose shapes match the sort declarations in
//! `stdlib/anthill/reflect/reflect.anthill`. The KB walks are the shared
//! [`reader`] (`kb::reflect_reader`), which anthill-stl's host-Rust bridge maps to
//! its typed structs.
//!
//! WI-20260923-9R5HN — `HOST_FNS` ROWS, NAMED BY BINDING BLOCKS. This module was
//! anthill-stl's `reflect::builtins`, whose `register_reflect_builtins` bound these
//! 24 operations by qualified name through the silent-skip `register_if_present`:
//! INVISIBLE to `is_interpreter_mapped_op` (so a rule body could not reduce them —
//! and `not(KB.constructors(kb(), Color) = [..])` answered 1 DEFINITE out of a call
//! that never ran, kernel-language.md §5.2's decided-false decline), unclaimed by
//! their declarations, and silently absent from a KB missing them. They are keyed
//! through `rustland/anthill-stl/anthill/reflect.anthill` and `kernel.anthill` like
//! the rest of the reflection surface (WI-880), and their declarations carry
//! `@[host_implemented]`.
//!
//! Two things had kept them out, both answered by the move. The functions lived in
//! the wrong CRATE — `HOST_FNS` is anthill-core's, and a binding block naming
//! anthill-stl functions breaks every interpreter built without that crate. And
//! eleven closed over symbols resolved from the KB after load, which WI-1122's
//! embedder table (sealed at load) cannot take; [`ReflectSyms`] is now resolved at
//! each call instead, from the KB the call runs against.
//!
//! A HANDFUL ARE NOT `KB` MEMBERS, and the difference is not cosmetic: an
//! operation whose question is about a KB (`sorts`, `rules`, `facts_of`) takes
//! it as a receiver, while one whose question is about a VALUE — `nonvar`,
//! `ground`, `qualified_name`, `kind` — is namespace-level, because a receiver
//! it never reads is dispatch ceremony that also captures the free name
//! (WI-982; proposal 059 R4). Where the resolver answers the same question as a
//! goal, this module must not re-derive it: it calls the resolver's own
//! predicate, so the two phases cannot drift.

use super::builtins::{expect_args, require_symbol, resolve_host_name};
use super::{EvalError, Interpreter, Value};
use crate::intern::Symbol;
use crate::kb::reflect_reader as reader;
use crate::kb::resolve::ResolveConfig;
use crate::kb::term::{Literal, Term as CoreTerm, TermId, Var};
use crate::kb::KnowledgeBase;

/// Symbols the reflect builtins need at runtime, resolved from the KB the call
/// runs against so per-call paths compare `Symbol`s instead of scanning strings.
///
/// PER CALL, not once at registration (WI-20260923-9R5HN): a `HOST_FNS` row is a
/// plain `fn`, with nowhere to hold state resolved after load. The cost is a few
/// dozen name lookups against a walk over the KB's facts, and only the eleven
/// functions that build reflect records pay it.
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
    f_type_params: Symbol,
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
    /// Resolve every reflect symbol. Each one is declared in (or imported by)
    /// `stdlib/anthill/reflect/reflect.anthill`, the file that declares the
    /// operation being called — so a miss is a KB that could not have dispatched the
    /// call, and it is an `EvalError::Internal` naming the symbol, never a skip.
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
            f_type_params: kb.intern("type_params"),
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

// ── KB introspection helpers ────────────────────────────────────
//
// The carrier-agnostic KB walks — `facts_by_sort_name`, `term_named_args`,
// `term_pos_args`, `term_display_name`, `short_of`, `collect_list_terms`,
// `members_of_kind`, and the per-op record readers — live in the shared
// `reader` module (WI-551). The builtins below map a `reader` record to a
// `Value` result; the host bridge maps the SAME record to a typed struct.

// ── Value helpers ──────────────────────────────────────────────

/// The `String` a reflect argument DENOTES, on whatever carrier it rides.
///
/// WI-20260827-3ZNBC — `Value::Str` alone was the wrong question. A reflect name
/// argument reaches these builtins from anthill code, so it arrives on whichever
/// carrier the value was built on: a `Value::Term` for a name read out of a fact, a
/// `Value::Node` for one bound in a rule body (WI-246). Asking
/// [`TermView::literal_string`] is the same question with no carrier list to keep in
/// step — the core-side `eval::builtins::str_operand` is its twin.
fn str_arg(kb: &crate::kb::KnowledgeBase, v: Value) -> Result<String, EvalError> {
    use crate::kb::term_view::TermView;
    v.literal_string(kb).ok_or_else(|| EvalError::TypeMismatch {
        expected: "String",
        got: v.type_name().to_string(),
    })
}

/// The already-resolved functor symbol of a by-reference sort/entity argument
/// (WI-632). A `sort`/`entity` reflect op takes the sort BY REFERENCE — a
/// `Value::Term(Ref)` / `Value::Entity` resolved to its qualified functor at the
/// caller's write site — so extraction is a pure `value_functor` read (the
/// `facts_of` precedent), loud on a non-reference. The interpreter twin of the
/// bridge's `value_functor(&kb, type.value())`.
fn sort_ref_functor(interp: &Interpreter, sort: &Value) -> Result<Symbol, EvalError> {
    crate::eval::value_functor(interp.kb(), sort).ok_or_else(|| EvalError::TypeMismatch {
        expected: "Type (entity/sort reference)",
        got: sort.type_name().to_string(),
    })
}

/// Unwrap `Option.some(value: s)` / `Option.none` → `Option<String>`.
///
/// WI-20260827-3ZNBC — READ THE OPTION THROUGH `TermView` TOO, not just the string
/// inside it. Widening the inner [`str_arg`] and leaving the outer scrutinee matching
/// `Value::Entity` alone stopped one level short: a `some(…)` bound in a rule body
/// arrives as a `Value::Node`, and `KB.sorts` / `KB.descriptions` then failed
/// "expected Option[String], got Node" on the very carrier the inner read had just
/// been taught to accept (found by /code-review). `Value::Entity`, `Value::Term` and
/// `Value::Node` all present `ViewHead::Functor`, so ONE read serves all three: a
/// nullary head is `none()`, a head with one child is `some(x)`.
fn option_string_arg(kb: &crate::kb::KnowledgeBase, v: Value) -> Result<Option<String>, EvalError> {
    use crate::kb::term_view::{TermView, ViewHead};
    match v.head(kb) {
        // `none()` — a nullary constructor, on whichever spelling its carrier uses
        // (one nullary head since WI-20260902-CZJ2N).
        ViewHead::Functor {
            pos_arity: 0,
            named_arity: 0,
            ..
        } => Ok(None),
        // `some(value: s)` — the payload rides positionally OR named, depending on
        // which producer built it, exactly as the callers of this pair elsewhere note.
        ViewHead::Functor { pos_arity, .. } => {
            let inner = if pos_arity > 0 {
                v.pos_arg(kb, 0).map(|c| c.to_value())
            } else {
                v.named_keys(kb)
                    .first()
                    .and_then(|k| v.named_arg(kb, *k))
                    .map(|c| c.to_value())
            };
            match inner {
                Some(inner) => Ok(Some(str_arg(kb, inner)?)),
                None => Err(EvalError::TypeMismatch {
                    expected: "Option[String]",
                    got: v.type_name().to_string(),
                }),
            }
        }
        _ => Err(EvalError::TypeMismatch {
            expected: "Option[String]",
            got: v.type_name().to_string(),
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

pub(super) fn kb_sort_template(
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [_kb, sort] = expect_args::<2>("KB.sort_template", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
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

pub(super) fn kb_sorts(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb, ns] = expect_args::<2>("KB.sorts", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
    let namespace = option_string_arg(interp.kb(), ns)?;
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

pub(super) fn kb_operations(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb, sort] = expect_args::<2>("KB.operations", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
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
        let type_params_v =
            build_list_value(syms, rec.type_params.into_iter().map(Value::term).collect());
        // EVERY DECLARED FIELD, in DECLARATION ORDER. `make_entity` sorts but does not
        // COMPLETE, so a field missing here yields a value with fewer slots than
        // `anthill.reflect.OperationInfo` declares — and both consumers are arity-strict
        // (`eval::pattern::match_constructor_pattern`, `resolve::unify_concrete`'s
        // `na != nb`), so one anthill pattern could not cover both this result and a
        // loader-emitted fact. That is the WI-20260823-GMG6N drift class one layer out:
        // `type_params` was added to the declaration and to the host bridge
        // (`bridge.rs`) and missed here, which no test would have caught.
        let fields = vec![
            (syms.f_name, Value::term(rec.name)),
            (syms.f_params, params_v),
            (syms.f_return_type, Value::term(rec.return_type)),
            (syms.f_effects, effects_v),
            (syms.f_requires, requires_v),
            (syms.f_ensures, ensures_v),
            (syms.f_type_params, type_params_v),
            (syms.f_meta, Value::term(rec.meta)),
        ];
        entries.push(make_entity(kb, syms.operation_info, fields));
    }
    Ok(build_list_value(syms, entries))
}

pub(super) fn kb_constructors(
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [_kb, sort] = expect_args::<2>("KB.constructors", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
    let sort_sym = sort_ref_functor(interp, &sort)?;
    let kb = interp.kb_mut();
    let items: Vec<Value> = reader::members_of_kind(kb, sort_sym, "Constructor")
        .into_iter()
        .map(|n| Value::Str(reader::short_of(&n).to_string()))
        .collect();
    Ok(build_list_value(syms, items))
}

pub(super) fn kb_fields(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb, entity] = expect_args::<2>("KB.fields", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
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

pub(super) fn kb_rules(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb, sort] = expect_args::<2>("KB.rules", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
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

pub(super) fn kb_descriptions(
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [_kb, target] = expect_args::<2>("KB.descriptions", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
    let target = option_string_arg(interp.kb(), target)?;
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

pub(super) fn kb_reify(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb, t] = expect_args::<2>("KB.reify", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
    // LOWERED, not read through the view: `reify_walk` is total over terms and panics on
    // a non-term child, which a `Value::Node` operand can carry below its head.
    let tid = expect_term(interp.kb_mut(), &t, "KB.reify")?;
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
pub(super) fn kb_reflect(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb, repr] = expect_args::<2>("KB.reflect", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
    let tid = reader::reflect_walk(interp.kb_mut(), ValueRepr { value: repr, syms })?;
    Ok(Value::term(tid))
}

/// The constructor of a reflect record (`TermRepr` / `LiteralRepr`), on whatever
/// carrier it rides.
///
/// WI-20260923-9R5HN — read through [`TermView`](crate::kb::term_view::TermView), with
/// [`repr_field`] and `view_list_items` for the rest of the record. The decoder matched
/// `Value::Entity` alone, which is what `KB.reify` builds and NOT what a rule body
/// writes: made interpreter-mapped, `KB.reflect` reduces at a rule-body operand, where
/// `ConstRepr(value: IntLiteral(value: 7))` is a `Value::Node` — MEASURED (/code-review),
/// "expected TermRepr, got Node" on every such call.
fn repr_functor(
    kb: &KnowledgeBase,
    v: &Value,
    expected: &'static str,
) -> Result<Symbol, EvalError> {
    use crate::kb::term_view::{TermView, ViewHead};
    match v.head(kb) {
        ViewHead::Functor {
            functor: Some(f), ..
        } => Ok(f),
        _ => Err(EvalError::TypeMismatch {
            expected,
            got: v.type_name().to_string(),
        }),
    }
}

/// A field of a reflect record: by the field's NAME — compared as a local name, since an
/// occurrence may carry the loader's qualified field symbol where `KB.reify` wrote the
/// bare one — and else at its declared POSITION, for a record written positionally.
fn repr_field(kb: &KnowledgeBase, v: &Value, key: Symbol, index: usize) -> Option<Value> {
    use crate::kb::term_view::TermView;
    let name = kb.local_name_of(key);
    v.named_keys(kb)
        .into_iter()
        .find(|k| kb.local_name_of(*k) == name)
        .and_then(|k| v.named_arg(kb, k))
        .or_else(|| v.pos_arg(kb, index))
        .map(|c| c.to_value())
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
        let functor = repr_functor(kb, &self.value, "TermRepr")?;
        // `TermRepr`'s constructors are one field or `name` + `args`, in that order.
        let lookup = |key: Symbol, index: usize| repr_field(kb, &self.value, key, index);

        if functor == syms.const_repr {
            let inner = lookup(syms.f_value, 0)
                .ok_or_else(|| EvalError::Internal("ConstRepr: missing `value`".into()))?;
            Ok(reader::ReflectShape::Const(decode_literal_repr(
                kb, syms, inner,
            )?))
        } else if functor == syms.var_repr {
            let name = lookup(syms.f_name, 0)
                .ok_or_else(|| EvalError::Internal("VarRepr: missing `name`".into()))?;
            Ok(reader::ReflectShape::Var(str_arg(kb, name)?))
        } else if functor == syms.ref_repr {
            let name = lookup(syms.f_name, 0)
                .ok_or_else(|| EvalError::Internal("RefRepr: missing `name`".into()))?;
            Ok(reader::ReflectShape::Ref(ref_repr_symbol(kb, name)?))
        } else if functor == syms.fn_repr {
            let name = lookup(syms.f_name, 0)
                .ok_or_else(|| EvalError::Internal("FnRepr: missing `name`".into()))?;
            let functor_sym = ref_repr_symbol(kb, name)?;
            let args_list = lookup(syms.f_args, 1)
                .ok_or_else(|| EvalError::Internal("FnRepr: missing `args`".into()))?;
            let children = super::builtins::view_list_items(kb, &args_list)
                .ok_or_else(|| EvalError::TypeMismatch {
                    expected: "FnRepr.args: a cons-list",
                    got: args_list.type_name().to_string(),
                })?
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
    let lit_ctor = repr_functor(kb, &inner, "LiteralRepr")?;
    let lit_val = repr_field(kb, &inner, syms.f_value, 0)
        .ok_or_else(|| EvalError::Internal("LiteralRepr: missing `value`".into()))?;
    // WI-20260827-3ZNBC — the PAYLOAD reads through the carrier-neutral view, like
    // the constructor above it (`Value::Entity`'s functor) already did. Which
    // `LiteralRepr` constructor was written still decides which core `Literal` this
    // is — that is the sort question and is unchanged — but a payload that an anthill
    // rule bound (`int_lit(value: ?n)` over a fact-matched `?n`) rides as a
    // `Value::Term` / `Value::Node`, and matching `Value::Int` refused it while
    // plainly denoting an int. The `IntLiteral -> BigIntLiteral` widening below is a
    // SORT widening and is kept as it was.
    let mismatch = |expected: &'static str| EvalError::TypeMismatch {
        expected,
        got: lit_val.type_name().to_string(),
    };
    let denoted = {
        use crate::kb::term_view::TermView;
        lit_val.as_literal(kb)
    };
    if lit_ctor == syms.int_lit {
        match denoted {
            Some(Literal::Int(n)) => Ok(Literal::Int(n)),
            _ => Err(mismatch("Int64")),
        }
    } else if lit_ctor == syms.bigint_lit {
        match denoted {
            Some(Literal::BigInt(n)) => Ok(Literal::BigInt(n)),
            Some(Literal::Int(n)) => Ok(Literal::BigInt(n.into())),
            _ => Err(mismatch("BigInt")),
        }
    } else if lit_ctor == syms.float_lit {
        match denoted {
            Some(Literal::Float(f)) => Ok(Literal::Float(f)),
            _ => Err(mismatch("Float")),
        }
    } else if lit_ctor == syms.str_lit {
        match denoted {
            Some(Literal::String(s)) => Ok(Literal::String(s)),
            _ => Err(mismatch("String")),
        }
    } else if lit_ctor == syms.bool_lit {
        match denoted {
            Some(Literal::Bool(b)) => Ok(Literal::Bool(b)),
            _ => Err(mismatch("Bool")),
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

pub(super) fn qualified_name(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("qualified_name", args)?;
    let sym = expect_symbol(interp.kb(), s, "qualified_name")?;
    Ok(Value::Str(interp.kb().qualified_name_of(sym).to_string()))
}

pub(super) fn short_name_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
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
pub(super) fn lookup_symbol_op(
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [name] = expect_args::<1>("lookup_symbol", args)?;
    let name_str = str_arg(interp.kb(), name)?;
    let sym = resolve_host_name(interp, "lookup_symbol", &name_str)?;
    Ok(Value::term(interp.kb_mut().alloc(CoreTerm::Ref(sym))))
}

pub(super) fn scope_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
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
    // Option.some / Option.none per call — not a hot path, and `ReflectSyms` would
    // resolve far more than this op reads.
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
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

pub(super) fn kind_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::intern::SymbolKind;
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

/// The `TermId` a `Term`-typed argument DENOTES, on whatever carrier it rides.
///
/// WI-20260923-9R5HN — BY CONTENT, through the one faithful `Value → Term` boundary
/// ([`crate::kb::node_occurrence::value_to_term`]). It matched `Value::Term` alone: a
/// by-CARRIER answer to a by-content question, since `as_term` is the identity and a
/// `Term` is whatever carrier its value rides. That held up while these operations
/// ran only from an operation body, where such an argument is usually interned. Made
/// interpreter-mapped, they reduce at a rule-body operand, and there the argument is
/// a `Value::Node` occurrence — MEASURED, `can_be_sort(as_term(Color))` in a rule
/// refused "expected Term, got Node" on every call. A carrier with no term form (a
/// closure, a stream, a runtime handle) is still a loud type error.
///
/// IT INTERNS, so it is for an operation that needs a `TermId` — one that builds a goal
/// (`kernel.not`), unifies terms (`reflect.unify`), or walks one totally (`KB.reify`).
/// A read that only needs the argument's SHAPE goes through [`TermView`] and leaves a
/// transient operand un-interned (CLAUDE.md: the term store is for persistent,
/// shared structure).
pub(super) fn expect_term(
    kb: &mut KnowledgeBase,
    v: &Value,
    op: &'static str,
) -> Result<TermId, EvalError> {
    crate::kb::node_occurrence::value_to_term(kb, v).map_err(|_| EvalError::TypeMismatch {
        expected: "Term",
        got: format!("{} for {op}", v.type_name()),
    })
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
pub(super) fn nonvar_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [x] = expect_args::<1>("nonvar", args)?;
    Ok(Value::Bool(!interp.kb().value_is_unbound_var(&x)))
}

/// `ground(x: Term) -> Bool` — the eval-time reading of the resolver's
/// `ground(?x)` builtin, answered by [`KnowledgeBase::value_is_ground_no_subst`].
/// See [`nonvar_op`] for why it is two-valued and what the TermId-only
/// derivation it replaces got wrong.
pub(super) fn ground_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [x] = expect_args::<1>("ground", args)?;
    Ok(Value::Bool(interp.kb().value_is_ground_no_subst(&x)))
}

// ── Sort ↔ Term (identity passthroughs — Types ARE Terms) ────────

/// Can the term `v` DENOTES stand in type position? Every term can but a literal and
/// `⊥` — read off its head through [`TermView`], on whatever carrier it rides and
/// without interning it (WI-20260923-9R5HN). The one predicate `can_be_sort` and
/// `term_as_sort` both answer by.
///
/// An OPAQUE head is the one case the view cannot settle: a runtime handle (no term
/// form — a loud type error) and a non-application occurrence (a lambda, say — a term,
/// and so a candidate sort) both read that way, and [`expect_term`] tells them apart.
fn denotes_a_sort_candidate(
    kb: &mut KnowledgeBase,
    v: &Value,
    op: &'static str,
) -> Result<bool, EvalError> {
    use crate::kb::term_view::{TermView, ViewHead};
    if v.index_var(kb).is_some() {
        return Ok(true);
    }
    match v.head(kb) {
        ViewHead::Const(_) | ViewHead::Bottom => Ok(false),
        ViewHead::Opaque | ViewHead::Functor { functor: None, .. } => {
            let tid = expect_term(kb, v, op)?;
            Ok(!matches!(
                kb.get_term(tid),
                CoreTerm::Const(_) | CoreTerm::Bottom
            ))
        }
        ViewHead::Var(_) | ViewHead::Ident(_) | ViewHead::Functor { .. } => Ok(true),
    }
}

/// `sort_as_term(s: Type) -> Term` — Type and Term are both `TermId` in the
/// kernel (see memory `project_sort_data_distinction` / architecture note).
/// The operation exists for documentation and API symmetry: the argument comes back
/// on the carrier it arrived on, once it is known to have a term form.
pub(super) fn sort_as_term(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("sort_as_term", args)?;
    denotes_a_sort_candidate(interp.kb_mut(), &s, "sort_as_term")?;
    Ok(s)
}

/// `can_be_sort(t: Term) -> Bool` — every well-formed `Term` can stand in
/// type position (sorts are terms). Literals and `Bottom` are rejected.
pub(super) fn can_be_sort(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [t] = expect_args::<1>("can_be_sort", args)?;
    Ok(Value::Bool(denotes_a_sort_candidate(
        interp.kb_mut(),
        &t,
        "can_be_sort",
    )?))
}

/// `term_as_sort(t: Term) -> Option[T = Type]` — `some(t)` if `t` can be a
/// sort (the `can_be_sort` predicate), `none` otherwise; `t` on its own carrier.
pub(super) fn term_as_sort(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [t] = expect_args::<1>("term_as_sort", args)?;
    let ok = denotes_a_sort_candidate(interp.kb_mut(), &t, "term_as_sort")?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_field = interp.kb_mut().intern("value");
    if ok {
        Ok(Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_field, t)].into(),
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
pub(super) fn resolve_sort_instantiation_param(
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    use crate::kb::term_view::{TermView, ViewHead};
    let [inst, param] = expect_args::<2>("resolve_sort_instantiation_param", args)?;
    let param_sym = expect_symbol(interp.kb(), param, "resolve_sort_instantiation_param")?;
    let kb = interp.kb();
    // The SortView's named args, read through the view on whatever carrier it rides
    // (WI-20260923-9R5HN) — it read a hash-consed `Term::Fn` only.
    match inst.head(kb) {
        ViewHead::Functor {
            functor: Some(_), ..
        } => inst
            .named_arg(kb, param_sym)
            .map(|c| c.to_value())
            .ok_or_else(|| {
                EvalError::Internal(format!(
                    "resolve_sort_instantiation_param: '{}' not bound",
                    kb.local_name_of(param_sym)
                ))
            }),
        _ => Err(EvalError::TypeMismatch {
            expected: "SortView Term",
            got: inst.type_name().to_string(),
        }),
    }
}

// ── Substitution.apply / .compose ───────────────────────────────

/// The substitution handle a `Substitution` argument carries, READ THROUGH any
/// `Node(Spliced(…))` wrapper ([`Value::carried`], WI-1025).
///
/// WI-20260923-9R5HN — a rule body reaches these operations now, and there a
/// substitution bound by `<=>` arrives σ-walked into the call as a SPLICED
/// occurrence, not as the bare `Value::Substitution` an operation body passes.
/// MEASURED: `mk() <=> some(?s), Substitution.lookup(?s, "x") <=> none()` refused
/// "expected Substitution, got Node". Shared by all four `Substitution` operations,
/// `lookup` included (`builtins::subst_lookup`).
pub(super) fn expect_subst(
    v: &Value,
    op: &'static str,
) -> Result<super::value::SubstHandle, EvalError> {
    match v.carried() {
        Value::Substitution(h) => Ok(h.clone()),
        other => Err(EvalError::TypeMismatch {
            expected: "Substitution",
            got: format!("{} for {op}", other.type_name()),
        }),
    }
}

/// `Substitution.apply(s: Substitution, t: Term, kb: KB) -> Term`.
/// Rewrites `t` by walking every variable binding in `s`. Borrows the
/// substitution through the arena — no clone of `s`.
pub(super) fn subst_apply(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, t, _kb] = expect_args::<3>("Substitution.apply", args)?;
    let handle = expect_subst(&s, "Substitution.apply")?;

    // Read through the HANDLE, which carries the arena that minted it — not
    // `interp`'s, which a bridge interpreter reducing this call did not mint the
    // substitution in (`SubstHandle::with_subst`, WI-20260923-9R5HN). The handle's
    // borrow is also independent of `interp.kb`, so the KB can be borrowed mutably.
    let kb = interp.kb_mut();
    // Carrier-neutral σ-application (WI-20260905-N20EZ): an answer link is a
    // `Value::Var` alias or an `Entity` spine, which the term-world `apply_subst`
    // KEPT — handing back the query var untouched as if σ bound nothing. The op's
    // result is typed `Term`, so the reified value lowers to one here: this is a
    // genuine KB boundary, where interning is the point. A carrier with no term
    // form is a loud error, not a silently kept variable.
    // The TERM is σ-applied on its own carrier (`reify_value`), so a transient operand
    // is not interned; the RESULT is lowered below, at the declared `Term` boundary.
    let applied = handle.with_subst(|s| kb.reify_value(&t, s));
    let lowered = crate::kb::node_occurrence::value_to_term(kb, &applied).map_err(|e| {
        EvalError::Internal(format!(
            "Substitution.apply: the result has no term form: {e:?}"
        ))
    })?;
    Ok(Value::term(lowered))
}

/// `Substitution.compose(s1: Substitution, s2: Substitution, kb: KB) -> Substitution`.
/// Produces a new substitution: s2 applied to every Term-valued binding of
/// s1, extended by s2's bindings where the variable doesn't already appear
/// in s1. Borrows both substitutions through the arena — no full clones.
pub(super) fn subst_compose(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s1, s2, _kb] = expect_args::<3>("Substitution.compose", args)?;
    let h1 = expect_subst(&s1, "Substitution.compose")?;
    let h2 = expect_subst(&s2, "Substitution.compose")?;

    // Each operand read through its own handle — the two may even come from
    // different arenas (`SubstHandle::with_subst`).
    let kb = interp.kb_mut();
    let composed = h1.with_subst(|s1| {
        h2.with_subst(|s2| {
            let mut result = crate::kb::subst::Substitution::new();
            // (WI-569: `bindings` is an `imbl::HashMap` — persistent, no `reserve`.)
            for (var, val) in s1.bindings.iter() {
                // s2 applied on EVERY carrier (N20EZ): a `Term` binding through the
                // carrier-neutral `reify` (the term-world `apply_subst` kept a
                // nested var whose s2-binding is a `Value::Var` alias or an `Entity`
                // link), a bare `Value::Var` chased (WI-547), an `Entity` / `Tuple`
                // link through its children, a `Node` in place — `reify_value` is
                // the one owner of all four, so the former arms collapse onto it.
                let new_val = kb.reify_value(val, s2);
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
pub(super) fn subst_bindings(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [subst_val] = expect_args::<1>("Substitution.bindings", args)?;
    let syms = &ReflectSyms::resolve(interp.kb_mut())?;
    let handle = expect_subst(&subst_val, "Substitution.bindings")?;
    // Through the handle (`SubstHandle::with_subst`).
    let entries: Vec<_> = handle.with_subst(|s| {
        s.iter()
            .map(|(vid, val)| (*vid, val.clone()))
            .collect::<Vec<_>>()
    });
    let kb = interp.kb_mut();
    let mut pairs: Vec<Value> = Vec::with_capacity(entries.len());
    for (vid, val) in entries {
        let var_tid = kb.alloc(CoreTerm::Var(Var::Global(vid)));
        // The pair's `snd` is typed `Term`: lower the binding to one at this
        // boundary (N20EZ — an unbound answer rides `Value::Var`, a compound link an
        // `Entity` spine; both have a term form). A carrier with none is a loud
        // error here rather than a `TypeMismatch` at the first `Term` op downstream.
        let snd = crate::kb::node_occurrence::value_to_term(kb, &val).map_err(|e| {
            EvalError::Internal(format!(
                "Substitution.bindings: a binding has no term form: {e:?}"
            ))
        })?;
        pairs.push(make_entity(
            kb,
            syms.pair,
            vec![
                (syms.f_fst, Value::term(var_tid)),
                (syms.f_snd, Value::term(snd)),
            ],
        ));
    }
    Ok(build_list_value(syms, pairs))
}

// ── kernel.not (WI-080) ────────────────────────────────────────
//
// The one non-`anthill.reflect` function in this file, since WI-20260820-MH90F moved
// `not` to `anthill.kernel` where the rest of the resolver primitives live. Its MAPPING
// sits with its namespace — beside `struct_eq`'s in `rustland/anthill-stl/anthill/
// kernel.anthill`, the other kernel operation with an eval face (WI-20260923-9R5HN) —
// while the function stays here, because what it binds is an eval-time face over a
// reified `Term` and it needs this module's `expect_term` substrate. The resolver
// primitive (`BuiltinTag::Not`, the NAF a rule-body goal runs) is untouched by either.

/// `kernel.not(query: Term) -> Bool` — eval-time negation-as-failure.
/// Wraps `query` in a resolver `not(...)` goal and runs a fresh one-shot
/// SLD search. If the resolver surfaces a residual (floundering: query
/// has unbound variables), raises an error — NAF is unsound on ungrounded
/// goals and the eval context has no outer frame to resume on.
pub(super) fn kernel_not(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [q] = expect_args::<1>("kernel.not", args)?;
    let goal_tid = expect_term(interp.kb_mut(), &q, "kernel.not")?;
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
        // WI-20260911-8Y5BE — a sub-search that could not ASK part of the goal decides
        // nothing either way; refused as loudly as a flounder, with the resolver's words.
        Err(fault) => Err(EvalError::Internal(format!(
            "kernel.not: the search faulted — {}",
            fault.error.message
        ))),
        Ok(None) => Ok(Value::Bool(false)),
        Ok(Some((sol, _rest))) if sol.residual.is_empty() => Ok(Value::Bool(true)),
        Ok(Some(_)) => Err(EvalError::Internal(
            "kernel.not: floundering — query has unbound variables; bind them before calling"
                .into(),
        )),
    }
}

// ── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    use crate::eval::{self, Interpreter, Value};
    use crate::kb::term_view::TermView;

    /// The full closure — the stdlib plus anthill-stl's binding blocks, which is what
    /// NAMES these functions now (WI-20260923-9R5HN) — and `source`, with the standard
    /// builtins registered. `test_support::load_stdlib` is the crate's one fixture for
    /// it; this module carried its own copy while it lived in anthill-stl.
    fn load_stdlib_and_source(source: &str) -> Interpreter {
        let kb = crate::kb::test_support::load_stdlib(Some(source));
        let mut interp = Interpreter::new(kb);
        eval::builtins::register_standard_builtins(&mut interp).expect("register builtins");
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
                let sort_sym = crate::eval::value_functor(interp.kb(), &named[0].1)
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
  import anthill.prelude.List.{cons}
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

    /// WI-20260923-9R5HN — `sorts(kb, some(ns))` keeps the sorts declared in `ns` or
    /// beneath it, at a namespace boundary. The filter compared `ns` against each sort's
    /// SHORT name, so a namespace matched nothing and a short-name prefix matched.
    ///
    /// CONTROL, MEASURED with the old filter restored: the first row fails, `t9r.fx`
    /// answering `[]`; /code-review measured a short-name prefix (`Colo`) answering the
    /// sort through the CLI. The `t9r.fx.Col` row passes either way; it pins the
    /// boundary, as `t9r.fx` not reaching `t9r.fxy` does.
    #[test]
    fn kb_sorts_filters_by_namespace() {
        let mut interp = load_stdlib_and_source(
            "namespace t9r.fx\n  sort Color\n    entity red\n  end\nend\n\
             namespace t9r.fxy\n  sort Shape\n    entity circle\n  end\nend\n",
        );
        let some_sym = interp
            .kb()
            .try_resolve_symbol("anthill.prelude.Option.some")
            .expect("Option.some");
        let value_field = interp.kb_mut().intern("value");
        let mut sorts_in = |ns: &str| -> Vec<String> {
            let arg = Value::Entity {
                functor: some_sym,
                pos: Vec::new().into(),
                named: vec![(value_field, Value::Str(ns.to_string()))].into(),
            };
            let listed = interp
                .call("anthill.reflect.KB.sorts", &[Value::Unit, arg])
                .expect("sorts");
            let mut names: Vec<String> = list_values(&interp, listed)
                .iter()
                .map(|info| {
                    let name = entity_field(&interp, info, "name").expect("SortInfo.name");
                    let sym = interp.kb().value_symbol(&name).expect("a sort reference");
                    interp.kb().qualified_name_of(sym).to_string()
                })
                .collect();
            names.sort();
            names
        };
        assert_eq!(
            sorts_in("t9r.fx"),
            vec!["t9r.fx.Color"],
            "the namespace, not its sibling"
        );
        assert_eq!(
            sorts_in("t9r"),
            vec!["t9r.fx.Color", "t9r.fxy.Shape"],
            "beneath the namespace too"
        );
        assert!(
            sorts_in("t9r.fx.Col").is_empty(),
            "a name prefix is not a namespace"
        );
        assert!(sorts_in("Colo").is_empty(), "nor is a SHORT-name prefix");
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
  import anthill.prelude.List.{cons}
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
                        .and_then(|(_, v)| v.literal_string(interp.kb()))
                        .expect("content field");
                    let index = dn
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "index")
                        .and_then(|(_, v)| v.literal_int64(interp.kb()))
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
        use crate::kb::node_occurrence::{Expr, NodeOccurrence};
        use crate::span::{SourceId, SourceSpan};

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
                    Expr::Const(crate::kb::term::Literal::Int(7)),
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

    // WI-SPGBP's `the_two_builtin_registries_are_disjoint` and WI-759's
    // `field_access_is_not_shadowed_by_this_module` guarded a SECOND registrar
    // (`register_reflect_builtins`) that ran after the standard set, LAST WINS, and so
    // shadowed any qualified name the two shared. WI-20260923-9R5HN folded that registrar
    // into the `operation_map` registrations, so there is one registry and nothing runs
    // second; the hazard's remaining form — two mappings of one operation in one language
    // — is refused at LOAD (`LoadError::HostMappingDuplicate`), driven in
    // `wi_brt4y_host_implemented_test`.

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
  import anthill.prelude.Option.{some}
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
            crate::eval::value_functor(interp.kb(), &scope_answer)
                .map(|f| interp.kb().local_name_of(f).to_string()),
            Some("some".to_string()),
        );
        let inner = match &scope_answer {
            Value::Entity { named, .. } => named[0].1.clone(),
            other => panic!("expected `some(value: …)`, got {other:?}"),
        };
        assert_eq!(
            crate::eval::value_functor(interp.kb(), &inner)
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
        use crate::kb::subst::Substitution;
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
        use crate::kb::subst::Substitution;
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.subst_bindings
  import anthill.prelude.List.{cons}
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
        use crate::kb::subst::Substitution;
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
        let z_binding = handle.with_subst(|s| s.bindings.get(&vid_z).cloned());
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

    /// WI-20260923-9R5HN — A SUBSTITUTION IS READ IN THE ARENA THAT MINTED IT, whichever
    /// interpreter asks. This is the BRIDGE shape: the resolver reduces each rule-body
    /// host call in its own scratch interpreter over the one KB (`run_in_bridge_interp`
    /// takes the KB and builds a fresh interpreter), so a `Substitution` produced by one
    /// call reaches the next in a handle minted by an interpreter that is gone. Driven
    /// here directly: `a` mints `{?x → 7}`, the KB moves to `b`, and `b` — which holds a
    /// DIFFERENT substitution, `{?x → 1}`, in the same slot — runs all four
    /// `Substitution` operations on `a`'s handle.
    ///
    /// CONTROL, MEASURED on the pre-ticket code for `lookup` (the one of the four that was
    /// already interpreter-mapped, reading `interp.subst_arena().with_subst(&h, …)`): it
    /// answered `some(1)` — `b`'s binding, silently — and, with `b`'s arena left empty,
    /// panicked `index out of bounds`. The other three read the same way, from anthill-stl.
    #[test]
    fn a_substitution_is_read_in_the_arena_that_minted_it() {
        use crate::kb::subst::Substitution;
        let mut a = load_stdlib_and_source("namespace test.subst_cross\nend\n");
        let x = {
            let kb = a.kb_mut();
            let name = kb.intern("x");
            kb.fresh_var(name)
        };
        let bound_to = |interp: &mut Interpreter, n: i64| {
            let t = interp.kb_mut().alloc(CoreTerm::Const(Literal::Int(n)));
            let mut s = Substitution::new();
            s.bindings.insert(x, Value::term(t));
            s
        };
        let from_a = bound_to(&mut a, 7);
        let h = a.alloc_subst(from_a);

        let mut b = Interpreter::new(std::mem::take(a.kb_mut()));
        eval::builtins::register_standard_builtins(&mut b).expect("register builtins");
        let decoy = bound_to(&mut b, 1);
        let in_b = b.alloc_subst(decoy);
        assert_eq!(
            in_b.raw(),
            h.raw(),
            "both at slot 0 — the case that aliases"
        );
        drop(a);

        let int_of = |b: &Interpreter, v: &Value| v.literal_int64(b.kb());
        let payload = |b: &Interpreter, v: &Value, field: &str| -> Value {
            let kb = b.kb();
            v.named_keys(kb)
                .into_iter()
                .find(|k| kb.local_name_of(*k) == field)
                .and_then(|k| v.named_arg(kb, k))
                .map(|c| c.to_value())
                .unwrap_or_else(|| panic!("no `{field}` in {v:?}"))
        };

        // lookup — `some(7)`, a's binding.
        let looked = b
            .call(
                "anthill.reflect.Substitution.lookup",
                &[Value::Substitution(h.clone()), Value::Str("x".into())],
            )
            .expect("lookup");
        assert_eq!(
            int_of(&b, &payload(&b, &looked, "value")),
            Some(7),
            "lookup read {looked:?}"
        );

        // apply — `?x` under a's σ is 7.
        let x_term = b.kb_mut().alloc(CoreTerm::Var(Var::Global(x)));
        let applied = b
            .call(
                "anthill.reflect.Substitution.apply",
                &[
                    Value::Substitution(h.clone()),
                    Value::term(x_term),
                    Value::Unit,
                ],
            )
            .expect("apply");
        assert_eq!(int_of(&b, &applied), Some(7), "apply read {applied:?}");

        // bindings — one pair, `snd` = 7.
        let listed = b
            .call(
                "anthill.reflect.Substitution.bindings",
                &[Value::Substitution(h.clone())],
            )
            .expect("bindings");
        let pair = payload(&b, &listed, "head");
        assert_eq!(
            int_of(&b, &payload(&b, &pair, "snd")),
            Some(7),
            "bindings read {listed:?}"
        );

        // compose — `a`'s σ with `b`'s own: `?x` keeps a's 7 (s1 wins where both bind),
        // so each operand was read from its own arena.
        let composed = b
            .call(
                "anthill.reflect.Substitution.compose",
                &[
                    Value::Substitution(h),
                    Value::Substitution(in_b),
                    Value::Unit,
                ],
            )
            .expect("compose");
        let x_after = match &composed {
            Value::Substitution(c) => c.with_subst(|s| s.bindings.get(&x).cloned()),
            other => panic!("compose answered {other:?}"),
        };
        assert_eq!(
            x_after.as_ref().and_then(|v| int_of(&b, v)),
            Some(7),
            "compose read {x_after:?}"
        );
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

        use crate::kb::subst::Substitution;
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
    /// `wi913_host_name_ladder_test::sld_lookup_symbol_reads_the_implicit_tier` and its
    /// `…_does_not_read_the_reflect_sorts` sibling, and that pairing is the point: one
    /// declared operation, two backings, and after WI-984 they may not answer
    /// differently — for what the tier ANSWERS and for what it does not.
    #[test]
    fn lookup_symbol_no_longer_reads_a_bare_prelude_name() {
        let mut interp = load_stdlib_and_source(
            r#"
namespace test.wi913_stl
  sort Color
    entity red
  end
end
"#,
        );
        // WI-909's THIRD PASS took the constructors off the tier too, emptying it, so
        // this half is inverted like the reflect-sort half below. WI-913's finding is
        // untouched -- `lookup_symbol` still reads the LADDER rather than
        // `by_qualified_name` -- and the qualified arm is what keeps that visible: the
        // row would otherwise pass just as well if the operation had stopped resolving
        // anything at all.
        assert!(
            looked_up_name(&mut interp, "cons").is_err(),
            "the implicit tier is empty; a bare `cons` denotes nothing at `<global>`",
        );
        assert_eq!(
            looked_up_name(&mut interp, "anthill.prelude.List.cons")
                .expect("control: the qualified name is the migration and still resolves"),
            "anthill.prelude.List.cons",
        );
        // …AND A REFLECT RESULT SORT DOES NOT (WI-909 took the eight of them off the
        // tier). Inverted rather than deleted, and kept in this row rather than moved,
        // because the WI-984 pairing is the point: `anthill-core`'s
        // `wi913_host_name_ladder_test::sld_lookup_symbol_does_not_read_the_reflect_sorts`
        // asserts the same thing against the SLD backing, and the two may not diverge.
        assert!(
            looked_up_name(&mut interp, "SortInfo").is_err(),
            "`SortInfo` left the implicit tier; a bare reflect sort denotes nothing at \
             `<global>`, exactly as `MemberInfo` always has",
        );
        assert_eq!(
            looked_up_name(&mut interp, "anthill.reflect.SortInfo")
                .expect("the qualified name is the migration"),
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
      @[Refuel, Profile: "cpp20-stl"]
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
