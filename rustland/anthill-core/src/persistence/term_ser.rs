/// Term serialization — TOML/JSON ↔ KB terms.
///
/// Both formats use a `meta` + `data` envelope. The `meta.entity` field names
/// the fully-qualified entity type; `data` contains one or more instances.
///
/// The core conversion is format-agnostic: `serde_json::Value` is the common
/// intermediate. TOML is converted to/from `serde_json::Value` via serde.

use std::collections::HashMap;

use ordered_float::OrderedFloat;
use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::term::{Literal, Term, TermId, Var, VarId};
use crate::kb::{KnowledgeBase, RuleId};

// ── Error type ─────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub enum SerError {
    Format(String),
    MissingMeta(String),
    UnknownEntity(String),
    UnknownField { entity: String, field: String },
    MissingField { entity: String, field: String },
    InvalidValue(String),
}

impl std::fmt::Display for SerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SerError::Format(msg) => write!(f, "format error: {msg}"),
            SerError::MissingMeta(msg) => write!(f, "missing meta: {msg}"),
            SerError::UnknownEntity(name) => write!(f, "unknown entity: {name}"),
            SerError::UnknownField { entity, field } => {
                write!(f, "unknown field '{field}' on entity '{entity}'")
            }
            SerError::MissingField { entity, field } => {
                write!(
                    f,
                    "required field '{field}' absent from persisted entity '{entity}' \
                     (only an Option field may be omitted)"
                )
            }
            SerError::InvalidValue(msg) => write!(f, "invalid value: {msg}"),
        }
    }
}

impl std::error::Error for SerError {}

// ── Public API ─────────────────────────────────────────────────

/// Load entities from a TOML string into the KB.
/// Returns the number of facts loaded.
pub fn load_toml(
    kb: &mut KnowledgeBase,
    source: &str,
    domain: TermId,
) -> Result<usize, Vec<SerError>> {
    let toml_val: toml::Value = toml::from_str(source)
        .map_err(|e| vec![SerError::Format(e.to_string())])?;
    let json_val = toml_to_json(toml_val);
    load_value(kb, json_val, domain)
}

/// Load entities from a JSON string into the KB.
/// Returns the number of facts loaded.
pub fn load_json(
    kb: &mut KnowledgeBase,
    source: &str,
    domain: TermId,
) -> Result<usize, Vec<SerError>> {
    let json_val: serde_json::Value = serde_json::from_str(source)
        .map_err(|e| vec![SerError::Format(e.to_string())])?;
    load_value(kb, json_val, domain)
}

/// Serialize facts of a given entity type to TOML.
pub fn serialize_toml(
    kb: &KnowledgeBase,
    entity_name: &str,
    rule_ids: &[RuleId],
) -> Result<String, SerError> {
    let json_val = facts_to_value(kb, entity_name, rule_ids)?;
    let toml_val = json_to_toml(&json_val)
        .map_err(|e| SerError::Format(format!("TOML conversion: {e}")))?;
    toml::to_string_pretty(&toml_val)
        .map_err(|e| SerError::Format(e.to_string()))
}

/// Serialize facts of a given entity type to JSON.
pub fn serialize_json(
    kb: &KnowledgeBase,
    entity_name: &str,
    rule_ids: &[RuleId],
) -> Result<String, SerError> {
    let json_val = facts_to_value(kb, entity_name, rule_ids)?;
    serde_json::to_string_pretty(&json_val)
        .map_err(|e| SerError::Format(e.to_string()))
}

// ── TOML ↔ JSON conversion ────────────────────────────────────

fn toml_to_json(val: toml::Value) -> serde_json::Value {
    match val {
        toml::Value::String(s) => serde_json::Value::String(s),
        toml::Value::Integer(n) => serde_json::Value::Number(n.into()),
        toml::Value::Float(f) => {
            serde_json::Number::from_f64(f)
                .map(serde_json::Value::Number)
                .unwrap_or(serde_json::Value::Null)
        }
        toml::Value::Boolean(b) => serde_json::Value::Bool(b),
        toml::Value::Datetime(dt) => serde_json::Value::String(dt.to_string()),
        toml::Value::Array(arr) => {
            serde_json::Value::Array(arr.into_iter().map(toml_to_json).collect())
        }
        toml::Value::Table(tbl) => {
            let map = tbl.into_iter().map(|(k, v)| (k, toml_to_json(v))).collect();
            serde_json::Value::Object(map)
        }
    }
}

fn json_to_toml(val: &serde_json::Value) -> Result<toml::Value, String> {
    match val {
        // WI-501: TOML has no null. A `none()` field is dropped before reaching
        // here (an absent field reloads as none), so the only null that arrives
        // is a `none()` sitting INSIDE a list/tuple — which TOML genuinely cannot
        // represent. Erroring loudly beats the old silent `null → ""`, which
        // reloaded as `some(value: "")` and corrupted the round-trip. (Use JSON
        // for stores with none-valued list elements.)
        serde_json::Value::Null => Err(
            "cannot serialize a none()/null inside a list to TOML (TOML has no null); \
             use JSON for this entity"
                .into(),
        ),
        serde_json::Value::Bool(b) => Ok(toml::Value::Boolean(*b)),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                Ok(toml::Value::Integer(i))
            } else if let Some(f) = n.as_f64() {
                Ok(toml::Value::Float(f))
            } else {
                Err(format!("unsupported number: {n}"))
            }
        }
        serde_json::Value::String(s) => Ok(toml::Value::String(s.clone())),
        serde_json::Value::Array(arr) => {
            let items: Result<Vec<_>, _> = arr.iter().map(json_to_toml).collect();
            Ok(toml::Value::Array(items?))
        }
        serde_json::Value::Object(map) => {
            let mut tbl = toml::map::Map::new();
            for (k, v) in map {
                tbl.insert(k.clone(), json_to_toml(v)?);
            }
            Ok(toml::Value::Table(tbl))
        }
    }
}

// ── Core deserializer ──────────────────────────────────────────

/// Core deserializer: serde_json::Value → KB terms.
fn load_value(
    kb: &mut KnowledgeBase,
    value: serde_json::Value,
    domain: TermId,
) -> Result<usize, Vec<SerError>> {
    let obj = match value {
        serde_json::Value::Object(map) => map,
        _ => return Err(vec![SerError::Format("top-level value must be an object".into())]),
    };

    // Check for single-section (meta + data) vs multi-section layout
    if obj.contains_key("meta") && obj.contains_key("data") {
        // Single section
        load_section(kb, &obj, domain)
    } else {
        // Multi-section: each key is a section with .meta + .data
        let mut total = 0;
        let mut errors = Vec::new();
        for (_section_name, section_val) in &obj {
            match section_val {
                serde_json::Value::Object(section_map) => {
                    match load_section(kb, section_map, domain) {
                        Ok(n) => total += n,
                        Err(mut errs) => errors.append(&mut errs),
                    }
                }
                _ => {
                    errors.push(SerError::Format(
                        "each section must be an object with meta + data".into(),
                    ));
                }
            }
        }
        if errors.is_empty() {
            Ok(total)
        } else {
            Err(errors)
        }
    }
}

/// Load a single section: expects "meta" and "data" keys.
fn load_section(
    kb: &mut KnowledgeBase,
    obj: &serde_json::Map<String, serde_json::Value>,
    domain: TermId,
) -> Result<usize, Vec<SerError>> {
    let meta = obj.get("meta").ok_or_else(|| {
        vec![SerError::MissingMeta("section has no 'meta' key".into())]
    })?;

    let entity_name = meta
        .get("entity")
        .and_then(|v| v.as_str())
        .ok_or_else(|| vec![SerError::MissingMeta("meta.entity must be a string".into())])?;

    // Resolve entity functor in KB
    let functor = resolve_entity_functor(kb, entity_name)
        .ok_or_else(|| vec![SerError::UnknownEntity(entity_name.into())])?;

    // Get field schema
    let fields = kb
        .entity_field_names(functor)
        .map(|f| f.to_vec())
        .unwrap_or_default();

    let data = obj.get("data").ok_or_else(|| {
        vec![SerError::MissingMeta("section has no 'data' key".into())]
    })?;

    // Determine the sort for this entity
    let sort = entity_sort(kb, functor);

    let entries: Vec<&serde_json::Value> = match data {
        serde_json::Value::Array(arr) => arr.iter().collect(),
        serde_json::Value::Object(_) => vec![data],
        _ => {
            return Err(vec![SerError::Format(
                "data must be an array or object".into(),
            )])
        }
    };

    let mut count = 0;
    let mut errors = Vec::new();

    for entry in entries {
        match load_entry(kb, entry, functor, &fields, entity_name) {
            Ok(term) => {
                kb.assert_fact(term, sort, domain, None);
                count += 1;
            }
            Err(e) => errors.push(e),
        }
    }

    if errors.is_empty() {
        Ok(count)
    } else {
        Err(errors)
    }
}

/// Resolve an entity name to its functor Symbol.
fn resolve_entity_functor(kb: &mut KnowledgeBase, name: &str) -> Option<Symbol> {
    // Try qualified name first
    if let Some(sym) = kb.try_resolve_symbol(name) {
        return Some(sym);
    }
    // Try short name
    let short = name.rsplit('.').next().unwrap_or(name);
    if let Some(sym) = kb.try_resolve_symbol(short) {
        return Some(sym);
    }
    None
}

/// Get the sort term for an entity functor (its parent sort, or "Fact" fallback).
fn entity_sort(kb: &mut KnowledgeBase, functor: Symbol) -> TermId {
    let functor_term = kb.make_name_term_from_sym(functor);
    if let Some(parent) = kb.entity_parent_sort(functor_term) {
        parent
    } else {
        kb.make_name_term("Fact")
    }
}

/// Load a single data entry into a KB term, reconstructing each field
/// type-directedly (WI-501). The serializer is lossy without types — it strips
/// `some(value: x)` to `x`, DROPS `none()` entirely (the field becomes absent),
/// renders nullary entities (`Open`, enum variants) as bare strings, and flattens
/// lists — so reload MUST consult each field's DECLARED type to rebuild the
/// `Option` wrapper, the entity `Ref`, the cons-list, or the literal, or the
/// reloaded term silently fails to hash-cons- / discrim-match the source-loaded
/// form (the named-arg ORDER fix, WI-498, is necessary but not sufficient — the
/// VALUES must reconstruct too). An absent declared Option field is `none()`; an
/// absent required field is store corruption — a loud error.
fn load_entry(
    kb: &mut KnowledgeBase,
    entry: &serde_json::Value,
    functor: Symbol,
    fields: &[Symbol],
    entity_name: &str,
) -> Result<TermId, SerError> {
    let obj = entry.as_object().ok_or_else(|| {
        SerError::InvalidValue("data entry must be an object".into())
    })?;

    let field_types = entity_field_type_map(kb, functor);
    let mut var_map: HashMap<String, VarId> = HashMap::new();
    let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();

    for (key, value) in obj {
        let field_sym = find_field_sym(kb, fields, key);

        if !fields.is_empty() && !fields.contains(&field_sym) {
            return Err(SerError::UnknownField {
                entity: entity_name.into(),
                field: key.clone(),
            });
        }

        let ty = field_type_of(&field_types, field_sym);
        let term = value_to_term_typed(kb, value, ty, &mut var_map)?;
        named_args.push((field_sym, term));
    }

    backfill_absent_fields(kb, fields, &field_types, &mut named_args, entity_name)?;

    // WI-498: canonicalize named args to DECLARED field order via the WI-299
    // funnel (not `Symbol::index()` interning order). The loader canonicalizes
    // source-loaded facts to declared order and the discrim matcher descends
    // named keys positionally, so a fact reloaded from a persisted store must
    // use the same order or it silently fails to hash-cons- / discrim-match the
    // same fact loaded from .anthill source.
    Ok(kb.make_entity_term(functor, SmallVec::new(), named_args))
}

/// An entity's declared field types as `(field, ground-type-term)` pairs,
/// dropping any non-ground (`Value::Node`, dependent) field type. Empty when the
/// functor has no registered schema (a schema-less functor keeps the untyped
/// reconstruction path, preserving prior behavior).
fn entity_field_type_map(kb: &KnowledgeBase, functor: Symbol) -> Vec<(Symbol, TermId)> {
    kb.entity_field_types(functor)
        .map(|fts| {
            fts.iter()
                .filter_map(|(s, v)| match v {
                    crate::eval::value::Value::Term(t) => Some((*s, *t)),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default()
}

fn field_type_of(field_types: &[(Symbol, TermId)], field: Symbol) -> Option<TermId> {
    field_types.iter().find(|(s, _)| *s == field).map(|(_, t)| *t)
}

/// Backfill declared fields that are ABSENT from the persisted data: an Option
/// field is restored to `none()` (the value the serializer dropped); any other
/// (required) field is store corruption — a loud error, not a silent partial.
/// No-op for a schema-less functor (`fields` empty).
fn backfill_absent_fields(
    kb: &mut KnowledgeBase,
    fields: &[Symbol],
    field_types: &[(Symbol, TermId)],
    named_args: &mut SmallVec<[(Symbol, TermId); 2]>,
    entity_name: &str,
) -> Result<(), SerError> {
    if fields.is_empty() {
        return Ok(());
    }
    let option_sym = kb.try_resolve_symbol("anthill.prelude.Option");
    let absent: Vec<Symbol> = fields
        .iter()
        .copied()
        .filter(|f| !named_args.iter().any(|(s, _)| s == f))
        .collect();
    for field in absent {
        let is_option = field_type_of(field_types, field).is_some_and(|t| {
            let (head, _) = type_head_and_inner(kb, t);
            head.is_some() && head == option_sym
        });
        if is_option {
            let none = option_none_ref(kb);
            named_args.push((field, none));
        } else {
            return Err(SerError::MissingField {
                entity: entity_name.into(),
                field: kb.resolve_sym(field).to_string(),
            });
        }
    }
    Ok(())
}

/// Convert a JSON value to a KB term, reconstructing it to match the source-
/// loaded form using the declared type `ty` (WI-501). An `Option[T = U]` field
/// stores `some(value: x)` as the bare `x` and `none()` as JSON null / an absent
/// field, so a present value is re-wrapped in `some(...)` (recursing on `U`) and
/// a null is `none()`. Lists, entity variants, and literals are reconstructed by
/// [`value_to_term_typed`]'s kind dispatch below. With `ty = None` this is the
/// prior untyped behavior, except nullary entities now rebuild as `Ref` (the
/// loader's form) rather than `Fn` so they hash-cons-match.
fn value_to_term_typed(
    kb: &mut KnowledgeBase,
    value: &serde_json::Value,
    ty: Option<TermId>,
    var_map: &mut HashMap<String, VarId>,
) -> Result<TermId, SerError> {
    if let Some(t) = ty {
        let (head, inner) = type_head_and_inner(kb, t);
        if head.is_some() && head == kb.try_resolve_symbol("anthill.prelude.Option") {
            if value.is_null() {
                return Ok(option_none_ref(kb));
            }
            let inner_term = value_to_term_typed(kb, value, inner, var_map)?;
            return Ok(some_wrap(kb, inner_term));
        }
    }
    match value {
        // A null is `none()` only for an Option field (handled by the peel above)
        // or when the type is unknown (schema-less, can't tell). A null under a
        // KNOWN non-Option type is store corruption — loud error, not a silent
        // wrong-typed none() (loud-error principle).
        serde_json::Value::Null => {
            if ty.is_some() {
                Err(SerError::InvalidValue(
                    "null value for a non-Option field".into(),
                ))
            } else {
                Ok(option_none_ref(kb))
            }
        }
        serde_json::Value::Bool(b) => Ok(kb.alloc(Term::Const(Literal::Bool(*b)))),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                Ok(kb.alloc(Term::Const(Literal::Int(i))))
            } else if let Some(f) = n.as_f64() {
                Ok(kb.alloc(Term::Const(Literal::Float(OrderedFloat(f)))))
            } else {
                Err(SerError::InvalidValue(format!("unsupported number: {n}")))
            }
        }
        serde_json::Value::String(s) => string_to_term_typed(kb, s, ty, var_map),
        serde_json::Value::Array(arr) => {
            // Thread the element type for a `List[T = U]` field so list elements
            // (entity variants, options, nested lists) reconstruct correctly.
            let elem_ty = ty.and_then(|t| {
                let (head, inner) = type_head_and_inner(kb, t);
                if head.is_some() && head == kb.try_resolve_symbol("anthill.prelude.List") {
                    inner
                } else {
                    None
                }
            });
            let mut items = Vec::with_capacity(arr.len());
            for it in arr {
                items.push(value_to_term_typed(kb, it, elem_ty, var_map)?);
            }
            Ok(build_cons_list(kb, &items))
        }
        serde_json::Value::Object(map) => object_to_term_typed(kb, map, ty, var_map),
    }
}

/// Build a cons/nil list, preferring the canonical `anthill.prelude.List.cons/nil`
/// symbols (matching the source loader so the list hash-cons-matches) but falling
/// back to bare interned `cons`/`nil` when the prelude `List` is not loaded — so a
/// schema-less deserialize never panics (unlike [`KnowledgeBase::build_list`],
/// which resolves-or-panics).
fn build_cons_list(kb: &mut KnowledgeBase, items: &[TermId]) -> TermId {
    let nil_sym = match kb.try_resolve_symbol("anthill.prelude.List.nil") {
        Some(s) => s,
        None => resolve_or_intern(kb, "nil"),
    };
    let cons_sym = match kb.try_resolve_symbol("anthill.prelude.List.cons") {
        Some(s) => s,
        None => resolve_or_intern(kb, "cons"),
    };
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");
    let mut list = kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    for &item in items.iter().rev() {
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named.push((head_sym, item));
        named.push((tail_sym, list));
        list = kb.make_entity_term(cons_sym, SmallVec::new(), named);
    }
    list
}

/// Convert a string value, handling `?name` variables, `\?` escapes, and (WI-501)
/// type-directed nullary entity / enum-variant references: a string whose declared
/// sort has a variant named `s` is that variant as a `Ref` (the loader's form),
/// not a string literal.
fn string_to_term_typed(
    kb: &mut KnowledgeBase,
    s: &str,
    ty: Option<TermId>,
    var_map: &mut HashMap<String, VarId>,
) -> Result<TermId, SerError> {
    if let Some(var_name) = s.strip_prefix('?') {
        if var_name.is_empty() {
            // Anonymous variable `?`
            let anon_sym = kb.intern("_");
            let vid = kb.fresh_var(anon_sym);
            return Ok(kb.alloc(Term::Var(Var::Global(vid))));
        }
        let vid = *var_map.entry(var_name.to_string()).or_insert_with(|| {
            let sym = kb.intern(var_name);
            kb.fresh_var(sym)
        });
        return Ok(kb.alloc(Term::Var(Var::Global(vid))));
    }
    if let Some(rest) = s.strip_prefix("\\?") {
        // Escaped: literal string starting with ?
        return Ok(kb.alloc(Term::Const(Literal::String(format!("?{rest}")))));
    }
    // Type-directed: a string under a declared entity/enum sort is a nullary
    // variant of that sort, resolved within the sort's namespace → `Ref(variant)`.
    // When the declared type IS known, it is authoritative: if the string is not
    // a variant of that sort it is a plain literal (a `String`-typed field whose
    // value happens to equal a qualified entity name stays a literal — we do NOT
    // fall through to the global entity heuristic below, which would mis-type it).
    if let Some(t) = ty {
        if let (Some(sort), _) = type_head_and_inner(kb, t) {
            let qualified = format!("{}.{}", kb.qualified_name_of(sort), s);
            if let Some(vsym) = kb.try_resolve_symbol(&qualified) {
                return Ok(kb.alloc(Term::Ref(vsym)));
            }
        }
        return Ok(kb.alloc(Term::Const(Literal::String(s.to_string()))));
    }
    // No declared type (schema-less): a globally-known nullary entity is a `Ref`
    // (matching the loader); otherwise a plain string literal.
    if let Some(sym) = kb.try_resolve_symbol(s) {
        if kb.entity_field_names(sym).map_or(false, |f| f.is_empty()) {
            return Ok(kb.alloc(Term::Ref(sym)));
        }
    }
    Ok(kb.alloc(Term::Const(Literal::String(s.to_string()))))
}

/// Head sort symbol + first type-argument of a ground type term: for
/// `Option[T = U]` / `List[T = U]` returns `(Option/List, Some(U))`; for a bare
/// `Ref(S)` returns `(S, None)`.
fn type_head_and_inner(kb: &KnowledgeBase, ty: TermId) -> (Option<Symbol>, Option<TermId>) {
    match kb.get_term(ty) {
        Term::Fn { functor, named_args, .. } => {
            (Some(*functor), named_args.first().map(|(_, v)| *v))
        }
        Term::Ref(sym) => (Some(*sym), None),
        _ => (None, None),
    }
}

/// `anthill.prelude.Option.none` as a `Ref` — the SAME form the source loader
/// emits for a written `none`, so a backfilled / null-derived none hash-cons-
/// matches the source.
fn option_none_ref(kb: &mut KnowledgeBase) -> TermId {
    let none_sym = match kb.try_resolve_symbol("anthill.prelude.Option.none") {
        Some(s) => s,
        None => resolve_or_intern(kb, "none"),
    };
    kb.alloc(Term::Ref(none_sym))
}

/// Wrap `inner` as `anthill.prelude.Option.some(value: inner)` — the SAME form
/// the loader emits, so a re-wrapped Option value hash-cons-matches the source.
fn some_wrap(kb: &mut KnowledgeBase, inner: TermId) -> TermId {
    let some_sym = match kb.try_resolve_symbol("anthill.prelude.Option.some") {
        Some(s) => s,
        None => resolve_or_intern(kb, "some"),
    };
    let value_sym = kb.intern("value");
    let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    named.push((value_sym, inner));
    kb.make_entity_term(some_sym, SmallVec::new(), named)
}


/// Convert a single-key JSON object `{ Variant: payload }` to a constructor /
/// enum-variant term (WI-501, type-directed). The variant name is resolved
/// within the declared sort `ty`'s namespace first (so `{ Verified: … }` under a
/// `WorkStatus` field becomes `anthill.stage0.WorkStatus.Verified`), then
/// globally, then interned.
fn object_to_term_typed(
    kb: &mut KnowledgeBase,
    map: &serde_json::Map<String, serde_json::Value>,
    ty: Option<TermId>,
    var_map: &mut HashMap<String, VarId>,
) -> Result<TermId, SerError> {
    if map.len() == 1 {
        let (key, value) = map.iter().next().unwrap();
        let ctor_sym = resolve_variant_sym(kb, key, ty);
        return build_constructor_term_typed(kb, ctor_sym, value, var_map);
    }

    // Multiple keys: not a standard pattern in the envelope format.
    Err(SerError::InvalidValue(
        "inline object with multiple keys must be inside a data entry".into(),
    ))
}

/// Resolve a constructor/variant name: within the declared sort `ty`'s namespace
/// first, then as a global name, finally interning it.
fn resolve_variant_sym(kb: &mut KnowledgeBase, key: &str, ty: Option<TermId>) -> Symbol {
    if let Some(t) = ty {
        if let (Some(sort), _) = type_head_and_inner(kb, t) {
            let qualified = format!("{}.{}", kb.qualified_name_of(sort), key);
            if let Some(vsym) = kb.try_resolve_symbol(&qualified) {
                return vsym;
            }
        }
    }
    match kb.try_resolve_symbol(key) {
        Some(s) => s,
        None => kb.intern(key),
    }
}

/// Build a constructor term, reconstructing each field type-directedly from the
/// constructor's own declared field types (WI-501) and backfilling its absent
/// Option fields. The single-field shorthand (`{ ToolPasses: "cargo-test" }`)
/// fills the lone declared field; with no schema it falls back to positional.
fn build_constructor_term_typed(
    kb: &mut KnowledgeBase,
    ctor_sym: Symbol,
    value: &serde_json::Value,
    var_map: &mut HashMap<String, VarId>,
) -> Result<TermId, SerError> {
    let fields = kb.entity_field_names(ctor_sym).map(|f| f.to_vec()).unwrap_or_default();
    let field_types = entity_field_type_map(kb, ctor_sym);
    match value {
        serde_json::Value::Object(inner) => {
            // Constructor with named fields: { "Verified": { "at": "2027" } }
            let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            for (k, v) in inner {
                let field_sym = find_field_sym(kb, &fields, k);
                let fty = field_type_of(&field_types, field_sym);
                let term = value_to_term_typed(kb, v, fty, var_map)?;
                named_args.push((field_sym, term));
            }
            let ctor_name = kb.resolve_sym(ctor_sym).to_string();
            backfill_absent_fields(kb, &fields, &field_types, &mut named_args, &ctor_name)?;
            // WI-498: canonicalize named-constructor / enum-variant args to
            // declared field order via the funnel (not interning order).
            Ok(kb.make_entity_term(ctor_sym, SmallVec::new(), named_args))
        }
        _ => {
            // Single-field shorthand: { "ToolPasses": "cargo-test" }
            if fields.len() == 1 {
                let fty = field_type_of(&field_types, fields[0]);
                let inner_term = value_to_term_typed(kb, value, fty, var_map)?;
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                named_args.push((fields[0], inner_term));
                Ok(kb.make_entity_term(ctor_sym, SmallVec::new(), named_args))
            } else {
                // No field schema or zero/multiple fields — use positional.
                let inner_term = value_to_term_typed(kb, value, None, var_map)?;
                Ok(kb.alloc(Term::Fn {
                    functor: ctor_sym,
                    pos_args: SmallVec::from_elem(inner_term, 1),
                    named_args: SmallVec::new(),
                }))
            }
        }
    }
}

/// Find a field Symbol by name, falling back to intern if not in the schema.
fn find_field_sym(kb: &mut KnowledgeBase, fields: &[Symbol], key: &str) -> Symbol {
    fields.iter()
        .find(|&&f| kb.resolve_sym(f) == key)
        .copied()
        .unwrap_or_else(|| kb.intern(key))
}

/// Resolve a name in KB, falling back to intern.
fn resolve_or_intern(kb: &mut KnowledgeBase, name: &str) -> Symbol {
    kb.try_resolve_symbol(name).unwrap_or_else(|| kb.intern(name))
}

// ── Core serializer ────────────────────────────────────────────

/// Core serializer: KB facts → serde_json::Value.
fn facts_to_value(
    kb: &KnowledgeBase,
    entity_name: &str,
    rule_ids: &[RuleId],
) -> Result<serde_json::Value, SerError> {
    let mut data = Vec::new();

    for &rid in rule_ids {
        let head = kb.rule_head(rid);
        let val = term_to_value(kb, head)?;
        // Extract named fields from the term — skip the functor wrapper
        match val {
            serde_json::Value::Object(map) if map.len() == 1 => {
                // The term serialized as { "EntityName": { fields } }
                // Unwrap to just the fields
                let (_, inner) = map.into_iter().next().unwrap();
                data.push(inner);
            }
            _ => data.push(val),
        }
    }

    let mut result = serde_json::Map::new();
    let mut meta = serde_json::Map::new();
    meta.insert("entity".into(), serde_json::Value::String(entity_name.into()));
    result.insert("meta".into(), serde_json::Value::Object(meta));

    if data.len() == 1 {
        result.insert("data".into(), data.into_iter().next().unwrap());
    } else {
        result.insert("data".into(), serde_json::Value::Array(data));
    }

    Ok(serde_json::Value::Object(result))
}

/// Convert a KB term to a JSON value.
fn term_to_value(kb: &KnowledgeBase, term: TermId) -> Result<serde_json::Value, SerError> {
    match kb.get_term(term) {
        Term::Const(lit) => literal_to_json(lit),
        Term::Var(Var::Global(vid)) => {
            let name = kb.resolve_sym(vid.name());
            if name == "_" {
                Ok(serde_json::Value::String("?".into()))
            } else {
                Ok(serde_json::Value::String(format!("?{name}")))
            }
        }
        Term::Var(Var::DeBruijn(n)) => {
            Ok(serde_json::Value::String(format!("?#{n}")))
        }
        Term::Var(Var::Rigid(vid)) => {
            Ok(serde_json::Value::String(format!("!{}", kb.resolve_sym(vid.name()))))
        }
        Term::Fn { functor, pos_args, named_args } => {
            let functor = *functor;
            let pos_args = pos_args.clone();
            let named_args = named_args.clone();
            let name = kb.resolve_sym(functor);

            // Check for list cons/nil
            if name == "nil" && pos_args.is_empty() && named_args.is_empty() {
                return Ok(serde_json::Value::Array(vec![]));
            }
            if name == "cons" {
                return cons_to_json_array(kb, term);
            }

            // Check for Option some/none
            if name == "some" {
                if let Some((_, val_id)) = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "value") {
                    return term_to_value(kb, *val_id);
                }
                if pos_args.len() == 1 {
                    return term_to_value(kb, pos_args[0]);
                }
            }
            if name == "none" && pos_args.is_empty() && named_args.is_empty() {
                return Ok(serde_json::Value::Null);
            }

            // Nullary functor → string (e.g. "Open")
            if pos_args.is_empty() && named_args.is_empty() {
                return Ok(serde_json::Value::String(name.to_string()));
            }

            // Entity with named fields only
            if pos_args.is_empty() && !named_args.is_empty() {
                let mut fields = serde_json::Map::new();
                for &(sym, val_id) in &named_args {
                    let field_name = kb.resolve_sym(sym).to_string();
                    let val = term_to_value(kb, val_id)?;
                    // Skip none() values (Option absent)
                    if val != serde_json::Value::Null {
                        fields.insert(field_name, val);
                    }
                }

                // Check if this functor is a constructor (entity with parent sort)
                if kb.is_constructor_symbol(functor) {
                    // Single-field shorthand
                    if named_args.len() == 1 {
                        let val = term_to_value(kb, named_args[0].1)?;
                        let mut wrapper = serde_json::Map::new();
                        wrapper.insert(name.to_string(), val);
                        return Ok(serde_json::Value::Object(wrapper));
                    }
                    // Multi-field constructor
                    let mut wrapper = serde_json::Map::new();
                    wrapper.insert(name.to_string(), serde_json::Value::Object(fields));
                    return Ok(serde_json::Value::Object(wrapper));
                }

                // Top-level entity: just return the fields
                return Ok(serde_json::Value::Object(fields));
            }

            // Positional args only
            if !pos_args.is_empty() && named_args.is_empty() {
                if pos_args.len() == 1 {
                    let val = term_to_value(kb, pos_args[0])?;
                    let mut wrapper = serde_json::Map::new();
                    wrapper.insert(name.to_string(), val);
                    return Ok(serde_json::Value::Object(wrapper));
                }
                let arr: Result<Vec<_>, _> = pos_args.iter().map(|&id| term_to_value(kb, id)).collect();
                let mut wrapper = serde_json::Map::new();
                wrapper.insert(name.to_string(), serde_json::Value::Array(arr?));
                return Ok(serde_json::Value::Object(wrapper));
            }

            // Mixed positional + named — serialize as object with all args
            let mut all_fields = serde_json::Map::new();
            for (i, &pos_id) in pos_args.iter().enumerate() {
                let val = term_to_value(kb, pos_id)?;
                all_fields.insert(format!("_{i}"), val);
            }
            for &(sym, val_id) in &named_args {
                let field_name = kb.resolve_sym(sym).to_string();
                let val = term_to_value(kb, val_id)?;
                all_fields.insert(field_name, val);
            }
            let mut wrapper = serde_json::Map::new();
            wrapper.insert(name.to_string(), serde_json::Value::Object(all_fields));
            Ok(serde_json::Value::Object(wrapper))
        }
        Term::Ref(sym) => {
            // WI-501: a written `none` loads as `Ref(anthill.prelude.Option.none)`
            // (a nullary entity is a `Ref`, not a `Fn`). Render it to JSON null so
            // the entity-field loop DROPS it — an absent field means `none` and is
            // restored by the type-directed deserializer's backfill (see
            // `value_to_term_typed`). Any other nullary entity (`Open`, an enum
            // variant) stays its short-name string and is rebuilt type-directedly.
            if kb.qualified_name_of(*sym) == "anthill.prelude.Option.none" {
                return Ok(serde_json::Value::Null);
            }
            let name = kb.resolve_sym(*sym);
            Ok(serde_json::Value::String(name.to_string()))
        }
        Term::Ident(sym) => {
            let name = kb.resolve_sym(*sym);
            Ok(serde_json::Value::String(name.to_string()))
        }
        Term::Bottom => Ok(serde_json::Value::Null),
        Term::ParseAux(_) => Err(SerError::InvalidValue(
            "parse-only Term::ParseAux variant reached term_to_value (should never happen post-load)".into(),
        )),
    }
}

/// Flatten a cons-list to a JSON array.
fn cons_to_json_array(
    kb: &KnowledgeBase,
    mut term: TermId,
) -> Result<serde_json::Value, SerError> {
    let mut items = Vec::new();
    loop {
        // Extract head/tail TermIds from the cons cell without holding the borrow
        let cell = match kb.get_term(term) {
            Term::Fn { functor, named_args, .. } => {
                let name = kb.resolve_sym(*functor);
                if name == "nil" {
                    break;
                }
                if name == "cons" {
                    let head = named_args.iter()
                        .find(|(s, _)| kb.resolve_sym(*s) == "head")
                        .map(|(_, id)| *id);
                    let tail = named_args.iter()
                        .find(|(s, _)| kb.resolve_sym(*s) == "tail")
                        .map(|(_, id)| *id);
                    Some((head, tail))
                } else {
                    None
                }
            }
            // WI-511: the canonical nullary `nil` terminator is `Ref(nil)`.
            Term::Ref(s) if kb.resolve_sym(*s) == "nil" => break,
            _ => None,
        };
        match cell {
            Some((head, tail)) => {
                if let Some(h) = head {
                    items.push(term_to_value(kb, h)?);
                }
                if let Some(t) = tail {
                    term = t;
                } else {
                    break;
                }
            }
            None => {
                items.push(term_to_value(kb, term)?);
                break;
            }
        }
    }
    Ok(serde_json::Value::Array(items))
}

/// Convert a Literal to JSON.
fn literal_to_json(lit: &Literal) -> Result<serde_json::Value, SerError> {
    match lit {
        Literal::String(s) => Ok(serde_json::Value::String(s.clone())),
        Literal::Int(n) => Ok(serde_json::Value::Number((*n).into())),
        Literal::BigInt(n) => {
            if let Ok(i) = i64::try_from(n) {
                Ok(serde_json::Value::Number(i.into()))
            } else {
                Ok(serde_json::Value::String(n.to_string()))
            }
        }
        Literal::Float(f) => {
            serde_json::Number::from_f64(f.into_inner())
                .map(serde_json::Value::Number)
                .ok_or_else(|| SerError::InvalidValue(format!("non-finite float: {f}")))
        }
        Literal::Bool(b) => Ok(serde_json::Value::Bool(*b)),
        Literal::Handle(kind, id) => Ok(serde_json::Value::String(format!("<handle:{:?}:{}>", kind, id))),
    }
}
