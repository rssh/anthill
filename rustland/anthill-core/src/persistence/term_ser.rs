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
        serde_json::Value::Null => Ok(toml::Value::String("".into())),
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

/// Load a single data entry into a KB term.
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

        let term = value_to_term(kb, value, &mut var_map)?;
        named_args.push((field_sym, term));
    }

    // Sort named_args by Symbol index for hash-consing consistency
    named_args.sort_by_key(|(sym, _)| sym.index());

    Ok(kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args,
    }))
}

/// Convert a JSON value to a KB term.
fn value_to_term(
    kb: &mut KnowledgeBase,
    value: &serde_json::Value,
    var_map: &mut HashMap<String, VarId>,
) -> Result<TermId, SerError> {
    match value {
        serde_json::Value::Null => {
            // null → none()
            let none_sym = resolve_or_intern(kb, "none");
            Ok(kb.alloc(Term::Fn {
                functor: none_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            }))
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
        serde_json::Value::String(s) => string_to_term(kb, s, var_map),
        serde_json::Value::Array(arr) => array_to_list_term(kb, arr, var_map),
        serde_json::Value::Object(map) => object_to_term(kb, map, var_map),
    }
}

/// Convert a string value, handling variable (`?name`) and escape (`\?`) prefixes.
fn string_to_term(
    kb: &mut KnowledgeBase,
    s: &str,
    var_map: &mut HashMap<String, VarId>,
) -> Result<TermId, SerError> {
    if let Some(var_name) = s.strip_prefix('?') {
        // Variable
        if var_name.is_empty() {
            // Anonymous variable `?`
            let anon_sym = kb.intern("_");
            let vid = kb.fresh_var(anon_sym);
            Ok(kb.alloc(Term::Var(Var::Global(vid))))
        } else {
            let vid = var_map
                .entry(var_name.to_string())
                .or_insert_with(|| {
                    let sym = kb.intern(var_name);
                    kb.fresh_var(sym)
                });
            Ok(kb.alloc(Term::Var(Var::Global(*vid))))
        }
    } else if let Some(rest) = s.strip_prefix("\\?") {
        // Escaped: literal string starting with ?
        let literal = format!("?{rest}");
        Ok(kb.alloc(Term::Const(Literal::String(literal))))
    } else {
        // Check if this is a known entity/constructor name (nullary)
        if let Some(sym) = kb.try_resolve_symbol(s) {
            // Check if it's a known entity with no fields (nullary constructor)
            if kb.entity_field_names(sym).map_or(false, |f| f.is_empty()) {
                return Ok(kb.alloc(Term::Fn {
                    functor: sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::new(),
                }));
            }
        }
        // Plain string literal
        Ok(kb.alloc(Term::Const(Literal::String(s.to_string()))))
    }
}


/// Convert a JSON array to a cons/nil list term.
fn array_to_list_term(
    kb: &mut KnowledgeBase,
    arr: &[serde_json::Value],
    var_map: &mut HashMap<String, VarId>,
) -> Result<TermId, SerError> {
    let nil_sym = resolve_or_intern(kb, "nil");
    let cons_sym = resolve_or_intern(kb, "cons");
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");

    let mut result = kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });

    // Build list from back to front
    for item in arr.iter().rev() {
        let head_term = value_to_term(kb, item, var_map)?;
        let mut named = SmallVec::new();
        named.push((head_sym, head_term));
        named.push((tail_sym, result));
        named.sort_by_key(|&(sym, _): &(Symbol, TermId)| sym.index());
        result = kb.alloc(Term::Fn {
            functor: cons_sym,
            pos_args: SmallVec::new(),
            named_args: named,
        });
    }

    Ok(result)
}

/// Convert a JSON object to a term.
///
/// - Single key → constructor: look up key as entity/constructor name
/// - Multiple keys → entity with named fields
fn object_to_term(
    kb: &mut KnowledgeBase,
    map: &serde_json::Map<String, serde_json::Value>,
    var_map: &mut HashMap<String, VarId>,
) -> Result<TermId, SerError> {
    if map.len() == 1 {
        let (key, value) = map.iter().next().unwrap();
        // Try as constructor name
        if let Some(ctor_sym) = kb.try_resolve_symbol(key) {
            return build_constructor_term(kb, ctor_sym, value, var_map);
        }
        // Unknown single-key object: treat as constructor with interned name
        let ctor_sym = kb.intern(key);
        return build_constructor_term(kb, ctor_sym, value, var_map);
    }

    // Multiple keys: not a standard pattern in the envelope format,
    // but handle as an inline record
    Err(SerError::InvalidValue(
        "inline object with multiple keys must be inside a data entry".into(),
    ))
}

/// Build a constructor term from a key-value pair.
fn build_constructor_term(
    kb: &mut KnowledgeBase,
    ctor_sym: Symbol,
    value: &serde_json::Value,
    var_map: &mut HashMap<String, VarId>,
) -> Result<TermId, SerError> {
    match value {
        serde_json::Value::Object(inner) => {
            // Constructor with named fields: { "Verified": { "at": "2027" } }
            let fields = kb.entity_field_names(ctor_sym).map(|f| f.to_vec()).unwrap_or_default();
            let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            for (k, v) in inner {
                let field_sym = find_field_sym(kb, &fields, k);
                let term = value_to_term(kb, v, var_map)?;
                named_args.push((field_sym, term));
            }
            named_args.sort_by_key(|(sym, _)| sym.index());
            Ok(kb.alloc(Term::Fn {
                functor: ctor_sym,
                pos_args: SmallVec::new(),
                named_args,
            }))
        }
        _ => {
            // Single-field shorthand: { "ToolPasses": "cargo-test" }
            let fields = kb.entity_field_names(ctor_sym).map(|f| f.to_vec()).unwrap_or_default();
            let inner_term = value_to_term(kb, value, var_map)?;
            if fields.len() == 1 {
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                named_args.push((fields[0], inner_term));
                Ok(kb.alloc(Term::Fn {
                    functor: ctor_sym,
                    pos_args: SmallVec::new(),
                    named_args,
                }))
            } else {
                // No field schema or zero/multiple fields — use positional
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
