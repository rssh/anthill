//! Term serialization — one value at a declared type ↔ JSON, and the TOML/JSON data files
//! built on it (proposal 021).
//!
//! THE UNIT IS THE VALUE. [`decode_value`] reads one JSON value as a term of a declared type
//! and [`encode_value`] writes one value, on any carrier, at its declared type. The type is a
//! term too, on any carrier, and is required: the mapping is directed by it at every step,
//! in both directions. [`CodecOptions`] chooses among the spellings the proposal admits.
//!
//! A data file — the `meta` + `data` envelope — is one use of the pair: each `data` entry is
//! the object of the fields of the constructor `meta.entity` names, decoded with variables
//! on and asserted as a fact ([`load_json`], [`load_toml`]); [`serialize_json`] and
//! [`serialize_toml`] write facts back the same way. TOML is converted to and from
//! `serde_json::Value`, so it follows the same mapping.
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use ordered_float::OrderedFloat;
use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::{is_positional_label_at, Contested, ResolveResult, Symbol};
use crate::kb::load::{lower_type_text, LoadError};
use crate::kb::term::{Literal, Term, TermId, Var, VarId};
use crate::kb::term_view::{TermView, ViewHead};
use crate::kb::typing::{extract_type, type_display_name_value, type_qualified_text, TypeExtractor};
use crate::kb::{ClauseKind, KnowledgeBase, RuleId};
use crate::parse::desugar_target as dt;
use crate::parse::ir::Item;
use crate::persistence::print::TermPrinter;

// The prelude sorts and constructors the mapping gives a spelling of its own. Detected by
// QUALIFIED name (WI-503), so a user entity merely named `some` / `cons` in another
// namespace is mapped as the entity it is.
const OPTION: &str = "anthill.prelude.Option";
const OPTION_SOME: &str = "anthill.prelude.Option.some";
const OPTION_NONE: &str = "anthill.prelude.Option.none";
const LIST: &str = "anthill.prelude.List";
const LIST_CONS: &str = "anthill.prelude.List.cons";
const LIST_NIL: &str = "anthill.prelude.List.nil";
// A set's and a map's values in a term are the chains of their operations a fact writes
// (`insert(insert(empty, 2), 1)`, `put(empty, "a", 1)`); a running map is a host handle.
const SET: &str = "anthill.prelude.Set";
const SET_INSERT: &str = "anthill.prelude.Set.insert";
const SET_EMPTY: &str = "anthill.prelude.Set.empty";
const MAP: &str = "anthill.prelude.Map";
const MAP_PUT: &str = "anthill.prelude.Map.put";
const MAP_EMPTY: &str = "anthill.prelude.Map.empty";
// A value at a sort with abstract values, as an operation body builds it (proposal 073 §2).
const INSTANCE: &str = "anthill.realization.runtime.Instance";

// ── Options ────────────────────────────────────────────────────

/// How the mapping spells what it has two spellings for (proposal 021, "API"). Each default
/// is the mapping as the proposal states it. The JSON does not record the options it was
/// written with, so a value is read with the options it was written with: where an option
/// chooses between two spellings the reader takes the chosen one and refuses the other,
/// except [`BigIntSpelling`], whose reader takes both.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CodecOptions {
    /// `false`: a string is the string it spells. `true`: `"?name"` is a variable, `"?"` an
    /// anonymous one, and a leading `\` escapes a literal `?` string.
    pub variables: bool,
    pub entity_tags: EntityTags,
    pub tag_names: TagNames,
    pub big_int: BigIntSpelling,
    pub wider_tuple: WiderTuple,
    pub spec_values: SpecValues,
    pub collection_order: CollectionOrder,
}

impl CodecOptions {
    /// The options a data file is read and written with: the defaults, with variables on, a
    /// wider tuple refused, a value at a sort with abstract values read as its provider's value
    /// alone, and a set or a map written as it was built, so a data file has one format and a
    /// fact is written whole and reads back as the source fact (a projected tuple, a value
    /// paired with its dictionary, or a set's chain in another order would reload as another
    /// fact).
    pub fn data_file() -> Self {
        CodecOptions {
            variables: true,
            wider_tuple: WiderTuple::Refuse,
            spec_values: SpecValues::Plain,
            collection_order: CollectionOrder::AsBuilt,
            ..CodecOptions::default()
        }
    }
}

/// How a set's elements and a map's entries are written and read. A set or a map is one value
/// with many chains (`insert(insert(empty, 2), 1)` and `insert(insert(empty, 1), 2)` are one set,
/// and two terms).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum CollectionOrder {
    /// One text per value: the elements, or the entries by their keys, in [`json_order`], each
    /// once (a later `put` of a key shadowing an earlier one); the reader refuses an element or
    /// a key written twice.
    #[default]
    Canonical,
    /// One text per chain: the elements, or the entries, in the order the chain was built,
    /// an element inserted twice or a key put twice written each time; the reader builds that
    /// chain again, so the term reads back as itself.
    AsBuilt,
}

/// What a value read at a sort with abstract values (a spec whose values are its providers'
/// values, proposal 073 §2: `Sp`, with `Car` and `Van` providing it) is built as. The writer
/// takes both, and writes them alike.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SpecValues {
    /// `Instance(dict, value)`: the provider's value paired with the dictionary of its
    /// provision, as an operation body builds a value it uses at the abstract sort and as a
    /// call at one takes it. The dictionary is built where the value is read.
    #[default]
    Instances,
    /// The provider's value alone, as a source fact holds it.
    Plain,
}

/// Whether a constructed value always carries its constructor's tag.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum EntityTags {
    /// Every constructed value is `"Tag"` or `{"Tag": …}`, whatever its declared type.
    #[default]
    Always,
    /// A value whose declared type's ONE constructor is the type itself (a free-standing
    /// entity, an eponymous sort with no other constructor, a constructor's own type) is the
    /// object of its fields, at any depth. Every other constructed value is tagged still.
    OmitAtEntityType,
}

/// How a tag names its constructor.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TagNames {
    /// The constructor's short name, looked up among the declared type's constructors.
    #[default]
    Short,
    /// Its qualified name, which reads without the schema at hand.
    Qualified,
}

/// How a `BigInt` is written. The reader takes both spellings.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BigIntSpelling {
    /// A number in the `i64` range, its decimal digits past it.
    #[default]
    NumberWhenItFits,
    /// Always its digits, for a reader that loses integers past 2^53.
    AlwaysDigits,
}

/// What the writer does with a tuple value wider than its declared type (kernel §4.5).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum WiderTuple {
    /// Write the components the type names and no others.
    #[default]
    Project,
    /// Refuse it ([`ValueProblem::WiderThanDeclared`]).
    Refuse,
}

// ── Errors ─────────────────────────────────────────────────────

/// Where in a JSON value a problem is: a sequence of keys and indices from the value's root.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct JsonPath(Vec<PathStep>);

/// One step of a [`JsonPath`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathStep {
    Key(String),
    Index(usize),
}

impl JsonPath {
    pub fn steps(&self) -> &[PathStep] {
        &self.0
    }

    /// The path written from `root` — `$` for a value, `data[2]` for a file's row.
    fn write_from(&self, root: &str, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(root)?;
        for step in &self.0 {
            match step {
                PathStep::Index(i) => write!(f, "[{i}]")?,
                PathStep::Key(k) if is_identifier(k) => write!(f, ".{k}")?,
                PathStep::Key(k) => write!(f, "[{}]", serde_json::Value::String(k.clone()))?,
            }
        }
        Ok(())
    }
}

impl std::fmt::Display for JsonPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.write_from("$", f)
    }
}

fn is_identifier(k: &str) -> bool {
    let mut chars = k.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// What was wrong with one value, at the place a [`ValueError`] names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueProblem {
    /// The JSON value, or the value being written, is not of a shape the type takes.
    WrongShape { found: String },
    /// A number under `Int64` or `BigInt` written with a fraction or an exponent.
    NotAnInteger { found: String },
    /// A number past the range of `Int64`, or an unquoted one past `u64` under `BigInt`.
    OutOfRange { found: String },
    /// A key that names no field of the constructor, or no label of the tuple.
    UnknownField { name: String },
    /// A required field or a tuple component is absent.
    MissingField { name: String },
    /// A tag, or a value's constructor, that is no constructor of the declared type.
    UnknownConstructor { name: String, sort: String },
    /// A tag that names several constructors the declared type admits — at a sort with abstract
    /// values, constructors of two of its providers that share a short name. `constructors` are
    /// their qualified names, which [`TagNames::Qualified`] writes.
    AmbiguousTag { tag: String, constructors: Vec<String> },
    /// With [`CollectionOrder::Canonical`], an element of a set written a second time: `first` is
    /// the index it was first written at.
    RepeatedElement { first: usize },
    /// With [`CollectionOrder::Canonical`], a key of a map written a second time: `first` is the
    /// index of its first entry.
    RepeatedKey { first: usize },
    /// A map's entry that is not the array of two, its key and its value.
    NotAnEntry { found: String },
    /// A value read at a sort with abstract values for which no dictionary can be built: its
    /// provider provides the sort at no application the declared type admits, or its provision
    /// asks for one nothing answers.
    NoInstance { reason: String },
    /// An object where a constructed value is expected that is not the object of one key, its
    /// constructor's tag (`tags` are the ones the declared type admits).
    NotTagged { found: String, tags: Vec<String> },
    /// A shorthand payload for a constructor without exactly one field, or a bare tag for one
    /// with fields.
    NotOneField { constructor: String, fields: usize },
    /// A constructor reserved to the runtime ([`crate::kb::RuntimeAccount`]), at any depth.
    RuntimeAccount { constructor: String },
    /// The declared type has no data spelling: a function type, a sort with no constructors
    /// that is neither one the mapping spells (`Set`, `Map`, …) nor a sort with abstract values
    /// some sort with constructors provides (`Cell`, a spec no data sort provides).
    NoDataSpelling,
    /// With [`WiderTuple::Refuse`], a tuple value with components its type does not name.
    WiderThanDeclared { labels: Vec<String> },
    /// A type still holds a parameter after substitution and defaults.
    UnboundParameter { name: String },
    /// A variable where none has a spelling: any with variables off, a rigid or de Bruijn
    /// one, one standing for a whole `Option`.
    Variable,
    /// A value with no spelling: `some(none())`, a list with a variable tail, a non-finite
    /// float.
    Unrepresentable { what: String },
    /// A name in a type's text that is absent at `<global>`.
    UnknownName { name: String },
    /// A name in a type's text that is ambiguous at `<global>`.
    AmbiguousName { name: String, candidates: Vec<String> },
    /// A name in a type's text that is `internal` to where it is declared.
    InternalName { name: String, declared_in: String },
    /// A type's text that is not the text of one type.
    NotAType { text: String, reason: String },
}

impl std::fmt::Display for ValueProblem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueProblem::WrongShape { found } => write!(f, "found {found}"),
            ValueProblem::NotAnInteger { found } => {
                write!(f, "found {found}, which is not written as an integer")
            }
            ValueProblem::OutOfRange { found } => write!(f, "found {found}, which is out of range"),
            ValueProblem::UnknownField { name } => write!(f, "`{name}` names no field"),
            ValueProblem::MissingField { name } => write!(
                f,
                "required field `{name}` is absent (only an Option field may be omitted)"
            ),
            ValueProblem::UnknownConstructor { name, sort } => {
                write!(f, "'{name}' is not a constructor of sort '{sort}'")
            }
            ValueProblem::AmbiguousTag { tag, constructors } => write!(
                f,
                "'{tag}' names {} constructors ({}), so a value tagged so has no one reading; \
                 tag them by their qualified names (TagNames::Qualified)",
                constructors.len(),
                constructors.join(", ")
            ),
            ValueProblem::RepeatedElement { first } => write!(
                f,
                "found the element written at index {first} again; a set holds an element once"
            ),
            ValueProblem::RepeatedKey { first } => write!(
                f,
                "found the key of the entry at index {first} again; a map holds a key once"
            ),
            ValueProblem::NotAnEntry { found } => {
                write!(f, "found {found}, where a map's entry is the array [key, value]")
            }
            ValueProblem::NoInstance { reason } => write!(f, "the value has no instance: {reason}"),
            ValueProblem::NotTagged { found, tags } => write!(
                f,
                "found {found}, where a constructed value is its constructor's tag ({})",
                tags.join(", ")
            ),
            ValueProblem::NotOneField {
                constructor,
                fields: 0,
            } => write!(f, "`{constructor}` declares no fields, so it is written as its tag alone"),
            ValueProblem::NotOneField {
                constructor,
                fields: 1,
            } => write!(
                f,
                "`{constructor}` declares one field, so its payload is the object of its fields \
                 or its one field's value"
            ),
            ValueProblem::NotOneField {
                constructor,
                fields,
            } => write!(
                f,
                "`{constructor}` declares {fields} fields, so its payload is the object of its fields"
            ),
            ValueProblem::RuntimeAccount { constructor } => write!(
                f,
                "`{constructor}` is {}; a value read from outside does not hold one",
                crate::kb::RuntimeAccount::NOT_CONSTRUCTED
            ),
            ValueProblem::NoDataSpelling => write!(f, "the type has no data spelling"),
            ValueProblem::WiderThanDeclared { labels } => write!(
                f,
                "the tuple has components the type does not name: {}",
                labels.join(", ")
            ),
            ValueProblem::UnboundParameter { name } => write!(
                f,
                "type parameter `{name}` is bound neither by the type nor by a default"
            ),
            ValueProblem::Variable => write!(f, "found a variable, which has no spelling here"),
            ValueProblem::Unrepresentable { what } => write!(f, "{what} has no spelling"),
            ValueProblem::UnknownName { name } => write!(f, "`{name}` names nothing at <global>"),
            ValueProblem::AmbiguousName { name, candidates } => write!(
                f,
                "`{name}` is ambiguous at <global>: {}",
                candidates.join(", ")
            ),
            ValueProblem::InternalName { name, declared_in } => {
                write!(f, "`{name}` is internal to `{declared_in}`")
            }
            ValueProblem::NotAType { text, reason } => write!(f, "`{text}` is not one type: {reason}"),
        }
    }
}

/// A value the pair could not read or write: where, what type was expected there, and what
/// went wrong. Renders `{path}: expected {expected}, {problem}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueError {
    /// Where, e.g. `$.order.Order.lines[1]`.
    pub path: JsonPath,
    /// The type declared there, printed as the KB prints a type.
    pub expected: String,
    pub problem: ValueProblem,
}

impl ValueError {
    fn write_from(&self, root: &str, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.path.write_from(root, f)?;
        write!(f, ": expected {}, {}", self.expected, self.problem)
    }
}

impl std::fmt::Display for ValueError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.write_from("$", f)
    }
}

impl std::error::Error for ValueError {}

/// An error of the file readers and writers: of the envelope, or of one row ([`Self::Row`]).
#[derive(Debug, Clone)]
pub enum SerError {
    Format(String),
    /// `meta.entity` names a constructor of one of the runtime's accounts.
    RuntimeAccount(String),
    MissingMeta(String),
    UnknownEntity(String),
    /// WI-912: `meta.entity` resolved to SEVERAL symbols at `<global>` — the ladder's
    /// ambiguity stop (WI-907). Qualify the name in the data file.
    AmbiguousName {
        name: String,
        candidates: Vec<String>,
        /// What `candidates` are readings of — only the HEAD of a dotted `name` when that
        /// is the contested segment (WI-918).
        contested: Contested,
    },
    /// WI-912: `meta.entity` names a symbol that EXISTS but is `internal` to
    /// `declared_in`, so a data file — outside code — may not name it.
    ForbiddenInternalEntity {
        entity: String,
        declared_in: String,
    },
    /// WI-926: `meta.entity` resolved to a symbol that declares no fields. The
    /// name is not an entity — typically a multi-constructor sort, which has no
    /// single row shape to deserialize against.
    NoFieldSchema {
        entity: String,
        constructors: Vec<String>,
    },
    /// The type arguments `meta.entity` applies its constructor to could not be read, or the
    /// type they make is not the constructor's.
    EntityType {
        entity: String,
        error: ValueError,
    },
    /// A row of a section is not a value of the constructor's fields: the `data` entry at
    /// `index`, or the one `data` object (`None`); for a writer, the fact at that position of
    /// the facts written.
    Row {
        index: Option<usize>,
        error: ValueError,
    },
}

impl std::fmt::Display for SerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SerError::Format(msg) => write!(f, "format error: {msg}"),
            SerError::RuntimeAccount(ctor) => write!(
                f,
                "`{ctor}` is {}; a data file does not hold one",
                crate::kb::RuntimeAccount::NOT_CONSTRUCTED
            ),
            SerError::MissingMeta(msg) => write!(f, "missing meta: {msg}"),
            SerError::UnknownEntity(name) => write!(f, "unknown entity: {name}"),
            SerError::AmbiguousName {
                name,
                candidates,
                contested,
            } => write!(
                f,
                "ambiguous name '{name}': {} {candidates:?}; qualify it in the data file",
                contested.candidates_label()
            ),
            SerError::ForbiddenInternalEntity {
                entity,
                declared_in,
            } => write!(
                f,
                "entity '{entity}' is internal to '{declared_in}' and cannot be named by a data file"
            ),
            SerError::NoFieldSchema {
                entity,
                constructors,
            } => {
                write!(
                    f,
                    "'{entity}' declares no fields, so a persisted row has no \
                           schema to reconstruct against"
                )?;
                if !constructors.is_empty() {
                    write!(
                        f,
                        " (it is a sort with constructors {}; name one of them \
                               in meta.entity)",
                        constructors.join(", ")
                    )?;
                }
                Ok(())
            }
            SerError::EntityType { entity, error } => {
                write!(f, "meta.entity '{entity}': ")?;
                error.write_from("meta.entity", f)
            }
            SerError::Row { index: Some(index), error } => error.write_from(&format!("data[{index}]"), f),
            SerError::Row { index: None, error } => error.write_from("data", f),
        }
    }
}

impl std::error::Error for SerError {}

// ── The pair ───────────────────────────────────────────────────

/// Read `json` as ONE value of type `ty` (on any carrier) and return its term, hash-consed
/// into `kb`'s store. Nothing is asserted: the KB's facts and rules are as they were. With
/// `opts.variables` on, the value's variables are fresh, and their scope is this one call.
/// To pass the result to an operation, wrap it as `Value::term(id)`. A set and a map are read
/// as the chains of their operations a fact writes (`insert(insert(empty, 2), 1)`, `put(empty,
/// "a", 1)`); a running `Map` operation takes a host handle, and refuses the chain.
pub fn decode_value(
    kb: &mut KnowledgeBase,
    json: &serde_json::Value,
    ty: &impl TermView,
    opts: CodecOptions,
) -> Result<TermId, ValueError> {
    let ty = DeclaredType::closed(ty);
    Decoder::new(kb, opts).value(json, &ty)
}

/// Write `value` at type `ty`, each on any carrier: a `TermId`, a `Value` an operation
/// returned, an occurrence. One term encodes to the same bytes on every carrier, and a map to
/// the same bytes as its `put` chain or its running handle, which carries its own arena. Reads
/// `kb` and changes nothing. A value that is not data — a closure, a stream, a cell — is
/// refused, as is a type with no data spelling.
pub fn encode_value(
    kb: &KnowledgeBase,
    value: &impl TermView,
    ty: &impl TermView,
    opts: CodecOptions,
) -> Result<serde_json::Value, ValueError> {
    let ty = DeclaredType::closed(ty);
    let value = owned(value);
    Encoder::new(kb, opts, &value).value(&value, &ty)
}

/// Read a type from its text — how a value at `Type` is spelled, and `meta.entity`. Names
/// are resolved at `<global>`, and one that is absent, ambiguous or `internal` is refused.
/// The type is lowered as a declaration's type is, so it is the term the same type is in a
/// declaration: an entity's type is its constructor's face, an unwritten parameter takes its
/// default. A type holding a variable is refused.
pub fn type_from_text(kb: &mut KnowledgeBase, text: &str) -> Result<TermId, ValueError> {
    let refuse = |problem| ValueError {
        path: JsonPath::default(),
        expected: "Type".to_owned(),
        problem,
    };
    let not_a_type = |reason: String| {
        refuse(ValueProblem::NotAType {
            text: text.to_owned(),
            reason,
        })
    };
    // One `const` with no value, whose declared type is the text: the grammar's type rule, and
    // no other item. A text that closes the declaration and writes another (`Int64 const x:
    // …`) parses to two items, and one that gives it a value (`Int64 = 3`) has one.
    let source = format!("const __anthill_type_text: {text}\n");
    let parsed = crate::parse::parse(&source).map_err(|errs| {
        not_a_type(errs.iter().map(|e| e.message.as_str()).collect::<Vec<_>>().join("; "))
    })?;
    // A top-level `import` is kept apart from the items, and is refused as well.
    let ty = match parsed.items.as_slice() {
        [Item::Const(c)] if c.value.is_none() && parsed.imports.is_empty() => &c.ty,
        _ => return Err(not_a_type("the text holds more than a type".to_owned())),
    };
    let value = lower_type_text(kb, &parsed, ty).map_err(|errs| {
        let first = errs.into_iter().next().expect("a refused lowering reports an error");
        refuse(type_text_problem(text, first))
    })?;
    if holds_variable(kb, &value) {
        return Err(refuse(ValueProblem::Variable));
    }
    kb.alloc_from_value(&value)
        .map_err(|e| not_a_type(format!("it has no term: {e:?}")))
}

/// Write a type as its text: every name qualified, an application's bindings in the order of
/// their keys' names, so one type has one text in every load. The text [`type_from_text`]
/// reads back as the same type. A type holding a variable, or a value that is not a type, is
/// refused.
pub fn type_to_text(kb: &KnowledgeBase, ty: &impl TermView) -> Result<String, ValueError> {
    type_text(kb, &owned(ty)).map_err(|problem| ValueError {
        path: JsonPath::default(),
        expected: "Type".to_owned(),
        problem,
    })
}

/// [`type_to_text`] without a location: the encoder places the problem.
fn type_text(kb: &KnowledgeBase, ty: &Value) -> Result<String, ValueProblem> {
    if holds_variable(kb, ty) {
        return Err(ValueProblem::Variable);
    }
    if !is_type_term(kb, ty) {
        return Err(ValueProblem::WrongShape {
            found: describe_value(kb, ty),
        });
    }
    Ok(type_qualified_text(kb, &crate::kb::term_view::ViewItem::Value(ty)))
}

/// The value's problem for the first refusal of a type's lowering: a name's, named as the
/// name ladder names it; any other, as the loader renders it.
fn type_text_problem(text: &str, e: LoadError) -> ValueProblem {
    match e {
        // The location is in the one-line source the text was wrapped in, not the caller's.
        LoadError::Located { inner, .. } => type_text_problem(text, *inner),
        LoadError::UnresolvedName { name, .. } | LoadError::UnresolvedTypeName { name, .. } => {
            ValueProblem::UnknownName { name }
        }
        LoadError::AmbiguousSymbol {
            name, candidates, ..
        } => ValueProblem::AmbiguousName { name, candidates },
        LoadError::ForbiddenInternalAccess {
            name, declared_in, ..
        } => ValueProblem::InternalName { name, declared_in },
        other => ValueProblem::NotAType {
            text: text.to_owned(),
            reason: other.to_string(),
        },
    }
}

/// Any carrier as an owned `Value`, so the walks read one carrier type and descend by
/// [`crate::kb::term_view::ViewItem::to_value`].
fn owned(v: &impl TermView) -> Value {
    match v.as_bind_value() {
        crate::kb::persist_subst::BindValue::Term(t) => Value::term(t),
        crate::kb::persist_subst::BindValue::Value(v) => v,
        crate::kb::persist_subst::BindValue::Path(_) => {
            unreachable!("a view's own value is never a path into a fact")
        }
    }
}

/// Does `v` hold a variable anywhere?
fn holds_variable(kb: &KnowledgeBase, v: &impl TermView) -> bool {
    match v.head(kb) {
        ViewHead::Var(_) => true,
        ViewHead::Functor { pos_arity, .. } => {
            (0..pos_arity).any(|i| v.pos_arg(kb, i).is_some_and(|a| holds_variable(kb, &a)))
                || v.named_keys(kb)
                    .into_iter()
                    .any(|k| v.named_arg(kb, k).is_some_and(|a| holds_variable(kb, &a)))
        }
        ViewHead::Const(_) | ViewHead::Ident(_) | ViewHead::Bottom | ViewHead::Opaque => false,
    }
}

/// How often each flex variable occurs in `v`.
fn count_variables(kb: &KnowledgeBase, v: &impl TermView, counts: &mut HashMap<VarId, usize>) {
    match v.head(kb) {
        ViewHead::Var(Var::Global(vid)) => *counts.entry(vid).or_default() += 1,
        ViewHead::Functor { pos_arity, .. } => {
            for i in 0..pos_arity {
                if let Some(a) = v.pos_arg(kb, i) {
                    count_variables(kb, &a, counts);
                }
            }
            for k in v.named_keys(kb) {
                if let Some(a) = v.named_arg(kb, k) {
                    count_variables(kb, &a, counts);
                }
            }
        }
        _ => {}
    }
}

/// Is `v` a type, as a value at `Type` must be — and not an instance, or a value? A name is a
/// type when it is a face, or has a type reading and no face beside it (`Int64`): a
/// constructor's instance and its type share a name, and the type is the FACE
/// (WI-20260902-JB6RS). The reader's rule ([`type_from_text`] refuses what this refuses),
/// so a `Type` value the writer writes reads back.
fn is_type_term(kb: &KnowledgeBase, v: &Value) -> bool {
    let names_a_type =
        |s: Symbol| s.is_type_face() || (kb.has_type_reading(s) && kb.type_face_of(s) == s);
    match extract_type(kb, v) {
        TypeExtractor::SortRef(s) => names_a_type(s),
        TypeExtractor::Parameterized { base, .. } => {
            // A parameterized type's head is its functor, which may be a constructor's face.
            match v.head(kb) {
                ViewHead::Functor { functor, .. } => names_a_type(functor),
                _ => names_a_type(base),
            }
        }
        TypeExtractor::NamedTuple(_)
        | TypeExtractor::Arrow { .. }
        | TypeExtractor::PolyType { .. }
        | TypeExtractor::EffectsRows(_)
        | TypeExtractor::Nothing => true,
        _ => false,
    }
}

// ── The declared type, as the walks read it ───────────────────

/// A declared type as a walk over values at it reads it: a type term on whatever carrier it
/// rides, and what the type parameters it may name are bound to. A constructor's field is
/// typed in its sort's parameters; at a value of `Box[T = Int64]` the field `items: List[T =
/// T]` is read with `T` bound to `Int64`. The binding is itself a type with the bindings of the
/// place it was written in, so a parameter is substituted at any depth without building a
/// type term (the encoder has a `&` KB).
///
/// THE ONE READING (WI-20261125-CMQJ4). The codec reads every type it walks through
/// [`DeclaredType::shape`] and every constructor's fields through [`DataShape::fields`], and
/// so does any caller that walks a value at its declared type as the codec does — a value
/// generator, a differ. A field's type read from `entity_field_types` is written in its sort's
/// parameters (`value: T`); rebuilt outside, the substitution is a second copy of the rule —
/// a default, a positional binding or a binding naming an outer parameter read one way there
/// and another here — and nothing keeps the two alike.
#[derive(Clone, Debug)]
pub struct DeclaredType {
    view: Value,
    env: Env,
}

/// The bindings of the parameters a type may name: each parameter's canonical variable (its
/// `VarId`'s raw id) and what it stands for.
#[derive(Clone, Debug, Default)]
struct Env(Rc<Vec<(u32, Binding)>>);

#[derive(Clone, Debug)]
enum Binding {
    To(DeclaredType),
    /// A parameter the type leaves unwritten and that declares no default, kept by its name: its
    /// canonical variable is anonymous (`?_`), and a message names the parameter.
    Open(Symbol),
}

impl Env {
    fn lookup(&self, id: u32) -> Option<&Binding> {
        self.0.iter().find(|(v, _)| *v == id).map(|(_, b)| b)
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl DeclaredType {
    /// A type that names no parameter of a place, on any carrier: what a caller hands the
    /// pair, and where a walk starts.
    pub fn closed(ty: &impl TermView) -> DeclaredType {
        DeclaredType {
            view: owned(ty),
            env: Env::default(),
        }
    }

    fn within(&self, view: Value) -> DeclaredType {
        DeclaredType {
            view,
            env: self.env.clone(),
        }
    }

    /// What the type is, once a parameter it names is looked up in its place's bindings:
    /// `T` at `Cell`'s `value` within `Cell[T = Int64]` is `Int64`. A parameter nothing binds —
    /// left unwritten with no default, or free in a type handed in — is refused by its name
    /// (`UnboundParameter`); a type with no data spelling (a function type, `Cell`) is
    /// `NoDataSpelling`. A sort with abstract values (proposal 073 §2) is the [`DataShape`] of
    /// its providers' constructors ([`DataShape::provider`]).
    pub fn shape(&self, kb: &KnowledgeBase) -> Result<TypeShape, ValueProblem> {
        let (ty, extracted) = resolve(kb, self)?;
        let (head, bindings) = match extracted {
            TypeExtractor::SortRef(s) => (s, Vec::new()),
            TypeExtractor::Parameterized { base, bindings } => (base, bindings),
            TypeExtractor::NamedTuple(fields) => {
                return Ok(TypeShape::Tuple(
                    fields.into_iter().map(|(l, t)| (l, ty.within(t))).collect(),
                ))
            }
            _ => return Err(ValueProblem::NoDataSpelling),
        };
        let sort = head.plain();
        // A prelude sort's parameter, by its name or its position in the sort's declaration.
        let arg = |name: &str, index: usize| {
            bindings
                .iter()
                .find(|(k, _)| {
                    let label = kb.local_name_of(*k);
                    label == name || is_positional_label_at(label, index)
                })
                .map(|(_, v)| ty.within(v.clone()))
                .ok_or_else(|| ValueProblem::UnboundParameter {
                    name: name.to_owned(),
                })
        };
        if !head.is_type_face() {
            match kb.qualified_name_of(sort) {
                "anthill.prelude.String" => return Ok(TypeShape::String),
                "anthill.prelude.Int64" => return Ok(TypeShape::Int64),
                "anthill.prelude.Float" => return Ok(TypeShape::Float),
                "anthill.prelude.BigInt" => return Ok(TypeShape::BigInt),
                "anthill.prelude.Bool" => return Ok(TypeShape::Bool),
                "anthill.prelude.Type" => return Ok(TypeShape::Type),
                OPTION => return Ok(TypeShape::Option(arg("T", 0)?)),
                LIST => return Ok(TypeShape::List(arg("T", 0)?)),
                SET => return Ok(TypeShape::Set(arg("T", 0)?)),
                MAP => {
                    return Ok(TypeShape::Map {
                        key: arg("K", 0)?,
                        value: arg("V", 1)?,
                    })
                }
                _ => {}
            }
        }
        let ctors = kb.field_constructors_of_sort(sort);
        if !ctors.is_empty() {
            let own = ctors.len() == 1 && ctors[0] == sort;
            let env = sort_env(kb, sort, &ty, &bindings);
            return Ok(TypeShape::Data(DataShape {
                sort,
                ctors,
                own,
                homes: Homes::Sort(env),
            }));
        }
        // A sort with abstract values: a value of it is a value of one of its providers, each
        // constructor's fields typed in its provider's own parameters. The type applying the
        // abstract sort binds the abstract sort's parameters, not the provider's, so these are
        // at their defaults, and one with none is refused where a field names it.
        if crate::kb::typing::is_abstract_carrier_sort(kb, sort) {
            // The abstract sort's own bindings, each by its parameter's name: a provider that
            // provides it at another application (`Bike provides Sk[T = String]`, at `Sk[T =
            // Int64]`) has no value here, and a writer walking the shape writes none.
            let params = kb.type_param_syms_of(sort);
            let written: Vec<(String, Value)> = bindings
                .iter()
                .filter_map(|(k, v)| {
                    let label = kb.local_name_of(*k);
                    let name = crate::intern::positional_label_index(label)
                        .and_then(|i| params.get(i))
                        .map_or(label, |p| kb.local_name_of(*p));
                    // A binding that does not close (it names an open parameter, or a form
                    // the substitution does not go through) is left out, and so admits every
                    // provider, as a binding that is not ground does (`provider_admitted_at`).
                    // A value READ at the place is refused where its dictionary is built
                    // (`Decoder::paired`), by the same `closed_type`.
                    ty.within(v.clone()).closed_type(kb).ok().map(|t| (name.to_owned(), t))
                })
                .collect();
            let mut ctors = Vec::new();
            let mut providers = Vec::new();
            for provider in crate::kb::typing::data_providers_of_abstract_sort(kb, sort)
                .into_iter()
                .filter(|p| crate::kb::typing::provider_admitted_at(kb, *p, sort, &written))
            {
                let env = sort_env(kb, provider, &ty, &[]);
                for ctor in kb.field_constructors_of_sort(provider) {
                    ctors.push(ctor);
                    providers.push((provider, env.clone()));
                }
            }
            if !ctors.is_empty() {
                return Ok(TypeShape::Data(DataShape {
                    sort,
                    ctors,
                    own: false,
                    homes: Homes::Providers(providers),
                }));
            }
        }
        Err(ValueProblem::NoDataSpelling)
    }

    /// The type the declared type stands for, as a type the KB holds: every parameter its
    /// place binds substituted, at any depth (`Cell[T = Bool]` for `Holder`'s `c: Cell[T =
    /// A]` at `Holder[A = Bool]`, `(a: Bool, n: Int64)` for its `t: (a: A, n: Int64)`).
    ///
    /// THE COMPARISON (WI-20261126-SRY02). A caller that must compare a field's type at an
    /// application with a type it holds compares this with it by
    /// [`crate::kb::term_view::views_structurally_equal`], as the KB compares types
    /// everywhere else — not the [`TypeShape`]s, which would be a second definition of type
    /// equality, nor the [`DeclaredType::display_name`]s. It is also the place a value read
    /// at a sort with abstract values is used at, which its dictionary is built for.
    ///
    /// A type, or a part of one, that names no parameter comes back as it is, on its
    /// carrier. The substitution goes through the data forms [`DeclaredType::shape`] reads,
    /// a type application and a tuple; any other form that names a parameter — a function
    /// type, an effect row, a projection off a parameter (`P.Key`) — is refused as `shape`
    /// refuses it (`NoDataSpelling`): substituted in, it would be a type the loader does not
    /// write for the same type (`P.Key` at `P = MemStore` is not the term `MemStore.Key`
    /// is). A parameter nothing binds is refused by its name (`UnboundParameter`), as `shape`
    /// refuses it — here wherever it stands, where `shape` refuses it only when a walk
    /// reaches it; so is any other free variable, by its own name. A de Bruijn variable,
    /// which no type holds, is `Variable`.
    pub fn closed_type(&self, kb: &KnowledgeBase) -> Result<Value, ValueProblem> {
        Ok(closing(kb, self)?.unwrap_or_else(|| self.view.clone()))
    }

    /// The type as the KB prints one, with the parameters its place binds substituted
    /// (`Cell[T = Bool]` for `Holder`'s `c: Cell[T = A]` at `Holder[A = Bool]`). Display only:
    /// to compare it with a type, [`DeclaredType::closed_type`].
    pub fn display_name(&self, kb: &KnowledgeBase) -> String {
        expected_text(kb, self)
    }
}

/// What a declared type is, to a walk over values at it.
#[derive(Debug)]
pub enum TypeShape {
    String,
    Int64,
    Float,
    BigInt,
    Bool,
    Type,
    /// `Option`, at its element's type.
    Option(DeclaredType),
    /// `List`, at its element's type.
    List(DeclaredType),
    /// `Set`, at its element's type: written as the array of its elements.
    Set(DeclaredType),
    /// `Map`, at its key's and its value's types: written as the array of its `[key, value]`
    /// entries.
    Map { key: DeclaredType, value: DeclaredType },
    /// Components in the type's order, each `(label, type)`.
    Tuple(Vec<(Symbol, DeclaredType)>),
    /// A sort or an entity: the constructors its values may be. At a sort with abstract values,
    /// its providers' constructors.
    Data(DataShape),
}

/// A sort or an entity at the type that applies it: its constructors, and the bindings of its
/// parameters there — the place its constructors' fields are typed in. At a sort with abstract
/// values (proposal 073 §2: a spec whose values are its providers'), the constructors of the
/// sorts with constructors that provide it, each typed in its own provider's parameters.
#[derive(Debug)]
pub struct DataShape {
    sort: Symbol,
    ctors: Vec<Symbol>,
    /// The type's one constructor is the type itself (an entity's type).
    own: bool,
    homes: Homes,
}

/// Where a [`DataShape`]'s constructors' fields are typed.
#[derive(Debug)]
enum Homes {
    /// A sort's or an entity's: every constructor's, in the bindings of the type's parameters.
    Sort(Env),
    /// A sort with abstract values': each constructor's provider and the bindings of the
    /// provider's parameters, in the order of the constructors.
    Providers(Vec<(Symbol, Env)>),
}

impl DataShape {
    /// The sort the type is headed by (for an entity's type, the entity; for a sort with
    /// abstract values, that sort).
    pub fn sort(&self) -> Symbol {
        self.sort
    }

    /// The constructors a value of the type may be, in declared order; at a sort with abstract
    /// values, its providers' constructors, provider by provider.
    pub fn constructors(&self) -> &[Symbol] {
        &self.ctors
    }

    /// The provider `ctor` is a constructor of, where the type is a sort with abstract values
    /// (`Car` for `car` at `Sp`): a value of `ctor` at the type is an instance of that provider
    /// (`Instance(dict, car(n: 1))`, [`SpecValues`]). `None` at any other type, and for a
    /// constructor that is not one of the type's.
    pub fn provider(&self, ctor: Symbol) -> Option<Symbol> {
        let i = self.ctors.iter().position(|c| *c == ctor.plain())?;
        match &self.homes {
            Homes::Sort(_) => None,
            Homes::Providers(providers) => Some(providers[i].0),
        }
    }

    /// Is the type a sort with abstract values?
    fn is_abstract(&self) -> bool {
        matches!(self.homes, Homes::Providers(_))
    }

    /// `ctor`'s fields, each `(field, type)` in declared order, each type in this type's
    /// bindings: `Cell`'s `value` at `Cell[T = Int64]` is read as `Int64` by its
    /// [`DeclaredType::shape`]; at a sort with abstract values, in its provider's. A parameter
    /// the type leaves open is refused there, at the field that names it. Refused here: a
    /// constructor that is not one of the type's (`UnknownConstructor`), and one the KB records
    /// a field's name for and no type for (`NoDataSpelling`).
    pub fn fields(&self, kb: &KnowledgeBase, ctor: Symbol) -> Result<Vec<(Symbol, DeclaredType)>, ValueProblem> {
        // A constructor is its plain symbol; a type names one by its face.
        let ctor = ctor.plain();
        let Some(i) = self.ctors.iter().position(|c| *c == ctor) else {
            return Err(ValueProblem::UnknownConstructor {
                name: kb.qualified_name_of(ctor).to_owned(),
                sort: kb.qualified_name_of(self.sort).to_owned(),
            });
        };
        let env = match &self.homes {
            Homes::Sort(env) => env,
            Homes::Providers(providers) => &providers[i].1,
        };
        declared_fields(kb, ctor)
            .into_iter()
            .map(|(field, fty)| match fty {
                Some(view) => Ok((
                    field,
                    DeclaredType {
                        view,
                        env: env.clone(),
                    },
                )),
                None => Err(ValueProblem::NoDataSpelling),
            })
            .collect()
    }

    /// The constructors of the type a tag names (more than one only at a sort with abstract
    /// values, whose providers' constructors may share a short name).
    fn tagged(&self, kb: &KnowledgeBase, tag: &str, names: TagNames) -> Vec<Symbol> {
        let names_it = |c: Symbol| match names {
            TagNames::Short => kb.local_name_of(c) == tag,
            TagNames::Qualified => kb.qualified_name_of(c) == tag,
        };
        self.ctors.iter().copied().filter(|c| names_it(*c)).collect()
    }
}

/// The type `ty` stands for once its parameter is looked up: `T` at `cons.head` within
/// `List[T = Stock]` is `Stock`. A parameter nothing binds is refused, naming it.
fn resolve(kb: &KnowledgeBase, ty: &DeclaredType) -> Result<(DeclaredType, TypeExtractor), ValueProblem> {
    let mut cur = ty.clone();
    loop {
        match extract_type(kb, &cur.view) {
            TypeExtractor::FlexVar { name, id } => match cur.env.lookup(id) {
                // A binding is a type of an OUTER place, so the walk ends.
                Some(Binding::To(bound)) => cur = bound.clone(),
                Some(Binding::Open(param)) => {
                    return Err(ValueProblem::UnboundParameter {
                        name: kb.local_name_of(*param).to_owned(),
                    })
                }
                // Free in the type handed in. A parameter's canonical variable is anonymous
                // (`?_`), so it is named by the parameter it stands for: the field type as
                // WRITTEN (`value: T`) handed in for the type at an application.
                None => {
                    let param = kb.type_param_of_canonical_var(VarId::new(id, name)).unwrap_or(name);
                    return Err(ValueProblem::UnboundParameter {
                        name: kb.local_name_of(param).to_owned(),
                    });
                }
            },
            TypeExtractor::Skolem { name, .. } | TypeExtractor::TypeVar(name) => {
                return Err(ValueProblem::UnboundParameter {
                    name: kb.local_name_of(name).to_owned(),
                })
            }
            other => return Ok((cur, other)),
        }
    }
}

/// The bindings of `sort`'s parameters at the type `ty` applies it to: each parameter the
/// type binds, by its name or its position, to the type written there (within `ty`'s own
/// bindings); one it leaves unwritten to its declared default (within the parameters bound
/// before it); one with neither is OPEN, refused, by its name, where a field names it.
fn sort_env(kb: &KnowledgeBase, sort: Symbol, ty: &DeclaredType, bindings: &[(Symbol, Value)]) -> Env {
    // A constructor's own type is typed in its sort's parameters.
    let owner = if kb.type_param_syms_of(sort).is_empty() {
        kb.sort_of_constructor(sort).unwrap_or(sort)
    } else {
        sort
    };
    let mut bound: Vec<(u32, Binding)> = Vec::new();
    for (i, &param) in kb.type_param_syms_of(owner).iter().enumerate() {
        // WI-954: every declared parameter publishes its canonical variable, and it is a
        // plain `Var::Global` (the loader refuses any other); a field names the parameter by it.
        let var = kb.canonical_type_param_var(param).unwrap_or_else(|| {
            panic!("`{}` declares no canonical variable", kb.qualified_name_of(param))
        });
        let Term::Var(Var::Global(vid)) = kb.get_term(var) else {
            panic!("`{}`'s canonical variable is no `Var::Global`", kb.qualified_name_of(param))
        };
        let id = vid.raw();
        let name = kb.local_name_of(param);
        let written = bindings.iter().find(|(k, _)| {
            let label = kb.local_name_of(*k);
            label == name || is_positional_label_at(label, i)
        });
        let binding = match written {
            Some((_, v)) => Binding::To(ty.within(v.clone())),
            None => match kb.sort_param_defaults.get(&param) {
                Some(&default) => Binding::To(DeclaredType {
                    view: Value::term(default),
                    env: Env(Rc::new(bound.clone())),
                }),
                None => Binding::Open(param),
            },
        };
        bound.push((id, binding));
    }
    Env(Rc::new(bound))
}

/// The type `ty` stands for, printed as the KB prints a type, with the parameters its place
/// binds substituted where they occur in an application (`List[T = Int64]`, not `List[T =
/// T]`). Display only: the application is rebuilt as an entity value, which the KB's one
/// type renderer reads as it reads a term (WI-20260904-B1KFS).
fn expected_text(kb: &KnowledgeBase, ty: &DeclaredType) -> String {
    type_display_name_value(kb, &shown_type(kb, ty))
}

fn shown_type(kb: &KnowledgeBase, ty: &DeclaredType) -> Value {
    let mut ty = ty.clone();
    while let TypeExtractor::FlexVar { id, name } = extract_type(kb, &ty.view) {
        match ty.env.lookup(id) {
            Some(Binding::To(bound)) => ty = bound.clone(),
            // An open parameter is shown by its own name, not by its anonymous variable.
            Some(Binding::Open(param)) => return Value::SymbolRef(*param),
            // Free: a parameter's canonical variable by the parameter's name, as `resolve`
            // names it; any other variable as itself.
            None => {
                return match kb.type_param_of_canonical_var(VarId::new(id, name)) {
                    Some(param) => Value::SymbolRef(param),
                    None => ty.view,
                }
            }
        }
    }
    if ty.env.is_empty() {
        return ty.view;
    }
    match (ty.view.head(kb), extract_type(kb, &ty.view)) {
        (ViewHead::Functor { functor, .. }, TypeExtractor::Parameterized { bindings, .. })
            if !bindings.is_empty() =>
        {
            let named: Vec<(Symbol, Value)> = bindings
                .into_iter()
                .map(|(k, v)| (k, shown_type(kb, &ty.within(v))))
                .collect();
            Value::Entity {
                functor,
                pos: Rc::from(Vec::new()),
                named: named.into(),
            }
        }
        _ => ty.view,
    }
}

/// [`DeclaredType::closed_type`] of `ty`, or `None` where `ty`'s own view is that type
/// already (it names no parameter), so it comes back unrebuilt, on its carrier.
fn closing(kb: &KnowledgeBase, ty: &DeclaredType) -> Result<Option<Value>, ValueProblem> {
    let bound = matches!(extract_type(kb, &ty.view), TypeExtractor::FlexVar { .. });
    let (ty, extracted) = resolve(kb, ty)?;
    let rebuilt = match extracted {
        TypeExtractor::Parameterized { .. } | TypeExtractor::NamedTuple(_) => rebuilt_children(kb, &ty)?,
        // `resolve` reads every flexible and rigid variable; a variable left is a rule's binder.
        _ if matches!(ty.view.head(kb), ViewHead::Var(_)) => return Err(ValueProblem::Variable),
        _ if names_parameter(kb, &ty.view) => return Err(ValueProblem::NoDataSpelling),
        _ => None,
    };
    Ok(match rebuilt {
        Some(v) => Some(v),
        // A parameter's binding that names none of its own place's.
        None if bound => Some(ty.view),
        None => None,
    })
}

/// A type application's or a tuple's children, each closed in `ty`'s bindings; `None` where
/// every child is closed as it stands, and so the form is.
fn rebuilt_children(kb: &KnowledgeBase, ty: &DeclaredType) -> Result<Option<Value>, ValueProblem> {
    let ViewHead::Functor { functor, pos_arity, .. } = ty.view.head(kb) else {
        unreachable!("a type application or a tuple is headed by its functor")
    };
    let mut changed = false;
    let mut close = |item: crate::kb::term_view::ViewItem| -> Result<Value, ValueProblem> {
        let child = ty.within(item.to_value());
        Ok(match closing(kb, &child)? {
            Some(v) => {
                changed = true;
                v
            }
            None => child.view,
        })
    };
    let pos = (0..pos_arity)
        .map(|i| close(ty.view.pos_arg(kb, i).expect("a view answers for a position its head counts")))
        .collect::<Result<Vec<Value>, ValueProblem>>()?;
    let named = ty
        .view
        .named_keys(kb)
        .into_iter()
        .map(|k| Ok((k, close(ty.view.named_arg(kb, k).expect("a view answers for a named key it lists"))?)))
        .collect::<Result<Vec<(Symbol, Value)>, ValueProblem>>()?;
    Ok(changed.then(|| Value::Entity {
        functor,
        pos: pos.into(),
        named: named.into(),
    }))
}

/// Does `v` name a parameter: a variable anywhere, or a projection off a parameter (`P.Key`,
/// whose subject is the parameter's own name, not its variable)?
fn names_parameter(kb: &KnowledgeBase, v: &impl TermView) -> bool {
    match v.head(kb) {
        ViewHead::Var(_) => true,
        ViewHead::Functor { pos_arity, .. } => {
            if let TypeExtractor::RigidTypeProjection { subject, .. } = extract_type(kb, v) {
                return match extract_type(kb, &subject) {
                    TypeExtractor::SortRef(s) => kb.canonical_type_param_var(s).is_some(),
                    _ => names_parameter(kb, &subject),
                };
            }
            (0..pos_arity).any(|i| v.pos_arg(kb, i).is_some_and(|a| names_parameter(kb, &a)))
                || v.named_keys(kb)
                    .into_iter()
                    .any(|k| v.named_arg(kb, k).is_some_and(|a| names_parameter(kb, &a)))
        }
        ViewHead::Const(_) | ViewHead::Ident(_) | ViewHead::Bottom | ViewHead::Opaque => false,
    }
}

/// A short rendering of a JSON value for a message.
fn describe_json(v: &serde_json::Value) -> String {
    match v {
        serde_json::Value::Array(a) => format!("an array of {} elements", a.len()),
        serde_json::Value::Object(m) if m.len() == 1 => {
            format!("an object of one key `{}`", m.keys().next().expect("one key"))
        }
        serde_json::Value::Object(m) => format!("an object of {} keys", m.len()),
        other => clip(other.to_string()),
    }
}

/// A short rendering of a value for a message.
fn describe_value(kb: &KnowledgeBase, v: &Value) -> String {
    clip(TermPrinter::new(kb).print_value(v))
}

fn clip(mut s: String) -> String {
    const MAX: usize = 60;
    if s.chars().count() > MAX {
        s = s.chars().take(MAX).collect::<String>() + "…";
    }
    s
}

/// The tag a constructor is written with.
fn tag_of(kb: &KnowledgeBase, ctor: Symbol, names: TagNames) -> String {
    match names {
        TagNames::Short => kb.local_name_of(ctor).to_owned(),
        TagNames::Qualified => kb.qualified_name_of(ctor).to_owned(),
    }
}

/// The refusal of a tag that names each of `ctors`, by their qualified names.
fn ambiguous_tag(kb: &KnowledgeBase, tag: &str, ctors: &[Symbol]) -> ValueProblem {
    let mut constructors: Vec<String> = ctors.iter().map(|c| kb.qualified_name_of(*c).to_owned()).collect();
    constructors.sort();
    ValueProblem::AmbiguousTag {
        tag: tag.to_owned(),
        constructors,
    }
}

/// The order a set's elements and a map's entries are written in: by their spellings, so one
/// set or map is written the same whatever order it was built in. Kinds rank null, booleans,
/// numbers, strings, arrays, objects; numbers by value (an integer exactly, then the text when
/// two read as one float), strings by code point, arrays and objects element by element (an
/// object's keys in its order, each key before its value), a shorter one first.
fn json_order(a: &serde_json::Value, b: &serde_json::Value) -> std::cmp::Ordering {
    use serde_json::Value as J;
    use std::cmp::Ordering;
    let rank = |v: &J| match v {
        J::Null => 0,
        J::Bool(_) => 1,
        J::Number(_) => 2,
        J::String(_) => 3,
        J::Array(_) => 4,
        J::Object(_) => 5,
    };
    match (a, b) {
        (J::Bool(x), J::Bool(y)) => x.cmp(y),
        (J::Number(x), J::Number(y)) => match (x.as_i64(), y.as_i64()) {
            (Some(i), Some(j)) => i.cmp(&j),
            _ => {
                let (f, g) = (x.as_f64().unwrap_or(f64::NAN), y.as_f64().unwrap_or(f64::NAN));
                f.total_cmp(&g).then_with(|| x.to_string().cmp(&y.to_string()))
            }
        },
        (J::String(x), J::String(y)) => x.cmp(y),
        (J::Array(x), J::Array(y)) => x
            .iter()
            .zip(y)
            .map(|(p, q)| json_order(p, q))
            .find(|o| *o != Ordering::Equal)
            .unwrap_or_else(|| x.len().cmp(&y.len())),
        (J::Object(x), J::Object(y)) => x
            .iter()
            .zip(y)
            .map(|((k, p), (l, q))| k.cmp(l).then_with(|| json_order(p, q)))
            .find(|o| *o != Ordering::Equal)
            .unwrap_or_else(|| x.len().cmp(&y.len())),
        _ => rank(a).cmp(&rank(b)),
    }
}

/// A constructor's declared fields, each `(field, type)`, in declared order. A constructor the
/// KB records names for and no types for is not one the mapping can read.
fn declared_fields(kb: &KnowledgeBase, ctor: Symbol) -> Vec<(Symbol, Option<Value>)> {
    let types = kb.entity_field_types(ctor).map(<[_]>::to_vec).unwrap_or_default();
    kb.entity_field_names(ctor)
        .map(<[_]>::to_vec)
        .unwrap_or_default()
        .into_iter()
        .map(|f| {
            let t = types.iter().find(|(s, _)| *s == f).map(|(_, t)| t.clone());
            (f, t)
        })
        .collect()
}

fn runtime_account(kb: &KnowledgeBase, ctor: Symbol) -> Result<(), ValueProblem> {
    match kb.runtime_account_of(ctor) {
        Some(_) => Err(ValueProblem::RuntimeAccount {
            constructor: kb.qualified_name_of(ctor).to_owned(),
        }),
        None => Ok(()),
    }
}

/// An operation application's operand, by its parameter's name or its position (a fact writes
/// `insert(s, x)` positionally).
fn operand(kb: &KnowledgeBase, v: &Value, name: &str, index: usize) -> Option<Value> {
    v.named_field(kb, name)
        .or_else(|| v.pos_arg(kb, index))
        .map(|a| a.to_value())
}

/// The `TupleLiteral` functor a tuple value is built on, as a rule writes it.
fn tuple_functor(kb: &KnowledgeBase) -> Option<Symbol> {
    kb.try_resolve_symbol(dt::qualified(dt::TUPLE_LITERAL))
}

/// Are the components all positional (`_1`, `_2`, … in order)? Such a tuple is an array.
fn all_positional(kb: &KnowledgeBase, comps: &[(Symbol, DeclaredType)]) -> bool {
    comps
        .iter()
        .enumerate()
        .all(|(i, (l, _))| is_positional_label_at(kb.local_name_of(*l), i))
}

// ── Decoding ───────────────────────────────────────────────────

struct Decoder<'k> {
    kb: &'k mut KnowledgeBase,
    opts: CodecOptions,
    /// The variables of this one value, by name.
    vars: HashMap<String, VarId>,
    path: Vec<PathStep>,
    /// Where a TOML row held a float with no JSON value (`nan`, `inf`), and which: refused
    /// when the walk reaches the place, as a value of the row ([`toml_to_json`]).
    nonfinite: Vec<(Vec<PathStep>, f64)>,
}

impl<'k> Decoder<'k> {
    fn new(kb: &'k mut KnowledgeBase, opts: CodecOptions) -> Self {
        Decoder {
            kb,
            opts,
            vars: HashMap::new(),
            path: Vec::new(),
            nonfinite: Vec::new(),
        }
    }

    fn err(&self, ty: &DeclaredType, problem: ValueProblem) -> ValueError {
        ValueError {
            path: JsonPath(self.path.clone()),
            expected: expected_text(self.kb, ty),
            problem,
        }
    }

    fn at<R>(&mut self, step: PathStep, f: impl FnOnce(&mut Self) -> R) -> R {
        self.path.push(step);
        let r = f(self);
        self.path.pop();
        r
    }

    fn value(&mut self, json: &serde_json::Value, ty: &DeclaredType) -> Result<TermId, ValueError> {
        let shape = ty.shape(self.kb).map_err(|p| self.err(ty, p))?;
        if let Some((_, f)) = self.nonfinite.iter().find(|(at, _)| *at == self.path) {
            let what = format!("the TOML float `{}`", toml_float_text(*f));
            return Err(self.err(ty, ValueProblem::Unrepresentable { what }));
        }
        if let Some(var) = self.variable(json) {
            // Under an `Option` the variable is the present value's (021, "Variables"), and one
            // that would stand for a whole inner `Option` has no spelling, as the writer says.
            return match shape {
                TypeShape::Option(inner) => match inner.shape(self.kb) {
                    Ok(TypeShape::Option(_)) => Err(self.err(&inner, ValueProblem::Variable)),
                    _ => Ok(self.some(var)),
                },
                _ => Ok(var),
            };
        }
        let wrong = |me: &Self| me.err(ty, ValueProblem::WrongShape { found: describe_json(json) });
        use serde_json::Value as J;
        match shape {
            TypeShape::String => match json {
                J::String(s) => Ok(self.literal(Literal::String(self.unescape(s)))),
                _ => Err(wrong(self)),
            },
            TypeShape::Bool => match json {
                J::Bool(b) => Ok(self.literal(Literal::Bool(*b))),
                _ => Err(wrong(self)),
            },
            TypeShape::Int64 => match json {
                J::Number(n) => match n.as_i64() {
                    Some(i) => Ok(self.literal(Literal::Int(i))),
                    // Past `i64` either way: a `u64`, or an integer the parser has rounded to
                    // an f64 (`-9223372036854775809`). An f64 in range was written with a
                    // fraction or an exponent (`3.0`, `1e3`).
                    None if n.is_u64() || n.as_f64().is_some_and(past_i64) => {
                        Err(self.err(ty, ValueProblem::OutOfRange { found: n.to_string() }))
                    }
                    None => Err(self.err(ty, ValueProblem::NotAnInteger { found: n.to_string() })),
                },
                _ => Err(wrong(self)),
            },
            TypeShape::Float => match json {
                J::Number(n) => {
                    let f = n.as_f64().expect("a JSON number is an f64 without arbitrary_precision");
                    Ok(self.literal(Literal::Float(OrderedFloat(f))))
                }
                _ => Err(wrong(self)),
            },
            TypeShape::BigInt => {
                let digits = match json {
                    J::Number(n) if n.is_i64() || n.is_u64() => n.to_string(),
                    J::Number(n) => {
                        // An f64: written with a fraction or an exponent, or an integer past
                        // `u64` (or below `i64`) that the parser has already rounded.
                        let f = n.as_f64().unwrap_or(f64::NAN);
                        let problem = if f.fract() == 0.0 && (f >= TWO_TO_64 || f <= -TWO_TO_63) {
                            ValueProblem::OutOfRange { found: n.to_string() }
                        } else {
                            ValueProblem::NotAnInteger { found: n.to_string() }
                        };
                        return Err(self.err(ty, problem));
                    }
                    J::String(s) if is_decimal_integer(s) => s.clone(),
                    _ => return Err(wrong(self)),
                };
                let n: num_bigint::BigInt = digits.parse().expect("decimal digits parse as a BigInt");
                Ok(self.literal(Literal::BigInt(n)))
            }
            TypeShape::Type => match json {
                J::String(s) => type_from_text(self.kb, s).map_err(|e| self.err(ty, e.problem)),
                _ => Err(wrong(self)),
            },
            TypeShape::Option(inner) => match json {
                J::Null => Ok(self.none()),
                other => {
                    let v = self.value(other, &inner)?;
                    Ok(self.some(v))
                }
            },
            TypeShape::List(elem) => match json {
                J::Array(items) => {
                    let mut terms = Vec::with_capacity(items.len());
                    for (i, item) in items.iter().enumerate() {
                        terms.push(self.at(PathStep::Index(i), |me| me.value(item, &elem))?);
                    }
                    Ok(self.kb.build_list(&terms))
                }
                _ => Err(wrong(self)),
            },
            TypeShape::Set(elem) => match json {
                J::Array(items) => self.set(items, ty, &elem),
                _ => Err(wrong(self)),
            },
            TypeShape::Map { key, value } => match json {
                J::Array(entries) => self.map(entries, ty, &key, &value),
                _ => Err(wrong(self)),
            },
            TypeShape::Tuple(comps) => self.tuple(json, ty, &comps),
            TypeShape::Data(data) => self.data(json, ty, &data),
        }
    }

    /// A set from the array of its elements: `insert(insert(empty, 2), 1)` from `[2, 1]`, each
    /// element inserted in the array's order, as a fact writing that chain builds it. An element
    /// written twice — the same term, however spelled — is refused at its second place, but with
    /// [`CollectionOrder::AsBuilt`], whose writer writes a chain that inserts one twice.
    fn set(&mut self, items: &[serde_json::Value], ty: &DeclaredType, elem: &DeclaredType) -> Result<TermId, ValueError> {
        let empty = self.kb.resolve_symbol(SET_EMPTY);
        let insert = self.kb.resolve_symbol(SET_INSERT);
        // Each element read so far, and the index it was read at.
        let mut members: HashMap<TermId, usize> = HashMap::with_capacity(items.len());
        let mut set = self.kb.alloc(Term::Ref(empty));
        for (i, item) in items.iter().enumerate() {
            let member = self.at(PathStep::Index(i), |me| me.value(item, elem))?;
            if let Some(&first) = members.get(&member) {
                if self.opts.collection_order == CollectionOrder::Canonical {
                    return Err(self.at(PathStep::Index(i), |me| me.err(ty, ValueProblem::RepeatedElement { first })));
                }
            }
            members.entry(member).or_insert(i);
            set = self.kb.alloc(Term::Fn {
                functor: insert,
                pos_args: SmallVec::from_slice(&[set, member]),
                named_args: SmallVec::new(),
            });
        }
        Ok(set)
    }

    /// A map from the array of its `[key, value]` entries: `put(put(empty, k1, v1), k2, v2)`,
    /// each entry put in the array's order, as a fact writing that chain builds it. A key written
    /// twice — the same term, however spelled — is refused at its second entry, since which value
    /// it maps to would be the array's order alone; with [`CollectionOrder::AsBuilt`] that order is
    /// the chain's, and the later entry shadows the earlier, as its `put` does.
    fn map(
        &mut self,
        entries: &[serde_json::Value],
        ty: &DeclaredType,
        key: &DeclaredType,
        value: &DeclaredType,
    ) -> Result<TermId, ValueError> {
        use serde_json::Value as J;
        let empty = self.kb.resolve_symbol(MAP_EMPTY);
        let put = self.kb.resolve_symbol(MAP_PUT);
        // Each key read so far, and the index of its entry.
        let mut keys: HashMap<TermId, usize> = HashMap::with_capacity(entries.len());
        let mut map = self.kb.alloc(Term::Ref(empty));
        for (i, entry) in entries.iter().enumerate() {
            let (k, v) = self.at(PathStep::Index(i), |me| match entry {
                J::Array(pair) if pair.len() == 2 => {
                    let k = me.at(PathStep::Index(0), |me| me.value(&pair[0], key))?;
                    let v = me.at(PathStep::Index(1), |me| me.value(&pair[1], value))?;
                    Ok((k, v))
                }
                other => Err(me.err(ty, ValueProblem::NotAnEntry { found: describe_json(other) })),
            })?;
            if let Some(&first) = keys.get(&k) {
                if self.opts.collection_order == CollectionOrder::Canonical {
                    return Err(self.at(PathStep::Index(i), |me| me.err(ty, ValueProblem::RepeatedKey { first })));
                }
            }
            keys.entry(k).or_insert(i);
            map = self.kb.alloc(Term::Fn {
                functor: put,
                pos_args: SmallVec::from_slice(&[map, k, v]),
                named_args: SmallVec::new(),
            });
        }
        Ok(map)
    }

    /// The variable `json` spells, with variables on: `"?name"`, or `"?"` for an anonymous one.
    fn variable(&mut self, json: &serde_json::Value) -> Option<TermId> {
        if !self.opts.variables {
            return None;
        }
        let name = json.as_str()?.strip_prefix('?')?;
        let vid = if name.is_empty() {
            let anon = self.kb.intern("_");
            self.kb.fresh_var(anon)
        } else {
            match self.vars.get(name) {
                Some(&v) => v,
                None => {
                    let sym = self.kb.intern(name);
                    let v = self.kb.fresh_var(sym);
                    self.vars.insert(name.to_owned(), v);
                    v
                }
            }
        };
        Some(self.kb.alloc(Term::Var(Var::Global(vid))))
    }

    /// With variables on, a string of one or more `\` and then `?` loses one `\`.
    fn unescape(&self, s: &str) -> String {
        if self.opts.variables && s.starts_with('\\') && s.trim_start_matches('\\').starts_with('?') {
            s[1..].to_owned()
        } else {
            s.to_owned()
        }
    }

    fn literal(&mut self, lit: Literal) -> TermId {
        self.kb.alloc(Term::Const(lit))
    }

    /// `none`, as the loader writes it: the nullary constructor's `Ref`.
    fn none(&mut self) -> TermId {
        let none = self.kb.resolve_symbol(OPTION_NONE);
        self.kb.alloc(Term::Ref(none))
    }

    fn some(&mut self, inner: TermId) -> TermId {
        let some = self.kb.resolve_symbol(OPTION_SOME);
        let field = self.kb.entity_field_names(some).expect("`some` declares its field")[0];
        self.kb
            .make_entity_term(some, SmallVec::new(), SmallVec::from_elem((field, inner), 1))
    }

    fn tuple(&mut self, json: &serde_json::Value, ty: &DeclaredType, comps: &[(Symbol, DeclaredType)]) -> Result<TermId, ValueError> {
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        if all_positional(self.kb, comps) {
            let Some(items) = json.as_array() else {
                return Err(self.err(ty, ValueProblem::WrongShape { found: describe_json(json) }));
            };
            if items.len() != comps.len() {
                let problem = match comps.get(items.len()) {
                    Some((label, _)) => ValueProblem::MissingField {
                        name: self.kb.local_name_of(*label).to_owned(),
                    },
                    None => ValueProblem::UnknownField {
                        name: crate::intern::positional_label(comps.len()),
                    },
                };
                return Err(self.err(ty, problem));
            }
            for (i, ((label, cty), item)) in comps.iter().zip(items).enumerate() {
                let t = self.at(PathStep::Index(i), |me| me.value(item, cty))?;
                named.push((*label, t));
            }
        } else {
            let Some(obj) = json.as_object() else {
                return Err(self.err(ty, ValueProblem::WrongShape { found: describe_json(json) }));
            };
            if let Some(k) = obj
                .keys()
                .find(|k| !comps.iter().any(|(l, _)| self.kb.local_name_of(*l) == k.as_str()))
            {
                return Err(self.err(ty, ValueProblem::UnknownField { name: k.clone() }));
            }
            if let Some((label, _)) = comps.iter().find(|(l, _)| !obj.contains_key(self.kb.local_name_of(*l))) {
                let name = self.kb.local_name_of(*label).to_owned();
                return Err(self.err(ty, ValueProblem::MissingField { name }));
            }
            // In the order the object writes them: a labelled tuple's order is its identity
            // (kernel §4.5), and the writer writes the value's own.
            for (name, item) in obj {
                let (label, cty) = comps
                    .iter()
                    .find(|(l, _)| self.kb.local_name_of(*l) == name.as_str())
                    .expect("every key names a component");
                let t = self.at(PathStep::Key(name.clone()), |me| me.value(item, cty))?;
                named.push((*label, t));
            }
        }
        let functor = tuple_functor(self.kb).ok_or_else(|| self.err(ty, ValueProblem::NoDataSpelling))?;
        Ok(self.kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: named,
        }))
    }

    fn data(&mut self, json: &serde_json::Value, ty: &DeclaredType, data: &DataShape) -> Result<TermId, ValueError> {
        let value = self.constructed(json, ty, data)?;
        if !data.is_abstract() || self.opts.spec_values == SpecValues::Plain {
            return Ok(value);
        }
        self.paired(value, ty)
    }

    /// `value`, read at `ty`, a type headed by a sort with abstract values, paired with its
    /// provider's dictionary there, `Instance(dict, value)`: the pair an operation body builds
    /// where it uses the provider's value at the abstract sort (073 §2), which is the term a
    /// call at one takes. Refused where no provision answers at the place's type
    /// (`NoInstance`).
    fn paired(&mut self, value: TermId, ty: &DeclaredType) -> Result<TermId, ValueError> {
        let place = ty.closed_type(self.kb).map_err(|p| self.err(ty, p))?;
        let value = Value::term(value);
        let dict = crate::kb::typing::instance_dictionary_of_read_value(self.kb, &value, &place)
            .map_err(|reason| self.err(ty, ValueProblem::NoInstance { reason }))?;
        let no_instance = |me: &Self, reason: String| me.err(ty, ValueProblem::NoInstance { reason });
        let instance = self
            .kb
            .try_resolve_symbol(INSTANCE)
            .ok_or_else(|| no_instance(self, format!("this knowledge base never loaded `{INSTANCE}`")))?;
        // The term the running pair lowers to: its two components positional, as eval makes it.
        let pair = Value::Entity {
            functor: instance,
            pos: vec![dict, value].into(),
            named: Vec::new().into(),
        };
        self.kb
            .alloc_from_value(&pair)
            .map_err(|e| no_instance(self, format!("the pair has no term: {e:?}")))
    }

    /// The constructed value `json` spells at `ty`: a tag, or a tag and its payload.
    fn constructed(&mut self, json: &serde_json::Value, ty: &DeclaredType, data: &DataShape) -> Result<TermId, ValueError> {
        use serde_json::Value as J;
        let ctors = data.constructors();
        if data.own && self.opts.entity_tags == EntityTags::OmitAtEntityType {
            runtime_account(self.kb, ctors[0]).map_err(|p| self.err(ty, p))?;
            return match json {
                J::Object(fields) => self.fields(ctors[0], data, fields, ty),
                other => Err(self.err(ty, ValueProblem::WrongShape { found: describe_json(other) })),
            };
        }
        match json {
            J::String(tag) => {
                let ctor = self.ctor_by_tag(tag, data, ty)?;
                let fields = declared_fields(self.kb, ctor).len();
                if fields != 0 {
                    return Err(self.err(
                        ty,
                        ValueProblem::NotOneField {
                            constructor: self.kb.local_name_of(ctor).to_owned(),
                            fields,
                        },
                    ));
                }
                Ok(self.kb.alloc(Term::Ref(ctor)))
            }
            J::Object(m) if m.len() == 1 => {
                let (tag, payload) = m.iter().next().expect("one key");
                let ctor = self.ctor_by_tag(tag, data, ty)?;
                let ctor_ty = ty.within(Value::SymbolRef(self.kb.type_face_of(ctor)));
                self.at(PathStep::Key(tag.clone()), |me| match payload {
                    J::Object(fields) => me.fields(ctor, data, fields, &ctor_ty),
                    other => me.shorthand(ctor, data, other, &ctor_ty),
                })
            }
            other => {
                let mut tags: Vec<String> =
                    ctors.iter().map(|c| tag_of(self.kb, *c, self.opts.tag_names)).collect();
                tags.sort();
                tags.dedup();
                Err(self.err(
                    ty,
                    match other {
                        J::Object(_) => ValueProblem::NotTagged {
                            found: describe_json(other),
                            tags,
                        },
                        _ => ValueProblem::WrongShape { found: describe_json(other) },
                    },
                ))
            }
        }
    }

    /// The constructor of the declared type a tag names — among those constructors and nowhere
    /// else (WI-912): a tag outside the type is a wrong-typed value, not a name to look up. A tag
    /// naming two of them (two providers' constructors sharing a short name) is refused, naming
    /// both: no one value is meant.
    fn ctor_by_tag(&self, tag: &str, data: &DataShape, ty: &DeclaredType) -> Result<Symbol, ValueError> {
        let ctor = match data.tagged(self.kb, tag, self.opts.tag_names).as_slice() {
            [] => {
                return Err(self.err(
                    ty,
                    ValueProblem::UnknownConstructor {
                        name: tag.to_owned(),
                        sort: self.kb.qualified_name_of(data.sort).to_owned(),
                    },
                ))
            }
            [ctor] => *ctor,
            several => return Err(self.err(ty, ambiguous_tag(self.kb, tag, several))),
        };
        runtime_account(self.kb, ctor).map_err(|p| self.err(ty, p))?;
        Ok(ctor)
    }

    /// The object of a constructor's fields: each key a field, decoded at its declared type in
    /// the type's bindings (`data`); an absent `Option` field is `none()`, any other absent
    /// field an error.
    fn fields(
        &mut self,
        ctor: Symbol,
        data: &DataShape,
        obj: &serde_json::Map<String, serde_json::Value>,
        ty: &DeclaredType,
    ) -> Result<TermId, ValueError> {
        let declared = data.fields(self.kb, ctor).map_err(|p| self.err(ty, p))?;
        if let Some(k) = obj
            .keys()
            .find(|k| !declared.iter().any(|(f, _)| self.kb.local_name_of(*f) == k.as_str()))
        {
            return Err(self.err(ty, ValueProblem::UnknownField { name: k.clone() }));
        }
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for (field, fty) in &declared {
            let name = self.kb.local_name_of(*field).to_owned();
            let term = match obj.get(&name) {
                Some(v) => self.at(PathStep::Key(name), |me| me.value(v, fty))?,
                None => match fty.shape(self.kb) {
                    Ok(TypeShape::Option(_)) => self.none(),
                    Ok(_) => return Err(self.err(ty, ValueProblem::MissingField { name })),
                    Err(problem) => {
                        return Err(self.at(PathStep::Key(name), |me| me.err(fty, problem)))
                    }
                },
            };
            named.push((*field, term));
        }
        Ok(self.construct(ctor, named))
    }

    /// The single-field shorthand: the payload is the value of the constructor's one field.
    fn shorthand(
        &mut self,
        ctor: Symbol,
        data: &DataShape,
        payload: &serde_json::Value,
        ty: &DeclaredType,
    ) -> Result<TermId, ValueError> {
        let declared = data.fields(self.kb, ctor).map_err(|p| self.err(ty, p))?;
        let (field, fty) = match declared.as_slice() {
            [(field, fty)] => (field, fty),
            _ => {
                return Err(self.err(
                    ty,
                    ValueProblem::NotOneField {
                        constructor: self.kb.local_name_of(ctor).to_owned(),
                        fields: declared.len(),
                    },
                ))
            }
        };
        let term = self.value(payload, fty)?;
        Ok(self.construct(ctor, SmallVec::from_elem((*field, term), 1)))
    }

    /// A constructed value as the loader writes it: a nullary constructor its `Ref`, any other
    /// an application with its fields in declared order (WI-498).
    fn construct(&mut self, ctor: Symbol, named: SmallVec<[(Symbol, TermId); 2]>) -> TermId {
        if named.is_empty() {
            self.kb.alloc(Term::Ref(ctor))
        } else {
            self.kb.make_entity_term(ctor, SmallVec::new(), named)
        }
    }
}

const TWO_TO_63: f64 = 9_223_372_036_854_775_808.0;
const TWO_TO_64: f64 = 18_446_744_073_709_551_616.0;

/// An integral f64 at or past `i64`'s range. The parser rounds an integer past it to an f64,
/// and `-9223372036854775809` rounds to -2^63 exactly, `i64::MIN`; so the bound includes it,
/// and `-9223372036854775808.0`, written with a fraction, is refused as out of range too.
fn past_i64(f: f64) -> bool {
    f.fract() == 0.0 && f.abs() >= TWO_TO_63
}

fn is_decimal_integer(s: &str) -> bool {
    let digits = s.strip_prefix('-').unwrap_or(s);
    !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
}

// ── Encoding ───────────────────────────────────────────────────

struct Encoder<'k> {
    kb: &'k KnowledgeBase,
    opts: CodecOptions,
    path: Vec<PathStep>,
    /// With variables on, how often each variable occurs in the value being written, and the
    /// name each one is written with: the scope of a variable is one value, so two variables
    /// that share a name (`?x`, renamed apart in two clauses) are written apart (`?x`, `?x_2`),
    /// and an anonymous one that occurs twice is named, or the reader would read one
    /// variable as two, or two as one.
    occurrences: HashMap<VarId, usize>,
    names: HashMap<VarId, String>,
}

impl<'k> Encoder<'k> {
    /// An encoder of the one value `v`.
    fn new(kb: &'k KnowledgeBase, opts: CodecOptions, v: &Value) -> Self {
        let mut occurrences = HashMap::new();
        if opts.variables {
            count_variables(kb, v, &mut occurrences);
        }
        Encoder {
            kb,
            opts,
            path: Vec::new(),
            occurrences,
            names: HashMap::new(),
        }
    }

    /// The spelling of the variable `vid` in this value.
    fn variable(&mut self, vid: VarId) -> String {
        if let Some(name) = self.names.get(&vid) {
            return name.clone();
        }
        let base = self.kb.local_name_of(vid.name()).to_owned();
        if base == "_" && self.occurrences.get(&vid).copied().unwrap_or(0) <= 1 {
            return "?".to_owned();
        }
        let mut name = format!("?{base}");
        let mut k = 2;
        while self.names.values().any(|n| *n == name) {
            name = format!("?{base}_{k}");
            k += 1;
        }
        self.names.insert(vid, name.clone());
        name
    }

    fn err(&self, ty: &DeclaredType, problem: ValueProblem) -> ValueError {
        ValueError {
            path: JsonPath(self.path.clone()),
            expected: expected_text(self.kb, ty),
            problem,
        }
    }

    fn at<R>(&mut self, step: PathStep, f: impl FnOnce(&mut Self) -> R) -> R {
        self.path.push(step);
        let r = f(self);
        self.path.pop();
        r
    }

    fn wrong(&self, ty: &DeclaredType, v: &Value) -> ValueError {
        self.err(
            ty,
            ValueProblem::WrongShape {
                found: describe_value(self.kb, v),
            },
        )
    }

    fn value(&mut self, v: &Value, ty: &DeclaredType) -> Result<serde_json::Value, ValueError> {
        use serde_json::Value as J;
        let kb = self.kb;
        let shape = ty.shape(kb).map_err(|p| self.err(ty, p))?;
        if let ViewHead::Var(var) = v.head(kb) {
            return match (var, &shape) {
                (Var::Global(vid), shape) if self.opts.variables && !matches!(shape, TypeShape::Option(_)) => {
                    Ok(J::String(self.variable(vid)))
                }
                _ => Err(self.err(ty, ValueProblem::Variable)),
            };
        }
        match shape {
            TypeShape::String => match v.literal_string(kb) {
                Some(s) => Ok(J::String(self.escape(s))),
                None => Err(self.wrong(ty, v)),
            },
            TypeShape::Bool => v.literal_bool(kb).map(J::Bool).ok_or_else(|| self.wrong(ty, v)),
            TypeShape::Int64 => v
                .literal_int64(kb)
                .map(|n| J::Number(n.into()))
                .ok_or_else(|| self.wrong(ty, v)),
            TypeShape::Float => {
                let f = v.literal_f64(kb).ok_or_else(|| self.wrong(ty, v))?;
                serde_json::Number::from_f64(f).map(J::Number).ok_or_else(|| {
                    self.err(
                        ty,
                        ValueProblem::Unrepresentable {
                            what: format!("the non-finite float {f}"),
                        },
                    )
                })
            }
            TypeShape::BigInt => {
                let n = v.literal_big_int(kb).ok_or_else(|| self.wrong(ty, v))?;
                match (self.opts.big_int, i64::try_from(&n)) {
                    (BigIntSpelling::NumberWhenItFits, Ok(i)) => Ok(J::Number(i.into())),
                    _ => Ok(J::String(n.to_string())),
                }
            }
            TypeShape::Type => type_text(kb, v).map(J::String).map_err(|p| self.err(ty, p)),
            TypeShape::Option(inner) => match v.head(kb) {
                ViewHead::Functor {
                    functor,
                    pos_arity: 0,
                    named_arity: 0,
                } if kb.qualified_name_of(functor) == OPTION_NONE => Ok(J::Null),
                ViewHead::Functor { functor, .. } if kb.qualified_name_of(functor) == OPTION_SOME => {
                    let present = v
                        .named_field(kb, "value")
                        .or_else(|| v.pos_arg(kb, 0))
                        .map(|p| p.to_value())
                        .ok_or_else(|| self.wrong(ty, v))?;
                    match self.value(&present, &inner)? {
                        J::Null => Err(self.err(
                            ty,
                            ValueProblem::Unrepresentable {
                                what: "`some(none())`".to_owned(),
                            },
                        )),
                        json => Ok(json),
                    }
                }
                _ => Err(self.wrong(ty, v)),
            },
            TypeShape::List(elem) => self.list(v, ty, &elem),
            TypeShape::Set(elem) => self.set(v, ty, &elem),
            TypeShape::Map { key, value } => self.map(v, ty, &key, &value),
            TypeShape::Tuple(comps) => self.tuple(v, ty, &comps),
            TypeShape::Data(data) => self.data(v, ty, &data),
        }
    }

    /// A set as the array of its elements, in [`json_order`] and each once, so one set is one
    /// text whatever order its `insert`s were made in or how often one was; with
    /// [`CollectionOrder::AsBuilt`], in the order they were inserted, each time. Read off its
    /// `insert` / `empty` chain; an element's error is at its place in the order the set was
    /// built, the innermost `insert` first. A chain of another operation (`union(s1, s2)`, not
    /// reduced) has no spelling.
    fn set(&mut self, v: &Value, ty: &DeclaredType, elem: &DeclaredType) -> Result<serde_json::Value, ValueError> {
        let kb = self.kb;
        let mut members: Vec<Value> = Vec::new();
        let mut cell = v.clone();
        loop {
            match cell.head(kb) {
                ViewHead::Functor {
                    functor,
                    pos_arity: 0,
                    named_arity: 0,
                } if kb.qualified_name_of(functor) == SET_EMPTY => break,
                ViewHead::Functor { functor, .. } if kb.qualified_name_of(functor) == SET_INSERT => {
                    let (Some(rest), Some(member)) = (operand(kb, &cell, "s", 0), operand(kb, &cell, "x", 1)) else {
                        return Err(self.wrong(ty, &cell));
                    };
                    members.push(member);
                    cell = rest;
                }
                ViewHead::Var(_) => {
                    return Err(self.err(
                        ty,
                        ValueProblem::Unrepresentable {
                            what: "a set with a variable tail".to_owned(),
                        },
                    ))
                }
                _ => return Err(self.wrong(ty, &cell)),
            }
        }
        members.reverse();
        let mut items = Vec::with_capacity(members.len());
        for (i, member) in members.iter().enumerate() {
            items.push(self.at(PathStep::Index(i), |me| me.value(member, elem))?);
        }
        if self.opts.collection_order == CollectionOrder::Canonical {
            items.sort_by(json_order);
            items.dedup();
        }
        Ok(serde_json::Value::Array(items))
    }

    /// A map as the array of its `[key, value]` entries, in [`json_order`] of their keys, so one
    /// map is one text whatever order it was built in; with [`CollectionOrder::AsBuilt`], every
    /// `put` in the order made. Read off a running map's handle (which
    /// carries its own arena) or off its `put` / `empty` chain, where a later `put` of a key
    /// written the same as an earlier one's shadows it. An entry's error is at its place in the
    /// order the map was built, the first `put` first.
    fn map(
        &mut self,
        v: &Value,
        ty: &DeclaredType,
        key: &DeclaredType,
        value: &DeclaredType,
    ) -> Result<serde_json::Value, ValueError> {
        use serde_json::Value as J;
        let kb = self.kb;
        // The entries in the order they were made, each with its place there.
        let entries: Vec<(Value, Value)> = match v {
            Value::Map(handle) => {
                handle.with_body(|body| body.iter().map(|(k, x)| (k.to_value(), x.clone())).collect())
            }
            _ => {
                let mut puts: Vec<(Value, Value)> = Vec::new();
                let mut cell = v.clone();
                loop {
                    match cell.head(kb) {
                        ViewHead::Functor {
                            functor,
                            pos_arity: 0,
                            named_arity: 0,
                        } if kb.qualified_name_of(functor) == MAP_EMPTY => break,
                        ViewHead::Functor { functor, .. } if kb.qualified_name_of(functor) == MAP_PUT => {
                            let (Some(rest), Some(k), Some(x)) = (
                                operand(kb, &cell, "m", 0),
                                operand(kb, &cell, "key", 1),
                                operand(kb, &cell, "value", 2),
                            ) else {
                                return Err(self.wrong(ty, &cell));
                            };
                            puts.push((k, x));
                            cell = rest;
                        }
                        ViewHead::Var(_) => {
                            return Err(self.err(
                                ty,
                                ValueProblem::Unrepresentable {
                                    what: "a map with a variable tail".to_owned(),
                                },
                            ))
                        }
                        _ => return Err(self.wrong(ty, &cell)),
                    }
                }
                puts.reverse();
                puts
            }
        };
        if self.opts.collection_order == CollectionOrder::AsBuilt {
            let mut written = Vec::with_capacity(entries.len());
            for (i, (k, x)) in entries.iter().enumerate() {
                let k = self.at(PathStep::Index(i), |me| me.at(PathStep::Index(0), |me| me.value(k, key)))?;
                let x = self.at(PathStep::Index(i), |me| me.at(PathStep::Index(1), |me| me.value(x, value)))?;
                written.push(J::Array(vec![k, x]));
            }
            return Ok(J::Array(written));
        }
        // The last entry of a key first, so it is the one written.
        let mut written: Vec<(J, J)> = Vec::with_capacity(entries.len());
        let mut spelled: HashSet<String> = HashSet::with_capacity(entries.len());
        for (i, (k, x)) in entries.iter().enumerate().rev() {
            let k = self.at(PathStep::Index(i), |me| me.at(PathStep::Index(0), |me| me.value(k, key)))?;
            if !spelled.insert(k.to_string()) {
                continue;
            }
            let x = self.at(PathStep::Index(i), |me| me.at(PathStep::Index(1), |me| me.value(x, value)))?;
            written.push((k, x));
        }
        written.sort_by(|(a, _), (b, _)| json_order(a, b));
        Ok(J::Array(written.into_iter().map(|(k, x)| J::Array(vec![k, x])).collect()))
    }

    /// With variables on, a string of zero or more `\` and then `?` gains one `\`.
    fn escape(&self, s: String) -> String {
        if self.opts.variables && s.trim_start_matches('\\').starts_with('?') {
            format!("\\{s}")
        } else {
            s
        }
    }

    fn list(&mut self, v: &Value, ty: &DeclaredType, elem: &DeclaredType) -> Result<serde_json::Value, ValueError> {
        let kb = self.kb;
        let mut items = Vec::new();
        let mut cell = v.clone();
        loop {
            match cell.head(kb) {
                ViewHead::Functor {
                    functor,
                    pos_arity: 0,
                    named_arity: 0,
                } if kb.qualified_name_of(functor) == LIST_NIL => break,
                ViewHead::Functor { functor, .. } if kb.qualified_name_of(functor) == LIST_CONS => {
                    let (Some(head), Some(tail)) = (cell.named_field(kb, "head"), cell.named_field(kb, "tail")) else {
                        return Err(self.wrong(ty, &cell));
                    };
                    let (head, tail) = (head.to_value(), tail.to_value());
                    let i = items.len();
                    items.push(self.at(PathStep::Index(i), |me| me.value(&head, elem))?);
                    cell = tail;
                }
                ViewHead::Var(_) => {
                    return Err(self.err(
                        ty,
                        ValueProblem::Unrepresentable {
                            what: "a list with a variable tail".to_owned(),
                        },
                    ))
                }
                _ => return Err(self.wrong(ty, &cell)),
            }
        }
        Ok(serde_json::Value::Array(items))
    }

    fn tuple(&mut self, v: &Value, ty: &DeclaredType, comps: &[(Symbol, DeclaredType)]) -> Result<serde_json::Value, ValueError> {
        let kb = self.kb;
        match v.head(kb) {
            ViewHead::Functor { functor, .. } if Some(functor) == tuple_functor(kb) => {}
            _ => return Err(self.wrong(ty, v)),
        }
        let wider: Vec<String> = v
            .named_keys(kb)
            .into_iter()
            .map(|k| kb.local_name_of(k).to_owned())
            .filter(|k| !comps.iter().any(|(l, _)| kb.local_name_of(*l) == k.as_str()))
            .collect();
        if !wider.is_empty() && self.opts.wider_tuple == WiderTuple::Refuse {
            return Err(self.err(ty, ValueProblem::WiderThanDeclared { labels: wider }));
        }
        if let Some((label, _)) = comps.iter().find(|(l, _)| v.named_field(kb, kb.local_name_of(*l)).is_none()) {
            let name = kb.local_name_of(*label).to_owned();
            return Err(self.err(ty, ValueProblem::MissingField { name }));
        }
        if all_positional(kb, comps) {
            let mut array = Vec::with_capacity(comps.len());
            for (i, (label, cty)) in comps.iter().enumerate() {
                let component = v.named_field(kb, kb.local_name_of(*label)).expect("present").to_value();
                array.push(self.at(PathStep::Index(i), |me| me.value(&component, cty))?);
            }
            return Ok(serde_json::Value::Array(array));
        }
        // A labelled tuple in the VALUE's own order, which is its identity (kernel §4.5): a
        // value conforming to its type in another order is another value, and written in the
        // type's order it would read back as that other one.
        let mut object = serde_json::Map::new();
        for key in v.named_keys(kb) {
            let name = kb.local_name_of(key).to_owned();
            let Some((_, cty)) = comps.iter().find(|(l, _)| kb.local_name_of(*l) == name) else {
                continue; // a wider component, projected away (refused above when asked)
            };
            let component = v.named_arg(kb, key).expect("a key the value holds").to_value();
            let json = self.at(PathStep::Key(name.clone()), |me| me.value(&component, cty))?;
            object.insert(name, json);
        }
        Ok(serde_json::Value::Object(object))
    }

    fn data(&mut self, v: &Value, ty: &DeclaredType, data: &DataShape) -> Result<serde_json::Value, ValueError> {
        let kb = self.kb;
        // At a sort with abstract values a value is its provider's value paired with the
        // provider's dictionary, as an operation body makes it, or the provider's value alone, as
        // a fact holds it: both are written as the provider's value, which is what the dictionary
        // is built from where the value is read back.
        let opened;
        let v = match data.is_abstract().then(|| crate::kb::typing::instance_value_of(kb, v)).flatten() {
            Some(carried) => {
                opened = carried;
                &opened
            }
            None => v,
        };
        let ViewHead::Functor { functor, .. } = v.head(kb) else {
            return Err(self.wrong(ty, v));
        };
        if functor.is_type_face() {
            // A type is not an instance of the type it names.
            return Err(self.wrong(ty, v));
        }
        let Some(ctor) = data.constructors().iter().copied().find(|c| *c == functor) else {
            return Err(self.err(
                ty,
                ValueProblem::UnknownConstructor {
                    name: kb.qualified_name_of(functor).to_owned(),
                    sort: kb.qualified_name_of(data.sort).to_owned(),
                },
            ));
        };
        runtime_account(kb, ctor).map_err(|p| self.err(ty, p))?;
        self.declared_only(v, ctor, ty)?;
        if data.own && self.opts.entity_tags == EntityTags::OmitAtEntityType {
            return Ok(serde_json::Value::Object(self.fields(v, ctor, data, ty)?));
        }
        let tag = tag_of(kb, ctor, self.opts.tag_names);
        // A tag that reads back as two constructors is not written: the reader refuses it. Only
        // two providers' constructors can share one; a sort's own are named apart.
        if data.is_abstract() {
            let tagged = data.tagged(kb, &tag, self.opts.tag_names);
            if tagged.len() > 1 {
                return Err(self.err(ty, ambiguous_tag(kb, &tag, &tagged)));
            }
        }
        if declared_fields(kb, ctor).is_empty() {
            return Ok(serde_json::Value::String(tag));
        }
        let ctor_ty = ty.within(Value::SymbolRef(kb.type_face_of(ctor)));
        let fields = self.at(PathStep::Key(tag.clone()), |me| me.fields(v, ctor, data, &ctor_ty))?;
        // The shorthand, where the one field's encoding is not an object: an object there would
        // read back as the constructor's own fields (021, "Entities and sorts"). A one field
        // omitted (`none()`) leaves the object of no fields, which reads back the same.
        let shorthand = declared_fields(kb, ctor).len() == 1
            && fields.values().next().is_some_and(|json| !json.is_object());
        let payload = if shorthand {
            fields.into_iter().next().map(|(_, json)| json).expect("one field")
        } else {
            serde_json::Value::Object(fields)
        };
        let mut wrapper = serde_json::Map::new();
        wrapper.insert(tag, payload);
        Ok(serde_json::Value::Object(wrapper))
    }

    /// A constructed value holds its constructor's declared fields and nothing else: an argument
    /// beyond them has no place in the object of its fields, and dropping it would write
    /// another value.
    fn declared_only(&self, v: &Value, ctor: Symbol, ty: &DeclaredType) -> Result<(), ValueError> {
        let kb = self.kb;
        let declared = declared_fields(kb, ctor);
        let ViewHead::Functor { pos_arity, .. } = v.head(kb) else {
            return Ok(());
        };
        let extra_named = v
            .named_keys(kb)
            .into_iter()
            .map(|k| kb.local_name_of(k).to_owned())
            .find(|k| !declared.iter().any(|(f, _)| kb.local_name_of(*f) == k.as_str()));
        let extra = match extra_named {
            Some(name) => Some(name),
            None if pos_arity > declared.len() => Some(crate::intern::positional_label(declared.len())),
            None => None,
        };
        match extra {
            Some(name) => Err(self.err(ty, ValueProblem::UnknownField { name })),
            None => Ok(()),
        }
    }

    /// The object of a constructed value's fields, in declared order, each at its declared type
    /// in the type's bindings (`data`); a `none()` `Option` field is omitted.
    fn fields(
        &mut self,
        v: &Value,
        ctor: Symbol,
        data: &DataShape,
        ty: &DeclaredType,
    ) -> Result<serde_json::Map<String, serde_json::Value>, ValueError> {
        let kb = self.kb;
        let mut object = serde_json::Map::new();
        let declared = data.fields(kb, ctor).map_err(|p| self.err(ty, p))?;
        for (i, (field, fty)) in declared.into_iter().enumerate() {
            let name = kb.local_name_of(field).to_owned();
            // A positional application fills the declared fields in order.
            let Some(arg) = v.named_field(kb, &name).or_else(|| v.pos_arg(kb, i)).map(|a| a.to_value()) else {
                return Err(self.err(ty, ValueProblem::MissingField { name }));
            };
            let json = self.at(PathStep::Key(name.clone()), |me| me.value(&arg, &fty))?;
            if json.is_null() && matches!(fty.shape(kb), Ok(TypeShape::Option(_))) {
                continue;
            }
            object.insert(name, json);
        }
        Ok(object)
    }
}

// ── The data file: `meta` + `data` ─────────────────────────────

/// The file extensions this module can read: [`load_toml`] and [`load_json`].
///
/// Exported because whatever NAMES data files must key off the same list. The
/// CLI builds its conventional `anthill.{ext}` names from it (WI-746), so a
/// format it looks for is always one there is a reader for, and a format there
/// is a reader for is always one it looks for.
pub const DATA_EXTENSIONS: [&str; 2] = ["toml", "json"];

/// Load the rows of a TOML data file into the KB as facts of `domain`. Returns the number of
/// facts loaded; every row's error is reported, not only the first.
pub fn load_toml(
    kb: &mut KnowledgeBase,
    source: &str,
    domain: Symbol,
) -> Result<usize, Vec<SerError>> {
    let toml_val: toml::Value =
        toml::from_str(source).map_err(|e| vec![SerError::Format(e.to_string())])?;
    let mut nonfinite = Vec::new();
    let json_val = toml_to_json(toml_val, &mut Vec::new(), &mut nonfinite);
    load_value(kb, json_val, domain, &nonfinite)
}

/// Load the rows of a JSON data file into the KB as facts of `domain`. Returns the number of
/// facts loaded; every row's error is reported, not only the first.
pub fn load_json(
    kb: &mut KnowledgeBase,
    source: &str,
    domain: Symbol,
) -> Result<usize, Vec<SerError>> {
    let json_val: serde_json::Value =
        serde_json::from_str(source).map_err(|e| vec![SerError::Format(e.to_string())])?;
    load_value(kb, json_val, domain, &[])
}

/// Write the facts `rule_ids` as one TOML envelope whose `meta.entity` is `entity`, a
/// constructor's NAME. A constructor applied to type arguments is written by
/// [`serialize_toml_at`], which takes its type.
pub fn serialize_toml(kb: &KnowledgeBase, entity: &str, rule_ids: &[RuleId]) -> Result<String, SerError> {
    to_toml_text(&facts_to_value(kb, &row_type_by_name(kb, entity)?, rule_ids)?)
}

/// Write the facts `rule_ids` as one JSON envelope whose `meta.entity` is `entity`, a
/// constructor's NAME. A constructor applied to type arguments is written by
/// [`serialize_json_at`], which takes its type.
pub fn serialize_json(kb: &KnowledgeBase, entity: &str, rule_ids: &[RuleId]) -> Result<String, SerError> {
    to_json_text(&facts_to_value(kb, &row_type_by_name(kb, entity)?, rule_ids)?)
}

/// [`serialize_toml`] at a constructor's TYPE (`test.Box[T = Int64]`, from [`type_from_text`]
/// or the KB), written as `meta.entity` by its text ([`type_to_text`]).
pub fn serialize_toml_at(kb: &KnowledgeBase, entity: &impl TermView, rule_ids: &[RuleId]) -> Result<String, SerError> {
    to_toml_text(&facts_to_value(kb, &row_type_at(kb, owned(entity))?, rule_ids)?)
}

/// [`serialize_json`] at a constructor's TYPE (`test.Box[T = Int64]`, from [`type_from_text`]
/// or the KB), written as `meta.entity` by its text ([`type_to_text`]).
pub fn serialize_json_at(kb: &KnowledgeBase, entity: &impl TermView, rule_ids: &[RuleId]) -> Result<String, SerError> {
    to_json_text(&facts_to_value(kb, &row_type_at(kb, owned(entity))?, rule_ids)?)
}

fn to_json_text(v: &serde_json::Value) -> Result<String, SerError> {
    serde_json::to_string_pretty(v).map_err(|e| SerError::Format(e.to_string()))
}

fn to_toml_text(v: &serde_json::Value) -> Result<String, SerError> {
    let toml_val = json_to_toml(v).map_err(|e| SerError::Format(format!("TOML conversion: {e}")))?;
    toml::to_string_pretty(&toml_val).map_err(|e| SerError::Format(e.to_string()))
}

/// The constructor a section's rows are, and the type that types its fields.
struct RowType {
    /// `meta.entity` as it is written.
    entity: String,
    ctor: Symbol,
    ty: DeclaredType,
    data: DataShape,
}

/// A `meta.entity` NAME: read by THE NAME LADDER AT `<global>` (WI-912), the question a
/// host-supplied extent-owner name asks (WI-908). A data file is KB-external text written in
/// no scope, so it gets the same reading and the same three refusals: absent, ambiguous, or
/// hidden by `internal`; and a constructor reserved to the runtime is refused. There is NO
/// short-name fallback: `a.b.Rec`, declared nowhere, does not load onto a top-level `Rec`.
fn resolve_entity_functor(kb: &KnowledgeBase, name: &str) -> Result<Symbol, SerError> {
    let sym = match kb.resolve_name_in_global(name) {
        ResolveResult::Found(sym) => sym,
        ResolveResult::Ambiguous(cands, contested) => {
            return Err(SerError::AmbiguousName {
                name: name.to_owned(),
                candidates: kb.candidate_names(&cands),
                contested,
            })
        }
        ResolveResult::NotFound => {
            return Err(match kb.hidden_internal_in_global(name) {
                Some(declared_in) => SerError::ForbiddenInternalEntity {
                    entity: name.to_owned(),
                    declared_in,
                },
                None => SerError::UnknownEntity(name.to_owned()),
            })
        }
    };
    if kb.runtime_account_of(sym).is_some() {
        return Err(SerError::RuntimeAccount(kb.qualified_name_of(sym).to_string()));
    }
    // A MISS IS FATAL (WI-926): a name that declares no fields — a sort with several
    // constructors — has no row shape, and reading against an empty schema is a different
    // reconstruction, not a degraded one.
    if kb.entity_field_names(sym).is_none() {
        return Err(SerError::NoFieldSchema {
            entity: name.to_owned(),
            constructors: kb
                .constructors_of_sort(sym)
                .iter()
                .map(|c| kb.qualified_name_of(*c).to_string())
                .collect(),
        });
    }
    Ok(sym)
}

/// The row type of a constructor NAME: the constructor's type, its parameters at their
/// defaults.
fn row_type_by_name(kb: &KnowledgeBase, entity: &str) -> Result<RowType, SerError> {
    if entity.contains('[') {
        return Err(SerError::Format(format!(
            "meta.entity '{entity}' applies its constructor to type arguments; a writer is given \
             that type as a term (`serialize_json_at`, `serialize_toml_at`)"
        )));
    }
    let ctor = resolve_entity_functor(kb, entity)?;
    row_type(kb, entity.to_owned(), ctor, Value::SymbolRef(kb.type_face_of(ctor)))
}

/// The row type of a constructor's TYPE: the type's head names the constructor.
fn row_type_at(kb: &KnowledgeBase, ty: Value) -> Result<RowType, SerError> {
    let entity = type_to_text(kb, &ty).map_err(|error| SerError::EntityType {
        entity: describe_value(kb, &ty),
        error,
    })?;
    let head = match ty.head(kb) {
        ViewHead::Functor { functor, .. } => functor.plain(),
        _ => {
            return Err(SerError::UnknownEntity(entity));
        }
    };
    let ctor = resolve_entity_functor(kb, kb.qualified_name_of(head))?;
    row_type(kb, entity, ctor, ty)
}

/// The row type of a `meta.entity` as a data file writes it: a NAME, or a name applied to
/// type arguments (`test.Box[T = anthill.prelude.Int64]`), read as a type.
fn row_type_of_text(kb: &mut KnowledgeBase, entity: &str) -> Result<RowType, SerError> {
    let Some((name, _)) = entity.split_once('[') else {
        return row_type_by_name(kb, entity);
    };
    let ctor = resolve_entity_functor(kb, name.trim())?;
    let entity_error = |error| SerError::EntityType {
        entity: entity.to_owned(),
        error,
    };
    let ty = type_from_text(kb, entity).map_err(entity_error)?;
    row_type(kb, entity.to_owned(), ctor, Value::term(ty))
}

fn row_type(kb: &KnowledgeBase, entity: String, ctor: Symbol, view: Value) -> Result<RowType, SerError> {
    let ty = DeclaredType::closed(&view);
    let refused = |problem| SerError::EntityType {
        entity: entity.clone(),
        error: ValueError {
            path: JsonPath::default(),
            expected: kb.qualified_name_of(ctor).to_owned(),
            problem,
        },
    };
    match ty.shape(kb).map_err(refused)? {
        // The row's constructor is the one `meta.entity` names, even at a type that admits
        // others beside it (`sort Mix { entity Mix(…)  entity Other }`).
        TypeShape::Data(data) if data.constructors().contains(&ctor) => Ok(RowType {
            entity,
            ctor,
            ty,
            data,
        }),
        _ => Err(refused(ValueProblem::WrongShape {
            found: format!("the type {}", describe_value(kb, &ty.view)),
        })),
    }
}

/// Core deserializer: serde_json::Value → KB facts. `nonfinite` are the places of the TOML
/// floats with no JSON value, from the file's root.
fn load_value(
    kb: &mut KnowledgeBase,
    value: serde_json::Value,
    domain: Symbol,
    nonfinite: &[(Vec<PathStep>, f64)],
) -> Result<usize, Vec<SerError>> {
    let obj = match value {
        serde_json::Value::Object(map) => map,
        _ => {
            return Err(vec![SerError::Format(
                "top-level value must be an object".into(),
            )])
        }
    };

    // Check for single-section (meta + data) vs multi-section layout
    if obj.contains_key("meta") && obj.contains_key("data") {
        load_section(kb, &obj, domain, &[], nonfinite)
    } else {
        // Multi-section: each key is a section with .meta + .data
        let mut total = 0;
        let mut errors = Vec::new();
        for (section_name, section_val) in &obj {
            match section_val {
                serde_json::Value::Object(section_map) => {
                    let at = [PathStep::Key(section_name.clone())];
                    match load_section(kb, section_map, domain, &at, nonfinite) {
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

/// Load a single section: expects "meta" and "data" keys. Each row is the object of the
/// fields of the constructor `meta.entity` names, untagged since `meta.entity` names it,
/// decoded with variables on in its own variable scope, and asserted as a FACT (WI-922),
/// unlabeled: a data file's rows are a program's, read back (WI-20261121-G8E02).
fn load_section(
    kb: &mut KnowledgeBase,
    obj: &serde_json::Map<String, serde_json::Value>,
    domain: Symbol,
    at: &[PathStep],
    nonfinite: &[(Vec<PathStep>, f64)],
) -> Result<usize, Vec<SerError>> {
    let meta = obj
        .get("meta")
        .ok_or_else(|| vec![SerError::MissingMeta("section has no 'meta' key".into())])?;
    let entity = meta
        .get("entity")
        .and_then(|v| v.as_str())
        .ok_or_else(|| vec![SerError::MissingMeta("meta.entity must be a string".into())])?;
    let row = row_type_of_text(kb, entity).map_err(|e| vec![e])?;

    let data = obj
        .get("data")
        .ok_or_else(|| vec![SerError::MissingMeta("section has no 'data' key".into())])?;
    let entries: Vec<(Option<usize>, &serde_json::Value)> = match data {
        serde_json::Value::Array(arr) => arr.iter().enumerate().map(|(i, e)| (Some(i), e)).collect(),
        serde_json::Value::Object(_) => vec![(None, data)],
        _ => {
            return Err(vec![SerError::Format(
                "data must be an array or object".into(),
            )])
        }
    };

    let mut count = 0;
    let mut errors = Vec::new();
    for (index, entry) in entries {
        // A row is an object: with variables on, `data = ["?row"]` would otherwise be a row
        // holding a variable, of no constructor at all.
        let mut decoder = Decoder::new(kb, CodecOptions::data_file());
        // The places, under this row, of the floats TOML holds and JSON does not.
        let mut place: Vec<PathStep> = at.to_vec();
        place.push(PathStep::Key("data".to_owned()));
        place.extend(index.map(PathStep::Index));
        decoder.nonfinite = nonfinite
            .iter()
            .filter_map(|(p, f)| p.strip_prefix(place.as_slice()).map(|rest| (rest.to_vec(), *f)))
            .collect();
        let decoded = match entry.as_object() {
            Some(fields) => decoder.fields(row.ctor, &row.data, fields, &row.ty),
            None => Err(decoder.err(
                &row.ty,
                ValueProblem::WrongShape {
                    found: describe_json(entry),
                },
            )),
        };
        match decoded {
            Ok(term) => {
                kb.assert_fact(term, ClauseKind::Fact, domain, None, crate::kb::ClauseLabel::Runtime);
                count += 1;
            }
            Err(error) => errors.push(SerError::Row { index, error }),
        }
    }

    if errors.is_empty() {
        Ok(count)
    } else {
        Err(errors)
    }
}

/// Core serializer: KB facts → serde_json::Value. Each fact is a row of the row type's
/// constructor, written as the object of its fields; a fact of another constructor is
/// refused.
fn facts_to_value(kb: &KnowledgeBase, row: &RowType, rule_ids: &[RuleId]) -> Result<serde_json::Value, SerError> {
    let mut data = Vec::with_capacity(rule_ids.len());
    for (index, &rid) in rule_ids.iter().enumerate() {
        let head = Value::term(kb.rule_head(rid));
        let mut encoder = Encoder::new(kb, CodecOptions::data_file(), &head);
        let refused = |encoder: &Encoder, problem| SerError::Row {
            index: Some(index),
            error: encoder.err(&row.ty, problem),
        };
        match head.head(kb) {
            ViewHead::Functor { functor, .. } if functor == row.ctor => {}
            ViewHead::Functor { functor, .. } => {
                return Err(refused(
                    &encoder,
                    ValueProblem::UnknownConstructor {
                        name: kb.qualified_name_of(functor).to_owned(),
                        sort: kb.qualified_name_of(row.ctor).to_owned(),
                    },
                ))
            }
            _ => {
                return Err(refused(
                    &encoder,
                    ValueProblem::WrongShape {
                        found: describe_value(kb, &head),
                    },
                ))
            }
        }
        encoder
            .declared_only(&head, row.ctor, &row.ty)
            .map_err(|error| SerError::Row {
                index: Some(index),
                error,
            })?;
        let fields = encoder
            .fields(&head, row.ctor, &row.data, &row.ty)
            .map_err(|error| SerError::Row {
                index: Some(index),
                error,
            })?;
        data.push(serde_json::Value::Object(fields));
    }

    let mut meta = serde_json::Map::new();
    meta.insert("entity".into(), serde_json::Value::String(row.entity.clone()));
    let mut result = serde_json::Map::new();
    result.insert("meta".into(), serde_json::Value::Object(meta));
    let data = if data.len() == 1 {
        data.pop().expect("one row")
    } else {
        serde_json::Value::Array(data)
    };
    result.insert("data".into(), data);
    Ok(serde_json::Value::Object(result))
}

// ── TOML ↔ JSON ───────────────────────────────────────────────

/// TOML as the JSON the mapping reads. A TOML `nan` or `inf` has no JSON value: its place is
/// recorded in `nonfinite` and the JSON holds `null` there, which the row's decoder never
/// reads, refusing the float at its place instead. So it is the error of its row, beside the
/// other rows' (021: every row's error is reported). It used to become a `null` that was
/// read, so `f = nan` under `Option[T = Float]` loaded as `none()`.
fn toml_to_json(
    val: toml::Value,
    path: &mut Vec<PathStep>,
    nonfinite: &mut Vec<(Vec<PathStep>, f64)>,
) -> serde_json::Value {
    match val {
        toml::Value::String(s) => serde_json::Value::String(s),
        toml::Value::Integer(n) => serde_json::Value::Number(n.into()),
        toml::Value::Float(f) => match serde_json::Number::from_f64(f) {
            Some(n) => serde_json::Value::Number(n),
            None => {
                nonfinite.push((path.clone(), f));
                serde_json::Value::Null
            }
        },
        toml::Value::Boolean(b) => serde_json::Value::Bool(b),
        toml::Value::Datetime(dt) => serde_json::Value::String(dt.to_string()),
        toml::Value::Array(arr) => {
            let mut items = Vec::with_capacity(arr.len());
            for (i, v) in arr.into_iter().enumerate() {
                path.push(PathStep::Index(i));
                items.push(toml_to_json(v, path, nonfinite));
                path.pop();
            }
            serde_json::Value::Array(items)
        }
        toml::Value::Table(tbl) => {
            let mut map = serde_json::Map::new();
            for (k, v) in tbl {
                path.push(PathStep::Key(k.clone()));
                map.insert(k.clone(), toml_to_json(v, path, nonfinite));
                path.pop();
            }
            serde_json::Value::Object(map)
        }
    }
}

/// A non-finite float as TOML writes it.
fn toml_float_text(f: f64) -> &'static str {
    match (f.is_nan(), f > 0.0) {
        (true, _) => "nan",
        (false, true) => "inf",
        (false, false) => "-inf",
    }
}

fn json_to_toml(val: &serde_json::Value) -> Result<toml::Value, String> {
    match val {
        // WI-501: TOML has no null. A `none()` field is omitted (an absent field reloads as
        // none), so the only null that arrives is a `none()` where nothing can be omitted — a
        // list element, a tuple component — which TOML cannot represent. (Use JSON for it.)
        serde_json::Value::Null => Err(
            "cannot serialize a none()/null inside a list or a tuple to TOML (TOML has no \
             null); use JSON for this entity"
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
