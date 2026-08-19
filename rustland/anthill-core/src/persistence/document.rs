//! The item DOCUMENT format: an `## Attributes` chapter of data, then prose.
//!
//! Specification: `rustland/anthill-todo/docs/design/document-mapping.md`. That
//! file is normative; this module implements it and the section numbers below
//! cite it. It replaces the fenced-head encoding WI-1120 shipped, whose head was
//! ONE physical line per item — the thing that made two agents editing two
//! different fields of one item conflict in git.
//!
//! ````markdown
//! ## Attributes                                  <- the item's fact, as data
//!
//! - id: WI-1121
//!
//! - status: Delivered
//! - status_agent: claude                         <- adjacent: one FieldGroup
//! - status_at: 2026-08-18T15:28:08Z
//!
//! ## Description                                 <- a prose FIELD chapter
//!
//! anthill-todo backend …
//!
//! ## Changes                                     <- a CONTAINER
//!
//! ### 2026-08-17T09:19:35Z — feedback — user     <- an ENTRY
//!
//! id should be minted from content …
//! ````
//!
//! ## What is data and what is prose
//!
//! Everything in the attributes chapter is DATA: one line per field, spelled by
//! that field's DECLARED TYPE (§3.2), with a backticked anthill term as the
//! total escape so the writer never has to refuse a value. Everything in a field
//! chapter or an entry is PROSE, carried verbatim.
//!
//! The consequence is that this module reads the domain's entity declarations —
//! a [`DomainSchema`] — alongside the mapping. That is a real departure from the
//! fenced-head encoding, which never learned the schema because the head was
//! anthill source the parser handled. It is stated here rather than buried:
//! spelling a value BY ITS TYPE is what removes the second scalar language, and
//! a type-directed spelling needs the types.
//!
//! ## Blank lines are load-bearing
//!
//! Measured on git 3-way merges: two edited lines with NOTHING between them
//! conflict; with one unchanged line between them they merge. So a blank line
//! between two fields declares "these change independently" and adjacency
//! declares "these change together" — which is what [`FieldGroupSpec`] states,
//! and why the separator is a rule rather than a style (§3.3).

use std::collections::HashMap;
use std::fmt;
use std::ops::Range;

use crate::kb::term::{Literal, Term, TermId};
use crate::kb::typing::get_named_arg;
use crate::kb::KnowledgeBase;

use super::print;

// ── The declared mapping (§5) ──────────────────────────────────

/// Fields written ADJACENT, with no blank line between them (§3.3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldGroupSpec {
    pub functor: String,
    pub fields: Vec<String>,
}

/// A bare scalar `s` in a position of `sort` denotes `constructor(slot: s)`.
/// `ScalarForm(sort: AcceptanceCriterion, constructor: ToolPasses, slot: "tool")`
/// is what lets `- acceptance: cargo-test` mean a `ToolPasses`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarFormSpec {
    pub sort: String,
    pub constructor: String,
    pub slot: String,
}

/// A prose field of the item's own fact: one chapter, fixed heading (§4.2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChapterSpec {
    pub functor: String,
    pub field: String,
    pub named: String,
}

/// A repeated satellite WITH prose: one container, one entry per fact (§4.3).
///
/// `key` is filled from the item's own `id` and is never written in the
/// document — an entry in this file is about this item, so writing the key
/// would be 1173 repetitions of what the file already says (§1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChapterGroupSpec {
    pub functor: String,
    /// Several groups may share one container.
    pub container: String,
    /// The word discriminating this group's entries, written in every heading
    /// after the first field. A container holding one kind still writes it, so
    /// that a second kind is additive rather than a fourth rewrite of the tree.
    pub kind: String,
    pub key: String,
    /// Fields carried by the entry heading, in order.
    pub heading: Vec<String>,
    /// The field carried by the entry body.
    pub field: String,
}

/// A repeated satellite WITHOUT prose: one attributes field holding a list, one
/// fact per element (§3.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatelliteListSpec {
    pub functor: String,
    /// The attributes field the list is written as.
    pub named: String,
    /// The field each element fills.
    pub field: String,
    pub key: String,
}

/// A RECORD-VALUED field written as SIBLING attribute lines rather than as one
/// nested value.
///
/// The attributes chapter is one line per datum, and a nested record has no data
/// spelling — written whole it would land as a single backticked term, which is
/// the one long line this format exists to break up. Flattening is what lets a
/// `StatusChange` be a record in the domain and four independently mergeable
/// lines on the page.
///
/// THE NAMING RULE, and its one deliberate exception: the record's FIRST
/// declared field takes `prefix` as its whole name, every other field takes
/// `<prefix>_<field>`. The exception is there because the first field is the
/// record's HEADLINE — the value the directory mirrors and §10 checks the path
/// against — and `status_status` is not a name anyone would write.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatRecordSpec {
    pub functor: String,
    /// The record-valued field of `functor`.
    pub field: String,
    /// The attribute name its first field takes.
    pub prefix: String,
}

/// One line the attributes chapter can hold: its key, the declared type of the
/// value it carries, and the PATH from the fact to that value.
///
/// The path is one segment for an ordinary field and two for a flattened
/// record's, which is the whole of what flattening costs every reader of this
/// list: everything else — chapters, field groups, value spelling, the
/// well-formedness checks — sees a flat functor and does not know a record is
/// involved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttrSlot {
    pub name: String,
    pub ty: FieldType,
    pub path: Vec<String>,
    /// The record constructor to rebuild, for a flattened slot.
    pub record: Option<String>,
}

/// The whole declared mapping, plus the schema its value spelling reads.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DocumentMapping {
    /// `DocumentFormat(level:)` — the first structural level. Chapters and
    /// containers sit here and a container's entries at `level + 1`.
    pub level: usize,
    /// `DocumentFormat(attributes:)` — the chapter holding the item's own fact.
    pub attributes: String,
    pub field_groups: Vec<FieldGroupSpec>,
    pub scalar_forms: Vec<ScalarFormSpec>,
    pub chapters: Vec<ChapterSpec>,
    pub groups: Vec<ChapterGroupSpec>,
    pub lists: Vec<SatelliteListSpec>,
    pub flat_records: Vec<FlatRecordSpec>,
    pub schema: DomainSchema,
}

impl DocumentMapping {
    /// The functor whose fact the attributes chapter holds.
    ///
    /// DERIVED, not declared, and the derivation is the well-formedness rule
    /// [`Self::check`] enforces: it is the one functor a `Chapter` or
    /// `FieldGroup` names and no `ChapterGroup` or `SatelliteList` does. A
    /// satellite has a home of its own; the item's fact is what is left.
    pub fn item_functor(&self) -> Option<&str> {
        let mut found: Option<&str> = None;
        let named = self
            .chapters
            .iter()
            .map(|c| c.functor.as_str())
            .chain(self.field_groups.iter().map(|g| g.functor.as_str()))
            .chain(self.flat_records.iter().map(|r| r.functor.as_str()));
        for f in named {
            if self.satellite_for(f).is_some() {
                continue;
            }
            match found {
                Some(seen) if seen != f => return None,
                _ => found = Some(f),
            }
        }
        found
    }

    /// The lines the attributes chapter can hold for one functor, in DECLARED
    /// order, with each `FlatRecord` field replaced in place by its record's own
    /// fields under their flattened names.
    ///
    /// THIS IS THE ONLY PLACE FLATTENING EXISTS. Every other reader of a
    /// functor's fields goes through here and sees a flat list, so `Chapter`,
    /// `FieldGroup`, the value spelling and the well-formedness checks are all
    /// written against flattened names and none of them knows a record is
    /// involved.
    pub fn attribute_slots(&self, functor: &str) -> Vec<AttrSlot> {
        let Some(schema) = self.schema.functor(functor) else {
            return Vec::new();
        };
        let mut out = Vec::with_capacity(schema.fields.len());
        for field in &schema.fields {
            let flat = self
                .flat_records
                .iter()
                .find(|r| r.functor == functor && r.field == field.name);
            let Some(flat) = flat else {
                out.push(AttrSlot {
                    name: field.name.clone(),
                    ty: field.ty.clone(),
                    path: vec![field.name.clone()],
                    record: None,
                });
                continue;
            };
            // The record's own declaration decides which lines appear and in
            // what order, so a field added to the record shows up here with
            // nothing else to change.
            let FieldType::Named(record) = &field.ty else {
                continue;
            };
            let Some(inner) = self.schema.functor(record) else {
                continue;
            };
            for (i, f) in inner.fields.iter().enumerate() {
                out.push(AttrSlot {
                    name: if i == 0 {
                        flat.prefix.clone()
                    } else {
                        format!("{}_{}", flat.prefix, f.name)
                    },
                    ty: f.ty.clone(),
                    path: vec![field.name.clone(), f.name.clone()],
                    record: Some(record.clone()),
                });
            }
        }
        out
    }

    /// The slot one attribute key names, if any.
    pub fn slot_of(&self, functor: &str, key: &str) -> Option<AttrSlot> {
        self.attribute_slots(functor).into_iter().find(|s| s.name == key)
    }

    pub fn chapter_for(&self, functor: &str) -> Option<&ChapterSpec> {
        self.chapters.iter().find(|c| c.functor == functor)
    }

    pub fn group_for(&self, functor: &str) -> Option<&ChapterGroupSpec> {
        self.groups.iter().find(|g| g.functor == functor)
    }

    pub fn list_for(&self, functor: &str) -> Option<&SatelliteListSpec> {
        self.lists.iter().find(|l| l.functor == functor)
    }

    /// Whether this functor is a satellite — a repeated fact keyed to the item,
    /// with a home of its own rather than a line in the attributes chapter.
    fn satellite_for(&self, functor: &str) -> Option<()> {
        (self.group_for(functor).is_some() || self.list_for(functor).is_some()).then_some(())
    }

    fn field_chapter_named(&self, name: &str) -> Option<&ChapterSpec> {
        self.chapters.iter().find(|c| c.named == name)
    }

    fn container_named(&self, name: &str) -> bool {
        self.groups.iter().any(|g| g.container == name)
    }

    fn group_of(&self, container: &str, kind: &str) -> Option<&ChapterGroupSpec> {
        self.groups
            .iter()
            .find(|g| g.container == container && g.kind == kind)
    }

    fn list_named(&self, name: &str) -> Option<&SatelliteListSpec> {
        self.lists.iter().find(|l| l.named == name)
    }

    fn scalar_form(&self, sort: &str) -> Option<&ScalarFormSpec> {
        self.scalar_forms.iter().find(|s| s.sort == sort)
    }

    /// The group a field belongs to, and its position in it.
    fn group_of_field(&self, functor: &str, field: &str) -> Option<&FieldGroupSpec> {
        self.field_groups
            .iter()
            .find(|g| g.functor == functor && g.fields.iter().any(|f| f == field))
    }

    /// Where a chapter sits in the writer's canonical order: the attributes
    /// chapter, then field chapters in declaration order, then containers.
    ///
    /// A NEW chapter is inserted at its rank rather than appended, so a file
    /// that gains a `## Reason` gets it above `## Changes` and not below.
    pub fn rank_of(&self, kind: &SegmentKind) -> usize {
        match kind {
            SegmentKind::Attributes => 0,
            SegmentKind::Field { name } => self
                .chapters
                .iter()
                .position(|c| c.named == *name)
                .map(|i| 1 + i)
                .unwrap_or(usize::MAX - 1),
            SegmentKind::Container { name } | SegmentKind::Entry { container: name, .. } => self
                .groups
                .iter()
                .position(|g| g.container == *name)
                .map(|i| 1 + self.chapters.len() + i)
                .unwrap_or(usize::MAX - 1),
            SegmentKind::Unread { .. } => usize::MAX,
        }
    }

    /// §5.1 — a mapping that loads wrong silently produces documents that lose
    /// data, so every rule that can be checked from the declaration alone is
    /// checked when it is read.
    pub fn check(&self) -> Result<(), String> {
        if self.level == 0 {
            return Err("no `fact DocumentFormat(level:)`, so there is no structural level for \
                        a chapter heading to sit at"
                .to_string());
        }
        if self.attributes.is_empty() {
            return Err("no `fact DocumentFormat(attributes:)`, so no chapter holds a \
                        document's own fact"
                .to_string());
        }
        let Some(item) = self.item_functor() else {
            return Err(
                "the attributes functor is the one a `Chapter` or `FieldGroup` names and no \
                 `ChapterGroup` or `SatelliteList` does; this mapping names none, or several"
                    .to_string(),
            );
        };

        // A flattened record must BE a record, and its expanded names must not
        // shadow a field the functor already has — a shadowed field would be
        // silently unwritable, which is exactly the failure §5.1 exists for.
        for r in &self.flat_records {
            let Some(FieldType::Named(record)) = self.schema.field_type(&r.functor, &r.field)
            else {
                return Err(format!(
                    "`{}.{}` is flattened but is not a record-valued field",
                    r.functor, r.field
                ));
            };
            if self.schema.functor(&record).is_none() {
                return Err(format!(
                    "`{}.{}` is flattened but `{record}` declares no fields",
                    r.functor, r.field
                ));
            }
            let slots = self.attribute_slots(&r.functor);
            for (i, s) in slots.iter().enumerate() {
                if slots[..i].iter().any(|o| o.name == s.name) {
                    return Err(format!(
                        "flattening `{}.{}` produces the attribute `{}`, which `{}` already \
                         has — one name, two values",
                        r.functor, r.field, s.name, r.functor
                    ));
                }
            }
        }

        // Names are unique: no two chapters or containers share a name, and no
        // two groups of one container share a kind.
        let mut names: Vec<&str> = vec![self.attributes.as_str()];
        for c in &self.chapters {
            if names.contains(&c.named.as_str()) {
                return Err(format!("two chapters are named `{}`", c.named));
            }
            names.push(&c.named);
        }
        for g in &self.groups {
            if self.chapters.iter().any(|c| c.named == g.container) || g.container == self.attributes
            {
                return Err(format!(
                    "`{}` is both a chapter and a container",
                    g.container
                ));
            }
        }
        for (i, g) in self.groups.iter().enumerate() {
            if self.groups[..i]
                .iter()
                .any(|o| o.container == g.container && o.kind == g.kind)
            {
                return Err(format!(
                    "two groups of `{}` share the kind `{}`",
                    g.container, g.kind
                ));
            }
            if g.heading.is_empty() {
                return Err(format!(
                    "`{}`'s heading names no field, and the kind is written \"after the \
                     first\" — which is undefined with no first",
                    g.functor
                ));
            }
            // Only the LAST heading field may hold free text: a heading is split
            // from the left, so every earlier field must be one the separator
            // cannot occur in. Checked HERE, once, rather than per value.
            let free = free_text_field(g.heading.len());
            for (i, field) in g.heading.iter().enumerate() {
                if free == Some(i) {
                    continue;
                }
                let ty = self.schema.field_type(&g.functor, field);
                if !matches!(ty, Some(FieldType::Text)) {
                    continue;
                }
                if !self.schema.is_machine_field(&g.functor, field) {
                    return Err(format!(
                        "`{}.{field}` is free text before the last heading position; a heading \
                         is split from the left, so only its LAST field may hold text carrying \
                         the separator",
                        g.functor
                    ));
                }
            }
            self.check_covers(&g.functor, {
                let mut homes = vec![g.key.clone(), g.field.clone()];
                homes.extend(g.heading.iter().cloned());
                homes
            })?;
        }
        for l in &self.lists {
            self.check_covers(&l.functor, vec![l.key.clone(), l.field.clone()])?;
            if self.slot_of(item, &l.named).is_some() {
                return Err(format!(
                    "`{}` writes the attributes field `{}`, which is also a field of `{item}`",
                    l.functor, l.named
                ));
            }
        }
        // No field has two homes: a field named by a `Chapter` may not also
        // appear in the attributes chapter, and no field may be named twice.
        for (i, c) in self.chapters.iter().enumerate() {
            if self.chapters[..i]
                .iter()
                .any(|o| o.functor == c.functor && o.field == c.field)
            {
                return Err(format!(
                    "`{}.{}` is given two chapters",
                    c.functor, c.field
                ));
            }
            if self.slot_of(&c.functor, &c.field).is_none() {
                return Err(format!(
                    "`{}` has no field `{}`, so no chapter can hold it",
                    c.functor, c.field
                ));
            }
        }
        // `FieldGroup` names real attributes, in no other group.
        for (i, g) in self.field_groups.iter().enumerate() {
            for f in &g.fields {
                if self.slot_of(&g.functor, f).is_none() {
                    return Err(format!("`{}` has no field `{f}` to group", g.functor));
                }
                if self
                    .chapters
                    .iter()
                    .any(|c| c.functor == g.functor && c.field == *f)
                {
                    return Err(format!(
                        "`{}.{f}` is a chapter, so it is not written in the attributes \
                         chapter and cannot be grouped with what is",
                        g.functor
                    ));
                }
                if self.field_groups[..i]
                    .iter()
                    .any(|o| o.functor == g.functor && o.fields.contains(f))
                {
                    return Err(format!("`{}.{f}` is in two field groups", g.functor));
                }
            }
        }
        Ok(())
    }

    /// Every field of a mapped satellite has exactly one home. A field with no
    /// home is silently dropped on write — the failure this rule exists for.
    fn check_covers(&self, functor: &str, homes: Vec<String>) -> Result<(), String> {
        let Some(schema) = self.schema.functor(functor) else {
            return Err(format!(
                "`{functor}` is mapped but this domain declares no such entity, so its fields \
                 cannot be checked for a home"
            ));
        };
        for (i, h) in homes.iter().enumerate() {
            if homes[..i].contains(h) {
                return Err(format!("`{functor}.{h}` is named twice by its mapping"));
            }
            if schema.fields.iter().all(|f| f.name != *h) {
                return Err(format!("`{functor}` has no field `{h}`"));
            }
        }
        for f in &schema.fields {
            if !homes.contains(&f.name) {
                return Err(format!(
                    "`{functor}.{}` has no home in the document; a field with no home is \
                     dropped on write",
                    f.name
                ));
            }
        }
        Ok(())
    }
}

// ── The domain schema a value's spelling is read against (§3.2) ─

/// How a field's value is written. Derived from the declared type: this is what
/// makes `- status: Delivered` a variant and `- created: 2026-…` a string
/// without a second scalar language to tell them apart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldType {
    /// `String` — the text, unquoted.
    Text,
    /// `Int64` — the digits.
    Int,
    Bool,
    /// A declared sort: an enum with no payload writes the variant name, and a
    /// sort with a `ScalarForm` writes the scalar.
    Named(String),
    List(Box<FieldType>),
    Option(Box<FieldType>),
    /// Anything with no data spelling — `Term`, an arrow, a tuple. Only the
    /// backticked term spelling applies.
    Opaque,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldSchema {
    pub name: String,
    pub ty: FieldType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctorSchema {
    pub name: String,
    /// In DECLARED order, which is the order the writer writes them (§3.3).
    pub fields: Vec<FieldSchema>,
}

/// The entity and enum declarations of the mapped domain.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DomainSchema {
    pub functors: Vec<FunctorSchema>,
    /// Enum sort → its variants, each with whether it carries fields. Only a
    /// payload-free variant has a bare spelling.
    pub enums: Vec<(String, Vec<(String, bool)>)>,
}

impl DomainSchema {
    pub fn functor(&self, name: &str) -> Option<&FunctorSchema> {
        self.functors.iter().find(|f| f.name == name)
    }

    pub fn field_type(&self, functor: &str, field: &str) -> Option<FieldType> {
        self.functor(functor)?
            .fields
            .iter()
            .find(|f| f.name == field)
            .map(|f| f.ty.clone())
    }

    fn variants(&self, sort: &str) -> Option<&[(String, bool)]> {
        self.enums
            .iter()
            .find(|(n, _)| n == sort)
            .map(|(_, v)| v.as_slice())
    }

    /// Whether a `String` field is MACHINE-GENERATED — a timestamp, an id — as
    /// opposed to free text a person writes. Read only by §5.1's heading rule,
    /// which needs to know whether the separator could occur in a value.
    ///
    /// Decided by the FIELD NAME, and that is the honest statement of it: the
    /// declared type of a timestamp and of an author's name is the same
    /// `String`, so nothing in the schema distinguishes them. The alternative is
    /// to refuse every `String` before the last heading position, which would
    /// refuse `heading: ["at", "author"]` — the one mapping this format exists
    /// to carry.
    fn is_machine_field(&self, _functor: &str, field: &str) -> bool {
        matches!(field, "at" | "since" | "created" | "id")
    }
}

// ── Errors and faults (§7) ─────────────────────────────────────

/// A file that cannot be read as an item document at all.
///
/// The set is deliberately small: §7 scopes a fault to the smallest thing it
/// makes ambiguous, so only a fault that makes the item's IDENTITY ambiguous —
/// no attributes chapter, no `id` — costs the item. Everything else is a
/// [`DocumentFault`] and the rest of the file still loads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DocumentError {
    /// Text before the first chapter. There is no region outside a chapter, so
    /// this is a file that is not in this format.
    TextBeforeFirstChapter { line: usize },
    /// A heading ABOVE the first structural level. The hierarchy runs from
    /// `level` downwards and nothing above it has a meaning, so an `h1` is
    /// refused rather than silently classified.
    HeadingAboveLevel { level: usize, line: usize },
    /// No attributes chapter: the file is not an item.
    NoAttributes { named: String },
    /// The item's own fact carries no id, so nothing can be attached to it.
    NoIdentity { field: String },
    /// A fenced code block opened in prose and never closed. It swallows every
    /// chapter after it, so a file's entries silently become description text —
    /// facts vanishing with nothing reported. Named by the line it opens on
    /// rather than guessed at (§4.4).
    UnclosedFence { line: usize },
    /// The prose a writer was handed cannot survive a round trip. Refused
    /// BEFORE the file is written — see [`demote_prose`].
    UnwritableProse { reason: String },
}

impl fmt::Display for DocumentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DocumentError::TextBeforeFirstChapter { line } => write!(
                f,
                "line {line}: text before the first chapter — every region of an item document \
                 is a chapter, so there is nowhere for this to belong"
            ),
            DocumentError::HeadingAboveLevel { level, line } => write!(
                f,
                "line {line}: a heading above the first structural level ({} `#`) — the \
                 hierarchy runs from there downwards and nothing above it has a meaning here",
                level
            ),
            DocumentError::NoAttributes { named } => write!(
                f,
                "no `## {named}` chapter — that chapter holds the item's own fact, so a file \
                 without one is not an item"
            ),
            DocumentError::NoIdentity { field } => write!(
                f,
                "the attributes chapter carries no `{field}`, and every entry in this file is \
                 keyed by it — there is nothing to attach them to"
            ),
            DocumentError::UnclosedFence { line } => write!(
                f,
                "the fenced code block opened at line {line} is never closed — it swallows \
                 every chapter below it, so those facts would vanish with nothing reported"
            ),
            DocumentError::UnwritableProse { reason } => write!(f, "{reason}"),
        }
    }
}

/// A fault SCOPED to the smallest thing it makes ambiguous (§7).
///
/// Every fault is reported at load and listed by `fsck`; what varies is whether
/// it BLOCKS, and a fault blocks exactly when it makes a write a guess. Blocking
/// blocks WRITES, never reads — the store is always built, because `fsck` needs
/// it before it can say anything.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DocumentFault {
    pub blocking: bool,
    pub message: String,
}

impl DocumentFault {
    fn blocking(message: impl Into<String>) -> Self {
        DocumentFault {
            blocking: true,
            message: message.into(),
        }
    }

    fn diagnostic(message: impl Into<String>) -> Self {
        DocumentFault {
            blocking: false,
            message: message.into(),
        }
    }
}

impl fmt::Display for DocumentFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

// ── The document model ─────────────────────────────────────────

/// The separator between an entry heading's fields.
pub const HEADING_SEPARATOR: &str = " — ";

/// The prefix marking a heading field value that has no literal spelling (§4.3).
pub const B64_PREFIX: &str = "b64:";

/// A value longer than this in the attributes chapter is a diagnostic: a prose
/// field wants declaring as a chapter (§4.2). Not a rule — length decides
/// nothing about where a field lives.
pub const LONG_VALUE: usize = 255;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SegmentKind {
    /// The chapter holding the item's own fact as data.
    Attributes,
    /// A prose field of that fact.
    Field { name: String },
    /// A container heading, together with whatever text precedes its first
    /// entry. It maps to no datum.
    Container { name: String },
    /// One entry of a container.
    Entry {
        container: String,
        /// The word naming which group — which functor — this entry belongs to.
        kind: String,
        /// The heading's field values, in the group's `heading` order, decoded.
        fields: Vec<String>,
    },
    /// A region the reader could not interpret. Kept so the file's text can
    /// still be reproduced; the fault that produced it BLOCKS writes, because
    /// re-rendering from facts would drop it.
    Unread { heading: String },
}

/// One structural region of the document, as a byte range of the source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Segment {
    pub kind: SegmentKind,
    /// The whole region, heading line included, up to the next segment.
    pub span: Range<usize>,
    /// The prose inside it: everything after the heading line, with the blank
    /// lines around it trimmed off. Empty for a container.
    pub body: Range<usize>,
}

/// One `- key: value` line of the attributes chapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttrLine {
    pub key: String,
    /// Everything after `: `, trimmed. A backticked value keeps its backticks —
    /// [`spell_read`] strips them, because that is where the two spellings are
    /// told apart.
    pub value: String,
    pub line: usize,
    /// Whether a blank line stood above this one. It is DATA, not formatting:
    /// §3.3 makes adjacency the statement "these fields change together", so a
    /// group written apart no longer says what it declares.
    pub separated: bool,
}

/// A document, as byte ranges into the source it was read from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Document {
    pub segments: Vec<Segment>,
    /// The attributes chapter's lines, in written order.
    pub attributes: Vec<AttrLine>,
    /// Everything wrong with this file that did not cost the whole item.
    pub faults: Vec<DocumentFault>,
}

impl Document {
    /// The value of one attributes field, if it is written and read cleanly.
    pub fn attribute(&self, key: &str) -> Option<&str> {
        self.attributes
            .iter()
            .find(|a| a.key == key)
            .map(|a| a.value.as_str())
    }

    pub fn blocking(&self) -> bool {
        self.faults.iter().any(|f| f.blocking)
    }
}

// ── The scanner ────────────────────────────────────────────────

/// One line of the source, with the byte range it occupies (terminator included).
struct Line<'a> {
    text: &'a str,
    start: usize,
    end: usize,
    number: usize,
}

fn lines(source: &str) -> Vec<Line<'_>> {
    let mut out = Vec::new();
    let mut start = 0usize;
    let mut number = 1usize;
    while start < source.len() {
        let rest = &source[start..];
        let end = match rest.find('\n') {
            Some(at) => start + at + 1,
            None => source.len(),
        };
        out.push(Line {
            text: source[start..end].trim_end_matches('\n').trim_end_matches('\r'),
            start,
            end,
            number,
        });
        start = end;
        number += 1;
    }
    out
}

/// A fence opener/closer: three or more `` ` `` or `~`, with the run length and
/// the info string. Indentation up to three spaces is allowed, as in CommonMark.
fn fence_of(line: &str) -> Option<(char, usize, &str)> {
    let trimmed = line.trim_start_matches(' ');
    if line.len() - trimmed.len() > 3 {
        return None;
    }
    let marker = trimmed.chars().next()?;
    if marker != '`' && marker != '~' {
        return None;
    }
    let run = trimmed.chars().take_while(|c| *c == marker).count();
    if run < 3 {
        return None;
    }
    Some((marker, run, trimmed[run..].trim()))
}

/// An ATX heading: 1–6 `#` followed by a space. The level and the text.
fn heading_of(line: &str) -> Option<(usize, &str)> {
    let trimmed = line.trim_start_matches(' ');
    if line.len() - trimmed.len() > 3 {
        return None;
    }
    let level = trimmed.chars().take_while(|c| *c == '#').count();
    if level == 0 || level > 6 {
        return None;
    }
    let rest = &trimmed[level..];
    if !rest.is_empty() && !rest.starts_with(' ') {
        return None;
    }
    // `## text ##` — a closing run of `#` is decoration in CommonMark, but ONLY
    // when whitespace precedes it. Stripping it unconditionally truncated any
    // heading VALUE ending in `#`: an entry authored by `bot#` was read back as
    // `bot`, and the next write persisted the truncation — a silent data change
    // on round trip, in the one place a heading is data rather than decoration.
    let text = rest.trim();
    let closing = text.len() - text.trim_end_matches('#').len();
    let head = &text[..text.len() - closing];
    Some((level, if closing > 0 && (head.is_empty() || head.ends_with(' ')) {
        head.trim()
    } else {
        text
    }))
}

/// Read an item document.
///
/// THE FENCE TRACKING IS NOT OPTIONAL: 392 descriptions and 240 feedback entries
/// on this repo's tracker already contain backticks, and a `#` at the start of a
/// line inside a fenced block is a comment in whatever language the block holds,
/// never a chapter boundary.
pub fn read_document(source: &str, mapping: &DocumentMapping) -> Result<Document, DocumentError> {
    let lines = lines(source);
    let level = mapping.level;

    let mut segments: Vec<Segment> = Vec::new();
    let mut faults: Vec<DocumentFault> = Vec::new();
    let mut open_fence: Option<(char, usize, usize)> = None;
    let mut container: Option<String> = None;

    for line in &lines {
        // THERE IS NO REGION OUTSIDE A CHAPTER (§2), so ANY content before the
        // first one is a load error — checked before the fence and heading
        // branches, not after. Checked only in the non-heading branch, a file
        // opening with a fenced block or with a heading deeper than the
        // structural level left those bytes in no segment at all and reported
        // nothing; the next write, which rebuilds from the attributes and the
        // segments, then dropped them. Silent loss is what this rule exists to
        // prevent, so it must not depend on which SHAPE the stray text has.
        if segments.is_empty() && !line.text.trim().is_empty() && heading_of(line.text).is_none() {
            return Err(DocumentError::TextBeforeFirstChapter { line: line.number });
        }
        if let Some((marker, run, info)) = fence_of(line.text) {
            match open_fence {
                Some((open_marker, open_run, _)) => {
                    if marker == open_marker && run >= open_run && info.is_empty() {
                        open_fence = None;
                    }
                }
                None => open_fence = Some((marker, run, line.number)),
            }
            continue;
        }
        if open_fence.is_some() {
            continue;
        }
        let Some((heading_level, text)) = heading_of(line.text) else {
            continue;
        };
        // A heading BELOW the structural level, before any chapter, is content
        // with nowhere to live just as plain text is.
        if segments.is_empty() && heading_level > level {
            return Err(DocumentError::TextBeforeFirstChapter { line: line.number });
        }
        if heading_level < level {
            return Err(DocumentError::HeadingAboveLevel {
                level,
                line: line.number,
            });
        }
        if heading_level == level {
            let kind = if text == mapping.attributes {
                container = None;
                SegmentKind::Attributes
            } else if let Some(spec) = mapping.field_chapter_named(text) {
                container = None;
                SegmentKind::Field {
                    name: spec.named.clone(),
                }
            } else if mapping.container_named(text) {
                container = Some(text.to_string());
                SegmentKind::Container {
                    name: text.to_string(),
                }
            } else {
                // THE TRUNCATION CASE: a heading at the reserved level that the
                // mapping does not name ENDS the chapter above it, so its text
                // is cut off there. Blocking, and the region is kept as text so
                // nothing is lost while it is being repaired.
                container = None;
                faults.push(DocumentFault::blocking(format!(
                    "line {}: `{text}` is a chapter heading the mapping does not name. That \
                     level is reserved — if this is prose, give it a deeper heading, because \
                     here it ENDS the chapter above it",
                    line.number
                )));
                SegmentKind::Unread {
                    heading: text.to_string(),
                }
            };
            if let SegmentKind::Attributes = kind {
                if segments
                    .iter()
                    .any(|s| matches!(s.kind, SegmentKind::Attributes))
                {
                    faults.push(DocumentFault::blocking(format!(
                        "line {}: a second `{}` chapter — which one holds the item's fact \
                         would be a guess",
                        line.number, mapping.attributes
                    )));
                }
            }
            if let SegmentKind::Field { name } = &kind {
                if segments
                    .iter()
                    .any(|s| matches!(&s.kind, SegmentKind::Field { name: n } if n == name))
                {
                    faults.push(DocumentFault::blocking(format!(
                        "line {}: a second chapter named `{name}`, where the mapping declares \
                         one field — a rewrite could not know which of them it means",
                        line.number
                    )));
                }
            }
            close_previous(&mut segments, line.start, source);
            segments.push(Segment {
                kind,
                span: line.start..source.len(),
                body: line.end..source.len(),
            });
        } else if heading_level == level + 1 {
            // A heading one below the structural level is an ENTRY only inside a
            // container. Inside a FIELD chapter it is ordinary prose — which is
            // what keeps a hand-added sub-section alive across a rewrite.
            let Some(container) = container.clone() else {
                continue;
            };
            let kind = match parse_entry_heading(text, &container, mapping, line.number, &mut faults)
            {
                Ok(kind) => kind,
                Err(message) => {
                    faults.push(DocumentFault::blocking(format!(
                        "line {}: {message}",
                        line.number
                    )));
                    SegmentKind::Unread {
                        heading: text.to_string(),
                    }
                }
            };
            close_previous(&mut segments, line.start, source);
            segments.push(Segment {
                kind,
                span: line.start..source.len(),
                body: line.end..source.len(),
            });
        }
        // Anything deeper is prose, carried verbatim.
    }
    if let Some((_, _, line)) = open_fence {
        return Err(DocumentError::UnclosedFence { line });
    }
    trim_bodies(&mut segments, source);

    let attributes = match segments
        .iter()
        .find(|s| matches!(s.kind, SegmentKind::Attributes))
    {
        Some(seg) => read_attributes(&source[seg.body.clone()], seg.body.start, source, &mut faults),
        None => {
            return Err(DocumentError::NoAttributes {
                named: mapping.attributes.clone(),
            })
        }
    };
    if let Some(item) = mapping.item_functor() {
        check_grouping(&attributes, item, mapping, &mut faults);
    }

    Ok(Document {
        segments,
        attributes,
        faults,
    })
}

/// Split an entry heading into its kind and its field values (§4.3).
///
/// SPLIT FROM THE LEFT, exactly *n − 1* times for *n* parts, so the last field
/// takes the remainder of the line: an author named `release — bot` round-trips
/// with no encoding at all, because nothing after the last separator is looked at
/// again. The kind sits after the first field, so it is found before the group —
/// and therefore before *n* — is known.
fn parse_entry_heading(
    text: &str,
    container: &str,
    mapping: &DocumentMapping,
    at_line: usize,
    faults: &mut Vec<DocumentFault>,
) -> Result<SegmentKind, String> {
    let Some((_, rest)) = text.split_once(HEADING_SEPARATOR) else {
        return Err(format!(
            "`{text}` is an entry heading with no `{HEADING_SEPARATOR}` — every entry names \
             its kind after its first field"
        ));
    };
    let kind = rest
        .split_once(HEADING_SEPARATOR)
        .map(|(k, _)| k)
        .unwrap_or(rest)
        .trim();
    let Some(group) = mapping.group_of(container, kind) else {
        return Err(format!(
            "`{kind}` names no group of `{container}`, so which functor this entry is would be \
             a guess"
        ));
    };
    let want = group.heading.len() + 1;
    let parts: Vec<&str> = text.splitn(want, HEADING_SEPARATOR).collect();
    if parts.len() < want {
        return Err(format!(
            "`{text}` has {} part(s) where `{}` declares {want}",
            parts.len(),
            group.functor
        ));
    }
    let mut fields = Vec::with_capacity(group.heading.len());
    let free = free_text_field(group.heading.len());
    for (i, part) in parts.iter().enumerate() {
        if i == 1 {
            continue; // the kind word
        }
        let at = fields.len();
        let value = decode_heading_field(part.trim())
            .map_err(|e| format!("`{text}`: the `{}` field {e}", group.heading[at]))?;
        // ONE SPELLING PER DATUM (§4.3): a value is encoded exactly when it has
        // to be, so an encoding that was not needed is a second spelling of
        // something already writable — reported, and rewritten by the next write.
        if part.trim().starts_with(B64_PREFIX)
            && encode_heading_field(&value, free == Some(at)) != *part.trim()
        {
            faults.push(DocumentFault::diagnostic(format!(
                "line {at_line}: the `{}` field is written `{B64_PREFIX}…` but `{value}` \
                 needs no encoding — one datum, two spellings",
                group.heading[at]
            )));
        }
        fields.push(value);
    }
    Ok(SegmentKind::Entry {
        container: container.to_string(),
        kind: kind.to_string(),
        fields,
    })
}

/// Read the attributes chapter's bullet list (§3.1).
fn read_attributes(
    text: &str,
    offset: usize,
    source: &str,
    faults: &mut Vec<DocumentFault>,
) -> Vec<AttrLine> {
    // COUNTED TO THE START OF THE LINE, not to `offset`. `trim_bodies` advances
    // a body past its leading whitespace, INCLUDING the indent of its first
    // line, so counting the prefix directly reported every fault in an indented
    // chapter one line low.
    let line_start = source[..offset].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let base = source[..line_start].lines().count() + 1;
    let mut out: Vec<AttrLine> = Vec::new();
    let mut separated = false;
    for (n, raw) in text.lines().enumerate() {
        let line = base + n;
        if raw.trim().is_empty() {
            separated = true;
            continue;
        }
        let Some(rest) = raw.trim_start().strip_prefix("- ") else {
            faults.push(DocumentFault::blocking(format!(
                "line {line}: `{}` is not a `- key: value` field line, and the attributes \
                 chapter holds nothing else",
                raw.trim()
            )));
            continue;
        };
        let Some((key, value)) = rest.split_once(':') else {
            faults.push(DocumentFault::blocking(format!(
                "line {line}: `{}` carries no `:`, so it names no field",
                raw.trim()
            )));
            continue;
        };
        let key = key.trim().to_string();
        if !is_field_key(&key) {
            faults.push(DocumentFault::blocking(format!(
                "line {line}: `{key}` is not a field name"
            )));
            continue;
        }
        if out.iter().any(|a| a.key == key) {
            faults.push(DocumentFault::blocking(format!(
                "line {line}: `{key}` is written twice — which value wins would be a guess"
            )));
            continue;
        }
        let value = value.trim().to_string();
        if value.len() > LONG_VALUE {
            faults.push(DocumentFault::diagnostic(format!(
                "line {line}: `{key}` carries {} characters in the attributes chapter — a \
                 prose field wants declaring as a chapter",
                value.len()
            )));
        }
        out.push(AttrLine {
            key,
            value,
            line,
            separated: separated || out.is_empty(),
        });
        separated = false;
    }
    out
}

/// §3.3, read back: a `FieldGroup`'s members are ADJACENT and everything else is
/// blank-separated.
///
/// A DIAGNOSTIC RATHER THAN AN ERROR, because nothing is ambiguous — the fields
/// are all there and all readable. What is wrong is the STATEMENT the layout
/// makes: a group written apart no longer collides on a concurrent half-edit,
/// and two independent fields written together collide when they need not. It is
/// repaired by the next write, which re-renders the chapter from the facts.
fn check_grouping(
    attributes: &[AttrLine],
    item: &str,
    mapping: &DocumentMapping,
    faults: &mut Vec<DocumentFault>,
) {
    for (i, line) in attributes.iter().enumerate().skip(1) {
        let previous = &attributes[i - 1].key;
        let together = mapping
            .group_of_field(item, &line.key)
            .is_some_and(|g| g.fields.contains(previous));
        if together && line.separated {
            faults.push(DocumentFault::diagnostic(format!(
                "line {}: `{}` is written apart from `{previous}`, which it is declared to \
                 change WITH — separated, a concurrent edit to the pair merges into a half \
                 transition instead of colliding",
                line.line, line.key
            )));
        } else if !together && !line.separated {
            faults.push(DocumentFault::diagnostic(format!(
                "line {}: `{}` is written against `{previous}`, which it is not declared to \
                 change with — adjacent, two independent edits collide for nothing",
                line.line, line.key
            )));
        }
    }
}

fn is_field_key(key: &str) -> bool {
    let mut chars = key.chars();
    match chars.next() {
        Some(c) if c.is_ascii_lowercase() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
}

/// Close the segment being filled at `at`, which is where the next one starts.
fn close_previous(segments: &mut [Segment], at: usize, source: &str) {
    if let Some(last) = segments.last_mut() {
        last.span.end = at;
        last.body.end = at.min(source.len());
    }
}

/// A chapter's VALUE is its prose with the blank lines around it dropped.
fn trim_bodies(segments: &mut [Segment], source: &str) {
    for seg in segments.iter_mut() {
        if matches!(seg.kind, SegmentKind::Container { .. }) {
            seg.body = seg.span.start..seg.span.start;
            continue;
        }
        let text = &source[seg.body.clone()];
        let lead = text.len() - text.trim_start().len();
        let trail = text.len() - text.trim_end().len();
        let start = seg.body.start + lead;
        let end = (seg.body.end - trail).max(start);
        seg.body = start..end;
    }
}

// ── Value spelling (§3.2) ──────────────────────────────────────

/// Read one attributes value into ANTHILL SOURCE, spelled by its declared type.
///
/// The output is source text rather than a term because the whole document is
/// handed to the ordinary parser: what the loader, the typer and every reader
/// downstream see is the parse IR a plain `fact` file would have produced, which
/// is what keeps this an encoding rather than a second front end.
pub fn spell_read(value: &str, ty: &FieldType, mapping: &DocumentMapping) -> Result<String, String> {
    if let Some(inner) = value.strip_prefix('`') {
        let Some(term) = inner.strip_suffix('`') else {
            return Err(format!("`{value}` opens a backtick and never closes it"));
        };
        if term.trim().is_empty() {
            return Err("an empty backticked value denotes no term".to_string());
        }
        return Ok(term.trim().to_string());
    }
    match ty {
        FieldType::Text => {
            let mut out = String::with_capacity(value.len() + 2);
            print::write_anthill_string(value, &mut out);
            Ok(out)
        }
        FieldType::Int => value
            .parse::<i64>()
            .map(|n| n.to_string())
            .map_err(|_| format!("`{value}` is not an integer")),
        FieldType::Bool => match value {
            "true" | "false" => Ok(value.to_string()),
            _ => Err(format!("`{value}` is neither `true` nor `false`")),
        },
        FieldType::Option(inner) => {
            Ok(format!("some(value: {})", spell_read(value, inner, mapping)?))
        }
        FieldType::List(inner) => {
            if value.is_empty() {
                return Ok("[]".to_string());
            }
            let mut parts = Vec::new();
            for e in value.split(", ") {
                parts.push(spell_read(e.trim(), inner, mapping)?);
            }
            Ok(format!("[{}]", parts.join(", ")))
        }
        FieldType::Named(sort) => {
            if let Some(form) = mapping.scalar_form(sort) {
                let mut slot = String::new();
                print::write_anthill_string(value, &mut slot);
                return Ok(format!("{}({}: {slot})", form.constructor, form.slot));
            }
            match mapping.schema.variants(sort) {
                Some(variants) => match variants.iter().find(|(n, _)| n == value) {
                    Some((n, false)) => Ok(n.clone()),
                    Some((n, true)) => Err(format!(
                        "`{n}` carries fields, so it has no bare spelling — write it as a \
                         backticked term"
                    )),
                    None => Err(format!("`{value}` is not a variant of `{sort}`")),
                },
                None => Err(format!(
                    "`{sort}` declares no variants and no `ScalarForm`, so a bare value has no \
                     spelling for it — write it as a backticked term"
                )),
            }
        }
        FieldType::Opaque => Err(
            "this field's type has no data spelling — write the value as a backticked term"
                .to_string(),
        ),
    }
}

/// Write one value as data, or `None` when it has no data spelling and must be
/// written as a backticked term.
///
/// `None` is not a refusal: the caller falls back to the term spelling, which is
/// total. That is what lets the writer never refuse a value (§3.2).
pub fn spell_write(
    kb: &KnowledgeBase,
    term: TermId,
    ty: &FieldType,
    mapping: &DocumentMapping,
) -> Option<String> {
    match ty {
        FieldType::Text => {
            let Term::Const(Literal::String(s)) = kb.get_term(term) else {
                return None;
            };
            renders_as_itself(s).then(|| s.clone())
        }
        FieldType::Int => match kb.get_term(term) {
            Term::Const(Literal::Int(n)) => Some(n.to_string()),
            _ => None,
        },
        FieldType::Bool => match kb.get_term(term) {
            Term::Const(Literal::Bool(b)) => Some(b.to_string()),
            _ => None,
        },
        FieldType::Option(inner) => {
            let value = option_value(kb, term)?;
            spell_write(kb, value, inner, mapping)
        }
        FieldType::List(inner) => {
            let elements = list_elements(kb, term)?;
            let mut out: Vec<String> = Vec::with_capacity(elements.len());
            for e in elements {
                let text = spell_write(kb, e, inner, mapping)?;
                // An element carrying the separator has no place in a
                // comma-separated list, so the WHOLE field takes the term
                // spelling — a partly escaped list has more ways to be subtly
                // wrong than one that is plainly a term.
                if text.contains(", ") || text.is_empty() {
                    return None;
                }
                out.push(text);
            }
            Some(out.join(", "))
        }
        FieldType::Named(sort) => {
            if let Some(form) = mapping.scalar_form(sort) {
                return scalar_of(kb, term, form);
            }
            let variants = mapping.schema.variants(sort)?;
            let name = nullary_name(kb, term)?;
            variants
                .iter()
                .any(|(n, payload)| *n == name && !*payload)
                .then_some(name)
        }
        FieldType::Opaque => None,
    }
}

/// The value inside a `some(value: …)`, or `None` for `none` — which the caller
/// turns into an OMITTED line (§3.5).
fn option_value(kb: &KnowledgeBase, term: TermId) -> Option<TermId> {
    match kb.get_term(term) {
        Term::Ref(s) | Term::Ident(s) if kb.local_name_of(*s) == "none" => None,
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if kb.local_name_of(*functor) == "some" => {
            get_named_arg(kb, named_args, "value").or_else(|| pos_args.first().copied())
        }
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if kb.local_name_of(*functor) == "none"
            && pos_args.is_empty()
            && named_args.is_empty() =>
        {
            None
        }
        _ => None,
    }
}

/// Whether a term is `none` — an absent Option, which is written as no line at
/// all rather than as a value.
pub fn is_absent(kb: &KnowledgeBase, term: TermId) -> bool {
    match kb.get_term(term) {
        Term::Ref(s) | Term::Ident(s) => kb.local_name_of(*s) == "none",
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            kb.local_name_of(*functor) == "none" && pos_args.is_empty() && named_args.is_empty()
        }
        _ => false,
    }
}

/// The elements of a list, in order.
///
/// THROUGH THE PRINTER'S OWN SPINE READER, not a second copy of it. A written
/// `[a, b]` lowers to a `cons`/`nil` CHAIN (§4.6), which is what a loaded fact
/// holds, while a reflect-built list rides as a flat `ListLiteral` (WI-1099);
/// `unwrap_list_spine` already knows both, including which `cons` shapes are NOT
/// a spine. A rule that missed the chain read every real `depends_on` as
/// unspellable and quietly wrote it as a backticked term — legible, but not the
/// data spelling the format promises, and a divergence no test would name.
fn list_elements(kb: &KnowledgeBase, term: TermId) -> Option<Vec<TermId>> {
    if let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(term)
    {
        if kb.local_name_of(*functor) == "ListLiteral" && named_args.is_empty() {
            return Some(pos_args.to_vec());
        }
    }
    print::TermPrinter::new(kb).unwrap_list_spine(term)
}

/// A `ScalarForm`'s scalar: the `slot` field's text, and only when every OTHER
/// field of the constructor is absent — a `ToolPasses` carrying params says more
/// than its tool name, so its bare spelling would lose data.
fn scalar_of(kb: &KnowledgeBase, term: TermId, form: &ScalarFormSpec) -> Option<String> {
    let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(term)
    else {
        return None;
    };
    if kb.local_name_of(*functor) != form.constructor || !pos_args.is_empty() {
        return None;
    }
    let mut scalar = None;
    for (name, value) in named_args.iter() {
        if kb.local_name_of(*name) == form.slot {
            let Term::Const(Literal::String(s)) = kb.get_term(*value) else {
                return None;
            };
            if !renders_as_itself(s) {
                return None;
            }
            scalar = Some(s.clone());
        } else if !is_absent(kb, *value) {
            return None;
        }
    }
    scalar
}

/// The name of a payload-free constructor, however it was built. A nullary
/// entity rides as `Ref(c)` or as `Fn{c}` with no arguments — WI-719's canon —
/// and both spell the same variant name.
fn nullary_name(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    match kb.get_term(term) {
        Term::Ref(s) | Term::Ident(s) => Some(kb.local_name_of(*s).to_string()),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => {
            Some(kb.local_name_of(*functor).to_string())
        }
        _ => None,
    }
}

/// Whether a value written bare in the attributes chapter RENDERS AS ITSELF.
///
/// A bare value sits in markdown inline context, so a value that would render as
/// markup rather than as itself has no data spelling and takes the backticked
/// term spelling instead, whose code span suspends inline parsing. Rendering is
/// why this format is `.md` at all, so a value the page shows differently from
/// the data it denotes is a defect.
///
/// THE TEST IS THE RENDERING, NOT A CHARACTER BLACKLIST, and the difference is
/// not academic: CommonMark does not open emphasis with an INTRAWORD `_`, so the
/// tag `prop025_1` is inert and a blacklist would quote it for nothing. Measured
/// on this tracker, exactly two values carry any candidate character and both
/// render as themselves.
///
/// Where it cannot decide it OVER-quotes: a code span renders the literal text,
/// so the term spelling is always safe and only ever costs a pair of backticks.
pub fn renders_as_itself(value: &str) -> bool {
    if value.is_empty() || value.trim() != value {
        // A leading or trailing space is dropped on read, so the value would not
        // come back as itself.
        return false;
    }
    if value.contains('\n') || value.contains('\r') {
        return false;
    }
    let bytes: Vec<char> = value.chars().collect();
    for (i, c) in bytes.iter().enumerate() {
        match c {
            // A code span, a link, raw HTML, an entity, an escape: each changes
            // what the page shows.
            '`' | '[' | ']' | '<' | '>' | '&' | '\\' | '*' | '|' => return false,
            // GFM strikethrough needs a PAIR; one tilde is literal.
            '~' if bytes.get(i + 1) == Some(&'~') => return false,
            // Emphasis with `_` opens only at a word boundary, so an intraword
            // underscore is inert — which is the whole reason this is a
            // rendering test.
            '_' => {
                let left = i.checked_sub(1).and_then(|j| bytes.get(j));
                let right = bytes.get(i + 1);
                let word = |c: Option<&char>| c.is_some_and(|c| c.is_alphanumeric());
                if !(word(left) && word(right)) {
                    return false;
                }
            }
            _ => {}
        }
    }
    // A leading `-`, `+` or `#` would start a list item or a heading of its own,
    // and a leading digit-dot an ordered list. None of these can actually open a
    // block here — the value always follows `- key: ` on its line — but a value
    // that READS as one is still a value the page shows as something else.
    // (`>` and the emphasis characters are refused above, in the scan.)
    if bytes[0].is_ascii_digit() {
        let dot = bytes.iter().position(|c| !c.is_ascii_digit());
        if matches!(bytes.get(dot.unwrap_or(bytes.len())), Some('.') | Some(')')) {
            return false;
        }
    }
    !matches!(bytes[0], '-' | '#' | '+' | '=')
}

// ── The facts a document denotes ───────────────────────────────

/// Which segment's prose fills which field of which emitted fact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProseBinding {
    /// Index into [`DocumentFacts::source`]'s facts, in emission order.
    pub fact: usize,
    /// The path from the fact to the field the chapter fills — one segment for
    /// an ordinary field, two when the field lives inside a flattened record.
    pub path: Vec<String>,
    /// The record constructor to rebuild, for a two-segment path.
    pub record: Option<String>,
    /// Index into [`Document::segments`].
    pub segment: usize,
}

/// The facts a document denotes, as the anthill source a plain `fact` file would
/// have held — with every PROSE field left off, to be spliced in from its
/// chapter by the caller.
///
/// TWO STEPS RATHER THAN ONE, and the split is what keeps the prose exact: a
/// description carrying a `"` or a backslash would have to be escaped into the
/// source and unescaped by the parser, and the round trip through two escaping
/// layers is the failure this encoding exists to remove. The text is handed to
/// the IR directly instead, as the string literal it already is.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct DocumentFacts {
    pub source: String,
    pub prose: Vec<ProseBinding>,
    /// Faults found while spelling values — a field with no reading costs that
    /// FIELD, not the fact, so the fact is emitted without it and this says so.
    pub faults: Vec<DocumentFault>,
}

/// Read a document's facts.
///
/// `id_field` is the item's key field — the store's `ItemFields::id`, passed in
/// rather than assumed, so this module stays domain-neutral. Every satellite's
/// `key` is filled from the value of that field IN THE ATTRIBUTES CHAPTER and
/// never from the filename: taking it from the path would make a hand-renamed
/// file silently re-attribute every entry in it, while the filename check
/// reported the rename as a separate and apparently harmless fault (§4.3).
pub fn document_facts(
    doc: &Document,
    mapping: &DocumentMapping,
    id_field: &str,
) -> Result<DocumentFacts, DocumentError> {
    let item = mapping
        .item_functor()
        .expect("the mapping was checked when it was read")
        .to_string();
    let Some(id) = doc.attribute(id_field) else {
        return Err(DocumentError::NoIdentity {
            field: id_field.to_string(),
        });
    };
    let mut id_literal = String::new();
    print::write_anthill_string(id, &mut id_literal);

    let mut out = DocumentFacts::default();
    // Top-level named arguments, and — per flattened record — the inner ones,
    // keyed by the field that holds the record so they can be reassembled into
    // one constructor call at the end.
    let mut args: Vec<String> = Vec::new();
    let mut nested: Vec<(String, String, Vec<String>)> = Vec::new();
    let mut satellites: Vec<(&SatelliteListSpec, Vec<String>)> = Vec::new();

    for line in &doc.attributes {
        if let Some(spec) = mapping.list_named(&line.key) {
            // A satellite list is one attributes field holding many facts.
            let ty = mapping
                .schema
                .field_type(&spec.functor, &spec.field)
                .unwrap_or(FieldType::Text);
            let mut elements = Vec::new();
            let mut bad = false;
            for e in line.value.split(", ").filter(|e| !e.trim().is_empty()) {
                match spell_read(e.trim(), &ty, mapping) {
                    Ok(text) => elements.push(text),
                    Err(message) => {
                        out.faults.push(DocumentFault::blocking(format!(
                            "line {}: `{}`: {message}",
                            line.line, line.key
                        )));
                        bad = true;
                    }
                }
            }
            if !bad {
                satellites.push((spec, elements));
            }
            continue;
        }
        let Some(slot) = mapping.slot_of(&item, &line.key) else {
            out.faults.push(DocumentFault::blocking(format!(
                "line {}: `{}` names neither a field of `{item}` nor a declared attributes \
                 field — writing this file back would drop it",
                line.line, line.key
            )));
            continue;
        };
        if mapping
            .chapters
            .iter()
            .any(|c| c.functor == item && c.field == line.key)
        {
            out.faults.push(DocumentFault::blocking(format!(
                "line {}: `{}` is a chapter field, so it has a home already — two writable \
                 places for one datum",
                line.line, line.key
            )));
            continue;
        }
        match spell_read(&line.value, &slot.ty, mapping) {
            Ok(text) => push_arg(&mut args, &mut nested, &slot, text),
            Err(message) => out.faults.push(DocumentFault::blocking(format!(
                "line {}: `{}`: {message}",
                line.line, line.key
            ))),
        }
    }

    // A prose chapter fills a field like any other, so it is collected the same
    // way — but its VALUE is not here: it is spliced in by the caller, from the
    // chapter's own bytes. That keeps the text out of a string literal and back
    // through the parser, which is the round trip through two escaping layers
    // this encoding exists to remove.
    let mut prose: Vec<(AttrSlot, usize)> = Vec::new();
    for (i, seg) in doc.segments.iter().enumerate() {
        let SegmentKind::Field { name } = &seg.kind else {
            continue;
        };
        let Some(spec) = mapping.chapters.iter().find(|c| c.named == *name) else {
            continue;
        };
        if spec.functor != item {
            continue;
        }
        if let Some(slot) = mapping.slot_of(&item, &spec.field) {
            prose.push((slot, i));
        }
    }
    // A prose field inside a flattened record has to be RESERVED in the
    // constructor call before it is emitted — the caller splices into a term,
    // and there is no term to splice into unless the record exists.
    for (slot, _) in &prose {
        if slot.path.len() > 1 {
            reserve_nested(&mut nested, slot);
        }
    }

    // The item's own fact first, then its satellites — which is the order the
    // file reads in, and the order the store re-renders them in.
    for (field, record, inner) in &nested {
        args.push(format!("{field}: {record}({})", inner.join(", ")));
    }
    out.source.push_str(&format!("fact {item}({})\n", args.join(", ")));
    for (slot, segment) in prose {
        out.prose.push(ProseBinding {
            fact: 0,
            path: slot.path,
            record: slot.record,
            segment,
        });
    }

    for (spec, elements) in satellites {
        for e in elements {
            out.source.push_str(&format!(
                "fact {}({}: {id_literal}, {}: {e})\n",
                spec.functor, spec.key, spec.field
            ));
        }
    }

    for (i, seg) in doc.segments.iter().enumerate() {
        let SegmentKind::Entry {
            container,
            kind,
            fields,
        } = &seg.kind
        else {
            continue;
        };
        let Some(group) = mapping.group_of(container, kind) else {
            continue;
        };
        let mut args = vec![format!("{}: {id_literal}", group.key)];
        let mut bad = false;
        for (name, value) in group.heading.iter().zip(fields.iter()) {
            let ty = mapping
                .schema
                .field_type(&group.functor, name)
                .unwrap_or(FieldType::Text);
            match spell_read(value, &ty, mapping) {
                Ok(text) => args.push(format!("{name}: {text}")),
                Err(message) => {
                    out.faults.push(DocumentFault::blocking(format!(
                        "the entry `{}`: its `{name}` {message}",
                        heading_text(kind, fields)
                    )));
                    bad = true;
                }
            }
        }
        if bad {
            continue;
        }
        let fact = out.source.lines().count();
        out.source
            .push_str(&format!("fact {}({})\n", group.functor, args.join(", ")));
        out.prose.push(ProseBinding {
            fact,
            path: vec![group.field.clone()],
            record: None,
            segment: i,
        });
    }
    Ok(out)
}

/// Place one read value into the fact's argument list — at the top level, or
/// inside the constructor call of the record its slot names.
fn push_arg(
    args: &mut Vec<String>,
    nested: &mut Vec<(String, String, Vec<String>)>,
    slot: &AttrSlot,
    text: String,
) {
    if slot.path.len() == 1 {
        args.push(format!("{}: {text}", slot.path[0]));
        return;
    }
    reserve_nested(nested, slot).push(format!("{}: {text}", slot.path[1]));
}

/// The argument list of the constructor call a flattened slot's record becomes,
/// created if this is the record's first line.
fn reserve_nested<'a>(
    nested: &'a mut Vec<(String, String, Vec<String>)>,
    slot: &AttrSlot,
) -> &'a mut Vec<String> {
    let field = slot.path[0].clone();
    if let Some(i) = nested.iter().position(|(f, _, _)| *f == field) {
        return &mut nested[i].2;
    }
    nested.push((field, slot.record.clone().unwrap_or_default(), Vec::new()));
    let last = nested.len() - 1;
    &mut nested[last].2
}

// ── Rendering (the writer) ─────────────────────────────────────

/// One `- key: value` of the attributes chapter, plus whether it opens a new
/// blank-separated group.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttrField {
    pub key: String,
    pub value: String,
    /// A blank line goes ABOVE this field. False for the first field of the
    /// chapter and for every field written adjacent to the one before it.
    pub separated: bool,
}

/// Render the attributes chapter.
pub fn render_attributes(level: usize, named: &str, fields: &[AttrField]) -> String {
    let mut out = String::new();
    out.push_str(&"#".repeat(level));
    out.push(' ');
    out.push_str(named);
    out.push_str("\n\n");
    for f in fields {
        if f.separated && !out.ends_with("\n\n") {
            out.push('\n');
        }
        out.push_str("- ");
        out.push_str(&f.key);
        out.push_str(": ");
        out.push_str(&f.value);
        out.push('\n');
    }
    out.push('\n');
    out
}

/// The canonical text of one prose chapter: heading, blank line, prose, blank
/// line.
pub fn render_chapter(level: usize, heading: &str, body: &str) -> String {
    let mut out = String::with_capacity(body.len() + heading.len() + 8);
    out.push_str(&"#".repeat(level));
    out.push(' ');
    out.push_str(heading);
    out.push_str("\n\n");
    if !body.is_empty() {
        out.push_str(body);
        out.push_str("\n\n");
    }
    out
}

/// An entry's heading text: its fields joined by the separator, with the kind
/// inserted after the first, and every part with no literal spelling encoded.
pub fn entry_heading(kind: &str, fields: &[String]) -> String {
    let mut parts: Vec<String> = Vec::with_capacity(fields.len() + 1);
    for (i, f) in fields.iter().enumerate() {
        parts.push(encode_heading_field(f, free_text_field(fields.len()) == Some(i)));
        if i == 0 {
            parts.push(kind.to_string());
        }
    }
    parts.join(HEADING_SEPARATOR)
}

/// The heading text of an entry already read back, for a diagnostic.
fn heading_text(kind: &str, fields: &[String]) -> String {
    entry_heading(kind, fields)
}

/// Which heading field, if any, may hold free text — the one that ends up LAST
/// in the rendered line, because splitting from the left gives it the remainder.
///
/// IT IS NOT ALWAYS `n - 1`. The kind is written after the FIRST field, so a
/// heading of one field renders as `<field> — <kind>` and the last part is the
/// KIND, not the field. A rule that answered `n - 1` there let a one-field
/// heading carry the separator literally and then read back as a different
/// kind — an entry lost, reported as "names no group".
fn free_text_field(count: usize) -> Option<usize> {
    (count > 1).then(|| count - 1)
}

// ── Heading field encoding (§4.3) ──────────────────────────────

/// Write one heading field, BASE64-ENCODED exactly when it has no literal
/// spelling.
///
/// A heading is one line and its parts are trimmed on read, so a value carrying
/// a line break, one with leading or trailing whitespace, an empty one, and —
/// for a field that is not the last — one carrying the separator have no literal
/// spelling. Those are encoded; nothing is refused, so no command can fail on a
/// name.
///
/// THIS IS WHAT MAKES INJECTION IMPOSSIBLE RATHER THAN MERELY CAUGHT. Written
/// naively, `--agent $'claude\n### 2026-01-01 — status — root'` would produce a
/// WELL-FORMED EXTRA ENTRY: it parses, names a real kind, and denotes a fact
/// indistinguishable from a recorded one. Under this rule the break has no
/// literal spelling, so the value is encoded at the single point a heading is
/// rendered — the illegal state is unrepresentable rather than rejected by a
/// check someone must remember to call.
///
/// ENCODED EXACTLY WHEN IT HAS TO BE, which keeps one spelling per datum. The
/// self-referential case falls out of the same rule: a value that genuinely
/// begins with `b64:` cannot be written literally either, so it is encoded.
pub fn encode_heading_field(value: &str, is_last: bool) -> String {
    let literal = !value.is_empty()
        && value.trim() == value
        && !value.contains('\n')
        && !value.contains('\r')
        && !value.starts_with(B64_PREFIX)
        && (is_last || !value.contains(HEADING_SEPARATOR));
    if literal {
        return value.to_string();
    }
    format!("{B64_PREFIX}{}", base64_encode(value.as_bytes()))
}

/// Read one heading field back.
pub fn decode_heading_field(text: &str) -> Result<String, String> {
    let Some(encoded) = text.strip_prefix(B64_PREFIX) else {
        return Ok(text.to_string());
    };
    let bytes = base64_decode(encoded).ok_or_else(|| format!("`{text}` is not valid base64"))?;
    String::from_utf8(bytes).map_err(|_| format!("`{text}` decodes to bytes that are not text"))
}

const B64_ALPHABET: &[u8; 64] =
    b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn base64_encode(input: &[u8]) -> String {
    let mut out = String::with_capacity(input.len().div_ceil(3) * 4);
    for chunk in input.chunks(3) {
        let b = [chunk[0], *chunk.get(1).unwrap_or(&0), *chunk.get(2).unwrap_or(&0)];
        let n = ((b[0] as u32) << 16) | ((b[1] as u32) << 8) | b[2] as u32;
        out.push(B64_ALPHABET[(n >> 18) as usize & 63] as char);
        out.push(B64_ALPHABET[(n >> 12) as usize & 63] as char);
        out.push(if chunk.len() > 1 {
            B64_ALPHABET[(n >> 6) as usize & 63] as char
        } else {
            '='
        });
        out.push(if chunk.len() > 2 {
            B64_ALPHABET[n as usize & 63] as char
        } else {
            '='
        });
    }
    out
}

fn base64_decode(input: &str) -> Option<Vec<u8>> {
    let value = |c: u8| -> Option<u32> {
        B64_ALPHABET
            .iter()
            .position(|a| *a == c)
            .map(|p| p as u32)
    };
    let bytes: Vec<u8> = input.bytes().collect();
    if bytes.is_empty() || bytes.len() % 4 != 0 {
        return None;
    }
    let mut out = Vec::with_capacity(bytes.len() / 4 * 3);
    for chunk in bytes.chunks(4) {
        let pad = chunk.iter().filter(|c| **c == b'=').count();
        if pad > 2 {
            return None;
        }
        let mut n = 0u32;
        for (i, c) in chunk.iter().enumerate() {
            let v = if *c == b'=' {
                if i < 4 - pad {
                    return None;
                }
                0
            } else {
                value(*c)?
            };
            n = (n << 6) | v;
        }
        out.push((n >> 16) as u8);
        if pad < 2 {
            out.push((n >> 8) as u8);
        }
        if pad < 1 {
            out.push(n as u8);
        }
    }
    Some(out)
}

// ── Prose: demotion and refusal (§4.1) ─────────────────────────

/// The deepest heading level that ENDS this chapter, and so may not appear in
/// its prose.
///
/// IT DIFFERS BY KIND, and making it uniform was WI-1120's worst defect: a
/// heading one below the structural level is ordinary prose inside a FIELD
/// chapter and starts the next entry inside a CONTAINER. A writer that reserved
/// `level + 1` everywhere refused prose the READER accepts, so a description
/// carrying a sub-section loaded fine, round-tripped into the fact, and then made
/// its item permanently unwritable.
pub fn deepest_reserved_for(kind: &SegmentKind, level: usize) -> usize {
    match kind {
        SegmentKind::Entry { .. } => level + 1,
        _ => level,
    }
}

/// Shift a prose body's own headings below the reserved set for the chapter it
/// is going into (§4.1).
///
/// Text written somewhere else — a design note, a pasted document, an agent that
/// has never heard of this format — carries a hierarchy starting at `#` or `##`,
/// which collides with the levels reserved here. The whole hierarchy shifts down
/// by the MINIMUM that clears the reserved set, so the RELATIVE hierarchy is
/// preserved exactly and sibling sections stay siblings.
///
/// It is IDEMPOTENT, which is what makes it safe to apply on every write: stored
/// prose has no collision, so writing it back shifts nothing, and a round trip is
/// identity from the second write onward.
///
/// Two things it does not touch. A `#` inside a fenced block is not a heading and
/// is left exactly as written. And a shift that would push a heading past level 6
/// cannot be represented: that is refused, naming the heading and the depth,
/// because there is no correct answer rather than because the format is strict.
pub fn demote_prose(value: &str, deepest_reserved: usize) -> Result<String, DocumentError> {
    let scan = scan_prose(value)?;
    let Some(min) = scan.min_level else {
        return Ok(value.to_string());
    };
    if min > deepest_reserved {
        return Ok(value.to_string());
    }
    let shift = deepest_reserved + 1 - min;
    if let Some((text, level)) = scan.deepest {
        if level + shift > 6 {
            return Err(DocumentError::UnwritableProse {
                reason: format!(
                    "this text carries `{text}` at heading level {level}; shifting its \
                     hierarchy below `{}` `#` would put it at level {}, and markdown has no \
                     heading deeper than 6",
                    deepest_reserved,
                    level + shift
                ),
            });
        }
    }
    let mut out = String::with_capacity(value.len() + scan.headings * shift);
    let mut open_fence: Option<(char, usize)> = None;
    for line in lines(value) {
        let raw = &value[line.start..line.end];
        if let Some((marker, run, info)) = fence_of(line.text) {
            match open_fence {
                Some((open_marker, open_run)) => {
                    if marker == open_marker && run >= open_run && info.is_empty() {
                        open_fence = None;
                    }
                }
                None => open_fence = Some((marker, run)),
            }
            out.push_str(raw);
            continue;
        }
        if open_fence.is_none() && heading_of(line.text).is_some() {
            let indent = line.text.len() - line.text.trim_start_matches(' ').len();
            out.push_str(&line.text[..indent]);
            out.push_str(&"#".repeat(shift));
            out.push_str(&raw[indent..]);
            continue;
        }
        out.push_str(raw);
    }
    Ok(out)
}

struct ProseScan {
    min_level: Option<usize>,
    /// The deepest heading and its level, for the refusal's message.
    deepest: Option<(String, usize)>,
    headings: usize,
}

/// Scan prose for its headings, fence-aware. An unbalanced fence is refused
/// here, before the file is written: it would swallow every chapter after it.
fn scan_prose(value: &str) -> Result<ProseScan, DocumentError> {
    let mut open_fence: Option<(char, usize, usize)> = None;
    let mut min_level: Option<usize> = None;
    let mut deepest: Option<(String, usize)> = None;
    let mut headings = 0usize;
    for line in lines(value) {
        if let Some((marker, run, info)) = fence_of(line.text) {
            match open_fence {
                Some((open_marker, open_run, _)) => {
                    if marker == open_marker && run >= open_run && info.is_empty() {
                        open_fence = None;
                    }
                }
                None => open_fence = Some((marker, run, line.number)),
            }
            continue;
        }
        if open_fence.is_some() {
            continue;
        }
        if let Some((level, text)) = heading_of(line.text) {
            headings += 1;
            min_level = Some(min_level.map_or(level, |m: usize| m.min(level)));
            if deepest.as_ref().is_none_or(|(_, d)| level > *d) {
                deepest = Some((text.to_string(), level));
            }
        }
    }
    if let Some((_, _, line)) = open_fence {
        return Err(DocumentError::UnclosedFence { line });
    }
    Ok(ProseScan {
        min_level,
        deepest,
        headings,
    })
}

// ── The previous encoding, read only to convert it ─────────────

/// THE WI-1120 ENCODING: a fenced `anthill` head of facts, then markdown
/// chapters. Kept ONLY so `migrate --to document` can convert a tracker that
/// still holds one, and deliberately kept minimal — it reads the shape and
/// nothing else, because everything it produces is about to be rewritten.
///
/// Nothing else in the codebase reads it. When no tracker holds one, delete this
/// module and [`ItemPerFileStore::record_legacy_document`] with it.
pub mod legacy {
    use super::{fence_of, heading_of, lines};
    use std::ops::Range;

    /// One chapter of a legacy document: its heading text (name and decoration
    /// still joined) and the prose under it.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct LegacyChapter {
        pub level: usize,
        pub heading: String,
        pub body: Range<usize>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct LegacyDocument {
        /// The head's TEXT, inside the fences.
        pub head: Range<usize>,
        pub chapters: Vec<LegacyChapter>,
    }

    /// Whether this file is in the previous encoding.
    ///
    /// DECIDED BY THE FIRST NON-BLANK LINE, which is the one place the two
    /// encodings cannot agree: a legacy document opens with the head's fence,
    /// and an attribute document opens with a heading. Nothing else about the
    /// two shapes is a reliable discriminator — both hold `##` chapters.
    pub fn is_legacy(source: &str) -> bool {
        source
            .lines()
            .find(|l| !l.trim().is_empty())
            .and_then(fence_of)
            .is_some_and(|(_, _, info)| info == "anthill")
    }

    /// Read one, or `None` if it is not in this encoding.
    pub fn read(source: &str) -> Option<LegacyDocument> {
        let lines = lines(source);
        let mut head: Option<Range<usize>> = None;
        let mut after = 0usize;
        let mut i = 0usize;
        while i < lines.len() {
            let Some((marker, run, info)) = fence_of(lines[i].text) else {
                i += 1;
                continue;
            };
            let content_start = lines[i].end;
            let mut j = i + 1;
            let mut content_end = None;
            while j < lines.len() {
                if let Some((cm, cr, ci)) = fence_of(lines[j].text) {
                    if cm == marker && cr >= run && ci.is_empty() {
                        content_end = Some(lines[j].start);
                        break;
                    }
                }
                j += 1;
            }
            let content_end = content_end?;
            if info == "anthill" {
                head = Some(content_start..content_end);
                after = j + 1;
                break;
            }
            i = j + 1;
        }
        let head = head?;

        let mut chapters: Vec<LegacyChapter> = Vec::new();
        let mut open_fence: Option<(char, usize)> = None;
        for line in &lines[after..] {
            if let Some((marker, run, info)) = fence_of(line.text) {
                match open_fence {
                    Some((om, or)) => {
                        if marker == om && run >= or && info.is_empty() {
                            open_fence = None;
                        }
                    }
                    None => open_fence = Some((marker, run)),
                }
                continue;
            }
            if open_fence.is_some() {
                continue;
            }
            let Some((level, text)) = heading_of(line.text) else {
                continue;
            };
            if level > 3 {
                continue;
            }
            if let Some(last) = chapters.last_mut() {
                last.body.end = line.start;
            }
            chapters.push(LegacyChapter {
                level,
                heading: text.to_string(),
                body: line.end..source.len(),
            });
        }
        for c in chapters.iter_mut() {
            let text = &source[c.body.clone()];
            let lead = text.len() - text.trim_start().len();
            let trail = text.len() - text.trim_end().len();
            let start = c.body.start + lead;
            c.body = start..(c.body.end - trail).max(start);
        }
        Some(LegacyDocument { head, chapters })
    }
}

// ── Term rendering for the escape spelling ─────────────────────

/// The backticked spelling of a value with no data spelling (§3.2).
pub fn term_value(kb: &KnowledgeBase, term: TermId) -> String {
    format!("`{}`", print::TermPrinter::new(kb).print_term(term))
}

/// Build the attributes chapter's fields for one fact, in DECLARED order, with
/// a `FieldGroup`'s members pulled together.
///
/// The order is the entity's own, so the mapping does not have to restate it and
/// cannot drift from it. A group is emitted where its FIRST member is declared,
/// which is what puts `status`/`status_agent`/`status_at` together wherever
/// `status` sits.
pub fn attribute_fields(
    kb: &KnowledgeBase,
    fact: TermId,
    functor: &str,
    mapping: &DocumentMapping,
) -> Vec<AttrField> {
    let slots = mapping.attribute_slots(functor);
    let mut out: Vec<AttrField> = Vec::new();
    let mut written: Vec<String> = Vec::new();
    for slot in &slots {
        if written.contains(&slot.name) {
            continue;
        }
        let members: Vec<&AttrSlot> = match mapping.group_of_field(functor, &slot.name) {
            Some(group) => group
                .fields
                .iter()
                .filter_map(|f| slots.iter().find(|s| s.name == *f))
                .collect(),
            None => vec![slot],
        };
        let mut group_lines: Vec<AttrField> = Vec::new();
        for member in members {
            written.push(member.name.clone());
            if mapping
                .chapters
                .iter()
                .any(|c| c.functor == functor && c.field == member.name)
            {
                continue;
            }
            let Some(value) = value_at(kb, fact, &member.path) else {
                continue;
            };
            // An absent Option, and an Option holding an EMPTY collection, are
            // written as no line at all (§3.5).
            if is_absent(kb, value) || is_empty_collection(kb, value, &member.ty) {
                continue;
            }
            let text = spell_write(kb, value, &member.ty, mapping)
                .unwrap_or_else(|| term_value(kb, unwrap_option(kb, value, &member.ty)));
            group_lines.push(AttrField {
                key: member.name.clone(),
                value: text,
                separated: false,
            });
        }
        if let Some(first) = group_lines.first_mut() {
            first.separated = true;
        }
        out.extend(group_lines);
    }
    if let Some(first) = out.first_mut() {
        first.separated = false;
    }
    out
}

/// Follow a slot's path into a fact: one named argument, or one inside a
/// flattened record's value.
pub fn value_at(kb: &KnowledgeBase, fact: TermId, path: &[String]) -> Option<TermId> {
    let mut current = fact;
    for segment in path {
        let Term::Fn { named_args, .. } = kb.get_term(current) else {
            return None;
        };
        current = get_named_arg(kb, named_args, segment)?;
    }
    Some(current)
}

/// Whether a value is a collection with nothing in it — written as no line at
/// all, exactly as an absent `Option` is.
///
/// THE ONE PLACE THIS ENCODING IS NOT VALUE-PRESERVING (§3.5). `some([])` and
/// `none` are different values and writing neither means the document cannot
/// tell them apart. It is the right trade here — an item with no dependencies
/// and an item with an empty dependency list are the same item — but a domain
/// that needs the distinction cannot use this rule.
fn is_empty_collection(kb: &KnowledgeBase, value: TermId, ty: &FieldType) -> bool {
    match ty {
        FieldType::List(_) => list_elements(kb, value).is_some_and(|e| e.is_empty()),
        FieldType::Option(inner) => match (inner.as_ref(), option_value(kb, value)) {
            (FieldType::List(_), Some(v)) => list_elements(kb, v).is_some_and(|e| e.is_empty()),
            _ => false,
        },
        _ => false,
    }
}

/// The term a backticked value should print: the value INSIDE an `Option`, so
/// that `- acceptance: \`[FactHolds(…)]\`` reads back through the same
/// `some(value: …)` wrapper the data spelling would have.
fn unwrap_option(kb: &KnowledgeBase, value: TermId, ty: &FieldType) -> TermId {
    match ty {
        FieldType::Option(_) => option_value(kb, value).unwrap_or(value),
        _ => value,
    }
}

/// The attributes chapter's satellite-list fields, one per declared list that
/// has elements. Elements arrive already spelled, in the order they were written.
pub fn list_fields(mapping: &DocumentMapping, elements: &HashMap<String, Vec<String>>) -> Vec<AttrField> {
    let mut out = Vec::new();
    for spec in &mapping.lists {
        let Some(values) = elements.get(&spec.named) else {
            continue;
        };
        if values.is_empty() {
            continue;
        }
        out.push(AttrField {
            key: spec.named.clone(),
            value: values.join(", "),
            separated: true,
        });
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn schema() -> DomainSchema {
        DomainSchema {
            functors: vec![
                FunctorSchema {
                    name: "WorkItem".into(),
                    fields: vec![
                        FieldSchema {
                            name: "id".into(),
                            ty: FieldType::Text,
                        },
                        FieldSchema {
                            name: "created".into(),
                            ty: FieldType::Text,
                        },
                        FieldSchema {
                            name: "last_status_change".into(),
                            ty: FieldType::Named("StatusChange".into()),
                        },
                        FieldSchema {
                            name: "description".into(),
                            ty: FieldType::Option(Box::new(FieldType::Text)),
                        },
                        FieldSchema {
                            name: "acceptance".into(),
                            ty: FieldType::List(Box::new(FieldType::Named(
                                "AcceptanceCriterion".into(),
                            ))),
                        },
                        FieldSchema {
                            name: "depends_on".into(),
                            ty: FieldType::Option(Box::new(FieldType::List(Box::new(
                                FieldType::Text,
                            )))),
                        },
                    ],
                },
                FunctorSchema {
                    name: "StatusChange".into(),
                    fields: vec![
                        FieldSchema {
                            name: "status".into(),
                            ty: FieldType::Named("WorkStatus".into()),
                        },
                        FieldSchema {
                            name: "agent".into(),
                            ty: FieldType::Option(Box::new(FieldType::Text)),
                        },
                        FieldSchema {
                            name: "at".into(),
                            ty: FieldType::Option(Box::new(FieldType::Text)),
                        },
                        FieldSchema {
                            name: "reason".into(),
                            ty: FieldType::Option(Box::new(FieldType::Text)),
                        },
                    ],
                },
                FunctorSchema {
                    name: "Feedback".into(),
                    fields: vec![
                        FieldSchema {
                            name: "workitem".into(),
                            ty: FieldType::Text,
                        },
                        FieldSchema {
                            name: "at".into(),
                            ty: FieldType::Text,
                        },
                        FieldSchema {
                            name: "author".into(),
                            ty: FieldType::Text,
                        },
                        FieldSchema {
                            name: "content".into(),
                            ty: FieldType::Text,
                        },
                    ],
                },
                FunctorSchema {
                    name: "Tag".into(),
                    fields: vec![
                        FieldSchema {
                            name: "workitem".into(),
                            ty: FieldType::Text,
                        },
                        FieldSchema {
                            name: "name".into(),
                            ty: FieldType::Text,
                        },
                    ],
                },
            ],
            enums: vec![(
                "WorkStatus".into(),
                vec![
                    ("Open".into(), false),
                    ("Claimed".into(), false),
                    ("Delivered".into(), false),
                ],
            )],
        }
    }

    fn mapping() -> DocumentMapping {
        DocumentMapping {
            level: 2,
            attributes: "Attributes".into(),
            field_groups: vec![
                FieldGroupSpec {
                    functor: "WorkItem".into(),
                    fields: vec!["id".into(), "created".into()],
                },
                FieldGroupSpec {
                    functor: "WorkItem".into(),
                    fields: vec![
                        "status".into(),
                        "status_agent".into(),
                        "status_at".into(),
                    ],
                },
            ],
            scalar_forms: vec![ScalarFormSpec {
                sort: "AcceptanceCriterion".into(),
                constructor: "ToolPasses".into(),
                slot: "tool".into(),
            }],
            chapters: vec![
                ChapterSpec {
                    functor: "WorkItem".into(),
                    field: "description".into(),
                    named: "Description".into(),
                },
                ChapterSpec {
                    functor: "WorkItem".into(),
                    field: "status_reason".into(),
                    named: "Reason".into(),
                },
            ],
            groups: vec![ChapterGroupSpec {
                functor: "Feedback".into(),
                container: "Changes".into(),
                kind: "feedback".into(),
                key: "workitem".into(),
                heading: vec!["at".into(), "author".into()],
                field: "content".into(),
            }],
            lists: vec![SatelliteListSpec {
                functor: "Tag".into(),
                named: "tags".into(),
                field: "name".into(),
                key: "workitem".into(),
            }],
            flat_records: vec![FlatRecordSpec {
                functor: "WorkItem".into(),
                field: "last_status_change".into(),
                prefix: "status".into(),
            }],
            schema: schema(),
        }
    }

    const DOC: &str = "\
## Attributes

- id: WI-1121
- created: 2026-08-17T08:43:54Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-18T15:28:04Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-1114

- tags: wi437

## Description

anthill-todo backend, INCREMENT 2c.

### the id has three parts

Hand-added prose rides along inside its chapter.

## Changes

### 2026-08-17T09:19:35Z — feedback — user

id should be minted from content, not from a counter.

### 2026-08-18T15:27:52Z — feedback — claude

delivered.
";

    #[test]
    fn the_mapping_is_well_formed_and_names_its_item_functor() {
        let m = mapping();
        m.check().expect("well formed");
        assert_eq!(m.item_functor(), Some("WorkItem"));
    }

    #[test]
    fn the_attributes_chapter_is_read_as_fields() {
        let doc = read_document(DOC, &mapping()).expect("reads");
        assert!(doc.faults.is_empty(), "{:#?}", doc.faults);
        assert_eq!(doc.attribute("id"), Some("WI-1121"));
        assert_eq!(doc.attribute("status"), Some("Delivered"));
        assert_eq!(
            doc.attribute("acceptance"),
            Some("cargo-test, scaland-sbt-test")
        );
        assert_eq!(doc.attribute("tags"), Some("wi437"));
    }

    /// DRIVES the reading: the document's facts are the anthill source a plain
    /// `fact` file would have held, prose fields excepted.
    #[test]
    fn a_document_denotes_its_facts() {
        let doc = read_document(DOC, &mapping()).expect("reads");
        let facts = document_facts(&doc, &mapping(), "id").expect("denotes");
        assert!(facts.faults.is_empty(), "{:#?}", facts.faults);
        let lines: Vec<&str> = facts.source.lines().collect();
        assert_eq!(lines.len(), 4, "{:#?}", lines);
        assert_eq!(
            lines[0],
            "fact WorkItem(id: \"WI-1121\", created: \"2026-08-17T08:43:54Z\", \
             acceptance: [ToolPasses(tool: \"cargo-test\"), ToolPasses(tool: \"scaland-sbt-test\")], \
             depends_on: some(value: [\"WI-1114\"]), \
             last_status_change: StatusChange(status: Delivered, agent: some(value: \"claude\"), \
             at: some(value: \"2026-08-18T15:28:04Z\")))"
        );
        assert_eq!(lines[1], "fact Tag(workitem: \"WI-1121\", name: \"wi437\")");
        assert_eq!(
            lines[2],
            "fact Feedback(workitem: \"WI-1121\", at: \"2026-08-17T09:19:35Z\", author: \"user\")"
        );
        // The description's prose binds to the item's fact, and each entry's to
        // its own.
        assert_eq!(facts.prose.len(), 3);
        assert_eq!(facts.prose[0].fact, 0);
        assert_eq!(facts.prose[0].path, vec!["description".to_string()]);
        let seg = &doc.segments[facts.prose[0].segment];
        assert!(DOC[seg.body.clone()].starts_with("anthill-todo backend"));
        assert!(
            DOC[seg.body.clone()].contains("### the id has three parts"),
            "a heading below the structural level rides along inside its chapter"
        );
    }

    #[test]
    fn a_file_with_no_attributes_chapter_is_not_an_item() {
        let err = read_document("## Description\n\ntext\n", &mapping()).unwrap_err();
        assert!(matches!(err, DocumentError::NoAttributes { .. }), "{err:?}");
    }

    #[test]
    fn text_before_the_first_chapter_is_a_load_error() {
        let err = read_document("stray\n\n## Attributes\n\n- id: X\n", &mapping()).unwrap_err();
        assert!(
            matches!(err, DocumentError::TextBeforeFirstChapter { .. }),
            "{err:?}"
        );
    }

    #[test]
    fn a_heading_above_the_structural_level_is_a_load_error() {
        let err = read_document("# Title\n\n## Attributes\n\n- id: X\n", &mapping()).unwrap_err();
        assert!(
            matches!(err, DocumentError::HeadingAboveLevel { .. }),
            "{err:?}"
        );
    }

    #[test]
    fn an_unclosed_fence_is_a_load_error_naming_its_line() {
        let src = "## Attributes\n\n- id: X\n\n## Description\n\n```\nnever closed\n";
        let err = read_document(src, &mapping()).unwrap_err();
        assert_eq!(err, DocumentError::UnclosedFence { line: 7 });
    }

    #[test]
    fn a_hash_inside_a_fenced_block_is_not_a_heading() {
        let src = "## Attributes\n\n- id: X\n\n## Description\n\n```sh\n## not a chapter\n```\n";
        let doc = read_document(src, &mapping()).expect("reads");
        assert_eq!(doc.segments.len(), 2);
        assert!(src[doc.segments[1].body.clone()].contains("## not a chapter"));
    }

    /// A fault is SCOPED: a key that names no field costs that field, and the
    /// rest of the item still loads — but it BLOCKS, because writing the file
    /// back would drop it.
    #[test]
    fn an_unknown_attributes_key_costs_that_field_and_blocks() {
        let src = "## Attributes\n\n- id: WI-1\n\n- nonesuch: 3\n";
        let doc = read_document(src, &mapping()).expect("reads");
        let facts = document_facts(&doc, &mapping(), "id").expect("denotes");
        assert_eq!(facts.source.trim(), "fact WorkItem(id: \"WI-1\")");
        assert_eq!(facts.faults.len(), 1);
        assert!(facts.faults[0].blocking);
        assert!(facts.faults[0].message.contains("nonesuch"));
    }

    #[test]
    fn a_repeated_key_is_a_guess_and_blocks() {
        let src = "## Attributes\n\n- id: WI-1\n\n- id: WI-2\n";
        let doc = read_document(src, &mapping()).expect("reads");
        assert_eq!(doc.attribute("id"), Some("WI-1"));
        assert!(doc.blocking());
    }

    #[test]
    fn a_backticked_value_is_an_anthill_term() {
        let src = "## Attributes\n\n- id: WI-1\n\n- acceptance: `[FactHolds(domain: \"kb\", pattern: p)]`\n";
        let doc = read_document(src, &mapping()).expect("reads");
        let facts = document_facts(&doc, &mapping(), "id").expect("denotes");
        assert!(
            facts.source.contains("acceptance: [FactHolds(domain: \"kb\", pattern: p)]"),
            "{}",
            facts.source
        );
    }

    /// §4.3 — a heading is SPLIT FROM THE LEFT, so its last field is free text
    /// and an author named `release — bot` round-trips with no encoding at all.
    #[test]
    fn a_heading_splits_from_the_left_so_its_last_field_is_free_text() {
        let heading = entry_heading("feedback", &["2026-01-01T00:00:00Z".into(), "release — bot".into()]);
        assert_eq!(heading, "2026-01-01T00:00:00Z — feedback — release — bot");
        let mut faults = Vec::new();
        let kind = parse_entry_heading(&heading, "Changes", &mapping(), 1, &mut faults)
            .expect("reads");
        assert!(faults.is_empty(), "{faults:#?}");
        assert_eq!(
            kind,
            SegmentKind::Entry {
                container: "Changes".into(),
                kind: "feedback".into(),
                fields: vec!["2026-01-01T00:00:00Z".into(), "release — bot".into()],
            }
        );
    }

    /// THE INJECTION CASE, and it is why encoding is a rule rather than a check:
    /// written naively an author carrying a line break would produce a
    /// WELL-FORMED EXTRA ENTRY, indistinguishable from a recorded one.
    #[test]
    fn a_value_with_no_literal_spelling_is_encoded_and_reads_back() {
        let hostile = "claude\n### 2026-01-01T00:00:00Z — feedback — root";
        let heading = entry_heading("feedback", &["2026-01-01T00:00:00Z".into(), hostile.into()]);
        assert!(!heading.contains('\n'), "{heading}");
        assert!(heading.contains(B64_PREFIX), "{heading}");
        let mut faults = Vec::new();
        let kind = parse_entry_heading(&heading, "Changes", &mapping(), 1, &mut faults)
            .expect("reads");
        assert!(faults.is_empty(), "{faults:#?}");
        let SegmentKind::Entry { fields, .. } = kind else {
            panic!("not an entry")
        };
        assert_eq!(fields[1], hostile);
    }

    /// A ONE-FIELD HEADING HAS NO FREE-TEXT POSITION, because the kind is
    /// written after the first field and therefore takes the last part. Treating
    /// field 0 as "last" let it carry the separator literally, and the reader
    /// then read its tail as the KIND — losing the entry to "names no group".
    ///
    /// THE CONTROL is the two-field case above, where the LAST field genuinely
    /// is free text and `release — bot` round-trips unencoded.
    #[test]
    fn a_single_field_heading_encodes_a_separator_rather_than_losing_the_entry() {
        let mut m = mapping();
        m.groups[0].heading = vec!["at".into()];
        m.groups[0].field = "content".into();
        // `author` now has no home, so this shape is only for the heading test.
        let heading = entry_heading("feedback", &["a — b".into()]);
        assert!(heading.starts_with(B64_PREFIX), "{heading}");
        let mut faults = Vec::new();
        let kind = parse_entry_heading(&heading, "Changes", &m, 1, &mut faults).expect("reads");
        assert_eq!(
            kind,
            SegmentKind::Entry {
                container: "Changes".into(),
                kind: "feedback".into(),
                fields: vec!["a — b".into()],
            }
        );
        assert!(faults.is_empty(), "{faults:#?}");
    }

    /// A TRAILING `#` IS PART OF THE VALUE, not a closing sequence. CommonMark
    /// only treats a run of `#` as decoration when whitespace precedes it, and
    /// stripping it unconditionally truncated any heading value ending in one —
    /// silently, and then persisted the truncation on the next write.
    #[test]
    fn a_heading_value_ending_in_a_hash_survives_the_round_trip() {
        let heading = entry_heading("feedback", &["2026-01-01T00:00:00Z".into(), "bot#".into()]);
        let line = format!("### {heading}");
        let (level, text) = heading_of(&line).expect("a heading");
        assert_eq!(level, 3);
        let mut faults = Vec::new();
        let kind = parse_entry_heading(text, "Changes", &mapping(), 1, &mut faults).expect("reads");
        let SegmentKind::Entry { fields, .. } = kind else {
            panic!("not an entry")
        };
        assert_eq!(fields[1], "bot#", "the author kept its last character");
        // …and the decoration form still works where CommonMark says it does.
        assert_eq!(heading_of("## Attributes ##").expect("a heading").1, "Attributes");
    }

    /// §2 admits no region outside a chapter, and the check must not depend on
    /// what SHAPE the stray content has: a leading fenced block, or a heading
    /// deeper than the structural level, used to land in no segment at all and
    /// be dropped by the next write with nothing reported.
    #[test]
    fn content_before_the_first_chapter_is_refused_whatever_shape_it_has() {
        for stray in [
            "loose text\n\n## Attributes\n\n- id: X\n",
            "```\na fenced block\n```\n\n## Attributes\n\n- id: X\n",
            "### a deep heading\n\n## Attributes\n\n- id: X\n",
        ] {
            assert!(
                matches!(
                    read_document(stray, &mapping()),
                    Err(DocumentError::TextBeforeFirstChapter { .. })
                ),
                "not refused: {stray}"
            );
        }
    }

    #[test]
    fn a_value_that_begins_with_the_encoding_prefix_is_itself_encoded() {
        let literal = "b64:not-really";
        let written = encode_heading_field(literal, true);
        assert_ne!(written, literal);
        assert_eq!(decode_heading_field(&written).unwrap(), literal);
    }

    /// §4.1 — prose written elsewhere arrives with its own hierarchy and is
    /// DEMOTED by the minimum that clears the reserved set, not refused.
    #[test]
    fn prose_with_its_own_headings_is_demoted_by_the_minimum() {
        let written = "# Overview\n\ntext\n\n## The id\n\nmore\n\n### three parts\n\nend\n";
        let in_field = demote_prose(written, 2).expect("demotes");
        assert!(in_field.starts_with("### Overview\n"), "{in_field}");
        assert!(in_field.contains("#### The id"), "{in_field}");
        assert!(in_field.contains("##### three parts"), "{in_field}");
        // An entry reserves one level more, so the same text demotes one further.
        let in_entry = demote_prose(written, 3).expect("demotes");
        assert!(in_entry.starts_with("#### Overview\n"), "{in_entry}");
        assert!(in_entry.contains("###### three parts"), "{in_entry}");
        // …and it is IDEMPOTENT: stored prose has no collision, so a round trip
        // is identity from the second write onward.
        assert_eq!(demote_prose(&in_field, 2).unwrap(), in_field);
        assert_eq!(demote_prose(&in_entry, 3).unwrap(), in_entry);
    }

    #[test]
    fn a_hash_inside_a_fence_is_not_demoted() {
        let written = "```md\n# not a heading\n```\n";
        assert_eq!(demote_prose(written, 2).unwrap(), written);
    }

    #[test]
    fn a_demotion_past_level_six_is_refused_naming_the_heading() {
        let written = "# a\n\n## b\n\n### c\n\n#### d\n\n##### e\n\n###### f\n";
        let err = demote_prose(written, 2).unwrap_err();
        let DocumentError::UnwritableProse { reason } = err else {
            panic!("wrong error")
        };
        assert!(reason.contains('f'), "{reason}");
    }

    #[test]
    fn prose_with_an_unbalanced_fence_is_refused_before_it_is_written() {
        let err = demote_prose("text\n\n```\nnever closed\n", 2).unwrap_err();
        assert!(matches!(err, DocumentError::UnclosedFence { .. }), "{err:?}");
    }

    /// The rendering test, not a character blacklist: an INTRAWORD `_` does not
    /// open emphasis, so `prop025_1` is inert and quoting it would cost a pair
    /// of backticks for nothing.
    #[test]
    fn inertness_is_decided_by_the_rendering() {
        assert!(renders_as_itself("prop025_1"));
        assert!(renders_as_itself("WI-20260818-7X7NK-a-projection"));
        assert!(renders_as_itself("2026-08-17T08:43:54Z"));
        assert!(!renders_as_itself("_leading"));
        assert!(!renders_as_itself("a [link](x)"));
        assert!(!renders_as_itself("`code`"));
        assert!(!renders_as_itself("a*b*c"));
        assert!(!renders_as_itself(" padded "));
        assert!(!renders_as_itself(""));
    }

    #[test]
    fn base64_round_trips() {
        for s in ["", "a", "ab", "abc", "abcd", "line\nbreak", "— em dash —"] {
            let encoded = base64_encode(s.as_bytes());
            if s.is_empty() {
                assert!(encoded.is_empty());
                continue;
            }
            assert_eq!(
                String::from_utf8(base64_decode(&encoded).expect("decodes")).unwrap(),
                s
            );
        }
        assert!(base64_decode("!!!!").is_none());
    }

    /// The blank-line rule, which is the whole reason the layout is what it is:
    /// two fields of one `FieldGroup` are ADJACENT, everything else is separated.
    #[test]
    fn a_field_group_is_written_adjacent_and_everything_else_separated() {
        let fields = vec![
            AttrField {
                key: "id".into(),
                value: "WI-1".into(),
                separated: false,
            },
            AttrField {
                key: "created".into(),
                value: "t".into(),
                separated: false,
            },
            AttrField {
                key: "status".into(),
                value: "Open".into(),
                separated: true,
            },
        ];
        let text = render_attributes(2, "Attributes", &fields);
        assert_eq!(
            text,
            "## Attributes\n\n- id: WI-1\n- created: t\n\n- status: Open\n\n"
        );
    }

    /// The concatenation property every rewrite rests on: the segments ARE the
    /// file.
    #[test]
    fn the_segments_reconstruct_the_file() {
        let doc = read_document(DOC, &mapping()).expect("reads");
        let rebuilt: String = doc
            .segments
            .iter()
            .map(|s| &DOC[s.span.clone()])
            .collect::<Vec<_>>()
            .concat();
        assert_eq!(rebuilt, DOC);
    }
}
