//! A work item is a DOCUMENT: an anthill head plus markdown chapters (WI-1120).
//!
//! Design: `rustland/anthill-todo/docs/design/backend-github-coordination.md`
//! §5.3 (the rules) and §5.4 (the artifact). The measurement that motivates it
//! is on this repo's own tracker: **92.5% of it is prose inside string
//! literals** — 1110 descriptions averaging 2107 characters and 1129 feedback
//! entries averaging 2116, each stored as ONE physical line of escaped text,
//! because the grammar has no multi-line string. A work item was already a
//! document with a small structured head, encoded as a string literal.
//!
//! FOUR BACKTICKS on the outer fence, and it is not a style choice: the example
//! CONTAINS a three-backtick block, which would otherwise close the outer one
//! early and hand rustdoc the remainder as a Rust doctest — which then fails to
//! compile. The same nesting rule this module implements, applied to itself.
//!
//! ````text
//! ```anthill                                  <- the HEAD: the file's first
//! fact WorkItem(id: "WI-688", status: …)         fenced block with the
//! fact Feedback(workitem: "WI-688", at: …)       `anthill` info string
//! ```
//!
//! ## description                              <- a FIELD chapter
//!
//! whole-`step` direct derivation …
//!
//! ### why the intermediate pass exists        <- prose, carried verbatim
//!
//! ## Feedback                                 <- a CONTAINER
//!
//! ### 2026-07-10T11:02:10Z — user             <- an ENTRY
//!
//! both deferrals landed …
//! ````
//!
//! ## Heading vs chapter
//!
//! A **heading** is markdown syntax: a line beginning with `#`. A **chapter** is
//! this format's unit of meaning: a named region of prose that fills exactly one
//! field of one fact, introduced by a heading at a STRUCTURAL level and running
//! to the next heading at that level.
//!
//! So every chapter begins with a heading, but **not every heading begins a
//! chapter**. A heading below the structural level is ordinary markdown, part of
//! its chapter's text, carried verbatim — which is exactly why those levels are
//! RESERVED. If any heading could start a chapter, a subsection someone typed
//! mid-description would silently cut the field in half, and the tail would
//! reappear as an innocuous-looking unreferenced chapter.
//!
//! There are TWO structural levels and they nest: `##` carries fields and
//! containers, `###` carries a container's entries, and prose begins at `####`.
//! A repeated fact is not a field of the item, and grouping feedback under one
//! container rather than strewing timestamped chapters across the top level is
//! what says so.
//!
//! ## What this module is and is not
//!
//! It is a SCANNER, not a markdown implementation. Nothing here renders
//! markdown — GitHub does that — so the whole job is finding headings at the
//! reserved levels while tracking fenced code blocks, and cutting the file into
//! byte ranges. No markdown dependency is taken and none is wanted.
//!
//! It is also DOMAIN-NEUTRAL. Which functor's which field becomes which chapter
//! arrives as a [`DocumentMapping`], declared in anthill (`anthill.stage0.document`)
//! and read out of the KB by the host. This module learns exactly one concept —
//! *this field's text is the chapter named N* — and never learns stage0's schema.

use std::fmt;
use std::ops::Range;

// ── The declared mapping (§5.4) ────────────────────────────────

/// A prose field of a fact that occurs ONCE per document: one chapter, fixed
/// name. `Chapter(functor: WorkItem, field: "description", named: "description")`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChapterSpec {
    pub functor: String,
    pub field: String,
    pub named: String,
}

/// A satellite fact keyed to the item and repeated 0..n: one container chapter,
/// one entry chapter per fact inside it.
/// `ChapterGroup(functor: Feedback, container: "Feedback", field: "content",
///  named_by: "at", decorate: ["author"])`.
///
/// The SPLIT from [`ChapterSpec`] is what keeps a `repeated` flag out of the
/// mapping: repetition is not a property of a field, it is the whole point of a
/// group. Making the two illegal to confuse is cheaper than checking a boolean.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChapterGroupSpec {
    pub functor: String,
    pub container: String,
    pub field: String,
    pub named_by: String,
    pub decorate: Vec<String>,
}

/// The whole declared mapping, plus the structural level it is written at.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DocumentMapping {
    /// `DocumentFormat(level:)` — fields and containers sit here, a container's
    /// entries at `level + 1`, and prose begins below that.
    pub level: usize,
    pub chapters: Vec<ChapterSpec>,
    pub groups: Vec<ChapterGroupSpec>,
}

impl DocumentMapping {
    pub fn chapter_for(&self, functor: &str) -> Option<&ChapterSpec> {
        self.chapters.iter().find(|c| c.functor == functor)
    }

    pub fn group_for(&self, functor: &str) -> Option<&ChapterGroupSpec> {
        self.groups.iter().find(|g| g.functor == functor)
    }

    fn field_named(&self, name: &str) -> Option<&ChapterSpec> {
        self.chapters.iter().find(|c| c.named == name)
    }

    fn container_named(&self, name: &str) -> Option<&ChapterGroupSpec> {
        self.groups.iter().find(|g| g.container == name)
    }
}

/// Everything after a chapter's name in its heading — the author, a
/// human-readable date. REGENERATED from the head and CHECKED against it at
/// load, exactly as §4 treats the directory name: a projection regenerated
/// WITHOUT being read would silently overwrite a hand correction.
pub const DECORATION_SEPARATOR: &str = " — ";

// ── Errors ─────────────────────────────────────────────────────

/// A document that cannot be read as one. Every variant is a LOAD ERROR, and
/// each names the file and the offending heading — §5.3's malformed-editing
/// table, which a format people hand-edit owes its readers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DocumentError {
    /// No fenced block with the `anthill` info string. The head is where every
    /// structured field lives, so a document without one holds no rows at all.
    NoHead,
    /// The head fence is opened and never closed.
    UnterminatedHead { line: usize },
    /// A heading at the reserved level that the mapping does not name. THE
    /// TRUNCATION CASE, and it must not look like a note: with unreferenced
    /// chapters merely "legal", a level-N heading typed mid-description would
    /// end that chapter there and the tail would reappear as an innocent-looking
    /// stray chapter.
    UnknownChapter { name: String, line: usize },
    /// An entry heading with no container above it — the truncation case one
    /// level down.
    EntryOutsideContainer { name: String, line: usize },
    /// Two chapters with one name where the mapping declares a single field:
    /// `update` could not know which to rewrite.
    DuplicateChapter { name: String, line: usize },
    /// The prose a writer was handed cannot survive a round trip through this
    /// format. Refused BEFORE the file is written — see [`check_prose`].
    UnwritableProse { reason: String },
}

impl fmt::Display for DocumentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DocumentError::NoHead => write!(
                f,
                "no ```anthill block — an item document is a head of facts followed by \
                 markdown chapters, and this file has no head"
            ),
            DocumentError::UnterminatedHead { line } => write!(
                f,
                "the ```anthill block opened at line {line} is never closed"
            ),
            DocumentError::UnknownChapter { name, line } => write!(
                f,
                "line {line}: `{name}` is a chapter heading the mapping does not name. That \
                 level is reserved for the mapping — if this is prose, give it a deeper \
                 heading, because at this level it ENDS the chapter above it"
            ),
            DocumentError::EntryOutsideContainer { name, line } => write!(
                f,
                "line {line}: the entry `{name}` sits under no container heading"
            ),
            DocumentError::DuplicateChapter { name, line } => write!(
                f,
                "line {line}: a second chapter named `{name}`, where the mapping declares one \
                 field — a rewrite could not know which of them it means"
            ),
            DocumentError::UnwritableProse { reason } => write!(f, "{reason}"),
        }
    }
}

// ── The document model ─────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SegmentKind {
    /// A `##` chapter filling one field of the document's own primary fact.
    Field { name: String },
    /// A `##` container heading, together with whatever text precedes its first
    /// entry. It maps to no datum: it is the only structural thing in the file
    /// that names nothing.
    Container { name: String },
    /// A `###` entry inside the container named here.
    Entry {
        container: String,
        name: String,
        decoration: Vec<String>,
    },
}

/// One structural region of the document's body, as a byte range of the source.
///
/// FLAT, not a tree, and deliberately: rendering the file is then a
/// concatenation and replacing one chapter is one `Vec` element, which is what
/// makes "rewrite only the chapters whose text actually changed, and leave every
/// other chapter byte-identical" (§5.3) fall out rather than be arranged for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Segment {
    pub kind: SegmentKind,
    /// The whole region, heading line included, up to the next segment.
    pub span: Range<usize>,
    /// The prose inside it: everything after the heading line, with the blank
    /// lines around it trimmed off. Empty for a container.
    pub body: Range<usize>,
}

impl Segment {
    pub fn name(&self) -> &str {
        match &self.kind {
            SegmentKind::Field { name } | SegmentKind::Container { name } => name,
            SegmentKind::Entry { name, .. } => name,
        }
    }
}

/// A document, as byte ranges into the source it was read from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Document {
    /// The head's TEXT — inside the fences, so a parser is handed anthill and
    /// nothing else. Add this range's start to every span the parse returns and
    /// they address the whole file.
    pub head: Range<usize>,
    /// Where the body begins: the first structural heading, or end of file.
    /// Everything before it — the preamble, the head, the fence lines, the blank
    /// line after them — is one stretch of text nothing here interprets.
    pub body_start: usize,
    pub segments: Vec<Segment>,
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
    // `## text ##` — a closing run of `#` is decoration in CommonMark.
    Some((level, rest.trim().trim_end_matches('#').trim()))
}

/// Split a heading's text into its chapter NAME and its DECORATION.
fn split_decoration(text: &str) -> (String, Vec<String>) {
    let mut parts = text.split(DECORATION_SEPARATOR);
    let name = parts.next().unwrap_or("").trim().to_string();
    (name, parts.map(|p| p.trim().to_string()).collect())
}

/// Read a head-plus-chapters document.
///
/// THE FENCE TRACKING IS NOT OPTIONAL and not prospective either: 392
/// descriptions and 240 feedback entries on this repo's tracker already contain
/// backticks, and a `#` at the start of a line inside a fenced block is a
/// comment in whatever language the block holds — never a chapter boundary.
pub fn read_document(source: &str, mapping: &DocumentMapping) -> Result<Document, DocumentError> {
    let lines = lines(source);
    let level = mapping.level;

    // ── the head: the FIRST fenced block whose info string is `anthill`
    let mut head: Option<Range<usize>> = None;
    let mut after_head = 0usize;
    let mut i = 0usize;
    while i < lines.len() {
        match fence_of(lines[i].text) {
            Some((marker, run, info)) => {
                let opener_line = lines[i].number;
                let content_start = lines[i].end;
                let mut j = i + 1;
                let mut content_end = None;
                while j < lines.len() {
                    if let Some((close_marker, close_run, close_info)) = fence_of(lines[j].text) {
                        if close_marker == marker && close_run >= run && close_info.is_empty() {
                            content_end = Some(lines[j].start);
                            break;
                        }
                    }
                    j += 1;
                }
                let Some(content_end) = content_end else {
                    // An unterminated fence swallows the rest of the file. Only
                    // the head's own is an error here — a stray fence in prose
                    // is the writer's refusal ([`check_prose`]) rather than the
                    // reader's, because by the time it is read the damage is
                    // already on disk and refusing the whole file would hide it.
                    if info == "anthill" {
                        return Err(DocumentError::UnterminatedHead { line: opener_line });
                    }
                    break;
                };
                if info == "anthill" {
                    head = Some(content_start..content_end);
                    after_head = j + 1;
                    break;
                }
                i = j + 1;
            }
            None => i += 1,
        }
    }
    let Some(head) = head else {
        return Err(DocumentError::NoHead);
    };

    // ── the body: structural headings, fences tracked
    let mut segments: Vec<Segment> = Vec::new();
    let mut body_start = source.len();
    let mut open_fence: Option<(char, usize)> = None;
    // The container a `###` would belong to, and the level-N segment currently
    // being filled (so its span can be closed when the next one opens).
    let mut container: Option<ChapterGroupSpec> = None;

    for line in &lines[after_head..] {
        if let Some((marker, run, info)) = fence_of(line.text) {
            match open_fence {
                Some((open_marker, open_run)) => {
                    if marker == open_marker && run >= open_run && info.is_empty() {
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
        let Some((heading_level, text)) = heading_of(line.text) else {
            continue;
        };

        if heading_level == level {
            let (name, _) = split_decoration(text);
            let kind = if let Some(spec) = mapping.field_named(&name) {
                if segments.iter().any(|s| {
                    matches!(&s.kind, SegmentKind::Field { name: n } if *n == spec.named)
                }) {
                    return Err(DocumentError::DuplicateChapter {
                        name,
                        line: line.number,
                    });
                }
                container = None;
                SegmentKind::Field { name }
            } else if let Some(group) = mapping.container_named(&name) {
                container = Some(group.clone());
                SegmentKind::Container { name }
            } else {
                return Err(DocumentError::UnknownChapter {
                    name,
                    line: line.number,
                });
            };
            close_previous(&mut segments, line.start, source);
            body_start = body_start.min(line.start);
            segments.push(Segment {
                kind,
                span: line.start..source.len(),
                body: line.end..source.len(),
            });
        } else if heading_level == level + 1 {
            // A `###` is an ENTRY only inside a container. Inside a FIELD
            // chapter it is ordinary prose (§5.3's fourth row) — which is what
            // keeps hand-added sub-sections alive.
            let Some(group) = container.clone() else {
                if segments.is_empty() {
                    return Err(DocumentError::EntryOutsideContainer {
                        name: split_decoration(text).0,
                        line: line.number,
                    });
                }
                continue;
            };
            let (name, decoration) = split_decoration(text);
            close_previous(&mut segments, line.start, source);
            segments.push(Segment {
                kind: SegmentKind::Entry {
                    container: group.container.clone(),
                    name,
                    decoration,
                },
                span: line.start..source.len(),
                body: line.end..source.len(),
            });
        }
        // Any other level is prose: shallower than the structural level is not a
        // boundary either, so it can never truncate a chapter.
    }
    if segments.is_empty() {
        body_start = source.len();
    }
    trim_bodies(&mut segments, source);

    Ok(Document {
        head,
        body_start,
        segments,
    })
}

/// Close the segment being filled at `at`, which is where the next one starts.
fn close_previous(segments: &mut [Segment], at: usize, source: &str) {
    if let Some(last) = segments.last_mut() {
        last.span.end = at;
        last.body.end = at.min(source.len());
    }
}

/// A chapter's VALUE is its prose with the blank lines around it dropped, so a
/// document written as `## description\n\n<text>\n\n` yields exactly `<text>`
/// and writing it back reproduces the file byte for byte.
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

// ── Rendering ──────────────────────────────────────────────────

/// The canonical text of one chapter: heading, blank line, prose, blank line.
///
/// A chapter is rendered ONLY when its value changed; every other chapter is
/// carried across as the bytes it already was (§5.3). That is what makes the
/// opacity invariant hold — hand-add a sub-section inside a description, run a
/// command that rewrites the head and renames the file, and the sub-section
/// survives byte-identical.
pub fn render_chapter(level: usize, name: &str, decoration: &[String], body: &str) -> String {
    let mut out = String::with_capacity(body.len() + name.len() + 8);
    out.push_str(&"#".repeat(level));
    out.push(' ');
    out.push_str(name);
    for d in decoration {
        out.push_str(DECORATION_SEPARATOR);
        out.push_str(d);
    }
    out.push_str("\n\n");
    if !body.is_empty() {
        out.push_str(body);
        out.push_str("\n\n");
    }
    out
}

/// The deepest heading level that ENDS this chapter, and so may not appear in its
/// prose.
///
/// IT DIFFERS BY KIND, and making it uniform was a defect: a `###` inside a FIELD
/// chapter is ordinary prose (§5.3's fourth row — the invariant that keeps
/// hand-added sub-sections alive), while inside an ENTRY it starts the next
/// entry. A writer that reserved `level + 1` everywhere refused prose the READER
/// accepts, which is worse than either rule alone would have been: a description
/// carrying a `###` sub-section loaded fine, round-tripped into the fact, and
/// then made its item permanently unwritable — `claim`, `update` and `deliver`
/// all failing on text already on disk.
///
/// A field ends at its own level; an entry ends at its own AND at the container
/// level above it, and `level + 1` is the deeper of those two.
pub fn deepest_reserved_for(kind: &SegmentKind, level: usize) -> usize {
    match kind {
        SegmentKind::Field { .. } | SegmentKind::Container { .. } => level,
        SegmentKind::Entry { .. } => level + 1,
    }
}

/// Refuse prose that this format could not read back.
///
/// THE WRITER'S CHECK, not the reader's, and the direction matters: a value that
/// carries a heading at a level that IS a boundary for its chapter, or an
/// unbalanced fence, would produce a file whose next load truncates or swallows a
/// chapter. Caught HERE, the command fails and nothing is written; caught at read
/// time, the damage is already on disk. §5.3 requires the same scan over
/// pre-existing prose at migration, for the same reason: `\n#` is one escape away
/// in a one-line string literal, and 274 feedback entries on this tracker already
/// carry an escaped newline.
///
/// `deepest_reserved` is the last level that ends this chapter — `level` for a
/// field, `level + 1` for an entry (see [`reserved_for`]'s note on why they
/// differ, and what a uniform rule cost).
pub fn check_prose(value: &str, deepest_reserved: usize) -> Result<(), DocumentError> {
    let mut open_fence: Option<(char, usize)> = None;
    for line in lines(value) {
        if let Some((marker, run, info)) = fence_of(line.text) {
            match open_fence {
                Some((open_marker, open_run)) => {
                    if marker == open_marker && run >= open_run && info.is_empty() {
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
        if let Some((heading_level, text)) = heading_of(line.text) {
            if heading_level <= deepest_reserved {
                return Err(DocumentError::UnwritableProse {
                    reason: format!(
                        "this text carries `{}` on line {} — a heading at level {heading_level}, \
                         which ends this chapter. Writing it would cut the field there and the \
                         rest would read back as a stray chapter. Use a deeper heading (at least \
                         {} `#`)",
                        text,
                        line.number,
                        deepest_reserved + 1
                    ),
                });
            }
        }
    }
    if open_fence.is_some() {
        return Err(DocumentError::UnwritableProse {
            reason: "this text opens a fenced code block and never closes it — written out, the \
                     fence would swallow every chapter after it"
                .to_string(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mapping() -> DocumentMapping {
        DocumentMapping {
            level: 2,
            chapters: vec![ChapterSpec {
                functor: "WorkItem".into(),
                field: "description".into(),
                named: "description".into(),
            }],
            groups: vec![ChapterGroupSpec {
                functor: "Feedback".into(),
                container: "Feedback".into(),
                field: "content".into(),
                named_by: "at".into(),
                decorate: vec!["author".into()],
            }],
        }
    }

    const DOC: &str = r#"```anthill
fact WorkItem(id: "WI-688", status: Open)

fact Feedback(workitem: "WI-688", author: "user", at: "2026-07-10T11:02:10Z")
fact Feedback(workitem: "WI-688", author: "claude", at: "2026-07-11T08:41:02Z")
```

## description

whole-`step` direct derivation.

### why the intermediate pass exists

Hand-added prose lives below the structural level.

## Feedback

### 2026-07-10T11:02:10Z — user

both deferrals landed.

### 2026-07-11T08:41:02Z — claude

delivered.
"#;

    #[test]
    fn the_head_is_the_first_anthill_fence_and_carries_only_facts() {
        let doc = read_document(DOC, &mapping()).expect("reads");
        let head = &DOC[doc.head.clone()];
        assert!(head.starts_with("fact WorkItem(id: \"WI-688\""), "{head}");
        assert!(head.ends_with("2026-07-11T08:41:02Z\")\n"), "{head}");
        assert!(!head.contains("```"), "the fences are not part of the head");
    }

    #[test]
    fn a_field_chapter_and_two_entries_under_one_container() {
        let doc = read_document(DOC, &mapping()).expect("reads");
        let names: Vec<_> = doc
            .segments
            .iter()
            .map(|s| (s.kind.clone(), DOC[s.body.clone()].to_string()))
            .collect();
        assert_eq!(names.len(), 4, "{names:#?}");
        assert!(matches!(&names[0].0, SegmentKind::Field { name } if name == "description"));
        assert!(matches!(&names[1].0, SegmentKind::Container { name } if name == "Feedback"));
        assert!(
            matches!(&names[2].0, SegmentKind::Entry { name, decoration, .. }
                     if name == "2026-07-10T11:02:10Z" && decoration == &["user".to_string()])
        );
        assert_eq!(names[2].1, "both deferrals landed.");
        assert_eq!(names[3].1, "delivered.");
    }

    /// §5.3's fourth row, and the invariant that keeps a user's notes alive: a
    /// heading DEEPER than the structural level is prose, so a `###` typed
    /// inside `## description` rides along inside the field's text.
    #[test]
    fn a_deeper_heading_inside_a_field_chapter_is_prose() {
        let doc = read_document(DOC, &mapping()).expect("reads");
        let body = &DOC[doc.segments[0].body.clone()];
        assert!(
            body.contains("### why the intermediate pass exists"),
            "the sub-section was cut out of its chapter: {body}"
        );
        assert!(body.ends_with("below the structural level."), "{body}");
    }

    /// The concatenation property every rewrite rests on: preamble plus every
    /// segment IS the file.
    #[test]
    fn the_segments_and_the_preamble_reconstruct_the_file() {
        let doc = read_document(DOC, &mapping()).expect("reads");
        let mut rebuilt = DOC[..doc.body_start].to_string();
        for seg in &doc.segments {
            rebuilt.push_str(&DOC[seg.span.clone()]);
        }
        assert_eq!(rebuilt, DOC);
    }

    #[test]
    fn a_hash_inside_a_fenced_block_is_not_a_heading() {
        let src = "```anthill\nfact A()\n```\n\n## description\n\n```sh\n## not a chapter\n```\n\ntail\n";
        let doc = read_document(src, &mapping()).expect("reads");
        assert_eq!(doc.segments.len(), 1);
        assert!(src[doc.segments[0].body.clone()].contains("## not a chapter"));
    }

    #[test]
    fn an_unnamed_heading_at_the_reserved_level_is_the_truncation_case() {
        let src = "```anthill\nfact A()\n```\n\n## description\n\ntext\n\n## Notes\n\nmore\n";
        let err = read_document(src, &mapping()).unwrap_err();
        assert!(
            matches!(&err, DocumentError::UnknownChapter { name, .. } if name == "Notes"),
            "{err:?}"
        );
    }

    #[test]
    fn two_chapters_with_one_name_refuse() {
        let src = "```anthill\nfact A()\n```\n\n## description\n\na\n\n## description\n\nb\n";
        let err = read_document(src, &mapping()).unwrap_err();
        assert!(
            matches!(&err, DocumentError::DuplicateChapter { name, .. } if name == "description"),
            "{err:?}"
        );
    }

    #[test]
    fn an_entry_with_no_container_refuses() {
        let src = "```anthill\nfact A()\n```\n\n### 2026-07-10T11:02:10Z — user\n\ntext\n";
        let err = read_document(src, &mapping()).unwrap_err();
        assert!(
            matches!(&err, DocumentError::EntryOutsideContainer { .. }),
            "{err:?}"
        );
    }

    #[test]
    fn a_file_with_no_head_is_not_a_document() {
        assert_eq!(
            read_document("# just markdown\n", &mapping()).unwrap_err(),
            DocumentError::NoHead
        );
    }

    #[test]
    fn a_missing_chapter_is_simply_absent() {
        let src = "```anthill\nfact A()\n```\n";
        let doc = read_document(src, &mapping()).expect("reads");
        assert!(doc.segments.is_empty());
        assert_eq!(doc.body_start, src.len());
    }

    /// The round trip the writer relies on: render a chapter, read it back, get
    /// the value that went in.
    #[test]
    fn a_rendered_chapter_reads_back_as_its_value() {
        let body = "one line\n\nand another";
        let src = format!(
            "```anthill\nfact A()\n```\n\n{}",
            render_chapter(2, "description", &[], body)
        );
        let doc = read_document(&src, &mapping()).expect("reads");
        assert_eq!(&src[doc.segments[0].body.clone()], body);
    }

    #[test]
    fn prose_carrying_a_reserved_heading_is_refused_before_it_is_written() {
        let field = SegmentKind::Field { name: "description".into() };
        let deepest = deepest_reserved_for(&field, 2);
        let err = check_prose("intro\n\n## a chapter\n\ntail", deepest).unwrap_err();
        assert!(matches!(err, DocumentError::UnwritableProse { .. }), "{err:?}");
        // A heading inside a balanced fence is not a heading.
        assert!(check_prose("```md\n## in a fence\n```", deepest).is_ok());
    }

    /// THE WRITER AND THE READER MUST AGREE, and this is where they did not: a
    /// `###` inside a FIELD chapter is prose the reader carries verbatim
    /// (`a_deeper_heading_inside_a_field_chapter_is_prose`, above), so a writer
    /// that refused it made every item holding one permanently unwritable —
    /// `claim` and `update` failing on text already on disk.
    ///
    /// THE ENTRY CASE IS THE CONTROL: the same `###` inside an entry DOES end it,
    /// and must still be refused. A single uniform rule cannot satisfy both, which
    /// is why the depth is asked per chapter kind.
    #[test]
    fn a_sub_heading_is_prose_in_a_field_and_a_boundary_in_an_entry() {
        let prose = "intro\n\n### a sub-section\n\ntail";
        let field = SegmentKind::Field { name: "description".into() };
        let entry = SegmentKind::Entry {
            container: "Feedback".into(),
            name: "2026-07-10T11:02:10Z".into(),
            decoration: vec![],
        };

        assert!(
            check_prose(prose, deepest_reserved_for(&field, 2)).is_ok(),
            "a `###` inside `## description` is prose — the reader says so"
        );
        assert!(
            check_prose(prose, deepest_reserved_for(&entry, 2)).is_err(),
            "the same `###` inside a `###` entry starts the next entry"
        );
        // …and `####` is prose in both.
        let deeper = "intro\n\n#### a note\n\ntail";
        assert!(check_prose(deeper, deepest_reserved_for(&field, 2)).is_ok());
        assert!(check_prose(deeper, deepest_reserved_for(&entry, 2)).is_ok());
    }

    #[test]
    fn prose_with_an_unbalanced_fence_is_refused() {
        let err = check_prose("text\n\n```\nnever closed\n", 2).unwrap_err();
        // …at every depth: a fence swallows what follows regardless of level.
        assert!(matches!(err, DocumentError::UnwritableProse { .. }), "{err:?}");
    }
}
