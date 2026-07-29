/// Source location tracking (byte offsets into the source text).

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    pub fn from_ts_node(node: &tree_sitter::Node) -> Self {
        Self {
            start: node.start_byte() as u32,
            end: node.end_byte() as u32,
        }
    }

    pub fn merge(a: Span, b: Span) -> Span {
        Span {
            start: a.start.min(b.start),
            end: a.end.max(b.end),
        }
    }
}

/// Line starts for ONE source text, so a byte offset resolves to `line:col`
/// without re-walking the text from byte 0.
///
/// WHY: every diagnostic rendering resolves a span, and the old scan walked from
/// the start of the file per call — so N errors in one file cost O(N × len).
/// Measured on a 2.7 MB source with 2100 diagnostics: ~50 s in the debug CLI,
/// nearly all of it re-walking. Building this once is O(len), and each lookup is
/// then a binary search plus a walk of ONE line.
///
/// THE COLUMN WALK IS THE REMAINING COST, and one line can be the whole file: a
/// generated or minified single-line source keeps the old quadratic (measured at
/// -O0: 2100 lookups over a 2.7 MB ONE-LINE source, 49.4 s — the same text split
/// into ~54-byte lines, 2.2 ms). Hand-written sources have lines; a memo of the
/// last lookup would close even that, and is worth it only if such a source
/// shows up.
///
/// A SINGLE lookup is SLOWER than the scan this replaced, and deliberately so:
/// that scan stopped AT the offset (O(offset)), while building the index reads
/// to EOF. So one error at byte 100 of a 3 MB file went from ~100 steps to a
/// full pass. WI-854's ticket said the one-shot would stay "so single-lookup
/// callers are unaffected"; they are affected, and the trade was taken anyway —
/// every caller in the tree renders a BATCH, where the full pass is amortized
/// over every error, and leaving a cheap-looking one-shot in place is what let
/// the quadratic spread in the first place.
///
/// It is the single owner of the line/col RULE as well: both families' renderings
/// (`ParseError::format_with_source`, `LoadError::format_at`) resolve positions
/// here, so they cannot disagree about what a column counts.
pub struct LineIndex<'a> {
    source: &'a str,
    /// Byte offset of each line's first character; `starts[0]` is always 0, so
    /// this is never empty and line numbers are `starts` positions + 1.
    starts: Vec<u32>,
}

impl<'a> LineIndex<'a> {
    pub fn new(source: &'a str) -> Self {
        // A `Span` is u32, so a source this large cannot be addressed by any span
        // that could be rendered against this index; `as u32` below would wrap and
        // leave `starts` unsorted, which silently breaks every lookup rather than
        // just the far ones. Loud in debug rather than silently wrong.
        debug_assert!(
            source.len() <= u32::MAX as usize,
            "LineIndex over a >= 4 GiB source: line starts would truncate"
        );
        // `match_indices` on a char pattern searches through `memchr`, which is
        // precompiled into `core` — so this stays fast in the debug builds the
        // measurements above come from, where a per-byte closure chain does not
        // inline. No `with_capacity`: a byte-per-line guess was measured 24x too
        // large on this repo's own 3.1 MB tracker file (767 B/line) and too small
        // for ordinary sources, so it mis-served both; `extend`'s amortized growth
        // is honest and costs a few reallocations on an error path.
        let mut starts = vec![0];
        starts.extend(source.match_indices('\n').map(|(i, _)| (i + 1) as u32));
        Self { source, starts }
    }

    /// Convert byte offset to (line, col), both 1-based. Columns count CHARACTERS,
    /// not bytes, which is why the column walks the line rather than subtracting
    /// offsets. An offset past the end, or inside a multi-byte character, resolves
    /// the same way the old full scan did: every character strictly before it counts.
    pub fn line_col(&self, byte_offset: u32) -> (usize, usize) {
        let offset = byte_offset as usize;
        let line = self.starts.partition_point(|&s| (s as usize) <= offset);
        let line_start = self.starts[line - 1] as usize;
        let col = self.source[line_start..]
            .char_indices()
            .take_while(|(i, _)| line_start + i < offset)
            .count()
            + 1;
        (line, col)
    }

    /// Format a span's start as "line:col".
    pub fn format_start(&self, span: Span) -> String {
        let (line, col) = self.line_col(span.start);
        format!("{}:{}", line, col)
    }
}

// ── Located rendering ──────────────────────────────────────────

/// WI-745 / WI-852: the ONE file-prefix rendering, shared by every diagnostic
/// family — [`crate::kb::load::LoadError::Located`] and
/// [`crate::parse::error::ParseError::format_located`] — so which STAGE found a
/// fault cannot change how its location reads. WI-745 gave LOAD errors
/// `path:line:col`; parse errors kept rendering a raw byte offset, so the author
/// got a clickable location or a number to count to depending on a stage
/// boundary they cannot predict (WI-852).
///
/// WHAT IS SHARED: this owns the FILE PREFIX rule; [`LineIndex::format_start`]
/// owns the `line:col` that precedes the message, and BOTH families now resolve
/// and spell a position through it (`ParseError::format_at`, `LoadError`'s ~20
/// message arms). Together those two are the whole location, so the families
/// cannot drift — which they could when this note first claimed otherwise: the
/// load arms each hand-rolled `Span::line_col` + `format!("{}:{}: …")` until the
/// line-index work folded them into one spelling.
///
/// `body` is the already-rendered diagnostic — `line:col: message` when it
/// carries a span, bare `message` when it does not, which is what `has_span`
/// reports. Taken BY VALUE so the pathless case moves it instead of copying.
/// The separator differs between the two cases on purpose: `path:line:col: msg`
/// is the form editors and terminals make clickable, while a span-less
/// `path:msg` would read as a mangled location, so it takes `path: msg`.
pub fn render_located(path: Option<&std::path::Path>, body: String, has_span: bool) -> String {
    match path {
        Some(p) if has_span => format!("{}:{}", p.display(), body),
        Some(p) => format!("{}: {}", p.display(), body),
        None => body,
    }
}

// ── Source identification ──────────────────────────────────────

/// Opaque handle to a loaded source text. Sequential, not hash-consed.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SourceId(u32);

impl SourceId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn from_raw(raw: u32) -> Self {
        SourceId(raw)
    }

    pub fn raw(self) -> u32 {
        self.0
    }
}

/// A span with file identity — for cross-file use in the legacy occurrence side-table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub source: SourceId,
    pub span: Span,
}

impl SourceSpan {
    pub fn new(source: SourceId, start: u32, end: u32) -> Self {
        Self { source, span: Span::new(start, end) }
    }

    pub fn from_span(source: SourceId, span: Span) -> Self {
        Self { source, span }
    }

    pub fn start(&self) -> u32 {
        self.span.start
    }

    pub fn end(&self) -> u32 {
        self.span.end
    }
}

/// A registered source: its display name plus (WI-745) the on-disk path and full
/// text, so a `SourceId` carried by a span can be rendered as `path:line:col`.
struct SourceEntry {
    name: String,
    /// The file's source text. Empty for sources registered by name only
    /// (`register`), in which case span rendering degrades to `1:1`.
    source: std::sync::Arc<str>,
    /// The on-disk path, if known. `None` for embedded / synthetic sources.
    path: Option<std::sync::Arc<std::path::Path>>,
}

/// Registry mapping SourceId → file name + (WI-745) path + source text.
pub struct SourceRegistry {
    entries: Vec<SourceEntry>,
}

impl SourceRegistry {
    pub fn new() -> Self {
        Self { entries: Vec::new() }
    }

    /// Register a source by name only (no text/path). Span rendering against
    /// this source degrades to `1:1`.
    pub fn register(&mut self, name: String) -> SourceId {
        let id = SourceId(self.entries.len() as u32);
        self.entries.push(SourceEntry {
            name,
            source: std::sync::Arc::from(""),
            path: None,
        });
        id
    }

    /// WI-745: register a source WITH its on-disk path and full text, so a load
    /// error carrying the returned `SourceId` renders `path:line:col: message`.
    pub fn register_file(
        &mut self,
        name: String,
        source: std::sync::Arc<str>,
        path: Option<std::sync::Arc<std::path::Path>>,
    ) -> SourceId {
        let id = SourceId(self.entries.len() as u32);
        self.entries.push(SourceEntry { name, source, path });
        id
    }

    pub fn name(&self, id: SourceId) -> &str {
        &self.entries[id.index()].name
    }

    /// WI-745: the `(path, source text)` provenance of a source, for rendering a
    /// span as `path:line:col`. Returns `None` if the id is out of range or the
    /// source carries no text (registered by name only).
    pub fn provenance(
        &self,
        id: SourceId,
    ) -> Option<(Option<std::sync::Arc<std::path::Path>>, std::sync::Arc<str>)> {
        let e = self.entries.get(id.index())?;
        if e.source.is_empty() {
            return None;
        }
        Some((e.path.clone(), e.source.clone()))
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[cfg(test)]
mod line_index_tests {
    use super::{LineIndex, Span};

    /// The scan `Span::line_col` was before [`LineIndex`] existed, kept verbatim
    /// as the ORACLE: the index is a performance change, so "same answer for
    /// every offset" is the whole correctness claim, including the odd offsets
    /// (past the end, inside a multi-byte character) that no caller means to
    /// produce but a recovery span can.
    fn reference_line_col(source: &str, byte_offset: u32) -> (usize, usize) {
        let offset = byte_offset as usize;
        let mut line = 1;
        let mut col = 1;
        for (i, ch) in source.char_indices() {
            if i >= offset {
                break;
            }
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
        (line, col)
    }

    fn agrees_at_every_offset(source: &str) {
        let idx = LineIndex::new(source);
        // `len + 2` so offsets just past the end are covered, then the extremes:
        // a recovery span can carry an offset far beyond the text, and the
        // `partition_point` / `line - 1` indexing must not misbehave there.
        let sweep = (0..=(source.len() as u32 + 2)).chain([u32::MAX / 2, u32::MAX - 1, u32::MAX]);
        for offset in sweep {
            assert_eq!(
                idx.line_col(offset),
                reference_line_col(source, offset),
                "disagreed at offset {offset} of {source:?}"
            );
        }
    }

    #[test]
    fn line_index_agrees_with_the_scan_it_replaced() {
        for source in [
            "",
            "\n",
            "\n\n\n",
            "one line, no newline",
            "first\nsecond\nthird\n",
            "trailing blank line\n\n",
            // Multi-byte: a column counts CHARACTERS, so `é` and `…` must each
            // advance the column by one while advancing the offset by 2 or 3.
            "héllo\nwörld…\nplain\n",
            "…\n…\n",
            // A '\r\n' file: `\r` is an ordinary character, counted in the column.
            "dos\r\nlines\r\n",
        ] {
            agrees_at_every_offset(source);
        }
    }

    #[test]
    fn a_span_start_formats_as_line_colon_col() {
        let idx = LineIndex::new("alpha\nbeta\ngamma\n");
        assert_eq!(idx.format_start(Span::new(6, 10)), "2:1");
        assert_eq!(idx.format_start(Span::new(8, 10)), "2:3");
    }
}
